#!/usr/bin/env python3
"""Instrument research-side sessions: the /attack track (2026-09-17 on) and, before it,
/coordinate-research coordinator sessions.

Usage: python3 notes/harness/instrument/analyze.py [--logs-root DIR] <session-id> [<session-id> ...] > all.json
       python3 notes/harness/instrument/report.py --attack all.json      # per-session table for /harness-review
       python3 notes/harness/instrument/report.py all.json               # the coordinator-era long report
Session ids come from sessions.py:
       analyze.py $(python3 notes/harness/instrument/sessions.py --since-review --select attack --ids) > all.json

Logs root: by default <config dir>/projects/<project dir>, where the config
dir is $CLAUDE_CONFIG_DIR (else the standard Claude Code config dir) and the
project dir is the working directory's path with '/' replaced by '-', which
is how Claude Code names it. Override with --logs-root or $CLAUDE_LOGS_ROOT.
Written 2026-09-15 for the evaluation of the /coordinate-research loop; the
per-call buckets (harness / tooling / math / driver / git / edit / dispatch /
keepalive / poll) are classify.py's. Token usage per API request is the MAX
over that request's blocks (usage is cumulative across blocks; reading the
first block undercounts subagent output ~4x -- notes/harness/incidents.md).
"""
import json, os, sys, re, collections, datetime, glob
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from classify import classify_tool, BUCKET_NAMES, file_class, paths_in, classify_bash, CMD, kind_of

def default_root():
    cfg = os.environ.get('CLAUDE_CONFIG_DIR') or os.path.join(os.path.expanduser('~'), '.claude')
    proj = os.getcwd().replace('/', '-')
    return os.path.join(cfg, 'projects', proj)
ROOT = os.environ.get('CLAUDE_LOGS_ROOT') or default_root()
# USD per MTok: (input, cache read, 5-minute cache write, 1-hour cache write, output), from
# platform.claude.com/docs/en/about-claude/pricing as read 2026-09-17 (first /harness-review).
# Before that date every token was priced at Opus 4.1's rates (15 / 1.5 / 18.75 / 75) whatever the
# model -- notes/harness/incidents.md 2026-09-17. A model id is matched by its longest key prefix;
# an unknown model is priced as FALLBACK_MODEL and listed under session['unpriced_models'].
PRICES = {
    'claude-fable-5-1':  (10.0, 0.25, 12.5, 20.0, 50.0),
    'claude-fable-5':    (10.0, 1.0, 12.5, 20.0, 50.0),
    'claude-opus-5':     (5.0, 0.5, 6.25, 10.0, 25.0),
    'claude-opus-4-8':   (5.0, 0.5, 6.25, 10.0, 25.0),
    'claude-opus-4-7':   (5.0, 0.5, 6.25, 10.0, 25.0),
    'claude-opus-4-6':   (5.0, 0.5, 6.25, 10.0, 25.0),
    'claude-opus-4-5':   (5.0, 0.5, 6.25, 10.0, 25.0),
    'claude-sonnet-5':   (2.0, 0.2, 2.5, 4.0, 10.0),
    'claude-sonnet-4-6': (3.0, 0.3, 3.75, 6.0, 15.0),
    'claude-sonnet-4-5': (3.0, 0.3, 3.75, 6.0, 15.0),
    'claude-haiku-4-5':  (1.0, 0.1, 1.25, 2.0, 5.0),
}
FALLBACK_MODEL = 'claude-opus-5'

def rates(model):
    """(rates tuple, known?) for a model id, by longest key prefix."""
    best = None
    for k in PRICES:
        if model and model.startswith(k) and (best is None or len(k) > len(best)): best = k
    return (PRICES[best], True) if best else (PRICES[FALLBACK_MODEL], False)

def ts(s):
    if not s: return None
    return datetime.datetime.fromisoformat(s.replace('Z','+00:00'))

def words(s): return len(re.findall(r'\S+', s or ''))

def load(path):
    for line in open(path, errors='replace'):
        line=line.strip()
        if not line: continue
        try: yield json.loads(line)
        except Exception: continue

def usage_of(d):
    u = d.get('message',{}).get('usage',{}) or {}
    return (u.get('input_tokens',0), u.get('cache_read_input_tokens',0),
            u.get('cache_creation_input_tokens',0), u.get('output_tokens',0))

def cost(i, cr, cw5, cw1, o, model=None):
    r, _ = rates(model)
    return (i*r[0] + cr*r[1] + cw5*r[2] + cw1*r[3] + o*r[4]) / 1e6

def cache_writes(u, cw_total):
    """(5-minute, 1-hour) cache-write tokens. usage.cache_creation carries the split; without
    it the total is taken as 1-hour, which is what every session of this project has used."""
    cc = u.get('cache_creation') or {}
    cw5 = cc.get('ephemeral_5m_input_tokens') or 0; cw1 = cc.get('ephemeral_1h_input_tokens') or 0
    if not (cw5 or cw1): cw1 = cw_total
    return cw5, cw1

def scan_transcript(path):
    """Normalized events.

    An assistant API turn is written as several records sharing a requestId, one per
    `apiBlockIndex`.  message.usage on each record is CUMULATIVE for the turn, so the
    turn total is the max over its blocks and a block's own cost is the increment over
    the previous block.  That increment is what we attribute to the block's tool_use /
    text / thinking content.
    """
    ev = []
    tok = dict(inp=0, cr=0, cw=0, out=0, cost=0.0)
    models = collections.Counter()
    blocks = collections.OrderedDict()   # requestId -> list of records
    users = []
    # per-session facts the attack rules make claims about, plus the session's kind
    meta = dict(compact_markers=0, stopped_by_user=0, idle_notifications=0, cmds=[], prompt=None,
                unpriced=set(), bymodel=collections.defaultdict(lambda: dict(inp=0, cr=0, cw=0, out=0, cost=0.0, requests=0)))
    for d in load(path):
        t = d.get('type')
        tstamp = ts(d.get('timestamp'))
        if any('compact' in k.lower() for k in d.keys()) or 'compact' in str(d.get('subtype', '')).lower():
            meta['compact_markers'] += 1
        if t == 'assistant':
            m = d.get('message',{})
            rid = d.get('requestId') or m.get('id')
            blocks.setdefault(rid, []).append((d.get('apiBlockIndex') or 0, d, tstamp))
        elif t == 'user':
            m = d.get('message',{}) or {}
            c = m.get('content')
            origin = (d.get('origin') or {})
            okind = origin.get('kind') if isinstance(origin,dict) else None
            text=''; has_tr=False; tr_ids=[]
            if isinstance(c,str): text=c
            else:
                for b in (c or []):
                    if b.get('type')=='tool_result':
                        has_tr=True; tr_ids.append(b.get('tool_use_id'))
                    elif b.get('type')=='text': text+=b.get('text','')
            users.append(dict(kind='user', t=tstamp, text=text, tool_result=has_tr,
                              okind=okind, tr_ids=tr_ids))
            if text and not d.get('isMeta'):
                tl = text.lower()
                if 'stopped by the user' in tl: meta['stopped_by_user'] += 1
                if 'idle_notification' in tl: meta['idle_notifications'] += 1
                for m in CMD.finditer(text): meta['cmds'].append((m.group(1).strip(), (m.group(2) or '').strip()))
                if meta['prompt'] is None and not text.lstrip().startswith('<'):
                    meta['prompt'] = text.strip()[:60].replace('\n', ' ')
    turns=[]
    for rid, recs in blocks.items():
        recs.sort(key=lambda x:x[0])
        i0,cr0,cw0,_ = usage_of(recs[0][1])
        outs=[usage_of(r[1])[3] for r in recs]
        total_out=max(outs) if outs else 0
        tok['inp']+=i0; tok['cr']+=cr0; tok['cw']+=cw0; tok['out']+=total_out
        model = recs[0][1]['message'].get('model','?')
        models[model]+=1
        cw5, cw1 = cache_writes(recs[0][1]['message'].get('usage', {}) or {}, cw0)
        c = cost(i0, cr0, cw5, cw1, total_out, model)
        tok['cost'] += c
        if not rates(model)[1]: meta['unpriced'].add(model)
        bm = meta['bymodel'][model]
        bm['inp']+=i0; bm['cr']+=cr0; bm['cw']+=cw0; bm['out']+=total_out; bm['cost']+=c; bm['requests']+=1
        T=dict(kind='assistant', t=recs[0][2], ctx=i0+cr0+cw0, out=total_out,
               txtw=0, thinkw=0, tools=[], text_out=0, think_out=0,
               model=recs[0][1]['message'].get('model'), rid=rid)
        # main-session records repeat the request total on every block while subagent
        # records carry it cumulatively, so neither is a reliable per-block cost.
        # Split the request's output tokens across its blocks by serialized length.
        items=[]
        for (bi, d, tstamp) in recs:
            for b in d['message'].get('content',[]):
                bt=b.get('type')
                if bt=='thinking': items.append(('think', len(b.get('thinking','') or ''), b, tstamp))
                elif bt=='text':   items.append(('text', len(b.get('text','') or ''), b, tstamp))
                elif bt=='tool_use':
                    items.append(('tool', len(json.dumps(b.get('input',{}) or {})), b, tstamp))
        tot=sum(x[1] for x in items) or 1
        for kind, ln, b, tstamp in items:
            share = total_out*ln/tot
            if kind=='think':
                T['thinkw']+=words(b.get('thinking','')); T['think_out']+=share
            elif kind=='text':
                T['txtw']+=words(b.get('text','')); T['text_out']+=share
            else:
                T['tools'].append((b.get('name'), b.get('input',{}) or {}, b.get('id'), share, tstamp))
        turns.append(T)
    turns.sort(key=lambda x: (x['t'] or datetime.datetime.min))
    meta['unpriced'] = sorted(meta['unpriced']); meta['bymodel'] = dict(meta['bymodel'])
    return turns, users, tok, models, meta

def human_user_turns(users):
    cnt = collections.Counter(); samples=collections.defaultdict(list)
    for e in users:
        txt = e['text'] or ''
        if e['tool_result'] and not txt.strip(): k='tool_result'
        elif 'KEEPALIVE' in txt[:400]: k='keepalive'
        elif txt.lstrip().startswith('<task-notification') or '<task-notification>' in txt[:200]: k='task-notification'
        elif '<system-reminder' in txt[:60] and len(txt)<4000: k='system-reminder'
        elif e['okind']=='human' or txt.lstrip().startswith('<command-message'): k='human'
        elif e['tool_result']: k='tool_result'
        else: k='human'
        cnt[k]+=1
        if len(samples[k])<6: samples[k].append((e['t'], txt[:120].replace('\n',' ')))
    return cnt, samples

def analyze_session(sid):
    path = os.path.join(ROOT, sid+'.jsonl')
    turns, users, tok, models, meta = scan_transcript(path)
    times=[x['t'] for x in turns if x['t']]+[u['t'] for u in users if u['t']]
    R = dict(sid=sid)
    R['label'], R['group'] = kind_of(meta['cmds'], meta['prompt'])
    R['start']=min(times); R['end']=max(times)
    R['span_h']=(R['end']-R['start']).total_seconds()/3600
    R['assistant_turns']=len(turns)
    R['user_cnt'], R['user_samples']=human_user_turns(users)
    R['models']=models; R['tok']=tok
    R['cost']=tok['cost']; R['bymodel']=meta['bymodel']; R['unpriced_models']=meta['unpriced']
    R['peak_ctx']=max((e['ctx'] for e in turns), default=0)
    # compaction: a record carrying a compact marker, or the context falling by more than 40%
    # from above 50k between consecutive requests (no marker has been seen in this project yet)
    drops=0; prev=None
    for e in turns:
        if e['ctx']:
            if prev and prev>50000 and e['ctx']<0.6*prev: drops+=1
            prev=e['ctx']
    R['compactions']=dict(markers=meta['compact_markers'], ctx_drops=drops)

    buckets=collections.Counter(); bucket_out=collections.Counter()
    calls=[]
    for e in turns:
        for (name, inp, tid, share, tstamp) in e['tools']:
            b,note = classify_tool(name, inp)
            buckets[b]+=1; bucket_out[b]+=share
            calls.append(dict(t=tstamp or e['t'], b=b, name=name, note=note, out=share, inp=inp,
                              tid=tid, ctx=e['ctx'], txtw=e['txtw'], thinkw=e['thinkw']))
    R['buckets']=buckets; R['bucket_out']=bucket_out; R['calls']=calls
    R['total_calls']=sum(buckets.values())
    R['out_no_tool']=sum(e['out'] for e in turns if not e['tools'])
    R['text_words']=sum(e['txtw'] for e in turns)
    R['text_out']=sum(e['text_out'] for e in turns)
    R['think_out']=sum(e['think_out'] for e in turns)
    R['think_words']=sum(e['thinkw'] for e in turns)

    first=None
    for i,c in enumerate(calls):
        if c['name']=='Agent': first=(i,c); break
    R['first_agent']=None
    if first:
        i,c=first; pre=calls[:i]
        preb=collections.Counter(x['b'] for x in pre)
        R['first_agent']=dict(idx=i, ctx=c['ctx'], t=c['t'], pre=len(pre), preb=preb,
                              harness=preb['a']+preb['c']+preb['f_proc'],
                              math=preb['b']+preb['d']+preb['f_math'],
                              elapsed_min=(c['t']-R['start']).total_seconds()/60)
    R['dispatches']=[dict(t=c['t'], tid=c['tid'],
                          desc=c['inp'].get('description') or c['inp'].get('name'),
                          sub=c['inp'].get('subagent_type'), model=c['inp'].get('model'),
                          prompt_w=words(c['inp'].get('prompt','')))
                     for c in calls if c['name']=='Agent']
    R['sendmessages']=len([c for c in calls if c['name']=='SendMessage'])
    # what the attack rules make claims about: reference PDFs opened, Lean read, helpers' fate
    def mentions(c, pat): return re.search(pat, json.dumps(c['inp']), re.I) is not None
    R['pdf_reads']=sum(1 for c in calls if mentions(c, r'\.pdf\b|\.refs/'))
    R['lean_reads']=sum(1 for c in calls if c['name'].startswith('mcp__lean') or mentions(c, r'\.lean\b'))
    R['helpers']=dict(spawned=len(R['dispatches']), stopped_by_user=meta['stopped_by_user'],
                      idle_notifications=meta['idle_notifications'])
    proc=sum(buckets[b] for b in ('a','c','e','f_proc','h','j')); math=sum(buckets[b] for b in ('b','d','f_math'))
    R['shares']=dict(process=proc, math=math, other=R['total_calls']-proc-math)
    R['crons']=[dict(t=c['t'],name=c['name']) for c in calls if c['name'] in ('CronCreate','CronDelete')]

    # last Agent return = timestamp of the user record carrying the last Agent tool_use_id
    R['last_agent_return']=None   # filled in by caller from subagent end times
    R['commits']=[dict(t=c['t'], cmd=c['inp'].get('command','')[:400])
                  for c in calls if c['name']=='Bash'
                  and re.search(r'git\b[^\n]{0,400}?\bcommit\b', c['inp'].get('command',''))]

    seq=sorted([(x['t'],'A') for x in turns if x['t']]+[(u['t'],'U') for u in users if u['t']])
    gaps=[]
    for (t1,_),(t2,_) in zip(seq,seq[1:]):
        g=(t2-t1).total_seconds()/60
        if g>20: gaps.append((t1,t2,g))
    R['gaps']=gaps
    R['turns_meta']=[dict(t=x['t'], out=x['out'], txtw=x['txtw'], thinkw=x['thinkw'],
                          text_out=x['text_out'], think_out=x['think_out'],
                          ntools=len(x['tools'])) for x in turns]
    return R

def subagent_files(sid):
    d=os.path.join(ROOT, sid, 'subagents')
    out=[]
    if not os.path.isdir(d): return out
    for mp in sorted(glob.glob(os.path.join(d,'*.meta.json'))):
        meta=json.load(open(mp))
        jp=mp.replace('.meta.json','.jsonl')
        if os.path.exists(jp): out.append((jp, meta))
    return out

def analyze_direction(path, meta):
    turns, users, tok, models, meta = scan_transcript(path)
    times=[x['t'] for x in turns if x['t']]+[u['t'] for u in users if u['t']]
    if not times: return None
    calls=[]
    for e in turns:
        for (name,inp,tid,share,tstamp) in e['tools']:
            b,note=classify_tool(name,inp)
            calls.append(dict(t=tstamp or e['t'],b=b,name=name,note=note,out=share,inp=inp))
    first20=collections.Counter(x['b'] for x in calls[:20])
    # final return message = trailing assistant turns with no tool calls
    # 'return' output = terminal text-only turns (last turn, or followed by a >120s gap:
    # an agent that was resumed via SendMessage emits one such verdict per episode)
    ret_out=0
    for k,e in enumerate(turns):
        if e['tools']: continue
        nxt = turns[k+1]['t'] if k+1 < len(turns) else None
        if nxt is None or (e['t'] and (nxt-e['t']).total_seconds()>120):
            ret_out+=e['out']
    draft_out=sum(c['out'] for c in calls if c['b'] in ('f_math','f_proc'))
    think_out=sum(e['think_out'] for e in turns); text_out=sum(e['text_out'] for e in turns)
    peak=max((e['ctx'] for e in turns), default=0)
    return dict(path=os.path.basename(path), desc=meta.get('description'),
                sub=meta.get('agentType'), model=meta.get('model'),
                start=min(times), end=max(times),
                wall_min=(max(times)-min(times)).total_seconds()/60,
                turns=len(turns), calls=len(calls), peak_ctx=peak,
                tok=tok, cost=tok['cost'],
                buckets=collections.Counter(x['b'] for x in calls), first20=first20,
                f20_harness=first20['a']+first20['c']+first20['f_proc'],
                f20_math=first20['b']+first20['d']+first20['f_math'],
                ret_out=ret_out, draft_out=draft_out, think_out=think_out, text_out=text_out,
                mid_out=max(0, tok['out']-ret_out-draft_out), models=models)

def post_landing(R):
    """Everything the coordinator did AFTER the last direction return."""
    anchor=R.get('last_agent_return')
    if anchor is None: return None
    b=collections.Counter(); out=0
    proc_w=0; math_w=0; commit_w=0
    reason_w=0; think_w=0
    ncalls=0
    for c in R['calls']:
        if not c['t'] or c['t']<anchor: continue
        ncalls+=1; b[c['b']]+=1; out+=c['out']
        cmd=c['inp'].get('command','') if c['name']=='Bash' else json.dumps(c['inp'])
        w=words(cmd)
        if c['b']=='f_proc': proc_w+=w
        elif c['b']=='f_math': math_w+=w
        elif c['b']=='e' and 'commit' in cmd: commit_w+=w
    for t in R['turns_meta']:
        if t['t'] and t['t']>=anchor:
            reason_w+=t['txtw']; think_w+=t['thinkw']
    span=(R['end']-anchor).total_seconds()/60
    return dict(anchor=anchor, span_min=span, ncalls=ncalls, buckets=b, out=out,
                proc_words=proc_w, math_words=math_w, commit_words=commit_w,
                text_words=reason_w, thinking_words=think_w)

def landing_episodes(R, subs):
    """For each direction return (subagent end time), the coordinator work up to the
    git commit that lands it: bookkeeping words vs mathematical verification."""
    commits=[c for c in R['calls'] if c['name']=='Bash' and re.search(r'git\b[^\n]{0,400}?\bcommit\b', c['inp'].get('command',''))]
    eps=[]
    ends=sorted(datetime.datetime.fromisoformat(str(s['end'])) if isinstance(s['end'],str) else s['end'] for s in subs)
    for st in ends:
        nxt=[c for c in commits if c['t'] and c['t']>st]
        if not nxt: continue
        end=nxt[0]['t']
        win=[c for c in R['calls'] if c['t'] and st<=c['t']<=end]
        b=collections.Counter(x['b'] for x in win)
        proc_w=math_w=commit_w=0
        for c in win:
            cmd=c['inp'].get('command','') if c['name']=='Bash' else json.dumps(c['inp'])
            w=words(cmd)
            if c['b']=='f_proc': proc_w+=w
            elif c['b']=='f_math': math_w+=w
            elif c['b']=='e' and 'commit' in cmd: commit_w+=w
        txt=sum(t['txtw'] for t in R['turns_meta'] if t['t'] and st<=t['t']<=end)
        thk=sum(t['thinkw'] for t in R['turns_meta'] if t['t'] and st<=t['t']<=end)
        out=sum(c['out'] for c in win)
        eps.append(dict(start=st, end=end, min=(end-st).total_seconds()/60, n=len(win),
                        buckets=b, proc_words=proc_w, math_words=math_w,
                        commit_words=commit_w, text_words=txt, thinking_words=thk, out=out))
    return eps

if __name__=='__main__':
    args = sys.argv[1:]
    if args[:1] == ['--logs-root']:
        ROOT = args[1]; args = args[2:]
    for sid in args:
        R=analyze_session(sid)
        subs=[analyze_direction(p,m) for p,m in subagent_files(sid)]
        subs=[s for s in subs if s]
        if subs: R['last_agent_return']=max(s['end'] for s in subs)
        pl=post_landing(R)
        eps=landing_episodes(R, subs) if subs else []
        out=dict(session=R, subs=subs, post_landing=pl, episodes=eps)
        print(json.dumps(out, default=str))
