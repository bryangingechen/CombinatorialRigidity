#!/usr/bin/env python3
"""Print analyze.py's output.

    python3 notes/harness/instrument/report.py --attack all.json   # one row per session: the /harness-review table
    python3 notes/harness/instrument/report.py all.json            # the coordinator-era long report (dispatches, episodes)

The --attack table (2026-09-17) carries what the harness rules make claims about: process vs
mathematics shares of tool calls (process = read harness docs, run tooling, git, edit status
surfaces, crons, polling; math = read corpus, run drivers, edit math prose), output split into
thinking, compactions (marker records + context drops), peak context, reference PDFs opened,
Lean read, helpers spawned / stopped by the user / idle notifications, commits, gaps > 20 min,
and cost at per-model rates (analyze.PRICES).
"""
import json, sys, collections, datetime
from classify import BUCKET_NAMES

def _dt(s):
    return datetime.datetime.fromisoformat(str(s)) if s else None

def attack_table(path):
    rows = [json.loads(l) for l in open(path) if l.strip()]
    hdr = (f"{'session':8} {'kind':13} {'start (local)':16} {'h':>5} {'req':>4} {'calls':>5} "
           f"{'proc%':>5} {'math%':>5} {'out_k':>6} {'thk%':>4} {'cost$':>6} {'cmp':>3} {'peak_k':>6} "
           f"{'pdf':>3} {'lean':>4} {'help':>4} {'stop':>4} {'idle':>4} {'cmt':>3} {'gap':>3}")
    print(hdr); print('-' * len(hdr))
    T = collections.Counter(); bym = collections.defaultdict(lambda: collections.Counter()); unpriced = set()
    for o in rows:
        R = o['session']; sh = R['shares']; tot = max(1, R['total_calls'])
        st = _dt(R['start']).astimezone(); cmp_ = R['compactions']; h = R['helpers']
        thk = 100 * R['think_out'] / max(1, R['tok']['out'])
        print(f"{R['sid'][:8]:8} {R['label'][:13]:13} {st:%m-%d %H:%M}       {R['span_h']:5.2f} {R['assistant_turns']:4d} {R['total_calls']:5d} "
              f"{100*sh['process']/tot:5.0f} {100*sh['math']/tot:5.0f} {R['tok']['out']/1000:6.0f} {thk:4.0f} {R['cost']:6.2f} "
              f"{cmp_['markers']+cmp_['ctx_drops']:3d} {R['peak_ctx']/1000:6.0f} "
              f"{R['pdf_reads']:3d} {R['lean_reads']:4d} {h['spawned']:4d} {h['stopped_by_user']:4d} {h['idle_notifications']:4d} "
              f"{len(R.get('commits', [])):3d} {len(R['gaps']):3d}")
        for k in ('span_h', 'assistant_turns', 'total_calls', 'cost', 'pdf_reads', 'lean_reads'): T[k] += R[k]
        T['process'] += sh['process']; T['math'] += sh['math']; T['out'] += R['tok']['out']; T['think'] += R['think_out']
        T['cmp'] += cmp_['markers'] + cmp_['ctx_drops']; T['spawned'] += h['spawned']; T['stopped'] += h['stopped_by_user']; T['idle'] += h['idle_notifications']
        T['commits'] += len(R.get('commits', [])); T['gaps'] += len(R['gaps'])
        for m, v in R['bymodel'].items():
            for k in ('inp', 'cr', 'cw', 'out', 'cost', 'requests'): bym[m][k] += v[k]
        unpriced.update(R.get('unpriced_models', []))
    tot = max(1, T['total_calls'])
    print('-' * len(hdr))
    print(f"{'TOTAL':8} {len(rows):>3d} sessions{'':13} {T['span_h']:5.2f} {T['assistant_turns']:4d} {T['total_calls']:5d} "
          f"{100*T['process']/tot:5.0f} {100*T['math']/tot:5.0f} {T['out']/1000:6.0f} {100*T['think']/max(1,T['out']):4.0f} {T['cost']:6.2f} "
          f"{T['cmp']:3d} {'':6} {T['pdf_reads']:3d} {T['lean_reads']:4d} {T['spawned']:4d} {T['stopped']:4d} {T['idle']:4d} {T['commits']:3d} {T['gaps']:3d}")
    print("\nby model (requests, input, cache-read, cache-write, output tokens; cost at analyze.PRICES):")
    for m, v in sorted(bym.items(), key=lambda kv: -kv[1]['cost']):
        print(f"  {m:<20} {v['requests']:5d} req  in {v['inp']:>8,}  cr {v['cr']:>12,}  cw {v['cw']:>10,}  out {v['out']:>10,}  ${v['cost']:.2f}")
    if unpriced:
        print(f"\nWARNING: priced at the fallback rate (no PRICES entry): {', '.join(sorted(unpriced))}")
    print("\ncolumns: proc%/math% = share of tool calls; out_k = output tokens (k), thk% = thinking share of output; "
          "cmp = compactions (markers + context drops >40%); peak_k = peak context (k); pdf/lean = calls touching reference PDFs / Lean; "
          "help/stop/idle = helper agents spawned / 'stopped by the user' messages / idle notifications; cmt = git commits; gap = gaps >20 min")

def coordinator_report(path):
    for line in open(path):
        o=json.loads(line); R=o['session']; subs=o['subs']
        print('='*90)
        print('SESSION', R['sid'], R.get('label',''))
        print(' span %s -> %s  = %.2f h' % (R['start'][:19], R['end'][:19], R['span_h']))
        print(' assistant turns %d ; total tool calls %d' % (R['assistant_turns'], R['total_calls']))
        print(' user records:', dict(R['user_cnt']))
        for k,v in R['user_samples'].items():
            if k in ('human','keepalive'):
                for t,s in v: print('    [%s] %s | %s' % (k, t[:19] if t else '?', s))
        print(' models:', dict(R['models']))
        print(' tokens:', R['tok'], ' cost $%.2f' % R['cost'])
        fa=R['first_agent']
        if fa:
            print(' FIRST AGENT DISPATCH: after %d tool calls, %.1f min in, ctx=%d tok' % (fa['pre'], fa['elapsed_min'], fa['ctx']))
            print('   pre-dispatch buckets:', dict(fa['preb']), ' harness=%d math=%d' % (fa['harness'], fa['math']))
        tot=R['total_calls']
        print(' BUCKETS:')
        for b in ['a','b','c','d','e','f_math','f_proc','g','h','j','i']:
            n=R['buckets'].get(b,0); ot=R['bucket_out'].get(b,0)
            if n or ot: print('   %-6s %-34s %4d (%5.1f%%)  out~%8d' % (b, BUCKET_NAMES[b], n, 100*n/tot, ot))
        print('   assistant prose out: %d ; thinking out: %d' % (R['text_out'], R['think_out']))
        print(' dispatches (%d):' % len(R['dispatches']))
        for d in R['dispatches']: print('   ', d['t'][:19], d['sub'], d['model'], '|', d['desc'], '| prompt %d words' % d['prompt_w'])
        print(' SendMessage: %s ; crons: %d ; assistant text words %d ; thinking words %d' % (R['sendmessages'], len(R['crons']), R['text_words'], R['think_words']))
        print(' git commits made: %d' % len(R.get('commits',[])))
        print(' GAPS >20min: %d' % len(R['gaps']))
        for g in R['gaps']: print('    %s -> %s  %.0f min' % (g[0][:19], g[1][:19], g[2]))
        pl=o['post_landing']
        if pl:
            print(' POST-LANDING (after last direction return %s, %.0f min, %d calls, out~%d):' % (pl['anchor'][:19], pl['span_min'], pl['ncalls'], pl['out']))
            print('   buckets:', dict(pl['buckets']))
            print('   words written: process-surface edits %d | math prose edits %d | commit msgs %d | assistant prose %d | thinking %d' % (
                pl['proc_words'], pl['math_words'], pl['commit_words'], pl['text_words'], pl['thinking_words']))
        print(' DIRECTIONS (%d):' % len(subs))
        for s in subs:
            print('  - %-28s %-24s wall %6.1f min turns %3d calls %3d peakctx %7d cost $%.2f' % (
                (s['desc'] or '')[:28], s['sub'], s['wall_min'], s['turns'], s['calls'], s['peak_ctx'], s['cost']))
            print('      first20: harness=%d math=%d  %s' % (s['f20_harness'], s['f20_math'], dict(s['first20'])))
            print('      buckets: %s' % dict(s['buckets']))
            print('      out: total %d | return %d (%.0f%%) | draft-writes %d (%.0f%%) | intermediate %d (%.0f%%)' % (
                s['tok']['out'], s['ret_out'], 100*s['ret_out']/max(1,s['tok']['out']),
                s['draft_out'], 100*s['draft_out']/max(1,s['tok']['out']),
                s['mid_out'], 100*s['mid_out']/max(1,s['tok']['out'])))
        eps=o.get('episodes') or []
        if eps:
            print(' LANDING EPISODES (direction return -> its git commit): %d' % len(eps))
            tp=tm=tc=tt=th=0; tn=0; tmin=0; tb=collections.Counter()
            for e in eps:
                print('   %.0f min, %d calls, out~%d | bookkeeping words: proc-edits %d + commit-msg %d ; math words: math-edits %d ; prose %d thinking %d' % (
                    e['min'], e['n'], e['out'], e['proc_words'], e['commit_words'], e['math_words'], e['text_words'], e['thinking_words']))
                print('      buckets %s' % dict(e['buckets']))
                tp+=e['proc_words']; tm+=e['math_words']; tc+=e['commit_words']; tt+=e['text_words']; th+=e['thinking_words']; tn+=e['n']; tmin+=e['min']
                tb.update(e['buckets'])
            print('   TOTAL across episodes: %.0f min, %d calls, buckets %s' % (tmin, tn, dict(tb)))
            print('   TOTAL words: process-surface+commit-msg bookkeeping %d | math-prose %d | prose %d | thinking %d' % (tp+tc, tm, tt, th))
        if subs:
            st={k:sum(s['tok'][k] for s in subs) for k in ('inp','cr','cw','out')}
            sc=sum(s['cost'] for s in subs)
            print(' SUBAGENT TOTAL tokens:', st, ' cost $%.2f' % sc)
            print(' COORD+SUB cost: $%.2f' % (R['cost']+sc))

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if a != '--attack']
    if not args: sys.exit(__doc__)
    (attack_table if '--attack' in sys.argv else coordinator_report)(args[0])
