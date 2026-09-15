import json,sys,collections
from classify import BUCKET_NAMES
for line in open(sys.argv[1]):
    o=json.loads(line); R=o['session']; subs=o['subs']
    print('='*90)
    print('SESSION', R['sid'])
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
