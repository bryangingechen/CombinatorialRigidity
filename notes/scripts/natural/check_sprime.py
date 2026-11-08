#!/usr/bin/env python3
"""Fresh read of Theorem S' (Phase 43a): check S' in its usable-level form,
and the sharper sub-claims of the proof sketch, on graph6 input.

Reuses the recon's validated deficiency code (shortrows.analyse / defD /
merged), read-only. Per class-C member (rows 1-5 fail) it checks:
  SP   : a chain with k>=3; or k=2, ends apart, def2(V1;a,b)+2<=def2(V1)
         (two-orbit); or k=1 with def3(V1;a,b) = def3(V1) (open-ear-one,
         usable form); or an additive core.
  P1s  : each k=2 chain, ends apart, two-orbit failing, has a rigid Z in V1
         holding a and b (|Z|>=3, def3(G[Z])=0) and a core avoiding x1.
  Q1   : k=2 chains with adjacent ends at def3(G)=0: which exits exist.
  RIG  : def3(G)=0 members: core or usable open-ear-one (or k>=3/two-orbit).

Written by the S' fresh reader of 2026-11-07 (`notes/Phase43a.md`, its item); banked in
Phase 43a with this paragraph, the harness bootstrap and the sibling import of `shortrows`
in place of a path argument, otherwise as run. Its invocations, populations and caps are
`notes/scripts/README.md` section 3, `natural/`:

  geng ... | python3 notes/scripts/natural/check_sprime.py
  python3 notes/scripts/natural/check_sprime.py --hub NAMES MAXK < /dev/null
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
import shortrows as S  # noqa: E402  -- the sibling driver, from the script's own directory

def rigid_sets_in(n, edges, V1, a, b):
    """closures inside V1 holding a and b with def_6 = 0 (min-degree-2 sets
    are unions of branches, so closures suffice)."""
    nb = S.nbrs_of(n, edges)
    br = S.chains_of(n, nb)
    V1 = set(V1)
    out = []
    for mask in range(1, 1 << len(br)):
        W = set()
        for i, (u, xs, w) in enumerate(br):
            if mask >> i & 1:
                W.add(u); W.add(w); W.update(xs)
        if not W <= V1 or a not in W or b not in W:
            continue
        iw = S.induced(edges, W)
        if S.defD(sorted(W), iw, 6) == 0:
            out.append(frozenset(W))
    return out

def main():
    tot = sp_fail = p1_cnt = p1_fail = q1_cnt = rig_cnt = rig_fail = 0
    q1_exits = {}
    fails = []
    def source():
        if len(sys.argv) > 1 and sys.argv[1] == '--hub':
            maxk = int(sys.argv[3])
            for name in sys.argv[2].split(','):
                pop, raw = S.hub_population(name, maxk)
                print(f'hub {name} maxk {maxk}: {raw} labelled simple patterns, {len(pop)} up to iso')
                for n, edges, ks in pop:
                    yield f'{name}{ks}', n, edges
        else:
            for line in sys.stdin:
                if not line.strip() or line.startswith('>'):
                    continue
                n, edges = S.parse_g6(line)
                yield line.strip(), n, edges
    for line, n, edges in source():
        r = S.analyse(n, edges)
        if r is None:
            continue
        tot += 1
        ch = r['chains']
        long_ = any(c['k'] >= 3 for c in ch)
        orbit = any(c['k'] == 2 and not c['adj'] and c['m2V1'] + 2 <= c['d2V1'] for c in ch)
        one_u = any(c['k'] == 1 and c['m3V1'] == c['d3V1'] for c in ch)
        core = bool(r['cores'])
        if not (long_ or orbit or one_u or core):
            sp_fail += 1
            fails.append(line)
        for c in ch:
            if c['k'] == 2 and not c['adj'] and not (c['m2V1'] + 2 <= c['d2V1']):
                p1_cnt += 1
                V1 = [v for v in range(n) if v not in c['xs']]
                Zs = [Z for Z in rigid_sets_in(n, edges, V1, c['a'], c['b']) if len(Z) >= 3]
                cav = [W for W in r['cores'] if c['xs'][0] not in W]
                if not Zs or not cav:
                    p1_fail += 1
                    fails.append('P1 ' + line)
            if c['k'] == 2 and c['adj'] and r['d3'] == 0:
                q1_cnt += 1
                key = (('long',) if long_ else ()) + (('orbit',) if orbit else ()) + \
                      (('one_u',) if one_u else ()) + (('core',) if core else ())
                q1_exits[key] = q1_exits.get(key, 0) + 1
        if r['d3'] == 0:
            rig_cnt += 1
            if not (core or one_u or long_ or orbit):
                rig_fail += 1
    print(f'class C members: {tot}')
    print(f'SP (usable-level S\') fails: {sp_fail}')
    print(f'P1 chains (k=2, ends apart, two-orbit fails): {p1_cnt}; without rigid Z>=3 in V1 or core avoiding x1: {p1_fail}')
    print(f'Q1 chains (k=2, adjacent ends, def3(G)=0): {q1_cnt}; exits available at their graphs: {q1_exits}')
    print(f'def3(G)=0 members: {rig_cnt}; with no core/open-ear-one(usable)/k>=3/two-orbit: {rig_fail}')
    for f in fails[:10]:
        print('  FAIL', f)

main()
