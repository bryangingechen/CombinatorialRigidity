#!/usr/bin/env python3
"""BINSERT (arc ordinal 82) — does KT's ROUTE B escape where route A fails?

The question this driver decides, and it is one link of option B's chain
(`notes/Pencil-strategy.md` §8.4, the *option B for `hbareSplit`* row):

  Probe KBARE-FALSIFY refuted **(K-bare-ext)** at tier T1 (§(K-bare-ext)
  (BE-5)): at the option-C C2 cube-skeleton index-2 danger gadget's
  KT-faithful hub-end split there are legal target-rank bare pencil
  realizations of `G'` from which **no placement of `v`** attains
  `target(G)` -- cap-free, all six `2x2` minors of `M` vanishing
  IDENTICALLY on the panel.

  That statement quantifies over placements of `v` ONLY, i.e. over KT's
  `M_2` alone -- what §(K-tight) *Step 1* calls **route A**.  KT's own
  Claim 6.12 (p. 690) needs *at least one* of `M_1`, `M_2`, `M_3` to have
  full rank, and the carrier kills only `M_1` (Step 1's table): **route B**
  (`M_3`, via the isomorphism `rho : G^{vc}_a = G^{ab}_v`, KT (6.44)) and
  the strictly larger joint sweep both survive it.  Nothing in the record
  tests route B at the (BE-5) hit seeds.

  So: at those seeds, does route B attain?

Why route B is IN SCOPE for `hbareSplit`, off the Lean statement rather
than off prose (`Molecule/Pencil/Escape.lean:351`, read this pass):
`hbareSplit`'s antecedents carry `G.TwoEdgeConnected` and
`hsafe : not G.PencilHub a or not G.PencilHub b`, and
`Graph.PencilHub G w := w in V(G) and 3 <= G.degree w`
(`Molecule/Pencil/Motive.lean:73`).  Under 2-edge-connectivity every vertex
has degree >= 2, so `not PencilHub w <-> deg w = 2` and `hsafe` DELIVERS an
adjacent degree-2 pair `(v, a)` -- exactly KT Lemma 6.10's own hypothesis.
Route B is therefore available to a prover of `hbareSplit`, not an extra
assumption.

Route B, implemented as route A at the OTHER end of the chain.  With `v`
degree 2 (neighbours `a`, `b`) and `a` degree 2 (neighbours `v`, `c`):

    G'_A = G - v + {a,b}        G'_B = G - a + {v,c}
    rho : G'_B -> G'_A,   v |-> a,  identity elsewhere

`rho` is an isomorphism of edge sets (both equal
`shared + {ab} + {ac}` after relabelling), so a seed `ptp` of `G'_A`
pulls back to `ptp_B[v] := ptp[a]`, `ptp_B[w] := ptp[w]` otherwise -- and
that pullback IS Step 1's *"pt(v) := old pt(a), new pt(a) sweeps
Pihat(c)"*.  Hence route B = `breakhunt`'s own route-A machinery run on
`split_ctx(G, a)` with the pulled-back seed, and every cap-free device
(`uniform_failure_exact`, `need_rank`, `hub_domain`, `pairing_rank`)
applies verbatim.  No new mathematics is introduced by this driver; it
re-points landed devices at the other end of the chain.

Modes:
  `routeb`  the decision: routes A and B at the same seeds, cap-free, at
            the Q3 index-2 hub-end split (the (BE-5) hit) and at DZ's two
            splits (the corank-2 control).
  `strata`  the per-index target-compatibility of the `cycleflat` (local
            flat) stratum -- the datum that stratifies the refutation and
            which (BE-8)'s four-stratum table does not carry.
  `combined` THE MECHANISM: the pairing of `U` against KT's own
            carrier-surviving escape span `Lambda^2 Pihat(b) +
            Lambda^2 Pihat(c)`, at the hit seeds and at non-hit target-rank
            controls.  The dichotomy is total -- `dim 5, rank 4, attains` at
            every control against `dim 3, rank 1, uniform failure` at every
            hit -- and `dim 3` means the two chain-end hub PANELS COINCIDE
            (two distinct planes' `Lambda^2`s span `3+3-1 = 5`).  Both KT
            routes, and the joint sweep, sweep inside that one plane.

Harness debt (recorded, NOT paid -- a dispatch does not move a landed
name, `notes/scripts/README.md` *Harness debt*): this is a further `w4/`
consumer of the standing UNPAID `kbare/` sibling-import item that probe
KBARE-FALSIFY created and direction BATTAIN extended as its first
cross-stack consumer.  It imports `breakhunt` (split_ctx, seed_calculus,
uniform_failure_exact, uniform_failure, need_rank, hub_domain,
pairing_rank, certify_uniform, observed, q3_gadget, sample_pencil_bfs,
BATTERY) and `danger.dz_gadget`.  No new hazard item: `bimage` is not
imported at all, so `pt_in`'s silent `K^4` truncation and `span`'s
width-6 special case are unreachable rather than merely avoided; every
`lambda2_plane` return is asserted non-`None`.

Reproduce:  python3 notes/scripts/w4/binsert.py routeb    (343 s)
            python3 notes/scripts/w4/binsert.py strata    ( 68 s)
            python3 notes/scripts/w4/binsert.py combined  ( 80 s)
"""

import random, sys, time
from fractions import Fraction as F

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import (degrees, neighbors, verts_of, hat,  # noqa: E402
                          rank_exact, build_rigidity, verify_pencil_witness,
                          dot, nullspace)
from breakhunt import (split_ctx, seed_calculus, uniform_failure_exact,  # noqa: E402
                       uniform_failure, need_rank, hub_domain, pairing_rank,
                       certify_uniform, observed, q3_gadget,
                       sample_pencil_bfs, BATTERY)
from danger import dz_gadget                       # noqa: E402  (sibling; debt)
from repin import lambda2_plane, star_generic      # noqa: E402


# --------------------------------------------------------------- route B ----

def chain_partner(edges, v):
    """The adjacent degree-2 body `a` of KT Lemma 6.10 and its far neighbour
    `c`, or None.  `hsafe` + 2-edge-connectivity guarantee one exists at any
    `hbareSplit` instance (see the module docstring); this returns it so the
    driver can ASSERT that rather than assume it."""
    deg, nb = degrees(edges), neighbors(edges)
    assert deg[v] == 2, f'{v} is not a degree-2 body'
    for a in sorted(nb[v], key=str):
        if deg[a] != 2:
            continue
        c = [w for w in nb[a] if w != v]
        assert len(c) == 1, f'degree-2 {a} has {len(c)} far neighbours'
        return a, c[0]
    return None


def panel_l2(ctx, ptp, h, rng):
    """A basis of `Lambda^2 Pihat(h)` at hub `h` from the seed `ptp`, built
    the way `hub_domain`/`pairing_rank` build the split end's: the panel is
    the nullspace of `h`'s own point together with its `G`-neighbours' points
    other than the inserted vertex.  Returns None on a degenerate draw (the
    caller asserts)."""
    nb = neighbors(ctx['G'])
    anchors = [hat(ptp[h])] + [hat(ptp[w]) for w in sorted(nb[h], key=str)
                               if w != ctx['v'] and w in ptp]
    ns = nullspace(anchors)
    if not ns or all(ns[0][i] == 0 for i in range(3)):
        return None
    return lambda2_plane(ptp[h], ns[0][:3], rng)


def rho_pullback(ctx_a, ptp, v, a):
    """Transport a `G'_A` seed to `G'_B` along `rho : v |-> a`.

    `ptp` is a point map on `V(G) \\ {v}`; the result is a point map on
    `V(G) \\ {a}` with `pt(v) := ptp[a]`.  Asserted to be a legal pencil
    witness of `G'_B` at the SAME exact rank, which is the content of `rho`
    being an isomorphism -- if either assert fires, the pullback (not the
    mathematics) is wrong."""
    out = {w: ptp[w] for w in ptp if w != a}
    out[v] = ptp[a]
    assert set(out) == set(verts_of(ctx_a['Gp'])), (
        'rho pullback has the wrong support')
    ok, _ = verify_pencil_witness(ctx_a['Gp'], out)
    assert ok, 'rho pullback is not a legal G_B pencil witness'
    return out


def verdict(ctx, ptp, sd, tag, seed, nplace=8):
    """The cap-free uniform-failure verdict for one route at one seed, with
    the grid test asserted equal to it (breakhunt's own contract) and the
    pairing rank against the hub end's `Lambda^2 Pihat` recorded."""
    try:
        dom = hub_domain(ctx, ptp)
    except RuntimeError:
        return {'tag': tag, 'skip': 'degenerate hub placement panel'}
    rng = random.Random(seed)
    ufx, why = uniform_failure_exact(ctx, ptp, sd, domain=dom,
                                     rng=random.Random(seed))
    uf, wit = uniform_failure(ctx, ptp, sd, domain=dom,
                              rng=random.Random(seed))
    assert uf == ufx, f'grid vs exact disagree at {tag}/{seed}: {uf} {ufx}'
    out = {'tag': tag, 'uniform_fail': ufx, 'why': why,
           's0': sd['s0'], 'dimRa': sd['dimRa'], 'dimU': sd['dimU'],
           'need': need_rank(ctx, sd),
           'pairing_rank': pairing_rank(ctx, ptp, sd, dom, rng)}
    if ufx:
        out['obs'] = certify_uniform(ctx, ptp, dom, seed, nplace=nplace)
    elif wit is not None:
        okw, rk = observed(ctx, ptp, wit)
        out['witness_rank'] = rk if okw else None
        out['target'] = ctx['tG']
        assert not okw or rk == ctx['tG'], (
            f'criterion says attain at {tag}, observed {rk} vs {ctx["tG"]}')
    return out


def run_routeb(nseeds=10, seed0=52000):
    """THE DECISION.  At every seed of the (BE-5) hit battery, run route A
    (the control -- must reproduce uniform failure) and route B."""
    print('===== BINSERT: does KT ROUTE B escape where route A fails? =====')
    print('  (BE-5) refuted (K-bare-ext) by exhibiting uniform failure of')
    print('  ROUTE A -- placements of `v` -- at 8 legal target-rank seeds.')
    print('  KT Claim 6.12 (p. 690) needs only ONE of M1/M2/M3 to have full')
    print('  rank; the carrier kills M1 alone (§(K-tight) Step 1), so route')
    print('  B (M3, via rho, KT (6.44)) survives and was never tested here.')
    print('  Seeds, batteries and seed0 are (BE-5)\'s own, so route A is a')
    print('  REPRODUCTION and route B is the new measurement.')

    cases = [('Q3 index-2 hub-end', q3_gadget(), None, (0, 0)),
             ('DZ non-hub-ends', dz_gadget(), 'u1h2_2', (0, 0)),
             ('DZ hub-end', dz_gadget(), 'u1h2_1', (0, 0))]
    summary = []
    for name, edges, vfix, defs in cases:
        deg, nb = degrees(edges), neighbors(edges)
        if vfix is None:
            v = next(x for x in verts_of(edges) if deg[x] == 2
                     and any(deg[w] == 2 for w in nb[x])
                     and any(deg[w] >= 3 for w in nb[x]))
        else:
            v = vfix
        ctxA = split_ctx(edges, v, defs=defs)
        part = chain_partner(edges, v)
        print(f'\n  {name}: v={v} index={ctxA["index"]} def(G)={ctxA["dG"]} '
              f'corank(G\')={ctxA["cGp"]} target(G)={ctxA["tG"]}')
        if part is None:
            print('    ROUTE B UNAVAILABLE: no adjacent degree-2 body.  Under '
                  '2EC this cannot happen at an hsafe instance -- report it.')
            continue
        a, c = part
        print(f'    KT chain: b={[x for x in nb[v] if x != a][0]} -- v={v} -- '
              f'a={a} (deg {deg[a]}) -- c={c} (deg {deg[c]}, '
              f'{"HUB" if deg[c] >= 3 else "non-hub"})')
        ctxB = split_ctx(edges, a, defs=(ctxA['dG'], ctxA['dGp']))
        assert ctxB['tG'] == ctxA['tG'], 'the two splits disagree on target(G)'
        # (INS-2)'s edge-set identity, ASSERTED rather than argued: applying
        # `rho` (v |-> a) to `E(G'_B)` must reproduce `E(G'_A)` exactly.  This
        # replaces an `... or True` assert that could not fire (correction 2 at
        # the landing; §4 convention 1's "a guard that passes vacuously is not
        # a guard", one level down).
        def _rho(e):
            return tuple(sorted((a if x == v else x for x in e), key=str))
        assert {_rho(e) for e in ctxB['Gp']} == \
            {tuple(sorted(e, key=str)) for e in ctxA['Gp']}, \
            'rho is not an edge-set isomorphism G_B -> G_A'
        nA = nB = both = 0
        for degen in BATTERY:
            for s in range(nseeds):
                rng = random.Random(seed0 + s)
                try:
                    ptp, _ = sample_pencil_bfs(ctxA['Gp'], rng, degen=degen)
                except (AssertionError, RuntimeError):
                    continue
                sdA = seed_calculus(ctxA, ptp)
                if sdA is None or not sdA['at_target']:
                    continue
                vA = verdict(ctxA, ptp, sdA, 'A', seed0 + s)
                if 'skip' in vA or not vA['uniform_fail']:
                    continue          # not a hit seed: nothing to ask route B
                nA += 1
                # --- the new measurement: route B at the SAME seed ---
                try:
                    ptpB = rho_pullback(ctxB, ptp, v, a)
                except AssertionError as e:
                    print(f'    seed {s}/{degen}: rho pullback REJECTED ({e})')
                    continue
                rkA = rank_exact(build_rigidity(ctxA['Gp'], ptp)[0])
                rkB = rank_exact(build_rigidity(ctxB['Gp'], ptpB)[0])
                assert rkA == rkB, (f'rho is not rank-preserving: '
                                    f'{rkA} vs {rkB}')
                sdB = seed_calculus(ctxB, ptpB)
                if sdB is None:
                    print(f'    seed {s}/{degen}: route-B seed illegal')
                    continue
                if not sdB['at_target']:
                    print(f'    seed {s}/{degen}: route-B seed OFF '
                          f"target(G'_B) ({sdB['rkGp']} vs {ctxB['tGp']})")
                    continue
                vB = verdict(ctxB, ptpB, sdB, 'B', seed0 + s)
                if 'skip' in vB:
                    print(f'    seed {s}/{degen}: route B {vB["skip"]}')
                    continue
                if vB['uniform_fail']:
                    nB += 1
                    both += 1
                mark = ('FAILS TOO' if vB['uniform_fail'] else '*** ESCAPES')
                print(f'    seed {s:>2}/{str(degen):9s}: '
                      f'A uniform-FAIL (s0={vA["s0"]} dimRa={vA["dimRa"]} '
                      f'dimU={vA["dimU"]} need={vA["need"]} '
                      f'pairA={vA["pairing_rank"]}) | '
                      f'B {mark} (s0={vB["s0"]} dimRa={vB["dimRa"]} '
                      f'dimU={vB["dimU"]} need={vB["need"]} '
                      f'pairB={vB["pairing_rank"]})'
                      + ('' if vB['uniform_fail'] else
                         f' -> attains {vB.get("witness_rank")} '
                         f'/ {vB.get("target")}'))
        print(f'    >>> {name}: route-A uniform-failure seeds {nA}; '
              f'of those, route B ALSO fails at {nB}, ESCAPES at {nA - nB}')
        summary.append((name, nA, nB))

    print('\n  >>> VERDICT')
    for name, nA, nB in summary:
        if nA == 0:
            print(f'      {name}: no route-A hit seed under this cap — '
                  f'nothing to decide here')
        elif nB == nA:
            print(f'      {name}: route B fails at ALL {nA} route-A hit '
                  f'seeds — the COMBINED A-or-B insertion statement is '
                  f'refuted too')
        else:
            print(f'      {name}: route B ESCAPES at {nA - nB} of {nA} '
                  f'route-A hit seeds — the combined statement SURVIVES '
                  f'(K-bare-ext)\'s refutation at those seeds')
    print('  CAP: seeds are (BE-5)\'s battery (6 strata x %d seeds); a route-B'
          % nseeds)
    print('  escape at an UNTESTED seed is not excluded.  "Not found under')
    print('  cap", never "does not exist".')
    return summary


def run_strata(nseeds=10, seed0=52000):
    """The per-index target-compatibility of the local-flat (`cycleflat`)
    stratum -- the stratum that carries the (BE-5) hit.  §(K-bare-ext)
    (BE-8)'s four-stratum table omits this row, and it is the row at which
    the corank-2 and corank-3 gadgets DIVERGE."""
    print('===== BINSERT: the local-flat stratum, per index =====')
    print('  (BE-8) tabulates four strata x two gadgets and does NOT carry')
    print('  the `cycleflat` (local flat) row -- the one the (BE-5) hit lives')
    print('  on.  This mode supplies it, which is what stratifies the')
    print('  refutation by corank.')
    cases = [('DZ non-hub-ends (index 1, corank(G\')=2)', dz_gadget(),
              'u1h2_2', (0, 0)),
             ('DZ hub-end (index 1, corank(G\')=2)', dz_gadget(),
              'u1h2_1', (0, 0))]
    eq3 = q3_gadget()
    deg, nb = degrees(eq3), neighbors(eq3)
    vq = next(x for x in verts_of(eq3) if deg[x] == 2
              and any(deg[w] == 2 for w in nb[x])
              and any(deg[w] >= 3 for w in nb[x]))
    cases.append(('Q3 hub-end (index 2, corank(G\')=3)', eq3, vq, (0, 0)))
    print(f'\n  {"case":42s} {"legal":>6s} {"AT target(G\')":>14s} '
          f'{"uniform-fail":>13s}')
    rows = []
    for name, edges, v, defs in cases:
        ctx = split_ctx(edges, v, defs=defs)
        nlegal = nat = nuf = 0
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctx['Gp'], rng, degen='cycleflat')
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctx, ptp)
            if sd is None:
                continue
            nlegal += 1
            if not sd['at_target']:
                continue
            nat += 1
            v_ = verdict(ctx, ptp, sd, 'A', seed0 + s)
            if 'skip' not in v_ and v_['uniform_fail']:
                nuf += 1
        print(f'  {name:42s} {nlegal:>6d} {nat:>14d} {nuf:>13d}')
        rows.append((name, nlegal, nat, nuf))
    print('\n  >>> READING.  The local-flat stratum is target-COMPATIBLE only')
    print('      where `AT target(G\')` > 0.  Where it is 0 the stratum is')
    print('      excluded by (K-bare-ext)\'s OWN target-rank antecedent, so')
    print('      the refutation cannot reach that index at all.')
    return rows


def run_combined(nseeds=10, seed0=52000):
    """How DEEP the hit seeds' degeneracy goes: the rank of the pairing of
    `U` against KT's own carrier-surviving escape span.

    KT Claim 6.12 (p. 691) shows the span (6.45)
    `Lambda^2 Pihat(a) + Lambda^2 Pihat(b) + Lambda^2 Pihat(c)` is
    6-dimensional at a generic nonparallel seed, forcing `r = 0` and hence
    escape.  The carrier deletes the `Pihat(a)` summand (M1 is dead,
    §(K-tight) Step 1), leaving `Lambda^2 Pihat(b) + Lambda^2 Pihat(c)` --
    5-dimensional -- and §(K-tight) *Step 2.5* reads uniform failure of BOTH
    routes as `r ⊥` that sum, at `dim R_a = 1`.

    At `dim R_a = 3` the analogue is `rank <U, Lambda^2 Pihat(b) +
    Lambda^2 Pihat(c)>`, and `>= 2` is what defeats uniform failure.  This
    mode measures it.  It matters for the ONE surviving repair of the
    insertion statement -- Step 1's *"NEW, not in KT"* joint sweep
    `(pt v, pt a) in Pihat(b) x Pihat(c)`, which is un-analyzed and whose
    escape space is built from these SAME two panels."""
    print('===== BINSERT: how deep is the hit seeds\' degeneracy? =====')
    print('  KT (6.45) is 6-dim at a generic nonparallel seed (Claim 6.12,')
    print('  p. 691).  The carrier keeps 5 of those 6 dimensions (§(K-tight)')
    print('  Step 2.6).  This measures the pairing of `U` against that')
    print('  5-dim carrier-surviving span at the (BE-5) hit seeds.')
    edges = q3_gadget()
    deg, nb = degrees(edges), neighbors(edges)
    v = next(x for x in verts_of(edges) if deg[x] == 2
             and any(deg[w] == 2 for w in nb[x])
             and any(deg[w] >= 3 for w in nb[x]))
    ctx = split_ctx(edges, v, defs=(0, 0))
    a, c = chain_partner(edges, v)
    b = [x for x in nb[v] if x != a][0]
    print(f'\n  Q3 index-2 hub-end: chain b={b} -- v={v} -- a={a} -- c={c}')
    print(f'  panels: Pihat({b}) hub={deg[b] >= 3}, Pihat({c}) '
          f'hub={deg[c] >= 3}')
    rows = []
    for s in range(nseeds):
        rng = random.Random(seed0 + s)
        try:
            ptp, _ = sample_pencil_bfs(ctx['Gp'], rng, degen='cycleflat')
        except (AssertionError, RuntimeError):
            continue
        sd = seed_calculus(ctx, ptp)
        if sd is None or not sd['at_target']:
            continue
        vv = verdict(ctx, ptp, sd, 'A', seed0 + s)
        if 'skip' in vv or not vv['uniform_fail']:
            continue
        r = random.Random(seed0 + s)
        Lb = panel_l2(ctx, ptp, b, r)
        Lc = panel_l2(ctx, ptp, c, r)
        assert Lb is not None and Lc is not None, (
            f'seed {s}: a panel basis came back None -- degenerate draw')
        assert rank_exact(Lb) == 3 and rank_exact(Lc) == 3, (
            f'seed {s}: a Lambda^2 panel is not 3-dimensional')
        dim_sum = rank_exact(list(Lb) + list(Lc))
        pb = rank_exact([[dot(u, l) for l in Lb] for u in sd['U']])
        pc = rank_exact([[dot(u, l) for l in Lc] for u in sd['U']])
        psum = rank_exact([[dot(u, l) for l in list(Lb) + list(Lc)]
                           for u in sd['U']])
        print(f'    seed {s:>2}: dim(L2Pi_b + L2Pi_c) = {dim_sum} '
              f'(KT: 6 at a generic seed, 5 on the carrier) | '
              f'rank<U,L2Pi_b> = {pb}  rank<U,L2Pi_c> = {pc}  '
              f'rank<U, SUM> = {psum}   (>= 2 would defeat uniform failure)')
        rows.append((s, dim_sum, pb, pc, psum))
    # --- the control: the SAME measurement at non-hit target-rank seeds, so
    # the panel collapse is a CHARACTERIZATION and not a correlation. ---
    print('\n  control — the same measurement at target-rank seeds of the')
    print('  robust-generic and global-hub-coplanar strata (NO route-A hit):')
    ctrl = []
    for degen in (None, 'hubplane'):
        for s in range(nseeds):
            rng = random.Random(seed0 + s)
            try:
                ptp, _ = sample_pencil_bfs(ctx['Gp'], rng, degen=degen)
            except (AssertionError, RuntimeError):
                continue
            sd = seed_calculus(ctx, ptp)
            if sd is None or not sd['at_target']:
                continue
            vv = verdict(ctx, ptp, sd, 'A', seed0 + s)
            if 'skip' in vv:
                continue
            r = random.Random(seed0 + s)
            Lb, Lc = panel_l2(ctx, ptp, b, r), panel_l2(ctx, ptp, c, r)
            if Lb is None or Lc is None:
                continue
            assert rank_exact(Lb) == 3 and rank_exact(Lc) == 3, (
                'a Lambda^2 panel is not 3-dimensional at a control seed')
            ctrl.append((degen, s, rank_exact(list(Lb) + list(Lc)),
                         rank_exact([[dot(u, l) for l in list(Lb) + list(Lc)]
                                     for u in sd['U']]),
                         vv['uniform_fail']))
    for degen, s, dsum, psum, uf in ctrl:
        print(f'    {str(degen):9s} seed {s:>2}: '
              f'dim(L2Pi_b + L2Pi_c) = {dsum}  rank<U, SUM> = {psum}  '
              f'uniform-fail = {uf}')
    if ctrl:
        print(f'    >>> control: dim(sum) in '
              f'{sorted({c[2] for c in ctrl})}, rank<U,sum> in '
              f'{sorted({c[3] for c in ctrl})}, uniform-fail in '
              f'{sorted({c[4] for c in ctrl})}')
    if rows:
        sums = sorted({r[4] for r in rows})
        print(f'\n  >>> rank<U, L2Pi_b + L2Pi_c> over {len(rows)} hit seeds: '
              f'{sums}')
        if sums == [1]:
            print('      ONE at every hit seed.  So the degeneracy is not')
            print('      per-route: `U` pairs to rank 1 against the WHOLE')
            print('      carrier-surviving escape span, which is exactly the')
            print('      locus KT Claim 6.12 proves empty at a generic')
            print('      nonparallel seed.  Any repair -- the joint sweep')
            print('      included -- must supply genericity these seeds')
            print('      provably cannot have (`hbareSplit`\'s antecedent is')
            print('      `not PencilNondegFeasible`).')
    else:
        print('  no hit seed reached under this cap')
    return rows


MODES = {'routeb': run_routeb, 'strata': run_strata,
         'combined': run_combined}

if __name__ == '__main__':
    args = sys.argv[1:] or ['all']
    todo = list(MODES) if args == ['all'] else args
    for m in todo:
        if m not in MODES:
            raise SystemExit(f'unknown mode {m!r}; modes: {", ".join(MODES)}')
        t0 = time.time()
        MODES[m]()
        print(f'\n[binsert {m}: {time.time() - t0:.0f}s]\n')
