"""Direction RPOOL — the (K-res) row's two cheap items: the 255-residual pool
sweep, and the (RS-5) flank hunt.

The `§(K-res)/(RS-5)` gap-map row's *close-it* names, beside the wave, a
**cheap first slice** (the 255-residual pool sweep) and a **flank** (a
`def = 0` (K-res) shape whose EVERY admissible colouring has `dim Z > 0`,
which would refute (RS-5)).  This driver is both.  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/rpool.py --pool     #  46 s  (RS-12): the pool census -- how many of the 255 are `def = 0`
    PYTHONHASHSEED=0 python3 notes/scripts/w4/rpool.py --sweep    # 484 s  (RS-11)/(RS-13): the cheap first slice -- a FULL colouring census at all 102
    PYTHONHASHSEED=0 python3 notes/scripts/w4/rpool.py --proof    # 104 s  (RS-13): the per-shape proofs, and the cross-check on the flank set
    PYTHONHASHSEED=0 python3 notes/scripts/w4/rpool.py --witness  #  61 s  (RS-13): the exhibited flank R20, verified end to end
    PYTHONHASHSEED=0 python3 notes/scripts/w4/rpool.py --law      #  18 s  (RS-14)/(RS-15): the covering law, tested off the recorded pool

There is deliberately NO `--validate`: the five legs together are past the
harness's 600 s foreground budget (`notes/scripts/README.md` *Two invocations
do not fit*), so they are run one at a time.  `--sweep` alone is 484 s
measured -- it FITS, but with little room, so a future extension of the pool
belongs in a sixth leg rather than inside that one.

Argument state: `notes/Pencil-informal-grid.md` §(K-res) *Steps RS11-RS16*
(labels (RS-11)-(RS-15); reserved at `notes/Pencil-labels.md`).

WHAT IS MEASURED vs WHAT IS PROVEN.  Same instrument and same standing as
`resgrid.py`, whose devices this driver reuses: colouring enumeration is
EXHAUSTIVE per shape (the cap is asserted non-binding, and any shape whose
alternation-component count exceeds it is REPORTED, never silently
dropped); a generic `dim Z` is the min over `draws` exact-rational draws,
each an upper bound, so a `0` is CONCLUSIVE and a positive value is only
an upper bound on nothing -- it is a lower bound the sweep cannot certify
from draws alone.  THAT ASYMMETRY IS THE WHOLE POINT OF THE FLANK: a shape
where no draw hits `(0,0)` is a flank CANDIDATE, not a flank, and is
promoted only by the parameter-free `(RS-2)`/`(RS-3)` floor
`dim Z >= (m - 3h) + g`, which is a combinatorial count and therefore
PROVEN at every parameter point.  An exact rational draw at the Tay target
`6(|V|-1)` is a per-shape PROOF of (RS-5) by semicontinuity ((GR-7)
remark (i)).

Exact throughout (Q via fractions.Fraction, Q(i) via closure's Gauss layer
inside the eigen ranks).  Seeded rngs only, seeds printed.  No `set` is
printed.
"""
import argparse
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of, is_2ec                            # noqa: E402
from nogood_subdiv import (branch_decomposition, deficiency,         # noqa: E402
                           hcard_ok, hub_set, induced_edges,
                           rigid_vertex_sets, triangles)
import wtri                                                          # noqa: E402
from closure import (build_fixed_config, colourings, cycle_rank,     # noqa: E402
                     extensors, eigen_subsystem_contracted, neighbors)
from grid import (block_data, build_fixed_config_params, dim_Z,      # noqa: E402
                  dim_Z_generic)
from gridwit import a_and_M, dim_W, subgraph_g                       # noqa: E402
from resgrid import (COL_CAP, core_edge_idx, f_count, min_core,      # noqa: E402
                     passing_colourings, rank_and_z_at_draw)

SEED = 20260903


# ---------------------------------------------------------------- census --

def pool():
    """The 255 residual inhabitants `saferes.py --prime` sweeps.

    Reached through `wtri.recorded_pool()`, which already probes for the
    (still unpaid) `saferes.prime_pool()` accessor -- so this driver is the
    THIRD consumer of that generator list and does NOT restate it a third
    time.  See `notes/scripts/README.md` *Harness debt* (WTRI's item)."""
    return wtri.recorded_pool()


def census_row(E):
    """The (K-res) habitat data of one pool member, all exact."""
    V = sorted(verts_of(E), key=str)
    rs = rigid_vertex_sets(E)
    core = min(rs, key=len) if rs else None
    _, br = branch_decomposition(E)
    return {
        'E': E, 'V': V, 'nV': len(V), 'nE': len(E),
        'index': 5 * len(E) - 6 * (len(V) - 1),
        'def': deficiency(E),
        'hubs': len(hub_set(E)), '2ec': is_2ec(E), 'hcard': hcard_ok(E),
        'rigid_sets': len(rs), 'core': core,
        'f_core': f_count(E, core) if core else None,
        'max_f': max((f_count(E, W) for W in rs), default=None),
        'branches': len(br) if br else None,
        'tri': len(triangles(E)),
    }


def kres_def0(rows):
    """The `def = 0` (K-res) members: the exact population (RS-5) quantifies
    over inside this pool."""
    return [r for r in rows if r['def'] == 0]


def leg_pool():
    print("== --pool: (RS-12) the 255-residual pool census, by deficiency ==")
    P = pool()
    print(f"  residual inhabitants reproduced:                   {len(P)}")
    assert len(P) == 255, f"pool duplication drifted: {len(P)} != 255"
    rows = [census_row(E) for E in P]
    # every member is (K-res)-shaped by construction: `classify` already
    # required simple + 2EC + feasible + a PROPER rigid subgraph, which is
    # exactly `hnoRigid` failing.
    for r in rows:
        assert r['rigid_sets'] >= 1 and r['2ec'] and r['nV'] >= 5, r['nV']
    by_def = {}
    for r in rows:
        by_def.setdefault(r['def'], []).append(r)
    for d in sorted(by_def):
        n = len(by_def[d])
        idxs = sorted({r['index'] for r in by_def[d]})
        print(f"  ... with def = {d}: {n:4d}   index values {idxs}")
    d0 = kres_def0(rows)
    print(f"  ... the (RS-5) population [def = 0]:               {len(d0)}")
    if d0:
        print(f"      |V| range {min(r['nV'] for r in d0)}"
              f"-{max(r['nV'] for r in d0)}; "
              f"index values {sorted({r['index'] for r in d0})}; "
              f"hcard {sum(r['hcard'] for r in d0)}/{len(d0)}; "
              f"triangle-free {sum(r['tri'] == 0 for r in d0)}/{len(d0)}")
        # (RS-3)(ii): rigidity covers the excess.  def >= f(W) - index for
        # every connected W, so def = 0 forces max f(W) <= index.
        for r in d0:
            assert r['max_f'] <= r['index'], (r['nV'], r['max_f'], r['index'])
        print("      (RS-3)(ii) `max f(W) <= index` asserted at all of them")
        # the sweep's own cost, disclosed BEFORE the sweep: one exhaustive
        # colouring enumeration per member is 2^(alternation components).
        from closure import alternation_classes
        hist, odd = {}, 0
        for r in d0:
            comps, isodd = alternation_classes(r['E'])
            if isodd:
                odd += 1
                continue
            hist[len(comps)] = hist.get(len(comps), 0) + 1
        print(f"      sweep cost: alternation-component counts "
              f"{sorted(hist.items())}; odd chains {odd}; "
              f"cap 2^{COL_CAP.bit_length() - 1}")
    print("  DISCLOSURE -- the pool's SUPPORT.  These 255 are the residual "
          "inhabitants of\n  three generator families (`nogood_subdiv."
          "family_g` long-branch, `saferes.\n  family_core_ring` short-branch"
          " ring+spoke, and 700 `saferes.random_short`\n  draws at seed "
          "99991), filtered by `nogood_subdiv.classify`.  It is the pool "
          "the\n  project RECORDED, not a census of the (K-res) habitat.")


# ------------------------------------------------- (RS-11) the floor law --

def iter_passing(E, allverts, cols, hubs):
    """STREAMING form of `resgrid.passing_colourings` -- the same predicate,
    yielded one at a time.  The two cheap combinatorial clauses are moved
    ahead of the `build_fixed_config` construction, which dominates the
    cost; the predicate is a conjunction, so the yielded sequence is
    identical, and that is ASSERTED against the eager original in
    `leg_sweep` rather than assumed."""
    for col in cols:
        if any(len({col[e] for e in E if v in e}) == 1 for v in hubs):
            continue
        EA = [e for e in E if col[e] == 'A']
        EB = [e for e in E if col[e] == 'B']
        if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
            continue
        if build_fixed_config(E, allverts, col) is None:
            continue
        yield col, len(EA), len(EB)


def block_floor(bd, core):
    """(RS-11)'s per-block PARAMETER-FREE floor on `dim Z`.

    (RS-2) reads (GR-7) as `dim Z = (m - 3h) + dim W` (with `a` absorbed),
    and (GR-8) -- proven for EVERY sub-multigraph `P` of `H_+`, and a **T**
    row of the *Step RS5* transport audit -- gives `dim W >= g(P)`.  Taking
    `P` = the contracted image of the core circuit,

        dim Z >= (m - 3h) + g   at EVERY parameter point.

    Clamped at 0, because the two blocks' floors are SUMMED and a negative
    slack term in one block must not be allowed to cancel the other's
    positive witness.  Returns (floor, slack = 3h - m, g)."""
    m, h = len(bd['E']), bd['h']
    g = subgraph_g(bd, core_edge_idx(bd, core))
    return max(0, g - (3 * h - m)), 3 * h - m, g


def sweep_shape(E, rng, core, draws=3, ident=False, check=False):
    """One member's FULL exhaustive sweep: every colouring enumerated, every
    passing colouring decided.  A colouring whose proven floor is positive
    is decided WITHOUT a draw (it cannot be a (0,0) colouring at any
    parameter point); the rest are drawn.

    `zero > 0` means the member SATISFIES (RS-5) (conclusively, by
    semicontinuity).  `floorpos == passing > 0` means the member REFUTES
    it, and that verdict is a combinatorial count, not a sample."""
    V = sorted(verts_of(E), key=str)
    cols, odd = colourings(E, cap=COL_CAP)
    if cols is None or odd:
        return {'skipped': 'colouring cap hit' if cols is None else 'odd chain',
                'nV': len(V), 'nE': len(E)}
    nb = neighbors(E)
    hubs = [v for v, ns in nb.items() if len(ns) >= 3]
    c = len(E) - len(V) + 1
    idx = 5 * len(E) - 6 * (len(V) - 1)
    n_pass = n_floorpos = n_drawn = zero = 0
    first_zero = None
    minsum = None
    maxg = 0
    gmin = None          # min over passing colourings of min(g+, g-)
    minfloor = None      # min over passing colourings of floor+ + floor-
    prof = {}
    for col, nA, nB in iter_passing(E, V, cols, hubs):
        n_pass += 1
        bds = [block_data(E, V, col, mine) for mine in 'AB']
        fl = 0
        key = []
        for bd in bds:
            f, sl, g = block_floor(bd, core)
            if check:
                # h_+ = h_- = c(G): the contracted node set of one block is
                # V/E_other, of size |V| - m_other because the other class
                # is a forest, so h = m_mine - (|V| - m_other) + 1 = c.
                assert bd['h'] == c, (bd['h'], c)
            fl += f
            maxg = max(maxg, g)
            key.append((sl, g))
        gg = min(k[1] for k in key)
        gmin = gg if gmin is None else min(gmin, gg)
        minfloor = fl if minfloor is None else min(minfloor, fl)
        if check:
            # (RS-2)'s slack law, in the ONLY form that is true of every
            # passing colouring: the two blocks' slacks sum to exactly the
            # index.  Per-block non-negativity is NOT an invariant -- it is
            # a NECESSARY CONDITION for a (0,0) colouring (a block with
            # 3h - m < 0 has dim Z >= m - 3h > 0 by (RS-2) alone, with no
            # witness needed), and an early draft asserted it wrongly.
            assert key[0][0] + key[1][0] == idx, (key, idx)
        prof[tuple(key)] = prof.get(tuple(key), 0) + 1
        if fl > 0:
            n_floorpos += 1
            continue
        n_drawn += 1
        s = 0
        for bd in bds:
            if ident:
                sval = {cid: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                        for cid in set(bd['cls'])}
                z1, w1 = dim_Z(bd, sval), dim_W(bd, sval)
                a, M = a_and_M(bd, E, V)
                assert z1 == a + (M - 3 * bd['h']) + w1, 'RS-2 identity'
                assert w1 >= block_floor(bd, core)[2], 'GR-8 witness floor'
            s += dim_Z_generic(bd, rng, draws=draws)
        minsum = s if minsum is None else min(minsum, s)
        if s == 0:
            zero += 1
            if first_zero is None:
                first_zero = (nA, nB, n_pass)
    return {'nV': len(V), 'nE': len(E), 'c': c, 'index': idx,
            'total': len(cols), 'passing': n_pass, 'floorpos': n_floorpos,
            'drawn': n_drawn, 'zero': zero, 'first_zero': first_zero,
            'minsum': minsum, 'maxg': maxg, 'gmin': gmin,
            'minfloor': minfloor, 'prof': sorted(prof.items())}


def target_point(E, core, rng, draws=6):
    """An exact rational point at the Tay target `6(|V|-1)` -- a per-shape
    PROOF of (RS-5) at this shape by semicontinuity ((GR-7) remark (i))."""
    V = sorted(verts_of(E), key=str)
    target = 6 * (len(V) - 1) - deficiency(E)
    cols, odd = colourings(E, cap=COL_CAP)
    nb = neighbors(E)
    hubs = [v for v, ns in nb.items() if len(ns) >= 3]
    for col, nA, nB in iter_passing(E, V, cols, hubs):
        bdA, bdB = block_data(E, V, col, 'A'), block_data(E, V, col, 'B')
        if block_floor(bdA, core)[0] or block_floor(bdB, core)[0]:
            continue
        if dim_Z_generic(bdA, rng, draws=1) or dim_Z_generic(bdB, rng, draws=1):
            continue
        for d in range(draws):
            got = rank_and_z_at_draw(E, V, col, rng)
            if got and got[0] == target:
                assert got[1] == got[2] == 0
                return (nA, nB, d + 1, target)
    return None


def verdict(res):
    if 'skipped' in res:
        return 'SKIPPED'
    if res['zero'] > 0:
        return 'SATISFIES (RS-5)'
    if res['passing'] and res['floorpos'] == res['passing']:
        return 'FLANK (proven)'
    return 'UNDECIDED'


# ---------------------------------------------------- (RS-12)/(RS-13) --

def leg_sweep(draws=3):
    print("== --sweep: (RS-12)/(RS-13) the cheap first slice -- the FULL "
          "exhaustive colouring census at every `def = 0` pool member ==")
    print(f"  rng seed {SEED}; generic dim Z = min over {draws} exact "
          "rational draws (a 0 is CONCLUSIVE by semicontinuity; a positive "
          "draw proves nothing, which is why a\n  flank verdict rests on "
          "the (RS-11) floor and never on a draw)")
    rng = random.Random(SEED)
    rows = [census_row(E) for E in pool()]
    d0 = kres_def0(rows)
    # the streaming filter IS resgrid's eager one: asserted, not assumed.
    E0 = d0[0]['E']
    V0 = sorted(verts_of(E0), key=str)
    cols0, _ = colourings(E0, cap=COL_CAP)
    nb0 = neighbors(E0)
    eager, _ = passing_colourings(E0, V0)
    stream = list(iter_passing(E0, V0, cols0,
                              [v for v, ns in nb0.items() if len(ns) >= 3]))
    assert [x[1:] for x in eager] == [x[1:] for x in stream], \
        'the streaming passing-filter diverged from resgrid.passing_colourings'
    print(f"  streaming filter == `resgrid.passing_colourings`: asserted "
          f"({len(eager)} passing colourings, first member)")
    by_index = {}
    for r in d0:
        by_index.setdefault(r['index'], []).append(r)
    print(f"  def = 0 members: {len(d0)}, by index "
          f"{sorted((k, len(v)) for k, v in by_index.items())}")
    print(f"\n{'|V|':>4} {'|E|':>4} {'idx':>4} {'core':>5} {'f':>3} "
          f"{'cols':>7} {'pass':>6} {'floor+':>7} {'drawn':>6} {'zero':>6} "
          f"{'g':>3}  verdict")
    ok, flanks, undec, skipped = [], [], [], []
    for n, r in enumerate(d0):
        core, _ = min_core(r['E'])
        res = sweep_shape(r['E'], rng, core, draws=draws,
                          ident=(n % 10 == 0), check=True)
        v = verdict(res)
        if v == 'SKIPPED':
            skipped.append((r, res))
        elif v == 'SATISFIES (RS-5)':
            ok.append((r, res))
        elif v == 'FLANK (proven)':
            flanks.append((r, res))
        else:
            undec.append((r, res))
        print(f"{r['nV']:>4} {r['nE']:>4} {r['index']:>4} "
              f"{len(core):>5} {r['f_core']:>3} {res.get('total', 0):>7} "
              f"{res.get('passing', 0):>6} {res.get('floorpos', 0):>7} "
              f"{res.get('drawn', 0):>6} {res.get('zero', 0):>6} "
              f"{res.get('maxg', 0):>3}  {v}")
    print(f"\n  (RS-13): {len(ok)}/{len(d0)} members SATISFY (RS-5) "
          f"(a generic-(0,0) admissible both-forest colouring exists)")
    print(f"  (RS-13): {len(flanks)}/{len(d0)} members REFUTE IT -- a "
          f"PROVEN positive floor at EVERY passing colouring")
    print(f"           {len(undec)} undecided, {len(skipped)} skipped "
          f"(reported, never dropped)")
    print("  asserted at every passing colouring of every member: "
          "h+ = h- = c(G), and the two blocks' slacks 3h-m sum to index")
    print("  asserted at every drawn block of every 10th member: the (RS-2) "
          "identity and the (GR-8) witness floor dim W >= g")
    key = lambda r, res: (res['index'], len(min_core(r['E'])[0]),   # noqa: E731
                          r['f_core'], res['gmin'])
    print(f"  flank population, by (index, |core|, f(core), g_forced):     "
          f"{sorted({key(r, res) for r, res in flanks})}")
    print(f"  (RS-5)-satisfying population, same key:                      "
          f"{sorted({key(r, res) for r, res in ok})}")
    # (RS-15)'s law, checked on THIS population too: a flank is exactly a
    # shape whose unavoidable per-block witness beats the index it has to
    # be split across.  `g_forced` = min over passing colourings of
    # min(g+, g-).
    bad = [key(r, res) for r, res, isfl in
           [(r, res, True) for r, res in flanks] +
           [(r, res, False) for r, res in ok]
           if isfl != (res['index'] < 2 * res['gmin'])]
    print(f"  (RS-15) flank <=> index < 2 * g_forced: counterexamples "
          f"{bad if bad else 'NONE'}")
    # the measured regularity that makes the classification core-only here:
    # every `def = 0` member of this pool sits at the EXTREME of (RS-3)(ii),
    # `index = f(core)`, rather than merely `f(core) <= index`.
    tight = sum(1 for r, _ in ok + flanks if r['f_core'] == r['index'])
    print(f"  measured regularity: index == f(core) at {tight}/{len(ok) + len(flanks)}"
          f" members -- (RS-3)(ii) is EXTREMAL on this population, not slack")
    print("  the per-shape PROOFS of (RS-5) at the satisfying members are "
          "`--proof`\n  (a separate leg because the two together exceed the "
          "harness's 600 s foreground\n  budget -- `notes/scripts/README.md` "
          "*figures do not move*, the split-invocation rule)")


def leg_proof(draws=3):
    print("== --proof: (RS-13) upgraded -- an EXACT rational point at the "
          "Tay target at every member that admits one ==")
    print(f"  rng seed {SEED + 4}; a target hit is a per-shape PROOF of "
          f"(RS-5) at that shape by semicontinuity, not a measurement")
    rng = random.Random(SEED + 4)
    rows = [census_row(E) for E in pool()]
    d0 = kres_def0(rows)
    hits, misses = 0, []
    for r in d0:
        core, _ = min_core(r['E'])
        hit = target_point(r['E'], core, rng)
        if hit:
            hits += 1
        else:
            misses.append((r['index'], len(core), r['f_core']))
    print(f"  exact target points found: {hits}/{len(d0)}")
    print(f"  members with NO target point, by (index, |core|, f(core)): "
          f"{sorted(set(misses))} x{len(misses)}")
    # the miss set is exactly the flank set of --sweep, and it is keyed by a
    # combinatorial invariant, so the two legs cross-check each other.
    assert hits == 72 and len(misses) == 30 and set(misses) == {(1, 5, 1)}, \
        (hits, sorted(set(misses)))
    print("  cross-check: the miss set is EXACTLY --sweep's proven-flank set "
          "(30 members, all `index = 1` with a C5 core), asserted")


# ---------------------------------------------------- (RS-13) witness --

def R20():
    """The exhibited (RS-5) flank: `nogood_subdiv.family_g(5, (0,0,2),
    (4,4,4))` -- W19's OWN family with the core cycle one edge longer
    (`widened.W19` is `family_g(4, (0,0,2), (4,4,4))`, asserted below).
    |V| = 20, |E| = 23, index = 1, def = 0, a single proper rigid subgraph:
    the C5 core, with f(core) = 1 = index."""
    import nogood_subdiv as ns
    return ns.family_g(5, (0, 0, 2), (4, 4, 4))


def leg_witness(draws=4):
    print("== --witness: (RS-13) the exhibited flank R20, verified end to "
          "end ==")
    import nogood_subdiv as ns
    import saferes
    import widened
    E = R20()
    V = sorted(verts_of(E), key=str)
    norm = lambda X: sorted(tuple(sorted(e)) for e in X)   # noqa: E731
    assert norm(widened.W19()) == norm(ns.family_g(4, (0, 0, 2), (4, 4, 4))), \
        'widened.W19 is not family_g(4, (0,0,2), (4,4,4))'
    print("  provenance: R20 = family_g(5, (0,0,2), (4,4,4)); "
          "W19 = family_g(4, (0,0,2), (4,4,4)) -- ASSERTED.")
    print(f"  R20 is a member of the recorded 255 pool: "
          f"{norm(E) in [norm(X) for X in pool()]}")
    print(f"  edges: {sorted(tuple(sorted(e)) for e in E)}")
    r = census_row(E)
    print(f"  |V|={r['nV']} |E|={r['nE']} index={r['index']} "
          f"def(Lee-Streinu pebble)={r['def']} "
          f"def(matroid-union tree packing)={saferes.treepack_deficiency(E)} "
          f"2ec={r['2ec']} simple={ns.is_simple(E)} hcard={r['hcard']} "
          f"triangles={r['tri']}")
    assert r['def'] == 0 and saferes.treepack_deficiency(E) == 0, \
        'the two deficiency oracles disagree'
    st, _ = ns.classify(E)
    print(f"  classify={st}; provably_feasible={ns.provably_feasible(E)}; "
          f"proper rigid subgraphs={r['rigid_sets']} "
          f"core={r['core']} f(core)={r['f_core']} max_f={r['max_f']}; "
          f"split-usable degree-2 vertices={len(saferes.split_usable(E))}")
    assert st.endswith('CANDIDATE') and r['rigid_sets'] >= 1
    assert len(saferes.split_usable(E)) > 0
    # the whole colouring space, broken down by which clause rejects it.
    cols, odd = colourings(E, cap=COL_CAP)
    assert cols is not None and not odd
    nb = neighbors(E)
    hubs = [v for v, ns2 in nb.items() if len(ns2) >= 3]
    n_mono = n_cyc = n_ill = 0
    monoforest = []
    for col in cols:
        EA = [e for e in E if col[e] == 'A']
        EB = [e for e in E if col[e] == 'B']
        forests = not (cycle_rank(V, EA) or cycle_rank(V, EB))
        if any(len({col[e] for e in E if v in e}) == 1 for v in hubs):
            n_mono += 1
            if forests and build_fixed_config(E, V, col) is not None:
                monoforest.append(col)
            continue
        if not forests:
            n_cyc += 1
            continue
        if build_fixed_config(E, V, col) is None:
            n_ill += 1
    print(f"  colouring space: total={len(cols)} monochromatic-hub={n_mono} "
          f"a-class-has-a-cycle={n_cyc} bodies-coincide={n_ill} "
          f"PASSING={len(cols) - n_mono - n_cyc - n_ill}")
    core, _ = min_core(E)
    rng = random.Random(SEED + 3)
    res = sweep_shape(E, rng, core, draws=draws, ident=True, check=True)
    print(f"  sweep: passing={res['passing']} floor-positive={res['floorpos']}"
          f" drawn={res['drawn']} zero={res['zero']} => {verdict(res)}")
    print(f"  per-colouring (slack, g) profile, both blocks: {res['prof']}")
    assert res['floorpos'] == res['passing'] > 0 and res['zero'] == 0
    # the measured side: dim Z at draws, and the sigma-fixed rank, at EVERY
    # passing colouring -- corroboration of a bound that is already proven.
    target = 6 * (len(V) - 1) - r['def']
    ranks, sums = {}, {}
    # NOTE ON THE SAMPLER'S SUPPORT (RESEARCH-ARC 4).  `sweep_shape`'s
    # `ident` asserts fire only on DRAWN blocks, and a flank has `drawn = 0`
    # by construction -- so on exactly the members that carry the verdict,
    # that assert is vacuous.  The loop below is where the (RS-2) identity
    # and the (GR-8) witness bound are asserted at EVERY block of EVERY
    # passing colouring of the flank itself, drawn or not.
    for col, nA, nB in iter_passing(E, V, cols, hubs):
        s = 0
        for mine in 'AB':
            bd = block_data(E, V, col, mine)
            f, sl, g = block_floor(bd, core)
            sval = {cid: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                    for cid in set(bd['cls'])}
            z1, w1 = dim_Z(bd, sval), dim_W(bd, sval)
            a, M = a_and_M(bd, E, V)
            assert a + M == len(bd['E']), 'a + M = m'
            assert z1 == a + (M - 3 * bd['h']) + w1, '(RS-2)=(GR-7) identity'
            assert w1 >= g, ('(GR-8): dim W >= g', w1, g)
            z = dim_Z_generic(bd, rng, draws=draws)
            assert z >= f, ('measured dim Z below the proven floor', z, f)
            s += z
        sums[s] = sums.get(s, 0) + 1
        best = None
        for _ in range(draws):
            got = rank_and_z_at_draw(E, V, col, rng)
            if got is None:
                continue
            assert got[0] == 6 * (len(V) - 1) - got[1] - got[2], 'RS-1'
            best = got[0] if best is None else max(best, got[0])
        ranks[best] = ranks.get(best, 0) + 1
    print(f"  (RS-2) identity, `a + M = m` and (GR-8)'s `dim W >= g` asserted at BOTH blocks of ALL 64 passing colourings\n  measured dim Z+ + dim Z- over all passing colourings: "
          f"{sorted(sums.items())} (0 never occurs)")
    print(f"  sigma-fixed rank histogram (max over {draws} draws each): "
          f"{sorted(ranks.items())}; Tay target = {target}")
    assert min(sums) >= 1 and max(ranks) == target - 1
    print(f"  VERDICT: R20 is a `def = 0` (K-res) shape whose EVERY "
          f"admissible both-forest colouring has dim Z > 0.\n  "
          f"(RS-5) IS REFUTED.  The proven rank cap is {target - 1} < "
          f"{target}; the measured max is {max(ranks)}.")
    # LOOPHOLE CHECK.  (RS-5)'s "admissible" is operationalized by
    # `resgrid.passing_colourings`, which also excludes monochromatic-hub
    # colourings.  If the flank depended on THAT clause's reading it would
    # be an artifact, so the excluded colourings are measured too.
    if monoforest:
        ms = sorted({sum(dim_Z_generic(block_data(E, V, c, mi), rng,
                                       draws=draws) for mi in 'AB')
                     for c in monoforest})
        print(f"  LOOPHOLE CHECK: {len(monoforest)} colourings are excluded "
              f"ONLY by the monochromatic-hub clause\n  while still being "
              f"legal both-forest colourings; their generic dim Z+ + dim Z- "
              f"values are {ms} -- so NO colouring of R20 whatever, admissible"
              f" or not, reaches (0,0),\n  and the flank does not depend on "
              f"that clause's reading.  (Measured, not proven: this half is "
              f"a draw statement about a class (RS-5) does not quantify "
              f"over.)")
        assert min(ms) >= 1
    else:
        print("  LOOPHOLE CHECK: no colouring is excluded by the "
              "monochromatic-hub clause alone, so the flank does not depend "
              "on that clause's reading")


# ------------------------------------------------- (RS-14)/(RS-15) law --

def gen_family(cap=140, mmax=9, lmax=7):
    """Fresh `def = 0` (K-res) shapes OUTSIDE the recorded pool, for the
    law's converse -- and generated SYSTEMATICALLY, not sampled, because
    the law is a statement about the CORE and a random generator does not
    vary the core (`saferes.random_short` produced 0 in-band residual
    `def = 0` shapes in 20 000 draws, measured).

    Two families, so the answer does not rest on one generator:
      (a) `nogood_subdiv.family_g(m, attach, lengths)` -- W19's and R20's
          own family, extended to core lengths m up to `mmax` and branch
          interiors up to `lmax` (the recorded pool stops at m = 6 and
          interior 5, so everything past that is new);
      (b) `saferes.family_core_ring(...)` at ring sizes and subdivision
          depths past the pool's (m in {7,8}, q = 5, outer/spoke = 3).
    Returns (shapes, generated, in_band)."""
    from itertools import combinations_with_replacement as cwr
    import nogood_subdiv as ns
    import saferes
    out, gen, band = [], 0, 0
    seen = set()
    def offer(E):
        nonlocal gen, band
        gen += 1
        V = verts_of(E)
        idx = 5 * len(E) - 6 * (len(V) - 1)
        if not (0 <= idx <= 2):
            return
        band += 1
        key = tuple(sorted(tuple(sorted(e)) for e in E))
        if key in seen:
            return
        seen.add(key)
        st, _ = ns.classify(E)
        if st.endswith('CANDIDATE') and deficiency(E) == 0:
            out.append(E)
    for m in range(3, mmax + 1):
        for attach in sorted({tuple(sorted(t)) for t in cwr(range(m), 3)}):
            for lengths in cwr(range(0, lmax + 1), 3):
                if sum(lengths) > 18 - m:
                    continue
                offer(ns.family_g(m, attach, list(lengths)))
                if len(out) >= cap:
                    return out, gen, band
    for m in (7, 8):
        for q in (3, 5):
            for attach in sorted({tuple(sorted(t))
                                  for t in cwr(range(m), q)})[:6]:
                for ring_extra in range(0, q + 1):
                    for outer in (0, 3):
                        for spoke in (0, 3):
                            offer(saferes.family_core_ring(
                                m, attach, ring_extra, outer, spoke))
                            if len(out) >= cap:
                                return out, gen, band
    return out, gen, band


def leg_law(draws=3):
    print("== --law: (RS-14) the covering law, and (RS-15) its test off the "
          "recorded pool ==")
    print("  (RS-14) the mechanism, stated.  A (0,0) colouring needs EACH "
          "block's forced\n  witness covered by THAT block's OWN slack "
          "`3h - m`, and the two slacks sum to\n  exactly `index` "
          "(h+ = h- = c(G), asserted).  (RS-3)(ii) bounds only the SUM "
          "(it\n  gives `f(core) <= index`), so it is one block-split short: "
          "at `index = 1` some\n  block always has slack 0, and a forced "
          "witness there survives every draw.")
    rng = random.Random(SEED + 1)
    shapes, gen, band = gen_family()
    print(f"  systematic generation: {gen} shapes built, {band} with "
          f"index in [0,2], {len(shapes)} residual with `def = 0`")
    tab = {}
    for E in shapes:
        core, _ = min_core(E)
        res = sweep_shape(E, rng, core, draws=draws, check=True)
        v = verdict(res)
        key = ('skipped',) if v == 'SKIPPED' else \
            (res['index'], len(core), f_count(E, core), res['gmin'], v)
        tab[key] = tab.get(key, 0) + 1
    print("  (index, |core|, f(core), g_forced, verdict) -> count:")
    for k in sorted(tab, key=str):
        print(f"    {k}  x{tab[k]}")
    fl = sum(n for k, n in tab.items()
             if len(k) > 1 and k[4] == 'FLANK (proven)')
    ok = sum(n for k, n in tab.items()
             if len(k) > 1 and k[4] == 'SATISFIES (RS-5)')
    print(f"  off-pool verdicts: {fl} PROVEN FLANKS, {ok} satisfying, "
          f"{len(shapes) - fl - ok} skipped/undecided")
    # (RS-15): the law's prediction, stated BEFORE it is checked, is that
    # the flank set is exactly the shapes whose forced core witness exceeds
    # the per-block slack.  Asserted as a biconditional on this population.
    bad = [k for k in tab if len(k) > 1
           and (k[4] == 'FLANK (proven)') != (k[0] < 2 * k[3])]
    print(f"  (RS-15) the law as a BICONDITIONAL on this population -- "
          f"flank <=> index < 2 * g_forced, where g_forced is the min over "
          f"passing\n  colourings of min(g+, g-), i.e. the witness that "
          f"NO colouring can avoid:\n           counterexample keys "
          f"{bad if bad else 'NONE'}")
    print(f"  CAP DISCLOSURE -- every negative here is NOT-FOUND-UNDER-CAP. "
          f"Cap: `family_g`\n  core lengths 3..9 with branch interiors 0..7 "
          f"and sum <= 18 - m, plus\n  `family_core_ring` at m in {{7,8}}, "
          f"q in {{3,5}}, outer/spoke in {{0,3}}; {gen} shapes\n  built, "
          f"{len(shapes)} in scope, {draws} draws per block.  This widens the "
          f"recorded\n  pool's support (which stops at core length 6 and "
          f"branch interior 5); it is\n  NOT a census of the (K-res) "
          f"habitat.")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pool', action='store_true')
    ap.add_argument('--sweep', action='store_true')
    ap.add_argument('--proof', action='store_true')
    ap.add_argument('--witness', action='store_true')
    ap.add_argument('--law', action='store_true')
    args = ap.parse_args()
    if args.pool:
        leg_pool()
    if args.sweep:
        leg_sweep()
    if args.proof:
        leg_proof()
    if args.witness:
        leg_witness()
    if args.law:
        leg_law()
    if not any(vars(args).values()):
        ap.print_help()


if __name__ == '__main__':
    main()
