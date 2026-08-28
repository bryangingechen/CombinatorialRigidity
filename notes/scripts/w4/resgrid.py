"""Direction RESGRID — does (GR-15)/§(K-grid) transport to the (K-res) habitat?

A `w4/` leaf beside `grid.py`/`gridwit.py`/`closure.py`, importing them
READ-ONLY (README §2: a new (K)-arc driver goes BESIDE the fan-out leaves;
same import pattern as `packmm.py`/`gcap.py`/`cflank.py`).  Run from the
repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/resgrid.py --audit    # (RS-3): habitat data, rigidity-covers-excess, the (GR-18)/(GR-25) sparsity failure at the core
    PYTHONHASHSEED=0 python3 notes/scripts/w4/resgrid.py --dimz     # (RS-5) measured: the exhaustive colouring sweep, (GR-7)=(RS-2) identity asserted per block, forced core witness asserted
    PYTHONHASHSEED=0 python3 notes/scripts/w4/resgrid.py --rank     # (RS-1) asserted + (RS-5) PROVEN per shape: exact rational target-rank points
    PYTHONHASHSEED=0 python3 notes/scripts/w4/resgrid.py --theta    # (RS-6): the deficient-fringe control theta(2,3,7) — the old (AC-6) miss, now a mechanism
    PYTHONHASHSEED=0 python3 notes/scripts/w4/resgrid.py --validate # all four

Argument state: `notes/Pencil-informal-grid.md` §(K-res) (new with this
driver; labels (RS-1)-(RS-6), *Steps RS1-RS10*, reserved at
`notes/Pencil-labels.md` §"Reserved namespace — direction RESGRID").

WHAT IS MEASURED vs WHAT IS PROVEN, in one paragraph.  The (K-res) shapes
(`widened.W19`, `saferes.w29`, `dominance.nt21c3`) are NOT tight class
shapes — each carries a proper rigid subgraph (`kslidecomb.shape_ok` would
reject them by construction; that rejection is the habitat discriminator,
not a bug, so it is not called here).  The section's (RS-1) rank identity
`rank = 6(|V|-1) - dim Z₊ - dim Z₋` (at ANY legal both-forest colouring —
(GR-1) + (AC-4), no tightness) is asserted here numerically at matched
parameter draws; the (GR-7) identity `dim Z = a + (M-3h) + dim W` is
asserted at every passing colouring-block; the forced core witness (the
(GR-8) bound `g >= 1` at the contracted core cycle) is a parameter-free
combinatorial count (`gridwit.subgraph_g`), so the per-block lower bounds
it yields are PROVEN, not sampled; and a `dim Z₊ = dim Z₋ = 0` draw at an
exact rational point PROVES generic vanishing by semicontinuity ((GR-7)
remark (i)), so `--rank`'s target hits are per-shape PROOFS of (RS-5).
Colouring enumeration is EXHAUSTIVE per shape (the alternation-component
count is <= 14 everywhere here, far under the 2^20 cap, asserted); the only
sampled figures are the generic-`dim Z` draws, each an upper bound on the
generic value, with `0` draws conclusive.

Exact throughout (ℚ via fractions.Fraction, ℚ(i) via closure's Gauss layer
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
                           rigid_vertex_sets)
from pitch import theta_edges                                        # noqa: E402
import widened                                                       # noqa: E402
import saferes                                                       # noqa: E402
import dominance                                                     # noqa: E402
from closure import (build_fixed_config, colourings, cycle_rank,     # noqa: E402
                     eigen_subsystem_contracted, extensors, neighbors)
from grid import (block_data, build_fixed_config_params, dim_Z,      # noqa: E402
                  dim_Z_generic)
from gridwit import a_and_M, dim_W, subgraph_g                       # noqa: E402

SEED = 20260828
COL_CAP = 1 << 20        # never binding here (max 2^14 colourings), asserted
IDENT_CAP = 24           # rank-identity asserts per shape beyond the zero hit


def f_count(edges, W):
    """f(W) = 5|E(G[W])| - 6(|W|-1), the (6,6)-count excess."""
    return 5 * len(induced_edges(edges, W)) - 6 * (len(W) - 1)


def shapes():
    """The three named (K-res) shapes of the spec, in spec order."""
    return [('W19', widened.W19()),
            ('S29', saferes.w29()),
            ('NT21c3', dominance.nt21c3()[0])]


def min_core(edges):
    """The smallest proper rigid vertex set (the shape's core)."""
    rs = rigid_vertex_sets(edges)
    assert rs, "no proper rigid subgraph: not a (K-res) shape"
    return min(rs, key=len), rs


def passing_colourings(edges, allverts):
    """Exhaustive: admissible (proper alternation), legal (all bodies
    distinct — a parameter-free condition on the component pair), no
    monochromatic hub, both ruling classes forests.  Yields
    (col, |E_A|, |E_B|)."""
    cols, odd = colourings(edges, cap=COL_CAP)
    assert cols is not None and not odd, "colouring cap hit or odd chain"
    nb = neighbors(edges)
    hubs = [v for v, ns in nb.items() if len(ns) >= 3]
    out = []
    for col in cols:
        if build_fixed_config(edges, allverts, col) is None:
            continue
        if any(len({col[e] for e in edges if v in e}) == 1 for v in hubs):
            continue
        EA = [e for e in edges if col[e] == 'A']
        EB = [e for e in edges if col[e] == 'B']
        if cycle_rank(allverts, EA) or cycle_rank(allverts, EB):
            continue
        out.append((col, len(EA), len(EB)))
    return out, len(cols)


def core_edge_idx(bd, core):
    """Indices (in bd['E']) of this block's edges with both ends in the
    core — the contracted image of the core circuit."""
    W = set(core)
    return [k for k, e in enumerate(bd['E']) if e[0] in W and e[1] in W]


def rank_and_z_at_draw(edges, allverts, col, rng):
    """One matched parameter draw: the sigma-fixed eigen ranks AND both
    blocks' dim Z at the SAME per-class parameters, for the (RS-1) assert.
    Returns (rank, zA, zB) or None on a coincidence at this draw."""
    from closure import components as ccomp
    EA = [e for e in edges if col[e] == 'A']
    EB = [e for e in edges if col[e] == 'B']
    compA = ccomp(allverts, EA)
    compB = ccomp(allverts, EB)
    pA = {c: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
          for c in set(compA.values())}
    pB = {c: F(rng.randint(1, 10 ** 4), rng.randint(1, 97))
          for c in set(compB.values())}
    built = build_fixed_config_params(edges, allverts, col, pA, pB)
    if built is None:
        return None
    pt, _, _ = built
    ext = extensors(edges, pt)
    rP, _ = eigen_subsystem_contracted(allverts, edges, col, ext, 'P')
    rM, _ = eigen_subsystem_contracted(allverts, edges, col, ext, 'M')
    zA = dim_Z(block_data(edges, allverts, col, 'A'), sval=pA)
    zB = dim_Z(block_data(edges, allverts, col, 'B'), sval=pB)
    return rP + rM, zA, zB


# ------------------------------------------------------------------ legs --

def leg_audit():
    print("== --audit: the (K-res) habitat data, and the two structural "
          "breaks ==")
    for name, E in shapes() + [('theta(2,3,7) [control]',
                                theta_edges((2, 3, 7)))]:
        V = sorted(verts_of(E), key=str)
        idx = 5 * len(E) - 6 * (len(V) - 1)
        de = deficiency(E)
        hubs = hub_set(E)
        _, branches = branch_decomposition(E)
        rs = rigid_vertex_sets(E)
        maxf = max((f_count(E, W) for W in rs), default=None)
        core = min(rs, key=len) if rs else None
        print(f"{name}: |V|={len(V)} |E|={len(E)} index={idx} def={de} "
              f"2ec={is_2ec(E)} hcard_ok={hcard_ok(E)} hubs={len(hubs)} "
              f"branches={len(branches)} rigid_sets={len(rs)} "
              f"core={core} f(core)={f_count(E, core) if core else None} "
              f"max_f={maxf}")
        assert rs, f"{name}: hnoRigid holds — not (K-res)-shaped"
        # (RS-3)(ii) rigidity covers the excess: def >= f(W) - index for
        # every connected W, so def = 0 forces max f(W) <= index.
        assert maxf <= idx + de, (name, maxf, idx, de)
        if name.startswith(('W19', 'S29')):
            assert de == 0 and idx == 2 and maxf == 2
            # the (GR-18)(i)/(GR-25)(i) sparsity input FAILS at the core:
            # the core's two length-2 branches have sum(6-l) = 8 > 6 =
            # 6(q-1) at q = 2 hubs, i.e. f(branch set) = 2 > -1.
            inner = [(h1, h2, ins) for (h1, h2, ins) in branches
                     if {h1, h2} | set(ins) <= set(core)]
            s = sum(6 - (len(ins) + 1) for (_, _, ins) in inner)
            q = len({h for (h1, h2, _) in inner for h in (h1, h2)})
            print(f"  core branch set: sum(6-l)={s} vs 6(q-1)={6 * (q - 1)}"
                  f"  -> Nash-Williams/(GR-25)(i) input {'FAILS' if s > 6 * (q - 1) else 'holds'}")
            assert s > 6 * (q - 1), "expected the packing/sparsity break"
        if name == 'NT21c3':
            assert de == 0 and idx == 0 and maxf == 0


def leg_dimz(draws=3):
    print("== --dimz: exhaustive colouring sweep; (RS-2)=(GR-7) identity "
          "asserted per passing block; forced core witness asserted ==")
    print(f"rng seed {SEED}; generic dim Z = min over {draws} draws "
          "(each draw an upper bound; a 0 draw is conclusive)")
    rng = random.Random(SEED)
    for name, E in shapes():
        V = sorted(verts_of(E), key=str)
        core, _ = min_core(E)
        target = 6 * (len(V) - 1) - deficiency(E)
        passing, total = passing_colourings(E, V)
        zero = 0
        first_zero = None
        minsum = None
        minW = None
        for col, nA, nB in passing:
            zz = []
            for mine in 'AB':
                bd = block_data(E, V, col, mine)
                # (RS-2) = (GR-7): dim Z = a + (M - 3h) + dim W, at one
                # generic draw, exact.
                sval = {c: F(rng.randint(1, 10 ** 5), rng.randint(1, 313))
                        for c in set(bd['cls'])}
                z1 = dim_Z(bd, sval)
                w1 = dim_W(bd, sval)
                a, M = a_and_M(bd, E, V)
                assert z1 == a + (M - 3 * bd['h']) + w1, (name, mine)
                minW = w1 if minW is None else min(minW, w1)
                # the forced core witness at the C4-core shapes: the
                # contracted core cycle meets <= 2 classes, so (GR-8)
                # gives the PROVEN, parameter-free bound dim W >= g >= 1.
                if name in ('W19', 'S29'):
                    g = subgraph_g(bd, core_edge_idx(bd, core))
                    assert g >= 1, (name, mine, g)
                zz.append(dim_Z_generic(bd, rng, draws=draws))
            s = zz[0] + zz[1]
            minsum = s if minsum is None else min(minsum, s)
            if s == 0:
                zero += 1
                if first_zero is None:
                    first_zero = (col, nA, nB)
        print(f"{name}: colourings total={total} passing={len(passing)} "
              f"zero-zero={zero} min(zA+zB)={minsum} "
              f"min dim_W={minW} target={target} "
              f"first-zero split={first_zero[1:] if first_zero else None}")
        assert zero > 0, f"{name}: no dim Z = 0 colouring found"
        if name in ('W19', 'S29'):
            assert minW == 1, "expected the forced witness to be tight"


def leg_rank(draws=3):
    print("== --rank: (RS-1) rank identity asserted at matched draws; "
          "an exact rational target hit PROVES (RS-5) per shape ==")
    print(f"rng seed {SEED}; identity asserted at the first {IDENT_CAP} "
          "passing colourings per shape (disclosure: a cap on the assert "
          "count, not on the enumeration) plus the first zero colouring; "
          f"target sought over {draws} draws")
    rng = random.Random(SEED)
    for name, E in shapes():
        V = sorted(verts_of(E), key=str)
        target = 6 * (len(V) - 1) - deficiency(E)
        passing, _ = passing_colourings(E, V)
        checked = 0
        for col, nA, nB in passing[:IDENT_CAP]:
            got = rank_and_z_at_draw(E, V, col, rng)
            if got is None:
                continue
            rk, zA, zB = got
            assert rk == 6 * (len(V) - 1) - zA - zB, (name, rk, zA, zB)
            checked += 1
        # the first generic-(0,0) colouring: hunt an exact target point.
        hit = None
        for col, nA, nB in passing:
            bdA = block_data(E, V, col, 'A')
            bdB = block_data(E, V, col, 'B')
            if dim_Z_generic(bdA, rng, draws=1) or \
               dim_Z_generic(bdB, rng, draws=1):
                continue
            for d in range(draws):
                got = rank_and_z_at_draw(E, V, col, rng)
                if got and got[0] == target:
                    hit = (nA, nB, d + 1)
                    assert got[1] == got[2] == 0
                    break
            if hit:
                break
        print(f"{name}: identity asserted at {checked} colourings; "
              f"TARGET {target} ATTAINED at an exact rational point "
              f"(split {hit[:2]}, draw {hit[2]})" if hit else
              f"{name}: identity asserted at {checked}; NO target point "
              f"found under the draw cap")
        assert hit, f"{name}: no exact target point (draw cap {draws})"


def leg_theta(draws=3):
    print("== --theta: the deficient-fringe control theta(2,3,7) — the "
          "recorded (AC-6) miss is a MECHANISM: forced witness + zero "
          "slack ==")
    rng = random.Random(SEED)
    E = theta_edges((2, 3, 7))
    V = sorted(verts_of(E), key=str)
    core, _ = min_core(E)          # the rigid C5 (branches 2+3)
    de = deficiency(E)
    target = 6 * (len(V) - 1) - de
    passing, total = passing_colourings(E, V)
    maxrk = None
    for col, nA, nB in passing:
        for mine in 'AB':
            bd = block_data(E, V, col, mine)
            g = subgraph_g(bd, core_edge_idx(bd, core))
            m, h = len(bd['E']), bd['h']
            # PROVEN: dim Z >= (m - 3h) + g at every parameter point;
            # here m = 3h (index 0) and g >= 1, so dim Z >= 1 per block
            # and rank <= 6(|V|-1) - 2 = target - 1 by (RS-1).
            assert m == 3 * h and g >= 1, (mine, m, h, g)
        for _ in range(draws):
            got = rank_and_z_at_draw(E, V, col, rng)
            if got is None:
                continue
            rk, zA, zB = got
            assert rk == 6 * (len(V) - 1) - zA - zB
            assert zA >= 1 and zB >= 1, "the proven floor was violated"
            maxrk = rk if maxrk is None else max(maxrk, rk)
    print(f"theta(2,3,7): |V|={len(V)} |E|={len(E)} def={de} "
          f"target={target}; colourings total={total} "
          f"passing={len(passing)} (exhaustive); PROVEN rank cap "
          f"{6 * (len(V) - 1) - 2} < target; max rank over "
          f"{draws} draws/colouring = {maxrk}")
    assert maxrk == 6 * (len(V) - 1) - 2 == target - 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--audit', action='store_true')
    ap.add_argument('--dimz', action='store_true')
    ap.add_argument('--rank', action='store_true')
    ap.add_argument('--theta', action='store_true')
    ap.add_argument('--validate', action='store_true')
    args = ap.parse_args()
    if args.validate or args.audit:
        leg_audit()
    if args.validate or args.dimz:
        leg_dimz()
    if args.validate or args.rank:
        leg_rank()
    if args.validate or args.theta:
        leg_theta()
    if not any(vars(args).values()):
        ap.print_help()


if __name__ == '__main__':
    main()
