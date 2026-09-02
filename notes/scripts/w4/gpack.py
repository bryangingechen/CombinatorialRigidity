"""
Phase 39 (K-grid) — direction GPACK: (GR-18)(iii), the grouping problem.

(GR-18)(i) is a THEOREM: `def(G) = 0` alone forces the hub multigraph `Ghat`
(branch `beta` at multiplicity `m_beta = 6 - ell_beta`) to partition into
exactly 6 spanning trees of `G^o`.  (GR-18)(iii) asks the converse-shaped
question: does SOME such partition admit a 3+3 split `J` with
`|C_beta ^ J| = 3 - A(beta)` for a length-legal `A(beta)`, together with an
A-end choice on each even branch and a consistent hub colouring?

RESULT (2026-09-02): the **split half is a THEOREM** ((GR-130)), the
**exchange freedom it uses is load-bearing** ((GR-131)), and what is left of
(GR-18)(iii) is **exactly** a hub list-colouring ((GR-132)).

  * `--split` is (GR-129)/(GR-130).  The split condition is exactly
    "`J` bisects every `C_beta` as evenly as possible", and a (packing,
    split) pair is exactly a signing `s : O -> {+-1}` of the ODD-length
    branches with `|s(F)| <= sigma(F)` at every branch set `F`, where
    `sigma(F) = 6 r(F) - sum_F m_beta = sum_F ell_beta - 6 c(F)` is the
    5/6-sparsity slack -- the SAME inequality `gridcol.nash_williams_ok`
    checks for (GR-18)(i).  A legal signing always exists (proof in the
    workbook, *Step G150*); this leg is the adversarial control, run
    EXHAUSTIVELY over all branch subsets and all balanced signings at every
    census shape, and cross-checked against `saferes.union_rank`.
  * `--arb` is (GR-131), the coordinator's expectation REFUTED.  An
    ARBITRARY 6-tree partition need not admit any legal split: enumerated
    exhaustively at the low-`m` census shapes, a measured 2.6% of them do
    not.  The mechanism is a parity one -- an ODD CYCLE in the split graph
    whose edges are the pairs a length-2 or length-4 branch demands be
    separated -- and it is exhibited.
  * `--resid` is (GR-132).  At `Lambda = 0` the remaining clauses of
    (GR-18)(iii) are a list-colouring of the HUBS: labels `g_A(u) in J`,
    `g_B(u) in J^c`, lists `J \\ C_beta` of size `A(beta)`, a `!=` edge at
    every branch with two same-colour ends, plus "no monochromatic hub".
    Both directions are asserted: every CSP witness rebuilds a
    filter-passing colouring carrying a both-block tree-triple, and every
    certificate-induced (packing, split) is CSP-feasible.

Oracles.  Shapes and their branch decompositions come from
`gridcol.pool_shapes` / `gridcol.branch_decomp` (the census's own);
3-spanning-tree packability is decided by `saferes.union_rank` (matroid
union), independently of the `sigma` criterion this file derives; the
certificate side is `packmm.fast_triple` on `grid.block_data`, gated by
`gridcol.filter_pass`, exactly as `gridcol.py --pack` does it.

Caps, with denominators (README section 4 convention 5).  `--split` is
exhaustive at all 907 census shapes (`2^m <= 2^15` branch subsets each,
`m <= 15`; `C(|O|, |O|/2) <= 252` signings each).  `--arb` enumerates 6-tree
partitions exhaustively but only at the first `ARB_SHAPES = 40` census
shapes with `m <= 6` -- an exhaustive statement about a NAMED subpool, never
about the census.  `--resid` runs at the first `RESID_SHAPES = 12` census
shapes with `m <= 6` AND `Lambda = 0` (`min ell >= 2`), for the same reason.

Run:
    python3 notes/scripts/w4/gpack.py --split    # (GR-129)/(GR-130)
    python3 notes/scripts/w4/gpack.py --arb      # (GR-131)
    python3 notes/scripts/w4/gpack.py --resid    # (GR-132)
    python3 notes/scripts/w4/gpack.py --validate # all three
"""
import random
import sys
from itertools import combinations, product

import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                     # noqa: E402
from closure import colourings, cycle_rank                            # noqa: E402
from grid import block_data                                           # noqa: E402
from packmm import fast_triple                                        # noqa: E402
from saferes import union_rank                                        # noqa: E402
from gridcol import (branch_decomp, branch_classes, filter_pass,      # noqa: E402
                     nash_williams_ok, pool_shapes)

G_SEED = 20260902
ARB_SHAPES = 40
RESID_SHAPES = 12
SUBSET_CAP = 1 << 16          # same cap `gridcol.nash_williams_ok` uses


# ------------------------------------------------------- local devices ------

def shape_rows(cap=None, mmax=None, lambda_free=False):
    """(label, hubs, ends, lens) for the census shapes, optionally filtered to
    `m <= mmax` branches and to `Lambda = 0` (no length-1 branch)."""
    n = 0
    for label, edges in pool_shapes(None):
        hubs, br = branch_decomp(edges)
        if br is None:
            continue
        ends = [(u, w) for (u, w, _) in br]
        lens = [len(p) for (_, _, p) in br]
        if mmax is not None and len(ends) > mmax:
            continue
        if lambda_free and min(lens) < 2:
            continue
        yield label, edges, hubs, br, ends, lens
        n += 1
        if cap is not None and n >= cap:
            return


def sigma_table(hubs, ends, lens):
    """`(ranks, sigma)` over every branch subset, indexed by bitmask, with
    `sigma(F) = 6 r(F) - sum_F (6 - ell)`.  `sigma >= 0` IS 5/6-sparsity (the
    inequality (GR-18)(i)'s proof establishes) and `sigma(E) = 0` IS
    count-tightness."""
    m = len(ends)
    assert (1 << m) <= SUBSET_CAP, "branch-subset enumeration over cap"
    idx = {v: i for i, v in enumerate(hubs)}
    rk = [0] * (1 << m)
    sig = [0] * (1 << m)
    for mask in range(1, 1 << m):
        sel = [i for i in range(m) if mask >> i & 1]
        vs = sorted({idx[ends[i][0]] for i in sel} |
                    {idx[ends[i][1]] for i in sel})
        ed = [(idx[ends[i][0]], idx[ends[i][1]]) for i in sel]
        rk[mask] = len(ed) - cycle_rank(vs, ed)
        sig[mask] = 6 * rk[mask] - sum(6 - lens[i] for i in sel)
    return rk, sig


def packs_three(hubs, ends, mult):
    """Does the multigraph `beta -> mult[beta]` partition into 3 spanning
    trees of the hub graph?  Decided by matroid union, NOT by `sigma`."""
    ed = []
    for i, (u, w) in enumerate(ends):
        ed += [(u, w)] * mult[i]
    if len(ed) != 3 * (len(hubs) - 1):
        return False
    return union_rank(ed, list(hubs), k=3) == 3 * (len(hubs) - 1)


def signings(lens):
    """Every balanced signing of the odd-length branches, as the set `P` of
    branches carrying `+1` (`|P| = |O|/2` is forced by `sigma(E) = 0`)."""
    O = [i for i in range(len(lens)) if lens[i] % 2]
    return O, [set(P) for P in combinations(O, len(O) // 2)]


def signing_ok(sig, O, P, m):
    """`|s(F)| <= sigma(F)` at every branch set -- the (GR-129)(iii) test."""
    for mask in range(1, 1 << m):
        tot = sum(1 if i in P else -1 for i in O if mask >> i & 1)
        if abs(tot) > sig[mask]:
            return False
    return True


def side_mults(lens, P):
    """The two multiplicity vectors a signing induces."""
    a = [(6 - lens[i]) // 2 + (1 if i in P else 0) for i in range(len(lens))]
    b = [(6 - lens[i]) - a[i] for i in range(len(lens))]
    return a, b


# -------------------------------------- [GP-1] --split: (GR-129)/(GR-130) ---

def leg_split():
    """[GP-1] The signing normal form, and the split theorem's control."""
    print("[GP-1] (GR-129)/(GR-130): the split is an equitable bisection, "
          "and one always exists; all census shapes")
    rng = random.Random(G_SEED)
    nshape = found = 0
    inst = 0
    rank_checks = 0
    lo, hi = 99, 0
    for label, edges, hubs, br, ends, lens in shape_rows():
        nshape += 1
        m = len(ends)
        rk, sig = sigma_table(hubs, ends, lens)
        assert min(sig) >= 0, f"{label}: sigma < 0 (5/6-sparsity fails)"
        assert sig[(1 << m) - 1] == 0, f"{label}: sigma(E) != 0 (not tight)"
        ok, exh = nash_williams_ok(hubs, ends, lens)
        assert exh and ok, f"{label}: nash_williams_ok disagrees with sigma"
        O, cands = signings(lens)
        lo, hi = min(lo, len(O)), max(hi, len(O))
        hit = None
        for P in cands:
            c = signing_ok(sig, O, P, m)
            a, b = side_mults(lens, P)
            u = packs_three(hubs, ends, a) and packs_three(hubs, ends, b)
            assert c == u, \
                f"{label}: sigma criterion {c} != matroid-union verdict {u}"
            inst += 1
            if c and hit is None:
                hit = (P, a, b)
        assert hit is not None, f"{label}: NO legal signing -- (GR-130) FAILS"
        found += 1
        # the split condition, read back off the two sides: every C_beta is
        # bisected as evenly as possible, and the A-values are length-legal
        # and BALANCED ((GR-129)(i)/(ii)).
        # Either side may play the role of `J`, so both readings are checked:
        # `A(beta) = 3 - |C_beta ^ J|` must be length-legal and sum to 3c.
        P, a, b = hit
        for side in (a, b):
            A = [3 - side[i] for i in range(m)]
            for i in range(m):
                assert abs(a[i] - b[i]) <= 1, \
                    f"{label}: side split not equitable"
                assert A[i] in (lens[i] // 2, (lens[i] + 1) // 2), \
                    f"{label}: A({i}) = {A[i]} not length-legal"
            assert sum(A) == 3 * (len(ends) - len(hubs) + 1), \
                f"{label}: the split's A-assignment is not balanced"
        # the theorem's matroid step, checked against the actual matroid on a
        # sampled S: |S| <= 2 rank_M(S) with M = (N_3 / H_0)|_O, and the
        # closed form rank_M(S) = |S| + min_F (3 r(F) - y_S(F)).
        if O and rank_checks < 200:
            H0 = [(6 - L) // 2 for L in lens]
            base = []
            for i, (u_, w_) in enumerate(ends):
                base += [(u_, w_)] * H0[i]
            r0 = union_rank(base, list(hubs), k=3)
            assert r0 == sum(H0), f"{label}: H_0 is not N_3-independent"
            for _ in range(2):
                S = {i for i in O if rng.random() < 0.5}
                ext = base + [ends[i] for i in sorted(S)]
                rM = union_rank(ext, list(hubs), k=3) - r0
                y = [H0[i] + (1 if i in S else 0) for i in range(m)]
                best = min(3 * rk[mask] -
                           sum(y[i] for i in range(m) if mask >> i & 1)
                           for mask in range(1 << m))
                closed = len(S) + best
                assert rM == closed, \
                    f"{label}: rank_M closed form {closed} != {rM}"
                assert len(S) <= 2 * rM, \
                    f"{label}: Edmonds covering condition FAILS at S = {S}"
                rank_checks += 1
    print(f"  sigma >= 0 and sigma(E) = 0 at {nshape}/{nshape} census shapes, "
          f"exhaustively over all 2^m branch subsets (m <= 15), and agreeing "
          f"with `gridcol.nash_williams_ok` at every shape")
    print(f"  a legal signing FOUND at {found}/{nshape} -- (GR-130)'s "
          f"conclusion, checked end to end: both sides asserted to pack 3 "
          f"spanning trees by `saferes.union_rank`, the split asserted "
          f"equitable, length-legal and BALANCED")
    print(f"  the sigma criterion vs. the matroid-union verdict: "
          f"{inst}/{inst} (shape, signing) instances agree, 0 disagreements "
          f"(|O| ranges {lo}..{hi})")
    print(f"  the theorem's own matroid step -- H_0 independent in N_3, the "
          f"rank_M closed form, and Edmonds' |S| <= 2 rank_M(S) -- asserted "
          f"at {rank_checks} sampled S")
    print()


# ------------------------------------------------ [GP-2] --arb: (GR-131) ----

def all_packings(hubs, ends, lens, cap=1 << 20):
    """Every partition of `Ghat` into 6 spanning trees, as the six branch
    index sets `T_j`.  Exhaustive (the cap is an assertion, not a sample)."""
    m, n = len(ends), len(hubs)
    idx = {v: i for i, v in enumerate(hubs)}
    ed = [(idx[u], idx[w]) for u, w in ends]
    out = []

    def acyclic(sel):
        return cycle_rank(list(range(n)), [ed[i] for i in sel]) == 0

    def rec(i, trees):
        if i == m:
            if all(len(t) == n - 1 for t in trees):
                out.append([tuple(t) for t in trees])
            return
        rem = sum(6 - lens[k] for k in range(i + 1, m))
        for C in combinations(range(6), 6 - lens[i]):
            nt = [list(t) for t in trees]
            ok = True
            for j in C:
                if len(nt[j]) >= n - 1:
                    ok = False
                    break
                nt[j].append(i)
                if not acyclic(nt[j]):
                    ok = False
                    break
            if not ok:
                continue
            if sum((n - 1) - len(nt[j]) for j in range(6)) > rem:
                continue
            rec(i + 1, nt)

    rec(0, [[] for _ in range(6)])
    assert len(out) < cap, "packing enumeration hit its cap"
    return out


def csets(lens, trees):
    return [set(j for j in range(6) if i in trees[j]) for i in range(len(lens))]


def legal_splits(lens, C):
    """Every 3-subset `J` bisecting every `C_beta` as evenly as possible."""
    out = []
    for J in combinations(range(6), 3):
        Js = set(J)
        if all(abs(2 * len(C[i] & Js) - (6 - lens[i])) <= 1
               for i in range(len(lens))):
            out.append(J)
    return out


def pair_graph(lens, C):
    """The pairs a length-2 or length-4 branch demands be SEPARATED by `J`:
    `C_beta` itself at `ell = 4`, its complement at `ell = 2`."""
    P = []
    for i, L in enumerate(lens):
        if L == 4:
            P.append(tuple(sorted(C[i])))
        elif L == 2:
            P.append(tuple(sorted(set(range(6)) - C[i])))
    return P


def bipartite_balanced(P):
    """(bipartite?, some proper 2-colouring with parts 3+3?)."""
    col = {}
    adj = {j: set() for j in range(6)}
    for u, w in P:
        adj[u].add(w)
        adj[w].add(u)
    comps = []
    for s in range(6):
        if s in col:
            continue
        col[s] = 0
        st, comp = [s], [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in col:
                    col[y] = 1 - col[x]
                    st.append(y)
                    comp.append(y)
                elif col[y] == col[x]:
                    return False, False
        comps.append(comp)
    for flips in product((0, 1), repeat=len(comps)):
        side = sum(sum(1 for x in c if col[x] ^ f == 0)
                   for c, f in zip(comps, flips))
        if side == 3:
            return True, True
    return True, False


def leg_arb():
    """[GP-2] (GR-131): an arbitrary packing need not split."""
    print(f"[GP-2] (GR-131): an ARBITRARY 6-tree partition need not admit a "
          f"legal split; first {ARB_SHAPES} census shapes with m <= 6")
    tot = bad = nshape = 0
    nonbip = unbal = only3 = 0
    wit = None
    for label, edges, hubs, br, ends, lens in shape_rows(ARB_SHAPES, mmax=6):
        nshape += 1
        for trees in all_packings(hubs, ends, lens):
            tot += 1
            C = csets(lens, trees)
            if legal_splits(lens, C):
                continue
            bad += 1
            bip, bal = bipartite_balanced(pair_graph(lens, C))
            if not bip:
                nonbip += 1
            elif not bal:
                unbal += 1
            else:
                only3 += 1
            if wit is None and not bip:
                wit = (label, lens, trees, pair_graph(lens, C))
    assert bad > 0, "no split-less packing found -- (GR-131) would be FALSE"
    print(f"  {tot} 6-tree partitions enumerated exhaustively over "
          f"{nshape} shapes; {bad} ({100.0 * bad / tot:.1f}%) admit NO legal "
          f"3+3 split")
    print(f"  failure mechanism: {nonbip} have a NON-BIPARTITE split graph "
          f"(an odd cycle among the separation pairs), {unbal} are bipartite "
          f"with no 3+3 side split, {only3} fail only through the length-3 "
          f"clause")
    label, lens, trees, P = wit
    print(f"  witness  {label}  lengths {lens}")
    print(f"    packing (branch sets of the six trees) {trees}")
    print(f"    separation pairs {P} -- an odd cycle, so no `J` at all")
    assert len(P) >= 3, "witness has too few separation pairs"
    print(f"  => the certificate-induced packing is NOT canonical, and "
          f"(GR-130)'s CONSTRUCTION of the packing is load-bearing; "
          f"`gridcol.py --pack`'s 907/907 is evidence for (GR-18)(i), which "
          f"is already a theorem, and none for (iii)")
    print()


# ---------------------------------------------- [GP-3] --resid: (GR-132) ----

def end_patterns(lens, A):
    """Per branch, the legal (colour at end u, colour at end w) options."""
    opts = []
    for i, L in enumerate(lens):
        if L % 2 == 0:
            if A[i] != L // 2:
                return None
            opts.append([('A', 'B'), ('B', 'A')])
        elif A[i] == (L + 1) // 2:
            opts.append([('A', 'A')])
        elif A[i] == (L - 1) // 2:
            opts.append([('B', 'B')])
        else:
            return None
    return opts


def csp_witness(hubs, ends, lens, C, J):
    """(GR-132): the hub list-colouring.  Returns an end pattern admitting
    hub labels, or None."""
    A = [3 - len(C[i] & set(J)) for i in range(len(lens))]
    opts = end_patterns(lens, A)
    if opts is None:
        return None
    sides = (('A', list(J)), ('B', [j for j in range(6) if j not in J]))
    for pick in product(*[range(len(o)) for o in opts]):
        pat = [opts[i][pick[i]] for i in range(len(lens))]
        seen = {}
        for i, (u, w) in enumerate(ends):
            seen.setdefault(u, set()).add(pat[i][0])
            seen.setdefault(w, set()).add(pat[i][1])
        if any(len(s) < 2 for s in seen.values()):
            continue                       # a monochromatic hub
        good = True
        for side, labels in sides:
            lists = {u: set(labels) for u in hubs}
            diff = []
            for i, (u, w) in enumerate(ends):
                for v, c in ((u, pat[i][0]), (w, pat[i][1])):
                    if c == side:
                        lists[v] -= C[i]
                if pat[i][0] == side and pat[i][1] == side:
                    diff.append((u, w))
            hs = list(hubs)
            if not any(all(g[u] != g[w] for u, w in diff)
                       for g in ({h: v for h, v in zip(hs, a)}
                                 for a in product(*[sorted(lists[u])
                                                    for u in hs]))):
                good = False
                break
        if good:
            return pat
    return None


def rebuild(br, pat):
    """The colouring an end pattern determines (alternation does the rest)."""
    col = {}
    for i, (_, _, path) in enumerate(br):
        cur = pat[i][0]
        for e in path:
            col[e] = cur
            cur = 'B' if cur == 'A' else 'A'
        last = 'B' if cur == 'A' else 'A'
        assert last == pat[i][1], "end pattern inconsistent with alternation"
    return col


def leg_resid():
    """[GP-3] (GR-132): the residual IS a hub list-colouring."""
    print(f"[GP-3] (GR-132): what is left of (GR-18)(iii) at Lambda = 0; "
          f"first {RESID_SHAPES} census shapes with m <= 6")
    nshape = nsound = ncomplete = ncert = 0
    forced = 0
    for label, edges, hubs, br, ends, lens in shape_rows(
            RESID_SHAPES, mmax=6, lambda_free=True):
        nshape += 1
        allverts = sorted(verts_of(edges), key=str)
        assert all(u != w for u, w in ends), f"{label}: a loop branch"
        forced += sum(1 for L in lens if L == 2)
        # SOUNDNESS: every CSP witness rebuilds a certified colouring.
        for trees in all_packings(hubs, ends, lens):
            C = csets(lens, trees)
            for J in legal_splits(lens, C):
                pat = csp_witness(hubs, ends, lens, C, J)
                if pat is None:
                    continue
                col = rebuild(br, pat)
                assert filter_pass(edges, allverts, col, hubs), \
                    f"{label}: a CSP witness fails the (GR-2) filter"
                for mine in ('A', 'B'):
                    bd = block_data(edges, allverts, col, mine)
                    tt, capped = fast_triple(bd)
                    assert not capped and tt is not None, \
                        f"{label}: a CSP witness carries no tree-triple"
                nsound += 1
        # COMPLETENESS: every certificate's own (packing, split) is feasible.
        cols, _ = colourings(edges, cap=1 << 16)
        for col in cols:
            if not filter_pass(edges, allverts, col, hubs):
                continue
            trees, ok = [], True
            for mine in ('A', 'B'):
                bd = block_data(edges, allverts, col, mine)
                tt, capped = fast_triple(bd)
                if capped or tt is None:
                    ok = False
                    break
                bc = branch_classes(bd, br)
                for grp in tt:
                    gs = set(grp)
                    trees.append(tuple(k for k in range(len(ends))
                                       if not (gs & set(bc[k]))))
            if not ok:
                continue
            ncert += 1
            C = csets(lens, trees)
            J = (0, 1, 2)
            assert J in legal_splits(lens, C), \
                f"{label}: a certificate's own split is not equitable"
            assert csp_witness(hubs, ends, lens, C, J) is not None, \
                f"{label}: a certificate's (packing, split) fails the CSP"
            ncomplete += 1
    print(f"  SOUND: {nsound}/{nsound} (packing, split) pairs the CSP accepts "
          f"rebuild a colouring that passes the (GR-2) filter and carries a "
          f"tree-triple in BOTH blocks")
    print(f"  COMPLETE: {ncomplete}/{ncert} certificate-induced (packing, "
          f"split) pairs are CSP-feasible, 0 misses")
    print(f"  over {nshape} shapes carrying {forced} length-2 branches -- "
          f"each of which FORCES one hub label on each side (list size "
          f"A(beta) = B(beta) = 1), which is where the residual's difficulty "
          f"sits")
    print()


def main():
    ran = False
    if '--split' in sys.argv or '--validate' in sys.argv:
        leg_split()
        ran = True
    if '--arb' in sys.argv or '--validate' in sys.argv:
        leg_arb()
        ran = True
    if '--resid' in sys.argv or '--validate' in sys.argv:
        leg_resid()
        ran = True
    if not ran:
        print(__doc__)


if __name__ == '__main__':
    main()
