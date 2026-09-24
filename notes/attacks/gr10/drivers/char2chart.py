#!/usr/bin/env python3
"""Attack gr10, probe (P): the Lean `pencilRow` chart matrix in characteristic 2.

Builds, per census shape, the row family `pencilRow hubSel G.endsOf q` of
`Molecule/Pencil/Engine.lean` (declaration `pencilRow`) at a random seed `q`
over a finite field, transcribed from the Lean definitions:

  * `PencilSeed.ofCoord q`: hubNormal v = q(v,0,.), fillHub v j = q(v,j+1,.);
  * `hubSlotNormal`: slot i of v's selector is hubNormal w if hubSel v i = some w,
    else fillHub v i;
  * `pencilChartPoint` = `cross₃` of the three slot normals, `cross₃ x y z` the
    vector representing w ↦ det[x; y; z; w] (Chart.lean `cross₃`), i.e. the
    cofactor vector along the last row;
  * `ScrewSpace.mk (extensor ![p_u, p_v])`: coordinates in the exterior-power
    basis of `Pi.basisFun` are the 2x2 minors p_u[i]p_v[j] - p_u[j]p_v[i],
    {i<j} ⊂ Fin 4 (`screwBasis 2`);
  * `annihRow C t1 t2 = C_t1 • e*_t2 - C_t2 • e*_t1` (PanelLayer.lean);
  * `hingeRow u v r = r ∘ screwDiff u v`: r in u's block, -r in v's.

`hubSel v` lists `closedHubNbhd v` (hubs = degree >= 3, among v and its
neighbours) in sorted order in slots 0.., padding slots `none`; this is an
`IsFin3SelectorOf` by construction (member / cover / injective, asserted).
`G.endsOf e` is taken as the stored orientation of e; swapping it negates rows.

The rows are reduced greedily in index order; the indices of the rows that
raise the rank are the certificate `s` of the bridge
`hasGenericPencilRealization_of_independent_pencilRow_target` (Escape.lean).
Rank = 6(|V|-1) (with def_3 = 0 asserted) is a HIT: a nonzero maximal minor at
a point of GF(2^k), hence a nonzero polynomial mod 2 (workbook S1).

Fields: GF(2^k) (k = 20, modulus x^20 + x^3 + 1, primitivity asserted), and
GF(p) for odd primes p as controls.  Exact arithmetic throughout.

Reproduce (all seeded; PYTHONHASHSEED=0 for the census enumeration):
  PYTHONHASHSEED=0 python3 notes/attacks/gr10/drivers/char2chart.py --control
  PYTHONHASHSEED=0 python3 notes/attacks/gr10/drivers/char2chart.py --sweep
  PYTHONHASHSEED=0 python3 notes/attacks/gr10/drivers/char2chart.py --cubic
  PYTHONHASHSEED=0 python3 notes/attacks/gr10/drivers/char2chart.py --cert 'theta(2, 5, 5)'
"""
import argparse
import itertools
import os
import random
import sys
import time

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                '..', '..', '..', 'scripts'))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from grid import census_shapes                                  # noqa: E402
from kbare_common import verts_of                               # noqa: E402
from nogood_subdiv import deficiency, hcard_ok                  # noqa: E402

SEED = 20260923
K2 = 20
MOD2 = (1 << 20) | (1 << 3) | 1          # x^20 + x^3 + 1
PAIRS = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]   # 2-subsets of Fin 4


# ---------------------------------------------------------------- fields
class GF2k:
    def __init__(self, k=K2, mod=MOD2):
        self.k, self.q, self.char = k, 1 << k, 2
        n = self.q - 1
        exp = [0] * (2 * n)
        log = [0] * self.q
        x = 1
        for i in range(n):
            exp[i] = x
            log[x] = i
            x <<= 1
            if x & self.q:
                x ^= mod
        assert x == 1, "modulus not primitive"
        assert len(set(exp[:n])) == n, "modulus not primitive"
        for i in range(n, 2 * n):
            exp[i] = exp[i - n]
        self.exp, self.log, self.n = exp, log, n
        self.name = f"GF(2^{k})"

    def add(self, a, b): return a ^ b
    def sub(self, a, b): return a ^ b
    def neg(self, a): return a

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[self.n - self.log[a]]

    def rand(self, rng): return rng.randrange(self.q)


class GFp:
    def __init__(self, p):
        self.q, self.char, self.p = p, p, p
        self.name = f"GF({p})"

    def add(self, a, b): return (a + b) % self.p
    def sub(self, a, b): return (a - b) % self.p
    def neg(self, a): return (-a) % self.p
    def mul(self, a, b): return (a * b) % self.p
    def inv(self, a): return pow(a, self.p - 2, self.p)
    def rand(self, rng): return rng.randrange(self.p)


# ---------------------------------------------------------------- chart
def det3(Fd, m):
    (a, b, c), (d, e, f), (g, h, i) = m
    mul, sub, add = Fd.mul, Fd.sub, Fd.add
    return add(sub(mul(a, sub(mul(e, i), mul(f, h))),
                   mul(b, sub(mul(d, i), mul(f, g)))),
               mul(c, sub(mul(d, h), mul(e, g))))


def cross3(Fd, x, y, z):
    """cross₃ x y z: the vector c with c·w = det[x; y; z; w] (Chart.lean).
    Expanding along the last row: c_i = (-1)^(3+i) det(minor deleting col i)."""
    out = []
    for i in range(4):
        cols = [j for j in range(4) if j != i]
        d = det3(Fd, [[r[j] for j in cols] for r in (x, y, z)])
        out.append(d if (3 + i) % 2 == 0 else Fd.neg(d))
    return out


def neighbours(edges):
    nb = {}
    for u, w in edges:
        nb.setdefault(u, set()).add(w)
        nb.setdefault(w, set()).add(u)
    return nb


def closed_hub_nbhd(nb, v):
    hub = {x for x in nb if len(nb[x]) >= 3}
    return sorted({w for w in (nb[v] | {v}) if w in hub})


def hub_selector(nb, v):
    chn = closed_hub_nbhd(nb, v)
    assert len(chn) <= 3, "hcard"
    sel = [chn[i] if i < len(chn) else None for i in range(3)]
    # IsFin3SelectorOf (closedHubNbhd v) sel: member / cover / injective
    assert all(w in chn for w in sel if w is not None)
    assert all(w in sel for w in chn)
    assert len([w for w in sel if w is not None]) == len(set(w for w in sel if w is not None))
    return sel


def chart_points(Fd, verts, nb, q):
    """pencilChartPoint (PencilSeed.ofCoord q) hubSel v for every v."""
    sel = {v: hub_selector(nb, v) for v in verts}
    pts = {}
    for v in verts:
        slots = [q[(w, 0)] if w is not None else q[(v, i + 1)]
                 for i, w in enumerate(sel[v])]
        pts[v] = cross3(Fd, *slots)
    return pts, sel


def pencil_rows(Fd, verts, edges, pts):
    """The pencilRow family, indexed (edge index, t1, t2), t1 < t2 (t1 = t2 is
    the zero row, (t2,t1) the negated row).  Yields (index, sparse row)."""
    col = {v: 6 * i for i, v in enumerate(verts)}
    for ei, (u, w) in enumerate(edges):
        pu, pw = pts[u], pts[w]
        C = [Fd.sub(Fd.mul(pu[i], pw[j]), Fd.mul(pu[j], pw[i])) for i, j in PAIRS]
        for t1, t2 in itertools.combinations(range(6), 2):
            r = {}
            # annihRow C t1 t2 = C_t1 e*_t2 - C_t2 e*_t1 ; hingeRow: +r at u, -r at w
            for t, c in ((t2, C[t1]), (t1, Fd.neg(C[t2]))):
                if c:
                    r[col[u] + t] = Fd.add(r.get(col[u] + t, 0), c)
                    r[col[w] + t] = Fd.add(r.get(col[w] + t, 0), Fd.neg(c))
            yield (ei, t1, t2), {k: x for k, x in r.items() if x}


def greedy_rank(Fd, rows, target, ncols):
    """Incremental elimination; returns (rank, indices of rank-raising rows)."""
    piv = {}          # pivot col -> dense normalized row (pivot entry 1)
    chosen = []
    for idx, sr in rows:
        v = [0] * ncols
        for k, x in sr.items():
            v[k] = x
        for c in sorted(piv):
            a = v[c]
            if a:
                pr = piv[c]
                for j in range(c, ncols):
                    if pr[j]:
                        v[j] = Fd.sub(v[j], Fd.mul(a, pr[j]))
        lead = next((j for j in range(ncols) if v[j]), None)
        if lead is None:
            continue
        il = Fd.inv(v[lead])
        piv[lead] = [Fd.mul(il, x) for x in v]
        chosen.append(idx)
        if len(chosen) == target:
            break
    return len(chosen), chosen


def dense_rank(Fd, mat):
    """Independent re-check: plain dense Gaussian elimination, rows x cols."""
    m = [list(r) for r in mat]
    rk, ncols = 0, len(m[0]) if m else 0
    for c in range(ncols):
        p = next((i for i in range(rk, len(m)) if m[i][c]), None)
        if p is None:
            continue
        m[rk], m[p] = m[p], m[rk]
        il = Fd.inv(m[rk][c])
        m[rk] = [Fd.mul(il, x) for x in m[rk]]
        for i in range(len(m)):
            if i != rk and m[i][c]:
                a = m[i][c]
                m[i] = [Fd.sub(x, Fd.mul(a, y)) for x, y in zip(m[i], m[rk])]
        rk += 1
    return rk


def verify_cert(Fd, verts, edges, pts, chosen):
    """The rows at s alone, rebuilt from scratch and dense-ranked: |s| and
    independent (so some |s| x |s| minor is nonzero), every index a genuine
    edge (an index into `edges`)."""
    want = set(chosen)
    ncols = 6 * len(verts)
    mat = []
    for idx, sr in pencil_rows(Fd, verts, edges, pts):
        if idx in want:
            assert 0 <= idx[0] < len(edges)
            row = [0] * ncols
            for k, x in sr.items():
                row[k] = x
            mat.append(row)
    assert len(mat) == len(chosen)
    return dense_rank(Fd, mat) == len(chosen)


def check_shape(edges):
    """The bridge's shape hypotheses, per shape: Simple, Nonempty, hcard,
    triangle-free, def_3 = 0."""
    verts = sorted(verts_of(edges), key=str)
    assert verts, "V nonempty"
    assert all(u != w for u, w in edges), "loop"
    assert len({frozenset(e) for e in edges}) == len(edges), "parallel edge"
    nb = neighbours(edges)
    assert hcard_ok(edges), "hcard"
    for u, w in edges:
        assert not (nb[u] & nb[w]), "triangle"
    assert deficiency(edges) == 0, "def_3 != 0"
    return verts, nb


def run_shape(Fd, edges, rng, verts=None, nb=None):
    if verts is None:
        verts, nb = check_shape(edges)
    q = {(v, role): [Fd.rand(rng) for _ in range(4)] for v in verts for role in range(4)}
    pts, sel = chart_points(Fd, verts, nb, q)
    target = 6 * (len(verts) - 1)
    rk, chosen = greedy_rank(Fd, pencil_rows(Fd, verts, edges, pts), target, 6 * len(verts))
    if rk == target:
        assert verify_cert(Fd, verts, edges, pts, chosen), "certificate re-check failed"
    return rk, target, chosen, q, sel


# ---------------------------------------------------------------- modes
def mode_control(args):
    print(f"[control] O1: chart rank over odd GF(p) on the first {args.cap} census "
          f"shapes, seed {SEED}; expected rank 6(|V|-1) at every one")
    for p in (2**31 - 1, 10007):
        Fd = GFp(p)
        rng = random.Random(SEED + p)
        hit = n = 0
        for lab, edges in itertools.islice(census_shapes(), args.cap):
            rk, target, *_ = run_shape(Fd, edges, rng)
            n += 1
            hit += rk == target
            if rk != target:
                print(f"  {Fd.name} MISS {lab}: rank {rk} < {target}")
        print(f"  {Fd.name}: {hit}/{n} at rank 6(|V|-1)")


def mode_sweep(args):
    Fd = GF2k()
    rng = random.Random(SEED)
    t0 = time.time()
    n = hits = 0
    misses = []
    for lab, edges in itertools.islice(census_shapes(), args.cap):
        verts, nb = check_shape(edges)
        n += 1
        best = -1
        for s in range(args.seeds):
            rk, target, *_ = run_shape(Fd, edges, rng, verts, nb)
            best = max(best, rk)
            if rk == target:
                break
        if best == target:
            hits += 1
        else:
            misses.append((lab, len(verts), target, best))
            print(f"  MISS {lab}: best rank {best} < {target} over {args.seeds} seeds")
        if n % 100 == 0:
            print(f"  ... {n} shapes, {hits} hits, {time.time() - t0:.0f}s", flush=True)
    print(f"[sweep] {Fd.name}, seed {SEED}, <= {args.seeds} seeds/shape, "
          f"population: census_shapes() cap {args.cap or 'all 907'}")
    print(f"  shapes {n}; HITS (proofs of (P)) {hits}; misses {len(misses)}; "
          f"{time.time() - t0:.0f}s")
    for m in misses:
        lab, nv, target, best = m
        print(f"  miss {lab}: |V| {nv}, deficit {target - best}, deg Δ <= {6 * target}, "
              f"per-seed miss prob <= {6 * target}/2^{K2}")


def mode_cubic(args):
    """Second population: the (GR-26) cubic D = 0 stratum at n_hub in (2, 4, 6),
    exactly as `gisland.leg_island` enumerates it (all length tuples at n <= 4,
    at most one length-1 branch at n = 6), one representative per isomorphism
    class (`gisland.stratum`), kept when `gridcol.class_shape` accepts it.  A
    chart-rank hit is invariant under relabelling, so a class hit covers every
    labelled member; the labelled count is reported beside the class count."""
    from gisland import stratum, specs_of, scan_shape, CUBIC_N
    from gridcol import class_shape
    Fd = GF2k()
    rng = random.Random(SEED + 1)
    srng = random.Random(0)
    t0 = time.time()
    for n in CUBIC_N:
        cap = 99 if n <= 4 else 1
        ncls = nlab = hits = lab26 = 0
        for hedges, lens, members, _auts in stratum(n, lamcap=cap):
            edges = class_shape(specs_of(hedges, lens))
            if edges is None:
                continue
            verts, nb = check_shape(edges)
            ncls += 1
            nlab += len(members)
            if scan_shape(specs_of(hedges, lens), srng, want_rank=False) is not None:
                lab26 += len(members)
            best = -1
            for _ in range(args.seeds):
                rk, target, *_ = run_shape(Fd, edges, rng, verts, nb)
                best = max(best, rk)
                if rk == target:
                    break
            if best == target:
                hits += 1
            else:
                print(f"  MISS n_hub={n} lens={lens}: best {best} < {target}")
        print(f"  n_hub={n}, |Lambda| <= {cap}: {ncls} isomorphism classes "
              f"({nlab} labelled; {lab26} labelled in the (GR-26) count), "
              f"HITS {hits}/{ncls}  [{time.time() - t0:.0f}s]", flush=True)
    print(f"[cubic] {Fd.name}, seed {SEED + 1}, <= {args.seeds} seeds/class")


def mode_cert(args):
    Fd = GF2k()
    rng = random.Random(SEED)
    for lab, edges in census_shapes():
        if lab != args.cert:
            continue
        rk, target, chosen, q, sel = run_shape(Fd, edges, rng)
        print(f"[cert] {lab} over {Fd.name}, seed {SEED} (first draw)")
        print(f"  edges (endsOf = stored orientation): {edges}")
        print(f"  hubSel: { {v: s for v, s in sel.items() if any(x is not None for x in s)} } (others all none)")
        print(f"  rank {rk} / target {target}: {'HIT' if rk == target else 'MISS'}")
        print(f"  s = {chosen}")
        return
    sys.exit(f"no census shape labelled {args.cert!r}")


def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument('--control', action='store_true')
    g.add_argument('--sweep', action='store_true')
    g.add_argument('--cubic', action='store_true')
    g.add_argument('--cert', metavar='LABEL')
    ap.add_argument('--cap', type=int, default=None)
    ap.add_argument('--seeds', type=int, default=3)
    args = ap.parse_args()
    if args.control:
        args.cap = args.cap or 20
        mode_control(args)
    elif args.sweep:
        mode_sweep(args)
    elif args.cubic:
        mode_cubic(args)
    else:
        mode_cert(args)


if __name__ == '__main__':
    main()
