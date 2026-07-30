"""
N9 (2026-07-30, non-constancy recon): corank stratification + canonical-move probes.

N9a: theta(4,4,3) -- a NON-cycle, index-1 candidate minimal-rigid habitat.
  index(G) = 5|E| - 6(|V|-1) = 55 - 54 = 1; if G is rigid and has no proper rigid
  subgraph, it is an hK habitat whose split G' has corank 2 at a pencil-generic
  target-rank seed. Test:
    (i)  generic + pencil-generic rank of G (target 54);
    (ii) split v = p31 (deg-2, adjacent hub h1) -> G' = G - v + (h1,p32);
         pencil-generic seed: rank (target 48), corank (expect 2);
    (iii) stress a-block image R_a (a = p32): dim (expect 2 = corank);
    (iv) dim S (both ends hubs: expect 5); R_a subset of S^perp? (expect NO ->
         escape automatic at corank >= 2, per the boundary-load derivation);
    (v)  extension test: re-insert v in Pi(h1) generically; G-rank (expect 54).

N9b: H1 canonical-move completeness -- for EVERY far movable vertex of the H1
  fiber (local block fixed), does a single in-constraint move change [r]?
"""
from fractions import Fraction as F
import random, itertools
import pencil_escape as pe
from pencil_escape import (build_rigidity, rank, left_nullspace, wedge2, hat, dot,
                           rvec3, rquat)
from localtest import (sample_local, build_cfg, K4, in_plane_point, plane_basis,
                       meet_line, normalize, escape_full)

# ---------- theta(4,4,3) ----------
H1v, H2v = 0, 1
P1 = [10, 11, 12]   # h1-10-11-12-h2
P2 = [20, 21, 22]
P3 = [30, 31]       # h1-30-31-h2   (v = 30, a = 31)

def theta_edges():
    E = []
    for P in (P1, P2, P3):
        E.append((H1v, P[0]))
        for x, y in zip(P, P[1:]):
            E.append((x, y))
        E.append((P[-1], H2v))
    return E

def theta_split_edges():
    """G' = G - 30 + (h1, 31)."""
    E = [e for e in theta_edges() if 30 not in e]
    E.append((H1v, 31))
    return E

def neighbors(edges):
    nb = {}
    for u, w in edges:
        nb.setdefault(u, set()).add(w); nb.setdefault(w, set()).add(u)
    return nb

def place_pencil(edges, rng, extra_inplane=()):
    """Pencil placement: hubs (deg>=3) get (pt, normal); deg-2 vertices adjacent
    to one hub go in-plane, to two hubs on the meet line, to none free.
    extra_inplane: list of (vertex, hub) forced-in-plane constraints (for deg-2
    vertices adjacent to a hub, whose coplanarity the hub's star demands)."""
    nb = neighbors(edges)
    V = sorted(nb)
    deg = {v: len(nb[v]) for v in V}
    hubs = [v for v in V if deg[v] >= 3]
    pt = {h: rvec3(rng) for h in hubs}
    nrm = {h: rvec3(rng) for h in hubs}
    placed = dict(pt)
    forced = dict(extra_inplane)
    for s in V:
        if s in hubs:
            continue
        hn = sorted(t for t in nb[s] if t in hubs)
        if s in forced:
            placed[s] = in_plane_point(pt[forced[s]], nrm[forced[s]], rng)
        elif len(hn) == 2:
            p0, d = meet_line(pt[hn[0]], nrm[hn[0]], pt[hn[1]], nrm[hn[1]])
            t = rquat(rng)
            placed[s] = [p0[i] + t*d[i] for i in range(3)]
        elif len(hn) == 1:
            placed[s] = in_plane_point(pt[hn[0]], nrm[hn[0]], rng)
        else:
            placed[s] = rvec3(rng)
    return placed, pt, nrm, hubs, nb

def rank_of(edges, placed):
    V = sorted(set(itertools.chain.from_iterable(edges)))
    data = {'edges': edges, 'V': V, 'pt': placed}
    rows, er, C, idx, n = build_rigidity(data)
    return rank(rows), 6*(len(V)-1), rows, er, idx, len(V)

def n9a():
    print("===== N9a: theta(4,4,3) =====")
    E = theta_edges()
    rng = random.Random(4243)
    # (i) fully generic rank
    Vs = sorted(set(itertools.chain.from_iterable(E)))
    placed = {v: rvec3(rng) for v in Vs}
    rk, tgt, *_ = rank_of(E, placed)
    print(f"  G generic: rank {rk} / target {tgt}  (rigid iff equal; index = {5*len(E)-tgt})")
    # pencil-generic rank of G (v=30 must be in Pi(h1) for h1's star)
    for s in range(3):
        rng2 = random.Random(100 + s)
        placed, pt, nrm, hubs, nb = place_pencil(E, rng2)
        rk, tgt, *_ = rank_of(E, placed)
        print(f"  G pencil-generic sample {s}: rank {rk} / {tgt}")
    # (ii)-(iv) split
    E2 = theta_split_edges()
    print(f"  G' = G - 30 + (h1,31): |E'| = {len(E2)}, rows {5*len(E2)}, "
          f"target {6*(9-1)}, structural corank {5*len(E2) - 48}")
    for s in range(3):
        rng2 = random.Random(200 + s)
        placed, pt, nrm, hubs, nb = place_pencil(E2, rng2)
        rk, tgt, rows, er, idx, nV = rank_of(E2, placed)
        ln = left_nullspace(rows)
        print(f"  G' pencil sample {s}: rank {rk}/{tgt}  corank {len(ln)}")
        if rk != tgt:
            continue
        a, b, c = 31, H1v, H2v
        e_ab = next(e for e in er if set(e) == {a, b})
        base_a = 6*idx[a]
        Ra = []
        for lam in ln:
            r = [F(0)]*6
            for ri in er[e_ab]:
                for k in range(6):
                    r[k] += lam[ri]*rows[ri][base_a+k]
            Ra.append(r)
        dimRa = rank(Ra)
        # S = L2 Pihat(a) + pencil(b) + pencil(c)
        ah, bh, ch = hat(placed[a]), hat(placed[b]), hat(placed[c])
        S = [wedge2(ah, bh), wedge2(ah, ch), wedge2(bh, ch)]
        for hub, hh in ((b, bh), (c, ch)):
            for u in nb[hub]:
                S.append(wedge2(hh, hat(placed[u])))
        dimS = rank(S)
        # R_a subset of S^perp?
        inSperp = all(all(dot(r, w) == 0 for w in S) for r in Ra)
        anyEscape = not inSperp
        print(f"     dim R_a = {dimRa}  dim S = {dimS}  R_a subset S^perp: {inSperp}"
              f"  -> escape available: {anyEscape}")
        # (v) extension: re-insert v = 30 in Pi(h1)
        for xs in range(2):
            rng3 = random.Random(300 + 10*s + xs)
            pl2 = dict(placed)
            pl2[30] = in_plane_point(pt[H1v], nrm[H1v], rng3)
            rkG, tgtG, *_ = rank_of(E, pl2)
            print(f"     extension sample {xs}: G rank {rkG} / {tgtG}")

def n9b():
    print("\n===== N9b: H1 canonical-move completeness (local block seed 500, far seed 1) =====")
    LOCAL = sample_local(500)
    cfg, (a, b, c), locB, locC = build_cfg(K4(), 0, LOCAL, far_seed=1)
    d0 = cfg(F(0))
    base = escape_full(d0)
    r0 = normalize(base['r'])
    print(f"  baseline ok: {base['ok']}  supp {base['supp']}/{base['nedges']}")
    # reconstruct far hub data (far_seed=1) to know planes
    rng = random.Random(1)
    pt0, nrm = {}, {}
    for h in d0['hubs']:
        if h in (b, c):
            continue
        pt0[h] = rvec3(rng); nrm[h] = rvec3(rng)
    nb = d0['nb']
    far_nonhub = sorted(s for s in d0['V'] if s not in d0['hubs']
                        and s != a and s not in locB and s not in locC)
    rngm = random.Random(31337)
    for x in far_nonhub:
        hn = [t for t in nb[x] if t in d0['hubs']]
        pl = dict(d0['pt'])
        if len(hn) == 1 and hn[0] in pt0:
            pl[x] = in_plane_point(pt0[hn[0]], nrm[hn[0]], rngm)
            kind = f"in-plane({hn[0]})"
        else:
            pl[x] = rvec3(rngm)
            kind = "free"
        res = escape_full({**d0, 'pt': pl})
        if not res['ok']:
            print(f"  move {x} ({kind}): degenerate (skip)")
            continue
        rx = normalize(res['r'])
        print(f"  move {x} ({kind}): [r] changed: {rx != r0}")

if __name__ == '__main__':
    n9a()
    n9b()
