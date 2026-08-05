"""
W5-L7 kernel (K) route-1 gate (2026-07-30): is the escape's (non)vanishing LOCAL?

Fix identical radius-1 local chain data:
    pt(b), normal(b), pt(c), normal(c),
    the two non-a in-plane neighbours of b and of c,
    pt(a)(t) = p0 + t*dir on the meet line Pi(b) ^ Pi(c),
and vary ONLY the far graph:
    (T1) within-habitat far resampling  (H1 = dbl-subdiv K4, far seeds 1,2,3)
    (T2) cross-habitat                  (H4 = dbl-subdiv (K5 - matching), same local block)
then compare, per run:
    - the normalized escape direction [r] at fixed t (projective 6-vector),
    - the sign pattern of E(t) = r.(bhat^chat) over integer t in [-8,8],
    - the bisected zero t* of E(t) (35 iterations, width ~1e-10),
    - the stress support (edges with nonzero stress vector; global circuit?).
Verdict rule: if [r] or t* moves when only far data changes, the escape's
(non)vanishing is NOT a function of the local chain data -> route-1 naive
localization gate FAILS.  If both are far-invariant -> locality supported.
"""
from fractions import Fraction as F
import random, itertools
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
import pencil_escape as pe
from pencil_escape import (double_subdivide, build_rigidity, rank, left_nullspace,
                           wedge2, hat, dot, rvec3, rquat)

# ---------- standalone local-geometry helpers (decoupled from any rng closure) ----------

def plane_basis(n):
    """DEGENERATE SAMPLER — kept verbatim as the record of what was measured.

    Whenever a coordinate of `n` is 0 this returns two PARALLEL in-plane
    directions, so `in_plane_point` samples a LINE rather than the plane.
    That is the defect behind the corrected `widened.py` escape figures
    (`--validate` 11/12, `--sample` 94/96; see the w4 README).  The robust
    successor is `repin.robust_plane_basis`; use that in any new work.
    NOT interchangeable with `kbare_common.plane_basis`, which is the same
    construction cleared of denominators — a different scalar multiple, hence
    different sampled points.  See `notes/scripts/README.md` *Divergences*."""
    basis = []
    for e in ([F(1),F(0),F(0)],[F(0),F(1),F(0)],[F(0),F(0),F(1)]):
        proj = dot(e, n) / dot(n, n)
        d = [e[i] - proj*n[i] for i in range(3)]
        if any(di != 0 for di in d):
            basis.append(d)
        if len(basis) == 2:
            break
    return basis

def in_plane_point(pt0, n, rng):
    bss = plane_basis(n)
    s = rquat(rng); t = rquat(rng)
    return [pt0[i] + s*bss[0][i] + t*bss[1][i] for i in range(3)]

def meet_line(pt_b, n_b, pt_c, n_c):
    """meet line of the two planes: base point p0, direction d."""
    n1, n2 = n_b, n_c
    d = [n1[1]*n2[2]-n1[2]*n2[1], n1[2]*n2[0]-n1[0]*n2[2], n1[0]*n2[1]-n1[1]*n2[0]]
    c1 = dot(n1, pt_b); c2 = dot(n2, pt_c)
    for fc in range(3):
        cols = [k for k in range(3) if k != fc]
        A = [[n1[cols[0]], n1[cols[1]]], [n2[cols[0]], n2[cols[1]]]]
        det = A[0][0]*A[1][1] - A[0][1]*A[1][0]
        if det != 0:
            p0 = [F(0)]*3
            inv = [[A[1][1]/det, -A[0][1]/det], [-A[1][0]/det, A[0][0]/det]]
            p0[cols[0]] = inv[0][0]*c1 + inv[0][1]*c2
            p0[cols[1]] = inv[1][0]*c1 + inv[1][1]*c2
            break
    return p0, d

def sample_local(seed):
    """One radius-1 local block, reused verbatim across all runs."""
    rng = random.Random(seed)
    pt_b = rvec3(rng); n_b = rvec3(rng)
    pt_c = rvec3(rng); n_c = rvec3(rng)
    nbrsB = [in_plane_point(pt_b, n_b, rng) for _ in range(2)]
    nbrsC = [in_plane_point(pt_c, n_c, rng) for _ in range(2)]
    p0, d = meet_line(pt_b, n_b, pt_c, n_c)
    return dict(pt_b=pt_b, n_b=n_b, pt_c=pt_c, n_c=n_c,
                nbrsB=nbrsB, nbrsC=nbrsC, p0=p0, d=d)

# ---------- habitat assembly with a fixed local block ----------

# base graphs: canonical home `pencil_escape` (2026-08-05); re-exported here
# because `n9` / `localtest_zeros` import them from this module.
from pencil_escape import K4, K5_minus_matching   # noqa: E402,F401

def build_cfg(base_edges, chain_idx, local, far_seed):
    """G' = (dbl-subdiv base)^{ab}_v with the given fixed local block and
    far data drawn from far_seed. Returns cfg(t) plus labels."""
    edges, hubs, chains, allverts = double_subdivide(base_edges)
    (u, x, y, w) = chains[chain_idx]
    b, c, a, v = u, w, y, x
    edges2 = [(p, q) for (p, q) in edges if p != v and q != v]
    edges2.append((b, a))
    Vp = sorted(set(itertools.chain.from_iterable(edges2)))
    nb = {vv: set() for vv in Vp}
    for p, q in edges2:
        nb[p].add(q); nb[q].add(p)

    rng = random.Random(far_seed)
    pt0 = {b: local['pt_b'], c: local['pt_c']}
    normal = {b: local['n_b'], c: local['n_c']}
    for h in hubs:
        if h in (b, c):
            continue
        pt0[h] = rvec3(rng); normal[h] = rvec3(rng)

    fixed = {h: pt0[h] for h in hubs}
    locB = sorted(s for s in Vp if s not in hubs and s != a and b in nb[s])
    locC = sorted(s for s in Vp if s not in hubs and s != a and c in nb[s])
    assert len(locB) == 2 and len(locC) == 2, (locB, locC)
    for s, p in zip(locB, local['nbrsB']):
        fixed[s] = p
    for s, p in zip(locC, local['nbrsC']):
        fixed[s] = p
    for s in Vp:
        if s in fixed or s == a:
            continue
        hub_nbrs = [t for t in nb[s] if t in hubs]
        assert len(hub_nbrs) == 1, (s, hub_nbrs)
        fixed[s] = in_plane_point(pt0[hub_nbrs[0]], normal[hub_nbrs[0]], rng)

    p0, d = local['p0'], local['d']
    def cfg(t):
        pt = dict(fixed)
        pt[a] = [p0[i] + t*d[i] for i in range(3)]
        return {'edges': edges2, 'V': Vp, 'pt': pt, 'nb': nb,
                'a': a, 'b': b, 'c': c, 'v': v, 'hubs': hubs}
    return cfg, (a, b, c), locB, locC

# ---------- extended escape evaluation ----------

def escape_full(data):
    """Returns dict: E, r (a-block escape vector), sanity flags, stress support."""
    rows, edge_rows, C, idx, n = build_rigidity(data)
    rk = rank(rows); tgt = 6*(n-1)
    ln = left_nullspace(rows)
    if rk != tgt or len(ln) != 1:
        return {'ok': False, 'rank': rk, 'target': tgt, 'nullity': len(ln)}
    lam = ln[0]
    a, b, c = data['a'], data['b'], data['c']; pt = data['pt']
    def find_edge(p, q):
        for e in edge_rows:
            if set(e) == {p, q}:
                return e
    e_ab = find_edge(a, b); e_ac = find_edge(a, c)
    def block_of(e, vert):
        base = 6*idx[vert]
        acc = [F(0)]*6
        for ri in edge_rows[e]:
            coef = lam[ri]
            for k in range(6):
                acc[k] += coef*rows[ri][base+k]
        return acc
    r = block_of(e_ab, a)
    r_ac = block_of(e_ac, a)
    ahat, bhat, chat = hat(pt[a]), hat(pt[b]), hat(pt[c])
    Cab = wedge2(ahat, bhat); Cac = wedge2(ahat, chat); Cbc = wedge2(bhat, chat)
    # stress support: per-edge 6-vector (at the first endpoint's block)
    supp = 0
    for e in edge_rows:
        vv = block_of(e, e[0])
        if any(x != 0 for x in vv):
            supp += 1
    return {'ok': True, 'rank': rk, 'target': tgt, 'nullity': 1,
            'eq644': all(r[k] + r_ac[k] == 0 for k in range(6)),
            'r_perp_Cab': dot(r, Cab) == 0, 'r_perp_Cac': dot(r, Cac) == 0,
            'r': r, 'E': dot(r, Cbc), 'supp': supp, 'nedges': len(edge_rows)}

def normalize(vec):
    for x in vec:
        if x != 0:
            return [y / x for y in vec]
    return vec

def sweep_and_bisect(cfg, label, tmin=-8, tmax=8, bisect_iters=35):
    print(f"\n--- {label}: integer sweep t in [{tmin},{tmax}] ---")
    vals = []
    for tnum in range(tmin, tmax+1):
        t = F(tnum)
        res = escape_full(cfg(t))
        if not res['ok']:
            print(f"  t={tnum:>3}: DEGENERATE rank={res['rank']}/{res['target']} nul={res['nullity']} (skip)")
            vals.append((t, None))
            continue
        s = '0' if res['E'] == 0 else ('+' if res['E'] > 0 else '-')
        assert res['eq644'] and res['r_perp_Cab'] and res['r_perp_Cac'], "sanity fail"
        vals.append((t, res['E']))
        print(f"  t={tnum:>3}: sign={s}  supp={res['supp']}/{res['nedges']}")
    # brackets
    zeros = []
    valid = [(t, E) for (t, E) in vals if E is not None]
    for (t1, E1), (t2, E2) in zip(valid, valid[1:]):
        if E1 == 0:
            zeros.append(('exact', t1)); continue
        if E1*E2 < 0:
            lo, hi, Elo = t1, t2, E1
            for _ in range(bisect_iters):
                mid = (lo+hi)/2
                res = escape_full(cfg(mid))
                if not res['ok']:
                    print(f"    (bisect hit degenerate at t={float(mid)}; stopping this bracket)")
                    break
                Em = res['E']
                if Em == 0:
                    zeros.append(('exact', mid)); break
                if (Em > 0) == (Elo > 0):
                    lo, Elo = mid, Em
                else:
                    hi = mid
            else:
                zeros.append(('bracket', (lo, hi)))
    for kind, z in zeros:
        if kind == 'exact':
            print(f"  ZERO (exact rational) at t = {z}")
        else:
            lo, hi = z
            print(f"  ZERO bracketed: t* in ({float(lo):.12f}, {float(hi):.12f})")
    if not zeros:
        print("  no sign change in sweep range")
    return zeros

if __name__ == '__main__':
    LOCAL = sample_local(500)
    print("local block: seed 500 (identical across ALL runs below)")

    runs = []
    # T1: within-habitat far resampling (H1)
    for fs in (1, 2, 3):
        cfg, (a, b, c), locB, locC = build_cfg(K4(), 0, LOCAL, far_seed=fs)
        runs.append((f"H1 (dsK4), far seed {fs}", cfg))
    # T2: cross-habitat (H4), same local block
    for fs in (1, 2):
        cfg, (a, b, c), locB, locC = build_cfg(K5_minus_matching(), 0, LOCAL, far_seed=fs)
        runs.append((f"H4 (ds(K5-M)), far seed {fs}", cfg))

    # direction comparison at fixed t = 0 and t = 1
    for tfix in (F(0), F(1)):
        print(f"\n===== [r] direction at fixed t = {tfix} (local data identical everywhere) =====")
        dirs = []
        for label, cfg in runs:
            res = escape_full(cfg(tfix))
            if not res['ok']:
                print(f"  {label:<28} DEGENERATE (rank {res['rank']}/{res['target']}, nul {res['nullity']})")
                dirs.append((label, None)); continue
            nr = normalize(res['r'])
            E = res['E']
            print(f"  {label:<28} E sign={'0' if E==0 else ('+' if E>0 else '-')}  "
                  f"supp={res['supp']}/{res['nedges']}  [r]={[str(x) for x in nr[:3]]}...")
            dirs.append((label, nr))
        base = next((d for _, d in dirs if d is not None), None)
        same = all(d == base for _, d in dirs if d is not None)
        print(f"  -> [r] identical across runs at t={tfix}: {same}")

    # zero-location comparison
    print("\n===== zero-location comparison (sweep + bisect) =====")
    allzeros = {}
    for label, cfg in runs:
        allzeros[label] = sweep_and_bisect(cfg, label)
