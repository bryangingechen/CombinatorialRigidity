"""Zero-location comparison for the route-1 locality gate: with the SAME local
block (seed 500), sweep t and bisect the zero t* of E(t) per far placement.
Faster evaluator: one rref (left nullspace) per eval; rank derived from nullity."""
from fractions import Fraction as F
from localtest import (sample_local, build_cfg, K4, K5_minus_matching)
from pencil_escape import build_rigidity, left_nullspace, wedge2, hat, dot

def escape_E(data):
    rows, edge_rows, C, idx, n = build_rigidity(data)
    ln = left_nullspace(rows)
    nullity = len(ln)
    rk = len(rows) - nullity
    tgt = 6*(n-1)
    if rk != tgt or nullity != 1:
        return None, rk, nullity
    lam = ln[0]
    a, b, c = data['a'], data['b'], data['c']; pt = data['pt']
    e_ab = next(e for e in edge_rows if set(e) == {a, b})
    base = 6*idx[a]
    r = [F(0)]*6
    for ri in edge_rows[e_ab]:
        coef = lam[ri]
        for k in range(6):
            r[k] += coef*rows[ri][base+k]
    return dot(r, wedge2(hat(pt[b]), hat(pt[c]))), rk, nullity

def sweep(cfg, label, tmin=-6, tmax=6, iters=28):
    print(f"\n--- {label} ---", flush=True)
    vals = []
    for tn in range(tmin, tmax+1):
        E, rk, nul = escape_E(cfg(F(tn)))
        s = 'DEG' if E is None else ('0' if E == 0 else ('+' if E > 0 else '-'))
        vals.append((F(tn), E))
        print(f"  t={tn:>3}: {s}", flush=True)
    valid = [(t, E) for t, E in vals if E is not None]
    zeros = []
    for (t1, E1), (t2, E2) in zip(valid, valid[1:]):
        if E1 == 0:
            zeros.append(t1); print(f"  exact zero at t={t1}")
            continue
        if E1*E2 < 0:
            lo, hi, Elo = t1, t2, E1
            for _ in range(iters):
                mid = (lo+hi)/2
                Em, rk, nul = escape_E(cfg(mid))
                if Em is None:
                    print(f"    degenerate at t={float(mid)}; abandoning bracket")
                    break
                if Em == 0:
                    zeros.append(mid); print(f"  exact zero at t={mid}")
                    break
                if (Em > 0) == (Elo > 0):
                    lo, Elo = mid, Em
                else:
                    hi = mid
            else:
                zeros.append((lo+hi)/2)
                print(f"  zero t* in ({float(lo):.10f}, {float(hi):.10f})")
    if not zeros:
        print("  NO sign change in sweep range")
    return zeros

if __name__ == '__main__':
    LOCAL = sample_local(500)
    out = {}
    for label, base, ci, fs in [("H1 far1", K4(), 0, 1),
                                ("H1 far2", K4(), 0, 2),
                                ("H4 far1", K5_minus_matching(), 0, 1)]:
        cfg, _, _, _ = build_cfg(base, ci, LOCAL, far_seed=fs)
        out[label] = sweep(cfg, label)
    print("\n===== SUMMARY (identical local block, seed 500) =====")
    for k, v in out.items():
        print(f"  {k}: zeros at t* ~ {[float(z) for z in v]}")
