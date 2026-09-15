"""Tasks 1 and 2: orbit dimension at representatives of the 19 claimed strata,
and the dimension of each stratum (parameter count + Jacobian of the closed
defining equations at the representative)."""
from fractions import Fraction as F
import random
from common import *

rng = random.Random(20260915)
GENS = lie_generators()

def orbit_dim(x):
    """dim of G-orbit of [x] in P^5 = rank(span{xi.x} + K x) - 1."""
    rows = [matvec(X, x) for (_, X, _) in GENS] + [list(x)]
    return rank(rows) - 1

# --- gradient helpers for the closed defining equations (in the affine cone K^6)
def grad_coord(i):
    def g(x):
        v = [F(0)] * 6
        v[i] = F(1)
        return v
    return g
def grad_Q2(x):
    return [F(0), x[4], -x[3], -x[2], x[1], F(0)]
def grad_Q1_minus_I_Q2(I):
    def g(x):
        return [x[5], -I * x[4], I * x[3], I * x[2], -I * x[1], x[0]]
    return g

def closed_locus_tangent_dim(x, grads):
    """dim of the Zariski tangent space at [x] in P^5 of the closed locus
    cut out by the given equations: 6 - rank(Jacobian) - 1."""
    if not grads:
        return 5
    J = [g(x) for g in grads]
    return 6 - rank(J) - 1

# --- stratum representatives ---------------------------------------------
def rank2_pair():
    while True:
        xu = rand_vec(rng, 2)
        xv = rand_vec(rng, 2)
        if xu[0] * xv[1] - xu[1] * xv[0] != 0:
            return xu, xv

def rank1_pair():
    """x_u, x_v both nonzero and parallel."""
    xu = rand_vec(rng, 2, nonzero=True)
    lam = rand_rat(rng, nonzero=True)
    return xu, [lam * c for c in xu]

def gen_point(I):
    xu, xv = rank2_pair()
    x0 = rand_rat(rng, nonzero=True)
    q2 = xu[0] * xv[1] - xu[1] * xv[0]
    xinf = I * q2 / x0
    return [x0] + xu + xv + [xinf]

def assemble(x0, xu, xv, xinf):
    return [x0] + list(xu) + list(xv) + [xinf]

NZ = lambda: rand_rat(rng, nonzero=True)
Z = lambda: F(0)
zero2 = lambda: [F(0), F(0)]

# name, claimed dim, generator of representative, closed defining-equation gradients, parameter-count string
STRATA = []
for I in (F(2), F(-3), F(1, 2), F(1)):
    STRATA.append((f"Gen(I={I})", 4, (lambda I=I: gen_point(I)), [grad_Q1_minus_I_Q2(I)],
                   "x_u,x_v (4) + x_0 (1), x_inf determined -> cone 5"))
STRATA += [
    ("Z0",       4, lambda: assemble(Z(), *rank2_pair(), NZ()), [grad_coord(0)], "x_u,x_v,x_inf free -> cone 5"),
    ("Zinf",     4, lambda: assemble(NZ(), *rank2_pair(), Z()), [grad_coord(5)], "x_0,x_u,x_v free -> cone 5"),
    ("Z0inf",    3, lambda: assemble(Z(), *rank2_pair(), Z()), [grad_coord(0), grad_coord(5)], "x_u,x_v free -> cone 4"),
    ("R1a-gen",  4, lambda: assemble(NZ(), *rank1_pair(), NZ()), [grad_Q2], "x_u (2) + lambda (1) + x_0,x_inf (2) -> cone 5"),
    ("R1a-0",    3, lambda: assemble(Z(), *rank1_pair(), NZ()), [grad_Q2, grad_coord(0)], "x_u,lambda,x_inf -> cone 4"),
    ("R1a-inf",  3, lambda: assemble(NZ(), *rank1_pair(), Z()), [grad_Q2, grad_coord(5)], "x_u,lambda,x_0 -> cone 4"),
    ("R1a-0inf", 2, lambda: assemble(Z(), *rank1_pair(), Z()), [grad_Q2, grad_coord(0), grad_coord(5)], "x_u,lambda -> cone 3"),
    ("U-gen",    3, lambda: assemble(NZ(), rand_vec(rng, 2, True), zero2(), NZ()), [grad_coord(3), grad_coord(4)], "x_u,x_0,x_inf -> cone 4"),
    ("U-0",      2, lambda: assemble(Z(), rand_vec(rng, 2, True), zero2(), NZ()), [grad_coord(3), grad_coord(4), grad_coord(0)], "x_u,x_inf -> cone 3"),
    ("U-inf",    2, lambda: assemble(NZ(), rand_vec(rng, 2, True), zero2(), Z()), [grad_coord(3), grad_coord(4), grad_coord(5)], "x_u,x_0 -> cone 3"),
    ("Pu",       1, lambda: assemble(Z(), rand_vec(rng, 2, True), zero2(), Z()), [grad_coord(3), grad_coord(4), grad_coord(0), grad_coord(5)], "x_u -> cone 2"),
    ("V-gen",    3, lambda: assemble(NZ(), zero2(), rand_vec(rng, 2, True), NZ()), [grad_coord(1), grad_coord(2)], "x_v,x_0,x_inf -> cone 4"),
    ("V-0",      2, lambda: assemble(Z(), zero2(), rand_vec(rng, 2, True), NZ()), [grad_coord(1), grad_coord(2), grad_coord(0)], "x_v,x_inf -> cone 3"),
    ("V-inf",    2, lambda: assemble(NZ(), zero2(), rand_vec(rng, 2, True), Z()), [grad_coord(1), grad_coord(2), grad_coord(5)], "x_v,x_0 -> cone 3"),
    ("Pv",       1, lambda: assemble(Z(), zero2(), rand_vec(rng, 2, True), Z()), [grad_coord(1), grad_coord(2), grad_coord(0), grad_coord(5)], "x_v -> cone 2"),
    ("Ax",       1, lambda: assemble(NZ(), zero2(), zero2(), NZ()), [grad_coord(i) for i in (1, 2, 3, 4)], "x_0,x_inf -> cone 2"),
    ("Luv",      0, lambda: assemble(F(1), zero2(), zero2(), Z()), [grad_coord(i) for i in (1, 2, 3, 4, 5)], "point -> cone 1"),
    ("ell",      0, lambda: assemble(Z(), zero2(), zero2(), F(1)), [grad_coord(i) for i in (0, 1, 2, 3, 4)], "point -> cone 1"),
]

def check_conditions(name, x):
    """Sanity: representative satisfies the stratum's open+closed conditions."""
    r = rank_uv(x)
    q1, q2 = Q1(x), Q2(x)
    x0, xinf = x[0], x[5]
    xu, xv = x[1:3], x[3:5]
    nzu, nzv = any(c != 0 for c in xu), any(c != 0 for c in xv)
    if name.startswith("Gen"):
        I = F(name[len("Gen(I="):-1])
        return r == 2 and q1 * q2 != 0 and q1 == I * q2
    if name == "Z0":    return r == 2 and x0 == 0 and xinf != 0
    if name == "Zinf":  return r == 2 and xinf == 0 and x0 != 0
    if name == "Z0inf": return r == 2 and x0 == 0 and xinf == 0
    if name.startswith("R1a"):
        ok = r == 1 and nzu and nzv
        if name == "R1a-gen":  return ok and x0 * xinf != 0
        if name == "R1a-0":    return ok and x0 == 0 and xinf != 0
        if name == "R1a-inf":  return ok and xinf == 0 and x0 != 0
        if name == "R1a-0inf": return ok and x0 == 0 and xinf == 0
    if name.startswith("U") or name == "Pu":
        ok = nzu and not nzv
        if name == "U-gen": return ok and x0 * xinf != 0
        if name == "U-0":   return ok and x0 == 0 and xinf != 0
        if name == "U-inf": return ok and xinf == 0 and x0 != 0
        if name == "Pu":    return ok and x0 == 0 and xinf == 0
    if name.startswith("V") or name == "Pv":
        ok = nzv and not nzu
        if name == "V-gen": return ok and x0 * xinf != 0
        if name == "V-0":   return ok and x0 == 0 and xinf != 0
        if name == "V-inf": return ok and xinf == 0 and x0 != 0
        if name == "Pv":    return ok and x0 == 0 and xinf == 0
    if name == "Ax":  return not nzu and not nzv and x0 * xinf != 0
    if name == "Luv": return x == [F(1), F(0), F(0), F(0), F(0), F(0)]
    if name == "ell": return x == [F(0), F(0), F(0), F(0), F(0), F(1)]
    raise ValueError(name)

NREP = 3
print(f"{'stratum':<12} {'claimed':>7} {'orbit dims (per rep)':<22} {'tangent dim of closed locus':>28} {'param count':>12}  flag")
mismatches = []
for name, claimed, mk, grads, pcount in STRATA:
    odims, tdims = [], []
    for k in range(NREP):
        x = mk()
        assert check_conditions(name, x), (name, x)
        odims.append(orbit_dim(x))
        tdims.append(closed_locus_tangent_dim(x, grads))
    cone = int(pcount.split("cone")[1])
    pdim = cone - 1
    flag = ""
    if any(d != claimed for d in odims): flag += " ORBIT-MISMATCH"
    if any(d != claimed for d in tdims): flag += " TANGENT-MISMATCH"
    if pdim != claimed: flag += " PARAM-MISMATCH"
    if flag: mismatches.append(name)
    print(f"{name:<12} {claimed:>7} {str(odims):<22} {str(tdims):>28} {pdim:>12} {flag}")

print()
print("representatives used (re-generated with the same seed):")
rng = random.Random(20260915)
for name, claimed, mk, grads, pcount in STRATA:
    reps = [mk() for _ in range(NREP)]
    print(f"  {name:<12}", "; ".join(fmt(x) for x in reps))
print()
print("mismatches:", mismatches if mismatches else "none")
