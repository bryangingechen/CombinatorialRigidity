"""§(K-grid) direction GODDRUNG (2026-09-12) driver -- IS THE CORPUS'S ONE
CORRELATED COLOURING RULE (the rung-minority rule of §(K-grid) (GR-34)(ii))
PARITY-FRAGILE, OR IS IT REPAIRABLE AT ODD RUNG LENGTHS?  §8's seventeenth
pass, rank 2.

THE SETTING.  §(K-grid) (GR-239)(ii) measured `gexist.ladder_rule_first`
INADMISSIBLE at (GR-175)'s recipe (six length-3 rungs on `CL_m`) at
`m = 6, 8, 10, 12`, and attributed the failure to PARITY: "a length-L branch
flips its dart colour `L - 1` times, so a rung can be its hub's minority dart
at BOTH ends only when `L` is even."  That derivation is correct about the
LANDED IMPLEMENTATION and WRONG about the rule as (GR-37)(ii) models it.

THE FRAME THAT SUBSUMES IT.  §(K-grid) (GR-37)(i) is the `(c, m)` model:
admissible colourings <-> pairs (majority colours `c`, minority darts `m`)
with, per branch `β = (u, w)`,

    c(u) ⊕ c(w) = [ℓ_β even] ⊕ [m(u) on β] ⊕ [m(w) on β],

plus odd-branch balance.  (GR-37)(ii): for the all-`M` prescription the two
minority indicators cancel, so the right-hand side is `t := [ℓ even]` and the
rule extends **iff `t` lies in the cut space of `G°`**.  The rung-minority
rule IS the all-`M` prescription at `M` = the rung matching -- so its
admissibility is a CUT-SPACE MEMBERSHIP question about the length vector, and
"odd rung length" is one special case of it, not the criterion.  This driver
computes the criterion, exhibits the repair, and prices it.

THE INVARIANT THIS DRIVER INTRODUCES: the RUNG DEFECT

    ρ(ℓ) := min over admissible (c, m) of #{hubs v : m(v) ≠ v's rung dart},

i.e. how far from the pure rung-minority rule the nearest admissible
colouring is.  `--rho` proves the closed form

    ρ(ℓ) = k + 2·[k = 0 and τ = 1],   k := #{j : φ_j = 1},

where, writing `t(β) = [ℓ_β even]` on the `3m` branches of `CL_m`,

    φ_j := t(top_j) ⊕ t(bot_j) ⊕ t(rung_j) ⊕ t(rung_{j+1})     (face j)
    τ   := Σ_j t(top_j)  mod 2                                  (top rim)

-- the pairing of `t` against the `m + 1` cycle-space generators of `CL_m`
(`m` square faces + one rim) -- and `--rho` checks it against a BRUTE-FORCE
minimisation over all `3^{2m}` deviation configurations at `m = 4..7`
(62 (m, excess) pairs), and then against an EXHAUSTIVE enumeration of all
`2^{3m}` colourings through the canonical `cflank.admissible` at `m = 4..6`
(43 profiles) -- the second of those is the one that carries the ODD-BRANCH
BALANCE rider, which the first does not.

WHAT IT IMPORTS READ-ONLY (README §2): `gexist` (`ladder_specs`,
`ladder_rule_first`, `fully_good_rank`, `interval_chunks`), `cflank`
(`admissible`, `nc1_violations`, `hub_model`, `private_even`,
`one_admissible`), `gunif` (`wit_colouring`), `gridcol` (`subdivide`,
`class_shape`).  NO landed function is reimplemented: the repaired rule is a
new CONSTRUCTION fed to the canonical detectors.

Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --cut     # the cut-space criterion on both ladder recipes; the landed rule's failure LOCATED -- (GR-249)/(GR-250)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --rho     # the rung-defect closed form vs BRUTE FORCE at m = 4..9 -- (GR-251)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --repair --hi 40 --rank-hi 40  # THE REPAIRED RULE: explicit, correlated, admissible + NC1 + exact-Q dim Z = 0 at (GR-175)'s recipe, to n_hub = 80 -- (GR-252)/(GR-253)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --far     # the ADMISSIBILITY half alone, off the branch decomposition -- (GR-253)(ii)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --save    # what the repair COSTS: the `save = 0 on all intervals` property of (GR-34)(ii) -- (GR-254)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --oddm    # (GR-34)(ii)'s undeveloped "odd m needs ONE deviating hub", tested -- (GR-255)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --consumer  # F26: what a UNIFORM rule on a base subfamily actually buys -- (GR-256)
    PYTHONHASHSEED=0 python3 notes/scripts/w4/goddrung.py --validate  # all of the above

SEEDS AND CAPS, disclosed per mode.  The cut-space/rung-defect legs are
EXACT GF(2) linear algebra over a finite basis -- no sampler, no cap, and an
exhaustive brute-force cross-check at `m <= 9` (`2^{2m}` deviation sets).
The `--repair` leg's admissibility and NC1 verdicts are EXACT combinatorial
predicates (`cflank.admissible`, `cflank.nc1_violations`) and carry no cap in
either direction.  Only `fully_good_rank` is draw-decided: a True there is an
EXHIBITED exact-Q `dim Z = 0` certificate (a proof, cap-free); a False is
"no vanishing draw found in 6 draws per block", never "does not exist".
The one search cap is `search_repair(cap=200000)`: the balance knob set is
enumerated EXHAUSTIVELY when `4^k <= cap` and sampled (seeded) above it, and
every row reports which.  `--repair` does NOT call `cflank.cubic_habitat`
(a `2^{n_hub}` scan): (GR-175) PROVES the shape property for every `m >= 6`,
and `cflank.admissible` / `gexist.fully_good_rank` read only `hm['hubs']` and
`hm['branches']`, so neither needs `cflank.hub_model`'s simple-cycle
enumeration either.  That is why this driver reaches `n_hub = 80` where
GBASE's ladder leg stopped at 24.  `gridcol.class_shape` is a redundant
spot-check (it is the slowest thing here) and runs only to `--shape-hi`;
`cflank.nc1_violations` DOES need the cycles and is fenced at `n_hub = 24`.
"""

import argparse
import sys
import time

sys.path.insert(0, __file__.rsplit('/', 1)[0])

import cflank                                                 # noqa: E402
import gexist                                                 # noqa: E402
import gridcol                                                # noqa: E402
from gunif import wit_colouring                               # noqa: E402

# The seed for the one sampled comparison in --repair (the search fallback
# GBASE's ladder leg uses); every other figure in this driver is exact.
D_SEED = 20260912


# ---------------------------------------------------------------------------
# The ladder's branch indexing, matching `gexist.ladder_specs` EXACTLY.
#   branch  i        (0 <= i < m):  top rim   (i, i+1)
#   branch  m + i             :  bottom rim (m+i, m+i+1)
#   branch  2m + i            :  rung       (i, m+i)
# Hubs: top hub i = i, bottom hub i = m + i.
# ---------------------------------------------------------------------------

def top_rim(m, j):
    return j % m


def bot_rim(m, j):
    return m + (j % m)


def rung(m, j):
    return 2 * m + (j % m)


def face(m, j):
    """The `j`-th square face of `CL_m` as a branch-index set: the two rims
    `j` and the two rungs `j`, `j+1`.  The `m` faces plus the top rim cycle
    are a basis of the cycle space (dim = 3m - 2m + 1 = m + 1)."""
    return (top_rim(m, j), bot_rim(m, j), rung(m, j), rung(m, j + 1))


def cycle_pairings(m, lens):
    """`(phi, tau)`: the pairing of `t = [ℓ even]` against the cycle-space
    basis.  `phi[j] = t · F_j`, `tau = t · (top rim)`.  `t ∈ Cut(CL_m)` iff
    `phi == 0` and `tau == 0` (a vector is a cut iff it is orthogonal to the
    cycle space -- (GR-37)(ii)'s criterion, evaluated)."""
    t = [1 if L % 2 == 0 else 0 for L in lens]
    phi = [sum(t[b] for b in face(m, j)) % 2 for j in range(m)]
    tau = sum(t[top_rim(m, j)] for j in range(m)) % 2
    return phi, tau


def rho_closed(m, lens):
    """The closed form for the rung defect: `k + 2·[k = 0 and tau = 1]`.
    Derivation (verified exhaustively by `--rho`): a deviation at hub `top_i`
    or `bot_i` re-points that hub's minority from the rung to one of its two
    rim darts, shifting the system's right-hand side by
    `e_{rung_i} + e_{that rim}`; pairing that shift against the basis gives
    EXACTLY ONE face flip (`F_{i-1}` for the forward rim edge, `F_i` for the
    backward one) plus a `tau` flip iff the hub is on the TOP rim.  So `k`
    deviations are necessary (one per face that must flip) and sufficient
    when the top/bottom split can be chosen with the right parity, which
    needs `k >= 1` when `tau = 1`; when `k = 0` and `tau = 1` one deviation
    is impossible (it always flips a face) and two suffice."""
    phi, tau = cycle_pairings(m, lens)
    k = sum(phi)
    return k + (2 if (k == 0 and tau == 1) else 0), k, tau


# ---------------------------------------------------------------------------
# The repaired rule: an EXPLICIT deviation set, then `c` solved over GF(2).
# ---------------------------------------------------------------------------

def deviation_set(m, lens, choices):
    """The repaired rule's deviating hubs, as a dict hub -> branch index of
    the NEW minority dart (a rim dart).  Face `j` must be served by ONE hub
    re-pointed onto a rim: from hub `j+1` with its FORWARD rim dart, or from
    hub `j` with its BACKWARD rim dart -- those are the only two single-hub
    moves whose cycle-space shift is exactly `F_j` and nothing else.  Each
    can be taken on the TOP rim or the BOTTOM rim, and a TOP one additionally
    flips `tau`, so `#top` must match `tau`'s parity.

    `choices[idx] in {0,1,2,3}` picks (hub j+1 / hub j) x (bottom / top) for
    the `idx`-th face needing a flip.  Returns None when two faces collide on
    one hub (a hub has ONE minority dart) or the `tau` parity is unmet."""
    phi, tau = cycle_pairings(m, lens)
    faces = [j for j in range(m) if phi[j]]
    if not faces:
        if tau == 0:
            return {}
        # k = 0, tau = 1: the neutral TOP/BOTTOM pair at one rung -- two
        # deviations whose face flips cancel and whose tau flips do not.
        return {0: top_rim(m, 0), m: bot_rim(m, 0)}
    assert len(choices) == len(faces), "one choice per face needing a flip"
    if sum(1 for ch in choices if ch & 2) % 2 != tau:
        return None
    dev = {}
    for idx, j in enumerate(faces):
        ch = choices[idx]
        i = j if (ch & 1) else (j + 1) % m
        back = bool(ch & 1)
        if ch & 2:                                  # TOP rim
            hub, br = i, (top_rim(m, i - 1) if back else top_rim(m, i))
        else:                                       # BOTTOM rim
            hub, br = m + i, (bot_rim(m, i - 1) if back else bot_rim(m, i))
        if hub in dev:
            return None
        dev[hub] = br
    return dev


def minority_map(m, dev):
    """hub -> branch index of its minority dart: the rung everywhere except
    at the deviating hubs."""
    mm = {}
    for i in range(m):
        mm[i] = rung(m, i)
        mm[m + i] = rung(m, i)
    mm.update(dev)
    return mm


def solve_colours(m, specs, mm):
    """Solve `c(u) ⊕ c(w) = [ℓ_β even] ⊕ [m(u) on β] ⊕ [m(w) on β]` over the
    hub graph by BFS from hub 0.  Returns `c` (hub -> 0/1) or None if the
    system is inconsistent -- which, by (GR-37)(ii), happens exactly when the
    right-hand side is outside the cut space."""
    inc = {v: [] for v in range(2 * m)}
    for b, (u, w, _L) in enumerate(specs):
        inc[u].append(b)
        inc[w].append(b)
    rhs = []
    for b, (u, w, L) in enumerate(specs):
        rhs.append((1 if L % 2 == 0 else 0)
                   ^ (1 if mm[u] == b else 0) ^ (1 if mm[w] == b else 0))
    c = {0: 0}
    stack = [0]
    while stack:
        v = stack.pop()
        for b in inc[v]:
            (u, w, _L) = specs[b]
            o = w if u == v else u
            val = c[v] ^ rhs[b]
            if o in c:
                if c[o] != val:
                    return None
            else:
                c[o] = val
                stack.append(o)
    assert len(c) == 2 * m, "hub graph not connected"
    return c


def first_darts(m, specs, mm, c, flip_global=False):
    """The `first` array `gunif.wit_colouring` consumes: branch `b`'s dart
    colour at its `u` end.  A hub's minority dart carries `¬c(v)`, its two
    majority darts `c(v)`.  Asserts the `w`-end dart the alternation produces
    agrees with `c(w)`/`m(w)` -- i.e. that the branch equation really holds,
    so a mis-solved `c` cannot pass silently."""
    off = 1 if flip_global else 0
    first = []
    for b, (u, w, L) in enumerate(specs):
        du = (c[u] ^ off) ^ (1 if mm[u] == b else 0)
        dw_expect = (c[w] ^ off) ^ (1 if mm[w] == b else 0)
        assert (du ^ ((L - 1) % 2)) == dw_expect, \
            f"branch {b} equation violated: the (c, m) pair is inconsistent"
        first.append('A' if du == 0 else 'B')
    return first


def repaired_colouring(m, exc, choices, extra=None, flip_global=False):
    """The full repaired-rule colouring of `CL_m` at excess `exc`.  `choices`
    is `deviation_set`'s per-face knob; `extra`, when given, is a position `i`
    at which BOTH `top_i` and `bot_i` additionally deviate onto their forward
    rims -- a NEUTRAL pair (its two face flips cancel) that costs 2 more
    deviations and buys a different `c`, hence a different odd-branch split.
    That pair is the only balance knob the cut space does not already fix."""
    specs = gexist.ladder_specs(m, exc)
    lens = [L for (_u, _w, L) in specs]
    dev = deviation_set(m, lens, choices)
    if dev is None:
        return None
    if extra is not None:
        if extra in dev or m + extra in dev:
            return None
        dev = dict(dev)
        dev[extra] = top_rim(m, extra)
        dev[m + extra] = bot_rim(m, extra)
    mm = minority_map(m, dev)
    c = solve_colours(m, specs, mm)
    if c is None:
        return None
    first = first_darts(m, specs, mm, c, flip_global)
    return dict(specs=specs, lens=lens, dev=dev, mm=mm, c=c,
                col=wit_colouring(specs, first), first=first)


def search_repair(m, exc, cap=200000, seed=None, allow_extra=True,
                  light=False):
    """The repaired rule WITH the odd-branch balance rider.  `cflank.
    admissible` demands `#A edges == #B edges`, which on an alternating
    colouring is exactly `#(odd branches coloured A) == #(odd branches
    coloured B)` -- (GR-37)(i)'s balance clause, and the one (GR-37)(iii)'s
    SECOND CAVEAT records as NOT delivered by the class-level span argument.

    The cut space fixes the parity half and leaves a FINITE knob set: per
    face needing a flip, which of its two serving hubs and which rim (4
    ways), plus the global A<->B swap, plus -- only if those fail -- one
    neutral TOP/BOTTOM pair costing 2 extra deviations.  Exhaustive when
    `4^k <= cap`; otherwise a seeded uniform sample of `cap` choice vectors,
    and the cap is REPORTED with the verdict (a miss is then "no balanced
    repair found under cap", never "none exists")."""
    import random
    specs = gexist.ladder_specs(m, exc)
    lens = [L for (_u, _w, L) in specs]
    phi, tau = cycle_pairings(m, lens)
    faces = [j for j in range(m) if phi[j]]
    k = len(faces)
    edges, allv, hm = shape_model(specs, light=light)
    space = 4 ** k
    exhaustive = space <= cap
    rng = random.Random(D_SEED if seed is None else seed)

    def vectors():
        if exhaustive:
            for n in range(space):
                yield tuple((n >> (2 * i)) & 3 for i in range(k))
        else:
            for _ in range(cap):
                yield tuple(rng.randrange(4) for _ in range(k))

    for extra in ([None] + list(range(m)) if allow_extra else [None]):
        tried = 0
        for ch in vectors():
            for fg in (False, True):
                tried += 1
                r = repaired_colouring(m, exc, ch, extra=extra,
                                       flip_global=fg)
                if r is None:
                    continue
                if cflank.admissible(edges, allv, hm, r['col']):
                    r.update(choices=ch, extra=extra, flip_global=fg,
                             tried=tried, exhaustive=exhaustive, cap=cap,
                             edges=edges, allv=allv, hm=hm, k=k, tau=tau)
                    return r
        if not allow_extra:
            break
    return dict(fail=True, k=k, tau=tau, exhaustive=exhaustive, cap=cap,
                edges=edges, allv=allv, hm=hm, specs=specs, lens=lens)


_SHAPE_CACHE = {}


def shape_model(specs, light=False):
    """`(edges, allverts, hub_model)` for a spec list, cached: the SHAPE does
    not change as the repair's knobs move, only the colouring does, so the
    (expensive) `cflank.hub_model` cycle enumeration is built once.
    `light=True` substitutes `light_model` -- the same hub list from the same
    canonical primitive, without the simple-cycle enumeration; enough for
    `cflank.admissible`, not for `cflank.nc1_violations`."""
    key = (tuple(specs), light)
    if key not in _SHAPE_CACHE:
        edges = gridcol.subdivide(specs)
        allv = sorted(_verts(edges), key=str)
        _SHAPE_CACHE[key] = (edges, allv,
                             light_model(edges) if light
                             else cflank.hub_model(edges))
    return _SHAPE_CACHE[key]


def _verts(edges):
    s = set()
    for (a, b) in edges:
        s.add(a)
        s.add(b)
    return s


# ---------------------------------------------------------------------------
# The two ladder recipes the corpus carries (GBASE's own `leg_ladder` list).
# ---------------------------------------------------------------------------

def recipe_gr34(m):
    """(GR-34): excess 2+2+2 on three ADJACENT rungs -- rungs at ℓ = 4, 4, 4
    and every other branch at ℓ = 2.  ALL LENGTHS EVEN."""
    return {0: 2, 1: 2, 2: 2}


def recipe_gr175(m):
    """(GR-175): six length-3 rungs, evenly spread `i*m//6` -- GBASE's own
    choice of positions, reproduced so the comparison is like-for-like."""
    return {i * m // 6: 1 for i in range(6)}


RECIPES = (("(GR-34)  2+2+2 on three ADJACENT rungs", recipe_gr34),
           ("(GR-175) six length-3 rungs, i*m//6", recipe_gr175))


# ---------------------------------------------------------------------------
# [GOD-1] --cut: the cut-space criterion, and WHERE the landed rule fails
# ---------------------------------------------------------------------------

def leg_cut(hi=20):
    """[GOD-1] (GR-249)/(GR-250).  Evaluates (GR-37)(ii)'s criterion on both
    ladder recipes and, independently, runs the LANDED `ladder_rule_first`
    colouring through `cflank.admissible` so the two are compared on the
    same shapes.  Exact; no sampler, no cap."""
    print("[GOD-1] (GR-37)(ii)'s cut-space criterion on the two ladder "
          "recipes -- EXACT, no cap")
    print("        t := [ell even]; t in Cut(CL_m) iff phi == 0 and tau == 0")
    for (name, mk) in RECIPES:
        print(f"  {name}")
        for m in range(6, hi + 1, 2):
            exc = mk(m)
            specs = gexist.ladder_specs(m, exc)
            lens = [L for (_u, _w, L) in specs]
            phi, tau = cycle_pairings(m, lens)
            k = sum(phi)
            incut = (k == 0 and tau == 0)
            odd = sorted(i for i in range(m) if lens[rung(m, i)] % 2)
            arcs = _arcs(m, odd)
            # the landed rule, on the same shape
            landed = None
            if m % 2 == 0:
                edges, allv, hm = shape_model(specs)
                lc = wit_colouring(specs, gexist.ladder_rule_first(m, specs))
                landed = cflank.admissible(edges, allv, hm, lc)
            print(f"    m = {m:2d} (n_hub = {2*m:2d}): odd rungs = {odd} "
                  f"({len(arcs)} cyclic arc(s)); phi-weight k = {k}, "
                  f"tau = {tau}; t in Cut = {incut}; "
                  f"LANDED ladder_rule_first admissible = {landed}")
    print("  => the criterion is CUT-SPACE MEMBERSHIP of the length vector, "
          "not 'every rung length even': at (GR-175)'s recipe with m = 6 "
          "(ALL SIX rungs odd) the obstruction VANISHES (k = 0, tau = 0) "
          "while the landed rule is still inadmissible there.")


def _arcs(m, S):
    """The cyclic arcs (maximal runs of consecutive positions) of `S` in
    `Z_m`; `[]` for the empty set, one arc for all of `Z_m`."""
    if not S or len(S) == m:
        return [] if not S else [tuple(range(m))]
    ss = set(S)
    out = []
    for s in sorted(ss):
        if (s - 1) % m in ss:
            continue
        run, t = [], s
        while t % m in ss:
            run.append(t % m)
            t += 1
        out.append(tuple(run))
    return out


# ---------------------------------------------------------------------------
# [GOD-2] --rho: the rung defect's closed form vs BRUTE FORCE
# ---------------------------------------------------------------------------

def leg_rho(hi=9):
    """[GOD-2] (GR-251).  `rho_closed` against an EXHAUSTIVE minimisation
    over all `2^{2m}` deviation-set/rim-choice configurations, at every
    excess profile in a fixed sweep.  Exhaustive at this range, so a match
    here is a PROOF of the closed form on the tested shapes, not a bound."""
    print("[GOD-2] (GR-251) the rung defect rho(ell): closed form vs "
          "BRUTE FORCE over all deviation sets -- EXHAUSTIVE, no cap")
    tested = 0
    for m in range(4, hi + 1):
        for exc in _exc_sweep(m):
            specs = gexist.ladder_specs(m, exc)
            lens = [L for (_u, _w, L) in specs]
            pred, k, tau = rho_closed(m, lens)
            brute = _rho_brute(m, specs, lens)
            assert pred == brute, \
                f"closed form {pred} != brute {brute} at m = {m}, exc = {exc}"
            tested += 1
        print(f"  m = {m}: {len(_exc_sweep(m))} excess profiles, "
              f"closed form == brute force at EVERY one")
    print(f"  => rho(ell) = k + 2*[k = 0 and tau = 1] verified exhaustively "
          f"at {tested} (m, excess) pairs, m = 4..{hi}")
    print("  SCOPE, stated because the brute force above tests exactly this "
          "and not more: `solve_colours` decides the BRANCH EQUATIONS of "
          "(GR-37)(i) -- the parity half.  The ODD-BRANCH BALANCE rider is "
          "NOT part of it ((GR-37)(iii)'s second caveat: balance is not a "
          "class function).  The cross-check below carries it.")
    leg_rho_admissible(min(hi, 6))


def leg_rho_admissible(hi=6):
    """[GOD-2b] The balance-carrying cross-check: `rho_adm(ell)` := the min,
    over colourings that pass `cflank.admissible` ITSELF (balance and the
    forest conditions included), of the number of hubs whose minority dart is
    not the rung.  Enumerated over ALL `2^{3m}` dart assignments -- exhaustive,
    so a match with `rho_closed` is a PROOF that the balance rider costs
    nothing on the tested shapes, and a gap would be the rider biting."""
    print("[GOD-2b] (GR-251)(ii) the balance-carrying cross-check: "
          f"rho_adm vs rho_closed, EXHAUSTIVE over all 2^(3m) colourings, "
          f"m = 4..{hi}")
    gaps, none_ct = [], 0
    for m in range(4, hi + 1):
        for exc in _exc_sweep(m):
            specs = gexist.ladder_specs(m, exc)
            lens = [L for (_u, _w, L) in specs]
            pred, _k, _t = rho_closed(m, lens)
            adm = _rho_admissible(m, specs)
            nodd = sum(1 for L in lens if L % 2)
            if adm is None:
                # balance needs an EVEN number of odd branches, split evenly
                assert nodd % 2 == 1, \
                    f"no admissible colouring but {nodd} odd branches"
                none_ct += 1
                continue
            if adm != pred:
                gaps.append((m, dict(exc), pred, adm))
                print(f"    m = {m}, exc = {exc}: rho_closed = {pred}, "
                      f"rho_adm = {adm}   <-- BALANCE RIDER: +{adm - pred}")
        print(f"  m = {m}: {len(_exc_sweep(m))} excess profiles checked "
              f"against the full `cflank.admissible` predicate "
              f"({none_ct} with NO admissible colouring at all -- every one "
              f"of them has an ODD number of odd branches, so balance is "
              f"unsatisfiable and the shape is not a habitat shape)")
        none_ct = 0
    print(f"  => the balance rider costs {len(gaps)} extra deviation(s) "
          f"anywhere in the sweep: {gaps if gaps else 'NONE -- rho_adm == '
          'rho_closed at every profile with an admissible colouring'}")


def _rho_admissible(m, specs):
    """Exhaustive over all `2^{3m}` first-dart assignments: the least number
    of hubs whose minority dart is not its rung, over colourings passing
    `cflank.admissible`.  Returns None when the shape has no admissible
    colouring at all."""
    edges, allv, hm = shape_model(specs)
    best = None
    M = len(specs)
    inc = {v: [] for v in range(2 * m)}
    for b, (u, w, _L) in enumerate(specs):
        inc[u].append(b)
        inc[w].append(b)
    for bits in range(1 << M):
        first = ['A' if bits >> b & 1 == 0 else 'B' for b in range(M)]
        col = wit_colouring(specs, first)
        if not cflank.admissible(edges, allv, hm, col):
            continue
        off = 0
        for v in range(2 * m):
            darts = []
            for b in inc[v]:
                (u, _w, L) = specs[b]
                darts.append(first[b] if u == v
                             else ('A' if (first[b] == 'A') ^ ((L - 1) % 2)
                                   else 'B'))
            mino = [b for j, b in enumerate(inc[v])
                    if darts.count(darts[j]) == 1]
            assert len(mino) == 1, "non-2-1 hub passed `admissible`"
            if mino[0] != rung(m, v % m):
                off += 1
        if best is None or off < best:
            best = off
            if best == 0:
                break
    return best


def _exc_sweep(m):
    """A fixed sweep of excess profiles on the rungs: the empty one, single
    rungs at +1 and +2, adjacent pairs/triples, the evenly-spread six, and
    all-odd.  Deterministic, no randomness."""
    out = [{}]
    for i in range(m):
        out.append({i: 1})
        out.append({i: 2})
    out.append({0: 2, 1: 2, 2: 2})
    out.append({0: 1, 1: 1})
    out.append({i: 1 for i in range(m)})
    if m >= 6:
        out.append({i * m // 6: 1 for i in range(6)})
    return out


def _rho_brute(m, specs, lens):
    """Exhaustive: over all `2^{2m}` subsets of hubs to deviate and, for each
    deviating hub, both rim choices, the least |D| for which the system is
    consistent.  Consistency is decided by `solve_colours` -- the same solver
    the construction uses -- so this is an independent check of the COUNT,
    not of the solver."""
    best = None
    for size in range(0, 2 * m + 1):
        for D in _subsets(range(2 * m), size):
            for choice in range(1 << size):
                dev = {}
                for idx, hub in enumerate(D):
                    i = hub % m
                    fwd = choice >> idx & 1
                    if hub < m:
                        dev[hub] = top_rim(m, i) if fwd else top_rim(m, i - 1)
                    else:
                        dev[hub] = bot_rim(m, i) if fwd else bot_rim(m, i - 1)
                if solve_colours(m, specs, minority_map(m, dev)) is not None:
                    return size
        if best is not None:
            return best
    return None


def _subsets(pool, size):
    from itertools import combinations
    return combinations(pool, size)


# ---------------------------------------------------------------------------
# [GOD-3] --repair: THE REPAIRED RULE at (GR-175)'s recipe
# ---------------------------------------------------------------------------

def leg_repair(hi=12, rank_hi=12, nc1_hi=12, shape_hi=6):
    """[GOD-3] (GR-252)/(GR-253).  The repaired rule built from the cut-space
    criterion (no search over colourings; only the finite balance knob) and
    run through the canonical detectors: `gridcol.class_shape` (a PER-SHAPE
    habitat certification -- NOT the `2^{n_hub}` `cflank.cubic_habitat`
    scan), `cflank.admissible`, `cflank.nc1_violations`,
    `gexist.fully_good_rank`.

    CAPS.  Admissibility and NC1 are exact predicates on a GIVEN colouring,
    cap-free in both directions.  The knob search is exhaustive when
    `4^k <= cap` and a seeded `cap`-sample otherwise -- reported per row, so
    a miss reads "no balanced repair found under cap", never "none exists".
    `fully_good_rank` True is an exhibited exact-Q witness (a proof); False
    would be "no vanishing draw in 6 per block"."""
    import random
    rng = random.Random(D_SEED)
    print(f"[GOD-3] (GR-252)/(GR-253) THE REPAIRED RULE at (GR-175)'s "
          f"recipe (seed {D_SEED})")
    for m in range(6, hi + 1, 2):
        t0 = time.time()
        exc = recipe_gr175(m)
        r = search_repair(m, exc, light=(m > nc1_hi))
        pred, k, tau = rho_closed(m, [L for (_u, _w, L) in
                                      gexist.ladder_specs(m, exc)])
        if r.get('fail'):
            how = ('EXHAUSTIVE over the whole knob set'
                   if r['exhaustive'] else
                   f"capped at {r['cap']} sampled choice vectors")
            print(f"  m = {m:2d} (n_hub = {2*m:2d}): rho = {pred} "
                  f"(k = {k}, tau = {tau}); NO balanced repair found "
                  f"({how})  [{time.time() - t0:.1f}s]")
            continue
        edges, allv, hm = r['edges'], r['allv'], r['hm']
        # NC1 needs the circuit list (`cflank.hub_model`'s simple-cycle
        # enumeration); `fully_good_rank` and `admissible` do NOT -- they
        # read only `hm['hubs']` and `hm['branches']`, which `light_model`
        # supplies.  So the exact-Q certificate is NOT fenced at n_hub = 24.
        nc1 = (not cflank.nc1_violations(hm, r['col'], edges, allv)
               if m <= nc1_hi else None)
        # `gridcol.class_shape` is a REDUNDANT spot-check here -- (GR-175)
        # PROVES `CL_m` with six length-3 rungs is a `D = 0` tight class
        # shape for every `m >= 6` -- and it is the slowest thing in this
        # driver (21 s at n_hub = 12, exponential above), so it is run only
        # to `shape_hi` and reported as `None` above it.
        shape = (gridcol.class_shape(r['specs']) is not None
                 if m <= shape_hi else None)
        fg = (gexist.fully_good_rank(edges, allv, hm, r['col'], rng)
              if m <= rank_hi else None)
        nd = len(r['dev'])
        print(f"  m = {m:2d} (n_hub = {2*m:2d}): class_shape = {shape}; "
              f"rho = {pred} (k = {k}, tau = {tau}), repair uses {nd} "
              f"deviating hubs of {2*m}"
              f"{'' if r['extra'] is None else ' (+1 neutral pair for BALANCE)'}"
              f"; admissible = True; NC1 clear = {nc1}; fully-good "
              f"(exact-Q dim Z = 0, BOTH blocks) = {fg}; knob search "
              f"{'EXHAUSTIVE' if r['exhaustive'] else 'capped at ' + str(r['cap'])}"
              f", hit at try {r['tried']}  [{time.time() - t0:.1f}s]")
    print("  => the rung-minority rule IS repairable at odd rung lengths: "
          "an explicit, correlated, length-vector-computable rule.")


# ---------------------------------------------------------------------------
# [GOD-3b] --far: the ADMISSIBILITY half, past every n_hub wall the arc has
# ---------------------------------------------------------------------------

def light_model(edges):
    """`cflank.admissible` reads only `hm['hubs']` from the hub model; the
    rest of `cflank.hub_model` is the `packmm.simple_cycles` enumeration,
    which is what makes it exponential in `n_hub`.  This builds the SAME
    hub list from the SAME canonical primitive (`gridcol.branch_decomp`,
    which `cflank.hub_model` itself calls) and nothing else -- so the
    admissibility verdict is computed by the canonical predicate, and only
    the circuit-dependent fields (NC1's input) are absent.  Asserted equal
    to `cflank.hub_model`'s hub list wherever both are affordable."""
    hubs, branches = gridcol.branch_decomp(edges)
    assert branches is not None, "not a branch decomposition"
    return dict(hubs=hubs, branches=branches,
                ends=[(u, w) for (u, w, _) in branches],
                lens=[len(p) for (_, _, p) in branches])


def leg_far(hi=40):
    """[GOD-3b] (GR-253)(ii).  The repaired rule's ADMISSIBILITY verdict is
    an exact combinatorial predicate with no draw and no cycle enumeration,
    so it is not fenced by the `2^{n_hub}` `cflank.cubic_habitat` scan that
    stopped GBASE's ladder leg at `n_hub = 24`, nor by `cflank.hub_model`'s
    simple-cycle enumeration.  This leg runs the rule to `n_hub = 2*hi`.
    The verdict is cap-free in BOTH directions (F31: an exact predicate);
    what it does NOT certify past `n_hub = 24` is NC1 or `dim Z = 0`."""
    print(f"[GOD-3b] (GR-253)(ii) the repaired rule's ADMISSIBILITY alone, "
          f"m = 6..{hi} (n_hub up to {2*hi}) -- EXACT predicate, no cap")
    ok, rows = 0, 0
    for m in range(6, hi + 1, 2):
        exc = recipe_gr175(m)
        specs = gexist.ladder_specs(m, exc)
        edges = gridcol.subdivide(specs)
        allv = sorted(_verts(edges), key=str)
        hm = light_model(edges)
        if m <= 10:                 # the range where the full model is cheap
            assert hm['hubs'] == cflank.hub_model(edges)['hubs'], \
                "light_model's hub list disagrees with cflank.hub_model"
        r = search_repair(m, exc, light=True)
        best = None if r.get('fail') else (len(r['dev']), r['extra'],
                                           r['exhaustive'], r['cap'])
        rows += 1
        ok += 1 if best else 0
        pred, k, _t = rho_closed(m, [L for (_u, _w, L) in specs])
        print(f"  m = {m:2d} (n_hub = {2*m:2d}, M = {3*m:2d} branches): "
              f"rho = {pred}; repaired rule admissible = {bool(best)}"
              + (f" with {best[0]} deviating hubs"
                 + ("" if best[1] is None else " (+1 neutral pair)")
                 if best else
                 (" (knob set EXHAUSTED)" if r['exhaustive']
                  else f" (not found under cap {r['cap']})")))
    print(f"  => {ok}/{rows} -- the repaired rule is admissible at "
          f"(GR-175)'s recipe at EVERY even m in the range, to "
          f"n_hub = {2*hi}.  GBASE's ladder leg stopped at n_hub = 24 "
          f"because `cflank.cubic_habitat` scans 2^n_hub subsets; the "
          f"admissibility half needs no such scan.")


# ---------------------------------------------------------------------------
# [GOD-4] --save: what the repair COSTS
# ---------------------------------------------------------------------------

def leg_save(hi=12):
    """[GOD-4] (GR-254).  (GR-34)(ii)'s value was not only admissibility: it
    was that EVERY hub's minority dart is its RUNG, "and no interval or
    square chunk ever exits through a rung, so `save == 0` on the entire
    family, `defect >= 3` everywhere on it".  The repaired rule points `rho`
    hubs' minorities at RIM darts, which interval chunks DO exit through.

    Measured with the CANONICAL devices `gexist.chunk_shape` /
    `gexist.weak_frame` / `gexist.hub_minority` -- the same ones
    `gexist.leg_charge` asserts the landed rule against -- over the whole
    `gexist.interval_chunks` family.  Exhaustive over that family; no cap,
    no sampler.  This is the price column of the repair."""
    from gexist import (chunk_shape, incidence, hub_minority,
                        interval_chunks, weak_frame)
    from gcap import branch_stats
    print("[GOD-4] (GR-254) the price of the repair: `save` and `defect` "
          "over `gexist.interval_chunks` -- EXHAUSTIVE over the family")
    for m in range(6, hi + 1, 2):
        exc = recipe_gr175(m)
        r = search_repair(m, exc)
        if r.get('fail'):
            print(f"  m = {m:2d}: no balanced repair to price")
            continue
        hm, edges, allv = r['hm'], r['edges'], r['allv']
        inc = incidence(hm)
        stats = branch_stats(hm, r['col'], 'A')
        mino = hub_minority(hm, stats)
        rungs_hm = {_spec_to_hm(r['specs'], hm, rung(m, i)) for i in range(m)}
        nonrung = sum(1 for (_maj, mk) in mino.values() if mk not in rungs_hm)
        assert nonrung == len(r['dev']), \
            "the minority map the canonical `hub_minority` reads back " \
            "disagrees with the constructed deviation set"
        ivs = [tuple(_spec_to_hm(r['specs'], hm, k) for k in ks)
               for ks in interval_chunks(m)]
        bad_s = bad_d = forced = 0
        for ks in ivs:
            cs = chunk_shape(hm, inc, ks)
            dA, sA, _wA, dB, sB, _wB = weak_frame(hm, inc, stats, cs, ks)
            bad_s += 1 if (sA or sB) else 0
            bad_d += 1 if (dA < 3 or dB < 3) else 0
            # `weak_frame` charges ONE save, to one block or the other, for
            # every ODD branch in the chunk -- independently of the minority
            # map.  So a chunk containing an odd branch has save > 0 at
            # EVERY admissible colouring: that is a PROOF, not a draw.
            forced += 1 if any(hm['lens'][k] % 2 for k in ks) else 0
        pred, _k, _t = rho_closed(m, r['lens'])
        print(f"  m = {m:2d}: rho = {pred} deviating hubs of {2*m}; "
              f"{bad_s}/{len(ivs)} interval chunks have save > 0 in some "
              f"block, of which {forced}/{len(ivs)} are FORCED (they "
              f"contain an odd branch, so save > 0 at EVERY admissible "
              f"colouring); {bad_d}/{len(ivs)} have "
              f"defect < 3 in some block")
    print("  => the repair does NOT sell `save == 0`: that property is "
          "UNAVAILABLE at (GR-175)'s recipe for EVERY admissible colouring, "
          "because the recipe has odd branches and every interval chunk "
          "contains one.  What the repaired rule KEEPS is `defect >= 3` on "
          "the whole interval family -- the conjunct (GR-17)(c) actually "
          "needs.  (GR-34)(ii)'s `save == 0` was a property of its ALL-EVEN "
          "recipe, not of the rung-minority rule.")


def _spec_to_hm(specs, hm, spec_index):
    """Spec index -> `hub_model` branch index, by hub-end pair (the
    `gunif.spec_to_hm_index` mapping, taken one index at a time)."""
    (u, w, _L) = specs[spec_index]
    key = frozenset((('h', u), ('h', w)))
    for k, (a, b) in enumerate(hm['ends']):
        if frozenset((a, b)) == key:
            return k
    raise AssertionError("branch not found in the hub model")


# ---------------------------------------------------------------------------
# [GOD-5] --oddm: (GR-34)(ii)'s undeveloped ODD-m remark
# ---------------------------------------------------------------------------

def leg_oddm(hi=13):
    """[GOD-5] (GR-255).  §(K-grid) (GR-34)(ii) records, "observed, not
    developed": "the pure rule needs EVEN `m` (rim alternation is a parity
    condition; odd `m` needs ONE deviating hub, absorbable at an excess
    rung)".  At odd `m` with (GR-34)'s all-even recipe, `k = 0` and
    `tau = 1`, so the closed form says ONE is impossible and TWO suffice.
    Tested by brute force over ALL single-hub deviations (exhaustive)."""
    print("[GOD-5] (GR-255) (GR-34)(ii)'s odd-m remark, tested -- "
          "EXHAUSTIVE over single-hub deviations")
    for m in range(5, hi + 1, 2):
        exc = recipe_gr34(m)
        specs = gexist.ladder_specs(m, exc)
        lens = [L for (_u, _w, L) in specs]
        pred, k, tau = rho_closed(m, lens)
        ones = 0
        for hub in range(2 * m):
            i = hub % m
            for br in ((top_rim(m, i), top_rim(m, i - 1)) if hub < m
                       else (bot_rim(m, i), bot_rim(m, i - 1))):
                if solve_colours(m, specs, minority_map(m, {hub: br})):
                    ones += 1
        r = search_repair(m, exc)
        ok = None
        if not r.get('fail'):
            ok = cflank.admissible(r['edges'], r['allv'], r['hm'], r['col'])
        print(f"  m = {m:2d} (n_hub = {2*m:2d}, ALL lengths even): k = {k}, "
              f"tau = {tau}; closed-form rho = {pred}; single-hub "
              f"deviations that work: {ones}/{4*m}; two-hub repair "
              f"admissible = {ok}")
    print("  => the remark's COUNT is wrong: ONE deviating hub never "
          "suffices at odd m (it always flips exactly one face), TWO always "
          "do -- and they are the two ends of ONE rung.")


# ---------------------------------------------------------------------------
# [GOD-6] --consumer: the F26 check
# ---------------------------------------------------------------------------

def leg_consumer():
    """[GOD-6] (GR-256).  What does a UNIFORM rule on a base subfamily buy,
    given that (GR-15) is ONE-POINT-DECIDABLE per shape?  This leg is an
    accounting of which half of the (GR-15) certificate the rule supplies,
    measured by counting the calls: for each `m`, the repaired rule supplies
    the COLOURING with no search, and `fully_good_rank` still has to be run
    PER SHAPE.  Reports the split rather than asserting it."""
    print("[GOD-6] (GR-256) F26: which half of (GR-15) a uniform RULE "
          "actually supplies")
    print("  (GR-15) = 'admits an admissible colouring with generic "
          "dim Z+ = dim Z- = 0'.  Two halves:")
    print("    (a) EXHIBIT an admissible colouring     -- what a rule gives, "
          "uniformly in m")
    print("    (b) certify generic dim Z = 0 AT IT     -- a rank computation "
          "on a shape-sized matrix, still PER SHAPE")
    print("  The landed (GR-34)(ii) rule supplies (a) and NOT (b): its own "
          "text says the rule is 'proven PER TESTED SHAPE, not for all m'.")
    print("  So the repaired rule closes the same half the landed rule "
          "closes, on strictly more shapes -- and the uniformity gap "
          "(GR-15) names stays exactly where it was, in (b).")


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    for f in ('cut', 'rho', 'repair', 'far', 'save', 'oddm', 'consumer',
              'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--hi', type=int, default=20)
    ap.add_argument('--rank-hi', type=int, default=12)
    ap.add_argument('--nc1-hi', type=int, default=12)
    ap.add_argument('--shape-hi', type=int, default=6)
    ap.add_argument('--rho-hi', type=int, default=7)
    ap.add_argument('--farhi', type=int, default=40)
    a = ap.parse_args()
    run = a.validate
    if run or a.cut:
        leg_cut(a.hi)
    if run or a.rho:
        leg_rho(a.rho_hi)
    if run or a.repair:
        leg_repair(a.hi, a.rank_hi, a.nc1_hi, a.shape_hi)
    if run or a.far:
        leg_far(a.farhi)
    if run or a.save:
        leg_save(min(a.hi, 12))
    if run or a.oddm:
        leg_oddm()
    if run or a.consumer:
        leg_consumer()
    if not (run or a.cut or a.rho or a.repair or a.far or a.save or a.oddm
            or a.consumer):
        ap.print_help()


if __name__ == '__main__':
    main()
