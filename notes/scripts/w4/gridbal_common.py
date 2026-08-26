"""
Phase 39 kernel-(K) numerics harness -- the `w4/` BALANCE-LAYER common
module.

Moved down 2026-08-25 (README *Harness debt*, "New item (2026-08-25,
direction GFLIP)"): eleven read-only devices that `w4/gflip.py` pulls in
from five sibling leaves (`balb`, `gbal`, `gdesc`, `gflow`, `gpsa`), none
of them S1-catalogued and most already carrying two or more consumers
before GFLIP arrived -- exactly the "second consumer arrived unnoticed"
mechanism the 2026-08-20 move-down write-up warned about.  Every device
is BYTE-VERBATIM (same body, same docstring) as its old definition; only
its home changed.  Each old home RE-EXPORTS its moved names (`from
gridbal_common import ...`), so no consumer's import line changes -- the
`star_span_ranks` precedent (README S2 rule 2).

Four coherent jobs, matching the README items' own grouping:
  * pool / shape suppliers -- `v8_specs`/`stratum_cases` (from `balb`),
    `named_cases`/`random_cases` (from `gbal`), `seeded_shapes` (from
    `gflow`);
  * the (GR-49)/(GR-50) z-form + oracle surface -- `odd_idx`/`bounds_of`/
    `feasible_at` (from `gbal`), `feas_flip` (from `gflow`), plus, since
    2026-08-25, the rest of the z-form (`z_admissible`/`z_to_map`/
    `z_pattern`/`assign_feasible`/`z_of_orientation`, all from `gbal`);
  * pattern combinatorics -- `imb_of` (from `gdesc`), `branches_at`
    (from `gpsa` -- the widest fan-in recorded: 8 consumers before this
    move), plus, since 2026-08-25, `majority_of` (from `gdesc`);
  * cube combinatorics, joining 2026-08-25 -- `adm_cube`/`block_ends_at`/
    `f_layers` (all from `gflow`).

EXTENDED 2026-08-25 (README *Harness debt*, "New item (2026-08-25,
direction GCHEAP)" and "New item (2026-08-25, direction GPRICE)", the
GPRICE entry's own text saying to pay both together): nine more
read-only devices that `w4/gcheap.py` and `w4/gprice.py` pull in from
three of the same five sibling leaves (`gbal`, `gdesc`, `gflow`) --
none S1-catalogued, several already past two or more consumers before
GCHEAP/GPRICE arrived, exactly the mechanism the GFLIP move-down above
predicted for its own five-name surface ("the deferred-import wrinkle
dissolves if the whole surface moves" -- see `feasible_at` below).
Same byte-verbatim / re-export discipline.  `perfect_matchings`
(`gorient`) and `cubic_habitat` (`cflank`) are catalogued in
`README.md` §1 IN PLACE instead of moved: both already have a far
wider fan-in than a single layer's private device, but neither reads
nor is read by anything in this module, so moving them buys nothing.

DEFERRED IMPORTS, not an oversight.  Five of the original eleven bodies
read a name that stays BEHIND in their old home -- `gbal.pool_cases`,
`gbal.rand_cubic`, `balb.rand_habitat`,
`gpsa.nkp_specs`/`nk55_specs`/`nko2v_specs` -- and that old home now
imports THIS module back, to re-export.  A top-level `from gbal import
...` (or `from balb import ...` / `from gpsa import ...`) here would be
a genuine import cycle at module-load time; the KBARE-FALSIFY
precedent's generalization ("every global a moved body reads must
resolve in the new module") is honoured with a function-body-local
import instead of a top-level one.  That resolves cleanly regardless of
import order, because no caller ever invokes these functions while
another module's own top-level code is still executing -- every
driver's argparse dispatch runs after all imports in the process have
completed.  `WITNESSES` (`gunif`), `nk_specs` (`gdev`) and `nko_specs`
(`gadm`) are NOT cyclic -- neither of those three modules imports
anything from this layer -- and stay top-level imports.  Two of the
nine 2026-08-25 arrivals need the same treatment: `z_admissible` and
`z_to_map` each read `gbal.dart_col`, which stays behind (not itself
past §2 rule 2's trigger -- one consumer, this module, via this very
deferred import), so both keep a function-body-local `from gbal import
dart_col`.  `feasible_at`'s OWN former deferred import DISSOLVES
instead: `assign_feasible` and `z_of_orientation` now live in this
module alongside it, exactly as the GCHEAP entry predicted.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from gunif import WITNESSES                                            # noqa: E402
from gdev import nk_specs                                              # noqa: E402
from gadm import nko_specs                                             # noqa: E402


# --------------------------------------- pool / shape suppliers -------------

def v8_specs(long_chord=False):
    """The Wagner shape V8: the 8-cycle 0..7 plus the four long chords
    (i, i+4), the chords ODD.  Habitat (asserted at use): cubic,
    loop-free, 3-connected, cyclically 4-edge-connected, excess 6."""
    cyc = [(i, (i + 1) % 8) for i in range(8)]
    ch = [(0, 4), (1, 5), (2, 6), (3, 7)]
    if long_chord:
        return [(u, w, 2) for (u, w) in cyc] + \
            [(0, 4, 5), (1, 5, 3), (2, 6, 3), (3, 7, 3)]
    return [(u, w, 4 if j == 0 else 2) for j, (u, w) in enumerate(cyc)] + \
        [(u, w, 3) for (u, w) in ch]


def stratum_cases():
    """Every odd-carrying habitat shape of the Lambda = empty, D = 0
    stratum -- EXHAUSTIVE (gbal.pool_cases behind the (GR-25) cut
    criterion), all-even shapes dropped (balance is vacuous there)."""
    from gbal import pool_cases
    out = []
    for j, (n, sp) in enumerate(pool_cases()):
        if any(L % 2 == 1 for (_u, _w, L) in sp):
            out.append((f'pool#{j + 1}', n, sp))
    return out


def named_cases():
    """The named large shapes: GUNIF's W-witnesses and GPSA/GADM's
    commissioned odd-rich necklace constructions (reused read-only)."""
    from gpsa import nkp_specs, nk55_specs, nko2v_specs
    out = []
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    for tag in ('W3M', 'W3', 'W4', 'W5'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        out.append((tag, n, [tuple(s) for s in specs]))
    specs, _pent = nko2v_specs()
    out.append(('NKo2v', 10, specs))
    for m in (6, 8, 10, 12):
        sp, _pent = nkp_specs(m)
        out.append((f'NKp({m})', 5 * m, sp))
        sp, _pent = nk55_specs(m)
        out.append((f'NK55({m})', 5 * m, sp))
        sp, _pent, _F, _ch = nk_specs(m)
        out.append((f'NK({m})', 5 * m, sp))
        out.append((f'NKo({m})', 5 * m, nko_specs(m)[0]))
    return out


def random_cases(rng, sizes, per, k2s, conc_rate):
    """Seeded random cubic bridgeless shapes with prescribed odd counts;
    `conc_rate` of the placements are deliberately CONCENTRATED on one
    hub's neighbourhood (the adversarial side of the sweep)."""
    from gbal import rand_cubic
    out = []
    conc = 0
    for n in sizes:
        for _t in range(per):
            es = rand_cubic(n, rng)
            if es is None:
                continue
            M = len(es)
            for k2 in k2s:
                if M < k2:
                    continue
                sp = [[u, w, 2] for (u, w) in es]
                if rng.random() < conc_rate:
                    v0 = rng.randrange(n)
                    pref = sorted(
                        range(M),
                        key=lambda i: (v0 not in es[i], rng.random()))
                    idxs = pref[:k2]
                    conc += 1
                else:
                    idxs = rng.sample(range(M), k2)
                for i in idxs:
                    sp[i][2] = 3
                sp = [tuple(s) for s in sp]
                if len(odd_idx(sp)) != k2:
                    continue
                out.append((f'rand(n={n},2k={k2})', n, sp))
    return out, conc


def seeded_shapes(n, tries, rng):
    """Seeded habitat shapes at n hubs (balb.rand_habitat, behind the (GR-25)
    cut criterion).  A GRAPH sampler; no placement is drawn."""
    from balb import rand_habitat
    return [s for s in rand_habitat(n, rng, tries) if odd_idx(s)]


# ------------------------------------- the (GR-49)/(GR-50) oracle surface ---

def odd_idx(specs):
    """The odd-branch indices, in gpsa.parity_census's own order."""
    return [i for i, (_u, _w, L) in enumerate(specs) if L % 2 == 1]


def bounds_of(specs, n, oidx, p):
    """(GR-50): (o, q, d, lo, hi) for the pattern `p` (p[j] = the colour
    of oidx[j]; colour 0 = A).  lo/hi bound the number of even branches
    at v whose A-end is v."""
    o = [0] * n
    q = [0] * n
    for j, i in enumerate(oidx):
        (u, w, _L) = specs[i]
        for v in (u, w):
            q[v] += 1
            if p[j] == 0:
                o[v] += 1
    d = [3 - q[v] for v in range(n)]
    assert all(x >= 0 for x in d), "hub with more than three odd branches"
    lo = [max(0, 1 - o[v]) for v in range(n)]
    hi = [min(d[v], 2 - o[v]) for v in range(n)]
    return o, q, d, lo, hi


def z_admissible(specs, n, binc, z):
    """(GR-49): no hub sees three equal dart colours."""
    from gbal import dart_col
    for v in range(n):
        a, b, c = (dart_col(specs, z, v, i) for i in binc[v])
        if a == b == c:
            return False
    return True


def z_to_map(specs, n, binc, z):
    """(GR-49) forward: the (m, c) of an admissible z -- c(v) = the
    majority dart colour at v, m(v) = the minority dart."""
    from gbal import dart_col
    m, c = {}, {}
    for v in range(n):
        cs = [dart_col(specs, z, v, i) for i in binc[v]]
        maj = 0 if cs.count(0) >= 2 else 1
        c[v] = maj
        lone = [t for t in range(3) if cs[t] != maj]
        assert len(lone) == 1, "hub not 2-1 split: z was not admissible"
        i = binc[v][lone[0]]
        m[v] = (i, 0 if v == specs[i][0] else 1)
    return m, c


def z_pattern(z, oidx):
    """The odd-branch majority pattern of z, in pattern_of's bit order."""
    bits = 0
    for j, i in enumerate(oidx):
        if z[i]:
            bits |= 1 << j
    return bits


def assign_feasible(nv, edges, lo, hi):
    """(GR-50)/(GR-51): assign every edge to ONE endpoint with
    lo[v] <= load[v] <= hi[v].  Returns (assignment, None) on success or
    (None, R) with R a hub set violating the two-sided Hall condition --
    the infeasibility CERTIFICATE.  Augmenting-path algorithm, exact
    integers; this is the constructive half of (GR-51)'s proof."""
    bad = {v for v in range(nv) if lo[v] > hi[v]}
    if bad:
        return None, bad
    asg = [e[0] for e in edges]
    load = [0] * nv
    for a in asg:
        load[a] += 1
    inc = {v: [] for v in range(nv)}
    for j, (a, b) in enumerate(edges):
        inc[a].append(j)
        inc[b].append(j)

    def other(j, v):
        a, b = edges[j]
        return b if a == v else a

    for phase in (0, 1):
        moved = True
        while moved:
            moved = False
            for v in range(nv):
                while (load[v] > hi[v]) if phase == 0 else (load[v] < lo[v]):
                    par = {v: None}
                    stack = [v]
                    tgt = None
                    while stack and tgt is None:
                        x = stack.pop()
                        for j in inc[x]:
                            y = other(j, x)
                            if phase == 0 and asg[j] != x:
                                continue
                            if phase == 1 and asg[j] != y:
                                continue
                            if y in par:
                                continue
                            par[y] = (x, j)
                            ok = (load[y] < hi[y]) if phase == 0 \
                                else (load[y] > lo[y])
                            if ok:
                                tgt = y
                                break
                            stack.append(y)
                    if tgt is None:
                        return None, set(par)
                    y = tgt
                    while par[y] is not None:
                        x, j = par[y]
                        if phase == 0:
                            asg[j] = y
                            load[y] += 1
                            load[x] -= 1
                        else:
                            asg[j] = x
                            load[x] += 1
                            load[y] -= 1
                        y = x
                    moved = True
    for v in range(nv):
        assert lo[v] <= load[v] <= hi[v], "assignment out of bounds"
    return asg, None


def z_of_orientation(specs, oidx, p, even, asg):
    """(GR-49)+(GR-50): rebuild the branch colouring z from a balanced
    pattern and an even-branch orientation."""
    z = [0] * len(specs)
    for j, i in enumerate(oidx):
        z[i] = p[j]
    for t, i in enumerate(even):
        (u, _w, _L) = specs[i]
        z[i] = 0 if asg[t] == u else 1
    return z


def feasible_at(specs, n, oidx, p):
    """The (GR-50) decision at ONE pattern: returns z or None."""
    _o, _q, _d, lo, hi = bounds_of(specs, n, oidx, p)
    if any(hi[v] < lo[v] for v in range(n)):
        return None
    oset = set(oidx)
    even = [i for i in range(len(specs)) if i not in oset]
    edges = [(specs[i][0], specs[i][1]) for i in even]
    asg, _R = assign_feasible(n, edges, lo, hi)
    if asg is None:
        return None
    return z_of_orientation(specs, oidx, p, even, asg)


def feas_flip(specs, n, oidx, pat, j):
    """Is the pattern with odd branch oidx[j] recoloured (GR-50)-feasible?"""
    p2 = [(pat >> t) & 1 for t in range(len(oidx))]
    p2[j] ^= 1
    return feasible_at(specs, n, oidx, p2) is not None


# ------------------------------------------- pattern combinatorics ----------

def imb_of(k2, p):
    """Signed imbalance a - b (#A-majority - #B-majority; bit 1 = B)."""
    return k2 - 2 * bin(p).count('1')


def branches_at(specs, n):
    """hub -> the 3 incident branch indices (cubic, loop-free asserted)."""
    inc = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        assert u != w, "loop in hub multigraph"
        inc[u].append(i)
        inc[w].append(i)
    for v in range(n):
        assert len(inc[v]) == 3, "hub not cubic"
    return inc


def majority_of(oidx, p, sgn):
    """specs-indices of the majority-side odd branches (sgn = sign of
    the imbalance; bit 0 = A-majority)."""
    assert sgn != 0
    return [i for j, i in enumerate(oidx)
            if (sgn > 0) == (((p >> j) & 1) == 0)]


# ---------------------------------------------- cube combinatorics ---------

def block_ends_at(specs, m, i):
    """The ends of odd branch `i` at which `i` carries the MINORITY dart --
    the BLOCKED ends.  0 = dart-free, 1 = one-end-blocked, 2 = doubly
    blocked."""
    (u, w, _L) = specs[i]
    return [v for v in (u, w) if m[v][0] == i]


def adm_cube(specs, n, binc, oidx):
    """EXHAUSTIVE: every admissible z of the full 2^|E| cube, with its (m, c)
    and its odd pattern.  Usable to |E| = 18 (n_hub = 12)."""
    mn = len(specs)
    out = []
    for bits in range(1 << mn):
        z = [(bits >> i) & 1 for i in range(mn)]
        if z_admissible(specs, n, binc, z):
            mm, c = z_to_map(specs, n, binc, z)
            out.append((z, mm, c, z_pattern(z, oidx)))
    return out


def f_layers(cube, n, base):
    """f(pattern) = the exact minimum dist(., M) over admissible z with that
    pattern, off the exhaustive cube; plus d_par(M) = min f."""
    f = {}
    for (_z, mm, _c, pat) in cube:
        d = sum(1 for v in range(n) if mm[v] != base[v])
        if pat not in f or d < f[pat]:
            f[pat] = d
    return f, min(f.values())
