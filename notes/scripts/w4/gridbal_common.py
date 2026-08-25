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

Three coherent jobs, matching the README item's own grouping:
  * pool / shape suppliers -- `v8_specs`/`stratum_cases` (from `balb`),
    `named_cases`/`random_cases` (from `gbal`), `seeded_shapes` (from
    `gflow`);
  * the (GR-49)/(GR-50) oracle surface -- `odd_idx`/`bounds_of`/
    `feasible_at` (from `gbal`), `feas_flip` (from `gflow`);
  * pattern combinatorics -- `imb_of` (from `gdesc`), `branches_at`
    (from `gpsa` -- the widest fan-in recorded: 8 consumers before this
    move).

DEFERRED IMPORTS, not an oversight.  Five of the eleven bodies read a
name that stays BEHIND in their old home -- `gbal.pool_cases`,
`gbal.rand_cubic`, `gbal.assign_feasible`, `gbal.z_of_orientation`,
`balb.rand_habitat`, `gpsa.nkp_specs`/`nk55_specs`/`nko2v_specs` -- and
that old home now imports THIS module back, to re-export.  A top-level
`from gbal import ...` (or `from balb import ...` / `from gpsa import
...`) here would be a genuine import cycle at module-load time; the
KBARE-FALSIFY precedent's generalization ("every global a moved body
reads must resolve in the new module") is honoured with a
function-body-local import instead of a top-level one.  That resolves
cleanly regardless of import order, because no caller ever invokes
these functions while another module's own top-level code is still
executing -- every driver's argparse dispatch runs after all imports in
the process have completed.  `WITNESSES` (`gunif`), `nk_specs` (`gdev`)
and `nko_specs` (`gadm`) are NOT cyclic -- neither of those three
modules imports anything from this layer -- and stay top-level imports.
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


def feasible_at(specs, n, oidx, p):
    """The (GR-50) decision at ONE pattern: returns z or None."""
    from gbal import assign_feasible, z_of_orientation
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
