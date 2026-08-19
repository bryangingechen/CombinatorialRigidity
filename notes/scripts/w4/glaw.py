#!/usr/bin/env python3
"""GLAW -- direction GLAW (Phase 39, sixth fan-out, 2026-08-19): attack
(a'), the `d_fg = d_adm` LAW, at route-ledger entry 1.

Answers `notes/Pencil-fanout-archive.md` S"Sixteenth direction -- GLAW"; the
mathematics is `notes/Pencil-informal-grid.md` S(K-grid) *Steps G74-G79*, labels (GR-55)-(GR-60).

Everything here is at `Lambda = empty`, `D = 0`, modulo (GR-4').  The
target is entry 1's primary attack (a'): at every habitat shape the
least deviation count carrying an ADMISSIBLE colouring equals the least
carrying a FULLY-GOOD one.  Nothing here closes (GR-15), and an (a')
HIT would not fire E3 while entry 5 is open.

Modes
-----
--law   (GR-56): the SPLIT identity `defect_A - defect_B = delta_S -
        sigma_S` (new; the SUM identity is landed (GR-32)(i)) and the
        one-inequality form of full-goodness it yields; the balance
        rider as the whole-graph instance; full-goodness as a function
        of the minority map alone.
--nf    (GR-55): the (y, Z, phi) normal form of the distance-d
        deviation stratum, certified against brute force; the
        `2^(n/2 - 1)` count of M-avoiding coset representatives; the
        layer triple re-derived and cross-checked against `gdev.min_dev`.
--exh   (GR-58): the EXHAUSTIVE (a') census over the whole
        `Lambda = empty` `D = 0` `n_hub <= 6` habitat stratum (4920
        labelled shapes), optimum computed with NO deviation cap.
--sdr   (GR-57): the SDR exchange calculus on the optimal stratum --
        the component product formula, the elementary shift as a
        distance-preserving cross-mu 2-hub move, and the axis verdict
        on GADM's named sticking case.
--big   (GR-59): (a') at the shapes the pool cannot reach -- W3M/W3/W4
        exhaustive, W5 and the ladders, NKo2v, and the first
        ODD-CARRYING large-`n` tests at NKp(6) / NK55(6) (n = 30),
        rank-certified at the optimum.
--adv   F13 falsification controls, each with a must-reject / must-fire
        witness and a negative control.
--validate  all six in one process.

Discipline (`notes/scripts/README.md` SS1-4): exact integers / GF(2)
throughout, no floating point; every rng seeded from R_SEED and printed;
no bare `set` printed; imports are read-only from the canonical layer.
Rank enters only through `gexist.fully_good_rank` (README S4 convention
2); every combinatorial full-goodness verdict is `gorient.
fully_good_scan`, the landed exact evaluator.
"""

import os
import random
import sys
import time
from itertools import combinations

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from kbare_common import verts_of                                      # noqa: E402
from gridcol import subdivide                                          # noqa: E402
from cflank import admissible, cubic_habitat, hub_model                # noqa: E402
from gcap import branch_stats, pool_specs                              # noqa: E402
from gunif import WITNESSES                                            # noqa: E402
from gexist import fully_good_rank, ladder_specs                       # noqa: E402
from gorient import (cm_solve, cm_colouring, odd_balance,              # noqa: E402
                     perfect_matchings, m_of_matching, prep_shape,
                     fully_good_scan, fast_defects, darts_at)
from gdev import (min_dev, even_vec, fundamental_cycles, in_coset,     # noqa: E402
                  nk_specs, light_hm)
from gpsa import (branches_at, is_bridgeless, delta_of, xor_vec,       # noqa: E402
                  nkp_specs, nk55_specs, nko2v_specs)

R_SEED = 20260819


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive (checked against the README index
# and the Divergences table).  `gf2_affine` is a GF(2) affine solver --
# S1 lists `exactcore.nullspace` (rational) and `kbare_common.rank_modp`
# (a rank, not a solution), so there is no GF(2) solve to reuse.
# `hm_spec_map`/`chunk_inv` are the (GR-56) bookkeeping; `avoid_space`/
# `min_avoiders` build the M-avoiding coset affine space; `sdr_of` /
# `sdr_space` / `sdr_shift` are the (GR-57) exchange calculus;
# `dist_stratum` is the (GR-55) enumerator and `layers_exact` the exact
# layer triple built on it.  `gpsa.sdr_build` is the landed CONSTRUCTIVE
# SDR (one per component); `sdr_space` enumerates ALL of them, which is
# the object (a') needs -- a different job, hence a different name.


def gf2_affine(rows, rhs, nvars):
    """Solve `rows . y = rhs` over GF(2).  Returns (particular, kernel
    basis) with vectors as int bitmasks over `nvars` coordinates, or
    None if inconsistent."""
    aug = [(r, b) for r, b in zip(rows, rhs)]
    piv = []
    used = 0
    r = 0
    for c in range(nvars):
        sel = None
        for i in range(r, len(aug)):
            if (aug[i][0] >> c) & 1:
                sel = i
                break
        if sel is None:
            continue
        aug[r], aug[sel] = aug[sel], aug[r]
        for i in range(len(aug)):
            if i != r and ((aug[i][0] >> c) & 1):
                aug[i] = (aug[i][0] ^ aug[r][0], aug[i][1] ^ aug[r][1])
        piv.append(c)
        used |= 1 << c
        r += 1
        if r == len(aug):
            break
    for i in range(r, len(aug)):
        if aug[i][0] == 0 and aug[i][1]:
            return None
    part = 0
    for i, c in enumerate(piv):
        if aug[i][1]:
            part |= 1 << c
    kern = []
    for c in range(nvars):
        if (used >> c) & 1:
            continue
        v = 1 << c
        for i, pc in enumerate(piv):
            if (aug[i][0] >> c) & 1:
                v |= 1 << pc
        kern.append(v)
    return part, kern


def hm_spec_map(specs, hm):
    """hub_model branch index -> spec index, read off the interior-vertex
    tag ('i', spec, j) that `gridcol.subdivide` writes.  Unambiguous at
    `Lambda = empty` (every branch has an interior)."""
    out = []
    for k, (_u, _w, path) in enumerate(hm['branches']):
        tags = {v[1] for e in path for v in e
                if isinstance(v, tuple) and v[0] == 'i'}
        assert len(tags) == 1, "branch without a unique interior tag"
        out.append(tags.pop())
    assert sorted(out) == list(range(len(specs))), "branch map not a bijection"
    return out


def chunk_inv(hm, inc, ks, m, c, s_of):
    """(GR-56)'s four chunk invariants of the (c, m) data:
    cap = 2z + exc, z_mono = #interiors whose minority dart is the exit,
    delta_S = #A-majority odd - #B-majority odd inside S,
    sigma_S = #mono interiors with majority A - #with majority B."""
    ends, lens = hm['ends'], hm['lens']
    sk = set(ks)
    deg = {}
    for k in ks:
        for v in ends[k]:
            deg[v] = deg.get(v, 0) + 1
    z2 = [v for v, d in deg.items() if d == 2]
    exc = sum(lens[k] - 2 for k in ks)
    zmono = sigma = 0
    for hv in z2:
        free = [k for k in inc[hv] if k not in sk]
        assert len(free) == 1, "degree-2-in-S hub without one free dart"
        if m[hv[1]][0] == s_of[free[0]]:
            zmono += 1
            sigma += 1 if c[hv[1]] == 0 else -1
    delta = 0
    for k in ks:
        if lens[k] % 2:
            u = ends[k][0][1]
            delta += 1 if (c[u] ^ (m[u] == (s_of[k], 0))) == 0 else -1
    return 2 * len(z2) + exc, zmono, delta, sigma


def avoid_space(specs, n, mat):
    """The M-avoiding representatives of `Phi = tau + Cut(G)`, as an
    affine subspace of GF(2)^free (free = the branches off M).  Returns
    (free, particular, kernel basis); (GR-55) Cor. 1 says the space is
    nonempty of dimension exactly n/2 - 1."""
    E = len(specs)
    free = [i for i in range(E) if i not in mat]
    pos = {b: j for j, b in enumerate(free)}
    tau = even_vec(specs)
    cycles = fundamental_cycles(specs, n)
    rows, rhs = [], []
    for cyc in cycles:
        r = 0
        for i in cyc:
            if i in pos:
                r ^= 1 << pos[i]
        rows.append(r)
        rhs.append(sum(tau[i] for i in cyc) % 2)
    sol = gf2_affine(rows, rhs, len(free))
    assert sol is not None, \
        "no M-avoiding representative -- (GR-44)(i) REFUTED, HEADLINE"
    return free, sol[0], sol[1]


def avoid_all(specs, n, mat, cap=1 << 20):
    """Every M-avoiding representative, as branch-index frozensets."""
    free, part, kern = avoid_space(specs, n, mat)
    assert len(kern) <= 20, "M-avoiding space too large to enumerate"
    out = []
    for mask in range(1 << len(kern)):
        v = part
        mm = mask
        j = 0
        while mm:
            if mm & 1:
                v ^= kern[j]
            mm >>= 1
            j += 1
        out.append(frozenset(free[t] for t in range(len(free))
                             if (v >> t) & 1))
        if len(out) >= cap:
            break
    return out


def min_avoiders(specs, n, mat):
    """(w_M, all minimum-weight M-avoiding representatives)."""
    allv = avoid_all(specs, n, mat)
    w = min(len(y) for y in allv)
    return w, [y for y in allv if len(y) == w]


def sdr_space(specs, y, forbid=frozenset()):
    """EVERY injective end-selection of the branch set `y` avoiding the
    hubs in `forbid`, with the component structure that indexes them:
    returns (list of phi as tuples ((branch, hub), ...), comps) where
    comps is [('path', k), ('cycle', k)] per component of `y`."""
    ylist = sorted(y)
    adj = {}
    for b in ylist:
        (u, w, _L) = specs[b]
        adj.setdefault(u, []).append(b)
        adj.setdefault(w, []).append(b)
    for v, lst in adj.items():
        assert len(lst) <= 2, "supp(y) has a hub of degree > 2"
    comps = []
    seen = set()
    for b0 in ylist:
        if b0 in seen:
            continue
        cv, ce, st = set(specs[b0][:2]), {b0}, [b0]
        while st:
            b = st.pop()
            for v in specs[b][:2]:
                cv.add(v)
                for b2 in adj[v]:
                    if b2 not in ce:
                        ce.add(b2)
                        st.append(b2)
        seen |= ce
        comps.append(('cycle' if len(cv) == len(ce) else 'path', len(ce)))
    out = []

    def rec(i, used, acc):
        if i == len(ylist):
            out.append(tuple(acc))
            return
        for v in specs[ylist[i]][:2]:
            if v not in used and v not in forbid:
                rec(i + 1, used | {v}, acc + [(ylist[i], v)])
    rec(0, frozenset(), [])
    return out, comps


def map_from(specs, mat, binc, matbr, y_phi, Zbranches):
    """The minority map of a (y, Z, phi) triple: the all-M prescription,
    deviated at every phi rep and at both ends of every Z branch, each
    deviating hub sending its dart to the THIRD branch."""
    m = m_of_matching(specs, mat)
    pairs = [(b, v) for b in Zbranches for v in specs[b][:2]]
    pairs += list(y_phi)
    for (b, v) in pairs:
        t = [i for i in binc[v] if i != b and i != matbr[v]]
        assert len(t) == 1, "hub star not three distinct branches"
        m[v] = (t[0], 0 if specs[t[0]][0] == v else 1)
    return m


def matb(specs, mat):
    out = {}
    for i in mat:
        (u, w, _L) = specs[i]
        out[u] = i
        out[w] = i
    return out


def dist_stratum(specs, n, mat, binc, d, avoiders=None):
    """(GR-55): every PARITY-CONSISTENT minority map at distance exactly
    `d` from the perfect matching `mat`, as (m, y, Z, phi).  `avoiders`
    is the precomputed M-avoiding coset space."""
    E = len(specs)
    mb = matb(specs, mat)
    free = [i for i in range(E) if i not in mat]
    if avoiders is None:
        avoiders = avoid_all(specs, n, mat)
    out = []
    for y in avoiders:
        if len(y) > d or (d - len(y)) % 2:
            continue
        nz = (d - len(y)) // 2
        pool = [i for i in free if i not in y]
        for Z in combinations(pool, nz):
            vz = set()
            ok = True
            for b in Z:
                (u, w, _L) = specs[b]
                if u in vz or w in vz:
                    ok = False
                    break
                vz.add(u)
                vz.add(w)
            if not ok:
                continue
            phis, _comps = sdr_space(specs, y, frozenset(vz))
            for phi in phis:
                out.append((map_from(specs, mat, binc, mb, phi, Z),
                            y, frozenset(Z), phi))
    return out


def layers_exact(specs, n, edges, allverts, hm, tec_cf, lens, mats, binc,
                 dmax=8, want_census=False):
    """Exact (d_par, d_adm, d_fg) by (GR-55) enumeration -- no deviation
    cap below `dmax`, and `dmax` is only a guard.  With `want_census`,
    also returns the optimal-stratum census (n_optimal, n_fully_good,
    per-(M, y, Z)-cell fully-good availability)."""
    av = {i: avoid_all(specs, n, mat) for i, mat in enumerate(mats)}
    d_par = d_adm = d_fg = None
    cens = None
    for d in range(dmax + 1):
        seen = set()
        adm = []
        cells = {}
        for mi, mat in enumerate(mats):
            for (m, y, Z, phi) in dist_stratum(specs, n, mat, binc, d,
                                               av[mi]):
                key = tuple(sorted(m.items()))
                if key in seen:
                    continue
                seen.add(key)
                sols = cm_solve(specs, m)
                assert sols is not None, "(GR-55) map not parity-consistent"
                if d_par is None:
                    d_par = d
                for c in sols:
                    na, nb = odd_balance(specs, m, c)
                    if na != nb:
                        continue
                    col = cm_colouring(specs, m, c)
                    if not admissible(edges, allverts, hm, col):
                        continue
                    good = fully_good_scan(hm, None, tec_cf, lens,
                                           branch_stats(hm, col, 'A'))
                    adm.append((m, c, col, good))
                    ck = (mi, y, Z)
                    a, g = cells.get(ck, (0, 0))
                    cells[ck] = (a + 1, g + (1 if good else 0))
                    break
        if adm and d_adm is None:
            d_adm = d
            if want_census:
                cens = (len(adm), sum(1 for r in adm if r[3]), cells)
        if adm and any(r[3] for r in adm) and d_fg is None:
            d_fg = d
        if d_fg is not None:
            break
    return d_par, d_adm, d_fg, cens


def shape_prep(specs, n):
    edges, allverts, hm, inc, tec, tec_cf, allks = prep_shape(specs)
    return dict(specs=specs, n=n, edges=edges, allverts=allverts, hm=hm,
                inc=inc, tec_cf=tec_cf, lens=hm['lens'],
                mats=perfect_matchings(specs), binc=branches_at(specs, n),
                s_of=hm_spec_map(specs, hm))


def all_maps(specs, dinc, hubs):
    """Every 3^n minority map, in deterministic order."""
    idx = [0] * len(hubs)
    while True:
        yield {v: dinc[v][idx[i]] for i, v in enumerate(hubs)}
        j = len(hubs) - 1
        while j >= 0:
            idx[j] += 1
            if idx[j] < 3:
                break
            idx[j] = 0
            j -= 1
        if j < 0:
            return


def stratum_shapes(gate=True):
    """The `Lambda = empty` `D = 0` `n_hub <= 6` habitat stratum, in
    `gcap.pool_specs` order behind the `cflank.cubic_habitat` gate."""
    for n, specs in pool_specs():
        if gate and not cubic_habitat(n, [(u, w) for (u, w, _L) in specs],
                                      [L for (_u, _w, L) in specs]):
            continue
        yield n, specs


# ------------------------------------------------- [GLW-1] --law -----------

def leg_law():
    """[GLW-1] (GR-56): the split identity and the one-inequality form of
    full-goodness."""
    t0 = time.time()
    print(f"[GLW-1] (GR-56) the split identity  (seed {R_SEED + 1})")
    rng = random.Random(R_SEED + 1)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    pairs = 0
    admiss = 0
    forest_bites = 0
    cflip = 0
    crit = 0
    whole = 0

    def run(tag, specs, n, exhaustive):
        nonlocal pairs, admiss, forest_bites, cflip, crit, whole
        sh = shape_prep(specs, n)
        hm, inc, lens, s_of = sh['hm'], sh['inc'], sh['lens'], sh['s_of']
        dinc = darts_at(specs)
        hubs = sorted(dinc)
        allks = tuple(range(len(hm['ends'])))
        for m in all_maps(specs, dinc, hubs):
            sols = cm_solve(specs, m)
            if sols is None:
                continue
            verdicts = []
            for c in sols:
                na, nb = odd_balance(specs, m, c)
                col = cm_colouring(specs, m, c)
                bal = (na == nb)
                adm = admissible(sh['edges'], sh['allverts'], hm, col)
                if bal and not adm:
                    forest_bites += 1
                if not bal:
                    # (GR-56)(iv): balance IS the whole-graph instance
                    _cap, zm, dl, sg = chunk_inv(hm, inc, allks, m, c, s_of)
                    assert zm == 0 and sg == 0 and dl != 0, \
                        "whole-graph instance disagrees with the balance rider"
                    whole += 1
                    continue
                assert adm, "balanced but not admissible -- forest conjunct bit"
                admiss += 1
                acnt, du, dw = branch_stats(hm, col, 'A')
                ok = True
                for (cf, improper) in sh['tec_cf']:
                    ks = cf[0]
                    dA, dB = fast_defects(cf, lens, acnt, du, dw)
                    cap, zm, dl, sg = chunk_inv(hm, inc, ks, m, c, s_of)
                    assert dA + dB == cap - zm, "(GR-32)(i) sum identity broken"
                    assert dA - dB == dl - sg, \
                        "(GR-56)(i) SPLIT identity broken -- HEADLINE"
                    pairs += 1
                    if improper:
                        assert dA == 3 and dB == 3 and cap == 6 and zm == 0, \
                            "whole graph not (3,3) at a balanced colouring"
                        whole += 1
                        continue
                    if zm + abs(dl - sg) > cap - 6:
                        ok = False
                gs = fully_good_scan(hm, None, sh['tec_cf'], lens,
                                     (acnt, du, dw))
                assert ok == gs, \
                    "(GR-56)(iii) criterion disagrees with fully_good_scan"
                crit += 1
                verdicts.append(gs)
            if len(verdicts) == 2:
                assert verdicts[0] == verdicts[1], \
                    "(GR-56)(v) full-goodness depends on the c-choice"
                cflip += 1

    for tag in ('W3M', 'W3'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        run(tag, specs, n, True)
    print(f"  W3M + W3 exhaustive (all 3^n minority maps): "
          f"{admiss} admissible (m, c) pairs, {pairs} (colouring, chunk) "
          f"pairs -- BOTH identities hold at every one")
    npool = 0
    for n, specs in stratum_shapes():
        if rng.random() >= 0.02:
            continue
        npool += 1
        run('pool', specs, n, True)
    print(f"  + {npool} seeded stratum shapes (rate 0.02), exhaustive per "
          f"shape: cumulative {pairs} (colouring, chunk) pairs, "
          f"{admiss} admissible (m, c) pairs")
    print(f"  (GR-56)(iii) the ONE-INEQUALITY criterion "
          f"`z_mono + |delta_S - sigma_S| <= cap(S) - 6` agrees with "
          f"`fully_good_scan` at all {crit} admissible colourings")
    print(f"  (GR-56)(iv) the whole-graph instance IS the balance rider: "
          f"{whole} instances, no disagreement")
    print(f"  (GR-56)(v) full-goodness is a function of the minority map "
          f"alone: verified at {cflip} c-pairs")
    print(f"  the forest conjunct of `admissible` never bit: "
          f"{forest_bites} balanced-but-not-admissible colourings "
          f"(MEASURED on this census, not proven)")
    print(f"  [{time.time() - t0:.0f}s]")


# ------------------------------------------------- [GLW-2] --nf ------------

def leg_nf():
    """[GLW-2] (GR-55): the (y, Z, phi) normal form of the distance-d
    deviation stratum, and the closed form for the optimal stratum."""
    t0 = time.time()
    print(f"[GLW-2] (GR-55) the deviation normal form  (seed {R_SEED + 2})")
    rng = random.Random(R_SEED + 2)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    cells = 0
    prodchk = 0
    dimchk = 0

    def certify(specs, n, dmax):
        nonlocal cells, prodchk, dimchk
        sh = shape_prep(specs, n)
        dinc = darts_at(specs)
        hubs = sorted(dinc)
        allpc = []
        for m in all_maps(specs, dinc, hubs):
            if cm_solve(specs, m) is not None:
                allpc.append(m)
        for mat in sh['mats']:
            av = avoid_all(specs, n, mat)
            assert len(av) == 1 << (n // 2 - 1), \
                "(GR-55) Cor. 1: M-avoiding space is not 2^(n/2 - 1)"
            assert len({len(y) % 2 for y in av}) == 1, \
                "(GR-55)(iii): M-avoiding representatives of mixed weight " \
                "parity -- the per-matching distance parity fails"
            dimchk += 1
            base = m_of_matching(specs, mat)
            for d in range(dmax + 1):
                brute = {tuple(sorted(m.items())) for m in allpc
                         if sum(1 for v in hubs if m[v] != base[v]) == d}
                para = dist_stratum(specs, n, mat, sh['binc'], d, av)
                got = {tuple(sorted(m.items())) for (m, _y, _Z, _p) in para}
                assert len(got) == len(para), "(GR-55) parametrization not 1-1"
                assert got == brute, \
                    "(GR-55) normal form misses / overshoots the stratum"
                cells += 1
            w, mins = min_avoiders(specs, n, mat)
            dpar = min(sum(1 for v in hubs if m[v] != base[v]) for m in allpc)
            assert w == dpar, "(GR-44) d_par(M) = w_M contradicted"
            prod = 0
            for y in mins:
                phis, comps = sdr_space(specs, y)
                pr = 1
                for (kind, k) in comps:
                    pr *= (k + 1) if kind == 'path' else 2
                assert pr == len(phis), \
                    "(GR-57)(i) component product formula broken"
                prod += pr
            opt = dist_stratum(specs, n, mat, sh['binc'], w, av)
            assert prod == len(opt), \
                "(GR-55) Cor. 2: optimal-stratum count formula broken"
            prodchk += 1

    for tag in ('W3M', 'W3'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        certify(specs, n, 4)
    npool = 0
    for n, specs in stratum_shapes():
        if rng.random() >= 0.01:
            continue
        npool += 1
        certify(specs, n, 4)
    print(f"  W3M + W3 + {npool} seeded stratum shapes (rate 0.01): the "
          f"normal form is EXACT at {cells} (matching, distance) cells -- "
          f"every parity-consistent map at distance d is one (y, Z, phi) "
          f"triple and conversely")
    print(f"  the M-avoiding coset space has dimension n/2 - 1 exactly at "
          f"all {dimchk} (shape, matching) pairs")
    print(f"  the optimal-stratum closed form "
          f"|{{m : dist(m, M) = w_M}}| = SUM_y PROD_paths (k+1) "
          f"PROD_cycles 2 holds at all {prodchk} (shape, matching) pairs")
    nmd = 0
    for n, specs in stratum_shapes():
        if rng.random() >= 0.01:
            continue
        sh = shape_prep(specs, n)
        a = layers_exact(specs, n, sh['edges'], sh['allverts'], sh['hm'],
                         sh['tec_cf'], sh['lens'], sh['mats'], sh['binc'])
        b = min_dev(specs, sh['edges'], sh['allverts'], sh['hm'],
                    sh['tec_cf'], sh['lens'], sh['mats'], 3)
        assert a[:3] == b, "(GR-55) layer triple disagrees with gdev.min_dev"
        nmd += 1
    print(f"  the (GR-55)-enumerated layer triple (d_par, d_adm, d_fg) "
          f"agrees with the landed `gdev.min_dev` at all {nmd} seeded "
          f"stratum shapes")
    print(f"  [{time.time() - t0:.0f}s]")


def layers_at_matching(sh, specs, n, mat, dmax=8):
    """The PER-MATCHING layer triple (d_par(M), d_adm(M), d_fg(M)) at one
    perfect matching -- the quantities GADM's stronger (a') variant is
    stated over."""
    av = avoid_all(specs, n, mat)
    dp = da = df = None
    for d in range(dmax + 1):
        for (m, _y, _Z, _phi) in dist_stratum(specs, n, mat, sh['binc'], d,
                                              av):
            if dp is None:
                dp = d
            sols = cm_solve(specs, m)
            assert sols is not None
            for c in sols:
                na, nb = odd_balance(specs, m, c)
                if na != nb:
                    continue
                col = cm_colouring(specs, m, c)
                if not admissible(sh['edges'], sh['allverts'], sh['hm'], col):
                    continue
                if da is None:
                    da = d
                if df is None and fully_good_scan(
                        sh['hm'], None, sh['tec_cf'], sh['lens'],
                        branch_stats(sh['hm'], col, 'A')):
                    df = d
                break
        if df is not None:
            break
    return dp, da, df


# ------------------------------------------------- [GLW-3] --exh -----------

def leg_exh():
    """[GLW-3] (GR-58): (a') EXHAUSTIVELY over the whole `Lambda = empty`
    `D = 0` `n_hub <= 6` habitat stratum, optimum with NO deviation cap."""
    t0 = time.time()
    print(f"[GLW-3] (GR-58) the exhaustive (a') census "
          f"(no seed: the sweep is the whole stratum)")
    lay = {}
    nsh = 0
    nodd = 0
    broken = []
    worst = None
    tight = 0
    cell_all_ok = 0
    cell_dead = 0
    worst_cell = None
    freedom_min = None
    contentful = 0
    odd_worst = None
    for n, specs in stratum_shapes():
        sh = shape_prep(specs, n)
        d_par, d_adm, d_fg, cens = layers_exact(
            specs, n, sh['edges'], sh['allverts'], sh['hm'], sh['tec_cf'],
            sh['lens'], sh['mats'], sh['binc'], want_census=True)
        nsh += 1
        assert d_adm is not None, \
            f"d_adm = infinity within the guard at {sorted(specs)} -- " \
            f"E1 clause (v) HEADLINE (an exhausted cap is not infinity)"
        assert d_fg is not None, \
            f"d_fg NOT FOUND within the guard at {sorted(specs)} -- " \
            f"disclose the cap; an exhausted cap is not infinity"
        if d_fg != d_adm:
            broken.append((sorted(specs), d_adm, d_fg))
            continue
        lay[(d_par, d_adm, d_fg)] = lay.get((d_par, d_adm, d_fg), 0) + 1
        nopt, ngood, cells = cens
        assert ngood > 0, "census misses the fully-good optimum"
        if ngood < nopt:
            contentful += 1
        if worst is None or ngood * worst[1] < worst[0] * nopt:
            worst = (ngood, nopt, tuple(sorted(specs)))
        if freedom_min is None or nopt < freedom_min[0]:
            freedom_min = (nopt, tuple(sorted(specs)))
        dead = sum(1 for (a, g) in cells.values() if g == 0)
        if dead == 0:
            cell_all_ok += 1
        else:
            cell_dead += 1
            if worst_cell is None or dead / len(cells) > worst_cell[0] / worst_cell[1]:
                worst_cell = (dead, len(cells), tuple(sorted(specs)))
        wodd = sum(1 for (_u, _w, L) in specs if L % 2)
        if wodd:
            nodd += 1
            if odd_worst is None or ngood * odd_worst[1] < odd_worst[0] * nopt:
                odd_worst = (ngood, nopt, tuple(sorted(specs)))
        if d_par == d_adm:
            tight += 1
    assert not broken, \
        f"(a') REFUTED at finite witnesses {broken[:3]} -- E2's refutation " \
        f"branch, HEADLINE (a finite d_fg > d_adm is a LAW-refutation, " \
        f"never E1)"
    print(f"  {nsh} labelled habitat shapes -- the ENTIRE stratum, no "
          f"subsample; `d_fg = d_adm` at EVERY one, optimum computed "
          f"with no deviation cap")
    print(f"    layer triples (d_par, d_adm, d_fg) -> count: "
          f"{sorted(lay.items())}")
    print(f"    balance layer: {tight} shapes at d_adm = d_par, "
          f"{nsh - tight} above it (a (b') by-product, not this "
          f"direction's target)")
    print(f"    odd-carrying shapes: {nodd}; worst fully-good fraction "
          f"among their optima: {odd_worst[0]}/{odd_worst[1]}")
    print(f"    optimal stratum: worst fully-good fraction "
          f"{worst[0]}/{worst[1]}; smallest optimal stratum "
          f"{freedom_min[0]} map(s); {contentful} shapes carry a "
          f"NON-fully-good optimum (where (a') has content)")
    print(f"    the (M, y, Z) cell axis: at {cell_all_ok} shapes EVERY "
          f"optimal cell carries a fully-good SDR; at {cell_dead} shapes "
          f"some cell is DEAD -- there the exchange must move y, Z or M, "
          f"not only the SDR (GADM's named sticking case, relocated)")
    if worst_cell:
        print(f"    worst cell profile: {worst_cell[0]}/{worst_cell[1]} "
              f"optimal cells dead at specs {list(worst_cell[2])}")
    # ---- part (b): the PER-MATCHING variant, exhaustively
    npm = 0
    viol = []
    gaps = {}
    vshapes = set()
    byn = {}
    for n, specs in stratum_shapes():
        sh = shape_prep(specs, n)
        for mi, mat in enumerate(sh['mats']):
            npm += 1
            dp, da, df = layers_at_matching(sh, specs, n, mat)
            assert da is not None and df is not None, \
                f"per-matching layer not found within the guard at " \
                f"{sorted(specs)} M#{mi} -- disclose the cap"
            if df != da:
                g = df - da
                gaps[g] = gaps.get(g, 0) + 1
                vshapes.add(tuple(sorted(specs)))
                byn[n] = byn.get(n, 0) + 1
                if len(viol) < 1 or n < viol[0][0]:
                    viol.insert(0, (n, tuple(sorted(specs)), mi, dp, da, df))
            assert (df - da) % 2 == 0, \
                "(GR-55)(iii) violated: a per-matching layer gap is odd"
    print(f"  (GR-59) THE PER-MATCHING VARIANT OF (a') IS REFUTED. Over "
          f"all {npm} (shape, perfect matching) pairs of the stratum, "
          f"{sum(gaps.values())} carry `d_adm(M) < d_fg(M) < infinity`, at "
          f"{len(vshapes)} distinct shapes; gap histogram "
          f"{sorted(gaps.items())} (always EVEN by (GR-55)(iii)); "
          f"violations by n_hub {sorted(byn.items())}")
    print(f"    smallest witness: n_hub = {viol[0][0]}, M#{viol[0][2]}, "
          f"(d_par, d_adm, d_fg) at that matching = "
          f"({viol[0][3]}, {viol[0][4]}, {viol[0][5]}), specs "
          f"{list(viol[0][1])}")
    print(f"    this is NOT an (a') refutation and NOT an E1/E2 event: the "
          f"min-over-matchings form is what the closure chain consumes and "
          f"it holds at every one of the {nsh} shapes above.  What dies is "
          f"the stronger per-matching variant GADM flagged as a separate "
          f"recorded result -- so `min_M` is LOAD-BEARING and no (a') proof "
          f"can work at a fixed anchor matching.")
    print(f"  [{time.time() - t0:.0f}s]")


def sdr_graph(specs, y, phis):
    """The graph on SDRs of `y` whose edges change exactly ONE branch's
    representative -- the elementary (GR-57) SHIFT.  Returns (component
    count, component sizes sorted, edge list as index pairs)."""
    idx = {p: i for i, p in enumerate(phis)}
    adj = {i: [] for i in range(len(phis))}
    edges = []
    for i, p in enumerate(phis):
        for j, q in enumerate(phis):
            if j <= i:
                continue
            diff = [k for k in range(len(p)) if p[k] != q[k]]
            if len(diff) == 1:
                adj[i].append(j)
                adj[j].append(i)
                edges.append((i, j))
    seen, comps = set(), []
    for i in range(len(phis)):
        if i in seen:
            continue
        c, st = {i}, [i]
        while st:
            v = st.pop()
            for u in adj[v]:
                if u not in c:
                    c.add(u)
                    st.append(u)
        seen |= c
        comps.append(len(c))
    return len(comps), sorted(comps), edges


# ------------------------------------------------- [GLW-4] --sdr -----------

def leg_sdr():
    """[GLW-4] (GR-57): the SDR exchange calculus on the optimal stratum,
    and the axis verdict on GADM's named sticking case."""
    t0 = time.time()
    print(f"[GLW-4] (GR-57) the SDR exchange calculus  (seed {R_SEED + 4})")
    rng = random.Random(R_SEED + 4)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    nshift = ncomp = 0
    twohub = 0
    cutmove = 0

    def calculus(specs, n):
        nonlocal nshift, ncomp, twohub, cutmove
        sh = shape_prep(specs, n)
        for mat in sh['mats']:
            mb = matb(specs, mat)
            w, mins = min_avoiders(specs, n, mat)
            for y in mins:
                phis, comps = sdr_space(specs, y)
                ncy = sum(1 for (kind, _k) in comps if kind == 'cycle')
                pathprod = 1
                for (kind, k) in comps:
                    if kind == 'path':
                        pathprod *= (k + 1)
                ncc, sizes, eds = sdr_graph(specs, y, phis)
                assert ncc == (1 << ncy), \
                    "(GR-57)(ii) SDR shift graph component count != 2^#cycles"
                assert all(s == pathprod for s in sizes), \
                    "(GR-57)(ii) SDR shift components are not the path product"
                ncomp += 1
                for (i, j) in eds:
                    m1 = map_from(specs, mat, sh['binc'], mb, phis[i], ())
                    m2 = map_from(specs, mat, sh['binc'], mb, phis[j], ())
                    moved = [v for v in m1 if m1[v] != m2[v]]
                    assert len(moved) == 2, \
                        "(GR-57)(iii) elementary shift moves != 2 hubs"
                    twohub += 1
                    base = m_of_matching(specs, mat)
                    assert (sum(1 for v in m1 if m1[v] != base[v])
                            == sum(1 for v in m2 if m2[v] != base[v])), \
                        "(GR-57)(iii) elementary shift is not distance-preserving"
                    mu1 = [0] * len(specs)
                    mu2 = [0] * len(specs)
                    for v in m1:
                        mu1[m1[v][0]] ^= 1
                        mu2[m2[v][0]] ^= 1
                    diff = xor_vec(mu1, mu2)
                    cut = xor_vec(delta_of(specs, {moved[0]}),
                                  delta_of(specs, {moved[1]}))
                    assert diff == cut, \
                        "(GR-57)(iii) shift does not move mu by the two-hub cut"
                    cutmove += 1
                    assert any(diff), \
                        "(GR-57)(iii) shift claimed cross-mu but mu is fixed"
                    nshift += 1

    for tag in ('W3M', 'W3', 'W4'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        calculus(specs, n)
    npool = 0
    for n, specs in stratum_shapes():
        if rng.random() >= 0.01:
            continue
        npool += 1
        calculus(specs, n)
    print(f"  W3M/W3/W4 + {npool} seeded stratum shapes: the SDR space of "
          f"every minimum-weight M-avoiding representative factors as "
          f"PROD_paths (k+1) x PROD_cycles 2 and the elementary-shift "
          f"graph has exactly 2^#cycles components ({ncomp} (M, y) cells)")
    print(f"  every one of the {nshift} elementary shifts is a "
          f"DISTANCE-PRESERVING 2-hub move ({twohub} checks) that moves "
          f"mu by the two-hub cut and therefore CROSSES mu-classes "
          f"({cutmove} checks) -- the second exchange axis GADM's census "
          f"named as missing")
    # ---- the axis verdict over the whole stratum
    lvl = {0: 0, 1: 0, 2: 0, 3: 0}
    for n, specs in stratum_shapes():
        sh = shape_prep(specs, n)
        _dp, d_adm, d_fg, cens = layers_exact(
            specs, n, sh['edges'], sh['allverts'], sh['hm'], sh['tec_cf'],
            sh['lens'], sh['mats'], sh['binc'], want_census=True)
        assert d_fg == d_adm, "(a') REFUTED -- HEADLINE"
        cells = cens[2]
        okM = {mi for (mi, _y, _Z), (_a, g) in cells.items() if g}
        okMy = {(mi, y) for (mi, y, _Z), (_a, g) in cells.items() if g}
        worst = 0
        for (mi, y, Z), (_a, g) in cells.items():
            if g:
                continue
            if (mi, y) in okMy:
                worst = max(worst, 1)
            elif mi in okM:
                worst = max(worst, 2)
            else:
                worst = max(worst, 3)
        lvl[worst] += 1
    print(f"  the exchange-axis ladder over the WHOLE stratum "
          f"(worst optimal cell per shape): "
          f"SDR alone suffices everywhere {lvl[0]}; must re-match Z "
          f"{lvl[1]}; must change the coset representative y {lvl[2]}; "
          f"must change the perfect matching M {lvl[3]}")
    print(f"  [{time.time() - t0:.0f}s]")


def min_form(specs, n, dmax=8):
    """The min-over-matchings layer triple, exhaustive (full chunk scan);
    asserts (a') at the shape."""
    sh = shape_prep(specs, n)
    d_par, d_adm, d_fg, cens = layers_exact(
        specs, n, sh['edges'], sh['allverts'], sh['hm'], sh['tec_cf'],
        sh['lens'], sh['mats'], sh['binc'], dmax=dmax, want_census=True)
    assert d_adm is not None, "d_adm not found within the guard -- disclose"
    assert d_fg is not None, "d_fg not found within the guard -- disclose"
    assert d_fg == d_adm, \
        "(a') REFUTED at a finite witness -- E2's refutation branch, HEADLINE"
    return d_par, d_adm, d_fg, cens


def rank_light(specs, n, mats, rng, cap=12, tag=''):
    """(a') at a shape too big for the 2^M chunk scan: the min-over-the-
    given-matchings parity optimum, its admissible members, and a RANK
    certificate of full-goodness at the optimum (README S4 convention 2).
    Returns (w, n_opt, n_adm, n_rank_tests, certified)."""
    edges = subdivide(specs)
    allverts = sorted(verts_of(edges), key=str)
    hm = light_hm(edges)
    binc = branches_at(specs, n)
    best = None
    for mat in mats:
        w, _mins = min_avoiders(specs, n, mat)
        if best is None or w < best[0]:
            best = (w, mat)
    w, mat = best
    strat = dist_stratum(specs, n, mat, binc, w)
    nadm = 0
    tests = 0
    cert = False
    for (m, _y, _Z, _phi) in strat:
        sols = cm_solve(specs, m)
        assert sols is not None
        for c in sols:
            na, nb = odd_balance(specs, m, c)
            if na != nb:
                continue
            col = cm_colouring(specs, m, c)
            if not admissible(edges, allverts, hm, col):
                continue
            nadm += 1
            if not cert and tests < cap:
                tests += 1
                if fully_good_rank(edges, allverts, hm, col, rng):
                    cert = True
            break
    assert nadm > 0, f"{tag}: no admissible colouring at the parity optimum"
    assert cert, \
        f"{tag}: no RANK-certified fully-good colouring among the first " \
        f"{tests} admissible optima (cap {cap}) -- raise the cap before " \
        f"reading anything into this"
    return w, len(strat), nadm, tests, cert


def sample_matchings(specs, n, rng, want, tries=400):
    """Seeded distinct perfect matchings built by `gadm.complete_matching`
    from a random forced branch; `perfect_matchings` is NEVER called at
    n >= 30."""
    from gadm import complete_matching
    out = []
    seen = set()
    for _ in range(tries):
        forced, cov = [], set()
        for f in rng.sample(range(len(specs)), min(6, len(specs))):
            (u, w, _L) = specs[f]
            if u in cov or w in cov:
                continue
            forced.append(f)
            cov.add(u)
            cov.add(w)
        mat = complete_matching(specs, n, forced)
        if mat is None or mat in seen:
            continue
        seen.add(mat)
        out.append(mat)
        if len(out) >= want:
            break
    assert out, "no perfect matching constructed"
    return out


# ------------------------------------------------- [GLW-5] --big -----------

def leg_big():
    """[GLW-5] (GR-59): (a') at the shapes the n <= 6 stratum cannot
    reach -- including the first ODD-CARRYING n = 30 tests."""
    t0 = time.time()
    print(f"[GLW-5] (GR-59) (a') off the pool  (seed {R_SEED + 5})")
    rng = random.Random(R_SEED + 5)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    for tag in ('W3M', 'W3', 'W4'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        d_par, d_adm, d_fg, cens = min_form(specs, n)
        nopt, ngood, cells = cens
        print(f"  {tag} (n = {n}, EXHAUSTIVE min-form, full chunk scan): "
              f"(d_par, d_adm, d_fg) = ({d_par}, {d_adm}, {d_fg}); optimal "
              f"stratum {nopt} maps in {len(cells)} (M, y, Z) cells, "
              f"{ngood} fully good")
    specs, _pent = nko2v_specs()
    d_par, d_adm, d_fg, cens = min_form(specs, 10)
    print(f"  NKo2v (n = 10, four odd branches, EXHAUSTIVE min-form): "
          f"(d_par, d_adm, d_fg) = ({d_par}, {d_adm}, {d_fg}); optimal "
          f"stratum {cens[0]} maps, {cens[1]} fully good")
    specs2, _p2, _F2, _c2 = nk_specs(2)
    d_par, d_adm, d_fg, cens = min_form(specs2, 10)
    print(f"  NK(2) (n = 10, all-even, EXHAUSTIVE min-form): "
          f"(d_par, d_adm, d_fg) = ({d_par}, {d_adm}, {d_fg}) -- agrees with "
          f"GADM's landed 2/2/2")
    for m, tag in ((5, 'CL5'), (6, 'CL6')):
        specs_l = ladder_specs(m, {0: 2, 1: 2, 2: 2})
        nl = 2 * m
        w, nopt, nadm, tests, _c = rank_light(specs_l, nl,
                                              perfect_matchings(specs_l),
                                              rng, tag=tag)
        print(f"  {tag} (n = {nl}, rank-light): parity optimum w = {w}; "
              f"{nadm}/{nopt} optimal maps admissible; fully good "
              f"RANK-CERTIFIED at the optimum ({tests} rank tests) -- so "
              f"d_fg = d_adm = {w} there")
    (_nm5, n5, specs5, _f5, _S5, _e5) = by_tag['W5']
    w, nopt, nadm, tests, _c = rank_light(specs5, n5,
                                          perfect_matchings(specs5), rng,
                                          tag='W5')
    print(f"  W5 (n = {n5}, rank-light -- the 2^24 chunk scan is out of "
          f"budget): parity optimum w = {w}; {nadm}/{nopt} optimal maps "
          f"admissible; fully good RANK-CERTIFIED at the optimum "
          f"({tests} rank tests) -- d_fg = d_adm = {w}")
    # ---- the first ODD-CARRYING n = 30 tests
    for tag, mk, nodd in (('NKp(6)', lambda: nkp_specs(6), 6),
                          ('NK55(6)', lambda: nk55_specs(6), 2)):
        sp, _pent = mk()
        n30 = 30
        assert is_bridgeless(sp, n30), f"{tag} not bridgeless"
        assert sum(1 for (_u, _w, L) in sp if L % 2) == nodd
        mats = sample_matchings(sp, n30, rng, 40)
        ws = []
        for mat in mats:
            ws.append(min_avoiders(sp, n30, mat)[0])
        w, nopt, nadm, tests, _c = rank_light(sp, n30, mats, rng, tag=tag)
        print(f"  {tag} (n = 30, {nodd} odd branches -- the first "
              f"ODD-CARRYING large-n (a') test): over {len(mats)} sampled "
              f"perfect matchings (a CAP, disclosed; `perfect_matchings` "
              f"is never called at n = 30) min w_M = {w} "
              f"(sampled range {min(ws)}..{max(ws)}); at the achieving "
              f"matching {nadm}/{nopt} optimal maps are balanced and "
              f"admissible and the optimum is fully good, RANK-CERTIFIED "
              f"({tests} rank tests) -- so d_fg(M) = d_adm(M) = "
              f"d_par(M) = {w} there")
        print(f"    NOT claimed: `min_M w_M` over ALL perfect matchings of "
              f"a 30-hub cubic multigraph -- out of reach, so the min-form "
              f"(a') EQUALITY at {tag} rests on the matching sample")
    print(f"  [{time.time() - t0:.0f}s]")


def verify_triple(specs, n, mat, binc, y, Z, phi, d):
    """The adversarial verifier for a (GR-55) triple: every clause of the
    normal form re-checked from scratch, then the built map's distance
    and parity-consistency.  Raises AssertionError on any doctored input
    (the F13 guard); returns the map."""
    matset = set(mat)
    assert all(b not in matset for b in y), "y meets the matching (doctored)"
    assert all(b not in matset for b in Z), "Z meets the matching (doctored)"
    assert not (set(y) & set(Z)), "y and Z overlap (doctored)"
    cycles = fundamental_cycles(specs, n)
    x = [1 if i in set(y) else 0 for i in range(len(specs))]
    assert in_coset(specs, n, x, cycles), "chi_y is not in Phi (doctored)"
    vz = set()
    for b in Z:
        (u, w, _L) = specs[b]
        assert u not in vz and w not in vz, "Z is not a matching (doctored)"
        vz.add(u)
        vz.add(w)
    seen = set()
    assert sorted(b for (b, _v) in phi) == sorted(y), \
        "phi does not select exactly y (doctored)"
    for (b, v) in phi:
        assert v in specs[b][:2], "phi rep is not an end of its branch"
        assert v not in seen, "phi reuses a hub (doctored)"
        assert v not in vz, "phi rep sits on a Z branch (doctored)"
        seen.add(v)
    assert len(y) + 2 * len(Z) == d, "the triple's size is not d (doctored)"
    m = map_from(specs, mat, binc, matb(specs, mat), phi, Z)
    base = m_of_matching(specs, mat)
    assert sum(1 for v in m if m[v] != base[v]) == d, "distance != d"
    assert cm_solve(specs, m) is not None, "built map not parity-consistent"
    return m


# ------------------------------------------------- [GLW-6] --adv -----------

def leg_adv():
    """[GLW-6] the F13 falsification controls: each guard gets a witness
    it must reject and a negative control it must pass."""
    t0 = time.time()
    print(f"[GLW-6] falsification controls  (seed {R_SEED + 6})")
    rng = random.Random(R_SEED + 6)
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    (_nm, n, specs, _f, _S, _e) = by_tag['W3']
    sh = shape_prep(specs, n)
    mat = sh['mats'][0]
    w, mins = min_avoiders(specs, n, mat)
    y = mins[0]
    phis, _comps = sdr_space(specs, y)
    phi = phis[0]
    verify_triple(specs, n, mat, sh['binc'], y, (), phi, w)
    print(f"  (1) the (GR-55) verifier PASSES the honest triple "
          f"(|y| = {w}, Z = empty)")
    dphi = list(phi)
    if len(dphi) >= 2:
        dphi[1] = (dphi[1][0], dphi[0][1])
    bad = False
    try:
        verify_triple(specs, n, mat, sh['binc'], y, (), tuple(dphi), w)
    except AssertionError:
        bad = True
    assert bad, "a hub-reusing SDR was ACCEPTED -- the guard is untested"
    print(f"      and REJECTS a hub-reusing selection (the pinned "
          f"counter-fact: `gpsa.sdr_build` only ever emits ONE selection "
          f"per component, so a reuse never arises there and is never "
          f"tested by it)")
    ymat = frozenset(list(y)[:-1] + [sorted(mat)[0]])
    bad = False
    try:
        verify_triple(specs, n, mat, sh['binc'], ymat, (), phi, w)
    except AssertionError:
        bad = True
    assert bad, "a matching-meeting y was ACCEPTED"
    print(f"  (2) REJECTS a representative meeting the anchor matching; "
          f"the honest one passes (negative control above)")
    # ---- (3) the |delta - sigma| term is load-bearing
    hm, inc, lens, s_of = sh['hm'], sh['inc'], sh['lens'], sh['s_of']
    dinc = darts_at(specs)
    hubs = sorted(dinc)
    fired = 0
    checked = 0
    for m in all_maps(specs, dinc, hubs):
        sols = cm_solve(specs, m)
        if sols is None:
            continue
        c = sols[0]
        na, nb = odd_balance(specs, m, c)
        if na != nb:
            continue
        col = cm_colouring(specs, m, c)
        if not admissible(sh['edges'], sh['allverts'], hm, col):
            continue
        checked += 1
        stats = branch_stats(hm, col, 'A')
        truth = fully_good_scan(hm, None, sh['tec_cf'], lens, stats)
        doctored = True
        for (cf, improper) in sh['tec_cf']:
            if improper:
                continue
            cap, zm, dl, sg = chunk_inv(hm, inc, cf[0], m, c, s_of)
            if zm > cap - 6:                      # the |delta - sigma| term dropped
                doctored = False
        if doctored != truth:
            fired += 1
    assert fired > 0, \
        "dropping the |delta_S - sigma_S| term never misclassified -- the " \
        "term would be vacuous and (GR-56)(iii) would not be sharp"
    print(f"  (3) the `|delta_S - sigma_S|` term is LOAD-BEARING: the "
          f"criterion with it dropped misclassifies {fired} of {checked} "
          f"admissible W3 colourings (must-fire); with it, 0 (asserted in "
          f"--law)")
    # ---- (4) the 2^(n/2-1) count is not an artifact
    free, part, kern = avoid_space(specs, n, mat)
    cycles = fundamental_cycles(specs, n)
    pos = {b: j for j, b in enumerate(free)}
    tau = even_vec(specs)
    rows, rhs = [], []
    for cyc in cycles[:-1]:                       # one equation deliberately dropped
        r = 0
        for i in cyc:
            if i in pos:
                r ^= 1 << pos[i]
        rows.append(r)
        rhs.append(sum(tau[i] for i in cyc) % 2)
    sol = gf2_affine(rows, rhs, len(free))
    assert sol is not None and len(sol[1]) == len(kern) + 1, \
        "dropping a cycle equation did not enlarge the solution space -- " \
        "the cycle system is degenerate and the 2^(n/2-1) count is an artifact"
    print(f"  (4) the M-avoiding system is non-degenerate: dropping one "
          f"cycle equation raises the solution dimension {len(kern)} -> "
          f"{len(sol[1])} (must-fire), so `2^(n/2 - 1)` is a rank "
          f"statement and not an accident")
    # ---- (5) E1 clause (iv): finite d_fg > d_adm vs d_fg = infinity
    sp4 = ((0, 1, 5), (0, 2, 4), (0, 3, 2), (1, 2, 2), (1, 3, 2), (2, 3, 3))
    sh4 = shape_prep(list(sp4), 4)
    dp, da, df = layers_at_matching(sh4, list(sp4), 4, sh4['mats'][0])
    assert da is not None and df is not None and df > da, \
        "the per-matching witness did not reproduce"
    mn = min_form(list(sp4), 4)
    assert mn[2] == mn[1], "the min-form must still hold at the witness"
    print(f"  (5) E1 clause (iv) discriminator: at the n_hub = 4 witness "
          f"the PER-MATCHING triple is ({dp}, {da}, {df}) -- a FINITE "
          f"d_fg(M) > d_adm(M), reported as a per-matching-variant "
          f"refutation -- while the MIN-FORM triple is {mn[:3]}, so (a') "
          f"itself is untouched: the two quantifiers are kept apart "
          f"(negative control)")
    # ---- (6) E1 clause (v): an exhausted cap is not infinity
    capped = layers_at_matching(sh4, list(sp4), 4, sh4['mats'][0], dmax=1)
    assert capped[2] is None, "the capped search should not have found d_fg"
    print(f"  (6) E1 clause (v) discriminator: the SAME search at cap "
          f"dmax = 1 returns d_fg = NOT-FOUND-WITHIN-CAP, never infinity; "
          f"at the full guard it returns {df}.  A synthetic genuinely-"
          f"unsatisfiable predicate (`n_A = n_B + 1` with an even number "
          f"of odd branches) has NO solution at FULL enumeration -- that, "
          f"and only that, is an `infinity`")
    sat = 0
    for m in all_maps(specs, dinc, hubs):
        sols = cm_solve(specs, m)
        if sols is None:
            continue
        for c in sols:
            na, nb = odd_balance(specs, m, c)
            if na == nb + 1:
                sat += 1
    assert sat == 0, "the impossible predicate was satisfied -- mock broken"
    print(f"      (the mock: 0 solutions at FULL 3^{n} enumeration of W3, "
          f"against {checked} genuine balanced-admissible ones)")
    print(f"  [{time.time() - t0:.0f}s]")


# ---------------------------------------------------------------- main -----

def main():
    args = sys.argv[1:]
    modes = {'--law': leg_law, '--nf': leg_nf, '--exh': leg_exh,
             '--sdr': leg_sdr, '--big': leg_big, '--adv': leg_adv}
    if not args or args == ['--validate']:
        order = ['--law', '--nf', '--adv', '--sdr', '--big', '--exh']
    else:
        order = [a for a in args if a in modes]
        assert len(order) == len(args), f"unknown mode in {args}"
    t0 = time.time()
    print(f"GLAW -- (a'), the `d_fg = d_adm` law (Phase 39, direction "
          f"GLAW; base seed {R_SEED}; PYTHONHASHSEED=0 assumed)")
    for a in order:
        modes[a]()
    print(f"OK -- all requested GLAW modes PASSED "
          f"[{time.time() - t0:.0f}s total]")


if __name__ == '__main__':
    main()
