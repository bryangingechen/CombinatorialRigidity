#!/usr/bin/env python3
"""YLOC -- direction YLOC (Phase 39, seventh fan-out, 2026-08-19): does
GBAL's (GR-49)-(GR-54) instrument LOCALIZE to proper chunks, and does it
discharge input (Y) -- (a')'s named residual, §(K-grid) (GR-60)?

Answers `notes/Pencil-fanout.md` §"Twentieth direction -- YLOC"; the
mathematics is `notes/Pencil-informal-grid.md` §(K-grid) *Steps G80-G85*, labels (GR-61)-(GR-66).

Everything here is at `Lambda = empty`, `D = 0`, modulo (GR-4').  Nothing
here closes (GR-15); (a') is NOT hit here, so E3 (ARMED by GBAL's
entry-5 HIT) does not fire.

Modes
-----
--loc     (GR-61): the (GR-56) chunk invariants re-expressed in (GR-49)'s
          one-bit-per-branch coordinate `z`, asserted equal to
          `glaw.chunk_inv` at every (admissible z, chunk) pair; and the
          DEGENERACY that makes GBAL's reduction whole-graph-only --
          `E(G°)` is the unique chunk with no interiors, so it is the
          unique chunk whose inequality is a function of `z|_O` alone.
--fibre   (GR-62): the REFUTATION of the localization's step 2 -- full
          goodness is NOT a function of the (GR-50) degree data
          (balanced pattern + even-branch in-degree vector), witnessed by
          two admissible balanced `z` in one fibre of opposite verdict.
          So no degree-constrained-orientation criterion can decide the
          proper-chunk instances.
--par     (GR-63): the coordinator's PREDICTED obstruction tested and
          REFUTED as stated -- (GR-52)'s parity step is a per-hub-subset
          identity (`Sum_{v in R} a_v = 2 e_H(R)`), available at every
          `R`, so it is not where the chain breaks.
--coll    (GR-64): the COLLISION bound -- a colouring-free lower bound on
          `d_fg` coupling (Y)'s distance quantifier to its chunk
          constraints, its `<= 2` per-chunk ceiling, its packing form,
          and its use as an anchor-matching prune.
--fit     (GR-65): the fit identity -- `dist(m, M)` and `z_mono(S)` are
          the SAME statistic (the minority dart on a prescribed branch),
          which is what names the successor instrument.
--cert    (GR-66): GBAL's own certificate measured against (Y) -- its
          deviation distance versus `d_adm`, and its full-goodness rate.
--adv     F13 falsification controls, each with a must-fire witness and a
          negative control.
--validate  all six in one process.

Discipline (`notes/scripts/README.md` §§1-4): exact integers / GF(2)
throughout, no floating point; every rng seeded from R_SEED and printed;
no bare `set` printed; imports read-only from the canonical layer.  No
geometry is sampled anywhere in this driver -- every object is a hub
multigraph, a branch colouring or a matching -- so the `plane_basis`
degeneracy precedent has no sampled placement to guard; the standing
guard is discharged instead by routing every structural verdict through
the LANDED oracles (`cflank.admissible` for admissibility,
`gorient.fully_good_scan` for full goodness, `glaw.chunk_inv` for the
(GR-56) invariants, `gbal.*` for the z-form) and asserting agreement.
Rank enters ONLY through `gexist.fully_good_rank`, on the (GR-62) witness
pair (README §4 convention 2).
"""

import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from cflank import admissible, cubic_habitat                           # noqa: E402
from gcap import pool_specs, branch_stats                              # noqa: E402
from gunif import WITNESSES                                            # noqa: E402
from gexist import fully_good_rank                                     # noqa: E402
from gorient import (cm_colouring, prep_shape, perfect_matchings,        # noqa: E402
                     fully_good_scan)
from gbal import (dart_col, z_admissible, z_to_map, map_to_z, odd_idx,  # noqa: E402
                  balance_oracle, verify_balanced)
from glaw import chunk_inv, hm_spec_map                                 # noqa: E402
from gdev import nk_specs                                              # noqa: E402
from gadm import nko_specs                                             # noqa: E402
from gpsa import (branches_at, nkp_specs, nk55_specs, nko2v_specs)     # noqa: E402

R_SEED = 20260819


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a §1 primitive (checked against the README index
# and the Divergences table).  `chunk_static` / `chunk_inv_z` are the
# (GR-61) translation (the z-side counterpart of `glaw.chunk_inv`, which
# stays the oracle); `adm_zs` enumerates the admissible cube; `indeg_of`
# is the (GR-50) in-degree read-off; `collide` / `pack_bound` are the
# (GR-64) collision statistic; `dist_of` / `fit_M` the (GR-65) identity;
# `d_adm_exact` is an exhaustive-cube `d_adm` (NOT a (GR-58) census
# re-derivation: `d_fg` is never computed here, and the (a') verdict is
# consumed from (GR-58), not re-measured).


def chunk_static(specs, n, binc, ks_spec):
    """Colouring-free data of a chunk given as a set of SPEC branch
    indices: (interiors, cap, z, exc, odd-branch list, improper).  An
    interior is a hub of S-degree 2; it has exactly one free (exit or
    chord) branch.  Every hub of a chunk has S-degree 2 or 3
    (`gcap.two_ec_masks` enforces >= 2; the host is cubic)."""
    S = set(ks_spec)
    deg = {}
    for i in S:
        (u, w, _L) = specs[i]
        deg[u] = deg.get(u, 0) + 1
        deg[w] = deg.get(w, 0) + 1
    assert all(d in (2, 3) for d in deg.values()), \
        "chunk hub of S-degree not in {2, 3}: not a chunk of a cubic host"
    ints = []
    for v, d in deg.items():
        if d != 2:
            continue
        inS = [i for i in binc[v] if i in S]
        free = [i for i in binc[v] if i not in S]
        assert len(inS) == 2 and len(free) == 1, "interior star not 2 + 1"
        ints.append((v, inS[0], inS[1], free[0]))
    exc = sum(specs[i][2] - 2 for i in S)
    odds = [i for i in S if specs[i][2] % 2 == 1]
    z = len(ints)
    return dict(S=tuple(sorted(S)), ints=tuple(ints), cap=2 * z + exc,
                z=z, exc=exc, odds=tuple(odds), nW=len(deg),
                improper=(len(S) == len(specs)))


def chunk_inv_z(specs, cd, z):
    """(GR-61): the four (GR-56) chunk invariants read off the branch
    colouring `z` alone.

        cap(S)     = 2 z(S) + exc(S)                (colouring-free)
        z_mono(S)  = #{interiors whose two S-darts share a dart colour}
        sigma_S    = signed count of those, by that shared colour
        delta_S    = Sum_{odd beta in S} (-1)^{z_beta}

    Returns (cap, z_mono, delta, sigma), the tuple `glaw.chunk_inv`
    returns from the (c, m) side."""
    zmono = sigma = 0
    for (v, b1, b2, _b3) in cd['ints']:
        c1 = dart_col(specs, z, v, b1)
        if c1 == dart_col(specs, z, v, b2):
            zmono += 1
            sigma += 1 if c1 == 0 else -1
    delta = 0
    for i in cd['odds']:
        delta += 1 if z[i] == 0 else -1
    return cd['cap'], zmono, delta, sigma


def good_z(specs, cds, z):
    """(GR-56)(iii) in z-coordinates: every PROPER chunk satisfies
    `z_mono + |delta - sigma| <= cap - 6`."""
    for cd in cds:
        if cd['improper']:
            continue
        cap, zm, dl, sg = chunk_inv_z(specs, cd, z)
        if zm + abs(dl - sg) > cap - 6:
            return False
    return True


def adm_zs(specs, n, binc):
    """The whole admissible cube of a shape, in mask order."""
    E = len(specs)
    out = []
    for msk in range(1 << E):
        z = [(msk >> i) & 1 for i in range(E)]
        if z_admissible(specs, n, binc, z):
            out.append(z)
    return out


def indeg_of(specs, n, binc, oset, z):
    """(GR-50)'s degree datum of an admissible z: per hub, the number of
    EVEN branches whose A-end (dart colour 0) is that hub."""
    return tuple(sum(1 for i in binc[v]
                     if i not in oset and dart_col(specs, z, v, i) == 0)
                 for v in range(n))


def is_balanced_z(specs, oidx, z):
    """Balance in z-coordinates ((GR-49)(ii)): `wt(z|_O) = k`."""
    if not oidx:
        return True
    s = sum(z[i] for i in oidx)
    return 2 * s == len(oidx)


def matb(specs, mat):
    """hub -> its matching branch."""
    out = {}
    for i in mat:
        (u, w, _L) = specs[i]
        out[u] = i
        out[w] = i
    return out


def dist_of(specs, n, m, mat):
    """`dist(m, M)` -- the number of hubs whose minority dart is not the
    matching dart."""
    mb = matb(specs, mat)
    return sum(1 for v in range(n) if m[v][0] != mb[v])


def fit_M(specs, n, binc, z, mat):
    """(GR-65): #{v : the two NON-matching darts at v share a colour} --
    asserted equal to `n - dist(m, M)`."""
    mb = matb(specs, mat)
    tot = 0
    for v in range(n):
        oth = [i for i in binc[v] if i != mb[v]]
        assert len(oth) == 2, "hub star not three distinct branches"
        if dart_col(specs, z, v, oth[0]) == dart_col(specs, z, v, oth[1]):
            tot += 1
    return tot


def collide(cd, mb):
    """(GR-64): the collision hub set of a chunk at a matching --
    interiors whose MATCHING branch is their FREE branch.  These are the
    hubs where `m(v) = M(v)` forces `v` into `z_mono(S)`."""
    return frozenset(v for (v, _b1, _b2, b3) in cd['ints'] if mb[v] == b3)


def coll_terms(specs, cds, mb):
    """Per proper chunk: (term, collision hub set) with
    `term = coll_M(S) - cap(S) + 6`, keeping only positive terms."""
    out = []
    for cd in cds:
        if cd['improper']:
            continue
        cs = collide(cd, mb)
        t = len(cs) - cd['cap'] + 6
        if t > 0:
            out.append((t, cs))
    return out


def pack_bound(terms):
    """The (GR-64) packing bound: the maximum of `Sum term` over families
    of proper chunks with PAIRWISE DISJOINT collision hub sets.  Exact
    (branch and bound over the positive-term chunks, of which habitat
    shapes carry few)."""
    if not terms:
        return 0
    best = 0

    def rec(i, used, acc):
        nonlocal best
        if acc > best:
            best = acc
        if i == len(terms):
            return
        rem = sum(t for (t, _c) in terms[i:])
        if acc + rem <= best:
            return
        (t, cs) = terms[i]
        if not (cs & used):
            rec(i + 1, used | cs, acc + t)
        rec(i + 1, used, acc)

    rec(0, frozenset(), 0)
    return best


def d_adm_exact(specs, n, binc, oidx, edges, allverts, hm, zs, mats):
    """`d_adm` by exhaustive z-cube enumeration: the least
    `dist(m, M)` over all perfect matchings `M` and all BALANCED
    admissible configurations.  No deviation cap anywhere.  `d_fg` is
    deliberately NOT computed (the (a') census is (GR-58)'s, landed and
    exhaustive; this driver consumes it and does not re-derive it)."""
    best = None
    for z in zs:
        if not is_balanced_z(specs, oidx, z):
            continue
        m, c = z_to_map(specs, n, binc, z)
        col = cm_colouring(specs, m, c)
        if not admissible(edges, allverts, hm, col):
            continue
        for mat in mats:
            d = dist_of(specs, n, m, mat)
            if best is None or d < best:
                best = d
    return best


# --------------------------------------------------- shape inventories ------

def pool_shapes():
    """The `Lambda = empty`, `D = 0`, `n_hub <= 6` habitat stratum behind
    the (GR-25) cut criterion -- EXHAUSTIVE, 4920 labelled shapes."""
    out = []
    for n, specs in pool_specs():
        hedges = [(u, w) for (u, w, _L) in specs]
        lens = [L for (_u, _w, L) in specs]
        if not cubic_habitat(n, hedges, lens):
            continue
        out.append((n, [tuple(s) for s in specs]))
    return out


def named_shapes():
    """The named large shapes, reused read-only: GUNIF's W-witnesses, the
    odd-rich necklaces, NKo2v."""
    out = []
    by_tag = {w[0].split()[0]: w for w in WITNESSES}
    for tag in ('W3M', 'W3', 'W4', 'W5'):
        (_nm, n, specs, _f, _S, _e) = by_tag[tag]
        out.append((tag, n, [tuple(s) for s in specs]))
    specs, _p = nko2v_specs()
    out.append(('NKo2v', 10, [tuple(s) for s in specs]))
    for mm in (6, 8):
        sp, _p = nkp_specs(mm)
        out.append((f'NKp({mm})', 5 * mm, [tuple(s) for s in sp]))
        sp, _p = nk55_specs(mm)
        out.append((f'NK55({mm})', 5 * mm, [tuple(s) for s in sp]))
        sp, _p, _F, _ch = nk_specs(mm)
        out.append((f'NK({mm})', 5 * mm, [tuple(s) for s in sp]))
        out.append((f'NKo({mm})', 5 * mm, [tuple(s) for s in nko_specs(mm)[0]]))
    return out


def named_small():
    """The named shapes whose `2^M` chunk scan and `2^E` z-cube are both
    in reach (`E <= 18`): GUNIF's W3M / W3 / W4 and GPSA's NKo2v.  W5
    (`E = 24`) and the necklaces (`E >= 45`) are out of reach for the
    chunk scan -- a DISCLOSED CAP, never a measured 0."""
    keep = ('W3M', 'W3', 'W4', 'NKo2v')
    return [(t, n, s) for (t, n, s) in named_shapes() if t in keep]


def all_shapes():
    """The whole inventory: the exhaustive `n_hub <= 6` habitat stratum,
    then the four named larger shapes."""
    out = [('pool', n, specs) for (n, specs) in pool_shapes()]
    out += [(t, n, s) for (t, n, s) in named_small()]
    return out


def shape_ctx(specs, n, want_chunks=True):
    """One shape's shared context: the landed prep, the spec-side chunk
    statics, the incidence data."""
    edges, allverts, hm, inc, tec, tec_cf, allks = prep_shape(specs)
    binc = branches_at(specs, n)
    s_of = hm_spec_map(specs, hm)
    cds = []
    hmks = []
    if want_chunks:
        for (ks, _kk) in tec:
            cds.append(chunk_static(specs, n, binc, [s_of[k] for k in ks]))
            hmks.append(tuple(ks))
    return dict(specs=specs, n=n, edges=edges, allverts=allverts, hm=hm,
                inc=inc, tec=tec, tec_cf=tec_cf, allks=allks, binc=binc,
                s_of=s_of, cds=cds, hmks=hmks, lens=hm['lens'],
                oidx=odd_idx(specs), oset=set(odd_idx(specs)))


# ------------------------------------------------ [YL-1] --loc: (GR-61) -----

def leg_loc():
    """[YL-1] (GR-61): the (GR-56) chunk invariants in z-coordinates, and
    the degeneracy that confines GBAL's reduction to the whole graph."""
    t0 = time.time()
    print(f"[YL-1] (GR-61) the chunk invariants in z-coordinates")
    shapes = all_shapes()
    print(f"  inventory: {len(shapes)} shapes -- the exhaustive n_hub <= 6 "
          f"habitat stratum plus {len(named_small())} named larger shapes "
          f"({', '.join(t for (t, _n, _s) in named_small())})")

    pairs = 0
    zseen = 0
    crit_ok = 0
    zzero = 0
    zzero_is_whole = 0
    nonconst = 0          # proper chunks with z_mono non-constant at fixed p
    shapes_nonconst = 0
    exc_by_n = {}         # shapes where EVERY proper chunk is p-determined
    chk_by_n = {}         # (total proper chunks, #shapes) per n_hub
    for (_tag, n, specs) in shapes:
        ctx = shape_ctx(specs, n)
        cds, hmks = ctx['cds'], ctx['hmks']
        zs = adm_zs(specs, n, ctx['binc'])
        assert zs, "shape with NO admissible z -- (GR-54) REFUTED, HEADLINE"
        # the z = 0 (interior-free) chunks, and (GR-32)(ii)'s claim that
        # E(G°) is the only one.
        for cd in cds:
            if cd['z'] == 0:
                zzero += 1
                if cd['improper']:
                    zzero_is_whole += 1
        npro = sum(1 for cd in cds if not cd['improper'])
        (tc, sc) = chk_by_n.get(n, (0, 0))
        chk_by_n[n] = (tc + npro, sc + 1)
        per_chunk_seen = {}
        for z in zs:
            zseen += 1
            m, c = z_to_map(specs, n, ctx['binc'], z)
            assert map_to_z(specs, m, c) == z, "(GR-49) round trip broken"
            for j, cd in enumerate(cds):
                mine = chunk_inv_z(specs, cd, z)
                theirs = chunk_inv(ctx['hm'], ctx['inc'], hmks[j], m, c,
                                   ctx['s_of'])
                assert mine == theirs, \
                    f"(GR-61) translation FAILS: {mine} != {theirs}"
                pairs += 1
                if not cd['improper']:
                    key = (j, tuple(z[i] for i in ctx['oidx']))
                    per_chunk_seen.setdefault(key, set()).add(mine[1])
            # (GR-56)(iii) in z == the landed combinatorial evaluator
            col = cm_colouring(specs, m, c)
            gz = good_z(specs, cds, z)
            gl = fully_good_scan(ctx['hm'], None, ctx['tec_cf'], ctx['lens'],
                                 branch_stats(ctx['hm'], col, 'A'))
            assert gz == gl, "(GR-56)(iii) in z disagrees with fully_good_scan"
            crit_ok += 1
        nc = sum(1 for vals in per_chunk_seen.values() if len(vals) > 1)
        nonconst += nc
        if nc:
            shapes_nonconst += 1
        else:
            nev = sum(1 for (_u, _w, L) in specs if L % 2 == 0)
            exc_by_n[(n, nev)] = exc_by_n.get((n, nev), 0) + 1

    print(f"  (admissible z, chunk) pairs asserted vs glaw.chunk_inv: {pairs}")
    print(f"  admissible z round-tripped: {zseen};  "
          f"(GR-56)(iii)-in-z == fully_good_scan at all {crit_ok}")
    print(f"  interior-free (z(S) = 0) chunks: {zzero}, "
          f"of which improper (= E(G°)): {zzero_is_whole}")
    assert zzero == zzero_is_whole == len(shapes), \
        "(GR-32)(ii) violated: an interior-free chunk other than E(G°)"
    print(f"  DEGENERACY: E(G°) is the UNIQUE chunk with z_mono = sigma = 0 "
          f"identically -> the unique chunk whose inequality is a function "
          f"of z|_O alone")
    print(f"  proper (chunk, pattern) cells whose z_mono is NON-constant "
          f"over the fibre: {nonconst} at {shapes_nonconst}/{len(shapes)} "
          f"shapes")
    print(f"  proper chunks per shape, mean by n_hub: "
          f"{ {k: round(v[0] / v[1], 1) for k, v in sorted(chk_by_n.items())} }"
          f"  -- the chunk family carries NO shape-independent cap, unlike "
          f"the <= 6 odd branches (GR-53) exhausts")
    print(f"  shapes where EVERY proper chunk's z_mono IS pattern-determined, "
          f"by (n_hub, #even branches): {dict(sorted(exc_by_n.items()))}")
    assert all(nn <= 4 and nev <= 1 for (nn, nev) in exc_by_n), \
        "the pattern-determined exception reaches a shape with even-branch " \
        "freedom to spare -- recharacterize before relying on the boundary"
    print(f"  EXACT BOUNDARY: the localization's premise (every chunk "
          f"invariant a function of the odd pattern) holds ONLY on a "
          f"{sum(exc_by_n.values())}-shape exceptional family -- the "
          f"one-even-branch theta shapes and the all-length-3 K4, which has "
          f"NO even branch at all -- and FAILS at every one of the other "
          f"{len(shapes) - sum(exc_by_n.values())} shapes")
    print(f"  [YL-1] {round(time.time() - t0, 1)} s")


# ---------------------------------------------- [YL-2] --fibre: (GR-62) -----

def leg_fibre():
    """[YL-2] (GR-62): full goodness is NOT a function of the (GR-50)
    degree data -- the localization's step 2 refuted by witness."""
    t0 = time.time()
    print(f"[YL-2] (GR-62) full goodness vs the (GR-50) degree data")
    inv = all_shapes()
    fibres = 0
    split = 0
    shapes = 0
    shapes_split = 0
    witness = None
    bal_const = 0
    split_by_n = {}
    seen_by_n = {}
    for (_tag, n, specs) in inv:
        ctx = shape_ctx(specs, n)
        oidx, oset, binc = ctx['oidx'], ctx['oset'], ctx['binc']
        cds = ctx['cds']
        cells = {}
        for z in adm_zs(specs, n, binc):
            if not is_balanced_z(specs, oidx, z):
                continue
            key = (tuple(z[i] for i in oidx),
                   indeg_of(specs, n, binc, oset, z))
            cells.setdefault(key, []).append(z)
        shapes += 1
        loc = 0
        for key, zl in cells.items():
            fibres += 1
            vs = {good_z(specs, cds, z) for z in zl}
            # the whole-graph instance is constant on the fibre by (GR-61)
            bal = {is_balanced_z(specs, oidx, z) for z in zl}
            assert bal == {True}, "balance not constant on a fixed-p fibre"
            bal_const += 1
            if len(vs) > 1:
                split += 1
                loc += 1
                if witness is None and len(zl) >= 2:
                    zg = next(z for z in zl if good_z(specs, cds, z))
                    zb = next(z for z in zl if not good_z(specs, cds, z))
                    witness = (n, specs, key, zg, zb, len(zl))
        seen_by_n[n] = seen_by_n.get(n, 0) + 1
        if loc:
            shapes_split += 1
            split_by_n[n] = split_by_n.get(n, 0) + 1
    print(f"  balanced admissible fibres over (pattern, in-degree vector): "
          f"{fibres}")
    print(f"  fibres on which full goodness SPLITS: {split} "
          f"at {shapes_split}/{shapes} shapes")
    print(f"  balance is constant on every one of the {bal_const} fibres "
          f"(the whole-graph instance IS a degree statement)")
    print(f"  shapes with a split fibre, by n_hub: "
          f"{dict(sorted(split_by_n.items()))} of "
          f"{dict(sorted(seen_by_n.items()))}")
    assert split > 0, \
        "(GR-62) FAILS: full goodness constant on every degree fibre -- " \
        "the localization's step 2 would then be OPEN, not refuted"
    (n, specs, key, zg, zb, sz) = witness
    print(f"  smallest witness: n_hub = {n}, specs = {specs}")
    print(f"    pattern {key[0]}, in-degree vector {key[1]}, fibre size {sz}")
    print(f"    z_good = {zg}   (fully good)")
    print(f"    z_bad  = {zb}   (a proper chunk binds)")
    # rank-certify the witness pair through the landed rank oracle
    ctx = shape_ctx(specs, n)
    rng = random.Random(R_SEED + 2)
    cols = []
    for z in (zg, zb):
        m, c = z_to_map(specs, n, ctx['binc'], z)
        col = cm_colouring(specs, m, c)
        assert admissible(ctx['edges'], ctx['allverts'], ctx['hm'], col)
        cols.append(col)
    rg = fully_good_rank(ctx['edges'], ctx['allverts'], ctx['hm'], cols[0], rng)
    rb = fully_good_rank(ctx['edges'], ctx['allverts'], ctx['hm'], cols[1], rng)
    print(f"    rank certificate (gexist.fully_good_rank, seed {R_SEED + 2}): "
          f"good -> {rg}, bad -> {rb}")
    assert rg and not rb, "rank oracle disagrees with the combinatorial split"
    # the violated chunk of the bad member, for the record
    for cd in ctx['cds']:
        if cd['improper']:
            continue
        cap, zm, dl, sg = chunk_inv_z(specs, cd, zb)
        if zm + abs(dl - sg) > cap - 6:
            print(f"    violated chunk: S = {cd['S']}, cap = {cap}, "
                  f"z = {cd['z']}, exc = {cd['exc']}, z_mono = {zm}, "
                  f"|delta - sigma| = {abs(dl - sg)}, budget = {cap - 6}")
    print(f"  CONSEQUENCE: a (GR-51)-shaped criterion cuts its feasible set "
          f"out by in-degree bounds, i.e. as a union of degree classes; the "
          f"fully-good set is not one, so (GR-51) has NO chunk analogue.  "
          f"SCOPE: this excludes a (GR-51)-shaped criterion, not every "
          f"conceivable existence criterion -- existence at a fixed pattern "
          f"is trivially a function of the pattern.")
    print(f"  [YL-2] {round(time.time() - t0, 1)} s")


# ------------------------------------------------ [YL-3] --par: (GR-63) -----

def leg_par():
    """[YL-3] (GR-63): the coordinator's predicted obstruction --
    (GR-52)'s parity contradiction -- tested and refuted as stated."""
    t0 = time.time()
    print(f"[YL-3] (GR-63) is (GR-52)'s parity step the break point?")
    inv = all_shapes()
    subsets = 0
    shapes = 0
    for (_tag, n, specs) in inv:
        oset = set(odd_idx(specs))
        even = [i for i in range(len(specs)) if i not in oset]
        # H = the even-branch graph; the identity is over an ARBITRARY hub set
        for msk in range(1 << n):
            R = {v for v in range(n) if (msk >> v) & 1}
            e_in = 0
            b_out = 0
            for i in even:
                (u, w, _L) = specs[i]
                iu, iw = (u in R), (w in R)
                if iu and iw:
                    e_in += 1
                elif iu or iw:
                    b_out += 1
            d_sum = sum(1 for i in even for v in specs[i][:2] if v in R)
            assert d_sum - b_out == 2 * e_in, \
                "(GR-52)'s counting identity FAILS at a hub subset"
            subsets += 1
        shapes += 1
    print(f"  identity `Sum_{{v in R}} a_v = 2 e_H(R)` asserted at "
          f"{subsets} (shape, hub subset) pairs over {shapes} shapes: "
          f"0 failures")
    print(f"  READING: `2 e_H(R)` is a PER-SUBSET count -- `R` is the Hall "
          f"violator inside the orientation model, not a chunk, and the "
          f"identity holds for every `R` in every shape.  (GR-52) is "
          f"therefore NOT chunk-indexed and NOT the break point.")
    print(f"  The chain breaks two steps EARLIER, at (GR-50) -> (GR-51): "
          f"by (GR-62) there is no degree model at a proper chunk, so "
          f"(GR-52) never gets a Hall condition to repair.")
    print(f"  [YL-3] {round(time.time() - t0, 1)} s")


# ----------------------------------------------- [YL-4] --coll: (GR-64) -----

def leg_coll():
    """[YL-4] (GR-64): the collision bound."""
    t0 = time.time()
    print(f"[YL-4] (GR-64) the collision bound on d_fg")
    inv = all_shapes()
    ineq = tight = 0
    per_chunk_max = 0
    bdist = {}            # min-over-M packing bound, per shape
    mdist = {}            # per-matching packing bound, per (shape, M)
    dadm_hist = {}
    killed = clean = 0
    kill_shapes = 0
    missed = 0            # M with no fully-good optimum the bound does NOT kill
    viol = []
    for (tag, n, specs) in inv:
        ctx = shape_ctx(specs, n)
        binc, oidx = ctx['binc'], ctx['oidx']
        cds = ctx['cds']
        mats = perfect_matchings(specs)
        assert mats, "habitat shape with no perfect matching"
        zs = adm_zs(specs, n, binc)
        # the admissible-balanced maps, with their full-goodness verdict
        maps = []
        for z in zs:
            if not is_balanced_z(specs, oidx, z):
                continue
            m, c = z_to_map(specs, n, binc, z)
            col = cm_colouring(specs, m, c)
            if not admissible(ctx['edges'], ctx['allverts'], ctx['hm'], col):
                continue
            maps.append((z, m, good_z(specs, cds, z)))
        # (a) the inequality, over EVERY (admissible z, matching, chunk)
        for z in zs:
            m, _c = z_to_map(specs, n, binc, z)
            for mat in mats:
                mb = matb(specs, mat)
                d = dist_of(specs, n, m, mat)
                for cd in cds:
                    if cd['improper']:
                        continue
                    cs = collide(cd, mb)
                    _cap, zm, _dl, _sg = chunk_inv_z(specs, cd, z)
                    assert zm >= len(cs) - d, \
                        "(GR-64) inequality FAILS -- HEADLINE"
                    if zm == len(cs) - d:
                        tight += 1
                    ineq += 1
        # (b) d_adm, exhaustive, no cap
        dadm = min((dist_of(specs, n, m, mat) for (_z, m, _g) in maps
                    for mat in mats), default=None)
        assert dadm is not None, \
            "d_adm = infinity -- E1 clause (v) FIRES, HEADLINE"
        dadm_hist[dadm] = dadm_hist.get(dadm, 0) + 1
        # (c) the per-matching bound, its prune, and the prune's soundness
        best = None
        for mat in mats:
            mb = matb(specs, mat)
            # (iv)/(v): the ceiling profile and the parity, per proper chunk
            for cd in cds:
                if cd['improper']:
                    continue
                assert cd['z'] >= 2, \
                    "(GR-64)(iv) proof step FAILS: proper chunk with z < 2"
                c0 = len(collide(cd, mb))
                assert (c0 - cd['nW']) % 2 == 0, \
                    "(GR-64)(v) parity FAILS"
                if c0 - cd['cap'] + 6 == 2:
                    assert (cd['z'], cd['exc']) in ((3, 1), (4, 0)) \
                        and c0 == cd['z'], \
                        "(GR-64)(iv) ceiling profile FAILS"
            terms = coll_terms(specs, cds, mb)
            for (t, _cs) in terms:
                per_chunk_max = max(per_chunk_max, t)
            pb = pack_bound(terms)
            mdist[pb] = mdist.get(pb, 0) + 1
            best = pb if best is None else min(best, pb)
            # ground truth: does M host a fully-good map at distance <= d_adm?
            hosts = any(g and dist_of(specs, n, m, mat) <= dadm
                        for (_z, m, g) in maps)
            if pb > dadm:
                assert not hosts, \
                    "(GR-64) prune UNSOUND: a killed matching hosts a " \
                    "fully-good optimum -- HEADLINE"
                killed += 1
            else:
                clean += 1
                if not hosts:
                    missed += 1
        if any(pack_bound(coll_terms(specs, cds, matb(specs, mat))) > dadm
               for mat in mats):
            kill_shapes += 1
        bdist[best] = bdist.get(best, 0) + 1
        if best > dadm:
            viol.append((tag, n, specs, best, dadm))
    print(f"  (a) `z_mono(S) >= coll_M(S) - dist(m, M)` asserted at "
          f"{ineq} (shape, admissible z, matching, proper chunk) "
          f"instances: 0 failures, {tight} at equality")
    print(f"  (b) per-chunk term max over the whole pool: {per_chunk_max} "
          f"(proven ceiling: 2)")
    assert per_chunk_max <= 2, "the proven <= 2 ceiling is violated"
    print(f"      per-matching packing bound, over all (shape, M): "
          f"{dict(sorted(mdist.items()))}")
    print(f"      min-over-M packing bound, per shape: "
          f"{dict(sorted(bdist.items()))}")
    print(f"  (c) d_adm distribution (exhaustive z-cube, NO cap): "
          f"{dict(sorted(dadm_hist.items()))}")
    print(f"      anchor matchings the bound KILLS (pack_bound(M) > d_adm): "
          f"{killed} of {killed + clean}, at {kill_shapes} shapes; "
          f"every kill verified SOUND against the exhaustive ground truth")
    print(f"      matchings with no fully-good optimum that the bound does "
          f"NOT kill (its incompleteness): {missed}")
    print(f"  E1(iv)/E2 detector: shapes with min_M pack_bound > d_adm "
          f"(would prove d_adm < d_fg): {len(viol)}")
    assert not viol, \
        f"(a') REFUTED by the collision bound at {viol[:2]} -- HEADLINE, " \
        f"E2 refutation branch"
    print(f"  CAP DISCLOSED: chunk enumeration is `gcap.two_ec_subsets`' "
          f"2^M scan, so this leg is the inventory only (n_hub <= 6 plus "
          f"W3M/W3/W4/NKo2v, E <= 18); W5 (E = 24) and the necklaces "
          f"(E >= 45) are out of reach, and the large-`n` extension is a "
          f"named residual, NOT a measured 0.")
    print(f"  [YL-4] {round(time.time() - t0, 1)} s")


# ------------------------------------------------ [YL-5] --fit: (GR-65) -----

def leg_fit():
    """[YL-5] (GR-65): `dist(m, M)` and `z_mono(S)` are one statistic."""
    t0 = time.time()
    print(f"[YL-5] (GR-65) the fit identity")
    inv = all_shapes()
    inst = 0
    for (_tag, n, specs) in inv:
        ctx = shape_ctx(specs, n, want_chunks=False)
        binc = ctx['binc']
        mats = perfect_matchings(specs)
        for z in adm_zs(specs, n, binc):
            m, _c = z_to_map(specs, n, binc, z)
            for mat in mats:
                assert fit_M(specs, n, binc, z, mat) == \
                    n - dist_of(specs, n, m, mat), \
                    "(GR-65) fit identity FAILS"
                inst += 1
    print(f"  `dist(m, M) = n - #{{v : the two non-M darts at v agree}}` "
          f"asserted at {inst} (shape, admissible z, matching) instances: "
          f"0 failures")
    print(f"  So `dist(m, M)` and `z_mono(S)` are the SAME statistic "
          f"(`fit`): the minority dart sitting on a prescribed branch, "
          f"counted over a prescribed hub set.  (Y) asks for one map "
          f"MAXIMIZING fit at some matching selection while every proper "
          f"chunk's exit selection is CAPPED.")
    print(f"  [YL-5] {round(time.time() - t0, 1)} s")


# ----------------------------------------------- [YL-6] --cert: (GR-66) -----

def leg_cert():
    """[YL-6] (GR-66): GBAL's own certificate measured against (Y)."""
    t0 = time.time()
    print(f"[YL-6] (GR-66) GBAL's certificate vs (Y)'s two constraints")
    inv = all_shapes()
    over = 0
    at_opt = 0
    fg = 0
    tot = 0
    gap_hist = {}
    named_rows = []
    for (tag, n, specs) in inv:
        ctx = shape_ctx(specs, n)
        binc, oidx = ctx['binc'], ctx['oidx']
        mats = perfect_matchings(specs)
        zs = adm_zs(specs, n, binc)
        dadm = d_adm_exact(specs, n, binc, oidx, ctx['edges'], ctx['allverts'],
                           ctx['hm'], zs, mats)
        z, p = balance_oracle(specs, n, oidx)
        assert z is not None, "(GR-54) produced no certificate -- HEADLINE"
        verify_balanced(specs, n, binc, oidx, z,
                        ground=(ctx['edges'], ctx['allverts'], ctx['hm']))
        m, _c = z_to_map(specs, n, binc, z)
        dcert = min(dist_of(specs, n, m, mat) for mat in mats)
        gap_hist[dcert - dadm] = gap_hist.get(dcert - dadm, 0) + 1
        tot += 1
        if dcert > dadm:
            over += 1
        else:
            at_opt += 1
        cert_fg = good_z(specs, ctx['cds'], z)
        if cert_fg:
            fg += 1
        if tag != 'pool':
            named_rows.append((tag, dadm, dcert, cert_fg))
    print(f"  shapes: {tot}")
    for (tag, da, dc, cg) in named_rows:
        print(f"    {tag}: d_adm = {da}, certificate distance = {dc}, "
              f"certificate fully good = {cg}")
    print(f"  GBAL certificate distance minus d_adm, distribution: "
          f"{dict(sorted(gap_hist.items()))}")
    print(f"  certificate ABOVE the admissibility optimum: {over}/{tot}; "
          f"at the optimum: {at_opt}/{tot}")
    print(f"  certificate FULLY GOOD: {fg}/{tot}")
    print(f"  READING: (GR-54)'s construction carries no distance datum and "
          f"no chunk datum -- both of (Y)'s constraints are invisible to it.")
    print(f"  [YL-6] {round(time.time() - t0, 1)} s")


# ------------------------------------------------------- [YL-7] --adv ------

def leg_adv():
    """[YL-7] F13 falsification controls."""
    t0 = time.time()
    print(f"[YL-7] F13 controls  (seed {R_SEED + 7})")
    rng = random.Random(R_SEED + 7)
    pool = pool_shapes()
    samp = [(n, s) for (_t, n, s) in named_small()] + rng.sample(pool, 300)

    # (1) MUST-FIRE: the z-side translation with delta's sign convention
    #     flipped must DISAGREE with glaw.chunk_inv somewhere.
    fired = 0
    for (n, specs) in samp[:60]:
        ctx = shape_ctx(specs, n)
        for z in adm_zs(specs, n, ctx['binc'])[:8]:
            m, c = z_to_map(specs, n, ctx['binc'], z)
            for j, cd in enumerate(ctx['cds']):
                cap, zm, dl, sg = chunk_inv_z(specs, cd, z)
                bad = (cap, zm, -dl, sg)
                if bad != chunk_inv(ctx['hm'], ctx['inc'], ctx['hmks'][j],
                                    m, c, ctx['s_of']):
                    fired += 1
    print(f"  (1) sign-flipped delta MUST disagree: {fired} disagreements "
          f"(a passing translation would be untested)")
    assert fired > 0, "control (1) did not fire -- the delta test is vacuous"

    # (2) MUST-FIRE: dropping the |delta - sigma| term from the chunk
    #     criterion must MISCLASSIFY (the (GR-56) F13 control, re-run in
    #     z-coordinates on this pass's own evaluator).
    mis = 0
    tot = 0
    for (n, specs) in samp:
        ctx = shape_ctx(specs, n)
        for z in adm_zs(specs, n, ctx['binc']):
            m, c = z_to_map(specs, n, ctx['binc'], z)
            col = cm_colouring(specs, m, c)
            if not admissible(ctx['edges'], ctx['allverts'], ctx['hm'], col):
                continue
            truth = good_z(specs, ctx['cds'], z)
            naive = True
            for cd in ctx['cds']:
                if cd['improper']:
                    continue
                cap, zm, _dl, _sg = chunk_inv_z(specs, cd, z)
                if zm > cap - 6:
                    naive = False
                    break
            tot += 1
            if naive != truth:
                mis += 1
    print(f"  (2) |delta - sigma| dropped: {mis} misclassifications of "
          f"{tot} admissible colourings (must be > 0)")
    assert mis > 0, "control (2) did not fire"

    # (3) NEGATIVE CONTROL: the per-matching collision bound must be
    #     VACUOUS (= 0) at some (shape, M) and POSITIVE at others --
    #     otherwise it is either empty or trivially always-on.
    pos = zero = 0
    for (n, specs) in samp:
        ctx = shape_ctx(specs, n)
        for mat in perfect_matchings(specs):
            b = pack_bound(coll_terms(specs, ctx['cds'], matb(specs, mat)))
            if b > 0:
                pos += 1
            else:
                zero += 1
    print(f"  (3) per-matching collision bound over {len(samp)} shapes: "
          f"positive at {pos} (shape, M) pairs, vacuous at {zero} "
          f"(both must be > 0)")
    assert pos > 0 and zero > 0, "control (3): the bound is degenerate"

    # (4) MUST-FIRE: dropping the PACKING disjointness (a plain sum over
    #     the positive-term chunks) must OVERSHOOT the sound bound
    #     somewhere -- and must produce a value that is NOT a valid lower
    #     bound on the per-matching fully-good distance, i.e. the
    #     disjointness hypothesis is load-bearing, not decoration.
    over = unsound = 0
    for (n, specs) in samp:
        ctx = shape_ctx(specs, n)
        binc, oidx, cds = ctx['binc'], ctx['oidx'], ctx['cds']
        mats = perfect_matchings(specs)
        maps = []
        for z in adm_zs(specs, n, binc):
            if not is_balanced_z(specs, oidx, z):
                continue
            m, c = z_to_map(specs, n, binc, z)
            col = cm_colouring(specs, m, c)
            if not admissible(ctx['edges'], ctx['allverts'], ctx['hm'], col):
                continue
            if good_z(specs, cds, z):
                maps.append(m)
        for mat in mats:
            terms = coll_terms(specs, cds, matb(specs, mat))
            naive = sum(t for (t, _c) in terms)
            if naive > pack_bound(terms):
                over += 1
                dmin = min((dist_of(specs, n, m, mat) for m in maps),
                           default=None)
                if dmin is not None and naive > dmin:
                    unsound += 1
    print(f"  (4) disjointness dropped: the naive sum exceeds the packing "
          f"bound at {over} (shape, M) pairs, and is UNSOUND (exceeds a "
          f"realized fully-good distance) at {unsound} of them "
          f"(both must be > 0)")
    assert over > 0 and unsound > 0, "control (4) did not fire"

    # (5) MUST-FIRE: a DEGREE-ONLY predicate on the (GR-62) fibres cannot
    #     reproduce full goodness -- exhibited as a nonzero irreducible
    #     error rate for the best degree-only classifier.
    best_err = None
    for (n, specs) in samp[:120]:
        ctx = shape_ctx(specs, n)
        binc, oidx, oset = ctx['binc'], ctx['oidx'], ctx['oset']
        cells = {}
        for z in adm_zs(specs, n, binc):
            if not is_balanced_z(specs, oidx, z):
                continue
            key = (tuple(z[i] for i in oidx),
                   indeg_of(specs, n, binc, oset, z))
            cells.setdefault(key, []).append(good_z(specs, ctx['cds'], z))
        err = tot2 = 0
        for _k, vs in cells.items():
            err += min(sum(vs), len(vs) - sum(vs))
            tot2 += len(vs)
        if tot2 and (best_err is None or err > 0):
            best_err = (err, tot2, n)
            if err > 0:
                break
    print(f"  (5) best degree-only classifier's irreducible error: "
          f"{best_err[0]} of {best_err[1]} at n_hub = {best_err[2]} "
          f"(must be > 0)")
    assert best_err[0] > 0, "control (5) did not fire"
    print(f"  [YL-7] {round(time.time() - t0, 1)} s")


# --------------------------------------------------------------- main -------

def main():
    args = sys.argv[1:]
    legs = {'--loc': leg_loc, '--fibre': leg_fibre, '--par': leg_par,
            '--coll': leg_coll, '--fit': leg_fit, '--cert': leg_cert,
            '--adv': leg_adv}
    if not args or args[0] == '--validate':
        order = ['--loc', '--fibre', '--par', '--coll', '--fit', '--cert',
                 '--adv']
    else:
        order = args
    print(f"YLOC -- (GR-61)-(GR-66), Steps G80-G85   (R_SEED = {R_SEED})")
    for a in order:
        assert a in legs, f"unknown mode {a}"
        legs[a]()
        print()


if __name__ == '__main__':
    main()
