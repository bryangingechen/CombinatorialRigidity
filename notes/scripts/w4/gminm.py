"""GMINM -- the thirty-seventh kernel-(K) ordinal: does GHWIT's
refutation REACH THE LEDGER?  (spec: notes/Pencil-fanout.md S"GMINM").

TARGET.  GHWIT landed *"per-matching (b') at the constant 2 is FALSE"*
-- (GR-104)(i) at 2k = 2 refuted at the habitat-gated n = 20 pair
`refut20`, gap 4.  Two questions this pass settles:

  (Q1) does the min_M reading survive -- is
       min_M (d_adm(M) - d_par(M)) <= 2 at the refuting shapes?
  (Q2) which reading do (b')'s downstream consumers actually need?

(GR-125) THE INSTRUMENT (new here, proven; --check): the GENERAL
word model.  (GR-106)'s
reversal-set normal form is stated at O <= M pairs, where the 2-factor
F = E - M is all-even.  The SAME 2^n model works at EVERY perfect
matching once the per-branch parity twist tau_i = [ell_i even] is
carried explicitly:

  * a word w assigns to each F-branch the colour of its dart at the
    traversal TAIL; the dart at the HEAD is that xor tau;
  * hub v (head of p, tail of q) is a REVERSAL hub iff its two F-darts
    agree, and then admissibility FORCES the M-dart at v to the other
    colour; otherwise v is THROUGH and the M-dart is free;
  * dist(z, M) = #through = n - |R(w)| at every admissible z
    ((GR-106)(iv)'s proof, which never used all-evenness for this
    clause);
  * an M-branch with both ends resident imposes one GF(2) consistency
    condition, which is (GR-106)(ii)'s exclusion when tau = 1 and
    (GR-106)(iii)'s end-forcing when tau = 0;
  * an ODD branch lying in F carries its colour directly on its own
    word bit.

Hence f(p), d_par(M) = min_p f(p) and d_adm(M) = min over BALANCED p
of f(p) are computable in 2^n at ANY (shape, matching) pair -- where
the 2^{3n/2} cube (gridbal_common.adm_cube) stops at n = 12.  The
model is CROSS-ASSERTED f-value-by-f-value against that landed cube at
every (shape, matching) pair of the small pools (--check), O <= M and
O !<= M alike, and it re-derives refut20's landed (4, 8, 4) triple.

OUTCOME.

  (GR-126) THE ESCAPE THEOREM (proven; --pm, --min).  At 2k = 2, every
  perfect matching M with O !<= M has d_adm(M) - d_par(M) <= 2 -- this
  is the landed (GR-107)(iii) off-M half, whose (GR-C1) hypothesis is
  VACUOUS at 2k = 2 (|delta| in {0, 2} always).  And no branch of a
  bridgeless cubic multigraph lies in EVERY perfect matching (Edmonds'
  perfect-matching polytope: x = 1/3 is in it, so no coordinate is 1
  on every vertex of the combination), while every habitat hub graph is
  bridgeless.  Therefore

      min_M (d_adm(M) - d_par(M)) <= 2  at EVERY 2k = 2 habitat,

  and the hunted refutation -- a shape pricing >= 4 at every matching
  -- is IMPOSSIBLE at 2k = 2.  GHWIT's kill is confined to the
  per-matching reading.

  (GR-127) THE LEDGER READING IS NEITHER OF THEM (--gdev, --min).  The
  growth law's balance term is d_adm(shape) - d_par(shape) with BOTH
  ends minima over matchings (gdev.min_dev, notes/scripts/w4/gdev.py:
  `for nd ...: for mat in mats:`), i.e. a DIFFERENCE OF MINIMA, not a
  minimum of differences.  The landed W3 figures already separate the
  two: the shape-level balance gap at W3 is 1, and (GR-67) proves every
  PER-MATCHING gap even -- so W3's ledger gap is attained at two
  DIFFERENT matchings and is not any per-matching gap at all.

  (GR-128) THE MEASURED VERDICT (--min, --hunt).  At refut20,
  clause20, the three n = 12 (GR-108) witnesses and every landed pool
  shape: min_M gap and the shape-level gap, per shape, with the
  O <= M matching's own gap alongside.

Modes:
  --check    the general word model against the landed 2^{3n/2} cube.
  --gdev     the W3 separation: the shape-level gap is not a
             per-matching gap.
  --pm       no odd branch lies in every perfect matching (the
             (GR-126) combinatorial half), at every pool shape.
  --min      the min_M and shape-level sweep.
  --hunt     more n = 20 all-(2,2) / gap-4 diagrams from the
             transposition neighbourhood, gated and measured.
  --validate all five.

Sibling imports (S2 rule-2 trips, DISCLOSED -- extending the recorded
GBLAW/GXESC *Harness debt* item's consumer lists; the move is the
coordinator's, not this dispatch's): `specs_of_diagram` from
`w4/gxesc.py` (THIRD consumer).  Balance-layer devices come DIRECTLY
from gridbal_common.  The five pinned witness diagrams are RE-ENTERED
locally (independent reconstruction, ghwit's own discipline), so no
import of `w4/ghwit.py` is taken.

Rank-free throughout: gexist.fully_good_rank is never imported or
called and no d_fg claim is made anywhere.  Exact integers / GF(2); no
floating point; every rng seeded, seed printed.
"""
import argparse
import collections
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from gridbal_common import (adm_cube, branches_at, f_layers,         # noqa: E402
                            imb_of, named_cases, odd_idx,
                            seeded_shapes, stratum_cases, v8_specs,
                            z_admissible, z_pattern, z_to_map)
from gorient import perfect_matchings                                # noqa: E402
from gxesc import specs_of_diagram                                   # noqa: E402
from cflank import cubic_habitat                                     # noqa: E402

R_SEED = 20260826


# ----------------------------------------------------- local devices --------
#
# All new; none shadows a S1 primitive or a w4 name (checked against the
# README index and the Divergences table).  `bit_masks` the word-bit
# bitsets; `f_2factor` the 2-factor of ANY perfect matching as ordered
# cycles; `size_planes`/`maxsize` the bit-sliced |R| decomposition;
# `pair_model` the GENERAL word model of one (shape, matching) pair;
# `pair_layers` its (f-table, d_par, d_adm); `cube_layers` the landed
# 2^{3n/2} oracle in the same shape; `shape_scan` the per-shape sweep
# over all matchings; `witness_diagrams` the five pinned diagrams,
# re-entered; `pool_shapes` the landed pools; `transpositions` the
# n = 20 neighbourhood.


def bit_masks(n):
    """S[e][x] = the set of words in [0, 2^n) whose bit e is x, as a
    2^n-bit integer.  Built by doubling a periodic block (setting bits
    one at a time on a 2^n-bit int is quadratic)."""
    W = 1 << n
    ALL = (1 << W) - 1
    S = []
    for e in range(n):
        half = 1 << e
        blk = ((1 << half) - 1) << half
        length = half << 1
        while length < W:
            blk |= blk << length
            length <<= 1
        S.append((ALL ^ blk, blk))
    return S, ALL


def f_2factor(specs, n, mat):
    """F = E \\ mat as a list of cycles, each an ordered list of
    (branch index, tail hub, head hub).  Asserts F is a 2-factor."""
    finc = {v: [] for v in range(n)}
    for i, (u, w, _L) in enumerate(specs):
        if i in mat:
            continue
        assert u != w, 'loop in hub multigraph'
        finc[u].append(i)
        finc[w].append(i)
    for v in range(n):
        assert len(finc[v]) == 2, 'E minus M is not a 2-factor'
    used = set()
    cycles = []
    for v0 in range(n):
        for i0 in finc[v0]:
            if i0 in used:
                continue
            cyc = []
            v, i = v0, i0
            while i not in used:
                used.add(i)
                (a, b, _L) = specs[i]
                nxt = b if a == v else a
                cyc.append((i, v, nxt))
                v = nxt
                i = finc[v][0] if finc[v][1] == i else finc[v][1]
            cycles.append(cyc)
    assert sum(len(c) for c in cycles) == n, 'F edge count != n'
    return cycles


def size_planes(RES, n, ALL):
    """SZ[s] = the words at which exactly s hubs are reversal hubs, by a
    bit-sliced ripple-carry sum of the per-hub RES bitsets."""
    planes = []
    for v in range(n):
        x = RES[v]
        k = 0
        while x:
            if k == len(planes):
                planes.append(0)
            c = planes[k] & x
            planes[k] ^= x
            x = c
            k += 1
    SZ = []
    for s in range(n + 1):
        if s >> len(planes):
            SZ.append(0)
            continue
        b = ALL
        for k in range(len(planes)):
            b &= planes[k] if (s >> k) & 1 else (ALL ^ planes[k])
        SZ.append(b)
    return SZ


def maxsize(bs, SZ, n):
    """The largest |R| attained on a nonempty word bitset; -1 if empty."""
    if not bs:
        return -1
    for s in range(n, -1, -1):
        if bs & SZ[s]:
            return s
    return -1


def pair_model(specs, n, mat, oidx, S, ALL):
    """THE GENERAL WORD MODEL of one (shape, matching) pair -- see the
    module docstring.  Returns (VALID, Aset, Bset, SZ, RES, CA, CB)."""
    cycles = f_2factor(specs, n, mat)
    pe, ne, pos, tau = {}, {}, {}, {}
    k = 0
    for cyc in cycles:
        for (i, a, b) in cyc:
            pos[i] = k
            k += 1
            tau[i] = 1 if specs[i][2] % 2 == 0 else 0
            ne[a] = i
            pe[b] = i
    assert k == n and len(pe) == n and len(ne) == n, 'word layer malformed'
    CA = [0] * n
    CB = [0] * n
    for v in range(n):
        p, q = pe[v], ne[v]
        CA[v] = S[pos[q]][0] & S[pos[p]][tau[p]]
        CB[v] = S[pos[q]][1] & S[pos[p]][tau[p] ^ 1]
    RES = [CA[v] | CB[v] for v in range(n)]
    valid = ALL
    for i in mat:
        (u, w, L) = specs[i]
        if L % 2 == 0:
            bad = (CA[u] & CA[w]) | (CB[u] & CB[w])
        else:
            bad = (CA[u] & CB[w]) | (CB[u] & CA[w])
        valid &= ALL ^ bad
    Aset, Bset = [], []
    for i in oidx:
        (u, w, _L) = specs[i]
        if i in mat:
            Aset.append(ALL ^ (CA[u] | CA[w]))
            Bset.append(ALL ^ (CB[u] | CB[w]))
        else:
            Aset.append(S[pos[i]][0])
            Bset.append(S[pos[i]][1])
    return (valid, Aset, Bset, size_planes(RES, n, ALL), RES, CA, CB,
            (pos, tau, pe, ne))


def pair_layers(n, k2, valid, Aset, Bset, SZ):
    """(f-table, d_par(M), d_adm(M)) off the general word model, plus an
    OPTIMAL WORD for each pattern.  f[p] is None where the pattern admits
    no admissible configuration."""
    f, wit = {}, {}
    for p in range(1 << k2):
        s = valid
        for j in range(k2):
            s &= Bset[j] if (p >> j) & 1 else Aset[j]
            if not s:
                break
        if not s:
            f[p] = wit[p] = None
            continue
        m = maxsize(s, SZ, n)
        f[p] = n - m
        top = s & SZ[m]
        wit[p] = (top & -top).bit_length() - 1
    live = [v for v in f.values() if v is not None]
    dpar = min(live) if live else None
    assert dpar == (None if not valid else n - maxsize(valid, SZ, n)), \
        'a valid word admits no pattern -- the model is wrong'
    bal = [p for p in f if imb_of(k2, p) == 0 and f[p] is not None]
    dadm = min(f[p] for p in bal) if bal else None
    return f, dpar, dadm, wit


def certify(specs, n, mat, oidx, aux, CA, CB, w, p, dist):
    """AN INDEPENDENT CERTIFICATE, through the LANDED (GR-49) devices:
    decode the word `w` into an explicit branch colouring z, and assert
    with `gridbal_common.z_admissible` / `z_pattern` / `z_to_map` that z
    IS admissible, HAS pattern p, and sits at distance `dist` from M.
    This certifies the ACHIEVABILITY half of every f-value the general
    word model reports -- at every n, including n = 20 where the
    2^{3n/2} cube oracle is out of reach."""
    (pos, tau, pe, ne) = aux
    z = [0] * len(specs)
    need = {}
    for v in range(n):
        if (CA[v] >> w) & 1:
            need[v] = 1
        elif (CB[v] >> w) & 1:
            need[v] = 0
    free_odd = {i: (p >> j) & 1 for j, i in enumerate(oidx) if i in mat}
    for i in range(len(specs)):
        (u, ww, _L) = specs[i]
        if i in mat:
            if u in need:
                z[i] = need[u]
            elif ww in need:
                z[i] = need[ww] ^ (1 if specs[i][2] % 2 == 0 else 0)
            else:
                z[i] = free_odd.get(i, 0)
        else:
            b = (w >> pos[i]) & 1
            z[i] = b if ne[u] == i else b ^ tau[i]
    binc = branches_at(specs, n)
    assert z_admissible(specs, n, binc, z), 'certificate: z NOT admissible'
    assert z_pattern(z, oidx) == p, 'certificate: pattern moved'
    mm, _c = z_to_map(specs, n, binc, z)
    base = {}
    for i in mat:
        (u, ww, _L) = specs[i]
        base[u] = (i, 0)
        base[ww] = (i, 1)
    d = sum(1 for v in range(n) if mm[v] != base[v])
    assert d == dist, f'certificate: dist {d} != model {dist}'
    return z


def cube_layers(specs, n, mat, oidx):
    """The LANDED 2^{3n/2} oracle in the same shape: (f-table, d_par,
    d_adm) from gridbal_common.adm_cube + f_layers."""
    binc = branches_at(specs, n)
    base = {}
    for i in mat:
        (u, w, _L) = specs[i]
        base[u] = (i, 0)
        base[w] = (i, 1)
    cube = adm_cube(specs, n, binc, oidx)
    f, dpar = f_layers(cube, n, base)
    k2 = len(oidx)
    bal = [f[p] for p in f if imb_of(k2, p) == 0]
    return f, dpar, (min(bal) if bal else None)


def shape_scan(specs, n, S, ALL, cap=500):
    """Every perfect matching of one shape through the general word
    model.  Returns (rows, ncap) with rows = (mat, sub, dpar, dadm, gap)
    and sub = True iff O <= M."""
    oidx = odd_idx(specs)
    k2 = len(oidx)
    mats = perfect_matchings(specs, cap=cap)
    rows = []
    for mat in mats:
        valid, Aset, Bset, SZ, _R, CA, CB, aux = pair_model(
            specs, n, mat, oidx, S, ALL)
        _f, dpar, dadm, wit = pair_layers(n, k2, valid, Aset, Bset, SZ)
        for p in range(1 << k2):
            if _f[p] is not None:
                certify(specs, n, mat, oidx, aux, CA, CB,
                        wit[p], p, _f[p])
        gap = None if (dpar is None or dadm is None) else dadm - dpar
        rows.append((mat, set(oidx) <= set(mat), dpar, dadm, gap))
    return rows, len(mats)


def witness_diagrams():
    """The five pinned GHWIT witnesses, RE-ENTERED here from the landed
    write-up (Steps G142/G143) for independent reconstruction: positional
    single-F-cycle diagrams on 0..n-1, (tag, n, even chords, odd chords,
    pinned per-matching (d_par, d_adm, gap) of the O <= M matching)."""
    return [
        ('n12a', 12, [(0, 2), (1, 4), (6, 8), (7, 10)],
         [(3, 11), (5, 9)], (4, 6, 2)),
        ('n12b', 12, [(0, 2), (1, 10), (4, 7), (6, 8)],
         [(3, 11), (5, 9)], (4, 6, 2)),
        ('n12c', 12, [(0, 3), (2, 4), (6, 9), (8, 10)],
         [(1, 5), (7, 11)], (4, 6, 2)),
        ('refut20', 20,
         [(15, 6), (13, 1), (17, 11), (18, 16), (7, 2), (5, 3), (9, 4),
          (0, 8)], [(10, 14), (12, 19)], (4, 8, 4)),
        ('clause20', 20,
         [(12, 16), (15, 5), (9, 7), (10, 19), (11, 1), (8, 3), (0, 13),
          (14, 18)], [(17, 4), (2, 6)], (4, 6, 2)),
    ]


def pool_shapes(args):
    """The landed pools, tagged: the n <= 6 habitat stratum (EXHAUSTIVE),
    V8, the named large shapes, and seeded n = 8/10/12 cells.  No pool is
    new; every one is a gridbal_common supplier."""
    out = []
    for (tag, n, sp) in stratum_cases():
        out.append(('stratum', tag, n, sp))
    out.append(('V8', 'V8', 8, v8_specs()))
    for (tag, n, sp) in named_cases():
        if n <= args.namedcap and odd_idx(sp):
            out.append(('named', tag, n, sp))
    for n in (8, 10, 12):
        rng = random.Random(R_SEED + n)
        for j, sp in enumerate(seeded_shapes(n, args.tries, rng)):
            out.append((f'seed{n}', f'seed{n}#{j + 1}', n, sp))
    return out


def transpositions(n, chords):
    """Every 2-chord endpoint transposition of a positional diagram, with
    F-parallel chords excluded (a chord joining two cycle-neighbours is
    not a chord)."""
    m = len(chords)
    for i in range(m - 1):
        for j in range(i + 1, m):
            (a, b), (c, d) = chords[i], chords[j]
            for (p1, p2) in (((a, c), (b, d)), ((a, d), (b, c))):
                if (p1[0] - p1[1]) % n in (1, n - 1):
                    continue
                if (p2[0] - p2[1]) % n in (1, n - 1):
                    continue
                cc = list(chords)
                cc[i], cc[j] = p1, p2
                yield cc


def bridgeless(specs, n):
    """Is the hub multigraph 2-edge-connected?  (The (GR-25) cut criterion
    already FORBIDS a bridge -- both sides of one would need excess >= 5
    against a total of 6 -- so this is the machine check of a two-line
    consequence, and it is what (GR-126)'s Edmonds argument consumes.)"""
    for k in range(len(specs)):
        seen, st = {0}, [0]
        while st:
            v = st.pop()
            for j, (u, w, _L) in enumerate(specs):
                if j == k:
                    continue
                if u == v and w not in seen:
                    seen.add(w)
                    st.append(w)
                elif w == v and u not in seen:
                    seen.add(u)
                    st.append(u)
        if len(seen) != n:
            return False
    return True


def diagram_pair(n, ech, gch):
    """The (specs, mat, oidx) of a positional single-F-cycle diagram
    through the LANDED specs_of_diagram habitat recipe, or None."""
    got = specs_of_diagram(n, ech, gch)
    if got is None:
        return None
    specs, mat = got
    hedges = [(u, w) for (u, w, _L) in specs]
    lens = [L for (_u, _w, L) in specs]
    assert cubic_habitat(n, hedges, lens), 'specs_of_diagram returned a non-habitat'
    oidx = odd_idx(specs)
    assert len(oidx) == 2 and set(oidx) <= set(mat), 'not an O <= M, 2k = 2 pair'
    return specs, mat, oidx


# ---------------------------------------------------- [GMN-1] --check -------

def leg_check(args):
    """The general word model against the LANDED 2^{3n/2} cube, f-value
    by f-value, at EVERY (shape, matching) pair of the small pools --
    O <= M and O !<= M alike -- plus refut20's landed triple."""
    t0 = time.time()
    print('  [GMN-1] --check: the GENERAL word model vs the landed '
          'gridbal_common.adm_cube + f_layers oracle')
    legs = [('stratum (EXHAUSTIVE, n <= 6)',
             [(t, n, sp) for (t, n, sp) in stratum_cases()]),
            ('V8 (n = 8)', [('V8', 8, v8_specs())])]
    rng = random.Random(R_SEED)
    legs.append((f'seeded n = 10 (seed {R_SEED}, {args.tries} tries)',
                 [(f'seed10#{j + 1}', 10, sp) for j, sp in
                  enumerate(seeded_shapes(10, args.tries, rng))]))
    rng12 = random.Random(R_SEED + 12)
    legs.append((f'seeded n = 12 (seed {R_SEED + 12}, {args.cube12} shapes)',
                 [(f'seed12#{j + 1}', 12, sp) for j, sp in
                  enumerate(seeded_shapes(12, args.tries, rng12))
                  ][:args.cube12]))
    ncert = 0
    for (name, shapes) in legs:
        npair = nsub = nk = 0
        k2s = collections.Counter()
        for (tag, n, sp) in shapes:
            oidx = odd_idx(sp)
            if not oidx or len(oidx) > 6:
                continue
            nk += 1
            k2s[len(oidx)] += 1
            S, ALL = bit_masks(n)
            for mat in perfect_matchings(sp, cap=args.matcap):
                cf, cdpar, cdadm = cube_layers(sp, n, mat, oidx)
                valid, Aset, Bset, SZ, _R, CA, CB, aux = pair_model(
                    sp, n, mat, oidx, S, ALL)
                wf, wdpar, wdadm, wwit = pair_layers(n, len(oidx),
                                                     valid, Aset, Bset, SZ)
                for p in range(1 << len(oidx)):
                    if wf[p] is not None:
                        certify(sp, n, mat, oidx, aux, CA, CB,
                                wwit[p], p, wf[p])
                        ncert += 1
                for p in range(1 << len(oidx)):
                    assert (p in cf) == (wf[p] is not None), \
                        f'{tag}: pattern {p} feasibility disagrees'
                    if p in cf:
                        assert cf[p] == wf[p], \
                            f'{tag}: f({p}) {cf[p]} != {wf[p]}'
                assert (cdpar, cdadm) == (wdpar, wdadm), \
                    f'{tag}: (d_par, d_adm) disagree'
                npair += 1
                nsub += 1 if set(oidx) <= set(mat) else 0
        print(f'    {name}: {nk} odd-carrying shapes, {npair} (shape, '
              f'matching) pairs cross-asserted f-value-by-f-value '
              f'({nsub} with O <= M, {npair - nsub} with O !<= M); '
              f'2k histogram {dict(sorted(k2s.items()))}; running '
              f'landed-predicate certificates: {ncert}  '
              f'[{time.time() - t0:.0f}s]')
    print(f'    => {ncert} f-values additionally CERTIFIED by decoding the '
          f'optimal word into an explicit z and asserting the landed '
          f'(GR-49) z_admissible / z_pattern / z_to_map on it')
    print('    (ii) the landed refut20 / clause20 / n = 12 triples, '
          're-derived by the general model at the O <= M matching:')
    for (tag, n, ech, gch, pinned) in witness_diagrams():
        got = diagram_pair(n, ech, gch)
        assert got is not None, f'{tag}: the landed habitat recipe rejects it'
        specs, mat, oidx = got
        S, ALL = bit_masks(n)
        valid, Aset, Bset, SZ, _R, CA, CB, aux = pair_model(
            specs, n, mat, oidx, S, ALL)
        f, dpar, dadm, wit = pair_layers(n, 2, valid, Aset, Bset, SZ)
        for p in range(4):
            certify(specs, n, mat, oidx, aux, CA, CB,
                    wit[p], p, f[p])
        assert (dpar, dadm, dadm - dpar) == pinned, \
            f'{tag}: the landed (d_par, d_adm, gap) triple moved'
        print(f'      {tag}: n = {n}, O <= M matching -- f-table '
              f'{dict(sorted(f.items()))}, d_par = {dpar}, d_adm = {dadm}, '
              f'GAP = {dadm - dpar}  (pinned {pinned})')
    print(f'  leg check OK  [{time.time() - t0:.0f}s]')


# ----------------------------------------------------- [GMN-2] --gdev -------

def leg_gdev(args):
    """(GR-127): the ledger's (b') term is a DIFFERENCE OF MINIMA.  At
    W3 the shape-level balance gap is 1 -- and (GR-67) proves every
    PER-MATCHING gap even, so the ledger's own number is not any
    per-matching gap."""
    t0 = time.time()
    print('  [GMN-2] --gdev: the shape-level (gdev.min_dev) reading vs '
          'the per-matching one, at the landed named shapes')
    for (tag, n, sp) in named_cases():
        if n > args.namedcap or not odd_idx(sp):
            continue
        S, ALL = bit_masks(n)
        rows, nm = shape_scan(sp, n, S, ALL, cap=args.matcap)
        dpars = [r[2] for r in rows if r[2] is not None]
        dadms = [r[3] for r in rows if r[3] is not None]
        gaps = [r[4] for r in rows if r[4] is not None]
        shape_gap = min(dadms) - min(dpars)
        assert all(g % 2 == 0 for g in gaps), \
            f'{tag}: (GR-67) parity law contradicted'
        print(f'    {tag} (n = {n}, 2k = {len(odd_idx(sp))}): {nm} perfect '
              f'matchings; d_par(shape) = {min(dpars)}, d_adm(shape) = '
              f'{min(dadms)} -> SHAPE-LEVEL gap {shape_gap}; per-matching '
              f'gap histogram {dict(sorted(collections.Counter(gaps).items()))}'
              f', min_M gap = {min(gaps)}'
              + ('   <== SHAPE GAP IS ODD: not any per-matching gap'
                 if shape_gap % 2 else ''))
    print(f'  leg gdev OK  [{time.time() - t0:.0f}s]')


# ------------------------------------------------------- [GMN-3] --pm -------

def leg_pm(args):
    """(GR-126)'s combinatorial half: no branch of a habitat hub graph
    lies in EVERY perfect matching -- in particular some M has
    O !<= M.  Asserted branch-by-branch at every pool shape."""
    t0 = time.time()
    print('  [GMN-3] --pm: every habitat hub graph is BRIDGELESS, and no '
          'branch lies in every perfect matching (the (GR-126) halves)')
    tot = collections.Counter()
    worst = None
    wits = []
    for (tag, n, ech, gch, _p) in witness_diagrams():
        got = diagram_pair(n, ech, gch)
        assert got is not None, f'{tag}: the landed habitat recipe rejects it'
        wits.append(('witness', tag, n, got[0]))
    for (leg, tag, n, sp) in wits + pool_shapes(args):
        assert bridgeless(sp, n), f'{tag}: habitat hub graph has a BRIDGE'
        mats = perfect_matchings(sp, cap=args.matcap)
        assert len(mats) < args.matcap, f'{tag}: matching cap {args.matcap} BINDS'
        for i in range(len(sp)):
            assert any(i not in m for m in mats), \
                f'{tag}: branch {i} lies in EVERY perfect matching'
        oidx = odd_idx(sp)
        esc = [m for m in mats if not set(oidx) <= set(m)]
        assert esc, f'{tag}: every perfect matching contains O'
        frac = (len(mats) - len(esc), len(mats))
        if worst is None or frac[0] / frac[1] > worst[0] / worst[1]:
            worst = frac + (tag,)
        tot[leg] += 1
        tot[f'{leg}_mats'] += len(mats)
        tot[f'{leg}_esc'] += len(esc)
    for leg in [k for k in tot if not k.endswith(('_mats', '_esc'))]:
        print(f'    {leg}: {tot[leg]} shapes, {tot[f"{leg}_mats"]} perfect '
              f'matchings, {tot[f"{leg}_esc"]} of them with O !<= M -- '
              f'BRIDGELESS asserted, every branch avoidable, every shape '
              f'has an escape matching')
    print(f'    highest O <= M fraction seen: {worst[0]}/{worst[1]} at '
          f'{worst[2]}  [{time.time() - t0:.0f}s]')
    print(f'  leg pm OK  [{time.time() - t0:.0f}s]')


# ------------------------------------------------------ [GMN-4] --min -------

def report_shape(tag, n, specs, S, ALL, args, pinned=None, verbose=True):
    """One shape's whole matching census: per-matching (d_par, d_adm, gap),
    min_M gap, and the SHAPE-LEVEL gap d_adm(shape) - d_par(shape)."""
    oidx = odd_idx(specs)
    rows, nm = shape_scan(specs, n, S, ALL, cap=args.matcap)
    assert nm < args.matcap, f'{tag}: matching cap {args.matcap} BINDS'
    dpars = [r[2] for r in rows if r[2] is not None]
    dadms = [r[3] for r in rows if r[3] is not None]
    gaps = [r[4] for r in rows if r[4] is not None]
    sub = [r for r in rows if r[1]]
    shape_gap = min(dadms) - min(dpars)
    if pinned is not None:
        assert any((r[2], r[3], r[4]) == pinned for r in sub), \
            f'{tag}: no O <= M matching carries the pinned triple {pinned}'
    offg = [r[4] for r in rows if not r[1] and r[4] is not None]
    subg = [r[4] for r in rows if r[1] and r[4] is not None]
    # (GR-107)(iii)'s off-M half, ASSERTED at every O !<= M matching of
    # every shape this driver touches -- 2k = 2 only, where its (GR-C1)
    # hypothesis |delta| <= 2 is vacuous
    if len(oidx) == 2:
        assert all(g <= 2 for g in offg), \
            f'{tag}: an O !<= M matching prices > 2 -- (GR-107)(iii) FAILS'
    if verbose:
        print(f'    {tag} (n = {n}, 2k = {len(oidx)}): {nm} perfect '
              f'matchings, {len(sub)} with O <= M (their (d_par, d_adm, gap) '
              f'triples {sorted({(r[2], r[3], r[4]) for r in sub})})')
        print(f'      per-matching gap histogram '
              f'{dict(sorted(collections.Counter(gaps).items()))}'
              f' (O <= M {dict(sorted(collections.Counter(subg).items()))}, '
              f'O !<= M {dict(sorted(collections.Counter(offg).items()))}); '
              f'MIN_M GAP = {min(gaps)}; d_par(shape) = {min(dpars)}, '
              f'd_adm(shape) = {min(dadms)}, SHAPE-LEVEL GAP = {shape_gap}')
    return min(gaps), shape_gap, max(gaps), nm, len(sub), subg, offg


def leg_min(args):
    """(GR-128): min_M (d_adm - d_par) and the shape-level gap, at the
    five pinned witnesses and across every landed pool shape."""
    t0 = time.time()
    print('  [GMN-4] --min: the min_M reading and the SHAPE-LEVEL reading')
    print('    (i) the five pinned GHWIT witnesses (habitat-gated, '
          'single F-cycle, O <= M at the witness matching):')
    for (tag, n, ech, gch, pinned) in witness_diagrams():
        got = diagram_pair(n, ech, gch)
        assert got is not None, f'{tag}: the landed habitat recipe rejects it'
        specs, _mat, _oidx = got
        S, ALL = bit_masks(n)
        mn, sg, mx, _nm, _ns, _sg, _og = report_shape(
            tag, n, specs, S, ALL, args, pinned=pinned)
        assert mn <= 2, f'{tag}: min_M gap > 2 -- (GR-126) REFUTED'
        assert sg <= 2, f'{tag}: shape-level gap > 2 -- the LEDGER form fails'
        print(f'      => per-matching MAX gap {mx} (GHWIT\'s reading), '
              f'min_M gap {mn}, ledger (shape-level) gap {sg}')
    print('    (ii) the landed pools -- every shape, every matching:')
    agg = collections.defaultdict(collections.Counter)
    hard = []
    for (leg, tag, n, sp) in pool_shapes(args):
        S, ALL = bit_masks(n)
        mn, sg, mx, nm, ns, subg, offg = report_shape(
            tag, n, sp, S, ALL, args, verbose=False)
        assert mn <= 2, f'{tag}: min_M gap > 2 -- (GR-126) REFUTED'
        agg[leg][f'min_{mn}'] += 1
        agg[leg][f'shape_{sg}'] += 1
        agg[leg][f'max_{mx}'] += 1
        agg[leg]['shapes'] += 1
        agg[leg]['mats'] += nm
        agg[leg]['sub'] += ns
        agg[leg]['k2_2'] += 1 if len(odd_idx(sp)) == 2 else 0
        agg[leg]['cover'] += len(offg) if len(odd_idx(sp)) == 2 else 0
        for g in subg:
            agg[leg][f'subgap_{g}'] += 1
        for g in offg:
            agg[leg][f'offgap_{g}'] += 1
        if sg >= 2:
            agg[leg]['hard'] += 1
            hard.append((leg, tag, n, sg))
    for leg in sorted(agg):
        c = agg[leg]
        mns = {int(k[4:]): v for k, v in c.items() if k.startswith('min_')}
        shs = {int(k[6:]): v for k, v in c.items() if k.startswith('shape_')}
        mxs = {int(k[4:]): v for k, v in c.items() if k.startswith('max_')}
        sgh = {int(k[7:]): v for k, v in c.items() if k.startswith('subgap_')}
        ogh = {int(k[7:]): v for k, v in c.items() if k.startswith('offgap_')}
        print(f'    {leg}: {c["shapes"]} shapes ({c["k2_2"]} at 2k = 2), '
              f'{c["mats"]} matchings ({c["sub"]} with O <= M) -- min_M gap '
              f'{dict(sorted(mns.items()))}, SHAPE-LEVEL gap '
              f'{dict(sorted(shs.items()))}, per-matching MAX gap '
              f'{dict(sorted(mxs.items()))}')
        print(f'      per-matching gap by containment: O <= M '
              f'{dict(sorted(sgh.items()))}, O !<= M {dict(sorted(ogh.items()))}')
    print(f'    => (GR-107)(iii)\'s off-M half ASSERTED (gap <= 2) at '
          f'{sum(agg[l]["cover"] for l in agg)} O !<= M pairs of 2k = 2 pool '
          f'shapes; 0 violations')
    print(f'    the {len(hard)} pool shapes whose SHAPE-LEVEL gap is 2 '
          f'(the ledger term\'s measured maximum): '
          f'{sorted(hard)[:args.hardcap]}'
          + (f'  [CAP: first {args.hardcap} listed]'
             if len(hard) > args.hardcap else ''))
    print(f'  leg min OK  [{time.time() - t0:.0f}s]')


# ----------------------------------------------------- [GMN-5] --hunt -------

def diagram_scan(n, chords, oj, S, ALL, CA, CB, SZ, RES):
    """The O <= M reading of one positional single-F-cycle diagram, in
    the shared word layer of the n-cycle (the F-cycle -- hence CA/CB/SZ
    -- is the same for every chord diagram, so only the chord
    constraints are rebuilt).  Returns (dpar, gap, n22, nfam)."""
    ev = ALL
    for j, (a, b) in enumerate(chords):
        if j in oj:
            continue
        ev &= ALL ^ ((CA[a] & CA[b]) | (CB[a] & CB[b]))
    (a1, b1) = chords[oj[0]]
    (a2, b2) = chords[oj[1]]
    aa = ev & (ALL ^ (CA[a1] | CA[b1])) & (ALL ^ (CA[a2] | CA[b2]))
    ab = ev & (ALL ^ (CA[a1] | CA[b1])) & (ALL ^ (CB[a2] | CB[b2]))
    m_aa = maxsize(aa, SZ, n)
    m_ab = maxsize(ab, SZ, n)
    mstar = m_aa if m_aa > m_ab else m_ab
    gap = m_aa - m_ab if m_aa > m_ab else 0
    if gap <= 0:
        return n - mstar, 0, 0, 0
    fam = aa & SZ[mstar]
    full = RES[a1] & RES[b1] & RES[a2] & RES[b2]
    return n - mstar, gap, bin(fam & full).count('1'), bin(fam).count('1')


def leg_hunt(args):
    """More n = 20 all-(2,2) / gap-4 pairs, from the 2-chord
    transposition neighbourhood of the two pinned n = 20 witnesses (a
    NEW population and a NEW sentence: the min_M and SHAPE-LEVEL
    readings at a POPULATION of refuting pairs, not at refut20 alone).
    GHWIT's --build climb is NOT re-run; this leg is cheaper and
    targets a different statement."""
    t0 = time.time()
    print('  [GMN-5] --hunt: the transposition neighbourhood of the two '
          'pinned n = 20 witnesses, gated, then measured at EVERY matching')
    n = 20
    S, ALL = bit_masks(n)
    # the shared word layer of the positional n-cycle: build it once, via
    # the general model at the diagram's own O <= M matching
    seed = witness_diagrams()[3]
    specs0, mat0, oidx0 = diagram_pair(n, seed[2], seed[3])
    _v, _A, _B, SZ, RES, CA, CB, _aux = pair_model(
        specs0, n, mat0, oidx0, S, ALL)
    found = []
    for (tag, nn, ech, gch, _p) in witness_diagrams():
        if nn != n:
            continue
        chords = list(ech) + list(gch)
        oj = (len(chords) - 2, len(chords) - 1)
        base = diagram_scan(n, chords, oj, S, ALL, CA, CB, SZ, RES)
        nvar = ngap = n22 = ngate = 0
        for cc in transpositions(n, chords):
            nvar += 1
            r = diagram_scan(n, cc, oj, S, ALL, CA, CB, SZ, RES)
            if r[1] == 0:
                continue
            ngap += 1
            if r[2] != r[3]:
                continue
            n22 += 1
            got = diagram_pair(n, cc[:len(ech)], cc[len(ech):])
            if got is None:
                continue
            ngate += 1
            found.append((f'{tag}+t{ngate}', got[0], r[1]))
        print(f'    {tag}: base (d_par {base[0]}, gap {base[1]}, (2,2) '
              f'{base[2]}/{base[3]}); {nvar} transpositions, {ngap} with '
              f'gap > 0, {n22} all-(2,2), {ngate} of those habitat-GATED')
    print(f'    (ii) the {len(found)} newly gated all-(2,2) pairs, each '
          f'measured at EVERY perfect matching of its shape:')
    hist = collections.Counter()
    for (tag, specs, dgap) in found[:args.huntcap]:
        mn, sg, mx, nm, ns, _sg2, _og2 = report_shape(
            tag, n, specs, S, ALL, args)
        assert mn <= 2, f'{tag}: min_M gap > 2 -- (GR-126) REFUTED'
        hist[(dgap, mx, mn, sg)] += 1
    print(f'    (iii) (diagram gap, per-matching MAX, min_M, shape-level) '
          f'over the measured pairs: {dict(sorted(hist.items()))}'
          + (f'  [CAP: only the first {args.huntcap} of {len(found)} '
             f'measured]' if len(found) > args.huntcap else ''))
    print(f'  leg hunt OK  [{time.time() - t0:.0f}s]')


# ------------------------------------------------------------ main ----------

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    ap.add_argument('--gdev', action='store_true')
    ap.add_argument('--pm', action='store_true')
    ap.add_argument('--min', action='store_true')
    ap.add_argument('--hunt', action='store_true')
    ap.add_argument('--validate', action='store_true')
    ap.add_argument('--tries', type=int, default=200)
    ap.add_argument('--cube12', type=int, default=3)
    ap.add_argument('--matcap', type=int, default=2000)
    ap.add_argument('--namedcap', type=int, default=12)
    ap.add_argument('--huntcap', type=int, default=40)
    ap.add_argument('--hardcap', type=int, default=20)
    args = ap.parse_args()
    if args.validate:
        args.check = args.gdev = args.pm = args.min = args.hunt = True
    if not (args.check or args.gdev or args.pm or args.min or args.hunt):
        ap.error('pick a mode')
    t0 = time.time()
    print('GMINM -- does GHWIT\'s refutation reach the ledger?')
    if args.check:
        leg_check(args)
    if args.gdev:
        leg_gdev(args)
    if args.pm:
        leg_pm(args)
    if args.min:
        leg_min(args)
    if args.hunt:
        leg_hunt(args)
    print(f'ALL LEGS OK  [{time.time() - t0:.0f}s]')


if __name__ == '__main__':
    main()
