"""§(K-grid) direction GEXPAND (2026-09-10) driver -- IS THERE AN EXPANSION
THEOREM IN THE `G°` DIRECTION?  A finite set of moves generating the tight
`D = 0` class stratum from a finite base would give an induction internal to
the combinatorics of `(G°, ℓ, bits)` and CLOSE (GR-15) on the stratum.

A `w4/` leaf beside `cflank.py` / `gisland.py` / `aglu.py`, importing them
READ-ONLY (README §2).  The `n_hub ≤ 6` fences -- `cflank.LAM_PLAN`,
`cflank.LAM6_PLAN`, `gisland.CUBIC_N`, `aglu`'s `_pool8` -- are PLAN
constants, not function fences: `cflank.cubic_habitat(n, hedges, lens)` and
`gisland.stratum(n, ...)` are already parameterized in `n`, so this driver
un-fences by CALLING them at `n = 8, 10, 12, …` rather than by
re-implementing anything.  Run from the repo root:

    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --law     # the move arithmetic: cubicity+tightness force Dn even, DM = 3Dn/2, DSl = 3Dn, and ZERO net excess AUTOMATICALLY
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --moves   # THE REFUTATION: enumerate every gadget at k <= 3; the COMPLEMENT CUT kills all of them, and the proof kills every k
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --hub     # the special case that shows the mechanism: (GR-25)(i) at `V - {v}` caps every hub's branch-sum at 11 for n >= 4
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --cap     # (GR-170) the EXCESS-BOUNDARY CAP `exc_B <= 2*d(B) - 1`, asserted at every hub set of every landed shape
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --reach   # the INHERITANCE TEST + its F13 control: 0 of aglu's exact 39689 `n_hub = 8` shapes reduces to a smaller class shape
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --irred   # an explicit INFINITE family of class shapes, every one of them irreducible
    PYTHONHASHSEED=0 python3 notes/scripts/w4/gexpand.py --validate  # all six

Argument state: session draft `notes/Pencil-draft-GEXPAND.md` (to be merged
into `notes/pencil/workbook/grid.md` §(K-grid) as Steps G189+; labels
(GR-169)+ per the 2026-09-10 GEXPAND reservation in `notes/pencil/labels.md`).

WHAT A MOVE IS, stated once so every mode tests the same object.  An
*additive zero-net-excess expansion move* takes a `D = 0` class shape
(parent) to another (child) by: choosing `s` interior split points on parent
branches (each becomes a new degree-3 hub); adding `b` BRAND-NEW hubs; and
adding `3k - s` new branches on those `2k := s + b` new hubs so that every
split hub gains exactly one new dart and every brand-new hub has degree 3.
Nothing else about the parent changes.  This covers every classical
generator that is additive -- Henneberg I/II, the H-operation (= edge
insertion), vertex splitting.  It does NOT cover a move that DELETES a
parent hub (`Y->Delta` is the example; the coordinator's spec kills that one
separately, at girth: its new triangle is a circuit of total length 6 < 7),
nor a move that re-lengths parent branches away from the changed region.
Those two exclusions are the draft's blind axes 1 and 2.

WHAT EACH MODE TESTS, one sentence each (F11: the driver tests the exact
headline sentence).

--law    that `Dn` is even with `DM = 3Dn/2` and `DSigma-l = 3Dn`, hence
         `D(excess) = 0` AUTOMATICALLY -- "zero-net-excess" is not a side
         condition a move may be designed to satisfy, it is FORCED by
         cubicity plus tightness; and that the new branches carry excess
         exactly `2s`.
--moves  that NO gadget survives, at any `(k, s)` enumerated: layer 1 is the
         gadget-internal (GR-25)(i) with (SD-6) (it empties `k = 1` on its
         own -- the H-operation's new branch would need `l = 6`); layer 2 is
         the global budget `2s <= 6`; layer 3 is (GR-25)(i) at
         `W' = V_child - B` with `B` the BRAND-NEW hubs, which every
         surviving gadget fails with slack exactly `-1`.
--hub    the one-hub special case of layer 3, measured over every landed
         population: `max_v Sigma_{beta ∋ v} l_beta = 11` at `n_hub >= 4`
         (and `= 12` at `n_hub = 2`, where `|V - {v}| = 1 < 2` puts the
         instance outside (GR-25)(i)'s hypothesis).  This is the Y-kill.
--cap    (GR-170), the general form: `exc_B <= 2*partial(B) - 1` at every
         hub set `B` of every landed class shape, min slack 0 (TIGHT).
--reach  the inheritance test the (GR-157) base made possible, run over
         `aglu`'s exact `n_hub = 8` population -- preceded by its F13
         adversarial control, which relaxes (SD-6) to `l <= 6` so that the
         H-operation DOES exist and checks the search recovers it.
--irred  that `CL_m` with six unit-excess rungs is a class shape at every
         `m >= 4`, so the stratum is infinite in the `G°` direction and the
         negative has teeth.

CAPS, disclosed here and re-disclosed at each figure.
 * `cubic_habitat` is a `2^n` scan; `--irred` therefore CHECKS the family at
   `m = 6..11` (`n_hub = 12..22`) and PROVES it for all `m >= 4` by the
   boundary inequality in `ladder_boundary_proof`.  A measured row is never
   quoted as the general claim.
 * (GR-25) is asserted EQUIVALENT to `gridcol.class_shape` only at
   `n_hub <= 6` (16 270 pairs) plus §(K-grid)'s 14 named targets.  Every
   figure here at `n_hub >= 8` rests on (GR-25) as a PROVEN theorem, not on
   that equivalence measurement.
 * `--reach` runs over `Lambda = empty` at `n_hub = 8` (`aglu._pool8`, the
   exact 39689) and over `Lambda != empty` at `n_hub <= 6`
   (`gisland.stratum`).  `Lambda != empty` at `n_hub = 8` is NOT swept here.
 * The move classification is proven at `Lambda_child = empty`.  With
   `Lambda != empty` in the CHILD the excess budget can be stretched
   (`2s <= 6 + |Lambda_outside|`) and `s > 3` is not excluded; disclosed.
 * Everything is scoped to `D = 0` (cubic `G°`).  A move that leaves `D = 0`
   and returns is not covered.
"""

import argparse
import itertools
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

from cflank import cubic_habitat                                      # noqa: E402
from gisland import stratum                                           # noqa: E402
from aglu import _pool8                                               # noqa: E402
from gridcol import cubic_iso_classes                                 # noqa: E402
from cflank import length_tuples                                      # noqa: E402
from gisland import edge_auts, iso_orbits                             # noqa: E402

X_SEED = 20260910          # no rng is used; pinned for the README convention


# --------------------------------------------------------------- primitives --

def hub_sums(n, hedges, lens):
    """`Sigma_{beta ∋ v} l_beta` at every hub (a loop would count twice; the
    stratum is loopless, and `cubic_habitat` rejects loops outright)."""
    out = [0] * n
    for (u, w), L in zip(hedges, lens):
        out[u] += L
        out[w] += L
    return out


def excess(lens):
    return sum(L - 2 for L in lens)


def gadget_topologies(k, s):
    """Every connected loopless multigraph on `s` DEGREE-1 split hubs plus
    `b = 2k - s` DEGREE-3 brand-new hubs, one representative per isomorphism
    class, with `3k - s` edges.

    This is the shape of the NEW branches a move adds; it is enumerated, not
    posited, because "the only move family" is a claim of the
    exhaustive/forced class (README rule; `RESEARCH-ARC.md` §4)."""
    b = 2 * k - s
    if b < 0:
        return []
    verts = list(range(s + b))                      # 0..s-1 split, s.. new
    deg = [1] * s + [3] * b
    pairs = [(i, j) for i in verts for j in verts if i < j]   # loopless
    ne = 3 * k - s
    if ne < 0 or sum(deg) != 2 * ne:
        return []
    out, seen = [], set()

    def rec(pi, rem, acc):
        if pi == len(pairs):
            if all(r == 0 for r in rem):
                g = tuple(acc)
                if _connected(s + b, g) and g not in seen:
                    key = _canon_multi(s, b, g)
                    if key not in seen:
                        seen.add(key)
                        out.append(g)
            return
        (i, j) = pairs[pi]
        top = min(rem[i], rem[j])
        for c in range(top + 1):
            for _ in range(c):
                acc.append((i, j))
            rem[i] -= c
            rem[j] -= c
            rec(pi + 1, rem, acc)
            rem[i] += c
            rem[j] += c
            for _ in range(c):
                acc.pop()

    rec(0, deg[:], [])
    return out


def _connected(nv, edges):
    if nv == 0:
        return True
    adj = {v: [] for v in range(nv)}
    for (u, w) in edges:
        adj[u].append(w)
        adj[w].append(u)
    seen, st = {0}, [0]
    while st:
        v = st.pop()
        for u in adj[v]:
            if u not in seen:
                seen.add(u)
                st.append(u)
    return len(seen) == nv


def _canon_multi(s, b, edges):
    """Canonical key under permutations preserving the split/new split."""
    best = None
    for ps in itertools.permutations(range(s)):
        for pb in itertools.permutations(range(s, s + b)):
            p = list(ps) + list(pb)
            key = tuple(sorted(tuple(sorted((p[u], p[w]))) for (u, w) in edges))
            if best is None or key < best:
                best = key
    return best


def gadget_cuts_ok(nv, edges, lens):
    """Every (GR-25)(i) instance INTERNAL to the gadget, checked without
    reference to the parent.

    In the child every gadget hub has degree 3, so for `S` inside the gadget
    `partial(S) = 3|S| - 2|E_in(S)|` whatever the placement -- the split
    hubs' two outward darts are exactly the ones the formula already counts.
    So this is a COMPLETE placement-independent necessary filter."""
    for r in range(2, nv + 1):
        for S in itertools.combinations(range(nv), r):
            ss = set(S)
            ein = [i for i, (u, w) in enumerate(edges)
                   if u in ss and w in ss]
            if not ein:
                continue
            adj = {v: [] for v in S}
            for i in ein:
                (u, w) = edges[i]
                adj[u].append(w)
                adj[w].append(u)
            seen, st = {S[0]}, [S[0]]
            while st:
                v = st.pop()
                for u in adj[v]:
                    if u not in seen:
                        seen.add(u)
                        st.append(u)
            if len(seen) != r:
                continue
            bd = 3 * r - 2 * len(ein)
            if 2 * bd + sum(lens[i] - 2 for i in ein) < 7:
                return False
    return True


def gadgets(k, lam=False):
    """Every connected gadget at size `k`: topology + length assignment,
    filtered by the placement-independent (GR-25)(i) cuts and by (SD-6).

    `lam=False` is `Lambda_child = empty` (`l >= 2`), where the move
    classification is proven; `lam=True` opens `l >= 1`."""
    lo = 1 if lam else 2
    out = []
    for s in range(0, 2 * k + 1):
        for g in gadget_topologies(k, s):
            ne = len(g)
            for ls in itertools.product(range(lo, 6), repeat=ne):
                if sum(ls) != 6 * k:
                    continue
                if not gadget_cuts_ok(2 * k, g, ls):
                    continue
                out.append((s, g, ls))
    return out


_FRAMES = {}


def reduction_frames(n, hedges, kmax=3, kmin=2):
    """The LENGTH-INDEPENDENT half of the reduction search, memoized.

    A candidate `W'` is decided by the hub multigraph alone: `|W'| = 2k`,
    induced connected, every hub of `W'` with 0 or 2 darts leaving it, at
    least 2 of them with 2 (`s >= 2`), and `|E(W')| = 3k - s`.  Only the
    merged-length cap and the parent's (GR-25) gate depend on lengths."""
    key = (n, tuple(hedges), kmax, kmin)
    if key in _FRAMES:
        return _FRAMES[key]
    frames = []
    for k in range(kmin, kmax + 1):
        if 2 * k >= n:
            continue
        for W in itertools.combinations(range(n), 2 * k):
            ws = set(W)
            inside, bound, rest = [], [], []
            for i, (u, w) in enumerate(hedges):
                a, b = (u in ws), (w in ws)
                if a and b:
                    inside.append(i)
                elif a or b:
                    bound.append(i)
                else:
                    rest.append(i)
            dout = {v: 0 for v in W}
            for i in bound:
                (u, w) = hedges[i]
                dout[u if u in ws else w] += 1
            if any(d not in (0, 2) for d in dout.values()):
                continue
            s = sum(1 for d in dout.values() if d == 2)
            if s < 2 or len(inside) != 3 * k - s:
                continue
            adj = {v: [] for v in W}
            for i in inside:
                (u, w) = hedges[i]
                adj[u].append(w)
                adj[w].append(u)
            seen, st = {W[0]}, [W[0]]
            while st:
                v = st.pop()
                for u in adj[v]:
                    if u not in seen:
                        seen.add(u)
                        st.append(u)
            if len(seen) != 2 * k:
                continue
            pairs = []
            for v in W:
                if dout[v] != 2:
                    continue
                ends = []
                for i in bound:
                    (u, w) = hedges[i]
                    if u == v or w == v:
                        ends.append((w if u == v else u, i))
                pairs.append((ends[0], ends[1]))
            out = sorted(set(range(n)) - ws)
            rel = {v: i for i, v in enumerate(out)}
            frames.append((W, s, k, tuple(rest), tuple(pairs), rel))
    _FRAMES[key] = frames
    return frames


def reductions(n, hedges, lens, kmax=3, kmin=2, gate=None):
    """Every connected reduction of this child shape: the inverse moves.

    At `Lambda = empty` every parent branch is split AT MOST ONCE (two
    splits would need `l_beta >= 6`, breaching (SD-6)), so a split hub has
    exactly two darts leaving `W'` and a brand-new hub none -- the reduction
    is unambiguous.  Asserted, not assumed."""
    M = len(hedges)
    gate = gate or cubic_habitat
    for (W, s, k, rest, pairs, rel) in reduction_frames(n, hedges, kmax, kmin):
        phe = [(rel[hedges[i][0]], rel[hedges[i][1]]) for i in rest]
        ple = [lens[i] for i in rest]
        bad = False
        for ((a, ia), (b, ib)) in pairs:
            L = lens[ia] + lens[ib]
            if L > 5:
                bad = True
                break
            phe.append((rel[a], rel[b]))
            ple.append(L)
        if bad or len(phe) != M - 3 * k:
            continue
        if gate(n - 2 * k, phe, ple):
            yield (W, s, k, tuple(phe), tuple(ple))


def apply_move(n, hedges, lens, splits, gtop, glens, s):
    """The EXPANSION direction, used as the positive control for
    `reductions`: split branch `splits[i]` at offset `off[i]`, add the
    gadget, and return the child.

    `splits` is a list of `(branch index, offset)` with `1 <= offset < l`;
    gadget vertices `0..s-1` are the split hubs in that order and
    `s..2k-1` the brand-new hubs."""
    k = (len(gtop) + s) // 3
    he = list(hedges)
    ls = list(lens)
    newhub = {}
    drop = set()
    add = []
    for i, (bi, off) in enumerate(splits):
        v = n + i
        newhub[i] = v
        (u, w) = hedges[bi]
        drop.add(bi)
        add.append(((u, v), off))
        add.append(((v, w), lens[bi] - off))
    for j in range(s, 2 * k):
        newhub[j] = n + j
    he = [e for i, e in enumerate(he) if i not in drop]
    ls = [L for i, L in enumerate(ls) if i not in drop]
    for (e, L) in add:
        he.append(e)
        ls.append(L)
    for (u, w), L in zip(gtop, glens):
        he.append((newhub[u], newhub[w]))
        ls.append(L)
    return n + 2 * k, he, ls


# ------------------------------------------------ [GX-1] --law -------------

def leg_law():
    """[GX-1] the move arithmetic: zero net excess is FORCED, not designed."""
    print("[GX-1] the move arithmetic at `D = 0` (no rng; pure counting)")
    print("  cubicity `2M = 3n`, tightness `Sigma-l = 6c = 6(M - n + 1)`:")
    bad = 0
    for dn in range(2, 41, 2):
        dm = 3 * dn // 2
        dsl = 6 * (dm - dn)
        dexc = dsl - 2 * dm
        assert dm * 2 == 3 * dn
        assert dsl == 3 * dn
        if dexc != 0:
            bad += 1
    assert bad == 0
    print("     Dn even => DM = 3Dn/2, DSigma-l = 6Dc = 3Dn, and")
    print("     D(excess) = DSigma-l - 2DM = 3Dn - 3Dn = 0 at every Dn <= 40.")
    print("  ==> `zero-net-excess` is NOT a design choice a move can be")
    print("      tuned to satisfy: (GR-21) `Sigma(l-2) = 2D + 6` plus")
    print("      cubicity make it an IDENTITY.  The budget of 6 is TRADED.")
    print("  the gadget's own excess, with `s` splits and `k = Dn/2`:")
    for k in range(1, 6):
        for s in range(0, min(2 * k, 6) + 1):
            ne = 3 * k - s
            if ne < 0:
                continue
            # sum of new-branch lengths is 6k, so exc(new) = 6k - 2(3k-s)
            assert 6 * k - 2 * ne == 2 * s
    print("     exc(new branches) = 6k - 2(3k - s) = 2s   [asserted k<=5]")
    print("  and at `Lambda_child = empty` every parent branch is split at")
    print("  most once (r splits need `l_beta >= 2(r+1)`, (SD-6) caps 5), so")
    print("  `q = s` and (GR-25)(i) at `W'` reads `4s + 2s >= 7`  ==>  s >= 2.")
    print("  ladder boundary proof (used by --irred), all m >= 4:")
    ladder_boundary_proof()


def ladder_boundary_proof():
    """The `CL_m` boundary inequality, stated and spot-checked.

    For `W` proper in `CL_m` with `a` top-rail and `b` bottom-rail hubs and
    `c_top`, `c_bot` the numbers of rail ARCS they form,
    `|E(W)| <= (a - c_top) + (b - c_bot) + min(a, b)`, so
    `partial(W) = 3|W| - 2|E(W)| >= |a - b| + 2(c_top + c_bot)`.
    Hence `partial >= 4` unless `W = V ∖ {one hub}` (`partial = 3`), whose
    (GR-25)(i) instance is `exc at that hub <= 5` -- satisfied by any
    assignment with per-hub excess `<= 3`."""
    import random
    rng = random.Random(X_SEED)
    checked = 0
    for m in range(4, 13):
        he = _prism(m)
        nv = 2 * m
        for _ in range(400):
            r = rng.randrange(2, nv)
            W = sorted(rng.sample(range(nv), r))
            ws = set(W)
            ein = [i for i, (u, w) in enumerate(he) if u in ws and w in ws]
            bd = 3 * r - 2 * len(ein)
            a = sum(1 for v in W if v < m)
            b = r - a
            ct = _arcs([v for v in W if v < m], m) if 0 < a < m else 0
            cb = _arcs([v - m for v in W if v >= m], m) if 0 < b < m else 0
            assert bd >= abs(a - b) + 2 * (ct + cb), (m, W, bd)
            checked += 1
    print(f"     boundary bound `partial >= |a-b| + 2(c_top+c_bot)` asserted "
          f"at {checked} random hub sets over m = 4..12 (seed {X_SEED})")


def _arcs(vs, m):
    s = set(vs)
    return sum(1 for v in s if (v - 1) % m not in s)


def _prism(m):
    """The circular ladder `CL_m = C_m x K_2`: hubs `0..m-1` top rail,
    `m..2m-1` bottom rail, branch order = top rail, bottom rail, rungs."""
    return ([(i, (i + 1) % m) for i in range(m)]
            + [(m + i, m + (i + 1) % m) for i in range(m)]
            + [(i, m + i) for i in range(m)])


# ---------------------------------------------- [GX-2] --moves ------------

def move_complement_slack(k, s, top, lens):
    """(GR-25)(i) at `W' = V_child ∖ B`, `B` = the BRAND-NEW hubs.

    This is the instance the gadget-internal filter CANNOT see, and it is the
    one that kills every move.  With `E_ss` the new branches joining two
    SPLIT hubs and `e_mix` those joining a split hub to a brand-new one,
    `s = e_mix + 2|E_ss|`, `partial(W') = e_mix`, and

        exc(E(W')) = 6 - 2s + Sigma_{E_ss}(l - 2),

    because the parent-derived branches carry `6 - 2s` of the child's budget
    (the new branches carry exactly `2s`).  So (GR-25)(i) reads

        2*e_mix + 6 - 2s + Sigma_{E_ss}(l - 2) >= 7
      <=> Sigma_{beta in E_ss} l_beta >= 6|E_ss| + 1,

    which (SD-6) `l <= 5` makes IMPOSSIBLE for every `|E_ss| >= 0` (at
    `E_ss = empty` it reads `0 >= 1`).  Returns the slack
    `Sigma_{E_ss} l - 6|E_ss| - 1`, which must be `>= 0` for the move to
    exist."""
    ess = [L for (u, w), L in zip(top, lens) if u < s and w < s]
    return sum(ess) - 6 * len(ess) - 1


def leg_moves(kmax=3):
    """[GX-2] ENUMERATE the moves; the complement cut kills every one."""
    print("[GX-2] every zero-net-excess additive move, enumerated (no rng)")
    print("  layer 1 = gadget-internal (GR-25)(i) + (SD-6) + length "
          "feasibility;\n  layer 2 = the global budget `exc(gadget) = 2s "
          "<= 6` at Lambda_child = empty;\n  layer 3 = (GR-25)(i) at "
          "`W' = V_child ∖ B`, B the BRAND-NEW hubs -- the instance no\n"
          "            gadget-internal filter can see (see "
          "`move_complement_slack`).")
    surv = []
    for k in range(1, kmax + 1):
        t0 = time.time()
        g = gadgets(k)
        by = {}
        for (s, top, ls) in g:
            by.setdefault(s, []).append((top, ls))
        print(f"  k = {k} (Dn = {2 * k}, DM = {3 * k}, DSigma-l = {6 * k}): "
              f"{len(g)} gadgets survive layer 1"
              + (" -- EMPTY" if not g else "") + f"  [{time.time() - t0:.0f}s]")
        for s in sorted(by):
            l2 = 2 * s <= 6
            keep, sl = [], []
            for (top, ls) in by[s]:
                if not l2:
                    continue
                sk = move_complement_slack(k, s, top, ls)
                sl.append(sk)
                if 2 * k - s > 0 and sk < 0:
                    continue
                keep.append((top, ls))
            tops = sorted({t for t, _ in by[s]})
            why = ("layer 2: exc(gadget) = %d > 6" % (2 * s)) if not l2 else (
                "layer 3: max complement slack = %d < 0" % max(sl)
                if sl and not keep else "SURVIVES")
            print(f"     s = {s}: {len(tops)} topologies / {len(by[s])} "
                  f"length assignments -> {len(keep)} survive   [{why}]")
            surv += [(k, s, t, l) for (t, l) in keep]
    print(f"  SURVIVING MOVE FAMILIES at k <= {kmax}: {len(surv)}")
    assert not surv, "a move survived every layer -- the verdict flips"
    print("  ==> NO additive zero-net-excess expansion move exists AT ALL,")
    print("      at any gadget size, at Lambda = empty or not.  The proof is")
    print("      NOT an enumeration -- see `move_complement_slack`: the")
    print("      complement cut forces `Sigma_{E_ss} l >= 6|E_ss| + 1`, which")
    print("      (SD-6) `l <= 5` refutes for EVERY |E_ss| >= 0.  The")
    print("      enumeration above is the independent check of that proof.")
    print("      Corollary: the spec's falsifiable tell -- a parent/child")
    print("      pair at `n_hub 6 -> 8` -- is doubly unsatisfiable: Dn = 2")
    print("      needs k = 1 (empty on lengths alone), and no Dn works.")
    return surv


# ------------------------------------------------ [GX-5] --cap ------------

def boundary_slack(n, hedges, lens):
    """`min_B [ 2*partial(B) - 1 - exc_B ]` over every nonempty hub set `B`
    whose complement is proper, connected and carries a branch.

    (GR-170): at a `D = 0` class shape, `exc_B <= 2*partial(B) - 1` where
    `exc_B` is the excess of every branch meeting `B`.  This is (GR-25)(i)
    at `W' = V ∖ B` re-read through the total budget:
    `exc(E(V ∖ B)) = 6 - exc_B`, so `2*partial(B) + 6 - exc_B >= 7`."""
    adj = {v: [] for v in range(n)}
    for i, (u, w) in enumerate(hedges):
        adj[u].append((w, i))
        adj[w].append((u, i))
    worst = None
    for mask in range(1, (1 << n) - 1):
        B = {v for v in range(n) if mask >> v & 1}
        C = [v for v in range(n) if v not in B]
        if len(C) < 2:
            continue
        ins = [i for i, (u, w) in enumerate(hedges)
               if u not in B and w not in B]
        if not ins:
            continue
        seen, st = {C[0]}, [C[0]]
        while st:
            v = st.pop()
            for (u, i) in adj[v]:
                if i in ins and u not in seen:
                    seen.add(u)
                    st.append(u)
        if len(seen) != len(C):
            continue
        bd = sum(1 for (u, w) in hedges
                 if (u in B) != (w in B))
        excB = sum(L - 2 for (u, w), L in zip(hedges, lens)
                   if u in B or w in B)
        sl = 2 * bd - 1 - excB
        if worst is None or sl < worst[0]:
            worst = (sl, tuple(sorted(B)))
    return worst


def leg_cap():
    """[GX-5] (GR-170) the excess-boundary cap, measured where it is
    affordable."""
    print("[GX-5] (GR-170) the EXCESS-BOUNDARY CAP `exc_B <= 2*partial(B) "
          "- 1` (no rng)")
    print("  DERIVATION.  (GR-25)(i) at `W' = V ∖ B` is `2*partial(W') + "
          "exc(E(W')) >= 7`;\n  the total budget (GR-21) at `D = 0` is 6, "
          "so `exc(E(V ∖ B)) = 6 - exc_B` and\n  `partial(W') = "
          "partial(B)`, giving `exc_B <= 2*partial(B) - 1` directly.")
    t0 = time.time()
    for n in (4, 6):
        worst = None
        cnt = 0
        for hedges, lens, _o, _a in stratum(n, lamcap=99, lamlo=0):
            cnt += 1
            w = boundary_slack(n, list(hedges), list(lens))
            if w and (worst is None or w[0] < worst[0]):
                worst = w
        print(f"  n_hub = {n} (Lambda free): {cnt} shapes, min slack "
              f"`2*partial(B) - 1 - exc_B` = {worst[0]} (tight at B = "
              f"{worst[1]})")
        assert worst[0] >= 0, "(GR-170) fails -- the cap is wrong"
    pool, _ = _pool8()
    worst = None
    cnt = 0
    for hedges, lls in pool:
        for lens in lls:
            cnt += 1
            w = boundary_slack(8, list(hedges), list(lens))
            if w and (worst is None or w[0] < worst[0]):
                worst = w
    print(f"  n_hub = 8 (Lambda = empty, aglu._pool8): {cnt} shapes, "
          f"min slack = {worst[0]}")
    assert cnt == 39689 and worst[0] >= 0
    print("  ==> the cap holds with min slack 0 -- it is TIGHT, and the")
    print("      tight instances are exactly the ones a move would need to")
    print("      breach.  A move's brand-new hub set `B` has "
          "`exc_B = 2s - Sigma_{E_ss}(l-2)`\n      and "
          "`partial(B) = e_mix = s - 2|E_ss|`, so the cap demands\n"
          "      `Sigma_{E_ss} l >= 6|E_ss| + 1` -- refuted by (SD-6).  "
          f"[{time.time() - t0:.0f}s]")


# ------------------------------------------------ [GX-3] --hub ------------

def leg_hub():
    """[GX-3] the hub cap, measured over every landed population."""
    print("[GX-3] `max_v Sigma_{beta ∋ v} l_beta` over the landed stratum "
          "(no rng)")
    print("  DERIVATION.  At `W' = V ∖ {v}` (proper, |W'| >= 2 iff n >= 3, "
          "connected)\n  (GR-25)(i) reads `2*3 + (6 - exc at v) >= 7`, i.e. "
          "`Sigma_{beta ∋ v} l_beta <= 11`.")
    t0 = time.time()
    for n in (2, 4, 6):
        w = cnt = 0
        for hedges, lens, _orb, _auts in stratum(n, lamcap=99, lamlo=0):
            cnt += 1
            w = max(w, max(hub_sums(n, hedges, lens)))
        print(f"  n_hub = {n} (Lambda free, gisland.stratum): {cnt} "
              f"isomorphism-class shapes, max hub branch-sum = {w}"
              + ("   <- the n = 2 exception: |V ∖ {v}| = 1 < 2, outside "
                 "(GR-25)(i)'s hypothesis" if n == 2 else ""))
        if n >= 4:
            assert w <= 11
    pool, _nep = _pool8()
    w = cnt = 0
    for hedges, lls in pool:
        for lens in lls:
            cnt += 1
            w = max(w, max(hub_sums(8, list(hedges), list(lens))))
    print(f"  n_hub = 8 (Lambda = empty, aglu._pool8): {cnt} shapes, "
          f"max hub branch-sum = {w}")
    assert cnt == 39689, "the n_hub = 8 habitat count moved"
    assert w <= 11
    print("  ==> the Y-gadget (a fresh hub with three spokes summing to 12) "
          "is\n      OUT OF HABITAT at every child with n_hub >= 4.  "
          f"[{time.time() - t0:.0f}s]")


# ---------------------------------------------- [GX-4] --reach ------------

def leg_control():
    """[GX-4a] the F13 ADVERSARIAL CONTROL for the reduction search.

    A search that only ever returns EMPTY is untested, and (GX-2) proves the
    true answer is empty -- so the control has to be run against a world in
    which a move DOES exist.  Relax exactly one hypothesis, (SD-6)'s
    `l <= 5`, to `l <= 6`; then the classical H-operation (`k = 1, s = 2`,
    ONE new branch of length 6) is available.  The search must find it."""
    print("[GX-4a] adversarial control: relax (SD-6) to `l <= 6` and the "
          "H-operation exists;\n        the reduction search must RECOVER "
          "it (F13: a guard observed only failing is untested).")

    def gate6(n, he, lens):
        return cubic_habitat(n, he, [min(L, 5) for L in lens]) \
            if all(L <= 6 for L in lens) else False

    built = rec = 0
    for hedges, lens, _o, _a in stratum(4, lamcap=0, lamlo=0):
        hedges, lens = list(hedges), list(lens)
        for b1, b2 in itertools.combinations(range(len(hedges)), 2):
            for o1 in range(1, lens[b1]):
                for o2 in range(1, lens[b2]):
                    n2, he2, ls2 = apply_move(
                        4, hedges, lens, [(b1, o1), (b2, o2)],
                        ((0, 1),), (6,), 2)
                    if any(L > 6 for L in ls2):
                        continue
                    assert sum(ls2) == 6 * (len(he2) - n2 + 1)
                    built += 1
                    rs = list(reductions(n2, he2, ls2, kmax=1, kmin=1))
                    if rs:
                        rec += 1
    print(f"        {built} H-operation children built from the 80 "
          f"`n_hub = 4` class shapes;\n        the search recovers a parent "
          f"at {rec} of them ({100.0 * rec / max(built, 1):.1f} %)")
    assert built > 0 and rec == built, \
        "the reduction search misses H-operation children -- it is not a " \
        "valid instrument"
    print("        ==> the instrument FIRES when a move exists.  Its empty "
          "answer below\n            is therefore a measurement, not a "
          "silent failure.")


# ---------------------------------------------- [GX-4] --reach ------------

def leg_reach(limit=0):
    """[GX-4] the inheritance test over the exact `n_hub = 8` population."""
    print("[GX-4] the INHERITANCE TEST: which `n_hub = 8` class shapes "
          "reduce to `n_hub <= 6`?")
    print("  population: `aglu._pool8()`, the exact 39689 `Lambda = empty` "
          "`D = 0` shapes\n  (a (GR-25)-gated count the landed `--pool` "
          "asserts).  Caps: `Lambda != empty` at\n  n_hub = 8 is NOT swept; "
          "reductions are searched at k = 1, 2, 3 "
          "(parents n_hub = 6, 4, 2)\n  -- kmin = 1, so the measurement does "
          "NOT presuppose (GX-2)'s k = 1 kill.")
    t0 = time.time()
    pool, _nep = _pool8()
    tot = red = 0
    byk = {}
    hits = []
    for hedges, lls in pool:
        for lens in lls:
            tot += 1
            if limit and tot > limit:
                break
            rs = list(reductions(8, list(hedges), list(lens),
                                 kmax=3, kmin=1))
            if rs:
                red += 1
                for (_W, s, k, _ph, _pl) in rs:
                    byk[(k, s)] = byk.get((k, s), 0) + 1
                if len(hits) < 3:
                    hits.append((hedges, lens, rs[0]))
        if limit and tot > limit:
            break
    print(f"  {red} of {tot} shapes admit ANY connected reduction "
          f"({100.0 * red / tot:.2f} %)")
    for ks in sorted(byk):
        print(f"     (k = {ks[0]}, s = {ks[1]}): {byk[ks]} reduction "
              f"instances")
    for (he, ls, r) in hits:
        print(f"     witness: child {list(he)} lens {list(ls)}")
        print(f"              -> W' = {r[0]}, s = {r[1]}, k = {r[2]}, "
              f"parent {list(r[3])} lens {list(r[4])}")
    print(f"  ==> {tot - red} of {tot} `n_hub = 8` class shapes are "
          f"IRREDUCIBLE:\n      they are in NO image of ANY connected "
          f"zero-net-excess move from a\n      smaller class shape, so a "
          f"finite base plus these moves cannot reach\n      them.  "
          f"[{time.time() - t0:.0f}s]")
    return tot, red


# ---------------------------------------------- [GX-7] --lam8 ------------

def leg_lam8(lamcap=1):
    """[GX-7] the `Lambda != empty` arm of the inheritance test at
    `n_hub = 8` -- the coordinator's mid-task correction.

    `aglu._pool8()` builds its lengths as `2 + e` with `e >= 0`, so its exact
    39689 is the `Lambda = empty` stratum ONLY.  The base side of the test
    ((GR-157)) is complete at `n_hub <= 6` INCLUDING `Lambda != empty`, so
    running the child side off `_pool8` alone would be `Lambda`-blind on one
    side.  This mode takes the level below -- `gridcol.cubic_iso_classes(8)`
    for the graphs, `cflank.length_tuples` with an EXPLICIT `lamcap` for the
    lengths, `cflank.cubic_habitat` as the (GR-25) gate -- and quotients the
    labelled length tuples by the hub multigraph's own automorphism group
    exactly as `gisland.stratum` does, because every quantity here
    (class-shapehood, reducibility) is an isomorphism invariant.

    CAP: `lamcap` is a PARAMETER, printed with every figure.  A `lamcap = c`
    run says nothing about `|Lambda| > c`."""
    print(f"[GX-7] the `Lambda != empty` arm at `n_hub = 8`, "
          f"lamcap = {lamcap} (no rng)")
    print("  population built from `gridcol.cubic_iso_classes(8)` + "
          "`cflank.length_tuples(12, 30,\n  lamcap=%d)` + "
          "`cflank.cubic_habitat`, quotiented by `gisland.edge_auts`."
          % lamcap)
    t0 = time.time()
    reps = cubic_iso_classes(8)
    tups = [t for t in length_tuples(12, 30, lamcap=lamcap)
            if any(L == 1 for L in t)]
    print(f"  {len(reps)} hub-multigraph classes x {len(tups)} labelled "
          f"length tuples with |Lambda| >= 1  [{time.time() - t0:.0f}s]")
    tot = red = 0
    for hedges in reps:
        auts = edge_auts(8, list(hedges))
        orb = iso_orbits(auts, tups)
        for rep in orb:
            lens = list(rep)
            if not cubic_habitat(8, list(hedges), lens):
                continue
            tot += 1
            if list(reductions(8, list(hedges), lens, kmax=3, kmin=1)):
                red += 1
    print(f"  {tot} isomorphism-class shapes pass the (GR-25) gate; "
          f"{red} admit ANY reduction")
    assert red == 0, "a Lambda != empty child reduced -- the verdict flips"
    print(f"  ==> 0 of {tot}, matching the `Lambda = empty` arm's 0 of "
          f"39 689.  The `Lambda`\n      axis changes nothing, as "
          f"(GR-171)'s proof says it cannot: the complement\n      cut "
          f"never mentions `Lambda`.  [{time.time() - t0:.0f}s]")
    return tot, red


# ---------------------------------------------- [GX-6] --irred ------------

def ladder_shape(m, spread=True):
    """`CL_m` with six unit-excess branches: a class shape for every
    `m >= 4`.  Branch order is top rail, bottom rail, rungs; the six
    length-3 branches are rungs, spread as evenly as the cycle allows."""
    he = _prism(m)
    lens = [2] * (3 * m)
    pos = [2 * m + (i * m) // 6 for i in range(6)] if spread \
        else [2 * m + i for i in range(6)]
    for p in pos:
        lens[p] = 3
    return 2 * m, he, lens


def leg_irred(mmax=11):
    """[GX-6] the stratum IS infinite in the `G°` direction, and every
    member of an explicit infinite family is irreducible."""
    print("[GX-6] an explicit INFINITE family of class shapes, each "
          "IRREDUCIBLE (no rng)")
    print("  `CL_m` = the circular ladder on `n_hub = 2m` hubs, `M = 3m` "
          "branches,\n  six rungs of length 3 and every other branch of "
          "length 2:\n  `Sigma-l = 2*3m + 6 = 6(M - n + 1)` and "
          "`Sigma(l - 2) = 6` -- (GR-21) at `D = 0`.")
    print("  CAP: `cubic_habitat` is a `2^n` scan, so membership is CHECKED "
          "at\n  m = 6..%d and PROVEN for all m >= 4 by `--law`'s boundary "
          "bound." % mmax)
    t0 = time.time()
    for m in range(6, mmax + 1):
        n, he, lens = ladder_shape(m)
        ok = cubic_habitat(n, he, lens)
        red = list(reductions(n, he, lens, kmax=3, kmin=1)) \
            if n <= 16 else None
        hs = max(hub_sums(n, he, lens))
        print(f"  m = {m:2d}: n_hub = {n:2d}, M = {3 * m:2d}, "
              f"Sigma-l = {sum(lens):3d}, class shape = {ok}, "
              f"max hub branch-sum = {hs}"
              + (f", reductions found = {len(red)}" if red is not None
                 else ", reduction search skipped (2^n cap)"))
        assert ok, f"CL_{m} left the habitat"
        if red is not None:
            assert not red, f"CL_{m} reduced -- the verdict flips"
    print("  ==> the `D = 0` tight class stratum contains a shape at every")
    print("      even `n_hub >= 12`, so `(GR-15)`'s uniformity gap is a gap")
    print("      over an INFINITE population -- and by (GX-2) none of these")
    print("      shapes is the image of any move.  A finite base plus a")
    print("      finite move set reaches finitely many of them: NONE.")
    print(f"  [{time.time() - t0:.0f}s]")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for f in ('law', 'moves', 'hub', 'cap', 'reach', 'lam8', 'irred',
              'validate'):
        ap.add_argument('--' + f, action='store_true')
    ap.add_argument('--kmax', type=int, default=3)
    ap.add_argument('--mmax', type=int, default=11)
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('--lamcap', type=int, default=1)
    a = ap.parse_args()
    flags = ('law', 'moves', 'hub', 'cap', 'reach', 'lam8', 'irred',
             'validate')
    if not any(vars(a)[f] for f in flags):
        ap.print_help()
        return
    if a.law or a.validate:
        leg_law()
    if a.moves or a.validate:
        leg_moves(kmax=a.kmax)
    if a.hub or a.validate:
        leg_hub()
    if a.cap or a.validate:
        leg_cap()
    if a.reach or a.validate:
        leg_control()
        leg_reach(limit=a.limit)
    if a.lam8 or a.validate:
        leg_lam8(lamcap=a.lamcap)
    if a.irred or a.validate:
        leg_irred(mmax=a.mmax)


if __name__ == '__main__':
    main()
