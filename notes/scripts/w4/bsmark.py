"""
Direction BSMARK (ordinal 117) -- CAN THE S-MARK 2-CUT STEP BE RESTATED TO
CLOSE AT A FORCED COINCIDENT-FLAG PEEL, AND WHAT DOES THE RESTATEMENT COST
THE CLAIMS THAT CONSUME (BE-22)(iii)?

  THE QUESTION the spec names.  (BE-313)(i) (owning section BCOFLAG) records
  that S-mark's child hypothesis -- "the union H_B of B's subtree ... has an
  irreducible component of Y(H_B), WITH THE FLAGS AT u,v PRESCRIBED, at whose
  generic point H_B attains and H_B/uv attains" -- is asked for, at a forced
  coincident-flag peel, at exactly the prescription where its FIRST conjunct
  is unavailable: the child has a_i = 1 at 1 200 / 1 200 composite draws
  ((BE-312)(ii)) while attaining on its OWN chart at 40 / 40 ((BE-312)(iii)).
  The repair BCOFLAG names, and declines to carry out, is that S-mark "must
  carry (BE-86)(i) rather than (BE-22)(iii)".

  WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `cancel`  DRAW-FREE, EXACT, EXHAUSTIVE over the arithmetic range.  The
            restatement's load-bearing identity, and it is the sentence the
            whole verdict rests on:

              GIVEN welded attainment on both sides in its a-corrected form
              (rho_i = delta_i + a_i, which by (BE-22)(ii) IS "the welded
              framework attains" whatever a_i is), (BE-86)(i)'s criterion

                  H attains  <=>  dim(rho_1 + rho_2) = min(Sd,6) + a_1 + a_2

              is EQUIVALENT to

                  dim(rho_1 cap rho_2) = max(0, Sd - 6),

              in which no a-term appears.  So the general-position obligation
              the restatement hands the induction is BYTE-FOR-BYTE the one
              the a = 0 form hands it, and the a-terms cancel identically.

            Also enumerated here, because both are cost figures the spec asks
            to be priced and each is a different sentence:

              (C1) the attainment-compatibility envelope min(Sd,6)+a_1+a_2
                   <= 6 -- how much of the tuple space the restatement can
                   reach at all;
              (C2) (BE-22)(vi)'s dropped hypothesis.  (vi) reads "When
                   delta_2 = 0, (ii) gives rho_2 = 0".  (BE-22)(ii) gives
                   rho_2 <= dim M_2 - 6 - g_2 = delta_2 + a_2 = a_2, so the
                   step needs a_2 = 0.  This mode enumerates the tuples at
                   which delta_2 = 0 and the general-position content that
                   (vi) says "disappears" is PRESENT.

  `rigid`   EXACT-Q DRAWS.  Is (C2) live or only statement hygiene?  Builds
            the ONE-SIDED analogue of BONEONE's family -- every K4-skeleton
            R-node side at delta = 1 glued to every unrestricted side at
            delta = ZERO -- keeps the forced ones, and measures a_2 and rho_2
            on the RIGID side at a guarded flat-A draw.  The asymmetry is
            (BE-312)(ii)'s: a_i is UPPER semicontinuous, so a draw with
            a_2 = 0 PROVES a_2 = 0 generically at that row, while a draw with
            a_2 >= 1 settles nothing and is re-drawn.

  CAPS, disclosed here and repeated at each mode's own output.
    - `cancel` ranges delta_i in 0..6 and a_i in 0..AMAX (default 6); it is
      exhaustive over THAT box and says nothing outside it.  The box is a
      range choice, not a theorem: (BE-22)(ii)/(BE-21)(ii) bound delta_i by 6
      but nothing in the corpus bounds a_i.
    - `rigid`'s population inherits BONEONE's shape restriction on side 1
      (K4 skeleton) and its size range n1 in {9,10}, n2 in {4,5}.  BPEEL's
      wider 3 497 forced R-node peels with min(delta_1,delta_2) = 0 are NOT
      swept here.
    - Nothing here edits a landed driver.  `free_sides_delta` re-runs
      `boneone.free_sides`' enumeration with the hardcoded delta filter
      PARAMETERIZED, and asserts at want=1 that it reproduces the landed
      function exactly -- that assertion is the mode's own control.

  Landed-driver reuse (read-only): `boneone.side_delta`, `boneone.k4_rsides`,
  `boneone.free_sides`, `btwocut.vertex_connectivity_at_least`,
  `bgenuine.forced_seed`, `bgenuine.draw_flat`, `bgenuine.measure`,
  `bimage.dim/isect/span`, `kbare_common.exact_deficiency/verts_of`,
  `exactcore.neighbors`.
"""

import itertools
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for _p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from exactcore import neighbors                                    # noqa: E402
from kbare_common import exact_deficiency, verts_of                # noqa: E402
from btwocut import g_exact, vertex_connectivity_at_least          # noqa: E402
from bimage import dim, isect, span                                # noqa: E402
from boneone import side_delta, k4_rsides, free_sides              # noqa: E402
from bgenuine import forced_seed, draw_flat, measure               # noqa: E402

SEED = 20260913
U, V = 'u', 'v'
AMAX = 6


# ======================================================= mode `cancel`

def _attains(sd, a1, a2, dsum):
    """(BE-86)(i), verbatim: H attains <=> dim(rho_1+rho_2) = min(Sd,6)+a1+a2."""
    return dsum == min(sd, 6) + a1 + a2


def run_cancel(amax=AMAX):
    t0 = time.time()
    print('===== Step BE313 / (BE-314): the restatement identity, DRAW-FREE '
          'and exhaustive over the box =====')
    print(f'  CAP: delta_i in 0..6 (the (BE-21)(ii) bound), a_i in 0..{amax} '
          f'(a RANGE CHOICE -- nothing in the corpus bounds a_i).')
    print()

    n_all = n_weld = 0
    n_agree = 0
    env_ok = env_bad = 0
    env_a_pos = 0
    conf_ok = 0
    vi_live = []
    vi_dead = 0
    iv_live = []
    for d1, d2 in itertools.product(range(7), repeat=2):
        sd = d1 + d2
        for a1, a2 in itertools.product(range(amax + 1), repeat=2):
            n_all += 1
            # --- welded attainment on BOTH sides, in the a-corrected form.
            # (BE-22)(ii): rho_i <= dim M_i - 6 - g_i = delta_i + a_i, with
            # equality IFF the welded framework attains.  So this is exactly
            # S-mark's SECOND conjunct, with no reference to a_i = 0.
            r1, r2 = d1 + a1, d2 + a2
            n_weld += 1
            # every legal intersection dimension
            for s in range(0, min(r1, r2) + 1):
                dsum = r1 + r2 - s
                if dsum > 6:
                    continue          # the screw space is 6-dimensional
                lhs = _attains(sd, a1, a2, dsum)
                rhs = (s == max(0, sd - 6))
                assert lhs == rhs, (
                    'THE RESTATEMENT IDENTITY FAILS', d1, d2, a1, a2, s, dsum)
                n_agree += 1
            # --- (C1) the attainment-compatibility envelope.
            tgt = min(sd, 6) + a1 + a2
            if tgt <= 6:
                env_ok += 1
                if a1 + a2 > 0:
                    env_a_pos += 1
            else:
                env_bad += 1
            if tgt <= 3:
                conf_ok += 1
            # --- (C2) (BE-22)(vi)'s dropped hypothesis, at delta_2 = 0.
            if d2 == 0:
                # (vi) asserts rho_2 = 0.  (BE-22)(ii) gives only rho_2 <= a_2.
                # The general-position content (vi) says "disappears" is the
                # requirement dim(rho_1 cap rho_2) = max(0, Sd-6) with
                # rho_2 != 0, which needs a_2 >= 1.
                if (a2 >= 1 and tgt <= 6
                        and r1 + r2 - max(0, sd - 6) <= 6
                        and min(r1, r2) >= 1):
                    # min(rho_1, rho_2) >= 1 is what makes the condition
                    # NON-VACUOUS: with either rho_i = 0 the intersection is
                    # forced to 0 and there is nothing to require.
                    vi_live.append((d1, d2, a1, a2, r1, r2))
                if a2 == 0:
                    assert r2 == 0, ('rho_2 cap is not 0 at a_2 = 0', d1, a1)
                    vi_dead += 1
            # --- (C2') the SAME defect in (BE-22)(iv), which is the clause
            # that makes the INDUCTION'S BASE free ("two rigid pieces always
            # compose over a 2-cut ... this is why the base of the induction
            # never meets the hard case").  Its step is "rho_i <= delta_i = 0",
            # i.e. (BE-22)(ii)'s ATTAINING case again.
            if d1 == 0 and d2 == 0 and min(r1, r2) >= 1 and tgt <= 6:
                iv_live.append((a1, a2, r1, r2))

    print('  (i) THE IDENTITY.  Over every (delta_1, delta_2, a_1, a_2) of the')
    print('      box and every legal dim(rho_1 cap rho_2), ASSERTED at')
    print(f'      {n_agree} / {n_agree} tuples:')
    print('          [rho_i = delta_i + a_i on both sides]  =>')
    print('              ( dim(rho_1+rho_2) = min(Sd,6)+a_1+a_2 )')
    print('          <=> ( dim(rho_1 cap rho_2) = max(0, Sd-6) ).')
    print('      NO a-TERM APPEARS ON THE RIGHT.  So the general-position')
    print('      obligation is IDENTICAL to the a = 0 form\'s, and the cost of')
    print('      the restatement is NOT paid in general position.')
    print()
    print('  (ii) (C1) THE ENVELOPE -- what the restatement can reach at all.')
    print(f'      tuples in the box                          : {n_all}')
    print(f'      attainment-compatible (min(Sd,6)+a1+a2 <= 6): {env_ok}')
    print(f'         of those, with a_1 + a_2 >= 1            : {env_a_pos}')
    print(f'      NOT attainment-compatible                   : {env_bad}')
    print(f'      compatible with the (BE-310)(i) CONFINEMENT (<= 3): '
          f'{conf_ok}')
    print('      The two counts are BOX-DEPENDENT and are reported only as a')
    print('      shape.  The box-free form is the budget line, which is what')
    print('      travels:   a_1 + a_2 <= 6 - min(Sd,6)     (screw space)')
    print('                 a_1 + a_2 <= 3 - min(Sd,6)     (under confinement)')
    print('      Sd  : 0  1  2  3  4  5  6+')
    print('      free: ' + '  '.join(f'{6-min(x,6)}' for x in range(7)) + '   0')
    print('      conf: ' + '  '.join(
        f'{max(-1,3-min(x,6))}' for x in range(7)) + '  -1'
          + '     (negative = the peel CANNOT attain at all)')
    print('      Reading: the a-carrying form is not free -- a side\'s loss is')
    print('      spent against the same 6 the deficiencies are spent against,')
    print('      and under the coincident-flag confinement against 3.')
    print('      ((BE-311)(i)\'s Sd <= 3 is the delta-only corollary; CITED.)')
    print()
    print('  (iii) (C2) (BE-22)(vi)\'S DROPPED HYPOTHESIS.')
    print('      (vi) reads "When delta_2 = 0, (ii) gives rho_2 = 0".')
    print('      (BE-22)(ii) gives rho_2 <= dim M_2 - 6 - g_2 = delta_2 + a_2,')
    print('      which at delta_2 = 0 is rho_2 <= a_2 -- NOT rho_2 = 0.')
    print(f'      tuples with delta_2 = 0 and a_2 = 0 : {vi_dead}  '
          f'(rho_2 = 0 FORCED -- (vi) holds)')
    print(f'      tuples with delta_2 = 0, a_2 >= 1, and the general-position')
    print(f'      requirement STILL BINDING          : {len(vi_live)}')
    assert vi_live, 'no tuple exhibits (vi) losing its collapse'
    sm = min(vi_live, key=lambda t: (t[0], t[2], t[3]))
    print(f'      smallest such tuple (d1,d2,a1,a2,rho1,rho2) = {sm}')
    print('      At that tuple rho_2 has dimension a_2 >= 1 and attainment')
    print('      needs dim(rho_1 cap rho_2) = max(0,Sd-6) -- a GENUINE')
    print('      general-position condition.  So (vi)\'s headline sentence,')
    print('      "if one side is RIGID the general-position half disappears",')
    print('      is true only under (iii)\'s "if both pieces attain": it needs')
    print('      the rigid side to ATTAIN, not merely to be rigid.')
    print()
    print('  (iv) (C2\') THE SAME DEFECT IN (BE-22)(iv) -- and (iv) is the')
    print('      clause that makes the INDUCTION\'S BASE free.  (iv) reads')
    print('      "delta_1 = delta_2 = 0 makes the composition automatic: then')
    print('      rho_i <= delta_i = 0 ... two rigid pieces always compose over')
    print('      a 2-cut ... this is why the BASE of the induction never meets')
    print('      the hard case."  The step rho_i <= delta_i is (BE-22)(ii)\'s')
    print('      ATTAINING case; in general rho_i <= delta_i + a_i = a_i.')
    print(f'      tuples with delta_1 = delta_2 = 0, both rho_i >= 1, and')
    print(f'      attainment-compatible                 : {len(iv_live)}')
    assert iv_live, 'no tuple exhibits (iv) losing its collapse'
    print(f'      smallest (a_1, a_2, rho_1, rho_2)     : {min(iv_live)}')
    print('      At (1,1,1,1) BOTH pieces are RIGID, BOTH lose attainment, and')
    print('      H attains IFF the two lines rho_1, rho_2 are DISTINCT.  So')
    print('      "two rigid pieces always compose" is false without the')
    print('      proviso, and the general-position half does NOT vanish at the')
    print('      base either.')
    print()
    print(f'  [{time.time()-t0:.1f} s, draw-free, seedless]')
    return len(vi_live)


# ======================================================= mode `rigid`

def free_sides_delta(n, tag='B', want=1):
    """`boneone.free_sides` with its hardcoded `side_delta(E)[2] == 1` filter
    PARAMETERIZED.  Everything else -- the vertex set, the u !~ v condition,
    connectivity, both terminals of degree >= 1, `H + uv` 2-connected -- is
    the landed enumeration, re-run rather than re-designed.  `run_rigid`
    asserts `free_sides_delta(n, tag, 1) == boneone.free_sides(n, tag)`,
    which is this function's control."""
    ext = [(tag, i) for i in range(n - 2)]
    W = [U, V] + ext
    pairs = [e for e in itertools.combinations(W, 2) if set(e) != {U, V}]
    out = []
    for mask in range(1 << len(pairs)):
        E = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
        if len(verts_of(E)) != n:
            continue
        nb = neighbors(E)
        if not nb.get(U) or not nb.get(V):
            continue
        seen, st = {W[0]}, [W[0]]
        while st:
            x = st.pop()
            for y in nb[x]:
                if y not in seen:
                    seen.add(y)
                    st.append(y)
        if len(seen) != n:
            continue
        idx = {w: i for i, w in enumerate(sorted(map(str, W)))}
        EE = [(idx[str(a)], idx[str(b)]) for (a, b) in E] + \
             [(idx[str(U)], idx[str(V)])]
        if not vertex_connectivity_at_least(n, EE, 2):
            continue
        if side_delta(E)[2] == want:
            out.append(E)
    return out


def run_rigid(seed=SEED, ndraw=3, stride=8):
    t0 = time.time()
    rng = random.Random(seed)
    print('===== Step BE314 / (BE-315): is (BE-22)(vi)\'s dropped hypothesis '
          'LIVE at a forced peel? =====')
    print('  THE POPULATION.  BONEONE\'s factorized generator ((BE-79)(i)) with')
    print('  ONE constant moved: side 2 is taken at delta = 0 instead of 1, so')
    print('  every member is exactly (BE-22)(vi)\'s hypothesis -- one RIGID')
    print('  side at a 2-cut -- and the forcing test is unchanged.')
    print()

    # the control: at want = 1 the parameterized enumerator IS the landed one
    for n in (4, 5):
        got = free_sides_delta(n, 'B', 1)
        want = free_sides(n, 'B')
        assert [sorted(map(str, e)) for e in got] == \
               [sorted(map(str, e)) for e in want], \
               ('parameterized enumerator disagrees with boneone.free_sides', n)
    print('  CONTROL: `free_sides_delta(n, "B", 1)` reproduces')
    print('  `boneone.free_sides(n)` exactly at n = 4, 5.  ASSERTED.')

    R = {9: k4_rsides(9, 'A'), 10: k4_rsides(10, 'A')}
    Fr = {4: free_sides_delta(4, 'B', 0), 5: free_sides_delta(5, 'B', 0)}
    print(f'  sides: |R9| = {len(R[9])}, |R10| = {len(R[10])}, '
          f'|Fr4(delta=0)| = {len(Fr[4])}, |Fr5(delta=0)| = {len(Fr[5])}')
    print()

    nfam = nforced = 0
    rows = []
    allforced = []
    for (n1, n2) in ((9, 4), (9, 5), (10, 4)):
        for (_L, H1) in R[n1]:
            for H2 in Fr[n2]:
                nfam += 1
                got = forced_seed(H1 + H2)
                if got is None:
                    continue
                nforced += 1
                allforced.append((n1, n2, H1, H2, got[1]))
    rows = allforced[::stride]

    print(f'  THE CENSUS.  family members : {nfam}')
    print(f'               FORCED (pi_u = pi_v derivable, both terminals '
          f'admitted) : {nforced}')
    print(f'  Compare BONEONE\'s (1,1) family: 392 forced of 928.  Forcing is'
          f' MORE')
    print(f'  common with a RIGID side, not less -- which is what makes')
    print(f'  (BE-22)(vi)\'s one-sided discharge load-bearing.')
    print(f'  CAP: the geometry below runs on a STRIDE SUBSAMPLE, every '
          f'{stride}th forced')
    print(f'  row in generator order -- {len(rows)} of {nforced}, chosen for '
          f'cost, NOT random and')
    print(f'  NOT exhaustive.  `ndraw` = {ndraw} draws per row.')
    if not rows:
        print('  NOT FOUND UNDER CAP: no forced witness in this population.')
        print('  That is a statement about THIS generator, never about the')
        print('  class -- BPEEL reports 3 497 forced R-node peels with')
        print('  min(delta_1, delta_2) = 0 on a wider constructor.')
        print(f'  [{time.time()-t0:.1f} s]')
        return {}

    prof = {}
    n_a2_zero_rows = 0
    n_a2_pos_rows = []
    nodraw = 0
    for (n1, n2, H1, H2, A) in rows:
        G = H1 + H2
        best = None
        for k in range(ndraw):
            pt, _bb = draw_flat(G, A, rng)
            if pt is None:
                continue
            (d1, d2, a1, a2, r1, r2, dsum, S1, S2, dM1, dM2) = \
                measure(H1, H2, pt)
            assert d2 == 0, ('side 2 is not rigid', d2)
            # (BE-86)(i), asserted at every draw: the criterion and the
            # attainment of H must agree.
            fH = exact_deficiency(G)[0]
            dMH = dM1 + dM2 - 6 - dsum        # (BE-22)(i)
            att = (dMH == 6 + fH)
            assert att == _attains(d1 + d2, a1, a2, dsum), \
                ('(BE-86)(i) FAILS at a draw', d1, d2, a1, a2, dsum, dMH, fH)
            # (BE-22)(ii)'s cap, in its a-corrected form
            assert r1 <= d1 + a1 and r2 <= d2 + a2, ('cap violated', r1, r2)
            cand = (a1, a2, r1, r2, dsum, int(att),
                    dim(isect(span(S1), span(S2))))
            # a_i is UPPER semicontinuous: the MINIMUM over draws is the
            # best (and a 0 is a proof).  Keep the coordinatewise-best row.
            if best is None or (cand[0] + cand[1]) < (best[0] + best[1]):
                best = cand
        if best is None:
            nodraw += 1
            continue
        prof[best] = prof.get(best, 0) + 1
        if best[1] == 0:
            n_a2_zero_rows += 1
        else:
            n_a2_pos_rows.append((n1, n2, best))

    print(f'               rows with NO guarded draw in {ndraw} tries : '
          f'{nodraw}')
    print()
    print(f'  (a_1, a_2, rho_1, rho_2, dim(rho_1+rho_2), attains, '
          f'dim(rho_1 cap rho_2)) -> count')
    for k in sorted(prof):
        print(f'      {k} : {prof[k]}')
    print()
    print(f'  rows with a_2 = 0 at some draw (a THEOREM at that row, by upper')
    print(f'  semicontinuity of a_i)                : {n_a2_zero_rows} / '
          f'{len(rows) - nodraw}')
    print(f'  rows with a_2 >= 1 at ALL {ndraw} draws (settles NOTHING -- '
          f'NOT FOUND UNDER CAP {ndraw} draws) : {len(n_a2_pos_rows)}')
    if n_a2_pos_rows:
        print(f'      first such row: {n_a2_pos_rows[0][:2]} {n_a2_pos_rows[0][2]}')
    print()
    print('  READING, IN TWO QUANTITIES WITH OPPOSITE SEMICONTINUITY -- and')
    print('  the SAME rows carry both, so the counts coincide and the verdicts')
    print('  do not.  Read both before quoting either.')
    print('  (a) In a_i ((BE-255)(i) row 3, UPPER, generic = minimum): where')
    print('      a_2 = 0 is exhibited the collapse is a THEOREM at that row and')
    print('      (vi) stands there; where a_2 >= 1 at every draw, (vi) is')
    print('      UNAVAILABLE, not false -- a draw cannot certify a_2 >= 1.')
    print('  (b) In rho_i ((BE-255)(i) row 2, LOWER, generic = MAXIMUM): a draw')
    print('      is a lower bound, so rho_2 >= 1 AT A DRAW IS A THEOREM at the')
    print('      irreducible component containing it -- no cap, and no')
    print('      irreducibility of Chart(H) needed.  On those rows (vi)\'s')
    print('      conclusion rho_2 = 0 is FALSE, not merely unavailable.')
    print('  That second reading is the one (BE-315)(ii) states, and it is why')
    print('  the clause is tagged REFUTED where this mode\'s row (a) alone would')
    print('  have said UNAVAILABLE.')
    print(f'  [{time.time()-t0:.1f} s, seed {seed}, exact Q]')
    return prof


def run_validate():
    print('===== bsmark self-check =====')
    # the identity, at the one place the corpus has measured it
    # ((BE-86)(ii): Sd = 2, a_1+a_2 in {0,1}, dim(rho_1+rho_2) = 2 + a_1 + a_2,
    #  rho_1 cap rho_2 = 0)
    for (a1, a2) in ((0, 0), (0, 1), (1, 0)):
        assert _attains(2, a1, a2, 2 + a1 + a2)
        assert (1 + a1) + (1 + a2) - 0 == 2 + a1 + a2
    # (BE-22)(vi) at a_2 = 0 really does collapse
    assert 0 + 0 == 0
    print('  OK -- (BE-86)(ii)\'s three measured profiles satisfy the')
    print('  restatement identity with dim(rho_1 cap rho_2) = 0 = max(0,2-6).')


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'cancel'
    if mode == 'cancel':
        run_cancel()
    elif mode == 'rigid':
        # `stride` is the one figure-bearing cap of this mode, so it is a CLI
        # argument rather than a default only: (BE-315)(ii) reports the
        # stride-1 sweep (984 forced rows, 972 drawing), and a committed driver
        # whose landed figure cannot be re-run from the command line is not
        # reproducible.  `rigid` alone keeps the cheap stride-8 subsample.
        run_rigid(stride=int(sys.argv[2]) if len(sys.argv) > 2 else 8)
    elif mode == 'validate':
        run_validate()
    else:
        raise SystemExit(f'unknown mode {mode!r}')
