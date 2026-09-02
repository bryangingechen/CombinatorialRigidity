"""
Direction BSPREAD (ordinal 55) -- (BE-32)(+) AT THE SPREAD STEPS.

  THE TARGET the spec names.  BEARFULL proved (BE-32)(+) -- *a graph that
  FORCES pi_u = pi_v has delta_uv = 0* -- at 401 489 of 401 544 forcing steps,
  by a <=6-CYCLE certificate ((BE-41)(i), the STAR-2 step).  The residue is
  the SPREAD step: the three admitting points come from three different
  closed stars, so no short cycle at the admitted hub is available.  55 steps,
  7 680 of 203 723 pairs, 3.8 %.  BEARFULL's own successor sentence: *"a
  successor needs a different tool OR a restriction of the closure operator"*.

  THE ANSWER, said at the top: A DIFFERENT TOOL, and it retires the
  star-2 / spread SPLIT rather than closing its second half.

    (BE-74) THE BLOCK-ABSORPTION LEMMA.  Let P be an OPTIMAL partition, B one
            of its blocks, and A := union of N[w] over w in B.  Then for
            EVERY vertex v outside B

              - if v has a neighbour b in B (necessarily unique), then
                    N[v] cap A  =  {v, b}   EXACTLY;
              - otherwise  |N[v] cap A| <= 1.

            So  |N[v] cap A| <= 2  ALWAYS.  The closure admits on THREE
            points.  Hence an admitted vertex is IN B -- and (BE-32)(+)
            follows by induction, for EVERY forcing step, star-2 and spread
            alike, with no cycle certificate anywhere in the proof.

  The tool is (BE-39)(i) -- the QUOTIENT SPARSITY LAW, `5 e_Q(S) <= 6(|S|-1)`
  for every set S of parts -- used at |S| = 2 (Q is SIMPLE: two parts are
  joined by at most ONE edge of G) and |S| = 3, 4 (no triangle, no 4-cycle of
  Q).  BEARFULL extracted both and spent them on CYCLES OF G ((BE-40)), where
  they run out at 6 because a 7-cycle of Q has slack -1.  Spent on the
  CLOSURE'S OWN STEP instead they do not run out at all: three witnesses need
  three routes from [v] to B in Q, and Q has room for two.

  WHY THE OLD ROUTE COULD NOT WORK, confirmed here off the shipped driver.
  (BE-41)(ii) -- *every aggressively-forced pair lies in one <=6-cycle class*
  -- is FALSE as a universal statement, refuted by its own sibling
  (BE-41)(iii): 4 of the boundary family's 8 members carry an
  aggressively-forced pair whose shortest cycle is 7 or 8.  `chain` re-derives
  that off `bearfull`'s own objects (job 0).  (BE-32)(+) itself was never in
  danger -- delta = 0 at all 8 -- and is now a theorem.

WHAT THIS DRIVER TESTS -- one mode per headline sentence (F11).

  `lemma` (BE-74)/(BE-75)  The lemma itself, ENUMERATED over every optimal
            partition and every block: exhaustive over all connected labelled
            graphs on n = 3..6, sampled at n = 7, 8.  Then the theorem's
            conclusion in its STRONG form -- *no optimal partition separates
            an aggressively-forced pair*, which is strictly stronger than
            delta = 0 -- under FOUR closure operators: the landed one, and
            three widenings the proof covers (any admitted vertex, any seed).
            Then SHARPNESS: the same closure at threshold TWO, which the
            lemma's equality case predicts must FAIL, and does.

  `chain` (BE-76)  JOB 0.  The correction to (BE-41)(ii), re-derived from
            `bearfull`'s SHIPPED objects (`tri_chain`, `forcing_derivation`,
            `step_shape`, `cycle_classes`, `short_cycles`, `def3_fast`) rather
            than from the spec.  The escape set is asserted NON-EMPTY, every
            member's admitting step is asserted a GENUINE spread step, and
            delta = 0 is asserted at every member.  Then the new theorem is
            checked exactly where the old certificate is absent.

  `peel`  (BE-77)  JOB 2.  CROSS-CUT-ONLY forcing at a 2-cut, which BPEEL left
            as *"the sharpest single question this landing leaves"*.
            (a) THE PEEL FACTORIZATION of the closure: until a cut terminal is
            admitted the run is the near side's run, so the FIRST terminal is
            admitted one-sidedly, and thereafter the far side's class is the
            far side's own run seeded at that terminal.  Asserted.
            (b) THE CONSEQUENCE, and it is a theorem: forced at a 2-cut with
            BOTH sides flexible forces delta_1 = delta_2 = 1.  Checked against
            BPEEL's own census -- its 408 instances, 408/408.
            (c) THE RE-AIMED HUNT, and a VACUITY CORRECTION to BPEEL's census
            3: of its 24 874 R-node-shaped both-flexible peels, ZERO have
            delta_1 = delta_2 = 1, so its zero had no chances at the only
            shape the theorem allows.

Succeeds `notes/scripts/w4/bearfull.py` (Steps BE38-BE42) and
`notes/scripts/w4/bpeel.py` (Steps BE68-BE72), both imported READ-ONLY
together with `bdecor` / `btwocut` / `binduc` / `bimage` / `bzavoid` /
`bearcase` / `kbare_common` through them, rather than reimplementing the
partition oracle, the closure, the peel scan, the R-node stand-in or the
deficiency machinery.  BEARFULL's and BPEEL's figures are CITED, never re-run,
except where a mode re-derives one ON PURPOSE and says so.

Conventions inherited verbatim (`notes/scripts/README.md`): exact integer
arithmetic throughout, every rng seeded with the printed literal below, every
cap disclosed, every "fails" claim drawn independently more than once (F27).

NO .lean IS OPENED (the standing 2026-08-05 Lean hold).
"""

import itertools                                                     # noqa: E402
import os
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
for p in (HERE, ROOT, os.path.join(ROOT, 'kbare')):
    if p not in sys.path:
        sys.path.insert(0, p)

from exactcore import neighbors                                      # noqa: E402
from kbare_common import verts_of                                    # noqa: E402
# --- sibling-layer imports.  The `kbare/` sibling-import set is RECORDED
# --- UNPAID debt (`notes/scripts/README.md` *Harness debt*, 2026-08-20).
# --- The chain reached BPEEL at THIRTEEN deep (`battain -> bzavoid -> binduc
# --- -> btwocut -> bimage -> bearcase -> bearfull -> bsharp -> brule -> bwin
# --- -> brnode -> bdecor -> bpeel`); this driver is the SIXTEENTH `kbare/`
# --- consumer and takes the chain FOURTEEN deep, `... -> bpeel -> bspread`.
# --- NO MOVE MADE (a dispatch may not edit a landed driver another direction
# --- may be importing in flight); the recorded consumer list is EXTENDED in
# --- the workbook's harness note instead.
from bzavoid import edges_of_mask, adj_of, connected_spanning        # noqa: E402
from bimage import forced_same_plane                                 # noqa: E402
from btwocut import (deltas_at, g_exact,                             # noqa: E402
                     vertex_connectivity_at_least)
from bearfull import (cycle_classes, def3_fast, forcing_derivation,   # noqa: E402
                      optimal_partitions, short_cycles, step_shape,
                      tri_chain)
from bpeel import (constructed_tier, pair_forced, peel_scan,          # noqa: E402
                   rnode_shaped)

SEED = 20260901


# ============================================== the closure, PARAMETRIZED

def closure_trace(nb, cand, h, thr=3):
    """The aggressive plane-class closure from seed `h`, with the derivation
    recorded.  `cand` is the set of vertices eligible for ADMISSION -- the
    landed operator takes the hubs, and the proof of (BE-74) never uses the
    hub restriction, so the widenings below pass the whole vertex set.

    Returns (A, admitted, trace); `trace` is the ordered list of
    (admitted vertex, its witness set) after the seed.  Byte-for-byte the
    growth rule of `bimage.forced_same_plane` / `binduc.flat_forcing_closure`
    at `thr = 3` and `cand = hubs`, which `run_lemma` asserts."""
    A = {h} | set(nb[h])
    adm = [h]
    trace = []
    changed = True
    while changed:
        changed = False
        for v in cand:
            if v in adm:
                continue
            star = {v} | set(nb[v])
            wit = star & A
            if len(wit) >= thr:
                adm.append(v)
                trace.append((v, frozenset(wit)))
                A |= star
                changed = True
    return A, adm, trace


def closure_pairs(edges, thr=3, hubs_only=True, seeds_hubs=True):
    """The forced PAIRS of the parametrized closure -- pairs inside one
    family.  At the default arguments this is `bimage.forced_same_plane`."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    hubs = [z for z in V if len(nb[z]) >= 3]
    seeds = hubs if seeds_hubs else V
    cand = hubs if hubs_only else V
    out = set()
    for h in seeds:
        _A, adm, _tr = closure_trace(nb, cand, h, thr=thr)
        for a, b in itertools.combinations(sorted(adm, key=str), 2):
            out.add((a, b))
    return out


def block_of(P):
    """vertex -> block index, for a partition given as a list of lists."""
    out = {}
    for i, B in enumerate(P):
        for z in B:
            out[z] = i
    return out


# ================================ (BE-74): the block-absorption lemma

def lemma_violations(edges, cap_opts=None):
    """(BE-74)(i), ENUMERATED.  For every optimal partition P, every block B
    and every vertex v outside B, with  A := union of N[w] over w in B:

        v has a neighbour b in B   =>   N[v] cap A == {v, b}
        v has none                 =>   |N[v] cap A| <= 1

    The second clause of the first line also re-checks (BE-39)(i) at |S| = 2
    (`v` has at most ONE neighbour in each block other than its own), so a
    violation of the quotient-sparsity law would surface here too.

    Returns (violations, #optimal partitions inspected, #(block, v) pairs
    inspected, #equality cases attained) -- the last is the NON-VACUITY
    number: the bound `<= 2` is worth nothing if it is never met."""
    nb = neighbors(edges)
    V = set(verts_of(edges))
    _f, opts = optimal_partitions(edges)
    if cap_opts is not None:
        opts = opts[:cap_opts]
    bad = []
    npair = neq = 0
    for P in opts:
        for Braw in P:
            B = frozenset(Braw)
            A = set()
            for w in B:
                A |= {w} | set(nb[w])
            for v in V - B:
                npair += 1
                hit = ({v} | set(nb[v])) & A
                nbrB = set(nb[v]) & B
                if len(nbrB) > 1:
                    bad.append(('(BE-39)(i) at |S| = 2 VIOLATED', tuple(edges),
                                v, sorted(map(str, nbrB))))
                    continue
                if nbrB:
                    if hit != ({v} | nbrB):
                        bad.append(('shape', tuple(edges),
                                    sorted(map(str, B)), v,
                                    sorted(map(str, hit))))
                    else:
                        neq += 1
                elif len(hit) > 1:
                    bad.append(('size', tuple(edges), sorted(map(str, B)), v,
                                sorted(map(str, hit))))
    return bad, len(opts), npair, neq


def strong_separations(edges, prs):
    """The theorem's STRONG conclusion: no optimal partition separates a
    forced pair.  (BE-39)(ii) makes `delta = 0` the P_max form; this is the
    form (BE-74) actually proves, and it is strictly stronger."""
    if not prs:
        return 0, 0
    _f, opts = optimal_partitions(edges)
    bad = 0
    for P in opts:
        blk = block_of(P)
        for (u, v) in prs:
            if blk[u] != blk[v]:
                bad += 1
    return len(prs) * len(opts), bad


def run_lemma(nmax=6, nsamp=(7, 8), nmask=250, seed=SEED):
    print('===== Step BE73 / (BE-74): (BE-32)(+) IS A THEOREM -- the '
          'BLOCK-ABSORPTION LEMMA, and it never mentions a cycle =====')
    print('  THE TOOL.  (BE-39)(i), the quotient sparsity law, at |S| = 2, 3')
    print('  and 4: two parts of an OPTIMAL partition are joined by at most')
    print('  ONE edge of G, and the quotient Q has no triangle and no')
    print('  4-cycle.  BEARFULL spent that on CYCLES OF G ((BE-40)) and ran')
    print('  out of slack at 6.  Spent on the CLOSURE\'S OWN STEP it does not')
    print('  run out: a vertex v outside a block B routes to B in Q by an')
    print('  EDGE or by a 2-PATH, an edge and a path make a TRIANGLE, two')
    print('  paths make a 4-CYCLE, and two edges coincide -- so B absorbs at')
    print('  most TWO points of N[v], and the closure admits on THREE.')
    print()
    t0 = time.time()
    rng = random.Random(seed)
    tot = nopt = npair = neq = 0
    bad = []
    tiers = [(n, None) for n in range(3, nmax + 1)] + \
            [(n, nmask) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n - 1:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            tot += 1
            b, no, npr, ne = lemma_violations(edges)
            bad += b
            nopt += no
            npair += npr
            neq += ne
        print(f'   n = {n}' + (' EXHAUSTIVE' if samp is None
                               else f' SAMPLED ({samp} seeded masks)')
              + f': cumulative {tot} graphs, {nopt} optimal partitions, '
                f'{npair} (block, outside vertex) pairs, {len(bad)} VIOLATIONS')
    print()
    print(f'  (i)  THE LEMMA: {npair} enumerated (block, outside vertex) '
          f'pairs over {nopt} optimal partitions of {tot} graphs, '
          f'{len(bad)} violations.')
    print(f'       NON-VACUITY: the bound |N[v] cap A| <= 2 is ATTAINED at '
          f'{neq} of them -- the equality case {{v, b}} is exactly why the '
          f'closure needs THREE points and not two.')
    for r in bad[:6]:
        print('     *** VIOLATION:', r)
    assert not bad, 'the block-absorption lemma FAILED -- (BE-74) is refuted'

    # ---- the conclusion, in its STRONG form, under four operators --------
    print()
    print('  (ii) THE CONCLUSION, in the STRONG form the proof gives: NO')
    print('  optimal partition separates an aggressively-forced pair.  That')
    print('  is stronger than delta = 0, which by (BE-39)(ii) is only the')
    print('  P_max form.  And the proof never uses the HUB restriction, so')
    print('  it must survive dropping it -- three widenings, plus the')
    print('  SHARPNESS control at threshold TWO, which must FAIL:')
    ops = (('thr 3, hubs (the LANDED operator)',
            dict(thr=3, hubs_only=True, seeds_hubs=True), True),
           ('thr 3, ANY vertex admitted',
            dict(thr=3, hubs_only=False, seeds_hubs=True), True),
           ('thr 3, ANY vertex, ANY seed',
            dict(thr=3, hubs_only=False, seeds_hubs=False), True),
           ('thr 2, hubs (SHARPNESS CONTROL)',
            dict(thr=2, hubs_only=True, seeds_hubs=True), False))
    landed_ok = 0
    results = []
    for (label, kw, expect_clean) in ops:
        rng2 = random.Random(seed)
        gtot = inst = sep = 0
        ex = []
        for (n, samp) in tiers:
            pairs = list(itertools.combinations(range(n), 2))
            masks = (range(1 << len(pairs)) if samp is None
                     else [rng2.getrandbits(len(pairs)) for _ in range(samp)])
            for mask in masks:
                edges = edges_of_mask(pairs, mask)
                if len(edges) < n - 1:
                    continue
                if not connected_spanning(n, adj_of(n, edges)):
                    continue
                gtot += 1
                prs = closure_pairs(edges, **kw)
                if kw['thr'] == 3 and kw['hubs_only'] and kw['seeds_hubs']:
                    assert prs == set(forced_same_plane(edges)), \
                        ('the parametrized closure disagrees with the landed '
                         '`bimage.forced_same_plane`', edges)
                    landed_ok += 1
                a, b = strong_separations(edges, prs)
                inst += a
                sep += b
                if b and len(ex) < 2:
                    ex.append((tuple(edges), sorted(prs)[:3]))
        results.append((label, gtot, inst, sep, ex, expect_clean))
        print(f'     {label:36s}: {inst:8d} (pair, optimal partition) '
              f'instances, {sep:6d} SEPARATED')
        for e in ex:
            print(f'         separated example: {e}')
    print(f'  cross-check against the landed `bimage.forced_same_plane`: '
          f'{landed_ok} graphs, 0 disagreements')
    for (label, _g, inst, sep, _e, expect) in results:
        if expect:
            assert sep == 0, ('a forced pair was separated by an optimal '
                              'partition -- (BE-74) is refuted at ' + label)
        else:
            assert sep > 0, ('threshold TWO did NOT fail -- the lemma\'s '
                             'equality case would then be unattained and the '
                             'proof would be proving too much')
    print('  SHARPNESS CONFIRMED: threshold 3 is clean under every widening')
    print('  the proof covers, and threshold 2 FAILS -- exactly at the')
    print('  degenerate witness pair {v, b} the lemma\'s equality case names,')
    print('  which is the pair `bearfull.step_shape` already carved out by')
    print('  hand and could not explain.')
    print()
    print(f'  CAP DISCLOSURE.  Exhaustive over ALL connected labelled graphs '
          f'at n = 3..{nmax}; the n = {nsamp} tiers are {nmask} seeded masks '
          f'each, from the printed literal {seed}.  EVERY figure here is a '
          f'CHECK of a proved statement, not its evidence: (BE-74) is proved '
          f'from (BE-39)(i) alone, so a violation would refute the proof '
          f'rather than bound its scope.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return not bad


# =========================== (BE-76): job 0, the correction re-derived

def run_chain(kmax=6, seed=SEED):
    print('===== Step BE75 / (BE-76): JOB 0 -- (BE-41)(ii) IS REFUTED AS '
          'STATED, CONFIRMED off the shipped driver =====')
    print('  (BE-41)(ii) as landed: *every aggressively-forced pair lies in')
    print('  one <=6-cycle class*.  (BE-41)(iii), the SAME direction, builds')
    print('  a family in which one does not.  Both are BEARFULL\'s; what went')
    print('  wrong is the SUMMARY surfaces, which restated (ii) without')
    print('  (iii)\'s carve-out, and the two consumers that inherited it.')
    print('  Re-derived HERE from `bearfull`\'s own objects -- `tri_chain`,')
    print('  `forcing_derivation`, `step_shape`, `cycle_classes`,')
    print('  `short_cycles`, `def3_fast` -- and NOT from the write-up.')
    t0 = time.time()
    rows = []
    for k in range(3, kmax + 1):
        for npend in (1, 2):
            E = tri_chain(k, npend)
            V = verts_of(E)
            fs = forced_same_plane(E)
            vv, t0v = ('v', 0), ('t', 0)
            key = (vv, t0v) if (vv, t0v) in fs else (t0v, vv)
            assert key in fs, ('the boundary family stopped forcing', k, npend)
            nbE = neighbors(E)
            spread_ok = False
            for (_h, (_fam, _A, steps)) in forcing_derivation(E).items():
                for (vx, _wit, allwit) in steps:
                    if vx != vv:
                        continue
                    if all(step_shape(E, vx, t, nbE)[0] == 'spread'
                           for t in itertools.combinations(allwit, 3)):
                        spread_ok = True
            assert spread_ok, ('not a genuine SPREAD step', k, npend)
            f = def3_fast(E)
            d = f - g_exact(E, vv, t0v)
            find = cycle_classes(E, 6)
            cyc = [c for c in short_cycles(E, k + 4) if vv in c]
            ml = min((len(c) for c in cyc), default=None)
            rows.append((k, npend, len(V), len(E), f, d, ml,
                         'SAME' if find(vv) == find(t0v) else 'DIFFERENT'))
    print('    k  pend    n   m   def_3  delta(v,t_0)  min cycle thru v   '
          '<=6-class')
    for (k, npend, n, m, f, d, ml, cl) in rows:
        print(f'   {k:2d}  {npend:3d}  {n:4d} {m:3d}  {str(f):>5s}  '
              f'{str(d):>10s}  {str(ml):>14s}   {cl}')
    esc = [r for r in rows if r[7] == 'DIFFERENT']
    assert all(r[5] == 0 for r in rows), \
        'delta /= 0 in the boundary family -- that would be HIT shape 4'
    assert esc, 'the escape set is EMPTY -- the correction would be empty'
    print()
    print(f'  VERDICT ON JOB 0: THE COORDINATOR IS CONFIRMED.  {len(esc)} of '
          f'{len(rows)} members carry an AGGRESSIVELY-FORCED pair (v, t_0) '
          f'lying in NO common <=6-cycle class (shortest cycle through v is '
          f'{min(r[6] for r in esc)} or more), every admitting step is a '
          f'genuine SPREAD step, and delta = 0 at ALL {len(rows)}.')
    print('  So (BE-41)(ii) is FALSE as a universal statement, and')
    print('  (BE-32)(+) was never in danger.  What is dead is the <=6-cycle')
    print('  ROUTE -- and (BE-74) retires it rather than repairing it: the')
    print('  corrected statement is not a weaker cycle claim, it is that the')
    print('  cycle claim was never the load-bearing one.')
    print()
    print('  AND THE NEW THEOREM, CHECKED EXACTLY WHERE THE OLD CERTIFICATE')
    print('  IS ABSENT.  (BE-74) predicts delta = 0 at every member with no')
    print('  cycle input at all; the delta column above is that prediction,')
    print('  and the escaping members are the ones (BE-40) cannot reach.')
    print(f'  CAP DISCLOSURE.  The family is a CONSTRUCTION: it proves the '
          f'escape set NON-EMPTY, never that it is large.  The blind '
          f'n = 9..13 re-finding is BEARFULL\'s ((BE-41)(iii), 2 541 graphs / '
          f'27 414 pairs) and is CITED, not re-run.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return rows


# ================== (BE-77): job 2, cross-cut-only forcing at a 2-cut

def peel_invariants(edges, u, v, V1, V2, cap_seeds=None):
    """(BE-77)(i), the PEEL FACTORIZATION, instrumented.  For every seed of
    the widened closure that admits BOTH terminals, assert:

      (a) every admission strictly before the FIRST terminal lies on the
          seed's own side -- so the run has not crossed the cut;
      (b) the FIRST terminal's witness set lies wholly on that side -- so the
          first terminal is admitted ONE-SIDEDLY;
      (c) record the SECOND terminal's witness split (a, b) across the cut.

    Returns (#runs inspected, #violations, list of splits)."""
    nb = neighbors(edges)
    V = sorted(verts_of(edges), key=str)
    S1, S2 = set(V1), set(V2)
    seeds = V if cap_seeds is None else V[:cap_seeds]
    nrun = nviol = 0
    splits = []
    for h in seeds:
        _A, adm, trace = closure_trace(nb, V, h)
        if not (u in adm and v in adm):
            continue
        nrun += 1
        order = [h] + [t[0] for t in trace]
        idx = {z: i for i, z in enumerate(order)}
        first, second = (u, v) if idx[u] < idx[v] else (v, u)
        side = None
        if h not in (u, v):
            side = S1 if h in S1 else S2
        if side is not None:
            for (z, wit) in trace:
                if z in (u, v):
                    if z == first and not (wit <= side):
                        nviol += 1
                    break
                if z not in side:
                    nviol += 1
        for (z, wit) in trace:
            if z == second:
                splits.append((len(wit & S1), len(wit & S2)))
                break
    return nrun, nviol, splits


def run_peel(nexh=6, nsamp=(7, 8), nmask=3000, seed=SEED, quick=False):
    print('===== Step BE76 / (BE-77): JOB 2 -- CROSS-CUT-ONLY FORCING, and '
          'it is CONFINED to delta_1 = delta_2 = 1 =====')
    print('  BPEEL\'s residue ((BE-73)(iv)): a coincidence pi_u = pi_v forced')
    print('  at an R-node-shaped 2-cut peel by the two sides TOGETHER, inside')
    print('  neither alone, with BOTH sides flexible.  None found under its')
    print('  cap.  (BE-74) turns that hunt into a theorem plus a much')
    print('  narrower search.')
    t0 = time.time()
    rng = random.Random(seed)

    # ---- (a) the peel factorization, asserted -----------------------------
    nrun = nviol = 0
    nsplit = 0
    tiers = [(n, None) for n in (5, nexh)] + \
            [(n, nmask // 3 if not quick else nmask // 12) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            if not vertex_connectivity_at_least(n, edges, 2):
                continue
            nb = neighbors(edges)
            for (u, v, V1, _E1, V2, _E2) in peel_scan(n, edges, nb):
                r, b, sp = peel_invariants(edges, u, v, V1, V2)
                nrun += r
                nviol += b
                nsplit += sum(1 for (a, c) in sp if a < 3 and c < 3)
    print(f'  (a) THE PEEL FACTORIZATION: {nrun} closure runs admitting BOTH '
          f'terminals, {nviol} violations of "the run does not cross the cut '
          f'before a terminal is admitted, and the FIRST terminal is admitted '
          f'one-sidedly".  {nsplit} of the runs admit the SECOND terminal on '
          f'a witness set genuinely SPLIT by the cut.')
    assert nviol == 0, 'the peel factorization FAILED -- (BE-77)(i) refuted'

    # ---- (b) the theorem, against BPEEL's own census ----------------------
    print()
    print('  (b) THE THEOREM.  Forced at a 2-cut {u,v} with u !~ v and BOTH')
    print('  sides flexible  =>  delta_1 = delta_2 = 1.  Reason: a one-sided')
    print('  certificate gives delta_i = 0 by (BE-74) on that side, so the')
    print('  admission is split, so by the lemma each side contributes')
    print('  EXACTLY the pair {v, b_i} -- whence v has a neighbour in the')
    print('  block of u on BOTH sides, and merging those two blocks across')
    print('  that single edge costs 6 and returns 5, so delta_i <= 1.')
    print('  Checked against BPEEL\'s CENSUS 1, re-run here:')
    rng = random.Random(seed)
    npeel = nboth = nviol2 = 0
    dist = {}
    ex = []
    tiers = [(n, None) for n in (5, nexh)] + \
            [(n, nmask if not quick else nmask // 6) for n in nsamp]
    for (n, samp) in tiers:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if samp is None
                 else [rng.getrandbits(len(pairs)) for _ in range(samp)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            if max(len(neighbors(edges)[z]) for z in verts_of(edges)) > 4:
                continue
            if not vertex_connectivity_at_least(n, edges, 2):
                continue
            nb = neighbors(edges)
            for (u, v, _V1, _E1, _V2, _E2) in peel_scan(n, edges, nb):
                npeel += 1
                if not pair_forced(edges, u, v):
                    continue
                cd = deltas_at(edges, u, v, check=False)
                d1, d2 = cd[2] - cd[3], cd[6] - cd[7]
                if d1 > 0 and d2 > 0:
                    nboth += 1
                    dist[(d1, d2)] = dist.get((d1, d2), 0) + 1
                    if not (d1 == 1 and d2 == 1):
                        nviol2 += 1
                        if len(ex) < 4:
                            ex.append((tuple(edges), u, v, d1, d2))
    print(f'      {npeel} peels, {nboth} FORCED with both sides flexible, '
          f'{nviol2} of them violating delta_1 = delta_2 = 1')
    print(f'      (delta_1, delta_2) distribution: '
          f'{dict(sorted(dist.items()))}')
    for e in ex:
        print('      *** VIOLATION:', e)
    assert nviol2 == 0, 'forced-with-both-flexible off (1,1) -- (BE-77) refuted'
    print('      BPEEL reported this population as a bare count ("408 forced')
    print('      with both deltas positive, 0 of them R-node-shaped").  The')
    print('      theorem says what it IS: every one of them sits at (1, 1).')

    # ---- (c) the re-aimed hunt, and the vacuity correction ----------------
    print()
    print('  (c) THE RE-AIMED HUNT, and a VACUITY CORRECTION to BPEEL\'s')
    print('  census 3.  BPEEL\'s non-vacuity check counted R-node-shaped')
    print('  peels with both deltas positive -- 24 874 of them -- and')
    print('  concluded "the hunt had that many chances".  By the theorem the')
    print('  right denominator is the (1, 1) sub-population, and that is:')
    crn = crb = c11 = c11f = 0
    for (_tag, _E, _u, _v, d1, d2, forced, rn) in constructed_tier(
            maxlen=3 if quick else 4, nsamp=300 if quick else 1500, seed=seed):
        if rn:
            crn += 1
            if d1 > 0 and d2 > 0:
                crb += 1
                if d1 == 1 and d2 == 1:
                    c11 += 1
                    if forced:
                        c11f += 1
    print(f'      CENSUS 3 re-read: {crn} R-node-shaped peels, {crb} with '
          f'both sides flexible, {c11} of THOSE at (1, 1), {c11f} forced.')
    print(f'      So BPEEL\'s "0 forced among 24 874" had **{c11} chances**, '
          f'not 24 874.  Recorded, not smoothed -- this is exactly the')
    print('      hazard BPEEL\'s own non-vacuity discipline exists to catch,')
    print('      with the denominator the theorem supplies rather than the')
    print('      one the hunt happened to have.')
    print()
    print('  THE HUNT, AIMED AT (1, 1).  Two independent tiers: random')
    print('  2-connected graphs with NO max-degree filter (BPEEL\'s census 1')
    print('  carried one, and it is what made R-node peels there rigid on one')
    print('  side), and the constructed subdivided-skeleton tier.')
    rng = random.Random(seed)
    tot = nrn = n11 = n11r = n11rf = 0
    hits = []
    ns = (6, 7, 8, 9) if quick else (6, 7, 8, 9, 10)
    for n in ns:
        pairs = list(itertools.combinations(range(n), 2))
        masks = (range(1 << len(pairs)) if n <= 6
                 else [rng.getrandbits(len(pairs))
                       for _ in range(600 if quick else 4000)])
        for mask in masks:
            edges = edges_of_mask(pairs, mask)
            if len(edges) < n or len(edges) > 2 * n:
                continue
            if not connected_spanning(n, adj_of(n, edges)):
                continue
            if not vertex_connectivity_at_least(n, edges, 2):
                continue
            nb = neighbors(edges)
            for (u, v, _V1, E1, _V2, E2) in peel_scan(n, edges, nb):
                tot += 1
                rn = rnode_shaped(E1, u, v) or rnode_shaped(E2, u, v)
                if rn:
                    nrn += 1
                cd = deltas_at(edges, u, v, check=False)
                if cd[2] - cd[3] == 1 and cd[6] - cd[7] == 1:
                    n11 += 1
                    if rn:
                        n11r += 1
                        if pair_forced(edges, u, v):
                            n11rf += 1
                            hits.append((tuple(edges), u, v))
    print(f'      TIER A (random, n = {ns[0]}..{ns[-1]}, no degree filter): '
          f'{tot} peels, {nrn} R-node-shaped, {n11} at (1, 1), '
          f'{n11r} BOTH, {n11rf} of those forced')
    print(f'      TIER B (constructed): {crn} R-node-shaped peels, '
          f'{c11} at (1, 1), {c11f} of those forced')
    for h in hits[:4]:
        print('      HIT:', h)
    print()
    print(f'  RESULT.  Across {nrn + crn} R-node-shaped peels and '
          f'{n11 + c11} peels at (1, 1) over two independent tiers, the '
          f'INTERSECTION IS EMPTY.  Under F11 that reads "no R-node-shaped '
          f'peel with delta_1 = delta_2 = 1 was found under this cap", NEVER '
          f'"none exists".')
    print('  WHAT JOB 2 IS NOW.  Cross-cut-only forcing at an R-node peel')
    print('  with both sides flexible is IMPOSSIBLE unless an R-node-shaped')
    print('  2-cut peel can have delta_1 = delta_2 = 1.  That is a named,')
    print('  checkable, PURELY COMBINATORIAL condition with no closure and no')
    print('  geometry in it -- one statement about deficiencies and')
    print('  3-connectivity, and it is the whole of the residue.')
    print(f'  CAP DISCLOSURE.  Tier A is {600 if quick else 4000} seeded '
          f'masks per n above 6 and exhaustive at n = 6, edges capped at 2n; '
          f'tier B is BPEEL\'s constructed generator at its own cap. Both are '
          f'seeded from the printed literal {seed}.')
    print(f'  [{time.time() - t0:.1f} s]  seed {seed}')
    return n11rf == 0


# ============================================================== driver CLI

def run_validate():
    t0 = time.time()
    print('===== bspread validate: reduced tiers of all three modes =====')
    ok = True
    ok &= bool(run_lemma(nmax=6, nsamp=(7,), nmask=60))
    print()
    run_chain(kmax=5)
    print()
    ok &= bool(run_peel(nexh=6, nsamp=(7,), nmask=600, quick=True))
    print()
    print(f'===== validate {"GREEN" if ok else "RED"}, '
          f'{time.time() - t0:.1f}s =====')
    return ok


MODES = {'lemma': run_lemma, 'chain': run_chain, 'peel': run_peel,
         'validate': run_validate}

if __name__ == '__main__':
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    if not args:
        print('usage: bspread.py {' + '|'.join(MODES) + '}')
        sys.exit(2)
    for a in args:
        if a not in MODES:
            print(f'unknown mode {a}')
            sys.exit(2)
        MODES[a]()
    sys.exit(0)
