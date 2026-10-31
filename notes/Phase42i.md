# Phase 42i — PD-STEPS: open ears with three interior bodies in dimensions four to six (work log)

**Status:** ✓ closed 2026-10-31 (opened the same day at the PI's word, "All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 and the last of PD-STEPS, which it
completes; Phase 42 stays in progress with no sub-phase open. Forward mode, the Lean under
`/coordinate-phase`: the four `-short-three` nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-short` are green, the theorem at `4 ≤ d ≤ 6`, in nine commits with the open, the
recon, a fixup and the close. At the PI's word stars-three's statement and proof follow its Lean;
the other route differences wait for the cleanup after Phase 42 (`notes/Cleanup42.md`). Next
(*Hand-off*): PD-COVERAGE's open goes to the PI.

## Current state

**Closed.** The fourth and last sub-phase of PD-STEPS: Phase 40's short-ear step in `Pᵈ` at three
interior bodies, SHORT-CORE's `k = 3` step at `d = 4` to `6`, on a variant of 42h's factoring.
File map, one line each:
- `Grade/Short.lean` (42h's) gained the variant: the motions and relative screws on joins
  (`joinMotions`, `joinRelScrews`, `map_relScrews_ofNormals_eq_joinRelScrews`,
  `joinRelScrews_le_span_of_mem_closedNbhd`) and `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`,
  of which `of_openEar_splitOff` is a corollary; `starsCond_of_smul` and `span_joins_succAbove_two`
  start one index down.
- `Grade/Stars.lean` (42h's) gained stars-three's helpers (the first-order step, the pivot,
  `not_starGrade_sup_le_of_finrank_le_two`) and `starGrade_smul`, moved home; `starsFamily` and its
  chain start one index down.
- `Grade/StarsThree.lean` (imports `Grade.Stars`): `exists_mvPolynomial_starsThree`
  (`lem:pencil-d-stars-three`).
- `Grade/PlanesMeet.lean` (imports `Grade.ConditionLinear`, `Grade.Stars`, `MainComponent.Cut`,
  `MainComponent.Flat`): `Graph.liftingPlanesDiff`, `Graph.exists_mvPolynomial_planesMeet`
  (`lem:pencil-d-planes-meet`); helpers the fixed inverse, the intersection's dimension, the ear
  extension.
- `Grade/GluedEnds.lean` (imports `Grade.Short`, `Grade.PlanesMeet`, `MainComponent.Bridge`,
  `MainComponent.ContractCurve`): `Graph.exists_mvPolynomial_gluedEnds` (`lem:pencil-d-glued-ends`);
  helpers `⋀²π` (`gradePi`), `Z⁰` and its polynomial, the two-body contraction and the partition
  lemmas, some with homes elsewhere (*Hand-off*).
- `Grade/ShortThree.lean` (imports `Grade.GluedEnds`, `Grade.StarsThree`):
  `Graph.X0AttainsGrade.of_openEar_three` (`thm:pencil-d-open-ear-three`), with the third condition
  `exists_mvPolynomial_earDataGrade_starsCond_three` and the insertion
  `exists_insertion_earDataGrade_three`.

`#print axioms` at the close (`lake lean`, a scratch file) on the 5 pinned names and 66 helpers
(every declaration of the four new files, and those 42i added to or changed in `Grade/Short.lean`
and `Grade/Stars.lean`): `[propext, Classical.choice, Quot.sound]` on every pinned name and on all
but seven helpers, which use part of it (`gradePlanarProj`, `Graph.mem_closedNbhd_comm` and 42h's
index and chain lemmas); no `sorryAx`. The close re-read the section's four nodes end to end
against the landed statements: every hypothesis and conclusion matches its pin, the Lean stronger
only in dropping planes-meet's infinite `K` and the `d ≥ 3` of glued-ends and planes-meet; no
sentence was false (*Decisions*).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the four nodes as the chapter states them, the
  theorem at `4 ≤ d ≤ 6`, though the coverage uses it only at `d = 4`
  (`thm:pencil-d-chain-or-core`).
- **Encoding** as 42h (`notes/Phase42h.md` *Architectural choices*): `m = d − 2` heights at grade
  `k = m + 1`, so `4 ≤ d ≤ 6` is `2 ≤ m ≤ 4`; annihilators are read on the forms on `⋀²`, no
  exterior power past `⋀²`.

## Lemma checklist

All four nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. PD-COVERAGE opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open, and PD-STEPS is complete (25 nodes, all green).
The next step is **putting PD-COVERAGE's open to the PI** (design doc §3), no letter minted until
it opens (answered at 42j's open: all four as written, design doc §1; `notes/Phase42j.md`): the
four red nodes of `pencil-d.tex`'s `sec:pencil-d-chains`
(`lem:pencil-d-chain-count`, COUNT-C, and `thm:pencil-d-chain-or-core`) and
`sec:pencil-d-coverage` (`thm:pencil-d-coverage`, `lem:pencil-d-distinct-statement`); then
PD-REDUCTION (8 nodes) and PD-HEAD (21), each at the PI's word. What 42i hands on:
- **The three-body step** `Graph.X0AttainsGrade.of_openEar_three`, at `2 ≤ m ≤ 4`; the coverage
  uses it at `m = 2` (`d = 4`), beside 42h's `of_openEar_four` and 42g's long ear at every `m`.
- **What the coverage's Lean needs besides** is design doc §3, *Handed on from PD-RECON*,
  PD-COVERAGE (COUNT-C, and reductions that return their bridge, cut-vertex or cycle data).
- **The standing rule** (design doc §3): its recon and builds add a row to `notes/Cleanup42.md` §2
  where their Lean departs from the chapter's proof; R-9 to R-12 and R-14 to R-16 are open, R-7,
  R-8 and R-13 aligned.

**Deferred, where it lands** (design doc §3, *Deferred to them from PD-STEPS (42i)*; FRICTION's
`[open]` entries), each with the next commit that edits the target file: glued-ends'
`Graph.mem_closedNbhd_comm` to `Pencil/Motive.lean`, its six two-body contraction lemmas to
`MainComponent/ContractCurve.lean`, `Graph.liftingPlanesDiff_eq_top_of_notMem` to
`Grade/PlanesMeet.lean`, and `gradePlanarProj`, a third copy of the picture projection, into
PD-CARRIER's fold. At a cleanup round, `exists_insertion_earDataGrade_three`, which repeats
`of_openEar_four`'s inline tail at three bodies, becomes one insertion lemma both steps call. The
deferrals of 42b–42h are unchanged, but for `starGrade_smul`, moved home with stars-three.

## Decisions made during this phase

- **PI, 2026-10-31 (42i, stars-three):** "Restate to the Lean (Recommended)": stars-three's
  statement and proof follow its Lean, in the theorem's build. Verbatim, with the question and the
  other options: design doc §1.
- **The theorem's build (fifth):** the third condition and the insertion are lemmas of
  `Grade/ShortThree.lean` (inline, the step ran out of heartbeats); `Pq = g`, as the first
  coordinate of `q_a − q_b` served only stars-three's dropped independence; the chapter's route
  for `r ≤ 2` is kept (R-14 open; the PI's answer covered stars-three only).
- **Glued-ends (fourth build):** the chapter's route, `def₂(G')` for the merged deficiency (R-16).
- **Stars-three's helpers live in `Grade/Stars.lean`** (second build), with `starGrade_smul`.
- **The recon's verdict (design pass):** 42h's factoring cannot carry three bodies (kernel-checked,
  `scratch/42i/HinsFails.lean`: `hins` fails at `z = 0`, `la = lb = 0`, `ρ = ker ⋀²π`). The variant
  takes `hins` only at the first stage's base data, for `G[V₁]`'s `joinRelScrews`; the old
  factoring is its corollary, so `of_openEar_four` is unchanged.
- **PI, 2026-10-31 (42i's open):** the PI answered "All 4 nodes as written (Recommended)", whose
  option read: "The theorem at 4 ≤ d ≤ 6, as the chapter states it. An Opus open commit, a
  pre-build recon that spikes the four against the carrier on 42h's Lean, then roughly 3–6 builds.
  Closes PD-STEPS." The question as put, the other options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1): stars-three's environment
  is 98 lines, not about 430; "leaving only the insertion condition" held only as a type-check.
- **Consistency read at the open:** all four PASS, their 30 outside dependencies green.
- **The close:** the re-read changed no statement and found no false sentence; no `main_results`
  row (an intermediate close adds none, design doc §3, PD-HEAD).
