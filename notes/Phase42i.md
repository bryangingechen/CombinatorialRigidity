# Phase 42i — PD-STEPS: open ears with three interior bodies in dimensions four to six (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("All 4 nodes as written (Recommended)",
design doc §1), a sub-phase of Phase 42 and the fourth and last of PD-STEPS. Forward mode, the
Lean under `/coordinate-phase`: the four nodes of `pencil-d.tex`'s `-short-three`, the theorem at
`4 ≤ d ≤ 6`. The recon pinned a variant of 42h's factoring (*Decisions made*); the variant,
stars-three, planes-meet, glued-ends and the theorem have landed: all 4 nodes green, and
stars-three's chapter text restated to its Lean at the PI's word. Next (*Hand-off*): the close.

## Current state

**Landed, fifth build: the theorem.** `Graph.X0AttainsGrade.of_openEar_three` (new
`Grade/ShortThree.lean`, in the root import file) pins `thm:pencil-d-open-ear-three`, green, its
statement as pinned. It is the variant at the base data with `Pq = g` (glued-ends' polynomial for
`G[V₁]`, or `1`) and `Rz` planes-meet's, its insertion hypothesis discharged by two lemmas of the
file, `exists_mvPolynomial_earDataGrade_starsCond_three` (the third condition: `dim ρ ≤ 2` when
`r ≤ 2`, by `not_starGrade_sup_le_of_finrank_le_two` in `Grade/Stars.lean`, or stars-three when
`r = 3`) and `exists_insertion_earDataGrade_three` (the insertion). `Grade/Short.lean` gained
`joinRelScrews_le_span_of_mem_closedNbhd`, and `starsCond_of_smul` and `span_joins_succAbove_two`
now start one index down (`of_openEar_four` unchanged). Stars-three's statement and proof follow
its Lean (R-13 aligned); the theorem's proof keeps the chapter's route (R-14 open). `lake build` is
warning-clean, `lake lint` passes, `#print axioms` is `[propext, Classical.choice, Quot.sound]`.
**Landed before it:** glued-ends (`Grade/GluedEnds.lean`, R-16), planes-meet
(`Grade/PlanesMeet.lean`, R-15), stars-three (`Grade/StarsThree.lean`) and the variant factoring
(`Grade/Short.lean`). The recon's spikes are in the gitignored `scratch/42i/`. The chapter is the
lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the four nodes as the chapter states them, the
  theorem at `4 ≤ d ≤ 6`, though the coverage uses it only at `d = 4`
  (`thm:pencil-d-chain-or-core`). Their close closes PD-STEPS.
- **Encoding** as 42h (`notes/Phase42h.md` *Architectural choices*): `m = d − 2` heights at grade
  `k = m + 1`, so `4 ≤ d ≤ 6` is `2 ≤ m ≤ 4`; annihilators are read on the forms on `⋀²` (42h's
  recon, `fe5baf0f`), no exterior power past `⋀²`.
- **What 42h hands on** (`notes/Phase42h.md` *Hand-off*, each type-checked at its close): the
  factoring `Graph.X0AttainsGrade.of_openEar_splitOff` at `k = 2`, with `splitOff_ear_succAbove`
  at `k = 0`, leaving `G″`'s link and `hins`, which cannot be met at three bodies (*Decisions
  made*, the recon's verdict; the variant is in *Lemma checklist*); the dual route for
  stars-three's last step, `finrank_add_two_le_of_forall_ιMulti_eq_zero` (two-stars (3) as
  landed), with the kernel curve on forms `exists_mvPolynomial_dual_kernel_curve`.
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof, in the same commit
  (R-9 to R-12 and R-14 to R-16 open, R-14 to R-16 landed with their nodes; R-7, R-8 and R-13
  aligned).

## Lemma checklist

Build order as landed: the variant, stars-three, planes-meet, glued-ends, the theorem; each new file
is in the root import file. The signatures are the Lean's, and the chapter is the lemma index.

- [x] **Pre-build recon**: verdict in *Decisions made*.
- [x] **The variant factoring** (`Grade/Short.lean`; not a node): `joinMotions`, `joinRelScrews`,
  `map_relScrews_ofNormals_eq_joinRelScrews`, `Graph.exists_earBase_splitOff_grade` with a height
  polynomial `Rz`, and `Graph.X0AttainsGrade.of_openEar_splitOff_of_base` (the insertion
  hypothesis at the base data only), of which `of_openEar_splitOff` is a ten-line corollary.
- [x] `lem:pencil-d-stars-three` → `exists_mvPolynomial_starsThree` (`Grade/StarsThree.lean`), on
  forms as stars-four's; its chapter statement and proof restated to it in the theorem's build, at
  the PI's word (R-13 aligned).
- [x] `lem:pencil-d-planes-meet` → `Graph.exists_mvPolynomial_planesMeet` and
  `Graph.liftingPlanesDiff` (`Grade/PlanesMeet.lean`, R-15).
- [x] `lem:pencil-d-glued-ends` → `Graph.exists_mvPolynomial_gluedEnds` (`Grade/GluedEnds.lean`,
  R-16).
- [x] `thm:pencil-d-open-ear-three` → `Graph.X0AttainsGrade.of_openEar_three`
  (`Grade/ShortThree.lean`): `of_openEar_four`'s hypotheses at `x : Fin 3 → α`, `e : Fin 4 → β`,
  plus `(hm : 2 ≤ m) (hm4 : m ≤ 4)`, both used. The variant at `k = 2` with `Pq = g` (the spike's
  `(X (a, 0) − X (b, 0)) * g` without its first factor, at the PI's word: nothing else uses it) and
  `Rz` planes-meet's. The third condition is `exists_mvPolynomial_earDataGrade_starsCond_three`
  (`r ≤ 2`: `dim ρ ≤ 2` by `joinRelScrews_le_span_of_mem_closedNbhd` or glued-ends, then
  `not_starGrade_sup_le_of_finrank_le_two`; `r = 3`: stars-three), the insertion
  `exists_insertion_earDataGrade_three`, with `starsCond_of_smul` and `span_joins_succAbove_two`
  generalized one index down. The chapter's first stage drops the first coordinate of `q_a − q_b`;
  its route stays (R-14 open).
- [ ] **Close** 42i, an intermediate sub-phase close that completes PD-STEPS
  (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- **Nothing blocks the close.** All four nodes are green; the PI's answer on stars-three
  (design doc §1, *42i, stars-three*) is carried out (R-13 aligned).

## Hand-off / next phase

The next concrete commit is **the close** of 42i (`PHASE-BOUNDARIES.md` *When this commit closes
a phase*), an intermediate sub-phase close that completes PD-STEPS: all four `-short-three` nodes
are green. It flips 42i's ROADMAP row and §42 prose, compresses this note, writes 42i's entry in
`notes/BlueprintExposition.md` (stars-three's proof rerouted to forms at the PI's word), and runs
the chapter re-read.

- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure;
  42i's are R-13 (aligned) and R-14 to R-16 (open, each landed with its node).
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42h are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42h.md` *Hand-off* lists 42h's), except `starGrade_smul`, which moved to
  `Grade/Stars.lean` with stars-three. Planes-meet's and glued-ends' commits add files, which are
  no deferral's target; a lemma a build adds to an existing file takes along that file's debts.
  Glued-ends files new home debts (FRICTION): its contraction and closed-neighbourhood helpers and
  `liftingPlanesDiff_eq_top_of_notMem`, and `gradePlanarProj`, a third copy of the picture
  projection. The theorem's build adds no home debt; its insertion lemma repeats
  `of_openEar_four`'s inline tail at three bodies, a cleanup-round fold (FRICTION).
- **After 42i:** PD-STEPS is complete. PD-COVERAGE (`-chains`, `-coverage`, 4 red nodes),
  PD-REDUCTION and PD-HEAD open at the PI's word (design doc §3).

## Decisions made during this phase

- **PI, 2026-10-31 (42i, stars-three):** "Restate to the Lean (Recommended)": stars-three's
  statement and proof follow its Lean, in the theorem's build. Verbatim, with the question and the
  other options: design doc §1.
- **The theorem's build (2026-10-31, fifth):** composed inline as `of_openEar_four` is, the step
  ran out of heartbeats, so the third condition and the insertion are lemmas of
  `Grade/ShortThree.lean`. The coordinator's hypothesis held: the first coordinate of `q_a − q_b`
  served only stars-three's dropped independence, so `Pq = g`. The theorem's proof keeps the
  chapter's component and path route (R-14 open; the PI's answer covered stars-three only).
- **Glued-ends' route (fourth build):** the chapter's, with `def₂(G')` for the merged deficiency
  and `g` Jackson–Jordán's polynomial times `Z⁰`'s kernel-dimension polynomial (R-16).
- **Stars-three's helpers live in `Grade/Stars.lean`** (second build), their home, as does
  `starGrade_smul`; `Grade/StarsThree.lean` holds the node's lemma only.
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
