# Phase 42h — PD-STEPS: open ears with four or more interior bodies in every dimension (work log)

**Status:** ✓ closed 2026-10-31 (opened the same day at the PI's word, "k ≥ 4 half first
(Recommended)", design doc §1), a sub-phase of Phase 42, which stays in progress with no sub-phase
open. Forward mode, the Lean under `/coordinate-phase`: the eight `-short-four` nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-short` are green, their Lean at every `m`
(every `d ≥ 2`), in eight commits with the open, the recon and the close. At the PI's word
two-stars is stated on forms and stars-four's proof follows its Lean; the other route differences
wait for the cleanup after Phase 42 (`notes/Cleanup42.md`). Next (*Hand-off*): `-short-three`'s
open goes to the PI.

## Current state

**Closed.** The third sub-phase of PD-STEPS: Phase 40's short-ear step in `Pᵈ` at four or more
interior bodies, SHORT-CORE's every-`ρ` step (S35) with S20's factoring and the tools both halves
of `-short` use. File map, one line each:
- `Grade/Stars.lean` (imports `Grade.Polygon`, `MainComponent.Lines`, `MainComponent.Cut`):
  `lem:pencil-d-two-stars` (`starGrade` and six lemmas, parts (2) and (3) on the forms on `⋀²`),
  `exists_insertion_of_starGrade_sup` (`lem:pencil-d-insertion`),
  `exists_mvPolynomial_kernel_curve` (`lem:pencil-d-kernel-curve`) and
  `exists_mvPolynomial_starsFour` (`lem:pencil-d-stars-four`); helpers the insertion gain, rank
  is open, the first-order step, the dual kernel curve, `starsFamily` and
  `eq_zero_of_starsFour_firstOrder`, with eight `normalsJoin` and `pathVertex` lemmas whose homes
  are elsewhere (*Hand-off*).
- `Grade/EarData.lean` (imports `Grade.Stars`, `Grade.Chain`, `Grade.ConditionLinear`,
  `MainComponent.EarGen`): `earPictureGrade`, `earHeightGrade`, `earConfigGrade`
  (`def:pencil-d-ear-data`), the nine pins of `lem:pencil-d-ear-data` and the two of
  `lem:pencil-d-ear-data-open`.
- `Grade/Short.lean` (imports `Grade.Cut`, `Grade.EarData`, `Grade.Stars`, `MainComponent.Short`):
  `Graph.X0AttainsGrade.of_openEar_four` (`thm:pencil-d-open-ear-four`); helpers
  `splitOff_ear_succAbove`, `Graph.exists_earBase_splitOff_grade`,
  `Graph.X0AttainsGrade.of_openEar_splitOff` (the factoring through `G″`, with `complementScrew`),
  `starsCond_of_smul`, `span_joins_succAbove_two` and nine small lemmas.

`#print axioms` at the close (`lake lean`, a scratch file) on the 25 pinned names and the 47
helpers of the three files: `[propext, Classical.choice, Quot.sound]` on every pinned name, and on
all but eleven helpers, which use part of it (path-sequence and index lemmas, `starsPoint`,
`starsDir`, `starsEnds`); no `sorryAx`. The close re-read the section's eight nodes end to end
against the landed statements: every hypothesis and conclusion matches its pin, the Lean stronger
only in dropping the nodes' `d ≥ 3`; one sentence of the section's overview was false and is
repaired (*Decisions*).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eight nodes above.
- **Naming the halves** (the open's choice): `-short` stays the section's code; its halves are
  `-short-four` (these eight) and `-short-three` (four nodes), stable codes (design doc §3).
- **Encoding** as 42b–42g: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`,
  `def_d` is `G.deficiency (m + 2)`, attaining is `Graph.X0AttainsGrade K m`. `σ_a`, `σ_b` are
  `gradeSigma la`, `gradeSigma lb`; `Π_a`, `Π_b` their ranges. Joins live in
  `⋀[K]^2 (Fin (k + 2) → K)` (`normalsJoin`); the relative screws in `ScrewSpace K k`.
- **The annihilator** (the recon's choice): `U°` is `U.dualAnnihilator` in
  `Module.Dual K (⋀[K]^2 V)`, the chapter's perfect pairing identifying `⋀^{d−1}` with the forms
  on `⋀²`; no exterior power past `⋀²`; `star y` is `starGrade y`. The chapter's section defines
  `U°` so too (the PI, *Decisions*).

## Lemma checklist

All eight nodes are green, each pinned in its section with its Lean names; the chapter is the
index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. `-short-three` opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 stays in progress with no sub-phase open. The next step is **putting `-short-three`'s
open to the PI** (design doc §3): the four red nodes of `sec:pencil-d-short` for the open ear with
three interior bodies at `d = 4` to `6` (`lem:pencil-d-stars-three`, `lem:pencil-d-glued-ends`,
`lem:pencil-d-planes-meet`, `thm:pencil-d-open-ear-three`), the last of PD-STEPS, no letter minted
until it opens (answered at 42i's open: all four as written, design doc §1; `notes/Phase42i.md`
*Decisions made*: `hins` below cannot be met at three bodies, so 42i took a variant). What 42h
hands it, each checked against the landed Lean at the close (a scratch type-check):
- **The factoring.** `Graph.X0AttainsGrade.of_openEar_splitOff` keeps the `P³` shape (any
  `v u w e₀`, `G″`'s ear given, `2 ≤ k`). At three interior bodies it applies at `k = 2`, with
  `splitOff_ear_succAbove` at `k = 0` and the four-body theorem's arguments otherwise, leaving
  `G″`'s link `e 1` (discharged as at four) and `hins`, the half's own condition.
- **The dual route.** `lem:pencil-d-stars-three`'s last step is two-stars (3) as landed: with
  `Π_a + Π_b` in the radical of a nonzero form on `⋀²`,
  `finrank_add_two_le_of_forall_ιMulti_eq_zero` gives `dim(Π_a + Π_b) + 2 ≤ d + 1`, so
  `d + κ ≥ 7`. The rest of its proof reads annihilators in `⋀^{d−1}` through the pairing; carrying
  it onto forms is the recon's (the kernel curve on forms is
  `exists_mvPolynomial_dual_kernel_curve`).
- **The standing rule** (design doc §3): its recon and builds add a row to `notes/Cleanup42.md` §2
  where their Lean departs from the chapter's proof; R-9 to R-12 are open, R-7 and R-8 aligned.

**Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries), each with the next
commit that edits the target file. From 42g, unchanged: the four `normalsJoin` lemmas of
`Grade/Polygon.lean` to `PanelLayer.lean` (42c's move) and `pencilConfigPointGrade_ofPoints` to
`Grade/Carrier.lean` (42e's fold). From 42h: `Grade/Stars.lean`'s `normalsJoin_sub_left`,
`normalsJoin_zero_right`, `normalsJoinLin` and `normalsJoin_add_smul_add_smul`, and
`Grade/Short.lean`'s `complementScrew` (beside `panelSupportExtensor`), to `PanelLayer.lean` with
42c's move; the `pathVertex` lemmas, `Stars.lean`'s `pathVertex_add_smul`,
`pathVertex_succ_castSucc`, `pathVertex_eq_of_val_eq` and `pathVertex_zero_single` and
`Short.lean`'s `pathVertex_comp_succAbove_one`, `pathVertex_smul_comp` and `pathVertex_map`, to
`MainComponent/Cut.lean`; `starGrade_smul` to `Grade/Stars.lean`; and the upstream candidates
`coe_succAbove_one` and `coe_succAbove_two`, as one `Fin.val_succAbove` in the mirror
`Mathlib/Data/Fin/Basic.lean`, and `span_range_smul_eq` (a new mirror, at a cleanup round). The
other deferrals of 42b, 42c, 42e and 42f are unchanged: 42h's Lean is three new files.

## Decisions made during this phase

- **PI, 2026-10-31 (42h's open):** the PI answered "k ≥ 4 half first (Recommended)", whose option
  read: "8 nodes, Phase 40's open-ear factoring in Pᵈ at four or more interior bodies. Opus open
  commit, a pre-build recon against the carrier, then roughly 4–8 builds. The three-body case (4
  nodes) stays mapped by section for its own sub-phase, which lets its recon build on the landed
  k ≥ 4 Lean." The question as put, the other options and a note on them: design doc §1.
- **The question's attribution, corrected** (not the PI's text; design doc §1): "SHORT-CORE's hand
  proof, the coverage's only new mathematics" is SHORT-CORE's whole step; 42h carried S35 with
  S20's factoring and the shared tools, and `-short-three` carries `k = 3` at `d = 4` to `6`.
- **Consistency read at the open:** all eight PASS; no `-short-four` node uses a `-short-three`
  one; the 30 dependencies outside the eight are green, proofs too.
- **The pre-build recon (`fe5baf0f`):** the annihilator on forms (above), so stars-four needs no
  `⋀^{d−3}` and no quotient; seven nodes spiked complete, the theorem's composition checked over
  three `P³` transcriptions; every `m`, no `1 ≤ m`; departures R-7 to R-10.
- **PI, 2026-10-31 (42h, after the recon), two-stars:** the PI answered "Restate in forms
  (Recommended)", whose option read: "Edit the node's parts (2) and (3) to what the Lean proves
  (forms on ⋀², part (3) at the degree used), with one sentence keeping the ⋀^{d−1} reading through
  the section's pairing. Lands in the Stars.lean build commit; no extra Lean or commits. The citing
  proofs get matching wording." The question as put, the other option and a note: design doc §1.
- **PI, 2026-10-31 (42h, after the recon), the routes:** the PI answered "Stars-four only
  (Recommended)", whose option read: "Rewrite stars-four's chapter proof to the Lean's shorter forms
  route in the Stars.lean build, which keeps it consistent with a forms-worded two-stars. R-9 and
  R-10 stay in the ledger for the cleanup." The question as put, the other options: design doc §1.
- **The builds** (five commits, the recon's pins token for token): both answers carried out in
  `Grade/Stars.lean` (R-7, R-8 aligned; part (1)'s basis is R-11, open); `Grade/EarData.lean` as
  spiked, the base data's compatibility entering as part (1)'s hypotheses (R-10 open);
  `Grade/Short.lean` leaf-first, the theorem's `hins` discharged by stars-four, ear data (3) and
  the insertion, an order the chapter does not take (R-12 open). Honesty gate: no hypothesis added.
- **The close:** the section's overview said that `W` is everything at general points of the ear,
  where stars-four gives "whenever it contains both stars"; repaired, no statement changed.
  Docstrings read against their statements (`pathVertex_map` takes any function). Home debts filed
  (FRICTION). No `main_results` row: an intermediate close adds none (design doc §3, PD-HEAD).
