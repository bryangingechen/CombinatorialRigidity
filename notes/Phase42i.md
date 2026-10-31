# Phase 42i — PD-STEPS: open ears with three interior bodies in dimensions four to six (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 and the fourth and last of PD-STEPS. Forward
mode, the Lean under `/coordinate-phase`: the four red nodes of `pencil-d.tex`'s `-short-three`, the
theorem at `4 ≤ d ≤ 6`. The pre-build recon has landed: 42h's factoring cannot take the three-body
condition (a kernel-checked counterexample), so a variant is pinned, with the four signatures and a
build order of five or six commits (*Lemma checklist*). Next (*Hand-off*): land the variant, whose
spike is complete.

## Current state

**Next: land the variant factoring** (*Hand-off*), the first of five or six builds. The recon spiked
everything under `lake lean` in the gitignored `scratch/42i/`, on HEAD `64f0fe75`:
- **Complete, no `sorry`:** `HinsFails.lean` (134 lines, Question 1's counterexample);
  `Variant.lean` (577 lines, most of them copied from the landed Lean: the variant, its bridge
  and the landed factoring as its corollary); `Helpers.lean` (132 lines) and `StarsFamily.lean`
  (116 lines; the four-body helpers and stars-four's family one index down, landed proofs
  unchanged).
- **Signatures and composition:** `Three.lean` (705 lines, `Variant.lean` plus the four
  signatures, each `sorry`, and the theorem built on the variant). Its one residual is the
  insertion hypothesis at the base data (*Lemma checklist*, the theorem).
No Lean in the tree yet. The chapter is the lemma index (forward mode).

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
  (R-9 to R-15 open, R-13 to R-15 planned at the recon; R-7 and R-8 aligned).

## Lemma checklist

Build order, leaf first: the variant, stars-three, planes-meet, glued-ends (one or two commits),
the theorem. Import order: `Grade/Stars` → `Grade/StarsThree`; `Grade/ConditionLinear` and
`MainComponent/Flat` → `Grade/PlanesMeet`; `Grade/Short` and `Grade/PlanesMeet` →
`Grade/GluedEnds`; `Grade/StarsThree` and `Grade/GluedEnds` → `Grade/ShortThree`. Each new file
goes in the root import file. Every statement below type-checks in `scratch/42i/Three.lean`.

- [x] **Pre-build recon** (this commit): verdict in *Decisions made*, signatures here.
- [ ] **The variant factoring** (`Grade/Short.lean`; not a node: the theorem's factoring, tracked
  here). Copy `scratch/42i/Variant.lean`, which is complete:
  - `joinMotions H c` (`⨅` over links of `comap (proj u − proj w) (K ∙ c u ∨ c w)`),
    `mem_joinMotions`, `joinRelScrews H c a b := (joinMotions H c).map (proj b − proj a)`: the
    section's motions and `ρ`, in `⋀²`. Instances: on a graph with no links `joinRelScrews = ⊤`
    for `a ≠ b` (`S = Pi.single b ω`); on the one link `a b` it is `K ∙ (c a ∨ c b)`.
  - `map_relScrews_ofNormals_eq_joinRelScrews` (`hends` for `G`, `H`'s links `G`'s): the relative
    screws of `⟨H, ofNormals G ends c⟩`, pulled back by `complementScrew`, are `joinRelScrews`.
  - `Graph.exists_earBase_splitOff_grade`, generalized in place, its one caller the factoring:
    `+ {Rz : (α × Fin 2 → K) → MvPolynomial (α × Fin m) K}`
    `(hRz : ∀ q, G″.IsAdmissiblePicture q → ∃ z ∈ G″.liftingSpaceGrade q m, eval z (Rz q) ≠ 0)`;
    it also returns `zs` (after `z₁`) with `zs ∈ L_{G″}(q)^m`, `eval zs (Rz q) ≠ 0`,
    `∀ t ∈ V₁, ∀ i, z₁ (t, i) = zs (t, i)`, and `la`, `lb` the planes of `zs` on `G″`'s closed
    neighbourhoods of `a`, `b`. `z*` avoids `Rz q*` by two fibre intersections.
  - `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`: the landed factoring with
    `{Pq} (hPq : Pq ≠ 0) {Rz} hRz` before `hins`, and `hins` replaced by
    `∀ q z zs la lb, eval q Pq ≠ 0 → G″.IsAdmissiblePicture q → zs ∈ L_{G″}(q)^m →`
    `eval zs (Rz q) ≠ 0 → (∀ t ∈ V₁, ∀ i, z (t, i) = zs (t, i)) → (planes la at a) →`
    `(planes lb at b) → ∃ Q, …` (the landed body, with
    `ρ := joinRelScrews (G.induce V₁) (pencilConfigPointGrade q z) a b` for the quantified `ρ`).
  - `Graph.X0AttainsGrade.of_openEar_splitOff`, statement unchanged, becomes a corollary
    (`Pq = 1`, `Rz = fun _ => 1`, ten lines). `of_openEar_four` is untouched.
- [ ] `lem:pencil-d-stars-three` → `exists_mvPolynomial_starsThree`, new `Grade/StarsThree.lean`.
  At `V = Fin (k + 2) → K`, `d = k + 1`, every `k`:
  `(ρ) {Sa Sb} (hSa : finrank Sa = 3) (hSb : finrank Sb = 3) (hdκ : k + finrank (Sa ⊓ Sb) ≤ 5)`
  `{pa pb} (hpa : pa ∈ Sa) (hpb : pb ∈ Sb) : ∃ f : MvPolynomial (Fin 2 × Fin (k + 2)) K, …`,
  the conclusion `exists_mvPolynomial_starsFour`'s at two interior points (`Y : Fin 2 → V`, the
  three joins of `pathVertex pa Y pb`). The proof is stars-four's on forms: the dual kernel curve
  for stars-four's family one index down (generalize the seven declarations from `starsPoint` to
  `exists_mvPolynomial_repr_starsFamily` from `Fin (n + 3)` to `Fin (n + 2)` points, checked in
  `StarsFamily.lean`; stars-four's body then names `n + 1`, not checked), `ν` a coordinate of
  `Y 0 ∨ Y 1`. Move `Y 0` along `pa`, then any `u ∈ Sa`, and `Y 1` along `pb`, then any `w ∈ Sb`.
  Each time `φ₁` kills `W`, hence the stars, so `u` (`w`) joins the radical of `φ₀`. Then
  `finrank_add_two_le_of_forall_ιMulti_eq_zero` on `Sa ⊔ Sb`, of dimension `6 − κ`, contradicts
  `hdκ`. Derived in prose, not compiled. It does not use the statement's `κ ≤ 1`, `p_a`, `p_b`
  independent or `d ≥ 4`, so the Lean drops them (*Blockers*; `notes/Cleanup42.md` R-13).
- [ ] `lem:pencil-d-planes-meet` → `Graph.liftingPlanesDiff` and
  `Graph.exists_mvPolynomial_planesMeet`, new `Grade/PlanesMeet.lean`, every `m`:
  `liftingPlanesDiff G q a b := (G.liftingPlanes q).map (proj b − proj a)` (instance: no links,
  `a ≠ b`: all of `K³`). Hypotheses: the ear `a − y 0 − y 1 − b` in the landed form
  (`hcover hinj hyV₁ ha hb hab hpath hsep`, `y : Fin 2 → α`, `e : Fin 3 → β`) and
  `hq : G.IsAdmissiblePicture q`. Conclusion: `∃ R : MvPolynomial (α × Fin m) K,`
  `(∃ z ∈ G.liftingSpaceGrade q m, eval z R ≠ 0) ∧ ∀ z ∈ …, eval z R ≠ 0 → ∀ la lb,`
  `(planes la at a) → (planes lb at b) →`
  `finrank (range (gradeSigma la) ⊓ range (gradeSigma lb)) =`
  `3 − min m (finrank ((G.induce V₁).liftingPlanesDiff q a b))`. The planes are taken as the
  base data give them (R-15).
- [ ] `lem:pencil-d-glued-ends` → `Graph.exists_mvPolynomial_gluedEnds`, new
  `Grade/GluedEnds.lean`, every `m`:
  `(hS : G.Simple) (h3 : ∀ v ∈ V(G), 3 ≤ (G.closedNbhd v).ncard) (ha : a ∈ V(G)) (hb : b ∈ V(G))`
  `(hab : Disjoint (G.closedNbhd a) (G.closedNbhd b)) : ∃ g, g ≠ 0 ∧ ∀ q, eval q g ≠ 0 →`
  `finrank (G.liftingPlanesDiff q a b) ≤ 2 → ∀ (m) (z : α × Fin m → K),`
  `finrank (joinRelScrews G (pencilConfigPointGrade q z) a b) ≤`
  `finrank (G.liftingPlanesDiff q a b)`.
  `g` comes before `m` and `z`. `h3` is the Jackson–Jordán Lean's form of "degree at least two",
  and `Disjoint` packs `a ≠ b`, not adjacent, no common neighbour. Not spiked; the largest build.
- [ ] `thm:pencil-d-open-ear-three` → `Graph.X0AttainsGrade.of_openEar_three`, new
  `Grade/ShortThree.lean`: `of_openEar_four`'s hypotheses at `x : Fin 3 → α`, `e : Fin 4 → β`,
  plus `(hm : 2 ≤ m) (hm4 : m ≤ 4)`, both used. The spike builds it from the variant
  (`k = 2`, `splitOff_ear_succAbove (k := 0)`, the relinked edge discharged), with
  `Pq = (X (a, 0) − X (b, 0)) * g` (`g` glued-ends' polynomial for `G[V₁]`, or `1` when the closed
  neighbourhoods meet) and `Rz` planes-meet's `R` for `G″` (`choose!`). Its residual, which the
  kernel checked, is the variant's `hins` at those data:
  - (r ≤ 2) `Q = X (inl (x 0, 0)) − X (inl (x 2, 0))`. If both stars lie in `W`, then
    `finrank ρ ≥ 2m ≥ 4`. A common member `t` of the closed neighbourhoods of `a` and `b` in
    `G[V₁]` would put `ρ` in `span (b_a ∨ b_t, b_t ∨ b_b)` (a short new helper, from the
    motions). Otherwise glued-ends gives `finrank ρ ≤ r ≤ 2`.
  - (r = 3) `κ = 3 − min(m, 3)` by `hRz`'s conclusion (`G″[V₁] = G[V₁]`); stars-three at
    `Sa = range (gradeSigma la)` and `pa ∈ Sa` (`pencilConfigPointGrade_eq_gradeSigma_iff`); then
    `exists_mvPolynomial_earDataGrade_of_smul`.
  - The insertion, `of_openEar_four`'s tail at three bodies, needs `starsCond_of_smul` and
    `span_joins_succAbove_two` one index down: generalize them in place (checked in `Helpers.lean`,
    which also checks that the four-body call shapes still unify).
  The first coordinate of `q_a − q_b` in `Pq` drops if stars-three drops `p_a`, `p_b` independent.
- [ ] **Close** 42i, an intermediate sub-phase close that completes PD-STEPS
  (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- **Nothing blocks the builds.** The recon's questions are settled (*Decisions made*, the
  verdict). One question goes to the PI, and nothing waits on it:
  - **Stars-three's statement.** Its forms proof (*Lemma checklist*) uses only
    `d + κ ≤ 6`, `p_a ∈ Π_a`, `p_b ∈ Π_b` and `dim Π_a = dim Π_b = 3`, not `κ ≤ 1`, `p_a`, `p_b`
    independent or `d ≥ 4`. The chapter's proof needs `κ ≤ 1` only for its four-points step, which
    the Lean replaces by a coordinate of `y₁ ∨ y₃` as stars-four's does. The Lean drops the three,
    which proves a stronger lemma. The statement stays (no edit to a node's statement). Whether
    it and the proof follow the Lean, as stars-four's did at the PI's word, goes to the PI or the
    cleanup (`notes/Cleanup42.md` R-13). This is derived in prose; the build compiles it.
- **Risks the builds carry:** glued-ends is new planar mathematics on Phase 40's carrier, and may
  take two commits. That includes the contraction `G.map (collapseTo a {a, b})` with
  `def₂ = deficiencyMerged` (`partitionDef_map`), `Z⁰(q)` bounded by rank openness
  (`exists_mvPolynomial_le_finrank_span_of_repr`), and the `3|V(G)ᶜ|` the lifting planes count off
  `V(G)` (`Graph.finrank_liftingPlanes`). Planes-meet reads `la i` as the inverse of the
  admissible three-point matrix applied to `z`. Neither is spiked.

## Hand-off / next phase

The next concrete commit is **the variant factoring in `Grade/Short.lean`**: copy
`scratch/42i/Variant.lean`'s `joinMotions`, `mem_joinMotions`, `joinRelScrews`,
`map_relScrews_ofNormals_eq_joinRelScrews`, the generalized `Graph.exists_earBase_splitOff_grade`
(in place, unprimed) and `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`. Then replace
`of_openEar_splitOff`'s body by the spike's corollary proof. It is one commit and a whole spike
(`lake lean` clean but for long lines). It flips no node, and the chapter's prose waits for the
theorem's build. Then the builds in the *Lemma checklist*'s order, each adding its node's
`\lean{}` and `\leanok`: stars-three (one commit), planes-meet (one), glued-ends (one or two),
the theorem (one).
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure;
  the recon added R-13 to R-15 (planned, `open`).
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42h are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42h.md` *Hand-off* lists 42h's). The variant's commit edits `Grade/Short.lean`,
  which is no deferral's target. Stars-three's commit, generalizing stars-four's family in place,
  edits `Grade/Stars.lean`, the target of `starGrade_smul`, which moves there with it.
- **After 42i:** PD-STEPS is complete. PD-COVERAGE (`-chains`, `-coverage`, 4 red nodes),
  PD-REDUCTION and PD-HEAD open at the PI's word (design doc §3).

## Decisions made during this phase

- **The recon's verdict (2026-10-31, design pass).** 42h's factoring cannot carry three bodies.
  Kernel-checked (`scratch/42i/HinsFails.lean`, `hins_three_false`, axioms `propext`,
  `Classical.choice`, `Quot.sound`): at `k = 2`, `m ≥ 2`, whenever `G″` has an admissible picture
  (which `h₂` supplies), `hins` fails at `z = 0`, `la = lb = 0`, `ρ = ker ⋀²π` (`π` the heights,
  codimension `binom(m, 2) ≥ 1`). Every ear point but `x₂` has zero heights, so every join lies in
  `ρ`. The variant takes `hins` only at the first stage's base data, for `G[V₁]`'s `joinRelScrews`.
  It is a generalization whose old form is a ten-line corollary, which leaves `of_openEar_four` as
  it is (an added sibling would copy 200 lines).
- **PI, 2026-10-31 (42i's open):** the PI answered "All 4 nodes as written (Recommended)", whose
  option read: "The theorem at 4 ≤ d ≤ 6, as the chapter states it. An Opus open commit, a
  pre-build recon that spikes the four against the carrier on 42h's Lean, then roughly 3–6 builds.
  Closes PD-STEPS." The question as put, the other options and a note on them: design doc §1.
- **The question's wording, checked** (not the PI's text; design doc §1): stars-three's
  environment is 98 lines (2682–2779 at `59ceecee`), not about 430; the range 2683–3111 ran on to
  glued-ends' label, through 42h's green ear-data nodes and four-body theorem. "Leaving only the
  insertion condition" holds at the type level; whether that condition can be met at three bodies
  was the recon's first question (answered above: it cannot).
- **Consistency read at the open:** all four PASS. Each was read in full against the nodes it
  cites: every proof routes through the argument its statement claims, and no wording needs a
  repair. With every `\uses` list parsed whole, the 30 dependencies outside the four (13
  definitions, 15 lemmas, 2 theorems) are green, proofs too, none superseded. Within the four only
  the theorem uses the other three; outside the section only `thm:pencil-d-coverage` uses the
  theorem; no `-short-four` node uses or cites any of the four.
