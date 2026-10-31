# Phase 42i — PD-STEPS: open ears with three interior bodies in dimensions four to six (work log)

**Status:** in progress, opened 2026-10-31 at the PI's word ("All 4 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 and the fourth and last of PD-STEPS. Forward
mode, the Lean under `/coordinate-phase`: the four red nodes of `pencil-d.tex`'s `-short-three`, the
theorem at `4 ≤ d ≤ 6`. The pre-build recon has landed: 42h's factoring cannot take the three-body
condition (a kernel-checked counterexample), so a variant is pinned, with the four signatures and a
build order of five or six commits (*Lemma checklist*). The variant factoring and stars-three have
landed: 1 of 4 nodes green. Next (*Hand-off*): planes-meet, a new `Grade/PlanesMeet.lean`.

## Current state

**Landed, second build: stars-three.** `exists_mvPolynomial_starsThree` (new `Grade/StarsThree.lean`)
pins `lem:pencil-d-stars-three`, green, its statement unchanged. It takes `ρ`,
`hSa : finrank Sa = 3`, `hSb : finrank Sb = 3`, `hdκ : k + finrank (Sa ⊓ Sb) ≤ 5`, `hpa : pa ∈ Sa`
and `hpb : pb ∈ Sb`: the recon's signature, compiled. Its forms proof uses none of `κ ≤ 1`, `p_a`,
`p_b` independent or `d ≥ 4` (*Blockers*). In `Grade/Stars.lean`: the seven family declarations
(`starsPoint` to `exists_mvPolynomial_repr_starsFamily`) one index down, at `Fin (n + 2)` points,
with stars-four's statement unchanged and its body at `n + 1`; two first-order helpers; and
`starGrade_smul`, moved from `Grade/Short.lean`. `lake build` is warning-clean and `lake lint`
passes. `#print axioms` of the new and changed declarations is `[propext, Classical.choice,
Quot.sound]` or less.
**Landed, first build: the variant factoring** in `Grade/Short.lean` (*Lemma checklist*).
**Next: planes-meet** (*Hand-off*), then glued-ends and the theorem. The recon's spikes, on HEAD
`64f0fe75` under `lake lean`, are in the gitignored `scratch/42i/`: `Three.lean` (the four
signatures and the theorem composed on the variant; its one residual is the insertion hypothesis
at the base data), `Helpers.lean` (the four-body helpers one index down, for the theorem) and
`HinsFails.lean` (the recon's counterexample). `StarsThreeDev.lean` is this build's spike.
The chapter is the lemma index (forward mode).

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
  (R-9 to R-15 open; R-13 landed with stars-three, R-14 and R-15 planned at the recon; R-7 and
  R-8 aligned).

## Lemma checklist

Build order, leaf first: the variant, stars-three, planes-meet, glued-ends (one or two commits),
the theorem. Import order: `Grade/Stars` → `Grade/StarsThree`; `Grade/ConditionLinear` and
`MainComponent/Flat` → `Grade/PlanesMeet`; `Grade/Short` and `Grade/PlanesMeet` →
`Grade/GluedEnds`; `Grade/StarsThree` and `Grade/GluedEnds` → `Grade/ShortThree`. Each new file
goes in the root import file. Every statement below type-checks in `scratch/42i/Three.lean`.

- [x] **Pre-build recon** (this commit): verdict in *Decisions made*, signatures here.
- [x] **The variant factoring** (`Grade/Short.lean`; not a node: the theorem's factoring, tracked
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
- [x] `lem:pencil-d-stars-three` → `exists_mvPolynomial_starsThree`, new `Grade/StarsThree.lean`,
  green. At `V = Fin (k + 2) → K`, `d = k + 1`, every `k`:
  `(ρ) {Sa Sb} (hSa : finrank Sa = 3) (hSb : finrank Sb = 3) (hdκ : k + finrank (Sa ⊓ Sb) ≤ 5)`
  `{pa pb} (hpa : pa ∈ Sa) (hpb : pb ∈ Sb) : ∃ f : MvPolynomial (Fin 2 × Fin (k + 2)) K, …`,
  the conclusion `exists_mvPolynomial_starsFour`'s at two interior points (`Y : Fin 2 → V`, the
  three joins of `pathVertex pa Y pb`). The proof is stars-four's on forms: the dual kernel curve
  for `starsFamily` at `n = 0` (the seven family declarations generalized to `Fin (n + 2)` points;
  stars-four calls them at `n + 1`), `ν` a coordinate of `Y 0 ∨ Y 1`; moving `Y 0` along `pa`, then
  any `u ∈ Sa` (`forall_mem_normalsJoin_eq_zero_of_pivot`), `φ₁` kills `W`, so `u` joins the
  radical of `φ₀` (`forall_normalsJoin_eq_zero_of_firstOrder`), and likewise `Y 1` along `Sb`; then
  `finrank_add_two_le_of_forall_ιMulti_eq_zero` on `Sa ⊔ Sb`, of dimension `6 − κ`, contradicts
  `hdκ`. The statement's `κ ≤ 1`, `p_a`, `p_b` independent and `d ≥ 4` are not taken (*Blockers*;
  `notes/Cleanup42.md` R-13).
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
  - **Stars-three's statement.** Its Lean, landed and green, takes exactly `ρ`,
    `dim Π_a = dim Π_b = 3` (`hSa`, `hSb`), `d + κ ≤ 6` (`hdκ : k + κ ≤ 5`, `d = k + 1`),
    `p_a ∈ Π_a` and `p_b ∈ Π_b`. It drops three of the node's hypotheses: `κ ≤ 1`, `p_a`, `p_b`
    linearly independent, and `d ≥ 4`. The chapter's proof needs `κ ≤ 1` and the independence
    only for its four-points step, which the Lean replaces by a coordinate of `y₁ ∨ y₃` as
    stars-four's does. The statement is unchanged (no edit to a node's statement), so the Lean is
    stronger than the node. Whether the statement and its proof follow the Lean, as stars-four's
    did at the PI's word, goes to the PI or the cleanup (`notes/Cleanup42.md` R-13).
- **Risks the builds carry:** glued-ends is new planar mathematics on Phase 40's carrier, and may
  take two commits. That includes the contraction `G.map (collapseTo a {a, b})` with
  `def₂ = deficiencyMerged` (`partitionDef_map`), `Z⁰(q)` bounded by rank openness
  (`exists_mvPolynomial_le_finrank_span_of_repr`), and the `3|V(G)ᶜ|` the lifting planes count off
  `V(G)` (`Graph.finrank_liftingPlanes`). Planes-meet reads `la i` as the inverse of the
  admissible three-point matrix applied to `z`. Neither is spiked.

## Hand-off / next phase

The next concrete commit is **planes-meet**: `lem:pencil-d-planes-meet` → `Graph.liftingPlanesDiff`
and `Graph.exists_mvPolynomial_planesMeet`, a new `Grade/PlanesMeet.lean` (root import file too),
with their `\lean{}` and `\leanok`. The signatures are in the *Lemma checklist* and type-check in
`scratch/42i/Three.lean`; the proof is not spiked. Each `la i` is the inverse of the admissible
three-point matrix applied to `z`, and `R` comes by rank openness
(`exists_mvPolynomial_le_finrank_span_of_repr`) at a height whose rows are independent
(`notes/Cleanup42.md` R-15), so assess first whether it is one session's work. If not, land
`liftingPlanesDiff` with the lemma that reads the planes off `z`, and hand off the count. Update
R-15 (planned, becomes aligned or open). Then glued-ends (one or two commits) and the theorem (one).

- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure;
  the recon added R-13 to R-15 (`open`); R-13 has landed, R-14 and R-15 are planned.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42h are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42h.md` *Hand-off* lists 42h's), except `starGrade_smul`, which moved to
  `Grade/Stars.lean` with stars-three. Planes-meet's commit adds a file, which is no deferral's
  target; a lemma it adds to an existing file takes along that file's debts.
- **After 42i:** PD-STEPS is complete. PD-COVERAGE (`-chains`, `-coverage`, 4 red nodes),
  PD-REDUCTION and PD-HEAD open at the PI's word (design doc §3).

## Decisions made during this phase

- **Stars-three's helpers live in `Grade/Stars.lean`** (2026-10-31, second build), beside
  `starGrade` and `normalsJoinLin`, whose file is their home, so the build adds no home debt;
  `Grade/StarsThree.lean` holds the node's lemma only. `starGrade_smul` moved there too, re-proved
  by mathlib's one-scalar `Submodule.span_smul_eq_of_isUnit`, so `span_range_smul_eq` stays in
  `Grade/Short.lean` with its one consumer, `starsCond_of_smul`.
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
