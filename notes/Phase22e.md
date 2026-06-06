# Phase 22e — candidate-completion + Claim 6.12 (KT §6.4.1, eqs. (6.24)–(6.45)) (work log)

**Status:** in progress (opened 2026-06-06 design-pass-first). The candidate-completion
(eqs. (6.24)–(6.29)) landed green-modulo across 8 commits (`78f7eb4`…`3ab70cd`); the
**Claim-6.12 design pass** decomposed KT §6.4.1 (eqs. (6.30)–(6.45)) into buildable
red nodes N1–N9 and re-shaped the mis-shaped interface node `lem:case-III-eq629-conditional`
(single-candidate → the true 3-way disjunction). **N1, N2, N4, N5, N6, N7, N8 are green** and **N3b is
decomposed with its dictionary leaf `complementIso_toDual` AND step (i) green**
(`span_omitTwoExtensor_eq_top`, `eq_zero_of_annihilates_span_top`,
`linearIndependent_sumElim_candidateRow_iff` + `mem_hingeRowBlock_iff`, `candidateRow_ne_zero`,
the symmetric `p₂` producer `linearIndependent_sum_p2_candidateRow`, the third-candidate `p₃`
producer `linearIndependent_sum_p3_candidateRow`, and the eq.-(6.44) `candidateRow_ac_eq_neg`
+ `hingeRow_comp_single_{tail,off}`). The three candidate producers (`p₁`/`p₂`/`p₃`) are now all
green; what remains is the contrapositive glue. The N3b duality bridge was found multi-commit
(needs the Hodge-star / regressive-duality-on-decomposables theorem); its metric-free dictionary entry
`complementIso_toDual` and step (i) (`complementIso(n_u∧n')∈⋀²W`) are green, leaving one named step
(`dim ⋀²W=1`). Next: build N3b step (ii) + assemble N3b, then N3a, capstone N9, N10 flip.
Successor to 22d, the next chunk of Case III at `d=3` (KT §6.4.1,
Lemma 6.10). Lifts 22c's stratum-1 `D(|V|−1)−1` brick (`case_II_placement_eq612`,
green) to full `D(|V|−1)` by converting 22d's green redundant `ab`-row
(`exists_redundant_panelRow_ab_of_finrank_eq` = KT eq. (6.23)) into the missing
`+1` full-rank row, then resolving the `D`-candidate disjunction (Claim 6.12).
**Forward-mode / structural-edit:** no new blueprint chapter — the target nodes
(`lem:case-II-realization`, `lem:case-III`) are already stubbed red in
`algebraic-induction/case-ii.tex` / `case-iii.tex`; Lean lands in
`Molecular/AlgebraicInduction/` (+ `RigidityMatrix.lean` for LA leaves). KT math is
worked out in `notes/Phase22d.md` *Hand-off* + KT §6.4.1; 22e **formalizes** it.

## Current state

**Next concrete commit: build N3b step (ii) — `dim ⋀²W = 1` for a 2-dim `W`**, forcing the two
nonzero members `pᵢ∨pⱼ` and `C(L) = complementIso(n_u∧n')` to be scalar multiples, then assemble N3b.
Step (i) (this commit) puts `complementIso(n_u∧n')` in `⋀²W` (operational dual form: annihilated by
every 2-extensor sharing a vector with `n_u∧n'`); step (ii) is the 1-dimensionality that closes
"two nonzero members of a 1-dim space are proportional", giving `pᵢ∨pⱼ = λ·C(L)`. The incidence
`⟨p̄, n⟩=0` (both panels) puts `pᵢ∨pⱼ ∈ ⋀²W`. Build (ii) next, then assemble N3b.

**N3b step (i) landed green (this commit)** (`Molecular/Meet.lean`, axiom-clean). The
decomposable-of-orthogonal-complement step `complementIso(n_u∧n') ∈ ⋀²W`, in operational dual form,
as a two-half composition: `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` (the dictionary half —
a vanishing wedge `X∨ₑB=0` gives `toDual(complementIso X) B = vol(X∨ₑB) = 0`, one `rw` chain via the
green `complementIso_toDual` + `map_zero`) ∘ `wedgeProd_extensor_eq_zero_of_shared_vector` (the
concrete half at `k=2`/`⋀²ℝ⁴` — two 2-extensors sharing a vector wedge to `0`: the join's appended
family repeats the shared normal, `join_extensor` + `extensor_eq_zero_of_eq`), assembled in
`complementIso_toDual_extensor_eq_zero_of_shared_vector`. New green blueprint node
`lem:complement-iso-decomposable-wedge-perp` in `meet.tex`; N3b's `\uses` + proof prose rewired
(step (i) green, step (ii) the remaining content). `verify.sh` green; supersession + uses/cref gates
clean; `lake lint` clean. No new mirror, no FRICTION (standard `complementIso`-unfold idiom, as
predicted by the design recon).

After N3b: N3a (4 affinely-indep points, LOW risk — general position direct from `IsGeneralPosition`,
NOT alg-independence), capstone N9 (the 3-way disjunction, discharges `lem:case-III-eq629-conditional`),
then N10 flips `lem:case-II-realization` + the `d=3` half of `lem:case-III` green.

**N6 green** (`linearIndependent_sum_p2_candidateRow`, `RigidityMatrix.lean`, axiom-clean): the
symmetric `p₂` candidate (`va ↔ vb`). The candidate-completion assembly
`linearIndependent_sum_augment_candidateRow` takes the splitting body `v`, its endpoints, the
candidate `ρ`, and the two blocks abstractly, so applying it at the column op `columnOp (v≠b)` for
edge `vb` in place of `va` is the *same* lemma; the one hypothesis (operated top-left block full
rank) is fed by the N4 row-space criterion at the `vb`-hinge, with the bridge
`hingeRow_comp_columnOp_comp_single` identifying the operated, `v`-pinned candidate row with `ρ`
itself (`((hingeRow v b ρ)∘Φ)∘single v = ρ`, value `ρ(S v)`). Producer direction (`ρ(C)≠0 ⟹ full
family LI`) — exactly what N9's contrapositive consumes. No new mirror; both helpers in
`RigidityMatrix.lean`.

**N5 green** (`candidateRow_ne_zero`, `RigidityMatrix.lean`, axiom-clean): the eq. (6.42) `r̂ ≠ 0`
leaf. The common candidate row `r̂ = Σ_j λ_{(ab)j} rⱼ` is nonzero because `λ_{(ab)i*}=1` (green
redundant-decomposition, eq. (6.25)) and the `rⱼ` are LI: a combination of an LI family with a unit
coefficient is nonzero. Built on a new upstream-eligible mirror `linearIndependent_sum_smul_ne_zero`
(`∑ c_j • v_j ≠ 0` when some `c i ≠ 0`, the contrapositive of `Fintype.linearIndependent_iff`).

**N4 green** (`linearIndependent_sumElim_candidateRow_iff` + `mem_hingeRowBlock_iff`,
`RigidityMatrix.lean`, axiom-clean): the eq. (6.42) row-space criterion. The `D`-functional family
(`D−1` `va`-block rows spanning `(span C)^⊥ = r(p(e))` + candidate `r̂`) is LI ⟺ `r̂(C) ≠ 0`. Built
on a new upstream-eligible mirror `linearIndependent_sumElim_unit_iff` (appending one vector to an LI
family stays LI ⟺ the vector is fresh) + the membership translation `mem_hingeRowBlock_iff`
(`r̂ ∈ r(p(e)) ⟺ r̂(C) = 0`, the dual-annihilator evaluated at the spanning `C`).

**N2 green** (`eq_zero_of_annihilates_span_top`, `RigidityMatrix.lean`, axiom-clean): a functional
`r : Module.Dual ℝ (ScrewSpace k)` vanishing on a set `S` with `span S = ⊤` is `0`, via
`LinearMap.ext_on` (`r` agrees with `0` on the spanning set). The dual-annihilator framing —
not the inner-product `⟨r,r⟩=0` of the original blueprint prose — matches the `Module.Dual`
candidate-row chain; blueprint prose + `\leanok` updated to the `LinearMap.ext_on` route.

**N1 (`span_omitTwoExtensor_eq_top`, `RigidityMatrix.lean`) — green, axiom-clean.** The 6
panel-support 2-extensors of 4 affinely-independent points in ℝ³ span `ScrewSpace 2 = ⋀²ℝ⁴`
(finrank 6): `omitTwoExtensor_linearIndependent` (Lemma 2.1, `e=2`) gives LI of the 6 omit-two
extensors, lifted into the `⋀²` graded piece via `extensor_mem_exteriorPower`; LI of
`6 = finrank` vectors is a basis (`basisOfLinearIndependentOfCardEqFinrank`), hence spans.

**The Claim-6.12 design-pass recon decomposed KT §6.4.1
(eqs. (6.30)–(6.45)) into buildable nodes and found the interface node mis-shaped. Recorded the
decomposition durably and re-scoped:
- **Interface re-shape (ROOT FINDING).** `lem:case-III-eq629-conditional` previously asserted a
  SINGLE-candidate fact ("p₁'s top-left D×D block is full rank"). That is **not** a theorem at `d=3`:
  KT proves a **3-way disjunction** (Claim 6.12, eq. (6.42)) — at least one of `M₁/M₂/M₃` (candidates
  p₁ = split at `v` along `va`; p₂ = along `vb`; p₃ = split at the OTHER degree-2 vertex `a` along
  `vc`/`ac`, transported by `Gᵥᵃᵇ ≅ Gₐᵛᶜ`) is full rank, for some lines `L ⊂ Π(a)`, `L′ ⊂ Π(b)`,
  `L″ ⊂ Π(c)`. Re-shaped the node to the true existential. **Does NOT strand green Lean:** the
  assembly `linearIndependent_sum_augment_candidateRow` takes `ρ`/`rn`/`ro` abstractly, so it stays
  green; only the consumer `lem:case-III` instantiates at the chosen candidate.
- **New red nodes N1–N9** cut in a new `case-iii.tex` subsection *The D-candidate disjunction (KT
  eqs. (6.30)–(6.45))* — each statement + prose-proof sketch + `\uses`, no `\leanok`. Capstone N9
  (`lem:case-III-claim612`) wired into `lem:case-III`'s `\uses`. See *Lemma checklist* for the
  ordered N1–N10 build list with deps + risk.

**Already green (the candidate-completion, eqs. (6.24)–(6.29)):** the full block-assembly producer
`linearIndependent_sum_augment_candidateRow` (`RigidityMatrix.lean`) + its chain
(`lem:case-III-{redundant-decomposition,seam,columnop,vanish-off-column,transport-collapse,
candidate-row-construction,conditional-block,candidate-row}`), all green-modulo the now-re-shaped
`lem:case-III-eq629-conditional`. N1–N9 discharge exactly that conditional.

## Red-node consistency gate — recon verdict (2026-06-06, opening commit)

Read the three target red nodes end-to-end (statement + proof); ran the
supersession gate (`blueprint/CLAUDE.md` *Static checks → the supersession gate*)
over `algebraic-induction/*.tex`. **All consistent; gate clean.**

- **`lem:case-II-realization`** (case-ii.tex, KT's Case III producer) — statement +
  proof both route through `lem:case-II-realization-placement` (eq. (6.12) degenerate
  placement) → the N7a glue `lem:realization-of-independent-rows`. The two earlier
  dead-ends (row-side N7b-4, motion-side M1–M3) are named only as audit-trail
  `\cref{}` pointers, explicitly "off this route". Statement+proof `\uses` reach no
  superseded node.
- **`lem:case-II-realization-placement`** (genericity-and-count.tex) — routes through
  the green N7b-0/1/2/3 (`-new-rows`, `-old-rows`, `-old-rows-extract`,
  `-block-independent`) + the eq. (6.12) degeneracy (`p₁(vb)=q(ab)`, the `vb`-row
  reproduces the `e₀`-row). Superseded N7b-4 / M1–M3 referenced via audit-trail
  `\cref{}` only, never `\uses`.
- **`lem:case-III`** (case-iii.tex, the deferred Case-III target) — statement `\uses`
  the full green Claim-6.11 chain + `lem:case-II-realization-placement` (stratum-1
  brick) + `lem:extensor-independence` (green Lemma 2.1); proof "Deferred to
  Phases 22–23". The candidate-completion + Claim 6.12 are correctly its named
  deferred remainder. No superseded `\uses`.
- **Supersession gate:** superseded labels = {`-disjoint-line-meet`, `-e0-recovery`,
  `-motion-side-assembly`, `-pin-vertex`}; live-node-reaching-superseded set = ∅.
  All four carry the `superseded` marker in their environment title and `\uses` only
  each other or nothing.

**Verdict: the build is safe to scope.** The statements route through the same
argument they claim; the green N7b infra + the 22d redundant-`ab`-row are real
inputs; the candidate-completion is the genuine remaining content (no smuggled
hypothesis, no dead-end on the live route).

## Architectural choices made up front

- **Boundary preservation (confirmed against the existing plan).** The downstream
  `d=3` assembly (`prop:rigidity-matrix-prop11` `hub` partition brick — Track-%
  independent, Phase-19-partition — + the `thm:theorem-55` flip + wiring the
  fully-green `case_I_realization`) and **general-`d`** (Lemma 6.13) **stay separate**,
  as planned (ROADMAP §22 / `notes/MolecularConjecture.md`): the `d=3` assembly is the
  next deferred-unlettered cut after 22e, general-`d` is **Phase 23**. The recon found
  no reason to fold either in. 22e's scope is exactly the candidate-completion
  (eqs. (6.24)–(6.29)) + the Claim-6.12 disjunction (eqs. (6.30)–(6.45)) at `d=3`,
  stratum 1 — the content that takes `lem:case-II-realization` / `lem:case-III` from
  red to (the `d=3` half of) green.
- **Design-pass-first** (`DESIGN.md` *Scale-up: design the LAYER, not just the node*).
  Like 22c/22d, this is research-shaped and interlocking (the row-op `w` construction
  + the `D`-candidate disjunction + the eq. (6.44) "same `r`" reduction onto Lemma 2.1).
  Opened on this recon, not a build.

## Lemma checklist

- [x] **Candidate-completion (eqs. (6.24)–(6.29)) — all green-modulo** (commits `78f7eb4`…`3ab70cd`).
  The 8-node chain converting 22d's redundant `ab`-row into the missing `+1`:
  `lem:case-III-{vanish-off-column, seam, redundant-decomposition, acolumn-zero, columnop,
  conditional-block, transport-collapse, candidate-row-construction, candidate-row}` (Lean in
  `RigidityMatrix.lean` / `CaseI.lean` / `PanelHinge.lean`, all axiom-clean). The producer
  `linearIndependent_sum_augment_candidateRow` is green-**modulo** the now-re-shaped
  `lem:case-III-eq629-conditional`. Detail: *Decisions made* (one-lined) + git.
- [x] **Claim-6.12 design pass (this commit)** — interface re-shape + N1–N9 node-cut (below).

### Claim 6.12 — the 3-way disjunction (KT eqs. (6.30)–(6.45)); discharges `lem:case-III-eq629-conditional`

Ordered build list (leaf-most first; deps are blueprint `\uses`). Blueprint nodes all cut red this
commit (no `\lean`/`\leanok`); build greens them.

- [x] **N1** `lem:case-III-claim612-extensor-span` (`span_omitTwoExtensor_eq_top`, green,
  axiom-clean) — the 6 panel-support 2-extensors of 4 affinely-indep points in ℝ³ span
  `ScrewSpace 2 = ⋀²ℝ⁴` (finrank 6), via `omitTwoExtensor_linearIndependent` (Lemma 2.1, `e=2`)
  + `extensor_mem_exteriorPower` lift + `basisOfLinearIndependentOfCardEqFinrank`.
- [x] **N2** `lem:case-III-claim612-orthseq-vanish` (`eq_zero_of_annihilates_span_top`, green,
  axiom-clean) — a functional `r : Module.Dual ℝ (ScrewSpace k)` vanishing on a set `S` with
  `span S = ⊤` is `0`, via `LinearMap.ext_on`. Deps: N1. Dual-annihilator framing (not the
  inner-product `⟨r,r⟩=0` of the original prose) to match the `Module.Dual` candidate-row chain.
- [ ] **N3a** `lem:case-III-claim612-points-affineIndep` — from a general-position framework
  (`IsGeneralPosition`: pairwise-indep panel normals `n_a,n_b,n_c`), 4 **affinely-independent**
  points `p : Fin 4 → Fin 3 → ℝ` realizing the `Π(a)/Π(b)/Π(c)` incidence pattern
  (`pᵢ ∈ Π(u) ⟺ ⟨homogenize pᵢ, n_u⟩ = 0`). The span side N1 consumes. Deps: `def:rigidity-matrix`,
  `def:panel-hinge-framework`. **LOW RISK** — general position direct from `IsGeneralPosition`, **NOT**
  an alg-independence use (`notes/AlgebraicIndependence.md` row #106 re-classified).
- [ ] **N3b** `lem:case-III-claim612-line-in-panel-union` — the point-join↔panel-meet duality
  bridge (still red, decomposed this commit). For a pair whose connecting line `L` lies in panel
  `Π(u)`, the join `pᵢ∨pⱼ` equals a scalar multiple of the panel-meet extensor `C(L) =
  panelSupportExtensor n_u (·) = complementIso(normalsJoin)`, so `r ⊥ all C(L⊂Π(u)) ⟹ r(pᵢ∨pⱼ)=0`.
  Recon found this multi-commit (full "= λ·" needs Hodge-star / decomposable-duality, not in
  mathlib/in-project). Three leaves:
  - [x] **N3b-dict** `lem:complement-iso-toDual` (`complementIso_toDual`, `Meet.lean`, green,
    axiom-clean) — the metric-free dictionary entry `b.toDual (complementIso X) B = wedgePairing X B
    = vol(X∨B)`. Three-line proof. Deps: `def:meet-complement-iso`, `def:meet-top-equiv`.
  - [x] **N3b-(i)** `complementIso(n_u∧n') ∈ ⋀²W` for `W = {n_u,n'}^⊥` (decomposable-of-orthogonal-
    complement, green, axiom-clean) — `complementIso_toDual_extensor_eq_zero_of_shared_vector`
    (`Meet.lean`), the composition of the dictionary half
    `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` (vanishing wedge ⟹ vanishing complement
    pairing, via N3b-dict) and the concrete half `wedgeProd_extensor_eq_zero_of_shared_vector`
    (two 2-extensors sharing a vector wedge to 0 at `k=2`, `join_extensor` + alternating law). New
    green node `lem:complement-iso-decomposable-wedge-perp` in `meet.tex`. Deps: N3b-dict, `def:join`,
    `def:extensor`, `def:meet-complement-iso`.
  - [ ] **N3b-(ii)** `dim ⋀²W = 1` for a 2-dim `W`, forcing the two nonzero members to be scalar
    multiples; then assemble N3b. Deps for full N3b: N1 + Phase-21a Meet (`def:join`, `def:meet`,
    `def:meet-complement-iso`, `def:panel-support-extensor`, `lem:extensor-independence`).
- [x] **N4** `lem:case-III-claim612-block-iff-perp` (`linearIndependent_sumElim_candidateRow_iff` +
  `mem_hingeRowBlock_iff`, green, axiom-clean) — the D functionals (D−1 va-block rows spanning
  `(span C)^⊥` + candidate `r̂`) are LI ⟺ `r̂ ∉ (span C)^⊥` ⟺ `r̂(C) ≠ 0`. Built on new mirror
  `linearIndependent_sumElim_unit_iff`. Deps: `def:rigidity-matrix`, `def:hinge-row-block`,
  `lem:case-II-placement-new-rows`.
- [x] **N5** `lem:case-III-claim612-r-nonzero` (`candidateRow_ne_zero`, green, axiom-clean) —
  `r̂ := Σⱼ λ_{(ab)j} rⱼ(q(ab)) ≠ 0` (`λ_{(ab)i*}=1` from the green redundant-decomposition). Built on
  new mirror `linearIndependent_sum_smul_ne_zero`. Deps: `lem:case-III-redundant-decomposition`,
  `lem:case-II-placement-new-rows`.
- [x] **N6** `lem:case-III-claim612-p2-placement` (`linearIndependent_sum_p2_candidateRow`, green,
  axiom-clean) — the symmetric p₂ (va↔vb), reusing the abstract assembly
  `linearIndependent_sum_augment_candidateRow` at `columnOp (v≠b)` for edge `vb` + the N4 criterion
  at the `vb`-hinge, bridged by `hingeRow_comp_columnOp_comp_single` (`((hingeRow v b ρ)∘Φ)∘single v
  = ρ`). Producer direction `ρ(C)≠0 ⟹ full family LI`. Deps: `lem:case-II-realization-placement`,
  `lem:case-III-columnop`, `lem:case-III-claim612-block-iff-perp` (all green; **not**
  `lem:case-III-candidate-row` — that would close a dep-graph cycle through the green-modulo
  conditional, FRICTION `[blueprint]`).
- [x] **N7** `lem:case-III-claim612-p3-placement` (`linearIndependent_sum_p3_candidateRow`, green,
  axiom-clean) — the p₃ third candidate (split at degree-2-`a` along `ac`, `Gᵥᵃᵇ ≅ Gₐᵛᶜ`). The
  `va↔ac` analog of N6: the *same* abstract assembly `linearIndependent_sum_augment_candidateRow` at
  `columnOp hac` (edge `ac`, split body `a`, endpoint `c`) + the N4 criterion at the `ac`-hinge,
  bridged by `hingeRow_comp_columnOp_comp_single hac`. The `Gᵥᵃᵇ≅Gₐᵛᶜ` iso is handled
  **functionally** (candidate row `hingeRow a c ρ`; no `ofNormals` swap, defeq trap does **not**
  bite); the link to common `r̂` is N8 (eq. (6.44)), consumed by N9, not N7's producer. Deps:
  `lem:case-II-realization-placement`, `lem:case-III-columnop`, `lem:case-III-claim612-block-iff-perp`,
  `lem:case-III-claim612-eq644` (N8) — all green (**not** `lem:case-III-candidate-row`: cycle,
  FRICTION `[blueprint]`).
- [x] **N8** `lem:case-III-claim612-eq644` (`candidateRow_ac_eq_neg` + `hingeRow_comp_single_{tail,off}`,
  green, axiom-clean) — eq. (6.44) `Σⱼ λ_{(ac)j} rⱼ = −Σⱼ λ_{(ab)j} rⱼ`, routing M₃ onto the same `r̂`.
  Stated abstractly: the eq. (6.43) `a`-column combination `(ab-sum)+(ac-sum)+grest` with `grest`
  vanishing off `a` (the degree-2-at-`a` content as hypothesis `hrest`) regroups, via the two new
  column-restriction leaves, into `r̂ + rAC = 0`. Deps: `lem:case-III-acolumn-zero`,
  `lem:case-III-redundant-decomposition` (both green).
- [ ] **N9** `lem:case-III-claim612` (capstone) — at least one of `M₁/M₂/M₃` is LI; discharges
  `lem:case-III-eq629-conditional`. Contrapositive: all dependent ⟹ `r ⊥ C(L),C(L′),C(L″)` (N4×2 +
  N8) ⟹ (N3b duality) `r` annihilates each spanning join `pᵢ∨pⱼ` ⟹ `r` annihilates the span (6.45)
  spanning set (N3a + N1) ⟹ `r=0` (N2), contradicting N5. Deps: N1, N2, N3a, N3b, N4, N5, N6, N7, N8.
  Wired into `lem:case-III`'s `\uses`.
- [ ] **N10 Flip** `lem:case-II-realization` (+ the `d=3` half of `lem:case-III`) green once N9
  discharges `lem:case-III-eq629-conditional`. Candidate-completion subsection nodes are all green
  (green-modulo the conditional N9 closes).

## Blockers / open questions

- **Recurring Lean trap (carry from 22a–d, FRICTION):** heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps can
  `isDefEq`-timeout — make the two frameworks *syntactically* equal before `convert`;
  transfer rigidity via a `mem_infinitesimalMotions` round-trip. The 22e producers
  are all graph-free (abstract block functionals), so the trap does **not** bite 22e;
  it bites the **`d=3` assembly** (the consumer that extracts `rn`/`ro` from
  `case_II_placement_eq612` and wires the real graph data).

## Hand-off / next phase

**Next concrete commit: build N3b step (ii) — `dim ⋀²W = 1` for a 2-dim `W`**, forcing the two
nonzero members `pᵢ∨pⱼ` and `C(L) = complementIso(n_u∧n')` to be scalar multiples
(`pᵢ∨pⱼ = λ·C(L)`), then assemble N3b. Step (i) (just landed) put `complementIso(n_u∧n')` in `⋀²W`
in operational dual form (annihilated by every 2-extensor sharing a vector); the incidence
`⟨p̄,n⟩=0` (both panels) puts `pᵢ∨pⱼ ∈ ⋀²W` too. Step (ii) is the 1-dimensionality: `⋀²` of a 2-dim
space is 1-dim, so any two nonzero members are proportional — the standard fact (mathlib's
exterior-power finrank of a 2-dim space, or `extensor`-line span; tractable). Assembling N3b is then
the annihilation transfer `r(C(L))=0 ⟹ r(pᵢ∨pⱼ) = λ·r(C(L)) = 0`.

**Why N3b is decomposed:** complete N3b ("`pᵢ∨pⱼ = λ·C(L)`") needs the Hodge-star /
regressive-duality-on-decomposables content — not in mathlib, not yet in-project — so it is
multi-commit. The dictionary leaf `complementIso_toDual` (prior commit) and step (i) (this commit)
are green; step (ii) + the assembly are the remaining leaves, named above + in the checklist.

Then, in order: **N3a** (`lem:case-III-claim612-points-affineIndep`, 4 affinely-indep points — LOW
risk, general position direct from `IsGeneralPosition`, NOT alg-independence), then capstone **N9**
(`lem:case-III-claim612`, the 3-way disjunction) — which discharges the re-shaped
`lem:case-III-eq629-conditional` — after which **N10** flips `lem:case-II-realization` + the `d=3`
half of `lem:case-III` green. The three candidate producers (`p₁`/`p₂`/`p₃` = N6/N7 + the
candidate-completion `lem:case-III-candidate-row`) are all green; N3b/N3a/N9 are the contrapositive
glue (`r ⊥ all panel-meets ⟹ r ⊥ the spanning joins ⟹ r=0`).

**Note (the brick-block extraction is deferred to the `d=3` assembly, not 22e).** The assembly
producer takes `rn`/`ro` as abstract block functionals; the consumer (the unlettered `d=3` assembly
after 22e) extracts them from `case_II_placement_eq612` (which packages a `Set`-family) and wires the
augment with the real graph data — that is where the **recurring `ofNormals` defeq-timeout trap
(Blockers)** bites, *not* in 22e (the 22e producer is graph-free by design).

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` row #106 (re-classified this commit:
N3a/N3b are NOT alg-independence sites — general position direct from `IsGeneralPosition`).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **N3b step (i) green — the decomposable-of-orthogonal-complement step as a two-half composition
  (2026-06-06).** `complementIso_toDual_extensor_eq_zero_of_shared_vector` (`Meet.lean`, axiom-clean):
  `complementIso(n_u∧n') ∈ ⋀²W` in operational dual form (annihilated by every 2-extensor sharing a
  vector with `n_u∧n'`). Factored into the **dictionary half**
  `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` (`wedgeProd X B = 0 ⟹ toDual(complementIso X)
  B = 0`, one `rw` chain via the green `complementIso_toDual` + `map_zero`) and the **concrete half**
  `wedgeProd_extensor_eq_zero_of_shared_vector` (two 2-extensors sharing a vector wedge to 0 at `k=2`:
  `Subtype.ext` + `coe_wedgeProd` + a `change` to the join + `join_extensor` + `extensor_eq_zero_of_eq`
  on the repeated appended index). New green node `lem:complement-iso-decomposable-wedge-perp` in
  `meet.tex`; N3b's `\uses` + proof prose rewired. No new mirror, no FRICTION (the `change` is a routine
  subtype-coercion defeq, not a missing lemma) — as the design recon predicted.
- **N3b decomposed; dictionary leaf `complementIso_toDual` green (2026-06-06).** Recon confirmed the
  complete duality bridge (`pᵢ∨pⱼ = λ·C(L)`) is multi-commit research — it bottoms on the Hodge-star /
  regressive-duality-on-decomposables theorem (in `⋀²ℝ⁴`: `complementIso` of a decomposable lands in
  the orthogonal complement's `⋀²`, and `⋀²W` is 1-dim for 2-dim `W`), absent from both mathlib and
  the project. Landed the genuinely-new tractable staging leaf: the metric-free Grassmann–Cayley
  **dictionary entry** `complementIso_toDual` (`Meet.lean`, axiom-clean) — `b.toDual (complementIso X)
  B = wedgePairing X B = vol(X∨B)`, the defining wedge-pairing property of `complementIso`, three lines
  via `complementIso = wedgePairing-equiv ≪≫ toDualEquiv.symm` + `apply_symm_apply` (modelled on the
  existing `complementIso_exteriorPower_repr_mem_range_intCast`). Re-decomposed the still-red N3b node
  to route through it (new green node `lem:complement-iso-toDual` in `meet.tex`), naming the two
  remaining leaves: (i) `complementIso(n_u∧n')∈⋀²W`, (ii) `dim ⋀²W=1`. No new mirror; no FRICTION
  (standard `complementIso`-unfold idiom). Lean home: `Meet.lean` (the `complementIso` definition file).
- **N3 re-shape — split into N3a (points) + N3b (the duality bridge); N7 de-risked (2026-06-06,
  design pass, docs/blueprint only).** A recon found the old single N3 `lem:case-III-claim612-points`
  mis-shaped for its N9 consumer: it promised KT's triple-intersection incidence *device* (the way KT
  arranges the point choice), but N9 consumes two distinct facts. Split into **N3a**
  (`lem:case-III-claim612-points-affineIndep`: 4 affinely-indep points, the span side N1 uses) and
  **N3b** (`lem:case-III-claim612-line-in-panel-union`: the point-join↔panel-meet Grassmann–Cayley
  duality — `pᵢ∨pⱼ` ∝ `C(L)=panelSupportExtensor=complementIso(normalsJoin)` — the genuinely-missing
  content N9 needs to turn `r⊥C(L)` into `r(pᵢ∨pⱼ)=0`). Re-wired N9's `\uses` + the `lem:case-III`
  prose off the old label (no dangling). **General position is NOT alg-independence** (row #106
  re-classified — direct from `IsGeneralPosition`). **N7 de-risked**: follows N6's graph-free producer
  pattern (assembly at `columnOp hac` + green N8 routing M₃ onto `r̂`; the iso is functional via N8,
  no `ofNormals` swap, defeq trap does NOT bite). All gates clean; `verify.sh` green (no cycle).
- **N7 green — the `p₃` candidate is the abstract assembly at the `va↔ac` role change (2026-06-06).**
  `linearIndependent_sum_p3_candidateRow` (`RigidityMatrix.lean`, axiom-clean): the third-candidate
  producer is the *same* assembly `linearIndependent_sum_augment_candidateRow` as N6, at `columnOp hac`
  for edge `ac` (split body `a`, endpoint `c`) + the N4 criterion at the `ac`-hinge, bridged by
  `hingeRow_comp_columnOp_comp_single hac`. The `Gᵥᵃᵇ≅Gₐᵛᶜ` iso is **functional** (candidate row
  `hingeRow a c ρ`; no `ofNormals` swap, defeq trap does not bite); the common-`r̂` link is N8
  (eq. (6.44)), consumed by N9, not by N7. Three-line proof, structurally identical to N6 — no new
  helper, no FRICTION. All three candidate producers (`p₁`/`p₂`/`p₃`) now green.
- **N8 green — eq. (6.44) is column-restriction regrouping + add-cancellation (2026-06-06).**
  `candidateRow_ac_eq_neg` (`RigidityMatrix.lean`, axiom-clean): the eq. (6.43) `a`-column combination,
  written abstractly as `(ab-sum) + (ac-sum) + grest` with `grest` vanishing off `a` (the
  degree-2-at-`a` content supplied as hypothesis `hrest` — the `d=3` assembly consumer discharges it
  via the new leaf `hingeRow_comp_single_off`), regroups by the column-restriction leaf
  `hingeRow_comp_single_tail` (`(hingeRow a b ρ)∘single a = ρ`) into `r̂ + rAC = 0`, so `rAC = −r̂`.
  Graph-free like the rest of the chain; N7's `p₃` consumes it to route `M₃` onto `r̂`. Comp-over-sum
  went pointwise (no `LinearMap.sum_comp`) → FRICTION *Mirrored* + TACTICS-GOLF § 16.
- **N6 green — the `p₂` candidate is the abstract assembly at swapped roles (2026-06-06).**
  `linearIndependent_sum_p2_candidateRow` (`RigidityMatrix.lean`, axiom-clean): the candidate-completion
  producer `linearIndependent_sum_augment_candidateRow` takes `v`/endpoints/`ρ`/blocks abstractly, so
  the `va↔vb` symmetric candidate is the *same* lemma at `columnOp (v≠b)` for edge `vb`; its one
  hypothesis (operated top-left block full rank) is the N4 criterion at the `vb`-hinge, bridged by a
  new one-line helper `hingeRow_comp_columnOp_comp_single` (`((hingeRow v b ρ)∘Φ)∘single v = ρ`,
  value `ρ(S v)`). Producer direction (`ρ(C)≠0 ⟹ full family LI`) — what N9's contrapositive
  consumes; the "iff" lives in N4. No new mirror (both helpers project-internal). Dep-graph caveat
  promoted → FRICTION `[blueprint]`.
- **N5 green — the `r̂ ≠ 0` leaf via a unit coefficient on an LI family (2026-06-06).**
  `candidateRow_ne_zero` (`RigidityMatrix.lean`, axiom-clean): the common candidate row
  `r̂ = Σⱼ λⱼ • rⱼ` is nonzero because the redundant index carries `λ_{i*} = 1` (eq. (6.25), green
  `exists_redundant_panelRow_ab_decomposition`) and the `rⱼ` are LI. One line over a new
  upstream-eligible mirror `linearIndependent_sum_smul_ne_zero` (`∑ c_j • v_j ≠ 0` when some
  `c i ≠ 0`, contrapositive of `Fintype.linearIndependent_iff`) → FRICTION *Mirrored*. Honesty gate:
  both hypotheses (`hr` LI, `hlam` unit) are conclusions of the two `\uses`'d green nodes.
- **N4 green — the eq. (6.42) row-space criterion as an abstract augment-iff
  (2026-06-06).** `linearIndependent_sumElim_candidateRow_iff` + `mem_hingeRowBlock_iff`
  (`RigidityMatrix.lean`, axiom-clean): the `D`-functional family (`D−1` `va`-block rows spanning
  `(span C)^⊥ = r(p(e))` + candidate `r̂`) is LI ⟺ `r̂(C) ≠ 0`. Factored into (i) a new
  upstream-eligible mirror `linearIndependent_sumElim_unit_iff` (appending one vector to an LI family
  stays LI ⟺ it is fresh — `linearIndependent_sum` + `disjoint_span_singleton'`), and (ii) the
  membership translation `mem_hingeRowBlock_iff` (`r̂ ∈ dualAnnihilator (span {C}) ⟺ r̂(C) = 0`).
  N4 is then a one-line `rw` chain. The lemma takes `rn`/`r̂` abstractly (no `columnOp` plumbing) —
  it is the clean criterion the candidate-completion assembly's `hnewpinaug` recasts to. The mirror
  + the `of_subsingleton` torsion-free import gotcha → FRICTION *Mirrored* + TACTICS-QUIRKS § 40.
- **Claim-6.12 interface re-shape — the conditional is a 3-WAY disjunction, not single-candidate
  (2026-06-06; design-pass, this commit).** A recon against KT §6.4.1 (eqs. (6.30)–(6.45), verified
  against the .refs PDF pp. 689–691) found `lem:case-III-eq629-conditional` mis-shaped: it asserted
  "p₁'s top-left `D×D` block is full rank", a SINGLE-candidate fact that is **not** a theorem at `d=3`
  (a single degenerate placement can fail; at `d=2` p₁/p₂ suffice, at `d≥3` they need not). KT's
  Claim 6.12 (eq. (6.42)) is the existential over **three** candidates `M₁/M₂/M₃` (p₁ = split at `v`
  along `va`; p₂ = along `vb`; p₃ = split at the OTHER degree-2 vertex `a` along `vc`, via the graph
  iso `Gᵥᵃᵇ ≅ Gₐᵛᶜ`) and choices of lines `L/L′/L″`. Re-shaped the node to that existential.
  **Crucially does NOT strand green Lean:** the assembly `linearIndependent_sum_augment_candidateRow`
  takes `ρ`/`rn`/`ro` abstractly (verified signature, `RigidityMatrix.lean:806`), so it stays green;
  only the consumer `lem:case-III` instantiates at the chosen candidate. Cut N1–N9 in a new
  `case-iii.tex` subsection (all red, no `\leanok`); N9 capstone wired into `lem:case-III`'s `\uses`.
  (N3 later split + N7 de-risked — see the *N3 re-shape* entry above.) BlueprintExposition: capture
  entries added (p₃ transport (a); eq. 6.44 (a); the span (6.45)+Lemma-2.1 step (c); + the
  point-join↔panel-meet duality (c), this commit).
- **Candidate-completion (eqs. (6.24)–(6.29)) — all landed green-modulo, now one-lined.** Eight green
  axiom-clean nodes (commits `78f7eb4`…`3ab70cd`), the candidate-row chain that converts 22d's
  redundant `ab`-row into the missing `+1`: the eqs.-(6.24)/(6.25) extraction
  (`-redundant-decomposition`), the eq.-(6.43) `a`-block vanishing (`-acolumn-zero`, **re-scoped to a
  Claim-6.12 input — the `M₃` case = N8**), the seam (`-seam`, per-row form to sidestep the
  `ofNormals` defeq trap), the eqs.-(6.14)–(6.16) column op `Φ S = update S v (S v + S a)`
  (`-columnop`), the eq.-(6.29) conditional block (`-conditional-block`), the eq.-(6.27) transport
  collapse (`-transport-collapse`), the combination-level threading core (`-candidate-row-construction`,
  the *common* element `wGv` is one `hingeRow a b ρ` — no per-row `λ`-expansion), and the full
  block-assembly producer (`-candidate-row`: precompose `rn⊔{w}⊔ro` with `Φ.dualMap`, run the augment
  on the operated family where `w ∘ Φ` is pure-`v`-column, transport back). All graph-free (abstract
  block functionals) — the `ofNormals` trap bites only the deferred `d=3` assembly consumer.
- **Route-finding lesson (the column op is load-bearing, the seam alone is not) — promoted to
  FRICTION (2026-06-06).** A recon found the planned candidate-row route (seam + eq. (6.43) → off-`v`
  vanishing) mis-identified the vanishing *mechanism*: `w = hingeRow v a ρ_g` is supported on columns
  `v` AND `a`, so it does not vanish off `v` on its own — the off-`v` vanishing is KT's eqs.
  (6.14)–(6.16) column op, and eq. (6.43) is the separate Claim-6.12 `M₃` fact (now N8). Lesson (a
  recon must verify the *mechanism* of a claimed vanishing, not just the count) → FRICTION;
  BlueprintExposition `(c)` capture stands.
