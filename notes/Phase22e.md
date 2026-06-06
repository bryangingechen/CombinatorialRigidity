# Phase 22e — candidate-completion + Claim 6.12 (KT §6.4.1, eqs. (6.24)–(6.45)) (work log)

**Status:** in progress (opened 2026-06-06 design-pass-first). The candidate-completion
(eqs. (6.24)–(6.29)) landed green-modulo across 8 commits (`78f7eb4`…`3ab70cd`); the
**Claim-6.12 design pass** decomposed KT §6.4.1 (eqs. (6.30)–(6.45)) into buildable
red nodes N1–N9 and re-shaped the mis-shaped interface node `lem:case-III-eq629-conditional`
(single-candidate → the true 3-way disjunction). **N1, N2, N4, N5 are now green**
(`span_omitTwoExtensor_eq_top`, `eq_zero_of_annihilates_span_top`,
`linearIndependent_sumElim_candidateRow_iff` + `mem_hingeRowBlock_iff`, `candidateRow_ne_zero`).
**N6 is now green** (`linearIndependent_sum_p2_candidateRow`, the symmetric `p₂` producer).
Next: N8 (medium), N3/N7 (research-shaped — recon-before-build), capstone N9.
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

**Next concrete commit: build N8 (`lem:case-III-claim612-eq644`)** — eq. (6.44)
`r = −Σⱼ λ_{(ac)j} rⱼ(q(ac))`, routing the `M₃` candidate row onto the *same* common vector `r` as
`M₁/M₂`, from the green eq. (6.43) `a`-column vanishing (`exists_redundant_panelRow_ab_decomposition_acolumn_zero`)
+ degree-2-at-`a` (only `ab`/`ac` incident to `a`). Deps: `lem:case-III-acolumn-zero`,
`lem:case-III-redundant-decomposition` (both green). **Medium.** Then N3/N7 (research-shaped,
recon-before-build), capstone N9.

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
- [ ] **N3** `lem:case-III-claim612-points` — from a generic nonparallel framework, 4
  affinely-indep points with the `Π(a)/Π(b)/Π(c)` triple-intersection incidence pattern, every line
  `pᵢpⱼ` in `Π(a)∪Π(b)∪Π(c)`. Deps: `def:rigidity-matrix`. **RESEARCH-SHAPED** (general position;
  likely a new alg-independence use — see `notes/AlgebraicIndependence.md` risk #8). Recon-before-build.
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
- [ ] **N7** `lem:case-III-claim612-p3-placement` — the p₃ third candidate via the `Gᵥᵃᵇ ≅ Gₐᵛᶜ`
  isomorphism (degree-2-at-`a`), `columnOp` at `(v,c)`/`(a,c)`. Deps: `lem:case-II-realization-placement`,
  `lem:case-III-columnop`, `lem:case-III-candidate-row`, N8. **HIGH RISK** (`ofNormals` graph-swap
  defeq trap, *Blockers*; KT's most-compressed step, eqs. (6.31)–(6.41)). Recon-before-build.
- [ ] **N8** `lem:case-III-claim612-eq644` — eq. (6.44) `r = −Σⱼ λ_{(ac)j} rⱼ(q(ac))`, routing M₃
  onto the same `r`, from the green eq. (6.43) + degree-2-at-`a` (only `ab`/`ac` incident to `a`).
  Deps: `lem:case-III-acolumn-zero`, `lem:case-III-redundant-decomposition`. **Medium.**
- [ ] **N9** `lem:case-III-claim612` (capstone) — at least one of `M₁/M₂/M₃` is LI; discharges
  `lem:case-III-eq629-conditional`. Contrapositive: all dependent ⟹ `r ⊥ C(L),C(L′),C(L″)` (N4×2 +
  N8) ⟹ `r` annihilates the span (6.45) spanning set (N3 + N1) ⟹ `r=0` (N2), contradicting N5.
  Deps: N1–N8. Wired into `lem:case-III`'s `\uses`.
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

**Next concrete commit: build N8 (`lem:case-III-claim612-eq644`)** — eq. (6.44)
`r = −Σⱼ λ_{(ac)j} rⱼ(q(ac))`, routing the `M₃` candidate row onto the *same* common `r` as `M₁/M₂`.
From the green eq. (6.43) `a`-column vanishing (`exists_redundant_panelRow_ab_decomposition_acolumn_zero`):
in `G_v^{ab}` only `ab`/`ac` are incident to `a`, so the `a`-column restriction of the eq. (6.24)
vanishing combination reads `0 = Σⱼ λ_{(ab)j} rⱼ(q(ab)) + Σⱼ λ_{(ac)j} rⱼ(q(ac))`; rearranging for
`r = Σⱼ λ_{(ab)j} rⱼ(q(ab))` gives eq. (6.44). Deps: `lem:case-III-acolumn-zero`,
`lem:case-III-redundant-decomposition` (both green). **Medium** — the algebra is light, but the
"only `ab`/`ac` incident to `a`" step needs the degree-2-at-`a` graph fact. Then N3/N7
(research-shaped — recon-before-build), capstone N9 — which discharges the re-shaped
`lem:case-III-eq629-conditional`, after which N10 flips `lem:case-II-realization` + the `d=3` half of
`lem:case-III` green.

**Recon-before-build the two research-shaped nodes.** N3 (`-claim612-points`, general position of the
4 incidence points) and N7 (`-claim612-p3-placement`, the `Gᵥᵃᵇ ≅ Gₐᵛᶜ` transport — KT's most
compressed step, the `ofNormals` defeq trap territory). The rest (N2/N4/N5/N8 mechanical, N6 medium)
are routine; do them in dependency order so the capstone N9 has its inputs.

**Note (the brick-block extraction is deferred to the `d=3` assembly, not 22e).** The assembly
producer takes `rn`/`ro` as abstract block functionals; the consumer (the unlettered `d=3` assembly
after 22e) extracts them from `case_II_placement_eq612` (which packages a `Set`-family) and wires the
augment with the real graph data — that is where the **recurring `ofNormals` defeq-timeout trap
(Blockers)** bites, *not* in 22e (the 22e producer is graph-free by design).

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` (the alg-independence tracker,
risk #8 — add a row if 22e introduces a new alg-independence use).

## Decisions made during this phase

### Phase-local choices and proof techniques
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
  N3/N7 flagged research-shaped (recon-before-build). BlueprintExposition: capture entries added this
  commit (p₃ transport (a); eq. 6.44 (a); the span (6.45)+Lemma-2.1 step (c)).
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
