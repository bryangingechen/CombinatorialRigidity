# Phase 22e — candidate-completion + Claim 6.12 (KT §6.4.1, eqs. (6.24)–(6.45)) (work log)

**Status:** in progress (opened 2026-06-06 design-pass-first; opening recon +
eq.-(6.28) blueprint node + `w` constructibility recon + `w` node-cut + the
seam-identity build + the eqs.-(6.24)/(6.25) decomposition + the eq.-(6.43)
`a`-block vanishing landed).
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

**Next concrete commit: assemble the row `w` (KT eqs. (6.26)–(6.28))** — transport the
eqs.-(6.24)/(6.25) decomposition across the seam and certify its `V∖{v}` part vanishes, then
apply the eq.-(6.28) leaf to land `lem:case-III-candidate-row` green. All four inputs are now
green: the eqs.-(6.24)/(6.25) decomposition (`exists_redundant_panelRow_ab_decomposition`), the
eq.-(6.43) `a`-block vanishing (`…_acolumn_zero`, this commit), the per-edge seam
(`ofNormals_panelRow_eq_of_ends_seed_eq`), and the eq.-(6.28) leaf
(`dualMap_eq_comp_single_proj_of_vanish_off`). The open crux is the eq.-(6.27) *assembly*:
build `w = Σⱼ λ_{(ab)j} hingeRow v b r_j + Σ_{E_v} λ_{ej}(…)` in `span(R(G,p₁)-rows)`, show its
`V∖{v}` part = the eq.-(6.24) sum (= 0) *minus* the ab-part `a`-block (killed by eq. (6.43)),
then `dualMap_eq_comp_single_proj_of_vanish_off` makes `w` a pure `v`-column row. Then the
conditional `D`-row block (eq. (6.29), `linearIndependent_sum_pinned_block`) and Claim 6.12.

**Landed this commit (KT eq. (6.43), the `a`-column block of eq. (6.24) is `0`):**
- `BodyHingeFramework.exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`,
  axiom-clean) — extends the eqs.-(6.24)/(6.25) decomposition with the eq.-(6.43) conclusion: the
  vanishing combination `g := wGv + wOther − r i*` (= 0 since `r i* = wGv + wOther`) precomposed
  with the column injection `single a` is `0` for every body `a`, i.e. the `a`-column block of
  eq. (6.24) is itself `0` (`Σ_{e∈E_v∪{ab},j} λ_{ej} R(G_v^{ab},q;e_j,a) = 0`). One-line proof
  (`rw [hsum, sub_self, LinearMap.zero_comp]`): trivial *given* the decomposition, but the
  load-bearing fact the `w`-assembly's off-`v` vanishing consumes. Blueprint node
  `lem:case-III-acolumn-zero` (green, `\uses lem:case-III-redundant-decomposition`); wired into
  `lem:case-III-candidate-row` (statement + proof `\uses`) and `lem:case-III`. Candidate-completion
  preamble + the candidate-row proof caveat updated (eq. (6.43) now green, only the transport open).

## Constructibility recon — `w`'s row operation (KT eqs. (6.24)→(6.28))

Read KT §6.4.1 pp. 684–686 (eqs. (6.22)–(6.30)) end-to-end against the green Lean.
**Verdict: the arithmetic closes; the only open Lean is the seam identity.**

- Claim 6.11 / eq. (6.23) gives the redundant `ab`-row; the green
  `exists_redundant_panelRow_ab_of_finrank_eq` delivers exactly KT's eq. (6.24)/(6.25):
  a redundant row `r i ∈ span(R(Gv,q)-rows) ⊔ span(r '' {j≠i})`, i.e. a vanishing
  combination of the `Gv`-rows + other `ab`-rows with `λ_{(ab)i*}=1`.
- **The seam (KT eq. (6.26), the build):** `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)`.
  The `(ab)j`-row of `R(G_v^{ab},q)` ↔ the `(vb)j`-row of `R(G,p₁)` (KT (6.16)); the
  `ej`-rows (`e∈Ev`) correspond directly. Transporting the combination gives the new
  `(vb)i*`-row `w` (eq. (6.27)) in `span(R(G,p₁)-rows)`.
- **`V∖{v}` part of `w` vanishes:** those columns reproduce the `R(G_v^{ab},q)`-rows,
  which eq. (6.24) sums to 0.
- **`v`-column part:** `R(G,p₁;Ev,v)=0` (the `Ev`-edges avoid `v`, KT (6.16)), so only
  the `(vb)j`-rows contribute, `= Σⱼ λ_{(ab)j} rⱼ(p₁(vb)) = Σⱼ λ_{(ab)j} rⱼ(q(ab))`
  (using `p₁(vb)=q(ab)`, the eq.-(6.12) degenerate placement).
- The eq.-(6.28) leaf (green) then certifies `w` as a pure `v`-column row.

KT typo noted (not blocking): p. 684 says the seam restricts to `E∖{vb}`, p. 685 says
`E∖{va}`; the substance (the `V∖{v}` columns reproduce `R(G_v^{ab},q)`) is the same.
No new BlueprintExposition ledger entry: this is a *planned* node-cut matching KT's
stated argument, not a reroute surfacing a new insight (ledger inclusion = KT-math
reroute, not planned scoping).

## Red-node consistency gate — recon verdict (2026-06-06, this commit)

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

- [x] `BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` — eq. (6.28)
  column-support core (green, e8e7753). **Blueprint node `lem:case-III-vanish-off-column`
  added this commit (green).**
- [x] Constructibility recon on `w`'s row operation (KT eqs. (6.24)→(6.28)) — done
  this commit; arithmetic closes (verdict above). Node `lem:case-III-candidate-row`
  cut red.
- [x] **The seam identity** `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` (KT eq. (6.26)) —
  `PanelHingeFramework.ofNormals_panelRow_eq_of_ends_seed_eq` (`PanelHinge.lean`,
  axiom-clean). Per-row form; `lem:case-III-seam` (green). **Caveat:** covers only the
  `E_v`-rows (literal functional equality); the `(vb)↔(ab)` step needs eq. (6.43) — see
  *Decisions*.
- [x] **The eqs. (6.24)/(6.25) extraction** — `exists_redundant_panelRow_ab_decomposition`
  (`CaseI.lean`, axiom-clean) — the redundant `ab`-row `= wGv + wOther` (`Submodule.mem_sup`
  on the eq.-(6.23) membership), `λ_{(ab)i*}=1`. Blueprint node
  `lem:case-III-redundant-decomposition` (green).
- [x] **KT eq. (6.43)** — `exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`,
  axiom-clean): the `a`-column block of the eq.-(6.24) vanishing combination is `0`
  (`(wGv + wOther − r i).comp (single a) = 0`, all `a`). Blueprint node
  `lem:case-III-acolumn-zero` (green).
- [ ] **The eq.-(6.27) `w`-assembly** — transport the decomposition across the seam, off-`v`
  vanishing now from seam-on-`E_v` + eq. (6.43)-on-`a`-block, then the eq.-(6.28) leaf →
  `lem:case-III-candidate-row` green. **Next concrete commit.**
- [ ] **The conditional `D`-row block** — `w` (a pure `v`-column row by eq. (6.28))
  extends the `va`-block to a `D`-row new block (`linearIndependent_sum_pinned_block`),
  giving a `D(|V|−1)`-family **conditional** on the top-left `D×D` block being full
  rank (eq. (6.29)).
- [ ] **Claim 6.12** — the `D`-candidate extensor-span disjunction (de-risked: bottoms
  on the green Phase-17 Lemma 2.1 `omitTwoExtensor_linearIndependent`; the degree-2
  eq. (6.44) forces all candidates to test the same `r ∈ ℝ⁶`, which ⟂ all `d+1`
  generic-panel extensors must vanish — contradiction, picking the full-rank candidate).
- [ ] **Flip** `lem:case-II-realization` (+ the `d=3` half of `lem:case-III`) green
  once the assembly lands. Candidate-completion subsection nodes
  (`lem:case-III-vanish-off-column`, `lem:case-III-seam`,
  `lem:case-III-redundant-decomposition` green; `lem:case-III-candidate-row` red) are in
  `case-iii.tex` as of this commit; the Claim-6.12 disjunction node is still to add.

## Blockers / open questions

- **The off-`v` vanishing is two facts, not one (eq.-(6.43) finding).** KT eq. (6.27)→(6.28)'s
  "`V∖{v}` part vanishes from the seam + eq. (6.24)" needs *also* KT eq. (6.43): the per-edge seam
  only transports the `E_v`-rows verbatim; the `(vb)j`-row and `(ab)j`-row restricted to `V∖{v}`
  differ by the `a`-block `r_j(·a)`, killed only by the `a`-block of eq. (6.24) being `0` (eq. 6.43,
  now green: `…_acolumn_zero`). **Next commit = the eq.-(6.27) `w`-assembly** (the open crux of
  `lem:case-III-candidate-row`); the remaining pieces after it (the pin-a-body `D`-row block; the
  Lemma-2.1 disjunction) are bounded.
- **Recurring Lean trap (carry from 22a–d, FRICTION):** heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps can
  `isDefEq`-timeout — make the two frameworks *syntactically* equal before `convert`;
  transfer rigidity via a `mem_infinitesimalMotions` round-trip. Bites in the
  candidate-completion assembly.

## Hand-off / next phase

**Next concrete commit: the eq.-(6.27) `w`-assembly — land `lem:case-III-candidate-row` green.**
All four inputs are now green (eqs.-(6.24)/(6.25) decomposition
`exists_redundant_panelRow_ab_decomposition`; eq.-(6.43) `a`-block vanishing
`…_acolumn_zero`; per-edge seam `ofNormals_panelRow_eq_of_ends_seed_eq`; eq.-(6.28) leaf
`dualMap_eq_comp_single_proj_of_vanish_off`). Build the transported row
`w = Σⱼ λ_{(ab)j} hingeRow v b r_j + Σ_{E_v} λ_{ej}(…)` in `span(R(G,p₁)-rows)` at the eq.-(6.12)
degenerate placement `p₁` (`p₁(vb)=q(ab)`); over `V∖{v}`, the `(vb)j`-rows differ from the `(ab)j`-rows
by the `a`-block `r_j(·a)`, so `w`'s `V∖{v}` part = the eq.-(6.24) sum (= 0) minus the ab-part `a`-block
(killed by eq. (6.43)) = 0; then `dualMap_eq_comp_single_proj_of_vanish_off` certifies `w` is a pure
`v`-column row. **Recurring trap (Blockers):** make the two frameworks syntactically equal before
`convert`; transfer rigidity via a `mem_infinitesimalMotions` round-trip.

The follow-on after the `w`-assembly: the conditional `D`-row block (eq. (6.29),
extending `va` via `linearIndependent_sum_pinned_block`), then Claim 6.12.

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` (the alg-independence tracker,
risk #8 — add a row if 22e introduces a new alg-independence use).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **eq. (6.43) — `a`-block of eq. (6.24) is `0` (2026-06-06).** Landed
  `exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`, axiom-clean):
  precomposing the eq.-(6.24) zero combination `g = wGv + wOther − r i*` with the column injection
  `single a` is `0` for every body `a` (`rw [hsum, sub_self, LinearMap.zero_comp]`). The off-`v`
  vanishing finding (the per-edge seam transports only `E_v`-rows; the `(vb)j` vs `(ab)j` rows
  differ over `V∖{v}` by the `a`-block `r_j(·a)`, so `w`'s `V∖{v}` part = eq.-(6.24) sum (= 0)
  minus that ab-part `a`-block) is what makes this fact load-bearing for the `w`-assembly. Blueprint
  node `lem:case-III-acolumn-zero` (green); BlueprintExposition capture entry stands (KT-math (a)).
- **eqs. (6.24)/(6.25) extraction (2026-06-06).** Landed
  `exists_redundant_panelRow_ab_decomposition` (`CaseI.lean`, axiom-clean): a one-line
  `Submodule.mem_sup.1` unwind of the eq.-(6.23) redundant-row *membership* into the
  functional-identity decomposition `r i* = wGv + wOther` (`λ_{(ab)i*}=1`). Blueprint node
  `lem:case-III-redundant-decomposition` (green), wired into the candidate-row + `lem:case-III`.
- **Settled earlier (2026-06-06), now one-lined.** Open recon (target red nodes read,
  supersession gate clean, `d=3`-assembly/Phase-23 boundaries confirmed); candidate-completion
  node-cut (`lem:case-III-vanish-off-column` + `-candidate-row`); seam build
  `ofNormals_panelRow_eq_of_ends_seed_eq` (`lem:case-III-seam`, green) — chose the per-row
  form (a `panelRow` reads only `ends`/index/extensor, graph never enters) to sidestep the
  `ofNormals`/`withGraph` `IsInfinitesimallyRigidOn`-`convert` defeq-timeout (Blockers).
