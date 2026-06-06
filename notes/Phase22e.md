# Phase 22e — candidate-completion + Claim 6.12 (KT §6.4.1, eqs. (6.24)–(6.45)) (work log)

**Status:** in progress (opened 2026-06-06 design-pass-first; opening recon +
eq.-(6.28) blueprint node + `w` constructibility recon + `w` node-cut + the
seam-identity build + the eqs.-(6.24)/(6.25) decomposition + the eq.-(6.43)
`a`-block vanishing + the eqs.-(6.14)–(6.16) column-op device + the eq.-(6.29)
conditional `D`-row block landed).
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

**Next concrete commit: assemble the transported combination into `w` (eq. (6.27) transport).** The
conditional `D`-row block (eq. (6.29)) is now green (this commit), so every candidate-row *leaf* is
in place (decomposition, seam, column op, vanish-off, conditional block). What remains for
`lem:case-III-candidate-row` proper: thread the green leaves into the eq.-(6.27)/(6.28) row `w`
itself — at the eq.-(6.12) placement `p₁` transport the redundant-`ab`-row combination across the
seam (`ofNormals_panelRow_eq_of_ends_seed_eq`), collapse it via `r i* = wGv + wOther` to
`w = hingeRow v a ρ_g`, then column-op (`columnOp` + `hingeRow_comp_columnOp_vanish_off`) and apply
`dualMap_eq_comp_single_proj_of_vanish_off` to get the pure-`v`-column row, finally feed it to the
new `linearIndependent_sum_pinned_block_augment`. **Recurring defeq-timeout trap (*Blockers*)** bites
in the `ofNormals`/`withGraph` graph-swap of the transport. After that: Claim 6.12.

**Landed this commit (the eq.-(6.29) conditional `D`-row block):**
- `BodyHingeFramework.linearIndependent_sum_pinned_block_augment` (`RigidityMatrix.lean`,
  axiom-clean): augments `linearIndependent_sum_pinned_block` (N7b-3) at index `ιn ⊕ Unit` — the
  `va`-block's `D−1` rows `rn` plus the operated pure-`v`-column row `w`, jointly independent with
  the old block `ro` (vanishing at `update 0 v`), **conditional** on the *augmented* pinned new
  block `Sum.elim (rn ∘ single v) (w ∘ single v)` being independent on `v`'s `D`-dim column (KT
  eq. (6.29) top-left `D×D` full rank). `w` joins the `hnewpin` slot (it's a new-block row, pinned
  through `v`'s column — no `hold` vanishing needed); a `funext`/`cases <;> rfl` bridges the
  `Sum.elim`-of-`.comp` vs `.comp`-of-`Sum.elim` shapes. The `hwvanish` (pure-`v`-column) property
  is the *caller's* responsibility — it is carried into the augmented-pinned hypothesis, so the
  lemma itself takes only the four pin-block-style inputs.
- Blueprint node `lem:case-III-conditional-block` (green), wired into `lem:case-III-candidate-row`'s
  `\uses` (candidate-row stays red — what remains is the `w`-assembly proper).

**Landed earlier this sub-phase (KT eq. (6.43), the `a`-column block of eq. (6.24) is `0`):**
`BodyHingeFramework.exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`,
axiom-clean): the vanishing combination `g := wGv + wOther − r i*` (= 0) precomposed with
`single a` is `0` for every body `a`. Blueprint node `lem:case-III-acolumn-zero` (green). A
Claim-6.12 input (`M3`-case), not the candidate-row vanishing.

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

- [x] `BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` — eq. (6.28)
  column-support core (green, e8e7753). **Blueprint node `lem:case-III-vanish-off-column`
  added this commit (green).**
- [x] Constructibility recon on `w`'s row operation (KT eqs. (6.12)→(6.28)) — done; found
  the column op (not the seam + eq. (6.43)) gives the vanishing. Acted on this commit.
- [x] **The seam identity** `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` (KT eq. (6.26)) —
  `PanelHingeFramework.ofNormals_panelRow_eq_of_ends_seed_eq` (`PanelHinge.lean`,
  axiom-clean). Per-row form; `lem:case-III-seam` (green). **Re-scoped:** transports the
  `E_v`-rows verbatim; the `(vb)↔(ab)` step is the column op, not this seam.
- [x] **The eqs. (6.24)/(6.25) extraction** — `exists_redundant_panelRow_ab_decomposition`
  (`CaseI.lean`, axiom-clean) — the redundant `ab`-row `= wGv + wOther` (`Submodule.mem_sup`
  on the eq.-(6.23) membership), `λ_{(ab)i*}=1`. Blueprint node
  `lem:case-III-redundant-decomposition` (green).
- [x] **KT eq. (6.43)** — `exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`,
  axiom-clean): the `a`-column block of the eq.-(6.24) vanishing combination is `0`
  (`(wGv + wOther − r i).comp (single a) = 0`, all `a`). Blueprint node
  `lem:case-III-acolumn-zero` (green). **Re-scoped: a Claim-6.12 input (`M3`-case), not the
  candidate-row vanishing.**
- [x] **The column-operation device (KT eqs. (6.14)–(6.16)).** `BodyHingeFramework.columnOp hva`
  (the `col_a += col_v` `≃ₗ` automorphism `Φ S = update S v (S v + S a)`, `v ≠ a`) +
  `hingeRow_comp_columnOp_apply`/`…_vanish_off` (`(hingeRow v a ρ)(Φ S) = ρ(S v)`, vanishes off
  `v`). `RigidityMatrix.lean`, axiom-clean. Blueprint node `lem:case-III-columnop` (green). This
  unblocks the candidate-row reroute; the `w`-assembly itself stays open (next two items).
- [x] **The conditional `D`-row block** — `linearIndependent_sum_pinned_block_augment`
  (`RigidityMatrix.lean`, axiom-clean): augments the pin-block (N7b-3) at `ιn ⊕ Unit` with the
  operated pure-`v`-column row `w`, giving a `D(|V|−1)`-family **conditional** on the augmented
  pinned new block being independent (eq. (6.29) top-left `D×D` full rank). Blueprint node
  `lem:case-III-conditional-block` (green).
- [ ] **Assemble the transported combination into `w`** (eq. (6.27) transport) — the `w`-assembly
  proper, threading the green leaves (decomposition, seam, column op, vanish-off, conditional
  block) into the eq.-(6.28) row. **Next concrete commit.**
- [ ] **Claim 6.12** — the `D`-candidate extensor-span disjunction (de-risked: bottoms
  on the green Phase-17 Lemma 2.1 `omitTwoExtensor_linearIndependent`; the degree-2
  eq. (6.44) forces all candidates to test the same `r ∈ ℝ⁶`, which ⟂ all `d+1`
  generic-panel extensors must vanish — contradiction, picking the full-rank candidate).
- [ ] **Flip** `lem:case-II-realization` (+ the `d=3` half of `lem:case-III`) green
  once the `w`-assembly lands. Candidate-completion subsection nodes
  (`lem:case-III-vanish-off-column`, `lem:case-III-columnop`, `lem:case-III-seam`,
  `lem:case-III-redundant-decomposition`, `lem:case-III-acolumn-zero`,
  `lem:case-III-conditional-block` green; `lem:case-III-candidate-row` red, needs the
  `w`-assembly) are in `case-iii.tex`; the Claim-6.12 disjunction node is still to add.

## Blockers / open questions

- **Recurring Lean trap (carry from 22a–d, FRICTION):** heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps can
  `isDefEq`-timeout — make the two frameworks *syntactically* equal before `convert`;
  transfer rigidity via a `mem_infinitesimalMotions` round-trip. Bites in the
  candidate-completion assembly.

## Hand-off / next phase

**Next concrete commit: assemble the transported combination into `w` (eq. (6.27) transport).** Every
candidate-row leaf is now green (decomposition, seam, column op, vanish-off, conditional block); what
remains for `lem:case-III-candidate-row` proper is the `w`-assembly. At the eq.-(6.12) placement `p₁`:
transport the redundant-`ab`-row combination (`exists_redundant_panelRow_ab_decomposition`) across
the seam (`ofNormals_panelRow_eq_of_ends_seed_eq`), substitute `r i* = wGv + wOther` to collapse it to
`w = hingeRow v a ρ_g`, then column-op (`columnOp` + `hingeRow_comp_columnOp_vanish_off`) and apply
`dualMap_eq_comp_single_proj_of_vanish_off` for the pure-`v`-column row, finally feed it to
`linearIndependent_sum_pinned_block_augment`. **Recurring trap (Blockers):** the `ofNormals`/`withGraph`
graph-swap in the transport — make the two frameworks syntactically equal before `convert`; transfer
rigidity via a `mem_infinitesimalMotions` round-trip.

The follow-on: Claim 6.12, then flip `lem:case-II-realization` + the `d=3` half of `lem:case-III`
green.

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` (the alg-independence tracker,
risk #8 — add a row if 22e introduces a new alg-independence use).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **The eq. (6.29) conditional `D`-row block (2026-06-06).** Landed
  `linearIndependent_sum_pinned_block_augment` (`RigidityMatrix.lean`, axiom-clean): augments
  N7b-3's `linearIndependent_sum_pinned_block` at index `ιn ⊕ Unit` with the operated
  pure-`v`-column row `w`. `w` is a *new-block* row (pinned through `v`'s column), so it joins `rn`
  in the `hnewpin` slot — no `hold` vanishing — and the lemma's only non-pin-block input is the
  *augmented* pinned independence `Sum.elim (rn ∘ single v) (w ∘ single v)` (KT eq. (6.29) top-left
  `D×D` full rank, the **conditional**). `hwvanish` (pure-`v`-column) is the *caller's*
  responsibility, carried into that augmented hypothesis, so I dropped it as an explicit arg
  (unused → lint). Proof = `linearIndependent_sum_pinned_block` + a `funext`/`cases <;> rfl` bridging
  `Sum.elim`-of-`.comp` vs `.comp`-of-`Sum.elim`. Blueprint node `lem:case-III-conditional-block`
  (green), wired into `lem:case-III-candidate-row`'s `\uses`.
- **The eqs. (6.14)–(6.16) column-op device (2026-06-06).** Landed `BodyHingeFramework.columnOp hva`
  (`RigidityMatrix.lean`, axiom-clean): the `col_a += col_v` `≃ₗ` automorphism `Φ S = update S v
  (S v + S a)` (inverse `update S v (S v − S a)`, both directions need `v ≠ a` so the `v`-update
  leaves coord `a` fixed), modelled as the *dual* substitution on the screw assignment (rows read
  relative screws). `@[simps! apply]` for the apply lemma; `left_inv`/`right_inv` need a `simp only`
  to beta-reduce the field lambda before the `Function.update_self`/`_of_ne` `rw` chain fires.
  `hingeRow_comp_columnOp_apply`/`…_vanish_off`: `(hingeRow v a ρ)(Φ S) = ρ(S v)`, so it kills every
  `S v = 0` — the off-`v` vanishing `dualMap_eq_comp_single_proj_of_vanish_off` consumes. Blueprint
  node `lem:case-III-columnop` (green), wired into `lem:case-III-candidate-row`'s `\uses`. Unblocks
  the candidate-row reroute (the column op was the missing leaf); the `w`-assembly stays open.
- **Candidate-row route finding — the column op is load-bearing, the seam alone is not
  (2026-06-06; acted on).** A recon against KT pp. 681–690 found the planned route (per-edge seam +
  eq. (6.43) → off-`v` vanishing) wrong: `w = hingeRow v a ρ_g` (`ρ_g = Σ λ_{(ab)j} r_j ≠ 0`) is
  supported on columns `v` AND `a` (`w S = ρ_g(S v − S a) ≠ 0` at `S v = 0`); the off-`v` vanishing
  is KT's eqs. (6.14)–(6.16) column op (now `columnOp`, above), and eq. (6.43) is a Claim-6.12 fact.
  Promoted the lesson to FRICTION (a recon must verify the *mechanism* of a claimed vanishing, not
  just the count). BlueprintExposition: a `(c)` ledger entry to write at phase close.
- **eq. (6.43) — `a`-block of eq. (6.24) is `0` (2026-06-06).** Landed
  `exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`, axiom-clean):
  precomposing the eq.-(6.24) zero combination `g = wGv + wOther − r i*` with the column injection
  `single a` is `0` for every body `a` (`rw [hsum, sub_self, LinearMap.zero_comp]`). **Re-scoped
  (the route finding above): this is a Claim-6.12 input (`M3`-case extensor-orthogonality), NOT
  the candidate-row vanishing fact.** Blueprint node `lem:case-III-acolumn-zero` (green); a
  BlueprintExposition entry stands but moves to the Claim-6.12 node (KT-math (a)).
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
