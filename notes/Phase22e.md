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

**BLOCKED on a route finding (2026-06-06): the planned `w`-assembly does not close as
designed — the off-`v` vanishing comes from KT's eqs. (6.14)–(6.16) *column operation*
(add column `v` to column `a`), NOT from the per-edge seam + eq. (6.43).** Worked the
arithmetic of `lem:case-III-candidate-row` against KT pp. 681–690 end-to-end (eqs.
(6.12)–(6.30) + (6.42)–(6.43)). The candidate row is `w = hingeRow v a ρ_g` (`ρ_g = Σⱼ
λ_{(ab)j} r_j ≠ 0`), supported on the *two* columns `v` and `a`: `g = 0` forces `wGv =
−hingeRow a b ρ_g`, so `w = wGv + hingeRow v b ρ_g = hingeRow v b ρ_g − hingeRow a b ρ_g =
hingeRow v a ρ_g`. In the natural frame `w S = ρ_g(S v − S a)`, which does **not** vanish
for `S v = 0` (it is `−ρ_g(S a)`, nonzero in general). It becomes pure `v`-column
`w_new S = ρ_g(S v)` only after KT's column op `col_a += col_v` (eqs. (6.14)→(6.15)), i.e.
precomposing with the automorphism `Φ S = update S v (S v + S a)`: `(hingeRow v a ρ_g)(Φ S)
= ρ_g(S v + S a − S a) = ρ_g(S v)`. The per-edge seam transports `E_v`-rows verbatim but the
`vb` vs `ab` rows differ over `V∖{v}` by the `a`-column; that residual is absorbed by the
column op, **not** by eq. (6.43). **eq. (6.43) is a Claim-6.12 fact** (KT p. 690, the
`M3`-case extensor-orthogonality), *not* the candidate-row vanishing fact: the green
`…_acolumn_zero` (= `g.comp(single a)=0`, trivially `g=0`) is real and reusable there, but it
is **not** the load-bearing input for `lem:case-III-candidate-row` the blueprint/notes claimed.

**Next concrete commit (re-scoped):** model the column operation. Add a `Φ`-style
change-of-variables automorphism on `α → ScrewSpace k` (`col_a += col_v`) and restate
`lem:case-III-candidate-row` so `w = (hingeRow v a ρ_g) ∘ Φ` is a pure `v`-column row in the
column-operated frame; the downstream pin-block (eq. (6.29)) and `lem:case-II-realization`
then live in that frame too. This is a **design-level reroute of the candidate-completion
node**, not the mechanical build the prior hand-off assumed — see *Blockers*.

**Landed earlier this sub-phase (KT eq. (6.43), the `a`-column block of eq. (6.24) is `0`):**
`BodyHingeFramework.exists_redundant_panelRow_ab_decomposition_acolumn_zero` (`CaseI.lean`,
axiom-clean): the vanishing combination `g := wGv + wOther − r i*` (= 0) precomposed with
`single a` is `0` for every body `a` (`rw [hsum, sub_self, LinearMap.zero_comp]`). Blueprint
node `lem:case-III-acolumn-zero` (green). **Re-scoped (this commit): it feeds Claim 6.12
(`M3`-case), not the candidate-row vanishing.**

## Constructibility recon — `w`'s row operation (KT eqs. (6.12)→(6.28)); route finding

Read KT §6.4.1 pp. 681–690 (eqs. (6.12)–(6.30), (6.42)–(6.43)) end-to-end against the green
Lean. **Verdict: the planned route is mathematically wrong about the vanishing mechanism;
the node needs the column operation. BLOCKED pending that reroute.**

- Claim 6.11 / eq. (6.23) → the green `exists_redundant_panelRow_ab_of_finrank_eq` gives the
  redundant `ab`-row, decomposed (green `…_decomposition`) as `r i* = wGv + wOther`, the
  vanishing combination `g = wGv + wOther − r i* = 0` (eq. (6.24)/(6.25), `λ_{(ab)i*}=1`).
- **The transported row** `w = Σⱼ λ_{(ab)j} hingeRow v b r_j + Σ_{E_v} λ_{ej}(…)` simplifies
  (via `g = 0`, project convention `vb`-reproduces-`ab`) to `w = hingeRow v a ρ_g` with
  `ρ_g = Σⱼ λ_{(ab)j} r_j ≠ 0`. Supported on columns `v` AND `a`.
- **The vanishing-off-`v` is NOT from the seam + eq. (6.43).** In the natural frame
  `w S = ρ_g(S v − S a)`; for `S v = 0` this is `−ρ_g(S a) ≠ 0`. KT gets `w` pure-`v` only
  via the eqs. (6.14)→(6.15) **column operation** `col_a += col_v` (`Φ S = update S v (S v +
  S a)`): `w(Φ S) = ρ_g(S v)`. The `a`-column residual is absorbed by the column op.
- **eq. (6.43) belongs to Claim 6.12** (KT p. 690), the `M3`-case extensor-orthogonality — it
  is `g`'s `a`-column = 0, trivially true since `g = 0`, consumed there, not in the
  candidate-row vanishing. The green `…_acolumn_zero` is sound but mis-wired in the prior plan.
- KT typo (p. 684 `E∖{vb}` vs p. 685 `E∖{va}`) is not the issue; the issue is the column op
  being silently elided in the project's per-edge-seam plan.

BlueprintExposition ledger: add a `(c)` entry (a reroute surfacing a stable KT-math insight —
the column op is load-bearing and was missed) at the candidate-completion node, written up at
phase close once the rerouted node is green.

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
- [x] Constructibility recon on `w`'s row operation (KT eqs. (6.12)→(6.28)) — done; the
  recon found the planned route wrong (the column op, not the seam + eq. (6.43), gives the
  vanishing). Node `lem:case-III-candidate-row` stays red. **BLOCKED — see *Current state*.**
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
- [ ] **The column-operation device + `w`-assembly (RE-SCOPED, BLOCKED).** Add the `col_a +=
  col_v` automorphism `Φ` on `α → ScrewSpace k`; `w = (hingeRow v a ρ_g) ∘ Φ` is pure
  `v`-column. Restate `lem:case-III-candidate-row` in the column-operated frame and thread it
  to the pin-block + `lem:case-II-realization`. **Next concrete commit (design-level reroute).**
- [ ] **The conditional `D`-row block** — `w` (pure `v`-column in the column-operated frame)
  extends the `va`-block to a `D`-row new block (`linearIndependent_sum_pinned_block`),
  giving a `D(|V|−1)`-family **conditional** on the top-left `D×D` block being full
  rank (eq. (6.29)). The pin-block must consume the column-operated rows.
- [ ] **Claim 6.12** — the `D`-candidate extensor-span disjunction (de-risked: bottoms
  on the green Phase-17 Lemma 2.1 `omitTwoExtensor_linearIndependent`; the degree-2
  eq. (6.44) forces all candidates to test the same `r ∈ ℝ⁶`, which ⟂ all `d+1`
  generic-panel extensors must vanish — contradiction, picking the full-rank candidate).
- [ ] **Flip** `lem:case-II-realization` (+ the `d=3` half of `lem:case-III`) green
  once the rerouted column-op assembly lands. Candidate-completion subsection nodes
  (`lem:case-III-vanish-off-column`, `lem:case-III-seam`,
  `lem:case-III-redundant-decomposition`, `lem:case-III-acolumn-zero` green;
  `lem:case-III-candidate-row` red, needs the column op) are in `case-iii.tex`; the
  Claim-6.12 disjunction node is still to add.

## Blockers / open questions

- **BLOCKED (2026-06-06): the candidate-row vanishing needs the column op, not the seam +
  eq. (6.43).** The recon (above) found the planned `w`-assembly cannot close: `w = hingeRow v a
  ρ_g` is supported on columns `v` AND `a`, so in the natural frame it does not vanish off `v`
  (`w S = ρ_g(S v − S a)`, `= −ρ_g(S a) ≠ 0` at `S v = 0`). KT's vanishing comes from the eqs.
  (6.14)→(6.15) column operation `col_a += col_v` (`Φ S = update S v (S v + S a)`), giving
  `w(Φ S) = ρ_g(S v)`. eq. (6.43) is a Claim-6.12 fact, NOT the vanishing input. **To unblock:**
  add a `Φ`-style change-of-variables automorphism on `α → ScrewSpace k` and restate
  `lem:case-III-candidate-row` (and the downstream pin-block / `lem:case-II-realization`) in the
  column-operated frame. The green `dualMap_eq_comp_single_proj_of_vanish_off`, seam, and
  decomposition leaves are still reusable; the candidate-row node's *statement* and the blueprint
  caveat (which both currently describe the broken seam-only route) need rewriting.
- **Recurring Lean trap (carry from 22a–d, FRICTION):** heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps can
  `isDefEq`-timeout — make the two frameworks *syntactically* equal before `convert`;
  transfer rigidity via a `mem_infinitesimalMotions` round-trip. Bites in the
  candidate-completion assembly.

## Hand-off / next phase

**Next concrete commit: model the eqs. (6.14)–(6.16) column operation, then re-scope
`lem:case-III-candidate-row`.** The prior hand-off (a mechanical `w`-assembly from the
per-edge seam + eq. (6.43)) is wrong — see *Blockers* and the recon. The candidate row is
`w = hingeRow v a ρ_g` (`ρ_g = Σⱼ λ_{(ab)j} r_j`), pure `v`-column **only after** precomposing
with `Φ S = update S v (S v + S a)`. The reroute: (1) define `Φ` (a `≃ₗ` automorphism, `col_a +=
col_v`) and the column-operated row space `(R(G,p₁)-rows) ∘ Φ`; (2) prove `(hingeRow v a ρ_g) ∘ Φ
= hingeRow-on-`v`-only`, i.e. vanishes off `v` — then `dualMap_eq_comp_single_proj_of_vanish_off`
applies; (3) restate `lem:case-III-candidate-row`'s blueprint node + Lean to live in the
column-operated frame, and confirm the downstream pin-block (eq. (6.29),
`linearIndependent_sum_pinned_block`) + `lem:case-II-realization` accept that frame (rank is
column-op-invariant). The green seam / decomposition / `…_acolumn_zero` / vanish-off-column
leaves are all reusable; `…_acolumn_zero` re-targets to Claim 6.12. **Recurring trap
(Blockers):** make the two frameworks syntactically equal before `convert`; transfer rigidity via
a `mem_infinitesimalMotions` round-trip.

The follow-on after the `w`-assembly: the conditional `D`-row block (eq. (6.29),
extending `va` via `linearIndependent_sum_pinned_block`), then Claim 6.12.

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` (the alg-independence tracker,
risk #8 — add a row if 22e introduces a new alg-independence use).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Candidate-row route finding — the column op is load-bearing, the seam alone is not
  (2026-06-06).** A constructibility recon against KT pp. 681–690 found the planned
  `lem:case-III-candidate-row` route (per-edge seam + eq. (6.43) → off-`v` vanishing) is
  mathematically wrong: `w = hingeRow v a ρ_g` (`ρ_g = Σ λ_{(ab)j} r_j ≠ 0`) is supported on
  columns `v` AND `a`, so `w S = ρ_g(S v − S a) ≠ 0` at `S v = 0`. The off-`v` vanishing is KT's
  eqs. (6.14)–(6.15) column op `col_a += col_v` (`Φ S = update S v (S v + S a)`, `w(Φ S) =
  ρ_g(S v)`), and eq. (6.43) is a Claim-6.12 fact, not this one. **BLOCKED** pending modelling
  `Φ` + restating the node in the column-operated frame (*Current state*, *Blockers*, *Hand-off*).
  Updated `case-iii.tex` (candidate-row proof caveat + preamble) to the corrected route; the
  green leaves (seam, decomposition, vanish-off-column, `…_acolumn_zero`) are all reusable.
  Promoted the lesson to FRICTION (constructibility recon must verify the *mechanism* of a claimed
  vanishing, not just the count). BlueprintExposition: a `(c)` ledger entry to write at phase close.
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
