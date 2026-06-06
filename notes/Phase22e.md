# Phase 22e — candidate-completion + Claim 6.12 (KT §6.4.1, eqs. (6.24)–(6.45)) (work log)

**Status:** in progress (opened 2026-06-06 design-pass-first; opening recon landed,
this commit). Successor to 22d, the next chunk of Case III at `d=3` (KT §6.4.1,
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

**This commit is the opening recon only — no build started** (per the open mandate:
the first leaf build is the next commit). The recon read the target red nodes
end-to-end (statement AND proof) and confirms them self-consistent and free of any
live-route reference to a superseded node (verdict below). The leaf-most-first build
plan is in *Hand-off* below.

The seam from 22d is in hand: the eq. (6.28) column-support LA core
`BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`,
landed commit e8e7753, green + axiom-clean) is 22e's **first leaf, already green** —
a rigidity row vanishing on every screw assignment supported off `v` factors as
`(f ∘ₗ single v) ∘ₗ proj v`, a pure `v`-column row. It is the structural input that
turns the row-op output `w` (whose `V∖{v}` part is zero) into the `v`-column row that
joins the `va`-block in `linearIndependent_sum_pinned_block`'s `D`-row-capable
pin-a-body split. It carries **no blueprint node yet** — that is 22e's to add (a leaf
under the candidate-completion assembly), with the rest of the chain.

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
  column-support core (green, landed commit e8e7753 under 22d's tail). **First leaf.**
  Needs a blueprint node (a leaf under the candidate-completion assembly).
- [ ] **The row-op construction of `w`** (KT p. 680, eqs. (6.24)→(6.27)) — the open
  crux. Lift the green redundant `ab`-row's combination
  (`exists_redundant_panelRow_ab_of_finrank_eq`) to `R(G,p₁)` via
  `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)`, producing `w ∈ span(R(G,p₁)-rows)` vanishing
  off `v`. Its eq. (6.18)/(6.22) finrank hypotheses are wired from the green
  seed-rank-bridge / rank-attainment via rank-nullity `dim Z + dim span(rigidityRows)
  = D|α|`. Research-shaped — decompose math-first before cutting nodes.
- [ ] **The conditional `D`-row block** — `w` (now a pure `v`-column row by eq. (6.28))
  extends the `va`-block to a `D`-row new block (`linearIndependent_sum_pinned_block`),
  giving a `D(|V|−1)`-family **conditional** on the top-left `D×D` block being full
  rank (eq. (6.29)).
- [ ] **Claim 6.12** — the `D`-candidate extensor-span disjunction (de-risked: bottoms
  on the green Phase-17 Lemma 2.1 `omitTwoExtensor_linearIndependent`; the degree-2
  eq. (6.44) forces all candidates to test the same `r ∈ ℝ⁶`, which ⟂ all `d+1`
  generic-panel extensors must vanish — contradiction, picking the full-rank candidate).
- [ ] **Flip** `lem:case-II-realization` (+ the `d=3` half of `lem:case-III`) green;
  add the eq.-(6.28)/-(6.29) / Claim-6.12 blueprint nodes in `case-ii.tex` /
  `case-iii.tex` in step with the Lean.

## Blockers / open questions

- The row-op construction of `w` is the one genuinely research-shaped piece; everything
  else (eq. (6.28) leaf, the pin-a-body block, the Lemma-2.1 disjunction) is bounded.
  Decompose `w`'s construction math-first (the constructibility recon) before scheduling
  it as a build — confirm the eq. (6.24)→(6.27) row operation's arithmetic closes
  against `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` before committing to a node cut.
- **Recurring Lean trap (carry from 22a–d, FRICTION):** heavy
  `IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps can
  `isDefEq`-timeout — make the two frameworks *syntactically* equal before `convert`;
  transfer rigidity via a `mem_infinitesimalMotions` round-trip. Bites in the
  candidate-completion assembly.

## Hand-off / next phase

**Recon verdict (this commit): build is safe to scope; the target red nodes are
self-consistent and the supersession gate is clean (see *Red-node consistency gate*
above).**

**Leaf-most-first build plan (the next concrete commit):** the eq. (6.28) column-%
support leaf is already green (commit e8e7753) — the *first build commit* gives it its
blueprint node (a leaf under the candidate-completion assembly in `case-ii.tex`), then
the next research-shaped step is the **row-op construction of `w`** (KT eqs.
(6.24)→(6.27)), which should be **decomposed math-first** (constructibility recon
against `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)`) before any node is cut. So the
smallest forward commit is: blueprint-node the green eq. (6.28) leaf + run the
constructibility recon on `w`'s construction (docs-only), landing the node-cut for `w`.

Downstream (still deferred, unlettered): the `d=3` assembly
(`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + Case-I wiring);
then general-`d` is **Phase 23**. KT math: `notes/Phase22d.md` *Hand-off*, KT §6.4.1
(eqs. (6.24)–(6.45)); `notes/AlgebraicIndependence.md` (the alg-independence tracker,
risk #8 — add a row if 22e introduces a new alg-independence use).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Open recon (2026-06-06).** Read the target red nodes end-to-end; ran the
  supersession gate clean; confirmed the existing planned boundaries (the `d=3`
  assembly + general-`d` Phase 23 stay separate). The eq. (6.28) leaf (e8e7753) folds
  in as the first green leaf; it needs a blueprint node, which 22e adds with the rest.
