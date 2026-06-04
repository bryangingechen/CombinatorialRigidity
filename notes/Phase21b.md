# Phase 21b — Genericity device (work log)

**Status:** ✓ Complete (opened 2026-06-03; closed 2026-06-04 on the device
deliverable). The phase's named target — the **genericity device** (Claim
6.4/6.9) — plus the genericity-free accounting iffs, the `V(G)`-relative count
bridges, and the reusable row/glue infrastructure are all **green and
axiom-clean** {propext, Classical.choice, Quot.sound}. The **realization
producers** (Case I splice; Case II split) are **re-scoped to Phases 22–23**
after a math-first feasibility pass (2026-06-04) found the Case-II producer is
actually KT Case-III content. See *The realization-layer re-scope* below.

Sub-phase scoped out of Phase 21 (user decision, risk #4/#7) — the **analytic
sibling** of the Phase-21a meet. The device lifts a rank attained at one
realization to the same rank at a generic point (Claim 6.4/6.9), discharging the
genericity black-box the Phase-21 accounting nodes carried as `hglue`/`hspan`/
`hgen`.

Forward-mode: the authoritative node list + green inventory is the blueprint
dep-graph `algebraic-induction.tex` (`sec:molecular-algebraic-induction`). This
file carries state, decisions, the re-scope findings, and the hand-off to 22–23.
Program plan / reuse map / citations: `notes/MolecularConjecture.md`. Lean:
`Molecular/AlgebraicInduction.lean` + mirror bricks under
`Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative*, *Forward-mode reduction
chains*, *Genericity device …*, *Constructibility recon before a producer build*,
*Phase Case-naming vs. KT's k-bookkeeping*.

## What 21b delivered (green)

- **The genericity device** `lem:genericity-device` (`exists_good_realization`,
  `_const`, `_ofParam`) — the multivariate Claim 6.4/6.9 on the route-(a)
  `exists_…_polynomial` mirror engine; applied to the *varying* panel family via
  the **B0 keystone** `lem:rows-polynomial-in-normals`
  (`exists_good_realization_ofParam`, the device closure on `ofNormals G ends q`).
- **The genericity-free accounting iffs** `lem:case-I` / `lem:case-II` (green —
  the device leg now discharged): the α-independent rank-side rigidity bridges
  `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le` (Case I) /
  `isInfinitesimallyRigidOn_insert_iff` (Case II); the α-dependent nullity iffs
  kept as siblings. Plus `def:rank-hypothesis`, `lem:theorem-55-base`, the panel
  layer, the cycle-realization, the `R(G,p)` coordinatization, and the block-pin
  machinery (`lem:pinned-motions-on-rank-bound` etc.).
- **The `V(G)`-relative count bridge N1–N3** (`finrank_pinnedMotionsOn_vertexSet`,
  `exists_relative_full_count_ofParam`, `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`)
  + the **device-to-motive glue N7a** `lem:realization-of-independent-rows`
  (`hasFullRankRealization_of_independent_panelRow`, the `N2 ∘ N3` closure):
  a witnessed independent `panelRow` family of size `D(|V(G)|−1)` at one seed ⇒
  `HasFullRankRealization`.
- **The Case-I splice glue** `lem:case-I-splice-seed`
  (`isInfinitesimallyRigidOn_of_splice`) + the union-glue
  `isInfinitesimallyRigidOn_union_of_inter`.
- **The four Case-II row sub-nodes N7b-0/1/2/3** (the old-block producer
  `exists_independent_panelRow_subfamily_of_rigidOn`, the new-block rows
  `exists_independent_panelRow_subfamily_of_edge`, the `ofNormals` transport, the
  pin-a-body column split `linearIndependent_sum_pinned_block`). **Retained** —
  they feed the Case-I producer N6 (the row-counting/device route) in Phase 22+.

(Authoritative inventory: the blueprint dep-graph.)

## The realization-layer re-scope (2026-06-04) — math-first findings

After four honest re-plans circling the Case-II producer, a math-first
feasibility pass against KT §6.2–6.3 (paper in `.refs/`) found the realization
producers were mis-scoped. Two findings; the second decisive.

**Finding A — the row-side direction was right; the motion-side detour was a
wrong turn.** KT's actual Case-II construction (Lemma 6.8, eq. (6.12)) is
**row-side with a *degenerate* placement**, not a generic motion-pin. With
`(G_v^{ab}, q)` the inductive realization, define `p1` on `E(G)` by `p1(e)=q(e)`
on the common `G−v` edges, `p1(va)=L` a `(d−2)`-hinge *inside `a`'s panel*, and
**`p1(vb)=q(ab)`** — `v`'s hinge to `b` placed at the very `e₀=ab` hinge of `q`.
Column ops then make `R(G,p1)` block-triangular (eq. 6.16) with `R(G_v^{ab},q)`
as a submatrix, the `vb`-row *reproducing* the `e₀`-row of `R(G_v^{ab},q)`. So
`rank R(G,p1) ≥ (D−1) + rank R(G_v^{ab},q)`, then a slight rotation of `Π(v)`
(semicontinuity, Lemma 5.2 / the device, green) lifts to a nonparallel
realization. The "`e₀`-recovery" the row-side recons sought (N7b-4) is real and
*is* resolvable — not by an impossible `e₀`-free block, but by `p1(vb)=q(ab)`
making `vb`'s row *be* the `e₀`-row. The motion-side M1/M2/M3 nodes are **not**
KT's argument (M3 hand-waves "a motion constant on `V(G)∖{v}`", which a `G`-motion
need not be — `G−v` is not rigid); M1/M2 are elementary but irrelevant to the
real proof. **Retire M1/M2/M3 when Phase 22+ builds Case II properly.**

**Finding B (decisive) — the project's `hsplit` is KT Case III, not Case II.**
`theorem_55.hsplit` is scoped `IsMinimalKDof n 0` (k=0), `∀ H, ¬ IsProperRigidSubgraph`
(no proper rigid subgraph), degree-2 `v`, target full rank `D(|V|−1)`. Run KT's
own construction at that scope:
- KT Lemma 4.8(i): for k=0, `G_v^{ab}` is minimal **0-dof**, so the IH gives
  `rank R(G_v^{ab},q) = D(|V∖{v}|−1)` (full).
- eq. (6.12) at the degenerate `p1`: `rank R(G,p1) ≥ (D−1) + D(|V∖{v}|−1) =
  D(|V|−1) − 1`. **Exactly one row short of the target.**
- KT page 33 (printed 680), verbatim: for k=0 "we only have `rank R(G,p1) ≥
  6(|V|−1)−1 … which does not complete the proof." The missing row comes from
  the redundant-edge / `M(G̃)`-base argument — **Case III** (Lemma 6.10/6.13),
  deferred to Phases 22–23.

KT Lemma 6.8 (where `+(D−1)` *suffices*) is **k>0 only** (target `D(|V|−1)−k`).
The blueprint `lem:case-II` prose said "k>0" (Lemma 6.8) but was wired to
discharge the **k=0** `hsplit`; that conflation is the bug. The project's own
`theorem_55` doc-comment already says it: *"Case III (k=0, no proper rigid
subgraph) … realized in Phases 22–23"* — exactly `hsplit`'s condition. **So N7
(`lem:case-II-realization`) is Case-III content and was never a 21b deliverable.**
No row-side or motion-side rearrangement inside 21b can manufacture that row.

**Case I is different and *is* 21b-tractable (so it moves to 22+ as a near-leaf,
not a research node).** KT §6.2 (Lemmas 6.2/6.3/6.5) realizes the proper-rigid-
subgraph case by **splicing** the two inductive legs `(G',p1)` (rigid subgraph,
full rank) and `(G/E',p2)` (contraction, rank `−k`) along boundary hinges at
**panel intersections** (eq. 6.6: `p(uv)=Π_{G/E',p2}(u) ∩ Π_{G',p1}(v)`), block-
triangular via Lemma 5.1 (pin-a-body). For k=0 this reaches **full `D(|V|−1)` with
no shortfall**. Every ingredient is already green: the splice glue
`isInfinitesimallyRigidOn_union_of_inter`, pin-a-body Lemma 5.1, and the device
(Claim 6.4 lift). Its one genuine remaining geometric obligation is the
**panel-transversality lemma** (two generic `(d−1)`-panels meet in a `(d−2)`-hinge)
plus assembling the spliced `ofNormals` field; KT splits it into three sub-cases
(6.2/6.3/6.5 by whether a simple contraction exists). Bounded, not research-open.

## Architectural choices / Decisions

- **The motive is `V(G)`-relative.** `IsInfinitesimallyRigidOn (s : Set α)` =
  "every motion is constant on `s`"; `HasFullRankRealization k G := ∃ Q, Q.graph
  = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`. The absolute null-space form
  is α-dependent and unsatisfiable for non-spanning inductive subgraphs.
  → `DESIGN.md` *Realization motive must be V(G)-relative*.
- **`theorem_55.hsplit` premise carries `v`'s reducible-degree-2 data** (the two
  edges `eₐ, e_b`, their links, the degree-2 closure), strengthened 2026-06-04 in
  step with `minimal_kdof_reduction`; the Case-II/III producer in Phase 22+ needs
  it to name `v`'s edges (forwarded one-line at `Induction.lean` dispatch).

### Promoted (cross-cutting lessons)
- *Build the keystone / validate the target shape before growing a reduction
  chain.* → `DESIGN.md` *Forward-mode reduction chains*.
- *A producer node may not carry an unsatisfiable or laundered hypothesis.* →
  `blueprint/CLAUDE.md` *the honesty gate* + *producer scrutiny*.
- *An absolute (ambient-type) rigidity motive is unsatisfiable for non-spanning
  subgraphs; carry it relative to `V(G)`.* → `DESIGN.md` *Realization motive must
  be V(G)-relative*.
- *Before scheduling a realization/existence producer as a build, run a
  constructibility recon: check the target rank/count arithmetic against the
  source construction, not just the node types.* (The k=0 one-row shortfall was
  visible in three lines of arithmetic, yet sat under four build-and-re-plan
  cycles.) → `DESIGN.md` *Constructibility recon before a producer build*.
- *Match the project's case names to KT's k-bookkeeping: the k=0 degree-2 split
  is Case III, not "Case II"; only Case I (proper rigid subgraph) reaches full
  rank without the Case-III extra row.* → `DESIGN.md` *Phase Case-naming vs. KT's
  k-bookkeeping*.
- TACTICS-QUIRKS §30/§32/§33/§34 (panel-coordinate / `Module.Dual` / `finrank ↥`
  / `Basis.repr`-through-`∑` rescues, all from the device build).

## Hand-off to Phases 22–23 (the realization layer)

21b is closed; the realization producers move here. The math is worked out above
(Findings A/B) — Phase 22+ formalizes it, not re-discovers it.

- **Case I producer (N6 = N4 + N5 + glue), KT §6.2.** Full-rank, no shortfall;
  the most tractable producer. Needs: **N4** `lem:rigidContract-isMinimalKDof`
  (the graph↔matroid contraction-minimality bridge, a Phase-20 carry-forward,
  `Induction.lean:2956–2961`; matroid side `contraction_isMinimalKDof` green) and
  **N5** `lem:case-I-splice-placement` (the splice: spliced `ofNormals` field +
  the panel-transversality lemma + block-triangular independence; three KT
  sub-cases 6.2/6.3/6.5). Compose with the green glue + device.
- **Case II / III producer (N7 → Case III), KT §6.3 (Lemma 6.8) + §6.4 (Lemma
  6.10/6.13).** The k>0 step (Lemma 6.8) is the degenerate eq.(6.12) placement
  (Finding A) giving `+(D−1)`; the k=0 step (the project's `hsplit`) needs that
  *plus* the Case-III redundant-edge row (Lemma 4.3 / `M(G̃)`-base). Reuses the
  green row infra N7b-0/1/2/3 + N7a + `linearIndependent_sum_pinned_block`. This
  is the existing Phases 22–23 scope (Case III at d=3, then general d).
- **`thm:theorem-55`, `prop:rigidity-matrix-prop11` (+ brick `hub`, the Phase-19
  partition count), `lem:case-III`** all flip in 22–23, once the producers land.

**Process lessons (don't repeat) — see *Promoted* above; the headline is lesson
(e′): a producer's *constructibility* must be checked by arithmetic against the
source, before it is scheduled as a build.**

**Completed items (per-commit history).** Device + route-(a) engine; B0 keystone
(sub-commits 1–4); Case-I splice glue; N1–N3 relative count bridge; N7a glue;
N7b-1/2/3 + N7b-0; the `hsplit` premise strengthening. All on `master`-local
commits 13406ff…3f725a8 (+ the re-plan/recon commits). Not pushed (session note;
match author `bryangingechen@gmail.com`; do not push without asking).
