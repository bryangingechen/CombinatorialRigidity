# Phase 21b — Genericity device + realization layer (work log)

**Status:** in progress (opened 2026-06-03; realization layer re-planned
2026-06-04; node-decomposition re-plan 2026-06-06). Cold-start-ready hand-off below.

Sub-phase scoped out of Phase 21 (user decision, risk #4/#7) — the **analytic
sibling** of the Phase-21a meet. Two halves: (1) the **genericity device**
(Claim 6.4/6.9 — rigidity-matrix entries are polynomials in the panel
coordinates, so one good realization lifts to a generic one), **GREEN**; and
(2) the **realization layer** of Theorem 5.5 (producers exhibiting a rigid
panel framework for each inductive case), the remaining build.

Forward-mode: the authoritative node list + green inventory is the blueprint
dep-graph `algebraic-induction.tex` (`sec:molecular-algebraic-induction`). This
file carries state, decisions, blockers, and the ordered hand-off — it does
*not* duplicate the dep-graph. Program plan / reuse map / citations:
`notes/MolecularConjecture.md` *Phase 21b*. Lean:
`Molecular/AlgebraicInduction.lean` + mirror bricks under
`Mathlib/{Algebra/MvPolynomial,LinearAlgebra/Matrix}/`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative* + *Forward-mode reduction
chains* + *Genericity device …*.

## Current state

**Green: the device + the realization-layer scaffolding.** The device
(`exists_good_realization{,_const,_ofParam}`), the panel layer, the
cycle-realization, the `R(G,p)` coordinatization, the block-pin machinery, the
relativized motive + base case (`def:rank-hypothesis`, `lem:theorem-55-base`),
the rank-side accounting iffs (`lem:case-I` / `lem:case-II`, green-modulo-21b),
the **B0 keystone** (`lem:rows-polynomial-in-normals` — the device closure on the
*varying* panel family), and the Case-I splice **glue** (`lem:case-I-splice-seed`)
are all green and axiom-clean {propext, Classical.choice, Quot.sound}.
(Authoritative inventory: the blueprint dep-graph. Per-commit history: *Completed
items* in the Hand-off.)

**Remaining: the realization producers, re-planned 2026-06-06** into the ordered
node list in the Hand-off. Three forward facts shape the plan:
- The device's output is an **absolute** codimension bound `#s + dim Z ≤ D·card α`
  over the ambient body type; the producers need the **`V(G)`-relative motive**
  `IsInfinitesimallyRigidOn V(G)`. The adapter is the relative-count bridge
  **N1–N3** (build-shaped, the next commit).
- The rigid-subgraph contraction is **mostly built, not fully**: `rigidContract`
  (`Induction.lean:1854`) + its vertex-drop (`:1869`) + the matroid-side
  `contraction_isMinimalKDof` (`:1998`) are green, but the graph↔matroid
  minimality bridge `(rigidContract).IsMinimalKDof` (**N4**) is a deliberate
  Phase-20 carry-forward (`Induction.lean:2956–2961`) that gates Case I.
- `thm:theorem-55` does **not** flip in 21b: its recursion needs all three
  case-producers, and Case III is Phases 22–23. **Phase 21b closes when the two
  producers `lem:case-I-realization` (N6) + `lem:case-II-realization` (N7) are
  green.**

## Architectural choices

- **Forward-mode, nodes beside the consumers.** The realization spine + device
  live in `algebraic-induction.tex` `sec:molecular-algebraic-induction`.
- **The motive is `V(G)`-relative.** `IsInfinitesimallyRigidOn (s : Set α)` =
  "every infinitesimal motion is constant on `s`"; `HasFullRankRealization k G :=
  ∃ Q, Q.graph = G ∧ Q.toBodyHinge.IsInfinitesimallyRigidOn V(G)`. The absolute
  null-space form is `α`-dependent and unsatisfiable for non-spanning inductive
  subgraphs. → `DESIGN.md` *Realization motive must be V(G)-relative*.

## Lemma checklist

Authoritative node list + green inventory: the blueprint dep-graph. Tracked here
only as the RED frontier (the build) + retirements; the Hand-off carries the
per-node detail.

**RED — the build (ordered; detail in Hand-off):**
- [ ] N1 `lem:relative-screw-split` — `dim Z = D(card α − V(G).ncard) + dim Z_{V(G)}` (`finrank_pi`).
- [ ] N2 `lem:relative-device-count` — the device re-wrapped relative.
- [ ] N3 `lem:isInfRigidOn-of-relative-count` — relative full count ⇒ `IsInfinitesimallyRigidOn V(G)`.
- [ ] N7 `lem:case-II-realization` — 1-extension producer (needs only N3 + device). Discharges `hsplit`.
- [ ] N4 `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction bridge; gates Case I.
- [ ] N5 `lem:case-I-splice-placement` — the splice geometry (decompose first).
- [ ] N6 `lem:case-I-realization` — compose N4+N5+glue+B0+N3/device. Discharges `hcontract`.
- [ ] `thm:theorem-55` / `prop:rigidity-matrix-prop11` / `lem:case-III` — carry to Phases 22–23.

**RETIRED (item 1, deleted; retirement note in `AlgebraicInduction.lean`):** the four
absolute-motive Case-I producers (`hasFullRankRealization_ofParam_of_*`,
`…_of_pinnedMotionsOn`) and the orphaned vacuous block-internal chain. The genuine
block-pin bricks (`isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot`, etc.)
are **retained** (blueprint `lem:pinned-motions-on-rank-bound`).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **The Case-I splice splits into a green `glue` + a red `placement`.** The
  original `lem:case-I-splice-seed` promised to *produce* a placement, so flipping
  it green while the Lean merely *assumes* the two legs' rigidity would launder
  the deliverable. Resolution: the green `isInfinitesimallyRigidOn_of_splice` is
  the honest **glue** (two legs realized on a common `F` ⇒ rigid on `V(G)`,
  hypotheses = satisfiable IH facts); the **placement** (one `F` realizing both
  legs generically) is the red `lem:case-I-splice-placement` (N5). → blueprint
  honesty gate / producer scrutiny.
- **The device's `hcoord` is a `≤`-containment, not equality.** At degenerate
  panel normals some `C(p(e)) = 0`, so `panelRow` *under*-spans `rigidityRows` and
  equality fails — but the device's generic output point is unknown, so it must
  work at degenerate `q`. It needs only `Z ⊆ (span (range g))ᵒ` (the `⊆`-half of
  `span_panelRow`, holds at every `q`); equality consumers pass `le_of_eq`.
- **B0 coordinatizes against the concrete `Pi.basis (screwBasis k)`, not
  `Module.finBasis`.** `B.dualBasis.equivFun (g i) ⟨a,t⟩ = (g i)(Pi.single a (sb t))`
  is a computable degree-2 panel poly; `Module.finBasis` is opaque. Price: a
  reindex via `exists_good_realization_reindex` (`LinearEquiv.funCongrLeft`).
- **The Case-I splice seed is genericity-free.** Block-triangular row independence
  (KT 6.3 + pin-a-body Lemma 5.1 column split) from the two IH legs; the device
  only lifts the seed to a generic point afterward.
- **B0 coordinate bilinearity is mathlib-supported.** `exteriorPower.basis_repr_apply`
  + `ιMultiDual_apply_ιMulti` + `Matrix.det_fin_two`; the device parameter is the
  panel **normals**, entries degree-2.
- **Coordinatize `R(G,p)` as a functional family.** Rows are `hingeRow u v r`;
  `Z = (span rigidityRows).dualCoannihilator`. → TACTICS-QUIRKS §30/§32/§33.

### Promoted
- *Build the keystone first (forward-mode + linear reduction chain → single-use
  wrapper sprawl).* → `DESIGN.md` *Forward-mode reduction chains*.
- *A producer node may not carry a load-bearing hypothesis no node discharges, and
  it must be **satisfiable**, not merely type-correct.* → `blueprint/CLAUDE.md`
  *the honesty gate* + *producer scrutiny*.
- *An absolute (ambient-type) rigidity/rank motive is unsatisfiable for
  non-spanning subgraphs; carry it relative to `V(G)`.* → `DESIGN.md` *Realization
  motive must be V(G)-relative*.
- *`rw [hsub]` over a `Submodule` under `finrank ℝ ↥(…)` trips the motive.* →
  TACTICS-QUIRKS § 33.
- *`map_sum` won't push `Basis.repr` through a `∑` — route via `Finsupp.lapply t
  ∘ₗ repr.toLinearMap`.* → TACTICS-QUIRKS § 34.

## Blockers / open questions

- **N1–N3 (the `V(G)`-relative count bridge) is the next build** — adapt the
  device's absolute count to `IsInfinitesimallyRigidOn V(G)`. Build-shaped (mathlib
  `finrank_pi` + the green block-pin bricks); shape MCP-validated as a `sorry`-stub.
- **N4 (graph↔matroid contraction-minimality bridge) gates Case I.**
  `(rigidContract).IsMinimalKDof` is not built (Phase-20 carry-forward 1,
  `Induction.lean:2956–2961`); the matroid side is green. Build-shaped but
  nontrivial (the matroid-of-a-mapped-graph identification is the content).
- **N5 (Case-I splice placement) is the one genuinely hard node** — research-shaped
  geometry (KT 6.2/6.6, the witness-transfer); decompose before building.
- **`thm:theorem-55`, `prop:rigidity-matrix-prop11`, Case III carry to Phases
  22–23** — not 21b close-conditions. (`prop11`'s `hub`, the Phase-19 partition
  count `D + def ≤ dim Z`, is an untracked hypothesis; independent.)

## Hand-off / next phase

**For the `coordinate-phase` orchestrator (cold-start ready).** The nodes below
are an ordered list; do them top to bottom, re-reading this section after each
commit (the building subagent updates it). Each commit lands Lean + flips its
blueprint node's `\leanok` (or adds green infra) + updates this file. **Mind the
shape tags — this is NOT uniformly build work:** `N4` (contraction bridge) is
build-shaped-but-nontrivial, and `N5` (splice placement) is genuinely hard
geometry that **warrants its own decomposition pass** (dispatch a planning/recon
subagent to break it into sub-nodes) before a build commit. **Do not** re-introduce
the retired vacuous lemmas. Scope: the remaining work is *known-construction*
formalization (KT 2011), not open math; `apnelson1/Matroid` offers no reusable
leverage (no `Pi`-finrank / generic-realization machinery).

**Next concrete commit: N1–N3, the `V(G)`-relative count bridge** (likely one
commit; the builder may split N1 from N2+N3). The device
(`exists_good_realization_ofParam`, green) gives an *absolute* codimension bound
`#s + dim Z(G,p) ≤ D·card α`; the producers need `IsInfinitesimallyRigidOn V(G)`.
Build the adapter (blueprint `sec:molecular-algebraic-induction-relative`):
- **N1 `lem:relative-screw-split`** — `dim Z = D(card α − V(G).ncard) + dim Z_{V(G)}`,
  the `Pi`-product split (`finrank_pi`) removing the ambient free bodies. The one
  piece with content; build-shaped (a clean free summand, NOT a relative-rank
  argument over a non-spanning block).
- **N2 `lem:relative-device-count`** — re-wrap the device with N1 substituted for
  `finrank_screwAssignment`: a generic point attains `#s + dim Z_{V(G)} ≤
  D(V(G).ncard − 1)`. Mechanical.
- **N3 `lem:isInfRigidOn-of-relative-count`** — from the relative full count
  conclude `IsInfinitesimallyRigidOn V(G)`, via green
  `screwDim_add_finrank_pinnedMotionsOn_le` + `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`.
  Mechanical; shape MCP-validated as a `sorry`-stub.

Then, in order:
1. **N7 `lem:case-II-realization`** — the cheapest full producer: needs only the
   bridge (N3) + device, NOT N4/N5. General-position panel normal
   (`exists_independent_panelSupportExtensor`), `+(D−1)` rows (KT 6.12);
   `isInfinitesimallyRigidOn_insert_iff` (green) + bridge ⇒ `HasFullRankRealization`.
   Discharges `theorem_55`'s `hsplit`.
2. **N4 `lem:rigidContract-isMinimalKDof`** — the graph↔matroid contraction bridge
   (independent of N1–N3): `(G.rigidContract H r).IsMinimalKDof n 0` from the green
   matroid-side `contraction_isMinimalKDof` (`Induction.lean:1998`) + a
   `matroidMG`-of-`(map ∘ deleteEdges)` correspondence (the content). Phase-20
   carry-forward 1 (`Induction.lean:2956–2961`); gates the Case-I IH application.
3. **N5 `lem:case-I-splice-placement`** — the genuinely hard node. **Decompose
   first** (KT eqs. 6.2/6.6: the boundary-panel intersection + combined
   block-triangular independence). Exhibit one parent `F` realizing both legs at a
   generic point; the glue `isInfinitesimallyRigidOn_of_splice` (green) + the device
   lift then conclude. The device's `hindep` comes from
   `exists_independent_panelSupportExtensor` via the hinge-row block (`panelRow`'s `s`).
4. **N6 `lem:case-I-realization`** — compose N4 + N5 + glue + B0 + N3/device ⇒
   `HasFullRankRealization k G`. Discharges `theorem_55`'s `hcontract`.

**Phase 21b closes when N6 + N7 are green.** `thm:theorem-55` does not flip here
(its recursion needs Case III, deferred to Phases 22–23, where it flips); same for
`prop:rigidity-matrix-prop11` (+ brick `hub`, the Phase-19 partition count).

**Completed items:** Item 1 (motive relativized, base green) + Item 2 (accounting
re-stated rank-side) — 2026-06-05; Item 3 (B0 keystone) + Item 4 (Case-I splice
glue) — 2026-06-06. Per-node detail in the blueprint dep-graph.

**Process lessons (don't repeat).**
(a) Build the keystone / validate the target shape *before* growing a reduction
chain (→ `DESIGN.md` *Forward-mode reduction chains*).
(b) A producer hypothesis must be **satisfiable**, not just type-correct — check
it against a concrete small instance (→ `blueprint/CLAUDE.md` *honesty gate /
producer scrutiny*).
(c) For a vertex-reducing induction the realization motive must be carried relative
to `V(G)`, not absolute over the ambient type (→ `DESIGN.md` *Realization motive
must be V(G)-relative*).
(d) When checking whether existing work covers a need, **cross-check the actual
statement, not the name.** The rigid-subgraph contraction was called "missing" by
a spike and "done" by a recon — both wrong; the truth (matroid side green,
graph-level `(rigidContract).IsMinimalKDof` = N4 not built) only surfaced by
reading the statement (matroid- vs graph-side) and the deferral comment at
`Induction.lean:2956–2961`.

**Session note.** Commits since an inadvertent earlier push are local. Match
author `bryangingechen@gmail.com`; do **not** push without asking.
