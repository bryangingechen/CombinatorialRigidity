# Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (work log)

**Status:** in progress (opened 2026-06-03).

Stratum 5 of the molecular-conjecture program (the *algebraic* half of
Katoh–Tanigawa's proof, KT §5, §6.1–6.3). Where Phase 20 reduced every
minimal `0`-dof-graph to the two-vertex double edge combinatorially
(Theorem 4.9, `Graph.minimal_kdof_reduction`), this phase realizes that
reduction at the rigidity-matrix rank: KT **Theorem 5.5** (every minimal
`k`-dof-graph `G` with `|V| ≥ 2` has a panel-hinge realization with
`rank R(G,p) = D(|V|−1) − k`), its base case, **Case I** (proper rigid
subgraph), and **Case II** (`k>0` splitting). The crux **Case III**
(`k=0`, no proper rigid subgraph) is deferred to Phases 22–23.

Program-level plan, reuse map, citations, and risk register:
`notes/MolecularConjecture.md` *Phase 21*. Forward-mode dep-graph /
lemma index: `blueprint/src/chapter/algebraic-induction.tex`
(`sec:molecular-algebraic-induction`). Lean lands in a new file
`CombinatorialRigidity/Molecular/AlgebraicInduction.lean`.

## Current state

`Molecular/AlgebraicInduction.lean` carries the induction-skeleton leaf
nodes (green): `def:rank-hypothesis`, `lem:theorem-55-base`, and the Case
II rank-lift accounting `lem:case-II-rank-lift`
(`rankHypothesis_iff_finrank_pinnedMotions`, the basis-free `+D` core of
the panel-hinge 1-extension). This commit lands the **framework-
construction op** (`def:framework-with-graph` / `lem:motions-mono-of-
graph-le`, green): `BodyHingeFramework.withGraph` (swap the underlying
multigraph, keep the hinge data — hence every supporting extensor /
hinge-row block) plus the graph-monotonicity of the null space
(`infinitesimalMotions_le_withGraph_of_le` and its `finrank` form,
"deleting edges enlarges `Z(G,p)`"). This is the shared, citation-free
primitive both inductive cases need; it is hand-off #1 from the previous
commit. The cycle input `lem:cycle-realization` (KT Lemma 5.4) is a
**verified cite** — not Lean: its proposition numbers ([4] Crapo–Whiteley
1982 Prop 3.4, [34] Whiteley 1999 Kluwer Prop 3) were checked against the
local OCR'd primaries and pinned. Still red: `prop:rigidity-matrix-prop11`,
`thm:theorem-55`, `lem:case-I`, `lem:case-II` (now gating on the *vertex-
level* graph ops — contraction `G/E(H)`, splitting-off `G_v^{ab}` — and
the genericity device, see *Hand-off*), and `lem:case-III` (deferred to
22–23).

**Basis-free rank convention (carried forward from Phase 18).** Phase 18
carries `rank R(G,p)` as the codimension `D|V| − dim Z(G,p)` of the null
space `Z(G,p) = F.infinitesimalMotions` (`finrank_screwAssignment`). The
realization hypothesis `rank R(G,p) = D(|V|−1) − k` is therefore stated
directly on the null-space dimension: `RankHypothesis F k' := (finrank
infinitesimalMotions : ℤ) = screwDim k + k'`. At `k'=0` this is exactly
infinitesimal rigidity (`rankHypothesis_zero_iff`, via
`finrank_trivialMotions` + `infinitesimalMotions_eq_trivialMotions_iff`).

## Architectural choices made up front

- **New file `Molecular/AlgebraicInduction.lean`, new chapter
  `algebraic-induction.tex`.** Per the one-`.lean` / one-`.tex` per
  molecular phase convention (post-Phase-18 cleanup split). Carrier:
  the Phase-18 panel-hinge rigidity matrix `R(G,p)` over `Graph α β`.
- **Driven by Theorem 4.9 (`thm:minimal-kdof-reduction`).** Theorem 5.5
  is induction on `|V|` over the *same* reduction dichotomy Phase 20's
  capstone exposes as a well-founded induction principle: base case
  `|V|=2`, then Case I (rigid-subgraph contraction) / Case II (splitting
  off) / Case III (deferred). Reuse the green `lem:reduction-step` +
  `lem:contraction-minimality` minimality-transport lemmas as the
  combinatorial inputs; this phase supplies only the rank realizations.
- **Rank arguments are block-triangular**, reusing Phase 18's pin-a-body
  Lemma 5.1 (`lem:rank-delete-vertex`) and parallel-hinges-full Lemma 5.3
  (`lem:rank-parallel-full`). Genericity (Claim 6.4 / 6.9: matrix entries
  are polynomials in algebraically independent panel coords ⇒ a generic
  point attains the max rank) lifts each single good realization to a
  generic one — the only genuinely new analytic device.
- **Cycle-realization Lemma 5.4** (`lem:cycle-realization`,
  Crapo–Whiteley [4] / Whiteley Kluwer 1999) enters as an input here;
  formalize-or-cite decision per-node (risk #4 in MolecularConjecture.md).
  Bib entry `crapoWhiteley1982` added this commit.

## Lemma checklist

Forward-mode: the authoritative node list is `algebraic-induction.tex`.
Tracked here for hand-off convenience; all red at phase open.

Generic-rank reconciliation (relocated forward from Phase 18/19):
- [ ] `prop:rigidity-matrix-prop11` — KT Prop 1.1, analytic half:
  `rank R(G,p) = D(|V|−1) − def(G̃)` for generic `(G,p)`. The matroidal
  half (`def = corank M(G̃)`, `thm:def-eq-corank`) is already green
  (Phase 19); this is the geometric side (JJ [15] Thm 6.1), depending on
  the Claim 6.4 generic-rank argument. Lands with / after Theorem 5.5.

Induction skeleton + base:
- [x] `def:rank-hypothesis` — the realization hypothesis (6.1):
  `RankHypothesis F k' := (finrank infinitesimalMotions : ℤ) = screwDim k + k'`
  (null-space form of `rank = D(|V|−1) − k`; see *Current state*). Green.
- [ ] `thm:theorem-55` — KT Theorem 5.5, the capstone of this phase.
  Induction on `|V|` over the Phase-20 reduction dichotomy.
- [x] `lem:theorem-55-base` — `|V|=2`, `k=0` base case (`theorem_55_base`
  + helper `rankHypothesis_zero_iff`); full rank `D` via
  `eq_of_hingeConstraint_two_parallel` (`lem:rank-parallel-full`, Phase 18
  green). Axiom-free.

Framework-construction op (shared infra for Cases I & II):
- [x] `def:framework-with-graph` — `BodyHingeFramework.withGraph`: swap
  the underlying multigraph, keep the hinge map (hence every supporting
  extensor / hinge-row block). The carrier for the inductive
  constructions. Green.
- [x] `lem:motions-mono-of-graph-le` — graph-monotonicity of the null
  space: `infinitesimalMotions_le_withGraph_of_le` (`G' ≤ G ⇒ Z(G,p) ≤
  Z(G',p)`) + its `finrank` form `finrank_infinitesimalMotions_le_of_
  graph_le` ("re-adding edges only grows the rank", the step
  `prop:rigidity-matrix-prop11` uses). Axiom-clean. Green.

Case I (proper rigid subgraph; KT §6.2):
- [ ] `lem:cycle-realization` — KT Lemma 5.4. **Decision revised
  2026-06-03: formalize before phase close** (was cite-only; see
  *Decisions made* below for the original citation work, which stands,
  and the abstract-model finding that reopened it). Statement is KT's
  form (a cycle graph with `3 ≤ |V| ≤ D` has an infinitesimally rigid =
  full-rank `D(|V|−1)` nonparallel realization). Citation to
  Crapo–Whiteley 1982 Prop 3.4 + Whiteley 1999 (Kluwer) Prop 3 stays as
  the source pointer. **Phase-close requirement:** must land green
  (`\leanok`) before Phase 21 closes — a focused 1–2 commit task, not a
  side phase (see the finding). Currently still red.
- [ ] `lem:case-I` — KT Lemmas 6.2/6.3/6.5: contract a proper rigid
  subgraph `H` (smaller minimal `k`-dof by green `lem:contraction-minimality`),
  glue block-triangularly with a pinned rigid realization of `H`
  (`lem:rank-delete-vertex`, Phase 18 green). Claim 6.4 genericity.

Case II (`k>0` splitting; KT §6.3):
- [x] `lem:case-II-rank-lift` — the `+D` accounting core
  (`rankHypothesis_iff_finrank_pinnedMotions`): `RankHypothesis F k' ↔
  finrank (pinnedMotions v) = k'`, via the green
  `finrank_pinnedMotions_add_screwDim` (pin-a-body Lemma 5.1, Phase 18).
  Axiom-clean. Green.
- [ ] `lem:case-II` — KT Lemmas 6.7/6.8: splitting off a reducible
  degree-2 vertex (smaller minimal `k`-dof by green `lem:reduction-step`),
  the panel-hinge analogue of Whiteley's bar-joint 1-extension; re-insert
  `v` to lift the rank by `D` (the accounting is `lem:case-II-rank-lift`).
  Still needs the framework construction from a realization of `G_v^{ab}` +
  Claim 6.9 genericity.

Case III (deferred to Phases 22–23):
- [ ] `lem:case-III` — KT Lemma 6.10/6.13: `k=0`, no proper rigid
  subgraph. Stated here only to close the Theorem-5.5 dichotomy; bottoms
  out on the extensor-independence Lemma 2.1 (`lem:extensor-independence`,
  Phase 17 green). **Deferred** — the crux, Phases 22–23.

## Carry-forwards inherited from Phase 20 (schedule as needed)

1. **Graph↔matroid contraction bridge.** `minimal_kdof_reduction`'s
   contraction branch is handed the IH rather than recursing internally
   (no `(G/E(H))̃ ↔ M(G̃)/E(H̃)` map built). Needed only if Case I's
   recursion wants a fully graph-level form; otherwise the IH-handed
   shape suffices. See `notes/Phase20.md` *Hand-off* #1.
2. **Forest surgery KT 4.2** (`lem:forest-surgery-unsplit`). Off the
   Theorem-4.9 critical path; sound, no balanced-packing gloss, not yet
   needed. See `notes/Phase20.md` *Hand-off* #2.

Also off the Thm-4.9 critical path, scheduled with this phase as Case 6.1
needs them: KT Lemma 3.2 (not 3-edge-connected), Lemma 3.6 (partition
decomposition).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Null-space form of the realization hypothesis.** `RankHypothesis`
  states `rank R(G,p) = D(|V|−1) − k` as the null-space dimension
  `dim Z(G,p) = D + k` rather than carrying an `ℤ`-valued rank and
  re-deriving the `D|V|` column count at each node — matches the
  basis-free convention Phase 18's rank lemmas
  (`finrank_pinnedMotions_add_screwDim`, `finrank_trivialMotions`) already
  speak. The two forms interchange by `finrank_screwAssignment`. See
  Phase21.md *Current state* and the file docstring.
- **Base case stated abstractly, not on a concrete 2-vertex graph.**
  `theorem_55_base` hypothesizes a 2-body framework (`Nonempty`/`Finite α`,
  `hcover : ∀ w, w = u ∨ w = v`) with two independent-extensor hinges
  linking `u v`, rather than constructing `Fin 2` + an explicit double
  edge. Keeps the base case reusable by the induction (which will supply
  the 2-body framework from its own data) and lets
  `eq_of_hingeConstraint_two_parallel` apply verbatim.
- **Framework-construction op landed at the `≤`/edge-set level only.**
  `withGraph` swaps `F.graph` keeping the hinge map; the one fact this
  phase needs is graph-monotonicity of `Z(G,p)` (`G' ≤ G ⇒ Z(G,p) ≤
  Z(G',p)`), proved through `Graph.IsLink.mono` (called explicitly, not
  via dot notation — FRICTION recurrence). The *vertex-level* ops
  (contraction `G/E(H)`, splitting-off `G_v^{ab}`) that actually change
  `|V|` are left for the next commit — they are where Cases I/II diverge.
  Needed the `Mathlib.Combinatorics.Graph.Subgraph` import (`≤` on
  `Graph` lives there, not `.Basic`).
- **Cycle Lemma 5.4 (`lem:cycle-realization`): citation work (stands).**
  KT's Lemma 5.4 — a cycle graph with `3 ≤ |V| ≤ D` has an
  infinitesimally rigid nonparallel panel-hinge realization (= full rank
  `D(|V|−1)`). Proposition numbers verified against the local OCR'd
  primaries: [4] Crapo–Whiteley 1982 **Proposition 3.4** (`.refs/`,
  French+English columns p.25, `D=6` case) and [34] Whiteley 1999 Kluwer
  **Proposition 3** (p.5); KT attributes "[4, Proposition 3.4] or [34,
  Proposition 3]" itself. Discharges the *Citation accuracy caveat* in
  MolecularConjecture.md. Corrected a prior mis-statement: the blueprint
  had glossed cycle realization as "rank one less than the free value" —
  backwards; short cycles (`|V| ≤ D`) are *rigid*, i.e. full rank. New
  bib entry `whiteley1999` (editor initials corrected from KT's
  OCR-typo'd "Thorpe, O., Duxbury, O.").
- **Cycle Lemma 5.4: revised to formalize before phase close
  (2026-06-03).** The cite-only call above was made on the premise that
  5.4 needs Crapo–Whiteley's *projective realizability* (a cycle of
  `n ≤ D` lines is physically realizable by panels in ℝ^d). It does
  not — in **our** model. `BodyHingeFramework` (`RigidityMatrix.lean`)
  is a **free per-edge hinge assignment** (`hinge : β → Fin k →
  Fin (k+1) → ℝ`); there is no per-body panel data and no
  geometric-consistency constraint, so physical realizability was
  abstracted away in Phase 18 and the rank depends only on the per-edge
  supporting extensors. So 5.4 reduces to pure linear algebra on
  existing API:
  1. cycle graph on `Fin n` (edge `i` links `i, i+1 mod n`) — modest
     structural plumbing on `Graph (Fin n) (Fin n)`, the only new piece;
  2. hinges with independent extensors — Lemma 2.1
     (`omitTwoExtensor_linearIndependent`, Phase 17 green) gives `D`
     independent extensors indexed by point-pairs; assign any `n ≤ D` to
     the edges. Each `omitTwoExtensor` *is* an `affineSubspaceExtensor`
     of a point sub-family, i.e. exactly what `supportExtensor`
     consumes — reindexing glue, not new math;
  3. rigidity bridge (short): around the cycle the constraints give
     `S(vᵢ)−S(vᵢ₊₁) = λᵢ·Cᵢ`; telescoping ⇒ `Σ λᵢ Cᵢ = 0`; `{Cᵢ}`
     independent ⇒ all `λᵢ=0` ⇒ `S` constant ⇒ trivial ⇒ rigid at rank
     `D(n−1)`.
  **Faithfulness caveat:** this proves an *abstract* hinge assignment
  with the target rank exists — which is what Cases I/II/III consume —
  not KT's stronger *physical* realization. That physical-realizability
  gap is inherited from the Phase-18 modeling choice and is identical
  for every node in the program; it is not specific to 5.4. User
  decision (2026-06-03): formalize after Cases I/II, before phase close.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *(none yet)*

## Blockers / open questions

- **Claim 6.4 / 6.9 genericity** is the new analytic device this phase
  introduces (matrix entries polynomial in alg.-indep. panel coords ⇒
  generic max rank). Reuse the Phase 6/8 genericity machinery
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean` Gram-det LI mirrors,
  `exists_uniform_rowIndependent_placement`-style perturbation) where it
  transfers; assess on contact whether the panel-coordinate
  parametrization needs new infrastructure.
- **Cycle Lemma 5.4 — to formalize before phase close** (revised
  2026-06-03, was cite-only). The abstract `BodyHingeFramework` model
  doesn't carry physical panel-realizability, so 5.4 reduces to linear
  algebra on existing Phase-17/18 API (cycle graph + Lemma 2.1 extensors
  + telescoping bridge — a 1–2 commit task). Citation work stands as the
  source pointer. See *Decisions made* for the finding + proof sketch.
  **Must land green before Phase 21 closes** (per user decision; do it
  after Cases I/II).

## Hand-off / next phase

Settled: base case (`def:rank-hypothesis` + `lem:theorem-55-base`), the
Case II `+D` rank-lift accounting (`lem:case-II-rank-lift`), the cycle
input (`lem:cycle-realization`, cite-only), and now the **graph-level
framework-construction op** (`def:framework-with-graph` /
`lem:motions-mono-of-graph-le`): `BodyHingeFramework.withGraph` swaps the
underlying multigraph keeping the hinge data, and edge deletion only
enlarges `Z(G,p)`. This is the citation-free `≤`-monotonicity primitive
both Cases need to compare a realization across the inductive graph
change. `Molecular/AlgebraicInduction.lean` carries five Lean nodes.
Remaining red: `lem:cycle-realization` (now slated to formalize before
phase close — see Blockers / Decisions), `prop:rigidity-matrix-prop11`,
`thm:theorem-55`, `lem:case-I`, `lem:case-II` (gating on the two pieces
below), `lem:case-III` (22–23).

**Phase-close requirement (do not lose):** `lem:cycle-realization` must
be formalized green before Phase 21 closes (user decision 2026-06-03,
after Cases I/II). Focused 1–2 commit task on existing API; the
abstract-model finding + telescoping proof sketch are in *Decisions
made*. The immediate next commit is still the Case I/II work below.

The next concrete commit must build one of two not-yet-existing pieces:
1. **Vertex-level graph ops realized as frameworks.** `withGraph` only
   changes *which edges* impose constraints; Cases I/II additionally
   change the *vertex set* — Case I contracts a proper rigid subgraph
   `H` (`G/E(H)`), Case II splits off a reducible degree-2 vertex
   (`G_v^{ab}`, re-insert `v` with two hinges). Neither vertex-deletion /
   extension / contraction op exists on `BodyHingeFramework` yet. Likely
   its own commit (or a small series): define the op + its
   `infinitesimalMotions` / `pinnedMotions` relationship to the parent,
   reusing the pin-a-body identity (`finrank_pinnedMotions_add_screwDim`)
   and the new `withGraph` monotonicity for the edge-set bookkeeping.
2. **Claim 6.4 / 6.9 genericity device** (Blockers): matrix entries are
   polynomials in alg.-indep. panel coords ⇒ a generic point attains max
   rank. First step is an *assessment* (scoping commit / FRICTION entry):
   does the Phase 6/8 genericity machinery transfer, or does the panel-
   coordinate parametrization need new infra? It determines whether
   Cases I/II are one commit or several.

Smallest forward step: start the vertex-level contraction op for Case I
(#1) — it can land its `pinnedMotions`-relationship lemma incrementally
before the genericity device is in place. Broad phase; may split Case I
from Case II (precedent: Phases 8–11). Phases 22–23 pick up Case III.
