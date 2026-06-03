# Phase 21 — Algebraic induction: Theorem 5.5 base + Cases I & II (work log)

**Status:** in progress (opened 2026-06-03); **paused 2026-06-03 for a
modeling re-scope** — the panel-hinge = hinge-coplanar body-hinge gap
(see *Blockers* + DESIGN.md *Panel-hinge = hinge-coplanar body-hinge*).
Plan-first: no further Lean until the panel-layer plan is reviewed.

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
nodes (green): `def:rank-hypothesis`, `lem:theorem-55-base`, the Case
II rank-lift accounting `lem:case-II-rank-lift`
(`rankHypothesis_iff_finrank_pinnedMotions`, the basis-free `+D` core of
the panel-hinge 1-extension), and the framework-construction op
`def:framework-with-graph` / `lem:motions-mono-of-graph-le`. This commit
lands the **Case I block-pinning op** (`def:pinned-motions-on`, green):
`BodyHingeFramework.pinnedMotionsOn s` — the infinitesimal motions
vanishing on every body of a set `s ⊆ α`, the set-level analogue of
Phase 18's `pinnedMotions v` and the framework-side carrier of
contracting a rigid subgraph `H` (pin all of `V(H)` → one body). Ships
the membership simp lemma, `pinnedMotionsOn_singleton` (recovers
`pinnedMotions v` at `s = {v}`), `pinnedMotionsOn_eq_iInf` (block pin =
`⨅ v ∈ s, pinnedMotions v` for nonempty `s`), and the two monotonicity
facts (`pinnedMotionsOn_mono`, `pinnedMotionsOn_le_pinnedMotions`). The
`s.Nonempty` hypothesis on the iInf identity is essential: the empty
infimum is `⊤` and would drop the shared `IsInfinitesimalMotion`
condition. This is hand-off #1's incremental first piece (the
`pinnedMotions`-relationship lemma, landed before the genericity
device). The cycle input `lem:cycle-realization` (KT Lemma 5.4) is a
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
- [x] `def:pinned-motions-on` — `BodyHingeFramework.pinnedMotionsOn s`:
  block-pin the bodies of a set `s` (motions vanishing on all of `s`).
  Set-level analogue of Phase 18's `pinnedMotions v`; the framework-side
  carrier of rigid-subgraph contraction (pin `V(H)`). Ships
  `pinnedMotionsOn_singleton`, `pinnedMotionsOn_eq_iInf` (nonempty `s`),
  `pinnedMotionsOn_mono`, `pinnedMotionsOn_le_pinnedMotions`. Axiom-clean.
  Green.
- [ ] `lem:cycle-realization` — KT Lemma 5.4. **Decision (2026-06-03):
  formalize as genuine *panel* content — its own sub-phase**, not cite,
  not the free-hinge telescoping reduction (which proved only the
  body-hinge cycle statement; superseded — see DESIGN.md). Statement is
  KT's form (a cycle with `3 ≤ |V| ≤ D` has an infinitesimally rigid
  full-rank `D(|V|−1)` *panel* realization). Needs the panel layer + the
  extensor meet algebra + a generic-panel independence argument bottoming
  on Lemma 2.1. Citation (CW82 Prop 3.4 / Whiteley99 Prop 3) stays as the
  source pointer. Still red.
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
  `|V|` are left for later commits — they are where Cases I/II diverge.
  Needed the `Mathlib.Combinatorics.Graph.Subgraph` import (`≤` on
  `Graph` lives there, not `.Basic`).
- **Case I block-pinning landed at the set-pin level (`pinnedMotionsOn`).**
  The first incremental piece of hand-off #1: rather than build a full
  vertex-quotient contraction op up front, the framework-side carrier of
  "contract rigid `H` to one body" is `pinnedMotionsOn (V(H))` — pin the
  whole block. Generalizes `pinnedMotions v` (= `pinnedMotionsOn {v}`)
  and equals `⨅ v ∈ s, pinnedMotions v` for nonempty `s`, the form Case
  I's block-triangular rank accounting will run against the per-body
  pin-a-body identity. No new mathlib needed; built directly mirroring
  the `pinnedMotions` submodule.
- **Cycle Lemma 5.4 citation work (Phase-local, stands).** Proposition
  numbers verified against the local OCR'd primaries: [4] Crapo–Whiteley
  1982 **Proposition 3.4** (`D=6` case) and [34] Whiteley 1999 Kluwer
  **Proposition 3**; KT attributes "[4, Prop 3.4] or [34, Prop 3]"
  itself. Discharged the *Citation accuracy caveat* in
  MolecularConjecture.md. Corrected a prior mis-statement (the blueprint
  glossed cycle realization as "rank one less" — backwards; short cycles
  are *rigid*, full rank). New bib entry `whiteley1999`.
- **Panel-coplanarity finding + Lemma 5.4 → formalize as panel content
  (2026-06-03).** Cross-cutting; full record promoted to DESIGN. Two
  superseded mid-Phase-21 calls are corrected there: (i) the cite-only
  call on 5.4, and (ii) the later "5.4 reduces to trivial telescoping in
  our free-hinge model" reduction — which proved only the *body-hinge*
  cycle statement (too weak), because `BodyHingeFramework` omits the
  hinge-coplanarity that *defines* panel-hinge. Net: add a **panel
  layer** (per-vertex hyperplanes, hinges as intersections — reuses all
  rank infra) and formalize 5.4 as genuine panel content, its own
  sub-phase. See *Promoted to … DESIGN* below.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *Panel-hinge = hinge-coplanar body-hinge; the coplanarity layer (form
  (A) predicate vs (B) panel-data, (B) chosen); which nodes are reused
  vs gain the panel requirement; Lemma 5.4 formalized as a panel
  sub-phase* → DESIGN.md *Panel-hinge = hinge-coplanar body-hinge: the
  coplanarity layer*; risk #7 in MolecularConjecture.md.

## Blockers / open questions

- **Claim 6.4 / 6.9 genericity** is the new analytic device this phase
  introduces (matrix entries polynomial in alg.-indep. panel coords ⇒
  generic max rank). Reuse the Phase 6/8 genericity machinery
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean` Gram-det LI mirrors,
  `exists_uniform_rowIndependent_placement`-style perturbation) where it
  transfers; assess on contact whether the panel-coordinate
  parametrization needs new infrastructure.
- **Panel-coplanarity re-scope (the active blocker; phase paused).**
  `thm:theorem-55` and the realization-existence nodes as first drafted
  prove the *body-hinge* rank theorem, not the molecular conjecture,
  because `BodyHingeFramework` omits hinge-coplanarity (= what defines
  panel-hinge). Prerequisite for Cases I–III: add a **panel layer**
  (per-vertex hyperplanes, hinges as intersections; reuses all rank
  infra). Decision + (A)/(B) analysis in DESIGN.md; risk #7 in
  MolecularConjecture.md. **Plan-first: no Lean until the plan is
  reviewed.**
- **Lemma 5.4 — formalize as genuine panel content, its own sub-phase**
  (user decision 2026-06-03; was cite-only, then mistakenly reduced to
  free-hinge telescoping). The cycle's panel realization with
  independent hinge extensors is the Crapo–Whiteley projective fact:
  needs the panel layer + the extensor *meet* algebra (hinges as panel
  intersections) + a generic-panel independence argument bottoming on
  Lemma 2.1 (Phase 17). Citation work stands as the source pointer.

## Hand-off / next phase

**Phase 21 is PAUSED for a modeling re-scope (2026-06-03, plan-first).**
The realization-existence statements as first drafted prove the
*body-hinge* rank theorem, not the molecular conjecture, because
`BodyHingeFramework` omits **hinge-coplanarity** (= what defines
panel-hinge; KT p.647). The fix is a **panel layer** and it is a
prerequisite for Cases I–III and Lemma 5.4. Full decision + the (A)/(B)
analysis: `DESIGN.md` *Panel-hinge = hinge-coplanar body-hinge*; risk #7
in MolecularConjecture.md. **No Lean until the plan is reviewed.**

Green so far (all regime-agnostic rank/structure facts — *retained
verbatim* under the panel layer): `def:rank-hypothesis`,
`lem:theorem-55-base` (rank content; gains a coplanarity conjunct when
assembled), `lem:case-II-rank-lift`, `def:framework-with-graph` +
`lem:motions-mono-of-graph-le`, `def:pinned-motions-on`.
`Molecular/AlgebraicInduction.lean` carries six Lean nodes; none are
wasted. Remaining red: `lem:cycle-realization` (now a panel sub-phase),
`prop:rigidity-matrix-prop11` (stays body-hinge), `thm:theorem-55`,
`lem:case-I`, `lem:case-II`, `lem:case-III` (all gain the panel
requirement; III is 22–23).

**Next concrete step (after plan sign-off):** design + land the panel
layer (form (B) — per-vertex hyperplane data, `panelRealization :
(α → Hyperplane) → BodyHingeFramework`, hinges as `panel(u) ∩ panel(v)`,
+ the `IsHingeCoplanar` spec it meets), then restate `thm:theorem-55`
over it. The first Lean commit is the panel constructor + its basic API
(does it reduce to existing `affineSubspaceExtensor` / extensor *meet*?
— scope on contact). Lemma 5.4 (panel cycle realization) and the
re-scoped Cases I/II/III follow. Broad phase; the panel layer may itself
be a sub-phase. Phases 22–23 still pick up Case III.
