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
the panel-hinge 1-extension). This commit settles the cycle input
`lem:cycle-realization` (KT Lemma 5.4) as a **verified cite** — not Lean:
its proposition numbers ([4] Crapo–Whiteley 1982 Prop 3.4, [34] Whiteley
1999 Kluwer Prop 3) were checked against the local OCR'd primaries and
pinned, the statement was corrected to KT's form (short cycles are
*rigid* = full rank, not "one short"), and a `whiteley1999` bib entry was
added. The dep-graph node stays red (external input, no `\leanok`). Still
red: `prop:rigidity-matrix-prop11`, `thm:theorem-55`, `lem:case-I`,
`lem:case-II` (all gating on the framework-construction op + genericity
device, see *Hand-off*), and `lem:case-III` (deferred to 22–23).

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

Case I (proper rigid subgraph; KT §6.2):
- [~] `lem:cycle-realization` — KT Lemma 5.4, **cite-only** (decision
  made; see *Decisions made* below). Statement corrected to KT's form
  (a cycle graph with `3 ≤ |V| ≤ D` has an infinitesimally rigid =
  full-rank `D(|V|−1)` nonparallel realization), citation pinned to the
  verified primary sources Crapo–Whiteley 1982 Prop 3.4 + Whiteley 1999
  (Kluwer) Prop 3. No `\leanok` (external geometric input, not
  formalized); dep-graph node stays red.
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
- **Cycle Lemma 5.4 (`lem:cycle-realization`): cite, don't formalize.**
  KT's Lemma 5.4 — a cycle graph with `3 ≤ |V| ≤ D` has an
  infinitesimally rigid nonparallel panel-hinge realization (= full rank
  `D(|V|−1)`) — is a projective-geometry fact KT themselves cite to
  external sources rather than reprove (the Grassmann-line-geometry
  independence of the `k` hinge lines). Cited, not formalized; the node
  stays red (no `\leanok`). Proposition numbers verified against the
  local OCR'd primaries before pinning: [4] Crapo–Whiteley 1982
  **Proposition 3.4** (`.refs/`, French+English columns p.25, `D=6`
  case) and [34] Whiteley 1999 Kluwer **Proposition 3** (p.5); KT
  attributes "[4, Proposition 3.4] or [34, Proposition 3]" itself. This
  discharges the *Citation accuracy caveat* in MolecularConjecture.md.
  Also corrected a prior mis-statement: the blueprint had glossed cycle
  realization as "rank one less than the free value" — backwards; short
  cycles (`|V| ≤ D`) are *rigid*, i.e. full rank. New bib entry
  `whiteley1999` (verified against KT ref [34]; editor initials
  corrected from KT's OCR-typo'd "Thorpe, O., Duxbury, O.").

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
- ~~Cycle Lemma 5.4 formalize-vs-cite decision~~ — **resolved this
  commit**: cite-only, proposition numbers verified and pinned ([4]
  Prop 3.4, [34] Prop 3). See *Decisions made*. Citation caveat in
  MolecularConjecture.md discharged for Phase 21.

## Hand-off / next phase

Base case (`def:rank-hypothesis` + `lem:theorem-55-base`), the Case II
`+D` rank-lift accounting (`lem:case-II-rank-lift`), and now the cycle
input (`lem:cycle-realization`, cite-only) are settled.
`Molecular/AlgebraicInduction.lean` carries the three Lean nodes;
`lem:cycle-realization` is a verified cite (no Lean). The remaining red
nodes (`prop:rigidity-matrix-prop11`, `thm:theorem-55`, `lem:case-I`,
`lem:case-II`) all gate on the same two not-yet-built pieces.

The next concrete commit must build one of those two pieces (neither
exists yet, so the next step is infrastructure, not a leaf node):
1. **Framework-construction op.** Case I needs the contraction `G/E(H)`
   realized as a `BodyHingeFramework`; Case II needs the splitting-off
   `G_v^{ab}` (re-insert `v` with two hinges). No vertex-deletion /
   extension / contraction op exists on `BodyHingeFramework` yet — this
   is the prerequisite for both full Cases. Likely its own commit (or a
   small series): define the op + its `infinitesimalMotions` /
   `pinnedMotions` relationship to the parent framework, reusing the
   pin-a-body identity (`finrank_pinnedMotions_add_screwDim`).
2. **Claim 6.4 / 6.9 genericity device** (Blockers): matrix entries are
   polynomials in alg.-indep. panel coords ⇒ a generic point attains max
   rank. Assess whether the Phase 6/8 genericity machinery transfers or
   the panel-coordinate parametrization needs new infrastructure; the
   first step here is that *assessment* (a scoping commit / FRICTION
   entry), since it determines whether Cases I/II are one commit or
   several.

Smallest forward step: start the framework-construction op (#1) — it is
the shared, citation-free prerequisite both Cases need, and it can land
its `pinnedMotions`-relationship lemma incrementally before the
genericity device is in place. Broad phase; may split Case I from Case II
(precedent: Phases 8–11). Phases 22–23 pick up Case III (the crux).
