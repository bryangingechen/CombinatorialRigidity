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

Phase just opened. This commit lays down the forward-mode blueprint
chapter `algebraic-induction.tex` (all nodes red — the to-do list),
creates this work log, flips the ROADMAP status row to *in progress*,
and syncs the user-facing status surfaces (README, home_page, intro.tex).
No Lean yet. The next concrete commit takes the leaf-most red node
(statement deps all green or mathlib) — likely `lem:cycle-realization`
(Crapo–Whiteley Lemma 5.4 input) or `lem:theorem-55-base` (the `|V|=2`
base case via the green parallel-hinges Lemma 5.3,
`lem:rank-parallel-full`) — and starts `Molecular/AlgebraicInduction.lean`.

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
- [ ] `def:rank-hypothesis` — the realization hypothesis (6.1): a
  panel-hinge realization at `rank = D(|V|−1) − k`, nonparallel if simple.
- [ ] `thm:theorem-55` — KT Theorem 5.5, the capstone of this phase.
  Induction on `|V|` over the Phase-20 reduction dichotomy.
- [ ] `lem:theorem-55-base` — `|V|=2` base case; full rank `D` via
  `lem:rank-parallel-full` (Phase 18, green).

Case I (proper rigid subgraph; KT §6.2):
- [ ] `lem:cycle-realization` — Crapo–Whiteley Lemma 5.4 input.
- [ ] `lem:case-I` — KT Lemmas 6.2/6.3/6.5: contract a proper rigid
  subgraph `H` (smaller minimal `k`-dof by green `lem:contraction-minimality`),
  glue block-triangularly with a pinned rigid realization of `H`
  (`lem:rank-delete-vertex`, Phase 18 green). Claim 6.4 genericity.

Case II (`k>0` splitting; KT §6.3):
- [ ] `lem:case-II` — KT Lemmas 6.7/6.8: splitting off a reducible
  degree-2 vertex (smaller minimal `k`-dof by green `lem:reduction-step`),
  the panel-hinge analogue of Whiteley's bar-joint 1-extension; re-insert
  `v` to lift the rank by `D`. Claim 6.9 genericity.

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
- *(none yet — phase just opened)*

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
- **Cycle Lemma 5.4 formalize-vs-cite** decision pending — re-confirm the
  exact proposition numbers in Crapo–Whiteley [4] / Whiteley Kluwer 1999
  before pinning, per MolecularConjecture.md *Citation accuracy caveat*.

## Hand-off / next phase

Phase just opened; nothing to hand off yet. The next concrete commit
takes the leaf-most red node in `algebraic-induction.tex` — the base
case `lem:theorem-55-base` (deps all green: `lem:rank-parallel-full`,
`def:rank-hypothesis`) or the cycle-realization input
`lem:cycle-realization` — and starts `Molecular/AlgebraicInduction.lean`.
Broad phase; may split Case I from Case II (precedent: Phases 8–11 spawned
sub-phases). Phases 22–23 pick up Case III (the crux).
