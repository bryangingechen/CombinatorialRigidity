# Phase 43c — NORMAL and SPRIME: the reduction on structural cases, then Theorem S′ (work log)

**Status:** ✓ closed 2026-11-08 (opened the same day with the PI), the third sub-phase of Phase 43
(PENCIL-NATURAL), which stays in progress: layers NORMAL and SPRIME as one sub-phase, at the PI's
word (design doc §1). Seven commits: slice 1, SPRIME's pin, slice A, the PI's review of the pin,
slices B and C, and the close. What comes next is *Hand-off*. Plan: `notes/Phase43-design.md`.

## Current state

**Closed.** The reduction is on five structural cases, with no dimension in its statement and no
induction hypothesis in its simple two-edge-connected case, and the minimum-degree lemma is in a new
appendix of further results. Theorem S′ holds at `d = 3` (`Graph.IsX0Graph.exists_additiveCore`, its
hypothesis weaker by two usable-chain disjuncts), its proof citing the maximal-rigid-core lemma, so
the open ear with two interior bodies and the split-off step left the `d = 3` coverage, with the
`d = 3` core bound. Measured against the open (`4f5fbeab`): 23 declarations went and 2 came (NEW-1
`Graph.exists_deficiency_three_induce_eq_zero_of_deficiency_two_lt`, NEW-2
`Graph.IsOpenEar.exists_additiveCoreAt_of_deficiency_induce_eq_zero`), `Graph.pencil_reduction`
moved to `Grade/Reduction.lean` (22 Lean files, +428 / −1,795 lines; `MainComponent/SplitOff.lean`,
`Mathlib/Data/Matrix/Mul.lean` and `Mathlib/Algebra/MvPolynomial/Polynomial.lean` whole); 13
dep-graph nodes and `sec:main-component-splitoff` went, none came, and `lem:pencil-min-degree-rigid`
moved to `further-results.tex`. The four main results' signatures are byte-identical; at the close
all 21 `formalization.yaml` main results print the standard three axioms, byte-identical to 43b's
close run net of the harness path, and so does `Graph.graded_pencil_realization_theorem`.

**Records left as they are.** `notes/pencil-natural/SprimeSpike.lean` and `sprime_walk.py` are
the pin's banked records: they name declarations slices B and C deleted, and the walk no longer
sweeps. `ROADMAP.md`'s Phase-40 paragraph keeps "the cut, bridge, ear, split-off and contraction
steps" as the record of what Phase 40 built.

## Architectural choices made up front

- **Statements byte-identical** (held): `pencil_realization_theorem`, `pencilPair_of_nonempty`,
  `Graph.graded_pencil_conditioned_pair`, `Graph.graded_pencil_realization_theorem`; each Lean
  slice diffed their signatures and ran `#print axioms` (the standard three).
- **Statements that change, by design** (held): `Graph.pencil_reduction` (slice 1);
  `Graph.ChainUsable`, `Graph.X0Reduces` and so `Graph.IsX0Graph.exists_additiveCore`'s hypothesis
  (slice B). None is a main result.
- **S′ at `d = 3` only** (held, the PI, design doc §1): `thm:pencil-d-theorem-s`,
  `def:pencil-d-usable-chain` and their Lean deleted, not restated in every `d`.
- **Slice boundaries from the bodies** (held): SPRIME's slices are the pin's kernel walk.

## Lemma checklist

- [x] **1. Slice 1 — NORMAL: the reduction on five structural cases** (`2b010699`; plan
  `git show 4f5fbeab:notes/Phase43c.md`).
- [x] **2. SPRIME's pin** (`27fd2c06`, docs only; plan `git show 2b010699:notes/Phase43c.md`).
- [x] **3. SPRIME slice A — NEW-1 and NEW-2** (`9fb254e4`; plan
  `git show 27fd2c06:notes/Phase43c.md`).
- [x] **4. SPRIME slice B — S′ at `d = 3`, and the `d = 3` core bound** (`f0c2f898`; plan, with
  the PI's review `bd63d237`, `git show bd63d237:notes/Phase43c.md`).
- [x] **5. SPRIME slice C — the two steps and what only they use** (`b9e9e2b2`; plan
  `git show f0c2f898:notes/Phase43c.md`).
- [x] **6. Close (43c).** The sub-phase close of `PHASE-BOUNDARIES.md` (this commit; *Decisions*).

## Blockers / open questions

None. The two questions slice 1 left (the KT Theorem 4.9 remark, where `thm:pencil-reduction`
lives) are EXPO's, in `notes/Phase43-design.md` §2.

## Hand-off / next phase

No sub-phase of Phase 43 is open. The next concrete step is EXPO's open, at the PI's word: the
last layer, a road map of the proof in the manner of KT §1.1 (`notes/Phase43-design.md` §2, EXPO,
with the items 43b and 43c left it).

## Decisions made during this phase

The open's decisions are `notes/Phase43-design.md` §1 (the PI's answers of 2026-11-08) and the
choices above.

- **S′'s proof cites the maximal-rigid-core lemma, and the `d = 3` core bound goes** (the PI,
  2026-11-08, reviewing the pin's choice taken in the PI's absence, which kept S′'s own `d = 3`
  argument through `lem:deficiency-core-bound`; the PI's words: design doc §1). The PI: "was there
  an opportunity for extra simplification using the maximal-rigid-core lemma? If so, I'd go with
  that." Then, of the `d = 3` node and its two Lean pins: "Would those results be independently
  interesting? If so we could put them in an appendix like we have been for some others, but if
  not then we can lose them." They are the case `d = 3` of the kept `lem:deficiency-core-bound-d`,
  so they go (item 4).
- **Slice B** (item 4): S′'s cores come from `lem:pencil-d-maximal-rigid-core`, directly or
  through `lem:pencil-d-chain-core`, or from `lem:pencil-d-core-positive-deficiency`; part (2) of
  `lem:deficiency-core-bound-d` reads with `def_d` only. Landed slices were swept by
  boundary-checked grep, as the walk no longer sees their names.
- **Slice C** (item 5): `rem:pencil-x0-theta` sends the `θ`-graphs with `k = 2` that
  `thm:pencil-x0-open-ear-two-orbit` misses to the coverage (`θ(1,3,3)` at a core).
- **SPRIME's pin** (item 2): S′ holds as Lean in the folded form, every consumer re-checked in the
  kernel; under S′ a sparse `θ`-graph may have no usable chain, so a core is reached instead.
- **The count that finds the bodies of degree two** (slice 1): part (1) of
  `lem:pencil-x0-sparse-count`; `lem:pencil-d-chain-count` is KT Lemma 4.6's edge count. The
  recon's "heir of KT Lemmas 4.5–4.6" is EXPO's to word (design doc §2).
- **The close**: no exposition-ledger entry (`notes/BlueprintExposition.md`, Phase 43c); one
  sentence reworded at the coordinator's word (`rem:pencil-x0-theta`, "that the ends not be
  adjacent"), and the re-read of 43c's prose found nothing else to change;
  `check-phase-note.py --selftest` green between sub-phases, its first live use.
