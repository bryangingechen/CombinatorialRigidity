# Phase 40l — PENCIL-X0 / COVERAGE-REDUCE: the one-step interface, the induction and the deficiency layer (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). REDUCE, COVERAGE's
first sub-phase (`notes/Phase40-design.md` §3 COVERAGE; the PI's calls in
`notes/pencil/adjudications.md`, 2026-09-28), landed the one-step predicate `X0Reduces`, the
strong induction carried on "every graph satisfying (H) reduces to smaller ones", and the
deficiency layer of the structural half, with the proof-level departures D1–D3. Phase 40
continued with **CHAINS with THEOREM-S folded in** (`notes/Phase40m.md`, closed 2026-09-28) and
on through the phase's own close, 2026-09-29 (`notes/Phase40-design.md` §3, ROADMAP §40).

## Current state

**Closed.** Three build commits (B1 `42352cea`, B2 `e6fb3fbf`, B3 `776daad5`), three coordinator
fixups (`5cdd034c`, `6cd7e352`, `0eb6298f`) and the close landed. All eleven REDUCE nodes are
green: the nine of `main-component.tex` §`sec:main-component-sparse` (the deficiency value
calculus, `lem:deficiency-singleton-bound` through `lem:deficiency-two-body-chain`) and the first
two of §`sec:main-component-coverage` (`def:pencil-x0-reduces`, `thm:pencil-x0-reduction-attains`).
The Lean is `Molecule/Pencil/MainComponent/Coverage.lean` (the interface) and
`Molecular/Induction/SparseDeficiency.lean` (the kit, S4's statements verbatim but for one
dropped unused hypothesis on `Graph.partitionDef_induce_id_le_of_maximal`), both leaf modules in
the root import. Headline axioms were re-verified at the close on 39 declarations (the eighteen
`formalization.yaml` main results and the 21 REDUCE pins): 38 exactly
`[propext, Classical.choice, Quot.sound]`, `Graph.IsOpenEar` (a structure) `[propext]`.

The gitignored spikes (`scratch/40l/`): `S5Full.lean` (exit 0 under `lake lean`, exactly five
`sorry`s, the plumbing statements) supplied 40m's CHAINS and THEOREM-S builds verbatim; `S1`, `S4`
and `S6Inst.lean` are consumed. Satisfiability (kernel-checked in S6) and faithfulness were
settled at the open: each `X0Reduces` clause is one step's hypothesis list verbatim.

## Architectural choices made up front

**The route** (the recon's verdict): the non-recursive `X0Reduces` (not the ruled-out
`Covered`), dispatch by case analysis on `G`'s structure, the carried induction, and a partition
kit on the landed `partitionDef_split_of_sides` and `partitionDef_merge`. **Proof-level
departures D1–D3** (kernel-checked in S4/S5, recorded in the node proofs, not second-read: the
PI's call, the 40k precedent; full statements in `notes/Phase40-design.md` §3 COVERAGE): D1
bounds every singleton value above a maximal rigid set avoiding `X₀`, by a minimal counterexample;
D2 refines the part holding `a, b` in an optimal merged partition, for the one-body-chain bound;
D3 shows a tight set of three or more bodies in an (S)-graph is rigid directly. None needs the
partition into maximal rigid sets and its rigid-free quotient the informal proofs pass through.
D4 (no θ branch) is THEOREM-S'. **The PI's calls** (2026-09-28, verbatim
`notes/pencil/adjudications.md`): three sub-phases with named interfaces; D1–D4 in the blueprint;
`X0Reduces` adopted; PI decision 2's `hatt` todo closed with `hatt` kept; the unconsumed Step
MC15–MC16 claims re-homed to the design doc's §2 *Not needed*.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read restated `lem:deficiency-merge-rigid` (1) at its Lean
  strength (some coarsening with `W` in one part, not the merge itself) and four red nodes to
  conclude only "reduces", as S5 does; expanded the core bound's proof as the exposition-ledger
  write-up.
- **B1–B3** landed verbatim from the spikes with fresh docstrings, all 25 of S4's warnings fixed
  on transcription; the coordinator fixups corrected a module docstring, a hand-off path, a
  proof-level `\leanok` and a hypothesis in a docstring bullet.
- **Layout** (the recon's, kept): the interface in `Coverage.lean`, the kit in
  `Induction/SparseDeficiency.lean` beside `SplitOffDeficiency.lean`. D5 pins paid here:
  `Graph.partitionDef_map`, `Graph.deficiencyMerged_le_deficiency`.

## Hand-off / next phase

**40l is closed; COVERAGE continues in 40m**, CHAINS with THEOREM-S folded in (the PI's call at
40m's open, 2026-09-28): work log `notes/Phase40m.md`. Then MOTIVES, which closed Phase 40 and
updated the public surfaces.
