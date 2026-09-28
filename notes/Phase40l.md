# Phase 40l — PENCIL-X0 / COVERAGE-REDUCE: the one-step interface, the induction and the deficiency layer (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-28). REDUCE, COVERAGE's first
of three sub-phases (`notes/Phase40-design.md` §3 COVERAGE; the PI's calls in
`notes/pencil/adjudications.md`, 2026-09-28), landed the one-step predicate `X0Reduces`, the strong
induction carried on "every graph satisfying (H) reduces to smaller ones", and the deficiency layer
of the structural half, with the departures D1–D3. **Next: CHAINS** (by code, not yet opened): a
design-first open at the top rung, its first step a spike of its cut half — see *Hand-off*.

## Current state

**Closed.** Three build commits (B1 `42352cea`, B2 `e6fb3fbf`, B3 `776daad5`), three coordinator
fixups (`5cdd034c`, `6cd7e352`, `0eb6298f`) and the close landed. All eleven REDUCE nodes are green:
the nine of `main-component.tex` §`sec:main-component-sparse` (`lem:deficiency-singleton-bound`,
`lem:deficiency-add-body`, `lem:deficiency-sparse`, `lem:deficiency-merge-rigid`,
`lem:deficiency-tight-rigid`, `lem:deficiency-core-bound`, `lem:deficiency-additive-core`,
`lem:deficiency-one-body-chain`, `lem:deficiency-two-body-chain`) and the first two of
§`sec:main-component-coverage` (`def:pencil-x0-reduces`, `thm:pencil-x0-reduction-attains`).

**Still red in §`sec:main-component-coverage`** (unpinned; statements checked at this close against
`scratch/40l/S5Full.lean`): CHAINS' five, `def:pencil-x0-chain`, `lem:pencil-x0-chain-exists`,
`lem:pencil-x0-chain-standing`, `lem:pencil-x0-cycle-reduces`, `lem:pencil-x0-cut-reduces`; and
THEOREM-S' six, `def:pencil-x0-usable-chain`, `lem:pencil-x0-chain-reduces`,
`lem:pencil-x0-planar-rigid-reduces`, `lem:pencil-x0-sparse-count`, `thm:pencil-x0-theorem-s`,
`thm:pencil-x0-coverage`. `thm:pencil-x0-generic-attains` stays red for MOTIVES.

The Lean is `Molecule/Pencil/MainComponent/Coverage.lean` (183 lines; imports `SplitOff.lean`,
`Chain.lean`, `Contract.lean`, `ContractAdditive.lean`) and `Molecular/Induction/SparseDeficiency.lean`
(889 lines; imports `Induction/ReducibleVertex.lean` and the `Graph/Delete.lean` mirror), both leaf
modules in the root import; each module docstring lists its statements. The kit is S4's statements
verbatim except `Graph.partitionDef_induce_id_le_of_maximal`, whose unused `hWV` B3 dropped.

**Headline axioms, re-verified at the close** on 39 declarations: the eighteen
`formalization.yaml` main results and the 21 REDUCE pins. 38 are exactly
`[propext, Classical.choice, Quot.sound]` and `Graph.IsOpenEar` (a structure) is `[propext]`; none
uses `sorryAx`. *Measured, script not retained*: one `#print axioms` line per declaration under
`import CombinatorialRigidity`, run with `lake lean` on the fully built tree (a full `lake build`
first: 2 989 jobs, 0 warnings).

**The spikes** (gitignored `scratch/40l/`, local to this checkout; builder pointers, not evidence):
**keep them**, since CHAINS and THEOREM-S transcribe from `S5Full.lean` (1 930 lines; exit 0 under
`lake lean` at `f7481590`, exactly five `sorry`s, lines 960–982, the plumbing statements). `S1`,
`S4` and `S6Inst.lean` are consumed. Satisfiability (kernel-checked in S6, measured by
`measure.py`) and faithfulness were settled at the open: each `X0Reduces` clause is one step's
hypothesis list verbatim, and the kit states the workbook claims at their Lean strength.

## Architectural choices made up front

- **The route** (the recon's verdict, `notes/Phase40-design.md` §3 COVERAGE): the non-recursive
  `X0Reduces` (not the ruled-out `Covered`), the dispatch, the carried induction, and a partition
  kit on the landed `partitionDef_split_of_sides` and `partitionDef_merge`. Proof-level departures
  D1–D3, in the node proofs and not second-read (the PI's call, the 40k precedent); D4 (no θ
  branch) is THEOREM-S'.
- **The PI's calls (2026-09-28, verbatim in `notes/pencil/adjudications.md`):** three sub-phases
  with named interfaces; D1–D4 in the blueprint; `X0Reduces` adopted; PI decision 2's `hatt` todo
  closed with `hatt` kept; the unconsumed Step MC15–MC16 claims re-homed to the design doc's §2
  *Not needed*.
- **Layout (the recon's, kept):** the interface in `Coverage.lean`, the kit in
  `Induction/SparseDeficiency.lean` beside `SplitOffDeficiency.lean` (`Deficiency.lean` is past the
  tripwire, and nothing outside COVERAGE consumes the kit). D5 pins paid here:
  `Graph.partitionDef_map`, `Graph.deficiencyMerged_le_deficiency`.

## Lemma checklist

All landed with the standard axioms (*Current state*); pins in **bold**.

- [x] **B1** (`42352cea`) — `Coverage.lean`: **`Graph.IsOpenEar`, `Graph.X0Reduces`** →
  `def:pencil-x0-reduces`; **`Graph.X0Reduces.x0Attains`,
  `Graph.X0Attains.of_isX0Graph_of_x0Reduces`** → `thm:pencil-x0-reduction-attains`; with
  `Graph.X0Below`.
- [x] **B2** (`e6fb3fbf`) — `SparseDeficiency.lean`, the value calculus:
  `lem:deficiency-singleton-bound`, `lem:deficiency-add-body`, `lem:deficiency-sparse`,
  `lem:deficiency-merge-rigid` (nine pins, `Graph.deficiencyMerged_le_deficiency` among them).
- [x] **B3** (`776daad5`) — `SparseDeficiency.lean`, the suppliers: `lem:deficiency-tight-rigid`,
  `lem:deficiency-core-bound`, `lem:deficiency-additive-core`, `lem:deficiency-one-body-chain`,
  `lem:deficiency-two-body-chain` (eight pins, `Graph.partitionDef_map` among them).
- [x] **The close** (docs and blueprint, with one Lean docstring chore): the re-read of both
  subsections, the headline axioms, the design doc, ROADMAP and `MolecularConjecture.md`, the
  exposition ledger; the public surfaces left unchanged (the PI's standing call: they update when
  Phase 40 closes).

## Blockers / open questions

- **None for 40l.**

## Hand-off / next phase

**40l is closed. The next concrete step is CHAINS' open** (by code; its letter is minted when it
opens). It is a **design-first recon and open at the top rung (opus), not a sonnet build**: the
builder-side "sonnet likely suffices" framing does not apply to an open. Its first step is a spike
of its cut half, which S5 leaves unspiked: S5's five `sorry`s are exactly CHAINS' plumbing
statements, and the design doc (§3 COVERAGE item 2, *To build*) names the work: a maximal path
through bodies of degree two (serving the chain, the cycle and the bridge chain), (H) at `G[V₁]`
by a cut argument through `G − x₁`, and BRIDGE and CUT with (H) at both sides (cut arguments via
`connected_iff_forall_exists_adj`).

- **CHAINS' interface** is S5's statements, listed in `notes/Phase40-design.md` §3 COVERAGE item 2:
  `Graph.IsChain`, `exists_isChain`, `IsChain.isX0Graph_induce`, `IsX0Graph.splitOff` and its four
  instances, `x0Reduces_of_forall_degree_eq_two`, and the two cut lemmas. Its blueprint nodes are
  the five red ones above; the close restated `lem:pencil-x0-cycle-reduces` and
  `lem:pencil-x0-cut-reduces` so their statements conclude only "reduces", as S5's do (which clause
  is in the proof). About 5–7 builds; files `MainComponent/Chains.lean`, split into a `Cuts.lean`
  past the ~1500-line tripwire. Every new top-level name greps to no prior definition (the open's
  check); root-level `IsChain` (mathlib, sets) exists, so use `Graph.IsChain` qualified or by dot
  notation.
- **Then THEOREM-S** (about 2 builds; closes COVERAGE), sorry-free in S5 over CHAINS' interface.
  At its one call of `Graph.partitionDef_induce_id_le_of_maximal` (S5's
  `exists_additiveCore_of_rigid`), drop S5's `hWV` argument; the producer's own `hWV` stays (for
  `W ⊂ V(G)` and `deficiency_induce_add_deficiency_rigidContract_le`). The close restated
  `lem:pencil-x0-chain-reduces` and `lem:pencil-x0-planar-rigid-reduces` the same way.
- **Then MOTIVES**, which closes Phase 40 and updates the public surfaces.

## Decisions made during this phase

- **2026-09-28 — the close.** The re-read restated `lem:deficiency-merge-rigid` (1) at its Lean
  strength (some coarsening with `W` in one part, not the merge itself; the proof builds the
  merge) and adjusted the core bound's proof to match; expanded that proof's part (2) as the
  exposition-ledger write-up; and restated four red nodes to conclude only "reduces", as S5 does.
  One Lean chore: four docstring passages in `SparseDeficiency.lean` (the module summary's
  wrong-way "sparse-set-is-rigid", the D5 sentence, and two chain docstrings stated at `G − x`
  for lemmas about any `V₁ ∌ x`).
- **B1–B3** — landed verbatim from the spikes with fresh docstrings, all 25 of S4's warnings
  fixed on transcription; the coordinator fixups corrected a module docstring, a hand-off path, a
  proof-level `\leanok` and a hypothesis in a docstring bullet.
- **2026-09-28 — opened design-first** from COVERAGE's design recon (opus, read-only,
  compiler-checked); the spikes re-run at `f7481590` with `lake lean` matched the coordinator's.
