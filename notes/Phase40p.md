# Phase 40p — PENCIL-X0 / MOTIVES-REDUCE+CLOSE: the good ear, the route-B assembly and both headlines (work log)

**Status:** in progress (opened design-first 2026-09-29). MOTIVES' third and last sub-phase (the
PI's call, 2026-09-28; plan `notes/Phase40-design.md` §3 MOTIVES): after DIST+BASE (40n) and EARS
(40o), **REDUCE+CLOSE** greens Phase 40's last five red nodes: (MC-129) at two-edge-connected
graphs, the route-B assembly and both headlines. **B1 landed**: all five nodes are `\leanok`,
warning-free `lake build`/`lake lint`, green `blueprint/verify.sh`/`lint.sh`, and the standard three
axioms on all nine pinned declarations. **Next: the Phase 40 close** — see *Hand-off*.

## Current state

**B1 landed.** All five nodes are green: `lem:pencil-rigid-good-ear`, `thm:pencil-generic-step`,
`thm:pencil-conditioned-pair-nonempty` and `thm:pencil-x0-generic-attains` (`main-component.tex`
§`sec:main-component-statements`), and `thm:pencil-conjecture` (`pencil.tex`), each `\leanok` on its
statement and its proof, pinned as follows:
- `lem:pencil-rigid-good-ear` ← `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`,
  `Graph.exists_eq_triple_of_minimal`, `Graph.exists_closedEar_two_of_triangle`;
- `thm:pencil-generic-step` ← `CombinatorialRigidity.Molecular.hasGenericPencilRealization_of_IH`;
- `thm:pencil-conditioned-pair-nonempty` ← `CombinatorialRigidity.Molecular.pencilPair_of_nonempty`,
  `CombinatorialRigidity.Molecular.pencilPair_of_IH`;
- `thm:pencil-x0-generic-attains` ← `Graph.IsX0Graph.x0Attains`, `CombinatorialRigidity.Molecular.x0Dist`,
  `CombinatorialRigidity.Molecular.x0Gen`;
- `thm:pencil-conjecture` ← `CombinatorialRigidity.Molecular.pencil_conjecture`,
  `CombinatorialRigidity.Molecular.pencilPair_of_nonempty`;
- `lem:deficiency-add-body` (green) gained `Graph.partitionDef_two_induce_insert_id` in its
  `\lean{}`: its statement at the singleton partition, `D = 3`, so no text change.

Placement: `partitionDef_two_induce_insert_id` sits in `Molecular/Induction/SparseDeficiency.lean`
right after `partitionDef_induce_insert`; the three good-ear declarations are a new
`Molecular/Molecule/Pencil/MainComponent/GoodEar.lean` over `MainComponent/CoverageTheoremS.lean`
alone; the assembly and both headlines are in `MainComponent/Statements.lean`, alongside `x0Dist`.
Gates run clean: `lake build` and `lake lint` warning-free, `blueprint/verify.sh` and `lint.sh`
green, and `#print axioms` on all nine pinned declarations gives the standard three
(`propext, Classical.choice, Quot.sound`).

**The red-node consistency gate, run at this open.** Each of the five proofs routes through the
argument its statement claims, and the good-ear proof is now the Lean route. Every `\uses` label
exists and is live (`blueprint/lint.sh`); none points at a superseded node.

**The spikes** (gitignored `scratch/40p/`, local to this checkout; builder sources, not evidence;
**keep them** until the close). All ran with `lake lean` at `23f31681`; the coordinator's re-run of
`Ax.lean` matched:
- `Close.lean` (488 lines, **the build source**): exit 0, 0 warnings, no `sorry`, no `#print`.
  Its shape: l.1–12 the header (`import CombinatorialRigidity`, `namespace
  CombinatorialRigidity.Molecular`), then the nine declarations in B1's order, then l.488 `end`.
- `Ax.lean`: `Close.lean` plus nine `#print axioms` lines and `#lint`. Every line reads
  `[propext, Classical.choice, Quot.sound]`, and the lint finds 0 errors in 9 declarations.
- Placement tests, each over its target's imports only, all exit 0 with 0 warnings:
  `PlaceSparse.lean`, `PlaceGoodEar.lean` and `StatementsImports.lean`.
- `Alt.lean`: the off-route alternatives (*Architectural choices* 4; `not_adj_of_oneEar`, choice 1).

A session without them rebuilds B1 from `scratch/ears/Route.lean`'s tail (l.2159 on, also local)
and this note: the (MC-129) proof is the one in `lem:pencil-rigid-good-ear`'s blueprint proof.

## Architectural choices made up front

The coordinator's calls, 2026-09-29, on the recon's verdict:
1. **Drop `¬ G.Adj a b`** from `exists_oneEar_or_pendantTriangle`'s one-ear disjunct and "non-adjacent"
   from the good-ear node (the Z1 precedent). No consumer: the landed one-ear step takes no `hnadj`.
   (F2) gives it if one is ever needed (`Alt.lean`, `not_adj_of_oneEar`, five lines).
2. **N1–N4 recorded in the good-ear node's blueprint proof, not second-read**: the PI's 40k/40l
   precedent (`notes/pencil/adjudications.md`, 2026-09-28 COVERAGE entry: proof-level departures,
   compiler-checked, recorded in the blueprint). **The PI may overturn it at the close.** N1: the
   all-hub case by the count at one edge, not "a cycle". N2: no chain walk, only the pair `y`, `u`.
   N3: step 4's rigidity by the tight-set lemma, not connectivity and bridges. N4: minimality only
   through (S) on proper subsets.
3. **`thm:pencil-x0-generic-attains` pins all three of its claims** (a shared pin has precedent: seven
   declarations are already pinned by two nodes each), restated to begin "Let $K$ be an infinite
   field", since `Graph.IsX0Graph.x0Attains` needs `[Infinite K]`.
4. **`pencil_conjecture` keeps the PI's form**, `pencil_conjecture_of_X0 x0Dist x0Gen`. Off-route
   alternative, for the PI: `pencilPair_of_nonempty G (hspan ▸ Set.univ_nonempty)`, which needs no
   `[DecidableEq β]` and no linter suppression (compiled, `Alt.lean`).
5. **Placement**, the PI's convention: the add-one-body identity beside `partitionDef_induce_insert`;
   (MC-129) and its two helpers in a new `MainComponent/GoodEar.lean` over `CoverageTheoremS` alone,
   so no chart stack and no `Sum` in its cone; the assembly and both headlines in
   `MainComponent/Statements.lean`, a leaf, so the `Sum` import enters no other cone.
6. **One build commit (B1)**, then the Phase 40 close.

## Lemma checklist

- [x] **B1** (one sonnet transcription commit; greens all five nodes). Source
  `scratch/40p/Close.lean`, three ranges, transcribed verbatim except as noted:
  - **l.14–28** `Graph.partitionDef_two_induce_insert_id` → `Molecular/Induction/SparseDeficiency.lean`,
    right after `partitionDef_induce_insert` (ends l.336), written `theorem
    partitionDef_two_induce_insert_id` (the file is `namespace Graph`). Add it to the module
    docstring's `lem:deficiency-add-body` bullet. Imports unchanged.
  - **l.30–392** → new `Molecular/Molecule/Pencil/MainComponent/GoodEar.lean`:
    `Graph.exists_eq_triple_of_minimal` (l.30–100), `Graph.exists_closedEar_two_of_triangle`
    (l.102–206), `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle` (l.208–392). Header: the
    copyright block; `import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.CoverageTheoremS`
    only; a module docstring listing the three; `open scoped Graph`; `namespace
    CombinatorialRigidity.Molecular`; `variable {α β : Type*}` (as `PlaceGoodEar.lean`). Root import:
    `import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.GoodEar` in
    `CombinatorialRigidity.lean`, between `…MainComponent.GenericTriangle` and `…MainComponent.Lines`.
  - **l.394–486** → `MainComponent/Statements.lean`, after `x0Dist` and before `end`:
    `hasGenericPencilRealization_of_IH`, `pencilPair_of_IH`, `pencilPair_of_nonempty`, `x0Gen`,
    `pencil_conjecture`. Keep `set_option linter.unusedDecidableInType false in` and put
    `Pencil/X0.lean` l.341–343's justification comment above it. The import block becomes `…Pencil.X0`,
    `…Pencil.Base`, `…MainComponent.CoverageTheoremS`, `…MainComponent.GenericBase`,
    `…MainComponent.GenericEar`, `…MainComponent.GenericTriangle` and `…MainComponent.GoodEar`
    (all under `CombinatorialRigidity.Molecular.Molecule`). Retitle the module docstring and extend
    its *Main statements*.
  - **Blueprint**: the pins above, and `\leanok` on the statement and the proof of each red node.
  - **Gates** (`CombinatorialRigidity/CLAUDE.md` *Before each commit*): a warning-free `lake build`,
    `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`, `#print axioms` on each pin (standard
    three), no `#print axioms` in any library file (40o's recorded defect), the honesty gate by eye
    on each `\leanok`.
- [ ] **The Phase 40 close** (`PHASE-BOUNDARIES.md` *When this commit closes a phase*): re-read the
  five nodes, headline axioms, the design doc, ROADMAP, `notes/MolecularConjecture.md`, the
  exposition ledger, and the three carried items (*Hand-off*).

## Blockers / open questions

- **None for the close.** The three carried items (*Hand-off*) are PI calls, not blockers on
  closing the phase.

## Hand-off / next phase

**B1 landed; next concrete step: the Phase 40 close** (`PHASE-BOUNDARIES.md` *When this commit
closes a phase*): re-read the five nodes, the headline axioms, the design doc, ROADMAP,
`notes/MolecularConjecture.md`, and the exposition ledger. **It carries three items the recon did
not settle** (coordinator, 2026-09-29):
- re-deciding the held kernels (`notes/Phase40-design.md` §6: (K-res)/`kres`, (K-c), (K-bare-c)
  with (α), smark's O7e programme): **the PI's call**, surfaced with options, not decided by the
  close;
- writing or closing the two `[pending]` exposition entries (design doc §7,
  `notes/BlueprintExposition.md`);
- the public surfaces (README, home_page, intro.tex, `formalization.yaml`; the PI's standing call).

The PI may also overturn choice 2 (N1–N4 without a second read) there.

## Decisions made during this phase

- **2026-09-29 — opened design-first** from REDUCE+CLOSE's pre-build recon (opus, read-only,
  compiler-checked; spikes in `scratch/40p/`). All of it compiled sorry-free with standard axioms
  and a clean `#lint`: (MC-129) at 2EC graphs by a shorter count than the workbook's (N1–N4), and the
  assembly from `scratch/ears/Route.lean`'s tail with the one-ear call one argument shorter.
  (MC-15)(i) step 2 is not landed in the bridgeless form and is not needed. No statement goes
  beyond the second-read workbook.
- **The blueprint restatement** (this open): the good-ear node assumes the standing hypotheses and
  drops "non-adjacent", and its proof is the Lean route with N1–N4 recorded; the section intro drops
  "non-adjacent" too. `thm:pencil-x0-generic-attains` begins "Let $K$ be an infinite field".
  `thm:pencil-conjecture` is unchanged: its "whole ambient body set" is `[Nonempty α]`, the
  convention of the green `thm:pencil-conditional-realization-main-component`. The workbook's
  (MC-129) gains a one-line pointer to the Lean route.
- **2026-09-29 — B1 landed**: the recon's spike transcribed verbatim to its three planned places
  (*Current state*); no gap surfaced. All gates green; the standard three axioms on all nine
  pinned declarations. Phase 40's last five red nodes are green.
