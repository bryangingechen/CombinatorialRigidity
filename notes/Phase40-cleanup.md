# Phase 40 cleanup round 1/5 — `40-cleanup`, the mechanical round (work log)

**Status:** in progress (opened 2026-09-29). Round 1 of the five post-Phase-40 cleanup rounds.
Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` A and B over what Phases 39–40 built, C as screening only, and five carried items.
Tasks 1–13, 14a–14b, 15 and 16 landed; 31 of 49 one-commit tasks remain. **Next concrete task:**
task 17, M2c-ii, deriving `Short.lean`'s `splitOff_ear_three` from `splitOff_ear_four` via
`Fin.succAbove 1` (Lean). Round manual: `CLEANUP.md`.

## Current state

**Next commit: task 17, M2c-ii** (*Lemma checklist*). The checklist holds 49 one-commit tasks;
tasks 1–13, 14a–14b, 15 and 16 landed, 31 remain. Nothing is mid-stream.

Landed so far, one line each under the checklist: tasks 1–13 (T1, B3 with its corrective
follow-up, B8, B7, F1, B6a, B6b, B6c, B5, B1a, B1b, B1c, B1d, M3), 14a–14b, 15 and 16. Outcome
detail goes on the task's checklist line, not here, so this section stays the forward pointer.

**Verified at the open** (`06d175b8`; its Lean and blueprint trees are identical to `91fcd24a`'s):
- Whole-project `lake build` green, 3000 jobs, 0 `warning:` lines, 0 `failed to cache artifact`.
- `#print axioms` on all **19** `formalization.yaml` main results gives `[propext,
  Classical.choice, Quot.sound]`. The check is a scratch file that imports each result's `file:`
  module and prints its axioms, run with `lake lean` (`scratch/40-cleanup/`, gitignored). Re-run it
  the same way at the close.

**How the open's figures were measured** (measured, script not retained; `HARNESS.md`
*Reproducibility*). The §B counts are `CLEANUP.md` §B's greps, verbatim, plus `maxHeartbeats`. They
cover every line of the pencil tree, but only the lines Phase 40 added in the files outside it
(the `+` side of `git diff -U0 c9d26ef9^ 91fcd24a -- <file>`). The §C ranking measures each
declaration from its header line to the next column-0 line, because `CLEANUP.md`'s awk stops a
proof at its first blank line past 50 lines. The recurring `rw` towers come from counting
consecutive argument pairs and triples across the 149 four-plus-argument `rw` chains. Line numbers
below are as of the open; the declaration names are the stable reference.

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2, restated only as far as a builder needs them:

- **Lean surface.** `Molecular/Molecule/Pencil/**` (40 files, 34 363 lines; every line), plus the
  lines Phase 40 added in 26 files outside it (`git diff --stat c9d26ef9^ 91fcd24a --
  CombinatorialRigidity/`).
- **Blueprint surface.** `pencil.tex`, `main-component.tex`, and Phase 40's nodes in
  `deficiency.tex` (6) and `rigidity-matrix.tex` (11). Also Phase 40's three nodes in
  `molecular-induction.tex` (2) and `panel-layer.tex` (1): the open's blueprint diff surfaced them,
  and they pin Lean inside the surface.
- **Hygiene only.** Headline statements and blueprint statement strength stay as they are. A
  finding that would change either goes to *Candidates for `40-simplify`*. It is not acted on, and
  it is not a stop. §C is screening only: land a local change (a tactic substitution, a missed
  mathlib lemma, a small extraction), and record anything structural as a candidate.
- **Not in this round** (already planned elsewhere, `notes/Cleanup40.md` §2): the hub
  normalization (round 2); the build-or-leave items, meaning the D5 blueprint debt, A6 and item 6's
  other laws, the "only if" halves of (MC-52)/(MC-53), and the edge-restricted row rank (round 3);
  `CLEANUP.md` D (round 5).
- **Gates, every commit.** Lean commits: `LAKE_CACHE_DIR` set, one whole-project `lake build` in
  the foreground, no `warning:` lines and no `failed to cache artifact` lines in the full output,
  and `lake lint` green. Blueprint commits: `blueprint/CLAUDE.md` *Static checks before commit*.
  Also a friction review, and this log's checklist and *Current state* / *Hand-off* updated
  (`CLEANUP.md` *Workflow* rule 3). A statement move, deletion or node split also runs
  `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*.
- **Standing file-size rule** (40h's plan, `notes/Phase40-design.md` §3 SHORT). `Short.lean` is at
  1 366 lines and `RigidityMatrix/Bricks.lean` at 1 458. A commit that would take `Bricks.lean`
  past ~1500 first splits its section `TwoCutCarriers` into its own file. A commit that would take
  `Short.lean` past ~1500 first splits out its antecedent and base-data layer (`## The antecedent
  G″` through `## The base data …`).
- **⚠Z marks a fragility-zone task.** These are `Molecular/AlgebraicInduction/`,
  `Molecular/RigidityMatrix/`, and edits to proofs over ScrewSpace-carrier terms. At the open, 23 of
  the surface's `Molecule/` files mention `ScrewSpace K`, `ScrewSpace.mk` or `ScrewSpace.val`. The
  playbook floor applies (`.claude/commands/coordinate-phase.md` *Fragility zone*): a
  producer-shaped edit there is Opus at minimum, and a mechanical refactor or doc edit stays
  rung-mapped. **(producer)** marks the ⚠Z tasks that are producer-shaped.

## Lemma checklist (the round's task list)

One commit per task, in the order given (the numbers). For the §B tasks, done means: every listed
site is either fixed, or kept with a one-word reason recorded under the task's checklist line.

### Status and small items

- [x] **1. T1: the stale toolchain status** (`a2686fde`). ROADMAP's toolchain row and
  `notes/ToolchainBumps.md` *Where this stands* rewritten: `origin/master` was at `91fcd24a` with a
  green *Build & deploy site* run, and hopscotch's issue #2 / PR #1 now track a real mathlib
  incompatibility (`ab64d1c`), so both stay open. The local-only `bump/lean-4.34.0-rc{1,2}` refs are
  the PI's call, recorded there and not acted on.
- [x] **2. B3: linter silencers and the heartbeat bump** (12 sites; `5a636c0e`, corrected by
  `244f6613`). 2 silencers deleted as stale (`Base.lean`: `pencilPair_of_habitat_ncard_eq_three`,
  and the second one on `…_eq_four`). 1 fixed at the source: `pencilPair_of_splitOff_of_habitat`
  (`Escape.lean`) has its `[DecidableEq β]` dropped, with `classical` in the proof. 6 are kept
  because they are pinned or headline (see *Candidates*): `pencil_conjecture_of_arms`,
  `…_of_arms_pair`, `…_of_hcontract_hK_hbareSplit` and its `_of_card` form, `…_of_X0`, and
  `pencil_conjecture`. Their comments say the binder is type-unused and name the callee it is
  threaded to. The 2 `unusedFintypeInType` in `GenericBase.lean` are kept, with their comments
  predating the task, and were not re-examined against `[Finite …]` + `Fintype.ofFinite`. The
  heartbeat budget of `…_eq_four` went from 1000000 to 400000 (bisected: 300000 times out at
  `Base.lean` 829). The first commit had called the linter a false positive. That was wrong: its fix
  is to drop the binder and use `classical`. The FRICTION entry is reframed, and
  `notes/dispatch-log.md` has the row.
- [x] **3. B8: `show … from rfl`** (32 sites; `9bf98a3c`). 29 fixed, 3 kept.
  - Added `screwDim_one` / `screwDim_two` beside `abbrev screwDim` (`RigidityMatrix/Basic.lean`),
    covering 15 sites.
  - Moved `Graph.bodyBarDim_two` / `_three` beside `def bodyBarDim` (`BodyBar/Framework.lean`, same
    names), covering 4 sites.
  - Mathlib's `Graph.vertexSet_induce` covers 8 sites. Take care not to confuse it with
    `Graph.induce_vertexSet : G.induce V(G) = G`.
  - `Short.lean`'s two `pt` unfolds use `simp only [hpt, …]`. A bare `rw [hpt]` leaves a
    beta-redex; the LSP accepted it, and only `lake build` caught it.
  - Kept as structural: the `Fin`-literal identities at `Ear.lean` 176 and 857, and
    `Orbit.lean` 1048's `F₁.graph = G₁`.
- [x] **4. B7: the recurring `rw` towers** (`CLEANUP.md` §B: a missing fused lemma). These are the
  only towers the open found recurring three or more times. The single chains are not this task's;
  §C's walks may touch them.
  - Fixed: `LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff` (×5,
    `SplitOff.lean`) — new `Graph.mem_ker_liftingMatrix_iff` beside
    `Graph.liftingMatrix_mulVec_eq_zero_iff` (`Carrier.lean`); no prior form (`lean_local_search`).
  - Fixed: `smul_smul, inv_mul_cancel₀ _, one_smul` (×4 + the `GenericEar.lean` 75 prefix) —
    mathlib's `inv_smul_smul₀`.
  - Fixed: `dotProduct_add, dotProduct_smul, smul_eq_mul` (×3, `SplitOff.lean`) — new
    `dotProduct_add_smul` / `dotProduct_smul_add_smul` (`Mathlib/Data/Matrix/Mul.lean`, new mirror
    file; `dotProduct_add`/`dotProduct_smul`/`smul_eq_mul` are all root-level in
    `Mathlib.Data.Matrix.Mul`, so the mirror is too).
  - Kept, local hypothesis rewrites: `Function.update_of_ne …, Function.update_of_ne …,
    Function.update_self` (`Base.lean`, the `point`/`normal`/`supp` nested-update unfolds) — each
    site's distinctness hypotheses (`hqs`, `hqr`, `he24`, `he23`, …) are local to that one nested
    `Function.update` chain; a general lemma would take the same hypotheses as arguments and not
    shorten the one-line `rw` it replaces.
  - Kept, local hypothesis rewrites: `Graph.degree_eq_ncard_add_ncard, hloops, hnonloops`
    (`Motive.lean`) and `hh0, hh1, hh2, one_smul` (`Engine.lean`) — `hloops`/`hnonloops`/`hh*` are
    freshly proved per site from a different set/term, so the callee would need them as hypotheses
    too.
  - The `ite_eq_right`/`ite_eq_left` runs in `Ear.lean` and `ContractCurve.lean`: task 7b kept all
    of them (local hypothesis rewrites; `ContractCurve.lean`'s already use `contractLimitMap_apply`).
    `this, certPt` (×6, `Chain.lean`) is task 5's, `hslot_*` is task 25's, and `hnu, hnv, hpu,
    hpv` is task 26's.
- [x] **5. F1: the certificate-picture glue** (the `[open]` FRICTION entry *The
  certificate-picture glue is written out a third time*, now resolved). `certPicture`,
  `certHeights` and a new height-general `pencilConfigPoint_certPicture` (`z w = certPt (lab w) 2`
  as its hypothesis) moved to `Ear.lean` beside `certPt`; `pencilConfigPoint_cert` is now its
  one-line corollary. `Graph.X0Attains.of_openEar` (`Chain.lean`) and `…of_openEar_two`
  (`Short.lean`) both call it in place of their inline `funext`/`fin_cases`/`change` copy;
  `of_cycle`'s packaging already used the moved names and needed no change. No statement, pin, or
  docstring citation moved (none of the three names carry one outside this file trio).

### §B: `change`/`show`, cardinalities, and trial removals

- [x] **6. B6a: `change`/`show` in the Phase 39 files** (35 sites; `552f5857`). 32 fixed, 3 kept
  (`Chart.lean` 121, `Engine.lean` 264/371 — carrier defeq). New:
  `hubSlotNormalPoly_eval_funext` / `nbrSlotPointPoly_eval_funext` (`Engine.lean`); everything
  else is `Graph.vertexSet_induce`, `linearIndependent_set_coe_iff`, `LinearEquiv.comp_symm`, or
  `simp only [F]`/`simp only []`. `TACTICS-GOLF.md` § 27 (new) writes up the shape.
- [x] **7a. B6b: `change`/`show` in the rest of `MainComponent/`, and in
  `SparseDeficiency.lean`** (30 sites; this commit). `Bridge.lean` 404/422 and `Flat.lean` 369
  were task 3's, already fixed. 24 fixed, 3 kept, 3 already-resolved. No new lemma:
  `Graph.rigidContract` / `pencilNormalOfPicture` unfold via `rw`/`simp only [Def]` directly;
  `Graph.deficiencyMerged` folds back via `rw [← Def]`. Kept (reason: coe-defeq) — `Flat.lean`
  544, `SplitOff.lean` 330/548. `TACTICS-GOLF.md` § 27 extended with the plain-`def`/fold/coe-defeq
  shapes.
- [x] **7b. B6c: `change`/`show` in the ear files** (26 sites; this commit). 16 fixed, 10 kept, no
  new lemma. Fixed: the closedHubNbhd cluster (5) via `simp only [S]`; `Ear.lean`'s `z`
  piecewise-def cluster (4) via `dsimp only [z]` — `simp only [z]` over-collapses a
  self-comparison branch here and breaks the follow-up `rw` (`TACTICS-GOLF.md` § 27 extended);
  `Ear.lean` 117/164/1140 via existing lemmas (`hingeConstraint`, `toBodyHinge_supportExtensor`
  trio); the `pt`/`cfg` cluster (4) via `simp only [pt]`. Kept, reason fold — `GenericEar.lean`
  376, `GenericTriangle.lean` 544, `Short.lean` 553, the rank-chain reshapes ×5; reason
  let-defeq — `Orbit.lean` 516; reason coe-defeq — `Short.lean` 586. The `ite_eq_right`/
  `ite_eq_left` runs task 4 deferred here (`Ear.lean` 123/811/846, `ContractCurve.lean` 541/614)
  are all kept too, local hypothesis rewrites. `FRICTION.md`'s B6a correction gets a B6c addendum.
- [x] **8. B5: `Set` against `Finset`, and cardinality coercions** (36 sites; this commit). 9
  fixed, 27 kept (reasons in the commit message). `Set.fintypeCard_eq_ncard` collapses the
  two-step `ncard`↔`Fintype.card`/`toFinset` bridge (4 sites); `Polynomial.finite_setOfPred_isRoot`
  replaces `.roots.toFinset` for a root set (3 sites); `Set.ncard_compl` + `Nat.card_fin` closes
  `{j | j ≠ i}.ncard = 2` (2 sites). `TACTICS-GOLF.md` § 2 gets both lemma pointers. The 17-site
  `CoverageTheoremS.lean` degree-sum pair is kept — the finsum route is structural (*Candidates*).
- **9–12. B1a–B1d: dead `classical` and unforced `noncomputable`** (204 `classical`, 203 of
  them opening a proof body and one mid-proof, in `Pair2.lean`; 70 `noncomputable def`).
  - **Method**, per batch: delete every `classical` line and every `noncomputable` on a `def` in
    the batch's files, build, and restore exactly the ones whose removal breaks the build. Record
    the removed and kept counts per file. A proof-top `classical` that is needed is the
    project-standard bridge (ROADMAP *Engineering conventions*, Decidability), not a smell.
  - [x] **9. B1a, the Phase 39 files** (15 files; 71 `classical` / 21 `noncomputable`; this
    commit). 25 `classical` kept as the project-standard bridge, 46 deleted as dead: `Arms` 3/9,
    `Base` 2/2, `Engine` 1/7, `Escape` 3/5, `Habitat` 0/3, `Motive` 0/5, `Pair` 4/5, `Pair2` 2/5,
    `Reseed` 1/4, `Statement` 1/8, `Steer` 2/9, `Witness` 5/8, `X0` 1/1 (kept/total; `Chart` and
    `TwoCut` have none). 17 `noncomputable` kept, 4 deleted: `Chart` 6/7, `Engine` 9/11, `Steer`
    0/1, `TwoCut` 2/2. Every restore was forced by an actual whole-project build break (a missing
    `Decidable`/`Fintype` instance or a genuine noncomputable dependency); no downstream file
    outside the batch needed a restore. Per-site detail in the commit message.
  - [x] **10. B1b, `MainComponent/` part 1** (59 `classical` / 33 `noncomputable`; this commit). 15
    classical kept as the project-standard bridge, 44 deleted as dead; 30 noncomputable kept (a
    genuine noncomputable dependency, including one within-batch cascade: `Flat.lean`'s
    `flatRebuild` needed restoring only once its own dependency `flatStdBiv` was restored), 3
    deleted. Per file (classical kept/total, noncomputable kept/total): Carrier 4/13, 6/7;
    Configuration 1/3, 3/4; Flat 2/5, 10/11; Bridge 1/3, –; Cut 2/8, 2/2; Contract 1/3, –;
    ContractCurve 3/23, 9/9; ContractAdditive 1/1, –. No downstream file outside the 8-file batch
    needed a restore. Per-site detail in the commit message.
  - [x] **11. B1c, `MainComponent/` part 2** (63 sites: 50 classical / 13 noncomputable; this
    commit). 23 classical kept as the project-standard bridge, 27 deleted as dead; all 13
    noncomputable kept (a genuine noncomputable dependency), 0 deleted. Per file (classical
    kept/total, noncomputable kept/total): Chain 2/4, –; Ear 3/4, –; EarGen 0/1, 7/7; Lines 2/2,
    3/3; Short 1/1, –; Orbit 1/2, 1/1; SplitOff 1/3, –; CoverageCut 0/1, –; CoverageTheoremS 1/5, –;
    GenericBase 4/9, 1/1; GenericEar 2/4, –; GenericSteer 3/5, 1/1; GenericTriangle 2/4, –;
    GoodEar 0/3, –; Statements 1/2, –. No downstream file outside the 15-file batch needed a
    restore. Per-site detail in the commit message.
  - [x] **12. B1d, outside the tree** (27 sites: 24 classical / 3 noncomputable; this commit). 7
    classical kept as the project-standard bridge, 17 deleted as dead; all 3 noncomputable kept (a
    genuine noncomputable dependency — `ScrewSpace`'s `AddCommGroup` instance), 0 deleted. Per file
    (classical kept/total, noncomputable kept/total): Deficiency 1/3, –; Coupling 0/1, –;
    SparseDeficiency 3/16, –; ReducibleVertex 1/1, –; SplitOffDeficiency 1/2, –; MvPolynomial 1/1,
    –; Duality –, 1/1 (⚠Z); ProjectiveInvariance –, 2/2 (⚠Z, carrier). No downstream file outside
    the batch needed a restore. Closes the B1 checklist item (tasks 9–12). Per-site detail in the
    commit message.

### The carried items (`notes/Phase40-design.md` §3/§4/§7)

- [x] **13. M3: `span_supportExtensor_ofNormals_eq`** (§3, the SPLITOFF entry; this commit). Moved
  above its consumer `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` (now `Cut.lean`
  112/128). The consumer's `hmot` now rewrites both sides with the lemma (at `hends'`/`q'` then
  `hends`/`q`) and closes with the existing `hnorm` rewrites at `he.left_mem`/`he.right_mem` — the
  inlined `rcases … panelSupportExtensor_swap` orientation split is gone, absorbed by the lemma.
  Statements, names and pins unchanged.
- **14a–14b. M4: call 12's four corollary rebases** (§3, the CONTRACT-A entry;
  `notes/Phase40k.md` *Hand-off* names G1, G4 and G5). Two commits. Statements and pins are
  unchanged. Add a `\uses` edge wherever a node's proof now cites the new source.
  - [x] **14a, (i)+(ii)** (`Contract.lean`; this commit). (i) derives the bound from G4 plus
    `dim (ker.map ρ) ≤ 3` (`liftingRestrict_mem_liftingSpace_induce_of_contract`, `hLH`,
    `Graph.finrank_affineLifts`, `omega`; needed a `set`-fold, TACTICS-QUIRKS.md § 1). (ii) is G5 at
    `n := 2`. `contractLimitMap` and friends, and `Graph.exists_core_plane`, keep a consumer
    elsewhere (liveness check: none orphaned). Blueprint: `lem:pencil-contract-limit`'s proof now
    `\uses lem:pencil-contract-kernel-bound` (part (1) rewritten to match) and drops the reverse
    edge from `…-kernel-bound` (would cycle; its own proof now inlines the map instead of pointing
    back); `lem:pencil-contract-standing`'s proof gains `\uses lem:pencil-contract-standing-rigid`.
  - [x] **14b, (iii)+(iv)** (this commit). (iii) `Graph.exists_core_plane`'s `hmem` is now one call to
    `…liftingRestrict_mem_liftingSpace_induce_of_contract` (`hcore` stays, still needed for the
    closing step). (iv) `…smul_add_affineLifts` builds its `LinearEquiv` `g` and calls G1, dropping
    the inlined `hspan`/`rw` chain. Blueprint: `lem:pencil-contract-core-plane`'s proof now
    `\uses lem:pencil-contract-kernel-bound`, whose own part (1) is inlined self-contained (the
    dangling-pointer target ran the other way from 14a's, into core-plane); `lem:pencil-rank-scale-
    shift`'s proof now `\uses lem:pencil-rank-collineation`.
- [x] **15. M2b: the B2 dedupe** (§3, the 40h items; this commit). Confirmed the two proofs
  matched step for step (only divergence: which label is relinked, and one fact — `e₀ ∉
  G.crossingEdges f`, trivial if fresh, via `hfv`/`hfa` if reused — everything downstream of it
  identical). Factored `private Graph.splitOff_deficiency_le_aux` over `e₀ ∉ E(G) ∨ e₀ = eₐ`;
  both public lemmas are now one-line corollaries (`Or.inl`/`Or.inr rfl`). No statement, name, or
  pin moved. `SplitOffDeficiency.lean`: 173 lines changed, net −67.
- **16–18. M2c: the three-body near-copies** (§3, the 40h items; the `[open]` FRICTION entry
  *The three-body step repeats the four-body step*, which proposes the fix). Close or narrow that
  entry as the parts land.
  - [x] **16. M2c-i** (this commit). The proofs matched step for step, diverging only in `F`'s
    length and the `W = ⊤` step (tetrahedron against `hG`). New `exists_insertion_of_star_sup_star`
    over `W = R ⊔ K ∙ (y₁ ∧ y₃)` with the star hypothesis; both are its corollaries by a span
    rearrangement, `_four` keeping its tetrahedron. Names, statements, pins unchanged (neither is
    pinned). Block 215 → 105 lines, 21 747 → 6 303 heartbeats (measured, script not retained; method
    in the FRICTION entry, now narrowed). TACTICS-QUIRKS § 113 (new).
  - [ ] **17. M2c-ii.** `splitOff_ear_three` (`Short.lean` 300) from `splitOff_ear_four` (228), via
    `Fin.succAbove 1`.
  - [ ] **18. M2c-iii.** About 200 lines of `Graph.X0Attains.of_openEar_three`'s assembly (`Short.lean`
    1012, 353 lines, tied tenth in the §C ranking) repeat `…_four`'s (646, 351 lines). Prove one
    assembly lemma from the round-1 point, parametrized by `k`. **⚠Z (producer)**. If it won't land
    as one green commit, record the attempt here, move the unification to *Candidates* with the
    same line in `notes/Cleanup40.md` §2 Round 4, and close the task.
- [ ] **19. M2d: the pin budget of `lem:pencil-ear-data`** (§3, the 40h items).
  `main-component.tex` 2181, §`sec:main-component-short`, carries nine pins, while
  `blueprint/AUTHORING.md` D says a node pinning four or more is bundling results. Either split the
  node along its three clauses, with the ear data as a definition node, or leave the helpers
  unpinned. Repoint the 14 docstring citations of the label in `EarGen.lean` clause by clause (40g's
  `75df1aac` is the precedent for a moved pin). No statement changes strength.
- [ ] **20. M5: lemmas to their definitions' files** (§3 COVERAGE).
  - Move CHAINS' `pathVertex` helpers to `Cut.lean`, beside `def pathVertex` (429). They are
    `pathVertex_cons`, `isLink_pathVertex_cons`, `isLink_pathVertex_rev`,
    `val_eq_zero_or_of_pathVertex_mem`, `pathVertex_eq_of_val_eq_zero`/`_last` (`CoverageChain.lean`
    `## Path sequences`, 39–98) and `pathVertex_mem_insert_insert_range` (434).
  - Move the `Graph.IsOpenEar.*` lemmas (`## Open ears`, 99–273, plus 443 and 470) to
    `Coverage.lean`, beside `structure Graph.IsOpenEar` (58), as far as `Coverage.lean`'s imports
    allow. Record any that stay, and why.

  No names change, so no pin moves. Every step file below `Cut.lean` rebuilds.
- **21a–21b. F2: two general facts downstream of their consumers** (the `[open]` FRICTION
  entry of that name). Two commits. No names change. The second closes the FRICTION entry.
  - [ ] **21a.** Move `Graph.closedNbhd_subset_vertexSet` (`Bridge.lean`) to `Motive.lean`, beside
    `Graph.closedNbhd`, and drop the inlined copies in `Graph.isAdmissiblePicture_congr` and
    `Graph.liftingSpace_congr` (`Carrier.lean`).
  - [ ] **21b.** Move the `infinitesimalMotions_eq_of_isLink_*` pair (`AlgebraicInduction/Pinning.lean`)
    to `RigidityMatrix/Basic.lean`, and drop `BodyHingeFramework.relScrews_congr`'s re-proof
    (`RigidityMatrix/Bricks.lean`). **⚠Z**.
- [ ] **22. M6: `mapExtensor` and `mapSupport`** (§4, *Still open*). `mapExtensor`
  (`Molecule/ProjectiveInvariance.lean` 79, pinned by `thm:projective-invariance`,
  `molecule-modelling.tex` 106) and `mapSupport` (`GenericLift/HingeGeneric.lean` 462, pinned by
  `lem:screw-map-rows`, `generic-lift.tex` 929) are one definition. `thm:projective-invariance`'s
  rank half restates `lem:screw-map-rows`.
  - At the open, `mapExtensor` has 32 occurrences (ProjectiveInvariance 26, Statement 3,
    Duality 3) and `mapSupport` 20 (HingeGeneric 8, Configuration 5, Arms 4, Pair, Motive and
    ProjectiveInvariance 1 each).
  - Settle which definition survives from the import order. Repoint its callers and the pin; this
    runs the deletion gate. Derive the rank half from `lem:screw-map-rows`'s Lean, adding the
    `\uses` edge.
  - If one definition would need an import restructure, record that as a candidate instead.
    **⚠Z**, carrier.
- **23a–23b. M1: the wider stand-in audit of `lem:trivial-motions-rank-bound`** (§3 FLAT).
  Blueprint only. There are 31 references outside the node's own label.
  - **Method.** For each reference, find the bound that the citing node's Lean actually calls.
    `BodyHingeFramework.screwDim_add_deficiency_le_finrank_infinitesimalMotions` is the spanning
    form, and the reference stays. `…screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
    or `…finrank_span_rigidityRows_add_deficiency_le` is the relative form: repoint to
    `lem:relative-deficiency-rank-bound`.
  - Done: every reference names the bound its Lean uses, with one tally line here per commit.
  - [ ] **23a, the molecular chapters** (24 references): `rigidity-matrix.tex` 7,
    `molecular-induction.tex` 6, `panel-layer.tex` 6, `case-i.tex` 3, `case-iii.tex` 1,
    `genericity-and-count.tex` 1. Also `generic-lift.tex`'s stand-in,
    `prop:rigidity-matrix-prop11`.
  - [ ] **23b, the molecule and pencil chapters** (7): `molecule-application.tex` 3,
    `molecule-modelling.tex` 2, `pencil.tex` 2.

### §C: the long-proof screen (the top ten, walked; screening only)

Each walk asks §C's four questions: API extraction, a missed mathlib lemma, tactic substitution,
and definitional refactor. Cross-proof unification is §C's fifth bullet; here it goes to
*Candidates* unless the change is a small local extraction. Local changes land, and structural
findings are recorded as candidates. First run a cheap liveness check (`lean_references`,
transitively, to `pencil_conjecture` / `pencilPair_of_nonempty`). A proof that feeds neither
headline is recorded as off-headline (round 4's third question) and gets no local work.

- [ ] **24. C1: `Base.lean`, a sibling pair.** #1 `pencilPair_of_habitat_ncard_eq_four` (571, 852
  lines, the only `maxHeartbeats` bump, which task 2 handles) and #3
  `pencilPair_of_habitat_ncard_eq_three` (63, 474). Also weigh §C's Phase-22j calibration: where
  the cost is diffuse, the lever is a file split, not an extraction.
- [ ] **25. C2: `Witness.lean`.** #2 `exists_coord_linearIndependent_pencilChartNormal_of_pendant_deg3`
  (670, 483) and #10 `exists_coord_linearIndependent_pencilChartPoint_of_pendant_deg3` (244, 353).
  - The sweep found one block written out nine times: the `hPu`/`hP1`/`hP2` triple (each
    `exists_smul_cross₃_pi_single` followed by `rw [pencilChartPoint, hslot_* 0, …, hcross]`). It
    is at `Witness.lean` 563–581 and 964–982, and at `GenericSteer.lean` 302–320 in
    `exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub` (48, 287 lines).
  - That is a small-extraction candidate: one lemma giving
    `∃ cc ≠ 0, pencilChartPoint … = cc • Pi.single j 1` from the slot equations. Land it if its
    locals factor.
- [ ] **26. C3: `Pair.lean` and `Pair2.lean`.**
  - #4 `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant` (`Pair2.lean` 66,
    448).
  - #5 `…_induce_union_singleton` (`Pair.lean` 794, 447).
  - #6 `…_induce_pendant_deg3` (`Pair2.lean` 549, 409).

  The `rw [hnu, hnv, hpu, hpv]` run recurs once in each of #4 and #6 (`Pair2.lean` 242/250,
  701/709). That is the sibling shape §C's calibration warns about: check for per-step divergence
  before proposing a unification.
- [ ] **27. C4: three singles.**
  - #7 `hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`
    (`GenericTriangle.lean` 155, 401).
  - #8 `hasPencilRealization_of_not_twoEdgeConnected_core` (`Arms.lean` 815, 376).
  - #9 `Graph.X0Attains.of_openEar_two_of_splitOff` (`Orbit.lean` 730, 368).

  (The ranking's tied tenth, `of_openEar_three`, and the twelfth, `of_openEar_four`, are task 18's.)
- [ ] **28. S1: the file-size tripwire.** `Witness.lean` is at 1 809 lines, the only surface file
  well past ~1500. Run this after task 25. It is cleanly sectioned: split it along a `/-! ##`
  header, for example `## The general-position core` (1154), so both halves come out under ~1200.
  No names or statements change. Its only importer is `Steer.lean`. Repoint any docstring file
  pointers (`grep -rn 'Witness.lean'`). `Arms.lean`, at 1 518, is split the same way only if it is
  still past ~1500 after task 27.

### §A: the blueprint against the Lean (every `\leanok` node, including the laundering walk)

For every node in the range:
- compare the statement with the pinned Lean signature (hypotheses, conclusion, binders);
- check that every hypothesis of a `\leanok` node is discharged in the Lean body or is the
  conclusion of a node it `\uses` (`CLEANUP.md` §A, the laundering walk);
- read the prose proof for "the Lean does X via Y" oversell, and for formalization asides (the
  first response to an aside is a Lean simplification).

A conditional theorem that states its kernels as hypotheses, as `pencil.tex`'s surviving
conditionals do, is honest. Laundering is a load-bearing hypothesis that the statement hides.
Done: one tally line per task (nodes walked, divergences found, fixes landed), with any
strength-changing finding under *Candidates*. The ranges are the open's line numbers.

- [ ] **29. A-P1: `pencil.tex`, from `sec:pencil-through-point` through `sec:pencil-extension`**
  (38–468; 13 environments).
- [ ] **30. A-P2: `sec:pencil-reduction`** (469–755; 11).
- [ ] **31. A-P3: `sec:pencil-nondegenerate` and `sec:pencil-main-component-route`** (756–1196; 9).
  The conditional theorems kept when design §6 was retired live here.
- [ ] **32. A-P4: `sec:pencil-girth-chain` and the chapter introduction** (1197–1412 and 1–37; 8).
- [ ] **33. A-MC1: `main-component.tex`, `sec:main-component-carrier` and the section
  introduction** (123–716 and 1–122; 21).
- [ ] **34. A-MC2: `sec:main-component-flat` and `sec:main-component-jj`** (717–1102; 13).
- [ ] **35. A-MC3: `sec:main-component-cut`** (1103–1330; 11).
- [ ] **36. A-MC4: `sec:main-component-contract`** (1331–1636; 9). Run it after tasks 14a–14b.
- [ ] **37. A-MC5: `sec:main-component-chain`** (1637–1967; 11).
- [ ] **38. A-MC6: `sec:main-component-short`** (1968–2541; 15). Run it after tasks 16–19.
- [ ] **39. A-MC7: `sec:main-component-orbit` and `sec:main-component-splitoff`** (2542–3230; 14).
- [ ] **40. A-MC8: `sec:main-component-contract-additive` and `sec:main-component-sparse`**
  (3231–3845; 15).
- [ ] **41. A-MC9: `sec:main-component-coverage`** (3846–4280; 13).
- [ ] **42. A-MC10: `sec:main-component-statements`** (4281–4809; 15). This holds both headline
  nodes.
- [ ] **43. A-D: Phase 40's deficiency nodes** (9). In `deficiency.tex`: `lem:deficiency-antitone`,
  `lem:deficiency-zero-connected`, `lem:deficiency-cut-vertex`, `lem:deficiency-ear`,
  `lem:deficiency-ear-merge`, `def:deficiency-merged`. In `molecular-induction.tex`:
  `lem:splitoff-deficiency-reuse`, `lem:splitoff-deficiency-merged`. In `panel-layer.tex`:
  `thm:theorem-55-6-rows`.
- [ ] **44. A-R: Phase 40's `rigidity-matrix.tex` nodes** (11): `lem:relative-deficiency-rank-bound`,
  `lem:block-rank-cut` (its pin extended), `lem:block-rank-cut-vertex`, `def:relative-screws`,
  `lem:block-rank-two-cut`, `cor:block-rank-vertex-two-cut`, `lem:block-rank-path`,
  `lem:relative-screws-path`, `lem:block-rank-ear`, `lem:block-rank-contract`,
  `lem:rank-polynomial-proj-eval`. **⚠Z** for any Lean fix (`RigidityMatrix/Bricks.lean`,
  `AlgebraicInduction/`).

### The close

- [ ] **45. X: close the round** (`CLEANUP.md` *Workflow* rule 5).
  - Re-run the open's §B sweep and record the counts after.
  - Re-run `#print axioms` on the 19 main results, the open's way.
  - Re-measure the file sizes (the standing rule, and task 28).
  - Flip the ROADMAP row, and set `40-cleanup`'s `done = true` in `.claude/autopilot/queue.toml`.
  - Point `notes/Cleanup40.md`'s **Status** and ROADMAP's cleanup-rounds bullet at round 2.
  - Hand *Candidates* to round 4: mirror each line into `notes/Cleanup40.md` §2 Round 4.

## Candidates for `40-simplify`

Structural findings, and any finding that would change a headline statement or a blueprint
statement's strength. They are recorded here and never acted on in this round
(`notes/Cleanup40.md` §2). Each line: the finding, its source task, and why it is structural. The
close mirrors them into `notes/Cleanup40.md` §2 Round 4.

- **Six type-unused `[DecidableEq β]` binders on pinned or headline pencil theorems** (task 2, B3).
  They are on `pencil_conjecture`, `pencil_conjecture_of_X0`, `pencil_conjecture_of_arms`,
  `pencil_conjecture_of_arms_pair`, `pencil_conjecture_of_hcontract_hK_hbareSplit` and `…_of_card`.
  The linter's fix is to drop each binder and use `classical` wherever a callee still takes one:
  `Graph.pencil_reduction` keeps its own, and the proofs that call it already open with
  `classical`. Done together, the three term proofs need nothing. `pencilPair_of_nonempty` is the
  in-tree precedent. The fix deletes all six silencers. It is deferred because it changes a
  headline signature (`thm:pencil-conjecture`) and pinned ones
  (`thm:pencil-conditional-realization`, `…-pair`, `…-main-component`).
- **A finsum-native rewrite of `CoverageTheoremS.lean`'s degree-sum pair** (task 8, B5;
  `Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard` and `…two_mul_ncard_le_ncard_edgeSet`, the 17
  kept sites). Both proofs bridge `Set.ncard` to a `Finset` sum (`G.vertexSet_finite.toFinset`, or
  a `set D : Finset α := …toFinset`) because the inequality/constant-sum steps they need —
  `Finset.sum_le_sum`, `Finset.sum_sub_distrib`, `Finset.sum_const`, `Finset.sum_boole`,
  `Finset.card_biUnion` — have no finsum (`∑ᶠ`) analogue in this mathlib vintage (checked: no
  `finsum_le_finsum`/`finsum_mono`/`finsum_mem_const` anywhere under `Mathlib/`). The Matroid
  package's `Graph.handshake_degree_subtype` (`∑ᶠ v ∈ V(G), G.degree v = 2 * E(G).ncard`) is exactly
  what the first proof's `Graph.handshake_degree_finset` call already reduces to internally, so
  swapping it in gains nothing. `Set.Finite.ncard_biUnion` (`Mathlib.Data.Set.Card.Arithmetic`) could
  replace the second proof's `Finset.card_biUnion`, but its output is a finsum whose constant-value
  sum still needs converting back to a multiple of `ncard` — the missing step above. A rewrite would
  need new finsum comparison/constant-sum mirror lemmas first, which is a new proof route, not a
  local substitution.

## Moved to a later round

Each line: the task, its target round, and a one-line reason. The same line goes into the target
round's plan section in `notes/Cleanup40.md` in the same commit.

- *(none yet)*

## Blockers / open questions

- None at the open.
- Seen at the open, outside the surface, so not a task: the `[open]` FRICTION entry *`open scoped
  Matrix` inside `namespace CombinatorialRigidity.Molecular`* proposes pinning three
  `RigidityMatrix/Concrete.lean` theorems to `_root_.Matrix`. That file is outside the round's
  surface.

## Hand-off / next phase

**Next concrete commit: task 17, M2c-ii** (§3, the 40h items; the `[open]` FRICTION entry *The
three-body step repeats the four-body step*, now narrowed to tasks 17–18). Derive
`splitOff_ear_three` (`Short.lean` 300) from `splitOff_ear_four` (228) via `Fin.succAbove 1`, first
confirming the two match step for step (`CLEANUP.md` §C's per-step-divergence calibration). Task 16
(just landed) unified the insertion pair in `exists_insertion_of_star_sup_star`.

## Decisions made during this round

- **2026-09-29, the open.** The task list comes from sweeping the surface first, before any fix
  (`CLEANUP.md` *Workflow* rule 2).
  - Beyond `notes/Cleanup40.md` §2's list, it added F1 and F2 (two `[open]` FRICTION entries whose
    sites are all in the Lean surface), S1 (the one surface file well past the tripwire), and
    Phase 40's three nodes outside the four named chapters (folded into A-D).
  - 40h's file-size item is a standing rule, not a task: its plan fires only on a crossing. The
    close re-measures. Nothing moved to a later round; fixes precede the §A walks.
