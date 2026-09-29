# Phase 40 cleanup round 1/5 — `40-cleanup`, the mechanical round (work log)

**Status:** in progress (opened 2026-09-29). Round 1 of the five post-Phase-40 cleanup rounds.
Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` A and B over what Phases 39–40 built, C as screening only, and five carried items.
Task 1 (T1) landed; 48 of 49 one-commit tasks remain. **Next concrete task:** task 2, B3, the
linter silencers and heartbeat bump (Lean, 12 sites). Round manual: `CLEANUP.md`.

## Current state

**Next commit: task 2, B3** (*Lemma checklist*). The checklist holds 49 one-commit tasks; task 1
landed, 48 remain. Nothing is mid-stream.

**Task 1 (T1) landed.** ROADMAP's toolchain row and `notes/ToolchainBumps.md` *Where this
stands* were stale: `origin/master` had already caught up to `91fcd24a` (one commit behind
local master) with a green *Build & deploy site* run, and hopscotch had stopped re-stamping
issue #2 with the old pin-order false positive — it now tracks a genuine mathlib incompatibility
at `ab64d1c`, with PR #1 offering the last-known-good bump to `0258e25`. Both surfaces rewritten;
the `bump/lean-4.34.0-rc{1,2}` local-only branches (never pushed, now 498 commits behind master)
are noted but left for the PI to delete or not. Detail: `notes/ToolchainBumps.md` *Where this
stands*.

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

- [x] **1. T1: the stale toolchain status.** Docs only. ROADMAP's Status row *Toolchain bumps to
  Lean v4.34.0-rc1 → rc2* still says "**Still unpushed — CI has never validated the stack**", and
  `notes/ToolchainBumps.md` *Where this stands — and the next concrete task* (lines 14–43) says
  `origin/master` is at `0920772` and CI has never validated the stack. On 2026-09-29,
  `origin/master` was at `91fcd24a` and CI's *Build & deploy site* run passed there
  (`notes/Cleanup40.md` §2). Verify with `gh run list --branch master`, and cite the run by its
  GitHub URL, not by a local path. Then rewrite both surfaces, and that section's "next concrete
  task" (for example, whether the hopscotch workflow stopped re-stamping issue #2). Whether to
  delete the `bump/lean-4.34.0-rc{1,2}` refs is the PI's call; note it and do not act on it. Done:
  `grep -rn -i "unpushed\|never validated" ROADMAP.md notes/ToolchainBumps.md` is empty.
- [ ] **2. B3: linter silencers and the heartbeat bump** (12 sites).
  - `set_option linter.unusedDecidableInType false in`, 9 sites: `Base.lean` 57, 543;
    `Arms.lean` 1437; `Escape.lean` 346, 443, 551; `Pair2.lean` 1219; `X0.lean` 344;
    `MainComponent/Statements.lean` 151. The last two have a justifying comment and the other
    seven have none.
  - `set_option linter.unusedFintypeInType false in`, 2 sites, both commented:
    `GenericBase.lean` 716, 772.
  - `set_option maxHeartbeats 1000000 in`, on `pencilPair_of_habitat_ncard_eq_four`
    (`Base.lean` 538, commented).

  Per site, remove the option and rebuild. If the linter no longer fires, the option stays deleted.
  If it fires, restore the option with a one-line comment saying why. Dropping the instance from a
  signature is the at-source fix, but on a headline or a pinned statement it changes the statement,
  so record it as a candidate instead. For the heartbeats, try the default and then the smallest
  budget that passes, and keep the comment. This is not a perf pass, so time nothing.
- [ ] **3. B8: `show … from rfl`** (32 sites, `CLEANUP.md` §B cases (a)–(d)).
  - `screwDim 2 = 6`, 12 sites: `Flat.lean` 604, 606, 621, 637, 676, 706; `Contract.lean` 429;
    `ContractAdditive.lean` 351; `Cut.lean` 416, 1042, 1043, 1044.
  - `screwDim 1 = 3`, 3 sites: `Flat.lean` 341, 369; `Bridge.lean` 422.
  - For both: add `screwDim_one` and `screwDim_two` beside `abbrev screwDim`
    (`RigidityMatrix/Basic.lean` 89, **⚠Z**, a mechanical addition that rebuilds the whole
    `Molecular/` tree). No site outside the surface uses the `show` form.
  - `Graph.bodyBarDim 2 = 3`, 3 sites (`Contract.lean` 198, 201; `Bridge.lean` 404), and
    `bodyBarDim 3 = 6` (`ContractAdditive.lean` 79). Use `Graph.bodyBarDim_two` / `_three`. They
    already exist, but in `Induction/SparseDeficiency.lean` 254/257; move them beside
    `def bodyBarDim` (`BodyBar/Framework.lean` 61), since a lemma lives with its definition.
  - `V(G.induce V₁) = V₁`, 8 sites: `Chain.lean` 726; `Short.lean` 180; `Ear.lean` 465, 560;
    `Cut.lean` 393, 394, 974, 975. Use mathlib's `Graph.vertexSet_induce : G[X].vertexSet = X`
    (checked at the open).
  - The other 5: `Short.lean` 1080, 1083 (a `pt`/`cfg` unfold, case (a)); `Ear.lean` 176, 857
    (`Fin` literals, (c)/(d)); `Orbit.lean` 1048 (`F₁.graph = G₁`, (a)).
- [ ] **4. B7: the recurring `rw` towers** (`CLEANUP.md` §B: a missing fused lemma). These are the
  only towers the open found recurring three or more times. The single chains are not this task's;
  §C's walks may touch them.
  - `LinearMap.mem_ker, Matrix.mulVecLin_apply, Graph.liftingMatrix_mulVec_eq_zero_iff`, ×5 in
    `SplitOff.lean` (274, 275, 305, 309, 342): a fused `mem_ker` form beside
    `Graph.liftingMatrix_mulVec_eq_zero_iff` (`Carrier.lean` 552). Check `lean_local_search` first.
  - `smul_smul, inv_mul_cancel₀ _, one_smul`, ×4 (`Engine.lean` 704; `Lines.lean` 531, 796, 800),
    plus the prefix at `GenericEar.lean` 75: use mathlib's `inv_smul_smul₀` (checked at the open).
  - `Function.update_of_ne …, Function.update_of_ne …, Function.update_self`, ×3 (`Base.lean` 946,
    1060, 1121, and 1119).
  - `dotProduct_add, dotProduct_smul, smul_eq_mul`, ×3 (`SplitOff.lean` 527, 585, 672).
  - `Graph.degree_eq_ncard_add_ncard, hloops, hnonloops`, ×4 (`Motive.lean` 965, 996, 1229, 1318)
    and `hh0, hh1, hh2, one_smul`, ×4 (`Engine.lean` 929, 959, 1191, 1254). Is a lemma missing
    here, or are these just local rewrites?
  - The `ite_eq_right`/`ite_eq_left` runs in `Ear.lean` and `ContractCurve.lean` go with task 7b.
    `this, certPt` (×6, `Chain.lean`) is task 5's, `hslot_*` is task 25's, and `hnu, hnv, hpu,
    hpv` is task 26's.
- [ ] **5. F1: the certificate-picture glue** (the `[open]` FRICTION entry *The
  certificate-picture glue is written out a third time*). The open's `rw` sweep found it again:
  `this, certPt` ×6 at `Chain.lean` 643–664. Move `certPicture` to `Ear.lean` beside `certPt`,
  with a height-general `pencilConfigPoint (certPicture lab) z w = certPt (lab w)` under
  `z w = certPt (lab w) 2`. Use it in `Graph.X0Attains.of_openEar` (`Chain.lean`) and
  `Graph.X0Attains.of_openEar_two` (`Short.lean`), and re-base `of_cycle`'s packaging on it. Close
  the FRICTION entry.

### §B: `change`/`show`, cardinalities, and trial removals

- [ ] **6. B6a: `change`/`show` in the Phase 39 files** (35 sites). `Arms.lean` 234, 266, 976,
  1166, 1515; `Base.lean` 315, 1224, 1251; `Chart.lean` 121; `Engine.lean` 165, 168, 171, 226, 229,
  232, 264, 371; `Pair.lean` 591, 738, 1038; `Pair2.lean` 1177, 1181; `Reseed.lean` 218, 290;
  `Statement.lean` 697, 706, 724; `Steer.lean` 289, 323, 325, 374, 384, 396; `X0.lean` 193, 224.
  Four clusters to try as fused lemmas:
  - `show (∃ a b, (G.induce V₂).IsLink e a b) from ⟨u, v, hl⟩`, ×4 (`Arms.lean` 976, 1166;
    `Pair.lean` 591, 1038): an edge of an induced subgraph.
  - `change ExtensorThroughPoint (supp e) (point u) ∧ …` / `ExtensorInPanel …`, ×5 (`Base.lean`,
    `Statement.lean`): unfolding a realization predicate.
  - The six `show (fun j => MvPolynomial.eval q (…Poly …))` in `Engine.lean`.
  - `change ∃ q, LinearIndepOn …`, ×3 (`Steer.lean`).

  ⚠Z where a site is a ScrewSpace-carrier term (`Arms`, `Base`, `Statement`, `Engine`, `X0`).
- [ ] **7a. B6b: `change`/`show` in the rest of `MainComponent/`, and in
  `SparseDeficiency.lean`** (30 sites). `Bridge.lean` 404, 422 (task 3's); `Carrier.lean` 754;
  `Chain.lean` 270, 282, 415, 418; `Configuration.lean` 124, 191; `Contract.lean` 321, 322;
  `ContractAdditive.lean` 151, 152; `ContractCurve.lean` 466, 1001, 1002, 1015, 1221;
  `CoverageCut.lean` 46; `Flat.lean` 306, 369 (task 3's), 544; `SplitOff.lean` 157, 332, 551, 673;
  `Induction/SparseDeficiency.lean` 236, 697, 795, 890.
  - Clusters: `change ((G.deleteEdges E(G.induce W)).map (Graph.collapseTo r W)).IsLink …`, ×4
    (`Contract.lean`, `ContractAdditive.lean`), with `(Gc.map f).IsLink`, ×3
    (`ContractCurve.lean`): a contraction `isLink` unfold lemma.
  - `change G.partitionDef n f = G.deficiencyMerged n a b at hf`, ×3 (`SparseDeficiency.lean`).

  ⚠Z where a site is a ScrewSpace-carrier term (`Configuration`, `Flat`).
- [ ] **7b. B6c: `change`/`show` in the ear files** (26 sites). `Ear.lean` 117, 164, 798, 801,
  810, 845, 1109; `GenericEar.lean` 376, 563; `GenericTriangle.lean` 544, 649, 657, 663, 675;
  `Orbit.lean` 516, 944, 953, 1082; `Short.lean` 562, 595, 898, 987, 994, 1269, 1355, 1362.
  - Clusters: `change (if v ∈ V₁ then G.closedHubNbhd v else ∅) …`, ×5 (`GenericTriangle.lean`,
    `GenericEar.lean`), and `Ear.lean`'s `change (if _ ∈ V₁ then _ else _)` ×4 with its
    `ite_eq_right`/`ite_eq_left` `rw` runs (`Ear.lean` 123, 811, 846; `ContractCurve.lean` 541,
    614): an `_of_mem`/`_of_not_mem` pair beside each piecewise definition.
  - `change (fun j => cfg st (x 1, j)) = x₂`, ×4 (`Short.lean`, `Orbit.lean`).
  - The `change _ ≤ … (Module.finrank K ↥(…))` reshapes of a rank chain, ×5 (`Short.lean` 987,
    994, 1355, 1362; `Orbit.lean` 1082).

  ⚠Z where a site is a ScrewSpace-carrier term (all five files are carrier-touching).
- [ ] **8. B5: `Set` against `Finset`, and cardinality coercions.**
  - The `toFinset` / `ncard_eq_toFinset_card` sites, 24: `CoverageTheoremS.lean` 167–254 (17, the
    degree-sum count in `Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard` and its neighbour);
    `Bridge.lean` 142, 144; `GenericSteer.lean` 532, 533; `Flat.lean` 230; `SplitOff.lean` 706;
    `Motive.lean` 479.
  - The `Fintype.card` sites other than the 35 routine `Fintype.card_fin` rewrites, 12:
    `Arms.lean` 595; `Steer.lean` 641; `Witness.lean` 1269; `Motive.lean` 474, 478;
    `Engine.lean` 352; `Flat.lean` 231, 520; `Chain.lean` 123, 389; `Ear.lean` 1214;
    `ContractCurve.lean` 1048.

  At each site, decide whether a bridge (`Set.ncard_eq_toFinset_card'`, `Nat.card_coe_set_eq`, …)
  or the `Set` form is cleaner. For the count, try the Matroid package's finsum form
  `Graph.handshake_degree_subtype` as a route with no `Finset`.
- **9–12. B1a–B1d: dead `classical` and unforced `noncomputable`** (204 `classical`, 203 of
  them opening a proof body and one mid-proof, in `Pair2.lean`; 70 `noncomputable def`).
  - **Method**, per batch: delete every `classical` line and every `noncomputable` on a `def` in
    the batch's files, build, and restore exactly the ones whose removal breaks the build. Record
    the removed and kept counts per file. A proof-top `classical` that is needed is the
    project-standard bridge (ROADMAP *Engineering conventions*, Decidability), not a smell.
  - [ ] **9. B1a, the Phase 39 files** (15 files; 71 `classical` / 21 `noncomputable`). `Arms` 9,
    `Base` 2, `Engine` 7/11, `Escape` 5, `Habitat` 3, `Motive` 5, `Pair` 5, `Pair2` 5, `Reseed` 4,
    `Statement` 8, `Steer` 9/1, `Witness` 8, `X0` 1, `Chart` 0/7, `TwoCut` 0/2.
  - [ ] **10. B1b, `MainComponent/` part 1** (59 / 33). `Carrier` 13/7, `Configuration` 3/4,
    `Flat` 5/11, `Bridge` 3, `Cut` 8/2, `Contract` 3, `ContractCurve` 23/9, `ContractAdditive` 1.
  - [ ] **11. B1c, `MainComponent/` part 2** (50 / 13). `Chain` 4, `Ear` 4, `EarGen` 1/7, `Lines` 2/3,
    `Short` 1, `Orbit` 2/1, `SplitOff` 3, `CoverageCut` 1, `CoverageTheoremS` 5, `GenericBase` 9/1,
    `GenericEar` 4, `GenericSteer` 5/1, `GenericTriangle` 4, `GoodEar` 3, `Statements` 2.
  - [ ] **12. B1d, outside the tree** (Phase-40-added lines only; 24 / 3). `Induction/SparseDeficiency`
    16, `Deficiency` 3, `Induction/SplitOffDeficiency` 2, `Induction/ReducibleVertex` 1,
    `Mathlib/LinearAlgebra/Matrix/MvPolynomial` 1, `AlgebraicInduction/Coupling` 1 (**⚠Z**);
    `noncomputable` in `Molecule/Duality` 73 and `Molecule/ProjectiveInvariance` 79, 236 (**⚠Z**,
    carrier).

### The carried items (`notes/Phase40-design.md` §3/§4/§7)

- [ ] **13. M3: `span_supportExtensor_ofNormals_eq`** (§3, the SPLITOFF entry). It could replace
  the orientation split inlined in `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr`
  (`Cut.lean` 113). The lemma is at `Cut.lean` 142, below its consumer, so move it up first.
  Statements are unchanged. **⚠Z**.
- **14a–14b. M4: call 12's four corollary rebases** (§3, the CONTRACT-A entry;
  `notes/Phase40k.md` *Hand-off* names G1, G4 and G5). Two commits. Statements and pins are
  unchanged. Add a `\uses` edge wherever a node's proof now cites the new source.
  - [ ] **14a, (i)+(ii)** (`Contract.lean`).
    - (i) The flat K3, `Graph.finrank_ker_contractLiftingMatrix_zero_le` (`Contract.lean` 118), as
      a corollary of G4, `Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`
      (`ContractCurve.lean`).
    - (ii) The `def₂` standing lemma, `Graph.isX0Graph_induce_of_deficiency_two_eq_zero`
      (`Contract.lean` 193), as a corollary of G5, `Graph.isX0Graph_induce_of_deficiency_eq_zero`
      (`ContractCurve.lean` 1059).
  - [ ] **14b, (iii)+(iv).**
    - (iii) The middle step of `Graph.exists_core_plane` (`Contract.lean` 80), its `hmem`, through
      the core-heights lemma `Graph.liftingRestrict_mem_liftingSpace_induce_of_contract`
      (`ContractCurve.lean` 834).
    - (iv) `Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` (`Configuration.lean`
      604) through G1, `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`
      (574). **⚠Z**.
- [ ] **15. M2b: the B2 dedupe** (§3, the 40h items). `Graph.splitOff_deficiency_le_of_eq_left`
  (`Induction/SplitOffDeficiency.lean` 191) re-runs about 110 lines of
  `Graph.splitOff_deficiency_le` (69). Factor out one core over any `e₀` with
  `e₀ ∉ E(G) ∨ e₀ = eₐ`, and make both lemmas corollaries of it. No statement or pin moves.
- **16–18. M2c: the three-body near-copies** (§3, the 40h items; the `[open]` FRICTION entry
  *The three-body step repeats the four-body step*, which proposes the fix). Close or narrow that
  entry as the parts land.
  - [ ] **16. M2c-i.** `exists_insertion_three` (`Lines.lean` 661) repeats about 90 lines of
    `exists_insertion_four` (547). Prove one insertion lemma over `R ⊔ K ∙ (y₁ ∧ y₃)` with the
    star hypothesis, and derive both from it. **⚠Z (producer)**.
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

- *(none yet)*

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

**Next concrete commit: task 2, B3.** Remove each of the 12 linter-silencer / heartbeat-bump
sites listed under task 2 and rebuild; restore only the ones whose removal breaks the build, with
a one-line comment. Lean, no blueprint. Then continue in task order. Each task above names its
files, sites and done criterion.

## Decisions made during this round

- **2026-09-29, the open.** The task list comes from sweeping the surface first, before any fix
  (`CLEANUP.md` *Workflow* rule 2).
  - Beyond `notes/Cleanup40.md` §2's list, it added F1 and F2 (two `[open]` FRICTION entries whose
    sites are all in the Lean surface), S1 (the one surface file well past the tripwire), and
    Phase 40's three nodes outside the four named chapters (folded into A-D).
  - 40h's file-size item is a standing rule, not a task: its plan fires only on a crossing. The
    close re-measures. Nothing moved to a later round; fixes precede the §A walks.
