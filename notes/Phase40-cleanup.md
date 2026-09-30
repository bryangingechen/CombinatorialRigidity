# Phase 40 cleanup round 1/5 — `40-cleanup`, the mechanical round (work log)

**Status:** in progress (opened 2026-09-29). Round 1 of the five post-Phase-40 cleanup rounds.
Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` A and B over what Phases 39–40 built, C as screening only, and five carried items.
Tasks 1–13, 14a–14b and 15–18 closed (17 not landed); 29 of 49 one-commit tasks remain.
**Next concrete task:** task 19, M2d, the pin budget of `lem:pencil-ear-data` (blueprint, plus
`EarGen.lean` docstrings). Round manual: `CLEANUP.md`.

## Current state

**Next commit: task 19, M2d** (*Lemma checklist*). The checklist holds 49 one-commit tasks;
tasks 1–13, 14a–14b and 15–18 are closed (17 not landed), 29 remain. Nothing is mid-stream.

Landed so far: tasks 1–18, one line each under *Lemma checklist → Landed* (task 17 closed not
landed). A finished task gets one or two lines there, with its commit; the detail stays in the
commit message, and this section stays the forward pointer.

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

### Landed: tasks 1–18 (one line each; each commit message has the detail)

- [x] **1. T1** (`a2686fde`). The toolchain status was stale. Master is pushed and CI-green at
  `91fcd24a`, and hopscotch's issue #2 / PR #1 are now live signal. The `bump/*` refs are the PI's call.
- [x] **2. B3** (`5a636c0e`, corrected in `244f6613`). 12 sites: 2 silencers stale, 1 fixed at the
  source (`classical` in place of the binder), 6 pinned or headline kept (see *Candidates*), and 2
  `unusedFintypeInType` kept. Heartbeats went from 1000000 to 400000. The FRICTION entry is reframed.
- [x] **3. B8** (`9bf98a3c`). 32 `show … from rfl`: 29 fixed with `screwDim_one`/`_two`, the moved
  `bodyBarDim_two`/`_three` and `Graph.vertexSet_induce`; 3 kept (structural).
- [x] **4. B7** (`63aee01d`). `rw` towers: 3 clusters fused (`Graph.mem_ker_liftingMatrix_iff`,
  `inv_smul_smul₀`, the new mirror `Mathlib/Data/Matrix/Mul.lean`); 2 kept as local rewrites.
- [x] **5. F1** (`088d5dec`). `certPicture`/`certHeights`/`pencilConfigPoint_certPicture` moved to
  `Ear.lean`. The FRICTION entry is resolved.
- [x] **6–7b. B6a–c** (`552f5857`, `72f492e9`, `9b8148ba`). `change`/`show`: 35/30/26 sites, 32/24/16
  fixed. The kept sites (carrier, coe, let-defeq and fold reshapes) are listed in the commits.
  `TACTICS-GOLF.md` §27.
- [x] **8. B5** (`2f66dff2`; fixup `93ece315`). `Set`/`Finset`: 36 sites, 9 fixed, 27 kept. The
  `CoverageTheoremS.lean` finsum route is structural (see *Candidates*).
- [x] **9–12. B1a–d** (`6f2d75e5`, `a6c71d1c`, `3faf440e`, `de644285`). Dead `classical` and
  unforced `noncomputable`: 204 + 70 sites, of which 134 `classical` and 7 `noncomputable` were
  removed. Every kept site was forced by a build break.
- [x] **13. M3** (`a0dda000`). `span_supportExtensor_ofNormals_eq` moved above
  `…_ofNormals_congr`, whose orientation split it now replaces.
- [x] **14a–14b. M4** (`58c4fa28`, blueprint fixup `388e5a18`; `ab2253e1`). Four corollary
  rebases onto G1, G4, G5 and the core-heights lemma, with `\uses` edges added and prose
  re-pointed. Nothing was orphaned.
- [x] **15. M2b** (`289f96c3`). A private `splitOff_deficiency_le_aux` over `e₀ ∉ E(G) ∨ e₀ = eₐ`.
  Both public lemmas are now one-line corollaries.
- [x] **16. M2c-i** (`d7fea229`). `exists_insertion_of_star_sup_star` makes both insertions
  corollaries: 215 → 105 lines, heartbeats down about 3.4×.
- [x] **17. M2c-ii, not landed** (`1080f59c`). A `Fin.succAbove`-general `splitOff_ear` needs ad hoc
  numeral-modulus unfolds at every pivot, so it nets no shorter. `_four`/`_three` stay.
- [x] **18. M2c-iii** (`b8b24c9a`). `Graph.X0Attains.of_openEar_splitOff`, parametrized by the
  antecedent's ear length, with no `Fin.succAbove`: 704 → 461 lines, heartbeats halved,
  `Short.lean` 1 357 → 1 139. The FRICTION entry is resolved. TACTICS-QUIRKS §112, §114.

### The carried items (`notes/Phase40-design.md` §3/§4/§7), continued

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

**Next concrete commit: task 19, M2d** (§3, the 40h items): the pin budget of
`lem:pencil-ear-data` (`main-component.tex` 2181, `sec:main-component-short`, nine pins against
`blueprint/AUTHORING.md` D's four). Split the node along its three clauses, with the ear data as a
definition node, or leave the helpers unpinned; then repoint `EarGen.lean`'s 14 docstring
citations of the label clause by clause (40g's `75df1aac` is the precedent). No statement changes
strength. Task 18 (`b8b24c9a`) closed the M2c group and its FRICTION entry.

## Decisions made during this round

- **2026-09-29, the open.** The task list comes from sweeping the surface first, before any fix
  (`CLEANUP.md` *Workflow* rule 2).
  - Beyond `notes/Cleanup40.md` §2's list, it added F1 and F2 (two `[open]` FRICTION entries whose
    sites are all in the Lean surface), S1 (the one surface file well past the tripwire), and
    Phase 40's three nodes outside the four named chapters (folded into A-D).
  - 40h's file-size item is a standing rule, not a task: its plan fires only on a crossing. The
    close re-measures. Nothing moved to a later round; fixes precede the §A walks.
