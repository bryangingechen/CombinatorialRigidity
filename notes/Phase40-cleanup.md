# Phase 40 cleanup round 1/5 — `40-cleanup`, the mechanical round (work log)

**Status:** in progress (opened 2026-09-29). Round 1 of the five post-Phase-40 cleanup rounds.
Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` A and B over what Phases 39–40 built, C as screening only, and five carried items.
Tasks 1–13, 14a–14b, 15–20, 21a–21b, 22, 23a–23b, 24, 25, 26, 27, 28, 28b and 29 closed (17 not
landed); 16 of 50 one-commit tasks remain. **Next concrete task:** task 30, A-P2, the
blueprint-against-Lean walk of `pencil.tex`'s `sec:pencil-reduction`. Round manual: `CLEANUP.md`.

## Current state

**Next commit: task 30, A-P2** (*Lemma checklist*). The checklist holds 50 one-commit tasks;
tasks 1–13, 14a–14b, 15–20, 21a–21b, 22, 23a–23b, 24, 25, 26, 27, 28, 28b and 29 are closed (17 not
landed), 16 remain. Nothing is mid-stream.

Landed so far: tasks 1–20, 21a–21b, 22, 23a–23b, 24, 25, 26, 27, 28, 28b and 29, one line each under
*Lemma checklist → Landed* (task 17 closed not landed). A finished task gets one or two lines
there, with its commit; the detail stays in the commit message, and this section stays the
forward pointer.

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

### Landed: tasks 1–28 (one line each; each commit message has the detail)

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
- [x] **19. M2d** (`d9acaee8`). `lem:pencil-ear-data`'s nine pins split along its three clauses:
  `def:pencil-ear-data` (the construction, `earPicture`/`earHeight`/`earConfig`), `lem:pencil-ear-data`
  (clause 1, kept the old label), `lem:pencil-ear-data-picture` (clause 2), `lem:pencil-ear-data-open`
  (clause 3). Every `\uses`/`\cref` site in `main-component.tex` and all 14 `EarGen.lean` docstring
  citations repointed clause by clause; no statement changed strength.
- [x] **20. M5** (`473a4a11`). CHAINS' seven `pathVertex` helpers moved to `Cut.lean`; three of
  them (`isLink_pathVertex_rev`, the `val_eq_zero_or_of_pathVertex_mem` trio,
  `pathVertex_mem_insert_insert_range`) sit beside `pathVertex_cases`/`pathVertex_rev` rather than
  literally beside `def pathVertex`, since they need those first. The thirteen `Graph.IsOpenEar.*`
  lemmas moved to `Coverage.lean` beside `structure Graph.IsOpenEar`. `Coverage.lean`'s import
  closure is a superset of `CoverageChain.lean`'s own (which imported only `Coverage.lean`), so
  every one of the twenty fit; none stayed behind. No file pointers named the old file for these
  lemmas (grepped `.lean`/`blueprint`/`notes`), so nothing to repoint.

- [x] **21a–21b. F2** (`24ad0724`, `dd5be5d9`, `84fcc137`). Moved `Graph.closedNbhd_subset_vertexSet`
  to `Motive.lean` (21 inline copies dropped across the pencil tree) and the
  `infinitesimalMotions_eq_of_isLink_*` pair to `RigidityMatrix/Basic.lean`, beside
  `mem_infinitesimalMotions`. Closes the `[open]` FRICTION entry (line 3017).
- [x] **22. M6** (`0b5fcd46`). `mapExtensor` and `mapSupport` were one definition; `mapExtensor`
  survives, moved to `RigidityMatrix/Basic.lean`, and `mapSupport` is deleted with its six lemmas
  renamed to `mapExtensor`. The rank half was not re-derived — the bridge needs `[Finite α]`, which
  neither statement has.
- [x] **23a–23b. M1** (`36aa7e10`; `2d3d3818`). The stand-in audit of
  `lem:trivial-motions-rank-bound`'s 31 references: 12 repoint to `lem:relative-deficiency-rank-bound`
  (8 of the molecular chapters' 24 in 23a, 4 of the molecule/pencil chapters' 7 in 23b), the rest
  stay; both of `generic-lift.tex`'s stand-in citations (23a) also repoint.
- [x] **24. C1** (`0bdb1681`). `_three` live, 469 → 362 lines (heartbeats 72 044 → 60 555), via
  local substitutions only; `_four` stays off-headline, no split or unification (*Candidates*).
- [x] **25. C2** (`c6557860`). Both `Witness.lean` proofs live to their headline nodes; the
  `hPu`/`hP1`/`hP2` triple fused into `Engine.lean`'s
  `exists_smul_pencilChartPoint_of_hubSlotNormal_eq_pi_single`, all nine sites collapsed.
- [x] **26. C3** (`6ff611b0`). `Pair.lean`/`Pair2.lean`'s #4–#6 live; `hcross_eq` fused into
  `Graph.eq_and_eq_of_isLink_crossing` (`Motive.lean`). #4/#6's byte-identical shared tail is a
  candidate (a real sub-lemma design, not a small extraction).
- [x] **27. C4** (`a9a141c6`). #7–#9 all live (task 24's `hasGenericPencilRealization_of_IH`
  chain); no local fix, `Arms.lean` unchanged at 1 513 lines; #8's case-split duplication over
  `ScrewSpace`-carrier terms is a candidate.
- [x] **28. S1** (`9a424770`). `Witness.lean` split along its `## The general-position core`
  header into `Witness.lean` (1 109 lines) and `WitnessGeneral.lean` (685 lines); every file
  pointer naming a moved declaration repointed. `Arms.lean` left unchanged, still past ~1500.
- [x] **28b. S1 follow-up** (`47a24752`). `Arms.lean` split along its `## W3-L5: the base arm`
  header into `Arms.lean` (1 224 lines, loop + cut-edge arms and infra) and the new
  `ArmsAssembly.lean` (324 lines, base arm + bare-motive wrapper); `Pair.lean` gained an import
  and two docstring repoints, `Pair2.lean` one.

### §C: the long-proof screen (the top ten, walked; screening only)

Each walk asks §C's four questions: API extraction, a missed mathlib lemma, tactic substitution,
and definitional refactor. Cross-proof unification is §C's fifth bullet; here it goes to
*Candidates* unless the change is a small local extraction. Local changes land, and structural
findings are recorded as candidates. First run a cheap liveness check (`lean_references`,
transitively, to `pencil_conjecture` / `pencilPair_of_nonempty`). A proof that feeds neither
headline is recorded as off-headline (round 4's third question) and gets no local work.

(Tasks 27–28b, C4/S1, closed above. The ranking's tied tenth, `of_openEar_three`, and the twelfth,
`of_openEar_four`, are task 18's.)

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

- [x] **29. A-P1: `pencil.tex`, from `sec:pencil-through-point` through `sec:pencil-extension`**
  (38–468; 13 environments; this commit). 13 nodes walked, 2 divergences found and fixed: the
  cycle pair's proof `\uses` ran backwards (`lem:cycle-coplanar-realization` narrated as built
  directly from `lem:cycle-normals`, `lem:cycle-pencil-realization` narrated as built from it,
  while the Lean does the reverse — the pencil version is primary and the coplanar version is its
  one-line forgetful corollary); and `lem:two-pencil-extension-iff`'s backward direction rested on
  `span_range_eq_of_extensor_eq` (Plücker injectivity), pinned nowhere — its own docstring names an
  intended label (`lem:decomposable-extensor-span-unique`) never added, now minted in `meet.tex`.
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
- **`pencilPair_of_habitat_ncard_eq_four` feeds neither headline** (task 24, C1; round 4's third
  question). Its only caller is `pencil_conjecture_of_hcontract_hK_hbareSplit` (`Escape.lean`),
  and that theorem's only caller, `…_of_card`, has none. The headline reaches `|V| = 4` through
  `hasGenericPencilRealization_of_IH`'s other branches, not through a base leaf. By §C's rule it
  got no local work, and its `maxHeartbeats 400000` stays.
  - If round 4 keeps it, `_three`'s task-24 substitutions carry over. Its degree-2 facts are
    already proved before the `clear`, so the `hE*_sub`/`hdeg*_le` block (~60 lines) goes.
    `hLI4pts.mono` with `Graph.closedNbhd_subset_vertexSet` replaces the four closed-neighbourhood
    computations (~64 lines). Together they may retire the bump.
  - No `_three`/`_four` unification. The two proofs diverge step by step: in the identification
    (`_three` links every pair; `_four` rules out degree 3 through a triangle, then splits on `w`'s
    non-neighbour) and in the witness (one shared normal, against an opposite normal per vertex).
    The shared step is the join-detector rank computation. Its `m`-general form would need a
    standard-basis API for `⋀²K⁴` that the project lacks, which is not worth building for an
    off-headline proof.
- **A #4/#6 cross-proof unification of `Pair2.lean`'s two pendant producers** (task 26,
  C3; `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant`, #4, and its
  `_deg3` sibling, #6). Once `hcross_eq` is factored out (landed), the two proofs' shared tail —
  `normal_vc`'s choice through the pendant hinge, the glued data, `hlinks`, the four
  nonzero/incidence `have`s, `hadjLI` (conjunct 2), and the entire rank section — is
  byte-identical, ~190 lines each. A shared sub-lemma would need to abstract over: (a) the
  `point_vc`-avoidance target (a `≤ 2`-generator cover of `H.closedNbhd u_c`'s point image in
  #4, vs. `span {point₁ u_c}` in #6), and (b) conjunct 3's closed-hub-neighbourhood
  transfer (`Graph.pencilHub_iff_induce_of_degree_ne`, unconditional, in #4; the promoted
  triple `hpromoted` at `{u_c, w₁, w₂}`, in #6) and conjunct 4's `v = u_c` case (a nontrivial
  `≤ 2`-generator cover argument in #4; vacuous — `u_c` is always a `G`-hub — in #6). That
  is a real design task (a shared lemma taking the avoidance target and the hub-transfer proof as
  parameters), not a small local extraction — structural, per §C's fifth bullet.
- **#8's `|C| = 0`/`|C| = 1` case-split duplication** (task 27, C4;
  `hasPencilRealization_of_not_twoEdgeConnected_core`, `Arms.lean`). The two branches of the case
  split share four near-identical sub-`have`s (`hnorm_nz`/`hextF_nz`/`hpoint_nz`/`hpoint_inc`)
  almost verbatim, differing only in referencing the primed (`F₂'`/`normal₂'`/`h (normal₂ ·)`) vs.
  unprimed `V₂`-side data, over `extF : β → ScrewSpace K 2` throughout. A shared local lemma would
  need to abstract over the assembled `normal`/`point`/`extF` on the `V₂` side (plain vs.
  transported by the repositioning automorphism `(g, h)`) — a real design task, not a small local
  extraction, and squarely in the scope-pin's `ScrewSpace`-carrier caution. Not attempted.

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

**Next concrete commit: task 30, A-P2** (§A, the blueprint-against-Lean walk). `pencil.tex`,
`sec:pencil-reduction` (469–755; 11 environments): compare each `\leanok` node's statement with its
pinned Lean signature, check the laundering walk, and read the prose proof for oversell. Tasks
30–44 (§A) walk the rest of the surface; task 45 closes the round.

Task 29 (this commit) walked `pencil.tex`'s 13 environments from `sec:pencil-through-point` through
`sec:pencil-extension` against their pinned Lean (`Molecular/Molecule/Pencil/Statement.lean`).
Every statement's hypotheses/conclusion/binders match its Lean signature, and every `\leanok`
node's hypotheses are ambient or discharged — no laundering. Two divergences surfaced and were
fixed, both in proof-level `\uses`/prose only (no statement changed):
- **The cycle pair's proof dependency ran backwards.** The Lean builds
  `exists_pencilPanelRealization_cycle` (`lem:cycle-pencil-realization`) directly from
  `exists_cycle_normals` + `exists_concurrency_point_of_extensorInPanel_pair`, and
  `exists_coplanarPanelRealization_cycle` (`lem:cycle-coplanar-realization`) is a one-line corollary
  that forgets the point (matching that decl's own Lean docstring: "Immediate corollary of the
  pencil realization … discarding the per-body concurrency point"). The blueprint had it exactly
  backwards — `lem:cycle-coplanar-realization`'s proof claimed the direct build from
  `lem:cycle-normals`, and `lem:cycle-pencil-realization`'s proof claimed to build from
  `lem:cycle-coplanar-realization`. Swapped both proofs' `\uses` edges and content to match; no
  statement changed.
- **A missing `\uses` target with no blueprint node at all.** `lem:two-pencil-extension-iff`'s
  backward direction rests on `span_range_eq_of_extensor_eq` (Plücker injectivity: equal nonzero
  decomposable `2`-extensors span the same plane), which was pinned nowhere in the blueprint — not
  even inside another node's declaration-list cluster. Its own Lean docstring names an intended
  label, `lem:decomposable-extensor-span-unique`, never added. Minted that node in `meet.tex`
  (beside `lem:case-III-claim612-line-in-panel-union`, whose converse it is) and added it to
  `lem:two-pencil-extension-iff`'s proof `\uses`.

`blueprint/lint.sh` and `blueprint/verify.sh` (bp + web + checkdecls) both green after the fixes.

Task 28b split `Arms.lean` at its `## W3-L5: the base arm` header into `Arms.lean`
(1 224 lines: loop arm `L3`, cut-edge arm `L4` and its transport/nondegeneracy/rank-assembly
infra) and the new `ArmsAssembly.lean` (324 lines: base arm `L5`, bare-motive wrapper `L7`).
`Pair.lean` — the only real caller of the moved `hasPencilRealization_of_ncard_le_two` (via
`Motive.lean`'s transitive import, which itself needs nothing from the new file) — gained a
direct `ArmsAssembly` import and its one specific-declaration docstring repoint;
`Pair2.lean` had one (`pencil_conjecture_of_arms`, docstring-only, never called elsewhere). Every
other `Arms.lean` docstring pointer in the tree (`Engine`/`Motive`/`Pair`/`Pair2`/`TACTICS-GOLF`/
`FRICTION`/`Phase40-design`) names a declaration that stayed, so was left as-is.

## Decisions made during this round

- **2026-09-29, the open.** The task list comes from sweeping the surface first, before any fix
  (`CLEANUP.md` *Workflow* rule 2).
  - Beyond `notes/Cleanup40.md` §2's list, it added F1 and F2 (two `[open]` FRICTION entries whose
    sites are all in the Lean surface), S1 (the one surface file well past the tripwire), and
    Phase 40's three nodes outside the four named chapters (folded into A-D).
  - 40h's file-size item is a standing rule, not a task: its plan fires only on a crossing. The
    close re-measures. Nothing moved to a later round; fixes precede the §A walks.
