# PROSE findings ledger

The one home of every finding the **PROSE** rounds make (`notes/Prose.md` §4). Round 1's open
created it (2026-10-07). Rounds 1–4 only append to it. Round 5, `prose-graph`, sets each entry's
disposition, acts on the `E`, `N`, `T` and `U` entries, and reports the `S`, `L` and `M` entries to
the PI. A round's work log names a finding by its ID, in one line under *Candidates for …* or
*Moved to a later round*; the finding itself is written only here (`notes/CLAUDE.md` *One
canonical home per content type*). At round 5's close (2026-10-15) all 250 entries have their
disposition, 87 `done`, 16 `left` and 147 `reported`, each round-5 task named by its commit; the
report is `notes/Prose-report.md`. Its follow-up, RECONCILE (`notes/Reconcile.md`, queued
2026-10-15), keeps this ledger as each finding's home and sets the dispositions it acts on. At
RECONCILE round 1's close (2026-10-15) the ledger has 252 entries (`F-251` and `F-252` are the
round's), 89 `done` (`F-228` and `F-251` joined), 16 `left` and 147 `reported`, each round-1 task
named by its commit. At RECONCILE round 2's close (2026-10-15) it has 264 entries (`F-253` to
`F-264` are the round's), 133 `done`, 11 `left` and 120 `reported` (the six `L` entries of the
round are `reported`, to round 3's docstring sweep), each round-2 task named by its commit.

## Format

One entry per finding, under its category's section, in ID order:

```
- **F-NNN** · <cat> · `<label or decl>` (`<file>`): the finding, in one or two sentences.
  *Evidence:* measured (script at <sha>) | read (Lean body, or source passage) | suspected.
  *Found:* <round> task N.
```

- **IDs** are minted in order across all categories and all rounds: the next ID is one more than
  the largest in this file. An ID is never reused or renumbered.
- **Evidence** says how the finding was established. *Measured* names the commit of the audit
  script (`scripts/blueprint-deps.py`, round 1 task 2) whose report shows it. *Read* names what
  was read: a Lean declaration's statement or body (never its docstring), or a source passage
  with its page. *Suspected* means neither, yet.
- **Round 5 adds a third line** to each entry: `*Disposition:* done (<sha>) | left (<reason>) |
  reported`. RECONCILE's new entries (from `F-251`) read `open (<work log>, task N)` until a task
  sets one of these (`notes/Reconcile-texts-cleanup.md` *Scope*).
- **What is not a finding.** A slice fixes, rather than records, what is prose and local to the
  slice: register, anchoring, a citation it can verify, and a terminology choice within its
  chapter.
- **The bar for "notice"** (`notes/Prose.md` §4). A builder records what it meets while reading
  its slice's pins and sources; no slice runs a separate Lean audit. Systematic coverage comes from
  the script's reports and the Lean baselines below.
- **The audit script's findings are grouped, not one per edge** (round 1 task 2). Missing edges
  get one `E` entry per chapter group: the four prose rounds' chapters, and `pencil.tex` with
  `main-component.tex` as a fifth. Each carries per-chapter counts. Unbacked edges, which are for a
  check and not defects, get one `E` entry with per-group counts. Each node-shape pattern gets one
  `N` entry naming its nodes. The edge-level detail is the script's output, reproducible on the
  entry's tree with `python3 scripts/blueprint-deps.py --chapter <name>` or `--label <label>`.
  Round 5's open re-runs it before it triages.

## Categories

| Cat | What | Acted on by |
|---|---|---|
| `E` | a `\uses` edge missing or unbacked; a node the graph draws unfilled | round 5 |
| `N` | a node bundling unrelated results (principle D), a pinned helper, a load-bearing lemma with no node | round 5 |
| `T` | a term or notation used inconsistently across chapters, or a coinage whose definition is hard to find | round 5 (prose) |
| `U` | `README.md`, `home_page/index.md` or `formalization.yaml` text that contradicts a rewritten chapter | round 5 |
| `S` | a statement stronger or weaker than its pins, or a headline signature oddity | the PI, after the report |
| `L` | Lean: dead or duplicated code, a long proof or missed mathlib lemma, a docstring or comment that contradicts its body, an unused binder, inconsistent naming | a later cleanup round |
| `M` | mathematics and sources: an unverifiable citation, a gap between a prose argument and the Lean, a misattribution too large for its slice | the PI, after the report |

## Lean baselines (round 1, task 2)

Measured by round 1's task 2 at `bca00d3f`, whose Lean tree is `6f4f7afa`'s and `64bb9754`'s.
These are inputs for a later Lean round, not tasks of this program (`notes/Prose.md` §4).

**`CLEANUP.md` §B's smells**, counted by `python3 scripts/cleanup-smell-sweep.py --base bca00d3f
--rev bca00d3f --tree CombinatorialRigidity/` over every line of the 152 files (110 881 lines):

| Smell | Count |
|---|---|
| `classical` | 430 |
| `haveI-Fintype` | 1 |
| `nolint/linter` | 34 |
| `noncomputable-def` | 191 |
| `change/show` | 169 |
| `rw4+` | 282 |
| `show-from-rfl` | 39 |
| `maxHeartbeats` | 5 |
| `toFinset` | 253 |
| `Fintype.card` | 322 |

**`CLEANUP.md` §C's ranking by declaration span, top 20.** §C's awk, run once per file over every
`.lean` file under `CombinatorialRigidity/`, with the file name added. §C's own command globs only
the 23 top-level files, and its `NR` runs on across files.

```sh
for f in $(find CombinatorialRigidity -name '*.lean' | sort); do awk -v f="$f" '
  /^(private )?(theorem|lemma) /{ if (line) print NR-line, f":"line, name; name=$0; line=NR; next }
  /^[^[:space:]]/{ if (line) { print NR-line, f":"line, name; line=0 } }
  END{ if (line) print NR-line+1, f":"line, name }' "$f"; done | sort -rn | head -20
```

Each entry gives the span, the file under `CombinatorialRigidity/` with the header's line, and the
declaration's name as its header writes it:

1. 801 lines, `Molecular/AlgebraicInduction/CaseII.lean:296`:
   `PanelHingeFramework.case_II_realization_all_k`
2. 484 lines, `Molecular/Induction/ForestSurgery/EdgeSplitting.lean:975`:
   `splitOff_reroute_packing` (private)
3. 402 lines, `Molecular/Molecule/Pencil/MainComponent/GenericTriangle.lean:158`:
   `hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization`
4. 393 lines, `Molecular/AlgebraicInduction/CaseIII/Realization.lean:318`:
   `PanelHingeFramework.case_III_candidate_dispatch`
5. 369 lines, `Molecular/Molecule/Pencil/MainComponent/Orbit.lean:729`:
   `Graph.X0Attains.of_openEar_two_of_splitOff`
6. 329 lines, `Molecular/Molecule/Pencil/MainComponent/SplitOff.lean:410`:
   `Graph.X0Attains.of_splitOff`
7. 326 lines, `Molecular/Molecule/Pencil/Pair2.lean:63`:
   `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI`
8. 320 lines, `Molecular/Molecule/Pencil/Pair.lean:682`:
   `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`
9. 303 lines, `Molecular/Molecule/Pencil/MainComponent/ContractAdditive.lean:64`:
   `Graph.X0Attains.of_additiveContract`
10. 298 lines, `Molecular/Induction/ForestSurgery/Reduction.lean:1143`:
    `forest_surgery_count`
11. 289 lines, `Molecular/Induction/ForestSurgery/Reduction.lean:1868`:
    `splitOff_isMinimalKDof_of_pos`
12. 286 lines, `Molecular/Molecule/Pencil/MainComponent/GenericTriangle.lean:693`:
    `pencilPair_of_simple_ncard_eq_three`
13. 285 lines, `Molecular/Molecule/Pencil/MainComponent/GenericEar.lean:98`:
    `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization`
14. 273 lines, `Molecular/AlgebraicInduction/Theorem55.lean:1783`:
    `case_I_realization_nonsimple_gen`
15. 273 lines, `MatroidIdentification.lean:337`:
    `typeII_edgeSetRowIndependent_extend`
16. 264 lines, `Molecular/Molecule/Pencil/MainComponent/GenericSteer.lean:48`:
    `exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub`
17. 263 lines, `Molecular/Induction/Operations.lean:1270`:
    `splitOff_isLink_relabel`
18. 262 lines, `Molecular/Induction/ForestSurgery/ChainExtraction.lean:465`:
    `chainWalk_trichotomy`
19. 255 lines, `Molecular/AlgebraicInduction/CaseIII/Realization.lean:859`:
    `PanelHingeFramework.chainData_split_w6b_gates`
20. 254 lines, `Molecular/AlgebraicInduction/Theorem55.lean:1500`:
    `case_cut_edge_realization_gp_gen`

## E — edges

- **F-001** · E · round 1's chapters (`sparsity.tex` … `executable.tex`): 83 missing edges, each
  a node its pins reach that its `\uses` do not name and the drawn graph does not show, at 37
  nodes (9 through a statement): `pebble-game` 36, `rigidity-matroid` 25, `laman-theorem` 5,
  `sparsity` 4, `executable` 4, `henneberg` 3, and 2 each in `frameworks`, `trivial-motions` and
  `count-matroid`. The commonest targets are
  `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow` (11), `dfs.tex`'s
  `def:reachClosureComputable` and `lem:mem-reachClosureComputable` (10 each) and
  `lem:rigidityMap-apply` (8); 293 more are implied by other `\uses`.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`9eb2c776`): of the 71 missing at `0f9c275c`, 40 added and 31 implied by
  them, and 5 that the task's removals of unbacked edges left missing added too; none is missing.
- **F-002** · E · round 2's chapters (`matroid-union.tex` … `meet.tex`): 99 missing edges at 58
  nodes (38 through a statement): `molecular-induction` 42, `meet` 24, `deficiency` 18,
  `rigidity-matrix` 13, `body-bar` and `extensor` 1 each. 38 of them go to `def:edge-multiply`;
  279 more are implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`3575835c`–`eaba775e`): none of the eight chapters has a missing edge. Of the
  26 and 17 missing at the two tasks' parents, 14 and 9 were added and the rest are implied by them;
  each task also added the edges its removals of unbacked edges left missing.
- **F-003** · E · round 3's files (`algebraic-induction.tex` and its five sections): 164 missing
  edges at 47 nodes (42 through a statement): `case-iii` 70, `case-i` 52, `panel-layer` 26,
  `case-ii` 15, `genericity-and-count` 1. The commonest targets are `def:rigidity-matrix` (15),
  `def:panel-general-position` (13) and `lem:general-position-support-nonzero` (10); 473 more are
  implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`6af43988`–`e1b16939`): none of the five sections has a missing edge. Of the
  44, 19 and 67 missing at the three tasks' parents, 27, 15 and 28 were added and the rest are
  implied by them; each task also added the edges its removals of unbacked edges left missing.
- **F-004** · E · round 4's chapters (`bar-joint-3d.tex` … `generic-lift.tex`): 76 missing edges
  at 42 nodes (28 through a statement): `jacobs` 33, `molecule-modelling` 17, `generic-lift` 14,
  `bar-joint-3d` and `molecule-application` 6 each. The commonest targets are
  `lem:rigidityMap-apply` and `lem:molecule-graph-carrier` (10 each); 267 more are implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`e9d59672`): none of the five chapters has a missing edge. Of the 65 missing
  at the task's parent, 32 were added and 33 are implied by them; the task also added the 6 edges
  its removals of unbacked edges left missing.
- **F-005** · E · `pencil.tex` and `main-component.tex`: 114 missing edges at 58 nodes (31
  through a statement): `main-component` 87, `pencil` 27. 43 go to two pinned helpers (F-010):
  `lem:pencil-bridge-fibre` (25) and `thm:pencil-jj-equality` (18); 710 more are implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`23bf8244`–`60c88e44`): neither chapter has a missing edge, nor does any
  other (`--summary` at `60c88e44`: 0 missing). Of the 26 and 28 missing in the two tasks' parts at
  their parents, 19 and 20 were added and the rest are implied by them; `23bf8244` also added the 5
  edges its removals of unbacked edges left missing, and `60c88e44`'s removals left none.
- **F-006** · E · unbacked `\uses`, every chapter: 397 `\uses` targets that no pin of the using
  node reaches. 87 are reached only through another pinned node, and 310 not at all; per group
  (through a node / not at all): round 1 5/19, round 2 11/88, round 3 32/120, round 4 22/21,
  `pencil`/`main-component` 17/62. They are for a check, not defects. Example:
  `thm:isSparse-exists-typeI-or-typeII-reverse` uses `def:typeI` and `def:typeII`, but its pin
  states the decomposition by degrees and neighbourhoods and names neither.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`);
  the example read (`IsSparse.exists_typeI_or_typeII_reverse`'s statement, `Sparsity.lean`).
  *Found:* round 1 task 2.
  *Disposition:* done (`9eb2c776`–`60c88e44`): each task read its chapters' unbacked edges under the
  edge policy (`notes/Prose-graph-cleanup.md` *Scope*) and removed those with no Lean basis that
  neither the statement, the proof prose nor the pins use, 196 in all (17, 34, 39, 27, 15, 33, 10,
  13 and 8), each with its reason in its task's commit. The rest stay, 84 + 145 at `60c88e44`: those
  through a node, a use by the pins, and those with no Lean basis that the text uses, read as the
  work log's *Decisions* records (a symbol the target defines, a step the proof cites, a pin two
  nodes share). The example's edges to `def:typeI` and `def:typeII` went at `9eb2c776`: the theorem
  states $G - v$ and $G - v + ab$ directly, and its proof names no move.
- **F-007** · E · `rem:kt-lemma-41` (`molecular-induction.tex`): `lem:base-vfiber-count`,
  `lem:acyclic-insert-vfiber` and `lem:balanced-forest-packing` use this remark, and the graph
  draws only edges between nodes, so none of the three edges is drawn (`lint.sh` check 1 passes
  them: the label exists). The same chapter's example `ex:kt-41-overquantified` pins
  `Graph.kt_lemma_41_overquantified`, which `checkdecls` checks and no node shows.
  *Evidence:* measured (`scripts/blueprint-deps.py`'s parse notes, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`eaba775e`): the three `\uses` of the remark removed, as an edge to KT Lemma
  4.1's node (`lem:forest-surgery-split`) would close a cycle through `lem:balanced-forest-packing`;
  each of the three proofs cites the remark instead. The remark had drawn 83 nodes `#9CEC8B`, as not
  fully proved; none is now. The example keeps its pin, which `checkdecls` checks.
- **F-008** · E · the graph's four unfilled nodes: `def:blockingWitness` (`pebble-game.tex`),
  `def:induced-span` and `lem:forest-surgery-unsplit` (`molecular-induction.tex`) have neither a
  pin nor `\leanok`; `def:dof-generic` (`rigidity-matrix.tex`) pins
  `BodyHingeFramework.IsInfinitesimallyRigid` without `\leanok`.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; the built graph at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`8e6786d3`) for `def:induced-span`; left for `def:blockingWitness` and
  `def:dof-generic` (no declaration defines them; `7b2a8272`, `a7b8ea35`) and
  `lem:forest-surgery-unsplit` (`F-091`); round 2: `lem:forest-surgery-unsplit` pinned and filled
  (`43c5c8d7`).
- **F-062** · E · `lem:case-II-placement-new-rows` (`algebraic-induction/genericity-and-count.tex`):
  its statement and proof use `lem:rank-delete-vertex`, which no pin reaches, and its proof cites
  that node for the dimension $D - 1$ of the hinge-row block, which is `def:hinge-row-block`'s
  (`finrank_hingeRowBlock`, which the pin reaches through its proof).
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:case-II-placement-new-rows`, at
  `47eb5225`'s Lean); read (the proof's prose).
  *Found:* round 2 task 2.5.
  *Disposition:* done (`1096d2d9`): both edges to `lem:rank-delete-vertex` removed, as the proof
  cites `def:hinge-row-block` and `lem:edge-rows-independent` for the dimension $D - 1$, and not
  that node; the proof now `\uses` `lem:rows-polynomial-in-normals`, which its pins reach and it
  cites.
- **F-066** · E · `lem:rank-transport-relabel-of-le-finrank` and
  `lem:rank-polynomial-IH-relabel-proj` (`rigidity-matrix.tex`): edges that name the wrong node.
  The first uses `def:genuine-hinge-realization`, which its pin does not reach; its hypothesis is
  `HasGenericFullRankRealization`, `def:rank-hypothesis`'s pin (implied), and it reaches
  `def:panel-general-position` (missing). The second uses `lem:rank-polynomial-of-le-finrank`,
  which its pin does not reach; it goes through the pin of `lem:rank-polynomial-proj-eval` and
  `lem:general-position-support-nonzero` (both missing). Task 2.7's prose cites the reached nodes.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter rigidity-matrix`, at `af438fd1`); read
  (both pins' statements and bodies).
  *Found:* round 2 task 2.7.
  *Disposition:* done (`3575835c`): both unbacked edges removed; the first's statement takes
  `def:rank-hypothesis` and `def:panel-general-position`, the second's proof
  `lem:rank-polynomial-proj-eval`, `lem:general-position-support-nonzero` and
  `lem:independent-rows-of-rank`.
- **F-071** · E · `def:matroid-MG`, `def:D-deficiency`, `lem:deficiency-antitone` and
  `lem:cut-edge-decomposition` (`deficiency.tex`): edges the pins do not back, two of them into
  later nodes of the chapter. `def:matroid-MG` uses `thm:tay-witness`, which its pins do not reach;
  their step is `thm:unionPow-cycle-indep-iff-sparse` (implied). `def:D-deficiency` uses
  `def:matroid-MG`, which `partitionDef` and `deficiency` do not reach. The proof of
  `lem:deficiency-antitone` uses the later `lem:rk-within-parts`, unreached (its third pin is the
  count the proof needs). The proof of `lem:cut-edge-decomposition` uses the later
  `thm:def-eq-corank`, unreached (the attaining partitions exist as there are finitely many),
  while its pins reach the later `lem:subgraph-minimality` (for its (2), through
  `exists_cut_decomposition_of_not_twoEdgeConnected`) and `lem:two-vertex-trichotomy` (that node's
  pin `deficiency_of_edgeSet_empty`, for its (3)), which its `\uses` do not name. Task 2.8's prose
  cites `lem:subgraph-minimality` as a later lemma and computes the one-vertex deficiency directly;
  moving KT Lemma 3.3's two nodes before KT Lemma 3.6, KT's order, would cure the forward use.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter deficiency`, at `27daa953`); read
  (the pins' statements and bodies).
  *Found:* round 2 task 2.8.
  *Disposition:* done (`3575835c`): the four unbacked edges removed, `def:matroid-MG`'s proof takes
  `thm:unionPow-cycle-indep-iff-sparse`, and `lem:cut-edge-decomposition`'s proof
  `lem:subgraph-minimality`. The move is moot: KT Lemma 3.3's two nodes have preceded KT Lemma 3.6's
  since round 2 (`22317b88`), and none of the four nodes' edges points forward now.
- **F-076** · E · `lem:circuit-rigid`, `lem:two-vertex-trichotomy` and `lem:deficiency-ear`
  (`deficiency.tex`): edges the pins do not back, and missing edges into later chapters. The
  statement of `lem:circuit-rigid` uses `def:rigid-subgraph`, which its pin does not reach (the
  rigidity of $G[V(X)]$ is `lem:circuit-induces-rigid`'s). The statement of
  `lem:two-vertex-trichotomy` uses `lem:matroid-restrict-subgraph` and `thm:def-eq-corank`, which
  only the proof of its third pin reaches; that proof also reaches `lem:two-vertex-zero-dof`
  (`molecular-induction.tex`) through `isKDof_zero_of_parallel_pair`, which no `\uses` names. The
  proof of `lem:deficiency-ear` reaches `lem:exists-tight-partition` (`jacobs.tex`) for an
  attaining partition. Task 2.9's prose computes the parallel pair's deficiency and cites the later
  node in a sentence; either missing edge would be a forward `\uses` across chapters (`F-050`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `86b44e1b`); read (the pins'
  statements and bodies).
  *Found:* round 2 task 2.9.
  *Disposition:* done (`3575835c` and `90b68fd1`): `lem:circuit-rigid`'s unbacked edge removed,
  `lem:two-vertex-trichotomy`'s two statement edges left to its proof, and the two missing edges
  added; both pointed to later chapters (the forward screen, `76c3c4d4`–`b384225a`). `90b68fd1`
  cured both: `lem:two-vertex-zero-dof` moved before `lem:two-vertex-trichotomy`, and
  `def:tight-partition` with `lem:exists-tight-partition` from `jacobs.tex` to follow
  `def:D-deficiency`.
- **F-078** · E · `thm:def-eq-corank`, `lem:rk-within-parts` and
  `lem:deficiency-zero-iff-tree-packing` (`deficiency.tex`): edges the pins do not back, and one
  missing. The statement of `thm:def-eq-corank` uses `lem:rank-matroidMG-le`, which none of its
  three pins reaches and its proof does not need: the bound is `lem:weak-duality` at the
  partition $\{V(G)\}$. `rank_matroidMG_le` is reached only from `lem:circuit-induces-rigid`
  (`molecular-induction.tex`). The statement of `lem:rk-within-parts` uses `def:matroid-MG` and
  `def:D-deficiency`, which its pin does not reach; it is about the cycle matroid of $\tilde G$
  and a partition. The pin of `lem:deficiency-zero-iff-tree-packing` reaches `def:k-dof`, which
  its `\uses` do not name, through the unpinned `IsKDof.exists_isBase_isForestPacking`.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `22317b88`); read (the pins'
  statements and bodies).
  *Found:* round 2 task 2.10.
  *Disposition:* done (`3575835c`): the three unbacked edges removed; `lem:rk-within-parts`'s
  statement takes $\tilde G$'s `def:edge-multiply` and `def:body-bar-framework` instead, and
  `lem:deficiency-zero-iff-tree-packing`'s proof `def:k-dof`.
- **F-082** · E · `def:induced-span`, `def:rigid-contraction` and the contraction lemmas
  (`molecular-induction.tex`): `def:induced-span` has no pin (`F-008`); its statement named
  `Graph.fiberSpan` and `Graph.inducedSpan` (`Induction/Operations.lean`), which define $V(X)$ and
  $G[V(X)]$ and which the two pins of `lem:circuit-induces-rigid` use, so pinning them would back
  that node's edge to it. The statements of `lem:contract-rank-bridge` and
  `lem:contract-minimality-transport` use `def:rigid-contraction`, which their pins, about the
  matroid contraction $M(\tilde G)/E(\tilde H)$, do not reach; the graph $G/E(H)$ enters with
  `lem:rigidContract-isMinimalKDof` (`case-i.tex`). The statement of `lem:contraction-minimality`
  uses `lem:rigid-full-rank` and `lem:contract-rank-bridge`, which only its proof's two nodes use.
  `def:rigid-contraction` stood after the three nodes that use it; task 2.11 moved it before them.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `1b06def1`); read (the pins'
  statements).
  *Found:* round 2 task 2.11.
  *Disposition:* done (`eaba775e`): `def:induced-span` pinned at `8e6786d3`; the edges of
  `lem:contract-rank-bridge` and `lem:contract-minimality-transport` to `def:rigid-contraction`
  removed, with the second's to `lem:subgraph-minimality`; `lem:contraction-minimality`'s statement
  edges to `lem:rigid-full-rank` and `lem:contract-rank-bridge` moved to its proof, and its edge to
  `lem:subgraph-minimality` removed.
- **F-089** · E · the surgery's lemmas (`molecular-induction.tex`): the statement edges of
  `lem:reroute-cycle-lift` and `lem:reverse-pendant-insert` to `lem:reroute-vfree-transport`, and
  of `lem:reverse-reroute-cycle-lift` to `lem:reroute-cycle-lift`, have no Lean basis; the prose
  proofs use those lemmas, so the edges belong on the proofs. `lem:forest-surgery-count`'s
  statement edge to `lem:balanced-forest-packing` is unbacked (the statement assumes such a
  partition). Its proof and `lem:edge-splitting`'s cite `lem:forest-packing-decomp`, which the
  first pin reaches and no proof `\uses` names. `lem:reverse-reroute-cycle-lift`'s pin reaches
  `lem:splitoff-edge-substitution` (`case-ii.tex`) through `removeVertex_le`: that node states that
  $G_v$ is a subgraph of $G$ and of $G_v^{ab}$, which the four reroute proofs use, two chapters
  later.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `01aec968`); read (the pins'
  statements).
  *Found:* round 2 task 2.13.
  *Disposition:* done (`eaba775e` and `90b68fd1`): `lem:reroute-cycle-lift`'s edge to
  `lem:reroute-vfree-transport` moved to its proof, which applies the lemma; those of
  `lem:reverse-pendant-insert` and `lem:reverse-reroute-cycle-lift` removed, as their proofs follow
  an argument ("as in the proof of", "we reverse the argument of", `F-175`);
  `lem:forest-surgery-count`'s edge to `lem:balanced-forest-packing` removed, and its proof and
  `lem:edge-splitting`'s now `\uses` `lem:forest-packing-decomp`; `lem:reverse-reroute-cycle-lift`'s
  proof edge to `lem:splitoff-edge-substitution` added, a forward edge, which `90b68fd1` cured by
  moving that lemma from `case-ii.tex` to follow `def:graph-operations`.
- **F-093** · E · `lem:splitoff-deficiency` and `lem:removal-deficiency`
  (`molecular-induction.tex`): edges the pins do not back. The statement of
  `lem:splitoff-deficiency` uses `def:matroid-MG` and `thm:def-eq-corank`, which neither of its
  pins reaches: both bounds compare partition values (`def:D-deficiency`, implied), and the prose
  said "through the def = corank bridge" until task 2.14. The statement of
  `lem:removal-deficiency` uses `lem:splitoff-deficiency`, which `removeVertex_deficiency_ge` does
  not call; its proof argues as that lemma's does. The proof edge of
  `lem:splitoff-deficiency-reuse` to `lem:splitoff-deficiency` is likewise unbacked (both pins apply
  a private shared core), and stands for the same argument.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `90051e3c`); read (the pins'
  statements and bodies).
  *Found:* round 2 task 2.14.
  *Disposition:* done (`eaba775e`): the four unbacked edges removed, the last two as their proofs
  follow `lem:splitoff-deficiency`'s argument; the two bounds' statements now `\uses`
  `def:D-deficiency`.
- **F-095** · E · KT Lemmas 4.3(ii)–4.8's nodes (`molecular-induction.tex`): edges the pins do
  not back, and edges they need. The statement edges of `lem:reduction-step` to
  `lem:reducible-vertex` and `lem:reduction-measure`, and of `lem:reduction-step-pos` to
  `lem:reduction-measure`, have no Lean basis; since task 2.15 neither statement names them (the
  vertex count follows `lem:reduction-step` in prose). `lem:reduction-step-pos` reaches
  `lem:edge-set-indep-pos` only through `lem:removal-deficiency-strict`. The statement edges of
  `lem:splitoff-kdof-criterion` and `lem:removal-deficiency-strict` (whose proof has no `\uses`)
  are their proofs'. Missing: `lem:rigid-full-rank`, which the proofs of `lem:edge-set-indep-pos`
  and `lem:reduction-step-pos` cite; `lem:splitoff-edge-substitution` (`case-ii.tex`, `F-089`),
  which the pins of `lem:removal-deficiency-strict` and `lem:reduction-step-pos` reach; and
  `def:cut-edges-2ec`, whose 2-edge-connectivity the statement of `lem:reducible-vertex` uses.
  Round 3's pointers: `lem:rigidContract-isMinimalKDof` (`case-i.tex`) uses and cites
  `lem:reduction-step` for the smaller vertex count, which is `lem:reduction-measure`'s, and the
  proof of `lem:case-II-realization` (`case-ii.tex`) cites `lem:reduction-step-pos` for the vertex
  of degree two, which is `lem:reducible-vertex`'s.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `d9b0e96a`); read (the pins'
  statements and bodies; the two citing passages).
  *Found:* round 2 task 2.15.
  *Disposition:* done (`eaba775e`): the three statement edges with no Lean basis removed; those of
  `lem:splitoff-kdof-criterion` and `lem:removal-deficiency-strict` moved to their proofs;
  `lem:edge-set-indep-pos`'s proof edge to `lem:rigid-full-rank` added, through which
  `lem:reduction-step-pos` reaches it, and `lem:reducible-vertex`'s to
  `lem:two-edge-connected-degree`, which implies `def:cut-edges-2ec`.
  `lem:splitoff-edge-substitution` is implied at both nodes, and `lem:reduction-step-pos`'s edge to
  `lem:edge-set-indep-pos`, reached through `lem:removal-deficiency-strict`, stays. The two citing
  passages cite `lem:reduction-measure` and `lem:reducible-vertex` already.
- **F-100** · E · KT Theorem 4.9 to `lem:chain-data-of-noRigid` (`molecular-induction.tex`): edges
  the pins do not back, and edges they need. `thm:minimal-kdof-reduction` has its five `\uses` on
  its statement and none on its proof. Its edge to `lem:contraction-minimality` has no Lean basis:
  the pin hands case (c) the induction hypothesis and forms no contraction (its part (i), which no
  declaration states, needs the graph form `lem:rigidContract-isMinimalKDof`, `case-i.tex`;
  `F-101`). It misses `def:cut-edges-2ec` (`twoEdgeConnected_of_isKDof_zero`). No node's pins
  reach `Graph.minimal_kdof_reduction`: `lem:case-I` (`case-i.tex`) uses the node all the same,
  and `algebraic-induction.tex`'s opening says that KT Theorem 5.5 is proved with it, while
  `thm:theorem-55` runs on `thm:minimal-kdof-reduction-all-k`. The statement edges of both KT
  Lemma 6.1 nodes to `thm:minimal-kdof-reduction-all-k` have no Lean basis (their hypotheses have
  the shape of its induction hypothesis). `lem:case-cut-edge-realization-gp`'s edge to
  `lem:genericity-device` has none (its pin takes a non-root of a product of polynomials by
  `MvPolynomial.exists_eval_ne_zero`, the device's argument), and the node misses
  `def:panel-general-position`, `lem:general-position-support-nonzero` and `def:graph-operations`
  (the endpoint choice), which its pin reaches. The proof edges of `lem:adjacent-degree-two-pair`
  to `lem:two-vertex-zero-dof` and `lem:simple-minimal-noRigid` have no Lean basis (the count uses
  only that $G$ has no loops and minimum degree two), and it misses `def:cut-edges-2ec`; its
  statement edges are its proof's.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `a2df0ed3`); read (the pins'
  statements and bodies).
  *Found:* round 2 task 2.16.
  *Disposition:* done (`eaba775e`): `thm:minimal-kdof-reduction`'s four lemma edges moved to its
  proof, which also takes `lem:rigidContract-isMinimalKDof` and `lem:two-vertex-trichotomy` for part
  (i) and reaches `lem:two-edge-connected-degree` through `lem:reducible-vertex`; both KT Lemma 6.1
  nodes' edges to `thm:minimal-kdof-reduction-all-k` removed, and the second's to
  `lem:genericity-device`, whose argument it follows; that node's proof takes
  `lem:general-position-support-nonzero`, which implies `def:panel-general-position`, and
  `lem:moment-curve-general-position`, two forward edges (`76c3c4d4`–`b384225a`);
  `lem:adjacent-degree-two-pair`'s two proof edges removed, its other statement edges moved to its
  proof, which also takes `lem:deficiency-zero-connected`, the node it cites.
- **F-105** · E · KT Lemma 4.6's nodes, `def:chain-data` to `lem:chain-data-extract`
  (`molecular-induction.tex`): edges the pins do not back, and edges they need. The statement
  edges of `def:chain-data` and `def:cycle-data` to `def:graph-operations` have no Lean basis: the
  records use links only, and the label the first records is used only by
  `lem:chain-data-extract`'s splitting off. The statement edges of `lem:chain-cycle-dichotomy` to
  `lem:two-edge-conn`, `lem:no-rigid-edge-count` and `lem:simple-minimal-noRigid` are its
  proof's, and it misses `lem:deficiency-zero-connected` (`two_le_degree_of_isKDof_zero`, which
  its proof cites since task 2.17), `def:cut-edges-2ec` and `def:edge-multiply`. The statement
  edges of `lem:chain-data-extract` to its four lemmas are its proof's, and its pin reaches
  `lem:simple-minimal-noRigid` only through the dichotomy's, as it assumes that $G$ is simple.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `1d455ed9`); read (the pins'
  statements and bodies).
  *Found:* round 2 task 2.17.
  *Disposition:* done (`eaba775e`): the two definitions' edges to `def:graph-operations` removed
  (`lem:case-III-chain-relabel-rows`, which reached it through `def:chain-data`, takes the edge);
  the statement edges of `lem:chain-cycle-dichotomy` and `lem:chain-data-extract` that their proofs
  name removed; the dichotomy's proof takes `lem:deficiency-zero-connected`, which implies the other
  two; `def:edge-multiply` is implied.
- **F-109** · E · `meet.tex`'s nodes: edges the pins do not back, and edges they need. The
  statement edge of `def:meet-pairing-dual` to `def:meet-top-equiv` has no Lean basis, nor have
  those of `lem:complement-iso-line-one-dim` to `def:join` and `def:extensor` (its pins are about
  an abstract $2$-dimensional space) and of `lem:complement-iso-exterior-map-injective` to
  `def:meet-complement-iso`. The edges of `lem:case-III-claim612-line-in-panel-union` to those two
  lemmas have none either: its first pin proves the proportionality through a $5$-dimensional count
  and a Gram determinant (`F-111`), as its proof has said since task 2.18. Its nine realization pins
  draw 20 missing edges: 14 to round 3's nodes, four to `rigidity-matrix.tex`'s, and one each to
  `def:D-deficiency` and `lem:extensor-independence` (`F-110`).
  `def:meet-complement-iso` and `lem:complement-iso-toDual` miss `def:join` and `def:extensor`,
  which `complementIso` reaches through the wedge product.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter meet`, at `d5db0e0c`); read (the
  pins' statements and bodies).
  *Found:* round 2 task 2.18.
  *Disposition:* done (`eaba775e`): the six edges with no Lean basis removed, four of them at the
  step lemmas and definitions and the claim's two; `def:meet-complement-iso`'s statement takes
  `def:join` and `def:extensor`, its body's reach, through which `lem:complement-iso-toDual` reaches
  them; the claim's proof takes `def:meet-pairing-dual`, whose determinant it cites. The nine
  realization pins left the claim at `56fb8b8c` (`F-110`).
- **F-129** · E · `thm:theorem-55-6` (`algebraic-induction/panel-layer.tex`): its statement and
  proof `\uses` `lem:subgraph-minimality` (a subgraph of a minimal $k$-dof-graph with deficiency
  $k'$ is a minimal $k'$-dof-graph), which the argument does not use. Its step is
  `lem:minimal-kdof-spanning-subgraph`'s (a spanning subgraph that is a minimal
  $\operatorname{def}(\tilde G)$-dof-graph), which the pin reaches through
  `thm:theorem-55-6-genuine`'s pin and which neither `\uses` names; the proof cites it since task
  2.3. `thm:theorem-55-6-multigraph`'s statement and proof have the same edge to
  `lem:subgraph-minimality` (task 2.5's), and its proof also uses
  `lem:minimal-kdof-spanning-subgraph`.
  *Evidence:* measured (`scripts/blueprint-deps.py --label thm:theorem-55-6` and `--label
  lem:minimal-kdof-spanning-subgraph`, at `5c65ea52`); read (the pins' bodies).
  *Found:* round 3 task 2.3.
  *Disposition:* left (`6af43988`): `thm:theorem-55-6`'s edge went at `1d35d435`, which reversed the
  derivation (the proof of `thm:theorem-55-6-genuine` uses `lem:minimal-kdof-spanning-subgraph`);
  `thm:theorem-55-6-multigraph`'s stays, as its pins reach `lem:subgraph-minimality` through
  `thm:theorem-55`'s, a use the edge policy keeps (`9eb2c776`'s reading), and the edge to
  `thm:theorem-55` implies it; its proof already cites `lem:minimal-kdof-spanning-subgraph`.
- **F-146** · E · `case-ii.tex`'s four nodes (`algebraic-induction/case-ii.tex`): `F-003`'s 15
  missing edges, and the edges the pins do not back. `lem:case-II-realization`'s statement edges to
  `lem:reduction-step-pos` and `lem:rank-polynomial-of-le-finrank` are its proof's; it misses
  `def:cut-edges-2ec` and `def:genuine-hinge-realization` (statement) and, in its proof,
  `lem:simple-minimal-noRigid`, `lem:reducible-vertex` (the vertex of degree two, which the proof
  cites since task 2.9, carry-in 3), `lem:rigidityRows-pinned-placement-rank-add`,
  `lem:case-II-placement-new-rows`, `lem:relative-deficiency-rank-bound`,
  `lem:general-position-support-nonzero`, `def:panel-general-position`,
  `lem:span-rigidityRows-eq-of-motions-eq` and `lem:case-III-transport-collapse` (the row
  identity, `hingeRow_sub_hingeRow_eq`); its proof's edge to `lem:genericity-device` has no Lean
  basis (`F-118`). `lem:case-II`'s edges to `def:rank-hypothesis`, `lem:reduction-step-pos`,
  `lem:splitoff-edge-substitution` and `lem:exists-independent-panel-extensor` have no Lean basis,
  and it misses `def:framework-with-graph`; `lem:case-II-rank-lift`'s edge to
  `def:rank-hypothesis` has none; `lem:splitoff-edge-substitution` misses `def:graph-operations`.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter case-ii`, at `5e9e329c`).
  *Found:* round 3 task 2.9.
  *Disposition:* done (`1096d2d9`): the 15 missing edges, 11 added and 4 implied by them (two
  forward, `76c3c4d4`–`b384225a`); `lem:case-II-realization`'s statement edges to
  `lem:reduction-step-pos` and `lem:rank-polynomial-of-le-finrank` removed, as its proof names both,
  and its proof's edge to `lem:genericity-device`, which the proof names only as the general form of
  the polynomial lemma's argument; `lem:case-II`'s edges to `def:rank-hypothesis`,
  `lem:reduction-step-pos` and `lem:exists-independent-panel-extensor` (cited only in the note after
  it) removed, and its statement edge to `lem:splitoff-edge-substitution`, while its proof, which
  cites two steps, keeps one; `lem:case-II-rank-lift`'s edge to `def:rank-hypothesis` removed (its
  $k'$ is any integer, and no realization at a target rank enters).
- **F-151** · E · `genericity-and-count.tex`'s eleven nodes
  (`algebraic-induction/genericity-and-count.tex`): one missing edge, from the proof of
  `lem:genericity-device` to `lem:trivial-motions-rank-bound` (`finrank_screwAssignment`), and 18
  edges the pins do not back, two of them only transitively. They are `lem:genericity-device`'s to
  `def:panel-hinge-framework`; `lem:relative-screw-split`'s to `def:rank-hypothesis`;
  `lem:relative-device-count`'s to `lem:relative-screw-split` and, transitively,
  `lem:genericity-device`; `lem:realization-of-independent-rows`'s to
  `lem:rows-polynomial-in-normals`, transitively; `lem:rank-polynomial-of-le-finrank`'s to
  `lem:rows-polynomial-in-normals`; `lem:case-II-realization-placement`'s to `lem:case-II`,
  `lem:exists-independent-panel-extensor` and `lem:genericity-device`;
  `lem:case-II-placement-old-rows`'s to `lem:case-II`, `lem:case-II-placement-old-rows-extract` and
  `lem:rows-polynomial-in-normals`; and those of `lem:case-II-placement-new-rows`,
  `lem:case-II-placement-old-rows-extract` and `lem:case-II-placement-block-independent` to
  `def:panel-hinge-framework`, `def:rank-hypothesis` and `lem:rank-delete-vertex`. The proofs as
  task 2.10 wrote them also cite nodes that no `\uses` names: `lem:rows-polynomial-in-normals`
  (`lem:genericity-device`, `lem:case-II-placement-new-rows`), `def:panel-support-extensor`,
  `def:hinge-row-block` (`lem:rank-polynomial-of-le-finrank`), and for the count of
  `lem:case-II-realization-placement` (`F-150`) `lem:with-normal-preserves`,
  `lem:splitoff-edge-substitution` and `lem:rigidityRows-pinned-placement-rank-add`.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter genericity-and-count`, at `120eca58`).
  *Found:* round 3 task 2.10.
  *Disposition:* done (`1096d2d9`): the missing edge to `lem:trivial-motions-rank-bound` went when
  `a7b8ea35` unpinned `finrank_screwAssignment`; the parent's four missing added. Removed: the edges
  to `def:rank-hypothesis`, the unbacked ones to `lem:rank-delete-vertex` (`F-062`),
  `lem:relative-device-count`'s to `lem:relative-screw-split`, `lem:case-II-placement-old-rows`'s to
  `lem:case-II` and the extraction, and `lem:case-II-realization-placement`'s three. Kept: the edges
  to `def:panel-hinge-framework` (each statement takes a panel-hinge framework),
  `lem:case-II-placement-old-rows`'s to `lem:rows-polynomial-in-normals` (its statement indexes the
  rows as there) and the transitive one; the rest are backed now. Of the citations,
  `lem:genericity-device`'s and `lem:case-II-placement-new-rows`'s proofs now `\uses`
  `lem:rows-polynomial-in-normals`, and `lem:case-II-realization-placement`'s
  `lem:with-normal-preserves` and `lem:splitoff-edge-substitution`; `def:panel-support-extensor` and
  `def:hinge-row-block` are ancestors; `lem:rigidityRows-pinned-placement-rank-add` takes none, as
  the count argues "as in" it (`F-175`).
- **F-155** · E · `case-iii.tex`'s KT Claim 6.11 group (`algebraic-induction/case-iii.tex`, five
  nodes): 12 missing edges, `lem:case-III-claim-6-11-base`'s and `lem:case-III-gap3-minimalKDof`'s to
  `def:edge-multiply`, the latter's to `lem:splitoff-edge-substitution`, and nine of
  `lem:case-III-nested-rank-lower`'s (among them `def:panel-hinge-framework`,
  `lem:general-position-support-nonzero`, `lem:rank-polynomial-of-le-finrank`). Three edges have no
  Lean basis: `lem:case-III-claim-6-11-base`'s to `lem:splitoff-deficiency`, and those of
  `lem:case-III-claim-6-11-redundant-row` and `lem:case-III-claim-6-11` to
  `lem:case-III-gap3-minimalKDof`. The proofs as task 2.11 wrote them also cite nodes that no
  `\uses` names: `lem:splitoff-kdof-criterion` and `lem:balanced-forest-packing` (the base),
  `def:D-deficiency`, `lem:splitoff-edge-substitution` and `lem:matroid-restrict-subgraph` (the
  bound on $k'$), `lem:general-position-support-nonzero` and `lem:rank-polynomial-of-le-finrank`
  (KT eq. (6.22)), and `lem:splitoff-edge-substitution` and `def:hinge-row-block` (Claim 6.11).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the five nodes, at `fe05a812`).
  *Found:* round 3 task 2.11.
  *Disposition:* done (`e1b16939`): the base's edge to `lem:splitoff-deficiency` and the edges of
  `lem:case-III-claim-6-11-redundant-row` and `lem:case-III-claim-6-11` to
  `lem:case-III-gap3-minimalKDof` removed (the statements assume what those lemmas give, and no
  proof cites them); the missing edges added or implied; `lem:case-III-claim-6-11`'s proof `\uses`
  `lem:splitoff-edge-substitution`, which implies that citation in
  `lem:case-III-redundant-decomposition`. `lem:splitoff-kdof-criterion`, which the base's proof
  names as also giving the claim, takes none (a comparison); the other citations are ancestors.
- **F-160** · E · `case-iii.tex`'s row operations of KT eqs. (6.24)–(6.29)
  (`algebraic-induction/case-iii.tex`, nine nodes): 11 missing edges, those of
  `lem:case-III-vanish-off-column` and `lem:case-III-columnop` to `def:rigidity-matrix`, four of
  `lem:case-III-seam` (`def:hinge-constraint`, `def:panel-hinge-framework`,
  `def:panel-support-extensor`, `def:rigidity-matrix`), and five of
  `lem:case-III-transport-collapse` (those four and `def:meet-complement-iso`). 14 edges have no
  Lean basis: `lem:case-III-columnop`'s to `lem:case-III-vanish-off-column`,
  `lem:case-III-conditional-block`'s to both of these, `lem:case-III-transport-collapse`'s to
  `lem:case-III-seam`, `lem:case-III-candidate-row-construction`'s to
  `lem:case-III-redundant-decomposition`, and nine of `lem:case-III-candidate-row`'s (all but
  `lem:case-III-columnop`), among them the forward edge to `lem:case-III-claim612` (`F-119`), which
  the statement no longer needs, and the edge to `lem:case-II-realization-placement` (`F-150`). The
  proofs as task 2.12 wrote them also cite nodes that no `\uses` names:
  `def:panel-hinge-framework` and `lem:rows-polynomial-in-normals` (the seam),
  `def:hinge-row-block` and `lem:splitoff-edge-substitution` (KT eq. (6.24)),
  `def:panel-support-extensor` and `lem:rows-polynomial-in-normals` (the one-row identity),
  `def:hinge-row-block` and `lem:case-III-columnop` (the new row), and `def:hinge-row-block` and
  `lem:rigidityRows-pinned-placement-rank-add` (the rank of KT eq. (6.29)).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the nine nodes, at `ba79d703`).
  *Found:* round 3 task 2.12.
  *Disposition:* done (`e1b16939`): the missing edges added or implied, and `lem:case-III-seam` and
  `lem:case-III-transport-collapse` take `lem:rows-polynomial-in-normals` on the statement, whose
  rows they index. Of the 14 edges with no Lean basis, `lem:case-III-columnop`'s moved to its proof,
  which cites the lemma; `lem:case-III-candidate-row-construction`'s kept (its statement takes that
  lemma's forms); those of `lem:case-III-conditional-block` and `lem:case-III-transport-collapse`
  removed; of `lem:case-III-candidate-row`'s nine, the two its statement names and the proof's to
  `lem:case-III-conditional-block` kept and six removed, the forward edge to `lem:case-III-claim612`
  (`F-119`) among them. Its proof now `\uses` `lem:rigidityRows-pinned-placement-rank-add`; the
  other citations are ancestors.
- **F-162** · E · `case-iii.tex`'s case $d = 3$: the span and the point choice
  (`algebraic-induction/case-iii.tex`, ten nodes): no missing edge, and 13 edges with no Lean
  basis: `lem:case-III-claim612-orthseq-vanish`'s to `lem:case-III-claim612-extensor-span`,
  `lem:case-III-claim612-panel-point-exists`'s to `def:panel-hinge-framework`, those of
  `lem:case-III-claim612-detpoly` and `lem:case-III-claim612-points-affineIndep-real-normals` to
  `lem:affine-indep-iff`, all six of `lem:case-III-claim612-points-affineIndep`'s (three of them for
  an alternative argument that the open's proof named and task 2.13's does not),
  `lem:case-III-claim612-block-iff-perp`'s to `lem:case-II-placement-new-rows`, and both of
  `lem:case-III-claim612-r-nonzero`'s. The new proofs also cite `def:homogeneous-coords`
  (`lem:case-III-claim612-detpoly`, already an ancestor) and `def:affine-subspace-extensor`
  (`lem:case-III-claim612-block-iff-perp`) without an edge.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the ten nodes, at `4502f035`).
  *Found:* round 3 task 2.13.
  *Disposition:* done (`e1b16939`): 11 of the 13 edges removed, as neither the statements, the
  proofs nor the pins use them; `lem:case-III-claim612-points-affineIndep`'s edge to the witness
  moved to its proof, which cites it; `lem:case-III-claim612-r-nonzero`'s to
  `lem:case-III-redundant-decomposition` kept (its statement takes that lemma's forms).
  `lem:case-III-claim612-detpoly`'s statement, which writes $\bar p_i(t)$, now `\uses`
  `def:homogeneous-coords`, which its proof cites; `def:affine-subspace-extensor` stays an ancestor
  of `lem:case-III-claim612-block-iff-perp`.
- **F-166** · E · `case-iii.tex`'s case $d = 3$: the three frameworks and KT Claim 6.12
  (`algebraic-induction/case-iii.tex`, eight nodes): 23 missing edges and 16 with no Lean basis.
  Missing: `lem:case-III-candidate-row` at both `lem:case-III-claim612-p2-placement` and
  `lem:case-III-claim612-p3-placement`; nine at `lem:splitOff-ofNormals-relabel` (six definitions,
  `lem:case-II-placement-old-rows-extract`, `lem:isInfRigidOn-of-relative-count` and
  `lem:trivial-motions-rank-bound`); five definitions at `lem:splitOff-rigidityRows-relabel`; and
  seven at `lem:case-III-candidate-dispatch-d3` (`def:panel-general-position`,
  `lem:case-III-claim612-line-in-panel-union`, `lem:general-position-support-nonzero`,
  `lem:isInfRigidOn-of-relative-count`, `lem:rank-polynomial-of-le-finrank`,
  `lem:relative-deficiency-rank-bound`, `lem:span-rigidityRows-eq-of-motions-eq`). No Lean basis:
  `lem:case-II-realization-placement` at the two placements and the dispatch,
  `lem:case-III-claim612-eq644` at the third framework, `lem:splitOff-ofNormals-relabel` at the rows
  lemma, both edges of `lem:case-III-claim612-eq644` and of `lem:case-III-claim612`, and seven more
  of the dispatch's (two of them reached only through other nodes). Task 2.14's proofs also cite
  without an edge: `lem:case-III-candidate-row` (the second framework), `def:panel-general-position`
  and `rem:rank-hypothesis-relative` (the realization of $G_a^{vc}$), `def:graph-operations` (KT eq.
  (6.44)), `lem:case-III-conditional-block` and the two relabel lemmas (the third framework),
  `def:panel-support-extensor`, `lem:case-III-claim612-block-iff-perp` and
  `lem:case-III-claim612-line-in-panel-union` (KT Claim 6.12), and nine nodes in the dispatch's
  proof, among them `lem:rank-rotation-semicont` and `lem:rows-polynomial-in-normals`.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the eight nodes, at `9190873a`).
  *Found:* round 3 task 2.14.
  *Disposition:* done (`e1b16939`): the missing edges added or implied. Of the edges with no Lean
  basis, those to `lem:case-II-realization-placement` (the two placements and the dispatch),
  `lem:case-III-claim612`'s to the real-normals lemma (its statement takes any independent vectors)
  and the dispatch's to `lem:genericity-device` removed, as no text uses them; three moved to the
  proofs that cite them (the third framework's to `lem:case-III-claim612-eq644`, that lemma's to
  `lem:case-III-acolumn-zero`, Claim 6.12's to `lem:case-III-claim612-r-nonzero`); the rest kept, as
  a statement takes the target's objects or assumes its conclusion, or the dispatch's proof cites
  the frameworks. Of the citations, the third framework's proof `\uses`
  `lem:splitOff-rigidityRows-relabel`, which implies the other relabel lemma, and
  `lem:case-III-candidate-row`, which implies the block lemma; Claim 6.12's paragraph after its
  proof, which derives KT's block form, takes none, nor the dispatch's "as in the proof of".
- **F-170** · E · `case-iii.tex`'s general case: the triangle, KT Lemma 6.13 and the chain
  (`algebraic-induction/case-iii.tex`, five nodes): 24 missing edges and 13 unbacked. Missing:
  `def:edge-multiply` and `lem:rigid-full-rank` at `lem:triangle-third-edge`; `def:graph-operations`
  and `lem:case-III-claim612-line-in-panel-union` at `lem:triangle-realization`; nine at
  `lem:case-III-chain-discriminator` (`def:genuine-hinge-realization`, `def:panel-general-position`,
  `lem:case-II-placement-old-rows-extract`, `lem:case-III-claim612-block-iff-perp`,
  `lem:general-position-support-nonzero`, `lem:isInfRigidOn-of-relative-count`,
  `lem:rank-polynomial-of-le-finrank`, `lem:relative-deficiency-rank-bound`,
  `lem:span-rigidityRows-eq-of-motions-eq`); eight at `lem:case-III-chain-dispatch` (two definitions,
  `lem:case-III-claim612-block-iff-perp`, `lem:case-III-claim612-eq644`, `lem:case-III-columnop`,
  `lem:case-III-transport-collapse`, `lem:general-position-support-nonzero`,
  `lem:isInfRigidOn-of-relative-count`); and `def:cut-edges-2ec`, `def:genuine-hinge-realization`
  and `lem:deficiency-zero-connected` at `lem:case-III`. No Lean basis (6): `lem:genericity-device`
  at the triangle realization and the dispatch, `lem:case-III-claim612-line-in-panel-union` at the
  discriminator, and `lem:case-II-realization-placement` and the two relabel lemmas at the dispatch;
  seven more are reached only through other nodes. Task 2.15's proofs also cite without an edge:
  `lem:rigid-full-rank` (the triangle); `lem:case-III-candidate-row-construction`,
  `lem:case-III-redundant-decomposition`, `lem:case-III-claim612-points-affineIndep-real-normals`,
  `lem:rank-polynomial-of-le-finrank` and `lem:relative-deficiency-rank-bound` (the discriminator);
  `lem:case-III-candidate-row`, `lem:case-III-claim612-p2-placement`, `lem:case-III-claim612-eq644`,
  `lem:rank-rotation-semicont`, `lem:case-II-realization` and `lem:case-III-candidate-dispatch-d3`
  (the dispatch); and `lem:two-edge-conn` (`lem:case-III`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the five nodes, at `c3586784`).
  *Found:* round 3 task 2.15.
  *Disposition:* done (`e1b16939`): the missing edges added or implied (`lem:case-III`'s through the
  chain dispatch); the edges to `lem:genericity-device` (the triangle realization, the dispatch), to
  `lem:case-II-realization-placement` and to the two relabel lemmas (the dispatch, `F-171`) removed,
  as no proof cites them. Of the citations, the dispatch's proof `\uses`
  `lem:case-III-claim612-p2-placement`, which implies `lem:case-III-candidate-row`; those "as in the
  proof of" another node, of KT Lemma 5.2 for how Katoh and Tanigawa rotate, and of the $d = 3$
  lemma or `lem:case-III-claim612-line-in-panel-union` for a comparison take none.
- **F-175** · E · `bar-joint-3d.tex`'s nine nodes (`bar-joint-3d.tex`): six missing edges and one
  unbacked. Missing: `lem:exists-generic-placement`'s to `def:rigidityRow`,
  `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow` and `lem:rigidityMap-apply`;
  `lem:genericRank-eq-finrank-span`'s to `lem:k-frame-incidence-finrank-rk`
  (`Matroid.Rep.finrank_span_image_eq_rk`); `lem:rigidityMap-rank-at-generic`'s to
  `lem:rigidityMap-apply` and `lem:span-range-rigidityRow`. Unbacked: `lem:genericRank-eq-finrank-span`'s
  to `lem:linearRigidityMatroid-indep-iff`, reached only through another node. Task 2.1's proofs
  cite every missing target but `def:rigidityRow`, and `def:linearRigidityMatroid` and
  `def:linearRigidityRow` (the row-space form), without an edge. The existence proof also cites
  `lem:exists-uniform-rowIndependent-placement` and `thm:edgeSet-rowIndependent-iff-isSparse` as
  the planar argument it follows; its pin reaches neither, and they want no edge. The pin of
  `lem:genericRigidityMatroid-two-eq-rigidityMatroid` is dead (`F-012`).
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter bar-joint-3d`, at `69bc7afb`).
  *Found:* round 4 task 2.1.
  *Disposition:* done (`e9d59672`): the six missing edges added or implied (`def:rigidityRow`
  through `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow`, and
  `lem:rigidityMap-rank-at-generic`'s to `lem:rigidityMap-apply` through `def:genericRank`, now that
  the existence proof `\uses` it); the transitive unbacked edge kept. The planar argument that the
  existence proof follows takes no edge.
- **F-181** · E · `molecule-modelling.tex`'s first eight nodes, task 2.2's (`molecule-modelling.tex`):
  eight missing edges and three unbacked. Missing: the edges of `def:hinge-concurrent` (proof),
  `def:screw-velocity`, `lem:screw-velocity-line` and `lem:screw-determination` to
  `def:rigidity-matrix`, through `ScrewSpace`, which is pinned there (the screw space is introduced
  at `def:hinge-constraint`); `thm:projective-invariance`'s to `def:dof-generic`,
  `lem:trivial-motions-rank-bound` (`IsTrivialMotion`) and `lem:rank-rotation-semicont`
  (`infinitesimalMotions_mono_of_span_le`, in the rescaling); `lem:panel-hinge-dual-molecular`'s
  to `def:dof-generic`. Unbacked: `thm:projective-invariance`'s to `def:rank-hypothesis`,
  `def:screw-velocity`'s to `def:hinge-constraint` and `lem:screw-velocity-line`'s to
  `def:hinge-concurrent`. Task 2.2's proof of `thm:projective-invariance` cites `def:dof-generic`
  and `def:rigidity-matrix` without an edge. Three pins of each of those two nodes are dead
  (`F-012`).
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter molecule-modelling`, at `67d44583`).
  *Found:* round 4 task 2.2.
  *Disposition:* done (`e9d59672`): `thm:projective-invariance`'s statement `\uses`
  `def:trivial-motions-rigid` (which implies `lem:panel-hinge-dual-molecular`'s missing edge) and
  its proof `lem:rank-rotation-semicont` (the rescaling); the others were not missing at the task's
  parent. The three unbacked edges removed: the theorem's to `def:rank-hypothesis` (only the note
  names it, for $\dim Z = D + k'$, not a realization at a target rank); `def:screw-velocity`'s to
  `def:hinge-constraint`, replaced by `def:screw-space`, where its screws lie; and
  `lem:screw-velocity-line`'s to `def:hinge-concurrent`, replaced by `def:extensor` and
  `def:homogeneous-coords`, for its $\bar a \vee \bar b$.
- **F-185** · E · `molecule-modelling.tex`'s last five nodes, task 2.3's (`molecule-modelling.tex`):
  nine missing edges and five unbacked. Missing: `thm:panel-hinge-iff-molecular`'s (proof) to
  `lem:rank-rotation-semicont` (`infinitesimalMotions_mono_of_span_le`, the rescaling);
  `lem:theorem-56-general-position`'s to `thm:theorem-55-6-genuine` (carry-in 9);
  `lem:exists-generic-general-position`'s to `def:rigidityRow`,
  `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow`, `lem:exists-generic-placement` and
  `lem:rigidityMap-apply`; `thm:molecular-iff-square-bar-joint`'s to `def:rigidity-matrix`,
  `def:rigidityMap` and `lem:rigidityMap-apply`. Unbacked: `thm:panel-hinge-iff-molecular`'s to
  `thm:projective-invariance` (through another node); `lem:theorem-56-general-position`'s to
  `def:general-position-placement` (its pin states the condition for the normals),
  `lem:genericity-device` and `thm:theorem-55-6-d3`; `def:general-position-placement`'s to
  `def:framework`. Task 2.3's prose also cites without an edge: in the proof of
  `lem:theorem-56-general-position`, `thm:theorem-55-6-genuine`,
  `lem:rank-polynomial-of-le-finrank`, `lem:general-position-support-nonzero` and
  `lem:affine-indep-iff`, which its pin reaches; in that of `thm:panel-hinge-iff-molecular`,
  `lem:trivial-motions-rank-bound`; in that of `thm:molecular-iff-square-bar-joint`,
  `def:screw-velocity`, `lem:rigidityMap-apply` and `lem:framework-finrank`, and for its unpinned
  realizability claim (`F-183`) `thm:panel-hinge-iff-molecular`, `lem:trivial-motions-rank-bound`,
  `lem:relative-deficiency-rank-bound`, `def:isInfinitesimallyRigid`, `def:generic-placement` and
  `lem:exists-generic-general-position`. No pin of these nodes is dead.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter molecule-modelling`, at `db71b408`).
  *Found:* round 4 task 2.3.
  *Disposition:* done (`e9d59672`): `lem:exists-generic-general-position`'s proof `\uses`
  `lem:exists-generic-placement`, implying the other three; the dictionary's proof `\uses` the four
  nodes it cites without an ancestor (`lem:framework-finrank`, and three in its proof of the
  realizations, `F-183`), which imply its three missing edges and the other citations;
  `thm:panel-hinge-iff-molecular`'s is implied through `thm:projective-invariance`. The unbacked
  edges kept: the transitive one; the general-position lemma's statement states the condition, and
  its proof cites KT Theorem 5.6 at $d = 3$ and the device for steps;
  `def:general-position-placement` takes a placement (`def:framework`).
- **F-189** · E · `molecule-application.tex`'s five nodes, task 2.4's (`molecule-application.tex`):
  six missing edges and two unbacked. Missing: `lem:square-rank-le-genericRank`'s to
  `lem:k-frame-incidence-finrank-rk` (`Matroid.Rep.finrank_span_image_eq_rk`);
  `lem:molecule-rank-lower-bound`'s to `lem:framework-finrank` (rank–nullity), and to
  `lem:rigidityMap-apply` and `lem:span-range-rigidityRow` (through the unpinned rank form of
  `F-188`); `lem:molecule-rank-upper-bound`'s to `lem:framework-finrank` and
  `lem:rigidityMap-rank-at-generic`. Unbacked: `lem:molecule-graph-carrier`'s to
  `def:hinge-concurrent` (no Lean basis); `lem:molecule-rank-upper-bound`'s to
  `lem:genericRank-eq-finrank-span` (through `lem:rigidityMap-rank-at-generic`). Task 2.4's prose
  cites without an edge: in the proof of `lem:square-rank-le-genericRank`,
  `def:linearRigidityMatroid`, `lem:k-frame-incidence-finrank-rk` and
  `lem:linearRigidityMatroid-indep-iff`, which its pin reaches, and
  `lem:rigidityMap-rank-at-generic` for the rank form; in that of the upper bound,
  `lem:rigidityMap-rank-at-generic`, which its pin uses in place of
  `lem:genericRank-eq-finrank-span`. No pin of these nodes is dead.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter molecule-application`, at `302cc117`).
  *Found:* round 4 task 2.4.
  *Disposition:* done (`e9d59672`): `lem:square-rank-le-genericRank`'s proof `\uses`
  `lem:k-frame-incidence-finrank-rk`, the lower bound's `lem:span-range-rigidityRow` and the upper
  bound's `lem:rigidityMap-rank-at-generic`, which it cites; `lem:framework-finrank` and
  `lem:rigidityMap-apply` are implied through the dictionary. `lem:molecule-graph-carrier`'s edge to
  `def:hinge-concurrent` removed (the lemma builds a multigraph); the transitive edge kept. The rank
  form "as in the proof of" `lem:rigidityMap-rank-at-generic` takes none.
- **F-193** · E · `jacobs.tex`'s first ten nodes, task 2.5's (`jacobs.tex`): two missing edges and
  three unbacked. Missing: `lem:tight-partition-parts`'s to `lem:exists-tight-partition`
  (`IsTightPartition`, in its statement) and to `lem:cut-edge-decomposition`
  (`partitionDef_congr`, in its proof). Unbacked: the proof of `lem:isLaman3-mono` to
  `lem:edgesIn-mono` (no Lean basis; that lemma is monotonicity in the vertex set, while the proof
  needs monotonicity in the graph, and task 2.5's prose no longer cites it);
  `lem:tight-partition-cross-pair-mult`'s and `lem:tight-partition-cross-pair-nbr`'s to
  `def:D-deficiency` (through another node). Task 2.5's prose cites no node without an edge. No
  pin of these nodes is dead.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter jacobs`, at `9c97fecc`); read (the
  body of `IsLaman3.mono_left`).
  *Found:* round 4 task 2.5.
  *Disposition:* done (`e9d59672`): `lem:tight-partition-parts`'s statement `\uses`
  `def:tight-partition` (`ae31af3e`'s node for `IsTightPartition`; its pin no longer reaches
  `lem:cut-edge-decomposition`); `lem:isLaman3-mono`'s edge to `lem:edgesIn-mono` removed; the two
  transitive edges kept.
- **F-196** · E · `jacobs.tex`'s counting bound, task 2.6's eleven nodes (`jacobs.tex`): 18
  missing edges and 14 unbacked. Missing: ten to `lem:molecule-graph-carrier` (every node but
  `def:g-cut-edges`, through `IsSquareTightPartition`, a tight partition of `shadowGraph`); five to
  `lem:normal-cross-count-rooted` (the statements of the producer, fiber, partition and count
  lemmas, and the theorem's proof, use `squareNormalCrossEdgesRootedAt`);
  `lem:normal-cross-count-local`'s statement to `lem:exists-tight-partition`; the producer's proof to
  `lem:singleton-part-neighborhood` (`isClique_neighborSet_square`); the theorem's proof to
  `lem:edgesIn-corners` (`edgesIn_singleton`). Unbacked, with no Lean basis: the converse's proof to
  `lem:singleton-part-neighborhood`; `lem:normal-cross-count-rooted`'s proof to
  `lem:square-cross-classification` (`F-195`); `def:g-cut-edges` to `def:D-deficiency`; the
  theorem's proof to `lem:singleton-part-converse`, whose pin is dead (`F-012`, `F-197`). Ten more
  are unbacked through another node. In task 2.6's prose the converse's proof no longer cites
  `lem:singleton-part-neighborhood`, nor the theorem's `lem:singleton-part-converse`, and the
  theorem's proof cites without an edge `lem:tight-partition-cross-pair-nbr` (implied) and
  `lem:normal-cross-count-rooted` (missing).
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter jacobs`, at `bc6573b9`, and the same
  report on task 2.6's tree).
  *Found:* round 4 task 2.6.
  *Disposition:* done (`e9d59672`): the statements of `lem:square-cross-classification`,
  `lem:singleton-part-neighborhood` and `lem:normal-cross-count-local` `\uses`
  `lem:molecule-graph-carrier`; the producer's statement `def:rooted-cross-edges` (`ae31af3e`'s
  node, which took the edges to `lem:normal-cross-count-rooted`) and its proof
  `lem:singleton-part-neighborhood`; the theorem's proof `lem:edgesIn-corners` and
  `lem:normal-cross-count-rooted`; the rest implied. The converse's edge to
  `lem:singleton-part-neighborhood` and the theorem's to `lem:singleton-part-converse` removed (no
  text cites them); `lem:normal-cross-count-rooted`'s to `lem:square-cross-classification` kept, as
  its proof cites it for the part's size (`F-195`), and `def:g-cut-edges`'s to `def:D-deficiency`,
  as it takes a part of a partition and writes $d_G$ as there.
- **F-199** · E · `jacobs.tex`'s easy direction and $0$-extensions, task 2.7's ten nodes
  (`jacobs.tex`): 12 missing edges and none unbacked. Missing: the proof of
  `lem:isLaman3-of-rowIndependent` to `def:rigidityRow`,
  `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow`, `lem:rigidityMap-apply` and
  `lem:span-range-rigidityRow`; that of `lem:zero-extension-rowIndependent` to the first three of
  these (through the unpinned `zero_extension_edgeSetRowIndependent_extend`); those of
  `cor:zero-extension-degree-le-three` and `lem:genericMatroid-induce-transport` to the second and
  third; that of `cor:zero-extension-clique-rank` to `lem:clique-edgesIn-count`
  (`IsClique.ncard_edgesIn`, through the unpinned `dep_k5`). The pin `genericRank_eq_rk_image` is
  dead (`F-012`): `thm:jacobs` uses only the independence half. In task 2.7's prose, cited without
  an edge: `lem:rigidityMap-apply` (missing) and, for the argument, `lem:typeI-rowIndependent-extend`
  (no Lean basis) in the lift's proof; `lem:isSparse-of-rowIndependent-two`, for the argument, in
  the proofs of `lem:isLaman3-of-rowIndependent` and `lem:genericMatroid-induce-transport`;
  `lem:clique-edgesIn-count` (missing) in the clique corollary's proof.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the ten nodes, at `723c460d`); read
  (the bodies of `zero_extension_edgeSetRowIndependent_lift` and `dep_k5`).
  *Found:* round 4 task 2.7.
  *Disposition:* done (`e9d59672`): the proofs of `lem:isLaman3-of-rowIndependent`,
  `lem:zero-extension-rowIndependent` and `cor:zero-extension-clique-rank` `\uses` the missing
  targets, `def:rigidityRow` through `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow`; the
  other two nodes' edges are implied. The arguments followed ("as in the proof of") take none.
- **F-201** · E · `jacobs.tex`'s last five nodes, task 2.8's (`jacobs.tex`): one missing edge and
  none unbacked. Missing: the proof of `thm:degree-one-rank-tree` to `lem:square-induce-support`
  (`square_support_subset`, in the base case). Implied through another node: those of
  `thm:jacobs-min-degree-two` to `def:D-deficiency`, `def:genericRank` and
  `lem:molecule-graph-carrier`, of `thm:jacobs` to `def:edgesIn`, and of
  `thm:degree-one-rank-tree` to `def:genericRigidityMatroid`. The pin `degree_one_rank_tree` is
  dead (`F-012`). Task 2.8's proofs cite no node without an edge. The lead of
  `sec:jacobs-degree-one` cites `lem:genericMatroid-induce-transport` for reading the rank of
  $G - v$ on either vertex set; the formal proofs keep $V$ fixed and do not use it
  (`fmlnote:degree-one-fixed-carrier`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the five nodes, at `0e8d7546`).
  *Found:* round 4 task 2.8.
  *Disposition:* done (`e9d59672`): `thm:degree-one-rank-tree`'s proof `\uses`
  `lem:square-induce-support`, and `thm:degree-one-rank`'s `lem:two-core-degree-one`, which it
  cites; "As in the proof of `thm:degree-one-rank-tree`" takes none.
- **F-208** · E · `generic-lift.tex`'s first eleven nodes, task 2.9's (`generic-lift.tex`): eight
  missing edges and six unbacked. Missing: the proof of `lem:generic-placement-abundance` to
  `def:rigidityRow`, `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow` and
  `lem:rigidityMap-apply`; the proofs of `cor:molecule-generic-rigid` and
  `cor:molecule-generic-square-packing` to `lem:framework-finrank`; the latter's to
  `lem:deficiency-zero-connected` (`two_le_degree_of_isKDof_zero`) and its statement to
  `def:edge-multiply`; the statement of `lem:panel-witness-transplant` to `def:generic-normals`.
  Unbacked, with no Lean basis: `def:generic-normals` to `def:panel-hinge-framework`; the proofs of
  `lem:generic-normals-abundance` to `lem:rows-polynomial-in-normals` (`F-137`),
  `lem:generic-normals-nondegenerate` to `lem:moment-curve-general-position` (the pin uses the
  unpinned pair lemma `momentCurve_pair_linearIndependent`) and `lem:panel-witness-transplant` to
  `lem:case-II-placement-old-rows-extract` (`F-209`). Through another node: the square corollary's
  to `def:cut-edges-2ec`, and `thm:panel-generic-rank`'s to `def:rank-hypothesis`. Nine pins at
  eight nodes are dead (`F-012`): every pin but those of the three molecule nodes. The rewritten
  proofs cite without an edge `lem:rigidityMap-apply` and
  `lem:edgeSetRowIndependent-iff-linearIndepOn-rigidityRow` (the abundance of placements),
  `lem:framework-finrank` (both molecule corollaries), `lem:union-indep-iff`,
  `lem:deficiency-zero-iff-tree-packing`, `lem:molecule-graph-carrier`, `def:k-dof` and
  `lem:deficiency-zero-connected` (the square corollary), `def:join`, `def:plucker-coords`,
  `def:meet-complement-iso` and `lem:generic-placement-abundance` (the abundance of normals; the
  minor formula is the unpinned `panelSupportPoly_eval`),
  `lem:rows-polynomial-in-normals` (the witness lemma) and `def:hinge-row-block` (the theorem).
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter generic-lift`, at `7c268bce`); read
  (the bodies of the twelve pins).
  *Found:* round 4 task 2.9.
  *Disposition:* done (`e9d59672`): the abundance proof `\uses` the two lemmas it cites,
  `lem:panel-witness-transplant`'s statement `def:generic-normals`, and the molecule corollaries'
  `lem:framework-finrank` is implied through the dictionary; `lem:generic-normals-abundance`'s proof
  `\uses` `def:plucker-coords`, cited for the minors. The unbacked edges kept: the transitive one;
  `def:generic-normals` states a panel-hinge framework, and the nondegeneracy proof cites the moment
  curve for its two normals. "The argument of" another node takes none.

- **F-213** · E · `generic-lift.tex`'s nine body-and-bar nodes, task 2.10's (`generic-lift.tex`):
  one missing edge, three unbacked, three dead pins. Missing: the proof of `lem:endpoint-witness`
  to `lem:k-frame-specialize-li` (`specRow_linearIndependent`, through
  `stdFramework_rigidityRow_linearIndependent_restrict`). Unbacked, with no Lean basis: the
  witness's proof to `prop:tay-witness-exists`, and the proofs of
  `thm:bodybar-generic-independence` and `cor:bodybar-generic-tay` to
  `lem:tay-isSparse-of-independent` (the theorem's pin uses the restricted form
  `isSparse_of_isIndependent_restrict`, the corollary's pins the theorem). Through another node:
  edges to `def:body-bar-framework` and `def:rigidity-map-body-bar` from five nodes, the witness's
  to `def:two-extensor`, and the theorem's to `lem:k-frame-pi-finrank` and
  `lem:k-frame-incidence-finrank-rk`. Dead pins (`F-012`): `twoExtensorPoly`,
  `exists_isGenericEndpoints_abundance` and `exists_isGenericEndpoints`. The rewritten proofs
  cite without an edge `def:rigidity-map-body-bar` and `lem:generic-placement-abundance` (the
  abundance lemma), `lem:k-frame-specialize-forest` and `lem:k-frame-specialize-li` (the
  witness), and `lem:k-frame-pi-finrank` and `lem:k-frame-incidence-finrank-rk` (the theorem).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the nine nodes, at `c8f1f0f1`);
  read (the bodies of the twelve pins).
  *Found:* round 4 task 2.10.
  *Disposition:* done (`e9d59672`): the three unbacked edges removed (the witness takes its vectors
  "as in" `prop:tay-witness-exists`, the theorem follows "the argument of"
  `lem:tay-isSparse-of-independent`, and the corollary does not cite it); the witness's proof
  `\uses` `lem:k-frame-specialize-li`, and the theorem's `lem:k-frame-pi-finrank` and
  `lem:k-frame-incidence-finrank-rk`, which the removals left missing and the theorem cites.

- **F-218** · E · `generic-lift.tex`'s five hinge-point nodes, task 2.11's (`generic-lift.tex`):
  one missing edge, three unbacked, no dead pin. Missing: the statement of
  `lem:hinge-rows-polynomial-in-points` to `def:rigidity-matrix` (the screw space, through
  `hingeExtensorPoly_eval`). Unbacked: that statement's edge to `def:plucker-coords`, with no Lean
  basis (`F-059`); the edges of the abundance lemma's statement and the nondegeneracy proof to
  `lem:affine-indep-iff`, transitive (both pins use the criterion
  `affineSubspaceExtensor_ne_zero_iff` of `def:affine-subspace-extensor` and the library's passage
  from linear to affine independence). Through another node: `def:extensor` and
  `def:homogeneous-coords` from the definition, the abundance lemma and the nondegeneracy lemma, and
  `def:rigidity-matrix` from the last two. The rewritten proofs cite without an edge
  `lem:generic-placement-abundance` (the abundance lemma; the minor lemma is `F-209`'s).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the five nodes, at `dc58265b`);
  read (the bodies of the seven pins).
  *Found:* round 4 task 2.11.
  *Disposition:* done (`e9d59672`): the statement of `lem:hinge-rows-polynomial-in-points` `\uses`
  `def:screw-space` (`a7b8ea35`'s node), and its edge to `def:plucker-coords` moved to the proof,
  which cites the minors; the transitive edges to `lem:affine-indep-iff` kept.

- **F-223** · E · `generic-lift.tex`'s seven body-and-hinge nodes, task 2.12's (`generic-lift.tex`):
  four missing edges, three unbacked, no dead pin. Missing: the statement of `lem:screw-map-rows`
  and the proof of `lem:hinge-point-witness` to `thm:projective-invariance` (both pins reach its pin
  `mapExtensor`); the proof of `lem:screw-map-rows` to `lem:case-III-claim612-block-iff-perp` (its
  pin `mem_hingeRowBlock_iff`); the statement of `cor:bodyhinge-generic-tree-packing` to
  `def:edge-multiply`. Unbacked, transitive: the witness's proof to `def:genuine-hinge-realization`
  and to `lem:case-II-placement-old-rows-extract` (the pin uses the unpinned extraction of `F-209`),
  and the tree-packing statement to `def:matroid-MG`. Through another node: 37 edges, among them
  `def:hinge-row-block` from the screw-map lemma, the witness and the rank theorem. The rewritten
  text cites without an edge `def:hinge-row-block` (the screw-map lemma and the rank theorem),
  `lem:rows-polynomial-in-normals` and `lem:panel-witness-transplant` (the witness, for their
  arguments), `lem:extensor-map-rows` (a comparison in the screw-map proof) and
  `thm:projective-invariance` (the lead-in to the screw-map lemma, its case $d = 3$).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the seven nodes, at `ac88bd18`);
  read (the bodies of the seven pins).
  *Found:* round 4 task 2.12.
  *Disposition:* done (`e9d59672`): `lem:screw-map-rows`'s statement `\uses`
  `thm:projective-invariance` (its framework $(G, \Lambda p)$), which implies the witness's, and its
  proof `lem:case-III-claim612-block-iff-perp` (`F-248`); the witness's proof `\uses`
  `def:induced-screw-map`, which it cites; the tree-packing statement's edge is implied through
  `def:matroid-MG`. The transitive edges kept; the comparisons and arguments followed take none.
- **F-255** · E · `lem:genericity-device` (`algebraic-induction/genericity-and-count.tex`): since
  round 2 task 5 its pin is `exists_rankPolynomial_of_le_finrank_linking`, whose body calls the pin
  of `lem:independent-rows-of-rank`, 218 lines later in the file. The proof edge is missing, the
  graph's one missing edge. Adding it makes a new forward `\uses` (that round's gate 4), and
  *Node order* cures it only by a move the task's line does not name: `lem:independent-rows-of-rank`
  and its note from the counting subsection to before the node, with both subsections' leads
  following, or the node after it, which leaves the node's subsection with its lead alone.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:genericity-device`, `--summary` and
  the forward screen, on round 2 task 5's tree).
  *Found:* RECONCILE round 2 task 5.
  *Disposition:* done (`daa53665`): `lem:independent-rows-of-rank` and its note moved into the first
  subsection, before the node, whose proof `\uses` it and cites it for the independent rows; both
  leads follow, and the screen is unchanged. The graph's missing edges are `F-257`'s three.
- **F-257** · E · `lem:case-III-candidate-row` and `lem:case-III-claim612-p2-placement`
  (`algebraic-induction/case-iii.tex`): since round 2 task 7 both pin `case_III_rank_certification`,
  whose body calls the pins of `lem:case-III-claim612-block-iff-perp` (`mem_hingeRowBlock_iff`,
  444 lines after the first node) and of `lem:case-III-claim612-eq644` (`hingeRow_comp_single_off`,
  688 and 183 lines after them). Three proof edges are missing, the first node's to both and the
  second's to the second. Adding them makes new forward `\uses` (that round's gate 4), and *Node
  order* cures them only by moves the task's line does not name: `lem:case-III-claim612-eq644`
  (with KT eq. (6.44)'s setting, the vertex $c$) to after `lem:case-III-acolumn-zero`, whose
  KT eq. (6.43) it follows, and `lem:case-III-claim612-block-iff-perp` (with the paragraph before
  it) to after `lem:case-III-candidate-row-construction`, which it `\uses`; both leads follow.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the two nodes, `--summary` and the
  forward screen, on round 2 task 7's tree).
  *Found:* RECONCILE round 2 task 7.
  *Disposition:* done (`98f89445`): `lem:case-III-claim612-eq644` moved to just after
  `lem:case-III-acolumn-zero`, with a lead for its setting, and `lem:case-III-claim612-block-iff-perp`
  to just before `lem:case-III-candidate-row`, with the lead its statement needs; the proofs of the
  candidate row (both edges) and of the second framework (the second) gain the three edges, each
  cited where its step is used, and the lead before the third framework cites the moved node. The
  screen is unchanged and the graph has no missing edge. Task 12 had measured that its pin move
  (`mem_hingeRowBlock_iff` to `def:hinge-row-block`) did not cure the first edge, as the
  certification also calls `case_III_full_family_restriction`, whose body calls the node's other pin,
  `linearIndependent_sumElim_candidateRow_iff`.
- **F-259** · E · `thm:panel-hinge-iff-molecular` (`molecule-modelling.tex`): round 2 task 9's
  pin for its "In particular", `BodyHingeFramework.rankHypothesis_zero_iff` (`Pinning.lean`), is a
  general lemma that five earlier nodes' pins call. Pinned at the theorem, it leaves five missing
  proof edges to it: from `thm:theorem-55-6` and `lem:theorem-56-general-position`, each closing a
  cycle, and from `thm:molecular-conjecture`, `thm:theorem-55-6-multigraph` and
  `thm:molecular-conjecture-multigraph` (`panel-layer.tex`), forward. No order cures a cycle, so
  the task did not make the pin. Pinned instead at `lem:trivial-motions-rank-bound`
  (`rigidity-matrix.tex`), whose "with equality if and only if $(G,p)$ is infinitesimally rigid"
  it proves in the dimension form, it leaves no missing edge; the theorem's proof, which cites
  that node, could then `\uses` it (an implied edge), its note citing it for the "In particular".
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, `--chapter` and `--summary` on
  scratch copies of round 2 task 9's parent with the pin at each node, `--tex-root`).
  *Found:* RECONCILE round 2 task 9.
  *Disposition:* done (`64a531db`): `lem:trivial-motions-rank-bound` pins it, its note reading it as
  the equality for $\dim Z(G,p)$; the theorem's proof `\uses` that node (an implied edge, the drawn
  graph unchanged), and its note cites it for the "In particular"; no missing edge.
- **F-261** · E · `lem:block-rank-path` (`rigidity-matrix.tex`): since round 2 task 12 unpinned
  `add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` (`F-247`), the node's pin
  `le_finrank_span_rigidityRows_path` reaches through that lemma's body (by
  `Graph.cutEdges_union_image_of_bridgePath` and `Graph.eq_cutEdge_of_isLink_crossing`)
  `Graph.cutEdges`, the pin of `def:cut-edges-2ec` (`deficiency.tex`, the next chapter). The proof
  edge is missing; the edge to `thm:pencil-x0-bridge` had made it implied. Adding it makes a new
  forward `\uses` (that round's gate 4); a cure moves nodes, or changes the Lean, outside that
  task's line.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:block-rank-path`, `--summary` and
  the forward screen, on round 2 task 12's tree); read (the bodies of the two lemmas).
  *Found:* RECONCILE round 2 task 12.
  *Disposition:* done (`cd516eda`): the proof `\uses` `def:cut-edges-2ec`, a forward edge in place of
  the one task 12 removed (the screen's `rigidity-matrix` count the open's, 3/2).
- **F-262** · E · `lem:case-I-realization-h65` (`algebraic-induction/case-i.tex`): its pin
  `case_I_realization_h65_gen` calls `exists_independent_panelRow_subfamily_of_edge`, the pin of
  `lem:case-II-placement-new-rows` (`genericity-and-count.tex`, the next file). The proof's edge to
  `lem:case-III-claim612-block-iff-perp`, which the pins reached only through
  `mem_hingeRowBlock_iff`, made it implied; round 2 task 12 moved that pin to
  `def:hinge-row-block` and the edge with it, so the proof edge is missing. Adding it makes a new
  forward `\uses` (that round's gate 4; the proof's edge to
  `lem:case-II-placement-block-independent`, in the same file, is forward already); a cure moves
  nodes outside that task's line.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:case-I-realization-h65`,
  `--summary` and the forward screen, on round 2 task 12's tree).
  *Found:* RECONCILE round 2 task 12.
  *Disposition:* done (`cd516eda`): the proof `\uses` `lem:case-II-placement-new-rows`, a forward edge
  in place of the one task 12 removed (the screen's `case-i` count the open's, 14/6).
- **F-270** · E · `lem:splitoff-simple` (`molecular-induction.tex`): since RECONCILE round 3 task
  11 its pin `isKDof_zero_of_triangle` is the case $m = 3$ of `isKDof_zero_of_cycle` (`F-108`),
  the pin of `lem:cycle-zero-dof`, 179 lines later in the chapter. The proof edge is missing, the
  graph's one missing edge, and the proof's edge to `def:D-deficiency` is now unbacked (through a
  node). Adding the edge makes a new forward `\uses` (that round's gate 7), and the node order
  cures it only by a move the task's line does not name: `lem:cycle-zero-dof` to `deficiency.tex`,
  beside `lem:two-vertex-zero-dof` (their pins share `Molecular/Deficiency.lean`), stating the
  cycle in its own words, as its pin takes two maps and not `Graph.CycleData` (its statement edge
  to `def:cycle-data` has no Lean basis); the proof then `\uses` it, a triangle being the cycle
  on three vertices. Moving `lem:splitoff-simple` after it instead makes
  `lem:chain-data-of-noRigid`'s proof edge to it forward.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:splitoff-simple`, `--summary` and
  the forward screen, on round 3 task 11's tree).
  *Found:* RECONCILE round 3 task 11.
  *Disposition:* done (task 11.1): `lem:cycle-zero-dof` moved after `lem:two-vertex-zero-dof`,
  stating the cycle in its own words, without `def:cycle-data`; `lem:splitoff-simple`'s proof
  `\uses` it for `def:D-deficiency`, its triangle the cycle on three vertices (missing 0, the
  screen the open's).

## N — node shape

- **F-009** · N · 28 nodes with four or more pins (principle D), exactly `notes/Prose.md` §7's
  list: 19 in rounds 1–4's chapters and 9 in `pencil.tex` and `main-component.tex`. The largest
  are `def:rigidity-matrix` (14), `lem:case-III-claim612-line-in-panel-union` (12) and
  `lem:pencil-jj-embed-edges` (11). Round 1's four are `def:pebble-counts` and
  `lem:pebble-game-invariants` (5 each), `def:tryReachPebble` and `lem:edgesIn-corners` (4 each).
  *Evidence:* measured (`scripts/blueprint-deps.py` report 3, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`7b2a8272`–`0f9c275c`): every node has principle D's choice, and the 12 nodes
  left with four or more pins state one result each, with a pin per clause and a role map. Split, a
  definition or a claim given a node of its own: `def:rigidity-matrix` and
  `lem:trivial-motions-rank-bound` (`a7b8ea35`), `lem:case-III-claim612-line-in-panel-union`
  (`56fb8b8c`), `def:cut-edges-2ec` and `lem:cut-edge-decomposition` (`8e6786d3`),
  `lem:panel-hinge-dual-molecular` (`dd34a61e`), `def:two-core` and
  `lem:normal-cross-count-partition` (`ae31af3e`), `lem:pencil-x0-one-witness` and
  `lem:pencil-jj-embed-edges` (`0f9c275c`). Steps unpinned: `def:tryReachPebble` (`7b2a8272`),
  `lem:two-vertex-trichotomy` and `def:graph-operations` (`8e6786d3`), `lem:cycle-realization-rigid`
  (`d851de0f`), `lem:case-III-claim612-eq644` (`24f04215`), `lem:pencil-bridge-fibre`,
  `thm:pencil-jj-equality` and `lem:pencil-x0-main-picture-open` (`24251386`),
  `lem:pencil-jj-rescale` (`0f9c275c`). Left, one result with a role map: `def:pebble-counts`,
  `lem:edgesIn-corners` and `lem:pebble-game-invariants` (`7b2a8272`), `thm:projective-invariance`
  and `lem:molecule-graph-carrier` (`dd34a61e`), `lem:square-cross-classification` (`ae31af3e`),
  `thm:pencil-x0-main-component`, `def:pencil-nondegenerate` and
  `lem:pencil-chain-span-certificates` (`24251386`).
- **F-010** · N · pinned helpers: a helper pinned on a node with another role draws missing
  in-edges from every node that uses only the helper. Each count is its target's missing
  in-edges through that pin: `lem:pencil-bridge-fibre`'s definition `pathVertex` (30, 5 of them
  from `rigidity-matrix.tex` and `deficiency.tex`), `def:rigidity-matrix`'s `ScrewSpace` (21),
  `thm:pencil-jj-equality`'s `Graph.closedNbhd_subset_vertexSet` (18),
  `lem:molecule-graph-carrier`'s `shadowGraph` (10), `def:graph-operations`'s `endsOf` (10) and
  `lem:trivial-motions-rank-bound`'s `finrank_screwAssignment` (8). Each wants principle D's
  choice: split, unpin, or a node of its own.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`a7b8ea35`, `8e6786d3` and `24251386`): `ScrewSpace` has a node of its own,
  `def:screw-space`, and `finrank_screwAssignment` is unpinned and named in its lemma's proof
  (`a7b8ea35`); `endsOf` is unpinned and named in its note (`8e6786d3`); `pathVertex` and its two
  lemmas are unpinned and named in a note, and `closedNbhd_subset_vertexSet` is unpinned and named
  in the equality's proof, which drops their 48 missing in-edges (`24251386`). Left for
  `shadowGraph`, a term of `lem:molecule-graph-carrier`'s one result, with a role map (`dd34a61e`);
  its in-edges are `e9d59672`'s.
- **F-011** · N · seven missing edges would close a cycle, so no `\uses` can add them; each needs
  a change of node shape or direction. The termination proofs of `def:runPebbleGame`'s pin
  `runPebbleGame` use the pins of three nodes downstream of it: `lem:runPebbleGame-underline-eq`,
  `lem:runPebbleGameWith-underline-subset` and `lem:workhorseWitness-certifies`. The statements
  of `def:hinge-constraint` and `def:hinge-row-block` use `ScrewSpace`, pinned on the downstream
  `def:rigidity-matrix`. `lem:trivial-motions-rank-bound` uses `IsInfinitesimallyRigid`, pinned on
  the downstream `def:dof-generic`. `thm:theorem-55-6`'s pin calls
  `thm:theorem-55-6-genuine`'s, which the blueprint derives from it.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* done (`7b2a8272`, `a7b8ea35` and `1d35d435`): the pebble game's three (`7b2a8272`),
  the two hinge definitions' and `lem:trivial-motions-rank-bound`'s (`a7b8ea35`), and KT Theorem
  5.6's, whose derivation now runs from `thm:theorem-55-6-genuine` to `thm:theorem-55-6`, as the
  Lean's does (`1d35d435`). No missing edge closes a cycle.
- **F-012** · N · liveness (`CLEANUP.md` §B): 202 pins at 153 nodes lie outside the closure of
  every main result, among them every pin of 112 nodes. Per group (pins / nodes with every pin
  outside): round 1 33/27, round 2 48/15, round 3 80/48, round 4 22/13,
  `pencil`/`main-component` 19/9. Round 1's include the executable surface, which no main result
  uses (the three `Decidable` instances, `def:runPebbleGameExec`), and side results such as
  `thm:typeII-isLaman`; `cor:pencil-flat-x0` is acceptance test (b). Each wants §B's three-way
  diagnosis (delete, wire in, or keep as exposition), not a reflex deletion.
  *Evidence:* measured (`scripts/blueprint-deps.py` report 2, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
  *Disposition:* left (`7b2a8272`–`0f9c275c` unpinned the dead wrappers and helpers whose claims
  live pins now carry, so 177 pins at 145 nodes lie outside every main result's closure, every pin
  of 109; deadness alone is no reason to unpin or retire (*Scope*), so the rest takes `CLEANUP.md`
  §B's three-way diagnosis in `notes/Prose-report.md`, G6).
- **F-014** · N · `lem:isSparse-exists-degree-le-three` (`sparsity.tex`): the low-degree step of
  the sparse reverse decomposition, `IsSparse.exists_one_le_degree_le_three` (a vertex of degree
  1, 2 or 3 in a $(2,3)$-sparse graph with an edge), has no node; the proof of
  `thm:isSparse-exists-typeI-or-typeII-reverse` (`rigidity-matroid.tex`) argues it inline. This
  node pins the weaker `IsSparse.exists_degree_le_three`, whose one Lean caller,
  `IsLaman.exists_two_le_degree_le_three` (`lem:isLaman-exists-two-le-degree-le-three`,
  `laman.tex`), has no caller and no node using it. Both pins lie outside every main result's
  closure (F-012), though `laman.tex`'s *Degree bounds* counts the Laman form among the degree
  conditions the Henneberg induction uses.
  *Evidence:* read (the body of `IsSparse.exists_typeI_or_typeII_reverse`, `Sparsity.lean`; a
  `grep` for both lemmas' callers); measured (`scripts/blueprint-deps.py --label`, dead pins, at
  `09106a34`).
  *Found:* round 1 task 5.1.
  *Disposition:* done (`7b2a8272`).

- **F-016** · N · the degree-three case of `thm:isSparse-exists-typeI-or-typeII-reverse`
  (`rigidity-matroid.tex`): its Lean, `IsSparse.False_of_pairwise_blocker_or_edge`, splits on how
  many neighbour pairs of $v$ are blocked by a tight set, through `IsSparse.contradiction_one_pair`
  (which uses `thm:isTightOn-insert-vertex-with-edges`), `_two_pair` (which uses
  `thm:isTightOn-union-with-bonus`), `_three_pair` and `no_isTightOn_excluding_three_neighbors`.
  None has a node. Jordán's Lemma 2.1.3 (three critical sets meeting pairwise in one vertex) is
  argued inside `_three_pair`, by two supermodularity counts; since task 5.9 the theorem's prose
  proof follows the same split and argues it in its three-pair case. The chapter's opening said it
  was `thm:isTightOn-union-with-bonus` composed twice until task 5.10 removed the sentence, and so
  did `notes/BlueprintExposition.md`'s Group-A note until task 5.2 corrected the note.
  *Evidence:* read (the bodies of `False_of_pairwise_blocker_or_edge` and the three templates,
  `Sparsity.lean`; `notes/Phase5.md` on the "1-deficient intermediate"); measured
  (`scripts/blueprint-deps.py --label thm:isSparse-exists-typeI-or-typeII-reverse`, at `4657a7fc`).
  *Found:* round 1 task 5.2.
  *Disposition:* done (`7b2a8272`).
- **F-019** · N · `thm:isSparse-exists-typeI-or-typeII-reverse` (`rigidity-matroid.tex`): the node
  is in §10 of the rendered blueprint, after its first user,
  `thm:isLaman-exists-typeI-or-typeII-reverse` (`henneberg.tex`, §5). Yet its pin `IsSparse.exists_typeI_or_typeII_reverse` is in
  `Sparsity.lean` and reaches only nodes of `sparsity.tex`. Prose cannot remove the cross-chapter
  forward reference; task 5.3 gives it a sentence in *Reverse decomposition*'s lead-in. Moving the
  node to the end of `sparsity.tex`, after the splitting lemma it uses, would remove it.
  *Evidence:* measured (`scripts/blueprint-deps.py --label
  thm:isSparse-exists-typeI-or-typeII-reverse`, at `0a2230a0`); read (the declaration's module).
  *Found:* round 1 task 5.3.
  *Disposition:* done (`76c3c4d4`): the theorem moved to the end of `sparsity.tex`, after the
  splitting lemma, with its subsection and that subsection's lead-in
  (`sec:isSparse-reverse-decomposition`, was `sec:rigidity-matroid-sparse-reverse`); its `\uses` all
  point at `sparsity.tex`, so no forward `\uses` is made. *Reverse decomposition*'s lead-in and
  `rigidity-matroid.tex`'s opening refer back to it; `fmlnote:reverse-vs-lift-form` stays in
  `rigidity-matroid.tex`.
- **F-029** · N · `def:rigidityMatroid` and `thm:rigidityMatroid-indep-iff-rowIndependent`
  (`rigidity-matroid.tex`, §10) use `def:countMatroid` and `thm:countMatroid-indep-iff` of
  `count-matroid.tex`, which is §11. `count-matroid.tex` uses only nodes of `sparsity.tex` and its
  own, and its opening read as if it came first ("Before packaging that result as a matroid in
  `sec:rigidity-matroid-instance`, we record the abstract object it realises"). Prose cannot remove
  the cross-section forward reference; task 5.10 gives it a sentence in the lead-in of *The rigidity
  matroid as a count matroid*, and task 5.11 rewrote `count-matroid.tex`'s opening to refer back to
  that subsection and to `thm:linearRigidityMatroid-eq-rigidityMatroid`. Moving `count-matroid.tex` before `rigidity-matroid.tex` in
  `main.tex` would remove it, and would turn that opening's `\cref`s into `rigidity-matroid.tex`
  into forward references instead.
  *Evidence:* read (the `\uses` of both chapters; `main.tex`; `count-matroid.tex`'s opening).
  *Found:* round 1 task 5.10.
  *Disposition:* left (`76c3c4d4`): moving `count-matroid.tex` before `rigidity-matroid.tex` would
  turn its opening's `\cref`s of `sec:rigidity-matroid-instance` and
  `thm:linearRigidityMatroid-eq-rigidityMatroid` into forward references. The two forward `\uses`
  stay, with the lead-in of *The rigidity matroid as a count matroid*, which names the next section.
- **F-043** · N · `thm:pebbleGameResult-isAccept-iff` (`pebble-game.tex`): its second pin,
  `runPebbleGameExec_isAccept_iff` (`Exec.lean`), is a statement about `def:runPebbleGameExec` of
  `executable.tex`, the next section, and its proof uses that section's sorted lists. The missing
  edges (counted in `F-001`) would point forward. Prose cannot remove the forward reference; task
  5.15's statement names the computable pebble game with a `\cref` of `sec:executable`. Moving the
  pin to a node of `executable.tex`, whose prose after `fmlnote:executable-computable-core` already
  restates the fact, would remove it.
  *Evidence:* measured (`scripts/blueprint-deps.py --label thm:pebbleGameResult-isAccept-iff`, at
  `640505ce`: `def:runPebbleGameExec` missing from the statement; `def:outListSorted`,
  `def:edgeListSorted`, `lem:mem-outListSorted` and `lem:mem-edgeListSorted` from the proof).
  *Found:* round 1 task 5.15.
  *Disposition:* done (`7b2a8272`).
- **F-044** · N · `runPebbleGameWith_witness_bridges` (`Correctness.lean`): a load-bearing lemma
  with no node. If the game on a list of edges of $G$, from an orientation of edges of $G$, returns
  a failure witness, then the witness's pair is an edge of $G$ and its orientation orients only
  edges of $G$ (by induction on the list). `runPebbleGameWith_correct`, `runPebbleGame.aux` and
  `runPebbleGameExec.aux` use it to apply `certifies_against`. Task 5.15's proof of
  `thm:pebble-game-correct` (2) argues it in words, citing `lem:runPebbleGameWith-underline-subset`.
  *Evidence:* read (its statement and body; a `grep` for its three callers); measured
  (`scripts/blueprint-deps.py --label thm:pebble-game-correct`, at `640505ce`: every proof chain
  of the pin runs through it).
  *Found:* round 1 task 5.15.
  *Disposition:* done (`7b2a8272`).
- **F-050** · N · `rigidity-matrix.tex` and `molecular-induction.tex`: 14 `\uses` edges at 11
  nodes point at nodes of later chapters. In `rigidity-matrix.tex`,
  `lem:trivial-motions-rank-bound` and `lem:relative-deficiency-rank-bound` use `def:D-deficiency`
  (`deficiency.tex`, the next chapter), and `lem:block-rank-contract`,
  `lem:rigidityRows-pinned-placement-rank-add` (two edges), `lem:extProj-preserves-rank-of-inter`,
  `lem:rank-transport-relabel-of-le-finrank`, `lem:rank-polynomial-IH-relabel`,
  `lem:rank-polynomial-IH-relabel-proj` and `lem:rank-polynomial-proj-eval` use nodes of round 3's
  `panel-layer`, `genericity-and-count`, `case-i` and `case-iii`. In `molecular-induction.tex`, the
  KT Lemma 6.1 realization lemmas `lem:case-cut-edge-realization` and
  `lem:case-cut-edge-realization-gp` use `def:genuine-hinge-realization` (both),
  `lem:genericity-device` and `lem:rank-polynomial-of-le-finrank`. Prose can only give each a
  sentence; moving these nodes after the nodes they use, or `def:D-deficiency` before its users,
  would remove them.
  *Evidence:* read (each node's statement and proof `\uses` against `main.tex`'s chapter order, at
  `ac7bd966`; the check is the third screen under `notes/Prose-molecular-cleanup.md` *Scope*).
  *Found:* round 2 task 1.
  *Disposition:* done (`9a7e56b1`–`90b68fd1`): the nodes moved after the nodes they use. `9a7e56b1`
  moved `rigidity-matrix.tex`'s two deficiency bounds to `deficiency.tex`, `lem:block-rank-contract`
  and KT Claim 6.4's three lemmas to `case-i.tex`, and the superseded
  `lem:rank-polynomial-IH-relabel` to `genericity-and-count.tex`; `90b68fd1` moved KT Lemma 6.1's
  two nodes to `panel-layer.tex`, before `thm:theorem-55`. Four edges stay forward, each cited in a
  sentence: `lem:rigidityRows-pinned-placement-rank-add`'s two (moving it after their targets turns
  `lem:case-II-realization`'s edge to it forward), and those of
  `lem:rank-polynomial-IH-relabel-proj` and `lem:case-cut-edge-realization-gp` to
  `genericity-and-count.tex`, now between sections of `algebraic-induction.tex` (`F-119`).
- **F-052** · N · `matroid-union.tex`: three load-bearing lemmas with no node.
  `Matroid.generalized_halls_marriage` is Welsh's theorem (Oxley 2011, Theorem 11.2.3), the core of
  `Matroid.rado` and `Matroid.rado_v2`. `Matroid.polymatroid_of_adjMap` is Oxley's Lemma 11.2.13
  (the matroid a bipartite graph induces from $M$ is $M_f$ for $f(Y) = r_M(N(Y))$, by Rado), the
  core of `adjMap_rank_eq` and `adjMap_rk_eq` and so of `thm:matroid-partition-rank`'s pins.
  `Matroid.Union_pow_indep_iff_count` is the independence criterion for $k$ copies of one matroid
  (`F-051`), used by `BodyBar/KFrame.lean`, `BodyBar/TreePacking.lean` and
  `Molecular/Induction/Contraction.lean`. Task 2.1 names each as an address in the proof it
  supports. A node for the third, or a pin on `thm:matroid-partition-rank`, would index it.
  *Evidence:* read (their statements and bodies; a `grep` for their callers).
  *Found:* round 2 task 2.1.
  *Disposition:* done (`56fb8b8c`).
- **F-054** · N · `lem:k-frame-span-le-pi` (`body-bar.tex`): its three pins, `Graph.blockPiSpan`,
  `kFrameRow_mem_blockPiSpan` and `span_kFrameRow_le_blockPiSpan`, state the form for all bars, and
  none has a Lean caller (outside every main result's closure, counted in `F-012`). The rank count
  of `lem:k-frame-nonzero-monomial-forest`, `forest_count_of_linearIndepOn_kFrameRow`, uses their
  per-set analogues `blockPiSpanOn`, `kFrameRow_mem_blockPiSpanOn`,
  `span_kFrameRowOn_le_blockPiSpanOn` and `finrank_blockPiSpanOn`, which have no node, and the
  statement edge from `lem:k-frame-pi-finrank` to this node is unbacked. Task 2.2's proof names
  `span_kFrameRowOn_le_blockPiSpanOn` as an address. Pinning the per-set forms here would index the
  proof, and the forms for all bars could then go.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:k-frame-span-le-pi`, at `6c26eed5`:
  three dead pins); read (the body of `forest_count_of_linearIndepOn_kFrameRow`; a `grep` for the
  three names' callers).
  *Found:* round 2 task 2.2.
  *Disposition:* done (`56fb8b8c`).
- **F-059** · N · `def:plucker-coords` (`extensor.tex`): its pins `pluckerCoord` and
  `pluckerVector` have no Lean caller outside `Molecular/Extensor.lean`, and no declaration relates
  them to `extensor`: the expansion that makes the Plücker coordinate vector the extensor's
  coordinate vector (KT p. 651's "symbolic version") is not formalized, and the statement's edges
  to `def:extensor` and `def:join` are unbacked. `generic-lift.tex` cites the node for an
  extensor's coordinates, which its pin `hingeExtensorPoly` computes without these declarations.
  Task 2.4 states the expansion in prose and says in a formalization note that it is not
  formalized. A lemma stating it would make the node index what the chapter uses it for.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter extensor`, at `53ec36db`: two dead
  pins, two unbacked edges); read (`Molecular/Extensor.lean`; a `grep` for the two names' callers).
  *Found:* round 2 task 2.4.
  *Disposition:* left (no declaration states the expansion; a lemma stating it is a Lean round's).
- **F-065** · N · `cor:block-rank-vertex-two-cut` (`rigidity-matrix.tex`): its pins
  `inf_span_rigidityRows_of_vertexTwoCut` and `finrank_span_rigidityRows_vertexTwoCut_eq` have no
  Lean caller, and no node uses the corollary (outside every main result's closure, counted in
  `F-012`). The ear lemma and `main-component.tex` use the general `lem:block-rank-two-cut`, whose
  sides are any two subgraphs. Keep it as exposition of the induced case, or drop it.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter rigidity-matrix`, at `5399e053`: two
  dead pins); read (a `grep` for the two names' callers and for the label in `blueprint/src/`).
  *Found:* round 2 task 2.6.
  *Disposition:* left (exposition of the induced case; deadness alone is no reason to unpin).
- **F-068** · N · `lem:rigidityRows-pinned-placement-rank-add` (`rigidity-matrix.tex`): its second
  pin, `le_finrank_span_rigidityRows_of_pinned_placement_augment` (the count with one more row,
  KT eq. (6.29)), has no Lean caller (counted in `F-012`); Case III uses the block-level
  `linearIndependent_sum_pinned_block_augment_block` directly. The node's edge to
  `lem:case-III-conditional-block` rests on that pin. Unpin it, or keep it as exposition of KT
  eq. (6.29).
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter rigidity-matrix`, at `af438fd1`: one
  dead pin); read (a `grep` for the two names' callers).
  *Found:* round 2 task 2.7.
  *Disposition:* left (the pin states the lemma's "in particular", KT eq. (6.29)).
- **F-087** · N · `lem:packing-move` (`molecular-induction.tex`): its pin
  `exists_packing_move_of_not_inc` has no Lean caller (counted in `F-012`).
  `exists_balanced_forest_packing` (`lem:balanced-forest-packing`) makes the same move inline,
  keeping the forests pairwise disjoint, so that node's edge to `lem:packing-move` is unbacked. Keep
  the node as exposition of the move, or have the descent call the pin (`F-088`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `ce54bf15`'s Lean: one dead pin at
  `lem:packing-move`, the edge unbacked at `lem:balanced-forest-packing`); read (the body of
  `exists_balanced_forest_packing`).
  *Found:* round 2 task 2.12.
  *Disposition:* done (task 14): the descent calls the pin, now live, which backs the edge; the
  node kept, its statement the move's re-choice (`F-272`). Before: left (exposition of the move;
  having the descent call the pin is a Lean change, `F-088`).
- **F-090** · N · `cor:forest-surgery-deficiency` (`molecular-induction.tex`): it restates
  `lem:forest-surgery-split`. Its pin `splitOff_deficiency_le_of_forest_surgery` is a
  `@[deprecated]` narrative-bridge shim that applies `forest_surgery_split` to the same hypotheses
  and has no Lean caller (counted in `F-012`); `AUTHORING.md`'s pattern is for a specialization.
  Its statement edge to `lem:splitoff-deficiency`, a later node of the chapter, has no Lean basis
  (the shim names `splitOff_deficiency_le` only in its attribute). Merge it into the lemma, with
  the comparison as prose, and delete the shim in a later Lean round.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `01aec968`: a dead pin and an
  unbacked edge); read (the shim's statement and body).
  *Found:* round 2 task 2.13.
  *Disposition:* done (task 6): the shim deleted, and the corollary repinned on
  `forest_surgery_split`, the pin it shares with `lem:forest-surgery-split` (its edge to that node
  is one the script cannot back); the merge not made. Before: left (a merge, which is not among
  principle D's fixes; the shim's deletion is a Lean round's); round 2: the corollary kept (no
  node merged away, the PI's choice) and framed by `rem:forest-surgery-kt-steps`, after the
  roadmap of the subsection *Forest surgery*, which says that the formal proof takes the bound
  from `lem:splitoff-deficiency`; its lead says that it restates `lem:forest-surgery-split` with
  the same hypotheses (`8db5a0c1`).
- **F-091** · N · `lem:forest-surgery-unsplit` (`molecular-induction.tex`; unfilled, `F-008`): in
  the form of independent sets it is the case $h' = 0$ of `lem:edge-splitting`'s case (i) for
  $G = H_{ab}^v$ ($D \ge 2$, $a \neq b$), which `splitOff_indep_extend_of_fiber_lt` proves, and no
  node uses it. Its statement ended "matching deficiencies under $(H_{ab}^v)_v^{ab} = H$"; task
  2.13 states the forest form its proof gives and the relation in prose. Pin it to that
  declaration with a note, or delete it and keep KT's use for Lemma 4.4 in `rem:kt-lemma-44`.
  *Evidence:* read (the pin's statement; KT 2011 pp. 660–662).
  *Found:* round 2 task 2.13.
  *Disposition:* done (tasks 3 and 20): the node restated as the pin's case $h' = 0$ and pinned to
  it, with a note, after `lem:edge-splitting` (`43c5c8d7`); kept, not retired (the PI's choice), its
  lead says that it restates that case of `lem:edge-splitting`, and `rem:forest-surgery-kt-steps`
  says that the formal proof applies `lem:edge-splitting` at it for the second assertion of KT
  Lemma 4.4 and compares partitions for the first (`8db5a0c1`).
- **F-096** · N · `lem:removal-deficiency-strict` and `lem:reduction-step`
  (`molecular-induction.tex`): each bundles results that KT state separately (principle E). The
  first is the second assertion of KT Lemma 4.4 and KT Lemma 4.7, one pin each. The second is KT
  Lemma 4.8(i) and, through `Graph.contraction_isMinimalKDof`, which is also
  `lem:contraction-minimality`'s pin, KT Lemma 3.5 at $k = 0$ (`F-084`). Split the first; unpin the
  second's contraction half and keep it a sentence.
  *Evidence:* read (the four pins' statements; KT 2011 pp. 662, 665–666).
  *Found:* round 2 task 2.15.
  *Disposition:* done (`20d62426`) for `lem:removal-deficiency-strict`, which keeps KT Lemma 4.7,
  the second assertion of KT Lemma 4.4 split off as `lem:removal-deficiency-equality`; left for
  `lem:reduction-step` (its part (ii) states KT Lemma 3.5 at $k = 0$, the narrowing the PI kept at
  `F-084`, so its second pin proves a clause; dropping the clause is a statement change, and folding
  it into `lem:contraction-minimality` a merge: `a111b17a`, `notes/Prose-report.md` G2, with
  `F-120`'s doubles).
- **F-098** · N · `lem:rigidContract-isMinimalKDof` (`case-i.tex`) and
  `lem:pencil-contract-standing` (`main-component.tex`): KT state Lemma 3.5 for the graph $G/E(H)$
  in their §3, where `molecular-induction.tex` now states only the matroid form (`F-084`) and gives
  the graph form in prose. Its node, `lem:rigidContract-isMinimalKDof`, sits in `case-i.tex`
  because Case I is its one consumer; `Graph.minimal_kdof_reduction` (KT Theorem 4.9) hands its
  contraction branch the induction hypothesis and needs no graph form. Move the node to follow
  `lem:contraction-minimality`: its pin is in `Induction/Contraction.lean` beside the matroid
  form's, and every node it reaches comes earlier, except `lem:reduction-step`, reached only
  through the pin `F-096` unpins, and `lem:pencil-contract-standing`, whose second pin
  `Graph.rigidContract_vertexSet_ncard` is the general count $|V(G/E(H))| = |V(G)| - |V(H)| + 1$,
  not a pencil fact. Re-home that pin first, to `lem:reduction-measure` (which pins the strict
  form) or `def:rigid-contraction`; the moved node's statement edge to `lem:reduction-step` is
  then `lem:reduction-measure`'s (`F-095`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `ddc4a8fc`); read (the
  statements of `contraction_isMinimalKDof`, `rigidContract_isMinimalKDof` and
  `minimal_kdof_reduction`).
  *Found:* round 2, the PI's review of `F-084` (2026-10-12).
  *Disposition:* done (`20d62426`): the count re-homed with its pin to `lem:reduction-measure`, and
  the node moved after `lem:contraction-minimality`, its statement edge now
  `lem:reduction-measure`'s.
- **F-103** · N · `lem:adjacent-degree-two-pair` and `lem:chain-data-of-noRigid`
  (`molecular-induction.tex`): the $d = 3$ extraction is a dead route. Both pins lie outside every
  main result's closure (counted in `F-012`). The only caller of `exists_adjacent_degree_two_pair`
  is `exists_chain_data_of_noRigid`, which has none, and neither node has a user outside the pair:
  Case III extracts its chain by `lem:chain-data-extract`. Only the second node's title carries the
  superseded marker. Collapse the pair to a remark (`blueprint/CLAUDE.md`, a whole dead route), or
  mark the first too. `thm:minimal-kdof-reduction`'s pin also lies outside every main result's
  closure; it stays, as KT's theorem.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, dead pins, at `a2df0ed3`); read (a
  `grep` for the two names' callers).
  *Found:* round 2 task 2.16.
  *Disposition:* done (`20d62426`): the first node's title marked superseded too.
- **F-106** · N · `def:cycle-data` and `lem:chain-cycle-dichotomy` (`molecular-induction.tex`):
  `def:cycle-data`'s third pin `CycleData.vertexSet_ncard` has no Lean caller and lies outside
  every main result's closure; like the second, it is immediate from the definition. The
  dichotomy's third pin `isKDof_zero_of_cycle` (a cycle on $m$ vertices, $3 \le m \le D$, is a
  $0$-dof-graph) is a load-bearing lemma with no node of its own. Since task 2.17 the dichotomy's
  proof proves it as a first step, and the proof of `lem:chain-data-extract` (the triangle of KT
  Lemma 6.7(ii), whose pin uses `isKDof_zero_of_triangle`, `F-108`) and the prose after the
  dichotomy cite that step. Give it a node that both lemmas use, and unpin `vertexSet_ncard`.
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, dead pins, at `1d455ed9`); read (a
  `grep` for the callers of `vertexSet_ncard` and `range_vtx`).
  *Found:* round 2 task 2.17.
  *Disposition:* done (`20d62426`): `lem:cycle-zero-dof`, which the two lemmas' proofs use;
  `vertexSet_ncard` unpinned and named in `def:cycle-data`'s note.
- **F-110** · N · `lem:case-III-claim612-line-in-panel-union` (`meet.tex`; twelve pins, `F-009`):
  the first three pins are the lemma, at $d = 3$. The other nine are a realization of Case III at
  $d = 3$ that applies it, and the last of them, `hasGenericFullRankRealization_of_rigidOn_ofNormals`
  (the bare-to-generic upgrade, KT's use of Lemma 5.2), is the one `lem:cycle-realization`
  (`case-i.tex`) cites this node for. All but that upgrade lie outside every main result's closure
  (counted in `F-012`). The form for every $d$, `extensor_join_proportional_complementIso_meet`
  (with `complementIso_extensor_mem_range_map_subtype` and `complementIso_map_contragredient_eq`),
  has no node, though `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` and
  `exists_extensor_eq_panelSupportExtensor_gen` call it; `lem:case-III-chain-discriminator`
  (`case-iii.tex`) cites the $d = 3$ node as "the general" duality. Give the general form a node,
  and move the nine pins to the Case I and Case III nodes that use them.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter meet`, dead pins, at `d5db0e0c`); read
  (the pins' statements and bodies; a `grep` for the general form's callers).
  *Found:* round 2 task 2.18.
  *Disposition:* done (`56fb8b8c`).
- **F-111** · N · `meet.tex`'s step nodes. `lem:complement-iso-line-one-dim` and
  `lem:complement-iso-exterior-map-injective` have no Lean caller (`finrank_exteriorPower_two_eq_one`
  is used only by the other pin of the first): the formal proof of
  `lem:case-III-claim612-line-in-panel-union` does not take their route through $\bigwedge^2 W$.
  The steps it does take have no node: the dimension $5$ of the span of the $n_i \vee v$
  (`finrank_sup_range_wedgeFixedLeft`, with `inf_range_wedgeFixedLeft` and
  `finrank_range_wedgeFixedLeft`) and the coordinate pairing of $2$-extensors as a Gram determinant
  (`exteriorPower_basis_toDual_eq_pairingDual_comp_map`, `extensor_toDual_extensor_eq_zero_of_perp`).
  `def:meet-pairing-dual` has no user node and its pins have no caller; the Gram determinant uses
  mathlib's `exteriorPower.pairingDual` itself. `def:meet`'s pin has no caller and no lemma about
  it exists (`F-112`). The basis formula `complementIso_exteriorPower_basis_eq_smul_compl` and the
  transformation law `complementIso_map_contragredient_eq`, on which the prose after `def:meet`
  rests since task 2.18, have no node.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter meet`, at `d5db0e0c`); read (a `grep`
  for each pin's callers).
  *Found:* round 2 task 2.18.
  *Disposition:* left (the steps of a route the formal proof does not take; the live steps are
  addresses, the transformation law in the prose after `def:meet` and the proof of
  `lem:meet-two-hyperplanes`); round 2: the two step lemmas, with `def:meet` and
  `def:meet-pairing-dual`, framed by `rem:meet-kt-steps`, after the roadmap of `meet.tex`'s second
  subsection, which says that the formal proof of KT Theorem 5.5 compares meet and join by
  `lem:meet-two-hyperplanes` in degree $d - 1$, uses the map of `def:meet-pairing-dual` but not that
  it is an isomorphism, and forms no meet; the chapter's roadmap points to it (`5955454a`).
- **F-119** · N · node order in `algebraic-induction.tex`'s five sections: 18 `\uses` edges at 10
  nodes point at nodes of later sections. `thm:theorem-55` uses seven Case I–III nodes;
  `prop:rigidity-matrix-prop11` uses `lem:genericity-device`; `lem:triangle-normals` and
  `lem:cycle-normals` (`panel-layer.tex`) use `case-i.tex`'s `lem:panel-support-extensor-independence`;
  and five `case-i.tex` nodes and `lem:case-II-realization` use `genericity-and-count.tex`'s
  `lem:genericity-device`, `lem:isInfRigidOn-of-relative-count` and
  `lem:rank-polynomial-of-le-finrank`. 12 more edges at 7 nodes point at later nodes of their own
  section, among them `lem:case-II-realization-placement`'s four at the four lemmas after it. No
  edge points at a later chapter. The slices cure a reference within a section by moving a node
  (principle E, *Node order*) and give the others a sentence, as for `F-050`; moving nodes or
  groups between sections, such as the genericity argument before Case I, is round 5's.
  *Evidence:* measured (the second screen under `notes/Prose-algebraic-cleanup.md` *Scope*, at
  `ef57b401`).
  *Found:* round 3 task 1.
  *Disposition:* done (`2ecbd37d`): four moves, each curing edges and making none. *Two operations
  on frameworks* now follows *Panel-hinge frameworks* (the two edges to
  `lem:motions-mono-of-graph-le`); the base of the induction precedes `thm:theorem-55`, as KT Lemma
  5.3 precedes KT Theorem 5.5 (the theorem's two edges to it);
  `lem:panel-support-extensor-independence` moved into *Panel-hinge frameworks*, after the join
  lemma (the edges of `lem:triangle-normals` and `lem:cycle-normals`); and the two subsections of
  `genericity-and-count.tex` now come between Cases I and II (`lem:case-II-realization`'s two edges
  into them). 26 edges stay forward: `thm:theorem-55`'s six into Cases I–III and
  `prop:rigidity-matrix-prop11`'s to it (KT state the theorem before its cases, and the proposition
  takes its lower bound from it); the base producers' three, to `lem:rows-polynomial-in-normals`
  (the first step of KT Claim 6.4, in its group in Case I) and to the counting subsection;
  `lem:case-cut-edge-realization-gp`'s and Case I's 13 into the counting subsection, which uses
  `lem:case-I`, `def:pinned-motions-on` and `lem:rows-polynomial-in-normals`, so that it can precede
  its users only by regrouping Case I; and two into Case III's subsections on KT Claim 6.12 and on
  KT eqs. (6.24)–(6.29), from `lem:case-I-realization-h65` and `lem:case-II-realization`.
- **F-120** · N · round 3's doubly pinned declarations (`algebraic-induction/case-iii.tex`): ten
  names in `blueprint/lean_decls` are pinned on two nodes, two of them here.
  `Graph.splitOff_exists_base_inter_fiber_lt` is the first pin of `lem:splitoff-kdof-criterion`
  (`molecular-induction.tex`, KT Lemma 4.3(ii)) and the only pin of `lem:case-III-claim-6-11-base`,
  which restates that lemma's forward half and does not use it.
  `exists_affineIndependent_panel_incidence` is the pin of both
  `lem:case-III-claim612-points-affineIndep-witness` and `lem:case-III-claim612-points-affineIndep`.
  It has no Lean caller, and neither have the pins of `lem:case-III-claim612-points-affineIndep-producer`
  and `lem:case-III-claim612-detpoly`, whose route the second node's proof says "would also work".
  The other eight doubles are `Graph.contraction_isMinimalKDof` (`F-096`) and seven in `pencil.tex`
  and `main-component.tex`.
  *Evidence:* measured (`sort blueprint/lean_decls | uniq -d` and each name's nodes, at
  `ef57b401`); read (a `grep` for the three pins' callers, which finds only docstrings).
  *Found:* round 3 task 1.
  *Disposition:* done (`58307442`): the two doubles here, each pair one claim stated twice, are one
  node each: `lem:case-III-claim-6-11-base`, the forward half of `lem:splitoff-kdof-criterion`, is
  merged into it, and `lem:case-III-claim612-points-affineIndep-witness` into
  `lem:case-III-claim612-points-affineIndep`. The other eight stay, as the PI decided
  (`notes/Reconcile.md` §3, G2), each doubled pin stating a clause of both its nodes.
  `contraction_isMinimalKDof`: `lem:reduction-step`'s part (ii) states KT Lemma 3.5 at $k = 0$
  (`20d62426`). The seven in `pencil.tex` and `main-component.tex`
  (`24251386`): `pencilPair_of_nonempty` is the claim of `thm:pencil-conditioned-pair-nonempty` and
  the general claim of `thm:pencil-realization-theorem`, a main result's node;
  `thm:pencil-x0-main-component`'s four pins and two of `thm:pencil-x0-generic-attains`' three state
  the claims of the lemmas their proofs cite, which those theorems restate.
- **F-131** · N · `lem:theorem-55-base-producer-empty`, `lem:theorem-55-base-producer-single`,
  `lem:theorem-55-base-producer-parallel`, `lem:extensor-pair-in-panel`
  (`algebraic-induction/panel-layer.tex`): the nodes pin the $d = 3$ (`k := 2`) wrappers
  `theorem_55_base_producer_empty`, `_empty_gp`, `_single_edge`, `_single_edge_gp`,
  `_parallel_pair` and `exists_linearIndependent_extensor_pair_perp`. None has a caller, and all six
  lie outside every main result's closure. The general forms that the induction uses
  (`theorem_55_base_producer_empty_gen` and the four other `_gen` names,
  `exists_linearIndependent_extensor_pair_perp_grade`), which `theorem_55_base_producer_gen` (the
  pin of `lem:theorem-55-base-producer`) and `case_I_realization_nonsimple_gen` call, have no node.
  So the three cases' statements, for every $d$, claim more than their pins, and the dispatch's
  three `\uses` of them have no Lean basis. Repinning the three cases to the `_gen` forms aligns
  both; `lem:extensor-pair-in-panel` states $K^4$, as its pin does, and the form for $K^{d+1}$ is
  the paragraph after it. `lem:case-I-realization-nonsimple` (`case-i.tex`) likewise pins the dead
  wrapper `case_I_realization_nonsimple`. Task 2.4 kept the statements, with a note after the third
  case that names the `_gen` forms.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the five base nodes and
  `lem:case-I-realization-nonsimple`, at `fd204aa5`: seven dead pins, the dispatch's three `\uses`
  unbacked); read (the wrappers' bodies, one-line specializations; a `grep` for their callers,
  which finds only docstrings).
  *Found:* round 3 task 2.4.
  *Disposition:* done (`1d35d435`) for the three base cases, repinned on the five `_gen` forms with
  their statements kept and a note on what the pins prove beyond them; left for
  `lem:extensor-pair-in-panel` (it states $K^4$, as its pin does);
  `lem:case-I-realization-nonsimple` repinned by `d851de0f` (`F-143`).
- **F-134** · N · `lem:cycle-realization-base`, `lem:cycle-realization-dim-bound`,
  `lem:exists-independent-panel-extensor`, `lem:pinned-motions-on-mono`,
  `lem:pinned-motions-on-rank-bound`, `lem:pinned-motions-on-rigid-iff`
  (`algebraic-induction/case-i.tex`): every pin of these six nodes lies outside every main result's
  closure, and no declaration outside the node calls one, except
  `screwDim_add_finrank_pinnedMotionsOn_le` (called by `rankHypothesis_iff_finrank_pinnedMotionsOn`,
  a dead pin of `lem:case-I`, `F-116`) and `pinnedMotionsOn_le_withGraph_of_le` (by two unpinned
  dead declarations). The first node restates
  `lem:theorem-55-base` for panel-hinge frameworks: its pin is `theorem_55_base` applied to
  `P.toBodyHinge`. The first three are used only by `\uses` edges with no Lean basis
  (`lem:cycle-realization-rigid` and `lem:cycle-realization`; `lem:case-II` and
  `lem:case-II-realization-placement`); the realization of KT Lemma 5.4 takes its normals from
  `lem:cycle-normals`, and the pairs of the third share no normals. No node uses the fourth or the
  sixth. The first three pins of `lem:cycle-realization-rigid`, its `Fin m`-body forms, likewise have
  no caller outside the node; the fourth, `theorem_55_cycle`, is the live one. Each wants `F-012`'s
  three-way diagnosis; merging the first node into `lem:theorem-55-base` and unpinning the `Fin m`
  forms are the obvious candidates.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the slice's ten nodes, dead pins and
  unbacked edges, and the closure of `formalization.yaml`'s main results over its cache, at
  `8cfa4531`); read (a `grep` for each pin's callers).
  *Found:* round 3 task 2.6.
  *Disposition:* done (`d851de0f`) for `lem:cycle-realization-rigid`, which pins `theorem_55_cycle`
  alone (its three `Fin m` forms unpinned, `F-238`); left for the six dead nodes, kept as exposition
  (merging the first into `lem:theorem-55-base` is not among principle D's fixes; `a111b17a`,
  `notes/Prose-report.md` G3 and G4); round 2: the six framed by `rem:case-I-kt-steps`, after the
  roadmap of `case-i.tex`, which says what the formal proof uses instead, and the lead of
  `lem:cycle-realization-base` says that it restates `lem:theorem-55-base` (`e6f1e425`).
- **F-139** · N · `lem:claim-6-4`, `lem:rows-polynomial-in-normals`, `lem:case-I-splice-seed`,
  `lem:case-I` (`algebraic-induction/case-i.tex`): every pin of the first three, and the second and
  third pins of `lem:case-I`, lie outside every main result's closure. Their callers are dead too:
  `case_I_realization` alone calls the pin of `lem:claim-6-4`; `exists_relative_full_count_ofParam`
  (the pin of `lem:relative-device-count`) alone calls that of `lem:rows-polynomial-in-normals`; four
  unpinned splice lemmas (`GenericityDevice.lean`, `Coupling.lean`) call that of
  `lem:case-I-splice-seed`; and the panel form of `rankHypothesis_iff_finrank_pinnedMotionsOn` calls
  the body form, and only the unpinned
  `toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition` calls the panel form.
  `lem:claim-6-4` states at $k = 0$ the claim of `lem:rank-polynomial-IH-relabel-proj`
  (`rigidity-matrix.tex`), whose pin the formal Case I reaches, and its pin is the degenerate-point
  step of that lemma's proof. Merging the two nodes, and repinning
  `lem:rows-polynomial-in-normals` on its polynomial declarations (`F-137`), are the candidates.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the slice's five nodes and
  `lem:case-I-realization`, at `9a465598`); read (a `grep` for each pin's callers).
  *Found:* round 3 task 2.7.
  *Disposition:* done (`d851de0f`) for `lem:rows-polynomial-in-normals`, repinned on its polynomial
  coordinates, their degree bound and the spanning, a pin per clause (`F-137`); left for
  `lem:claim-6-4` (merging it into `lem:rank-polynomial-IH-relabel-proj` is not a D fix; `a111b17a`,
  `notes/Prose-report.md` G3 and G4) and for the dead pins of `lem:case-I-splice-seed` and
  `lem:case-I` (deadness alone is no reason to unpin); round 2: the three framed by
  `rem:case-I-kt-steps`, which says what the formal proof uses instead: the row count in the proof
  of `lem:case-I-realization`, and `lem:rank-polynomial-IH-relabel-proj` for KT Claim 6.4 (`e6f1e425`).
- **F-143** · N · `lem:case-I-realization-nonsimple`, `lem:case-I-dispatch`
  (`algebraic-induction/case-i.tex`): the pin of the first, `case_I_realization_nonsimple`, lies
  outside every main result's closure and has no caller, so the second's `\uses` edge to it has no
  Lean basis; the dispatch calls the unpinned `case_I_realization_nonsimple_gen` (`F-142`). Three
  load-bearing steps of the formal Case I have no node: the case split for every $k$,
  `case_I_hcontract_gen`, which `thm:theorem-55`'s pin calls for Case I and whose $k = 0$ branch is
  the dispatch; KT Claim 6.6, `exists_degree_two_removeVertex_of_no_simple_contraction`, and its
  first assertion ($k = 0$), `deficiency_eq_zero_of_simple_rigid_no_simpleContraction`; and the
  combination of KT Lemma 6.3's two realizations,
  `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`. Repinning the
  first node on the general form, and a node for the case split (or a second pin on the dispatch)
  with KT Claim 6.6 in it, are the candidates.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the slice's four nodes, at
  `666f05f9`); read (a `grep` for each declaration's callers and for its pins in
  `blueprint/src`).
  *Found:* round 3 task 2.8.
  *Disposition:* done (`d851de0f`): `lem:case-I-realization-nonsimple` repinned on
  `case_I_realization_nonsimple_gen`; `lem:claim-6-6` pins KT Claim 6.6 and its first assertion, and
  `lem:case-I-all-k` the case split for every $k$, to which `thm:theorem-55`'s edge moved;
  `lem:case-I-realization`'s note names the coupler of KT Lemma 6.3 (principle C).
- **F-147** · N · `lem:case-II-rank-lift`, `lem:splitoff-edge-substitution`, `lem:case-II`
  (`algebraic-induction/case-ii.tex`): every pin of the first and third nodes, and the third pin
  of the second, `isLink_incident_of_not_removeVertex`, lie outside every main result's closure.
  The body form of the first is called only by the two panel forms, and nothing calls those,
  `isInfinitesimallyRigidOn_insert_iff` or `isLink_incident_of_not_removeVertex`; the formal Case II
  (`case_II_realization_all_k`) uses none of the three nodes. The third bundles a body-hinge and a
  panel-hinge assertion, and the second is vacuous (`F-145`).
  KT Lemma 6.7 has no node of its own: the pin of `lem:case-II-realization` proves $G_v^{ab}$
  simple with `splitOff_simple_of_noRigid`, `triangle_isProperRigidSubgraph` ($|V| \ge 4$) and
  `isKDof_zero_of_triangle` ($|V| = 3$, part (i)), all unpinned, while
  `lem:chain-data-extract`'s second pin is the form for $|V| \ge 4$. Retiring or merging the three
  nodes, and a node for KT Lemma 6.7 that both lemmas use, are the candidates.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the four nodes, at `5e9e329c`);
  read (a `grep` for each pin's callers and for the three declarations in `blueprint/src`).
  *Found:* round 3 task 2.9.
  *Disposition:* done (`657f3483`) for KT Lemma 6.7: `lem:splitoff-simple` pins
  `isKDof_zero_of_triangle`, `triangle_isProperRigidSubgraph` and
  `splitOff_simple_of_noRigid_of_card` (moved from `lem:chain-data-extract`), and both lemmas use
  it; left for the three dead nodes, kept as exposition (retiring or merging them is not among
  principle D's fixes; `a111b17a`, `notes/Prose-report.md` G4); round 2: `lem:case-II-rank-lift`
  and `lem:case-II` framed by `rem:case-II-kt-steps`, after the roadmap of `case-ii.tex`, which says
  that the formal proof counts rows instead, and the lead of the first says that its first
  assertion restates `lem:rank-delete-vertex` (`04b33020`).
- **F-152** · N · `lem:genericity-device`, `lem:relative-device-count`,
  `lem:realization-of-independent-rows`, `lem:case-II-placement-old-rows`,
  `lem:case-II-realization-placement` (`algebraic-induction/genericity-and-count.tex`): every pin of
  these five nodes, and the first pin of `lem:case-II-placement-old-rows-extract`, lie outside every
  main result's closure, seven of the file's fourteen pins. `lem:relative-device-count` and
  `lem:realization-of-independent-rows` hold at the given normals with no genericity step, as
  `F-117` found for `lem:genericity-device`. The used content is `lem:relative-screw-split`,
  `lem:isInfRigidOn-of-relative-count`, `lem:rank-polynomial-of-le-finrank` (the open-set form of
  `lem:genericity-device`, a subsection later), `lem:case-II-placement-new-rows`,
  `lem:case-II-placement-block-independent` and the second pin of
  `lem:case-II-placement-old-rows-extract`. That node is stated for a split-off and the block lemma
  for rows of a framework; their pins hold for every graph and every pair of families of forms, and
  `generic-lift.tex` and `rigidity-matrix.tex` cite them so. Retiring the dead nodes, joining
  `lem:genericity-device` to `lem:rank-polynomial-of-le-finrank`, and stating the two general lemmas
  generally are the candidates.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the eleven nodes, at `120eca58`);
  read (a `grep` for each dead pin's callers).
  *Found:* round 3 task 2.10.
  *Disposition:* left (retiring the dead nodes and joining `lem:genericity-device` to
  `lem:rank-polynomial-of-le-finrank` are not among principle D's fixes, `a111b17a`,
  `notes/Prose-report.md` G3 and G4; stating the two lemmas generally is a statement change,
  `F-239`). The extraction has its own node since `657f3483` (`F-209`); round 2:
  `lem:genericity-device` pins the live `exists_rankPolynomial_of_le_finrank_linking` with
  `lem:rank-polynomial-of-le-finrank`, and `lem:relative-device-count` no longer `\uses` it (task
  5); its other four nodes framed by `rem:case-II-kt-steps`, which says what the formal proof uses
  instead, and the lead of *Counting rows and motions* points to it (`04b33020`).
- **F-157** · N · `lem:case-III-claim-6-11` (`algebraic-induction/case-iii.tex`): the node states
  Claim 6.11 for $G_v^{ab}$ and $G_v = G - v$; its pin
  `exists_redundant_panelRow_ab_of_finrank_eq` holds for any two graphs whose links agree but for
  one edge, at any vertex count $m$. Its live callers have no node: they obtain KT eq. (6.18) at
  the chosen normals from rigidity, and set $k' = D(m - 1) - \operatorname{rank} R(G_v, q)$, so
  that KT eq. (6.22) holds by definition and `lem:case-III-nested-rank-lower` gives
  $k' \le D - 2$ (`exists_redundant_panelRow_ab_lam_of_rigidOn`, through
  `exists_redundant_panelRow_ab_lam` and `exists_redundant_panelRow_ab_decomposition`). With
  `exists_candidateRow_bottomRows_of_rigidOn`, `chainData_split_w6b_gates` and
  `exists_shared_redundancy_and_matched_candidate`, they are the path from Claim 6.11 to
  `lem:case-III-chain-discriminator`'s pin, which the blueprint does not show. A node for that step,
  or Claim 6.11 stated in its general form, are the candidates.
  *Evidence:* read (the bodies of the five declarations, `Molecular/AlgebraicInduction/CaseIII/
  Candidate.lean` and `Realization.lean`; a `grep` for each in `blueprint/src`).
  *Found:* round 3 task 2.11.
  *Disposition:* done (`24f04215`): `lem:case-III-redundant-combination` pins
  `exists_redundant_panelRow_ab_lam_of_rigidOn`, KT eqs. (6.24) and (6.25) at normals where
  $(G_v^{ab}, q)$ is rigid and KT eq. (6.22) holds as a bound; the notes of
  `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-discriminator` say that their $r$
  comes from it. Its edges to the users are `e1b16939`'s missing edges.
- **F-159** · N · `case-iii.tex`'s row operations of KT eqs. (6.24)–(6.29)
  (`algebraic-induction/case-iii.tex`): six of the nine nodes have every pin dead
  (`lem:case-III-vanish-off-column`, `lem:case-III-seam`, `lem:case-III-acolumn-zero`,
  `lem:case-III-conditional-block`, `lem:case-III-candidate-row-construction`,
  `lem:case-III-candidate-row`), and `lem:case-III-transport-collapse` two of its three; only the
  pins of `lem:case-III-columnop` and `lem:case-III-redundant-decomposition` and
  `hingeRow_sub_hingeRow_eq` lie in the main results' closure. The live path through these
  equations has no node: `caseIIICandidate` (KT's $(G, p_1)$ of eq. (6.12), with $L$ the meet of
  $\Pi(a)$ and a second panel), `exists_redundant_panelRow_ab_lam` (the coefficients with
  $\lambda_{i^*} = 1$ and $r \neq 0$), `linearIndependent_sum_augment_candidateRow_restriction`,
  `case_III_full_family_restriction` and `case_III_rank_certification` (the rank bound of KT
  eq. (6.29), with the bottom rows independent outside the columns of $v$). The dead nodes state
  the steps at the normals $q(a) + t\,q(b)$ at $v$, where the block of KT eq. (6.29) is singular
  (`F-158`). `lem:case-III-transport-collapse` bundles three facts, the third the composite of
  `lem:case-III-columnop` and `lem:case-III-vanish-off-column`. Nodes for KT's $(G, p_1)$ and for
  the rank bound in its live form (a repin of `lem:case-III-candidate-row`), and retiring or
  merging the dead nodes, are the candidates (`F-118`, `F-157`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the nine nodes, at `ba79d703`, and
  its Lean cache's closure of the main results for the five unpinned declarations); read (their
  statements and bodies, `Molecular/AlgebraicInduction/CaseIII/Candidate.lean`,
  `Molecular/RigidityMatrix/Basic.lean`; a `grep` for each in `blueprint/src`).
  *Found:* round 3 task 2.12.
  *Disposition:* done (`24f04215`) for the live path: `def:case-III-candidate` pins
  `caseIIICandidate` (KT's $(G, p_1)$ at $t = 0$), and `lem:case-III-rank-certification` pins
  `case_III_rank_certification` (the rank bound of KT eq. (6.29) in KT's count), placed after
  `lem:case-III-claim612-eq644`, whose pins it reaches; the notes that described the theorem cite
  it. Left: the six dead nodes, kept as KT's exposition (retiring or merging them is not among
  principle D's fixes, `a111b17a`, `notes/Prose-report.md` G3 and G4; `F-158` is the report's), and
  `lem:case-III-transport-collapse`, whose three pins state its two claims and the identity, a role
  map in its note; round 2: `lem:case-III-candidate-row`, one of the six, pins
  `case_III_rank_certification`, the rank bound in its live form (`9e98aaba`); the six framed by
  `rem:case-III-kt-steps`, after the roadmap of `case-iii.tex`, which says what the formal count at
  $(G, p_1)$ uses instead, and the candidate row's lead says that it is a case of
  `lem:case-III-rank-certification` (`98f89445`).
- **F-163** · N · `case-iii.tex`'s case $d = 3$: the span and the point choice
  (`algebraic-induction/case-iii.tex`): six of the ten nodes have every pin dead
  (`lem:case-III-claim612-points-affineIndep-producer`, `lem:case-III-claim612-detpoly`,
  `lem:case-III-claim612-points-affineIndep-witness`, `lem:case-III-claim612-points-affineIndep`,
  `lem:case-III-claim612-points-affineIndep-real-normals`, `lem:case-III-claim612-r-nonzero`). The
  first four are an affine form of KT's choice of points (KT p. 691) that no proof uses; the
  witness and `lem:case-III-claim612-points-affineIndep` share one pin and one statement (`F-120`),
  which asks for some three planes, not for the panels of $(G_v^{ab}, q)$. The point choice the formal proofs use has no live node:
  `exists_homogeneousIncidence_of_normals_gen` (every $d$; called by
  `exists_chainData_discriminator_pick_of_LI` under `lem:case-III-chain-discriminator`) is
  unpinned, and `lem:case-III-claim612-points-affineIndep-real-normals` pins its $d = 3$ wrapper;
  `exists_tripleLI_polynomial`, the factor that makes $q(a)$, $q(b)$, $q(c)$ independent in the
  $d = 3$ dispatch, has no node. On the live path $r \neq 0$ comes with
  `exists_redundant_panelRow_ab_lam` (`F-159`). A repin of the real-normals node to the general
  form, and merging or retiring the affine nodes, are the candidates (`F-118`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the ten nodes, at `4502f035`);
  read (`Molecular/RigidityMatrix/Claim612.lean`; the bodies of
  `PanelHingeFramework.case_III_candidate_dispatch` and `exists_chainData_discriminator_pick_of_LI`,
  `CaseIII/Realization.lean`; a `grep` of `blueprint/src` for the unpinned names).
  *Found:* round 3 task 2.13.
  *Disposition:* done (`258e9e73`): `lem:case-III-claim612-points-affineIndep-real-normals` is
  repinned on `exists_homogeneousIncidence_of_normals_gen`, the form for every $d$ that the chain
  discriminator's pin calls, in place of its dead $d = 3$ wrapper; the statement stays at $d = 3$,
  and its note says that the pin holds for every $d$. Left: the four affine nodes and
  `lem:case-III-claim612-r-nonzero`, kept as KT's exposition (retiring or merging them is not among
  principle D's fixes, `a111b17a`, `notes/Prose-report.md` G4; `F-120`'s double is `24251386`'s),
  and `exists_tripleLI_polynomial`, a step of the dead $d = 3$ dispatch's choice of normals;
  round 2: the witness and `lem:case-III-claim612-points-affineIndep` are one node (`58307442`); the
  three affine nodes and `lem:case-III-claim612-r-nonzero` framed by `rem:case-III-kt-steps`, which
  says that the formal proof takes vectors in homogeneous coordinates and obtains $r \neq 0$ with
  the relation (`98f89445`).
- **F-167** · N · `case-iii.tex`'s case $d = 3$: the three frameworks and KT Claim 6.12
  (`algebraic-induction/case-iii.tex`): ten of the thirteen pins of its eight nodes are dead, all
  but `case_III_claim612_gen` and `lem:case-III-claim612-eq644`'s `hingeRow_comp_single_tail` and
  `hingeRow_comp_single_off`. `hingeRow_acolumn_mem_span_rigidityRows` has no caller, and
  `acolumn_mem_hingeRowBlock_of_span_rigidityRows` is used only by the dispatch. The dispatch is
  dead by design (the subsubsection's lead says so), but its own route has no node: one theorem at
  three roles (`case_III_arm_realization`, `_M2`, `_M3`, through the unpinned
  `case_III_rank_certification` and `case_III_realization_of_rank`) gives the three frameworks'
  ranks and the rotation, and `exists_candidateRow_bottomRows_of_rigidOn` gives $r$. It uses
  neither placement pin and no relabel lemma; the two placement pins are one theorem at two roles.
  `lem:case-III-claim612-eq644` bundles five pins (`F-009`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the eight nodes, at `9190873a`);
  read (the bodies of `case_III_candidate_dispatch`, the three arms and
  `linearIndependent_sum_p2_candidateRow`/`_p3_`; a `grep` of `blueprint/lean_decls` and of the
  Lean for the unpinned names and the callers).
  *Found:* round 3 task 2.14.
  *Disposition:* left (the $d = 3$ dispatch is dead by design, as its subsubsection's lead says; its
  route's nodes came with `24f04215`, `lem:case-III-rank-certification` and
  `lem:case-III-redundant-combination`; the placement and relabel nodes stay as KT's exposition, as
  retiring or merging them is not among principle D's fixes, `a111b17a`, `notes/Prose-report.md` G3
  and G4; `lem:case-III-claim612-eq644`'s bundle was `24f04215`'s); round 2: the two placement
  nodes pin `case_III_rank_certification`, the arms' theorem at their roles (`9e98aaba`); the placement
  and relabel nodes framed by `rem:case-III-kt-steps`, the placements' leads saying that each is a
  case of `lem:case-III-rank-certification`, and the note after `lem:case-III-chain-dispatch` names
  the argument of its citations of the relabel nodes and of `lem:case-II-realization-placement`
  (`98f89445`).
- **F-171** · N · `case-iii.tex`'s general case (`algebraic-induction/case-iii.tex`): the formal
  route of KT Lemma 6.13 below the three live pins has no node. The choice of $q$ off four factors
  (`chainData_split_w6b_gates`, with the $d \times d$ minor `exists_tupleLI_polynomial`), KT's
  isomorphism $\rho_i$ as a permutation of the bodies (`Graph.ChainData.shiftPerm`), KT eq. (6.66)
  and the renamed redundancy (`interior_hρe₀_of_baseWidening`, `chainData_relabel_arm_hρGv`,
  `chainData_bottom_relabel`), the two branches (`chainData_dispatch_floor_of_discriminator`,
  `chainData_dispatch_interior_of_discriminator`), the arm theorem at three roles
  (`case_III_arm_realization`, `_M2`; `F-167`) and the producer `case_III_hsplit_producer_all_k`
  are unpinned; the dispatch's proof `\uses` the $d = 3$ relabel nodes, whose pins it does not reach
  (`F-118`). `lem:triangle-realization`'s pin is dead and is the case $m = 3$ of
  `lem:cycle-realization`'s construction; `lem:case-III`'s second pin `case_III_realization` (the
  $d = 3$ form) is dead. Nodes for KT eq. (6.66) and the renaming, or a repin of the relabel
  nodes to their general forms, are the candidates.
  *Evidence:* measured (`scripts/blueprint-deps.py --label` for the five nodes, dead pins, at
  `c3586784`); read (the bodies of `chainData_dispatch`, its two branches,
  `chainData_dispatch_interior` and `case_III_hsplit_producer_all_k`; a `grep` of
  `blueprint/lean_decls` for the unpinned names).
  *Found:* round 3 task 2.15.
  *Disposition:* done (`258e9e73`): before the chain dispatch, a lead-in for KT's $\rho_i$ and
  $q_i$, `lem:case-III-chain-relabel-rows` (KT eq. (6.62)) pinning `chainData_bottom_relabel`, and
  `lem:case-III-chain-eq666` (KT eq. (6.66) and its two consequences) pinning
  `interior_hρe₀_of_baseWidening` and `chainData_relabel_arm_hρGv`; the dispatch's proof and note
  cite both, and its (6.66) argument moved to the second. The relabel nodes' general forms
  (`ofNormals_relabel_perm`, `rigidityRow_relabel_perm`) lie outside the dispatch's closure, so they
  were not repinned. Left: the dispatch's `\uses` of the relabel nodes (unbacked, `F-170`,
  `e1b16939`); the route's other unpinned steps, which the proofs of the discriminator and the
  dispatch describe; `lem:triangle-realization`'s dead pin (deadness alone is no reason to unpin);
  and `lem:case-III`'s dead $d = 3$ pin `case_III_realization`, outside the open's choice for this
  finding, a candidate for `a111b17a`'s list, `notes/Prose-report.md` G4 (`1d35d435`–`d851de0f`
  unpinned such wrappers); round 2: `case_III_realization` unpinned (`58307442`).
- **F-192** · N · `lem:exists-tight-partition`, `lem:partitionDef-merge` (`jacobs.tex`): each
  lemma pins a definition beside its claim. The first pins `IsTightPartition`, and its statement
  defines "tight" in a closing sentence; the second pins `crossingEdgesWithin`, the count
  $e_G(Q)$, which its statement introduces and `lem:tight-partition-subfamily` restates. The
  missing statement edge of `lem:tight-partition-parts` (`F-193`) is the symptom: a lemma that
  only uses the definition reaches the existence lemma. Definition nodes for the tight partition
  and for $e_G(Q)$, or the two definitions unpinned, are the candidates.
  *Evidence:* read (the two definitions, `Molecular/Deficiency.lean`); measured
  (`scripts/blueprint-deps.py --chapter jacobs`, at `9c97fecc`).
  *Found:* round 4 task 2.5.
  *Disposition:* done (`ae31af3e`): `def:tight-partition` and `def:crossing-edges-within` pin
  `IsTightPartition` and `crossingEdgesWithin`; the existence and merge lemmas `\uses` them, and
  `lem:tight-partition-subfamily`'s statement edge goes to the first (its missing edges, `F-193`,
  are `e9d59672`'s).
- **F-197** · N · `lem:normal-cross-count-rooted`, `lem:normal-cross-count-partition`,
  `lem:singleton-part-converse` (`jacobs.tex`): the first two pin a definition beside their claims,
  `squareNormalCrossEdgesRootedAt` (whose statement defines "rooted") and `squareCutPairs`, as
  `F-192`'s two do; the five missing edges to the first (`F-196`) are the symptom. The third's pin
  is dead: `laman_square_count` counts the special cross edges by the part of their common
  neighbor, through the unpinned `squareSpecialCrossEdgesRootedAt` and its lemmas
  (`IsSquareTightPartition.squareSpecialCrossEdgesRootedAt_eq_edgesIn_neighborSet` is the converse
  in the form the count uses). A definition node for rooting, normal and special cross edges alike,
  and a repin or an unpinned converse, are the candidates.
  *Evidence:* read (the bodies of `laman_square_count`, `IsSquareTightPartition.perPart_le` and
  `IsSquareTightPartition.sum_perPart_le`, `JacobsCounting.lean`); measured
  (`scripts/blueprint-deps.py --chapter jacobs`, at `bc6573b9`).
  *Found:* round 4 task 2.6.
  *Disposition:* done (`ae31af3e`) for the two definitions: `def:rooted-cross-edges` pins
  `squareNormalCrossEdgesRootedAt` and `squareSpecialCrossEdgesRootedAt`, and `squareCutPairs`, the
  pairs leaving a part, goes to `def:g-cut-edges`; left for `lem:singleton-part-converse`, whose
  statement is the unique-part form its pin proves, not the rooted form the count uses (deadness
  alone is no reason to unpin, `F-012`).
- **F-202** · N · `def:two-core` (`jacobs.tex`; four pins, `F-009`): the definition pins three of
  its consequences, `twoCore_le`, `le_twoCore` and `twoCore_minDegree` (the core is a subgraph of
  $G$, contains every subgraph of minimum degree two, and has minimum degree two), which task 2.8
  proves in the prose after it. The facts about the core that `thm:degree-one-rank`'s proof uses
  are unpinned and have no node: `twoCore_eq_self_of_minDegree` (a graph of minimum degree two is
  its own core), `notMem_support_twoCore` and `twoCore_deleteIncidenceSet` (deleting the edge at a
  vertex of degree one leaves the core unchanged). A lemma node for these, and the definition
  pinning `twoCore` alone, are the candidates.
  *Evidence:* read (`TwoCore.lean`; the body of `degree_one_rank_of_ncard`,
  `JacobsDegreeOne.lean`); measured (`scripts/blueprint-deps.py --label def:two-core`, at
  `0e8d7546`).
  *Found:* round 4 task 2.8.
  *Disposition:* done (`ae31af3e`): `def:two-core` pins `twoCore` alone; `lem:two-core-largest` pins
  its three consequences, with the prose proof after it, and `lem:two-core-degree-one` the three
  facts, which `thm:degree-one-rank`'s proof cites (the edge is `e9d59672`'s).
- **F-209** · N · `lem:panel-witness-transplant`, `lem:generic-normals-abundance`
  (`generic-lift.tex`): two load-bearing steps of the panel section have no node. The witness
  lemma's pin extracts its rows with
  `BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank` (`GenericityDevice.lean`),
  which takes a bound on the rank in place of rigidity and is unpinned;
  the pins of `lem:hinge-point-witness` and of results in `CaseII.lean`, `CaseIII/Arms.lean`,
  `Coupling.lean`, `Pencil/Steer.lean` and `MainComponent/ContractCurve.lean` call it too. The node
  cites `lem:case-II-placement-old-rows-extract`, stated for a split-off and with pins its pin does
  not reach. The abundance lemma's pin uses the polynomial coordinates `annihRowPoly` and
  `annihRowPoly_eval` (`F-137`'s unpinned steps of `lem:rows-polynomial-in-normals`) and the
  unpinned minor lemma `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`
  (`Mathlib/LinearAlgebra/Matrix/Rank.lean`), which every abundance pin of the chapter calls.
  Candidates: pin the rank form of the extraction, stated for every framework, on
  `lem:case-II-placement-old-rows-extract` or a node of its own; repin
  `lem:rows-polynomial-in-normals` on its polynomial declarations (`F-139`).
  *Evidence:* read (the bodies of the two pins; a `grep` for the callers of the extraction and of
  the minor lemma); measured (`scripts/blueprint-deps.py --chapter generic-lift`, at `7c268bce`).
  *Found:* round 4 task 2.9.
  *Disposition:* done (`657f3483`): `lem:independent-rows-of-rank` pins the rank form of the
  extraction, for every body-hinge framework with nondegenerate hinges, and
  `lem:panel-witness-transplant` and `lem:hinge-point-witness` cite it in place of
  `lem:case-II-placement-old-rows-extract`; `d851de0f` repinned `lem:rows-polynomial-in-normals`
  (`F-139`).

- **F-214** · N · `def:two-extensor`, `lem:coordinate-extensor-basis`, `lem:extensor-map-rows`
  (`generic-lift.tex`): pinned helpers. `def:two-extensor` pins the bijection `pairIdxEquiv` (any
  bijection serves) and the polynomial form `twoExtensorPoly` (dead) beside `twoExtensor`, but not
  the evaluation identity `twoExtensorPoly_eval`, which the abundance pin uses. The two lemmas pin
  the definitions `coordPoint` and `mapPlacement` beside their claims. Task 2.10 added a role map
  for the three pins in a note. Candidates: pin `twoExtensor` alone, with the polynomial form and
  its evaluation identity on `lem:generic-endpoints-abundance` or a lemma node (as `F-209` asks
  for the panel rows), and the two lemmas on their theorems alone.
  *Evidence:* read (`BodyBar/GenericLift.lean`: the twelve pins and the body of
  `exists_isGenericEndpoints_abundance`); measured (`scripts/blueprint-deps.py --label
  def:two-extensor`, at `c8f1f0f1`).
  *Found:* round 4 task 2.10.
  *Disposition:* done (`dd34a61e`): `def:two-extensor` pins `twoExtensor` alone (`pairIdxEquiv`
  named in its note, `twoExtensorPoly` unpinned); `lem:two-extensor-polynomial`, before the
  abundance lemma, pins `twoExtensorPoly_eval`, and the abundance proof cites it; the two lemmas pin
  their theorems alone (`coordPoint` and `mapPlacement` unpinned).

- **F-219** · N · `def:generic-hinge-points`, `lem:hinge-rows-polynomial-in-points`
  (`generic-lift.tex`): pinned helpers. The definition pins the identity
  `hingePointRow_eq_panelRow` (true by definition; the witness and rank pins call it) beside the
  family `hingePointRow` and genericity `IsGenericHingePoints`; the lemma pins the definition
  `hingeExtensorPoly` beside its evaluation identity. Task 2.11 maps the pins in two notes.
  Candidates: pin the family and genericity alone on the definition, and the lemma on its
  evaluation identity (with the degree bound, `F-217`).
  *Evidence:* read (`GenericLift/HingeGeneric.lean`: the seven pins and the callers of
  `hingePointRow_eq_panelRow`); measured (`scripts/blueprint-deps.py --label
  def:generic-hinge-points`, at `dc58265b`).
  *Found:* round 4 task 2.11.
  *Disposition:* done (`dd34a61e`) for `lem:hinge-rows-polynomial-in-points`, which pins
  `hingeExtensorPoly_eval` alone (`hingeExtensorPoly` named in its note); left for
  `def:generic-hinge-points` (`7b2a8272`'s test: unpinning the identity, its one pin that states the
  framework $(G, q)$, leaves its `\uses` of `def:hinge-constraint` with no Lean basis).

- **F-224** · N · `lem:hinge-point-witness` (`generic-lift.tex`): two load-bearing steps of the
  witness have no node. The automorphism of the screw space induced by a linear map $g$ of
  $K^{d+1}$, `screwEquivOfLinearEquiv` with its extensor identity
  `screwEquivOfLinearEquiv_mk_extensor` (`GenericLift/HingeGeneric.lean`), is unpinned; the
  witness's pin uses it, and so do `Pencil/Arms.lean`, `Pair.lean`, `Motive.lean` and
  `MainComponent/Configuration.lean` (`pencil.tex` pins three lemmas about it), while
  `molecule-modelling.tex` describes it for $d = 3$ before `thm:projective-invariance`. The meet
  decomposition `exists_extensor_eq_panelSupportExtensor_gen` (`PanelLayer.lean`: a nonzero
  $C(n_1, n_2)$ is the join of a basis of $n_1^\perp \cap n_2^\perp$) is unpinned and stated only in
  the remark after `def:panel-support-extensor`; the witness, `GenericityDevice.lean` and
  `Pencil/MainComponent/Flat.lean` use it. Candidates: a lemma node for each, or pins on
  `thm:projective-invariance` and `def:panel-support-extensor`.
  *Evidence:* read (the body of `exists_hingePoints_independent_hingePointRow`; a `grep` for the
  callers of the two declarations).
  *Found:* round 4 task 2.12.
  *Disposition:* done (`1d35d435` and `dd34a61e`): the meet decomposition is
  `lem:panel-support-extensor-join` (`1d35d435`), and the screw map is `def:induced-screw-map`,
  before `thm:projective-invariance` (`dd34a61e`); the witness's proof cites both. Its missing edge
  to the second, and those of six `pencil.tex` and `main-component.tex` nodes, are
  `9eb2c776`–`60c88e44`'s.

- **F-247** · N · `thm:pencil-x0-bridge` (`main-component.tex`): its pin
  `add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`, the rank a path of bridges
  adds, is a step of its proof that its statement (the general configuration attains) does not
  state. The pin of `lem:block-rank-path` (`rigidity-matrix.tex`) applies it, so task 4.2 added
  that lemma's missing proof edge to the theorem, a `\uses` into the last chapter; through it the
  missing edge of `thm:pencil-x0-cycle` to `lem:pencil-lifting-restrict` reads as implied. A node
  for the rank lemma in `rigidity-matrix.tex`, or its unpinning, is a pin change, after task 3.
  *Evidence:* measured (`scripts/blueprint-deps.py --label thm:pencil-x0-bridge` and `--chapter
  rigidity-matrix`, at `9eb2c776`); read (the statement of the pin, and the body of
  `le_finrank_span_rigidityRows_path`).
  *Found:* round 5 task 4.2.
  *Disposition:* done (`94196444`): unpinned, as the pin's proof reaches
  `def:cut-edges-2ec` (`deficiency.tex`), so a node in `rigidity-matrix.tex` would have a forward
  edge; `lem:block-rank-path`'s proof edge to the theorem went, and `thm:pencil-x0-cycle`'s proof
  `\uses` `lem:pencil-lifting-restrict`. The path lemma's pin now reaches that definition
  (`F-261`).

- **F-248** · N · `lem:case-III-claim612-block-iff-perp` (`case-iii.tex`): its second pin
  `mem_hingeRowBlock_iff`, that a form vanishes on the span of a hinge's extensor if and only if it
  vanishes at it, is a step of its proof and a fact about `def:hinge-row-block` (the remark after
  it). The pin of `lem:screw-map-rows` (`generic-lift.tex`) uses it, through the unpinned
  `mapExtensor_rigidityRows`, so task 4.7 added that lemma's missing proof edge into
  `case-iii.tex`; nine more Lean files call it. A pin on `def:hinge-row-block`, or its
  unpinning, is a pin change, after task 3.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:screw-map-rows`, at `e1b16939`);
  read (the statement of `mem_hingeRowBlock_iff`, `RigidityMatrix/Claim612.lean`; a `grep` for
  its callers).
  *Found:* round 5 task 4.7.
  *Disposition:* done (`94196444`): `def:hinge-row-block`'s fourth pin, its claim in
  the remark after the definition and a new note; the proofs of `lem:screw-map-rows` and four
  nodes whose pins reached the lemma only through it `\uses` the definition instead.
- **F-249** · N · `def:pencil-x0-reduces` (`main-component.tex`): its first pin, `Graph.IsOpenEar`,
  defines the open ears that *Ears and cycles* defines in prose, with no node, and that the
  definition's statement takes "as in" that subsection. So every node whose pins take an open ear
  reaches the definition of a reduction: task 4.9 added the statement edges of
  `lem:pencil-generic-one-ear` and `lem:pencil-rigid-good-ear` to it, though neither statement
  mentions a reduction. A definition node for ears in *Ears and cycles*, taking the pin (principle
  E), is a node and pin change, after task 3.
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:pencil-generic-one-ear`, at
  `23bf8244`); read (`Graph.IsOpenEar`, a structure, `Pencil/MainComponent/Coverage.lean`).
  *Found:* round 5 task 4.9.
  *Disposition:* done (`cd516eda`): `def:open-ear` in *Ears and cycles* takes the
  pin, with $k \ge 0$ as its structure allows (an edge $ab$ at $k = 0$); the reduction `\uses` it,
  and the statement edges of the two lemmas and of `def:pencil-x0-chain`, whose pins reach the
  reduction only through the ear, move to it.

## T — terminology and notation

- **F-056** · T · the body-bar dimension (`generic-lift.tex`, `intro.tex`): task 2.3 wrote KT's $d$
  for the dimension and $D = \binom{d+1}{2}$ in `body-bar.tex` and `body-hinge.tex` (round 2's
  notation call), and tasks 2.4–2.18 align round 2's other chapters. Two chapters outside round 2
  keep Tay and Whiteley's letters: `generic-lift.tex`'s body-bar section writes bars in $\R^n$ with
  vectors in $\R^d$, $d = n(n+1)/2$, and $(d, d)$-sparsity (lines 449, 487, 631–724), and
  `intro.tex`'s Phase-15 and Phase-16 items write $d = n(n+1)/2$, $\delta = n(n+1)/2$,
  $(\delta-1)\cdot G$ and $(\delta,\delta)$-sparsity (lines 165–195). Round 4 rewrites both.
  *Evidence:* read (a `grep` for `n(n+1)` and `\delta` over the chapters, at task 2.3).
  *Found:* round 2 task 2.3.
  *Disposition:* done (`dc58265b`, `248ec772`): round 4's tasks 2.10 and 2.13 write $d$ and
  $D$ in `generic-lift.tex`'s body-bar section and `intro.tex`'s Phase-15 and Phase-16 items;
  $n(n+1)/2$ is left only in `body-bar.tex`'s gloss of Tay and Whiteley's letters and its
  formalization note.
- **F-067** · T · KT Proposition 1.1 (`panel-layer.tex`, `algebraic-induction.tex`,
  `deficiency.tex`, `case-i.tex`, `intro.tex`): KT's Proposition 1.1 (p. 648) is Tay and
  Whiteley's theorem, that $G$ has an infinitesimally rigid body-hinge realization if and only if
  $\tilde G$ contains $D$ edge-disjoint spanning trees. The generic rank formula
  $\operatorname{rank} R(G,p) = D(|V|-1) - \operatorname{def}(\tilde G)$ is KT's Proposition 2.3
  (p. 655), which KT credit to Jackson and Jordán (JJ 2009, Theorem 6.1). `panel-layer.tex` titles
  `prop:rigidity-matrix-prop11` and its subsection "KT Proposition 1.1, analytic half", and
  `deficiency.tex` calls $\operatorname{def} = \operatorname{corank}$ its "matroidal half" (lines
  16, 661); `algebraic-induction.tex` (15, 52), `case-i.tex` (332), `intro.tex` (222, 277),
  `panel-layer.tex`'s other mentions and `notes/BlueprintExposition.md`'s `rigidity-matrix.tex`
  entry follow. Task 2.7's opening names both as KT does; task 2.10 and rounds 3 and 4 can follow.
  *Evidence:* read (KT pp. 648 and 655; JJ 2009 Theorem 6.1, `.refs/`; a `grep` for
  "Proposition~1.1" over the chapters, at task 2.7).
  *Found:* round 2 task 2.7.
  *Disposition:* done (`1b06def1`, `db237dfd`, `5c65ea52`, `fd204aa5`, `8cfa4531`, `85e0e4f8`,
  `c766f589`, `248ec772`, `baa224cc`): rounds 2–4 name the rank formula KT Proposition 2.3, and
  `db237dfd` retitled `prop:rigidity-matrix-prop11` and its subsection; `baa224cc` corrected
  `notes/BlueprintExposition.md`'s entry. KT Proposition 1.1 is left only for Tay and Whiteley's
  theorem (`body-hinge.tex`, `rigidity-matrix.tex`, `panel-layer.tex`).
- **F-072** · T · "boundary regime" (`intro.tex`): the Phase-19 item calls $M(\tilde G)$ the
  $(D,D)$-count matroid "at the boundary regime $\ell = 2k = D$", not "the matroidal-regime count
  matroid of Phase~7". The $(D,D)$ count has $\ell = k = D < 2k$; what `count-matroid.tex` does not
  cover is parallel edges, as its matroid lives on the edges of $K_V$. Task 2.8 dropped the term
  from `deficiency.tex`'s subsection title and `def:matroid-MG`'s proof; tasks 2.9–2.11 replace
  "boundary-regime cleanliness" in the proofs of `lem:circuit-rigid`, `lem:rank-matroidMG-le` and
  `molecular-induction.tex`'s line 77, and round 4 rewrites `intro.tex`.
  *Evidence:* read (`count-matroid.tex`'s opening; `countMatroid`'s signature, a matroid on
  `Sym2 V` for `ℓ < 2 * k`, `CountMatroid.lean`).
  *Found:* round 2 task 2.8.
  *Disposition:* done (`86b44e1b`, `22317b88`, `1b06def1`, `ce54bf15`, `248ec772`): rounds 2 and 4
  dropped the term from `deficiency.tex`'s subsection title and proofs, `molecular-induction.tex`
  and `intro.tex`'s Phase-19 item; no chapter has "regime".
- **F-073** · T · the dimension letter (`main-component.tex`, `pencil.tex`): both write the
  dimension as $n$, the formalization's parameter: "the deficiencies of `def:D-deficiency` at $n = 2$
  and $n = 3$ ($D = 3$ and $D = 6$)", "the conditioned pair at $n = 3$", about 48 lines in all.
  Round 2 writes KT's $d$, and task 2.8's `deficiency.tex` writes $\operatorname{def}_d(G)$ for the
  deficiency at dimension $d$, which agrees with their $\operatorname{def}_2$ and
  $\operatorname{def}_3$.
  *Evidence:* read (a `grep` for "$n = 2$" and "$n = 3$" over the two chapters, at task 2.8).
  *Found:* round 2 task 2.8.
  *Disposition:* done (`04ed99ec` and its follow-up `34f61fd9`): KT's $d$ for the dimension on 15
  lines of `pencil.tex` and 42 of `main-component.tex`, with $\operatorname{def}_d$ for
  $\operatorname{def}_n$; `fmlnote:pencil-conditioned-pair` says that the formalization calls it
  $n$. Where $d$ would clash, `main-component.tex`'s degree $d$ is reworded (twice), a count $d$ is
  $m$, and $d(P)$ is `def:D-deficiency`'s $d_G(P)$ (the follow-up: its three places in
  `lem:pencil-lifting-space-deficiency`). The $n$ of a panel normal, of a polygon's size and of a
  dimension bound stays.
- **F-127** · T · the extensor of vectors (`molecular-induction.tex`, `main-component.tex`):
  `extensor.tex` writes the extensor of $v_1, \dots, v_j$ as the join $v_1 \vee \cdots \vee v_j$
  "from now on", and `meet.tex` writes $\wedge$ for the meet. `molecular-induction.tex` writes a
  hinge in two panels as $x_1 \wedge \dots \wedge x_{d-1}$ (twice, in the paragraph before
  `lem:case-cut-edge-realization` and in that proof), and `main-component.tex` writes
  $p_a \wedge x_1$ in one display. `def:genuine-hinge-realization` writes
  $x_1 \vee \cdots \vee x_{d-1}$ since task 2.2.
  *Evidence:* read (a `grep` for `\wedge` products of vectors over the chapters, at task 2.2).
  *Found:* round 3 task 2.2.
  *Disposition:* done (`04ed99ec`): $x_1 \vee \cdots \vee x_{d-1}$ in the proof of
  `lem:case-cut-edge-realization`, now in `panel-layer.tex` (`90b68fd1` moved it and dropped the
  paragraph before it), and $\vee$ for all 128 products on 92 lines of `main-component.tex`, each
  read as a join of vectors (none is a meet). With them, its $\Lambda^2$ (30 places) is the
  blueprint's $\bigwedge^2$, which leaves $\Lambda$ to the span of an ear's hinges. `extensor.tex`'s
  and `rigidity-matrix.tex`'s basis products $e_{i_1} \wedge \cdots$ stay.
- **F-203** · T · "core" (`jacobs.tex`, `main-component.tex`): the word names two objects.
  `def:two-core` is JJ's $G^{\mathrm{core}}$, the maximal subgraph of minimum degree at least two.
  `main-component.tex` calls the induced subgraph $H = G[W]$ of a contraction step "the core"
  (its notation list, and `sec:main-component-contract`), with "additive" cores. Neither chapter
  mentions the other's use. A different word for the contracted set in `main-component.tex`, or a
  sentence there that distinguishes it from JJ's core, is the candidate.
  *Evidence:* read (`sec:jacobs-degree-one`; `main-component.tex`'s notation list and
  `sec:main-component-contract`).
  *Found:* round 4 task 2.8.
  *Disposition:* done (`04ed99ec`): `main-component.tex`'s notation list, which defines its core,
  says that it is not the core of `def:two-core`, which every graph under the standing hypotheses is
  (`lem:two-core-degree-one`). The word stays, as the chapter's titles and
  `Graph.IsX0Graph.exists_additiveCore` use it.
- **F-227** · T · `lem:complement-iso-decomposable-wedge-perp` (`meet.tex`): its two parts are
  `\item[(i)]` and `\item[(ii)]` of an `enumerate`, and its proof says "For (i)" and "For (ii)".
  The PDF prints the labels; the web build prints the items as 1 and 2, since plasTeX drops an
  optional `\item` label (`blueprint/SETUP-AND-PITFALLS.md` *Pitfalls*). It is the blueprint's
  only `\item[…]`. Candidate: an `enumerate` with the proof's "For part 1", or inline "(i)" text.
  *Evidence:* read (the web build's `sec-molecular-meet.html`, one `<ol>`; `print.pdf` p. 139).
  *Found:* round 4 task 2.13.
  *Disposition:* done (`04ed99ec`): plain `\item`s, cited as part (1) and part (2) by the
  subsection's opening, the proof, the formalization note and the proof of
  `lem:case-III-claim612-line-in-panel-union`; `blueprint/SETUP-AND-PITFALLS.md`'s example of the
  pitfall is updated.

## U — status surfaces

- **F-099** · U · `formalization.yaml`: three places contradict round 2's rewritten chapters. (1)
  The main result `Graph.BodyHingeFramework.body_hinge_tay` and its alignment row describe a
  framework with hinges; the declaration's structure has none. `body-hinge.tex`'s formalization
  note says it is proved for bundles of bars, `generic-lift.tex` calls it the bar-bundle reduction
  statement, and the form with hinges is `cor:bodyhinge-generic-tree-packing` (`F-048`). (2) The alignment row "matroid union & partition
  rank formula" (proved): `matroid-union.tex` now says the family form is proved only at the whole
  ground set (`F-051`), with its credits (`F-053`). (3) JJ 2009's `location` and the alignment row
  "Thm 6.1 / Cor 6.2 (def = corank bridge)": `deficiency.tex` credits KT eq. (2.4) to KT and to JJ
  Theorem 4.1(a) (`F-081`). The `S` and `M` entries stay for the report.
  *Evidence:* read (`formalization.yaml`'s JJ 2009 reference and its `status.main_results` and
  alignment entries named; the chapters named).
  *Found:* round 2, the PI's review of `F-084` (2026-10-12).
  *Disposition:* done (`30c4b950`): (1) the main result's description and its alignment row say that
  `body_hinge_tay` is proved with each hinge replaced by a bundle of bars, and name the form with
  hinges (the declaration is unchanged); `status.scope` and Tay 1989's `location` no longer say
  "panel-hinge". (2) The row gives Nash-Williams and Edmonds the union's rank and Edmonds 1965 the
  partition criterion, lists the chapter's pins, and says where the family form is proved. (3) JJ
  2009's `location` and note, and the row, credit KT eq. (2.4) to KT and to JJ Theorem 4.1(a), and
  JJ Theorem 6.1 as the rank formula.
- **F-173** · U · `README.md`, `formalization.yaml`: two places contradict the rewritten opening of
  `algebraic-induction.tex`. (1) `README.md`'s molecular-conjecture item calls the algebraic
  induction the realization of KT Theorem 4.9's reduction; it runs on
  `thm:minimal-kdof-reduction-all-k`, over every deficiency, and no pin of `thm:theorem-55`
  reaches `Graph.minimal_kdof_reduction` (`F-100`). (2) `formalization.yaml`'s main result
  `rankHypothesis_of_theorem_55_gen` ("the Katoh-Tanigawa Proposition 1.1 reconciliation") and
  its alignment row "Theorem 5.6 + Proposition 1.1" name the rank formula KT Proposition 1.1; it
  is KT Proposition 2.3 (`F-067`).
  *Evidence:* read (`README.md`'s *The molecular conjecture* item; the `formalization.yaml`
  entries named; KT pp. 648, 655 and 671); measured (`scripts/blueprint-deps.py --label
  thm:theorem-55` at `889ebc08`).
  *Found:* round 3 task 2.16.
  *Disposition:* done (`30c4b950`): (1) `README.md` calls Theorem 5.5 an induction over the minimal
  $k$-dof-graphs of every deficiency. (2) The main result's description and the alignment row name
  the rank formula KT Proposition 2.3 (JJ 2009 Theorem 6.1), with `rigidityMatrix_prop11` as its
  upper bound.
- **F-204** · U · `README.md`, `home_page/index.md`, `formalization.yaml`: two places contradict
  or lag the rewritten opening of `jacobs.tex`. (1) `README.md` and the home page call Jacobs'
  conjecture and the degree-one rank formula "two further Jackson–Jordán 2008 consequences of the
  rank formula". The second does not use the rank formula: JJ prove their Lemma 4.2 from their
  Lemma 3.3, to show that the rank formula, applied to the core, determines $r(G^2)$ for every
  graph. (2) `formalization.yaml`'s entry for Jacobs 1998 has no DOI. It is
  `10.1088/0305-4470/31/31/012` (Crossref), which task 2.8 added to `bibliography.bib`.
  *Evidence:* read (`README.md`'s and the home page's paragraph on phase 32; `formalization.yaml`'s
  literature entry; JJ 2008 §4; Crossref's record for the DOI).
  *Found:* round 4 task 2.8.
  *Disposition:* done (`30c4b950`): (1) both pages call them two results of JJ 2008 on squares of
  graphs: JJ derive Jacobs' conjecture from the rank formula, and the degree-one formula reduces
  $r(G^2)$ to the core, as `jacobs.tex` says. (2) The DOI is the entry's `id`, checked again against
  Crossref's record (title, J. Phys. A 31(31), 6653–6668, 1998).
- **F-226** · U · `README.md`, `home_page/index.md`: two places contradict `rigidity-matroid.tex`
  and the rewritten *Organization of the blueprint* in `intro.tex`. (1) `README.md`'s second arc
  ("the planar rigidity matroid as a mathlib `Matroid` (Lovász–Yemini, …)") and the home page's
  phase-7 row ("Lovász–Yemini matroid id.") credit the planar identification of row independence
  with $(2,3)$-sparsity to Lovász and Yemini. Jordán (2016, p. 45, Theorem 2.2.1) credits it to
  Laman (`F-025`, which names `formalization.yaml` but not these two). (2) The home page's
  phase-21 row lists "the generic-max-rank device", which no main result's proof uses (`F-117`,
  `F-118`). Task 2.13 dropped both from `intro.tex`, and with the last citation of Lovász–Yemini
  1982 its `bibliography.bib` entry (`lint.sh` check 2).
  *Evidence:* read (`README.md` line 67; the home page's lines 177 and 191; Jordán 2016 p. 45, in
  `.refs/`).
  *Found:* round 4 task 2.13.
  *Disposition:* done (`30c4b950`): (1) `README.md` credits the characterization to Laman, and the
  home page's phase-7 row is *Row independence & count matroid*, after `intro.tex`'s item;
  `formalization.yaml`'s Lovász–Yemini lines stay with `F-025` (`M`, for the report). (2) The device
  is dropped from the phase-21 row.
- **F-229** · U · `README.md`, `home_page/index.md`: two places contradict the rewritten opening
  and *Reading this blueprint* of `intro.tex`. (1) `README.md` (lines 15 and 76) and the home page
  (lines 71–72) call the body-hinge theorem of Tay and Whiteley a "body-hinge / panel-hinge"
  theorem or extension. The panel-hinge characterization is the molecular conjecture
  (`body-hinge.tex`, after `thm:body-hinge-tay`), which the theorem does not imply. (2) Their
  status paragraphs mirror the *Reading* paragraph that task 2.14 removed: "fully green through the
  body-hinge Tay–Whiteley theorem" (`README.md` line 86, the home page's line 80) and "The
  blueprint dependency graph is fully green" (`README.md` line 153, the home page's line 141),
  while four nodes are unfilled, `def:blockingWitness` among them in phases 1–16 (`F-008`); "all
  three cases" of KT Theorem 5.5, which has four (KT p. 671, as `algebraic-induction.tex` says);
  and "genuine hinges".
  *Evidence:* read (the lines named; the built graph's 653 green and 4 blue nodes at this task's
  tree; KT p. 671).
  *Found:* round 4 task 2.14.
  *Disposition:* done (`30c4b950`): (1) both pages call it Tay and Whiteley's body-hinge theorem,
  proved with each hinge replaced by a bundle of bars (`F-099`). (2) They say instead that the main
  results of every chapter are formalized, as `intro.tex`'s *Reading* does; Theorem 5.5's induction
  has four cases, Case III the one KT call the most difficult (p. 650); its hinges are
  nondegenerate. The same phrases in `formalization.yaml` follow: "all three cases" in Theorem 5.5's
  description, and "genuine" in the two molecular conjecture descriptions.
- **F-231** · U · `formalization.yaml`: the alignment row "Lee-Streinu 2008 pebble-game
  correctness" lists `SimpleGraph.PartialOrientation.runPebbleGame_isAccept_iff` in its `lean:`,
  but no declaration has that name. The theorem is
  `CombinatorialRigidity.PebbleGame.PartialOrientation.runPebbleGame_isAccept_iff`, the name
  `thm:pebbleGameResult-isAccept-iff` pins.
  *Evidence:* read (`formalization.yaml` line 598; `PebbleGame/Correctness.lean`, the theorem at
  line 835 inside `namespace CombinatorialRigidity.PebbleGame` and `namespace PartialOrientation`).
  *Found:* round 5, the coordinator, verifying task 3.1.
  *Disposition:* done (`30c4b950`): the row names the theorem; every other declaration that
  `formalization.yaml` names resolves (`#check` on the built tree).
- **F-251** · U · `formalization.yaml` (`fidelity.divergences`): the paragraph says that the
  blueprint "states each result in the exact form proved and discusses its departures from the
  source in the chapter that proves it". The findings report's Part 1 records 65 open `S` entries
  where a blueprint statement claims more or less than its pins, S1 and S2 among them at main
  results' rows; the paragraph names no exception.
  *Evidence:* read (`formalization.yaml` lines 580–582 at `f39e35e6`; `notes/Prose-report.md` §1.2).
  *Found:* RECONCILE round 1 task 1.
  *Disposition:* done (b0eb63eb): the paragraph says the blueprint aims at the exact form, that a
  2026 review found statements claiming more or less than their declarations, which a cleanup acts
  on, and names the main results whose rows state their scope (S1's and S2's).

## S — statement strength

- **F-015** · S · `thm:isTightOn-insert-vertex-with-edges` (`sparsity.tex`): the statement assumes
  $V$ finite, which its pin `IsTightOn.insert_vertex_with_edges` does not (it takes only
  `DecidableEq V`; the set $s$ is finite). The statement is weaker than the pin. Its sibling
  `thm:isTightOn-union-with-bonus` assumes $V$ finite as its pin does.
  *Evidence:* read (the statement of `insert_vertex_with_edges`, `Sparsity.lean`).
  *Found:* round 1 task 5.2.
  *Disposition:* done (`40e1f4c8`): the statement takes no finiteness of $V$, as its pin.
- **F-020** · S · `def:isInfinitesimallyRigid` (`frameworks.tex`): `IsInfinitesimallyRigid` asks
  only $\dim\ker R(G,p) \le d(d+1)/2$, i.e. rank at least $d|V| - d(d+1)/2$, where Jordán (2016,
  pp. 36–37) asks for rank $S(|V|,d)$. The two agree for $|V| \ge d$ and $|V| \le 1$, so at
  $d = 2$ always; for $2 \le |V| \le d-1$ the formal notion is strictly weaker (two unjoined
  vertices in $\R^3$ satisfy it). `IsGenericallyRigid` inherits this. The $d = 3$ results that
  conclude it (`molecule_generic_rigid`, `molecule_generic_square_packing`) are unaffected: their
  hypotheses exclude $|V| = 2$. Task 5.4 states the divergence in `fmlnote:infinitesimal-rigidity`;
  the docstring does not mention it.
  *Evidence:* read (the body of `IsInfinitesimallyRigid`, `Framework.lean`; the two $d = 3$
  statements and `shadowGraph`); a `lake lean` witness, every graph on `Fin 2` at every $p$ in
  $d = 3$, by `Submodule.finrank_le` and `Framework.finrank` ($6 \le 3 \cdot 4 / 2$).
  *Found:* round 1 task 5.4.
  *Disposition:* reported (`notes/Prose-report.md`, S12); round 3: `IsInfinitesimallyRigid`'s
  docstring and `Framework.lean`'s header state the divergence (task 25.1).
- **F-026** · S · `lem:span-range-rigidityRow` (`laman-theorem.tex`): the statement assumes $V$
  finite, which its pin `span_range_rigidityRow` does not: it takes only `[Finite G.edgeSet]`. The
  statement is weaker than the pin, as in `F-015`.
  *Evidence:* read (the statement of `span_range_rigidityRow`, `RigidityMatroid.lean`).
  *Found:* round 1 task 5.7.
  *Disposition:* done (`40e1f4c8`): the statement asks only that $G$ have finitely many edges, as
  its pin.
- **F-027** · S · `lem:isSparse-of-rowIndependent-two` (`laman-theorem.tex`): the statement assumes
  $V$ finite, which its pin `isSparse_of_edgeSetRowIndependent_dim_two` does not (it takes no
  finiteness; the sets of at least three vertices it quantifies over are finite). The statement is
  weaker than the pin, as in `F-015` and `F-026`.
  *Evidence:* read (the statement of `isSparse_of_edgeSetRowIndependent_dim_two`, and the body of
  `EdgeSetRowIndependent`, `RigidityMatroid.lean`).
  *Found:* round 1 task 5.8.
  *Disposition:* done (`40e1f4c8`): the statement takes no finiteness, as its pin.
- **F-028** · S · five nodes of `rigidity-matroid.tex`'s *Lifting row-independence through
  Henneberg moves*: `lem:typeI-rowIndependent-extend`, `lem:typeI-rowIndependent-lift`,
  `lem:pendant-rowIndependent-lift`, `lem:typeII-rowIndependent-extend` and
  `lem:edgeSet-rowIndependent-iso` assume their vertex sets finite, which their pins
  (`typeI_edgeSetRowIndependent_extend`, `typeI_edgeSetRowIndependent_lift`,
  `typeI_pendant_edgeSetRowIndependent_lift`, `typeII_edgeSetRowIndependent_extend`,
  `EdgeSetRowIndependent.iso`) do not. Each statement is weaker than its pin, as in `F-015`. The
  other two pins of the subsection, `EdgeSetRowIndependent.eventually` and
  `typeII_edgeSetRowIndependent_lift`, take `[Finite V]` as their statements do.
  *Evidence:* read (the seven statements, `MatroidIdentification.lean` and `RigidityMatroid.lean`,
  whose only section variable is `{V : Type*}`).
  *Found:* round 1 task 5.9.
  *Disposition:* done (`40e1f4c8`): the five statements are for graphs on any sets, as their pins;
  the subsection's other two keep $V$ finite, as theirs do.
- **F-031** · S · `lem:exists-isTightOn-of-insert-not-sparse` (`count-matroid.tex`): the statement
  assumes $V$ finite, which its pin `IsSparse.exists_isTightOn_of_insert_not_sparse` does not (its
  only section variable is `{V : Type*}`; the tight set it produces is a finite set). The statement
  is weaker than the pin, as in `F-015`. The chapter's other seven pins take `[Finite V]`, as their
  statements say.
  *Evidence:* read (the statement, `Sparsity.lean`; `#check` in a `lake lean` scratch file).
  *Found:* round 1 task 5.11.
  *Disposition:* done (`40e1f4c8`): the statement is for a graph on any set $V$, and says so against
  the section's lead.
- **F-034** · S · `lem:pebble-game-invariants` (`pebble-game.tex`): the statement assumes $V$
  finite and $\ell < 2k$, and states all four invariants for a vertex $v$ and a set $V'$ with
  $\ell \le k|V'|$. Its five pins (`Reachable.out_le`, `Reachable.peb_add_out_eq`,
  `Reachable.pebOn_add_span_add_outOn`, `Reachable.pebOn_add_outOn_ge`, `Reachable.span_add_le`)
  assume neither of the first two (the section's variables are `{V : Type*} [DecidableEq V]` and
  `{k ℓ : ℕ}`); (1) and (2) hold for every vertex and every finite $V'$, and only (3) and (4) take
  $\ell \le k|V'|$. The statement is weaker than the pins. Task 5.13's prose after `def:tryAddEdge`,
  which needs $\mathrm{out}_D \le k$ without $\ell < 2k$, cites the proof of (1) instead.
  *Evidence:* read (the five statements and the section variables of `PebbleGame/Basic.lean`).
  *Found:* round 1 task 5.13.
  *Disposition:* done (`40e1f4c8`): the statement is on any $V$ at any $k$ and $\ell$, (1)–(2) for
  every vertex and finite $V'$, (3)–(4) each at $\ell \le k|V'|$; the four sentences that cited an
  invariant's proof for want of its hypotheses, the one after `def:tryAddEdge` among them, cite
  the invariant.
- **F-036** · S · `thm:pebble-game-soundness` (`pebble-game.tex`): the statement assumes
  $\ell < 2k$, which its pin `runPebbleGameWith_sound` does not take. The statement is weaker than
  the pin. Neither its proof nor that of `lem:pebble-game-invariants` uses $\ell < 2k$, and task
  5.14's proof says so. Also, the old statement's "an edge list whose Sym2-image is $E(G)$" did not
  say that each edge appears once, which the pin requires (`hpairwise`). Task 5.14's statement says
  it, as `def:runPebbleGame` does for the pebble game on $G$; so does the second part of
  `lem:runPebbleGame-underline-eq`.
  *Evidence:* read (the statement and body of `runPebbleGameWith_sound`, `Correctness.lean`;
  `#check` in a `lake lean` scratch file).
  *Found:* round 1 task 5.14 (the open's diagnosis saw the first half).
  *Disposition:* done (`40e1f4c8`): the statement takes no bound on $\ell$ but in its "In
  particular", for the pebble game on $G$, which `def:runPebbleGame` defines for $\ell < 2k$;
  the proof's remark says so.
- **F-037** · S · `lem:workhorseWitness-certifies` (`pebble-game.tex`): the statement takes a finite
  simple graph $G$ on $V$. Its pin `WorkhorseWitness.certifies_against` assumes only that $G$ has
  finitely many edges (`[Fintype G.edgeSet]`; nothing on $V$). The statement is weaker than the
  pin, as in `F-026`. Task 5.13's prose after `def:workhorseWitness` says the same.
  *Evidence:* read (the statement of `certifies_against`, `Correctness.lean`; `#check`).
  *Found:* round 1 task 5.14.
  *Disposition:* done (`40e1f4c8`): the statement, and the sentence after `def:workhorseWitness` that
  restates it, take a graph with finitely many edges.
- **F-038** · S · `def:blockingWitness` (`pebble-game.tex`): task 5.13 (`db7ff7d6`) changed the
  content of this unpinned definition. It said that a blocking witness is a finite $V' \subseteq V$
  with $|E_G[V']| > k|V'| - \ell$, and "Equivalently, $G$ is not $(k, \ell)$-sparse on $V'$". The
  two differ when $\ell > k|V'|$: then the first holds (with integer subtraction) and the second
  fails, since sparsity bounds only the sets with $\ell \le k|V'|$. The definition now also asks
  $\ell \le k|V'|$: the second sentence's reading, and what the reject verdict carries
  (`PebbleGameResult.reject`'s `h_size` and `h_lt`). The coordinator checked and accepted the
  change; it is recorded because the hygiene rule sends a change of statement content to the PI.
  *Evidence:* read (the definition at `db7ff7d6^` and at `db7ff7d6`; `PebbleGameResult`,
  `Correctness.lean`).
  *Found:* round 1 task 5.13; filed by task 5.14 at the coordinator's request.
  *Disposition:* reported (`notes/Prose-report.md`, S33).
- **F-041** · S · `thm:pebble-game-correct` (`pebble-game.tex`): the statement says more than its
  pin. `runPebbleGameWith_correct` states only the equivalence: $G$ is $(k, \ell)$-sparse if and
  only if the game on the list returns a partial orientation. The statement adds (1) that a
  returned $D$ has $\underline{D} = E(G)$, and (2) that the set of a returned failure witness is a
  blocking witness for $G$, and an "in particular" for the pebble game on $G$. (1) is the pins of
  `lem:runPebbleGame-underline-eq` and `thm:pebble-game-soundness`. (2) is proved inside the pin's
  proof and in the bodies of `runPebbleGame.aux` and `runPebbleGameExec.aux`, from
  `runPebbleGameWith_witness_bridges` and `certifies_against` (`F-044`), but no declaration states
  it. The old statement ("Concretely: (1) … (2) …") said both, and task 5.15 kept them. As in
  `F-036`, the old "edge list whose Sym2-image is $E(G)$" did not say that each edge appears once,
  which the pin requires (`hpairwise`); the statement now says it. Finiteness and $\ell < 2k$
  match the pin.
  *Evidence:* read (the statement and body of `runPebbleGameWith_correct`, `Correctness.lean`, and
  the two `aux` bodies, `Correctness.lean` and `Exec.lean`; `#check` of the four pins of task 5.15
  through the Lean server).
  *Found:* round 1 task 5.15.
  *Disposition:* reported (`notes/Prose-report.md`, S25).
- **F-042** · S · `def:pebbleGameResult` (`pebble-game.tex`): the definition takes a finite simple
  graph $G$ on $V$. Its pin `PebbleGameResult` takes only `[DecidableEq V]` and
  `[Fintype G.edgeSet]`, so $G$ need only have finitely many edges, as in `F-037`. The definition
  is narrower than the pin. The other three pins of task 5.15 take `[Fintype V]` and `ℓ < 2 * k`,
  as their statements say (`runPebbleGameExec_isAccept_iff` also `[LinearOrder V]`).
  *Evidence:* read (`#check @PebbleGameResult`: the `[Fintype V]` of `Correctness.lean`'s
  `Verdict` section is not among its binders).
  *Found:* round 1 task 5.15.
  *Disposition:* done (`40e1f4c8`): the definition takes a graph with finitely many edges, as its
  pin.
- **F-046** · S · `def:outListSorted`, `lem:mem-outListSorted`, `def:edgeListSorted`,
  `lem:mem-edgeListSorted` (`executable.tex`): the two out-neighbour nodes assume $V$ finite, and
  the two edge-list nodes take a finite simple graph $G$. The pins `outListSorted` and
  `mem_outListSorted` take only `[DecidableEq V]` and `[LinearOrder V]`; `edgeListSorted` and
  `mem_edgeListSorted` take `[LinearOrder V]` and `[Fintype G.edgeSet]`, so $G$ need only have
  finitely many edges, as in `F-042`. The four statements are narrower than their pins. The other
  four pins of task 5.16 take `[LinearOrder V]` and `[Fintype V]`, and all but
  `instDecidableIsLaman` take $\ell < 2k$, as their statements say.
  *Evidence:* read (`#check` of the eight pins through `lake lean`, and their bodies in
  `PebbleGame/Exec.lean`).
  *Found:* round 1 task 5.16.
  *Disposition:* done (`40e1f4c8`): `def:outListSorted` is on any set with a linear order, and
  `def:edgeListSorted` for a graph with finitely many edges; the two membership lemmas follow
  their definitions.
- **F-048** · S · `def:body-hinge-framework`, `thm:body-hinge-tay` (`body-hinge.tex`): the
  definition gives each hinge an $(n-2)$-dimensional affine subspace, "equivalently" a
  $(\delta-1)$-dimensional space of bar coordinates dual to it. Its pin `Graph.BodyHingeFramework`
  holds only a multigraph and an arbitrary two-extensor coordinate for each of the $\delta - 1$
  copies of every edge, with no hinge, so the definition is stronger than its pin. The main result
  `body_hinge_tay` is therefore the bar-bundle statement, and its existence direction produces bar
  coordinates, not hinges. `generic-lift.tex` calls `thm:body-hinge-tay` "the bar-bundle reduction
  statement" and proves the hinge form at generic hinge points
  (`cor:bodyhinge-generic-tree-packing`); `formalization.yaml` and `intro.tex` describe
  `body_hinge_tay` as the definition reads.
  *Evidence:* read (the structure `Graph.BodyHingeFramework` and the statement of
  `body_hinge_tay`, `BodyBar/BodyHinge.lean`; `notes/Phase16.md` *Decisions*).
  *Found:* round 2 task 1.
  *Disposition:* reported (`notes/Prose-report.md`, S11).
- **F-049** · S · `lem:rank-rotation-semicont` (`rigidity-matrix.tex`): the statement claims KT
  Lemma 5.2 as the lower-semicontinuity of rank along a panel rotation, then a monotonicity form:
  if $\operatorname{span} C(p(e)) \subseteq \operatorname{span} C(p'(e))$ at every edge, then
  $Z(G,p') \subseteq Z(G,p)$. Its pins `infinitesimalMotions_mono_of_span_le` and
  `finrank_infinitesimalMotions_le_of_span_le` assume the reverse inclusion, under which that
  conclusion holds; under the stated one it fails (a hinge with $C = 0$ welds its two bodies, one
  with $C \ne 0$ does not). Neither pin is KT Lemma 5.2, which perturbs a realization with one
  parallel pair of panels into a nonparallel one without losing rank (KT p. 669); `meet.tex`'s
  formalization note gives that role to
  `PanelHingeFramework.hasGenericFullRankRealization_of_rigidOn_ofNormals`.
  *Evidence:* read (the two pins' statements and bodies, `Molecular/RigidityMatrix/Basic.lean`;
  KT 2011 pp. 668–669, in `.refs/`).
  *Found:* round 2 task 1.
  *Disposition:* done (`3456d6a7`): the statement is its pins' inclusion, retitled, with a short proof
  and note; the rotation and KT Lemma 5.2 left it. The passage before
  `lem:generic-realization-of-rigid` states KT Lemma 5.2 (KT p. 669; a special case of JJ 2010
  Lemma 7.1, p. 584) and the formal steps that replace it: that lemma for infinitesimally rigid
  realizations, and `lem:rank-polynomial-of-le-finrank` in general (KT's input with the two equal
  panels joined by an edge is a degenerate hinge in the project's carrier). The subsection's lead
  and the six
  `\cref`s follow: `case-ii.tex` and `case-iii.tex` cite KT's pages for the rotation, `case-i.tex`
  the passage, `case-iii.tex` the lemma where two frameworks have equal hinge spans and
  `lem:rank-polynomial-of-le-finrank` for the minor in $t$, `molecule-modelling.tex` the inclusion
  both ways.
- **F-051** · S · `thm:matroid-partition-rank` (`matroid-union.tex`): the statement gives the rank
  of every $X \subseteq E$ in the union of any finite family $M_1, \dots, M_k$, and the
  independence criterion for any family. Its pins prove less: `Matroid.Union_rank_eq` gives the
  rank for any family at $X = E$ only, and `Matroid.Union_pow_rk_eq` the rank of every $X$ when
  all $M_j$ are one matroid. The criterion is proved only in that case, by the unpinned
  `Matroid.Union_pow_indep_iff_count` (`F-052`), the only case used later. Task 2.1 kept the
  statement and says this in a formalization note after the proof.
  *Evidence:* read (the three statements and bodies, `Matroid/Constructions/Union.lean`).
  `adjMap_rk_eq` with `sum'_rk_eq_rk_sum` would give the family form at every $X$, but no
  declaration states it, and none states the criterion for a family.
  *Found:* round 2 task 2.1.
  *Disposition:* reported (`notes/Prose-report.md`, S24).
- **F-058** · S · `thm:tay-witness` (`body-bar.tex`) and `thm:body-hinge-tay` (`body-hinge.tex`):
  both statements assume $d \ge 2$, and their pins `Graph.BodyBarFramework.tay_witness` and
  `Graph.BodyHingeFramework.body_hinge_tay` hold for every $d$, so the statements are weaker than
  the pins. `prop:tay-witness-exists`, `lem:tay-isSparse-of-independent` and
  `lem:edge-multiply-sparse` assume nothing on $d$, and the proof of `lem:edge-multiply-sparse`
  applies `thm:tay-witness` to $(D-1)\cdot G$ for every $d$. Task 2.3 kept every hypothesis.
  *Evidence:* read (the five pins' statements, `BodyBar/TayTheorem.lean` and `BodyHinge.lean`).
  *Found:* round 2 task 2.3.
  *Disposition:* done (`40e1f4c8`): both statements and `intro.tex`'s summary are at every $d$, and
  `deficiency.tex`'s sentence that applied `thm:tay-witness` "when $d \ge 2$" drops the bound; no
  row states one.
- **F-060** · S · `lem:case-III-claim612-extensor-span` (`algebraic-induction/case-iii.tex`): the
  statement says that the $D$ two-extensors $\bar p_i \vee \bar p_j$ of $k+2$ linearly independent
  vectors of $K^{k+2}$ span $\bigwedge^k K^{k+2}$, and calls them $k$-extensors. Its pin
  `span_omitTwoExtensor_eq_top` is about the omit-two extensors, each the join of the other $k$
  vectors; the two families coincide as sets only at $k = 2$. The proof applies KT Lemma 2.1 in
  the omit-two form, so it proves the pin's statement, not the node's.
  *Evidence:* read (the pin's statement, `Molecular/RigidityMatrix/Claim612.lean`).
  *Found:* round 2 task 2.4.
  *Disposition:* done (`3456d6a7`): the title and statement are the omit-two extensors $E_{ij}$, with
  the six joins at $d = 3$ as their case; the proof and the note follow, and
  `lem:case-III-chain-discriminator`'s citation names the lemma, not its proof.
- **F-079** · S · `lem:rk-within-parts` (`deficiency.tex`): the statement bounds $r(Y) + |P|$
  for the set $Y$ of all edges of $\tilde G$ whose ends lie in one part of $P$. Its pin
  `rk_cycleMatroid_within_parts_le` proves the bound for every $Y \subseteq E(\tilde G)$ whose
  edges have both ends in one part, so the statement is weaker than the pin. The formal proof of
  `thm:def-eq-corank` uses the general form, at the optimal set $Y_0$ (the private
  `rk_add_numParts_componentLabel`). Task 2.10 kept the statement and says this in a formalization
  note.
  *Evidence:* read (the statements of both, `Molecular/Deficiency.lean`).
  *Found:* round 2 task 2.10.
  *Disposition:* done (`0b8a78e0`): the statement is the pin's, for every set $Y$ of edges whose ends
  each lie in one part of $P$, the note replaced by a remark naming the two sets its users take;
  `lem:weak-duality`'s proof sets its $Y$, and `thm:def-eq-corank`'s note applies it at $Y_0$.
- **F-083** · S · `lem:circuit-induces-rigid` (`molecular-induction.tex`): the statement says, as KT
  Lemma 3.4 does, that $X - e$ is the union of $D$ edge-disjoint spanning trees on $V(X)$. Its pins
  `circuit_induces_isTight` (the count $|X - e| + D = D\,|V(X)|$) and
  `circuit_induces_isRigidSubgraph` (the rigidity of $G[V(X)]$) do not state it, and no
  declaration applies `isSpanningTreePacking_of_isTight` (`cor:k-spanning-trees`) to a circuit.
  Task 2.11 kept the statement. Its proof derives the partition from the count by
  `cor:k-spanning-trees` and the connectivity count of `lem:deficiency-zero-iff-tree-packing`,
  which no `\uses` names, and a formalization note says that the partition is not formalized.
  *Evidence:* read (the two pins' statements, `Induction/Operations.lean`; the callers of
  `isSpanningTreePacking_of_isTight`).
  *Found:* round 2 task 2.11.
  *Disposition:* reported (`notes/Prose-report.md`, S23).
- **F-084** · S · `lem:reduction-step` (`molecular-induction.tex`): the statement says that
  contracting a proper rigid subgraph (`lem:contraction-minimality`) carries a minimal $0$-dof-graph
  to a smaller one. Its pin for that branch, `Graph.contraction_isMinimalKDof` (also
  `lem:contraction-minimality`'s), states the deficiency and minimality of the matroid
  $M(\tilde G)/E(\tilde H)$, not of the graph $G/E(H)$. The graph form is
  `Graph.rigidContract_isMinimalKDof` (`lem:rigidContract-isMinimalKDof`, `case-i.tex`), which
  assumes $D \ge 2$ and that the new vertex lies in $H$. `lem:contraction-minimality`'s statement
  claimed the graph form too, beside "stated on the matroid side"; task 2.11 states its pin's
  matroid form and gives the graph form after it, citing `lem:rigidContract-isMinimalKDof`, as
  task 2.4 moved a gloss to the node whose pin proves it. Task 2.15 rewrites `lem:reduction-step`;
  the statement of `lem:case-I` (`case-i.tex`, round 3) also cites `lem:contraction-minimality`
  for the graph form. Task 2.15 states the pin's matroid form at $k = 0$ as part (ii) of
  `lem:reduction-step`, and after the node, with `lem:reduction-measure`, the fewer vertices and
  the graph form (`lem:rigidContract-isMinimalKDof`).
  *Evidence:* read (the statements of the three declarations, `Induction/Contraction.lean`).
  *Found:* round 2 task 2.11.
  *Disposition:* reported (`notes/Prose-report.md`, S30).
- **F-086** · S · `lem:acyclic-insert-vfiber` and `lem:packing-move` (`molecular-induction.tex`):
  both statements take $v$ to be a vertex of degree two of $G$, the setting in which
  `lem:balanced-forest-packing` uses them. Their pins `acyclicSet_insert_vfiber_of_not_inc` and
  `exists_packing_move_of_not_inc` assume nothing about the degree: at any vertex $v$, a forest of
  $\tilde G$ with no edge at $v$ stays a forest when an edge from $v$ to some $w \neq v$ is added.
  Each statement is weaker than its pin, as in `F-015`. Task 2.12 kept the degree, and the first
  proof says that it is not used.
  *Evidence:* read (the two statements, `Induction/ReducibleVertex.lean`).
  *Found:* round 2 task 2.12.
  *Disposition:* reported (`notes/Prose-report.md`, S39).
- **F-101** · S · `thm:minimal-kdof-reduction` (`molecular-induction.tex`): the statement claims KT
  Theorem 4.9 as KT state it, a sequence of minimal $0$-dof-graphs from $G$ to the two-vertex
  double edge, each obtained from the one before by splitting off or by contracting a proper rigid
  subgraph. Its pin `minimal_kdof_reduction` states only an induction principle, and no declaration
  states the sequence. The sequence follows from the pin with the two-vertex classification
  (`isMinimalKDof_ncard_le_two_trichotomy`) and the graph form of KT Lemma 3.5
  (`rigidContract_isMinimalKDof`, $D \ge 2$). At the open the statement gave the sequence and
  called the principle "the form the formalization states". Task 2.16 kept the claim as part (i),
  states the principle as part (ii), derives (i) from (ii) in the proof, and says in a
  formalization note that (i) is not formalized.
  *Evidence:* read (the statements of the three declarations).
  *Found:* round 2 task 2.16.
  *Disposition:* reported (`notes/Prose-report.md`, S22).
- **F-102** · S · `lem:case-cut-edge-realization-gp` (`molecular-induction.tex`): the statement
  assumes that every smaller simple minimal $k'$-dof-graph has a generic full-rank realization. Its
  pin `case_cut_edge_realization_gp_gen` also assumes that every smaller minimal $k'$-dof-graph has
  a nondegenerate-hinge panel realization: its hypothesis is the conjunction that
  `theorem_55_minimalKDof_k_all_k` inducts on, which passes it on whole. The proof uses only the
  first conjunct, so the statement is stronger than the pin; dropping the second conjunct from the
  pin would align them. Task 2.16 kept the statement, with a formalization note.
  *Evidence:* read (the pin's statement and body, `Molecular/AlgebraicInduction/Theorem55.lean`,
  and its call in `theorem_55_minimalKDof_gen`).
  *Found:* round 2 task 2.16.
  *Disposition:* done (task 12): the pin's hypothesis is the first conjunct, the statement's
  (`F-104`); the note's sentences on the second are gone. Before: reported
  (`notes/Prose-report.md`, S17).
- **F-107** · S · `lem:chain-cycle-dichotomy` (`molecular-induction.tex`): at the open the
  statement also said that both branches occur: for $d \ge 4$, minimal $0$-dof cycle graphs on
  $4 \le m \le d$ vertices have no chain of length $d$. No pin states this. `isKDof_zero_of_cycle`
  gives only that such a cycle is a $0$-dof-graph, and no declaration states that it is minimal,
  that it has no proper rigid subgraph, or that it has no chain. Task 2.17 moved the sentence out
  of the statement, as principle B moves an essentiality remark, to the prose after the lemma.
  That paragraph keeps the claim, for every $d \ge 3$ and $3 \le m \le d$, proves it, and says
  that under the bound $|V(G)| \ge 4$ of `lem:chain-data-extract` the cycle branch occurs
  exactly when $d \ge 4$. The dichotomy itself keeps KT's strength.
  *Evidence:* read (the three pins' statements).
  *Found:* round 2 task 2.17.
  *Disposition:* reported (`notes/Prose-report.md`, S30).
- **F-112** · S · `def:meet` (`meet.tex`): at the open the definition also said that the meet of
  the supporting extensors of two subspaces is the supporting extensor of their intersection, and
  that for $a = b = 1$ the meet of two hyperplane normals supports their codimension-$2$
  intersection. No declaration states a property of `meet`. Task 2.18 moved the sentence to prose
  after the definition, as principle B moves a definition's consequences. That prose keeps the
  claim and proves it, for subspaces $X$ and $Y$ with $X + Y = V$, from the formalized formula for
  $*e_S$ and transformation law of the complement isomorphism. The formalization proves the case of
  two hyperplanes in the form $*(n_A \vee n_B)$, for every $d$
  (`extensor_join_proportional_complementIso_meet`), and not the general case.
  *Evidence:* read (a `grep` for `meet` in the Lean; the statements of the cited declarations).
  *Found:* round 2 task 2.18.
  *Disposition:* reported (`notes/Prose-report.md`, S30).
- **F-113** · S · `lem:complement-iso-decomposable-wedge-perp` (`meet.tex`): the statement says that
  $*(n_1 \vee n_2)$ is orthogonal to every $2$-extensor $n \vee c$ with $n \in \{n_1, n_2\}$, for
  linearly independent $n_1, n_2$. The second and third pins state only $n = n_1$, and assume no
  independence; the case $n = n_2$ follows from the first pin by alternation, which the formal proof
  of `complementIso_smul_eq_extensor_join` does inline. Task 2.18 kept the statement, with a note.
  *Evidence:* read (the three pins' statements; the body of `complementIso_smul_eq_extensor_join`).
  *Found:* round 2 task 2.18.
  *Disposition:* done (`5955454a`): part (2) states $Y = n_1 \vee c$ for any $n_1, n_2, c$, as the
  second and third pins do; the case $n_2$ is at the end of the proof, by the repeated vector and
  part (1), and the note says that no pin states it; the proof of
  `lem:case-III-claim612-line-in-panel-union` cites part (2) for $n_1$ and that end for $n_2$.
- **F-115** · S · `lem:cycle-realization` (`algebraic-induction/case-i.tex`): the statement is KT
  Lemma 5.4 at KT's range, a cycle graph on $3 \le m \le D$ vertices (KT p. 670). Its pin
  `PanelHingeFramework.cycle_realization` assumes `cy.m ≤ n + 1` beside
  `bodyBarDim n = screwDim k`, so $n$ is the dimension $d$ and the pin covers $3 \le m \le d + 1$,
  fewer vertices than $D = \binom{d+1}{2}$ once $d \ge 3$. The formalization note after the lemma
  gives the formalized range as $m \le d$, one less than the pin's. KT's one use, in the proof of
  their Lemma 6.13 (p. 692), needs cycles of length at most $d$.
  *Evidence:* read (the pin's statement and the step `hnk` of its body,
  `Molecular/AlgebraicInduction/CaseIII/Arms.lean`; KT 2011 pp. 670 and 692, `.refs/`).
  *Found:* round 3 task 1.
  *Disposition:* done (`c2cfcd08`): the statement takes the pin's range $3 \le m \le d + 1$, and the
  note gives KT's range and both of KT's uses, each inside it: the triangle in the proof of their
  Lemma 6.7(i) (p. 677), which this entry missed, and the cycles on at most $d$ vertices in that of
  Lemma 6.13 (p. 692). `panel-layer.tex`'s `\cref` says the node's range.
- **F-116** · S · `lem:case-I` (`algebraic-induction/case-i.tex`): the statement is KT eq. (6.3)'s
  rank addition: for a minimal $k$-dof-graph $G$ with a proper rigid subgraph $H$, $(G,p)$
  attains the target rank if and only if $\operatorname{rank} R(G,p) = D(|V(H)|-1) +
  \operatorname{rank} R(G/E(H), p_2)$. No pin mentions the contraction, minimality or that
  identity. The three pins are block-pin criteria for any framework and nonempty $s$: when every
  motion is constant on $s \subseteq t$, rigidity on $t$ is $Z_s \le Z_t$
  (`isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`); and under the bound
  $\dim Z \le D + \dim Z_s$, the rank hypothesis at $k'$ is $\dim Z_s = k'$
  (`rankHypothesis_iff_finrank_pinnedMotionsOn` and its panel form, both outside every main
  result's closure). Both `lem:case-I` and `lem:case-I-realization` are crux nodes of the
  exposition ledger's KT eq. (6.3) entry; the second's proof argues the rank addition in full.
  *Evidence:* read (the three statements, `Molecular/AlgebraicInduction/Pinning.lean` and
  `PanelHinge.lean`); measured (dead pins, `scripts/blueprint-deps.py --label lem:case-I`, at
  `ef57b401`).
  *Found:* round 3 task 1.
  *Disposition:* reported (`notes/Prose-report.md`, S19); round 2: `rem:case-I-kt-steps` says that
  the formal proof uses neither the identity nor its forms with the block pin, and counts rows
  instead (`e6f1e425`).
- **F-117** · S · `lem:genericity-device` (`algebraic-induction/genericity-and-count.tex`): the
  statement says that each locus $\{p : \operatorname{rank} R(G,p) \ge r\}$ is Zariski-open, so
  the rank is lower semicontinuous and maximal on a dense set, and dually that $\dim Z(G,p)$ is
  minimized generically. Its pins state less. `exists_good_realization` gives a point $p$ with
  $\#s + \dim Z(F\,p) \le D|V|$ when the rows indexed by $s$ are independent at $p_0$; its own
  hypotheses at $p_0$ already give that bound at $p = p_0$. `exists_good_realization_const` gives
  the bound at one framework. The open-locus form is the pin of
  `lem:rank-polynomial-of-le-finrank`, `exists_rankPolynomial_of_le_finrank_linking`: a
  polynomial, nonzero at $q_0$, off whose zeros the rank bound holds.
  *Evidence:* read (the three statements, `Molecular/AlgebraicInduction/GenericityDevice.lean` and
  `CaseI.lean`).
  *Found:* round 3 task 1.
  *Disposition:* done (`1b46edc6`): the statement made true, at nondegenerate hinges (`3456d6a7`,
  `F-149`), and the node repinned on `exists_rankPolynomial_of_le_finrank_linking`, its note saying
  which clauses the pin proves and which are the proof's (`1b46edc6`).
- **F-121** · S · `prop:rigidity-matrix-prop11` (`algebraic-induction/panel-layer.tex`): the
  statement is KT Proposition 2.3's rank formula, Jackson and Jordán's Theorem 6.1, at a generic
  panel-hinge realization with nondegenerate hinges. Its pin `rigidityMatrix_prop11` takes any
  body-hinge framework with every supporting extensor nonzero, assumes the generic bound
  $\dim Z(G,p) \le D + \operatorname{def}(\tilde G)$ (`hgen`), and closes by `omega` from the
  genericity-free bound (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`). No pin shows
  that a generic realization meets `hgen`: the formalization has no generic realization in the
  sense of `def:dof-generic` (which carries no `\leanok`), and the pin reaches none of the nodes
  the proof cites for it. Its callers (`thm:theorem-55-6-genuine`, `thm:theorem-55-6-multigraph`,
  `cor:theorem-55-d3-spanning`) prove `hgen` for the realizations they build. The formula at every
  generic realization is formalized in `generic-lift.tex`, for simple spanning graphs on at least
  two bodies (`thm:panel-generic-rank`, `thm:bodyhinge-generic-rank`); no `\uses` edge joins those
  nodes to this one. Task 2.1 kept the statement, and its note says this. The proof now takes the
  lower bound from KT Theorem 5.5 and the maximality of a generic rank, so the statement's edge to
  `lem:genericity-device` has no sentence behind it (`F-118`).
  *Evidence:* read (the statement and body of `rigidityMatrix_prop11`,
  `Molecular/AlgebraicInduction/PanelHinge.lean`); measured (`scripts/blueprint-deps.py --label
  prop:rigidity-matrix-prop11` at `efa7ed2b`: `thm:theorem-55`, `lem:motions-mono-of-graph-le`,
  `def:dof-generic` and `lem:genericity-device` unbacked).
  *Found:* round 3 task 2.1.
  *Disposition:* reported (`notes/Prose-report.md`, S18).
- **F-122** · S · `def:panel-hinge-framework`, `def:hinge-coplanar`, `thm:molecular-conjecture`
  (`algebraic-induction/panel-layer.tex`): the structure `PanelHingeFramework` records, for every
  edge label, an ordered pair of bodies (`ends`), and computes the hinge from their normals;
  nothing ties the pair to the ends of the edge. So `IsHingeCoplanar F`
  (`∃ P, P.toBodyHinge = F`) holds whenever each hinge of `F` is the meet of the panels of some
  two bodies, not necessarily its ends (for instance, whenever every hinge is zero). That is
  broader than KT's hinge-coplanarity (KT p. 648), and the predicate has no Lean consumer. And the
  panel side of `PanelHingeFramework.molecular_conjecture`, `∃ Q, Q.graph = G ∧` (every hinge
  nonzero) `∧` (rigid), states no condition on `Q.ends`, so it asserts less than a rigid
  panel-hinge realization of $G$. The link-recording form is proved
  (`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, the second pin of
  `thm:theorem-55-6-genuine`). Task 2.1 states `def:panel-hinge-framework` with the edges' ends,
  as the round decided, and `fmlnote:panel-hinge-nondegenerate` and the note after
  `def:hinge-coplanar` say that the formal selector is unconstrained.
  *Evidence:* read (the structure `PanelHingeFramework`, `toBodyHinge` and `IsHingeCoplanar`,
  `Molecular/AlgebraicInduction/PanelHinge.lean`; the statements of `molecular_conjecture` and
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, `Theorem55.lean`; a `grep` for
  `IsHingeCoplanar`).
  *Found:* round 3 task 2.1.
  *Disposition:* reported (`notes/Prose-report.md`, S2); round 1: the molecular conjecture's scope
  stated (its panel side places no condition on the selector, so its body-hinge to panel-hinge
  direction concludes less than a panel-hinge realization) on its `main_results` row, its and JJ
  2008's `alignment` entries, README, the home page, `intro.tex` and ROADMAP §23, beside the
  link-recording form, which gives the panel side with each hinge at its edge's ends by the same
  argument (a `lake lean` witness, script not retained: `molecular_conjecture`'s proof with
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` in place of the genuine form proves the
  iff with the link conjunct on the panel side) (b0eb63eb); round 3: in `CaseI.lean` and
  `CaseII.lean`, the docstrings' sentences on what a selector records and what `ofNormals` gives
  back (the transports' selector swap, `Q = ofNormals Q.graph Q.ends …`, the last conjunct of
  `HasGenericFullRankRealization`), kept as they stand, moved to the phase (task 34); and in
  `GenericityDevice.lean` and `Coupling.lean`, the sentences on what a selector gives, on what a
  selector over every edge label asks, and on what `ofNormals`, `ofParam` and `withGraph` give back,
  kept as they stand, moved to the phase (task 34.1); and in `CaseIII/Arms.lean` and
  `Candidate.lean`, the sentences on what `ofNormals` gives at a label (the hinge from the normals
  of the selector's two bodies, which does not read the graph) and what the selector `G.endsOf`
  gives at a link, kept as they stand, moved to the phase (task 35); and in
  `CaseIII/Realization.lean`, the sentences on what `ofNormals` gives at a label (the rows read the
  selector only through the hinge at each link) and on the selector of a generic full-rank
  realization (it gives each link its ends in some order), kept as they stand, moved to the phase
  (task 35.1); and in `CaseIII/Relabel/Basic.lean` and `Arm.lean`, the sentences on what `ofNormals`
  gives at a label of a renamed framework (the hinge from the normals of the two bodies its selector
  gives the label, so that the renaming of the normals cancels that of the selector, and which does
  not read the graph) and on the selectors the renamings carry (each gives each link its ends in
  some order), kept as they stand, moved to the phase (task 35.2); and in
  `CaseIII/Relabel/Chain.lean`, `ChainColumn.lean` and `ForkedArm.lean`, the sentences on what
  `ofNormals` gives at a label (the hinge from the selector and the normals, which does not read the
  graph, so that a block of rows does not depend on it) and on the selectors of the frameworks of a
  chain (each gives each link its ends in some order), kept as they stand, moved to the phase (task
  35.3); and in `PanelHinge.lean`, the sentences that say what the structure's fields mean and what
  `toBodyHinge`, `withNormal`, `ofNormals` and `IsHingeCoplanar` give (the hinges at a body lie in
  its panel), on what `ofNormals` gives at a label (the hinge and the rows do not read the graph)
  and on the selector of a generic full-rank realization (it gives each link its ends in some order,
  and two such selectors agree up to order), kept as they stand (the section on the structure with
  KT's page, p. 648, and without a phase number), moved to the phase (task 36); and in the first
  half of `Theorem55.lean`, the docstrings of `reaim`, `reaimSub`, `reaimSubLink` and their three
  lemmas on motions (steps of `cor:theorem-55-d3-spanning` and of S2's rows), kept as they stand but
  for their leads (`reaim`'s gives a nonzero hinge at every label from general position and
  `x₀ ≠ y₀`, where a link also needs the selector to give it its ends), and the sentences on what
  `ofNormals` gives at a label (the hinge from the selector and the normals, which does not read the
  graph) and on the selectors of generic full-rank realizations (each gives each link its ends in
  some order), kept true, moved to the phase (task 36.1); and in the rest of `Theorem55.lean`, the
  meet model's hinges in the multigraph section's header and the docstrings of
  `theorem_55_6_multigraph` and `molecular_conjecture_multigraph`, moved to the phase (task 36.2);
  and in `Duality.lean`, the panel-hinge framework at the homogenized centres, edge by edge on the
  molecular framework's selector, and what a nonzero hinge at a label means on each side, moved to
  the phase (task 37); and in `Theorem56.lean` and `Modelling.lean`, the selector's conjunct (it
  records a `G`-link on every `G`-link, as the square-graph dictionary needs of the same selector),
  KT Theorem 5.6's realization viewed as `ofNormals G Q₀.ends q₀` at its own normals, and the
  panel-hinge framework on the homogenized poles, which differs from `Q` by a nonzero rescaling of
  each supporting extensor, kept as they stand but for the word "genuine", moved to the phase (task
  37.1); and in `Pencil/MainComponent/Carrier.lean` and `Configuration.lean`, the selector of
  `X0Attains` (it records every link of `G`), what `ofNormals` gives at the configuration points
  (the polar of the point-join framework, the meet of the two polar planes at each label, a hinge
  nonzero exactly when the normals at its ends are independent, and a zero hinge at the plane
  normals where adjacent planes coincide), what `HasCoplanarPanelRealization` asks (a nonzero hinge
  at every label) and that `ends` names the two ends of a link, kept as they stand but for their
  pointers and codes, moved to the phase (task 37.9); and in `Pencil/MainComponent/Flat.lean` and
  `Bridge.lean`, the hinge `ofNormals` gives at a label from the normals of the two bodies its
  selector gives it (`(u, v) = ends e`, under a rescaling of the normals; nonzero in the plane
  framework as adjacent picture points differ), the selector that the chart form of the planar
  case of KT Theorem 5.6 gives (it records every link) and the recorded hinges of the rank along a
  polynomial curve, kept as they stand but for their pointers and codes, and that the chart point
  needs no selector that records a link at every label (the "no total selector" of `Bridge.lean`'s
  *Design* section, folded into its header), moved to the phase (task 37.10); and in
  `Pencil/MainComponent/Cut.lean`, the hinge of an `ofNormals` framework at a recorded link (it
  spans the panel extensor of its two ends, in either orientation), the two selectors recording every
  link in the rank congruence (the row rank reads the selector only up to the orientation of each
  link) and the sides' own selectors carried to `G.endsOf` (its *Design* section, folded into its
  header), kept as they stand but for their pointers and codes, moved to the phase (task 37.11); and
  in `Pencil/MainComponent/Ear.lean`, the hinge of an `ofNormals` framework at a link (the meet at
  the link lies on it, in either orientation) and along a family of links (each the meet at its
  recorded ends, `±` the polar image of the join at the link's ends), kept as they stand but for
  their pointers and codes, moved to the phase (task 37.12); and in
  `Pencil/MainComponent/ContractCurve.lean`, the hinges of `G/H` at the normals (every one nonzero)
  and the rows of the `ofNormals` framework of `G − E(H)` at the collapsed placement (those of `G/H`
  with the column of `r` deleted), kept as they stand, moved to the phase (task 37.13); and in
  `Pencil/MainComponent/EarGen.lean`, the configuration points of ear data as the point function
  `ofNormals` reads (`earConfig`) and the witness's nonzero hinges at the links of `H`, at the labels
  where the selector gives a link (`exists_mvPolynomial_le_finrank_ofNormals_bind`), kept as they
  stand, moved to the phase (task 37.15); and in `Pencil/MainComponent/Short.lean`, the selector of
  `G` relinked at the freed label (`Graph.isLink_update_splitOff`: it orients every link of the
  split-off; and the header's bullet on it) and the ear datum of the base data at which `H`, with
  the selector relinked, has nonzero hinges and its target rank (`Graph.exists_earBase_splitOff`),
  kept as they stand but for their leads, moved to the phase (task 37.16); and in
  `Pencil/MainComponent/Orbit.lean`, the comment that the frameworks of `G` read the hinges of `G₁`
  on `V₁` (`Graph.X0Attains.of_openEar_two_of_splitOff`, `hCG`: at a link of `G[V₁]` the framework
  of `G` at every ear datum and that of `G₁`, whose selector is that of `G` relinked at `e 1`, give
  the same hinge), kept as it stands, moved to the phase (task 37.17); and in
  `Pencil/MainComponent/SplitOff.lean`, the hinges of an `ofNormals` framework at the special
  position (those at `a − x 0` and `x 0 − b` nonzero multiples of the hinge of `G″` at `a − b`,
  `Graph.finrank_span_rigidityRows_splitOff_special`) and the comment that the hinges of the special
  configuration are nonzero (`Graph.X0Attains.of_splitOff`), kept as they stand, moved to the phase
  (task 37.18).
- **F-124** · S · `lem:generic-yields-genuine-hinge` (`algebraic-induction/panel-layer.tex`): the
  statement gives every multigraph with at least two vertices that has a generic full-rank
  realization a nondegenerate-hinge panel realization. Its pin `hasPanelRealization_of_generic`
  assumes `[G.Loopless]` and returns the generic framework itself, whose hinge at a loop is
  $C(n_u, n_u) = 0$. The claim holds with loops, since a loop gives no row and its hinge can be
  replaced by a nonzero extensor in its panel, and the pin's three callers apply it to simple
  graphs. Task 2.2 kept the statement; its proof treats loops, and its note says the pin assumes
  none.
  *Evidence:* read (the statement and body of `hasPanelRealization_of_generic`,
  `Molecular/AlgebraicInduction/GenericityDevice.lean`; its callers in `Theorem55.lean`).
  *Found:* round 3 task 2.2.
  *Disposition:* reported (`notes/Prose-report.md`, S16).
- **F-125** · S · `cor:theorem-55-d3-spanning` (`algebraic-induction/panel-layer.tex`): the
  statement gives a simple minimal $0$-dof-graph at $d = 3$ a generic full-rank realization with
  $\dim Z(G,p) = D$. Its pin `rankHypothesis_deficiency_of_theorem_55_d3` takes the generic
  realization as a hypothesis (the conclusion of `thm:theorem-55-d3-instance`, a `\uses`'d node)
  and concludes only `∃ Q, Q.graph = G ∧ Q.toBodyHinge.RankHypothesis (G.deficiency 3)`: no general
  position, no condition on `Q.ends`, and no nonzero hinge. A framework whose normals are all equal
  meets that conclusion for every spanning $0$-dof-graph $G$, without the hypothesis: each hinge
  is zero and welds its ends, and a $0$-dof-graph is connected. The construction's nonzero hinges (`hC`) are not exported. The pin has
  no caller. Task 2.2 kept the statement, and the note after the proof says this (`F-122`).
  *Evidence:* read (the statement and body, `Molecular/AlgebraicInduction/Theorem55.lean`;
  `RankHypothesis`, `Pinning.lean`); measured (`scripts/blueprint-deps.py --label
  cor:theorem-55-d3-spanning` at `db237dfd`, dead pin).
  *Found:* round 3 task 2.2.
  *Disposition:* reported (`notes/Prose-report.md`, S2).
- **F-128** · S · `thm:theorem-55-6`, `thm:theorem-55-6-d3`, `thm:theorem-55-6-genuine`
  (`algebraic-induction/panel-layer.tex`): the statements give a simple graph a panel-hinge
  realization at the target rank (with nondegenerate hinges in the third), whose hinge at each edge
  is, since task 2.1, the meet of the panels of the edge's ends. Their pins
  `rankHypothesis_of_theorem_55_gen`, `rankHypothesis_of_theorem_55_d3` and
  `rankHypothesis_genuine_of_theorem_55_gen` conclude `∃ Q, Q.graph = G ∧ …` with no condition on
  `Q.ends`, and the framework they build (`reaimSub`) gives each edge of $G$ outside the minimal
  subgraph $G'$ the selector pair $(x_0, y_0)$, so its hinge there is $C(n_{x_0}, n_{y_0})$
  (`F-122`'s gap, at KT Theorem 5.6). The second pin of `thm:theorem-55-6-genuine`
  (`reaimSubLink`) and the first of `thm:theorem-55-6-rows` record the ends;
  `molecular_conjecture` calls the first form. At deficiency zero the first two pins' conclusion
  is also met by the framework with all normals zero, for every spanning $0$-dof-graph (as `F-125`
  found for the $d = 3$ corollary); the blueprint statements allow degenerate hinges too. Task 2.3
  kept the statements, and their notes say this.
  *Evidence:* read (the statements and bodies, `reaimSub` and `reaimSubLink`,
  `Molecular/AlgebraicInduction/Theorem55.lean`).
  *Found:* round 3 task 2.3.
  *Disposition:* reported (`notes/Prose-report.md`, S2); round 1: KT Theorem 5.6's scope stated
  (degenerate hinges, the free selector, and the all-zero-normals framework meeting the conclusion
  at deficiency zero for every spanning graph; a `lake lean` witness, script not retained: with
  `normal := 0` every hinge is zero, `Graph.preconnected_of_isKDof_zero` makes each motion
  constant, and `rankHypothesis_zero_iff` gives the conclusion) on its `main_results` row and
  `alignment` entry,
  README, the home page, `intro.tex` and ROADMAP §23, beside the proved form
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`, named in the text only; the row's
  rank-formula sentence now takes that form, as the upper bound needs nondegenerate hinges
  (b0eb63eb).
- **F-136** · S · `lem:case-I-splice-seed` (`algebraic-induction/case-i.tex`): at the open the
  statement glued $H$ and the contraction $G/E(H)$, "both subgraphs of $G$". The contraction is not
  a subgraph of $G$ when an edge not in $H$ has an end in $V(H) \setminus \{r\}$, since that end is
  replaced by $r$. The pin `isInfinitesimallyRigidOn_of_splice` glues the restrictions of a
  framework to two subgraphs $G_1, G_2 \le G$ whose body sets share a body, so the lemma is not an
  instance of it. Task 2.7 kept the contraction, stated with the hinges of $p$
  (`def:framework-with-graph`; KT eq. (6.7)), and dropped the false gloss. The statement then
  holds, because a motion of $(G,p)$ that is constant on $V(H)$ is a motion of $(G/E(H), p)$; no
  pin states that step, and the note after the lemma says so.
  *Evidence:* read (the statement and body, `Molecular/AlgebraicInduction/Pinning.lean`;
  `def:rigid-contraction`); measured (dead pin, `scripts/blueprint-deps.py --label`, at
  `9a465598`).
  *Found:* round 3 task 2.7.
  *Disposition:* reported (`notes/Prose-report.md`, S32).
- **F-137** · S · `lem:rows-polynomial-in-normals` (`algebraic-induction/case-i.tex`): the statement
  says that the rows of $R(G,n)$ at an edge can be chosen with coordinates that are polynomials of
  degree two in the normals. Task 2.7 added that the hinge at the edge be nondegenerate: the
  formal family is zero at a zero extensor. The pin `exists_good_realization_ofParam` states no
  polynomial. If $m$ of these rows are linearly independent at normals $q_0$, it gives normals $q$
  with $m + \dim Z(G,q) \le D|W|$, which $q_0$ itself satisfies (`F-117`'s pattern for the
  constant family). The polynomial coordinates (`annihRowPoly_eval`,
  `annihRowPoly_totalDegree_le`) and the spanning (`span_panelRow_eq_rigidityRows`) are steps of
  its proof with no node; `rigidity-matrix.tex` cites this node for them, in
  `lem:rank-polynomial-proj-eval` and the note after `lem:rank-polynomial-IH-relabel-proj`.
  *Evidence:* read (the statements and bodies, `Molecular/AlgebraicInduction/GenericityDevice.lean`,
  `PanelLayer.lean` and `Pinning.lean`).
  *Found:* round 3 task 2.7.
  *Disposition:* done (`d851de0f`): the node is repinned on `annihRowPoly_eval`,
  `annihRowPoly_totalDegree_le` and `span_annihRow_eq_dualAnnihilator`, which prove its three
  clauses (`F-139`), and `exists_good_realization_ofParam` is unpinned; the statement is unchanged.
- **F-138** · S · `lem:claim-6-4` (`algebraic-induction/case-i.tex`): the statement takes a simple
  minimal $0$-dof-graph $G$ whose contraction $G/E(H)$ has a generic full-rank realization, and
  gives a nonzero polynomial $Q$ in the normals off whose zeros the rows of $G \setminus E(H)$, with
  the columns of $V(H)$ deleted, have rank $D(|s_c| - 1)$. The pin
  `rigidContract_exterior_rank_transport_htransport` gives one point, KT's choice in the proof of
  Claim 6.4 (every body of $H$ with the normal of $r$). It assumes that $G/E(H)$ is simple and of
  deficiency zero, and of $G$ only that $V(H) \subseteq V(G)$. The statement's hypotheses do not make $G/E(H)$ simple;
  the proof needs only that it has no loops, which its minimality gives. The open-set form, for
  every $k$, is `lem:rank-polynomial-IH-relabel-proj` (`rigidity-matrix.tex`), whose pin the
  formal Case I reaches. Task 2.7 kept the statement, with a note.
  *Evidence:* read (the statement and body, `Molecular/AlgebraicInduction/CaseI.lean`; KT 2011
  p. 675, `.refs/`); measured (`scripts/blueprint-deps.py --label lem:claim-6-4` and
  `lem:case-I-realization`, at `9a465598`).
  *Found:* round 3 task 2.7.
  *Disposition:* done (`c2cfcd08`): the statement is the pin's: for any $G$, with $G/E(H)$ a simple
  $0$-dof-graph with a generic full-rank realization, some normals $q_0$ at which $D(|s_c| - 1)$
  rows of $G \setminus E(H)$ are independent after the columns of $V(H)$ are deleted. The pin's
  statement gives some $q_0$ only, so KT's point is the proof's, which keeps its steps and stops
  there; the passage before the node says that it is `lem:rank-polynomial-IH-relabel-proj`'s
  conclusion at $k = 0$ and one point, and the proof's edge to `lem:rank-polynomial-proj-eval` (no
  Lean basis) goes with the polynomial. The note names the pin's premise of a rigid realization in
  general position (`F-140`), which the proof's realization meets.
- **F-141** · S · `lem:case-I-realization`, `lem:case-I-realization-h65`, `lem:case-I-dispatch`
  (`algebraic-induction/case-i.tex`): three statements leave out hypotheses their pins assume.
  `lem:case-I-realization-h65` omits that $G$ has a proper rigid subgraph, which
  `case_I_realization_h65_gen` (`hrig`) and KT Lemma 6.5 (p. 676) assume and the proof of KT
  Claim 6.6 needs; without one the statement is Case III at $k = 0$, which also needs the induction
  hypothesis at positive deficiencies. `lem:case-I-dispatch` omits the induction hypothesis, which
  `case_I_dispatch_gen` (`hIH`) assumes. `lem:case-I-realization` assumes generic full-rank
  realizations of $H$ and $G/E(H)$, and `case_I_realization_all_k_gen` the induction hypothesis
  for every smaller graph; its proof uses only those two instances. Task 2.8 kept the three
  statements, wrote the proofs under the pins' hypotheses with a sentence saying so, and gave each a
  note. It also added, as anchoring, $d \ge 2$ to the slice's four statements (the pins' `hD` and
  `hk`), "$K$ infinite" to the three whose pins assume it, and "at least one vertex" to the
  induction-hypothesis clauses, as `def:genuine-hinge-realization` needs $V \ne \emptyset$.
  *Evidence:* read (the statements and bodies, `Molecular/AlgebraicInduction/Theorem55.lean`; KT
  2011 pp. 673--676, `.refs/`).
  *Found:* round 3 task 2.8.
  *Disposition:* done (`c2cfcd08`): `lem:case-I-realization-h65` assumes a proper rigid subgraph and
  `lem:case-I-dispatch` the induction hypothesis, for every $k'$, as their pins do; the proofs'
  sentences assuming them go, with the first node's note and the second's first sentence.
  `lem:case-I-realization` is kept, as the report suggests.
- **F-142** · S · `lem:case-I-realization-nonsimple` (`algebraic-induction/case-i.tex`): the
  statement is KT Lemma 6.2 for every $d \ge 2$; its pin `case_I_realization_nonsimple` is the case
  $d = 3$ (`hn : bodyBarDim n = screwDim 2`), a wrapper of `case_I_realization_nonsimple_gen`, the
  form for every $d$ that `case_I_dispatch_gen` and the Case I split for $k > 0$
  (`case_I_hcontract_gen`) call. In the other direction the statement assumes the full induction
  hypothesis, and the pin only nondegenerate-hinge realizations of the smaller graphs. Repinning the
  node on the general form makes its pin match the statement's dimension. Task 2.8 kept the
  statement, with a note.
  *Evidence:* read (the statements and bodies, `Molecular/AlgebraicInduction/Theorem55.lean`).
  *Found:* round 3 task 2.8.
  *Disposition:* done (`d851de0f`): the node is repinned on `case_I_realization_nonsimple_gen`,
  which matches the statement's dimension; its note says that the pin, assuming less of the smaller
  graphs, proves more than the statement (`F-143`).
- **F-145** · S · `lem:case-II`, `lem:splitoff-edge-substitution` (`algebraic-induction/case-ii.tex`):
  the second assertion of `lem:case-II` holds vacuously for $d \ge 2$. Its hypothesis, as in its
  pin `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` (`hspan`), asks that every
  motion $S$ of the framework on $G_v$ with $S(v) = 0$ have $S(a) \in \operatorname{span} C(e_a)$.
  When $v$ lies on no edge of that framework, the assignment $c$ off $v$ and $0$ at $v$ is such a
  motion for every screw $c$, so the hypothesis makes a line the whole screw space, of dimension
  $D \ge 3$. At the open the statement called the hypothesis KT Claim 6.9's general position,
  supplied by `lem:exists-independent-panel-extensor`; KT Claim 6.9 (p. 678) says only that
  $(G, p_1)$ is a panel-hinge realization for every $L$. The first assertion's pin
  `isInfinitesimallyRigidOn_insert_iff` holds for every framework, set $t$ and body $v$, so the
  statement, with its minimal $k$-dof-graph, is weaker than the pin; the title named KT Lemmas 6.7
  and 6.8, which neither assertion is. `lem:splitoff-edge-substitution` states that $G_v^{ab}$ is
  not a subgraph of $G$, which no pin states. Task 2.9 kept both statements (register only, the
  gloss dropped, the titles corrected), and the notes say this.
  *Evidence:* read (the pins' statements and bodies, `Molecular/AlgebraicInduction/PanelHinge.lean`,
  `Pinning.lean`, `Molecular/Induction/Operations.lean`; the definitions of `pinnedMotions`,
  `IsInfinitesimalMotion` and `hingeConstraint`; KT 2011 pp. 677--679, `.refs/`); a `lake lean`
  witness: under `hspan`, with no link of the smaller graph at $v$ and a new edge from $v$ to
  $w \neq v$, every screw lies in the span of that edge's extensor.
  *Found:* round 3 task 2.9.
  *Disposition:* done (`ab3a0d45`): the node drops the second assertion with its pin, the proof's
  second part and the note, and the lead's sentences on it; it keeps the first in its Case II
  setting, with a note that the pin is its form for every framework, set $t$ and body $v$.
  `lem:splitoff-edge-substitution`'s unpinned clause stays, as it is true (the open's decision).
- **F-149** · S · `lem:genericity-device` (`algebraic-induction/genericity-and-count.tex`): read
  with the rigidity matrix of `def:rigidity-matrix`, the statement fails at normals with a
  degenerate hinge. There the hinge constraint welds the two ends (the remark after
  `def:panel-hinge-framework`), and the rows of the edge have rank $D$. For the graph with one edge
  the rank is $D$ on the Zariski-closed set of dependent normals and $D - 1$ elsewhere, so
  $\{\operatorname{rank} \ge D\}$ is not open, the largest rank is attained only on that closed set,
  and $\dim Z$ is not upper semicontinuous. The statement holds for the matrix of the forms of
  `lem:rows-polynomial-in-normals`, which vanish at a degenerate hinge, and for $R(G,q)$ on the open
  set of normals with nondegenerate hinges, KT §5.1's nonparallel realizations;
  `lem:rank-polynomial-of-le-finrank`, which assumes them, is the open-set form. Task 2.10 kept the
  statement (`F-117`); its proof assumes nondegenerate hinges and says so, and the remark after the
  proof gives the example.
  *Evidence:* read (`def:panel-hinge-framework` and the definitions `hingeConstraint` and
  `IsInfinitesimalMotion`, `Molecular/RigidityMatrix/Basic.lean`; KT 2011 p. 668, `.refs/`); a `lake
  lean` witness: at an edge with a zero supporting extensor every motion has $S(u) = S(v)$.
  *Found:* round 3 task 2.10.
  *Disposition:* done (`1b46edc6`): the statement is restated on the Zariski-open set $U$ of normals
  with nondegenerate hinges, where it holds, which contains KT's nonparallel realizations; the
  remark after the proof says that the restriction is needed (`3456d6a7`). The node pins the open-set
  form, `exists_rankPolynomial_of_le_finrank_linking` (`1b46edc6`).
- **F-150** · S · `lem:case-II-realization-placement`
  (`algebraic-induction/genericity-and-count.tex`): the statement starts from a realization of the
  splitting-off $G_v^{ab}$, with nondegenerate hinges and every motion constant on its vertices. Its
  pin `case_II_placement_eq612` assumes instead a realization of a subgraph `Gv ≤ G` with `v ∉
  V(Gv)` and `V(Gv).ncard = V(G).ncard - 1` (`hGv`, `hvVc`, `hVcard`), rigid on `V(Gv)` with
  nondegenerate hinges (`hrig`, `hne_Gv`), whose rows are rows of $G$ (the transport with `f :=
  id`); it assumes no degree for $v$, and also concludes that the hinge of $va$ is nondegenerate.
  Such a subgraph has deficiency zero, so for $|V(G)| \ge 3$ it is a proper rigid subgraph of $G$,
  and no framework of Cases II and III meets the pin's hypotheses; the pin lies outside every main
  result's closure. The statement holds: task 2.10's proof gives the count of
  `lem:case-II-realization`'s proof at a rigid $G_v^{ab}$, with no pin behind it. At the open the
  proof transported $D(|V(G)| - 2)$ rows of $G_v^{ab}$ through $G_v$, which the remark after it said
  do not exist. Task 2.10 kept the statement, and its note says this.
  *Evidence:* read (the statement and body of `case_II_placement_eq612`,
  `Molecular/AlgebraicInduction/CaseII.lean`; KT 2011 pp. 678--680, `.refs/`); a `lake lean`
  witness: the pin's hypotheses on `Gv` give `Gv.deficiency n ≤ 0`, through
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` and
  `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`.
  *Found:* round 3 task 2.10.
  *Disposition:* reported (`notes/Prose-report.md`, S3).
- **F-154** · S · `lem:case-III-nested-rank-lower` (`algebraic-induction/case-iii.tex`): the
  statement omits two hypotheses of its pin `exists_nested_rankPolynomial_lower_all_k`, that $G$ is
  simple (`hSimple`) and the induction hypothesis for every $k'$ (`hIH`). Without simplicity it
  fails. For $d = 2$ ($D = 3$), the graph with the edges $va$, $vb$, $cb$ and two edges $ac$ is a
  minimal $0$-dof-graph in which $v$ has degree two. Parallel edges of a panel-hinge framework
  share one hinge, so wherever the two hinges of $(G_v, q)$ are nondegenerate its rank is at most
  $4 < 5 = D(|V(G_v)| - 1) - (D - 2)$, and over an infinite field no nonzero $P$ exists. For a
  simple $G$ the statement follows from KT Theorem 5.5 at $G_v$ (`thm:theorem-55`), so the omitted
  induction hypothesis loses no truth. Task 2.11 kept the statement; its proof assumes both and says
  so, the note gives them, and the paragraph after the note gives the example.
  *Evidence:* read (the statement and body of `exists_nested_rankPolynomial_lower_all_k`,
  `Molecular/AlgebraicInduction/CaseIII/Realization.lean`; `def:panel-hinge-framework`); the
  example's deficiencies by hand, over the fifteen partitions of its four vertices.
  *Found:* round 3 task 2.11.
  *Disposition:* done (`3456d6a7`): the statement takes $G$ simple, and the proof no longer assumes it.
  The induction hypothesis stays in the note, which says that over an infinite field the statement
  holds without it (KT Theorem 5.5 at $G_v$, `thm:theorem-55`), as this entry's reading has it.
- **F-158** · S · `lem:case-III-candidate-row` (`algebraic-induction/case-iii.tex`): the statement
  is KT's count at $(G, p_1)$ (KT pp. 684 and 686): if the top-left block of KT eq. (6.29) is
  nonsingular, $\operatorname{rank} R(G, p_1) \ge D(|V(G)| - 1)$. Its pin
  `linearIndependent_sum_augment_candidateRow` is linear algebra on families of forms, with no
  graph, framework or rank, and its old block must vanish on the screw assignments that vanish off
  $v$, which KT's bottom rows $(vb)j$ do not. The open's statement took $p_1$ from
  `lem:case-II-realization-placement`, whose normal $q(a) + t\,q(b)$ at $v$ gives $va$ the hinge
  $-t\,C(q(a), q(b))$, so $L = q(ab)$ for $t \neq 0$ and the block is singular; task 2.12
  anchored $p_1$ at KT eq. (6.12), as the statement's "for some choice of line" requires. The
  open's proof
  applied the pin to the rows of $R(G_v^{ab} \setminus (ab)i^*, q)$ without placing them in the row
  space of $R(G, p_1)$; task 2.12's proof places them there when the block is nonsingular. The
  graph-level count is the unpinned `case_III_rank_certification` (`F-159`). Task 2.12 kept the
  claim; the note says that the pin does not mention $G$, $p_1$ or the rank.
  *Evidence:* read (the statements and bodies of `linearIndependent_sum_augment_candidateRow`,
  `…_block`, `caseIIICandidate` and `case_III_rank_certification`; KT 2011 pp. 678, 684–686 and
  690, `.refs/`); `lake lean` witnesses: a row `hingeRow v b φ` reads `φ x` at the screw assignment
  with value `x` at `v` and `0` elsewhere; every form vanishing on `C(n_a, n_b)` vanishes on
  `C(n_a + t • n_b, n_a)` (`panelSupportExtensor_add_smul_left`); and
  `hingeRow a b φ = hingeRow v b φ - hingeRow v a φ`.
  *Found:* round 3 task 2.12.
  *Disposition:* done (`9e98aaba`): the node pins `case_III_rank_certification`, of which it is the
  case $(G, p_1)$, the framework of `def:case-III-candidate` for a normal of a hyperplane meeting
  $\Pi(a)$ in $L$; its note gives each hypothesis's source (`lem:case-III-redundant-decomposition`
  and the rank of $R(G_v^{ab}, q)$). Two of the pin's proof edges are forward (`F-257`).
- **F-165** · S · `lem:case-III-claim612-p2-placement`, `lem:case-III-claim612-p3-placement`
  (`algebraic-induction/case-iii.tex`): the statements are KT's counts at $(G, p_2)$ and
  $(G, p_3)$ (KT pp. 686–689): if the block $M_2$ of KT eq. (6.30), or $M_3$ of KT eq. (6.41), is
  nonsingular, the rank is at least $D(|V(G)| - 1)$. Their pins are
  `linearIndependent_sum_augment_candidateRow` at the roles $(v, b)$ and $(a, c)$, with the
  criterion of `lem:case-III-claim612-block-iff-perp`: linear algebra on families of forms, with no
  graph, framework or rank (as `F-158`). The graph-level counts are the unpinned
  `case_III_rank_certification` at the roles of $(G, p_2)$ and, with the relabelled normals on
  $G - a$, of $(G, p_3)$, which the formal proof of the case $d = 3$ uses (`F-167`). Task 2.14 kept
  the claims; the notes say that the pins do not mention $G$, $p_2$, $p_3$ or the rank.
  *Evidence:* read (the statements and bodies of the two pins, of `case_III_arm_realization`,
  `_M2` and `_M3`, and of `caseIIICandidate`; KT 2011 pp. 682 and 686–691, `.refs/`).
  *Found:* round 3 task 2.14.
  *Disposition:* done (`9e98aaba`): both nodes pin `case_III_rank_certification`, the theorem that
  `case_III_arm_realization_M2` applies with $a$ and $b$ exchanged and $-r$, and `_M3` with $a$,
  $c$, $v$ in the roles of $v$, $a$, $b$, the normals $q_\rho$, $-r$ and $G - a$; each statement
  names its framework as `def:case-III-candidate`'s at those roles, and each note gives each
  hypothesis's source (for $(G, p_3)$, KT eq. (6.44) and the proof's display at $S'$). One proof
  edge of the first is forward (`F-257`).
- **F-169** · S · `lem:case-III-chain-discriminator` (`algebraic-induction/case-iii.tex`): the
  statement claims less than its pin and than its consumer uses. It asks for some normals $q$, a
  nonzero form $r$ vanishing on $C(q(v_0), q(v_2))$, and $r(C(q(u_i), n')) \neq 0$ for some panel
  index $i$ and some $n'$ independent of $q(u_i)$; with $q(v_0) = q(v_2)$ this holds for any
  graph, so the hypotheses play no role. The pin `chainData_fire_discriminator` also gives $q$ in
  general position, that $S \mapsto r(S(v_0) - S(v_2))$ lies in the row space of
  $R(G - v_1, q)$ (KT eq. (6.52), with $r = \sum_j \lambda_j r_j$ and the relation grouped by
  edge), and $D(|V(G)| - 2)$ independent rows of $R(G_1, q)$, all of which
  `lem:case-III-chain-dispatch`'s pin uses. Task 2.15 kept the claim; its proof derives the rest,
  and the note says that the pin gives it.
  *Evidence:* read (the statement and body of `chainData_fire_discriminator`, and of
  `exists_shared_redundancy_and_matched_candidate` and `chainData_dispatch`).
  *Found:* round 3 task 2.15.
  *Disposition:* done (`ab3a0d45`): the statement gives the pin's conclusion: $q$ in general position,
  $D(|V(G)| - 2)$ independent rows of $R(G_1, q)$ (KT eq. (6.46)), the form
  $S \mapsto r(S(v_0) - S(v_2))$ in the row space of $R(G - v_1, q)$ (KT eq. (6.52)), and the
  panel; the note keeps the pin's formal extras and says that `chainData_dispatch` uses all of
  them but the decomposition $r = \sum_j \lambda_j r_j$.
- **F-174** · S · `thm:molecular-iff-square-bar-joint` (`molecule-modelling.tex`): the statement
  ends "in particular $G$ has an infinitesimally rigid molecular realization iff $G^2$ has an
  infinitesimally rigid bar-joint realization". Its pin `molecular_finrank_motions_eq_square_ker`
  gives only the equality $\dim Z_{\mathrm{mol}}(G, c) = \dim \ker R(G^2, c)$ at one placement $c$
  in general position up to order four, and no declaration states the realizability equivalence.
  Read with `def:hinge-concurrent`, which admits coincident centres, the sentence is false: with all
  centres equal every hinge is welded, so the molecular framework of a connected $G$ is rigid, while
  the square of the cycle $C_7$ (minimum degree two) has $14 < 3 \cdot 7 - 6$ edges and no rigid
  realization. With nondegenerate hinges it is the modelling equivalence of Whiteley and
  Jackson–Jordán; it then follows from `thm:panel-hinge-iff-molecular`, the deficiency bound for
  nondegenerate hinges, this dictionary and a placement both generic and in general position
  (`lem:exists-generic-general-position`), but no node states it. A crux node: task 2.3 keeps the
  claim with a note, or anchors it, and says which.
  *Evidence:* read (the statement and body of `molecular_finrank_motions_eq_square_ker` and the
  definition `molecularOfCentres`, `Molecular/Molecule/Dictionary.lean`; the edge count of
  $C_7^2$).
  *Found:* round 4 task 1.
  *Disposition:* reported (`notes/Prose-report.md`, S31).
- **F-177** · S · `def:genericRigidityMatroid`, `def:genericRank` (`bar-joint-3d.tex`): at the open
  the first definition ended "By `lem:linearRigidityMatroid-eq-genericRigidityMatroid` the matroid
  does not depend on the choice of $p$", a consequence with a forward `\cref`, and called
  $\mathcal{R}_d(V)$ "a matroid on $\mathrm{Sym}_2 V$ with ground set $E(K_V)$"; the second ended
  "At $d = 3$ this is the rank function $r(\cdot)$ of the molecule rank formula (KT Corollary
  5.7)". Task 2.1 moved both sentences out under principle B, as a definition's consequence and a
  role clause. The first is the statement of `lem:linearRigidityMatroid-eq-genericRigidityMatroid`
  (pin `linearRigidityMatroid_eq_genericRigidityMatroid`), two nodes later, and the opening says it;
  the second is in the opening. The pin `genericRigidityMatroid` takes the placement
  `(exists_isGenericPlacement d).choose`, so neither definition changes. $\mathrm{Sym}_2 V$ is the
  formal element type (the note at `def:linearRigidityRow`); the ground set stays $E(K_V)$.
  *Evidence:* read (the bodies of `genericRigidityMatroid` and `genericRank`; the statement of
  `linearRigidityMatroid_eq_genericRigidityMatroid`).
  *Found:* round 4 task 2.1.
  *Disposition:* reported (`notes/Prose-report.md`, S37).
- **F-178** · S · `thm:projective-invariance` (`molecule-modelling.tex`): at the open the statement
  was set in $\R^3$, for an automorphism $\Lambda$ of $\bigwedge^2 \R^4$, and ran eight sentences:
  the projective reading (a collineation or a correlation, Crapo–Whiteley §3.6), the correlation as
  "the one the duality below consumes", the rescaling, and "the argument uses only linearity and
  invertibility of $\Lambda$, so the Lean statement holds over an arbitrary field $K$ … $\R^3$ is
  fixed above because that is where the projective-transformation reading of $\Lambda$ applies",
  ending on a `\cref` to the later `sec:pencil-duality`. Task 2.2 states it over a field $K$, as
  (1) the motion isomorphism with dimension, rank and rigidity, (2) nondegenerate hinges and (3)
  the rescaling, and moves the projective reading, the role clause, the $\R^3$ remark and the
  pencil pointer to the prose after it. Two readings: the block already claimed the $K$ form, as
  "the Lean statement", so the claim is unchanged (the task's); or the headline was the $\R$ form
  and the sentence a formalization remark, so the headline now claims more, though no more than its
  pins (which hold over every field and in every dimension). `pencil.tex` reads the theorem as field-general
  (`lem:pencil-self-dual`, `lem:pencil-projective-transport`), which the first reading keeps true.
  *Evidence:* read (the statements of the seven pins, `Molecule/ProjectiveInvariance.lean` and
  `RigidityMatrix/Basic.lean`; `pencil.tex` at `lem:pencil-self-dual` and
  `lem:pencil-projective-transport`).
  *Found:* round 4 task 2.2.
  *Disposition:* reported (`notes/Prose-report.md`, S37).
- **F-179** · S · `def:hinge-concurrent`, `def:screw-velocity`, `lem:panel-hinge-dual-molecular`
  (`molecule-modelling.tex`): principle B's moves. `def:hinge-concurrent` named the endpoint selector
  and ended on five sentences: the hinge-concurrency it gives (KT p. 671), the converse "carrying the
  centres as data loses no generality", the molecule model, the welded hinge at coincident centres
  and "the genuine-hinge statements below therefore carry an injectivity or general-position
  hypothesis". Task 2.2 moved them to the prose after it, the converse stated for distinct adjacent
  centres (sources: KT p. 650, JJ 2008 §2.1, Whiteley 1999 Definition 4), and the selector to a
  note. `def:screw-velocity` called $(\omega_S, t_S)$ "the components pairing two affine
  directions, resp. a direction with the homogenizing coordinate", which swaps them ($\omega_S$
  reads the coordinates at $e_i \vee e_4$, as `omegaForm` does), and ended on the line's field
  $\omega = b - a$, $t = a \times b$. It now defines $\omega$ and $t$ by their values at
  $v \vee w$, as the pins do; the gloss is dropped, and the line's field is proved after it
  (`screwOmega_lineExtensor`, `screwTau_lineExtensor`). `lem:panel-hinge-dual-molecular`'s setup
  (the polarity's convention, KT's pole $c(v)$, $\Lambda$ as the complement isomorphism) went to a
  lead-in, and its claims are its items (1)–(3).
  *Evidence:* read (the bodies of `molecularOfCentres`, `omegaForm`, `tauForm`, `screwVel` and the
  two line lemmas; KT pp. 650, 671; JJ 2008 §2.1; Whiteley 1999 p. 27).
  *Found:* round 4 task 2.2.
  *Disposition:* reported (`notes/Prose-report.md`, S37).
- **F-180** · S · `lem:panel-hinge-dual-molecular`, `lem:screw-determination`
  (`molecule-modelling.tex`): statements that claim more or less than their pins. The first's
  "for normals with nonvanishing last coordinate the same holds after the rescaling normalization",
  now its (3), has no pin: `exists_molecular_rankHypothesis_generalPosition` (the pin of
  `thm:panel-hinge-iff-molecular`) proves the rescaling inline, by a span equality and
  `infinitesimalMotions_mono_of_span_le`, not through the pinned `infinitesimalMotions_scaleExtensor`.
  Its (1) is stated over $\R$, while `screwComplementIso` and `screwComplementIso_mk_extensor` are
  field-general. The second's part (2) asks for a finite family, and for every non-collinear triple
  with every fourth member to be affinely independent; `existsUnique_screwVel_eq` takes any index
  type and one fixed triple. Task 2.2 kept each claim, with a note.
  *Evidence:* read (the statements of the pins; the body of
  `exists_molecular_rankHypothesis_generalPosition`, `Molecule/Modelling.lean`).
  *Found:* round 4 task 2.2.
  *Disposition:* done (`6e56a1d1`): `lem:polarity-join` is stated over a field $K$, as its first two
  pins are, its second clause at $K = \R$; `lem:screw-determination`'s (2) as
  `existsUnique_screwVel_eq` states it, for any family and one non-collinear triple, its note
  gone. The rescaling keeps its note, which now names its formal form, `lem:pencil-jj-rescale`'s
  (`F-260`).
- **F-183** · S · `thm:molecular-iff-square-bar-joint` (`molecule-modelling.tex`): task 2.3's call
  on `F-174`, by anchoring. The statement's last sentence read "In particular $G$ has an
  infinitesimally rigid molecular realization iff $G^2$ has an infinitesimally rigid bar-joint
  realization (Whiteley's modelling equivalence, for which Jackson–Jordán is the citable published
  anchor; KT resolve the conjecture that closes the argument)". It now reads "Moreover, $G$ has an
  infinitesimally rigid molecular realization with nondegenerate hinges, that is, with $c(u) \neq
  c(v)$ at every edge $uv$, if and only if $G^2$ has an infinitesimally rigid bar-joint realization
  in $\R^3$"; the attribution went to the title and the subsection's lead. Two readings: anchoring a
  definition's domain, as the molecular frameworks of Jackson–Jordán and KT have lines through the
  centres as hinges (JJ 2008 §2.1; KT p. 671; Whiteley 1999 Definition 4 calls distinct centres
  non-degenerate), so the claim is the equivalence they state, now true; or a hypothesis added to an
  unpinned claim that, read with `def:hinge-concurrent`, was false (`F-174`'s $C_7$), with "In
  particular" changed to "Moreover", since the claim does not follow from the dimension equality
  alone. The claim stays unpinned, with a note. The proof now proves it: rigidity with nondegenerate
  hinges forces $\operatorname{def}(\tilde G) = 0$ (`lem:relative-deficiency-rank-bound`), then
  `thm:panel-hinge-iff-molecular` and the dimension equality give a rigid $(G^2, c')$; conversely a
  placement both generic and in general position (`lem:exists-generic-general-position`) gives,
  from any rigid $(G^2, p)$, a rigid molecular framework with injective centres.
  *Evidence:* read (the statement and body of `molecular_finrank_motions_eq_square_ker`;
  `molecularOfCentres`; JJ 2008 §2.1; KT pp. 650, 671; Whiteley 1999 p. 27).
  *Found:* round 4 task 2.3.
  *Disposition:* reported (`notes/Prose-report.md`, S31).
- **F-184** · S · `thm:panel-hinge-iff-molecular`, `lem:theorem-56-general-position`,
  `def:general-position-placement` (`molecule-modelling.tex`): principle B's moves and anchoring.
  The theorem's "simple spanning graph on at least one body, with enough hinge labels", its "endpoint
  selector … genuinely recording every $G$-link" and three role and attribution sentences ("the
  panel-hinge realization … carried to the molecular model", "the modelling equivalence KT state on
  p. 671", Jackson–Jordán as "the citable published anchor") left the statement: it reads "a simple
  graph with $V \neq \emptyset$", the label bound, the spanning hypothesis and the selector are in a
  note (`rem:fresh-edge-supply`, `fmlnote:panel-hinge-nondegenerate`), and the title is "Molecular
  realizations at the target rank; KT p. 671", not "Panel-hinge $\Leftrightarrow$ molecular,
  rank-carrying". Its "Taking $\operatorname{def}(\tilde G) = 0$ gives an infinitesimally rigid
  molecular realization", which the pin does not state (`rankHypothesis_zero_iff` gives it), stays
  as an "In particular", with a note. The lemma's "simple spanning graph on at least one body" is "a
  simple graph with $V \neq \emptyset$", and its "normals have nonvanishing last coordinate and …
  poles are in general position" is "normals $n_v = \lambda_v \bar c(v)$, $\lambda_v \neq 0$, with
  the $c(v)$ in general position", the same condition; the pin's label bound and its statement for
  the normals are in a note. The definition's "(so in particular $p$ is injective and no three
  points are collinear)" and its moment-curve witness went to the prose after it, with a proof.
  *Evidence:* read (the statements of `exists_molecular_rankHypothesis_generalPosition`,
  `exists_rankHypothesis_isGeneralPosition4`, `IsGeneralPosition4` and
  `IsGeneralPositionPlacement`).
  *Found:* round 4 task 2.3.
  *Disposition:* done (`64a531db`): the "In particular" is not pinned at the theorem, where
  `rankHypothesis_zero_iff` would leave five missing edges, two of them closing a cycle (`6e56a1d1`,
  `F-259`); that declaration joins the pins of `lem:trivial-motions-rank-bound`, which the
  theorem's proof now `\uses` and its note cites for the case.
- **F-187** · S · `lem:molecule-graph-carrier` (`molecule-application.tex`): the label supply left
  the statement. At the open it read "There is a multigraph $G'$ on $V$, spanning and simple, with an
  edge between distinct $u, v$ if and only if $u \sim_G v$, and with strictly more than $6(|V| -
  1)$ edge labels available". Task 2.4 states that there is a simple multigraph $G'$ with vertex set
  $V$ in which two distinct vertices are joined if and only if they are adjacent in $G$; the label
  bound, with the labels the pin uses, is in the note, citing `rem:fresh-edge-supply`. Two
  readings: principle E's "a Lean-side device … stays out of statements" and the round's *Terms*
  (the fresh-label supply leaves statements, as at `thm:panel-hinge-iff-molecular`, `F-184`), the
  pins unchanged and the bound stated in the note; or the statement now claims less than its pins,
  one of which (`card_shadowLabel_lt`) is the bound, against the rule that such a statement keeps
  its claim, with a note. Without the bound the statement reads a simple graph as a multigraph;
  whether the node stays one is `F-010`'s question (its pinned helper `shadowGraph`).
  *Evidence:* read (the statements of the five pins and the body of `shadowGraph`,
  `Molecule/Carrier.lean`; the signature of `exists_molecular_rankHypothesis_generalPosition`).
  *Found:* round 4 task 2.4.
  *Disposition:* done (`41e7a771`): the statement claims what its pins prove, with the bound as a
  clause ("whose edges are drawn from a set of more than $6(|V| - 1)$ labels",
  `card_shadowLabel_lt`); the proof builds the labels, and the note keeps why the bound is needed
  and the pins' roles.
- **F-188** · S · `lem:square-rank-le-genericRank` (`molecule-application.tex`): the statement's
  second form, "Equivalently, $\operatorname{rank} R(H, p) \le r_d(H)$", has no pin. The pin
  `finrank_span_rigidityRow_le_genericRank` bounds the span of the rows of $K_V$ at $E(H)$; the
  rank form is the unpinned `finrank_range_rigidityMap_le_genericRank`, which the pin of
  `lem:molecule-rank-lower-bound` uses. Task 2.4 kept the claim, with a note; whether to pin the
  rank form is round 5's call (principle D).
  *Evidence:* read (the statements of both declarations, `GenericRigidityMatroid.lean`; the body of
  `molecule_rank_lower_bound`).
  *Found:* round 4 task 2.4.
  *Disposition:* done (`41e7a771`): the node also pins `finrank_range_rigidityMap_le_genericRank` for
  the rank form, its note naming each pin's clause; its proof derives the rank form, its new edge
  to `lem:span-range-rigidityRow` per the pin's reach.
- **F-191** · S · `lem:exists-tight-partition`, `lem:partitionDef-merge`,
  `lem:tight-partition-cross-pair-mult`, `lem:tight-partition-cross-pair-nbr` (`jacobs.tex`): four
  statements assume a hypothesis that their pins do not. The first asks $V(G)$ nonempty;
  `exists_isTightPartition` holds on every finite vertex type (the empty set's one partition has
  value $-D$). The second asks $|Q| \ge 2$; `partitionDef_merge` asks only a member of $Q$, and at
  $|Q| = 1$ both sides agree. `main-component.tex` reads it for $m \ge 1$ parts, in the proof of
  `lem:deficiency-merge-rigid`, which the pin covers. The third asks $G$ simple;
  `crossingEdgesWithin_pair_le_one` holds for every multigraph. The fourth asks the two vertices
  nonadjacent, as JJ's cross edges are; `eq_of_common_nbr` asks only that they lie in distinct
  parts. Task 2.5 kept each claim, with one note at the end of the subsection
  (`fmlnote:tight-partition-consumed-forms`). No edit.
  *Evidence:* read (the statements of the four pins, `Molecular/Deficiency.lean`; JJ 2008 §§3
  and 5).
  *Found:* round 4 task 2.5.
  *Disposition:* reported (`notes/Prose-report.md`, S39); round 2: `lem:partitionDef-merge` is
  stated for every nonempty $Q$, its proof saying what $|Q| = 1$ gives, and its sentence left the
  note (`0b8a78e0`).
- **F-195** · S · `thm:laman-square-count`, `lem:normal-cross-count-rooted`,
  `lem:normal-cross-count-partition` and the lemmas of `sec:jacobs-counting` (`jacobs.tex`):
  statements that assume more, or claim more, than their pins. The theorem asks $V$ nonempty;
  `laman_square_count` holds on every finite vertex type (at $V = \emptyset$ both sides are $0$, the
  empty partition having value $-6$). The lemmas assume the subsection's $G$ (minimum degree two,
  $G^2$ Laman): of their 23 pins only `ncard_edgesIn_neighborSet_square` asks the minimum degree (at
  $v$), and only those that use the degree bound ask the Laman condition.
  `lem:normal-cross-count-local` asks $|A| \ge 3$ where its pin asks $|A| \ge 2$, the same for a
  tight partition. `lem:normal-cross-count-rooted`'s "this part has at least three vertices" is not
  in its pins: it is `squareNormalCrossEdges_part_three_le`, a pin of
  `lem:square-cross-classification`. `lem:normal-cross-count-partition`'s bijection is
  `ncard_squareCutPairs_eq_gCutEdges`, an equality of counts. Task 2.6 kept each claim, with one
  note at the end of the subsection (`fmlnote:normal-cross-split`). No edit.
  *Evidence:* read (the statements of the slice's 25 pins, `JacobsCounting.lean`, `Jacobs.lean`,
  `SquareGraph.lean`; the body of `laman_square_count`).
  *Found:* round 4 task 2.6.
  *Disposition:* reported (`notes/Prose-report.md`, S39).
- **F-206** · S · `def:generic-normals`, `lem:generic-normals-nondegenerate`,
  `lem:panel-witness-transplant`, `thm:panel-generic-rank`, `cor:panel-generic-rigid`
  (`generic-lift.tex`): the endpoint selector, the label set and the spanning left the statements.
  At the open the definition read "Fix finite body and edge label sets and an endpoint selector",
  its family indexed "by an edge label together with a pair of grade-$k$ exterior basis indices";
  the lemma took "a loopless multigraph each of whose edge labels links its selector pair"; the
  witness lemma that, and a realization "whose own endpoint selector also records a link of every
  edge"; the theorem "a simple spanning multigraph on at least two bodies, at any dimension
  $n \ge 2$ (equivalently $D = \binom{n+1}{2} \ge 3$) … with a link-recording endpoint selector";
  the corollary "In the setting of" the theorem, rigid "on $V(G)$". Task 2.9 states them for a
  multigraph $G = (V, E)$ (for the last two a simple graph with $|V| \ge 2$, and $d \ge 2$), with
  the family written out over the edges of $G$. The selector, "every label is an edge" and the
  spanning are in `fmlnote:generic-normals-selector` and the note after the corollary; the
  nondegeneracy lemma's parenthetical on the values of $D$ left (principle B). Two readings, as
  for `F-184` and `F-187`: principle E's "a Lean-side device … stays out of statements" and the
  round's *Terms*, the pins unchanged; or the statements drop hypotheses that the pins carry,
  which `F-207` shows are not innocuous.
  *Evidence:* read (the statements of the eight pins, `GenericLift/PanelGeneric.lean`).
  *Found:* round 4 task 2.9.
  *Disposition:* reported (`notes/Prose-report.md`, S34).
- **F-207** · S · `thm:panel-generic-rank`, `cor:panel-generic-rigid` (`generic-lift.tex`): the
  pins hold vacuously at every graph that is itself a minimal $k$-dof-graph. Both take `hends`
  (every edge label links its selector pair in $G$, so $E(G)$ is the whole label set) and `hfresh`
  (every minimal $k'$-dof-graph on the bodies misses some label). At $G' = G$ these contradict each
  other whenever $G$ is minimal: a single edge, a tree. The statements claim every simple graph
  with $|V| \ge 2$. The pins are not vacuous: $|E(G)| > D(|V| - 1)$ gives `hfresh`
  (`rem:fresh-edge-supply`), for instance $K_7$ at $d = 2$ ($21 > 18$). Task 2.9 kept the claims,
  with the note after the corollary. The same pair is in the pins of `lem:hinge-point-witness`,
  `thm:bodyhinge-generic-rank` and its two corollaries (task 2.12); README names the last as the
  generic body-hinge theorem. Candidate: index the family by the edges of $G$, so that the label
  set may exceed $E(G)$.
  *Evidence:* read (the statements of the six pins, `PanelGeneric.lean`, `HingeGeneric.lean`; the
  body of `IsMinimalKDof`, `Deficiency.lean`); a `lake lean` witness, script not retained: from
  `hends`, `hfresh` and `hmin : G.IsMinimalKDof n (G.deficiency n)`, `hfresh _ G hmin` gives
  `e₀ ∉ E(G)` and `(hends e₀).edge_mem` gives `e₀ ∈ E(G)`. A single edge is minimal: its $D - 1$
  copies are independent in $M(\tilde G)$, the only base, and $\operatorname{def}(\tilde G) = 1$.
  *Found:* round 4 task 2.9.
  *Disposition:* reported (`notes/Prose-report.md`, S1); round 1: the scope stated beside both
  theorems in `formalization.yaml` (the row and the two `alignment` entries), README, the home page,
  `intro.tex` and ROADMAP §34, with `rem:fresh-edge-supply`'s reading checked by a `lake lean`
  witness; its sharper reading is `F-252` (8ee0f8a8).

- **F-211** · S · `def:two-extensor`, `def:generic-endpoints` (`generic-lift.tex`): principle B's
  moves out of two definitions, task 2.10's hygiene-rule reading. At the open `def:two-extensor`
  ended "The direction coordinates $(0, j)$ equal $p'_j - p_j$, polynomials of degree one in the
  $2n$ endpoint coordinates; the moment coordinates $(i, j)$ with $i \ge 1$ equal
  $p_i p'_j - p_j p'_i$, of degree two", and `def:generic-endpoints` fixed its orientation with
  "(…; the orientation fixes row signs only)". Task 2.10 moved both to the prose after the
  definitions, where the coordinates are named and computed and the independence of the orientation
  is argued. The definitions now introduce $T(p, p')$, the endpoint realization and genericity, and
  end; "Fix an enumeration of the pairs" became "Index the coordinates by the pairs, through a fixed
  bijection" (register). Two readings: principle B, the pins unchanged (the note after the
  definition names `twoExtensorPoly` as the polynomial form); or the definition drops the degree
  claim that its third pin carries.
  *Evidence:* read (the bodies of `twoExtensor`, `twoExtensorPoly`, `twoExtensorPoly_eval` and
  `IsGenericEndpoints`, `BodyBar/GenericLift.lean`).
  *Found:* round 4 task 2.10.
  *Disposition:* reported (`notes/Prose-report.md`, S37).
- **F-212** · S · `def:generic-endpoints`, `lem:generic-endpoints-abundance`
  (`generic-lift.tex`): the statements give an endpoint pair to each bar of $G$, and a polynomial
  "in the $2d\,|E(G)|$ endpoint coordinates". The pins give a pair to every edge label
  (`q : β × Bool × Fin n → ℝ`, with the body and label types finite), and the abundance
  polynomial has $2n$ variables for each label (`MvPolynomial (β × Bool × Fin n) ℝ`). The rows read
  only the bars' pairs, so the two forms of every statement of the section are equivalent, but the
  pinned lemma does not state that its polynomial involves only the bars' coordinates. Unchanged
  since the open; task 2.10 kept the statements, with the note after the definition. Candidate:
  index the assignments by $E(G)$ in the Lean, or keep the note.
  *Evidence:* read (the statements of `ofEndpoints`, `IsGenericEndpoints` and
  `exists_isGenericEndpoints_abundance`, and the body of the last).
  *Found:* round 4 task 2.10.
  *Disposition:* reported (`notes/Prose-report.md`, S13).

- **F-216** · S · `def:generic-hinge-points`, `lem:hinge-rows-polynomial-in-points`,
  `lem:generic-hinge-points-abundance`, `lem:exists-generic-hinge-points`,
  `lem:generic-hinge-points-nondegenerate` (`generic-lift.tex`): the endpoint selector and the
  label sets left the statements, task 2.11's hygiene-rule reading. At the open the definition read
  "Fix finite body and edge label sets and an endpoint selector", its family "of rigidity rows …
  indexed by an edge label together with a pair of grade-$k$ exterior basis indices"; the
  polynomial lemma began "Fix a finite edge label set. For each edge label $e$"; the abundance lemma
  had no setup, and the existence lemma "Over an infinite field"; the nondegeneracy lemma took
  "$k \ge 1$ (so $D \ge 2$), and … a loopless multigraph each of whose edge labels links its
  selector pair". Task 2.11 states them for a multigraph $G = (V, E)$ (finite where the pins ask;
  $d \ge 2$ and no loops for the last). The definition now introduces the hinge-point assignment
  and its framework $(G, q)$, and writes the family out over the edges of $G$, the ends in a fixed
  order. The selector, the label sets, the points at every label and "every label is an edge" are
  in the note after it. Principle B moved the abundance lemma's gloss "— a genuine hinge" and the
  parenthetical "(so $D \ge 2$)" to the prose and the proof ($D \ge 3$); "every supporting extensor
  nonzero" is "every hinge nondegenerate", the term of `def:panel-hinge-framework`'s remarks. Two
  readings, as for `F-206` and `F-212`: principle E and the round's *Terms*, the pins unchanged; or
  the statements drop hypotheses the pins carry. Only the nondegeneracy pin takes `hends`, and no
  pin of the slice takes `hfresh`, so `F-207`'s vacuity does not arise here.
  *Evidence:* read (the statements of the seven pins, `GenericLift/HingeGeneric.lean`).
  *Found:* round 4 task 2.11.
  *Disposition:* reported (`notes/Prose-report.md`, S34).
- **F-217** · S · `lem:hinge-rows-polynomial-in-points` (`generic-lift.tex`): the statement claims a
  polynomial "of degree at most $d - 1$" ("at most $k$" at the open), and no pin states a degree
  bound. `hingeExtensorPoly` is the $k \times k$ minor of a matrix whose entries are indeterminates
  or $1$, so the bound can be read off it, and `hingeExtensorPoly_eval` gives its value; the
  docstrings assert the bound. Nothing uses it: the abundance argument needs only that the
  coordinates are polynomials. Kept, with the note after the proof. Candidate: prove the bound (the
  total degree of the determinant), or drop it from the statement.
  *Evidence:* read (the bodies of the two pins; no degree lemma in `HingeGeneric.lean`).
  *Found:* round 4 task 2.11.
  *Disposition:* done (`41e7a771`): the statement claims a polynomial, without the bound, as the pin
  proves; the proof and the abundance proof's citation say "polynomial", and the note no longer
  says that no pin states the bound. The docstrings' bound is `F-220`'s.

- **F-221** · S · `lem:hinge-point-witness`, `thm:bodyhinge-generic-rank`,
  `cor:bodyhinge-generic-rigid`, `cor:bodyhinge-generic-tree-packing` (`generic-lift.tex`): the
  endpoint selector, the spanning and the second form of the dimension left four statements, task
  2.12's hygiene-rule reading. At the open the lemma and the theorem took "a simple spanning
  multigraph on at least two bodies, at any dimension $n \ge 2$ … and over any infinite field $K$,
  with a link-recording endpoint selector", the theorem adding "(equivalently
  $D = \binom{n+1}{2} \ge 3$)"; the corollaries read "In the setting of" the theorem, rigid "on
  $V(G)$". Task 2.12 states all four for $d \ge 2$, an infinite field $K$ and a simple graph
  $G = (V, E)$ with $V$ finite and $|V| \ge 2$, as task 2.9 stated the panel theorem. The selector,
  "every label is an edge", the spanning, the separate dimension parameter and rigidity on $V(G)$
  are in the note after `cor:bodyhinge-generic-tree-packing`. Two readings, as for `F-206`:
  principle E's "a Lean-side device … stays out of statements" and the round's *Terms*, the pins
  unchanged; or the statements drop hypotheses the pins carry. The four pins take `hends` and
  `hfresh`, so `F-207`'s vacuity at minimal $k$-dof-graphs holds for them, as `F-207` records; the
  note says so. The three lemmas before the witness changed in notation only ($d - 1$ vectors of
  $K^{d+1}$; $\Lambda$; $\operatorname{rank} R(G, \Lambda p)$ for the dimension of the row span).
  *Evidence:* read (the statements of the seven pins, `GenericLift/HingeGeneric.lean`,
  `Extensor.lean`).
  *Found:* round 4 task 2.12.
  *Disposition:* reported (`notes/Prose-report.md`, S34).
- **F-234** · S · `lem:forest-surgery-unsplit` (`molecular-induction.tex`; unfilled): no declaration
  proves its statement. `splitOff_indep_extend_of_fiber_lt`, the pin `F-091` names, proves the form
  of independent sets: for $D \ge 2$, a vertex $v$ of $G$ of degree two whose edges join it to
  distinct $a, b \neq v$, and an independent set $I'$ of $M(\widetilde{G_v^{ab}})$ with fewer than
  $D - 1$ copies of $ab$, some independent set $I$ of $M(\tilde G)$ has $|I| = |I'| + D$ and
  $I \setminus (\tilde e_a \cup \tilde e_b) = I' \setminus \widetilde{ab}$. The node states the
  forest form (each forest $F'_i$ of $\tilde H$ extends to a forest of $\widetilde{H_{ab}^v}$ with
  one more edge) for every $H$ with an edge $ab$ and every $D$; it fails at $D = 1$, where
  $\tilde H$ and $\widetilde{H_{ab}^v}$ have no edges, and its proof uses the copy $(vb, 1)$.
  Filling it needs the statement restated in the pin's weaker form, or $D \ge 2$ added and a
  declaration for the forest form; retiring the node is `F-091`'s other option (task 8.2).
  *Evidence:* read (the pin's statement; the node's statement and proof).
  *Found:* round 5 task 3.4.
  *Disposition:* done (`43c5c8d7`): the node states the pin's case $h' = 0$ (for $D \ge 2$, an
  independent set of $M(\widetilde{G_v^{ab}})$ with no copy of $ab$), KT's use at p. 662, and is
  pinned and filled; its proof keeps the forest construction, a note says that the pin is
  `lem:edge-splitting`'s case (i), and it follows that lemma.
- **F-239** · S · `lem:case-II-placement-old-rows-extract`, `lem:case-II-placement-block-independent`
  (`algebraic-induction/genericity-and-count.tex`): each states a special case of its pins, which
  other nodes cite in general. The first is stated for a realization of a graph $G_v^{ab}$ obtained
  by splitting off a vertex; its two pins hold for every body-hinge framework rigid on its vertex
  set (the first with nondegenerate hinges), and the proofs of `cor:panel-generic-rigid` and
  `cor:bodyhinge-generic-rigid` (`generic-lift.tex`) cite its dimension count for such a framework.
  The second is stated for rows of $R(G,q)$ at edges with and without the end $v$; its pin
  `linearIndependent_sum_pinned_block` holds for any two families of linear forms on the screw
  assignments, the second of which vanishes on the assignments that vanish off $v$, and
  `lem:rigidityRows-pinned-placement-rank-add` (`rigidity-matrix.tex`) uses it in that form.
  Stating the two generally, `F-152`'s third candidate, strengthens two statements.
  *Evidence:* read (the statements of `exists_independent_panelRow_subfamily_of_rigidOn`,
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` and
  `linearIndependent_sum_pinned_block`; the citing proofs).
  *Found:* round 5 task 3.8.
  *Disposition:* done (`0b8a78e0`): the first node states the pins' dimension of $Z(G,p)$ and, at
  nondegenerate hinges, the independent rows, for every body-hinge framework whose motions are
  constant on $\emptyset \neq V(G) \subseteq W$; the block lemma is the pin's, for any two finite
  families of forms; each `\cref` that read the special case now cites the claim.
- **F-252** · S · `cor:panel-generic-rigid`, `cor:bodyhinge-generic-tree-packing` and the four other
  pins of `F-207` (`generic-lift.tex`): the gap is wider than `F-207`'s "every graph that is itself
  minimal". `hfresh` ranges over every graph on the bodies and the labels, not over subgraphs of
  $G$, so under `hspan` and `hends` it depends only on $|V(G)|$, $|E(G)|$ and $D$: it fails whenever
  some minimal $k$-dof-graph on at most $|V(G)|$ bodies has exactly $|E(G)|$ edges. A tree of single
  and double edges on $m$ bodies is one, with any edge count from $m - 1$ to $2(m - 1)$. So the six
  pins say nothing about any graph with at most $2(|V| - 1)$ edges, $K_4$ at $d = 2$ among them (6
  edges; not itself minimal, as $K_4 - e$ is already rigid), and the band left unsettled is
  $2(|V| - 1) < |E(G)| \le D(|V| - 1)$. Task 2's scope sentences ("not settled" in between) stand;
  the phase's refactor (a) removes both gaps.
  *Evidence:* read (the two main results' statements, where `hfresh` quantifies over
  `G' : Graph α β`; `matroidMG`'s body and `matroidMG_indep_iff`'s statement, the $(D,D)$-count); a
  `lake lean` witness, script not retained: from `hH : H.IsMinimalKDof n c` and `E(H) = univ`,
  `hfresh c H hH` gives a label outside `univ`. The tree's minimality is argued, not witnessed: a
  base of $M(\tilde H)$ takes at most $D$ of a double edge's $2(D - 1)$ copies, which span two
  bodies, and the blocks' bounds add, so every base takes exactly $D$ of them ($D \ge 3$), meeting
  both fibers of $D - 1$, and all $D - 1$ copies of a single edge.
  *Found:* RECONCILE round 1 task 2.
  *Disposition:* reported (`notes/Reconcile-texts-cleanup.md`, *Candidates for the PI*).
- **F-260** · S · `lem:panel-hinge-dual-molecular` (`molecule-modelling.tex`): its unpinned (2), the
  rescaling of the normals $\bar c(v)$ by nonzero $\lambda_v$, is the case $q = \bar c$ of
  `lem:pencil-jj-rescale` (`main-component.tex`), whose pins
  `PanelHingeFramework.supportExtensor_ofNormals_smul` and `infinitesimalMotions_ofNormals_smul`
  (`Pencil/MainComponent/Bridge.lean`) state the hinges' scaling and the equal motion spaces at any
  normals over any field. Round 2's line kept the note "as no declaration states it"; task 9's note
  names the lemma instead. Sharing the two pins with the node is clean by the reach report: 1011
  pins (994 distinct), the missing edges still 4, the unbacked transitive ones 84 (85).
  *Evidence:* read (the two pins' statements); a `lake lean` witness (the two pins at the
  homogenized centres, `scratch/reconcile-statements/RescaleWitness.lean`, gitignored); measured
  (`--summary` on a scratch copy with the pins shared, `--tex-root`).
  *Found:* RECONCILE round 2 task 9.
  *Disposition:* done (`64a531db`): (2) is pinned on the two, beside (1)'s five, its note saying
  which clause each gives; a `lake lean` witness derives (1)'s conclusions at the rescaled normals
  from them and (1)'s pins (`scratch/reconcile-statements/T91Witness.lean`, gitignored).
- **F-273** · S · `lem:reduction-step-pos` (`molecular-induction.tex`;
  `splitOff_isMinimalKDof_of_pos`, `Induction/ForestSurgery/Reduction.lean`): since RECONCILE round
  3 task 15 (`F-097`) the pin uses `hD : 3 ≤ bodyBarDim n` only as `2 ≤ bodyBarDim n`, so the
  node's "Let $D \ge 3$" could read $D \ge 2$, the bound of the KT 4.2 and 4.3 pins it calls. The
  two are one condition: $D = n(n+1)/2$ takes no value 2, so the change would alter the form, not
  the theorem. The same holds of each `2 ≤ bodyBarDim n` and `3 ≤ bodyBarDim n` the chapter's pins
  take; `removeVertex_deficiency_gt_of_noRigid`'s docstring called its `3 ≤ D` sharp "at `D = 2`"
  (removed in task 15).
  *Evidence:* read (the body: `hD` feeds only `hD2` and `hD1`); a `lake lean` witness of
  `2 ≤ bodyBarDim n ↔ 3 ≤ bodyBarDim n` (`scratch/reconcile-lean/BodyBarDimTwo.lean`, gitignored).
  *Found:* RECONCILE round 3 task 15.
  *Disposition:* reported (`notes/Reconcile-lean-cleanup.md`, *Candidates for the PI*).
- **F-301** · S · `def:extensor-through-point` (`pencil.tex`; `ExtensorThroughPoint`,
  `Molecule/Pencil/Statement.lean`): the remark after the node says that the zero element passes
  through every point ("take every $p_i = q$"). That holds for $k \ge 2$, where two equal vectors
  have extensor $0$. At $k = 1$ the extensor of the one vector $q$ is $q$, and the zero element
  passes through no nonzero point. The chapter uses the notion at $k = 2$ alone, so the remark
  could say $k \ge 2$, a blueprint text outside round 3's surface; the docstring says it (task
  37.2).
  *Evidence:* read (the definition's body); a `lake lean` witness at $k = 1$ and at $k = 2$
  (`scratch/reconcile-lean/t372/Zero.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.2.
  *Disposition:* reported (`notes/Reconcile-lean-cleanup.md`, *Candidates for the PI*).
- **F-323** · S · `thm:theorem-55-6`, `thm:molecular-conjecture` and
  `thm:molecular-conjecture-multigraph` (`panel-layer.tex`; their pins
  `PanelHingeFramework.rankHypothesis_of_theorem_55_gen`, `PanelHingeFramework.molecular_conjecture`
  and `molecular_conjecture_multigraph`, `AlgebraicInduction/Theorem55.lean`, three main results):
  each pin takes a `[DecidableEq β]` its statement does not use (hence its `set_option
  linter.unusedDecidableInType false in`), which `classical` supplies. `TACTICS-QUIRKS.md` §115's
  rule 1 would drop it, which changes a main result's statement; its rule 3 keeps the suppression
  meanwhile. The phase restates the three (S1, S2) and can drop it then; the nodes state no
  decidability.
  *Evidence:* read (the statements); a `lake lean` witness: the three stated without the instance
  and proved by the theorems under `classical`, with no warning, on the three standard axioms
  (`scratch/reconcile-lean/t38/MainDec.lean`, gitignored).
  *Found:* RECONCILE round 3 task 38.
  *Disposition:* reported (`notes/Reconcile-lean-cleanup.md`, *Candidates for the PI*).
- **F-324** · S · `thm:theorem-55` (`panel-layer.tex`; its pin
  `PanelHingeFramework.theorem_55_minimalKDof_gen`, `AlgebraicInduction/Theorem55.lean`, a main
  result): the pin's `hD : 3 ≤ bodyBarDim n` follows from `hk1 : 1 ≤ k` and `hn : bodyBarDim n =
  screwDim k` (`three_le_screwDim`), and its proof uses it only to pass it on, to
  `theorem_55_minimalKDof_k_all_k` and `case_I_hcontract_gen` and, by `omega`, to the base and the
  two cut-edge lemmas. Dropping it changes a main result's statement, so it stays until the phase
  restates it; and while it stays, so do the derivable `hD`s of the chain below it (`F-293`,
  `F-297`, `F-298`), as dropping them would leave the main result's unused (`lake lint`). With it
  would go the `hD`s of `theorem_55_minimalKDof_k_all_k`, `theorem_55_base_producer_gen`,
  `case_cut_edge_realization_gen`, `case_cut_edge_realization_gp_gen`,
  `finrank_span_rigidityRows_cutEdge_eq`, `case_I_hcontract_gen`, `case_I_dispatch_gen`,
  `case_I_realization_h65_gen`, `case_I_realization_nonsimple_gen`, `case_I_realization_all_k_gen`
  and `case_III_realization_all_k`.
  *Evidence:* read (the statement and its proof); a `lake lean` witness: the pin stated without
  `hD` and proved by it with `hn ▸ three_le_screwDim hk1`, on the three standard axioms
  (`scratch/reconcile-lean/t381/HD.lean`, gitignored).
  *Found:* RECONCILE round 3 task 38.1.
  *Disposition:* reported (`notes/Reconcile-lean-cleanup.md`, *Candidates for the PI*).

## L — Lean

- **F-013** · L · `SimpleGraph.Henneberg.typeII_isLaman` (`Henneberg.lean`): it takes `hab : a ≠ b`
  beside `hG_ab : G.Adj a b`, which implies it (`SimpleGraph.Adj.ne`). `thm:typeII-isLaman` now
  states only "$ab$ is an edge". The theorem has no Lean caller, so the binder can go alone.
  *Evidence:* read (the statement of `typeII_isLaman`; a `grep` finds no caller).
  *Found:* round 1 task 3.
  *Disposition:* done (task 8): `hab` dropped, the tightness branch reading `a ≠ b` off `hG_ab`,
  and the docstring states the hypotheses the theorem takes. Before: reported
  (`notes/Prose-report.md`, L7).
- **F-017** · L · `IsTightOn.union_with_bonus`, `IsTightOn.insert_vertex_with_edges`
  (`Sparsity.lean`): each takes `hF_finite : F.Finite`, which follows from `hF_sub`, since
  `edgesIn` of a finite vertex set is finite (`edgesIn_finite`). The blueprint statements no longer
  name it. The callers pass `Set.toFinite _` or `Set.finite_singleton _`.
  *Evidence:* read (both statements, and their two callers in `Sparsity.lean`).
  *Found:* round 1 task 5.2.
  *Disposition:* done (task 8): `hF_finite` dropped from both, each deriving it from `hF_sub` by
  `edgesIn_finite`; the callers `contradiction_one_pair` and `contradiction_two_pair` pass one
  argument fewer, and `contradiction_one_pair`'s `[Finite V]`, used only by its `Set.toFinite _`,
  went too (`lake lint`'s `unusedArguments`). Before: reported (`notes/Prose-report.md`, L7).
- **F-018** · L · `SimpleGraph.IsSparse.typeII_reverse_blocker` (`Sparsity.lean`): its docstring
  and the section docstring above it say "distinct vertices `x, y`", but the statement does not
  assume `x ≠ y`. (At `x = y` the hypothesis fails, since the added pair is a loop and is dropped.)
  *Evidence:* read (the statement and the two docstrings).
  *Found:* round 1 task 5.2.
  *Disposition:* done (task 25): both docstrings drop "distinct", and the section's says why
  the statement needs no `x ≠ y`. Before: reported (`notes/Prose-report.md`, L4).
- **F-021** · L · `SimpleGraph.Henneberg.typeII_isGenericallyRigidInj_two_of_nonCollinear`
  (`HennebergRigidity.lean`): it takes `hab : a ≠ b` beside `hLI_abc : LinearIndependent ℝ ![p b -
  p a, p c - p a]`, which implies it (the first vector is nonzero). The body uses `hab` only to get
  `p a ≠ p b`. `thm:typeII-isGenericallyRigidInj-two-of-nonCollinear` now states only the
  non-collinearity. Its one caller, `typeII_isGenericallyRigidInj_two`, passes `hab`.
  *Evidence:* read (the statement and body; a `grep` finds the one caller).
  *Found:* round 1 task 5.5.
  *Disposition:* done (task 8): `hab` dropped, `p a ≠ p b` read off `hLI_abc`; the caller passes
  one argument fewer. Before: reported (`notes/Prose-report.md`, L7).
- **F-022** · L · `typeI_isInfinitesimallyRigid_extend`, `typeII_isInfinitesimallyRigid_extend`
  (`HennebergRigidity.lean`): their docstrings contradict their declarations. The first calls
  itself "the rank-nullity heart of `typeI_isGenericallyRigid_two`", which names no declaration (the
  caller is `typeI_isGenericallyRigidInj_two`). The second lists `G.Adj a b` among its hypotheses;
  the statement does not take it, and the proof treats the edge $ab$ only when it is present.
  *Evidence:* read (both statements and docstrings; a `grep` for `typeI_isGenericallyRigid_two`).
  *Found:* round 1 task 5.5.
  *Disposition:* done (task 25): the first names `typeI_isGenericallyRigidInj_two`; the second
  drops `G.Adj a b` and says the statement does not ask it. Before: reported
  (`notes/Prose-report.md`, L4).
- **F-023** · L · `SimpleGraph.trivialMotions` (`TrivialMotions.lean`): its docstring cites
  `trivialMotions_three_le_finrank_of_affinelySpanning_two`, which no longer exists (only
  `notes/FRICTION.md` still names it), and the docstring of the section on the $d$-general bound
  says "The dim-2 case below is its `d = 2` instance", but the file has no such case. The docstring
  of `rigidityMap_ker_finrank_ge_of_affinelySpanning` credits the count to Asimow–Roth, a credit
  `trivial-motions.tex` dropped as unverified (task 5.6).
  *Evidence:* read (the file; a `grep` over the repository for the cited name).
  *Found:* round 1 task 5.6.
  *Disposition:* done (task 25): `trivialMotions` cites the lower bound it has
  (`trivialMotions_finrank_ge_of_affinelySpanning`), the section names the planar case as the
  instance at `d = 2`, and the kernel bound credits Jordán 2016, p. 36, and Whiteley 1996, §11.1,
  as `trivial-motions.tex` does. Before: reported (`notes/Prose-report.md`, L5).
- **F-024** · L · `SimpleGraph.trivialMotionFamily_linearIndependent` (`TrivialMotions.lean`): its
  `[Finite V]` is unused. The `@[nolint unusedArguments]` comment calls the linter's report a false
  positive, but the theorem elaborates without the binder, with the same proof minus its
  `Fintype.ofFinite` line. `lem:trivialMotionFamily-linearIndependent` states "Let $V$ be finite",
  as the pin does. Its one caller, `trivialMotions_finrank_ge_of_affinelySpanning`, needs
  `[Finite V]` for the dimension.
  *Evidence:* read (the statement and body); a `lake lean` witness (the theorem restated without
  `[Finite V]`, the proof copied with that line deleted; it elaborates with no output).
  *Found:* round 1 task 5.6.
  *Disposition:* done (task 8): `[Finite V]`, the `Fintype.ofFinite` line and the `@[nolint
  unusedArguments]` with its comment dropped; `lem:trivialMotionFamily-linearIndependent` no
  longer asks $V$ finite. Before: reported (`notes/Prose-report.md`, L6).
- **F-030** · L · `MatroidIdentification.lean`, `LinearRigidityMatroid.lean`: docstrings that
  contradict the declarations. In the first, the section header "`|E|`-induction: every sparse
  graph has a row-independent placement" and the docstring of
  `exists_distinct_rowIndependent_placement_dim_two` ("Phase 7's `|E|`-induction") call the
  induction one on edges, while `IsSparse.exists_rowIndependent_placement` inducts on
  `Fintype.card V`, as the header's own body says. In the second, the module docstring calls the
  identification `linearRigidityMatroid V 2 p = rigidityMatroid V` "the eventual Phase 8 target"
  of a file that lands only "the definition skeleton plus the independence bridge", and
  `linearRigidityMatroid`'s docstring calls it "the Phase 8 target"; the file proves it
  (`linearRigidityMatroid_eq_rigidityMatroid`).
  *Evidence:* read (the bodies of `IsSparse.exists_rowIndependent_placement` and
  `linearRigidityMatroid_eq_rigidityMatroid`, and the docstrings named).
  *Found:* round 1 task 5.10.
  *Disposition:* done (task 25): the induction on `|V|` named so (and Jordán's on `|E|`); the
  identification called proved, not a target. Before: reported (`notes/Prose-report.md`, L12).
- **F-032** · L · `SimpleGraph.countMatroid` (`CountMatroid.lean`): its docstring says that outside
  $\ell < 2k$ "the augmentation axiom can fail (e.g. `(3, 6)` in 3-dimensional rigidity)". By
  `IsSparse`'s definition a $(3,6)$-sparse graph has no edges (a pair $s$ has $6 \le 3|s|$, so it
  spans none), and the $(3,6)$-sparse edge sets form a matroid in which no edge is independent.
  `count-matroid.tex` made the same claim ("the bases need not have equal cardinality, for instance
  $(3, 6)$-tight graphs"), which task 5.11 dropped.
  *Evidence:* read (the body of `IsSparse`); a `lake lean` witness (every $(3,6)$-sparse
  `SimpleGraph V` is `⊥`; it elaborates with no output).
  *Found:* round 1 task 5.11.
  *Disposition:* done (task 25): the `(3, 6)` example dropped; the docstring says the
  construction needs the regime, where its augmentation lemma is proved. Before: reported
  (`notes/Prose-report.md`, L4).
- **F-033** · L · `CombinatorialRigidity.Search.reachableFinding`, `reachClosureComputable`
  (`Search/DFS.lean`): the search marks only the vertices of the current walk, since every
  recursive call from `v` gets the same `insert v visited`. When no vertex satisfies `P` it
  therefore follows every simple walk from `v`, exponentially many in general, and
  `reachClosureComputable` runs it once per vertex. The section docstring above
  `reachClosureComputable` calls this "$O(n)$ DFS invocations — quadratic in the worst case", and
  calls the search "iterative". Lee–Streinu's $O(m_a n)$ bound for the basic pebble game (§3,
  p. 1430) counts each search as linear in $|D|$, which a search keeping one marked set across
  sibling calls would be. `Exec.lean`'s docstrings and `executable.tex` say the pebble game runs in
  polynomial time; no bound is proved (task 5.16 checks the chapter). `dfs.tex` now describes the
  per-walk marking (task 5.12).
  *Evidence:* read (the body of `reachableFindingAux`); measured, script not retained: a `lake
  lean` file timing `reachableFinding` with `P` false on a chain of $n$ diamonds ($3n + 1$
  vertices, $4n$ arcs, $2^n$ simple walks end to end) took 2, 6, 29, 128, 631 and 3071 ms at
  $n = 8, 10, \ldots, 18$.
  *Found:* round 1 task 5.12.
  *Disposition:* done (tasks 17, 18 and 20): the search threads one marked set through its sibling
  calls, `reachableFinding_sound` and `_complete` re-proved, `dfs.tex` restated (task 17); the
  timing re-measured by the committed `scripts/DFSTiming.lean`, the old search beside the new,
  2196 ms and 157 µs at $n = 18$, the new one marking $3n + 1$ vertices (task 18); the texts
  rewritten (task 20): the section docstring above `reachClosureComputable` says what the closure
  runs, that no bound is proved and what the script measures, without "quadratic" or "iterative";
  `Exec.lean`'s docstrings claim no bound; and `pebble-game.tex`'s paragraph on Lee–Streinu's count,
  which task 17 left describing the per-walk marking, says that the search enters each vertex at
  most once and that no bound is proved. The closure's one search per vertex is `F-277`'s. Before:
  reported (`notes/Prose-report.md`, L1).
- **F-035** · L · `PebbleGame/Basic.lean`, `PebbleGame/Algorithm.lean`: docstrings that describe
  other states of the code. Basic.lean's *Path reversal* section header says the lemmas about
  `out`, `peb`, `span` and `outOn` "follow in a subsequent commit"; they are in that section.
  Algorithm.lean's *Try-reach-pebble* header and `tryReachPebbleWith`'s docstring say soundness and
  completeness theorems "will live" or "will land" on `tryReachPebbleWith`. The docstrings of
  `tryAddEdgeWith`, `tryAddEdge`, `tryAddEdgeWith_reachable` and `runPebbleGameWith` record Phase
  11's reshape ("was `some D'`", "was `Option (PartialOrientation V)`").
  *Evidence:* read (the docstrings named, against the two files).
  *Found:* round 1 task 5.13.
  *Disposition:* done (task 26): the *Path reversal* header says what the section proves; the
  *Try-reach-pebble* header and `tryReachPebbleWith`'s docstring say that
  `tryReachPebbleWith_eq_none_imp` is stated for it; the docstrings of `tryAddEdgeWith`,
  `tryAddEdge`, `tryAddEdgeWith_reachable`, `tryAddEdgeWith_underline`, `runPebbleGameWith` and
  `runPebbleGameWith_reachable` describe the return type as it is, without the reshape. Before:
  reported (`notes/Prose-report.md`, L12).
- **F-039** · L · `runPebbleGameWith_sound`, `runPebbleGameWith_underline_eq`,
  `runPebbleGameWith_correct` (`PebbleGame/Correctness.lean`, `Algorithm.lean`): the binder
  `hloops : ∀ p ∈ edges, p.1 ≠ p.2` follows from `himg`, since each entry's unordered pair is an
  edge of `G` and so not a loop. `runPebbleGame_edges_discharges` proves it separately.
  *Evidence:* read (the three statements); a `lake lean` witness deriving `hloops` from `himg` in
  three lines (`List.mem_toFinset`, `SimpleGraph.ne_of_adj`).
  *Found:* round 1 task 5.14.
  *Disposition:* done (task 9): `hloops` dropped from the three, `runPebbleGameWith_underline_eq`
  deriving it from `himg` (`SimpleGraph.ne_of_adj`); `runPebbleGame_edges_discharges` lost its
  no-loops conjunct, which no node states, and `edgeListSorted_no_loops` (unpinned), left without a
  caller, was deleted; the callers in `Correctness.lean` and `Exec.lean` follow. Before: reported
  (`notes/Prose-report.md`, L7).
- **F-040** · L · `PebbleGame/Correctness.lean`, `Algorithm.lean`: docstrings that name blueprint
  labels or declarations that do not exist, or describe other states of the code. Three labels do
  not exist: `lem:pebble-game-tryAddEdge-iff-independent` (`tryAddEdgeWith_isSparse`, "⇒ half of"),
  `thm:pebble-game-completeness` (the module docstring) and `thm:runPebbleGameWith-correct`
  (`runPebbleGameWith_underline_eq`). `span_succ_le_edgesIn_ncard_of_subset` and
  `tryReachPebbleWith_eq_none_imp` name `tryAddEdgeWith_eq_none_imp_exists_witness` and
  `tryAddEdgeWith_isSome` as their consumers; neither exists. `runPebbleGameWith_sound`'s docstring
  says its hypothesis is `some D'` (it is `.inr D'`). The *Completeness* section header says the
  graph form of Lemma 13 is what "the upcoming `tryAddEdgeWith` completeness recursion will
  iterate"; there is no such recursion, and no main result uses the lemma. `F-035` records the same
  kind of docstring in `Basic.lean` and `Algorithm.lean`.
  *Evidence:* read (the docstrings named; `grep` for the labels in `blueprint/src/` and for the
  names in the Lean).
  *Found:* round 1 task 5.14.
  *Disposition:* done (task 26): `tryAddEdgeWith_isSparse` names
  `lem:pebble-game-tryAddEdgeWith-isSparse` and `runPebbleGameWith_underline_eq`
  `lem:runPebbleGame-underline-eq`, and the module docstring no longer names
  `thm:pebble-game-completeness`; the consumers named are `tryAddEdgeWith`'s body (of
  `tryReachPebbleWith_eq_none_imp`) and `WorkhorseWitness.certifies_against` (of
  `span_succ_le_edgesIn_ncard_of_subset`); `runPebbleGameWith_sound` says `.inr D'`; the
  *Completeness* header lists the section's lemmas and says that the correctness proof uses
  neither Lemma 13 for a graph nor `tryAddEdgeWith_isSparse`. Before: reported
  (`notes/Prose-report.md`, L10).
- **F-045** · L · `runPebbleGame.aux` and the verdict's docstrings (`PebbleGame/Correctness.lean`):
  `runPebbleGame.aux`'s docstring says that `certifies_against` "calls
  `independent_brings_pebble_simpleGraph_form` whose size step uses `ℓ < 2 * k`". The body of
  `certifies_against` does not call it: it uses `Reachable.pebOn_add_span_add_outOn` and
  `span_succ_le_edgesIn_ncard_of_subset`, and gets `ℓ ≤ k * V'.card` from `2 ≤ V'.card` itself.
  The docstrings of `PebbleGameResult`, `PebbleGameResult.isAccept`, `runPebbleGame` and the
  section header above `runPebbleGameWith_correct` record Phase 11's reshape ("since retired", "the
  (now-retired) `Sum`-returning `runPebbleGameExec`", "maximally reshapes the previous Phase 11
  Layer 4 design"), the kind `F-035` records in `Basic.lean` and `Algorithm.lean`.
  *Evidence:* read (the body of `certifies_against` and the docstrings named).
  *Found:* round 1 task 5.15.
  *Disposition:* done (task 26): `runPebbleGame.aux`'s docstring says that `certifies_against`
  gets its size step from `ℓ < 2 * k` and the two ends of the witness's edge in `V'`, and the
  module docstring no longer routes `certifies_against` through Lemma 13; the docstrings of
  `PebbleGameResult`, `PebbleGameResult.isAccept`, `runPebbleGame`, `runPebbleGame_isAccept_iff`,
  the verdict's section header and the correctness section's describe the code as it is. Before:
  reported (`notes/Prose-report.md`, L12).
- **F-047** · L · `Main.lean`, `PebbleGame/Examples.lean`, `lakefile.toml`; `DESIGN.md` *One
  `Decidable` instance per project predicate*: running-time and `decide` claims beyond `F-033`'s.
  `Main.lean`'s module docstring and `lakefile.toml`'s comment on the `pebble-game` target say that
  the classification runs in polynomial time, and `Examples.lean`'s module docstring cites "the
  polynomial-time guarantee of `lake exe pebble-game`" and "a sub-second bytecode-interpreter
  run". No bound is proved (`F-033`). `DESIGN.md`'s section says the same, and that `decide`
  unfolds the instances' bodies. It does not: `reachableFindingAux` and `tryAddEdgeWith` are
  defined by well-founded recursion and are irreducible. `Main.lean` also points at a "three-row
  matrix" in `executable.tex` *Runtime and backends*, which task 5.16 made a list of three ways to
  run a decision procedure. `Main.lean` and the comment call the input "whitespace-separated", but
  `parsePair` splits on spaces only, so a tab makes a line malformed; and the comment says the
  classification goes through `instDecidableIsLaman` and `instDecidableIsSparse`, where
  `classify` calls `runPebbleGameExec` directly.
  *Evidence:* read (the docstrings, the comment and the section named; the bodies of `parsePair`
  and `classify`); measured, script not retained: `by decide` fails on
  `(⊤ : SimpleGraph (Fin 2)).IsLaman` and on `Examples.k4MinusE.IsLaman`, its reduction stuck at
  `runPebbleGameExec`; `decide +kernel` succeeds on the first and fails on the second;
  `getReducibilityStatus` reports both definitions `irreducible`; `native_decide` proves
  `k4MinusE.IsLaman` and `¬ k4.IsLaman`; `"3\t4".splitOn` is one token.
  *Found:* round 1 task 5.16.
  *Disposition:* done (tasks 18, 19 and 20): `scripts/DFSTiming.lean` holds five of these facts as
  tactics that fail the file if one changes: `decide` and `decide +kernel` fail on
  `k4MinusE.IsLaman`, `decide +kernel` proves `(⊤ : SimpleGraph (Fin 2)).IsLaman`, and
  `native_decide` proves `k4MinusE.IsLaman` and `¬ k4.IsLaman` (task 18); `parsePair` splits on
  `Char.isWhitespace`, so a tab, or a CRLF file's carriage return, no longer makes a line
  malformed; `lake exe pebble-game` on `examples/k4-minus-e.txt` with tabs prints `LAMAN`, where
  task 18's tree printed "malformed header" (task 19); the texts rewritten (task 20): `Main.lean`'s
  module docstring, `Examples.lean`'s and the `lakefile.toml` comment claim no bound, name what
  `classify` calls and the input's separators, and point at `executable.tex`'s list;
  `DESIGN.md`'s section says what `decide` and `decide +kernel` do, with the script's facts and
  `F-276`'s reasons, and the pebble-game style island, `Search/DFS.lean`'s and `Basic.lean`'s
  module docstrings and ROADMAP's convention no longer say that `decide` fires; `executable.tex`
  states the facts for `decide +kernel` and `native_decide`, and the input's tabs and carriage
  returns. Before: reported (`notes/Prose-report.md`, L2).
- **F-055** · L · `Graph.exists_forestPacking_cover_of_isSparse_restrict` (`BodyBar/KFrame.lean`;
  `lem:k-frame-forest-packing-of-sparse`): it derives the forward half of `Graph.tutte_nash_williams`
  (`TreePacking.lean`, which `KFrame.lean` imports) again, at $G \restriction E'$ and without
  disjointness, through `unionPow_cycleMatroid_indep_iff_isSparse_restrict` and
  `Matroid.union_indep_iff`. Both its callers, `linearIndepOn_kFrameRow_of_isSparse_restrict` and
  `exists_endpoints_linearIndependent_rigidityRow` (`GenericLift.lean`), then
  disjointify the cover with `Fintype.exists_disjointed_le` in the same five lines that
  `tutte_nash_williams`'s proof uses. One lemma giving a disjoint cover would serve all three.
  *Evidence:* read (the bodies of the four declarations).
  *Found:* round 2 task 2.2.
  *Disposition:* done (task 13): the lemma moved to `TreePacking.lean` and gives a disjoint cover
  (`disjointed`); `tutte_nash_williams`'s converse is it at `E' = E(G)`, and the two callers lost
  their disjointifications; the node states the disjoint forests, and the theorem's proof `\uses`
  it.
- **F-057** · L · docstrings of `BodyBar/` (`body-bar.tex`'s Tay nodes): three disagree with
  the declarations or the sources. `Graph.isSpanningTreePacking_of_isTight` credits Whiteley 1988
  Theorem 13, which is about frameworks on the flat torus (p. 249; only its (ii)⇔(iii) is the
  count). `exists_isIsostatic_of_isTight`'s docstring assumes a connected multigraph and a
  spanning-tree packing; its statement assumes tightness only, and its proof uses a forest packing.
  `Framework.lean`, `TayTheorem.lean` and `BodyHinge.lean` call the standard-basis vectors
  "degenerate two-extensors" that lie on the Plücker variety "vacuously"; they satisfy the
  quadratic Plücker relations and are the Plücker vectors of lines (Whiteley 1988, p. 243).
  *Evidence:* read (the three declarations' statements and bodies; Whiteley 1988 pp. 243, 249, in
  `.refs/`).
  *Found:* round 2 task 2.3.
  *Disposition:* done (task 27): `isSpanningTreePacking_of_isTight` cites no Whiteley theorem
  (the chapter's node credits none); `exists_isIsostatic_of_isTight`'s docstring assumes tightness
  only and names the forest packing; the three files call a standard basis vector the Plücker
  vector of a line (Whiteley 1988, proof of Theorem 8, p. 243) and the placement unconstrained.
- **F-061** · L · `BodyHingeFramework.linearIndependent_hingeRow_forest` and
  `exists_independent_rigidityRows_of_forest` (`Molecular/RigidityMatrix/Basic.lean`): the names
  and docstrings speak of a spanning forest, but the hypothesis `hsep` (no other end of an edge is
  the private end of any edge) holds only when every component of the edges is a star; a path with
  three edges fails it. The rows of any forest of nondegenerate hinges are independent (remove a
  leaf), but no declaration states it. `def:rigidity-matrix`'s prose claimed "any spanning forest";
  task 2.5 states the hypothesis instead.
  *Evidence:* read (the two statements and the first body).
  *Found:* round 2 task 2.5.
  *Disposition:* done (task 7): the two renamed `linearIndependent_hingeRow_starForest` and
  `exists_independent_rigidityRows_of_starForest`, their docstrings stating the star forest (and a
  path with three edges as a forest outside it), with `lem:own-end-rows-independent`'s pins and
  the two other docstrings that named them. The forest lemma, which no declaration states, is the
  phase's (c) (`notes/Reconcile.md` §3). Before: reported (`notes/Prose-report.md`, L4).
- **F-063** · L · `BodyHingeFramework.screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  (`Molecular/AlgebraicInduction/PanelLayer.lean`): its hypothesis asks $C(e) \neq 0$ at every
  edge label, also at labels that are not edges of $G$, where the extensor does not affect the
  motions. The relative bound `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
  in the same file asks it only at the edges of $G$.
  *Evidence:* read (the two statements).
  *Found:* round 2 task 2.5.
  *Disposition:* done (task 12): the hypothesis is `∀ e u v, F.graph.IsLink e u v →
  F.supportExtensor e ≠ 0`, the relative bound's; its four callers (`rigidityMatrix_prop11`, the
  two forms of the molecular conjecture, `molecule_rank_upper_bound`'s proof) pass their `∀ e`
  form at the edges and keep it (the first three state it: two main results, and S18's node, the
  phase's); the notes of `rem:molecular-conjecture-essential` and the molecule rank formula no
  longer say the bound asks every label. Before: reported (`notes/Prose-report.md`, L7).
- **F-064** · L · `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`
  (`Molecular/RigidityMatrix/Bricks.lean`): its docstring names the node
  `lem:rigidityRows-cut-rank-add`, which does not exist; the declaration is pinned on
  `lem:block-rank-cut`.
  *Evidence:* read (the docstring; a `grep` for the label in `blueprint/src/`).
  *Found:* round 2 task 2.6.
  *Disposition:* done (task 32): the lead names `lem:block-rank-cut`. Before: reported
  (`notes/Prose-report.md`, L10).
- **F-069** · L · docstrings of four pins in `rigidity-matrix.tex`'s Case I lemmas name the wrong
  node: `infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton`,
  `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton` and
  `finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`
  (`AlgebraicInduction/Coupling.lean`) name `lem:rigidityRows-splice-rank-add`, and are pinned on
  `lem:extProj-preserves-rank-of-inter`; `finrank_span_rigidityRows_ofNormals_relabel_eq`
  (`CaseI.lean`) names `lem:case-I-realization-all-k`, which does not exist.
  *Evidence:* read (the docstrings; a `grep` for the labels in `blueprint/src/`).
  *Found:* round 2 task 2.7.
  *Disposition:* done (task 34.1): `finrank_span_rigidityRows_ofNormals_relabel_eq`'s lead names its
  node `lem:rank-transport-relabel-of-le-finrank` (task 34), and the leads of `Coupling.lean`'s
  three name `lem:extProj-preserves-rank-of-inter` (task 34.1). Before: reported
  (`notes/Prose-report.md`, L10).
- **F-070** · L · `PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj`
  (`AlgebraicInduction/CaseI.lean`): its hypothesis `hcLoop` (the contraction has no loops)
  follows from `hKmin` (it is a minimal $k$-dof-graph) by `Graph.loopless_of_isMinimalKDof`.
  *Evidence:* read (the statement and body; `Graph.loopless_of_isMinimalKDof`, `Deficiency.lean`).
  *Found:* round 2 task 2.7.
  *Disposition:* done (task 12): `hcLoop` dropped, the body deriving it from `hKmin` by
  `Graph.loopless_of_isMinimalKDof`; the caller, `case_I_realization_all_k_gen`, passes one argument
  fewer; `lem:rank-polynomial-IH-relabel-proj`'s note no longer calls it a separate hypothesis.
  Before: reported (`notes/Prose-report.md`, L7).
- **F-074** · L · docstrings in `Molecular/Deficiency.lean`: `Graph.matroidMG`'s says that
  $M(\tilde G)$ is "the boundary regime `ℓ = 2k = D`", not "the matroidal regime `ℓ < 2k` of
  `CountMatroid.lean`". The $(D,D)$ count has $\ell = k$, inside $\ell < 2k$; `countMatroid` does
  not apply because it is a matroid on `Sym2 V`, with no parallel edges. The docstrings of
  `matroidMG_indep_iff` and `loopless_of_isMinimalKDof` call the independence criterion
  "boundary-regime cleanliness".
  *Evidence:* read (the docstrings; `countMatroid`'s signature, `CountMatroid.lean`).
  *Found:* round 2 task 2.8.
  *Disposition:* done (task 29): `matroidMG`'s docstring says that `M(G̃)` is the union of `D`
  copies of the cycle matroid of `G̃`, restricted to `E(G̃)`, and that `countMatroid` does not apply
  as a matroid on `Sym2 V`; `matroidMG_indep_iff` and `loopless_of_isMinimalKDof` without
  "boundary regime" and "cleanliness"; reported (`notes/Prose-report.md`, L4).
- **F-075** · L · `Graph.deficiency_eq_of_cutEdges_ncard_le_one` (`Molecular/Deficiency.lean`): its
  hypothesis `hD : 1 ≤ bodyBarDim n` is unused (the proof discards it, "part of the public API").
  `exists_cut_decomposition_of_not_twoEdgeConnected` and `Graph.deficiency_induce_union_singleton`
  (`Molecule/Pencil/Motive.lean`) take it only to pass it on. `lem:cut-edge-decomposition` states
  its (1)–(3) without it, so dropping it makes the three pins match.
  *Evidence:* read (the three statements and bodies).
  *Found:* round 2 task 2.8.
  *Disposition:* done (task 10): `hD` dropped from the three; the callers follow, among them
  `Graph.deficiency_induce_union_range_of_bridgePath` (a pin of `thm:pencil-x0-bridge`) and
  `hlb_induce_of_isNondegPencilRealization_induce_union_singleton` (unpinned), which only passed
  it on and lost it too. No node states it. Before: reported (`notes/Prose-report.md`, L6).
- **F-077** · L · docstrings and a binder of `deficiency.tex`'s pins (`Molecular/Deficiency.lean`,
  `MainComponent/Ear.lean`): `isSparse_diff_singleton_of_isCircuit`'s docstring says that the bound
  $|X| > D(|V(X)| - 1)$ for a circuit $X$ needs the reverse half of `thm:def-eq-corank`, "deferred
  with that node"; `circuit_ncard_gt` (`Induction/Operations.lean`) proves it from the minimality of
  $X$ alone, and the theorem is proved. `matroidMG_restrict_mulTilde`'s docstring names
  `lem:subgraph-minimality` as its node; it is pinned at `lem:matroid-restrict-subgraph`.
  `deficiency_induce_le_of_ear_of_merge`'s hypothesis `_hinj` (the ear's interior vertices are
  distinct) is unused.
  *Evidence:* read (the docstrings; the bodies of `circuit_ncard_gt` and
  `deficiency_induce_le_of_ear_of_merge`).
  *Found:* round 2 task 2.9.
  *Disposition:* done (task 29): `_hinj` dropped, its caller following, and
  `lem:deficiency-ear-merge` restated for a walk (task 10); `isSparse_diff_singleton_of_isCircuit`'s
  docstring names `lem:circuit-induces-rigid` and `circuit_ncard_gt` for the rest of KT Lemma 3.4,
  and `matroidMG_restrict_mulTilde`'s names its node (task 29); reported
  (`notes/Prose-report.md`, L6).
- **F-080** · L · docstrings in `Molecular/Deficiency.lean` around `thm:def-eq-corank`:
  `isBase_ncard_add_deficiency_eq`'s says that it "closes" `prop:rigidity-matrix-prop11`, which
  `rigidityMatrix_prop11` (`AlgebraicInduction/PanelHinge.lean`) proves; `rank_add_deficiency_le`'s
  calls the reverse inequality "the remaining JJ09 min–max content", which `le_rank_add_deficiency`
  proves; `rk_cycleMatroid_within_parts_le`'s and its section's call it "`thm:def-eq-corank`, piece
  1", and it is pinned at `lem:rk-within-parts`; `IsKDof.exists_isBase_isForestPacking`'s calls a
  Phase-22 construction "the remaining Track-A obstruction". Their credits are `F-081`'s.
  *Evidence:* read (the docstrings and the four statements).
  *Found:* round 2 task 2.10.
  *Disposition:* done (task 29.1): `isBase_ncard_add_deficiency_eq`'s docstring without
  `prop:rigidity-matrix-prop11`, `rank_add_deficiency_le`'s naming `le_rank_add_deficiency` for
  the reverse inequality, `rk_cycleMatroid_within_parts_le`'s and its section's naming
  `lem:rk-within-parts`, and `IsKDof.exists_isBase_isForestPacking`'s a step of
  `lem:deficiency-zero-iff-tree-packing`, without the Phase-22 paragraph; their credits are
  `F-081`'s; reported (`notes/Prose-report.md`, L12).
- **F-085** · L · docstrings of `molecular-induction.tex`'s first pins (`Induction/Operations.lean`,
  `Induction/ReducibleVertex.lean`): `inducedSpan`'s names `def:graph-operations` for
  `def:induced-span`. Those of `rank_matroidMG_of_isKDof_zero`, `contract_matroidMG_rank` and
  `contract_matroidMG_deficiency_eq` name `lem:contraction-minimality`, while they are pinned at
  `lem:rigid-full-rank`, `lem:contract-rank-bridge` and `lem:contract-deficiency-conservation`; the
  section before the third calls the minimality half "scheduled next" (it is
  `contract_minimality_transport`, `Induction/Contraction.lean`). `edgeSplit`'s says that splitting
  off its new vertex gives back $H$, "established later"; no declaration states it, and only two
  simp lemmas mention `edgeSplit`.
  *Evidence:* read (the docstrings; a `grep` for `edgeSplit`).
  *Found:* round 2 task 2.11.
  *Disposition:* done (task 30.1): in `Induction/Operations.lean`,
  the leads of `inducedSpan`, `rank_matroidMG_of_isKDof_zero`, `contract_matroidMG_rank` and
  `contract_matroidMG_deficiency_eq` name `def:induced-span`, `lem:rigid-full-rank`,
  `lem:contract-rank-bridge` and `lem:contract-deficiency-conservation`, and the section before
  them names `contract_minimality_transport` for the minimality half (task 30); `edgeSplit`'s says
  what the definition does, KT's edge-splitting when its new vertex and edges are new, and no
  longer claims an identity no declaration states (task 30.1); reported (`notes/Prose-report.md`,
  L10).
- **F-088** · L · the balanced-partition pins (`Induction/Operations.lean`,
  `Induction/ReducibleVertex.lean`, `Induction/ForestSurgery/Reduction.lean`):
  `exists_balanced_forest_packing` repeats the move of `exists_packing_move_of_not_inc` inline, while
  its docstring says that it uses it. The docstrings, or the sections before them, are stale: the
  section of `kt_lemma_41_overquantified` says that the balanced packing was neither justified nor
  recovered and gates "the deferred surgery TODO"; those of `isBase_vfiber_ncard_ge`,
  `acyclicSet_insert_vfiber_of_not_inc` and `exists_packing_move_of_not_inc` call the descent open
  or "the remaining surgery work"; `acyclicSet_insert_vfiber_of_not_inc`'s says the step holds
  because $v$ has degree two, which its statement does not assume. Six of them name
  `lem:forest-surgery-split`, not the node that pins them, and that of
  `matroidMG_indep_iff_exists_forest_packing` credits "Nash-Williams 1966 / Edmonds" (`F-053`).
  *Evidence:* read (the docstrings and sections; the body of `exists_balanced_forest_packing`).
  *Found:* round 2 task 2.12.
  *Disposition:* done (task 31.1): the descent calls the move, whose conclusion now states the
  re-choice (`F-272`) (task 14); in `Induction/Operations.lean`, the section before
  `kt_lemma_41_overquantified` follows `rem:kt-lemma-41` (a base has the balanced partition,
  `lem:balanced-forest-packing`), and the leads of that lemma and of
  `matroidMG_indep_iff_exists_forest_packing` name `ex:kt-41-overquantified` and
  `lem:forest-packing-decomp`, the second with `lem:union-indep-iff` for the union and without the
  credit (task 30); in `Induction/ReducibleVertex.lean`, the docstrings and sections of
  `isBase_vfiber_ncard_ge`, `acyclicSet_insert_vfiber_of_not_inc` and
  `exists_packing_move_of_not_inc` name their nodes, follow `rem:kt-lemma-41` (the descent is
  `exists_balanced_forest_packing`), and no longer tie the step to the degree of $v$ (task 30.1); in
  `ForestSurgery/Reduction.lean`, the lead of `exists_balanced_forest_packing` names
  `lem:balanced-forest-packing`, its docstring and section describe the descent that calls the move,
  and the section no longer calls it the last piece of a deferred surgery (task 31.1); reported
  (`notes/Prose-report.md`, L8).
- **F-092** · L · the surgery's pins (`Induction/ForestSurgery/EdgeSplitting.lean`,
  `Induction/ForestSurgery/Reduction.lean`): `splitOff_indep_extend_of_fiber_subset` and
  `splitOff_indep_extend_of_fiber_lt` take the degree-two hypothesis `_hdeg2` and do not use it.
  Docstrings are stale or misaddressed: `isAcyclicSet_splitOff_of_diff_fiberAtVertex`'s calls the
  second reroute step open, and the section before `fiberAtVertex` calls `lem:forest-surgery-split`
  red; `forest_surgery_count`'s calls `forest_surgery_split` superseded and vacuous, while it is the
  assembly that uses it; the two forward reroute lemmas name `lem:forest-surgery-split`, and the two
  reverse ones `lem:edge-splitting`, not the nodes that pin them.
  *Evidence:* read (the docstrings; the two wrappers' bodies, which do not pass `_hdeg2` on).
  *Found:* round 2 task 2.13.
  *Disposition:* done (task 31.1): `_hdeg2` dropped from both, the callers following, and with it
  `hdeg2` of `exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof`, which only passed it on (task
  10); in `ForestSurgery/EdgeSplitting.lean`, the leads of the two forward reroute lemmas name
  `lem:reroute-vfree-transport` and `lem:reroute-cycle-lift`, and of the two reverse ones
  `lem:reverse-reroute-cycle-lift` and `lem:reverse-pendant-insert`, and no docstring or section
  calls a reroute step open or `lem:forest-surgery-split` red (task 31); in
  `ForestSurgery/Reduction.lean`, `forest_surgery_count`'s docstring names `forest_surgery_split` as
  a lemma that applies it, not a superseded one, and states its second conclusion (task 31.1);
  reported (`notes/Prose-report.md`, L6).
- **F-094** · L · the deficiency bounds' pins (`Induction/SplitOffDeficiency.lean`): the private
  `splitOff_deficiency_le_aux` takes `heab : eₐ ≠ e_b` and does not use it, so
  `splitOff_deficiency_le` and `splitOff_deficiency_le_of_eq_left` take it only to pass it on.
  Docstrings misattribute or are stale: the file header, the section before `dof_tracking` and its
  docstring credit KT Lemmas 4.3–4.5 (KT Lemma 4.5 is `lem:no-rigid-edge-count`'s; the lemma is KT
  4.3(i) with 4.4); the section before `splitOff_deficiency_ge` says KT 4.3(ii) and its docstring
  "4.3(i)/(ii) refinement" (the lower bound is part of KT 4.3(i)), and that section calls the
  forest surgery "deferred"; `removeVertex_deficiency_ge`'s cites `notes/Phase20.md` *Finding 2*.
  *Evidence:* read (the bodies and docstrings).
  *Found:* round 2 task 2.14.
  *Disposition:* done (task 30.1): `heab` dropped from the three, the callers following (task
  10); the header, the sections and `dof_tracking`'s docstring credit KT Lemmas 4.3(i) and 4.4,
  the lower bound as part of 4.3(i), without the "deferred" surgery and `notes/Phase20.md` (task
  30.1); reported (`notes/Prose-report.md`, L5).
- **F-097** · L · the pins of KT Lemmas 4.5–4.8 (`Induction/ReducibleVertex.lean`,
  `Induction/Operations.lean`, `Induction/ForestSurgery/Reduction.lean`): in
  `splitOff_isMinimalKDof_of_pos`, the case $e = e_0$ of the minimality applies KT 4.7
  (`removeVertex_deficiency_gt_of_noRigid`). The criterion step of the other case (a base missing a
  copy of $ab$ would make $G_v^{ab}$ a $k$-dof-graph) settles it, so the proof needs neither KT 4.7
  nor `lem:edge-set-indep-pos`, and holds for $D \ge 2$. In it and in
  `removeVertex_deficiency_gt_of_noRigid`, `hV3 : 3 ≤ V(G).ncard` follows from the distinct
  $v, a, b \in V(G)$. The docstrings of `splitOff_vertexSet_ncard_lt` and
  `rigidContract_vertexSet_ncard_lt` name `lem:reduction-step`, not `lem:reduction-measure`; the
  section before `no_rigid_edge_count` states the bound for $k = 0$ only; those before
  `mulTilde_edgeSet_ncard` and `exists_degree_le_two` call KT 4.5(i) "still to land" and the
  degree-two step "the remaining `lem:reducible-vertex` work".
  *Evidence:* read (the bodies and docstrings).
  *Found:* round 2 task 2.15.
  *Disposition:* done (task 31.1): the case $e = e_0$ by the other case's criterion step, as KT
  Lemma 4.3's minimality argument (p. 661) has it, and `hV3` dropped from both pins;
  `lem:reduction-step-pos` and `lem:removal-deficiency-strict` restated, and KT 4.7's, 4.5(ii)'s and
  4.4's second assertion's pins now outside every main result's closure, dead pins 168 → 172 (task
  15); `splitOff_vertexSet_ncard_lt`'s lead names `lem:reduction-measure` (task 30), and those of
  `rigidContract_vertexSet_ncard_lt` and `rigidContract_vertexSet_ncard` (task 30.1); in
  `Induction/ReducibleVertex.lean`, `no_rigid_edge_count`'s section and docstring give every $k$,
  and those before `mulTilde_edgeSet_ncard` and `exists_degree_le_two` no longer call KT 4.5(i) or
  the degree-two step unfinished (task 30.1); in `ForestSurgery/Reduction.lean`, the two pins have
  docstrings that describe their proofs as task 15 left them, step (3) of KT Lemma 4.8(ii) by KT
  Lemma 4.3's minimality argument (task 31.1); reported (`notes/Prose-report.md`, L8). The $D \ge 2$
  question is `F-273`'s.
- **F-104** · L · the pins of KT Theorem 4.9, KT Lemma 6.1 and the $d = 3$ pair
  (`Induction/ForestSurgery/Reduction.lean`, `Induction/ReducibleVertex.lean`,
  `AlgebraicInduction/Theorem55.lean`, `AlgebraicInduction/PanelHinge.lean`):
  `case_cut_edge_realization_gen` and `case_cut_edge_realization_gp_gen` take
  `_hV3 : 3 ≤ V(G).ncard` and do not use it (KT Lemma 6.1 has no such hypothesis), and the second
  does not use the second conjunct of its hypothesis (`F-102`). Docstrings: both say that
  `theorem_55_minimalKDof_gen` applies them at `k := 2`, where it applies them at every grade;
  `Reduction.lean`'s header and `PanelHinge.lean`'s section on Theorem 5.5 say that the algebraic
  induction realizes or runs `minimal_kdof_reduction`, which nothing calls;
  `minimal_kdof_reduction`'s narrates Phases 20–22h and cites two notes;
  `exists_adjacent_degree_two_pair`'s and `exists_chain_data_of_noRigid`'s call $D \ge 6$ "the
  `d = 3` regime", which is $d \ge 3$.
  *Evidence:* read (the bodies and docstrings).
  *Found:* round 2 task 2.16.
  *Disposition:* done (task 36.1): `_hV3` dropped from `case_cut_edge_realization_gen` and
  `_gp_gen`, and the second conjunct from the latter's hypothesis (`F-102`), the call in
  `theorem_55_minimalKDof_gen` following, its statement unchanged; both nodes no longer ask three
  vertices (task 12); `exists_adjacent_degree_two_pair`'s docstring says $d \ge 3$ (task 30.1); in
  `ForestSurgery/Reduction.lean`, neither the header nor `minimal_kdof_reduction`'s docstring says
  that the algebraic induction runs it (it runs `minimal_kdof_reduction_all_k`; nothing uses
  `minimal_kdof_reduction`), the docstring narrates no phase and cites no note, and
  `exists_chain_data_of_noRigid`'s says $d \ge 3$ (task 31.1); `PanelHinge.lean`'s section on the
  realization hypotheses says that the proof of KT Theorem 5.5 inducts by
  `Graph.minimal_kdof_reduction_all_k` (task 36); the docstrings of the two pins (`Theorem55.lean`)
  say that `theorem_55_minimalKDof_gen` uses them at every `k` (task 36.1). Before: reported
  (`notes/Prose-report.md`, L6).
- **F-108** · L · the pins of KT Lemma 4.6's nodes (`Induction/ForestSurgery/ChainExtraction.lean`,
  `Induction/Operations.lean`, `Molecular/Deficiency.lean`): `chainData_extract` takes
  `hV3 : 3 ≤ V(G).ncard` beside `hV4 : 4 ≤ V(G).ncard`, and `[G.Simple]`, which
  `simple_of_isMinimalKDof_of_noRigid` derives from its other hypotheses. `chainWalk_charging`
  takes three hypotheses it does not use (`_hG0`, `_hD`, `_hV2`). `isKDof_zero_of_triangle`
  proves again, by its own count, the case $m = 3$ of `isKDof_zero_of_cycle`. Docstrings:
  `ChainExtraction.lean`'s header says "This commit lands **E3**" and that E5 "is next", and
  narrates design-note sections; `ChainData`'s cite KT eq. (6.46) for the chain and its label,
  where (6.46) is the rank of $(G_1, q_1)$ and the chain is KT Lemma 4.6's;
  `CycleData.vertexSet_ncard`'s names a use that no caller makes.
  *Evidence:* read (the bodies and docstrings; KT 2011 pp. 664 and 692).
  *Found:* round 2 task 2.17.
  *Disposition:* done (task 31): `chainData_extract` without
  `hV3` and `[G.Simple]`, both derived in its body, `chainWalk_charging` without the three, and
  `isKDof_zero_of_triangle` proved as the case $m = 3$ of `isKDof_zero_of_cycle`, after it in the
  file; `lem:chain-data-extract` restated without simplicity, and `F-270` (task 11);
  `Deficiency.lean`'s cycle and triangle sections without "ENTRY leaf E2c" and "brick" (task 29);
  `ChainData`'s docstrings without KT eq. (6.46), the chain credited to KT Lemma 4.6 (p. 664)
  (task 30); `ChainExtraction.lean`'s header names its two results and their nodes, without "This
  commit lands **E3**", E5 "is next" and the design note's sections, and its docstrings and
  sections without the leaf codes, the chain credited to KT Lemma 4.6 (p. 664) and the count to
  KT eqs. (4.6)–(4.9) (pp. 664–665) (task 31); reported (`notes/Prose-report.md`, L7).
- **F-114** · L · the pins of `meet.tex` (`Molecular/Meet.lean`): the file's header lists
  `meet_ne_zero_iff` and "the geometric reading" as deliverables, which no declaration provides, and
  narrates phases, commits and design codes ("this commit", "route (ii)", "N3b-2b-α", "CHAIN-3",
  "OD-8"); the header and `screwAlgebraPairingDualEquiv`'s docstring say Phase 25's projective
  invariance reuses it, which nothing does; `screwAlgebraTopEquiv_map_eq_det_smul`'s describes an
  O(n)-equivariance of `complementIso` that the file replaced by `complementIso_map_contragredient_eq`;
  the wedge-pairing lemmas call the diagonal sign "the open sign subproblem … deferred"; the duality
  lemmas call `n_u, n'` "the two panel normals of a panel Π(u)" (a panel has one normal, and `n'`
  is a second plane through the line); the docstrings of `finrank_exteriorPower_two_eq_one` and
  `exteriorPower_finrank_eq_one_proportional` call them the duality's payoff, which does not use
  them, and the second and `exteriorPower_map_subtype_injective` have no caller (`F-111`).
  *Evidence:* read (the bodies and docstrings; a `grep` for the callers).
  *Found:* round 2 task 2.18.
  *Disposition:* done (task 32.1): the header names the file's results and nodes and narrates no
  process; `screwAlgebraPairingDualEquiv`'s docstring says the formal proof uses the map
  `exteriorPower.pairingDual`, not the isomorphism; `screwAlgebraTopEquiv_map_eq_det_smul`'s gives
  the factor `det g` of `complementIso_map_contragredient_eq`; the wedge-pairing lemmas call
  `ε_S = ±1` a fact the proofs do not need; the duality lemmas give `n'` as the normal of a second
  plane through the line; and `finrank_exteriorPower_two_eq_one` and
  `exteriorPower_finrank_eq_one_proportional` are `lem:complement-iso-line-one-dim`'s case `n = 2`,
  the count the formal proof uses being `finrank_exteriorPower_self_eq_one`. Before: reported
  (`notes/Prose-report.md`, L9).
- **F-123** · L · the docstrings of `panel-layer.tex`'s first pins
  (`Molecular/AlgebraicInduction/PanelHinge.lean`): the field `ends` of `PanelHingeFramework` is
  documented as "the two bodies `e` joins", which nothing enforces (`F-122`);
  `rigidityMatrix_prop11`'s section header and docstring call it KT Proposition 1.1's analytic half
  "for a generic panel-hinge realization", while it assumes the generic bound for any body-hinge
  framework (`F-121`, `F-067`), and narrate "GREEN-modulo the Phase-21b genericity device",
  "honest" and "From Phase 21b (cited)"; the docstrings of `withMomentNormals`, `ofParam` and
  their general-position lemmas call them the construction the Case-I rigid block needs, but both
  pins of `lem:moment-curve-general-position` lie outside every main result's closure (`F-118`).
  *Evidence:* read (the docstrings and bodies); measured (`scripts/blueprint-deps.py --label` at
  `efa7ed2b`, dead pins).
  *Found:* round 3 task 2.1.
  *Disposition:* reported (`notes/Prose-report.md`, L3); round 3: in `PanelHinge.lean` (task 36),
  the docstrings of `isGeneralPosition_withMomentNormals` and `isGeneralPosition_ofParam` name
  `lem:moment-curve-general-position`, call neither a construction that Case I needs, and say that
  no declaration, or no main result, uses them; the leads of `withMomentNormals` and `ofParam` name
  that node; the rest of the docstrings of `withMomentNormals` and `ofParam`, the field `ends`, and
  `rigidityMatrix_prop11`'s header and docstring moved to the phase (the open).
- **F-126** · L · the docstrings and comments of `panel-layer.tex`'s KT Theorem 5.5 pins
  (`Molecular/AlgebraicInduction/PanelHinge.lean`, `Pinning.lean`, `Theorem55.lean`):
  `HasFullRankRealization`'s docstring calls it "the motive Theorem 5.5's induction is run
  against", and `RankHypothesis`'s "the predicate Katoh–Tanigawa's Theorem 5.5 establishes by
  induction"; the induction runs on `HasPanelRealization` and `HasGenericFullRankRealization`, and
  `HasFullRankRealization` lies outside every main result's closure. `HasGenericFullRankRealization`'s
  docstring places KT Theorem 5.5's "nonparallel, if G is simple" on "printed p. 669" (it is p. 670)
  and narrates phases and retired routes. The comments in `theorem_55_minimalKDof_k_all_k`'s
  signature call four of its hypotheses "`d = 3`-pinned in the landed tree", which its docstring
  denies. `rankHypothesis_deficiency_of_theorem_55_d3`'s binder `_hSimple` is unused.
  *Evidence:* read (the docstrings, signatures and bodies; KT 2011 p. 670); measured
  (`scripts/blueprint-deps.py --label def:rank-hypothesis` at `db237dfd`, dead pin).
  *Found:* round 3 task 2.2.
  *Disposition:* reported (`notes/Prose-report.md`, L12); round 3: `Pinning.lean`'s part (task 33):
  `RankHypothesis`'s docstring gives it as the form `dim Z(G,p) = D + k'` of the target rank in
  which KT Theorem 5.6, the molecular conjecture and the rank formula are stated, and says that the
  induction of KT Theorem 5.5 states its realizations with `HasGenericFullRankRealization` and
  `HasPanelRealization`; in `PanelHinge.lean` (task 36), `HasFullRankRealization`'s docstring says
  that no main result uses it and that the proof of KT Theorem 5.5 states its realizations with the
  other two, and `HasGenericFullRankRealization`'s places KT Theorem 5.5's "nonparallel, if G is
  simple" on p. 670 and narrates no phase or retired route; in `Theorem55.lean` (task 36.2), the
  comments of `theorem_55_minimalKDof_k_all_k`'s signature say what each hypothesis asks, not that it
  is "`d = 3`-pinned"; `rankHypothesis_deficiency_of_theorem_55_d3`'s part is the phase's.
- **F-130** · L · the docstrings of `panel-layer.tex`'s KT Theorem 5.6 and molecular-conjecture
  pins (`Molecular/AlgebraicInduction/Theorem55.lean`): `molecular_conjecture`'s says that dropping
  the nonzero-hinge conjunct "makes the statement false"; dropped from both sides, each side holds
  exactly when $G$ is connected (a zero hinge welds its ends, `IsInfinitesimalMotion`), so the
  equivalence still holds. `rankHypothesis_genuine_of_theorem_55_gen`'s names `thm:theorem-55-6`
  as its node; it is pinned on `thm:theorem-55-6-genuine`. `rankHypothesis_of_theorem_55_gen`'s
  and `rankHypothesis_of_theorem_55_d3`'s call them "the `def > 0` feed of `rigidityMatrix_prop11`
  (KT Prop 1.1)" and "Theorem 5.5 → Proposition 1.1" (`F-067`), and narrate phases and
  adjudications.
  *Evidence:* read (the docstrings and bodies; `IsInfinitesimalMotion`,
  `Molecular/RigidityMatrix/Basic.lean`).
  *Found:* round 3 task 2.3.
  *Disposition:* reported (`notes/Prose-report.md`, L4); round 3: the leads' labels and codes (task
  36.2): `rankHypothesis_genuine_of_theorem_55_gen`'s names `thm:theorem-55-6-genuine`, and the
  leads name no phase; the docstrings otherwise moved to the phase (the open).
- **F-132** · L · the docstrings of `panel-layer.tex`'s base pins
  (`Molecular/AlgebraicInduction/Theorem55.lean`, `PanelLayer.lean`, `Pinning.lean`): those of
  `theorem_55_base_producer_empty`, `_single_edge` and their `_gen` forms name
  `lem:theorem-55-base-producer`, and those of the four `_gp` and `_gp_gen` forms name
  `lem:theorem-55-base`; they belong to `lem:theorem-55-base-producer-empty` and `-single`. The
  docstrings of `theorem_55_base_producer_empty_gp` and `_empty_gp_gen` call $G$ simple, which
  neither assumes. `exists_linearIndependent_extensor_pair_perp`'s calls it the wrapper "feeding
  `theorem_55_base` (kept while the spine consumers in `Theorem55.lean` are still `k = 2`)"; it has
  no caller (`F-131`). `exists_triangle_normals`' heading says "`d = 3`", and the theorem holds for
  every `k ≥ 1`. `theorem_55_base`'s calls the independence of the two extensors the
  "general-position hypothesis", and `theorem_55_base_producer_gen`'s narrates "the L9 spine's
  conditioned motive", "carry" and phases.
  *Evidence:* read (the docstrings and signatures; a `grep` for the callers).
  *Found:* round 3 task 2.4.
  *Disposition:* done (task 36.1): `Pinning.lean`'s and `PanelLayer.lean`'s parts (task 33):
  `theorem_55_base`'s docstring without "general-position hypothesis",
  `exists_linearIndependent_extensor_pair_perp`'s says that no declaration uses it, without the
  claim that it feeds `theorem_55_base`, and `exists_triangle_normals`' lead says `k ≥ 1`, not
  "`d = 3`"; in `Theorem55.lean` (task 36.1), the leads of the two `_empty` and the two
  `_single_edge` forms name `lem:theorem-55-base-producer-empty` and
  `lem:theorem-55-base-producer-single`, `theorem_55_base_producer_empty_gp_gen`'s does not call `G`
  simple, and `theorem_55_base_producer_gen`'s narrates no spine, motive, carry or phase. Before:
  reported (`notes/Prose-report.md`, L10).
- **F-133** · L · the docstrings of `panel-layer.tex`'s framework-operation and multigraph pins
  (`Molecular/AlgebraicInduction/Pinning.lean`, `PanelHinge.lean`, `Theorem55.lean`):
  `BodyHingeFramework.withGraph`'s calls it "the carrier for the inductive constructions of Cases I
  and II"; its users in the main results' closure are the pins of `lem:motions-mono-of-graph-le`
  and the KT Theorem 5.6 forms (`rankHypothesis_genuine_of_theorem_55_gen`, two siblings and their
  private helpers, `theorem_55_6_multigraph_of_two_le`), none in Case I or II.
  `PanelHingeFramework.withGraph`'s calls it "the shared carrier both inductive cases of Theorem 5.5
  need" and says that every hinge of `P.withGraph G'` at a body lies in that body's panel; it lies
  outside every main result's closure, and the claim fails when the kept endpoint selector does not
  record the links of `G'`. `toBodyHinge_withGraph`'s names the
  same uses ("the green ... machinery"). `finrank_infinitesimalMotions_le_of_graph_le`'s names
  `prop:rigidity-matrix-prop11`'s step as its use; `rigidityMatrix_prop11` assumes that bound
  (`F-121`). `toBodyHinge_withNormal_pinnedMotions_eq`'s says it "carries the inductive realization
  of the splitting-off"; it lies outside every main result's closure, and
  `case_II_realization_all_k` uses the motion-space form. `HasCoplanarPanelRealization`'s and
  `theorem_55_6_multigraph_of_two_le`'s carry process codes ("W1", "M2", "the honest bare motive",
  "`hgen`"), and the latter calls `rigidityMatrix_prop11` "KT Prop 1.1" (`F-067`).
  *Evidence:* read (the docstrings and bodies); measured (the closure of `formalization.yaml`'s main
  results over the `scripts/blueprint-deps.py` cache, and `--label` for the slice's nodes, at
  `708f4443`).
  *Found:* round 3 task 2.5.
  *Disposition:* reported (`notes/Prose-report.md`, L3); round 3: `Pinning.lean`'s part (task 33):
  `BodyHingeFramework.withGraph`'s docstring without "the carrier for the inductive constructions of
  Cases I and II", and `finrank_infinitesimalMotions_le_of_graph_le`'s names its users, the proofs
  of KT Theorem 5.6 (`thm:theorem-55-6-genuine`, `thm:theorem-55-6-multigraph`), not
  `prop:rigidity-matrix-prop11`'s step; the other parts moved to the phase (the open), and in
  `PanelHinge.lean` (task 36) `toBodyHinge_withNormal_pinnedMotions_eq`'s lead names its node,
  `lem:with-normal-preserves`, the docstring otherwise kept as it stands; in `Theorem55.lean` (task
  36.2) the leads of `HasCoplanarPanelRealization` and `theorem_55_6_multigraph_of_two_le` carry no
  code (the latter's gives it as a step of `thm:theorem-55-6-multigraph`), and the former's names
  `BodyHingeFramework.IsHingeCoplanar`, not `PanelHingeFramework.IsHingeCoplanar`, which does not
  exist; the docstrings otherwise kept as they stand.
- **F-135** · L · the docstrings of `case-i.tex`'s first pins
  (`Molecular/AlgebraicInduction/PanelHinge.lean`, `PanelLayer.lean`, `Pinning.lean`,
  `CaseIII/Arms.lean`). `toBodyHinge_rankHypothesis_zero`'s calls
  it the brick the general cycle realization is built from, with its independent extensors "supplied
  generically (Claim 6.4/6.9, deferred)", and its section header says the general cycle remains red;
  `cycle_realization` uses `theorem_55_cycle` instead, and takes the extensors from
  `exists_cycle_normals`, a basis choice. `card_le_screwDim_of_supportExtensor_linearIndependent`'s
  calls that choice "the remaining red content of `lem:cycle-realization`".
  `exists_independent_normalsJoin`'s and `exists_independent_panelSupportExtensor`'s call them the
  genericity-device half of `lem:cycle-realization`, giving the extensors that KT Lemma 5.4 "feeds
  into" the cycle realization; their pairs share no normals, and nothing outside the two calls
  them.
  `toBodyHinge_rankHypothesis_zero_cycle`'s and `rankHypothesis_zero_of_cycle`'s say that with
  `exists_independent_panelSupportExtensor` they give KT Lemma 5.4 for $3 \le m \le D$ (the formal
  range is $m \le d + 1$, `F-115`). `cycle_realization`'s says a `[G.Simple]` binder is kept unused;
  the signature has none, and the docstring carries process codes (E5, GAP-2, design sections). The
  block-pin pins' docstrings call `screwDim_add_finrank_pinnedMotionsOn_le` "the lower-bound brick of
  Case I's block-triangular gluing", `pinnedMotionsOn_le_withGraph_of_le` "the direction Case I's
  block-triangular gluing travels", `isInfinitesimallyRigid_of_block_of_pinnedMotionsOn_eq_bot` its
  "framework-side core", and `pinnedMotionsOn_eq_iInf` "the form Case I's block-triangular
  accounting uses"; the live Case I (`case_I_realization_all_k_gen`) reaches none of them, and
  reaches the block pin only through the relative count
  (`finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn`).
  *Evidence:* read (the docstrings, signatures and bodies; a `grep` for the callers); measured (the
  main results' closure over the `scripts/blueprint-deps.py` cache, at `8cfa4531`).
  *Found:* round 3 task 2.6.
  *Disposition:* done (task 36): `PanelLayer.lean`'s and
  `Pinning.lean`'s parts (task 33): `exists_independent_normalsJoin`'s and
  `exists_independent_panelSupportExtensor`'s leads name `lem:exists-independent-panel-extensor`,
  not `lem:cycle-realization`, and their docstrings say that the pairs need not be the normals of a
  cycle and that no declaration uses the second; the four block-pin pins' docstrings no longer call
  them steps of Case I's gluing, and the block pin's section says that the formal proof uses it only
  through the counts relative to `V(G)` (`rem:case-I-kt-steps`); in `CaseIII/Arms.lean` (task 35),
  `cycle_realization`'s docstring claims no `[G.Simple]` binder and carries no process code; in
  `PanelHinge.lean` (task 36), the leads of `toBodyHinge_rankHypothesis_zero` and
  `card_le_screwDim_of_supportExtensor_linearIndependent` name `lem:cycle-realization-base` and
  `lem:cycle-realization-dim-bound`, neither docstring calls the general cycle red or its extensors
  deferred, and their section says that the formal proof realizes the cycles it needs with the
  normals of `lem:cycle-normals`; the two `Fin m` cycle forms were deleted (task 3, `F-238`).
  Before: reported (`notes/Prose-report.md`, L3).
- **F-140** · L · the docstrings of `case-i.tex`'s KT eq. (6.3) and Claim 6.4 pins
  (`Molecular/AlgebraicInduction/Pinning.lean`, `PanelHinge.lean`, `GenericityDevice.lean`,
  `CaseI.lean`). `rankHypothesis_iff_finrank_pinnedMotionsOn`'s calls the node "GREEN-modulo-21b",
  cites the matroid form `lem:contraction-minimality` for the graph $G/E(H)$, and calls its
  hypothesis `hglue` KT's Claim 6.4; that hypothesis is the lower bound of KT eq. (6.3) in motion
  form, and Claim 6.4 bounds the second block (KT p. 675). Its panel form's calls the block pin
  "the framework-side carrier of the contraction". `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`'s
  says the Case I realization consumes it; its callers are the relative-count lemmas, at one body.
  `isInfinitesimallyRigidOn_of_splice`'s calls $H$ and $G/E(H)$ "both subgraphs of `F.graph`"
  (`F-136`) and the seed "honest". `exists_good_realization_ofParam`'s names a hypothesis `hne`
  that the signature lacks, says `exists_independent_panelSupportExtensor` supplies `hindep` (no
  caller does, `F-135`), and calls it the device leg of the Case I and II realizations.
  `rigidContract_exterior_rank_transport_htransport` states its conclusion under
  `∀ Q, Q.graph = G.rigidContract H r → Q.IsGeneralPosition → Q.toBodyHinge.IsInfinitesimallyRigidOn
  _ → …`, three hypotheses its proof discards (`intro _ _ _ _`); its docstring carries process codes
  (U1–U4, "Phase 22b route (i) Commit 5") and calls the dead `case_I_realization` the composer.
  *Evidence:* read (the docstrings, signatures and bodies; a `grep` for the callers).
  *Found:* round 3 task 2.7.
  *Disposition:* done (task 36):
  `rigidContract_exterior_rank_transport_htransport` states its conclusion without the `∀ Q` and the
  three hypotheses, and `rigidContract_exterior_rank_transport` (unpinned), which took that form as
  its hypothesis and was left a pass-through, was deleted, `case_I_realization` calling the pin
  directly; `lem:claim-6-4`'s note no longer says the pin states its conclusion for every such
  realization (task 12); in `Pinning.lean` (task 33), `rankHypothesis_iff_finrank_pinnedMotionsOn`'s
  docstring without "GREEN-modulo-21b", `lem:contraction-minimality` and Claim 6.4, `hglue` given as
  the lower bound of KT eq. (6.3) in terms of motions;
  `isInfinitesimallyRigidOn_iff_pinnedMotionsOn_le`'s names its users, the relative counts at one
  body; `isInfinitesimallyRigidOn_of_splice`'s says that the contraction is not a subgraph, without
  "honest"; in `CaseI.lean` (task 34), `rigidContract_exterior_rank_transport_htransport`'s
  docstring carries no code (U1–U4, Phase 22b) and says that only `case_I_realization`, which no
  declaration uses, calls it; in `GenericityDevice.lean` (task 34.1),
  `exists_good_realization_ofParam`'s docstring names no hypothesis `hne` and no supplier of
  `hindep`, and says that only `exists_relative_full_count_ofParam` uses it; in `PanelHinge.lean`
  (task 36), `toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn`'s docstring calls the block
  pin no carrier of the contraction, gives `hglue` as the lower bound of KT eq. (6.3) in terms of
  motions, not Claim 6.4, carries no "GREEN-modulo" or Phase 21b, and says that no declaration uses
  it. Before: reported (`notes/Prose-report.md`, L6).
- **F-144** · L · the docstrings of `case-i.tex`'s last four pins
  (`Molecular/AlgebraicInduction/Theorem55.lean`). `case_I_dispatch_gen`'s calls "the `d = 3`
  `case_I_dispatch` below" its `k = 2` wrapper; the docstrings of `case_I_realization_h65_gen` and
  `case_I_realization_h65` and the file's header name the same `case_I_dispatch`, and those of
  `case_I_realization_nonsimple` and `case_I_realization_all_k` "the `d = 3` Case-I dispatch", as a
  consumer. No declaration of that name exists. `case_I_realization_h65_gen`'s and
  `case_I_realization_h65`'s give `lem:case-I-dispatch` as their node, which is
  `lem:case-I-realization-h65`. The three `d = 3` wrappers `case_I_realization_nonsimple`,
  `case_I_realization_all_k` and `case_I_realization_h65` have no caller. The docstrings carry
  process codes (L5a-ii, L5b-ii-d, L8c-2, OD-7, RELAX, "verbatim numeral pass") and the words
  "producer", "motive", "seed" and "brick".
  *Evidence:* read (the docstrings and bodies; a `grep` for each name across `CombinatorialRigidity/`).
  *Found:* round 3 task 2.8.
  *Disposition:* done (task 36.2): the three `d = 3` wrappers deleted, and the docstrings that named
  them repointed to their `_gen` forms (task 3); in `Theorem55.lean`, the header names no
  `case_I_dispatch`, and `case_I_realization_h65_gen`'s lead names `lem:case-I-realization-h65` and
  its user `case_I_dispatch_gen`, without the codes (task 36.1); the docstrings of
  `case_I_dispatch_gen`, `case_I_realization_nonsimple_gen` and `case_I_realization_all_k_gen` name
  no `case_I_dispatch` and no code, and give KT's three cases (task 36.2). Before: reported
  (`notes/Prose-report.md`, L9).
- **F-148** · L · the docstrings of `case-ii.tex`'s pins (`Molecular/AlgebraicInduction/Pinning.lean`,
  `PanelHinge.lean`, `CaseII.lean`; `Molecular/Induction/Operations.lean`). Those of
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`,
  `toBodyHinge_pinnedMotions_withGraph_eq` and `toBodyHinge_hnew_of_isLink_incident` say that
  `hspan` holds at the general-position normals of KT Claim 6.9, supplied by
  `exists_independent_panelSupportExtensor`; it holds at none for $k \ge 1$ (`F-145`).
  `isInfinitesimallyRigidOn_insert_iff`'s calls $S v = S w$ Claim 6.9's content and says it
  grounds two placement nodes; it has no caller. The docstrings of
  `rankHypothesis_iff_finrank_pinnedMotions`, `rankHypothesis_withNormal_iff_finrank_pinnedMotions`
  and `isLink_incident_of_not_removeVertex` give `lem:case-II` as their node, which is
  `lem:case-II-rank-lift`'s or `lem:splitoff-edge-substitution`'s; `removeVertex_le_splitOff`'s
  calls it the piece Case II's 1-extension needs, and its callers are KT Lemma 4.8's
  (`ForestSurgery/Reduction.lean`). They and `case_II_realization_all_k`'s carry process codes
  (Phase 21b, GREEN-modulo-21b, Phase 22i L6b, `hsplitPos`, W-suite, Brick A) and the words
  "producer", "brick" and "stratum".
  *Evidence:* read (the docstrings and bodies; a `grep` for each name across `CombinatorialRigidity/`).
  *Found:* round 3 task 2.9.
  *Disposition:* done (task 36): in `Induction/Operations.lean`,
  `isLink_incident_of_not_removeVertex`'s lead names `lem:splitoff-edge-substitution`, without
  "brick", and `removeVertex_le_splitOff`'s names its callers (`lem:removal-deficiency-equality`'s
  pin and `splitOff_removeVertex_minimalKDof`), not Case II (task 30); in `Pinning.lean` (task 33),
  `isInfinitesimallyRigidOn_insert_iff`'s docstring without Claim 6.9 and the two placement nodes,
  saying that no declaration uses it, `rankHypothesis_iff_finrank_pinnedMotions`'s lead names
  `lem:case-II-rank-lift`, and `pinnedMotions_withGraph_eq`'s, `hnew_of_isLink_incident`'s and their
  siblings' carry neither `lem:case-II`, Claim 6.9, general position nor
  `exists_independent_panelSupportExtensor`; in `CaseII.lean` (task 34),
  `case_II_realization_all_k`'s docstring carries none of the codes (Phase 22i L6b, `hsplitPos`,
  W-suite, Brick A) or the words; in `PanelHinge.lean` (task 36), the docstrings of
  `toBodyHinge_pinnedMotions_withGraph_eq` and `toBodyHinge_hnew_of_isLink_incident` carry neither
  Claim 6.9, general position nor `exists_independent_panelSupportExtensor`,
  `rankHypothesis_withNormal_iff_finrank_pinnedMotions`'s lead names `lem:case-II-rank-lift`, and
  none carries a process code. Before: reported (`notes/Prose-report.md`, L3).
- **F-153** · L · the docstrings of `genericity-and-count.tex`'s pins
  (`Molecular/AlgebraicInduction/GenericityDevice.lean`, `CaseI.lean`, `CaseII.lean`,
  `Pinning.lean`; `Molecular/RigidityMatrix/Basic.lean`). The file header and
  `exists_good_realization`'s credit the device to KT Claims 6.4 and 6.9 (Claim 6.9, p. 678, is that
  $(G, p_1)$ is a panel-hinge realization) and name consumers `hglue`, `hspan` and `hgen`; the
  section docstring describes "the remaining gap to per-consumer wiring".
  `exists_rankPolynomial_of_le_finrank_linking`'s calls its coordinatization the Gram determinant,
  where the body takes a maximal minor (`exists_polynomial_ne_zero_of_linearIndependent_at`).
  `case_II_placement_eq612`'s calls `Gv` the split-off $G_v^{ab}$, which `hGv : Gv ≤ G` excludes
  (`F-150`), and the lemma a brick toward the "still red" `lem:case-II-realization`.
  `exists_independent_panelRow_transport`'s says that the transported rows are the $D(|V(G)| - 2)$
  rows of $G_v^{ab}$ without $e_0$; `exists_independent_panelRow_of_edge`'s that
  `exists_independent_panelSupportExtensor` supplies the nondegenerate hinge;
  `hasFullRankRealization_of_independent_panelRow`'s names a node `lem:case-I-splice-placement` that
  does not exist. They carry process codes (N1–N3, N7a, N7b-0 to N7b-3, B0, Phase 21b, stratum 1)
  and the words "producer", "brick", "motive", "glue", "splice" and "seed".
  *Evidence:* read (the docstrings and bodies; a `grep` for `lem:case-I-splice-placement` in
  `blueprint/src`).
  *Found:* round 3 task 2.10.
  *Disposition:* done (task 34.1): in `RigidityMatrix/Basic.lean`,
  `linearIndependent_sum_pinned_block`'s docstring carries no code (N7b-1 to N7b-3) and names no
  consumer (task 32); in `Pinning.lean` (task 33), `exists_independent_panelRow_of_edge`'s docstring
  no longer has `exists_independent_panelSupportExtensor` supply the nondegenerate hinge,
  `span_panelRow_linking_eq_rigidityRows`'s lead names `lem:independent-rows-of-rank`, not the
  absent `lem:case-I-splice-placement`, and the file carries none of the codes (B0, N1, N3, N7a,
  N7b-1 to N7b-3, Phase 21b) or the words; in `CaseII.lean` (task 34), `case_II_placement_eq612`'s
  docstring states its hypotheses on a subgraph `Gv ≤ G`, says that its node starts from the
  split-off and that no declaration uses it, and calls it no brick; `CaseI.lean` and `CaseII.lean`
  carry none of the codes (N3, N7a, N7b-0 to N7b-3, stratum 1) or the words; in
  `GenericityDevice.lean` (task 34.1), the header and the docstrings of `exists_good_realization`
  and its section credit neither KT Claim 6.4 nor Claim 6.9 and name no consumer,
  `exists_rankPolynomial_of_le_finrank_linking`'s calls its polynomial a maximal minor,
  `exists_independent_panelRow_transport`'s states the lemma for any two frameworks, with no count,
  `hasFullRankRealization_of_independent_panelRow`'s lead names
  `lem:realization-of-independent-rows`, and the file carries none of the codes or the words.
  Before: reported (`notes/Prose-report.md`, L3).
- **F-156** · L · the docstrings of `case-iii.tex`'s KT Claim 6.11 pins
  (`Molecular/Induction/ForestSurgery/Reduction.lean`, `Molecular/AlgebraicInduction/CaseIII/
  Candidate.lean`, `Realization.lean`). `splitOff_exists_base_inter_fiber_lt`'s places KT Lemma 4.3
  on p. 660 (it is on p. 661). `splitOff_removeVertex_minimalKDof`'s calls the KT eq. (6.22) step
  "the next, deferred sub-phase", which `exists_nested_rankPolynomial_lower_all_k` has since
  proved; that one's points at "the collapsed remark at `case-iii.tex`", which task 2.11 replaced by
  KT's footnote-6 argument. `exists_redundant_panelRow_ab_of_finrank_eq`'s says that `h622` comes
  from the nested bound, where its live caller `exists_redundant_panelRow_ab_lam_of_rigidOn` makes it
  hold by definition, and calls the candidate completion deferred; the caller's own docstring calls
  `h622lb` an adjudicated carry awaiting a successor sub-phase. They carry process codes (Gap 1–3,
  Phases 22d, 22i, 22k, 23a and 30, RELAX, L7a, B2) and the words "brick", "stratum", "motive" and
  "seed".
  *Evidence:* read (the docstrings and bodies; KT 2011 p. 661, `.refs/`).
  *Found:* round 3 task 2.11.
  *Disposition:* done (task 35.1): in
  `Induction/ForestSurgery/Reduction.lean`, `splitOff_exists_base_inter_fiber_lt`'s docstring places
  KT Lemma 4.3 on p. 661, `splitOff_removeVertex_minimalKDof`'s names
  `exists_nested_rankPolynomial_lower_all_k` (`lem:case-III-nested-rank-lower`) as the lemma that
  uses it, and neither carries a process code (task 31.1); in `CaseIII/Candidate.lean` (task 35),
  `exists_redundant_panelRow_ab_of_finrank_eq`'s docstring says that the formal proof makes `h622`
  hold by the choice of `k'` and takes `k' ≤ D − 2` from `lem:case-III-nested-rank-lower`, and
  neither it nor `exists_redundant_panelRow_ab_lam_of_rigidOn`'s calls anything deferred or carried
  or has a process code; in `CaseIII/Realization.lean`, `exists_nested_rankPolynomial_lower_all_k`'s
  docstring credits KT eq. (6.22) and footnote 6 (p. 684), points at the remark after
  `lem:case-III-nested-rank-lower`, and has no process code (task 35.1). Before: reported
  (`notes/Prose-report.md`, L5).
- **F-161** · L · the docstrings of `case-iii.tex`'s pins for KT eqs. (6.24)–(6.29)
  (`Molecular/RigidityMatrix/Basic.lean`, `Molecular/AlgebraicInduction/PanelHinge.lean`,
  `CaseIII/Candidate.lean`). `exists_redundant_panelRow_ab_decomposition`'s says that the transport
  and the eq. (6.43) vanishing "remain the open crux" of `lem:case-III-candidate-row`, and
  `exists_redundant_panelRow_ab_decomposition_acolumn_zero`'s that eq. (6.43) is "the one fact" the
  transport still needs; `hingeRow_comp_columnOp_apply`'s says that the mechanism is the column
  operation and not eq. (6.43), and no live proof uses either. `ofNormals_panelRow_eq_of_ends_seed_eq`'s
  calls the identity KT eq. (6.26) (it is eq. (6.13)) and says that the transported row vanishes
  off $v$'s column, which holds only after the column operation. `exists_candidate_row_eq612`'s,
  `linearIndependent_sum_pinned_block_augment`'s, `comp_columnOp_eq_comp_single_proj`'s and
  `linearIndependent_sum_augment_candidateRow`'s say that the row lifts the rank
  $D(|V| - 1) - 1$ of `case_II_placement_eq612` to $D(|V| - 1)$; at those normals the block is
  singular (`F-158`). `panelRow_vb_sub_panelRow_ab_eq_hingeRow_va`'s credits the shear identity to
  KT eq. (6.16). They carry process codes (Phases 22d and 22e) and the words "brick", "stratum",
  "producer", "genuine", "seed", "green", "feeds", "threads" and "heart".
  *Evidence:* read (the docstrings and bodies; KT 2011 pp. 679 and 685–686, `.refs/`).
  *Found:* round 3 task 2.12.
  *Disposition:* done (task 36):
  `linearIndependent_sum_augment_candidateRow` deleted (task 4); in `RigidityMatrix/Basic.lean`,
  the docstrings of `hingeRow_comp_columnOp_apply`, `comp_columnOp_eq_comp_single_proj` and
  `linearIndependent_sum_pinned_block_augment` say neither that the column operation replaces
  eq. (6.43) nor that a row lifts a rank, and carry no process code (task 32); in
  `CaseIII/Candidate.lean` (task 35), `exists_redundant_panelRow_ab_decomposition`'s and
  `_acolumn_zero`'s docstrings call nothing an open crux or the one fact a transport needs (the
  second says that no declaration uses it), `exists_candidate_row_eq612`'s lifts no rank and says
  that at its normals the block of KT eq. (6.29) is singular,
  `panelRow_vb_sub_panelRow_ab_eq_hingeRow_va`'s credits the shear identity to no KT equation, and
  none carries a process code; in `PanelHinge.lean` (task 36),
  `ofNormals_panelRow_eq_of_ends_seed_eq`'s docstring names `lem:case-III-seam`, credits KT
  eq. (6.13) (p. 679), not eq. (6.26), and says nothing of a transported row vanishing off `v`'s
  column. Before: reported (`notes/Prose-report.md`, L3).
- **F-164** · L · the docstrings of the pins of `case-iii.tex`'s span and point choice
  (`Molecular/RigidityMatrix/Claim612.lean`). Those of `exists_ne_zero_dotProduct_eq_zero`,
  `exists_affineIndependent_of_det_polynomial_ne_zero`, `exists_detPolynomial_of_pointPolynomial`,
  `exists_homogeneousIncidence_of_normals_gen` and `exists_homogeneousIncidence_of_normals` name
  `lem:case-III-claim612-points-affineIndep` for their own nodes. The first calls that node "still
  red", and it and the next two tie the nonvanishing of the determinant to `lem:genericity-device`,
  which no proof here uses. `span_omitTwoExtensor_eq_top`'s calls each omit-two extensor "the join
  `pᵢ ∨ pⱼ`" (`F-060`), and `exists_affineIndependent_panel_incidence`'s calls its coordinate
  normals "the nonparallel hypothesis the framework supplies". They carry process codes (Phases
  22d–23b, N3a, R1, OD-4, CHAIN-4a, `hnewpinaug`) and the words "brick", "producer", "genuine",
  "seed", "leaf" and "feeding".
  *Evidence:* read (the docstrings and bodies).
  *Found:* round 3 task 2.13.
  *Disposition:* done (task 32.1): each lead names its own node; no docstring calls a node red or
  ties a determinant to `lem:genericity-device`; `span_omitTwoExtensor_eq_top`'s calls the omit-two
  extensor of `i < j` the join of the vectors with `l ≠ i, j`;
  `exists_affineIndependent_panel_incidence`'s gives its normals as the first three standard basis
  vectors; and no process code or word remains. Before: reported (`notes/Prose-report.md`, L3).
- **F-168** · L · the docstrings of the pins of `case-iii.tex`'s three frameworks and KT Claim 6.12
  (`Molecular/RigidityMatrix/Claim612.lean`, `CaseIII/Relabel/Basic.lean`, `Relabel/Chain.lean`,
  `CaseIII/Realization.lean`, `Molecular/Induction/Operations.lean`).
  `linearIndependent_sum_p2_candidateRow`'s says that $p_2$ splits off at $v$ along $vb$ (KT's
  $(G, p_2)$ is built on the same $G_v^{ab}$), and `linearIndependent_sum_p3_candidateRow`'s that
  $p_3$ splits off at $a$ along $ac$ (KT: along $vc$). `ofNormals_relabel`'s transports four
  conjuncts, one an algebraic independence that its statement lacks.
  `hasGenericFullRankRealization_of_splitOff_relabel`'s names a `hsplitZero` branch of
  `theorem_55_minimalKDof_k_all_k`, which has no such hypothesis, and an $M_3$ arm that it says
  needs the lemma and that does not use it. `case_III_candidate_dispatch`'s names
  `lem:case-II-realization` and `lem:case-III` as its nodes, says that it discharges the `hcand`
  parameter of `case_III_hsplit_producer_all_k`, whose `hcand` now takes chain data, and then that
  it has no caller. They carry process codes (Phases 22e–30, N1–N7, G4c-i to G4d-ii, W6b–W10b,
  GAP-6, RELAX) and the words "producer", "seed", "brick", "device" and "leaf".
  *Evidence:* read (the docstrings and bodies; the signatures of `theorem_55_minimalKDof_k_all_k`
  and `case_III_hsplit_producer_all_k`; KT 2011 pp. 682 and 686, `.refs/`).
  *Found:* round 3 task 2.14.
  *Disposition:* done (task 35.3):
  `linearIndependent_sum_p2_candidateRow` and `linearIndependent_sum_p3_candidateRow` deleted
  (task 4); `splitOff_isLink_relabel`'s docstring without "G4c-i", with KT p. 686 for the
  isomorphism and p. 687 for eq. (6.31) (task 30); `RigidityMatrix/Claim612.lean`'s docstrings
  without process codes or words (task 32.1); `case_III_candidate_dispatch`'s lead names
  `lem:case-III-candidate-dispatch-d3`, says that no main result uses it, the proof of `lem:case-III`
  taking the case of a chain, and claims no `hcand` (task 35.1); `ofNormals_relabel`'s gives the
  three conjuncts of its statement, and `hasGenericFullRankRealization_of_splitOff_relabel`'s names
  no `hsplitZero` branch and no user, as it has none (task 35.2); in `Relabel/Chain.lean`, the
  docstrings of `case_III_bottom_relabel`, `acolumn_mem_hingeRowBlock_of_span_rigidityRows` and
  `hingeRow_acolumn_mem_span_rigidityRows` carry no process code (W9b, G4d-i, G4d-ii), the last two
  give as their node no `lem:case-III-claim612-eq644`, which pins neither, and the first is credited
  to the isomorphism of KT pp. 686–687 and the row correspondence of p. 688 (task 35.3). Before:
  reported (`notes/Prose-report.md`, L4).
- **F-172** · L · the docstrings of the pins of `case-iii.tex`'s general case
  (`CaseIII/Realization.lean`, `CaseIII/Arms.lean`, `Molecular/Induction/Operations.lean`).
  `chainData_fire_discriminator`'s and `chainData_dispatch`'s say that they have no `\lean` pin;
  both are pinned. `case_III_realization_all_k`'s cites KT §6.4.1 and Lemma 6.10 for the all-$k$
  form, whose route is KT Lemma 6.13. `exists_isLink_of_isMinimalKDof_card_three`'s cites "KT §6.4
  §1.48(1)" and KT p. 659, which has no triangle (KT Lemma 6.7(i) is p. 677). They carry process
  codes (CHAIN-2c-iii, LEAF-3 and LEAF-5, RELAX, W6b, C.0–C.6, T1–T4, PROSPECT S1, Phases
  22h–40a) and the words "producer", "device", "seed", "motive", "brick" and "genuinely".
  *Evidence:* read (the docstrings and statements of the six pins; KT 2011 pp. 659, 677 and
  692, `.refs/`).
  *Found:* round 3 task 2.15.
  *Disposition:* done (task 35.1):
  `exists_isLink_of_isMinimalKDof_card_three` credited to the proof of KT Lemma 6.7(i) (p. 677),
  and the docstrings of `Induction/Operations.lean`'s chain without their process codes (task 30);
  `CaseIII/Arms.lean`'s docstrings without theirs, `case_III_hsplit_producer_all_k`'s citing
  `lem:case-III` and no `hsplitZero` (task 35); in `CaseIII/Realization.lean`, the leads of
  `chainData_fire_discriminator` and `chainData_dispatch` name their nodes,
  `case_III_realization_all_k`'s cites KT Lemma 6.13 (p. 692), and none has a process code
  (task 35.1). Before: reported (`notes/Prose-report.md`, L5).
- **F-176** · L · the docstrings of `bar-joint-3d.tex`'s pins (`GenericRigidityMatroid.lean`). The
  module header narrates process ("Phase 24", "This file lands the forward-mode chapter … end to
  end", "Phase 14's"), and `genericRank`'s cites "Phase 26". In the same file
  `exists_isGenericPlacement_abundance`, the pin of `generic-lift.tex`'s
  `lem:generic-placement-abundance`, says that its proof matches "the blueprint's Gram-determinant
  sketch in substance"; after task 2.1 no chapter has such a sketch (the existence proof here and
  the abundance proof take a minor), and it carries "Phase 34 PROSPECT G3". The other docstrings
  agree with their bodies.
  *Evidence:* read (the docstrings and bodies of the nine pins and of the abundance lemma; `grep
  -i gram` over `blueprint/src`).
  *Found:* round 4 task 2.1.
  *Disposition:* done (task 28): the header names the file's results and the blueprint sections
  that present them; `genericRank` cites KT Corollary 5.7 without "Phase 26"; the abundance lemma
  says its proof is the node's (a maximal minor for each witnessed edge set, multiplied) with no
  Gram determinant and no "PROSPECT G3"; reported (`notes/Prose-report.md`, L12).
- **F-182** · L · the docstrings of task 2.2's pins (`Molecule/ScrewVelocity.lean`, `Duality.lean`,
  `ProjectiveInvariance.lean`, `Dictionary.lean`). `ScrewVelocity.lean`'s header says that
  $\omega_S$ pairs two affine directions and $t_S$ a direction with the homogenizing coordinate;
  `omegaForm` and `tauForm` read the reverse. `screwComplementIso`'s says "the polarity never
  preserves adjacent-distinctness or nondegeneracy", which `supportExtensor_mapExtensor_ne_zero`
  contradicts for nondegeneracy. `Dictionary.lean`'s header says that injectivity, surjectivity and
  the finrank equality "are follow-up slices"; `molecular_finrank_motions_eq_square_ker` is in the
  same file. The headers narrate process (Phase 25 leaves W1, W2 and W7, "brick (1)"–"(4)", "design
  §2.3(4), flag F2 route two", DUAL-K) and say "genuine" and "consumes".
  *Evidence:* read (the docstrings and bodies of the slice's 26 pins and of `omegaForm`, `tauForm`).
  *Found:* round 4 task 2.2.
  *Disposition:* done (task 37): `ScrewVelocity.lean`'s header gives `ω_S` and `t_S` the pairings
  that `omegaForm` and `tauForm` read, `screwComplementIso`'s docstring says nothing of what the
  polarity preserves, `Dictionary.lean`'s header describes the whole file, and the four files narrate
  no process; reported (`notes/Prose-report.md`, L4).
- **F-186** · L · the docstrings of task 2.3's pins (`GeneralPositionPlacement.lean`,
  `Molecule/GeneralPosition4.lean`, `Theorem56.lean`, `Modelling.lean`). The docstring of
  `exists_molecular_rankHypothesis_generalPosition` credits the panel-hinge–molecular link to "the
  modelling equivalence Whiteley [35] / Jackson–Jordán 2008 state"; that is the square-graph
  equivalence, and the link is projective duality (KT p. 671, Crapo–Whiteley §3.6). The headers and
  docstrings narrate process (Phases 24–26, 30 and 31, leaves W5–W7, "the F1 fix", "RELAX",
  "PROSPECT S2") and say "capstone", "consumes", "producer", "genuine(ly)" and "rank-carrying". The
  other docstrings agree with their bodies.
  *Evidence:* read (the docstrings and bodies of the five pins, `IsGeneralPosition4` and
  `exists_generalPosition4_polynomial`).
  *Found:* round 4 task 2.3.
  *Disposition:* done (task 37.1): `GeneralPositionPlacement.lean`'s header and docstrings without
  Phases 24–25, leaf W5 and "genuinely" (task 28); the docstring of
  `exists_molecular_rankHypothesis_generalPosition` credits Katoh and Tanigawa (p. 671) with the
  molecular realization, by projective duality, and `GeneralPosition4.lean`, `Theorem56.lean` and
  `Modelling.lean` narrate no process and say none of the listed words (task 37.1; their sentences
  on the selector and on what `ofNormals` gives are `F-122`'s). Before: reported
  (`notes/Prose-report.md`, L5).
- **F-190** · L · the docstrings of task 2.4's pins (`Molecule/Carrier.lean`,
  `Molecule/Application.lean`). `Carrier.lean`'s header says that the labels `Sym2 V` alone are too
  few "e.g. for `Nat.card V ≤ 10`"; at $|V| = 10$ they number $55 > 54 = 6 \cdot 9$, and at
  $|V| = 1$ one, more than $0$: they are too few exactly when $2 \le |V| \le 9$.
  `molecule_rank_formula`'s says the formula "is due to Jackson–Jordán 2008, who proved it
  equivalent to the Molecular Conjecture", and calls `molecular_conjecture` KT Theorem 5.6; JJ
  conjectured the formula and proved $\le$ and the equivalence (Conjecture 2.2, Theorems 4.1 and
  4.3), and `molecular_conjecture` is KT Conjecture 1.2 (`thm:molecular-conjecture`). The headers and
  docstrings narrate process (Phases 24–26 and 34, leaf F4, Layer M, "not on the critical path")
  and say "shadowing carrier", "producer", "attainment leg", "fed", "carries", "transports",
  "genuine" and "consumers". The other docstrings agree with their bodies.
  *Evidence:* read (the docstrings and bodies of the eight pins in these files, and of
  `finrank_span_rigidityRow_le_genericRank`; JJ 2008 §§2 and 4, `.refs/`).
  *Found:* round 4 task 2.4.
  *Disposition:* done (task 37.1): `Carrier.lean`'s header says that on a nonempty `V` the labels
  `Sym2 V` are too few exactly when `2 ≤ |V| ≤ 9` (a `lake lean` witness,
  `scratch/reconcile-lean/t371/Sym2Count.lean`, gitignored); `molecule_rank_formula`'s docstring
  gives Jackson and Jordán's Conjecture 2.2 and Theorems 4.1 and 4.3 and Katoh and Tanigawa's
  Corollary 5.7, and names no `molecular_conjecture`; and the two files narrate no process and say
  none of the listed words. Before: reported (`notes/Prose-report.md`, L4).
- **F-194** · L · the docstrings of task 2.5's pins (`Jacobs.lean`, `EdgesIn.lean`,
  `Molecular/Deficiency.lean`). In `Deficiency.lean` the header of the tight-partition section and
  the docstring of `IsTightPartition` name `lem:tight-partition-cross-pair`, a label that no
  longer exists (it is `-mult` and `-nbr`). The header calls Lemma 3.2 that of JJ's "companion
  paper on partitions into maximal zero-deficiency subgraphs"; it is JJ 2008's Lemma 3.2, which
  they take from their reference [10], *Brick partitions of graphs*, and their companion paper is
  [8]. The header and docstrings narrate process ("This slice adds", "follows in a later
  commit", `partitionDef_merge`'s "a later commit", "JJ Lemma 3.2 bricks"; `Jacobs.lean`'s "Phase
  32" and "Thm 5.3 assembly infrastructure"), and `exists_fresh_label`'s says "genuinely" and
  "Feeds". The other docstrings agree with their bodies.
  *Evidence:* read (the docstrings and bodies of the twelve pins and of `exists_fresh_label`; JJ
  2008 §3, its closing remarks and its references).
  *Found:* round 4 task 2.5.
  *Disposition:* done (task 29.1): `Jacobs.lean`'s header and `IsLaman3.ncard_edgesIn_le`
  without "Phase 32" and "Thm 5.3 assembly", and `EdgesIn.lean`'s header and docstrings without
  their phase pointers (task 28); in `Deficiency.lean`, the tight partitions' section names
  `lem:tight-partition-cross-pair-mult` and `-nbr` and credits Lemma 3.2 to Jackson and Jordán
  2008, who take it from their [10], `IsTightPartition`'s lead names `def:tight-partition`, and
  the narration is gone, `exists_fresh_label`'s included (task 29.1); reported
  (`notes/Prose-report.md`, L5).
- **F-198** · L · the docstrings of task 2.6's pins (`JacobsCounting.lean`, `Jacobs.lean`,
  `SquareGraph.lean`). Five name `lem:normal-cross-count` for declarations pinned at the nodes split
  from it (`rootedAt_inj`, `ncard_inPartNeighbors_eq_two`, `mk_mem_squareNormalCrossEdgesRootedAt`,
  `squareNormalCrossEdgesRootedAt_eq_biUnion`, `squareCutPairs_pairwiseDisjoint`). Two, and a
  section header, name `fmlnote:normal-cross-split` for the count's split into four lemmas, which
  that note no longer describes (task 2.6 made it the subsection's note on the formal statements).
  `squareGCrossEdges` and `squareGCrossEdges_ncard_eq_crossingEdges` call the crossing count
  "Jackson–Jordán's `d_G(P)`"; JJ write $e_G(P)$, and $d_G(X)$ for the degree of a set (JJ §§2–3).
  The header and docstrings narrate process ("Phase 32", "in later commits", "This commit lands", "a
  later slice", "the closing slice", "item 5 of the hand-off", "superseded, see *Decisions made*",
  "encoding decision (a)", "Thm 5.3 assembly") and say "shadow carrier", "shadowing multigraph",
  "bricks", "consumes", "fed" and "producer". The other docstrings agree with their bodies.
  *Evidence:* read (the docstrings and bodies of the 25 pins and of the unpinned lemmas of
  `laman_square_count`'s proof; JJ 2008 §§2, 3 and 5, `.refs/`).
  *Found:* round 4 task 2.6.
  *Disposition:* done (task 28): the five leads name their own nodes
  (`lem:normal-cross-count-rooted`, `-local`, `-producer`, `-partition` twice);
  `fmlnote:normal-cross-split` is cited only for what it says (the classes defined for every
  partition, the empty vertex set); the crossing count is the chapter's `d_G(P)`, JJ's `e_G(P)`;
  the header and docstrings have no process narration, and `G.shadowGraph` is the multigraph of
  `lem:molecule-graph-carrier`; reported (`notes/Prose-report.md`, L10).
- **F-200** · L · the docstrings of task 2.7's pins (`JacobsZeroExtension.lean`,
  `RigidityMatroid.lean`, `SquareGraph.lean`, `GenericRigidityMatroid.lean`,
  `GeneralPositionPlacement.lean`, `Jacobs.lean`). They agree with their bodies, but narrate
  process: `JacobsZeroExtension.lean`'s header ("Phase 32 (`sec:jacobs-zero-extension`, S3)", "the
  S2 row-independence lift", "crux fact", "the K₅-closure assembly"), the zero-extension section
  of `RigidityMatroid.lean` ("the fixed-`V` analogue of Phase 7's", "the corollaries downstream")
  and two section headers of `SquareGraph.lean` ("Phase 32", "package what squaring does under
  that peel").
  *Evidence:* read (the docstrings and bodies of the 16 pins, of
  `zero_extension_edgeSetRowIndependent_extend` and of the three `K₅` lemmas).
  *Found:* round 4 task 2.7.
  *Disposition:* done (task 28): `JacobsZeroExtension.lean`'s header and `SquareGraph.lean`'s
  two section headers say what the file and the sections prove, with no phase, slice or "crux"
  narration, as do the pins' docstrings in `GenericRigidityMatroid.lean`,
  `GeneralPositionPlacement.lean` and `Jacobs.lean`; `RigidityMatroid.lean`'s zero-extension
  section (task 25); reported (`notes/Prose-report.md`, L12).
- **F-205** · L · the docstrings of task 2.8's pins (`JacobsTheorem.lean`, `JacobsDegreeOne.lean`,
  `TwoCore.lean`). They agree with their bodies, but narrate process: the three file headers
  ("Phase 32", "Phase 26", "the L2 slice plan, T1", "T3–T4", "This file lands", "the rank glue",
  pointers to `notes/Phase32.md`) and `degree_one_rank_tree_of_ncard`'s "the T2 maintenance
  identities". `twoCore`'s docstring credits the core to "Jackson–Jordán 2008 Lemma 4.2"; JJ
  define it in the paragraph before that lemma (JJ §4).
  *Evidence:* read (the docstrings and bodies of the eight pins and of
  `jacobs_of_isLaman3_of_ncard`, `degree_one_rank_tree_of_ncard` and `degree_one_rank_of_ncard`;
  JJ 2008 §4).
  *Found:* round 4 task 2.8.
  *Disposition:* done (task 28): the three headers say what their files prove and name the
  blueprint section, with no phase, slice or T-step pointers; the private strengthenings cite the
  lemmas they use; `twoCore` credits JJ §4, where the core is defined before Lemma 4.2; reported
  (`notes/Prose-report.md`, L5).
- **F-210** · L · the docstrings of task 2.9's pins (`GenericLift/PanelGeneric.lean`,
  `GenericRigidityMatroid.lean`, `Molecule/Application.lean`). `IsGenericNormals` "subsumes
  Jackson and Jordán's edge-induced-submatrix maximum-rank condition": not over all normal
  assignments, as a degenerate hinge welds its bodies and raises the rank; over those with
  nondegenerate hinges it does (task 2.9's paragraph after `lem:generic-normals-nondegenerate`).
  `supportExtensor_ofNormals_ne_zero_of_isGenericNormals` quotes blueprint text that no longer
  exists ("dimension at least two, so `D ≥ 3`"). `molecule_generic_rank` and the docstrings of
  task 2.4's pins in its file (`F-190`) write "`G̃ = G.shadowGraph`": `G.shadowGraph` is the
  multigraph $G'$ of `lem:molecule-graph-carrier`, and $\tilde G = 5 \cdot G'$. The rest narrates
  process: `PanelGeneric.lean`'s header ("Phase 34 (PROSPECT G3 …)", "Layer P"),
  "W6e", "OUR", "genuine", "producer", and `molecule_generic_square_packing`'s "existing
  Phase-19/22i machinery". The Lean dates Jackson–Jordán's paper 2009 in three files and 2010 in
  eight; it is 2010 (task 2.9 corrected the bibliography).
  *Evidence:* read (the docstrings and bodies of the twelve pins; `grep` for the year).
  *Found:* round 4 task 2.9.
  *Disposition:* reported (`notes/Prose-report.md`, L4); round 3: `GenericRigidityMatroid.lean`'s
  abundance lemma without "Phase 34 PROSPECT G3" (its credit dropped, as the node gives none) (task
  28); `Molecular/Deficiency.lean`'s header without the year 2009 (task 29), and its docstrings with
  Jackson and Jordán's Theorem 4.1(a) dated 2010 (task 29.1); `AlgebraicInduction/PanelLayer.lean`'s
  two (the deficiency bound's section and its pin) dated 2010 (task 33);
  `Molecule/Application.lean`'s docstrings give `def(G̃)` as `G.shadowGraph.deficiency 3`, the
  deficiency of `G̃ = 5·G'` for `G' = G.shadowGraph`, `molecule_generic_square_packing`'s names no
  earlier machinery, and `molecule_generic_rank`'s gives no Jackson–Jordán 2010 credit, which its
  node does not give (task 37.1).

- **F-215** · L · the docstrings of task 2.10's pins (`BodyBar/GenericLift.lean`).
  `exists_isGenericEndpoints_abundance` calls its polynomial one "in the `2n|E(G)|` endpoint
  coordinates"; its type has $2n$ variables for each label (`F-212`). `coordPoint` names the
  origin "$c_0$ in the paper's naming"; Jackson and Jordán write $p_0$ (JJ 2010 §5). The private
  `twoExtensor_coordPoint_zero` and `_succ` call their vectors rows of the entry table in the proof
  of JJ's Lemma 5.1, which has the opposite signs on the direction coordinates (JJ put the
  coordinate 1 last). The rest narrates process: the file header ("Layer BB", "Phase 34 (PROSPECT
  G3 …)", "the definition-plus-abundance leaf group of the chapter extension", "`notes/Phase34.md`
  adjudication item 3", "This closes Layer BB"), `IsGenericEndpoints` ("The Phase-24 transfer
  form", "the R0-era witness claim refuted"), "Phase 34" in thirteen more docstrings, and "feeding"
  twice.
  *Evidence:* read (the docstrings and bodies of the twelve pins and the private lemmas; JJ 2010
  §5, pp. 581–582).
  *Found:* round 4 task 2.10.
  *Disposition:* reported (`notes/Prose-report.md`, L3); round 3: all but S13's part (task 27):
  `coordPoint`'s origin is the chapter's `c₀` and JJ's `p₀` (2010, p. 581), the two private
  lemmas say JJ's table has the opposite signs on the direction coordinates, and the process
  narration is gone; S13's part, `exists_isGenericEndpoints_abundance`'s "`2n|E(G)|` endpoint
  coordinates", moved to the phase.

- **F-220** · L · the docstrings of task 2.11's pins (`GenericLift/HingeGeneric.lean`). Six credit
  their construction to "Jackson–Jordán 2010 §6", which has neither hinge points nor the row
  family: JJ give a body-and-hinge realization by its hinge subspaces (§3.3, p. 578) and define its
  genericity by maximum rank (p. 583). The file header and the docstrings of `hingeExtensorPoly`
  and the abundance lemma assert a degree bound that no declaration proves (`F-217`).
  `supportExtensor_ofHinge_ne_zero_of_isGenericHingePoints` places its reference family on $e$
  "(any values elsewhere)"; its body places it on every label. The rest narrates process: the
  header ("Layer BH", "Phase 34 (PROSPECT G3 …)", "This file opens the body-and-hinge layer"),
  "Phase 34" in six docstrings, "the Phase-24 transfer form", "subsequent Layer-BH work", "the
  consumers", "packaging", "seeded", and "genuine" five times.
  *Evidence:* read (the docstrings and bodies of the seven pins; JJ 2010 §§3.3 and 6, pp. 578 and
  583).
  *Found:* round 4 task 2.11.
  *Disposition:* reported (`notes/Prose-report.md`, L5).

- **F-225** · L · the docstrings of task 2.12's pins (`GenericLift/HingeGeneric.lean`,
  `Extensor.lean`). Six credit "Jackson–Jordán 2010 §6": right for the rank theorem and its
  rigidity corollary (JJ Theorem 6.1 and their generic realizations, pp. 582–583), not for the
  change of screw coordinates, the affine points, the simultaneous move or the witness assembly,
  which JJ do not make (`F-220`). `exists_linearEquiv_forall_last_ne_zero` attributes its
  "coordinate-choice device" to JJ's Lemma 7.1, which is in §7.
  `exists_hingePoints_independent_hingePointRow` says that it realizes "a generic hinge-point
  assignment `q₀`"; its statement claims no genericity for `q₀`. `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints` calls its upper
  bound "the dual form of `prop:rigidity-matrix-prop11`'s bound"; it is the second pin of
  `lem:relative-deficiency-rank-bound`. The rest narrates process: "Phase 34" in all seven,
  "Route:", "producer", "Layer-P", "Layer-BH", "W6e", "OUR", "subsequent Layer-BH work", "the
  Layer-BH hand-off flagged" (`screwEquivOfLinearEquiv`), "genuine" four times, "deficiency-graded
  rank".
  *Evidence:* read (the docstrings and bodies of the seven pins and of `screwEquivOfLinearEquiv`;
  JJ 2010 §§6–7, pp. 582–584).
  *Found:* round 4 task 2.12.
  *Disposition:* reported (`notes/Prose-report.md`, L5); round 3: `Extensor.lean`'s part (task
  32.2): `exists_affineSubspaceExtensor_eq_smul_extensor` credits no one, as
  `lem:extensor-affine-representation` does not, its "Phase 34" is gone, and its lead names the
  node; `GenericLift/HingeGeneric.lean`'s part moved to the phase.

- **F-230** · L · `runPebbleGame`, `runPebbleGame.aux` (`PebbleGame/Correctness.lean`) and
  `runPebbleGameExec_isAccept_iff` (`PebbleGame/Exec.lean`): their docstrings name the nodes their
  pins left in round 5's task 3.1. The first two say `def:runPebbleGame`, and `runPebbleGame` is
  now `def:runPebbleGame-verdict`'s pin; the third says `thm:pebbleGameResult-isAccept-iff`, and it
  is now `thm:runPebbleGameExec-isAccept-iff`'s.
  *Evidence:* read (the three docstrings; a `grep` for the two old labels in
  `CombinatorialRigidity/`).
  *Found:* round 5 task 3.1.
  *Disposition:* done (task 26): `runPebbleGame` names `def:runPebbleGame-verdict` in its lead,
  `runPebbleGame.aux` as the node it is a step of, and `runPebbleGameExec_isAccept_iff` names
  `thm:runPebbleGameExec-isAccept-iff`. Before: reported (`notes/Prose-report.md`, L11).
- **F-232** · L · the declarations round 5's task 3.2 moved or unpinned
  (`Molecular/Meet.lean`, `Molecular/AlgebraicInduction/`, `Molecular/RigidityMatrix/Claim612.lean`,
  `BodyBar/KFrame.lean`). The docstrings of `hasGenericFullRankRealization_of_rigidOn_ofNormals`
  and `extensor_join_proportional_complementIso_meet` name
  `lem:case-III-claim612-line-in-panel-union`, and their nodes are now
  `lem:generic-realization-of-rigid` and `lem:meet-two-hyperplanes`; the first also names
  `lem:case-III-realization`, which is no label. Seven of the eight declarations unpinned from that
  lemma name it too. Of the eight, `exists_line_data_of_homogeneousIncidence` and
  `exists_complementIso_ne_zero_of_homogeneousIncidence` serve the $d = 3$ dispatch; the other six
  have no caller outside themselves (`case_III_realization_of_line` none at all). `blockPiSpan`,
  `kFrameRow_mem_blockPiSpan` and `span_kFrameRow_le_blockPiSpan` have no caller, and the latter
  two's docstrings place them in the rank count of `lem:k-frame-nonzero-monomial-forest`, which
  uses the per-set forms.
  *Evidence:* read (the docstrings; a `grep` for each name's callers in `CombinatorialRigidity/`).
  *Found:* round 5 task 3.2.
  *Disposition:* done (task 34): the six without a caller outside themselves deleted, with
  `blockPiSpan` and its two lemmas, and the docstrings that named them repointed or cut (task 4);
  `extensor_join_proportional_complementIso_meet`'s lead names `lem:meet-two-hyperplanes`, and those
  of `exists_line_data_of_homogeneousIncidence` and
  `exists_complementIso_ne_zero_of_homogeneousIncidence` give them as steps of
  `lem:case-III-candidate-dispatch-d3` (task 32.1);
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`'s lead names
  `lem:generic-realization-of-rigid` (`AlgebraicInduction/CaseI.lean`, task 34). Before: reported
  (`notes/Prose-report.md`, L9).
- **F-233** · L · the declarations round 5's task 3.3 moved or unpinned
  (`Molecular/RigidityMatrix/Basic.lean`, `Molecular/AlgebraicInduction/PanelLayer.lean`). Their
  docstrings name the nodes their pins left: `screwSpace_finrank` and the five row-independence
  lemmas say `def:rigidity-matrix` (now `def:screw-space`, `lem:edge-rows-independent` and
  `lem:own-end-rows-independent`), `IsTrivialMotion` and `trivialMotions` say
  `lem:trivial-motions-rank-bound` and `IsInfinitesimallyRigid` says `def:dof-generic` (now
  `def:trivial-motions-rigid`), and `screwDim_add_deficiency_le_finrank_infinitesimalMotions` says
  `lem:trivial-motions-rank-bound` (now `lem:deficiency-rank-bound`). `IsInfinitesimallyRigid`'s
  also says that the equality form of the rank bound waits on the coordinatization
  `⋀^k K^(k+2) ≅ K^D`, which `screwSpace_finrank` and `finrank_trivialMotions` supply.
  `exists_finite_spanning_rigidityRows`, `linearIndependent_hingeRow_forest`,
  `linearIndependent_hingeRow_star` and `exists_independent_rigidityRows_of_forest` lie outside
  every main result's closure (`F-012`); the first and last have callers only in dead
  `Molecular/AlgebraicInduction/CaseI.lean` code.
  *Evidence:* read (the docstrings and statements; a `grep` for each name's callers);
  measured (`scripts/blueprint-deps.py --label`, dead pins).
  *Found:* round 5 task 3.3.
  *Disposition:* done (task 33): `exists_finite_spanning_rigidityRows` deleted, and the other
  three's docstrings no longer name the dead `CaseI.lean` code (task 5); the two `_forest` lemmas,
  renamed `_starForest`, name `lem:own-end-rows-independent` (task 7); in
  `RigidityMatrix/Basic.lean`, `screwSpace_finrank`, the other three row-independence lemmas,
  `IsTrivialMotion`, `trivialMotions` and `IsInfinitesimallyRigid` name their nodes, and the last no
  longer has the equality form wait on a coordinatization (task 32); in `PanelLayer.lean`,
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions`'s lead names `lem:deficiency-rank-bound`
  (task 33); reported (`notes/Prose-report.md`, L11).
- **F-235** · L · the declarations round 5's task 3.4 moved or unpinned (`Molecular/Deficiency.lean`,
  `Molecular/Induction/Operations.lean`). Their docstrings name the nodes their pins left:
  `twoEdgeConnected_of_isKDof_zero` and `two_le_degree_of_twoEdgeConnected` say `def:cut-edges-2ec`
  (now `lem:two-edge-connected-degree`), and `partitionDef_split_of_sides` says
  `lem:cut-edge-decomposition` (now `lem:separated-partition-value`). The three `cutLabeling`
  helpers (`cutEdges_eq_crossingEdges_cutLabeling`, `crossingEdges_cutLabeling_singleton_subset`,
  `crossingEdges_cutLabeling_singleton_ncard_le`) say that `def:cut-edges-2ec` uses them; the
  definition no longer does, and `lem:two-edge-connected-degree`'s note names them. `inducedSpan`'s
  says `def:graph-operations`, though its pin is at `def:induced-span`.
  *Evidence:* read (the docstrings).
  *Found:* round 5 task 3.4.
  *Disposition:* done (task 30): in `Molecular/Deficiency.lean`,
  the leads of `twoEdgeConnected_of_isKDof_zero` and `two_le_degree_of_twoEdgeConnected` name
  `lem:two-edge-connected-degree`, that of `partitionDef_split_of_sides`
  `lem:separated-partition-value`, and the three `cutLabeling` helpers are steps of
  `lem:two-edge-connected-degree` (task 29); `inducedSpan`'s lead names `def:induced-span` (task
  30); reported (`notes/Prose-report.md`, L11).
- **F-236** · L · the declarations round 5's task 3.5 moved or unpinned
  (`Molecular/Induction/ForestSurgery/Reduction.lean`, `Molecular/Induction/ReducibleVertex.lean`,
  `Molecular/Induction/Operations.lean`). The section header before
  `exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof` names `lem:removal-deficiency-strict`
  (now `lem:removal-deficiency-equality`). `rigidContract_vertexSet_ncard` and
  `rigidContract_vertexSet_ncard_lt` call themselves forms of `lem:reduction-step`; their node is
  `lem:reduction-measure`. `CycleData.vertexSet_ncard`'s says that the `d = 3` binder reshape uses
  it, but it has no caller (`F-106`).
  *Evidence:* read (the docstrings; a `grep` for the callers).
  *Found:* round 5 task 3.5.
  *Disposition:* done (task 31.1): `CycleData.vertexSet_ncard` deleted, and `def:cycle-data`'s note
  no longer names it (task 3); the leads of `rigidContract_vertexSet_ncard` and `_lt` name
  `lem:reduction-measure` (task 30.1); the section before
  `exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof` (`ForestSurgery/Reduction.lean`) names
  `lem:removal-deficiency-equality` (task 31.1); reported (`notes/Prose-report.md`, L11).
- **F-237** · L · the declarations round 5's task 3.6 pinned or unpinned
  (`Molecular/AlgebraicInduction/Theorem55.lean`, `PanelLayer.lean`). The five $d = 3$ base wrappers
  `theorem_55_base_producer_empty`, `_empty_gp`, `_single_edge`, `_single_edge_gp` and
  `_parallel_pair`, now unpinned, have no caller (`F-131`), and the `_gen` forms' docstrings call
  themselves their lifts. `exists_extensor_eq_panelSupportExtensor_gen`'s docstring names
  `def:genuine-hinge-realization` (its node is `lem:panel-support-extensor-join`), and that of its
  $d = 3$ wrapper `exists_extensor_eq_panelSupportExtensor` says that it is kept while
  `hasPanelRealization_of_generic` is at `k = 2`, which that theorem no longer is (it takes
  `[NeZero k]` and calls the `_gen` form). `rankHypothesis_of_theorem_55_gen`'s docstring gives the
  strip-realize-re-add assembly as its proof; its body takes the case $|V| \ge 2$ from
  `rankHypothesis_genuine_of_theorem_55_gen` (`F-011`).
  *Evidence:* read (the docstrings and bodies; a `grep` for the callers).
  *Found:* round 5 task 3.6.
  *Disposition:* reported (`notes/Prose-report.md`, L9); round 3: the five wrappers deleted, and the
  `_gen` forms' docstrings no longer name them as their lifts (task 3); in `PanelLayer.lean` (task
  33), `exists_extensor_eq_panelSupportExtensor_gen`'s lead names `lem:panel-support-extensor-join`,
  and `exists_extensor_eq_panelSupportExtensor`'s names its users, without the claim that it is kept
  while `hasPanelRealization_of_generic` is at `k = 2`; in `Theorem55.lean`, the base `_gen` forms'
  docstrings narrate no lift from `d = 3` (task 36.1); `rankHypothesis_of_theorem_55_gen`'s moved
  to the phase.
- **F-238** · L · the declarations round 5's task 3.7 unpinned or pinned
  (`Molecular/AlgebraicInduction/Pinning.lean`, `PanelHinge.lean`, `PanelLayer.lean`,
  `GenericityDevice.lean`, `Theorem55.lean`; `Molecular/Induction/Contraction.lean`). The three
  `Fin m` cycle forms `isTrivialMotion_of_isInfinitesimalMotion_cycle`,
  `rankHypothesis_zero_of_cycle` and `toBodyHinge_rankHypothesis_zero_cycle`, now unpinned, have
  no caller but one another (`F-134`), and their docstrings name `lem:cycle-realization`. The
  pinned `annihRowPoly_totalDegree_le` has no caller, and the $d = 3$ wrapper
  `case_I_realization_nonsimple`, now unpinned, has none either (`F-131`). The docstrings of
  `exists_good_realization_ofParam` and `case_I_realization_h65_gen` name
  `lem:rows-polynomial-in-normals` and `lem:case-I-dispatch`, which are not their nodes, and
  those of `case_I_hcontract_gen` and the two theorems of KT Claim 6.6 name none (now
  `lem:case-I-all-k` and `lem:claim-6-6`).
  *Evidence:* read (the docstrings; a `grep` for the callers).
  *Found:* round 5 task 3.7.
  *Disposition:* done (task 36.2): the three `Fin m` cycle forms
  deleted with their step (`F-266`), and `case_I_realization_nonsimple` (task 3); the leads of the
  two theorems of KT Claim 6.6 (`Induction/Contraction.lean`) name `lem:claim-6-6` (task 30.1);
  `PanelLayer.lean`'s `annihRowPoly_totalDegree_le` says that no declaration uses it (task 33);
  `exists_good_realization_ofParam`'s lead gives it as a step of `lem:relative-device-count`
  (`GenericityDevice.lean`, task 34.1); `case_I_realization_h65_gen`'s lead names
  `lem:case-I-realization-h65` (`Theorem55.lean`, task 36.1); `case_I_hcontract_gen`'s names
  `lem:case-I-all-k` (task 36.2). Before: reported (`notes/Prose-report.md`, L9).
- **F-240** · L · the declarations round 5's task 3.8 pinned (`Molecular/Deficiency.lean`,
  `Molecular/Induction/Operations.lean`, `Molecular/AlgebraicInduction/GenericityDevice.lean`). The
  section header over `isKDof_zero_of_triangle` names `lem:case-III`, which is not its node, and the
  docstring of the unpinned `splitOff_simple_of_noRigid` calls its triangle hypothesis `htri` and the
  deficiency of a triangle not yet formalized, which `triangle_isProperRigidSubgraph` and
  `isKDof_zero_of_triangle` are. The docstrings of these two, of
  `splitOff_simple_of_noRigid_of_card` and of `exists_independent_panelRow_subfamily_of_le_finrank`
  name no node (now `lem:splitoff-simple` and `lem:independent-rows-of-rank`).
  *Evidence:* read (the docstrings and the section header).
  *Found:* round 5 task 3.8.
  *Disposition:* done (task 34.1): in `Molecular/Deficiency.lean`,
  the section header and the lead of `isKDof_zero_of_triangle` name `lem:splitoff-simple` (task
  29); in `Induction/Operations.lean`, the leads of `triangle_isProperRigidSubgraph` and
  `splitOff_simple_of_noRigid_of_card` name `lem:splitoff-simple`, and
  `splitOff_simple_of_noRigid`'s says that `triangle_isProperRigidSubgraph` gives its `htri` (task
  30); `exists_independent_panelRow_subfamily_of_le_finrank`'s lead names
  `lem:independent-rows-of-rank` (task 34.1). Before: reported (`notes/Prose-report.md`, L11).
- **F-241** · L · the declarations round 5's task 3.9 pinned (`CaseIII/Candidate.lean`). The
  docstrings of `exists_redundant_panelRow_ab_lam_of_rigidOn` and of its caller
  `exists_candidateRow_bottomRows_of_rigidOn` name `lem:case-III-claim612-r`, a label the blueprint
  does not have; that of `case_III_rank_certification` names `lem:case-III`, and that of
  `caseIIICandidate` no node (now `lem:case-III-redundant-combination`,
  `lem:case-III-rank-certification` and `def:case-III-candidate`).
  *Evidence:* read (the docstrings; a `grep` for the label in `blueprint/src`).
  *Found:* round 5 task 3.9.
  *Disposition:* done (task 35): the leads of `exists_redundant_panelRow_ab_lam_of_rigidOn` and
  `case_III_rank_certification` name their nodes, `exists_candidateRow_bottomRows_of_rigidOn`'s
  gives it as a step of `lem:case-III-candidate-dispatch-d3` and `lem:case-III-chain-discriminator`,
  and `caseIIICandidate`'s names `def:case-III-candidate`. Before: reported
  (`notes/Prose-report.md`, L11).
- **F-242** · L · the declarations round 5's task 3.10 pinned or unpinned
  (`Molecular/RigidityMatrix/Claim612.lean`; `CaseIII/Relabel/Chain.lean`, `ChainColumn.lean`,
  `ForkedArm.lean`). The docstrings of `exists_homogeneousIncidence_of_normals_gen` and of its
  $d = 3$ wrapper `exists_homogeneousIncidence_of_normals` name
  `lem:case-III-claim612-points-affineIndep`, the affine node, and not
  `lem:case-III-claim612-points-affineIndep-real-normals`; the wrapper, now unpinned, has one
  caller, the dead $d = 3$ dispatch `case_III_candidate_dispatch` (`F-167`). The docstrings of
  `interior_hρe₀_of_baseWidening` and `chainData_bottom_relabel` name `lem:case-III general-d` and
  `lem:case-III`, and that of `chainData_relabel_arm_hρGv` no node (now `lem:case-III-chain-eq666`
  and `lem:case-III-chain-relabel-rows`). The docstring of
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` calls `chainData_relabel_arm_hρGv` dead,
  though `chainData_dispatch_interior` calls it and it lies in the main results' closure.
  *Evidence:* read (the docstrings; a `grep` for the callers); measured (the closure of
  `case_III_realization_all_k` in `scripts/blueprint-deps.py`'s Lean cache, at task 3.10).
  *Found:* round 5 task 3.10.
  *Disposition:* done (task 35.3):
  `exists_homogeneousIncidence_of_normals_gen`'s lead names
  `lem:case-III-claim612-points-affineIndep-real-normals`, and the wrapper's gives it as a step of
  `lem:case-III-candidate-dispatch-d3` and as that node's case `d = 3` (task 32.1); the leads of
  `interior_hρe₀_of_baseWidening` and `chainData_relabel_arm_hρGv` name `lem:case-III-chain-eq666`,
  that of `chainData_bottom_relabel` names `lem:case-III-chain-relabel-rows`, and
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`'s says that `chainData_dispatch_interior`
  uses `chainData_relabel_arm_hρGv` (task 35.3). Before: reported (`notes/Prose-report.md`, L11).
- **F-243** · L · the declarations round 5's task 3.11 pinned or unpinned
  (`Molecular/Molecule/Duality.lean`, `Pencil/Statement.lean`;
  `Molecular/GenericLift/HingeGeneric.lean`; `BodyBar/GenericLift.lean`). The docstrings of
  `screwComplementIso`, `screwComplementIso_lineExtensor`, `screwComplementIso_mk_extensor` and the
  helper `equivExteriorPower_lineExtensor` name `lem:panel-hinge-dual-molecular`, now
  `lem:polarity-join`. Those of `screwEquivOfLinearEquiv` and `screwEquivOfLinearEquiv_mk_extensor`
  call them internal plumbing for `lem:screw-map-rows` and `lem:hinge-point-witness`, though four
  `Pencil/` files use them, and they are now `def:induced-screw-map`. The docstring of
  `twoExtensorPoly_eval` names `def:two-extensor`, now `lem:two-extensor-polynomial`, and the
  module headers of `BodyBar/GenericLift.lean` and `HingeGeneric.lean` map `def:two-extensor` and
  `lem:hinge-rows-polynomial-in-points` to pins those nodes no longer have.
  *Evidence:* read (the docstrings and module headers; a `grep` for the callers).
  *Found:* round 5 task 3.11.
  *Disposition:* reported (`notes/Prose-report.md`, L11); round 3: `BodyBar/GenericLift.lean`'s
  header maps each node to its pins, and `twoExtensorPoly_eval`'s docstring names
  `lem:two-extensor-polynomial` (task 27); the docstrings of `screwComplementIso` and
  `screwComplementIso_lineExtensor` name `lem:polarity-join`, and `equivExteriorPower_lineExtensor`'s
  calls it a step of that node (task 37); `screwComplementIso_mk_extensor`'s lead names
  `lem:polarity-join` (task 37.2).
- **F-244** · L · the declarations round 5's task 3.12 pinned or moved (`Molecular/Deficiency.lean`,
  `JacobsCounting.lean`, `TwoCore.lean`). The docstrings of `IsTightPartition` and
  `crossingEdgesWithin` name `lem:exists-tight-partition` and `lem:partitionDef-merge`, now
  `def:tight-partition` and `def:crossing-edges-within`; the section docstring before them names
  `lem:tight-partition-cross-pair`, a label the blueprint lacks, and calls that lemma "a later
  commit". The docstring of `IsSquareTightPartition.rootedAt_inj` names `lem:normal-cross-count`
  for the clause of `lem:normal-cross-count-rooted`, and the section docstring of the rooted normal
  cross edges says "This commit lands" the definition and leaves the assembly to "a later slice".
  The module header of `TwoCore.lean` names `def:two-core` as the node of a file whose results
  three nodes now pin.
  *Evidence:* read (the docstrings and module header).
  *Found:* round 5 task 3.12.
  *Disposition:* done (task 29.1): `JacobsCounting.lean`'s (the lead of `rootedAt_inj` names
  `lem:normal-cross-count-rooted`, the section docstring no process) and `TwoCore.lean`'s header
  (it names the three nodes) (task 28); in `Deficiency.lean`, the leads of `IsTightPartition` and
  `crossingEdgesWithin` name `def:tight-partition` and `def:crossing-edges-within`, and the
  section docstring the two cross-pair nodes and no process (task 29.1); reported
  (`notes/Prose-report.md`, L11).
- **F-245** · L · `linearIndepOn_pencilChartNormal_closedHubNbhd` (`Molecular/Molecule/Pencil/Chart.lean`):
  its docstring calls it the `lem:pencil-nondegenerate` companion, a label the blueprint lacks; the
  node is `def:pencil-nondegenerate`, and no node pins the declaration. The docstrings of the five
  declarations task 3.13 unpinned name no node.
  *Evidence:* read (the docstrings; a `grep` of `blueprint/src` and `CombinatorialRigidity/` for the
  labels of task 3.13's nodes).
  *Found:* round 5 task 3.13.
  *Disposition:* done (task 37.11): the lead of `linearIndepOn_pencilChartNormal_closedHubNbhd`
  calls it a step of `lem:pencil-generic-steer` and names `def:pencil-nondegenerate`, the condition
  it gives (task 37.2); of the five, the lead of `Graph.closedNbhd_subset_vertexSet`
  (`Molecule/Pencil/Motive.lean`) calls it a step of `thm:pencil-jj-equality`, whose proof names it
  (task 37.4), that of `Graph.exists_isAdmissiblePicture` (`MainComponent/Carrier.lean`) a step of
  `lem:pencil-x0-main-picture-open`, whose proof names it (task 37.9), and in
  `MainComponent/Cut.lean` (task 37.11) that of `pathVertex` names the nodes whose formal
  statements give a path by it (`lem:pencil-bridge-fibre`, as the note after it says,
  `thm:pencil-x0-bridge` and `def:open-ear`), `pathVertex_zero` has a docstring, which calls it a
  step of `lem:pencil-bridge-fibre` and of the ear and cycle steps, and the lead of
  `pathVertex_eq_or_exists` calls it a step of `lem:pencil-bridge-fibre`, as the note after it
  says. Before: reported (`notes/Prose-report.md`, L11).
- **F-246** · L · the declarations round 5's task 3.14 moved or unpinned
  (`Molecular/Molecule/Pencil/MainComponent/Bridge.lean`, `Carrier.lean`). The docstring of
  `Graph.embedEdges` names `lem:pencil-jj-embed-edges`, now `def:pencil-embed-edges`. The module
  header of `Bridge.lean` lists `panelSupportExtensor_smul_right` among its main statements, a step
  that no node now pins. Of the other declarations task 3.14 moved or unpinned, two docstrings name
  the definition whose term they concern (`IsAdmissiblePicture.exists_mvPolynomial`,
  `def:pencil-admissible-picture`; `panelSupportExtensor_smul_right`, `def:panel-support-extensor`),
  as the chapter's prose does, and the rest name no node.
  *Evidence:* read (the docstrings and module headers; a `grep` of `CombinatorialRigidity/` for the
  labels of task 3.14's nodes).
  *Found:* round 5 task 3.14.
  *Disposition:* done (task 37.10): in `Carrier.lean` (task 37.9), the leads of
  `IsAdmissiblePicture.exists_mvPolynomial` and `IsAdmissiblePicture.supportExtensor_ne_zero` call
  each a step of the nodes whose proofs name it (the first also names the openness noted after
  `def:pencil-admissible-picture`), and those of `liftingMatrix`, `map_ker_liftingMatrix` and
  `finrank_ker_liftingMatrix` name their node, `def:pencil-lifting-system`; in `Bridge.lean` (task
  37.10), the lead of `Graph.embedEdges` names `def:pencil-embed-edges`, the module header no longer
  lists `panelSupportExtensor_smul_right` among its main results, and its lead calls it a step of
  `lem:pencil-jj-rescale`, whose proof names it, and of `lem:panel-hinge-dual-molecular`, before
  the definition whose term it concerns; the leads of the other declarations of task 3.14 there
  name their nodes (the five pins of `lem:pencil-jj-embed-edges` that node, each with its clause)
  or the node they are a step of. Before: reported (`notes/Prose-report.md`, L11).
- **F-250** · L · the declarations of the nodes round 5's task 5.3 moved across chapters
  (`Molecular/AlgebraicInduction/Theorem55.lean`, `Molecular/Deficiency.lean`). The docstring of
  `PanelHingeFramework.theorem_55_minimalKDof_k` places `lem:case-cut-edge-realization{,-gp}` in
  `molecular-induction.tex`, now `panel-layer.tex`. The section docstring before `IsTightPartition`
  heads it `sec:jacobs-tight-partitions` and places `lem:exists-tight-partition` in `jacobs.tex`,
  now in `deficiency.tex` with `def:tight-partition`. The docstrings of the other moved nodes' pins
  name no chapter.
  *Evidence:* read (the docstrings; a `grep` of `CombinatorialRigidity/` for the six labels and
  for the chapters' file names).
  *Found:* round 5 task 5.3.
  *Disposition:* done (task 36.2): the section docstring before `IsTightPartition` names
  `def:tight-partition` and `lem:exists-tight-partition`, without a chapter, and
  `sec:jacobs-tight-partitions` for the rest (task 29.1); `theorem_55_minimalKDof_k`'s names no
  chapter (task 36.2). Before: reported (`notes/Prose-report.md`, L11).
- **F-253** · L · `infinitesimalMotions_mono_of_span_le` and
  `finrank_infinitesimalMotions_le_of_span_le` (`Molecular/RigidityMatrix/Basic.lean`): their
  docstrings call them KT Lemma 5.2 and the lower semicontinuity of the rank along a panel rotation,
  whose generic member has "the largest supporting spans", and state the inclusion of spans
  reversed: "the constraint span of `F` is contained in that of `F'`", where `hspan` puts the span
  of `F'.supportExtensor e` in that of `F.supportExtensor e`. The blueprint node no longer says
  either (`F-049`, round 2 task 2).
  *Evidence:* read (the two docstrings beside the statements and bodies).
  *Found:* RECONCILE round 2 task 2.
  *Disposition:* done (task 32): both docstrings state the inclusion as `hspan` does,
  `span C'(e) ≤ span C(e)` with `C'` the extensors of `F'`, and say that the lemma is not KT
  Lemma 5.2; the section's header no longer calls them Lemma 5.2. Before: reported
  (`notes/Reconcile.md` §3): round 3's docstring sweep (*Moved to a later round*).
- **F-254** · L · `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
  (`Molecular/AlgebraicInduction/PanelHinge.lean`) and `isInfinitesimallyRigidOn_insert_iff`
  (`Molecular/AlgebraicInduction/Pinning.lean`): the first's docstring says that taking `hspan` as
  a hypothesis makes `lem:case-II` green, and the second's calls the two the Lean grounding of
  that node; since round 2 task 4 the node pins only the second (`F-145`), and nothing calls the
  first. `F-148` covers the rest of both docstrings.
  *Evidence:* read (the two docstrings; the node's pins; a `grep` for the first's callers).
  *Found:* RECONCILE round 2 task 4.
  *Disposition:* done (task 3): the first deleted, and the second's docstring now gives the second
  alone as the Lean grounding of `lem:case-II`, the node's one pin. `F-148` keeps the rest of it.
- **F-256** · L · `exists_good_realization` and `exists_good_realization_reindex`
  (`Molecular/AlgebraicInduction/GenericityDevice.lean`) and `exists_good_realization_const`
  (`CaseI.lean`): their docstrings, and the header of the first two's section, give them as
  `lem:genericity-device`'s Lean; since round 2 task 5 the node pins
  `exists_rankPolynomial_of_le_finrank_linking`, and none of the three is pinned.
  *Evidence:* read (the three docstrings and the section header; the node's pin).
  *Found:* RECONCILE round 2 task 5.
  *Disposition:* done (task 34.1): the third deleted (task 5); the docstrings of the first two, and
  the header of their section, give them as steps of `lem:relative-device-count` (task 34.1).
  Before: reported (`notes/Reconcile.md` §3), to round 3's docstring sweep; the first and the third
  are among the declarations round 2 unpinned.
- **F-258** · L · `linearIndependent_sum_augment_candidateRow` (`Molecular/RigidityMatrix/Basic.lean`),
  `linearIndependent_sum_p2_candidateRow` and `linearIndependent_sum_p3_candidateRow`
  (`Molecular/RigidityMatrix/Claim612.lean`): their docstrings give them as the Lean of
  `lem:case-III-candidate-row`, `lem:case-III-claim612-p2-placement` and
  `lem:case-III-claim612-p3-placement`; since round 2 task 7 the three nodes pin
  `case_III_rank_certification`, and none of the three is pinned.
  *Evidence:* read (the three docstrings; the nodes' pins).
  *Found:* RECONCILE round 2 task 7.
  *Disposition:* done (task 4): all three deleted, with the selectors and the block form
  (`F-267`); six brace-form mentions (`linearIndependent_sum_{augment,p2,p3}_candidateRow`) that
  task 4's `grep` missed repointed (task 5).
- **F-263** · L · `mem_hingeRowBlock_iff` (`Molecular/RigidityMatrix/Claim612.lean`): its
  docstring gives it as `lem:case-III-claim612-block-iff-perp`'s, and the file's header lists it
  in "the part the blueprint puts in `case-iii.tex` rather than `rigidity-matrix.tex`"; since
  round 2 task 12 it is a pin of `def:hinge-row-block` (`rigidity-matrix.tex`, `F-248`).
  *Evidence:* read (the docstring and the header; the two nodes' pins).
  *Found:* RECONCILE round 2 task 12.
  *Disposition:* done (task 32.1): the lead names `def:hinge-row-block`, and the file's header lists
  the lemma as a pin of that node, in `rigidity-matrix.tex`. Before: reported (`notes/Reconcile.md`
  §3): round 3's docstring sweep (*Moved to a later round*).
- **F-264** · L · `PanelHingeFramework.case_III_realization`
  (`Molecular/AlgebraicInduction/CaseIII/Realization.lean`): its docstring gives it as
  `lem:case-III`'s, and the file's header (17) and its first section's (35) call it the all-$k$
  capstone that `Theorem55.lean` consumes, `lem:case-III`'s; it is the $k = 2$ wrapper of
  `case_III_realization_all_k`, which is that capstone, and no declaration calls it. Since round 2
  task 14 `lem:case-III` pins only `case_III_realization_all_k`.
  *Evidence:* read (the docstring, the header and both declarations' statements and bodies; a
  `grep` of the Lean for callers).
  *Found:* RECONCILE round 2 task 14.
  *Disposition:* done (task 4): `case_III_realization` deleted, and the file's header and first
  section, with `case_III_realization_all_k`'s docstring, give `case_III_realization_all_k` as the
  capstone.
- **F-265** · L · `hglue_of_realization`, `hglue_of_independent_rigidityRows`, `hglue_of_forest`,
  `toBodyHinge_rankHypothesis_iff_pinnedMotionsOn_of_generalPosition`,
  `ofParam_rankHypothesis_iff_pinnedMotionsOn` (`Molecular/AlgebraicInduction/CaseI.lean`): five
  unpinned declarations that no main result's proof reaches, each called only by the next (the last
  by none). The first is the only caller of `exists_good_realization_const`, which round 2 unpinned
  (`F-152`, `F-256`), and the second of `exists_finite_spanning_rigidityRows` (`F-233`), so L9
  deletes the two with the five. No ledger entry named them.
  *Evidence:* measured (the liveness screen, block (b) of `notes/Reconcile-lean-cleanup.md`
  *Scope*, over `scripts/blueprint-deps.py`'s Lean cache at `347ba9c4`).
  *Found:* RECONCILE round 3 task 1.
  *Disposition:* done (task 5): the five deleted with the two; the pins they leave without a
  caller, `exists_independent_rigidityRows_of_forest` and
  `toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn`, stay with their nodes.
- **F-266** · L · `eq_succ_of_isInfinitesimalMotion_cycle`
  (`Molecular/AlgebraicInduction/Pinning.lean`): the step of the `Fin m` cycle forms (consecutive
  bodies of a rigid cycle carry the same screw), unpinned, which no main result's proof reaches.
  Its one caller was `isTrivialMotion_of_isInfinitesimalMotion_cycle`, one of the three cycle forms
  that `F-238` names and L9 deletes, so L9's three `Fin m` cycle forms are four; `theorem_55_cycle`
  runs the same telescoping on `α` without it. No ledger entry named it.
  *Evidence:* measured (the liveness screen, block (b) of `notes/Reconcile-lean-cleanup.md`
  *Scope*, over `scripts/blueprint-deps.py`'s Lean cache at `65a5c0ee`); read (its body and
  `theorem_55_cycle`'s).
  *Found:* RECONCILE round 3 task 3.
  *Disposition:* done (task 3).
- **F-267** · L · `BodyHingeFramework.linearIndependent_sum_augment_candidateRow_block`
  (`Molecular/RigidityMatrix/Basic.lean`): the candidate-completion assembly for a block of
  candidate rows, unpinned, which no main result's proof reaches. Its one caller was
  `linearIndependent_sum_augment_candidateRow`, its single-candidate instance, which `F-258` names
  and L9 deletes; `linearIndependent_sum_augment_candidateRow_restriction` runs the same column
  operation and transport back, for one candidate row against a restriction-independent bottom
  block. No ledger entry named it.
  *Evidence:* measured (the liveness screen, block (b) of `notes/Reconcile-lean-cleanup.md`
  *Scope*, over `scripts/blueprint-deps.py`'s Lean cache at `d85b9bea`); read (its body and
  `_restriction`'s).
  *Found:* RECONCILE round 3 task 4.
  *Disposition:* done (task 4).
- **F-268** · L · `PanelHingeFramework.case_III_old_new_blocks` (`CaseIII/Candidate.lean`),
  `hasFullRankRealization_of_independent_rigidityRow` and `hasFullRankRealization_of_candidateSelector`
  (`AlgebraicInduction/CaseI.lean`), `hasFullRankRealization_of_independent_panelRow_index`
  (`AlgebraicInduction/GenericityDevice.lean`): four unpinned declarations that no main result's
  proof reaches; none has a caller but the second, whose one caller is the third. They sit beside
  the declarations RECONCILE round 3 task 4 deletes, but no L9 entry names them.
  *Evidence:* measured (the liveness screen, block (b) of `notes/Reconcile-lean-cleanup.md`
  *Scope*, over `scripts/blueprint-deps.py`'s Lean cache after task 4).
  *Found:* RECONCILE round 3 task 4.
  *Disposition:* done (tasks 38.2 and 38.3): task 38's block (b) at `1b1d9d87` finds the four
  unpinned, dead and with no caller outside them; `case_III_old_new_blocks` deleted with task
  38.2's deletion in `CaseIII/`, the other three with task 38.3's (block (b) at `a1c4fe3a`
  agrees).
- **F-269** · L · `PanelHingeFramework.candidateCompletion_index_injective` and
  `candidateCompletion_panelRow_packaging` (`CaseIII/Arms.lean`),
  `BodyHingeFramework.linearIndependent_sumElim_candidateRow_swap` and
  `linearIndependent_sumElim_candidateBlock_swap` (`RigidityMatrix/Basic.lean`): four more unpinned
  declarations of the candidate-row route that no main result's proof reaches and nothing calls,
  beside `F-268`'s; no L9 entry names them.
  *Evidence:* measured (the liveness screen, block (b) of `notes/Reconcile-lean-cleanup.md`
  *Scope*, over `scripts/blueprint-deps.py`'s Lean cache after task 5).
  *Found:* RECONCILE round 3 task 5.
  *Disposition:* done (task 38.2): task 38's block (b) at `1b1d9d87` finds the four unpinned, dead
  and uncalled; deleting them leaves `linearIndependent_sumElim_block_swap`
  (`Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`, unpinned) without a caller, and it goes
  with them. Task 38.2's block (b) at `af9ad25b` agrees, and the five are deleted.
- **F-271** · L · `PanelHingeFramework.case_I_realization` (`AlgebraicInduction/CaseI.lean`): an
  unpinned declaration that no main result's proof reaches and nothing calls; it is the only caller
  of `lem:claim-6-4`'s pin, `rigidContract_exterior_rank_transport_htransport`, which stays with
  its node. `F-139` and `F-140` call it dead; no L9 entry names it.
  *Evidence:* measured (the liveness screen, block (b) of `notes/Reconcile-lean-cleanup.md`
  *Scope*, over `scripts/blueprint-deps.py`'s Lean cache at task 11.1's tree).
  *Found:* RECONCILE round 3 task 12.
  *Disposition:* done (task 38.3): task 38's block (b) at `1b1d9d87` finds it unpinned, dead and
  uncalled; with it goes `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`,
  which only it calls, and `rigidContract_exterior_rank_transport_htransport` stays with
  `lem:claim-6-4`. Task 38.3's block (b) at `a1c4fe3a` agrees, and the two are deleted.
- **F-272** · L · `exists_packing_move_of_not_inc` (`Induction/ReducibleVertex.lean`) and
  `lem:packing-move` (`molecular-induction.tex`): the conclusion, forests $F'_1, \dots, F'_D$ with
  union $I$ and $x \in F'_j$, holds without the move's hypotheses: swap the index of a forest that
  holds $x$ with $j$. So it does not state the move, and the descent, which needs the forests to
  stay disjoint and only $x$ to leave the donors, could not call it (`F-088`).
  *Evidence:* read (the statement; the descent's body); a `lake lean` witness at `3510e6da`
  (`Fs ∘ Equiv.swap i j` for `x ∈ Fs i`, by `Equiv.iSup_comp`; not retained).
  *Found:* RECONCILE round 3 task 14.
  *Disposition:* done (task 14): the conclusion states the re-choice, $F'_j = F_j \cup \{x\}$
  and $F'_i = F_i \setminus \{x\}$ for $i \neq j$; the node restated.
- **F-274** · L · `Graph.splitOff_isMinimalKDof_of_pos` (`Induction/ForestSurgery/Reduction.lean`):
  `haV : a ∈ V(G)`, `hbV : b ∈ V(G)` and `hvG : v ∈ V(G)` follow from `hla : G.IsLink eₐ v a` and
  `hlb : G.IsLink e_b v b` (the ends of a link are vertices). Its one caller,
  `case_II_realization_all_k` (`AlgebraicInduction/CaseII.lean`), derives its own and uses them
  elsewhere.
  *Evidence:* read (the statement and body).
  *Found:* RECONCILE round 3 task 15.
  *Disposition:* done (task 15.1): the three dropped, derived in the body by `IsLink.right_mem` and
  `IsLink.left_mem`; `lem:reduction-step-pos`, which states none of them, unchanged.
- **F-275** · L · `Graph.splitOff_isMinimalKDof` (`lem:reduction-step`), `Graph.forest_surgery_count`
  (`lem:forest-surgery-count`; both `Induction/ForestSurgery/Reduction.lean`) and
  `PanelHingeFramework.case_III_candidate_dispatch` (`lem:case-III-candidate-dispatch-d3`,
  `CaseIII/Realization.lean`): `F-274`'s pattern, vertex memberships the link hypotheses give. The
  first takes `haV`, `hbV`, `hvG` beside `hla`, `hlb`; the second `haV`, `hbV`; the third `hvG`,
  `haG`, `hbG`, `hcG` beside `hlea`, `hleb`, `hlec`. None is a pass-through of `F-274`'s pin. The
  first's one caller takes its two from `exists_splitOff_data_of_degree_eq_two`, whose conclusion
  states `a ∈ V(G)` and `b ∈ V(G)` beside the two links that give them.
  *Evidence:* read (the statements; a signature scan of the Lean, not retained).
  *Found:* RECONCILE round 3 task 15.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.14 and 38.17). Task 38.1: task
  38.14 drops `splitOff_isMinimalKDof`'s `haV`, `hbV`, `hvG` (from `hla`, `hlb`; callers
  `chainData_extract`, `minimal_kdof_reduction`) and `forest_surgery_count`'s `haV`, `hbV` (callers
  `forest_surgery_split`, `splitOff_exists_base_inter_fiber_lt`), restating `lem:reduction-step` and
  `lem:forest-surgery-count` where they state them; task 38.17 drops `case_III_candidate_dispatch`'s
  `hvG`, `haG`, `hbG`, `hcG` (a dead pin with no caller; `lem:case-III-candidate-dispatch-d3` states
  the links only). Left: the memberships in `exists_splitOff_data_of_degree_eq_two`'s conclusion, a
  conclusion that its four callers destructure.
- **F-276** · L · `SimpleGraph.instDecidableIsLaman` and the definitions under it
  (`PebbleGame/Exec.lean`, `PebbleGame/Algorithm.lean`, `Search/DFS.lean`): `decide +kernel` does
  not evaluate the pebble game's `Decidable` instances. The kernel unfolds the well-founded
  recursion of the search and of `tryAddEdgeWith`, but not core's `List.mergeSort`, which
  `Finset.sort` uses in `outListSorted` and `edgeListSorted`; and from a `module` file, as
  `PebbleGame/Examples.lean` is, it sees no body that is not `@[expose]`d, mathlib's
  `List.insertionSort` among them. A `decide +kernel` proof of `Examples.k4MinusE.IsLaman` would
  need a sort with an exposed body in the two list builders and `@[expose]` across the pebble game's
  and the search's definitions.
  *Evidence:* measured, script not retained (task 16's probes, `scratch/reconcile-lean/t16/`,
  gitignored): `[3, 1, 2].mergeSort` does not reduce in the kernel; with sort-free lists, and with
  insertion-sorted ones, `runPebbleGameWith` accepts K4 − e and rejects K4 under `decide +kernel` in
  a non-module file; from a `module` file `decide +kernel` fails on
  `(⊤ : SimpleGraph (Fin 2)).IsLaman`, which it proves from a non-module file, on the search alone,
  and on `List.insertionSort`.
  *Found:* RECONCILE round 3 task 16.
  *Disposition:* reported (to the PI at the round's close, as a possible later item: task 16 found
  the route not cheap, and the round does not queue it).
- **F-277** · L · `CombinatorialRigidity.Search.reachClosureComputable` (`Search/DFS.lean`;
  `def:reachClosureComputable`): it runs the search once for each vertex `w`, with the predicate
  `· = w`. Since task 17 a search from no marked vertex that fails returns a marked set that holds
  its start and is closed under the arcs (`reachableFindingAux_complete`), and each vertex it marks
  is reachable from the start, so one search with `P` false everywhere returns the region as its
  marked set. That body would restate `def:reachClosureComputable` (the region as the vertices `w`
  whose search for $P_w$ does not fail), a statement change under the round's hygiene rule.
  *Evidence:* read (the bodies of `reachClosureComputable` and of task 17's `reachableFindingAux`;
  the statement of `reachableFindingAux_complete`); that the marked vertices are reachable is not
  proved.
  *Found:* RECONCILE round 3 task 16.
  *Disposition:* reported (`notes/Reconcile-lean-cleanup.md` *Candidates for the PI*).
- **F-278** · L · `SimpleGraph.Henneberg.isoOfOptionSubtypeNe` (private) and
  `SimpleGraph.Henneberg.isoTypeIIOfThreeNeighbors` (`HennebergReverse.lean`): the first's
  `hnone : ¬ H.Adj none none` holds for every simple graph (`SimpleGraph.irrefl`; its callers pass
  `by simp`), and the second's `hab : a ≠ b` is not needed, as the iso holds at `a = b` too.
  *Evidence:* read (the statements and bodies); a `lake lean` witness, copies without the two
  that elaborate with the same proofs (`scratch/reconcile-lean/Docstrings-t25-1.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 25.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.11). Task 38.1: drop both, the
  private lemma's `hnone` by `SimpleGraph.irrefl` where its body needs it (its two callers in the
  file pass `by simp`), and `hab` (callers `IsLaman.exists_typeI_or_typeII_reverse`,
  `IsLaman.isGenericallyRigidInj_two_of_card` in `LamanTheorem.lean`,
  `IsSparse.exists_rowIndependent_placement` in `MatroidIdentification.lean`); no node pins either.
- **F-279** · L · unpinned declarations of `Search/DFS.lean`, of `Mathlib/`, of `PebbleGame/`, of
  `Matroid/` and of `BodyBar/` that no declaration of the project uses: twenty-six in the first
  three and sixty-five in the last two. Outside `Matrix/Rank.lean`,
  `Dimension/Constructions.lean` and `PebbleGame/`, `Fin.ofNat_eq_mk` (used only by the next) and
  `Fin.two_eq_mk_of_lt`,
  `Sym2.mk_mem_image_map_some_iff`, `Pi.basisFun_dualBasis`, `LinearIndepOn.dualMap_of_surjective`,
  `ExteriorAlgebra.ιMulti_family_congr`, `exteriorPower.coe_pairingDualEquiv`;
  `reachClosureComputable_closed`, `self_mem_reachClosureComputable`,
  `DirectedWalk.card_reversedArcsFinset`, `DirectedWalk.fst_mem_vertices_of_mem_reversedArcsFinset`,
  `DirectedWalk.mapRel_length`; in `Matrix/Rank.lean` (task 25.3; none in
  `Dimension/Constructions.lean`), `Matrix.det_mem_range_of_entries`,
  `Matrix.linearIndependent_rows_iff_det_mul_transpose_ne_zero`,
  `Matrix.linearIndependent_row_of_zero_left_cols`, `Matrix.rowOp_isUnit_det`,
  `Matrix.exists_rowOp_of_strictInjection`,
  `Matrix.rowOp_strictInjection_submatrix_eq_fromBlocks_zero₁₂` and `Matrix.rowOp_zeroes_upperRight`
  (used only by the previous),
  `LinearIndependent.finrank_dualCoannihilator_along_affine_path_cofinite` and
  `LinearIndependent.le_finrank_span_along_affine_path_cofinite` (used only by the previous); in
  `PebbleGame/Basic.lean` (task 26), `out_reverse_le_of_outle`, `peb_reverse_tail`,
  `peb_addArc_source` (whose statement `pebOn_addArc` re-derives in its proof), `span_addArc` and
  `span_empty`. In `Matroid/` and `BodyBar/` (task 27, the screen run to a fixed point, so a
  declaration that only others of the set use counts; `rfl` lemmas and generated names left
  out): in the files ported from `apnelson1/Matroid`, `Submodular.lean`'s structure
  `PartialTransversal` with its four fields, its `HasSubset` instance and the 42 declarations
  under its name, `rado_v2` (Rado's theorem in that form), `Transverses`, `Transverses'` and their
  seven lemmas, and `generalized_halls_marriage'`, and `Union.lean`'s `matroid_partition_eRk'`
  and `matroid_partition'` (used only by the previous), where removing package code is also a
  question about the port, whose credit stays; in the project's files, `Union_pow_rank_eq` and
  `cycleMatroid_eRk_add_numberOfComponents_restrict` (`TreePacking.lean`),
  `stdPlacement_rigidityMap_apply` (`TayTheorem.lean`) and `spanningVerts_edgeMultiply`
  (`BodyHinge.lean`; `body-hinge.tex`'s prose names it). Also
  `cross₃_ne_zero_iff_linearIndependent` (`Molecule/Pencil/Chart.lean`) builds, in each direction,
  the chain that `Matrix.linearIndependent_rows_iff_det_ne_zero` packages, which its imports do not
  reach.
  *Evidence:* measured (the reverse dependencies of statements and bodies in the Lean cache of
  `scripts/blueprint-deps.py`, at `522a0c0a` plus task 25.2's docstrings, at `0c34177f` for
  task 25.3, at `05b0dae4` for task 26 and at `7e5c1cb2` for task 27; `rfl` lemmas left out);
  read (`Chart.lean`'s proof and import closure; `pebOn_addArc`'s proof).
  *Found:* RECONCILE round 3 tasks 25.2, 25.3, 26 and 27.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.2 to 38.8 and 38.20; task 38's
  screen ends this entry). Task 28 adds two in
  `SquareGraph.lean`, `square_mono` and `three_le_ncard_closedNeighborSet_of_two_le_degree`, whose
  docstrings said the proof of `thm:jacobs` and the square-graph dictionary use them (no
  declaration does; the cache at `0819b42e`). Task 30 adds twenty-two in
  `Molecular/Induction/Operations.lean`: `splitOff_swap_ab`,
  `ChainData.removeVertex_isLink_edge_succ_pred_off`, `shiftCycle_eq_cons` (used only by the next),
  `shiftPerm_eq_swap_mul`, `shiftPerm_inv_apply_off`, `shiftPerm_inv_vtx_one`,
  `seedShift_inv_cancel`, `seedShift_off_cycle`, `getElem_shiftBodyList_zero`,
  `shiftBodyList_eq_cons`, `shiftBody_ne_succ`, the seven `shiftEdgePerm_inv_*` lemmas,
  `shiftEdgePerm_apply_edge_off`, `_edge_top` and `_edge_pred` (used only by three of those), and
  the definition `candidateSeed` (used only by its `rfl` lemma), all under `Graph.ChainData` but the
  first; their docstrings named consumers that do not use them or do not exist
  (`chainData_relabel_arm`, `bottomRelabel_image_mem_span_caseIIICandidate`,
  `case_III_arm_corner_assembly`). Its screen reads the code, comments stripped, for each name, to
  a fixed point, as the cache counts a shared `_proof_N` auxiliary as a use
  (`scratch/reconcile-lean/t30/unused_src.py`, gitignored; at `722c88ef`). Task 30.1 adds four in
  `Molecular/Induction/` (the same screen, at `552051eb`): `Graph.rigidContract_eq_contract`, whose
  docstring called it the entry point of `lem:rigidContract-isMinimalKDof`'s proof (that proof uses
  `rigidContract_eq_contract'`), `Graph.exists_adjacent_degree_two_pair_of_edgeBound` (used only by
  the next) and `Graph.exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos`, whose
  docstring said it discharged a "safe-vertex obligation" (`ReducibleVertex.lean`), and
  `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (`Contraction.lean`), which two docstrings
  said took the rank equality that `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` takes.
  Task 31 adds five in `Molecular/Induction/ForestSurgery/EdgeSplitting.lean` (the same screen, at
  `b08c948e`): `Graph.fiberAtVertex_inter_edgeSet` (used only by the next),
  `Graph.fiberAtVertex_inter_edgeSet_ncard` (used only by `fiberDegree_le`), the definition
  `Graph.fiberDegree` (used only by the next two), `Graph.fiberDegree_mono` and
  `Graph.fiberDegree_le`, whose docstrings said that the surgery's count `h' ≤ D − 2` rests on them
  and that they bound its degrees (`forest_surgery_count` uses `fiberAtVertex` alone).
  Task 32 adds four in `Molecular/RigidityMatrix/Basic.lean` (the same screen and the cache, at
  `8263eed0`): `BodyHingeFramework.isInfinitesimallyRigidOn_of_isInfinitesimallyRigid`, whose
  docstring said the cycle and two-body base cases use it,
  `linearIndependent_sumElim_corner_bottom_of_disjoint_pin`,
  `span_range_hingeRow_blockSpanning_eq_rigidityRows` (whose `hmem` `hspan` gives) and
  `span_range_hingeRow_crossFramework_eq_rigidityRows_of_off`; the file's two others,
  `linearIndependent_sumElim_candidateRow_swap` and `_candidateBlock_swap`, are `F-269`'s.
  Task 32.1 adds seven (the same screen and the cache, at `0bdbf32a`): in
  `Molecular/RigidityMatrix/Claim612.lean`, `exists_independent_perp_family_escape`, whose docstring
  said the discriminator builds its second normal through it (it uses
  `exists_independent_perp_family`), and `omitTwoExtensor_homogenize_eq_extensor_kept`, whose
  docstring named a caller `case_III_claim612` that does not exist; in `Molecular/Meet.lean`,
  `coe_gradedMul`, `wedgeProdBilin_apply`, `piBasisFun_toDual_symm`, and the `d = 3` forms
  `extensor_mem_range_map_subtype_of_mem` and `exists_smul_eq_of_mem_range_map_subtype`.
  Task 32.2 adds the whole of `Molecular/RigidityMatrix/Concrete.lean` and two declarations of
  `Molecular/Extensor.lean` (the same screen and the cache, at `814570e4`). No declaration outside
  `Concrete.lean` uses any of its 81 declarations, none of them pinned: `CaseIII/Candidate.lean`
  imports the file and uses none of them, and its docstrings named consumers that do not exist
  (`case_III_rank_certification_matrix`, `chainData_arm_realization_zero₁₂`) or do not use it
  (`chainData_dispatch`). Removing it would leave eleven declarations without a caller: in
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`, `Matrix.of_eq_mul_of_row_comb`,
  `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks`, `_submatrix_fromBlocks` and
  `_submatrix_fromBlocks_zero₁₂` (and through them
  `Matrix.rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` and `_zero₂₁_`),
  `Matrix.rank_submatrix_inr_of_zero_left_cols` and `exists_finCard_linearIndependent_selection`; in
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`, `Module.Basis.linearIndependent_coe_subtype`
  and `Module.Basis.span_coe_eq`; and in `RigidityMatrix/Basic.lean`,
  `BodyHingeFramework.span_range_hingeRow_crossFramework_eq_rigidityRows`. In `Extensor.lean`,
  `join_assoc` and `pluckerCoord_univ`.
  Task 33 adds eight (the same screen and the cache, at `a7e40ff4`): in
  `Molecular/AlgebraicInduction/Pinning.lean`, `pinnedMotionsOn_withGraph_eq_of_block_internal`,
  whose docstring said that it reads the block pin off the contraction, which is not a subgraph,
  `finrank_pinnedMotions_le_withGraph` and `finrank_pinnedMotions_withGraph_eq`; in
  `PanelLayer.lean`, `exists_two_perp_of_linearIndependent_normals`, whose hypothesis is unused too
  and whose docstring called it a step of the meet decomposition,
  `panelSupportExtensor_not_mem_span_of_triLI`, whose docstring said that
  `hingeRowBlock_not_le_of_supportExtensor_not_mem_span` (`Concrete.lean`) consumes it,
  `screwDim_le_finrank_infinitesimalMotions`, `trivialMotions_le_partitionMotions` and the `@[simp]`
  lemma `mem_partitionMotions`. Removing them leaves no other declaration without a caller.
  Task 34 adds none (the same screen and the cache, at `b03f8530`): of the four it finds in
  `CaseI.lean`, `hasFullRankRealization_of_independent_rigidityRow` and
  `hasFullRankRealization_of_candidateSelector` are `F-268`'s, and `case_I_realization` is
  `F-271`'s, as is `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set`, which
  only it uses; it finds none in `CaseII.lean`.
  Task 34.1 adds twenty-two (the same screen, over `GenericityDevice.lean` and `Coupling.lean`
  together, and the Lean cache, at `126c2dbb`): in `GenericityDevice.lean`,
  `exists_rankPolynomial_of_rigidOn`, `exists_rigidOn_ofNormals_of_hasFullRankRealization`,
  `hasFullRankRealization_of_rigidOn_seed`, the seven `hasFullRankRealization_of_splice…` and
  `hasGenericFullRankRealization_of_splice_ofNormals`, and
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` with its `_linking` and
  `_linking_set` forms; in `Coupling.lean`, the five `…_couple_…` realizations,
  `hasGenericFullRankRealization_of_splice_set_ofNormals`, `rigidContract_rigidity_transport` and
  `degeneratePlacement_ofNormals_normal`. The screen's twenty-third,
  `hasFullRankRealization_of_independent_panelRow_index`, is `F-268`'s. Removing the twenty-three
  would leave without a caller the pinned `hasFullRankRealization_of_independent_panelRow` and
  `exists_independent_panelRow_subfamily_of_rigidOn`, `Pinning.lean`'s pinned
  `isInfinitesimallyRigidOn_of_splice` and unpinned `isInfinitesimallyRigidOn_of_finrank_le_set`,
  and `PanelHinge.lean`'s pinned `isGeneralPosition_ofParam`; the pinned ones stay with their nodes.
  Task 35 adds thirteen in `CaseIII/Candidate.lean` (the same screen, over `Arms.lean` and
  `Candidate.lean` together, and the Lean cache, at `d4ec064b`): the three lemmas on the hinges of
  `F_0` and of a second framework (`caseIIICandidate_hsupp_of_rowClassifier`, and the two that only
  it uses, `caseIIICandidate_supportExtensor_eq_ofNormals_of_ends_eq` and
  `_reproduced_eq_ofNormals`), whose docstrings said that the dispatch supplies their hypotheses for
  `Concrete.lean`'s `_Gab` lemmas, `caseIIICandidate_supportExtensor_ne_zero_of_genPos`, whose
  docstring named a user `chainData_arm_realization_zero₁₂` that does not exist, and the nine
  lemmas of its count modulo a base block: `finrank_span_rigidityRows_ge_of_corner`,
  `exists_le_finrank_span_rigidityRows_eq_card_of_injective_map`,
  `exists_genuine_relabelImage_base_block` and
  `span_relabelImage_le_and_finrank_and_acolumn_vanish` (used only by it), `exists_seed_base_block`
  and `ofNormals_removeVertex_rigidityRow_comp_single_self` (used only by it), and
  `linearIndependent_mkQ_corner_of_gate` with `linearIndependent_mkQ_panelRow_of_edge` and
  `notMem_span_mkQ_pmR_row_of_gate` (used only by it), whose docstrings named users
  `case_III_arm_realization_chain`, `case_III_rank_certification_chain` and
  `case_III_arm_corner_assembly` that do not exist. The screen's other three,
  `case_III_old_new_blocks` and `Arms.lean`'s `candidateCompletion_index_injective` and
  `_panelRow_packaging`, are `F-268`'s and `F-269`'s. Removing them would leave without a caller
  `Submodule.finrank_add_card_le_of_linearIndependent_mkQ`,
  `exists_le_finrank_eq_card_of_injective_map`, `linearIndependent_mkQ_sumElim_unit_of_notMem_span`
  and `linearIndependent_mkQ_of_comp` (`Mathlib/LinearAlgebra/Dimension/Constructions.lean`), and
  `BodyHingeFramework.exists_genuine_linearIndependent_basis_of_rigidityRows_diff` and
  `span_rigidityRows_diff_singleton_eq_of_mem_span` (`RigidityMatrix/Basic.lean`); and
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link` with one user,
  `funLeft_dualMap_genuineRow_mem_span_caseIIICandidate` (`Relabel/Chain.lean`), which no main
  result reaches.
  Task 35.1 adds one in `CaseIII/Realization.lean` (the same screen and the Lean cache, at
  `e29aff9c`): `chainData_split_realization`, whose docstring gave it as `lem:case-III`'s step whose
  `htrans` the choice of a panel fills; its `htrans` asks for `n'` at every nonzero form, where the
  choice of a panel gives it at one, and the proof of `lem:case-III-chain-dispatch` does not use it.
  Removing it would leave `Graph.ChainData.succ_ne_pred_castSucc` (`Induction/Operations.lean`,
  unpinned) without a caller.
  Task 35.2 adds thirty-one in `CaseIII/Relabel/` (the same screen, over `Basic.lean` and
  `Arm.lean` together, and the Lean cache, at `2cbc6e2a`), none of them pinned. In `Basic.lean`:
  the general renamings `ofNormals_relabel_perm`, `rigidityRow_relabel_perm` (used only by the next)
  and `rigidityRow_chainData_relabel`, `rigidityRow_relabel_off_cycle`,
  `rigidityRow_relabel_to_block` and `_to_block_swap`; `mem_span_rigidityRows_ofNormals_relabel`;
  the two moves composed, `funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows`, and one move
  along the chain, `Graph.ChainData.funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows`;
  `wstep_foldr_funLeft_eq`, `wstep_foldl_funLeft_eq` (used only by
  `Graph.ChainData.shiftBodyListAsc_relabel_foldl_hingeRow`, also unused) and
  `wstep_foldr_mem_span_rigidityRows` (used only by the last of the next); and the frameworks of a
  chain with fixed normals, the definitions `Graph.ChainData.shiftBodyFramework` and
  `shiftBodyFrameworkTotal` with `shiftBodyFramework_graph`, `_supportExtensor`, `_htrans`,
  `shiftBodyFrameworkTotal_eq` and `shiftBodyList_foldr_mem_span_rigidityRows`. In `Arm.lean`, all
  under `Graph.ChainData`: the seven lemmas at `i = 3` (`i3_…_deRisk`),
  `panelCorrespondence_supportExtensor` (used only by one of those and the next),
  `candidate_supportExtensor_perp_of_base`, `freshEdge_interior_acolumn_sup` and
  `freshEdge_surviving_row_mem_of_witness`. Their docstrings named users that do not exist
  (`chainData_relabel_arm`, `exists_interior_redundancy_witness`, `ρ₀_perp_interior_chain_edge`) or
  called them the steps of a proof still to come. Removing them would leave without a caller
  `Relabel/Chain.lean`'s `BodyHingeFramework.acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows` and
  six lemmas of `Induction/Operations.lean` under `Graph.ChainData` (`shiftBody_pred_ne`,
  `shiftBody_pred_ne_succ`, `shiftBodyGraph_isLink_pred_edge`, `shiftBodyGraph_deg_two_right`,
  `shiftBodyGraph_off_succ`, `shiftBodyGraph_isLink_of_off_body`), all unpinned, and the pinned
  `rigidityRows_ofNormals_relabel`, which stays with its node.
  Task 35.3 adds twenty-one in `CaseIII/Relabel/` (the same screen, over `Chain.lean`,
  `ChainColumn.lean` and `ForkedArm.lean` and then over the five files of the directory, and the
  Lean cache, at `c3a4b34b`), none of them pinned. In `Chain.lean`: the definition
  `Graph.ChainData.shiftEndsAdv` with `shiftEndsAdv_zero` and `_succ`,
  `Graph.ChainData.shiftBodyFrameworkAsc_graph`, the two lemmas on the frameworks `F_t`
  (`funLeft_dualMap_genuineRow_mem_span_caseIIICandidate`, used only by
  `funLeft_dualMap_pmR_group_mem_span_caseIIICandidate`), `hingeRow_acolumn_mem_span_rigidityRows`,
  and three that only task 35.2's use, `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`,
  `candidate_perp_two_incident_supportExtensors` and `candidate_perp_two_incident_panels` (used only
  by the previous). In `ChainColumn.lean`, all under `Graph.ChainData` but the first:
  `BodyHingeFramework.edgeIndexedCombination_comp_single_off`,
  `interiorGroup_acolumn_two_group_decomp`, `baseRedundancy_group_acolumn_mem_inf` (used only by
  `baseRedundancy_group_acolumn_perp`, also unused),
  `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy`,
  `chainData_freshEdge_perp_of_witness`, and the five lemmas with the renamed selector:
  `i3_candidateBlock_transport_deRisk` (used only by
  `chainData_candidateRow_edgeGrouped_transport_blocks`),
  `chainData_candidateRow_edgeGrouped_transport_comb`,
  `chainData_freshEdge_perp_transport_base_to_candidate` (used only by the next) and
  `chainData_freshEdge_slot_perp`. None in `ForkedArm.lean`. Their docstrings named users that do
  not exist (`chainData_relabel_arm`, `case_III_rank_certification_chain`) or do not use them
  (`notMem_span_mkQ_pmR_row_of_gate`). Removing them with task 35.2's would also leave without a
  caller the pinned `candidateRow_ac_eq_neg` (`RigidityMatrix/Claim612.lean`), which stays with its
  node.
  Task 36 adds eight in `Molecular/AlgebraicInduction/PanelHinge.lean` (the same screen, over it and
  `Nonvacuity.lean` and then with `Pinning.lean`, and the Lean cache, at `62dced48`; `rfl` lemmas
  left out), none of them pinned: `ofNormals_withGraph`, `ofParam_eq_ofNormals_momentCurve`, the
  `@[simp]` lemma `withNormal_normal_self`, `toBodyHinge_hnew_of_isLink_incident`,
  `finrank_toBodyHinge_pinnedMotions_le_withGraph`,
  `finrank_toBodyHinge_pinnedMotions_withGraph_eq`, and `toBodyHinge_pinnedMotions_le_withGraph` and
  `toBodyHinge_pinnedMotions_withGraph_eq` (used only by the previous two). `Nonvacuity.lean` has
  only its witness, which nothing is meant to use. With task 33's, removing them would also leave
  without a caller `Pinning.lean`'s `pinnedMotions_le_withGraph`, `pinnedMotions_withGraph_eq` and
  `hnew_of_isLink_incident` and `RigidityMatrix/Basic.lean`'s `hingeConstraint_comm`, all unpinned,
  and the pinned `toBodyHinge_withGraph`, which stays with its node.
  Task 37 adds one in `Molecular/Molecule/ProjectiveInvariance.lean` (the same screen, over
  `ScrewVelocity.lean`, `Duality.lean`, `ProjectiveInvariance.lean` and `Dictionary.lean` together,
  and the Lean cache, at `b504aa52`; `rfl` lemmas left out, and the `@[simp]` lemmas that `simp`
  calls use, as the cache shows): `BodyHingeFramework.isInfinitesimallyRigidOn_mapExtensor`, whose
  docstring gave `thm:projective-invariance` as its node. Removing it leaves no other declaration
  without a caller.
  Task 37.2 adds ten in `Molecular/Molecule/Pencil/` (the same screen, over `Statement.lean` and
  `Chart.lean` together, at `b8cf8acb`; the `rfl` lemma `cross₃L_apply` left out), none of them
  pinned: in `Statement.lean`, `extensorInPanel_smul_iff`, `extensorInPanel_smul_normal_iff`,
  `extensorThroughPoint_smul_point_iff` and `extensorThroughPoint_smul_iff`, whose section header
  said that the cut case reasons with them; in `Chart.lean`, `cross₃_add_fst`, `cross₃_smul_fst`,
  `cross₃_add_snd` and `cross₃_smul_snd`, whose section header called the multilinearity of
  `cross₃` load-bearing for the chart's polynomial rows (`Engine.lean` takes the coordinates from
  `cross₃_apply`), and the private `cons_updateRow_zero` and `cons_updateRow_one` (used only by
  them). Removing them leaves no other declaration without a caller.
  Task 37.3 adds one in `Molecular/Molecule/Pencil/Arms.lean` (the same screen, over `Arms.lean` and
  `ArmsAssembly.lean` together, at `69fb2212`), not pinned: `le_finrank_toDualPerp_single`, which
  the docstring of `exists_reposition_cross_incidences_avoiding` said its choices use (they use
  `finrank_toDualPerp_single_eq`). Removing it leaves no other declaration without a caller.
  Task 37.7 adds one in `Molecular/Molecule/Pencil/Pair.lean` (the same screen, over `Pair.lean` and
  `Pair2.lean` together, at `d8f57d43`), not pinned:
  `exists_isNondegPencilRealization_parallel_pair`, the witness that two bodies joined by two edges
  are nondegeneracy-feasible, which the docstring of `PencilNondegFeasible` (`Motive.lean`) names
  and whose claim the remark before `def:pencil-conditioned-pair` states. Removing it leaves no
  other declaration without a caller. Task 37.13 adds one in
  `Molecular/Molecule/Pencil/MainComponent/ContractCurve.lean` (the same screen and the cache, at
  `30a83572`), not pinned: `Graph.IsAdmissiblePicture.eq_of_forall_closedNbhd`, two coefficient
  vectors that agree on the picture points of a closed neighbourhood are equal, whose docstring now
  says that no declaration uses it. Removing it leaves no other declaration without a caller.
  Task 37.15 adds two in `Molecular/Molecule/Pencil/MainComponent/` (the same screen, over
  `Lines.lean` and `EarGen.lean` together, and the cache, at `68a88088`), neither pinned:
  `pointJoin_mem_star_right` (`Lines.lean`), a line `u ∧ y` lies in the star of `y`, and
  `earPicture_of_notMem` (`EarGen.lean`), off `V₁` the picture of ear data is its own coordinate,
  whose docstrings now say that no declaration uses them. Removing them leaves no other declaration
  without a caller.
  Task 38's screen (block (b) of the work log's *Scope* over the Lean cache at `1b1d9d87`, the
  deletions taken in task order, each after the earlier ones; `scratch/reconcile-lean/t38/seq.py`,
  gitignored) finds each name above unpinned, dead and with no caller outside the set, but for four
  callers the cache gives wrongly: `chainData_freshEdge_slot_perp` and
  `chainData_freshEdge_perp_transport_base_to_candidate` (`ChainColumn.lean`) and
  `Graph.ChainData.shiftCycle_eq_cons` (`Operations.lean`) are "called" by later declarations that
  reuse their auxiliary `by omega` proofs (no use in the source), and `candidateSeed` by its `rfl`
  lemma `candidateSeed_apply`, which goes with it. `shiftEdgePerm_apply_edge_top` and `_edge_pred`
  have seven callers each, live ones among them, and stay. The tasks: 38.2, the `CaseIII/` parts
  (tasks 35 to 35.3) with `F-268`'s and `F-269`'s there, and nineteen orphans:
  `hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`; in `RigidityMatrix/Basic.lean`,
  `exists_genuine_linearIndependent_basis_of_rigidityRows_diff`,
  `span_rigidityRows_diff_singleton_eq_of_mem_span` and `funLeft_dualMap_comp_single`; ten of
  `Operations.lean` under `Graph.ChainData`, `succ_ne_pred_castSucc`, `shiftBody_pred_ne`,
  `shiftBody_pred_ne_succ`, `shiftBody_deg_two`, `shiftBody_isLink_pred_edge`,
  `shiftBodyGraph_deg_two`, `shiftBodyGraph_deg_two_right`, `shiftBodyGraph_isLink_pred_edge`,
  `shiftBodyGraph_off_succ` and `shiftBodyGraph_isLink_of_off_body`;
  `Dimension/Constructions.lean`'s four; and `linearIndependent_sumElim_block_swap`. The pinned
  `rigidityRows_ofNormals_relabel` and `candidateRow_ac_eq_neg` stay. 38.3, task 34.1's part with
  `F-268`'s three and `F-271`'s two, and the orphan `isInfinitesimallyRigidOn_of_finrank_le_set`
  (`Pinning.lean`). 38.4, tasks 33's and 36's parts, and the orphans `pinnedMotions_le_withGraph`,
  `pinnedMotions_withGraph_eq` and `hnew_of_isLink_incident` (`Pinning.lean`) and
  `hingeConstraint_comm` (`RigidityMatrix/Basic.lean`). 38.5, the whole of `Concrete.lean`, tasks
  32's and 32.1's parts and `join_assoc`, and twelve orphans, task 32.2's eleven and
  `BodyHingeFramework.hingeRow_mem_rigidityRows_of_supportExtensor_eq`. 38.6, tasks 30's to 31's
  parts with `candidateSeed_apply`, and the orphan `shiftBody_isLink_succ_edge`;
  `Graph.indep_matroidMG_of_noRigid_of_deficiency_pos`, which task 30.1's two
  `exists_adjacent_degree_two_pair_…` leave without a caller, waits for `F-282`'s repeated
  derivation, which would make it the step of `lem:edge-set-indep-pos`'s pin (task 38.1 decides).
  38.7, tasks 37's to 37.15's parts but `Pair.lean`'s. 38.8, tasks 25.2's, 25.3's, 26's and 28's
  parts and task 27's three in `BodyBar/`, with the orphans `out_reverse_tail` and `spanArcs_empty`
  (`PebbleGame/Basic.lean`) and `Matrix.linearIndependent_rows_iff_rank_eq_card`. Left: the vendored
  port's part (`Submodular.lean`'s and `Union.lean`'s), as `DESIGN.md` keeps the rebased port whole
  for an upstream offer; `spanningVerts_edgeMultiply` and `pluckerCoord_univ`, which
  `body-hinge.tex` and `extensor.tex` name as the Lean form of their prose; and
  `exists_isNondegPencilRealization_parallel_pair`, the Lean witness of the claim before
  `def:pencil-conditioned-pair`. `cross₃_ne_zero_iff_linearIndependent` is a mathlib-lemma item,
  task 38.1's. A whole-project screen of the cache (the declarations that no pin, main result,
  witness or executable reaches; `t38/dead.py`) holds every name above but the three with a false
  caller; its other hits are generated names, `@[simp]` and `rfl` lemmas whose uses leave no
  constant in a proof, and some fifteen basic lemmas of their files' definitions
  (`SimpleGraph.IsTight.isSparse`, `isLaman_iff`, `IsSparse.deleteEdges`,
  `EdgeSetRowIndependent.mono`, …), which no sweep task listed; task 38 does not act on them. Task
  38.1: task 38.20 re-proves `cross₃_ne_zero_iff_linearIndependent` by the mirror
  `Matrix.linearIndependent_rows_iff_det_ne_zero`
  (`Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean`, imported into `Chart.lean`), in place of
  its two `linearIndependent_row_iff_isUnit` chains. Round 3: the `CaseIII/` parts (tasks 35 to
  35.3) deleted with their nineteen orphans; block (b) at `af9ad25b` gives the same names, and the
  build confirms that the two `ChainColumn.lean` callers were a shared `by omega` auxiliary (task
  38.2). Round 3: task 34.1's twenty-two deleted, with `F-268`'s three and `F-271`'s two, and the
  orphan `isInfinitesimallyRigidOn_of_finrank_le_set`; block (b) at `a1c4fe3a` gives the same
  names, and the five pins stay, uncalled (task 38.3). Round 3: tasks 33's and 36's sixteen
  deleted, with the four orphans `pinnedMotions_le_withGraph`, `pinnedMotions_withGraph_eq`,
  `hnew_of_isLink_incident` and `hingeConstraint_comm`; block (b) at `f3677e99` gives the same
  names, and the pinned `toBodyHinge_withGraph` stays, uncalled (task 38.4). Round 3: the whole of
  `Concrete.lean` (81 declarations) deleted, with its imports, tasks 32's four, 32.1's seven and
  `join_assoc`, and the twelve orphans; block (b) at `faa83b72` gives the same names, and the build
  and the caches confirm that no other declaration is left without a caller (task 38.5).
  Round 3: tasks 30's twenty in `Operations.lean` (but `shiftEdgePerm_apply_edge_top` and
  `_edge_pred`, live) with `candidateSeed_apply`, 30.1's four and 31's five deleted, with the orphan
  `shiftBody_isLink_succ_edge` and `F-282`'s `indep_matroidMG_of_noRigid_of_deficiency_pos`;
  block (b) at `b630905b` gives the same names, `shiftCycle_eq_cons` live only through the shared
  `by omega` auxiliary of `shiftPerm_vtx_top`, and the build and the caches confirm that no other
  declaration is left without a caller (task 38.6).
  Round 3: tasks 37's to 37.15's fifteen in `Molecule/` deleted, `Pair.lean`'s witness staying;
  block (b) at `0f2d588e` gives the same names, unpinned, dead and with no caller outside
  the set, and no orphan, and the build and the caches confirm that no other declaration is left
  without a caller (task 38.7).
  Round 3: tasks 25.2's, 25.3's, 26's and 28's parts and task 27's three in `BodyBar/` deleted but
  `exteriorPower.coe_pairingDualEquiv`, thirty, with the orphans `out_reverse_tail`,
  `spanArcs_empty` and `Matrix.linearIndependent_rows_iff_rank_eq_card`, and the emptied
  `Mathlib/Data/Fin/Basic.lean` with them; block (b) at `6885f075` gives the same names, unpinned,
  dead and with no caller outside the set, the pinned `Union_rank_eq` left uncalled stays, and the
  build and the caches confirm that no other declaration is left without a caller.
  `coe_pairingDualEquiv` stays by task 38's rule for a declaration that witnesses a chapter's
  claim: `def:meet-pairing-dual` pins `exteriorPower.pairingDualEquiv`, a `Basis.equiv`, and states
  that the determinant map is an isomorphism, and it alone proves that the equivalence is that map
  (task 38.8).
- **F-280** · L · `Graph.isKDof_zero_of_cycle` and `Graph.deficiency_eq_of_cutEdges_ncard_le_one`
  (`Molecular/Deficiency.lean`): the first's `hD : 3 ≤ bodyBarDim n` follows from
  `hm : 3 ≤ m` and `hmD : m ≤ bodyBarDim n` (`lem:cycle-zero-dof` states `3 ≤ m ≤ D` alone), and
  the second's `hne : V₁.Nonempty` is used only for `Nonempty α`, which `hssub : V₁ ⊂ V(G)` gives.
  *Evidence:* read (the statements and bodies); a `lake lean` witness, the first called with
  `by omega` for `hD` and a copy of the second without `hne` that elaborates with the same proof
  (`scratch/reconcile-lean/Hyps-t29.lean`, gitignored).
  *Found:* RECONCILE round 3 task 29.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.12). Task 38.1: drop both: `hD`
  (`by omega` from `hm`, `hmD` where the body needs it; `lem:cycle-zero-dof` already states $3 \le m
  \le D$ alone; callers `isKDof_zero_of_triangle`, `cycle_isProperRigidSubgraph`,
  `pencilPair_of_simple_ncard_eq_three`) and `hne` (`Nonempty α` from `hssub`; callers
  `exists_cut_decomposition_of_not_twoEdgeConnected`, `deficiency_induce_union_singleton`,
  `exists_hasPencilPanelRealization_glue`, `X0Attains.of_bridgePath`, an untyped one pinning `(n :=
  n)` as FRICTION's entry on dropped hypotheses says), with `lem:cut-edge-decomposition` (1)
  restated without $\emptyset \neq V'$.
- **F-281** · L · five declarations of `Molecular/Deficiency.lean` whose proofs use less than a
  hypothesis gives: `Graph.IsTightPartition.subfamily_le`'s `hS2 : 2 ≤ S.ncard` only as
  `S.ncard ≠ 0`; `Graph.IsTightPartition.parts`'s `hD : 2 ≤ bodyBarDim n` only as
  `1 ≤ bodyBarDim n` (they differ at `n = 1`); `Graph.IsTightPartition.eq_of_common_nbr`'s
  `hG : G.Simple` only through `G.Loopless`; `Graph.deficiency_of_single_edge`'s
  `hD : 1 ≤ bodyBarDim n` not at all; and `Graph.deficiency_eq_zero_iff_exists_spanningTrees`'s
  `[DecidableEq β]`, which its statement does not use (hence its `set_option
  linter.unusedDecidableInType false`), only where `classical` would do. The first three nodes
  state Jackson and Jordán's setting (`|Q| ≥ 2`, `D ≥ 2`, `G` simple), so a weaker pin there is
  a form for `fmlnote:tight-partition-consumed-forms` to list, as it lists three.
  *Evidence:* read (the statements and bodies); a `lake lean` witness, copies of the five with the
  hypothesis weakened or dropped (and of their private helpers) that elaborate with the same
  proofs, one line changed in the last two (`have := hG` for `have := hG.toLoopless`, and
  `classical`), each on the three standard axioms (`scratch/reconcile-lean/Hyps-t29-1.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 29.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`): task 38.10 for the `[DecidableEq β]` and
  its `set_option`; task 38.12 drops `deficiency_of_single_edge`'s `hD` (unused; unpinned; callers
  `isMinimalKDof_ncard_le_two_trichotomy`, `hasPencilRealization_of_ncard_le_two`,
  `hasGenericPencilRealization_of_ncard_le_two`). Left (task 38.1): the over-strong `hS2`, `hD` and
  `hG` of the three pins, whose nodes state Jackson and Jordán's setting and whose callers all hold
  the strong form, a change of form only (as `F-273`).
- **F-282** · L · nine hypotheses of seven declarations of `Molecular/Induction/Operations.lean`
  that the others give or the proof does not use, and a repeated derivation:
  `Graph.exists_isProperRigidSubgraph_of_three_le_degree`'s `[DecidableEq β]`, which its statement
  does not use (hence its `set_option linter.unusedDecidableInType false`) and its proof, opening
  with `classical`, does not need; `Graph.cycle_isProperRigidSubgraph`'s `hD : 3 ≤ bodyBarDim n`,
  which `hm : 3 ≤ m` and `hmD : m ≤ bodyBarDim n` give (as for `F-280`'s `isKDof_zero_of_cycle`);
  `Graph.triangle_isProperRigidSubgraph`'s `hab : a ≠ b`, which `hf : G.IsLink f a b` gives in the
  simple `G` (the note after `lem:splitoff-simple` says so); the `hav : a ≠ v` and `hbv : b ≠ v` of
  `Graph.exists_isLink_of_isMinimalKDof_card_three` and `Graph.CycleData.ofCardThree`, which
  `hG_ea` and `hG_eb` give in the simple `G`; and `Graph.induce_insert_splitOff`'s
  `he₀ : e₀ ∉ E(G)` and `Graph.splitOff_isLink_relabel`'s `heac : eₐ ≠ e_c`, which their proofs do
  not use (`lake lint` reports neither). Also `Graph.indep_edgeSet_mulTilde_of_noRigid_of_pos`
  (`lem:edge-set-indep-pos`, `ReducibleVertex.lean`) proves again, by its own circuit argument,
  what `Graph.indep_matroidMG_of_noRigid_of_deficiency_pos` gives with `loopless_of_isMinimalKDof`
  and `G.deficiency n = k`.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: each statement without the
  hypothesis, proved by the lemma with `classical`, `by omega`, `hf.ne` or `hG_ea.ne.symm` for it;
  copies of the last two without `he₀` and `heac` that elaborate with the same proofs; and the pin
  of `lem:edge-set-indep-pos` from the other lemma; all on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t30.lean` and `Hyps-t30-2.lean`, gitignored).
  *Found:* RECONCILE round 3 task 30.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`): task 38.10 for the `[DecidableEq β]` and
  its `set_option`. Task 38.1: task 38.13 drops `cycle_isProperRigidSubgraph`'s `hD`
  (`lem:chain-cycle-dichotomy`), `triangle_isProperRigidSubgraph`'s `hab` (`hf.ne`;
  `lem:splitoff-simple`; callers `splitOff_simple_of_noRigid_of_card`,
  `exists_chain_data_of_noRigid`, `case_II_realization_all_k`), the `hav`, `hbv` of
  `exists_isLink_of_isMinimalKDof_card_three` (`lem:triangle-third-edge`; callers
  `CycleData.ofCardThree`, `hasGenericFullRankRealization_of_triangle`) and of
  `CycleData.ofCardThree` (callers `ofCardThree_m`, `case_III_hsplit_producer_all_k`),
  `induce_insert_splitOff`'s `he₀` (caller `splitOff_isMinimalKDof_of_pos`) and
  `splitOff_isLink_relabel`'s `heac` (`lem:splitOff-isLink-relabel`; callers `ofNormals_relabel`,
  `rigidityRows_ofNormals_relabel`), each node restated where it states the hypothesis. The repeated
  derivation: task 38.6 deletes `indep_matroidMG_of_noRigid_of_deficiency_pos` with its caller
  (block (b) at `abcd9d72`: no orphan), as the pin of `lem:edge-set-indep-pos` gives the node's
  argument (KT's rank count), and re-proving it by the other's fundamental circuit would leave the
  node's proof describing another argument. Round 3: the repeated derivation's part done,
  `indep_matroidMG_of_noRigid_of_deficiency_pos` deleted with its caller (task 38.6).
- **F-283** · L · six hypotheses of six declarations of `Molecular/Induction/` that the proofs do
  not use or the others give: `Graph.splitOff_deficiency_ge`'s `hdeg2`, which its proof does not use
  (`SplitOffDeficiency.lean`; `lake lint` does not report it);
  `Graph.exists_degree_two_removeVertex_of_no_simple_contraction`'s `_hV3`, which its proof does
  not use, and `Graph.deficiency_eq_zero_of_simple_rigid_no_simpleContraction`'s `hV3`, both
  `3 ≤ V(G).ncard`, which `hrig` gives, as a proper rigid subgraph has two vertices and not all of
  `G`'s (`lem:claim-6-6` states it); `Graph.contraction_isMinimalKDof`'s `hVGne : V(G).Nonempty`,
  which `hH` gives; `Graph.rigidContract_deficiency_eq`'s `[DecidableEq β]`, which its statement
  does not use (hence its `set_option linter.unusedDecidableInType false`) and `classical` supplies
  (`Contraction.lean`); and `Graph.not_simple_of_isMinimalKDof_of_ncard_two`'s
  `hG : G.IsMinimalKDof n 0`, used only as `G.IsKDof n 0`, with which its `[DecidableEq β]` goes
  too (`ReducibleVertex.lean`; `lem:theorem-55-base-producer`).
  *Evidence:* read (the statements and bodies); a `lake lean` witness: a copy of the first without
  `hdeg2`, and of the last with `G.IsKDof n 0`, that elaborate with the same proofs (`hG` for
  `hG.1` in the last); the second, third and fourth called with the hypothesis derived from `hrig`
  or `hH`; the fifth with `classical`; all on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t301.lean`, gitignored).
  *Found:* RECONCILE round 3 task 30.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`): task 38.10 for
  `rigidContract_deficiency_eq`'s `[DecidableEq β]` and its `set_option`. Task 38.1: task 38.13
  drops `splitOff_deficiency_ge`'s `hdeg2` (`lem:splitoff-deficiency`; caller `dof_tracking`),
  `exists_degree_two_removeVertex_of_no_simple_contraction`'s `_hV3` and
  `deficiency_eq_zero_of_simple_rigid_no_simpleContraction`'s `hV3` (from `hrig` by a new
  `IsProperRigidSubgraph.three_le_ncard`, beside `IsProperRigidSubgraph.vertexSet_nonempty` in
  `Deficiency.lean`: `2 ≤ |V(H)|` and `V(H) ⊂ V(G)`; `lem:claim-6-6` restated without $|V(G)| \ge
  3$; callers `case_I_realization_h65_gen`, `case_I_hcontract_gen`) and
  `contraction_isMinimalKDof`'s `hVGne` (from `hH`; caller `rigidContract_isMinimalKDof`;
  `lem:contraction-minimality`, `lem:reduction-step`), and weakens
  `not_simple_of_isMinimalKDof_of_ncard_two`'s `hG` to `G.IsKDof n 0`, its `[DecidableEq β]` going
  with it (caller `theorem_55_base_producer_gen` passes `hG.1`).
- **F-284** · L · three hypotheses of `Molecular/Induction/ForestSurgery/ChainExtraction.lean` that
  the proofs use less of than they give, or that the others give: `Graph.chainWalk_charging`'s
  `[G.Simple]`, used only through `G.Loopless`, with which
  `Graph.chainWalk_terminated_contradiction` would use its `hV3 : 3 ≤ V(G).ncard` only as
  `2 ≤ V(G).ncard` (the simplicity it derives from `hV3` is for that call);
  `Graph.exists_cyclic_data_of_closed_path`'s `h2 : 2 ≤ P.length`, used only as `1 ≤ P.length`; and
  `Graph.chainWalk_isPrefix_of_terminated`'s `hTlen1 : 1 ≤ T.length`, which `hfe` gives (`T` is
  nonempty). The four declarations are unpinned steps of `lem:chain-cycle-dichotomy`, whose pin
  needs its three vertices for `chainWalk_trichotomy`.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: copies of the first with
  `[G.Loopless]`, of `chainWalk_terminated_contradiction` with `2 ≤ V(G).ncard` calling it, and of
  the second with `1 ≤ P.length`, that elaborate with the same proofs (the line deriving `G.Simple`
  removed from the copy of `chainWalk_terminated_contradiction`), and the third called with
  `hneT.length_pos` from `hfe`; all on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t31.lean`, gitignored).
  *Found:* RECONCILE round 3 task 31.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.14). Task 38.1: weaken
  `chainWalk_charging`'s `[G.Simple]` to `[G.Loopless]` and `chainWalk_terminated_contradiction`'s
  `hV3` to `2 ≤ V(G).ncard`, the line deriving `G.Simple` removed (caller
  `chainData_or_cycleData_of_noRigid`), and drop `chainWalk_isPrefix_of_terminated`'s `hTlen1`
  (`hneT.length_pos` from `hfe`; caller `chainWalk_charging`); all unpinned. Left:
  `exists_cyclic_data_of_closed_path`'s `h2`, as its callers hold `2 ≤ P.length` and no step goes (a
  change of form only).
- **F-285** · L · three hypotheses of `Molecular/Induction/ForestSurgery/Reduction.lean` that the
  statements or the proofs do not use, or use less of than they give: `Graph.pencil_reduction`'s
  `[DecidableEq β]`, which its statement does not use (hence its
  `set_option linter.unusedDecidableInType false`, whose comment called the report a false positive)
  and `classical` supplies (`thm:pencil-reduction`); `Graph.exists_degree_eq_two_of_noRigid`'s
  `hV3 : 3 ≤ V(G).ncard`, used only as `2 ≤ V(G).ncard` (its one caller is Case III's
  `case_III_hsplit_producer_all_k`); and the private `Graph.vfiber_inc_iff`'s
  `_hpE : p ∈ E(G.mulTilde n)`, which its proof does not use.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the first stated without the
  instance and proved by the theorem under `classical`, and copies of the second with
  `2 ≤ V(G).ncard` (the line deriving it from `hV3` removed) and of the third without `_hpE` that
  elaborate with the same proofs, on at most the three standard axioms
  (`scratch/reconcile-lean/Hyps-t311.lean`, gitignored).
  *Found:* RECONCILE round 3 task 31.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`): task 38.10 for the `[DecidableEq β]` and
  its `set_option`. Task 38.1: task 38.14 weakens `exists_degree_eq_two_of_noRigid`'s `hV3` to `2 ≤
  V(G).ncard`, its line deriving that removed (caller `case_III_hsplit_producer_all_k`), and drops
  the private `vfiber_inc_iff`'s `_hpE` (caller `exists_balanced_forest_packing`).
- **F-286** · L · hypotheses of `Molecular/RigidityMatrix/Bricks.lean` that the proofs do not use,
  or use less of than the statements give. `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`
  (`lem:block-rank-cut`): its `_hE₁` (every other link inside `V₁` or outside it), which the proof
  does not use; its `[Finite β]`, used only by the proof's `have : Fintype β`, which nothing after
  it uses; and its `hC_ext`, used only at the edge of `C`. With these gone,
  `add_le_finrank_span_rigidityRows_induce_union_singleton` (the same node's second claim) needs
  neither its `honly` (`e₀` the only edge from `V₁` to `w₀`) nor its `[Finite β]`, and its `hext`
  only at `e₀`. `le_finrank_span_rigidityRows_of_splice`'s `[Finite β]`, as for the first (its
  `[Finite α]` is needed). And the `hoverlap : V₁ ∩ V₂ = {u, v}` of
  `inf_span_rigidityRows_of_vertexTwoCut` and `finrank_span_rigidityRows_vertexTwoCut_eq`
  (`cor:block-rank-vertex-two-cut`), used only as `V₁ ∩ V₂ ⊆ {u, v}`. The comments above the
  `@[nolint unusedArguments]` of the first and the third called `[Finite β]` a false positive that
  the proof needs to elaborate; copies of the two as they stand, linted
  (`#lint only unusedArguments`) without the attribute in a non-`module` file, are not reported.
  The nodes state the hypotheses (`lem:block-rank-cut`'s set of crossing edges and its "exactly one
  edge", `cor:block-rank-vertex-two-cut`'s equality), so a change restates them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: copies of the first without
  `_hE₁` and `[Finite β]`, then with `hC_ext` asked only at the edges of `C`; of the second from it,
  without `honly` and `[Finite β]` and with `ext e₀ ≠ 0`; of the third without `[Finite β]`; and of
  the last two with `⊆`; each with the same proof (one line changed in the first, the discharge of
  `_hE₁` removed from the second, a `.le` from the last two), on the three standard axioms; a copy
  of the third without `[Finite α]` as well fails (`scratch/reconcile-lean/Hyps-t32.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 32.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.15). Task 38's suppression screen
  agrees: a copy of the file without the two `@[nolint unusedArguments]` lints clean, and one
  without the two `[Finite β]` and their `have : Fintype β` elaborates, the linter then reporting
  the `[Finite β]` of `add_le_finrank_span_rigidityRows_induce_union_singleton`
  (`scratch/reconcile-lean/t38/BricksCopy.lean`, `BricksNoBeta.lean`, gitignored). Task 38.1: drop
  `le_finrank_span_rigidityRows_of_cut`'s `_hE₁` and `[Finite β]` (with its `have : Fintype β`, the
  `@[nolint unusedArguments]` and its comment; callers
  `add_le_finrank_span_rigidityRows_induce_union_singleton`, `le_finrank_span_rigidityRows_path`,
  `finrank_span_rigidityRows_cutEdge_eq`, `X0Attains.of_bridgePath`), the second's `honly` and
  `[Finite β]` (the discharge of `_hE₁` removed; caller
  `add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`), and
  `le_finrank_span_rigidityRows_of_splice`'s `[Finite β]` with its `nolint` and comment (callers
  `case_I_realization_nonsimple_gen`, `hasPencilRealization_of_not_simple`); `lem:block-rank-cut`
  restated (the crossing edges, "exactly one edge"); `notes/ToolchainBumps.md`'s count of `nolint`
  sites. Left: `hC_ext`, `hext` at every edge of `C`, and `hoverlap`'s equality, which the nodes
  state and every caller holds (a change of form only).
- **F-287** · L · hypotheses of `Molecular/Meet.lean` that the statements need not take, and a
  lemma's place. `meet`'s `ha : a ≤ k + 2` and `hb : b ≤ k + 2`, which `hab : a + b ≤ k + 2` gives
  (`def:meet` states `a + b ≤ d + 1` alone). `extensor_join_proportional_complementIso_meet`'s
  `hp : LinearIndependent K p` (`lem:meet-two-hyperplanes`, the second statement): for a dependent
  `p` the join is `0`, and `c = 0` serves; without it,
  `exists_line_data_of_homogeneousIncidence_gen` (`RigidityMatrix/Claim612.lean`) needs neither its
  `hpbar` nor its conclusion's `LinearIndependent K p`, which serve only `hp` (through
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`).
  `exists_smul_extensor_eq_of_mem_span_range`'s `hv : LinearIndependent K v`: for a dependent `v`
  the span has dimension at most `1`, so `u` is dependent, and `c = 0` serves. The node states `hp`,
  so dropping it restates the node. And `mem_hingeRowBlock_iff` (`def:hinge-row-block`) is in
  `RigidityMatrix/Claim612.lean`, apart from `hingeRowBlock` in `Basic.lean`, which `Claim612.lean`
  imports (`CombinatorialRigidity/CLAUDE.md`: a lemma goes in the file of its definition).
  *Evidence:* read (the statements and bodies); a `lake lean` witness: a copy of `meet` without `ha`
  and `hb`, equal to `meet` by `rfl`; copies of the other two without `hp` and `hv`, which call the
  lemmas when the family is independent and take `c = 0` otherwise; all on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t321.lean`, gitignored).
  *Found:* RECONCILE round 3 task 32.1.
  *Disposition:* done (task 38.5). Task 38.1: drop `meet`'s `ha`,
  `hb` (`def:meet` states $a + b \le d + 1$ alone; no caller), and move `mem_hingeRowBlock_iff` to
  `RigidityMatrix/Basic.lean` beside `hingeRowBlock` (its pin and callers unchanged). Left: `hp` and
  `hv`, each true without but only by a new degenerate case ($c = 0$) in a proof whose callers all
  hold the independence; `lem:meet-two-hyperplanes` states `hp`. Round 3: done so, `meet` now taking
  `hab` alone (task 38.5).
- **F-288** · L · hypotheses of `Molecular/RigidityMatrix/Concrete.lean` that the statements need
  not take, moot if task 38 removes the file (`F-279`). `hbot1 : ∀ i, v ≠ x ∨ x = v`, which is
  excluded middle, is a hypothesis of seven declarations
  (`submatrix_columnOp_toBlocks₂₂_eq_mixedBottom` and `_eq_Gab`,
  `rank_columnOp_toBlocks₂₂_eq_finrank_span_mixedBottom` and `_Gab`,
  `linearIndependent_toBlocks₂₂_row_mixedBottom_of_finrank_eq` and `_row_Gab_of_finrank_eq`, and
  `submatrix_columnOp_toBlocks₁₂_eq_mul_toBlocks₂₂`) and a conjunct of the conclusions of
  `bottom_selection_of_crossFramework_span` and `_Gab`. `edgeRowSplit_corner_card`'s `[Finite β]`
  carries `@[nolint unusedArguments]` and a comment that the proof needs it to elaborate; it does
  not.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: `edgeRowSplit_corner_card`
  without `[Finite β]` and without the proof's two `have`s, by `simp` alone, and `hbot1`'s statement
  by `eq_or_ne`, on the three standard axioms (`scratch/reconcile-lean/Hyps-t322.lean`, gitignored).
  *Found:* RECONCILE round 3 task 32.2.
  *Disposition:* done (task 38.5): moot, `Concrete.lean` deleted whole (`F-279`), these declarations
  with it.
- **F-289** · L · hypotheses of `Molecular/AlgebraicInduction/Pinning.lean` and `PanelLayer.lean`
  that the proofs do not use or the others give, and a repeated derivation. `theorem_55_base`'s
  `huv : u ≠ v` (`lem:theorem-55-base`) and `theorem_55_triangle`'s `huv`, `hvw` and `huw`
  (`lem:theorem-55-triangle`), which the proofs do not use; the nodes state the distinctness, so
  dropping them restates the nodes. `exists_independent_pinned_two_edge_span_full`'s `hne_a` and
  `hne_b`, which `hgen` gives (`LinearIndependent.ne_zero`);
  `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`'s
  `hr : r ∈ V(G)`, which `hinter : V(G) ∩ t = {r}` gives;
  `normalsJoin_pair_linearIndependent_of_triLI`'s `hLI_va` and `hLI_ab`, which `htriLI` gives
  (`triLI_subpairs`); and the `[Nonempty α]` of `screwDim_add_finrank_pinnedMotionsOn_le`
  (`lem:pinned-motions-on-rank-bound`) and of `rankHypothesis_iff_finrank_pinnedMotionsOn`
  (`lem:case-I`), which `hs : s.Nonempty` gives. `lake lint` reports none of them. And
  `Graph.ChainData.d_eq_kAdd` (`CaseIII/Realization.lean`) and the step `hnk` of `cycle_realization`
  (`CaseIII/Arms.lean`) derive again, line for line, `Graph.eq_add_one_of_bodyBarDim_eq_screwDim`,
  L8's repeated derivation; the two are in the footprint, whose code changes are this round's.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: copies of `theorem_55_base`
  and `theorem_55_triangle` without those hypotheses and with the same proofs, the others called
  with the hypothesis derived (`hgen.ne_zero`, `hinter`, `triLI_subpairs`, `⟨hs.some⟩`), and the
  arithmetic by `Graph.eq_add_one_of_bodyBarDim_eq_screwDim`, on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t33.lean`, gitignored).
  *Found:* RECONCILE round 3 task 33.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.4 and 38.17). Task 38.1: task
  38.4 drops `theorem_55_base`'s `huv` and `theorem_55_triangle`'s `huv`, `hvw`, `huw` (unused;
  `lem:theorem-55-base` and `lem:theorem-55-triangle` restated without the distinctness; callers:
  the first's five, `toBodyHinge_rankHypothesis_zero`, `theorem_55_base_producer_parallel_pair_gen`,
  `case_I_realization_nonsimple_gen`, `hasPencilRealization_of_ncard_le_two`,
  `hasPencilRealization_of_not_simple`, the second's `hasGenericFullRankRealization_of_triangle`),
  `exists_independent_pinned_two_edge_span_full`'s `hne_a`, `hne_b` (`hgen.ne_zero`; caller
  `case_I_realization_h65_gen`), `normalsJoin_pair_linearIndependent_of_triLI`'s `hLI_va`, `hLI_ab`
  (`triLI_subpairs`; caller `case_I_h65_extensor_pair_LI`), and the `[Nonempty α]` of
  `screwDim_add_finrank_pinnedMotionsOn_le` and `rankHypothesis_iff_finrank_pinnedMotionsOn`
  (`⟨hs.some⟩`; no node states an instance). Moot: `hr`, as task 38.3 deletes its lemma (`F-291`).
  Task 38.17: `ChainData.d_eq_kAdd` and `cycle_realization`'s `hnk` by
  `Graph.eq_add_one_of_bodyBarDim_eq_screwDim`. Round 3: task 38.4's part done, with the binders
  it left unused, `toBodyHinge_rankHypothesis_zero`'s `huv` and
  `toBodyHinge_rankHypothesis_iff_finrank_pinnedMotionsOn`'s `[Nonempty α]`;
  `lem:theorem-55-base`, `lem:theorem-55-triangle` and `lem:cycle-realization-base` restated without
  the distinctness (task 38.4).
- **F-290** · L · hypotheses of `Molecular/AlgebraicInduction/CaseI.lean` and `CaseII.lean` that the
  proofs do not use or the others give. `case_II_placement_eq612`'s `_hG_ea : G.IsLink e_a v a`,
  which its proof does not use (the dead pin of `lem:case-II-realization-placement`, S3's node,
  `F-150`); `rigidContract_exterior_rank_transport_htransport`'s
  `hne : V(G.rigidContract H r).Nonempty` (`lem:claim-6-4`), which `hr` and `hHsub` give, as `r` is
  a vertex of the contraction; the `hnesH : sH.Nonempty` of
  `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set` and of its `_kdof` form,
  which `hcH : c ∈ sH` gives; and `case_I_realization`'s `hVH2 : 2 ≤ V(H).ncard`, the second
  conjunct of `hH` (`F-271`'s declaration). `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: a copy of
  `case_II_placement_eq612` without `_hG_ea` and with the same proof, on the three standard axioms,
  and the others called or met with the hypothesis derived (`⟨r, …⟩` through
  `Graph.vertexSet_rigidContract`, `⟨c, hcH⟩`, `hH.2.1`) (`scratch/reconcile-lean/Hyps-t34.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 34.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.3 and 38.16). Task 38.1: task
  38.3 drops `rigidContract_exterior_rank_transport_htransport`'s `hne` (from `hr`, `hHsub`:
  `vertexSet_rigidContract`; `lem:claim-6-4` does not state it; a dead pin once task 38.3 deletes
  `case_I_realization`) and
  `hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`'s `hnesH` (`⟨c,
  hcH⟩`; caller `case_I_realization_all_k_gen`); task 38.16 drops `case_II_placement_eq612`'s
  `_hG_ea` (a dead pin with no caller; `lem:case-II-realization-placement` does not state it). Moot:
  the other `hnesH` and `case_I_realization`'s `hVH2` (task 38.3 deletes both). Round 3: `hne`
  and `hnesH` dropped, derived where they were used (task 38.3).
- **F-291** · L · repeated derivations and a derivable hypothesis in
  `Molecular/AlgebraicInduction/Coupling.lean` and `GenericityDevice.lean`. The rigid forms
  `infinitesimalMotions_sup_range_extProj_eq_top` and
  `BodyHingeFramework.injOn_extProj_dualMap_rigidityRows` state with `hrig` and `hr` what the pinned
  `_of_inter_eq_singleton` forms (`lem:extProj-preserves-rank-of-inter`) state without them, by a
  count of dimensions; their one user,
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` (which only `lem:claim-6-4`'s
  pin uses), could call the pinned `injOn` form, leaving the two and
  `infinitesimalMotions_inf_range_extProj_eq_pinnedMotionsOn` without a caller, and its
  `hnev : F.graph.vertexSet.Nonempty` is `⟨r, hr⟩`. In `GenericityDevice.lean`, the coordinatization
  of the rows (the basis `B`, `φ`, `g`, `c` and `hg`, some thirty lines) is written out in
  `exists_good_realization_ofParam` and in each of the four `exists_rankPolynomial_of_…` lemmas;
  rank–nullity, `finrank_span_rigidityRows_add_finrank_infinitesimalMotions`, is derived again
  inline in `finrank_span_rigidityRows_of_rigidOn`,
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set` and the three
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero…` lemmas; and the single-body pin of
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` is derived again in
  `finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn`. `lake lint` reports none.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the two rigid forms from the
  pinned ones, and a copy of the projected extraction without `hnev`, through the pinned `injOn`
  form, on the three standard axioms (`scratch/reconcile-lean/Hyps-t341.lean`, gitignored).
  *Found:* RECONCILE round 3 task 34.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.3 and 38.16). Task 38.1: task
  38.3 has `exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj` call the pinned
  `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`, without `hnev` (`⟨r, hr⟩`), adds that
  node to `lem:claim-6-4`'s proof `\uses` (the pin's new reach, backward), and deletes (gate 4)
  `injOn_extProj_dualMap_rigidityRows`, `infinitesimalMotions_sup_range_extProj_eq_top`,
  `infinitesimalMotions_inf_range_extProj_eq_pinnedMotionsOn`,
  `finrank_pinnedMotionsOn_of_isInfinitesimallyRigidOn_vertexSet_inter_eq_singleton`
  (`Pinning.lean`) and the orphans `finrank_pinnedMotionsOn_of_vertexSet_subset` and
  `pinnedMotionsOn_eq_iInf_ker_proj_of_vertexSet_subset` (block (b) at `abcd9d72`, all unpinned and
  dead). Task 38.16, `GenericityDevice.lean`: one lemma for the coordinatization of the rows
  (independent panel rows of `ofNormals G ends q₀` on `s` give a polynomial `Q` with `eval q₀ Q ≠
  0`, off whose zeros they stay independent: the basis `B`, `e`, `φ`, `g`, `c`, `hg` and
  `exists_polynomial_ne_zero_of_linearIndependent_at`, ~45 lines), called by the three
  `exists_rankPolynomial_of_…` lemmas task 38.3 leaves, and by `exists_good_realization_ofParam` if
  its coordinates are the lemma's at `ofParam`'s normals;
  `finrank_span_rigidityRows_add_finrank_infinitesimalMotions` moved above and called in
  `finrank_span_rigidityRows_of_rigidOn` and
  `exists_independent_panelRow_subfamily_of_rigidOn_linking_set`;
  `finrank_infinitesimalMotions_le_of_isInfinitesimallyRigidOn` through
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`. No statement changes.
  Round 3: the projected extraction calls the pinned `injOn` form, without `hnev`;
  `lem:claim-6-4`'s proof `\uses` `lem:extProj-preserves-rank-of-inter`; the six deleted, block
  (b) at `a1c4fe3a` finding them blocked only through that extraction (task 38.3). Its `hr` is
  now derivable (`F-325`).
- **F-292** · L · unused hypotheses and repeated derivations in
  `Molecular/AlgebraicInduction/CaseIII/Arms.lean` and `Candidate.lean`.
  `case_III_hsplit_producer_all_k` takes `_hk1 : 1 ≤ k`, which its proof does not use (its one
  caller, `case_III_realization_all_k`, passes `hk1`); `case_III_old_new_blocks` (`F-268`'s) takes
  `_hG_eb` and `_hG_ea`, which its proof does not use. `case_III_realization_of_rank`'s `hGv_off`
  is `case_III_rank_certification`'s `hGv_ne`, proof for proof (an edge of `Gv` is neither `e_a`
  nor `e_b`). `cycle_realization` derives `n = k + 1` from `bodyBarDim n = screwDim k` inline
  (`hnk`), as `Graph.ChainData.d_eq_kAdd` (`CaseIII/Realization.lean`, which `Arms.lean` does not
  import) does for a chain's length; a lemma on `n` alone would serve both.
  *Evidence:* read (the statements and bodies).
  *Found:* RECONCILE round 3 task 35.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.17). Task 38.1: drop
  `case_III_hsplit_producer_all_k`'s `_hk1` (caller `case_III_realization_all_k`); `hnk` by
  `Graph.eq_add_one_of_bodyBarDim_eq_screwDim` (`F-289`); one lemma for `hGv_off` (no link of `G −
  v` is a link at `v`, so neither `e_a` nor `e_b`; ~12 lines at each of eight sites, `Arms.lean`,
  `Candidate.lean`'s `hGv_ne` and six in `Realization.lean`, less those task 38.2 deletes), with the
  project's `removeVertex` lemmas. Moot: `case_III_old_new_blocks`'s two (task 38.2).
- **F-293** · L · an unused hypothesis, derivable ones and repeated derivations in
  `Molecular/AlgebraicInduction/CaseIII/Realization.lean`. `chainData_dispatch_floor_of_discriminator`
  takes `_hρ₀ne : ρ₀ ≠ 0`, which its proof does not use. `case_III_realization_all_k`'s
  `hD : 3 ≤ bodyBarDim n` follows from `hk1` and `hn` (`three_le_screwDim`), as
  `exists_nested_rankPolynomial_lower_all_k` derives it; the `hd2 : 2 ≤ cd.d` of
  `chainData_fire_discriminator` and `chainData_dispatch` follows from `hk1`, `hn` and
  `Graph.ChainData.d_eq_kAdd`, though the `by omega` proofs of the vertex indices in the types of
  their hypotheses read it; and `chainData_dispatch`'s `hdef` is `hG.1`, as its one caller passes
  it. The rigidity of `ofNormals Gab Q.ends q` from the rank polynomial and the deficiency bound,
  with the orientation of the form and the rows at `(a, b)`, is written out in both
  `case_III_candidate_dispatch` and `chainData_split_w6b_gates` (some 120 lines in each); the links,
  distinctness and edges of the split at `v₁` in `chainData_fire_discriminator`,
  `chainData_dispatch_interior_of_discriminator` and `chainData_dispatch_floor_of_discriminator`; and
  `hGv_off` (no link of `G − v` is `e_a` or `e_b`) in five proofs. `lake lint` reports none.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: `case_III_realization_all_k`
  called with `hn ▸ three_le_screwDim hk1` for `hD`, and `2 ≤ cd.d` from `cd.d_eq_kAdd hn` and `hk1`
  by `omega`, on the three standard axioms (`scratch/reconcile-lean/Hyps-t351.lean`, gitignored).
  *Found:* RECONCILE round 3 task 35.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.17). Task 38.1: drop
  `chainData_dispatch_floor_of_discriminator`'s `_hρ₀ne` (caller `chainData_dispatch`) and
  `chainData_dispatch`'s `hdef` (`hG.1`; `lem:case-III-chain-dispatch`; caller
  `case_III_realization_all_k`); one lemma on `Graph.ChainData` at `2 ≤ cd.d` for the split at `vtx
  1` (`hlea`, `hleb`, the distinctness `hav`, `hbv`, `hba`, `heab`, and `hclv`, ~30 lines written
  out in `chainData_fire_discriminator` and `chainData_dispatch_floor_of_discriminator`, with
  `ChainData.link`, `vtx_ne`, `edge_inj`, `deg_two_split`), at every site that writes it out;
  `hGv_off` by `F-292`'s lemma. Left: `case_III_realization_all_k`'s `hD`, on the main result's
  chain (`F-324`); `hd2`, which the `by omega` index proofs in the types of later hypotheses read;
  and the ~120-line rigidity block of `case_III_candidate_dispatch` and `chainData_split_w6b_gates`,
  which threads the split's normals, selector, form and rows (§C's calibration, the S4b trap).
- **F-294** · L · derivable hypotheses and repeated derivations in
  `Molecular/AlgebraicInduction/CaseIII/Relabel/Basic.lean` and `Arm.lean`.
  `BodyHingeFramework.funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` takes `hdeg2r`, which
  `hdeg2` gives by `Graph.IsLink.symm`, as `case_III_arm_realization_M3` and
  `Graph.ChainData.seedAdvance_wstep_hstep` derive it; the fourth conjunct of each step that
  `wstep_foldl_mem_span_rigidityRows` and `wstep_foldr_mem_span_rigidityRows` take follows from the
  third in the same way. `case_III_arm_realization_M3` takes `hV3 : 3 ≤ V(G).ncard`, which the
  distinct ends `v`, `a` and `b` of `hG_ea` and `hG_eb` give under `[Finite α]`. The pins
  `ofNormals_relabel` and `rigidityRows_ofNormals_relabel` write out the same derivations (the
  involutions `ρ ∘ ρ` and `σ ∘ σ`, three inequalities of labels and the hinges at `f` and `σ f`),
  and the first's proof is that of `ofNormals_relabel_perm` (`F-279`'s) at the transposition; the
  `htrans` of `case_III_arm_realization_M3` and that of `seedAdvance_wstep_hstep` are one argument
  (a link that does not meet `a` survives with its hinge, as the transposition fixes its ends) in
  two forms. `lake lint` reports none.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the move called with
  `fun f x h => hdeg2 f x h.symm` for `hdeg2r`, and `3 ≤ V(G).ncard` from the three distinct ends,
  on the three standard axioms (`scratch/reconcile-lean/Hyps-t352.lean`, gitignored).
  *Found:* RECONCILE round 3 task 35.2.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.18). Task 38.1: drop
  `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`'s `hdeg2r` (`fun f x h => hdeg2 f x h.symm`;
  callers `wstep_foldl_mem_span_rigidityRows`, `case_III_arm_realization_M3` and those task 38.2
  leaves), the fourth conjunct of `wstep_foldl_mem_span_rigidityRows`'s step (caller
  `shiftBodyListAsc_foldl_mem_span_rigidityRows`), and `case_III_arm_realization_M3`'s `hV3` (from
  the distinct ends of `hG_ea`, `hG_eb`; caller `case_III_candidate_dispatch`); all unpinned. Moot:
  `wstep_foldr_mem_span_rigidityRows` and `ofNormals_relabel_perm` (task 38.2). Left: the pins'
  written-out derivations, which the deleted perm form would have served, and `htrans`'s two forms
  (one argument, two statements).
- **F-295** · L · derivable hypotheses and repeated derivations in
  `Molecular/AlgebraicInduction/CaseIII/Relabel/Chain.lean`, `ChainColumn.lean` and
  `ForkedArm.lean`. `BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows`,
  `hingeRow_acolumn_mem_span_rigidityRows` and `acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows`
  take `hdeg2r`, which `hdeg2` gives by `Graph.IsLink.symm` (`F-294`'s form). The `h3 : 3 ≤ cd.d` of
  `Graph.ChainData.baseRedundancy_perp_interior_reproduced_panel`, `interior_hρe₀_of_widening` and
  the pins `interior_hρe₀_of_baseWidening` and `chainData_relabel_arm_hρGv` follows from
  `i : Fin cd.d` and `h2i : 2 ≤ i`, and that of `chainData_freshEdge_perp_of_baseRedundancy` from
  `h2s` and `hsd`, though the `by omega` proofs in the types of later hypotheses read it.
  `interior_group_eq_baseRedundancy`, `interior_group_acolumn_eq_neg_baseRedundancy` and
  `funLeft_dualMap_interior_group_acolumn_eq_neg_baseRedundancy` take variables `ab₁` and `ab₂` with
  `hab₁ : ab₁ = vtx 0` and `hab₂ : ab₂ = vtx 2`, which the two callers outside the three pass as
  `rfl`. The restriction to an interior vertex by edges (`hinc_ei`, `hinc_ep`, `hdeg`) is written
  out in both `interiorGroup_acolumn_adjacency` and `interiorGroup_acolumn_two_group_decomp`; the
  step from `−ρ₀` in a block of rows to `ρ₀` vanishing on its hinge, in both
  `baseRedundancy_perp_interior_reproduced_panel` and `chainData_freshEdge_perp_of_baseRedundancy`;
  and the case split on the order of the ends a selector gives (the hinge changes sign) in
  `baseRedundancy_perp_interior_reproduced_panel`, `chainData_bottom_relabel`, three times in
  `case_III_bottom_relabel` and four times in `chainData_freshEdge_slot_perp_ends₀`, where the
  private `perp_panelSupportExtensor_swap` restates `panelSupportExtensor_swap` with `map_neg`.
  `lake lint` reports none.
  *Evidence:* read (the statements and bodies; the callers of the three lemmas with `ab₁` and
  `ab₂`); a `lake lean` witness: `acolumn_mem_hingeRowBlock_of_span_rigidityRows` and its sum form
  called with `fun f x h => hdeg2 f x h.symm` for `hdeg2r`, and `interior_hρe₀_of_baseWidening`
  called with `3 ≤ cd.d` from `i.isLt` and `h2i`, on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t353.lean`, gitignored).
  *Found:* RECONCILE round 3 task 35.3.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.18). Task 38.1: drop
  `acolumn_mem_hingeRowBlock_of_span_rigidityRows`'s `hdeg2r` (the other two go in task 38.2), and
  the variables `ab₁`, `ab₂` with `hab₁`, `hab₂` of `interior_group_eq_baseRedundancy` and
  `interior_group_acolumn_eq_neg_baseRedundancy` (`vtx 0`, `vtx 2` in their place; callers
  `baseRedundancy_perp_interior_reproduced_panel`, `chainData_freshEdge_perp_of_baseRedundancy`);
  the private `perp_panelSupportExtensor_swap` replaced by `panelSupportExtensor_swap` with
  `map_neg`. Left: `h3`, which the `by omega` index proofs in the types of later hypotheses read;
  the case split on a selector's order, one per site; the step from `−ρ₀` (two statements). Moot:
  `interiorGroup_acolumn_two_group_decomp` (task 38.2).
- **F-296** · L · repeated derivations in `Molecular/AlgebraicInduction/PanelHinge.lean`.
  `momentCurve_pair_linearIndependent` proves again, for two points of the moment curve, the
  argument of `pair_linearIndependent_of_leading_minor_ne_zero`, whose minor there is `t − s`; and
  `isGeneralPosition_withMomentNormals` and `isGeneralPosition_ofParam` have one proof, as
  `P.withMomentNormals param` has the normals of `ofParam P.graph P.ends param`. `lake lint` reports
  none.
  *Evidence:* read (the bodies); a `lake lean` witness: `momentCurve_pair_linearIndependent` from
  `pair_linearIndependent_of_leading_minor_ne_zero`, and `isGeneralPosition_withMomentNormals` from
  `isGeneralPosition_ofParam`, on the three standard axioms (`scratch/reconcile-lean/Hyps-t36.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 36.
  *Disposition:* done (task 38.4). Task 38.1: `momentCurve_pair_linearIndependent` by
  `pair_linearIndependent_of_leading_minor_ne_zero` (its minor `t − s`) and
  `isGeneralPosition_withMomentNormals` by `isGeneralPosition_ofParam`, each tool moved above its
  user; no statement changes (`lem:moment-curve-general-position` pins both forms). Done so, the
  leading-minor lemma moved up and `isGeneralPosition_withMomentNormals` down.
- **F-297** · L · hypotheses the others give, and repeated derivations, in the first half of
  `Molecular/AlgebraicInduction/Theorem55.lean`. `theorem_55_base_producer_gen`'s
  `hD : 2 ≤ bodyBarDim n` (`lem:theorem-55-base-producer`) follows from `hk` and `hn`
  (`two_le_screwDim`); `case_I_realization_h65_gen`'s `hD : 3 ≤ bodyBarDim n` from `hk` and `hn`
  (`three_le_screwDim`), and its `hV3 : 3 ≤ V(G).ncard` from `hrig`, as a proper rigid subgraph has
  at least two vertices, not all of `V(G)` (`lem:case-I-realization-h65`); the `hLI_va` and `hLI_ab`
  of the private `case_I_h65_extensor_pair_LI` from `htriLI` (`triLI_subpairs`, as `F-289`'s for
  `normalsJoin_pair_linearIndependent_of_triLI`). `finrank_span_rigidityRows_cutEdge_eq` uses its
  `hD` only for `1 ≤ screwDim k`, which `one_le_screwDim` gives, and the two cut lemmas
  (`lem:case-cut-edge-realization`, `-gp`) use theirs only to pass it on; its `hFcut` follows from
  `hFgraph`, as its callers' short proofs of it show. The rank of the rows of the one edge is
  derived twice, in `theorem_55_base_producer_single_edge_gen` and `_single_edge_gp_gen` (the
  selector, the range of rows and `finrank_span_panelRow_edge`, some 30 lines each), and
  `case_cut_edge_realization_gp_gen` writes out the same steps for each side of the cut (the
  selector `G.endsOf`, the motions, the rank and the rank polynomial, some 60 lines each).
  `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the two pins called with `hD`
  (and `hV3`) derived, `htriLI`'s two pairs by `triLI_subpairs`, a copy of
  `finrank_span_rigidityRows_cutEdge_eq` without `hD` and with the same proof but
  `one_le_screwDim`, and `hFcut` from `hFgraph`, on the three standard axioms
  (`scratch/reconcile-lean/Hyps-t361.lean`, gitignored).
  *Found:* RECONCILE round 3 task 36.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.19). Task 38.1: drop
  `case_I_realization_h65_gen`'s `hV3` (`IsProperRigidSubgraph.three_le_ncard`, task 38.13;
  `lem:case-I-realization-h65` restated where it states it; caller `case_I_dispatch_gen`), the
  private `case_I_h65_extensor_pair_LI`'s `hLI_va`, `hLI_ab` (`triLI_subpairs`), and
  `finrank_span_rigidityRows_cutEdge_eq`'s `hFcut` (from `hFgraph`; its three callers' proofs of it
  go). Left: the `hD` of `theorem_55_base_producer_gen`, `case_I_realization_h65_gen`,
  `finrank_span_rigidityRows_cutEdge_eq` and the two cut lemmas, on the main result's chain
  (`F-324`); the one-edge rank in the two single-edge producers (~30 lines in two statements), and
  the two sides of `case_cut_edge_realization_gp_gen` (one proof). Round 3:
  `case_I_h65_extensor_pair_LI`'s `hLI_va` and `hLI_ab` dropped, which `F-289`'s change left
  unused, and with them the steps `hne_a` and `hne_b` of `case_I_realization_h65_gen`'s proof
  (task 38.4).
- **F-298** · L · hypotheses the others give, repeated derivations and four needless `set_option`s,
  in the second half of `Molecular/AlgebraicInduction/Theorem55.lean`.
  `case_I_realization_nonsimple_gen`'s `hD : 2 ≤ bodyBarDim n` (`lem:case-I-realization-nonsimple`)
  follows from `hk` and `hn` (`two_le_screwDim`); the `hD : 3 ≤ bodyBarDim n` of
  `case_I_dispatch_gen` and `case_I_hcontract_gen` (`lem:case-I-dispatch`, `lem:case-I-all-k`), of
  `theorem_55_minimalKDof_k_all_k`, of the four KT Theorem 5.6 forms that take `hk1` and of
  `theorem_55_6_multigraph_of_two_le` and `theorem_55_6_multigraph` from `hk1` (or `hk`) and `hn`
  (`three_le_screwDim`), and the two Case I lemmas' `hV3` from `hrig`, as for `F-297`'s
  `case_I_realization_h65_gen`; `theorem_55_minimalKDof_k`'s `hD` from `hn` alone
  (`screwDim 2 = 6`). `theorem_55_minimalKDof_gen` has the same `hD`, but it is a main result, whose
  statement stays. `case_I_hcontract_gen`'s case `c ≠ 0` repeats the case split of
  `case_I_dispatch_gen` (some 20 lines); `rankHypothesis_genuine_of_theorem_55_gen`,
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` and
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen` repeat the strip, the
  realization of the spanning subgraph, the re-aimed selector and its nonzero hinges (some 50 lines
  each); `rankHypothesis_of_theorem_55_gen` and `theorem_55_6_multigraph` derive `def(G̃) = 0` on one
  body the same way (some 20 lines each), and `molecular_conjecture` and
  `molecular_conjecture_multigraph` derive it the same way from a rigid realization with nonzero
  hinges. The `set_option linter.unusedDecidableInType false in` of
  `rankHypothesis_genuine_of_theorem_55_gen`, `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`,
  `theorem_55_6_multigraph_of_two_le` and `theorem_55_6_multigraph` is not needed, as their types
  use `[DecidableEq β]` through `hfresh` (`IsMinimalKDof`), and the docstring sentences that justify
  it go with it. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the three Case I pins and
  `theorem_55_minimalKDof_k` called with `hD` (and `hV3`) derived, `3 ≤ bodyBarDim n` from `hk` and
  `hn`, the four types restated without the `set_option` with no warning, and a type without
  `hfresh` (`theorem_55_6_multigraph_gen`'s) as the control, which warns; on the three standard
  axioms (`scratch/reconcile-lean/Hyps-t362.lean`, gitignored).
  *Found:* RECONCILE round 3 task 36.2.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`): task 38.10 for the four `set_option`s and
  their sentences. Task 38.1: task 38.19 drops the `hD` of `theorem_55_minimalKDof_k` (from `hn`;
  caller `theorem_55_d3`), of `rankHypothesis_genuine_of_theorem_55_gen`,
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`,
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`,
  `hasGenericFullRankRealization_of_theorem_55_gen`, `theorem_55_6_multigraph_of_two_le` and
  `theorem_55_6_multigraph` (`thm:theorem-55-6-multigraph`), each deriving `3 ≤ D` by `hn ▸
  three_le_screwDim hk1` where it calls the main result, and the `hV3` of `case_I_dispatch_gen` and
  `case_I_hcontract_gen` (`lem:case-I-dispatch`, `lem:case-I-all-k`; the main result's Case I
  argument then binds `_hV3`). Left: the `hD` on `theorem_55_minimalKDof_gen`'s chain
  (`case_I_realization_nonsimple_gen`, `case_I_dispatch_gen`, `case_I_hcontract_gen`,
  `case_I_realization_all_k_gen`, `theorem_55_minimalKDof_k_all_k`), which the main result's
  statement fixes (`F-324`); the repeated steps of S2's rows and their forms (the strip, the
  re-aimed selector, `def(G̃) = 0` on one body), which the phase's carrier refactor rewrites; and
  `case_I_hcontract_gen`'s case split, a sibling dispatch (§C).
- **F-299** · L · a missed mathlib lemma and a repeated derivation in `Molecular/Molecule/`.
  `screwCoord_injective` (`ScrewVelocity.lean`) proves by rank–nullity, from `screwCoord_surjective`
  and the two dimensions, what `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` gives; and
  `eq_zero_of_molecularVel_eq_zero` and `exists_screwVel_eq_on_closedNeighborSet`
  (`Dictionary.lean`) derive the same two distinct neighbours of `v` from `hmin` (three lines each).
  `lake lint` reports neither.
  *Evidence:* read (the bodies); a `lake lean` witness: `screwCoord_injective` from the mathlib
  lemma and `screwCoord_surjective`, on the three standard axioms
  (`scratch/reconcile-lean/t37/Hyps-t37.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.20). Task 38.1:
  `screwCoord_injective` by `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` with
  `screwCoord_surjective`. Left: the two neighbours of `v` (three lines in each of two proofs).
- **F-300** · L · a repeated derivation and three derivable instance arguments in
  `Molecular/Molecule/`. The proof of `exists_molecular_rankHypothesis_generalPosition`
  (`Modelling.lean`) derives, as its local `smul_right`, `hspaneq` and `hmotions`, that the panel
  support extensor is homogeneous in its second normal and that rescaling each normal by a nonzero
  scalar keeps the motions. `Pencil/MainComponent/Bridge.lean` states both, as
  `panelSupportExtensor_smul_right` and `PanelHingeFramework.infinitesimalMotions_ofNormals_smul`
  (`lem:pencil-jj-rescale`, with `supportExtensor_ofNormals_smul`), in a file that `Modelling.lean`
  does not import; beside `panelSupportExtensor_smul_left` (`AlgebraicInduction/PanelLayer.lean`)
  and `ofNormals` (`PanelHinge.lean`) they would serve both. And the `[Nonempty α]` of
  `exists_molecular_rankHypothesis_generalPosition` (`thm:panel-hinge-iff-molecular`) and of
  `PanelHingeFramework.exists_rankHypothesis_isGeneralPosition4` (`Theorem56.lean`,
  `lem:theorem-56-general-position`), which `hne : V(G).Nonempty` gives, and of
  `exists_rankHypothesis_isGeneralPosition4_of_two_le`, which `hV : 2 ≤ V(G).ncard` gives; the
  nodes state `V ≠ ∅`, so dropping them restates no node. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the rescaling step from the
  two lemmas, and each of the three theorems without `[Nonempty α]`, on the three standard axioms
  (`scratch/reconcile-lean/t371/Hyps-t371.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.1.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.10). Task 38.1: task 38.10 drops
  the three `[Nonempty α]` (`⟨hne.some⟩`, or from `hV`; no node restated). Left: the rescaling
  steps, as `panelSupportExtensor_smul_right` and `infinitesimalMotions_ofNormals_smul` pin
  `lem:pencil-jj-rescale` in `main-component.tex`, after `thm:panel-hinge-iff-molecular` and
  `lem:molecule-rank-lower-bound`, whose pins would then reach it (a forward edge, gate 7;
  `scratch/reconcile-lean/t381/reach.py`).
- **F-302** · L · repeated derivations in `Molecular/Molecule/Pencil/Statement.lean` and
  `Chart.lean`. The two transport lemmas
  (`extensorInPanel_screwComplementIso_of_extensorThroughPoint` and
  `extensorThroughPoint_screwComplementIso_of_extensorInPanel`) derive the same seven steps of
  their nonzero case, from `C ≠ 0` and `C.val = extensor v` to the pair `p'` of
  `exists_extensor_eq_panelSupportExtensor` and `screwComplementIso C = panelSupportExtensor
  (v 0) (v 1)`, and four proofs of `Statement.lean` write out `C.val ≠ 0` from `C ≠ 0`.
  `exists_linearIndependent_extensor_pair_through_point` and `_through_given_point` take the
  independence of two extensors from `⋀²K⁴` to `ScrewSpace K 2` by the same steps
  (`LinearMap.linearIndependent_iff` and `hfun`). `linearIndepOn_pencilChartNormal_closedHubNbhd`
  and `linearIndepOn_pencilChartPoint_closedNbhd` prove the same injectivity of the map from a
  set to the slots of its selector, which one lemma on `IsFin3SelectorOf` would state; and
  `linearIndependent_hubSlotNormal_iff` and `linearIndependent_nbrSlotPoint_iff` are both
  `![f 0, f 1, f 2] = f` at one `f`.
  *Evidence:* read (the bodies).
  *Found:* RECONCILE round 3 task 37.2.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.21). Task 38.1: one lemma on
  `IsFin3SelectorOf` (the map from the slots a selector fills to its set is injective) at
  `linearIndepOn_pencilChartNormal_closedHubNbhd`, `linearIndepOn_pencilChartPoint_closedNbhd` and
  `F-306`'s two sites. Left: the two transport lemmas' nonzero case (opposite directions), `C.val ≠
  0` (a line each), the transfer from `⋀²K⁴` (two sites) and `![f 0, f 1, f 2] = f`.
- **F-303** · L · hypotheses the others give, a missed mathlib lemma and repeated derivations in
  `Molecular/Molecule/Pencil/Arms.lean` and `ArmsAssembly.lean`. The `hD : 2 ≤ bodyBarDim n` of
  `exists_hasPencilPanelRealization_glue`, of `hasPencilRealization_of_not_twoEdgeConnected_core`
  and of its two forms (`lem:pencil-cut-case`, whose statement has no such hypothesis) follows from
  `hn : bodyBarDim n = screwDim 2` alone (`screwDim 2 = 6`), and each uses it only to pass it on to
  `finrank_span_rigidityRows_cutEdge_eq`, which uses its own only for `1 ≤ screwDim k` (`F-297`).
  `finrank_span_pair_le` and `finrank_span_triple_le` are mathlib's `finrank_span_le_card` with
  `Finset.card_le_two` and `Finset.card_le_three`, as `le_finrank_toDualPerp_single` uses it for one
  vector, and `finrank_span_insert_le` serves only them. `exists_perp_linearIndependent` derives,
  by its own linear form and rank–nullity, that the vectors orthogonal to `m` form a space of
  dimension at least `3`, which `le_finrank_toDualPerp_single` states (`F-279`). The proof of
  `hasPencilRealization_of_not_twoEdgeConnected_core` sorts each link of `G` into `G[V₁]`, `G[V₂]`
  or the cut, and counts `|V₁| + |V₂| = |V(G)|`, as `exists_hasPencilPanelRealization_glue` does
  (some 30 lines); and the parallel case of `hasPencilRealization_of_ncard_le_two` derives the rank
  `D` of two bodies made rigid by two independent hinges as
  `theorem_55_base_producer_parallel_pair_gen` (`Theorem55.lean`) does (some 15 lines each).
  `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the four declarations called
  with `hD` derived from `hn`, and the two bounds from `finrank_span_le_card`, on the three standard
  axioms (`scratch/reconcile-lean/t373/Hyps-t373.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.3.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.20). Task 38.1: drop the `hD` of
  `exists_hasPencilPanelRealization_glue`, `hasPencilRealization_of_not_twoEdgeConnected_core` and
  its two forms (`lem:pencil-cut-case` states none), giving `2 ≤ D` from `hn` at the call of
  `finrank_span_rigidityRows_cutEdge_eq` (callers of the four: `F-307`'s and
  `pencilPair_of_not_twoEdgeConnected`); `finrank_span_pair_le` and `finrank_span_triple_le` by
  `finrank_span_le_card` with `Finset.card_le_two` and `Finset.card_le_three`, and
  `finrank_span_insert_le`, which serves only them, deleted (gate 4). Left:
  `exists_perp_linearIndependent` (`le_finrank_toDualPerp_single` goes in task 38.7), the cut's
  sorting (two proofs) and the parallel case's rank (two statements, ~15 lines).
- **F-304** · L · an over-strong hypothesis, a missed mathlib lemma and repeated derivations in
  `Molecular/Molecule/Pencil/Motive.lean`. `dotProduct_point_eq_zero_of_mem_closedNbhd` takes
  `IsNondegPencilRealization` and uses only its first conjunct, the pencil realization
  (`HasPencilPanelRealization`), and `dotProduct_point_eq_zero_of_mem_closedHubNbhd` and
  `dotProduct_normal_eq_zero_of_mem_closedNbhd` only pass it on: the chapter derives the
  orthogonality from a pencil realization (the remark after `def:pencil-nondegenerate`).
  `linearIndependent_triple_of_linearIndepOn` is mathlib's `linearIndepOn_range_iff` at the
  injective `![x, y, z]`, whose range is `{x, y, z}` (its docstring said that mathlib has no such
  form). `hasPencilRealization_of_generic` is `hasPencilRealization_of_distinct` after
  `hasDistinctPencilRealization_of_generic`. `Graph.degree_induce_union_singleton_of_mem`,
  `Graph.degree_induce_of_forall_isLink_mem` and `Graph.degree_induce_eq_of_ne` each derive that the
  loops and the non-loops at `v` of `G.induce S` are those of `G` (some 15 lines each), from the
  links of `G` at `v` ending in `S`, which one lemma would state; the second uses its `hS` only at
  `v`. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the orthogonality, in both
  forms, from `HasPencilPanelRealization` alone, the triple from `linearIndepOn_range_iff` (its
  range by `simp only` with `Matrix.range_cons`, `Matrix.range_empty`, `Set.union_empty` and
  `Set.singleton_union`; `simp` with `Set.insert_eq` loops), the forgetful map as the composition,
  and the three degree lemmas from one local form, on the three standard axioms
  (`scratch/reconcile-lean/t374/Hyps-t374.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.4.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.20). Task 38.1: weaken the
  `IsNondegPencilRealization` of `dotProduct_point_eq_zero_of_mem_closedNbhd`,
  `dotProduct_point_eq_zero_of_mem_closedHubNbhd` and `dotProduct_normal_eq_zero_of_mem_closedNbhd`
  to `HasPencilPanelRealization`, as the chapter's remark derives it (unpinned; callers pass
  `hnd.1`); `linearIndependent_triple_of_linearIndepOn` by `linearIndepOn_range_iff` (the range by
  `simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]`);
  `hasPencilRealization_of_generic` as the composition; one lemma for the loops and non-loops at `v`
  of `G.induce S` (~15 lines in each of `degree_induce_union_singleton_of_mem`,
  `degree_induce_of_forall_isLink_mem`, `degree_induce_eq_of_ne`; the witness's local form). Left:
  the second's `hS` at every vertex (its callers hold it; a change of form only).
- **F-305** · L · a repeated derivation in `Molecular/Molecule/Pencil/Engine.lean`: the re-seeding
  at selectors it chooses. `exists_hubSlotOf_isNondegPencilRealization`,
  `exists_hubSel_fillHub_of_isNondegPencilRealization`,
  `exists_nbrSlotOf_isNondegPencilRealization` and
  `exists_nbrSel_fillNbr_of_isNondegPencilRealization` (some 370 lines), which
  `exists_pencilSeed_of_nondeg` (`Reseed.lean`) puts together, build a selector and the padding at
  each body, case by case on the number of members of its closed hub-neighbourhood or closed
  neighbourhood. `exists_pencilSeed_of_nondeg_of_selectors` (`Reseed.lean`) builds the padding for
  any given selectors, so `exists_pencilSeed_of_nondeg` follows from it and a selector of each set
  of at most three members, by the bounds
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` and
  `ncard_closedNbhd_le_three_of_not_pencilHub` (`Motive.lean`). Without the four,
  `exists_cross₃_eq_of_ne_zero`, `exists_cross₃_eq_of_linearIndependent_pair_of_dotProduct_eq_zero`
  and `exists_linearIndependent_triple_of_ne_zero` would have no caller. `lake lint` reports none of
  them.
  *Evidence:* read (the statements and bodies; the callers from `scripts/blueprint-deps.py`'s Lean
  cache); a `lake lean` witness: the selector of a set of at most three members (by
  `Finset.toList`, 19 lines; its injectivity by `List.Nodup.getElem?_inj`, which takes the index
  bound before the `Nodup`), and the statement of `exists_pencilSeed_of_nondeg` from it and
  `exists_pencilSeed_of_nondeg_of_selectors`, on the three standard axioms
  (`scratch/reconcile-lean/t375/Hyps-t375.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.5.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.9): task 38's block (b) at
  `1b1d9d87` finds the four unpinned and live only through `exists_pencilSeed_of_nondeg`, which
  calls the two `fill` lemmas and which the fix re-proves; the four and the three helpers above
  then have no caller, and none is pinned.
- **F-306** · L · a missed mathlib lemma and repeated derivations in
  `Molecular/Molecule/Pencil/Reseed.lean` and `Steer.lean`.
  `linearIndepOn_triple_of_linearIndependent` (`Steer.lean`) is mathlib's `linearIndepOn_range_iff`
  at the injective `![x, y, z]`, read the other way, as `F-304` finds of its converse
  `linearIndependent_triple_of_linearIndepOn`. `pencilChartPoint_ofCoord_toCoord` is
  `pencilChartPoint_congr` at `PencilSeed.ofCoord_toCoord_hubNormal` and
  `PencilSeed.ofCoord_toCoord_fillHub`, whose proof derives the equality of the slots that
  `hubSlotNormal_ofCoord_toCoord` states; that lemma would then have no caller.
  `exists_fill_linearIndependent_hubSlotOf` (`Reseed.lean`) derives the same equality of its slots
  twice (some 7 lines each), and it and `linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint`
  (`Steer.lean`) each derive the injective map from the slots a selector fills to its set, as the
  two lemmas of `F-302` do, which one lemma on `IsFin3SelectorOf` would state.
  `exists_pencilSeed_of_nondeg` and `exists_pencilSeed_of_nondeg_of_selectors` give the condition of
  `PencilChartWF` on links by the same steps (some 10 lines; `F-305` would remove the first).
  `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the triple from
  `linearIndepOn_range_iff`, `pencilChartPoint_ofCoord_toCoord` from `pencilChartPoint_congr`, and
  the lemma on `IsFin3SelectorOf`, with `linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint` from
  it, on the three standard axioms (`scratch/reconcile-lean/t376/Hyps-t376.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.6.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`): task 38.9 for
  `pencilChartPoint_ofCoord_toCoord` and `hubSlotNormal_ofCoord_toCoord` (unpinned; its one caller
  is the first, task 38's block (b) at `1b1d9d87`), whose re-proof of `exists_pencilSeed_of_nondeg`
  also ends the repeated `PencilChartWF` steps. Task 38.1: task 38.21 re-proves
  `linearIndepOn_triple_of_linearIndependent` by `linearIndepOn_range_iff` (`F-304`'s converse) and
  puts `F-302`'s lemma at `exists_fill_linearIndependent_hubSlotOf` and
  `linearIndepOn_nbrSlotPoint_isSome_of_pencilChartPoint`. Left: the two slot equalities of
  `exists_fill_linearIndependent_hubSlotOf` (one proof).
- **F-307** · L · hypotheses the others give, over-strong hypotheses and repeated derivations in
  `Molecular/Molecule/Pencil/Pair.lean` and `Pair2.lean`. The `hD : 2 ≤ bodyBarDim n` of
  `hasGenericPencilRealization_of_cutEdges_eq_empty`,
  `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`,
  `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI`,
  `hasGenericPencilRealization_pendant_of_IH` and `pencilPair_of_not_twoEdgeConnected` follows from
  `hn : bodyBarDim n = screwDim 2` alone, and each only passes it on, to the declarations of `F-303`
  (`exists_hasPencilPanelRealization_glue` and the cut-edge case) or to one another. The `hloop` of
  `hasGenericPencilRealization_of_ncard_le_two` follows from its `hSimple`
  (`Graph.Simple.toLoopless`). `pencilPair_of_isLoopAt` takes `PencilPair K n (G ＼ {e})` and uses
  only its pencil realization at the deficiency rank, and
  `hlb_induce_of_isNondegPencilRealization_induce_union_singleton` takes a nondegenerate realization
  and uses only its graph and its nonzero hinge at `e₀`.
  `exists_isNondegPencilRealization_parallel_pair` and the one-edge case of
  `hasGenericPencilRealization_of_ncard_le_two` build the same nondegenerate realization of two
  bodies (some 70 lines each), which one lemma on a graph whose links all join `x` and `y` would
  state. `hasGenericPencilRealization_of_cutEdges_eq_empty` takes each step for `V₁` and again for
  `V₂` (some 30 lines a side), and
  `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton` derives its four
  pairs of vectors to avoid by the same steps (some 13 lines each) and each of its last two
  conditions for the two sides by the same steps with the sides exchanged (some 30 lines a side).
  `hasGenericPencilRealization_of_isNondegPencilRealization_induce_pendant_of_hubLI` derives
  `v = v_c` from `v ∈ V(G)`, `v ∉ V₁` and `hVG` seven times by the same three lines
  (`hasGenericPencilRealization_pendant_of_IH` states it once, as `hoff`), and the two each derive
  that `v_c` is not a hub from `Graph.degree_induce_union_singleton_far`. `lake lint` reports none
  of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the five declarations called
  with `hD` derived from `hn`, the generic realization on at most two bodies without `hloop`, the
  conditioned pair at a loop from the pencil realization of `G ＼ {e}` alone, and the rank of a side
  from the graph of `F` and its nonzero hinge at `e₀` alone, on the three standard axioms
  (`scratch/reconcile-lean/t377/Hyps-t377.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.7.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.22). Task 38.1: drop the `hD` of
  the five (`2 ≤ D` from `hn` where `F-303`'s glue needed it) and
  `hasGenericPencilRealization_of_ncard_le_two`'s `hloop` (`hSimple.toLoopless`; caller
  `pencilPair_of_ncard_le_two`), all unpinned; state `v = v_c` once in `…_pendant_of_hubLI` for its
  seven copies (as `hoff` in `hasGenericPencilRealization_pendant_of_IH`). Left:
  `pencilPair_of_isLoopAt`'s and `hlb_induce_…`'s over-strong hypotheses, which their callers hold
  (a change of form only); the two-body realization (~70 lines), whose shared form would generalize
  `exists_isNondegPencilRealization_parallel_pair`, the chapter's witness; the four pairs and the
  per-side steps (one proof each); `degree_induce_union_singleton_far`'s two uses.

- **F-308** · L · an over-strong hypothesis, a hypothesis another gives and repeated derivations in
  `Molecular/Molecule/Pencil/X0.lean` and `MainComponent/GenericSteer.lean`.
  `pencil_realization_theorem_of_X0` uses its `hspan : V(G) = Set.univ` and its `[Nonempty α]` only
  for `V(G).Nonempty`, at which `pencilPair_of_arms` gives the conditioned pair from the two
  main-component statements at any graph, the form of `pencilPair_of_nonempty`
  (`MainComponent/Statements.lean`); its node, `thm:pencil-conditional-realization-main-component`,
  states the spanning form. The `hloop : H.Loopless` of `exists_isNondegPencilRealization_steer`
  follows from its nondegenerate realization `hnd₁` (`not_pencilNondegFeasible_of_isLoopAt`); part
  (b) of `lem:pencil-generic-steer` states it. Of the 226 code lines of
  `hasPencilRealization_of_not_simple` (comments and blank lines aside), 136 are lines of the 228 of
  `case_I_realization_nonsimple_gen` (`AlgebraicInduction/Theorem55.lean`), in the same order: the
  parallel pair, the subgraph `H'` and its properness, the rank of the rows of `H'`, the hypotheses
  of the splice and the rank arithmetic; the two differ in the induction hypothesis, the two new
  hinges and the conditions on the realization.
  `exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub` derives its facts at `w₁` and
  again at `w₂` by the same steps with the two exchanged (some 70 lines a side: no link between them
  when either is a hub, at most one other member of the closed hub-neighbourhood, and the indices of
  the slots). `exists_isNondegPencilRealization_restrict_of_demoted` and
  `exists_isNondegPencilRealization_steer` each derive the four conditions of `PencilChartWF` that
  do not read `fillNbr` from the independence of the points on `{v}` or the closed neighbourhood and
  on the two ends of each pair of adjacent bodies, by the same steps (some 30 lines each), and each
  shows these independences at the coordinate point of the realization it writes in the chart by the
  same steps (some 20 lines each), as `exists_coord_linearIndepOn_closedNbhd_of_demoted` does for
  `{v}` and a link. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies; the shared lines counted by a sequence match of the
  two bodies' code lines); a `lake lean` witness: the conditioned pair from the two statements at
  every nonempty graph without `hspan` and `[Nonempty α]`, and
  `exists_isNondegPencilRealization_steer` with `hloop` derived from `hnd₁`, on the three standard
  axioms (`scratch/reconcile-lean/t378/Hyps-t378.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.8.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.22). Task 38.1: drop
  `exists_isNondegPencilRealization_steer`'s `hloop` (`not_pencilNondegFeasible_of_isLoopAt` from
  `hnd₁`; `lem:pencil-generic-steer` (b) restated; callers
  `hasGenericPencilRealization_pendant_of_IH`, `IsOpenEar.hasGenericPencilRealization_of_one`,
  `hasGenericPencilRealization_of_closedEar_two`). Left: `pencil_realization_theorem_of_X0`'s
  `hspan` and `[Nonempty α]`, as its node states the spanning form and the general form is the main
  result `pencilPair_of_nonempty`'s; the 136 lines `hasPencilRealization_of_not_simple` shares with
  `case_I_realization_nonsimple_gen`, which differ in the induction hypothesis, the hinges and the
  realization's conditions, so a shared lemma would thread the parallel pair, `H'` and the splice's
  hypotheses (§C's calibration); `GenericSteer.lean`'s per-side and per-theorem steps.
- **F-309** · L · repeated derivations and an unneeded instance in
  `Molecular/Molecule/Pencil/MainComponent/Carrier.lean` and `Configuration.lean`.
  `Graph.liftingMatrix K G` is, by definition, `Graph.weightedLiftingMatrix K G` at the weights
  `fun _ w => pencilPicturePointPoly w` (`rfl`), and `Graph.liftingMatrix_mulVec_eq_zero_iff`
  repeats the proof of `Graph.weightedLiftingMatrix_mulVec_eq_zero_iff` (some 40 lines each), from
  which it follows in two lines (`eval_pencilPicturePointPoly`).
  `linearIndependent_pencilConfigPoint_pair` and `linearIndependent_pencilPicturePoint_pair` have
  the same proof (16 lines each), and the first follows from the second by
  `linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint`, which
  `Configuration.lean` states. `Graph.finrank_ker_liftingMatrix` proves the injectivity of the
  projection to the heights that `Graph.injective_liftingMatrix_ker_proj` states, and the second
  derives it back from the first by rank–nullity. `Graph.isAdmissiblePicture_congr`,
  `Graph.liftingSpace_congr` and `Graph.ker_liftingMatrix_congr` derive the same equality of picture
  points by the same two lines, and `Graph.finrank_affineLifts`, `Graph.finrank_ker_liftingMatrix`
  and `Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar` each show that a vector with dot
  product zero against three independent picture points is zero by the same steps through a unit
  matrix (some 10 lines each). The `[Finite α]` of `Graph.finrank_affineLifts` is not needed.
  `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the lifting system as the
  weighted one (`rfl`), its kernel from the weighted one, the pair of configuration points from the
  pair of picture points, and `Graph.finrank_affineLifts` without `[Finite α]`, on the three
  standard axioms (`scratch/reconcile-lean/t379/Hyps-t379.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.9.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.23). Task 38.1: one lemma that a
  vector of `K³` with dot product zero against three independent vectors is zero (mathlib's if
  `lean_loogle` finds it), at `finrank_affineLifts`, `finrank_ker_liftingMatrix`,
  `IsAdmissiblePicture.mem_liftingSpace_of_coplanar` and `F-310`'s `finrank_liftingPlanes` (~10
  lines each); `finrank_affineLifts` without `[Finite α]` (`lem:pencil-lifting-space-affine` states
  no instance). Left: `liftingMatrix_mulVec_eq_zero_iff`, whose re-proof from the weighted form
  would make `def:pencil-lifting-system` reach the later `def:pencil-weighted-lifting-system` (a
  forward edge, gate 7; `t381/reach.py`); `linearIndependent_pencilConfigPoint_pair`, whose tool is
  in `Configuration.lean`, which imports `Carrier.lean`; the rank–nullity between
  `finrank_ker_liftingMatrix` and `injective_liftingMatrix_ker_proj` (a few lines); the `_congr`
  lemmas' two lines.
- **F-310** · L · over-strong hypotheses, repeated derivations and a repeated binder in
  `Molecular/Molecule/Pencil/MainComponent/Flat.lean` and `Bridge.lean`.
  `Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint` and
  `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` take `G.IsAdmissiblePicture q` and
  use only its first conjunct, that the two ends of every link have distinct picture points; the
  other pins of their nodes (`lem:pencil-lifting-planes-motions`, `lem:pencil-flat-split`) read no
  picture or take the whole condition, so the statements of the nodes need not change.
  `exists_mvPolynomial_linearIndependent_pointJoin_picture` and
  `exists_mvPolynomial_linearIndependent_pointJoin_heights` have the same proof (13 lines each) but
  for the variables and the polynomial family, each passing to `Set.univ` and back around
  `exists_polynomial_ne_zero_of_linearIndependent_at_reindex`, which a form of that lemma for a
  whole family would spare. `Graph.finrank_liftingPlanes` shows that a vector with dot product zero
  against three independent picture points is zero through a unit matrix (9 lines), the steps that
  `F-309` finds in three lemmas. `PanelHingeFramework.finite_setOf_finrank_lt_of_curve` binds
  `{k : ℕ}`, which the file's `variable {k : ℕ}` already gives. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies; the two proofs compared line by line); a `lake lean`
  witness: the two motion-space lemmas with the first conjunct of admissibility in its place and the
  parents' proofs, on the three standard axioms (`scratch/reconcile-lean/t3710/Hyps-t3710.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 37.10.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.23). Task 38.1:
  `finrank_liftingPlanes` by `F-309`'s lemma; `finite_setOf_finrank_lt_of_curve` without its
  repeated `{k : ℕ}`. Left: the two motion-space lemmas' `IsAdmissiblePicture`, which their callers
  hold (a change of form only); the two `exists_mvPolynomial_…` (13 lines each: a whole-family form
  of the reindex lemma would be new, for two sites).
- **F-311** · L · repeated derivations in `Molecular/Molecule/Pencil/MainComponent/Cut.lean`.
  `Graph.X0Attains.of_cutVertex` and `Graph.X0Attains.of_bridgePath` repeat the same steps: the
  picture off the three polynomials and the two sides' data, `hendsI` (the selector `G.endsOf`
  records every link of an induced subgraph, 7 lines, also in `ContractAdditive.lean`, and for one
  side in `Short.lean`, `Orbit.lean` and `Ear.lean`) and `hcongr` (each side's rank read at
  `G.endsOf` and the heights of `G`, 11 lines), which two lemmas would spare.
  `Graph.X0Attains.of_bridgePath` derives the reversed path `hpath₂` (5 lines) that
  `isLink_pathVertex_rev hpath` gives, a lemma of the same file. `pathVertex_eq_or_exists` repeats
  the induction of `pathVertex_cases`, from which it follows in four lines. The instance `hmem` of
  `pathVertex_mem_union_image_iff` is derived the same way in
  `Graph.cutEdges_union_image_of_bridgePath`, `Graph.deficiency_induce_union_range_of_bridgePath` and
  `BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath`, and the
  step `hxj` in the last two. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies; the two theorems compared line by line); a `lake
  lean` witness: `hpath₂`'s statement by `isLink_pathVertex_rev hpath`, and
  `pathVertex_eq_or_exists` from `pathVertex_cases`, on the standard axioms
  (`scratch/reconcile-lean/t3711/Hyps-t3711.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.11.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.23 and 38.24). Task 38.1: task
  38.23 replaces `X0Attains.of_bridgePath`'s `hpath₂` by `isLink_pathVertex_rev hpath` and re-proves
  `pathVertex_eq_or_exists` from `pathVertex_cases` (moved above it); task 38.24 states `hendsI`
  once (the selector of `G` gives every link of `G.induce X` its ends; 7 lines at each of the eight
  `have hendsI`, in `Cut.lean`, `Ear.lean`, `ContractAdditive.lean`, `Short.lean` and `Orbit.lean`).
  Left: `hcongr` (two sites, one file), `hmem` and `hxj` (a few lines each).
- **F-312** · L · repeated derivations and a derivable hypothesis in
  `Molecular/Molecule/Pencil/MainComponent/Ear.lean`. `panelSupportExtensor_mem_span_ofNormals`
  repeats the case split on the orientation of `Cut.lean`'s `span_supportExtensor_ofNormals_eq`,
  from which it follows in two lines at `k = 2`, and `span_supportExtensor_comp_eq_map_pointJoin`
  repeats it once more (`hbase`, `hmem`). `span_supportExtensor_eq_top_of_linearIndependent` and
  `card_le_finrank_of_linearIndependent_pointJoin` derive the independence of the meets `hli'` the
  same way (7 lines each), and the first follows from the second at the span of the hinges, of
  dimension at most six. The hypothesis `hinj` of `Graph.mem_liftingSpace_oneEar` holds for every
  `x : Fin 1 → α`. `x i ≠ a` and `x i ≠ b` are derived from `hxV₁` the same way in
  `BodyHingeFramework.finrank_span_rigidityRows_ear_eq`, `Graph.closedNbhd_ear_subset` and
  `Graph.mem_closedNbhd_induce_of_ear`, and the four `linearIndependent_flat_*` lemmas repeat a
  near-identical `simp only` of six or seven lines and restate their family in `e1` and `e2`. `lake
  lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the first lemma from
  `span_supportExtensor_ofNormals_eq`, the second from
  `card_le_finrank_of_linearIndependent_pointJoin`, both on the standard axioms, and `hinj` at
  `Fin 1` by `Function.injective_of_subsingleton`, on `propext`
  (`scratch/reconcile-lean/t3712/Hyps-t3712.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.12.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.23). Task 38.1:
  `panelSupportExtensor_mem_span_ofNormals` from `span_supportExtensor_ofNormals_eq` (`Cut.lean`) at
  `k = 2`; `span_supportExtensor_eq_top_of_linearIndependent` from
  `card_le_finrank_of_linearIndependent_pointJoin` (moved above it; the hinges span at most six
  dimensions); `mem_liftingSpace_oneEar`'s `hinj` dropped (`Function.injective_of_subsingleton`;
  `lem:pencil-splitoff-ear-extension` restated where it states it; caller `X0Attains.of_splitOff`).
  Left: `span_supportExtensor_comp_eq_map_pointJoin`'s orientation split (one proof), `x i ≠ a` and
  `x i ≠ b` (a line or two each) and the four `simp only`s.
- **F-313** · L · repeated derivations, an unused hypothesis and needless steps in
  `Molecular/Molecule/Pencil/MainComponent/ContractCurve.lean`. `Graph.rigidContract_induce_simple`
  re-derives the file's `collapseTo_of_mem`, `collapseTo_of_not_mem` and `mem_of_collapseTo_eq` as
  `hcolW`, `hcolO` and `hin`, and the whole lemma follows in a few lines from
  `Graph.exists_isLink_pair_of_rigidContract_not_simple` (`Induction/Contraction.lean`, a step of
  the proof of KT Claim 6.6, p. 676) at `H = G[W]`. `Graph.closedNbhd_induce_subset` is
  `Graph.closedNbhd_mono (G.induce_le hW)` (`Pencil/Motive.lean`) at both its callers, which have
  `hW : W ⊆ V(G)`. The case analysis of a member of a closed neighbourhood of `G/H`
  (`Graph.mem_closedNbhd_rigidContract`, the ends placed in or out of `W`, the collapse rewritten
  away) is repeated, at `r` three times (`Graph.contractLimitMap_mem_liftingSpace`,
  `Graph.eq_zero_of_contractLimitMap_eq_zero`,
  `Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`) and at a body outside `W` four times
  (the first two, each at a neighbour of `W` and at another body, with a `hout` step each time); and
  `r ∈ V(G/H)` is derived the same way in three lemmas and in `ContractAdditive.lean`. The first
  conjunct of the hypothesis `hg` of `Graph.contractLimitMap_mem_liftingSpace` (the core heights on
  the plane of `g`) is not used; `Graph.exists_contractHeight_eq` states a `have hwW` it does not
  use; and the proof of `PanelHingeFramework.exists_rankPolynomial_rigidContract_induce_proj`
  elaborates without its `rw [hGcf] at hne hN`, which the file's header said a `panelRow` step needs
  to avoid an `isDefEq` timeout. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the simplicity from
  `Graph.exists_isLink_pair_of_rigidContract_not_simple`, the inclusion from
  `Graph.closedNbhd_mono`, the limit map's lemma without the first conjunct of `hg` and
  `Graph.exists_contractHeight_eq` without `hwW`, on the three standard axioms
  (`scratch/reconcile-lean/t3713/Hyps-t3713.lean`, gitignored); and the degenerate-rank lemma's
  proof without the rewrite, which elaborates with no error at the default heartbeats, in about the
  time of the proof with it (`scratch/reconcile-lean/t3713/DefeqA.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.13.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.25). Task 38.1:
  `rigidContract_induce_simple` from `exists_isLink_pair_of_rigidContract_not_simple` at `H = G[W]`
  (69 lines to a few); `closedNbhd_induce_subset` deleted (gate 4), its two callers calling
  `closedNbhd_mono (G.induce_le hW)`; the unused first conjunct of
  `contractLimitMap_mem_liftingSpace`'s `hg` dropped (unpinned; caller
  `finrank_ker_contractLiftingMatrix_zero_add_three_le`), `exists_contractHeight_eq`'s `have hwW`
  removed, and `exists_rankPolynomial_rigidContract_induce_proj`'s `rw [hGcf] at hne hN` with the
  header's sentence on it. Left: the case analyses of a member of a closed neighbourhood of `G/H`,
  and `r ∈ V(G/H)`, which thread each proof's locals.
- **F-314** · L · repeated derivations and an unused step in
  `Molecular/Molecule/Pencil/MainComponent/Chain.lean` and `ContractAdditive.lean`.
  `Graph.X0Attains.of_cycle_of_certificate` states a `have hcover'` it does not use, and the two
  branches of its `honlyP` (7 lines each) are one case analysis with the ends swapped.
  `Graph.X0Attains.of_cycle` (four times, one per polygon) and `Graph.X0Attains.of_openEar` (once)
  restate the joins of their configuration as those of a closed polygon of
  `lem:pencil-chain-span-certificates` by the same `funext`, `fin_cases`, `change` and `rw` steps
  (`heq`, a line per edge), which one lemma on a labelling of the bodies would spare, and the two
  derive `hxne` from `hinj` the same way. `Graph.X0Attains.of_additiveContract` derives twice
  (`hlow0`, `hdim`) the bound `3 + def₂(G) ≤ dim L_G(q(t)) ≤ dim ker M(t)` at a `t ≠ 0` where
  `q(t)` is a main picture, and states `hevZ`, an instance of `MvPolynomial.eval_bind₁`. `lake lint`
  reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness:
  `Graph.X0Attains.of_cycle_of_certificate` without `hcover'`, on the three standard axioms
  (`scratch/reconcile-lean/t3714/Hyps-t3714.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.14.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.25). Task 38.1: remove
  `X0Attains.of_cycle_of_certificate`'s unused `have hcover'`; `of_additiveContract`'s `hevZ` by
  `MvPolynomial.eval_bind₁`. Left: `honlyP`'s two branches (one case analysis, ends swapped), `heq`
  (a lemma on a labelling of the bodies would be new, for a few lines at five sites), `hxne`, and
  `hlow0`, `hdim` (one proof).
- **F-315** · L · repeated derivations in `Molecular/Molecule/Pencil/MainComponent/Lines.lean` and
  `EarGen.lean`. `Graph.earHeight_mem_liftingSpace` (`EarGen.lean`) repeats the proof of
  `Graph.earExtend_mem_liftingSpace` (`Ear.lean`) step for step (about 40 lines, through
  `Graph.mem_liftingSpace_of_ear` and `Graph.mem_closedNbhd_induce_of_ear`), with the planes and the
  free heights explicit, as its docstring says; with `earHeight` in `Ear.lean`, the second would
  follow from the first. `exists_insertion_gain` and `exists_insertion_two_aux` close by the same
  step, a case split on whether a vector `v` lies in a span `R`, then
  `exists_ne_zero_add_smul_notMem` and `Submodule.finrank_sup_span_singleton`, which one lemma (for
  spans `S t ⊇ R ⊔ K (v + t w)` at every `t ≠ 0`, `dim(R ⊔ K v) ≤ dim S t` at some `t ≠ 0`) would
  serve. The three branches of `klein_liftPlane`'s `ht0` (6 lines each) are one argument with the
  indices permuted. `exists_insertion_two` shows by hand (`hL`, `hR`, 36 lines) that reversing the
  joins of a family keeps its span, which `exists_insertion_of_star_sup_star` does in one rewrite
  (`pointJoin_swap`, `Set.neg_insert`, `Submodule.span_neg`). `exists_insertion_four` and
  `exists_insertion_three` regroup their spans by the same two rewrites (`hW` and the last `rw`).
  `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies).
  *Found:* RECONCILE round 3 task 37.15.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.25). Task 38.1:
  `exists_insertion_two`'s `hL`, `hR` (36 lines) by the rewrite of
  `exists_insertion_of_star_sup_star` (`pointJoin_swap`, `Set.neg_insert`, `Submodule.span_neg`).
  Left: `earExtend_mem_liftingSpace` from `earHeight_mem_liftingSpace`, which would make
  `lem:pencil-ear-fibre` reach the later `lem:pencil-ear-data` (a forward edge, gate 7); the common
  close of `exists_insertion_gain` and `exists_insertion_two_aux` (a new lemma for two sites);
  `klein_liftPlane`'s `ht0` (one argument, indices permuted); `hW` (two rewrites).
- **F-316** · L · repeated derivations and derivable hypotheses in
  `Molecular/Molecule/Pencil/MainComponent/Short.lean`. `splitOff_ear_four` and `splitOff_ear_three`
  are one proof (68 and 61 lines), the second with one interior body fewer, which one lemma at any
  number of interior bodies from three would serve. `Graph.X0Attains.of_openEar_four` and
  `Graph.X0Attains.of_openEar_three` derive the same `hdeg2` (the second interior body has degree
  two; 14 and 12 lines, and a third time in `Graph.X0Attains.of_openEar_two_of_splitOff`,
  `Orbit.lean`) and close by the same reindexing of the joins of the two ears (`e4` and `e5`, `e3`
  and `e4`, about 25 lines each). `Graph.exists_earBase_splitOff` proves its two neighbourhood
  conjuncts, at `a` and at `b`, by one argument with the ends swapped (7 lines each), and restricts
  the selector to `G[V₁]` (`hendsI`) as `Graph.X0Attains.of_openEar_of_cert` (`Ear.lean`),
  `Graph.X0Attains.of_openEar_one` and `Graph.X0Attains.of_openEar_two_of_splitOff` (`Orbit.lean`)
  do. The body count `hcard` of `Graph.X0Attains.of_openEar_splitOff`, `|V(H)| = |V₁| + k` when
  `V(H) = V₁ ∪ range z` with `z` injective and off `V₁`, is derived again in
  `Graph.X0Attains.of_openEar_of_cert`, three times in `Orbit.lean`
  (`Graph.X0Attains.of_openEar_one` once, `Graph.X0Attains.of_openEar_two_of_splitOff` twice) and in
  `Graph.X0Attains.of_splitOff` (`SplitOff.lean`). Derivable hypotheses: the `hle` of
  `Graph.exists_earBase_splitOff` follows from its `hcover` and `hind`, and the `hxfa` and `hxlb` of
  `Graph.X0Attains.of_openEar_splitOff` from its `hxV₁`, `ha` or `hb`, `hpath`, `hv`, `hl₀`, `hxf`
  or `hxl`, and `hvf` or `hvl` (the first and the last edge of the ear avoid `v`, so they stay links
  of `G″`). `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: `hle`, `hxfa` and `hxlb`
  derived from the others, on the standard axioms or fewer
  (`scratch/reconcile-lean/t3716/Hyps-t3716.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.16.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, tasks 38.24 and 38.26). Task 38.1: task
  38.24 states `hcard` once (`|V₁ ∪ range z| = |V₁| + k` for an injective `z : Fin k → α` off `V₁`;
  a `Mathlib/` mirror on `Set.ncard` unless mathlib has it) at its six sites (`Short.lean`,
  `Ear.lean`, `Orbit.lean` three, `SplitOff.lean`); task 38.26 drops `exists_earBase_splitOff`'s
  `hle` (from `hcover`, `hind`) and `X0Attains.of_openEar_splitOff`'s `hxfa`, `hxlb` (the first and
  last ear edges avoid `v`), both unpinned (callers `of_openEar_splitOff`; `of_openEar_four`,
  `of_openEar_three`). Left: `splitOff_ear_four`, `_three` and `F-317`'s `_two`, as a lemma at any
  number of interior bodies needs a new proof over `Fin k`; `hdeg2` (its lemma,
  `IsOpenEar.isLink_interior`, is downstream); the reindexing of the two ears' joins and the two
  conjuncts at `a` and `b` (per side).
- **F-317** · L · repeated derivations and derivable hypotheses in
  `Molecular/Molecule/Pencil/MainComponent/Orbit.lean`. Derivable hypotheses: the `hinj` of
  `Graph.exists_oneEar_base` and `Graph.X0Attains.of_openEar_one` (a map out of `Fin 1` is
  injective); the `hinj` of `Graph.X0Attains.of_openEar_two_of_splitOff` and
  `splitOff_ear_two_simple`, from simplicity and `hpath 1` (`x 0 ≠ x 1`, as `e 1` is no loop); and
  the `hab` of `Graph.exists_oneEar_base`, `Graph.X0Attains.of_openEar_one` and
  `Graph.X0Attains.of_openEar_two_of_splitOff`, from `hδ₂` (at `a = b` every partition puts `a` and
  `b` in one part, so the merged deficiency is the deficiency). Repeated derivations:
  `splitOff_ear_two` is the proof of `splitOff_ear_three` and `splitOff_ear_four` (`Short.lean`,
  `F-316`) with the relinked edge ending at `b`, which one lemma at any number of interior bodies
  from two would serve; `exists_dotProduct_eq_zero_ne_zero` proves its cases `c 0 ≠ 0` and
  `c 1 ≠ 0` by one argument with the coordinates swapped (16 lines each); in
  `Graph.X0Attains.of_openEar_two_of_splitOff`, `hlas` and `hlbs` are one argument at `a` and at `b`
  (10 lines each), and so are `hpt0` and `hpt1` (at `x 0` and `x 1`, 9 lines each) and the last two
  arguments of the call to `exists_insertion_two`; and the heights of an attainment are lifted to
  the kernel of the lifting matrix (`map_ker_liftingMatrix`, then `MvPolynomial.eval_rename`) in
  `Graph.exists_oneEar_base` (`hz₁'`, `h1`) and again in
  `Graph.X0Attains.of_openEar_two_of_splitOff` (`hz₂'`, its second fibre intersection). `lake lint`
  reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: the `hinj` of `Fin 1` and of
  `Fin 2` and `hab` derived from the others, and `Graph.X0Attains.of_openEar_one` and
  `Graph.X0Attains.of_openEar_two_of_splitOff` applied without them, on the standard axioms or fewer
  (`scratch/reconcile-lean/t3717/Hyps-t3717.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.17.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.26). Task 38.1: drop the `hinj` of
  `exists_oneEar_base` and `X0Attains.of_openEar_one` (`Function.injective_of_subsingleton`), of
  `X0Attains.of_openEar_two_of_splitOff` and `splitOff_ear_two_simple` (a new lemma beside
  `pathVertex`: a path `a, x 0, x 1, b` of a simple graph has `x` injective, from `hpath 1`;
  `F-321`'s two use it), and the `hab` of `exists_oneEar_base`, `of_openEar_one` and
  `of_openEar_two_of_splitOff` (a new lemma beside `deficiencyMerged`: `G.deficiencyMerged 2 a b + 2
  ≤ G.deficiency 2` gives `a ≠ b`, 5 lines, the witness's `hab_of_hδ₂`); `lem:pencil-one-ear-base`,
  `thm:pencil-x0-open-ear-one`, `thm:pencil-x0-open-ear-two-orbit` restated where they state them
  (callers `X0Reduces.x0Attains` and each other). Left: `splitOff_ear_two` (`F-316`'s),
  `exists_dotProduct_eq_zero_ne_zero`'s two cases and the per-end `hlas`, `hlbs`, `hpt0`, `hpt1`
  (one proof each), the heights' lift (two sites, two rewrites).
- **F-318** · L · repeated derivations, and derivable or unused hypotheses and `have`s, in
  `Molecular/Molecule/Pencil/MainComponent/SplitOff.lean`, `Coverage.lean` and `CoverageChain.lean`.
  Derivable hypotheses: the `hinj` of `Graph.planeDiff_eq_zero_of_splitOff` and
  `Graph.X0Attains.of_splitOff` (a map out of `Fin 1` is injective); the `hab` of
  `Graph.X0Attains.of_splitOff`, from `hδ` (at `a = b` the merged deficiency is the deficiency); and
  the `_hv` of `Graph.IsX0Graph.exists_isChain`, which its proof never reads and `hdeg` gives (a
  body of degree two is an end of a link). Unused: in
  `Graph.finrank_span_rigidityRows_splitOff_special`, the `obtain` of `Graph.splitOff_oneEar` (none
  of its conjuncts is read) and `he01`, with `hab'`, which only `he01` reads. Repeated derivations:
  the three theorems of `SplitOff.lean` open with the same facts about the ear (`hx0`, `hax`, `hbx`,
  `hV₁G`, `l0`, `l1`; `l''` and `hVG''` in two of them); `hpd` (the incidence functional as a
  difference of two dot products) is derived in `Graph.planeDiff_eq_zero_of_splitOff` and in
  `Graph.X0Attains.of_splitOff`, and `hends2` (the selector relinked at `e 0`) in
  `Graph.finrank_span_rigidityRows_splitOff_special` and in `Graph.X0Attains.of_splitOff`, whose
  `hdeg2` (the ear body's links are `e 0` and `e 1`) is `Graph.IsOpenEar.isLink_interior`
  (`Coverage.lean`, downstream) at one body. The first path edge (`Graph.IsOpenEar.isLink_first`) is
  derived again as `h0` in `Graph.IsOpenEar.adj_mem_of_adj_of_degree_eq_two`,
  `Graph.IsOpenEar.exists_isLink_of_degree_eq_two` and
  `Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two`, and the last (`Graph.IsOpenEar.isLink_last`)
  as the latter's `hlast` (`ear_isLink_first` and `ear_isLink_last`, `Ear.lean`, state them on
  `hpath` with the interior body named); the latter's `hg0` repeats that of
  `Graph.IsOpenEar.adj_mem_of_adj_of_degree_eq_two`; `1 ≤ m` (`hm`) is derived in
  `Graph.IsX0Graph.exists_isChain` and `Graph.IsX0Graph.x0Reduces_of_forall_degree_eq_two`;
  `x i ≠ a` and `x i ≠ b` (`hax`, `hbx`, `hxa`, `hxb`) are derived from `notMem` five times; and
  `Graph.X0Attains.of_isX0Graph_of_x0Reduces` writes `Graph.X0Below` out in `hcov`. `lake lint`
  reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: `hinj` and `hab` derived from
  the others and the two theorems applied without them, `exists_isChain` applied with `v ∈ V(G)`
  derived from `hdeg`, `Graph.finrank_span_rigidityRows_splitOff_special`'s proof without the
  `obtain`, `hab'` and `he01`, and `of_isX0Graph_of_x0Reduces` applied to `hcov` stated with
  `Graph.X0Below`, on the standard axioms or fewer (`scratch/reconcile-lean/t3718/Hyps-t3718.lean`,
  gitignored).
  *Found:* RECONCILE round 3 task 37.18.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.26). Task 38.1: drop the `hinj` of
  `planeDiff_eq_zero_of_splitOff` and `X0Attains.of_splitOff` (`Fin 1`), `of_splitOff`'s `hab`
  (`F-317`'s lemma), `IsX0Graph.exists_isChain`'s `_hv` (from `hdeg`; caller `exists_additiveCore`),
  and in `finrank_span_rigidityRows_splitOff_special` the unused `obtain` of `splitOff_oneEar`,
  `he01` and `hab'`; `h0` and `hlast` by `IsOpenEar.isLink_first`, `isLink_last` (or
  `ear_isLink_first`, `_last`); `lem:pencil-splitoff-flexes`, `thm:pencil-x0-splitoff`,
  `lem:pencil-x0-chain-exists` restated where they state them. Left: the ear facts the three
  theorems of `SplitOff.lean` open with, `hpd` and `hends2` (two sites each), `hdeg2` (its lemma is
  downstream), `hg0`, `hm`, the five `x i ≠ a`, and `hcov`'s unfolded `X0Below` (a change of form).

- **F-319** · L · repeated derivations, and derivable or unused hypotheses, in
  `Molecular/Molecule/Pencil/MainComponent/CoverageCut.lean`, `CoverageTheoremS.lean` and
  `GoodEar.lean`. Derivable hypotheses: the `hne` of `Graph.IsX0Graph.splitOff`, from `h₁`, `h₂` and
  `huw` (a label links `v` to one body), which each of its four callers
  (`Graph.IsOpenEar.isX0Graph_splitOff_four`, `_three`, `_orbit` and `_one`) derives in four or five
  lines; the `hv` of `Graph.IsX0Graph.x0Reduces_of_not_connected`, from `hdisc` and connectivity
  (for `v ∉ V(G)`, `G − v` is `G`); and the `hyu`, `hwy` and `hwu` of
  `Graph.exists_closedEar_two_of_triangle`, from `huy`, `hyw` and `huw` (adjacent bodies of a simple
  graph are distinct). Unused: the `_hG` of `Graph.IsOpenEar.deficiency_three_induce_cycle`, which
  its proof never reads. Repeated derivations: `Graph.IsOpenEar.isX0Graph_splitOff_four` and
  `_three` are one proof at `Fin 4` and at `Fin 3`; `Graph.IsChain.isX0Graph_induce` writes out the
  two ends (`y = a`, `y = b`) twice; the maximality step (a body outside a maximal set of deficiency
  zero with two neighbours in it would enlarge it) is derived in
  `Graph.IsX0Graph.x0Reduces_of_deficiency_two_rigid` and in
  `Graph.IsX0Graph.exists_additiveCore_of_rigid`; that a body of degree two of a loopless graph has
  two non-loop links, in `Graph.IsX0Graph.two_mul_ncard_le_ncard_edgeSet` and
  `Graph.IsX0Graph.partitionDef_three_induce_diff_nonpos`; `k < 3` from a chain that is not usable,
  twice in `Graph.IsX0Graph.exists_additiveCore`; `x i ≠ a` and `x i ≠ b` again in
  `Graph.IsOpenEar.deficiency_three_induce_cycle` (`F-318`'s five); and in
  `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`, the singleton-value step at `W₀ \ {y}`
  (`ht2`'s `h` and the one-body ear's `hins`), the degree two of a body that is not a pencil hub
  (`hy2`, `hu2`), and the link count at a pair (the `hone` of `Graph.exists_eq_triple_of_minimal`,
  again in `hW₀3`). `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies); a `lake lean` witness: `hne`, `hv` and the three
  distinctness hypotheses derived from the others and the three theorems applied without them, and
  `deficiency_three_induce_cycle`'s proof without `_hG`, on the standard axioms or fewer
  (`scratch/reconcile-lean/t3719/Hyps-t3719.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.19.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.27). Task 38.1: drop
  `IsX0Graph.splitOff`'s `hne` (from `h₁`, `h₂`, `huw`; `lem:pencil-x0-chain-standing` restated
  where it states it; its four callers' 4–5-line derivations go),
  `IsX0Graph.x0Reduces_of_not_connected`'s `hv` (`lem:pencil-x0-cut-reduces`; caller
  `IsX0Graph.x0Reduces`), `exists_closedEar_two_of_triangle`'s `hyu`, `hwy`, `hwu`
  (`lem:pencil-rigid-good-ear`; caller `exists_oneEar_or_pendantTriangle`) and
  `IsOpenEar.deficiency_three_induce_cycle`'s `_hG` (unpinned; caller `exists_additiveCore`). Left:
  `isX0Graph_splitOff_four`, `_three` (one proof at `Fin 4` and `Fin 3`; a lemma at any `k` needs a
  new proof); the two ends in `IsChain.isX0Graph_induce`, the maximality step, the two non-loop
  links, `k < 3`, `x i ≠ a`, and `exists_oneEar_or_pendantTriangle`'s steps (two sites each, or one
  proof).

- **F-320** · L · repeated derivations, and unused steps, in
  `Molecular/Molecule/Pencil/MainComponent/GenericBase.lean` and `GenericEar.lean`. Unused: the
  `have hloopless` of `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization` and
  the `have hloop` of `Graph.IsOpenEar.hasGenericPencilRealization_of_one`, as the instance
  `[G.Simple]` gives `G.Loopless`. Repeated derivations:
  `not_linearIndependent_of_dotProduct_eq_zero_pair` (three vectors orthogonal to two independent
  vectors are dependent) is derived again inside `not_pencilNondegFeasible_of_triangle_two_hubs` and
  `not_isNondegPencilRealization_of_two_hubs_three_common` (`Molecule/Pencil/Motive.lean`, which
  `GenericEar.lean` imports), and `exists_mem_perp_pair_linearIndependent` builds the same space
  `n_a^⊥ ∩ n_b^⊥`, with its dimension and its membership, once more; the ear facts (`a, b ∈ V₁`,
  `x 0 ∉ V₁`, `x 0 ≠ a, b`, `a ≠ b`, the two links) and that `x 0` is not a hub, in both theorems of
  `GenericEar.lean`; the five reorderings of the three independent points in the extension, each by
  `comp` and `convert`; in the extension, the case analysis of the links at `e 0` and at `e 1`,
  written twice (`hcls`), and one case analysis bounding the closed hub-neighbourhood and the closed
  neighbourhood of `x 0`, written twice; in `GenericBase.lean`, the two branches of
  `addTwoEar_deficiency` with one new crossing link (at `u` and at `w`), `a ∉ V(G)` from
  `some a ∉ V(G_{uw})` and the new body's membership twice each in `finrank_ker_inf_planeDiff_le`,
  the split on zero, one or two members at a hub and again at a body that is not a hub in
  `isNondeg_pencilConfig_of_planeDiff`, and the three families of polynomials of
  `hasGenericPencilRealization_of_forall_deficiency_two_ne_zero'`, each with the constant `1` at an
  index outside its condition. `lake lint` reports none of them.
  *Evidence:* read (the statements and bodies, and `Motive.lean`'s two lemmas); a `lake lean`
  witness: both theorems' proofs run without the two `have`s, on the standard axioms; the same test
  found the `have : G.Simple` of `hasGenericPencilRealization_of_forall_deficiency_two_ne_zero'`
  needed (`hl.ne` asks `G.Loopless`) (`scratch/reconcile-lean/t3720/Hyps-t3720.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.20.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.27). Task 38.1: remove the unused
  `have hloopless` and `have hloop` of `GenericEar.lean`'s two theorems; move
  `not_linearIndependent_of_dotProduct_eq_zero_pair` to `Pencil/Motive.lean` and call it in
  `not_pencilNondegFeasible_of_triangle_two_hubs` and
  `not_isNondegPencilRealization_of_two_hubs_three_common`, for their perpendicular space and its
  count (~15 lines each). Left: `exists_mem_perp_pair_linearIndependent` (it builds a member, not a
  bound), the ear facts and reorderings of the two theorems, the case analyses written twice in one
  proof, and `GenericBase.lean`'s per-branch steps and three polynomial families.

- **F-321** · L · repeated derivations, and unused or derivable hypotheses and `have`s, in
  `Molecular/Molecule/Pencil/MainComponent/GenericTriangle.lean` and `Statements.lean`. Unused: the
  `hS` of `not_pencilHub_of_closedEar_two`, which its proof reads only in a `have := hS` and a
  `have hloop` that it does not need, and the `have := hS` of
  `hasGenericPencilRealization_of_closedEar_two_of_isNondegPencilRealization` and of
  `hasGenericPencilRealization_of_closedEar_two`. Derivable: the `hinj` of those two theorems, from
  simplicity and `hpath 1` (`x 0 ≠ x 1`, as `e 1` is no loop), as `F-317`'s at `Fin 2`. Repeated
  derivations: the facts of the closed ear (`x 0 ≠ c`, `x 1 ≠ c` and `x 0 ≠ x 1` from `hxV₁`, `hc`
  and `hinj`, and the three links `l0`–`l2`) in `isLink_cases_of_closedEar_two`,
  `not_pencilHub_of_closedEar_two`, the extension and the assembly; the statement of
  `isLink_cases_of_closedEar_two` written out again as `hcls` in `not_pencilHub_of_closedEar_two`
  and the extension, and its case analysis done again in the assembly's `hfree`; in the extension,
  six pairs and two reorderings of the three independent points, each by `comp` and `convert`, and
  the two orientations of each edge of the triangle by two identical lines in `hreal`; `hjoin_ne`,
  `hinPanel` and `hthruPt` (a join of two independent points is nonzero, lies in a panel that
  contains both, and passes through both), derived again in
  `Graph.IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization` (`GenericEar.lean`)
  and, one hinge at a time, in `pencilPair_of_simple_ncard_eq_three`; the rank of a rigid triangle
  from `BodyHingeFramework.theorem_55_cycle` and
  `BodyHingeFramework.isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`, in the
  extension (`hrig`, `hside₂`) and in `pencilPair_of_simple_ncard_eq_three` (`hrig`, `hbridge`); in
  `pencilPair_of_simple_ncard_eq_three`, the relabellings `hVeqyzx` and `hVeqzxy` of `V(G)`, the
  three distinctness proofs of the labels, the independence of the three points twice (`hLI3`,
  `hgen`) and one case split twice (`hsupp_ne`, `hsupp_panel`); in `Statements.lean`, the standing
  hypotheses that `hasGenericPencilRealization_of_IH` builds field for field as
  `Graph.X0Attains.of_twoEdgeConnected` does (`CoverageTheoremS.lean`), its `hS₁` twice, and at the
  pendant triangle a seven-line `hlt` where the one-body ear has `Graph.IsOpenEar.ncard_lt`; and
  `pencilPair_of_IH`, which is `pencilPair_of_X0`'s proof (`X0.lean`) line for line, with
  `hasGenericPencilRealization_of_IH` for `X0Gen` and `x0Dist` for `X0Dist`. `lake lint` reports
  none of them.
  *Evidence:* read (the statements and bodies, and those of `GenericEar.lean`'s extension,
  `pencilPair_of_X0` and `Graph.X0Attains.of_twoEdgeConnected`); a `lake lean` witness: the proofs
  of the three theorems run without their `have`s (`not_pencilHub_of_closedEar_two`'s without
  both), and `hinj` derived from `hS` and `hpath`, with the three theorems applied without it, all
  on the standard axioms (`scratch/reconcile-lean/t3721/Hyps-t3721.lean`, gitignored).
  *Found:* RECONCILE round 3 task 37.21.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.27). Task 38.1: drop
  `not_pencilHub_of_closedEar_two`'s `hS` with its `have := hS` and `have hloop` (unpinned; callers
  the two theorems), the two theorems' `have := hS`, and their `hinj` (`F-317`'s lemma at `Fin 2`;
  `lem:pencil-generic-pendant-triangle` restated where it states it; caller
  `hasGenericPencilRealization_of_IH`); `hjoin_ne`, `hinPanel` and `hthruPt` as lemmas on
  `pointJoin` beside it (`Flat.lean`), at the extension,
  `IsOpenEar.hasGenericPencilRealization_of_isNondegPencilRealization` and
  `pencilPair_of_simple_ncard_eq_three`. Left: the closed ear's facts, `hcls`, the reorderings and
  orientations (per site, each proof's locals), the rigid triangle's rank (two sites),
  `pencilPair_of_simple_ncard_eq_three`'s relabellings and splits (one proof), `Statements.lean`'s
  standing hypotheses and `hlt`, and `pencilPair_of_IH` (16 lines, `pencilPair_of_X0`'s with other
  inputs).
- **F-322** · L · the `@[nolint …]` and `set_option linter.* false` sites that `CLEANUP.md` §B's
  suppression screen finds unneeded, unjustified or curable by `TACTICS-QUIRKS.md` §115's rule 1.
  The `@[nolint unusedArguments]` of `Graph.BodyBarFramework.finrank_realBlockPiSpanOn`
  (`BodyBar/TayTheorem.lean`) and of
  `BodyHingeFramework.exists_independent_panelRow_subfamily_of_le_finrank`
  (`AlgebraicInduction/GenericityDevice.lean`), whose comments call the report a false positive of
  the `Fintype.ofFinite` bridge: copies without the attribute lint clean, as the linter sees each
  `Finite` binder used, and a copy of each without one of them fails. That of
  `BodyHingeFramework.trivialMotions` (`RigidityMatrix/Basic.lean`), whose docstring says the
  attribute is for `_F`: Batteries' `unusedArguments` already skips an argument named with `_`. The
  `set_option linter.style.longLine false in` of
  `PanelHingeFramework.hasGenericFullRankRealization_of_couple_blockTriangular_ofNormals_set_kdof`
  (`CaseI.lean`), with no comment, for its header line, 102 columns because of the name. The
  `set_option linter.unusedDecidableInType false in` of `rankHypothesis_of_theorem_55_d3`,
  `theorem_55_6_multigraph_gen` and `theorem_55_6_multigraph_d3` (`Theorem55.lean`; the last's
  docstring does not justify it), `exists_molecular_rankHypothesis_generalPosition`
  (`Modelling.lean`), and `exists_rankHypothesis_isGeneralPosition4_of_two_le` and
  `exists_rankHypothesis_isGeneralPosition4` (`Theorem56.lean`): each `[DecidableEq β]` the type
  does not use, which `classical` supplies (§115 rule 1: drop it). And the two
  `set_option linter.unusedFintypeInType false in` of `Pencil/MainComponent/GenericBase.lean`:
  `exists_mem_forall_eval_ne_zero`'s `[Fintype ι]`, where `[Finite ι]` and the bridge do
  (`DESIGN.md` *Typeclass shape for finiteness on `V`*), and
  `hasGenericPencilRealization_of_forall_deficiency_two_ne_zero'`, whose one caller, the pin
  `Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`, only bridges its
  `[Finite α]` to it. The others are justified or another entry's: the two `IsInfinitesimallyRigid`
  contract guards (`Framework.lean`, `BodyBar/Framework.lean`; the linter reports both), the
  `openClassical` of `Bricks.lean`, `F-286`'s two `nolint`s, the `unusedDecidableInType` of
  `F-281`, `F-282`, `F-283` and `F-285` and `F-298`'s four, `F-323`'s three, and the `nolint`s of
  `Matrix.rank_ge_of_isUnit_mul_reindex_fromBlocks` and `edgeRowSplit_corner_card`, which task
  38.5 deletes.
  *Evidence:* read (the sites, their comments and bodies; Batteries' `unusedArguments`); a `lake
  lean` witness: copies of the declarations linted with `#lint only unusedArguments`, the two
  contract guards reported and the other three not, a control with an unused `[Finite α]`
  reported, and the copies without `[Finite β]` (the first) and `[Finite α]` (the second) failing
  (`scratch/reconcile-lean/t38/Nolint1.lean` to `Nolint3.lean`, gitignored); rule 1's statements
  follow from the theorems under `classical`, as `F-323`'s witness shows for three of them.
  *Found:* RECONCILE round 3 task 38.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.10).
- **F-325** · L · a derivable hypothesis of
  `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking_set_proj`
  (`AlgebraicInduction/Coupling.lean`, unpinned): `hr : r ∈ V(G)` follows from
  `hinter : V(G) ∩ proj = {r}`, now that the proof calls the pinned
  `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton`, which takes `hinter` alone; the
  proof uses `hr` only for `⟨r, hr⟩`. Its one caller,
  `rigidContract_exterior_rank_transport_htransport`, passes `hr'`, which it would no longer need.
  *Evidence:* read (the statement and body); a `lake lean` witness: the lemma called with
  `(hinter.ge (Set.mem_singleton r)).1` for `hr`, on the three standard axioms
  (`scratch/reconcile-lean/t383/Hyps-t383.lean`, gitignored).
  *Found:* RECONCILE round 3 task 38.3.
  *Disposition:* open (`notes/Reconcile-lean-cleanup.md`, task 38.16).

## M — mathematics and sources

- **F-025** · M · the credit for "row-independent iff $(2,3)$-sparse" (`rigidity-matroid.tex`,
  `laman-theorem.tex`, `intro.tex`; Lean docstrings): the blueprint credits Lovász–Yemini 1982 with
  the planar identification "an edge set is row-independent at a generic framework iff it is
  $(2,3)$-sparse": the titles of `thm:edgeSet-rowIndependent-iff-isSparse`,
  `thm:rigidityMatroid-indep-iff-rowIndependent` and `thm:linearRigidityMatroid-eq-rigidityMatroid`,
  `rigidity-matroid.tex`'s opening ("the classical strategy of Lovász–Yemini", for Jordán's proof of
  his Theorem 2.2.1), `intro.tex`, and docstrings in `RigidityMatroid.lean`, `LamanTheorem.lean`,
  `MatroidIdentification.lean` and `LinearRigidityMatroid.lean`. Jordán (2016, p. 45) credits the
  characterization to Laman (Theorem 2.2.1, his [43]) and proves it by induction with extensions; he
  credits Lovász–Yemini with the rank formula (Theorem 2.3.2, p. 49) and with the rigidity of
  6-connected graphs (Theorem 2.4.1, p. 51). Tasks 5.7 and 5.8 moved `laman-theorem.tex`'s credit
  to Laman (5.8: the opening, and the title *Sparsity from row-independence*). Task 5.9 credited
  Laman in `rigidity-matroid.tex`'s lifts lead-in and dropped "the pendant attachment used by
  Lovász–Yemini". Task 5.10 moved that credit into the chapter's new opening (Jordán's Theorem
  2.2.1, credited to Laman, and his proof, p. 45) and retitled the three nodes (*Row-independence
  in the plane is $(2,3)$-sparsity (Laman)*, *Independent sets of the planar rigidity matroid*,
  *The planar rigidity matroid as a linear matroid*), so `rigidity-matroid.tex` no longer names
  Lovász–Yemini. `count-matroid.tex` never named them, and task 5.11 added no such credit (it credits
  the count matroid to Lorea and to White–Whiteley, as Whiteley 1996 Proposition A.1.1 and Lee–Streinu
  do). Outside round 1's slices: `intro.tex`, the docstrings,
  `formalization.yaml`'s Lovász–Yemini lines, and `notes/BlueprintExposition.md`'s Group-A line
  "Lovász–Yemini easy direction" for `lem:isSparse-of-rowIndependent-two` (task 6 moved its credit,
  and the Phase-7 line's beside it, to Laman).
  *Evidence:* read (Jordán 2016 pp. 45, 49, 51, in `.refs/`; a `grep` for "Lov" over the blueprint
  and the Lean). Lovász–Yemini 1982 was not in `.refs/` then; RECONCILE round 1 task 5 read it
  (pp. 91–98), with the statements and bodies of the four pins and of
  `IsSparse.exists_rowIndependent_placement`.
  *Found:* round 1 task 5.7.
  *Disposition:* done (task 27): the docstrings credit Laman, with Pollaczek-Geiringer (task 25,
  the planar files), and `BodyBar/TayTheorem.lean`'s converse section no longer calls its rank
  bound "Lovász–Yemini-style" (task 27); reported (`notes/Prose-report.md`, M2); round 1: the
  verdict. LY credit the
  characterization to Laman themselves: their abstract gives "a new proof of Laman's theorem" (p.
  91); Theorem 1, the generic degree of freedom $2n - 3 - \min \sum (2|V(G_i)| - 3)$ over covers, is
  "a slight generalization of a theorem of Laman", with "an independent proof" (p. 92); Corollary
  1 derives from it that $G$ is generic independent iff $2|V(Y)| - 3 \ge |Y|$ for every $Y \subseteq
  E(G)$ (read for nonempty $Y$; p. 93, proof p. 96); Corollary 3 is "the theorem of Laman" (pp.
  93–94). Their own are Theorem 1 (Jordán's 2.3.2, p. 49), Theorem 2, 6-connected graphs are rigid
  (p. 94; Jordán's 2.4.1, p. 51), and Theorem 4; Theorem 1's proof (pp. 95–96) applies Lovász's
  hyperplane formula (their Theorem 3, p. 95), with no induction. Jordán agrees. The pins:
  `edgeSet_rowIndependent_iff_isSparse_dim_two` is Corollary 1 (Jordán's 2.2.1) with "some
  placement" for "generic"; `isSparse_of_edgeSetRowIndependent_dim_two` its necessity half, by the
  rank bound at a placement with no three points collinear (Jordán p. 45); the two matroid
  identities its packagings; the sufficiency half inducts on $|V|$ by reverse Henneberg moves,
  Jordán's proof (p. 45), not LY's. No declaration states LY's Theorems 1–2. So Laman is credited;
  LY is cited for Corollary 1, `independently-proves`; no LY "presentation we follow" credit (the
  presentation followed is Jordán's, credited). Fixed: `formalization.yaml` (the LY `sources`
  entry, `status.scope`, the linear-matroid row's description, `alignment`'s source), ROADMAP (the
  layout line, the Phase 7 row and heading, §6's and §7's texts, *References*), `DESIGN.md`'s two
  (b408df1a). The docstrings were round 3's, `BodyBar/TayTheorem.lean`'s among them.
- **F-053** · M · the credit for the matroid of a submodular function, the polymatroid rank formula
  and the union's rank formula (`matroid-union.tex`, `intro.tex`, `deficiency.tex`,
  `molecular-induction.tex`; Lean docstrings). The blueprint credited the first two to Edmonds 1970.
  Oxley (2011, §11.1, pp. 404–407) credits Proposition 11.1.1, Corollary 11.1.2 and Proposition
  11.1.7 to Edmonds and Rota (1966, an abstract), and Schrijver (*Combinatorial Optimization*,
  §44.6a, p. 775) says the result was "announced by Edmonds and Rota [1966] and proved by Pym and
  Perfect [1970]"; both cite Edmonds 1970 for polymatroids. Edmonds 1965's Theorem 1 is the
  partition criterion for $k$ copies of one matroid (p. 69), not a rank formula; Oxley (§11.3, p.
  427) credits the union to Nash-Williams 1966, and Schrijver (§42.1, pp. 725–726) its rank formula
  to Nash-Williams [1967] and, for several matroids, Edmonds [1968]. Task 2.1 moved the chapter's
  credits accordingly, with Oxley as the pointer, and retitled `thm:matroid-partition-rank` *The
  rank of a matroid union*. Outside the slice: `intro.tex`'s Phase-12 item (round 4);
  `deficiency.tex`'s "Edmonds matroid-partition rank formula" and `molecular-induction.tex`'s
  "(Nash--Williams, Edmonds [edmonds1965])" (tasks 2.10 and 2.11–2.12); the docstrings of
  `Submodular.lean`, which cite Oxley's numbers and page 406 as Edmonds 1970's, and of `Union.lean`,
  which credit Edmonds 1965 with the rank formulas.
  *Evidence:* read (Oxley 2011 pp. 404–407, 411–412, 416, 427–430; Schrijver pp. 725–726, 775;
  Edmonds 1965 p. 69; all in `.refs/`). Edmonds 1970 and Nash-Williams 1966 are not in `.refs/`.
  *Found:* round 2 task 2.1.
  *Disposition:* done (task 29.1): the docstrings of
  `Submodular.lean` and `Union.lean` credit the matroid of a submodular function and the
  polymatroid rank formula to Edmonds and Rota with Oxley's numbers as Oxley's, the union to
  Nash-Williams, its rank formula to Nash-Williams and Edmonds, and Edmonds 1965's Theorem 1 as
  the partition criterion (`Union_pow_indep_iff_count`), as `TreePacking.lean`'s
  `Union_pow_rank_eq` now does (task 27); `Molecular/Deficiency.lean`'s header without "the
  Edmonds-optimal `Y₀`" (task 29), and its "Edmonds matroid-partition rank formula" the rank of a
  matroid union, `thm:matroid-partition-rank` (task 29.1); the four chapters already credit them
  so; reported (`notes/Prose-report.md`, M4).
- **F-081** · M · the credit for KT eq. (2.4), $\operatorname{rank} M(\tilde G) +
  \operatorname{def}(\tilde G) = D(|V|-1)$ (`thm:def-eq-corank`): the blueprint credited it to
  Jackson and Jordán's Theorem 6.1, "whose Corollary 6.2" is the deficiency-zero case. JJ 2009's
  Theorem 6.1 (p. 582) is the maximum rank of a body–bar-and-hinge realization and Corollary 6.2
  (p. 583) its infinitesimally rigid case. The identity is their Theorem 4.1(a) (pp. 580–581, the
  largest union of $k$ forests, given as well known with Nash-Williams 1961 and 1964 and Tutte
  1961) applied to $\tilde G$; KT observe it from their Proposition 2.3 (pp. 655–656). Task 2.10
  credits `deficiency.tex` accordingly. Outside the slice: `intro.tex`'s Phase-19 item (round 4);
  `formalization.yaml`'s JJ 2009 reference and main-results row ("Thm 6.1 / Cor 6.2 (def = corank
  bridge)"); the docstrings of `rank_add_deficiency_eq`, `isBase_ncard_add_deficiency_eq`,
  `le_rank_add_deficiency`, and `deficiency_eq_zero_iff_exists_spanningTrees` (JJ Corollaries 6.2
  and 6.3, about realizations, for KT Proposition 2.2 at $\tilde G$).
  *Evidence:* read (JJ 2009 pp. 580–583; KT 2011 pp. 655–656; both in `.refs/`; the docstrings).
  *Found:* round 2 task 2.10.
  *Disposition:* done (task 29.1): `Molecular/Deficiency.lean`'s header credits KT eq. (2.4),
  without "Jackson–Jordán 2009 Thm 6.1 / Cor 6.2" (task 29); `rank_add_deficiency_eq` and
  `isBase_ncard_add_deficiency_eq` credit KT eq. (2.4) (p. 655), observed from their Proposition
  2.3, and the first Jackson and Jordán's Theorem 4.1(a) (2010, p. 580) with its credit to
  Nash-Williams and Tutte, `le_rank_add_deficiency` and its section no "Jackson–Jordán min–max
  content", and `deficiency_eq_zero_iff_exists_spanningTrees` KT Proposition 2.2 at `G̃` (task
  29.1); `intro.tex` and `formalization.yaml` already credit it so; reported
  (`notes/Prose-report.md`, M4).
- **F-118** · M · the route of Cases I–III (`algebraic-induction/case-i.tex` … `case-iii.tex`): the
  prose presents as steps of the induction several nodes that no main result's proof takes. Every
  pin of these nodes lies outside every main result's closure, and the pins of the live nodes that
  cite them do not reach them. Seven proofs use and cite `lem:genericity-device` (`F-117`) as the
  step that re-realizes a rank at a general-position seed; the pins of `lem:case-I-realization`,
  `lem:case-I-realization-h65` and `lem:case-II-realization` reach the rank polynomials instead
  (`lem:rank-polynomial-IH-relabel-proj`, `lem:rank-polynomial-of-le-finrank`), and
  `lem:case-III-chain-dispatch`'s through `lem:case-III-chain-discriminator`.
  `lem:case-I-dispatch` cites KT Lemma 6.2's `lem:case-I-realization-nonsimple`, and
  `thm:theorem-55` the Case II accounting `lem:case-II`; neither pin reaches them.
  `lem:case-III-chain-dispatch`'s proof cites the eq. (6.12) placement
  `lem:case-II-realization-placement` and the relabel lemmas `lem:splitOff-ofNormals-relabel` and
  `lem:splitOff-rigidityRows-relabel`; its pin reaches none of them, nor the candidate completion
  `lem:case-III-candidate-row`, through which the subsection says Case III supplies its missing
  row. Case I's crux accounts run through two more such nodes, `lem:claim-6-4` and
  `lem:case-I-splice-seed`. Of the 48 nodes in these files with every pin dead (`F-012`), the
  $d = 3$ instances and the off-route worked cases are dead by design; these are not.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter` and `--label`, dead pins and edges
  with no Lean basis; TeX and Lean at `ef57b401`).
  *Found:* round 3 task 1.
  *Disposition:* done (tasks 15–18; reported as `notes/Prose-report.md` M3, and the PI chose to keep
  KT's route, explained): the twelve `\cref`s of `lem:genericity-device` say which argument they
  borrow, three of them now citing the minor of `lem:rank-polynomial-of-le-finrank` (`daa53665`); Case
  I's group, `lem:claim-6-4` and `lem:case-I-splice-seed` among it, framed by `rem:case-I-kt-steps`
  (`e6f1e425`); Case II's group, `lem:case-II` and `lem:case-II-realization-placement` among it,
  framed by `rem:case-II-kt-steps` (`04b33020`); Case III's group, the candidate completion and the
  relabel lemmas among it, framed by `rem:case-III-kt-steps`, and `lem:case-III-chain-dispatch`'s
  note names the argument of each citation (`98f89445`).

- **F-222** · M · `cor:bodyhinge-generic-tree-packing`, as `body-hinge.tex` cites it: after
  `thm:body-hinge-tay` the chapter says that for frameworks "with hinges in general position", KT
  Proposition 1.1's form (a multigraph $G$ has an infinitesimally rigid body-hinge framework if and
  only if $\tilde G$ contains $D$ edge-disjoint spanning trees) "is" the corollary, and the note
  after `def:body-hinge-framework` calls it "the rigidity statement for frameworks with hinges".
  The corollary and its pin are for simple graphs with $|V| \ge 2$, $d \ge 2$ and an infinite
  field, at generic hinge-point assignments; for multigraphs the formalization has only the
  existence form for bundles of bars (`F-048`). The chapter is round 2's, outside this round's
  surface. Candidates: add "for simple graphs" there, or prove the multigraph form (JJ Theorem 6.1
  holds for multigraphs; the formal witness, KT Theorem 5.6 with nondegenerate hinges, is for
  simple graphs).
  *Evidence:* read (`body-hinge.tex`, the note after `def:body-hinge-framework` and the paragraph
  after `thm:body-hinge-tay`; the statement of
  `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`; JJ 2010 §6, p. 582).
  *Found:* round 4 task 2.12.
  *Disposition:* reported (`notes/Prose-report.md`, M1); round 1: `body-hinge.tex`'s two passages
  say the corollary is for simple graphs, with the rest of its pin's scope (at least two vertices,
  every body a vertex, an infinite field, the fresh-label supply by pointer), and that for
  multigraphs the formalization has the theorem for bundles of bars (b72c0202). Not "only":
  `thm:theorem-55-6-multigraph` realizes every spanning multigraph with nonzero hinges. The
  multigraph generic form is `RECONCILE-FORMAL`'s (b).
- **F-228** · M · the credit for Laman's theorem (`intro.tex`, `laman.tex`, `laman-theorem.tex`,
  `henneberg.tex`; `README.md`, `home_page/index.md`): the blueprint credits the characterization of
  the generically rigid graphs in the plane to Laman 1970 alone, as Jordán 2016 does (Theorems 2.2.1
  and 2.2.2, p. 45). Recent literature also credits it to H. Pollaczek-Geiringer, *Über die
  Gliederung ebener Fachwerke*, ZAMM 7(1) (1927), 58–72 (DOI `10.1002/zamm.19270070107`, Crossref
  checked), as the Pollaczek-Geiringer–Laman theorem. Neither paper is in `.refs/`, and the 1927
  paper's content was not read. Candidate: read it, then credit both where the blueprint names the
  theorem's originator.
  *Evidence:* suspected (the 1927 paper's content); read (Crossref's record for the DOI; Jordán 2016
  p. 45). The 1927 paper was not in `.refs/` then; RECONCILE round 1 task 6 read its page images
  (pp. 58–72, in German), Crossref's record again, and the reference lists of Jordán 2016 and LY
  1982.
  *Found:* round 4 task 2.14.
  *Disposition:* done (211e2737; reported, `notes/Prose-report.md`, M5). The verdict: **the paper
  states and proves the characterization.** Its theorem (p. 60): "Notwendig und hinreichend dafür,
  daß ein Fachwerk von $k$ Knoten und $(2k-3)$ Stäben brauchbar sei, ist, daß es kein Teilsystem von
  $l$ Punkten $(4 \le l < k)$ enthält, die durch mehr als $(2l-3)$ »innere« Stäbe mit einander
  verbunden sind" (for a framework with $k$ joints and $2k-3$ bars to be *usable* it is necessary
  and sufficient that it contain no subsystem of $l$ points, $4 \le l < k$, joined among themselves
  by more than $2l-3$ "inner" bars); p. 64, the *Hauptsatz* with its converse: "Ein komplettes
  ebenes $F_k$ ist dann und nur dann brauchbar, wenn es anhäufungsfrei ist" (a complete planar $F_k$
  is usable if and only if it has no accumulation), "das gewünschte einfache, rein abzählende
  Kriterium" (the desired simple, purely counting criterion). *Usable* is the generic notion: "Wir
  wollen eine Gliederung brauchbar nennen, wenn sie mindestens eine Realisierung durch ein starres
  Fachwerk besitzt" (we call a structure usable if it has at least one realization by a rigid
  framework), algebraically "wenn es irgend ein Wertesystem $x_1 y_1, \dots x_k y_k$ gibt, für
  welches die Matrix den Rang $s$ hat" (if there is some system of values for which the matrix, the
  rigidity matrix, has rank $s$; both p. 63); rigid is rank $2k-3$ (p. 59), where she separates a
  determinant vanishing at special positions (a hexagon's six points on a conic) from one vanishing
  "bei jeder Wahl dieser Koordinaten" (for every choice of the coordinates). So it is Jordán's
  Theorem 2.2.2 with "some placement" for "generic", the project's form, for simple graphs (bars
  join pairs of points, $s \le \binom k2$, p. 61; $l < 4$ is dropped as $\binom l2 = 2l-3$ for $l =
  2, 3$, p. 64). §8 (p. 70) extends the sufficiency to $2k-3-\nu$ bars, *usable* now meaning rank
  $s$: "Ein Gebilde $F_k^{(\nu)}$ $(\nu \ge 0)$ von $k$ Knoten und $2k-3-\nu$ Stäben hat nicht mehr
  als $\nu$ in der Gliederung begründete Beweglichkeiten, d. h. es ist im verallgemeinerten Sinne
  brauchbar, sofern es keine Anhäufung besitzt" (… has no more than $\nu$ mobilities founded in its
  structure, i.e. is usable in the generalized sense, if it has no accumulation): the hard half of
  the independence form (Jordán's 2.2.1, LY's Corollary 1), which "zeigt, daß Anhäufung tatsächlich
  das einzige Vorkommnis ist, das bei ebenen Fachwerksgebilden Unbrauchbarkeit hervorruft" (shows
  that accumulation is indeed the only thing that makes planar frameworks unusable, p. 70); the
  converse is the count she calls "sehr leicht zu sehen" (very easy to see, p. 64, stated for
  complete frameworks). The proof (pp.
  64–68) inducts on the number of joints from the triangle: a vertex of degree two is removed and
  put back off its neighbours' line (p. 65); one of degree three is removed, a bar inserted between
  two neighbours that a lemma on complete subsystems keeps free of accumulations (§4, pp. 65–67),
  and put back off a "gefährlicher Ort", a conic (§5, pp. 67–68): the reverse Henneberg moves of
  Jordán's proof (p. 45), which the project follows. §7 (pp. 69–70) derives the construction: the
  complete usable frameworks are those built from the triangle by the two moves. Neither Jordán nor
  LY cites her (their reference lists). Crossref: ZAMM 7(1) (1927), 58–72, Wiley; the scan's header
  "Band 7, Heft 1, Februar 1927". Credited beside Laman, the theorem keeping its name: the
  blueprint (`intro.tex`, `laman.tex`, `laman-theorem.tex`, `henneberg.tex`, `rigidity-matroid.tex`
  with `thm:edgeSet-rowIndependent-iff-isSparse`'s title, `bar-joint-3d.tex`) and a
  `bibliography.bib` entry; README; the home page; `formalization.yaml` (a `sources` entry, LY's
  note, `status.scope`, two rows, two `alignment` sources); ROADMAP (opening, layout line, §6, §7,
  *References*); `DESIGN.md`'s two (211e2737); round 3: the docstrings, `Laman.lean`'s header
  among them (task 25).
