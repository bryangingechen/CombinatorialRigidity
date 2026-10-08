# PROSE findings ledger

The one home of every finding the **PROSE** rounds make (`notes/Prose.md` §4). Round 1's open
created it (2026-10-07). Rounds 1–4 only append to it. Round 5, `prose-graph`, sets each entry's
disposition, acts on the `E`, `N`, `T` and `U` entries, and reports the `S`, `L` and `M` entries to
the PI. A round's work log names a finding by its ID, in one line under *Candidates for …* or
*Moved to a later round*; the finding itself is written only here (`notes/CLAUDE.md` *One
canonical home per content type*).

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
  reported`.
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
- **F-002** · E · round 2's chapters (`matroid-union.tex` … `meet.tex`): 99 missing edges at 58
  nodes (38 through a statement): `molecular-induction` 42, `meet` 24, `deficiency` 18,
  `rigidity-matrix` 13, `body-bar` and `extensor` 1 each. 38 of them go to `def:edge-multiply`;
  279 more are implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
- **F-003** · E · round 3's files (`algebraic-induction.tex` and its five sections): 164 missing
  edges at 47 nodes (42 through a statement): `case-iii` 70, `case-i` 52, `panel-layer` 26,
  `case-ii` 15, `genericity-and-count` 1. The commonest targets are `def:rigidity-matrix` (15),
  `def:panel-general-position` (13) and `lem:general-position-support-nonzero` (10); 473 more are
  implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
- **F-004** · E · round 4's chapters (`bar-joint-3d.tex` … `generic-lift.tex`): 76 missing edges
  at 42 nodes (28 through a statement): `jacobs` 33, `molecule-modelling` 17, `generic-lift` 14,
  `bar-joint-3d` and `molecule-application` 6 each. The commonest targets are
  `lem:rigidityMap-apply` and `lem:molecule-graph-carrier` (10 each); 267 more are implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
- **F-005** · E · `pencil.tex` and `main-component.tex`: 114 missing edges at 58 nodes (31
  through a statement): `main-component` 87, `pencil` 27. 43 go to two pinned helpers (F-010):
  `lem:pencil-bridge-fibre` (25) and `thm:pencil-jj-equality` (18); 710 more are implied.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`).
  *Found:* round 1 task 2.
- **F-006** · E · unbacked `\uses`, every chapter: 397 `\uses` targets that no pin of the using
  node reaches. 87 are reached only through another pinned node, and 310 not at all; per group
  (through a node / not at all): round 1 5/19, round 2 11/88, round 3 32/120, round 4 22/21,
  `pencil`/`main-component` 17/62. They are for a check, not defects. Example:
  `thm:isSparse-exists-typeI-or-typeII-reverse` uses `def:typeI` and `def:typeII`, but its pin
  states the decomposition by degrees and neighbourhoods and names neither.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; TeX and Lean at `bca00d3f`);
  the example read (`IsSparse.exists_typeI_or_typeII_reverse`'s statement, `Sparsity.lean`).
  *Found:* round 1 task 2.
- **F-007** · E · `rem:kt-lemma-41` (`molecular-induction.tex`): `lem:base-vfiber-count`,
  `lem:acyclic-insert-vfiber` and `lem:balanced-forest-packing` use this remark, and the graph
  draws only edges between nodes, so none of the three edges is drawn (`lint.sh` check 1 passes
  them: the label exists). The same chapter's example `ex:kt-41-overquantified` pins
  `Graph.kt_lemma_41_overquantified`, which `checkdecls` checks and no node shows.
  *Evidence:* measured (`scripts/blueprint-deps.py`'s parse notes, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
- **F-008** · E · the graph's four unfilled nodes: `def:blockingWitness` (`pebble-game.tex`),
  `def:induced-span` and `lem:forest-surgery-unsplit` (`molecular-induction.tex`) have neither a
  pin nor `\leanok`; `def:dof-generic` (`rigidity-matrix.tex`) pins
  `BodyHingeFramework.IsInfinitesimallyRigid` without `\leanok`.
  *Evidence:* measured (`scripts/blueprint-deps.py`, round 1 task 2; the built graph at `bca00d3f`).
  *Found:* round 1 task 2.
- **F-062** · E · `lem:case-II-placement-new-rows` (`algebraic-induction/genericity-and-count.tex`):
  its statement and proof use `lem:rank-delete-vertex`, which no pin reaches, and its proof cites
  that node for the dimension $D - 1$ of the hinge-row block, which is `def:hinge-row-block`'s
  (`finrank_hingeRowBlock`, which the pin reaches through its proof).
  *Evidence:* measured (`scripts/blueprint-deps.py --label lem:case-II-placement-new-rows`, at
  `47eb5225`'s Lean); read (the proof's prose).
  *Found:* round 2 task 2.5.
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

## N — node shape

- **F-009** · N · 28 nodes with four or more pins (principle D), exactly `notes/Prose.md` §7's
  list: 19 in rounds 1–4's chapters and 9 in `pencil.tex` and `main-component.tex`. The largest
  are `def:rigidity-matrix` (14), `lem:case-III-claim612-line-in-panel-union` (12) and
  `lem:pencil-jj-embed-edges` (11). Round 1's four are `def:pebble-counts` and
  `lem:pebble-game-invariants` (5 each), `def:tryReachPebble` and `lem:edgesIn-corners` (4 each).
  *Evidence:* measured (`scripts/blueprint-deps.py` report 3, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
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
- **F-012** · N · liveness (`CLEANUP.md` §B): 202 pins at 153 nodes lie outside the closure of
  every main result, among them every pin of 112 nodes. Per group (pins / nodes with every pin
  outside): round 1 33/27, round 2 48/15, round 3 80/48, round 4 22/13,
  `pencil`/`main-component` 19/9. Round 1's include the executable surface, which no main result
  uses (the three `Decidable` instances, `def:runPebbleGameExec`), and side results such as
  `thm:typeII-isLaman`; `cor:pencil-flat-x0` is acceptance test (b). Each wants §B's three-way
  diagnosis (delete, wire in, or keep as exposition), not a reflex deletion.
  *Evidence:* measured (`scripts/blueprint-deps.py` report 2, round 1 task 2; at `bca00d3f`).
  *Found:* round 1 task 2.
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
- **F-019** · N · `thm:isSparse-exists-typeI-or-typeII-reverse` (`rigidity-matroid.tex`): the node
  is in §10 of the rendered blueprint, after its first user,
  `thm:isLaman-exists-typeI-or-typeII-reverse` (`henneberg.tex`, §5). Yet its pin `IsSparse.exists_typeI_or_typeII_reverse` is in
  `Sparsity.lean` and reaches only nodes of `sparsity.tex`. Prose cannot remove the cross-chapter
  forward reference; task 5.3 gives it a sentence in *Reverse decomposition*'s lead-in. Moving the
  node to the end of `sparsity.tex`, after the splitting lemma it uses, would remove it.
  *Evidence:* measured (`scripts/blueprint-deps.py --label
  thm:isSparse-exists-typeI-or-typeII-reverse`, at `0a2230a0`); read (the declaration's module).
  *Found:* round 1 task 5.3.
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
- **F-065** · N · `cor:block-rank-vertex-two-cut` (`rigidity-matrix.tex`): its pins
  `inf_span_rigidityRows_of_vertexTwoCut` and `finrank_span_rigidityRows_vertexTwoCut_eq` have no
  Lean caller, and no node uses the corollary (outside every main result's closure, counted in
  `F-012`). The ear lemma and `main-component.tex` use the general `lem:block-rank-two-cut`, whose
  sides are any two subgraphs. Keep it as exposition of the induced case, or drop it.
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter rigidity-matrix`, at `5399e053`: two
  dead pins); read (a `grep` for the two names' callers and for the label in `blueprint/src/`).
  *Found:* round 2 task 2.6.
- **F-068** · N · `lem:rigidityRows-pinned-placement-rank-add` (`rigidity-matrix.tex`): its second
  pin, `le_finrank_span_rigidityRows_of_pinned_placement_augment` (the count with one more row,
  KT eq. (6.29)), has no Lean caller (counted in `F-012`); Case III uses the block-level
  `linearIndependent_sum_pinned_block_augment_block` directly. The node's edge to
  `lem:case-III-conditional-block` rests on that pin. Unpin it, or keep it as exposition of KT
  eq. (6.29).
  *Evidence:* measured (`scripts/blueprint-deps.py --chapter rigidity-matrix`, at `af438fd1`: one
  dead pin); read (a `grep` for the two names' callers).
  *Found:* round 2 task 2.7.
- **F-087** · N · `lem:packing-move` (`molecular-induction.tex`): its pin
  `exists_packing_move_of_not_inc` has no Lean caller (counted in `F-012`).
  `exists_balanced_forest_packing` (`lem:balanced-forest-packing`) makes the same move inline,
  keeping the forests pairwise disjoint, so that node's edge to `lem:packing-move` is unbacked. Keep
  the node as exposition of the move, or have the descent call the pin (`F-088`).
  *Evidence:* measured (`scripts/blueprint-deps.py --label`, at `ce54bf15`'s Lean: one dead pin at
  `lem:packing-move`, the edge unbacked at `lem:balanced-forest-packing`); read (the body of
  `exists_balanced_forest_packing`).
  *Found:* round 2 task 2.12.
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
- **F-091** · N · `lem:forest-surgery-unsplit` (`molecular-induction.tex`; unfilled, `F-008`): in
  the form of independent sets it is the case $h' = 0$ of `lem:edge-splitting`'s case (i) for
  $G = H_{ab}^v$ ($D \ge 2$, $a \neq b$), which `splitOff_indep_extend_of_fiber_lt` proves, and no
  node uses it. Its statement ended "matching deficiencies under $(H_{ab}^v)_v^{ab} = H$"; task
  2.13 states the forest form its proof gives and the relation in prose. Pin it to that
  declaration with a note, or delete it and keep KT's use for Lemma 4.4 in `rem:kt-lemma-44`.
  *Evidence:* read (the pin's statement; KT 2011 pp. 660–662).
  *Found:* round 2 task 2.13.

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
- **F-073** · T · the dimension letter (`main-component.tex`, `pencil.tex`): both write the
  dimension as $n$, the formalization's parameter: "the deficiencies of `def:D-deficiency` at $n = 2$
  and $n = 3$ ($D = 3$ and $D = 6$)", "the conditioned pair at $n = 3$", about 48 lines in all.
  Round 2 writes KT's $d$, and task 2.8's `deficiency.tex` writes $\operatorname{def}_d(G)$ for the
  deficiency at dimension $d$, which agrees with their $\operatorname{def}_2$ and
  $\operatorname{def}_3$.
  *Evidence:* read (a `grep` for "$n = 2$" and "$n = 3$" over the two chapters, at task 2.8).
  *Found:* round 2 task 2.8.

## U — status surfaces

- None yet.

## S — statement strength

- **F-015** · S · `thm:isTightOn-insert-vertex-with-edges` (`sparsity.tex`): the statement assumes
  $V$ finite, which its pin `IsTightOn.insert_vertex_with_edges` does not (it takes only
  `DecidableEq V`; the set $s$ is finite). The statement is weaker than the pin. Its sibling
  `thm:isTightOn-union-with-bonus` assumes $V$ finite as its pin does.
  *Evidence:* read (the statement of `insert_vertex_with_edges`, `Sparsity.lean`).
  *Found:* round 1 task 5.2.
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
- **F-026** · S · `lem:span-range-rigidityRow` (`laman-theorem.tex`): the statement assumes $V$
  finite, which its pin `span_range_rigidityRow` does not: it takes only `[Finite G.edgeSet]`. The
  statement is weaker than the pin, as in `F-015`.
  *Evidence:* read (the statement of `span_range_rigidityRow`, `RigidityMatroid.lean`).
  *Found:* round 1 task 5.7.
- **F-027** · S · `lem:isSparse-of-rowIndependent-two` (`laman-theorem.tex`): the statement assumes
  $V$ finite, which its pin `isSparse_of_edgeSetRowIndependent_dim_two` does not (it takes no
  finiteness; the sets of at least three vertices it quantifies over are finite). The statement is
  weaker than the pin, as in `F-015` and `F-026`.
  *Evidence:* read (the statement of `isSparse_of_edgeSetRowIndependent_dim_two`, and the body of
  `EdgeSetRowIndependent`, `RigidityMatroid.lean`).
  *Found:* round 1 task 5.8.
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
- **F-031** · S · `lem:exists-isTightOn-of-insert-not-sparse` (`count-matroid.tex`): the statement
  assumes $V$ finite, which its pin `IsSparse.exists_isTightOn_of_insert_not_sparse` does not (its
  only section variable is `{V : Type*}`; the tight set it produces is a finite set). The statement
  is weaker than the pin, as in `F-015`. The chapter's other seven pins take `[Finite V]`, as their
  statements say.
  *Evidence:* read (the statement, `Sparsity.lean`; `#check` in a `lake lean` scratch file).
  *Found:* round 1 task 5.11.
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
- **F-037** · S · `lem:workhorseWitness-certifies` (`pebble-game.tex`): the statement takes a finite
  simple graph $G$ on $V$. Its pin `WorkhorseWitness.certifies_against` assumes only that $G$ has
  finitely many edges (`[Fintype G.edgeSet]`; nothing on $V$). The statement is weaker than the
  pin, as in `F-026`. Task 5.13's prose after `def:workhorseWitness` says the same.
  *Evidence:* read (the statement of `certifies_against`, `Correctness.lean`; `#check`).
  *Found:* round 1 task 5.14.
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
- **F-042** · S · `def:pebbleGameResult` (`pebble-game.tex`): the definition takes a finite simple
  graph $G$ on $V$. Its pin `PebbleGameResult` takes only `[DecidableEq V]` and
  `[Fintype G.edgeSet]`, so $G$ need only have finitely many edges, as in `F-037`. The definition
  is narrower than the pin. The other three pins of task 5.15 take `[Fintype V]` and `ℓ < 2 * k`,
  as their statements say (`runPebbleGameExec_isAccept_iff` also `[LinearOrder V]`).
  *Evidence:* read (`#check @PebbleGameResult`: the `[Fintype V]` of `Correctness.lean`'s
  `Verdict` section is not among its binders).
  *Found:* round 1 task 5.15.
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
- **F-058** · S · `thm:tay-witness` (`body-bar.tex`) and `thm:body-hinge-tay` (`body-hinge.tex`):
  both statements assume $d \ge 2$, and their pins `Graph.BodyBarFramework.tay_witness` and
  `Graph.BodyHingeFramework.body_hinge_tay` hold for every $d$, so the statements are weaker than
  the pins. `prop:tay-witness-exists`, `lem:tay-isSparse-of-independent` and
  `lem:edge-multiply-sparse` assume nothing on $d$, and the proof of `lem:edge-multiply-sparse`
  applies `thm:tay-witness` to $(D-1)\cdot G$ for every $d$. Task 2.3 kept every hypothesis.
  *Evidence:* read (the five pins' statements, `BodyBar/TayTheorem.lean` and `BodyHinge.lean`).
  *Found:* round 2 task 2.3.
- **F-060** · S · `lem:case-III-claim612-extensor-span` (`algebraic-induction/case-iii.tex`): the
  statement says that the $D$ two-extensors $\bar p_i \vee \bar p_j$ of $k+2$ linearly independent
  vectors of $K^{k+2}$ span $\bigwedge^k K^{k+2}$, and calls them $k$-extensors. Its pin
  `span_omitTwoExtensor_eq_top` is about the omit-two extensors, each the join of the other $k$
  vectors; the two families coincide as sets only at $k = 2$. The proof applies KT Lemma 2.1 in
  the omit-two form, so it proves the pin's statement, not the node's.
  *Evidence:* read (the pin's statement, `Molecular/RigidityMatrix/Claim612.lean`).
  *Found:* round 2 task 2.4.
- **F-079** · S · `lem:rk-within-parts` (`deficiency.tex`): the statement bounds $r(Y) + |P|$
  for the set $Y$ of all edges of $\tilde G$ whose ends lie in one part of $P$. Its pin
  `rk_cycleMatroid_within_parts_le` proves the bound for every $Y \subseteq E(\tilde G)$ whose
  edges have both ends in one part, so the statement is weaker than the pin. The formal proof of
  `thm:def-eq-corank` uses the general form, at the optimal set $Y_0$ (the private
  `rk_add_numParts_componentLabel`). Task 2.10 kept the statement and says this in a formalization
  note.
  *Evidence:* read (the statements of both, `Molecular/Deficiency.lean`).
  *Found:* round 2 task 2.10.
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
  for the graph form.
  *Evidence:* read (the statements of the three declarations, `Induction/Contraction.lean`).
  *Found:* round 2 task 2.11.
- **F-086** · S · `lem:acyclic-insert-vfiber` and `lem:packing-move` (`molecular-induction.tex`):
  both statements take $v$ to be a vertex of degree two of $G$, the setting in which
  `lem:balanced-forest-packing` uses them. Their pins `acyclicSet_insert_vfiber_of_not_inc` and
  `exists_packing_move_of_not_inc` assume nothing about the degree: at any vertex $v$, a forest of
  $\tilde G$ with no edge at $v$ stays a forest when an edge from $v$ to some $w \neq v$ is added.
  Each statement is weaker than its pin, as in `F-015`. Task 2.12 kept the degree, and the first
  proof says that it is not used.
  *Evidence:* read (the two statements, `Induction/ReducibleVertex.lean`).
  *Found:* round 2 task 2.12.

## L — Lean

- **F-013** · L · `SimpleGraph.Henneberg.typeII_isLaman` (`Henneberg.lean`): it takes `hab : a ≠ b`
  beside `hG_ab : G.Adj a b`, which implies it (`SimpleGraph.Adj.ne`). `thm:typeII-isLaman` now
  states only "$ab$ is an edge". The theorem has no Lean caller, so the binder can go alone.
  *Evidence:* read (the statement of `typeII_isLaman`; a `grep` finds no caller).
  *Found:* round 1 task 3.
- **F-017** · L · `IsTightOn.union_with_bonus`, `IsTightOn.insert_vertex_with_edges`
  (`Sparsity.lean`): each takes `hF_finite : F.Finite`, which follows from `hF_sub`, since
  `edgesIn` of a finite vertex set is finite (`edgesIn_finite`). The blueprint statements no longer
  name it. The callers pass `Set.toFinite _` or `Set.finite_singleton _`.
  *Evidence:* read (both statements, and their two callers in `Sparsity.lean`).
  *Found:* round 1 task 5.2.
- **F-018** · L · `SimpleGraph.IsSparse.typeII_reverse_blocker` (`Sparsity.lean`): its docstring
  and the section docstring above it say "distinct vertices `x, y`", but the statement does not
  assume `x ≠ y`. (At `x = y` the hypothesis fails, since the added pair is a loop and is dropped.)
  *Evidence:* read (the statement and the two docstrings).
  *Found:* round 1 task 5.2.
- **F-021** · L · `SimpleGraph.Henneberg.typeII_isGenericallyRigidInj_two_of_nonCollinear`
  (`HennebergRigidity.lean`): it takes `hab : a ≠ b` beside `hLI_abc : LinearIndependent ℝ ![p b -
  p a, p c - p a]`, which implies it (the first vector is nonzero). The body uses `hab` only to get
  `p a ≠ p b`. `thm:typeII-isGenericallyRigidInj-two-of-nonCollinear` now states only the
  non-collinearity. Its one caller, `typeII_isGenericallyRigidInj_two`, passes `hab`.
  *Evidence:* read (the statement and body; a `grep` finds the one caller).
  *Found:* round 1 task 5.5.
- **F-022** · L · `typeI_isInfinitesimallyRigid_extend`, `typeII_isInfinitesimallyRigid_extend`
  (`HennebergRigidity.lean`): their docstrings contradict their declarations. The first calls
  itself "the rank-nullity heart of `typeI_isGenericallyRigid_two`", which names no declaration (the
  caller is `typeI_isGenericallyRigidInj_two`). The second lists `G.Adj a b` among its hypotheses;
  the statement does not take it, and the proof treats the edge $ab$ only when it is present.
  *Evidence:* read (both statements and docstrings; a `grep` for `typeI_isGenericallyRigid_two`).
  *Found:* round 1 task 5.5.
- **F-023** · L · `SimpleGraph.trivialMotions` (`TrivialMotions.lean`): its docstring cites
  `trivialMotions_three_le_finrank_of_affinelySpanning_two`, which no longer exists (only
  `notes/FRICTION.md` still names it), and the docstring of the section on the $d$-general bound
  says "The dim-2 case below is its `d = 2` instance", but the file has no such case. The docstring
  of `rigidityMap_ker_finrank_ge_of_affinelySpanning` credits the count to Asimow–Roth, a credit
  `trivial-motions.tex` dropped as unverified (task 5.6).
  *Evidence:* read (the file; a `grep` over the repository for the cited name).
  *Found:* round 1 task 5.6.
- **F-024** · L · `SimpleGraph.trivialMotionFamily_linearIndependent` (`TrivialMotions.lean`): its
  `[Finite V]` is unused. The `@[nolint unusedArguments]` comment calls the linter's report a false
  positive, but the theorem elaborates without the binder, with the same proof minus its
  `Fintype.ofFinite` line. `lem:trivialMotionFamily-linearIndependent` states "Let $V$ be finite",
  as the pin does. Its one caller, `trivialMotions_finrank_ge_of_affinelySpanning`, needs
  `[Finite V]` for the dimension.
  *Evidence:* read (the statement and body); a `lake lean` witness (the theorem restated without
  `[Finite V]`, the proof copied with that line deleted; it elaborates with no output).
  *Found:* round 1 task 5.6.
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
- **F-032** · L · `SimpleGraph.countMatroid` (`CountMatroid.lean`): its docstring says that outside
  $\ell < 2k$ "the augmentation axiom can fail (e.g. `(3, 6)` in 3-dimensional rigidity)". By
  `IsSparse`'s definition a $(3,6)$-sparse graph has no edges (a pair $s$ has $6 \le 3|s|$, so it
  spans none), and the $(3,6)$-sparse edge sets form a matroid in which no edge is independent.
  `count-matroid.tex` made the same claim ("the bases need not have equal cardinality, for instance
  $(3, 6)$-tight graphs"), which task 5.11 dropped.
  *Evidence:* read (the body of `IsSparse`); a `lake lean` witness (every $(3,6)$-sparse
  `SimpleGraph V` is `⊥`; it elaborates with no output).
  *Found:* round 1 task 5.11.
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
- **F-035** · L · `PebbleGame/Basic.lean`, `PebbleGame/Algorithm.lean`: docstrings that describe
  other states of the code. Basic.lean's *Path reversal* section header says the lemmas about
  `out`, `peb`, `span` and `outOn` "follow in a subsequent commit"; they are in that section.
  Algorithm.lean's *Try-reach-pebble* header and `tryReachPebbleWith`'s docstring say soundness and
  completeness theorems "will live" or "will land" on `tryReachPebbleWith`. The docstrings of
  `tryAddEdgeWith`, `tryAddEdge`, `tryAddEdgeWith_reachable` and `runPebbleGameWith` record Phase
  11's reshape ("was `some D'`", "was `Option (PartialOrientation V)`").
  *Evidence:* read (the docstrings named, against the two files).
  *Found:* round 1 task 5.13.
- **F-039** · L · `runPebbleGameWith_sound`, `runPebbleGameWith_underline_eq`,
  `runPebbleGameWith_correct` (`PebbleGame/Correctness.lean`, `Algorithm.lean`): the binder
  `hloops : ∀ p ∈ edges, p.1 ≠ p.2` follows from `himg`, since each entry's unordered pair is an
  edge of `G` and so not a loop. `runPebbleGame_edges_discharges` proves it separately.
  *Evidence:* read (the three statements); a `lake lean` witness deriving `hloops` from `himg` in
  three lines (`List.mem_toFinset`, `SimpleGraph.ne_of_adj`).
  *Found:* round 1 task 5.14.
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
- **F-061** · L · `BodyHingeFramework.linearIndependent_hingeRow_forest` and
  `exists_independent_rigidityRows_of_forest` (`Molecular/RigidityMatrix/Basic.lean`): the names
  and docstrings speak of a spanning forest, but the hypothesis `hsep` (no other end of an edge is
  the private end of any edge) holds only when every component of the edges is a star; a path with
  three edges fails it. The rows of any forest of nondegenerate hinges are independent (remove a
  leaf), but no declaration states it. `def:rigidity-matrix`'s prose claimed "any spanning forest";
  task 2.5 states the hypothesis instead.
  *Evidence:* read (the two statements and the first body).
  *Found:* round 2 task 2.5.
- **F-063** · L · `BodyHingeFramework.screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  (`Molecular/AlgebraicInduction/PanelLayer.lean`): its hypothesis asks $C(e) \neq 0$ at every
  edge label, also at labels that are not edges of $G$, where the extensor does not affect the
  motions. The relative bound `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
  in the same file asks it only at the edges of $G$.
  *Evidence:* read (the two statements).
  *Found:* round 2 task 2.5.
- **F-064** · L · `BodyHingeFramework.le_finrank_span_rigidityRows_of_cut`
  (`Molecular/RigidityMatrix/Bricks.lean`): its docstring names the node
  `lem:rigidityRows-cut-rank-add`, which does not exist; the declaration is pinned on
  `lem:block-rank-cut`.
  *Evidence:* read (the docstring; a `grep` for the label in `blueprint/src/`).
  *Found:* round 2 task 2.6.
- **F-069** · L · docstrings of four pins in `rigidity-matrix.tex`'s Case I lemmas name the wrong
  node: `infinitesimalMotions_sup_range_extProj_eq_top_of_inter_eq_singleton`,
  `injOn_extProj_dualMap_rigidityRows_of_inter_eq_singleton` and
  `finrank_span_rigidityRows_map_extProj_dualMap_of_inter_eq_singleton`
  (`AlgebraicInduction/Coupling.lean`) name `lem:rigidityRows-splice-rank-add`, and are pinned on
  `lem:extProj-preserves-rank-of-inter`; `finrank_span_rigidityRows_ofNormals_relabel_eq`
  (`CaseI.lean`) names `lem:case-I-realization-all-k`, which does not exist.
  *Evidence:* read (the docstrings; a `grep` for the labels in `blueprint/src/`).
  *Found:* round 2 task 2.7.
- **F-070** · L · `PanelHingeFramework.exists_rankPolynomial_of_IH_relabel_linking_set_proj`
  (`AlgebraicInduction/CaseI.lean`): its hypothesis `hcLoop` (the contraction has no loops)
  follows from `hKmin` (it is a minimal $k$-dof-graph) by `Graph.loopless_of_isMinimalKDof`.
  *Evidence:* read (the statement and body; `Graph.loopless_of_isMinimalKDof`, `Deficiency.lean`).
  *Found:* round 2 task 2.7.
- **F-074** · L · docstrings in `Molecular/Deficiency.lean`: `Graph.matroidMG`'s says that
  $M(\tilde G)$ is "the boundary regime `ℓ = 2k = D`", not "the matroidal regime `ℓ < 2k` of
  `CountMatroid.lean`". The $(D,D)$ count has $\ell = k$, inside $\ell < 2k$; `countMatroid` does
  not apply because it is a matroid on `Sym2 V`, with no parallel edges. The docstrings of
  `matroidMG_indep_iff` and `loopless_of_isMinimalKDof` call the independence criterion
  "boundary-regime cleanliness".
  *Evidence:* read (the docstrings; `countMatroid`'s signature, `CountMatroid.lean`).
  *Found:* round 2 task 2.8.
- **F-075** · L · `Graph.deficiency_eq_of_cutEdges_ncard_le_one` (`Molecular/Deficiency.lean`): its
  hypothesis `hD : 1 ≤ bodyBarDim n` is unused (the proof discards it, "part of the public API").
  `exists_cut_decomposition_of_not_twoEdgeConnected` and `Graph.deficiency_induce_union_singleton`
  (`Molecule/Pencil/Motive.lean`) take it only to pass it on. `lem:cut-edge-decomposition` states
  its (1)–(3) without it, so dropping it makes the three pins match.
  *Evidence:* read (the three statements and bodies).
  *Found:* round 2 task 2.8.
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
- **F-080** · L · docstrings in `Molecular/Deficiency.lean` around `thm:def-eq-corank`:
  `isBase_ncard_add_deficiency_eq`'s says that it "closes" `prop:rigidity-matrix-prop11`, which
  `rigidityMatrix_prop11` (`AlgebraicInduction/PanelHinge.lean`) proves; `rank_add_deficiency_le`'s
  calls the reverse inequality "the remaining JJ09 min–max content", which `le_rank_add_deficiency`
  proves; `rk_cycleMatroid_within_parts_le`'s and its section's call it "`thm:def-eq-corank`, piece
  1", and it is pinned at `lem:rk-within-parts`; `IsKDof.exists_isBase_isForestPacking`'s calls a
  Phase-22 construction "the remaining Track-A obstruction". Their credits are `F-081`'s.
  *Evidence:* read (the docstrings and the four statements).
  *Found:* round 2 task 2.10.
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
  and the Lean). Lovász–Yemini 1982 is not in `.refs/`.
  *Found:* round 1 task 5.7.
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
