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

## T — terminology and notation

- None yet.

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
  "Lovász–Yemini easy direction" for `lem:isSparse-of-rowIndependent-two` (task 6 checks it).
  *Evidence:* read (Jordán 2016 pp. 45, 49, 51, in `.refs/`; a `grep` for "Lov" over the blueprint
  and the Lean). Lovász–Yemini 1982 is not in `.refs/`.
  *Found:* round 1 task 5.7.
