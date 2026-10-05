# Phase 40 cleanup round 3/5 — `40-exposition`, the pencil proof explained (work log)

**Status:** ✓ closed 2026-10-04 (opened 2026-09-30). Round 3 of the five post-Phase-40 cleanup
rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The round rewrote the
prose of `pencil.tex` and `main-component.tex`, and `intro.tex`'s reader path into them, to
"explain the mathematics clearly" and "the proof and its key ideas in context" (the PI,
`notes/Cleanup40.md` §1). Pins, `\uses` edges and statement strength are as they were. 27
one-commit tasks, all landed (tasks 3 and 4 with a corrective each), and eight build-or-leave
recommendations for round 4's Stop 2. **Next concrete task:** none in this round; the current
round is named in `notes/Cleanup40.md`'s **Status**. Round manual: `CLEANUP.md`.

## Autopilot: for the PI

### 2026-09-30 — `NEEDS_PI`: Stop 1, the sample section (planned stop, `notes/Cleanup40.md` §2)

**What happened.** Task 1 landed the sample (`806db52e`; the full Stop-1 entry is at
`82d806c5`): its register, defaults (a)–(d), the granularity, and "an endpoint selector" (item 4).

**PI, 2026-10-03:** (transcribed verbatim from the attended session that reviewed the sample)
- On the sample: "I think the text is a bit wordy and there are redundancies. For example, "Each
  step deduces that the general configuration of $G$ attains from the same conclusion at smaller
  graphs on the same bodies and edge labels." is already implicit when it says the proof proceeds
  by strong induction. Furthermore the text still feels a bit overwrought; I think the term is
  "mannered prose"? Could you check the style of papers in .refs/ again and try and edit the text
  to be easier to follow?"
- On allowing "we", as KT do: "Yes, and at some point we should also look into doing a rewrite
  round of the rest of the blueprint too."
- On item 4: "Right, we should be skeptical of any nonstandard terminology; certainly any such
  uses need a definition / explanation in a hard-to-miss place."
- On writing the register guidance down for tasks 3–26: "Good idea. Yes, please add guidance per
  what you found above."
- On `blueprint/AUTHORING.md` principles A and C, whose bans and citation test push toward
  stilted prose: "Hmm, I wonder if we can find some balance here?"
- On leaving the chapter introduction to task 25: "Fine, as long as it doesn't get missed."
- On `lem:pencil-splitoff-curve`, which bundles three unrelated facts: "Good catch; yes, we also
  struggled with nodes containing too much in earlier blueprint phases, I wouldn't be surprised
  if there are still some left around."
- On the first revision: "In fact the whole paragraph still seems dense and tough to follow.
  Perhaps we could lessen the detail since this is supposed to just be an overview? There are
  also sentences which have too many clauses [...] It's not even clear to me what "This" refers
  to. Can you try again?"
- On the second revision and the balance for `AUTHORING.md`: "OK, this looks much better and your
  suggested balance also sounds good."
- On the granularity: "I think the task granularity is probably reasonable if it's backed by a
  judgment that this would be most efficient and effective." Then, given that judgment (one
  commit per subsection; *Decisions*): "The granularity judgment also looks fine."
- On the defaults: "(a) agreed. In cases where the informal argument might give more insight but
  we decided not to formalize it due to technical reasons, it could be worth mentioning as well.
  (b)-(d) These look fine." Then: "Let's commit."

**What follows.** Stop 1 is closed: the exemplar is pinned (task 2), defaults (a)–(f) and the
granularity are under *Decisions*, the introduction's flags are in task 25, and **PROSE** is queued.

## Current state

**Round 3 is closed** (task 27, docs only). All 27 tasks landed, tasks 3 and 4 with a corrective
each, and each has one line under *Lemma checklist* naming its commit. Nothing is mid-stream. Every
subsection of `pencil.tex` and `main-component.tex`, both introductions and `intro.tex`'s reader
path are rewritten, and the dependency graph and the pins are the open's. What carried over: the
eight build-or-leave recommendations and the nine *Candidates for `40-simplify`*, which are round
4's Stop-2 inputs, and the *Moved to a later round* lines, seven for round 4 and one for round 5.
All are mirrored into `notes/Cleanup40.md` §2.

**Verified at the close** (task 27; the Lean tree is `0b260626`'s, the blueprint `30e79461`'s):
- Whole-project `lake build` green, 3003 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`, and the output is byte-identical to the open's. The harness
  `scratch/40-exposition/Axioms.lean` (gitignored) was run with `lake lean` after its 19 names (in
  order) and 14 imports were diffed against `formalization.yaml`'s `declaration:` and `file:`
  fields: identical.
- The blueprint is at the open's baseline. `lint.sh` and `verify.sh` are green (`checkdecls`
  silent, 9 `WARNING:` lines, all plasTeX notices), with 0 `LaTeX Warning` lines; 1 062 pins, hash
  `36133299d3fcc3c8`; 668 nodes and 1 308 edges, fingerprint `6c5064b7034feb95`. Overfull boxes
  went from 187 to 181.
- The surface grew: `pencil.tex` 1 411 → 1 589 lines, `main-component.tex` 4 858 → 5 696,
  `intro.tex` 471 → 511. The subsections and nodes are the open's: 10 and 41 in `pencil.tex`, 13
  and 123 in `main-component.tex` (the open recorded 14 subsections; a recount at both commits
  finds 13).

**Verified at the open** (`5f9cbe04`, docs only; its Lean tree is `0b260626`'s): the same build
(3003 jobs, 0 `warning:` lines) and the same 19 axioms, through round 2's harness copied to
`scratch/40-exposition/Axioms.lean`; the blueprint baseline above, with 187 overfull boxes.

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2. How each task applied them is in its commit.

- **Surface.** `pencil.tex`, `main-component.tex`, and `intro.tex`'s reader path into them, all in
  `blueprint/src/chapter/`. No Lean edits, and no other chapter's TeX: a finding elsewhere went to
  *Moved to a later round* or *Candidates*.
- **Prose only** (Phase 28's rule). Every node's `\label`, `\lean{…}` pins, `\leanok` and `\uses`
  edges, and the strength of its statement, stayed as they were; a statement block was edited for
  register or anchoring only. A finding that would change a statement's strength went to
  *Candidates*, and an edge the graph lacks to *Moved*. A node could move within its chapter to
  cure a forward reference (*Decisions*, (d)).
- **Evidence.** Citations follow `CLAUDE.md` *Referencing prior work*, against the sources in
  `.refs/` (KT 2011, Crapo–Whiteley 1982, Whiteley 1996; for Jackson–Jordán 2008 the technical
  report EGRES TR-2006-06, each passage named in the commit that relies on it). Claims about the
  Lean were read from declarations' statements and bodies, never from docstrings. The workbook is
  a source for the argument, never a citation.
- **Gates for every slice**, each in the foreground with an explicit `timeout`: `blueprint/lint.sh`
  and `blueprint/verify.sh` green (`checkdecls` silent); the invariance check below equal to the
  open's values; 0 `LaTeX Warning` lines in `blueprint/print/print.log` and 9 `WARNING:` lines from
  `verify.sh`; this log under ~500 lines, kept by hand (`notes/check-phase-note.py` does not match
  its name). The invariance check, run from the repository root after `verify.sh`, sees a changed
  `\uses` edge or `\leanok`, which `checkdecls` and `lint.sh` cannot:
  ```sh
  python3 -c "import re,hashlib;g=open('blueprint/web/dep_graph_document.html').read();g=g[g.find('digraph'):];g=g[g.find('{')+1:g.find('}')];s=sorted(filter(None,(re.sub(r'\s+',' ',x).strip() for x in g.split(';'))));print(sum(' -> ' in x for x in s),'edges',hashlib.sha256('\n'.join(s).encode()).hexdigest()[:16])"
  sort blueprint/lean_decls | shasum -a 256 | cut -c1-16
  ```

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line names its commit. The commit, with this log as of
that commit, carries the task's diagnosis, its (f) coinage list and its forward `\cref`s.

- [x] **1. S — the sample, `sec:main-component-splitoff`** (`806db52e`; its JJ paragraph checked
  against the TR, Theorem 6.1, Claim 6.5, Case 1, pp. 15–16).
- [x] **2. E — pin the exemplar** (`316fb0f3`; attended, with the PI, 2026-10-03).
- [x] **3. P1 — `pencil.tex`'s opening subsections** (`99a3e639`, corrective `6c5572fc`).
- [x] **4. P2 — base, cycle and extension** (`6bc95de3`, corrective `1bd8f6ed`).
- [x] **5. P3 — `sec:pencil-reduction`** (`96eda8e2`).
- [x] **6. P4 — `sec:pencil-nondegenerate`** (`58fc3a52`).
- [x] **7. P5 — `sec:pencil-main-component-route`**, retitled *Reduction to the main component*
  (`1010c804`).
- [x] **8. P6 — `sec:pencil-girth-chain`** (`694d892e`; item 2 written).
- [x] **9. M1a — the carrier, first half** (`a23508c0`).
- [x] **10. M1b — the carrier, second half** (`a5f782a5`).
- [x] **11. M2 — `sec:main-component-flat`** (`89c856dd`; item 8 written).
- [x] **12. M3 — `sec:main-component-jj`** (`b805e623`; items 4 and 7 written).
- [x] **13. M4 — `sec:main-component-cut`** (`9c931242`; item 3 written).
- [x] **14. M5 — `sec:main-component-contract`** (`8248885c`).
- [x] **15. M6 — `sec:main-component-chain`** (`698af66a`; item 1 written).
- [x] **16. M7a — SHORT's opening and toolkit** (`18e55da1`).
- [x] **17. M7b — SHORT's three steps** (`f6f160f7`; item 5 written).
- [x] **18. M8 — `sec:main-component-orbit`** (`3892f286`).
- [x] **19. M10 — `sec:main-component-contract-additive`** (`a396d213`).
- [x] **20. M11 — `sec:main-component-sparse`** (`df911478`).
- [x] **21. M12 — `sec:main-component-coverage`** (`5fbe5784`; item 6 written).
- [x] **22. M13a — `sec:main-component-statements`, first half** (`d20cf90d`).
- [x] **23. M13b — the statements' second half** (`ed1b13c0`).
- [x] **24. F1 — `pencil.tex`'s introduction** (`1432722c`).
- [x] **25. F2 — `main-component.tex`'s introduction** (`b166f435`).
- [x] **26. F3 — `intro.tex`'s reader path** (`30e79461`).
- [x] **27. X — close the round** (this commit; what it verified and carried over is under
  *Current state*, and its ledger work in `notes/BlueprintExposition.md`'s round note).

## The build-or-leave items (recommendations for round 4's Stop 2)

From `notes/Cleanup40.md` §2 *Round 3*. Each gets one recommendation: build it, add its blueprint
node, refactor around it, or leave it with a recorded reason. The task named wrote it, once the
exposition had made the item's role clear. The PI decides at round 4's stop. The close (task 27)
mirrored the eight, one line each, into `notes/Cleanup40.md` §2 *Round 4*.

1. **The D5 blueprint debt.** Of the 40 names in `notes/Phase40-design.md` §7's list, nine are
   pinned; 31 have no node. *Task 8 read all 40 in the Lean* (the closure of both headlines' types
   and values; measured, script not retained): 11 are live, seven pinned names (not the two pins of
   `cor:block-rank-vertex-two-cut`) and four unpinned helpers. The other 29, `TwoCut.lean`'s nine
   included, feed neither headline. Role: tasks 8 and 15. *Recommendation (task 15): leave all 31
   unpinned, with no node.* Read in the Lean, three of the live helpers are reached through the ear
   formula: `lem:block-rank-ear`'s pin calls `lem:block-rank-two-cut`'s second pin, which calls the
   first and `finrank_span_jointRows`; the first calls `span_jointRows_eq_map_dualAnnihilator` and
   `map_screwDiff_comm`. Outside `Bricks.lean`, only the ear formula's pin calls the two pins. The
   three are an unfolding, an orientation flip, and the count `D − dim U` of the joint rows, which
   `rigidity-matrix.tex` states after `def:relative-screws` and uses in the two-cut proof. The
   fourth, `bddAbove_range_partitionDef_merged`, bounds a finite supremum. Helpers stay unpinned
   (principle C); at most a later round names `finrank_span_jointRows` in the two-cut proof, as task
   43 of `40-cleanup` named item 7. The 29 keep item 2's reason: they serve the unfinished two-cut
   composition, and a node would pin its shape (D5) with no proof to cite it. Whether to delete them
   is round 4's question of the Lean that feeds neither headline.
2. **A6, the welded pendant law, and item 6's other deferred laws.** These are S7(i), S7(ii),
   S7(iii), S7(v) and S9, all unbuilt. Role: task 8. *Recommendation (task 8): leave them unbuilt,
   with no node.* They belong to the two-cut composition, an unfinished attempt at kernel (K-bare):
   split `G` at case (3)'s `{w, w'}` and combine the sides' deficiencies
   (`Graph.deficiency_eq_of_vertexTwoCut`) and ranks (`cor:block-rank-vertex-two-cut`), as
   `pencilLoss_vertexTwoCut` does. In the Lean that composite has no caller, and the kernels are
   hypotheses only of three declarations off the proof: a build gains no caller. Nor are these laws
   its gap. A6 reduces at a side end of degree one, but both ends keep degree two or more
   (`lem:pencil-chain-side-connected`); the S7/S9 laws are not consumed; it lacks ear-profile facts
   and a variety layer (`notes/Phase39-design.md` *Item-6 carrier recon*). From the cut remark:
   it covers case (3) only, and case (2) falls to the induction's cut-vertex case.
3. **The "only if" halves of (MC-52)/(MC-53).** Unbuilt; stated informally in the remarks after
   `thm:pencil-x0-cut` and `thm:pencil-x0-bridge`, until task 13 cut them. Role: task 13.
   *Recommendation (task 13): leave them unbuilt, with no node.* As the remarks stated them, with
   only `G` under the standing hypotheses, they are false. A side whose joining body has degree one
   in it has a closed neighbourhood of two members, so no admissible picture, and never attains
   (checked against `Graph.X0Attains` by a scratch Lean witness, not retained). Two triangles joined
   by a path of two edges, split at its middle body or at either edge, leave such a side. With both
   sides under the standing hypotheses, as the workbook states them, each side attains by
   `Graph.IsX0Graph.x0Attains` (`thm:pencil-x0-coverage`) whatever `G` does. So a build is that
   corollary, and no proof needs it: `Coverage.lean` and the closed ear (`Chain.lean`) call only
   `Graph.X0Attains.of_cutVertex` and `of_bridgePath`. The two remarks' dimension counts for
   `L_G(q)` went with them: unformalized, and no proof uses them.
4. **The edge-restricted, non-spanning generic-normals row rank** (design §3 BRIDGE). Three
   declarations, compiled by a recon and not landed. Role: task 12. *Recommendation (task 12):
   leave them unbuilt, with no node.* The equality never forms generic normals
   (`lem:pencil-jj-chart` moves one realization into the chart). Read in the Lean, the declaration
   they generalize (`thm:panel-generic-rank`'s pin) has one caller, `cor:panel-generic-rigid`'s
   pin, which has none; neither is in either headline's closure (measured, script not retained).
   §3 BRIDGE lists `HingeGeneric.lean` and `Steer.lean` as call sites; they name it in docstrings.
5. **SHORT's shared assembly**, `Graph.X0Attains.of_openEar_splitOff` and
   `Graph.exists_earBase_splitOff` (`Short.lean`). Role: task 17. *Recommendation (task 17): leave
   both unpinned, with no node.* Read in the Lean, the assembly's callers are the four- and
   three-body steps' pins, the base data's is the assembly, and all are in `pencil_conjecture`'s
   closure (measured, script not retained). Those two proofs name both as addresses (principle C):
   the opening sketches the two stages, `-four`'s proof writes them out once, `-three`'s cites it. A
   node must state the pin's hypothesis: over all base data, a nonzero polynomial in the ear data
   off which a point for the suppressed body gives `dim(ρ + Λ) ≥ min(dim W + 1, 6)`, read by no
   other proof. Nor would it free `-three`'s proof from `-four`'s: their shared insertion,
   `exists_insertion_of_star_sup_star`, is called by `exists_insertion_four` and `-three`, outside
   the assembly. The base data are a twelve-conjunct existence. A node buys one copy of the shared
   `\uses` edges, now listed in both steps.
6. **The CHAINS pair**, `Graph.IsOpenEar.exists_maximal` (`CoverageChain.lean`) and
   `Graph.Connected.induce_of_gate` (`CoverageCut.lean`). Role: task 21. *Recommendation (task 21):
   leave both unpinned, with no node.* Read in the Lean, the first has two callers, the pins of
   `lem:pencil-x0-chain-exists` and `lem:pencil-x0-cycle-reduces`. The second has two:
   `lem:pencil-x0-chain-standing`(1)'s pin, and the unpinned `Graph.IsX0Graph.induce_of_gate`, which
   `lem:pencil-x0-cut-reduces`'s two pins call (the bridge's through a private helper). All are in
   `pencil_conjecture`'s closure, none in `molecular_conjecture`'s (measured, script not retained).
   Each is an elementary graph fact (extend a path through bodies of degree two; a set with one body
   adjacent outside it, in a connected graph, induces a connected graph). Each pinned caller's proof
   states it in a clause and, since task 21, names it, or at the cut and bridge the wrapper, as an
   address (principle C), as item 5's do. A node would hold only that fact. The bridge case grows
   its path by its own private induction: `exists_maximal` stops at once at a bridge, whose ends are
   adjacent.
7. **`Graph.exists_isMinimalKDof_spanning_subgraph`** (`Molecular/Deficiency.lean`). Role: task 12.
   *Recommendation (task 12): give it a node* in `deficiency.tex`, beside `lem:subgraph-minimality`.
   Unlike item 8 it is mathematics: KT's first step for Theorem 5.6 (p. 670, checked), deleting
   edges, the deficiency kept, down to a minimal k-dof-graph. Read in the Lean, its four callers are
   the pins of `thm:theorem-55-6-genuine` (two) and `thm:theorem-55-6-rows` (which
   `lem:pencil-jj-chart` consumes), and `theorem_55_6_multigraph_of_two_le` (under `-multigraph`).
   It is in the closure of `pencil_conjecture` and `molecular_conjecture` (measured, script not
   retained). The blueprint names it by `\texttt` in one proof; `thm:theorem-55-6`, `-multigraph`
   cite the argument behind `lem:subgraph-minimality`, which it does not call. A node gives those
   four proofs a `\cref`, and the graph its edges.
8. **`Graph.exists_normalized_labeling`** (`Molecular/Deficiency.lean`). It is the relabelling
   inside `lem:relative-deficiency-rank-bound` (`rigidity-matrix.tex`), which
   `lem:pencil-lifting-space-deficiency` uses. Role: task 11. *Recommendation (task 11): leave it
   unpinned, with no node.* Read in the Lean, it has two callers: the hub pinned at
   `lem:relative-deficiency-rank-bound`, on the proof (the flat lower bound's pin calls it, and the
   split-off step calls that), and the merged hub of `TwoCut.lean`, which only the library root
   imports. It serves the encoding: a partition is a self-map of the body type, the bound counts
   the map's range, and the relabelling makes each body off `V(G)` its own part (with no body off
   `V(G)`, the hub needs none). That proof says so in a clause. A node would hold only the
   encoding; at most a later round names it there, as `40-cleanup` task 43 named item 7's strip.

A node these items might gain would sit in `deficiency.tex`, `rigidity-matrix.tex` or
`panel-layer.tex`, outside this round's surface. The round only recommends.

## The pinned exemplar

In its own file, `notes/Phase40-exposition-exemplar.md` (task 2, 2026-10-03). Every builder of
tasks 3–26 read it. It is altered only to correct a verified factual error.

## Candidates for `40-simplify`

Structural findings, and any finding that would change a headline or blueprint statement. They are
recorded here and never acted on in this round (`notes/Cleanup40.md` §2). The close (task 27)
mirrored them, one line each, into `notes/Cleanup40.md` §2 *Round 4*.

- **`lem:pencil-splitoff-curve` bundles three unrelated facts** (seen at Stop 1; the PI agreed,
  2026-10-03). They are a linear-algebra lemma, the extension of a height across `x`, and the
  locality of the lifting system, under three pins. Splitting the node changes the dependency
  graph, so this round leaves it. The PI expects more such nodes in earlier chapters; that audit is
  queued with **PROSE** (ROADMAP).
- **`thm:pencil-reduction` is stronger than its pin** (task 5). It gives cases (iii)–(v) the
  property at every lexicographically smaller graph; `Graph.pencil_reduction`'s `hcut`, `hcontract`
  and `hsplit` get it only at graphs with fewer vertices. Matching them changes the statement.
- **`thm:pencil-conditional-realization-pair` is two results** (task 6). Its first pin,
  `pencil_conjecture_of_arms_pair`, is the live reduction with the contraction and split cases as
  hypotheses; its statement and other two pins are the kernel form, off the proof. Splitting it
  changes the graph.
- **…and its statement is stronger than its pins** (task 6). Kernel (K) is assumed only at a
  nondegeneracy-feasible `G`, while `hK` has no such antecedent. "Strictly smaller", read in
  `thm:pencil-reduction`'s order, also gives more than the pins' fewer vertices (likewise in
  `thm:pencil-conditional-realization`).
- **`lem:pencil-selector-independent-scalar` assumes an admissible picture** (task 9); its pin
  does not. Dropping the hypothesis would raise the statement to the pin's strength.
- **`lem:pencil-condition-linear` restates another lemma** (task 9's return, checked by task 10).
  Its clause "`p` gives a pencil realization whose adjacent points are distinct" is
  `lem:pencil-config-distinct-realization`'s content. Neither pin proves it:
  `mem_liftingSpace_of_coplanar` is the converse direction alone, `exists_smul_eq_interpolant` the
  plane's normal. The forward direction is `lem:pencil-selector-plane-contains-nbhd`'s pin.
- **`lem:pencil-x0-main-picture-open` claims more than its pins** (task 10). "In particular `U` is
  … Zariski-open" does not follow from its polynomial, and `Graph.exists_mvPolynomial_isMainPicture`
  gives only a nonempty open subset of `U`. `U` is open (admissibility and `dim ker M(q) ≤ ℓ₀` are),
  but nothing here proves it.
- **`lem:pencil-lifting-restrict` (6 pins) and `thm:pencil-x0-bridge` (8 pins) are bundled nodes**
  (task 13; counted by task 14), as `lem:pencil-splitoff-curve` is: principle D's four or more pins.
  The first pins a definition with its unfolding, two facts and a polynomial helper with its
  evaluation; the second its step with four path helpers and three counts. Splitting or unpinning
  changes the pins. `lem:pencil-contract-standing` (4 pins, task 14) is of the same kind, and so is
  `lem:pencil-generic-steer` (4 pins, task 23: the parametrization, a helper, parts (a) and (b)).
- **Two toolkit halves have no caller** (task 16, read in the Lean): the pairing's nondegeneracy
  (`eq_zero_of_kleinLin_eq_zero`, in `lem:pencil-line-pairing-join`) and the no-loss half of
  `lem:pencil-insertion` (`exists_insertion_ge`). Dropping them changes the statements and pins.

## Moved to a later round

Each line gives the task, its target round, and a one-line reason. The same line goes into the
target round's plan section in `notes/Cleanup40.md` in the same commit.

- **Task 4, target `40-simplify`.** `def:pencil-nondegenerate`'s hub threshold rests on
  `lem:coplanar-hinges-concurrent` (cited before task 6 in a note, now in the lead-in through
  `sec:pencil-realization`), with no `\uses` edge to it.
- **Task 5, target `40-simplify`.** Only the off-route `thm:pencil-conditional-realization` has
  `\uses` edges to `lem:pencil-loop-case` and `lem:pencil-base-case`. The live route uses them
  through the pins of `thm:pencil-conditional-realization-pair` and
  `thm:pencil-conditioned-pair-nonempty`.
- **Task 5, target `40-simplify`.** `lem:pencil-simple-of-noRigid` has no in-edge, though
  `thm:pencil-generic-step`'s pin calls it through the unpinned three-body construction.
- **Task 6, target `40-simplify`.** `thm:pencil-conditional-realization-main-component` has no
  `\uses` edge to `thm:pencil-conditional-realization-pair`, though its proof applies the
  reduction as in it and its pin calls `pencil_conjecture_of_arms_pair`.
- **Task 6, target `40-simplify`.** `thm:pencil-conditional-realization-pair`'s two notes sit
  between its statement and proof, so plasTeX attaches the proof to a note and the graph draws the
  node unfilled. Moving them after the proof fills it (the graph's one changed line); the only case.
- **Task 21, target `40-simplify`.** `thm:pencil-x0-theorem-s`'s proof uses
  `lem:deficiency-zero-connected` (a body of a rigid set has two neighbours in it), which its pin
  calls (`Graph.two_le_degree_of_isKDof_zero`), with no `\uses` edge to it.
- **Task 23, target `40-simplify`.** `lem:pencil-generic-steer`'s proof uses both halves of
  `lem:pencil-feasible-hub-conditions`, which its pins call
  (`not_pencilNondegFeasible_of_triangle_two_hubs`,
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`), with no `\uses` edge to it.
- **Task 26, target `40-docs`.** `README.md` and `home_page/index.md` repeat the old reader path
  (*hinge-pencil conjecture*, *bond-star*, "statements about the main component", "a fixed planar
  drawing"), and `formalization.yaml` says *hinge-pencil conjecture*: align them with `intro.tex`.

## Blockers / open questions

- None. The next planned stop is round 4's Stop 2, where the PI decides the build-or-leave items.

## Hand-off / next phase

**Round 3 is closed; there is no next step in it.** Round 4, `40-simplify`, the deep recon, opened
2026-10-04 (`notes/Phase40-simplify.md`); `notes/Cleanup40.md`'s **Status** names the current
round. What carried over, all mirrored into `notes/Cleanup40.md` §2:
- round 4's Stop-2 inputs: the eight build-or-leave recommendations and the nine *Candidates for
  `40-simplify`*;
- the *Moved to a later round* lines: seven for round 4 (six missing `\uses` edges and one node the
  graph draws unfilled), and one for round 5 (the README, the home page and `formalization.yaml`
  still use the reader path's old names).

No task of this round is left open. A later prose round (**PROSE**, in ROADMAP's queue) can reuse
the round's defaults (*Decisions*), its exemplar (`notes/Phase40-exposition-exemplar.md`) and the
invariance check (*Scope*).

## Decisions made during this round

- **The sample** was `sec:main-component-splitoff`, a typical step with a JJ citation (the open).
- **The task list:** one commit per subsection, in slices of 150–430 lines, the introductions and
  `intro.tex` last (principle F); the PI approved it, 2026-10-03.
- **Default (a):** promoted to `blueprint/AUTHORING.md` *Proof verbosity* (the PI's ruling and
  2026-10-03 amendment stay verbatim above, under *Autopilot: for the PI*).
- **Defaults (b)–(d):** (b) and (c) were already `blueprint/AUTHORING.md` principles D and B;
  (d) promoted to principle E.
- **(e) The register and (f) terminology:** promoted to `blueprint/AUTHORING.md`'s clauses of
  2026-10-03 (A, C, E, F).
- **The invariance check** (gate 3) sees what `checkdecls` and `lint.sh` cannot, and ignores node
  order.
- **Formalization notes:** a note left with no Lean divergence is deleted, label and all; a note
  stays on its side of a proof, as plasTeX attaches a proof to the environment just before it.
- **Rungs:** from task 5 every section task ran Opus, fresh per task, after Sonnet's tasks 3 and 4
  each needed an Opus corrective (`notes/dispatch-log.md`).
