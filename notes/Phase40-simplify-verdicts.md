# Round 4's verdicts, `40-simplify` (Stop 2's inputs)

The recon tasks' verdicts, the input to Stop 2. They lived in the work log,
`notes/Phase40-simplify.md`, under *Verdicts*, until task 4 moved them here to keep the log short
(that log's *Decisions*, 2026-10-04; tasks 1–3's subsections are verbatim). Each recon task adds a
subsection, `### Task N (X)`, with one entry per input it owns, in the format under the log's
*Scope and standing rules*, which bind this file too. Task 8 writes Stop 2 from it.

### Task 1 (L)

**The map** (*measured, script not retained*). The project's declaration graph at `4039ba02`, run
with `lake lean`: edges are `Expr.getUsedConstants` over types and values; matchers, `_proof_`,
`_auxLemma` and equation lemmas are expanded into their users, and constructors, projections and
recursors folded into their inductive. Of 3 221 project declarations, 2 380 feed the 19 main
results and 1 629 the two pencil headlines. A raw closure without folding (round 3's
`Liveness8.lean` method, checked and rerun) agrees on all 3 221 for both. The surface is 920
declarations: 778 in `Pencil/`, 96 that Phase 40 or rounds 1–3 added outside it, 18 more pins of
the two chapters, 28 more of D5's names.

**`q3`: 121 of the 920 feed no main result** (5 400 lines). With the 23 helpers outside the
surface that only they reach: 144 declarations, 5 963 lines, under 60 dead roots, none with a Lean
caller. Of the 799 live, 791 feed the pencil headlines and 8 feed only the other 17 results
(Phase 40's `mapExtensor` lemmas, `three_le_bodyBarDim_of_two_le`); nothing in `Pencil/` feeds
another result. Five `rfl` lemmas (four `@[simp]`) could serve `simp` with no trace in a term;
none is retired here, and trial deletion settles them. The 5 963 lines go as follows.

*Handed on (pinned clusters, decided by the task named):*
- **Task 2, 1 754 lines** (its `1a`–`1c-ii`): design §6's cluster under `_of_card`, 1 565 (it
  shares 746 with `q3a` and 43 with the girth chain); `pencil_conjecture_of_arms`, 78; two nodes
  the reduction layer `\uses` with no live pin, 111.
- **Task 3, 1 777 lines** (its entries): (a) three of the four parts the chapter's opening calls
  unused, the duality and cycle sections (366) and the girth chain (947); (b) eleven
  `main-component.tex` nodes with a caller-less pin, two of them on the headline's `\uses` ancestry
  with no live pin (337); (c) four nodes in other chapters (127).
- **Task 4, 153 lines.** `a7` (`thm:pencil-x0-closed-ear`, off the `\uses` ancestry; 118 with
  `pathVertex_shift`); `c9`'s halves, 15 and 20.

*Verdicts (the unpinned clusters and the two named sets):*
- **`r1`, delete the D5 debt's 29 off-headline names: GO for 27, NO-GO for the 2 pinned.** The 27,
  with two helpers only they reach, serve only the two-cut composition, built for smark's kernel
  attack, which design §6 retired; no blueprint text names them. 1 commit, Sonnet (a deletion in
  ⚠Z files): `TwoCut.lean` whole and 20 declarations elsewhere, 986 lines; nothing a reader sees.
  Keep the 2 (51 lines; two chapters cite their node). Moots `b2`, half of `b1`. Evidence: the map.
- **`b2`, the merged hub's `hne`: NO-GO.** Moot under `r1`: the hub and its one consumer,
  `weldedLoss_nonneg`, are in `TwoCut.lean`'s dead cluster. If the PI keeps that file: GO, 1
  commit, Sonnet, an unpinned statement (drop `hne`, its `have`, and `⟨u, hu⟩` at the call).
  Depends on `r1`. Spike: without `hne` the hub compiles warning-free, and at the consumer's call
  its conclusion is `rfl`-equal to the original's.
- **`q3a`, the kernel-route roots: GO with task 2's §6 verdict, else keep.**
  `hasGenericPencilRealization_of_independent_pencilRow_target` (`Escape.lean`, 129) and
  `pencilNondegFeasible_of_le_of_triangleFree` (`Steer.lean`, 42) serve only kernel (K)'s route.
  Retired with `_of_card`'s cluster they free 2 482 lines (`Escape.lean`, `Habitat.lean`,
  `WitnessGeneral.lean` whole); kept, they are its inputs if the PI reopens it. In that commit.
- **`q3b`, `pencilChartWF_standing_ofCoord_toCoord`: GO.** A Phase 39 leftover in `Steer.lean`'s
  live layer (27 lines): `exists_fillNbr_pencilChartWF_of_standing` takes its conclusion as
  hypotheses, which its callers build otherwise. In `r1`'s commit, Sonnet; nothing a reader sees.
- **`q3c`, the rest: NO-GO (keep), 255 lines.** API beside its definition: `Chart.lean`'s `cross₃`
  linearity lemmas, `Statement.lean`'s four scale-invariance iffs, seven short lemmas. A design
  witness: `exists_isNondegPencilRealization_parallel_pair` (`Pair.lean`, 90), cited in two live
  docstrings as the proof that feasibility could not replace `PencilPair`'s `G.Simple`.

Outside the surface, not this round's: 18 dead declarations (529 lines) whose headers were added
between Phase 39's open and Phase 40's, in none of the clusters above (one, 139 lines, is shared by
`_of_card` and an outside root); named in the commit message.

### Task 2 (R)

**The shape** (*read and measured, script not retained*; spikes run with `lake lean`). Every
conditional theorem in the layer concludes what `pencilPair_of_nonempty` proves outright:
`_of_card`'s exact statement, and `pencil_conjecture_of_arms`'s over an infinite field, compile from
the headlines. Over a finite field only `_of_arms` says more, with both its cases open there. So
they record routes; they are not results. The live layer is the induction and its lemmas, the bare
loop, base, cut and non-simple cases, the four definitions, and one conditioned-pair assembly that
both headlines can run. It lacks a node for the pair at a loop, on two bodies and at a cut edge: 42
live declarations (3 935 lines) are reached only through those three unpinned leaves, whose one
account is the proof of the off-route `thm:pencil-conditional-realization-pair` (`-pair` below;
`-main-component` likewise). Batching, for task 8: `c3`'s TeX carries `c2`, `m2`, `m4`, `m5`, `1c-i`
and `1b`'s node; one deletion carries `1a`, `1b` and `1c-ii`; `a2` last.

- **`1a`, design §6's conditional theorems, with `q3a`: a PI call (retire recommended).** Their
  conclusions are theorems now, and the PI cancelled the kernels' work; keeping the Lean "untouched"
  is the close's own **Decided** record (2026-09-29), not the PI's words, so retiring revisits it.
  *Retire:* the kernel statement leaves `c3`'s TeX, then 1 deletion (Sonnet, ⚠Z files), 2 482 lines
  (1 565 without `q3a`); moots `a4`, `c4`(a). *Keep:* no commit. Evidence: the map, spike.
- **`a4`, `pencilPair_of_habitat_ncard_eq_four`: with `1a`.** Retired, it goes with the cluster
  (879 lines, its largest proof, and the heartbeat bump). Kept: GO, 1 commit, Sonnet, ⚠Z,
  `_three`'s two substitutions (about 124 lines; both blocks confirmed in the proof), perhaps the
  bump; nothing a reader sees. Evidence: read, the map.
- **`c4`, `-pair`'s statement against its pins: GO, by part.** (a) The node assumes kernel (K) at
  a feasible `G` only, `hK` at every `G`, where at an infeasible one it asserts that `G′` has no
  generic realization. Kept: add `PencilNondegFeasible K G →` to `hK` in three signatures (two
  pinned), pass `hfeas` at its one call (spike compiles); 1 commit, Sonnet. Retired: moot.
  (b) "Strictly smaller" goes with `c2`. Depends on `1a`.
- **`c2`, `thm:pencil-reduction`'s cases: GO, restate the node to its pin.** The pin gives cases
  (iii)–(v) the property only at graphs on fewer vertices, and no proof needs more. Restate them so,
  and use the same phrase for "strictly smaller (such)" in the conditional nodes (`c4`(b)). 1
  commit, Sonnet, TeX; weakens a statement to its pin. A lexicographic hypothesis in the Lean would
  need adapters at every caller, for no consumer. Evidence: read.
- **`c3`, split `thm:pencil-conditional-realization-pair`: GO, one assembly.** `_of_arms_pair`
  is on `pencil_conjecture`'s chain. Generalized to every nonempty graph (no `hspan`,
  `[Nonempty α]`, `[DecidableEq β]`), it also proves `pencilPair_of_nonempty` in 3 lines (spike);
  the node states it. A new lemma pins the three pair leaves with the proof's first part; the kernel
  form follows `1a`. 2 commits, Opus; changes a pinned statement and the graph. Evidence: spike.
- **`c3a`, the headline's direct proof: NO-GO, an option for the PI.** `pencil_conjecture` is
  `pencilPair_of_nonempty` at a spanning graph (spike, one line), taking `X0Gen`, `x0Gen`,
  `pencilPair_of_X0`, `pencil_conjecture_of_X0` and `_of_arms_pair` (101 lines today) off the
  closure. But the PI chose the term (2026-09-28: "`pencil_conjecture_of_X0 x0Dist x0Gen`, the L0
  shape"), `formalization.yaml` says so, and it saves no line. Evidence: spike, the map.
- **`1b`, `pencil_conjecture_of_arms` (`thm:pencil-conditional-realization`): GO, retire.** No
  caller; over an infinite field the headline gives its statement (spike); the close's record does
  not name it. 1 commit, Sonnet, 78 lines, riding with `1a`'s deletion; the node and the
  subsection's closing paragraph go in `c3`'s. Changes the graph (`m2`). Evidence: map, spike.
- **`a2`, the six `[DecidableEq β]` binders: GO, a headline signature.** All six statements
  compile without the binder, by `classical` (spike, 0 warnings); `pencil_conjecture` becomes
  strictly more general. 1 commit, Sonnet, deleting the silencers: two sites if `1a`, `1b` and
  `c3` land first. The axioms harness re-runs. Depends on `1a`, `1b`, `c3`. Evidence: spike.
- **`m1`, `def:pencil-nondegenerate` to `lem:coplanar-hinges-concurrent`: NO-GO.** The threshold
  is motivation: `Graph.PencilHub` is `v ∈ V(G) ∧ 3 ≤ G.degree v`, and the lemma's pin feeds only
  the cycle realization. The edge would put `sec:pencil-cycle` under the headline, against the
  chapter opening's true claim; the lead-in's `\cref` is the link. Evidence: read, the map.
- **`m2`, edges to `lem:pencil-loop-case` and `lem:pencil-base-case`: GO, in `c3`.** `c3`'s new
  lemma `\uses` the three bare cases, whose pins its pins call. Without `c3`: add both to `-pair`'s
  proof, 1 commit, Sonnet, TeX. Evidence: the map.
- **`m3`, `lem:pencil-simple-of-noRigid`'s in-edge: GO, remove the call instead.** `_three` uses
  `hnoRigid` only to recover `G.Simple`, which its live caller has; restated from `G.Simple`,
  neither it nor the generic step names a no-rigid lemma (spike). `lem:pencil-three-bodies-no-rigid`
  and its pin (35 lines) retire; with `1a`, this node and its pin (62) too. 1 commit, Sonnet; an
  unpinned signature, the graph. Evidence: spike.
- **`m4`, `-main-component` to the pair theorem: GO, in `c3`.** After `c3` the pair theorem is
  the assembly both `-main-component`'s and `thm:pencil-conditioned-pair-nonempty`'s pins run; both
  get the edge. Evidence: the map, spike.
- **`m5`, the pair node drawn unfilled: GO, in `c3`.** The built graph draws it with no fill.
  Kept, the two notes follow the kernel node's proof; retired, they go. Alone: 1 commit, Sonnet,
  TeX. Evidence: measured.
- **`1c-i`, `lem:two-pencil-extension-iff`: GO, re-pin.** The iff has no caller, but its necessity
  half, `dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, feeds the hub bound of
  `lem:pencil-feasible-hub-conditions`, whose proof uses it with no edge. Pin it beside the iff and
  add that edge. 1 commit, Sonnet, TeX; the graph only. Evidence: the map, read.
- **`1c-ii`, `lem:pencil-base-parallel-pair`: GO, retire.** Its pin (exactly two edges) and the
  non-vacuity witness, 86 lines, have no live caller. `lem:pencil-base-case`'s pin calls the two
  lemmas this node's proof uses, so it `\uses` them instead. 1 commit, Sonnet, riding with `1a`'s
  deletion; the graph loses a node. Evidence: the map.

### Task 3 (N)

**The reading** (*read, and the pins' signatures `#check`ed; spikes run with `lake lean`, 0 errors,
0 warnings*). Four nodes disagree with their pins (`a1`, `c5`, `c6`, `c7`); reading the proofs
found two more (`c8`'s `-lifting-restrict` and `-contract-standing`). Batching, for task 8: one TeX
commit carries `m6`, `m7` (with `1c-i`), `c1`, the two-hubs edge and `c8`'s re-pins; one Lean
commit `c6` and `c7`; the 111 lines `c5`, `c8` and the polynomial retire go in `r1`'s deletion.

- **`sec:pencil-duality`, `sec:pencil-cycle` (task 1's (a)): NO-GO, keep.** Prior evidence stands:
  round 3 rewrote and kept both, and the chapter opening names them as unused (366 lines).
- **`sec:pencil-girth-chain` (task 1's (a)): with `1a`.** It is kept as a start for a proof of the
  kernels. *`1a` retires them:* GO, retire its 8 nodes and Lean, 947 lines (`MaximalChain.lean`,
  `Girth.lean`, `Motive.lean`'s girth-five lemma; 990 with the 43 shared with `_of_card`), in `1a`'s
  deletion, Sonnet; the graph loses the subsection, and `cor:block-rank-vertex-two-cut` keeps one
  citing chapter (`r1`'s premise for its 2). *Kept:* NO-GO. Evidence: the map, read.
- **`a1`, `lem:pencil-chain-side-connected`: with the girth chain.** Retired: moot. Kept: GO,
  strengthen the Lean. The `w′` count is a 12-line corollary by reversing the path (spike); pin it
  beside, and the formalization note goes. 1 commit, Sonnet; nothing a reader sees. Spike.
- **Task 1's (c), dead pins in other chapters: NO-GO, keep (127 lines).** Each is a clause of its
  node: Crapo–Whiteley's rigidity, genuineness and rescaling invariants, the polarity's dimension,
  rigidity and genuineness, KT 5.5's conclusion at every simple graph, the cut-vertex equality (its
  ≥ half is live). Evidence: read, `#check`.
- **Task 1's (b), six nodes with one caller-less clause: NO-GO, keep (100 lines).** Each dead pin
  is a clause, 11–27 lines: `-lifting-space-affine`'s `dim L(q) ≥ 3` (`cor:pencil-flat-x0` reads
  it), `-picture-local`'s admissibility, `thm:pencil-flat-rank`'s bound and equality case, the flat
  corollaries' second equivalence and vanishing deficiencies, `thm:pencil-jj-equality`'s `ℓ₀`.
  Evidence: the map, `#check`.
- **`def:pencil-configuration`'s polynomial (task 1's (b)): GO, retire.**
  `pencilNormalOfPicturePoly`, its evaluation and two helpers (32 lines) have no caller, and the
  definition does not state it; its docstring's use in `X0Gen` is false. With `r1`'s deletion,
  Sonnet; three pins stay; nothing a reader sees. Evidence: the map.
- **`c5`, `lem:pencil-selector-independent-scalar`: GO, retire.** At an admissible picture it is
  two lines from `-condition-linear`'s plane clause, its pin has no caller, and that proof cites it
  only "as in". Retire node and pin (52 lines), with `r1`'s deletion, Sonnet; the headline's
  `\uses` ancestry loses a node. Or keep it restated to its pin (drop "admissible"). The map, read.
- **`lem:pencil-x0-two-hubs-obstruction` (task 1's (b)): NO-GO for the node; GO, drop one edge.** A
  design witness, as `q3c`'s: three chapters cite it as why the generic statement goes through the
  reduction. Only `thm:pencil-x0-generic-attains`' proof `\uses` it, for that reason; without the
  edge it leaves the ancestry, as its pins (74 lines) have. TeX, batched. Evidence: the map, read.
- **`c6`, `lem:pencil-condition-linear`: GO, restate and pin the iff.** Its pencil-realization
  clause is `-config-distinct-realization`'s statement, and the iff's forward direction has no pin.
  Drop the clause (cite that node); pin `mem_liftingSpace_iff_coplanar`, 13 lines, whose half is the
  caller-less converse pin (spike). 1 commit, Sonnet; the node drops a clause another node states.
  Leave `-config-distinct-realization`. Depends on `c5`. Evidence: spike, `#check`.
- **`c7`, `lem:pencil-x0-main-picture-open`: GO, strengthen the Lean.** "`U` is Zariski-open" is
  the pin's proof run at any main picture: `IsMainPicture.exists_mvPolynomial` (nonzero at `q₀`,
  non-roots main, no `[Infinite K]`) compiles with it, and the pin becomes a 4-line corollary
  (spike). 1 commit, Sonnet, about +6 lines; pinned beside; no statement moves. Evidence: spike.
- **`c1`, split `lem:pencil-splitoff-curve`: GO, three one-pin nodes.** (1) keeps the label (two
  `SplitOff.lean` docstrings cite it); (2), the extension across `x`, follows it; (3), the lifting
  system's locality, goes after `def:pencil-weighted-lifting-system`, as `-picture-local` precedes
  the system. 1 commit, Sonnet, as round 1's task 19; graph +2 nodes, the theorem's three citations
  repointed; no strength change. Evidence: read.
- **`c8`, `lem:pencil-lifting-restrict` (6 pins): GO, restate to its pins.** Five proofs (the cut,
  three open-ear steps, the one-ear base) cite it for "a polynomial in the heights of `G′`, read at
  the restriction, is one in those of `G`" (`eval_restrictPoly`), which it does not state. Add the
  clause; pin one declaration per clause (three), leaving the map, its unfolding and `restrictPoly`
  unpinned. TeX, Sonnet; strengthens the node to its pins. Evidence: read.
- **`c8`, `thm:pencil-x0-bridge` (8 pins): GO, unpin five helpers.** Keep the step and its proof's
  two counts (`deficiency_induce_union_range_of_bridgePath`, the rank's `add_le_…_of_bridgePath`);
  the four `pathVertex` lemmas and `cutEdges_union_image_of_bridgePath` encode the path.
  `lem:pencil-bridge-fibre` keeps its lemma and `pathVertex`. TeX, Sonnet. Evidence: `#check`.
- **`c8`, `lem:pencil-contract-standing` (4 pins): GO, restate to two pins.** No proof reads
  "`G/H` is 2-edge-connected" (a smaller graph needs only the standing hypotheses; the pin has no
  caller, 27 lines), and "if `def₂(G[W]) = 0`, `H` satisfies them" is `-contract-standing-rigid` at
  `n = 2`, which its one reader can cite, as the additive step does. Drop both, retire the first
  pin; 1 commit, Sonnet; weakens the node to what its readers use. Evidence: the map, read.
- **`c8`, `lem:pencil-generic-steer` (4 pins): GO, unpin the helper.**
  `exists_coord_linearIndependent_pencilChartPoint_of_other_nonhub` (263 lines) is one step of
  (a), named there; three pins stay: the parametrization, (a), (b). No split: its two readers cite
  (a) and (b) by part, and both need the parametrization. TeX, Sonnet. Evidence: read.
- **`c8a`, seven more nodes with four or more pins: NO-GO here.** `def:pencil-nondegenerate`,
  `lem:pencil-x0-one-witness`, `thm:pencil-x0-main-component`, `lem:pencil-jj-rescale`,
  `lem:pencil-jj-embed-edges` (11), `thm:pencil-jj-equality`, `lem:pencil-chain-span-certificates`:
  mostly one pin per clause. For the principle-D audit queued with **PROSE**. Evidence: measured.
- **`m6`: GO.** `thm:pencil-x0-theorem-s`'s proof cites `lem:deficiency-zero-connected`, whose pin
  `two_le_degree_of_isKDof_zero` its pin calls: add the edge. TeX, batched. Evidence: the map, read.
- **`m7`: GO.** `lem:pencil-generic-steer`'s proof cites `lem:pencil-feasible-hub-conditions`
  twice, and its helper pin calls both halves of that node's pin: add the edge, with `1c-i`. TeX,
  batched. Evidence: the map, read.

### Task 4 (E)

**The reading** (*read; two spikes, not retained, run with `lake lean`: 0 errors and 0 warnings,
every re-derived step at the three standard axioms*). The seven steps choose their configuration in
four ways: a certificate inside one fibre (the cycle, `k ≥ 5`, `k = 2`); the incidence, the ear
body's picture chosen with the heights (`k = 1`, `Graph.exists_oneEar_base`); an antecedent and an
insertion (`k = 3`, `k = 4`, ORBIT's `k = 2`); the cut step with the cycle (the closed ear). `r5`
stands, and `q1a`'s helper follows it: unpinned, named by the two proofs. Batching, for task 8:
`q1a` is one Lean commit on its own; `c9` rides with `r1`'s deletion and task 3's TeX commit. For
task 7: the open-ear steps are walked, and beyond `q1a` their length is their argument.

- **`q1`, the open ears as one argument: NO-GO.** They diverge where the configuration is chosen
  (above). The cycle leaves the certificate family at `G[V₁]`, an edge: never admissible, so no
  `X0Attains`; its rank and relative screws are the path's, every height lifts, and the count is the
  partition into single bodies. `k = 1` shares only the count (about 35 lines); a count lemma under
  it and `q1a` would net under 10 lines (estimated), so left. Evidence: read, the two spikes.
- **`q1a`, one certificate step for `k ≥ 5` and `k = 2`: GO.** `Graph.X0Attains.of_openEar_of_cert`
  takes `n` ear links independent at a certificate whose heights lift at every admissible picture,
  and `(⋆)` at `n`; it holds both steps' picture, fibre intersection and count, as `-two`'s proof
  already says. 1 commit, Sonnet (the spike is the build; not ⚠Z); no statement moves. Spike:
  345 → 294 lines, about −43 with a docstring; −76 with the certificate through `certHeights`.
- **`q1b`, one second stage for the antecedent steps: NO-GO, it nets about 8 lines.** SHORT's
  assembly and ORBIT's `k = 2` share round 2 and the count, but the shared lemma (spiked at both
  call sites) states the base data in 35 lines: 103 lines for 111. Before that they diverge at the
  base: ORBIT's antecedent has a one-body ear, whose body lies on both end planes, so no ear data
  serve both graphs, there is no round 1, and both bodies move (`exists_insertion_two`). Not ⚠Z.
- **`a7`, `Graph.X0Attains.of_closedEar`: NO-GO (keep); the PI may revisit.** The PI kept it as a
  named theorem, knowing the coverage never consumes it (decision 2, 2026-09-27,
  `notes/Phase40g.md`); task 1's 118 lines are no new argument. No retarget: the coverage reduces at
  a cut vertex or a bridge chain directly. Retired: 1 commit, Sonnet, not ⚠Z; the node goes, and the
  section's opening and `rem:pencil-x0-ear-class` drop the closed ear. Evidence: read, the map.
- **`c9`, the two caller-less toolkit halves: GO, retire both.** No proof reads them:
  `lem:pencil-line-pairing-join`'s readers use the determinant, `lem:pencil-insertion`'s the gain
  half or its argument. Drop the nondegeneracy clause and the no-loss half with their pins (15 and
  20 lines), as task 3 did at `-contract-standing`. 1 commit, Sonnet (a deletion, not ⚠Z work),
  batched as above; weakens two statements to what their readers use. Evidence: the map, read.

### Task 5 (A)

**The reading** (*measured, scripts not retained*; spikes run with `lake lean`, 0 errors, 0
warnings). At statement level: no `Pencil/` declaration's type is alpha-equivalent to any other
theorem's in the environment (814 against 179 698). By shape, the weighted constants of their types,
the 680 `Pencil/` theorems against the project's other 2 107: the 110 with a match at 0.7 or more
screened by statement, the candidate pairs read in full; the rest are siblings (a join lemma beside
its meet) or corollaries already calling the outside lemma. `exact?`'s search, all solutions kept,
on the 118 whose statements name no `Pencil/` constant: of the 107 that finished, an outside lemma
closes only `screwComplementIso_mk_extensor`, which is `ScrewSpace.ext rfl` (compiled; a carrier
`rfl`, a local golf, not proposed); 11 timed out. Three re-proofs besides round 2's hub
normalization, `q2a`–`q2c`; the matches in `1a`'s cluster are moot if it retires. Batching, for
task 8: `q2b`, `q2c` and `a3` are one Sonnet commit outside the zone; `q2a` and `b1` one ⚠Z
commit, after `r1`'s deletion if it lands. For task 6: `q2d`.

- **`q2`, where `Pencil/` re-proves: GO for `q2a`–`q2c` only.** The rest of the surface states
  pencil facts, or corollaries of the outside lemma it calls (`deficiency_induce_union_singleton`
  runs KT 3.6's cut split); `exists_extend_linearIndependent` has no mathlib form (FRICTION). Two
  commits, below. Evidence: the screens above.
- **`q2a`, `Theorem55.lean`'s private cut-edge bricks: GO, keep one copy.** `Arms.lean` copies all
  four in public: the side span and the two endpoint lemmas verbatim, the rank assembly without
  minimality. With `hG` weakened to `hc : G.deficiency n = c`, Theorem55's assembly gives both
  statements (spike). Publish its four under Arms' names, delete Arms' (100 lines): 1 commit,
  Sonnet, ⚠Z (mechanical); nothing a reader sees (none pinned). Evidence: spike, read.
- **`q2b`, the perp's dimension, proved three times: GO.** `Meet.lean`'s pair, `Motive.lean`'s
  triple and `Statement.lean`'s single `finrank_toDualPerp_*_eq` run one dual-annihilator proof,
  and `Arms.lean`'s two `≤` forms are hand-derived. One lemma,
  `finrank (⨅ j, ker …) + finrank (span (range n)) = N`, gives all five in 3–8 lines (spike).
  1 commit, Sonnet, not ⚠Z; about −45 lines; nothing a reader sees (none pinned). Evidence: spike.
- **`q2c`, `exists_common_eval_ne_zero_of_forall_exists`: GO, in `q2b`'s commit.** `Engine.lean`'s
  proof repeats the product argument of the project's mirror
  `MvPolynomial.exists_eval_ne_zero_of_forall_ne_zero`; called, the body is 3 lines, not 11
  (spike). Sonnet, not ⚠Z; nothing a reader sees. Evidence: spike.
- **`q2d`, `Arms.lean`'s cut case against `Theorem55.lean`'s: NO-GO here; for task 6.** The core
  (407 lines) follows `case_cut_edge_realization_gen` (266) step for step. Past `q2a` they share
  only the edge classification (a link lies in a side or is the cut edge), derived inline in each
  arm; the points, distinctness and repositioning (204 lines) are pencil-only. A shared
  classification lemma is ⚠Z producer work: task 6 weighs it with `a6`. Evidence: read.
- **`b1`, `.compl` in the two hubs: GO, after `r1`.** Restated with `ᶜ` (definitionally equal),
  both hubs and all three consumers need no bridge (spike). With `r1`: one statement, the pinned
  PanelLayer hub (its node already reads `|B ∖ V(G)|`), three bridges, −5 lines; without, two and
  five, −9. 1 commit, Sonnet, ⚠Z (`PanelLayer.lean`, `GenericityDevice.lean`; mechanical); a pinned
  signature's form, not its strength. Depends on `r1` for its size only. Evidence: spike.
- **`a3`, the degree-sum pair: GO for `two_mul_ncard_le_ncard_edgeSet` only.** Round 1's missing
  constant sum is in the build, `finsum_mem_const` (Matroid's `ForMathlib/Card.lean`); with
  `Set.Finite.ncard_biUnion` that proof needs no `Finset`, 42 → 25 lines, no new lemma. Its partner
  goes 27 → 12 over two new mirrors (13 lines), so stays. 1 commit, Sonnet, not ⚠Z; nothing a
  reader sees. Evidence: spike.

### Task 6 (P)

**The reading** (*read; four spikes, kept in `scratch/40-simplify/6/` (gitignored) for the
landings, run with `lake lean`: 0 errors and 0 warnings, each re-derived declaration at the three
standard axioms and proving the original's exact statement*). All three sites are live and outside
`1a`'s cluster (task 1's graph): #4 and #6 feed `pencilPair_of_not_twoEdgeConnected`, the core both
cut-arm wrappers, Theorem55's cut case `theorem_55_minimalKDof_gen`. Both shapes are cheaper than
round 1 sketched. #6's avoidance target is #4's cover at a hub, so the shared tail takes only the
hub transfer as a parameter; the core's `|C| = 0` branch is its `|C| = 1` assembly at the
identity, a split Theorem55's cut case repeats (`a6a`). Batching, for task 8: `a6` and `a6a` are
one ⚠Z commit, which moves `Graph.eq_cutEdge_of_isLink_crossing` and
`Graph.eq_and_eq_of_isLink_crossing` from `Motive.lean` to `Deficiency.lean` (beside `cutEdges`,
upstream of both files); `a5` is another; both before `q2a`, whose rank-assembly calls then number
four in `Pencil/`, not six, and two in Theorem55, not three. For task 7: #5 and `Pair.lean`'s
`|C| = 0` producer glue as the core's two branches did (not spiked here).

- **`a5`, one tail for `Pair2.lean`'s #4 and #6: GO.** #4's cover is `{point₁ u_c, 0}` at a hub,
  #6's whole target, and an `H`-hub is a `G`-hub; so one lemma, with no degree hypothesis, takes
  only conjunct 3 on `V₁`: #4's hub transfer proves it, #6's `hpromoted` and its own transfer. 1
  commit, ⚠Z, Sonnet transcribing the spike (Opus if re-derived); 847 → 541 lines, about −295 with
  a docstring; nothing a reader sees (neither is pinned). Evidence: spike (`A5.lean`).
- **`a6`, the core's `|C| = 0` and `|C| = 1` branches: GO, one assembly.** `|C| = 0` is the
  `|C| = 1` assembly at the identity repositioning and a junk hinge: obtain `(g, h, C)` with each
  crossing link's incidences and distinctness (vacuous at `|C| = 0`), then one tail; no new lemma.
  1 commit with `a6a`, ⚠Z, Sonnet transcribing the spike; 376 → 227 lines (−149; −146 without the
  move); nothing a reader sees (statement unchanged). Evidence: spike (`A6b.lean`, `A6.lean`).
- **`a6a`, Theorem55's `case_cut_edge_realization_gen`: GO, the same shape.** Its two branches
  repeat the links, spans and rank; one hinge `C` for every crossing link (`0` at `|C| = 0`, as
  `HasPanelRealization` asks nonzero only on links) leaves one tail: 244 → 129 lines (−115). In
  `a6`'s commit, ⚠Z, Sonnet transcribing; spiked on `q2a`'s public bricks (the private names serve
  the same); nothing a reader sees (pinned; statement unchanged). Evidence: spike (`Q2d.lean`).
- **`q2d`, a shared edge-classification lemma: NO-GO, about 8 lines a site.** After `a6` and `a6a`
  the two cut cases share a shape, not a lemma: "a link in neither side crosses" costs 11 lines and
  saves 18 at Arms' two sites and 9 at Theorem55's (spiked at both): −16. A glued-extensor rank
  lemma would take about 10 of each site's 20–29-line rank block (estimated). Without `a6`/`a6a`,
  roughly −60 (estimated; 1 commit, Sonnet, ⚠Z): re-weigh then. Evidence: spike (`Q2dLemma.lean`).

### Task 7 (G)

**The reading** (*measured, script not retained*; five spikes, kept in `scratch/40-simplify/7/`
(gitignored) for the landings, run with `lake lean`: 0 errors and 0 warnings, each re-derived
declaration proving the original's exact statement at the three standard axioms). The re-rank,
round 1's method at `4039ba02` (the Lean is unchanged): `_four` 852 (`a4`), the normal witness 462,
#5 443, #4 443 and #6 404 (`a5`), #7 401, the core 376 (`a6`), ORBIT's `k = 2` 368 (task 4),
`_three` 361, `deficiency_eq_of_vertexTwoCut` 338 (`r1`), the point witness 329, `of_splitOff` 328,
`of_additiveContract` 302, GenericEar's producer 284, (MC-188) 263, v-f-6 246. Nothing rose; five
enter the walk as owned proofs leave it. Walked against their blueprint proofs: those ten, task 6's
hand-on, and CONTRACT-R (222), the case CONTRACT-A generalizes; the eleventh,
`hasPencilRealization_of_not_simple` (244), was not. Two proofs re-prove Phase 40 lemmas (`7a`,
1 300 lines; `7c`), one glue is written four times (`7b`), and one theorem is another's special case
(`7d`). Batching, for task 8: `7a` one ⚠Z commit (its larger form after `a5`); `7b` one ⚠Z commit
after `a6` (and `a5`); `7c` in `1a`'s deletion with `m3`; `7d` after the PI's call. Task 7 moves no
statement.

- **`7a`, the pendant cut at degree three by `lem:pencil-generic-steer`: GO.** v-e, v-f-6 and both
  Witness.lean witnesses are its (a) and (b) at `G − v_c`, as `-pair`'s proof and the one-ear and
  triangle steps run them: re-derived, the discharge takes 104 lines for 47 and frees 1 300 (−1 240,
  spike `A7a.lean`). After `a5`, one route for every degree also retires #4, #6 and the discharge:
  −1 470 more (`A7aB.lean`). 1 commit, ⚠Z, Sonnet transcribing; unpinned, nothing a reader sees.
- **`7b`, one glue for a cut's two realized sides: GO.** The glued data, links, nonzero facts and
  rank, written out in the `|C| = 0` producer, #5 and the core, become one lemma (115 lines with
  `HasPencilPanelRealization.restrict`): 213 → 107, 443 → 324, 227 → 124 after `a6`; −213 (spike
  `Glue.lean`), and about −70 more at `a5`'s tail (estimated). 1 commit, ⚠Z, Sonnet transcribing
  the three spiked sites; nothing a reader sees. Depends on `a6` (and `a5` for the fourth site).
- **`a6b`, `a6`'s shape at `Pair.lean`'s two producers: NO-GO; their shared part is `7b`.** Unlike
  the core's branches they take the IH at different graphs (`G[Vᵢ]`; `G[Vᵢ ∪ {far}]` with the drop
  brick) and carry conjuncts 2–4 differently (wholesale; boundary identities and the avoidance), so
  one theorem would split twice inside. Evidence: read, with the dispatch shell.
- **`7c`, `_three` re-proves `linearIndependent_pointJoin_triangle`: GO with `1a`.** Its 75-line
  wedge detector is that lemma once its hinges are `pointJoin`s: 361 → 287 (spike `Three.lean`).
  The lemma sits downstream; with `1a` retired, `_three`'s one caller is `Statements.lean`, and it
  moves into `MainComponent/`. In `1a`'s deletion with `m3`, ⚠Z, Sonnet; nothing a reader sees.
  With `1a` kept: NO-GO (the lemma's chain, `pointJoin` and the Klein pairing, would move up).
- **`7d`, CONTRACT-R a corollary of CONTRACT-A: GO for the Lean; a PI call for the chapter.** At
  `def₂(H) = 0`, `X₀(H)` attains by the flat case and additivity is `def₂`'s conservation: 238 → 22,
  and 122 lines only it reads go (spike `ContractR.lean`; the map). 1 commit, Sonnet, not ⚠Z; the
  statement stays. The chapter proves KT's Lemma 6.3 first: keep that proof (`-core-plane`,
  `-core-rank` and a `-limit` clause lose their Lean), or state R as A's corollary and retire them.
- **`7e`, #7 (`GenericTriangle.lean`): NO-GO.** Length is the argument: seven link cases, three
  incidences each, the triangle's rigidity and the cut-vertex rank. Its `hinPanel`/`hthruPt`
  helpers, repeated in GenericEar's producer, are a local golf. Evidence: read.
- **`7f`, `of_splitOff`: NO-GO.** It follows its proof step for step: counts, picture, flexes,
  dichotomy, curve, special rank, limit. Evidence: read.
- **`7g`, `of_additiveContract`: NO-GO.** Length is the argument (two kernel bounds, two open
  conditions, the section, the collineation, the coupling); with `7d` it serves both contractions.
- **`7h`, GenericEar's producer: NO-GO.** Length is the argument. A lemma for the `V₁` half that
  it, #7 and `a5`'s tail share would net roughly 60 lines (estimated from the three, not spiked).
- **`7i`, (MC-188), `GenericSteer.lean`: NO-GO.** The seed's combinatorics are its argument; its
  near-copy, the point witness, retires with `7a`; the `w₁`/`w₂` mirror is a local golf.
