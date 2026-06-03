# Phase 20 — Combinatorial induction → Theorem 4.9 (work log)

**Status:** ✓ complete. Capstone `thm:minimal-kdof-reduction` (KT Theorem 4.9,
`Graph.minimal_kdof_reduction`) green, axiom-free; commit H landed 2026-06-03.
Off-critical-path forest-surgery `-split` track (KT 4.1) is also fully landed
(2026-06-03 addendum). The compressed multi-route narrative lives below; the
commit-by-commit play-by-play is in git history (`e8ca530`…`144e3b5` and the
preceding `9f7f071`…`f51417a`).

This phase is stratum 4 of the molecular-conjecture program (KT §3 Lemmas
3.4/3.5 full forms, §4). Program-level plan, reuse map, citations, and risk
register: `notes/MolecularConjecture.md` *Phase 20*. Forward-mode dep-graph /
lemma index: `blueprint/src/chapter/molecular-induction.tex`
(`sec:molecular-induction`).

## Current state

Theorem 4.9 (`Graph.minimal_kdof_reduction`) is green, axiom-free, stated as
the well-founded induction principle the reduction dichotomy + the `|V|`
measure drive. Everything on its critical path is green `\leanok` in
`Molecular/Induction.lean` (all axiom-free):

- **Inherited KT 3.4 + 3.5 chain.** `lem:circuit-induces-rigid` (3.4, two
  decls: tightness `circuit_induces_isTight` + rigid-subgraph packaging
  `circuit_induces_isRigidSubgraph`), then the matroid-side 3.5 chain
  `lem:rigid-full-rank` → `lem:contract-rank-bridge` →
  `lem:contract-deficiency-conservation` → `lem:contract-minimality-transport`
  → `lem:contraction-minimality` (no graph↔matroid `map`).
- **Four graph operations** `def:induced-span` / `def:graph-operations`
  (`removeVertex` / `splitOff` / `edgeSplit`) / `def:rigid-contraction`.
- **Deficiency route to dof-tracking** (the *Replan*; commits B–E): the
  splitting-off bounds `splitOff_deficiency_{le,ge}` and the removal bound
  `removeVertex_deficiency_ge`, assembled into `dof_tracking` — all partition-
  count comparisons through the green `def = corank` bridge
  (`rank_add_deficiency_eq`), no forests.
- **KT 4.5–4.9 critical path** (commits F–H): `no_rigid_edge_count` (4.5(i)),
  `exists_degree_{le,eq}_two` (4.6), `lem:reduction-measure`,
  `splitOff_isMinimalKDof` (4.8(i)), and the capstone.

**Off the critical path, all landed (forest surgery, *Replan* Step 5):** the
KT 4.1 splitting-off direction `lem:forest-surgery-{count,split}` is green
(corrected non-vacuous construction; see *Forest surgery: the over-claim and
its repair*). KT 4.2 (`lem:forest-surgery-unsplit`) stays deferred — sound, no
balanced-packing gloss, not needed by Thm 4.9.

Per-lemma rationale and the `D ≥ 1/2/3` side-condition split are in the *Lemma
checklist*; cross-cutting lessons are in *Promoted to …*.

## Findings (the phase's genuine mathematical results)

### KT Lemma 4.1 / 5.1 is over-quantified, and its proof glosses a balanced-packing assumption

Sources verified directly: KT 2011 (*A proof of the molecular conjecture*, DCG
**45**:647–700) **Lemma 4.1, p.660**; KT 2009 arXiv predecessor **Lemma 5.1,
p.11** (essentially verbatim, makes the gloss *more* visible). The molecular
conjecture and KT's overall proof are **not** in question; the finding is
narrow and three-layered:

1. **Statement-as-quantified — false, formally disprovable.** Both versions
   read "for any independent set `I` of `M(G̃)` … there exists `I'` with `|I'|
   = |I| − D`." For `|I| < D` (e.g. `I = ∅`) this demands `|I'| < 0`. The
   intended quantifier is over **bases**. Formalized as
   `Graph.kt_lemma_41_overquantified` (`ex:kt-41-overquantified`; `I = ∅`,
   ℕ-cardinality: no `I'` with `|I'| + D = 0` for `D ≥ 1`).
2. **Proof of the intended base case — unjustified step, now discharged as a
   GAP not an error.** "Convert each `Fᵢ` to `F'ᵢ`" (2011) / `2h'+(D−h')=h`
   (2009) silently assume the chosen `D`-forest packing is **balanced at `v`**
   (every forest meets `v`). KT omits a justification; we recovered one (see
   the *VERDICT* below).
3. **Intended content — true.** The induction (KT 4.3) consumes the deficiency
   inequality `def(G̃ᵥᵃᵇ) ≤ def(G̃)`. Proved by partition-count comparison
   through `rank_add_deficiency_eq`, bypassing the forest surgery (*Replan*).

**Writeup principle (the blueprint Remark `rem:kt-lemma-41` follows this).**
Three-layer framing: (1) affirm KT's result + stature; (2) distinguish
statement-as-quantified-false / proof-glosses-balanced-packing / intended-
content-true; (3) phrase as "KT omits / we did not recover", **never** "KT
errs". Cite KT 2011 Lemma 4.1 p.660 + KT 2009 Lemma 5.1 p.11.

**VERDICT (2026-06-03): the balanced-packing gloss is a GAP, not an error —
resolved positively for all `D`.** The mechanism turns on `v` having degree 2:
a forest avoiding `v` has `v` isolated, so a free `v`-fiber `x : v—w` is a
*pendant* (bridge) of that forest and can be absorbed without creating a cycle.
A finite descent then makes every forest meet `v`. There is **no `D ≥ 3`
counterexample**; the earlier "`D = 2` balanced, `D ≥ 3` open" framing was too
pessimistic. Formalized in four green nodes: counting half
`lem:base-vfiber-count` (`isBase_vfiber_ncard_ge`: a base meets ≥ D fibers — no
pigeonhole obstruction), redistribution kernel `lem:acyclic-insert-vfiber`
(`acyclicSet_insert_vfiber_of_not_inc`), rebalancing move `lem:packing-move`
(`exists_packing_move_of_not_inc`), and the descent's outer loop
`lem:balanced-forest-packing` (`exists_balanced_forest_packing`).

### Finding 2 (KT 4.4) was self-refuted same day

An earlier 2026-06-03 analysis (commit `d44789e`) concluded `lem:removal-
deficiency` (KT 4.4, `def(G̃ᵥ) ≥ k`) is *not* a deficiency-counting fact and is
gated on the `h'=0` unsplit forest surgery. **That was wrong** (refuted in
commit `fa4544d`). Two flaws: (1) the `−(D−1)·d` sign in `partitionDef` makes a
*larger* crossing-drop *raise* the deficiency — dropping `d` is the *helpful*
direction, not "the wrong direction"; (2) in the part-losing case (`v`
isolated), `v`'s neighbours `a, b` are *forced* into distinct blocks, so both
`va` and `vb` cross — `c = 2` is forced. The clean partition-count comparison
goes through with `2 ≤ bodyBarDim n`: the `+2(D−1)` crossing-drop pays for the
`−D` part-loss exactly when `D ≥ 2`. `removeVertex` is structurally simpler
than `splitOff` (no fresh `e₀`/`ab` edge), so the proof is shorter than
`splitOff_deficiency_ge`. KT did not err — KT's `h'=0` unsplit-forest route is
a sound alternative; we just found a shorter count. (KT 2011 Lemma 4.4 is on
**p.662**, verified against the `.refs/` PDF; an independent scrutiny pass had
mis-placed it on p.661. Lemma 4.5 is on p.663.)

**Lesson for both findings: prefer the deficiency-count route over the forest
surgery.** The substantive content the induction needs is the deficiency
inequality, provable by partition arithmetic on green `def = corank`
infrastructure. The forest surgery is a recoverable but heavier alternative
KT's proof leans on; we route around it on the critical path.

## Replan (2026-06-02): route splitting-off via deficiency-counting

The viable route is a direct comparison of the deficiency max-formula on green
infrastructure (`def(G̃) = max_P [D(|P|−1) − (D−1)·d_G(P)]`; `rank M(G̃) +
def(G̃) = D(|V|−1)`). It is **NOT** matroid contraction — `Gᵥᵃᵇ ≅ G/va` does
*not* give a clean single-element minor of `M(G̃)` (the count matroid's rank
drops by `D` per removed vertex, not 1). Each bound is a partition extension /
restriction comparison; details in the relevant checklist entries.

## Forest surgery: the over-claim and its repair (off critical path)

Commit `c3df62f` flipped `lem:forest-surgery-split` green via a vacuous
`Graph.forest_surgery_split`: its `hr_inj : Fin D ↪ {e₀} × Fin (D−1)` is
unsatisfiable (codomain `D−1 < D`), and it assumed away the `dᶠ(v)=1` forests.
Reverted in `588af95`; the corrected non-vacuous construction landed in
`876f6d3`.

**The corrected surgery** (no source supplies it — reconstructed). A balanced
packing's forests are each `dᶠ(v) ∈ {1,2}`. A `dᶠ=2` forest swaps its `a–v–b`
path for one `ã̃b`-copy (cycle-lift, `lem:reroute-cycle-lift`); a `dᶠ=1` forest
drops its lone `v`-fiber and adds no copy (verbatim transport of the `v`-free
part, `lem:reroute-vfree-transport`). Balance ⟹ every forest shrinks by exactly
one ⟹ `|I′| = |I| − D` (`forest_surgery_count`, stated additively), and the
def\,=\,corank identity (one fewer vertex) gives `def(G̃ᵥᵃᵇ) ≤ def(G̃)`
(`forest_surgery_split`). The closing **narrative-bridge shim**
`splitOff_deficiency_le_of_forest_surgery` (`@[deprecated splitOff_deficiency_le
(since := "narrative-bridge")]`, `cor:forest-surgery-deficiency`) records that
the forest route reaches the *same* bound the critical-path
`splitOff_deficiency_le` delivers — API anchor, no caller.

## Architectural choices made up front

- **New file `Molecular/Induction.lean`.** Per the one-`.lean` / one-`.tex` per
  molecular phase convention (post-Phase-18 cleanup split). Carrier: mathlib
  core `Graph α β`.
- **Graph operations as `Graph α β` constructions, reusing the matroid layer.**
  Splitting-off / edge-splitting / removal / rigid-contraction are graph-level
  ops; their *deficiency* behaviour routes through `M(G̃)` (Phase 19) +
  matroid restriction/contraction + fundamental circuits + the vendored union
  subsystem. `edgeMultiply` / `mulTilde` carry the `(D−1)·G` plumbing.
- **Forest surgery (4.1/4.2) was the planned hard core — deferred off the
  critical path** after the KT 4.1 gloss surfaced (see *Findings*). Theorem 4.9
  routes through the deficiency-count argument instead.

## Lemma checklist

Forward-mode: the authoritative node list is `molecular-induction.tex`. Tracked
here for hand-off convenience.

Inherited from Phase 19 (schedule early):
- [x] `lem:circuit-induces-rigid` — KT 3.4 full form: a circuit `X` induces a
  rigid `G[V(X)]`. Two Lean decls: tightness `|X−e| = D(|V(X)|−1)`
  (`Graph.circuit_induces_isTight`; lower bound the direct circuit-minimality
  fact `Graph.circuit_ncard_gt`, NOT `thm:def-eq-corank`), and the
  **rigid-subgraph packaging** `Graph.circuit_induces_isRigidSubgraph` (commit
  F): `(G.inducedSpan n X).IsRigidSubgraph G n`. The packaging pins `rank
  M(G[V(X)]̃) = D(|V(X)|−1)` from both sides (`rank_matroidMG_le` ∧ the
  independent `X−e` of tight size via `matroidMG_restrict_mulTilde` +
  `subset_edgeSet_mulTilde_inducedSpan`), then `rank_add_deficiency_eq` forces
  `def = 0`. KT 4.5(i)/4.8 invoke this form.
- [x] `lem:rigid-full-rank` — KT 3.5 rank core: rigid `H` attains `rank M(H̃) =
  D(|V(H)|−1)`. `Graph.rank_matroidMG_of_isKDof_zero`; 4-line corollary of
  `rank_add_deficiency_eq`.
- [x] `lem:contract-rank-bridge` — `rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)`
  (`Graph.contract_matroidMG_rank`) via `Matroid.rank_contract_add_rank_restrict`
  + vendored `contract_rank_cast_int_eq` + `matroidMG_restrict_mulTilde`.
- [x] `lem:contract-deficiency-conservation` — `D(|V(G)|−|V(H)|) −
  rank(M(G̃)/E(H̃)) = def(G̃)` for rigid `H ≤ G`
  (`Graph.contract_matroidMG_deficiency_eq`); `zify` + `linarith`. Matroid-side.
- [x] `lem:contract-minimality-transport` — every base of `M(G̃)/E(H̃)` meets
  every surviving edge-fiber (`Graph.contract_minimality_transport`), via
  `Matroid.IsBase.union_isBasis_of_contract`, NOT fundamental-circuit swaps.
- [x] `lem:contraction-minimality` — contracting a proper rigid subgraph
  preserves minimal `k`-dof (`Graph.contraction_isMinimalKDof`); 4-line
  conjunction. NO graph↔matroid `map` — matroid contraction `M(G̃)/E(H̃)`.

Graph operations:
- [x] `def:induced-span` — `G[V(X)]` from a fiber set `X`
  (`Graph.fiberSpan`/`inducedSpan`, via mathlib `Graph.induce`).
- [x] `def:graph-operations` — `removeVertex` / `splitOff` / `edgeSplit`.
- [x] `def:rigid-contraction` — `Graph.rigidContract` (`deleteEdges` + `map
  (collapseTo …)`).

Deficiency route to dof-tracking (**the critical path**):
- [x] `lem:splitoff-deficiency` — KT 4.3(i), both directions (commits B + C):
  `Graph.splitOff_deficiency_le` (`def(G̃ᵥᵃᵇ) ≤ def(G̃)`, partition extension `f
  = update f' v (f' a)`, crossing injection `e_b ↦ e₀`) and `splitOff_deficiency_ge`
  (`def(G̃) − 1 ≤ def(G̃ᵥᵃᵇ)`, restriction of an attained maximizer +
  `v`-isolation case split). Pins `def(G̃ᵥᵃᵇ) ∈ {def(G̃), def(G̃) − 1}`.
  Degree-2 encoded as two edges `eₐ`/`e_b` (the only `v`-incident edges) +
  fresh `e₀ ∉ E(G)`. KT 4.3(ii) ("which alternative") needs the deferred forest
  surgery — off the critical path, omitted.
- [x] `ex:kt-41-overquantified` — the over-quantification disproof
  `Graph.kt_lemma_41_overquantified` (named lemma since cleanup A3; was an
  anonymous `example`). Blueprint Remark `rem:kt-lemma-41` carries the framing.
- [x] `lem:removal-deficiency` — KT 4.4 (p.662): `def(G̃) ≤ def(G̃ᵥ)`. Commit D,
  `Graph.removeVertex_deficiency_ge`, deficiency-count route, `2 ≤ bodyBarDim
  n`. (Finding 2 refuted — see *Findings*.)
- [x] `lem:dof-tracking` — KT 4.3–4.5 assembly (commit E, `Graph.dof_tracking`):
  a 3-way conjunction over `splitOff_deficiency_{le,ge}` +
  `removeVertex_deficiency_ge` under `2 ≤ bodyBarDim n`. For a `k`-dof-graph:
  `k − 1 ≤ def(G̃ᵥᵃᵇ) ≤ k` and `def(G̃ᵥ) ≥ k`. `\uses` the deficiency bounds,
  NOT forest surgery.
- [x] `lem:no-rigid-edge-count` — KT 4.5(i) edge bound `(D−1)|E| <
  D(|V|−1)+(D−1)` (≡ `corank M(G̃) ≤ D−2`) for a minimal 0-dof-graph with no
  proper rigid subgraph. `Graph.no_rigid_edge_count`, `2 ≤ bodyBarDim n`. The KT
  eq. 4.3 fundamental-circuit swap: `h* = minₐ |ẽ∩B|` over bases (finite-min via
  `Set.exists_min_image`); `h* ≥ 1` from `IsMinimalKDof`'s base-meets-fiber
  clause. The `X∩ẽ≠∅` step (the prior "blocker") is a **direct base-meets-fiber
  contradiction**, NOT forest reasoning: if `X∩ẽ=∅`, `X−ej` is full-rank
  (`(D,D)`-tight on `V(X)=V` via `circuit_induces_isTight`), hence a base
  avoiding `ẽ` — contra `hG.2`. The exchange `B = insert f B* ∖ {ej}` drops
  `|B∩ẽ| = h*−1`. Support: `mulTilde_edgeSet_ncard`,
  `fundCircuit_inducedSpan_vertexSet_eq`, `circuit_induces_isRigidSubgraph`.
- [x] `lem:low-degree-vertex` — KT 4.6 **F″ core**,
  `Graph.exists_degree_le_two` (`3 ≤ bodyBarDim n`): ∃ a degree-`≤2` vertex.
  Average-degree `2|E| < 3|V|` (from `no_rigid_edge_count` ×2) + handshake `∑
  deg = 2|E|` + Finset pigeonhole. **Finding:** the multigraph degree +
  handshake already exist in the **vendored `apnelson1/Matroid`** package
  (`Graph.degree`/`handshake_degree_subtype`,
  `.lake/packages/Matroid/Matroid/Graph/Degree/Basic.lean`) — no new degree
  infrastructure built. See FRICTION (grep `.lake/packages/Matroid` before
  building any `Graph α β` graph-theory notion).
- [x] `lem:reducible-vertex` — KT 4.6, ∃ a degree-`exactly`-2 vertex (`3 ≤
  bodyBarDim n`, `|V| ≥ 2`). `Graph.exists_degree_eq_two`. The F″ core gives `≤
  2`; two-edge-connectivity (`two_le_crossingEdges_of_isKDof_zero`, KT 3.1)
  rules out `≤ 1`. **Cut↔degree bridge** (the only new piece): crossing edges of
  `{v}` are exactly the *nonloop* edges at `v`, so `degree v ≥ d_G({v}) ≥ 2` via
  vendored `Graph.degree_eq_ncard_add_ncard`. FRICTION: `cutLabeling V'` in a
  statement needs `[∀ x, Decidable (x ∈ V')]`.
- [x] `lem:reduction-measure` — KT Thm 4.9 well-founded measure (commit G step
  1): both reductions strictly shrink `|V|`
  (`Graph.splitOff_vertexSet_ncard_lt`; `rigidContract_vertexSet_ncard_lt`
  *needs `2 ≤ |V(H)|`* — collapsing a single-vertex `H` is a vertex no-op).
- [x] `lem:reduction-step` — KT 4.7–4.8 (commit G step 2). Node green, both
  `\lean{}` pins: splitting-off branch `Graph.splitOff_isMinimalKDof` (`k=0`),
  contraction branch `Graph.contraction_isMinimalKDof`. **The iterated
  fundamental-circuit swap is BYPASSED by a rank count:** KT's claim (4.10) =
  "`E(G̃_v)` is circuit-free in `M(G̃_v^{ab})`"
  (`Graph.circuit_splitOff_meets_fiber`) makes `E(G̃_v)` a base of `M(G̃_v)`;
  with KT 4.7 (`def(G̃_v)>0`) a single cardinality split of any fiber-avoiding
  base across `ã̃b ⊔ E(G̃_v)` forces a contradiction through
  `isBase_ncard_add_deficiency_eq`. No matroid minor, no swap induction, no
  forests; `2 ≤ bodyBarDim n`. Ground-set bridge
  `edgeSet_mulTilde_splitOff_diff_fiber` (`E(G̃_v^{ab})∖ã̃b = E(G̃_v)`). The
  `k>0` branch (KT 4.8(ii)) is off the critical path. Circuit-transport idiom +
  swap-bypass lesson in FRICTION (`[matroid] Transporting circuits …`).
- [x] `thm:minimal-kdof-reduction` — KT Theorem 4.9 (capstone, commit H).
  `Graph.minimal_kdof_reduction`, green, axiom-free. Stated as the well-founded
  **induction principle** the dichotomy + `|V|` measure drive: a motive `P`
  closed under the two-vertex base case, under splitting off a reducible
  degree-2 vertex, and under contracting a proper rigid subgraph *given the
  strong IH on every smaller minimal `0`-dof-graph* holds of every minimal
  `0`-dof-graph with `2 ≤ |V|`. Proof: strong induction on `|V|` (idiom →
  TACTICS-GOLF §11); dichotomy on `∃` proper rigid subgraph (Case I hands
  `hcontract` the existence + IH; Case II splits off via
  `splitOff_isMinimalKDof` and recurses on the smaller `splitOff`). **Two scope
  decisions** (both in the doc-comment): (i) the contraction branch is handed
  the IH rather than recursing internally — the graph↔matroid map from
  matroid-side `contraction_isMinimalKDof` to `(rigidContract).IsMinimalKDof`
  was deliberately not built (carry-forward 1); (ii) an explicit freshness
  premise `hfresh : ∀ G', ∃ e₀ ∉ E(G')` supplies each `splitOff`'s short-circuit
  edge. Support: `exists_splitOff_data_of_degree_eq_two`. Needs `3 ≤ bodyBarDim
  n`.

Forest surgery (**off critical path; `-split` track complete, `-unsplit`
deferred**):
- [x] `lem:forest-packing-decomp` — framing sub-node of KT 4.1/4.2: `I`
  independent in `M(G̃)` ⟺ covered by `D` cycle-matroid-independent fiber sets
  (`Graph.matroidMG_indep_iff_exists_forest_packing`). The matroid-base framing
  is *forced* by `matroidMG`'s union definition; also the engine of the
  deficiency route.
- [x] `lem:base-vfiber-count` — counting half of the balanced-packing assumption
  (`Graph.isBase_vfiber_ncard_ge`, `2 ≤ bodyBarDim n`): every base meets ≥ D of
  the `2(D−1)` fibers at a degree-2 vertex. Rank count
  (`matroidMG_restrict_mulTilde` + def\,=\,corank + `removeVertex_deficiency_ge`),
  not a forest reroute. Discharges the pigeonhole obstruction `h < D`.
- [x] `lem:acyclic-insert-vfiber` — redistribution kernel
  (`Graph.acyclicSet_insert_vfiber_of_not_inc`): a `cycleMatroid`-independent
  fiber set avoiding `v` stays independent after inserting a non-loop `v`-fiber
  (`v` deg 2 ⟹ `v` isolated ⟹ the fiber is a bridge). `cycleMatroid_indep` →
  `IsAcyclicSet` → `IsForest.of_deleteEdges_singleton` with the fiber a bridge
  (`IsLink.isBridge_iff_not_connBetween` + `Isolated.connBetween_iff_eq`).
- [x] `lem:packing-move` — the descent's rebalancing step
  (`Graph.exists_packing_move_of_not_inc`): move a `v`-fiber `x` from a forest
  holding ≥2 into a `v`-avoiding forest `Fs j`; recipient acyclic via the
  kernel, donors as subsets, union unchanged. FRICTION/TACTICS-QUIRKS §28
  (`↓reduceIte` vs `if_pos rfl` on the beta-redex'd goal).
- [x] `lem:balanced-forest-packing` — the descent's outer loop
  (`Graph.exists_balanced_forest_packing`): a base admits a `D`-forest packing
  with every forest meeting `v`. Disjointify the packing (mathlib `disjointed`
  over `Fin D`), then strong induction on the `v`-avoiding-forest count;
  pigeonhole (`isBase_vfiber_ncard_ge` ⟹ a donor with ≥2) + the move +
  disjointness keep the count strictly decreasing. Also exports pairwise-
  disjointness, consumed by `forest_surgery_count`. FRICTION:
  `Set.ncard_iUnion_of_finite` returns `∑ᶠ`, bridge via
  `finsum_eq_sum_of_fintype`.
- [x] `lem:reroute-vfree-transport` (`isAcyclicSet_splitOff_of_diff_fiberAtVertex`)
  — the `v`-free part of a balanced forest transports verbatim into `G̃ᵥᵃᵇ`, via
  `IsAcyclicSet.anti_inter` + `isAcyclicSet_mulTilde_splitOff_of_removeVertex`.
- [x] `lem:reroute-cycle-lift` (`isAcyclicSet_splitOff_reroute`) — the
  genuinely-hard `dᶠ(v)=2` cycle-lift. A `G̃ᵥᵃᵇ`-cycle through the inserted
  short-circuit copy `r` rotates so `r` is first
  (`WList.exists_rotate_firstEdge_eq`), substitutes `r` (joining `a,b`) by the
  `v`-traversing 2-path `a—pa—v—pb—b` of `G̃` (surviving `w'` lifts via
  `mulTilde_splitOff_deleteFiber_le`), giving a closed `G̃`-trail containing a
  `G̃`-cycle (`IsTour.exists_isCyclicWalk` + `IsSublist.edge_subset`) — contra
  `F` acyclic. FRICTION (`[matroid] Cycle-lift by edge-substitution…`) /
  TACTICS-QUIRKS §29.
- [x] `lem:forest-surgery-count` — KT 4.1 surgery count
  (`Graph.forest_surgery_count`): a balanced packing of a base `I` reroutes into
  a `M(G̃ᵥᵃᵇ)`-independent `D`-forest packing with `|⋃F'ᵢ| + D = |I|` (additive,
  ℕ-subtraction-free). Each forest `dᶠ(v) ∈ {1,2}` (≥1 balance; ≤2 via new
  plain-`G̃` per-edge subsingleton `fiber_inter_subsingleton_of_isAcyclicSet_mulTilde`
  on `eₐ`/`e_b`), so each shrinks by one. Fresh copies `r i = (e₀, (paOf i).2)`
  distinct across disjoint forests (no global pigeonhole).
- [x] `lem:forest-surgery-split` — KT 4.1 splitting-off direction
  (`Graph.forest_surgery_split`): `def(G̃ᵥᵃᵇ) ≤ def(G̃)`. The corrected
  non-vacuous construction (see *Forest surgery: the over-claim and its
  repair*). Take a base `B`, its balanced packing, reroute
  (`forest_surgery_count`): `rank M(G̃ᵥᵃᵇ) ≥ |B|−D`, and def\,=\,corank (one
  fewer vertex) + `linarith` give the bound — same conclusion as the green
  `splitOff_deficiency_le`.
- [x] `cor:forest-surgery-deficiency` — narrative-bridge shim
  (`Graph.splitOff_deficiency_le_of_forest_surgery`, `@[deprecated
  splitOff_deficiency_le (since := "narrative-bridge")]`): a one-line wrapper of
  `forest_surgery_split` exposing the forest route to the *same* bound the
  critical-path deficiency count delivers. API anchor, no caller. Pattern:
  `blueprint/CLAUDE.md` *Narrative-bridge corollaries*; canonical example
  `IsLaman.exists_rowIndependent_placement`.
- [ ] `lem:forest-surgery-unsplit` — KT 4.2, edge-splitting direction.
  **DEFERRED / off critical path.** Sound (no balanced-packing gloss) but not
  needed by Theorem 4.9: the removal bound it was thought to gate (KT 4.4) lands
  by the deficiency-count route instead (commit D, *Finding 2*).

(Off the Thm-4.9 critical path; schedule with Phase 21:) KT Lemma 3.2 (not
3-edge-connected), Lemma 3.6 (partition decomposition — needed only by Case
6.1).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Vertex-induced subgraph = mathlib `Graph.induce`, not hand-rolled.**
  `Mathlib.Combinatorics.Graph.Delete` has `Graph.induce (X : Set α)` with full
  API. `inducedSpan G n X := G.induce (G.fiberSpan n X)` is a thin wrapper.
  Reach for mathlib's `induce` before hand-rolling.
- **KT 3.4 lower bound is the direct circuit-minimality fact, NOT
  `thm:def-eq-corank`.** A circuit is a minimal dependent set, so every proper
  subset is `(D,D)`-sparse; the dependency at `X` itself gives `|X| >
  D(|V(X)|−1)` (`circuit_ncard_gt`). Matches KT's "see [21]". Blueprint `\uses`
  corrected to drop `thm:def-eq-corank`.
- **Graph operations: reuse mathlib where possible, structure-literal where
  not.** `removeVertex`/`rigidContract` are thin compositions (mathlib `map`
  realizes the vertex-collapse). `splitOff`/`edgeSplit` *add* edges/vertices and
  mathlib `Graph` has no union/`addEdge`, so they are structure literals with
  explicit fresh edge labels; need a distinctness guard (FRICTION).
- **KT 3.5: rank core then contraction arithmetic, all matroid-side.** The
  earlier worry — a graph↔matroid `(G/E(H))̃ ↔ M(G̃)/E(H̃)` map — turned out
  unnecessary: KT reasons entirely on the matroid contraction, so the
  statements are against `M(G̃)/E(H̃)`, not the collapsed `rigidContract`.
- **Routed around KT 4.1 via deficiency-counting** (see *Findings* + *Replan*):
  the substantive content is the deficiency inequality `def(G̃ᵥᵃᵇ) ≤ def(G̃)`,
  proved by partition-count comparison through `rank_add_deficiency_eq`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION

- *Strong induction on a derived measure (`|V|`)* → TACTICS-GOLF §11.
- *`↓reduceIte` vs `if_pos rfl` on a beta-redex'd `if`-goal* → TACTICS-QUIRKS §28.
- *Cycle-lift by edge-substitution (rotate-then-substitute)* → TACTICS-QUIRKS §29.
- *`ciSup_le` on `deficiency = ⨆ f, …` needs `rw [deficiency]` + `haveI :
  Nonempty α`* → FRICTION `[resolved] ciSup_le on deficiency …`.
- *No mathlib "base of `M／C` lifts via a basis of `C`" — route through
  `IsBasis'.contract_eq_contract_delete`* → FRICTION `[resolved] [matroid] no
  mathlib "base of M／C lifts …"`.
- *`IsCircuit.subset_ground` for `M(G̃)` is defeq-but-not-syntactic to `E(G̃)` —
  ascribe once* → FRICTION `[resolved] [matroid] IsCircuit.subset_ground …`.
- *Contraction rank arithmetic already in vendored `Matroid.Minor.Rank`
  (`contract_rank_cast_int_eq`, ℤ-subtraction RHS) — keep atoms ℤ-cast + `omega`*
  → FRICTION `[resolved] [matroid] contraction rank arithmetic …`.
- *Hand-rolled `Graph` with several fresh edge labels needs a distinctness
  guard* → FRICTION `[resolved] A hand-rolled Graph α β …`.
- *The vendored `apnelson1/Matroid` package already supplies multigraph
  `Graph.degree`/`handshake` — grep `.lake/packages/Matroid` before building any
  graph-theory notion* → FRICTION `[resolved] [matroid] The vendored … package
  already supplies a full multigraph Graph.degree …`.
- *Transporting circuits between `M(G̃)` and `M(H̃)`; the swap-bypass-by-rank-
  count idiom; `cutLabeling V'` in a statement needs `[∀ x, Decidable (x ∈ V')]`*
  → FRICTION (respective `[matroid]` entries).

## Blockers / open questions

None at phase close. All resolved (forest-surgery framing; the KT 4.1
balanced-packing GAP-not-error verdict; the KT 4.5(i) `X∩ẽ≠∅` swap core; the KT
4.4 removal bound) are folded into *Findings* / the checklist above.

## Hand-off / next phase

**Next phase = Phase 21 (algebraic induction, KT §5–6).** Theorem 4.9 is the
*combinatorial* skeleton; Phase 21 realizes it at the rigidity-matrix rank (the
algebraic-induction base + Cases I & II) — see `notes/MolecularConjecture.md`
*Phase 21* and `ROADMAP.md` §21 (planning). First concrete Phase-21 commit:
create `notes/Phase21.md` + open the Phase-21 blueprint chapter (forward-mode).

**Two Phase-20 carry-forwards**, both off the Theorem-4.9 critical path, to
schedule as Phase 21 needs them:

1. **Graph↔matroid contraction bridge.** `minimal_kdof_reduction`'s contraction
   branch is handed the IH rather than recursing internally, because
   `(G.rigidContract H r).IsMinimalKDof` is not yet derived from matroid-side
   `contraction_isMinimalKDof` (no `(G/E(H))̃ ↔ M(G̃)/E(H̃)` map — deliberately
   deferred). Needed only if the algebraic induction wants a fully graph-level
   recursion; otherwise the IH-handed form suffices and the bridge stays unbuilt.
2. **Forest surgery KT 4.2 (`lem:forest-surgery-unsplit`).** The `-split` track
   is complete (green); only the edge-splitting inverse stays deferred — sound,
   no balanced-packing gloss, not needed by Thm 4.9. The KT 4.1 balanced-packing
   assumption is fully discharged (GAP not error; four green nodes — see
   *Findings*).
