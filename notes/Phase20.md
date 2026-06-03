# Phase 20 — Combinatorial induction → Theorem 4.9 (work log)

**Status:** in progress.

This phase is stratum 4 of the molecular-conjecture program (KT §3
Lemmas 3.4/3.5 full forms, §4). The program-level plan, reuse map,
citations, and risk register live in `notes/MolecularConjecture.md`
*Phase 20*; read that first. This file carries Phase-20-local state,
the lemma checklist, decisions, and hand-off. The forward-mode
dep-graph / lemma index is the new blueprint chapter
`blueprint/src/chapter/molecular-induction.tex`
(`sec:molecular-induction`); its red nodes are the live to-do list.

## Current state

`Molecular/Induction.lean` has all of the inherited structural lemmas (KT 3.4 full form +
the complete KT 3.5 chain) and the **graph operations** green: the vertex-induced-subgraph
construction (`def:induced-span`), the full form of KT Lemma 3.4 (`lem:circuit-induces-rigid`),
the four graph operations (`def:graph-operations` + `def:rigid-contraction`), and the full
KT 3.5 assembly `lem:contraction-minimality` (rank core → contraction arithmetic →
deficiency conservation → minimality transport → assembly). The forest-surgery **framing**
sub-node (`lem:forest-packing-decomp`) is now green too; next is the surgery proper
(KT 4.1, `lem:forest-surgery-split`).

- **`def:induced-span`** — `Graph.fiberSpan G n X = (G.mulTilde n).spanningVerts X`
  (the vertices `V(X)` spanned by a fiber set `X` of `G̃`) and
  `Graph.inducedSpan G n X = G.induce (G.fiberSpan n X)` (the induced subgraph
  `G[V(X)]` of the *original* `G`). The construction is **mathlib's
  `Graph.induce`** (`Mathlib.Combinatorics.Graph.Delete`) — no new graph
  machinery needed, contra the phase-open expectation; `inducedSpan` is a thin
  wrapper plus the simp lemma `vertexSet_inducedSpan`.
- **`lem:circuit-induces-rigid`** (`Graph.circuit_induces_isTight`, KT 3.4 full
  form) — for a circuit `X` of `M(G̃)` and `e ∈ X`, the tightness equality
  `|X − e| + D = D·|V(X)|` (i.e. `|X − e| = D(|V(X)| − 1)`), so `X − e` packs `D`
  spanning trees on `V(X)` and `G[V(X)]` is rigid. **Did NOT need
  `thm:def-eq-corank`** (the phase-open / blueprint `\uses` was overcautious): the
  lower bound `|X| > D(|V(X)| − 1)` is the matroidal circuit-minimality fact
  `circuit_ncard_gt`, proved directly from `matroidMG_indep_iff` (every proper
  subset of `X` is independent ⟹ `(D,D)`-sparse, so the dependent `X`'s sparsity
  failure is at `X` itself). Upper bound from Phase 19's
  `isSparse_diff_singleton_of_isCircuit`. Axiom-free.

- **`def:graph-operations` / `def:rigid-contraction`** — the four ops:
  `Graph.removeVertex` (= mathlib `deleteVerts {v}`), `Graph.splitOff v a b e₀`
  (delete `v`, add fresh edge `e₀` joining `a,b`), `Graph.edgeSplit a b v e₀ e₁ e₂`
  (subdivide `e₀` by fresh `v` via fresh `e₁,e₂`), and `Graph.rigidContract G H r`
  (= `(G.deleteEdges E(H)).map (collapseTo r V(H))`, collapse `V(H)` to representative
  `r`). `removeVertex` and `rigidContract` are thin mathlib compositions
  (`deleteVerts` / `deleteEdges` + `map`); `splitOff` / `edgeSplit` are structure
  literals (no graph union/`addEdge` in mathlib). Each has `vertexSet_*`/`*_isLink`
  simp lemmas. Axiom-free.

Now also green: `lem:rigid-full-rank` (`Graph.rank_matroidMG_of_isKDof_zero`), the
**rank core** of KT 3.5 — a rigid subgraph `H` (`def(H̃) = 0`) attains full rank
`rank M(H̃) = D(|V(H)| − 1)`. Four-line corollary of Phase 19's `rank_add_deficiency_eq`
(def\,=\,corank) with `def = 0`. This is the rank quantity contraction removes.

And now green: `lem:contract-rank-bridge` (`Graph.contract_matroidMG_rank`), the
**matroid contraction arithmetic** of KT 3.5 — `rank(M(G̃) / E(H̃)) + rank M(H̃) =
rank M(G̃)` for `H ≤ G`. This is the *matroid* side of the contraction bridge (the
graph-collapse `Matroid.map` correspondence the earlier hand-off worried about turned
out **not needed**): contraction in `M(G̃)` is the abstract matroid-rank identity
`rank(M/C) = rank M − rank_M(C)`, and the restriction `M(G̃) ↾ E(H̃)` is `M(H̃)`
(Phase 19's `matroidMG_restrict_mulTilde`). Both pieces already existed — the
`rank(M/C)` identity is in the vendored `Matroid/Minor/Rank.lean`
(`contract_rank_cast_int_eq`), so the bridge is a 5-line composition + a 4-line abstract
adapter `Matroid.rank_contract_add_rank_restrict`. Combined with the rank core this pins
the rank a *rigid* subgraph's contraction removes.

And now green: `lem:contract-deficiency-conservation` (`Graph.contract_matroidMG_deficiency_eq`),
the **deficiency-conservation half** of KT 3.5 `lem:contraction-minimality`. For a rigid
`H ≤ G` the corank of the matroid contraction `M(G̃)/E(H̃)` at the reduced ambient
`D(|V(G)| − |V(H)|)` equals `def(G̃)`:
`D(|V(G)| − |V(H)|) − rank(M(G̃)/E(H̃)) = def(G̃)`. Pure matroid bookkeeping (a `zify` +
`linarith`): `contract_matroidMG_rank` + rank core gives the rank drop `D(|V(H)|−1)`, which
cancels against the ambient drop in `rank_add_deficiency_eq`. Stated against the *matroid*
contraction directly — NO graph↔matroid `map` correspondence — confirming the earlier
hand-off's simplification. Axiom-free. Factored as its own blueprint node feeding
`lem:contraction-minimality` (matching how the rank core / contraction arithmetic are
separate sub-nodes).

And now green: `lem:contract-minimality-transport` (`Graph.contract_minimality_transport`),
the **minimality-transport half** of KT 3.5 `lem:contraction-minimality`. Every base `B'`
of the matroid contraction `M(G̃)/E(H̃)` meets every *surviving* edge-fiber `ẽ`
(`e ∈ E(G) \ E(H)`). The fundamental-circuit-swap worry was unnecessary: the transport is
a clean base-lift. Pick an `M(G̃)`-basis `J` of the contracted-out `E(H̃)`; the abstract
helper `Matroid.IsBase.union_isBasis_of_contract` lifts `B'` to a base `B' ∪ J` of `M(G̃)`
(via `IsBasis'.contract_eq_contract_delete` + the deleted part being loops), then `G`'s
minimality (`hG.2`) gives `(B' ∪ J) ∩ ẽ ≠ ∅` and the witness lands in `B'` because the
basis part `J ⊆ E(H̃)` is disjoint from the surviving fiber. **No `H ≤ G` hypothesis
needed** (matroid-side only; `H ≤ G` enters only the deficiency-conservation half).
Axiom-free. The abstract helper is the missing-mathlib piece (FRICTION).

And now green: `lem:contraction-minimality` (`Graph.contraction_isMinimalKDof`), the
**full KT 3.5 assembly**. For a proper rigid `H` of a minimal `k`-dof `G`, the matroid
contraction `M(G̃)/E(H̃)` is a *minimal `k`-dof matroid* at the reduced ambient
`D(|V(G)|−|V(H)|)`: corank `= k` (deficiency conservation, with `def(G̃)=k` rewritten via
`hG.1`) ∧ every base meets every surviving fiber (minimality transport). A 4-line
conjunction of `contract_matroidMG_deficiency_eq` + `contract_minimality_transport`; both
halves were already green. **Stated matroid-side — NO graph↔matroid `map`** (the earlier
hand-off's repeated finding, now confirmed at the assembly: `IsMinimalKDof` of the collapsed
`rigidContract` is never needed; KT reasons on `M(G̃)/E(H̃)` throughout). Axiom-free. The
graph-collapse `rigidContract` phrasing is deferred — Cases I/III of Phase 21+ consume the
matroid-side form directly.

And now green: `lem:forest-packing-decomp` (`Graph.matroidMG_indep_iff_exists_forest_packing`),
the **framing sub-node** of the forest surgery (KT 4.1/4.2). An `I ⊆ E(G̃)` is independent in
`M(G̃)` iff it is covered by `D = bodyBarDim n` cycle-matroid-independent fiber sets — the `D`
edge-disjoint forests KT's surgery operates on. **Resolves the open framing blocker:** the
matroid-base / `union_indep_iff` framing (NOT a hand-rolled graph-acyclicity predicate) is
forced, because `matroidMG = (⋃_{i<D} cycleMatroid(G̃)) ↾ E(G̃)` already (`def:matroid-MG`), so
"D edge-disjoint forests" = the `Matroid.union_indep_iff` decomposition and "forest" =
`(G̃).cycleMatroid`-independent. 1-line proof (`rw [matroidMG, restrict_indep_iff,
union_indep_iff]; tauto`). Axiom-free. Factored as its own blueprint node feeding
`lem:forest-surgery-split`.

And now landed: the **incidence/cardinality substrate** of the forest surgery
(`lem:forest-surgery-split`, KT 4.1) — three axiom-free bookkeeping lemmas, NOT a blueprint
node (the node stays red; these are the glue the still-open surgery proper consumes):
- `Graph.edgeFiber_ncard` (in `Deficiency.lean`): `|ẽ| = bodyHingeMult n = D − 1`, the
  `|ã̃b| = D − 1` quantity KT 4.1 counts the `< D − 1` short-circuit copies against.
- `Graph.edgeSet_splitOff`: `E(G_v^{ab}) = {fresh e₀ when a,b ≠ v ∈ V(G)} ∪ {e ≠ e₀ of G
  avoiding v}` — the edge-level description of the splitting-off short-circuit.
- `Graph.edgeFiber_subset_edgeSet_mulTilde_splitOff`: the fresh fiber `ã̃b = edgeFiber e₀ n`
  lies in `E(G̃_v^{ab})` when the short-circuit edge is present. This is the fiber the
  surgery reroutes the degree-2 forests onto.

Next concrete step (still): the **forest-surgery proper** (`lem:forest-surgery-split`, KT 4.1)
— the genuinely hard combinatorial core, still red. Take the `D`-forest packing of an
independent set `I`, reroute each forest across the degree-2 vertex `v` (degree-1-in-`Fᵢ`
forests drop their `v`-edge; degree-2-in-`Fᵢ` forests swap their two `v`-edges for one `ãb`
copy via `edgeFiber_subset_edgeSet_mulTilde_splitOff`), and reassemble into an independent `I'`
of `M(G̃ᵥᵃᵇ)` with `|I'| = |I| − D` and `|ãb ∩ I'| < D − 1` (bounded via `edgeFiber_ncard`).
The bookkeeping that remains — **per-forest acyclicity preservation across the short-circuit**
(cycles in `G̃ᵥᵃᵇ` lift to cycles/paths in `G̃`, via the `Matroid/Graph/AcyclicSet.lean`
cycle-characterization) **and edge-disjointness of the `ãb` copies used** (KT's `h' ≤ D − 2`
count) — is the residual combinatorial crux; it needs a degree-at-`v`-in-a-forest notion not
yet in place. Multi-commit; budget the most time.

## Architectural choices made up front

- **New file `Molecular/Induction.lean`.** Per the one-`.lean` /
  one-`.tex` per molecular phase convention (post-Phase-18 cleanup
  split). Carrier: mathlib core `Graph α β`, matching Phases 13–19.
- **Graph operations as `Graph α β` constructions, reusing the matroid
  layer.** Splitting-off / edge-splitting / removal / rigid-contraction
  are graph-level ops; their *deficiency* behaviour routes through the
  matroid `M(G̃)` (Phase 19) and matroid restriction/contraction +
  fundamental circuits (mathlib `Matroid.restrict`, `Matroid.contract`,
  `Matroid.fundCircuit`) + the vendored union subsystem
  (`Matroid/Constructions/Union.lean`). `edgeMultiply` / `mulTilde`
  carry the `(D−1)·G` plumbing already.
- **Forest surgery (4.1/4.2) is the hard new pure combinatorics** — no
  existing analogue, budget the most time (flagged in
  `notes/MolecularConjecture.md` *Phase 20* hard-core). Decide the
  packing-vs-matroid framing (explicit `D` forests vs. base of the
  `D`-fold cycle-matroid union) when the first surgery node lands.

## Lemma checklist

Forward-mode: the authoritative node list is `molecular-induction.tex`
(`sec:molecular-induction`). Tracked here for hand-off convenience;
flip to `[x]` as each lands `\leanok` in the chapter.

Inherited from Phase 19 (schedule early):
- [x] `lem:circuit-induces-rigid` — KT 3.4 full form: a circuit `X`
  induces a rigid `G[V(X)]` (tightness equality `|X−e| = D(|V(X)|−1)`).
  `Graph.circuit_induces_isTight`; lower bound is the direct circuit-minimality
  fact `Graph.circuit_ncard_gt` (NOT `thm:def-eq-corank`).
- [x] `lem:rigid-full-rank` — KT 3.5 rank core: a rigid subgraph `H`
  (`def(H̃) = 0`) attains full rank `rank M(H̃) = D(|V(H)| − 1)`.
  `Graph.rank_matroidMG_of_isKDof_zero`; 4-line corollary of `rank_add_deficiency_eq`.
- [x] `lem:contract-rank-bridge` — KT 3.5 contraction arithmetic:
  `rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)` (`Graph.contract_matroidMG_rank`),
  via the abstract adapter `Matroid.rank_contract_add_rank_restrict` + the vendored
  `contract_rank_cast_int_eq` + Phase 19's `matroidMG_restrict_mulTilde`.
- [x] `lem:contract-deficiency-conservation` — KT 3.5 deficiency-conservation half:
  `D(|V(G)| − |V(H)|) − rank(M(G̃)/E(H̃)) = def(G̃)` for rigid `H ≤ G`
  (`Graph.contract_matroidMG_deficiency_eq`); `zify` + `linarith` over `contract_matroidMG_rank`
  + rank core + `rank_add_deficiency_eq`. Matroid-side, no `map`.
- [x] `lem:contract-minimality-transport` — KT 3.5 minimality-transport half: every base
  of `M(G̃)/E(H̃)` meets every surviving edge-fiber (`Graph.contract_minimality_transport`).
  Base-lift via the abstract helper `Matroid.IsBase.union_isBasis_of_contract`, NOT
  fundamental-circuit swaps. Matroid-side, no `H ≤ G` needed.
- [x] `lem:contraction-minimality` — KT 3.5: contracting a proper rigid
  subgraph preserves minimal `k`-dof (Case I engine). `Graph.contraction_isMinimalKDof`,
  the 4-line conjunction of `contract_matroidMG_deficiency_eq` (corank `= k` via `hG.1`) +
  `contract_minimality_transport`. NO graph↔matroid `map` — matroid contraction `M(G̃)/E(H̃)`.

Graph operations:
- [x] `def:induced-span` — vertex-induced subgraph `G[V(X)]` from a fiber set
  `X` of `G̃` (`Graph.fiberSpan` / `Graph.inducedSpan`, via mathlib `Graph.induce`).
- [x] `def:graph-operations` — removal `G_v` (`Graph.removeVertex`), splitting-off
  `G_v^{ab}` (`Graph.splitOff`), edge-splitting `H_{ab}^v` (`Graph.edgeSplit`,
  inverse of splitting-off).
- [x] `def:rigid-contraction` — rigid-subgraph contraction `G/E(H)`
  (`Graph.rigidContract`, via `deleteEdges` + `map (collapseTo …)`).

Forest surgery (hard core):
- [x] `lem:forest-packing-decomp` — framing sub-node of KT 4.1/4.2:
  `I` independent in `M(G̃)` ⟺ covered by `D` cycle-matroid-independent fiber
  sets (the `D` edge-disjoint forests). `Graph.matroidMG_indep_iff_exists_forest_packing`;
  1-line `rw [matroidMG, restrict_indep_iff, union_indep_iff]; tauto`. **Decides the
  framing blocker** (matroid-base via `union_indep_iff`, not hand-rolled acyclicity).
- [ ] `lem:forest-surgery-split` — KT 4.1, splitting-off direction
  (the surgery proper: reroute each of the `D` forests across the degree-2
  vertex `v`, giving `|I'| = |I| − D` and `|ãb ∩ I'| < D − 1`). Built on
  `lem:forest-packing-decomp`. **Substrate landed** (`edgeFiber_ncard`,
  `edgeSet_splitOff`, `edgeFiber_subset_edgeSet_mulTilde_splitOff`); the
  acyclicity-preserving reroute + `h' ≤ D−2` disjointness count remain (no
  blueprint node yet — node stays red).
- [ ] `lem:forest-surgery-unsplit` — KT 4.2, edge-splitting direction
  (the inverse; makes split/unsplit inverse on deficiency).

Dof tracking:
- [ ] `lem:dof-tracking` — KT 4.3–4.5, deficiency under removal /
  splitting-off.
- [ ] `lem:reducible-vertex` — KT 4.6, existence of a reducible
  degree-2 vertex (maximal-chain / degree-sequence count).
- [ ] `lem:reduction-step` — KT 4.7–4.8, reduction preserves minimality
  (two circuit-swap arguments; the 4.8 capstone).

Capstone:
- [ ] `thm:minimal-kdof-reduction` — KT Theorem 4.9: every minimal
  `k`-dof-graph reduces to the two-vertex double edge.

(Off the Thm-4.9 critical path; schedule with Phase 21:) KT Lemma 3.2
(not 3-edge-connected), Lemma 3.6 (partition decomposition — needed
only by Case 6.1).

## Decisions made during this phase

- **Vertex-induced subgraph = mathlib `Graph.induce`, not a hand-rolled
  construction.** The phase-open blocker ("no existing analogue") was wrong:
  `Mathlib.Combinatorics.Graph.Delete` has `Graph.induce (X : Set α)` with the
  full API (`vertexSet_induce`, `induce_isLink`, `edgeSet_induce`, `induce_le`).
  `Graph.inducedSpan G n X := G.induce (G.fiberSpan n X)` is a thin wrapper;
  `fiberSpan` reuses Phase 16's `spanningVerts` on `mulTilde`. Reach for mathlib's
  `induce` before hand-rolling in the graph-operations nodes too.
- **KT 3.4 lower bound is the direct circuit-minimality fact, NOT
  `thm:def-eq-corank`.** A circuit `X` is a *minimal* dependent set, so every
  proper subset is independent ⟹ `(D,D)`-sparse (`matroidMG_indep_iff`); the
  dependent `X`'s sparsity failure is therefore at `X` itself, giving `|X| >
  D(|V(X)|−1)` (`circuit_ncard_gt`). This matches KT's "see [21]" (a count-matroid
  fact), not the JJ09 min–max. Blueprint `\uses` corrected to drop
  `thm:def-eq-corank`. (The def=corank reverse is still the engine for KT 3.5's
  rank-conservation, scheduled next.)

- **Graph operations: reuse mathlib where possible, structure-literal where not.**
  `removeVertex = deleteVerts {v}` and `rigidContract = (deleteEdges E(H)).map
  (collapseTo r V(H))` are thin compositions of mathlib `Graph` ops (mathlib's `map`
  realizes the vertex-collapse). `splitOff` / `edgeSplit` *add* edges/vertices, and
  mathlib's `Graph` has no union/join (`SemilatticeInf` only) or `addEdge`, so they
  are structure literals with explicit fresh edge labels (`e₀` for splitting-off;
  `e₁,e₂` for edge-splitting). `collapseTo r S` uses `open Classical in` for the
  membership `if`. Deficiency behaviour is deferred to the later surgery nodes.

- **KT 3.5 decomposed; rank core then contraction arithmetic.** The full
  `lem:contraction-minimality` is multi-commit. Earlier worry — a graph↔matroid `map`
  correspondence (`(G/E(H))̃` ↔ `M(G̃)/E(H̃)`) — turned out **unnecessary**: KT's proof
  reasons entirely on the matroid contraction `M(G̃)/E(H̃)`, so the deficiency/minimality
  statement is stated against the matroid, not the collapsed graph `rigidContract`. Two
  commits landed: (1) the **rank core** `lem:rigid-full-rank` (`rank M(H̃) = D(|V(H)|−1)`
  for rigid `H`, 4-line corollary of `rank_add_deficiency_eq`); (2) the **contraction
  arithmetic** `lem:contract-rank-bridge` (`rank(M(G̃)/E(H̃)) + rank M(H̃) = rank M(G̃)`).
  The latter is a 5-line composition of an abstract adapter
  `Matroid.rank_contract_add_rank_restrict` (`rank(M/C) + rank(M↾C) = rank M`, itself a
  4-line wrap of the vendored `contract_rank_cast_int_eq` + `restrict_rk_eq`) with Phase
  19's `matroidMG_restrict_mulTilde`. Remaining: deficiency conservation (assemble) +
  minimality transport (fundCircuit swaps).

### Promoted to FRICTION
- *No mathlib "base of `M ／ C` lifts to base of `M` via a basis of `C`" — route through
  `IsBasis'.contract_eq_contract_delete` + loops/spanning; `IsBasis'` carries no ground
  containment for its `X`* → FRICTION `[resolved] [matroid] no mathlib "base of M ／ C
  lifts …"`.
- *`IsCircuit.subset_ground` for `M(G̃)` gives a restrict-ground `⊆`, defeq-but-not-
  syntactic to `E(G̃)` — ascribe once* → FRICTION `[resolved] [matroid]
  IsCircuit.subset_ground for M(G̃) …`.
- *Contraction rank arithmetic is already in the vendored `Matroid/Minor/Rank.lean`
  (`contract_rank_cast_int_eq`); its `cast_int` RHS is ℤ-subtraction — keep atoms ℤ-cast
  + `omega`* → FRICTION `[resolved] [matroid] contraction rank arithmetic already lives
  in vendored Matroid.Minor.Rank …`.
- *Hand-rolled `Graph` with several fresh edge labels needs a distinctness guard in a
  clause, else `eq_or_eq_of_isLink_of_isLink` is unprovable* → FRICTION `[resolved] A
  hand-rolled Graph α β with several fresh edge labels …`.

## Blockers / open questions

- **[resolved] Forest-surgery framing.** Decided by `lem:forest-packing-decomp`:
  the matroid-base / `union_indep_iff` framing is *forced* by the existing
  `matroidMG` definition (`= (⋃_{i<D} cycleMatroid(G̃)) ↾ E(G̃)`), so the "D
  edge-disjoint forests" are the `union_indep_iff` decomposition and a "forest"
  is a `cycleMatroid`-independent fiber set. No hand-rolled acyclicity predicate.
  The surgery proper (`lem:forest-surgery-split`) now operates on this packing.

## Hand-off / next phase

Green in `Molecular/Induction.lean`, axiom-free, blueprint nodes `\leanok`:
`def:induced-span`, `lem:circuit-induces-rigid` (KT 3.4 full form), the four
graph operations `def:graph-operations` (`Graph.removeVertex` / `splitOff` /
`edgeSplit`) + `def:rigid-contraction` (`Graph.rigidContract`, via the auxiliary
`collapseTo`), `lem:rigid-full-rank` (`Graph.rank_matroidMG_of_isKDof_zero`, KT 3.5 rank
core), `lem:contract-rank-bridge` (`Graph.contract_matroidMG_rank`, KT 3.5 contraction
arithmetic; abstract adapter `Matroid.rank_contract_add_rank_restrict`),
`lem:contract-deficiency-conservation` (`Graph.contract_matroidMG_deficiency_eq`, KT 3.5
deficiency-conservation half), and now `lem:contract-minimality-transport`
(`Graph.contract_minimality_transport`, KT 3.5 minimality-transport half; abstract helper
`Matroid.IsBase.union_isBasis_of_contract`). Each op has `vertexSet_*` / `*_isLink` simp
lemmas.

`lem:contraction-minimality` (`Graph.contraction_isMinimalKDof`, KT 3.5 full assembly) is
green and `\leanok` — the matroid contraction `M(G̃)/E(H̃)` is a minimal `k`-dof matroid
(corank `= k` ∧ every base meets every surviving fiber). Stated matroid-side; the `map`
correspondence was confirmed unnecessary, and the graph-collapse `rigidContract` phrasing is
deferred (Phase 21+ consumes the matroid-side form).

And now green and `\leanok`: `lem:forest-packing-decomp`
(`Graph.matroidMG_indep_iff_exists_forest_packing`), the **framing sub-node** of the forest
surgery — an `I ⊆ E(G̃)` is independent in `M(G̃)` iff covered by `D` cycle-matroid-independent
fiber sets (the `D` edge-disjoint forests). This **resolves the open framing blocker**: the
matroid-base / `union_indep_iff` framing is forced by `matroidMG`'s definition, so a "forest"
is a `cycleMatroid`-independent fiber set and no hand-rolled acyclicity predicate is needed.

And now landed (axiom-free, **no blueprint node** — bookkeeping for the still-red
`lem:forest-surgery-split`): the surgery's **incidence/cardinality substrate** —
`Graph.edgeFiber_ncard` (`|ẽ| = D − 1`, `Deficiency.lean`), `Graph.edgeSet_splitOff` (the
edge set of the short-circuit splitting-off), and
`Graph.edgeFiber_subset_edgeSet_mulTilde_splitOff` (the fresh fiber `ã̃b ⊆ E(G̃ᵥᵃᵇ)`). These are
the quantities KT 4.1's count and reroute consume (`|ã̃b| = D − 1`, the target edge set, the
short-circuit fiber).

Next agent's concrete commit: the **forest-surgery proper** — `lem:forest-surgery-split`
(KT 4.1, splitting-off direction), still red. The framing (`lem:forest-packing-decomp`) and
the incidence substrate above are now in place; reroute each of the `D` forests across the
degree-2 vertex `v` — forests with `dᶠ(v)=1` drop their `v`-edge, forests with `dᶠ(v)=2` swap
their two `v`-edges for one fresh `ã̃b` copy (≤ `D−2` such, so `< D−1` copies used, all
edge-disjoint) — yielding an independent `I'` of `M(G̃ᵥᵃᵇ)` with `|I'| = |I| − D` and
`|ã̃b ∩ I'| < D − 1`. **What remains is the genuine crux** and likely needs a *new sub-node
first*: a **degree-at-`v`-in-a-forest** notion (KT's `dᶠ(v) ∈ {0,1,2}`, giving the count
`h' ≤ D − 2`) and a **acyclicity-preservation-across-the-short-circuit** lemma (a cycle of
`G̃ᵥᵃᵇ` using `ã̃b` lifts to a `v`-traversing path in `G̃`, via the
`Matroid/Graph/AcyclicSet.lean` `not_isAcyclicSet_iff` cycle characterization). Multi-commit;
budget the most time. After `-split`, its inverse `lem:forest-surgery-unsplit` (KT 4.2) makes
split/unsplit inverse on the deficiency, then the dof-tracking chain (4.3–4.8) and Theorem 4.9.
