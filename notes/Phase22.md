# Phase 22 — Realization layer (Case I + Case III at `d=3`) (work log)

**Status:** in progress (opened 2026-06-04).

Stratum 5 of the molecular-conjecture program, continued: the Theorem-5.5 *case
producers* that the Phase-21b genericity device feeds. Phase 21b closed the
genericity-free reductions (the accounting iffs, the `V(G)`-relative count
bridges, the device, the reusable row/glue infra) and re-scoped the realization
*producers* here after a math-first feasibility pass. The KT math for both
producers is worked out in `notes/Phase21b.md` *Finding A/B* + *Hand-off to
Phases 22–23* — **Phase 22 formalizes it, it does not re-derive it.**

Forward-mode / **structural-edit** discipline (`blueprint/CLAUDE.md`): Phase 22
does *not* open a new blueprint chapter. Its producers (N4/N5/N6, the Case II/III
producer) **extend the existing `algebraic-induction.tex`** — their nodes are
already stubbed red there. Program plan / reuse map / citations:
`notes/MolecularConjecture.md` *Phase 22*. Lean lands in
`Molecular/{Induction,AlgebraicInduction}.lean`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative*, *Constructibility recon
before a producer build*, *Phase Case-naming vs. KT's k-bookkeeping*.

## Current state

**N4 is GREEN** (`rigidContract_isMinimalKDof`, `Induction.lean`, axiom-clean — `lem:rigidContract-isMinimalKDof`
flipped `\leanok` green in `algebraic-induction.tex`): `G.IsMinimalKDof n 0 ∧ H proper rigid ∧ r ∈ V(H) ⟹
(G.rigidContract H r).IsMinimalKDof n 0`, under `[NeZero (bodyHingeMult n)]`. The rank/ambient
reconciliation closed cleanly: the matroid-side `contraction_isMinimalKDof` (green) packages
`M(G̃)／E(H̃)` as a minimal `0`-dof matroid; N4c (`matroidMG_rigidContract_eq_contract`) identifies that
contraction with `M((G/E(H))̃)`; then the two halves of `IsMinimalKDof` transport. **Minimality half:**
each edge of `G/E(H)` is a surviving `G`-edge (`edgeSet_rigidContract`: `E(G/E(H)) = E(G) \ E(H)`, one
`simp`), so `contraction_isMinimalKDof`'s base/fiber-meeting clause applies via `hN4c ▸ hB`. **Deficiency
half:** the def=corank bridge `rank_add_deficiency_eq` on `G/E(H)`, with the conserved rank from `hcons`
(`rank(M(G̃)／E(H̃)) = D(|V(G)|−|V(H)|)`) and the *exact* collapse vertex-count
`rigidContract_vertexSet_ncard` (`|V(G/E(H))| = (|V(G)|−|V(H)|)+1`, the sharpening of
`rigidContract_vertexSet_ncard_lt`), gives `def((G/E(H))̃) = 0` by `linarith`. Two new graph-side bricks
near `rigidContract`: `rigidContract_vertexSet_ncard` (exact count) + `edgeSet_rigidContract`.
**Track A's reduction infra (N4) is complete; the remaining Track-A producers are N5 + N6.** See *Hand-off*.

**N4c is GREEN** (`matroidMG_rigidContract_eq_contract`, `Induction.lean`, axiom-clean — infra
below the N4 blueprint node, no `\leanok` flip): `M((G/E(H))̃) = M(G̃) ／ E(H̃)` for a rigid
subgraph `H` of `G` (`H.IsKDof n 0`, `H ≤ G`, `r ∈ V(H)`, `V(H).Nonempty`, `[NeZero
(bodyHingeMult n)]`). The union↔contraction crux is closed via a new **abstract** matroid lemma
`Matroid.Union_pow_contract_eq_contract_of_rk_saturated`: when `C` saturates the `k`-fold union
rank (`N.rk C = k·M.rk C`), `Union (M ／ C)` and `(Union M) ／ C` agree on independent sets. The
two existing reduction bricks (`matroidMG_rigidContract_eq`, `matroidMG_contract_eq_restrict`)
plus the saturation specialization (`union_cycleMatroid_rk_saturated_of_isKDof_zero`) feed it.
**The crux proof took the count route, not the matching route the prior hand-off anticipated** —
see *Decisions* + FRICTION. **Remaining for N4:** the rank/ambient reconciliation that assembles
`(G.rigidContract H r).IsMinimalKDof n 0` from `contraction_isMinimalKDof` (green) + N4c, then N6.

**N4c saturation specialization landed green** (`union_cycleMatroid_rk_saturated_of_isKDof_zero`
+ bridge `cycleMatroid_mulTilde_eq_restrict`, `Induction.lean`, axiom-clean, no `\leanok` flip —
infra below the N4 blueprint node): the rank-saturation hypothesis the crux input wants, for a
rigid subgraph. `N.rk E(H̃) = D · G̃.cyc.rk E(H̃)` from two pieces — (a) `N.rk E(H̃) = rank M(H̃)
= D(|V(H)|−1)` (restriction-rank `matroidMG = N ↾ E(G̃)` + `matroidMG_restrict_mulTilde` +
def=corank `rank_add_deficiency_eq` with `def(H̃) = 0`), and (b) `G̃.cyc.rk E(H̃) = |V(H)|−1` via
the new bridge `H̃.cyc = G̃.cyc ↾ E(H̃)` + `Connected.eRk_cycleMatroid_restrict_add_one` (N4a
connectivity). Regime `[NeZero (bodyHingeMult n)]` (`D ≥ 2`, for N4a), `V(H).Nonempty`.

**N4c crux input landed previously** (`Matroid.Union_pow_isBasis'_split_of_rk_saturated`,
`Induction.lean`, axiom-clean, no `\leanok` flip — abstract-matroid infra below the N4 blueprint
node): the rigidity-content fact the union↔contraction crux consumes. When the `k`-fold union
`N = Union (fun _ : Fin k ↦ M)` saturates its rank on `c` (`N.rk c = k · M.rk c`), an `N`-basis
of `c` splits as `k` per-factor sets, each itself an `M`-basis of `c`. Counting argument: an
`N`-basis `B` decomposes (`union_indep_iff`) into per-factor `M`-independent `Jᵢ ⊆ c`; then
`|B| = N.rk c = k·M.rk c` and `|B| ≤ ∑|Jᵢ| ≤ k·M.rk c` (each `|Jᵢ| ≤ M.rk c`), so the chain is
tight and every `|Jᵢ| = M.rk c`, making each `Jᵢ` an `M`-basis of `c`. For the molecular crux
`M = G̃.cyc`, `k = D`, `c = E(H̃)`, the saturation is exactly what the specialization above supplies.
**Remaining:** the crux `ext_indep` itself, then assemble N4c. See *Hand-off*.

**N4c reduction bricks landed previously** (`Induction.lean`, three lemmas, axiom-clean, no
`\leanok` flip — infra below the N4 blueprint node): both sides of N4c
(`M((G/E(H))̃) = M(G̃) ／ E(H̃)`) are now rewritten over the **same restricted ground**
`S = E(G̃) \ E(H̃)`, isolating the irreducible **union↔contraction crux** to a single equality.
- `edgeSet_mulTilde_rigidContract` — the ground `E((G/E(H))̃) = E(G̃) \ E(H̃)` (one `simp only`:
  `rigidContract` is `map ∘ deleteEdges`, edge-preserving, so its edge set is `E(G)\E(H)`,
  lifted fiberwise).
- `matroidMG_contract_eq_restrict` — the **contraction side**: `M(G̃) ／ E(H̃) =
  (Union (fun _ ↦ G̃.cycleMatroid) ／ E(H̃)) ↾ S`, via mathlib's
  `Matroid.restrict_contract_eq_contract_restrict` (`E(H̃) ⊆ E(G̃)`).
- `matroidMG_rigidContract_eq` — the **contracted side**: `M((G/E(H))̃) =
  Union (fun _ ↦ G̃.cycleMatroid ／ E(H̃)) ↾ S`, combining N4b (per-factor
  `cycleMatroid_mulTilde_rigidContract`) with the ground brick (the per-factor N4b identity
  pushed under `Union` via `funext`).

So N4c is reduced to the lone matroid equality
`Union (fun _ ↦ G̃.cyc ／ E(H̃)) ↾ S = (Union (fun _ ↦ G̃.cyc) ／ E(H̃)) ↾ S` — union-of-contractions
vs. contraction-of-union on the surviving fibers, the point where the rigidity (forest-packing)
input bites. See *Hand-off*.

**N4b landed previously** (`cycleMatroid_mulTilde_rigidContract` + 3 bricks `mulTilde_rigidContract`,
`rigidContract_eq_contract'`, `rigidContract_collapseTo_isRepFun`, `Induction.lean`): the
per-cycle-matroid step `((G/E(H))̃).cycleMatroid = (G̃).cycleMatroid ／ E(H̃)`, for `H ≤ G` with `H̃`
preconnected (N4a) and `r ∈ V(H)`. The recon's "`cycleMatroid_contract` does not apply" was wrong —
it applies at the `mulTilde` level (N4a ⟹ `collapseTo r V(H)` is an `IsRepFun` of `H̃`'s single
component). **N4a** (`mulTilde_preconnected_of_isKDof_zero`, `Deficiency.lean`): a `0`-dof graph's
`G̃` is preconnected, regime `[NeZero (bodyHingeMult n)]` (`D ≥ 2`); cut-partition contradiction.

The N4 bridge remains a sub-build: the **union↔contraction crux** (above) is the remaining
content of N4c, plus the rank/ambient reconciliation that assembles
`(G.rigidContract H r).IsMinimalKDof n 0` from `contraction_isMinimalKDof` (green). See *Hand-off*.

## Architectural choices made up front

- **Two tracks; Track A first.** Track A (Case I producer, full-rank, KT §6.2) is
  the tractable entry point and independent of Case III. Track B (Case II/III
  reducible-vertex producer at `d=3`, KT §6.3 + §6.4.1) is the crux (Lemma 6.10,
  ~12 pages, the single largest proof in KT). See `notes/MolecularConjecture.md`
  *Phase 22* for the node-by-node plan.
- **The motive is `V(G)`-relative** (`DESIGN.md` *Realization motive must be
  V(G)-relative*; carried from Phase 21b). `HasFullRankRealization` is the
  `V(G)`-relative rank `D(|V(G)|−1)`; the absolute null-space form is
  unsatisfiable for non-spanning inductive subgraphs.

## Lemma checklist

**Track A — Case I producer (full-rank, KT §6.2).**
- [x] **N4** `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction-
  minimality bridge: `G.IsMinimalKDof n 0 ∧ H proper rigid ∧ r ∈ V(H) ⟹ (G.rigidContract H
  r).IsMinimalKDof n 0`. **GREEN** (`rigidContract_isMinimalKDof`, axiom-clean, `\leanok` flipped).
  The rank/ambient reconciliation assembled the green `contraction_isMinimalKDof` (corank +
  base-meets-fiber on `M(G̃)／E(H̃)`) through N4c (`matroidMG_rigidContract_eq_contract`) into the
  graph-level minimality, using the two new graph-side bricks `edgeSet_rigidContract`
  (`E(G/E(H)) = E(G)\E(H)`) and `rigidContract_vertexSet_ncard` (exact collapse count
  `|V(G/E(H))| = (|V(G)|−|V(H)|)+1`) + the def=corank bridge. Sub-bricks:
  - [x] **N4a** rigid subgraph's multiplied graph is connected
    (`mulTilde_preconnected_of_isKDof_zero`: `G.IsKDof n 0 ⟹ (G.mulTilde n).Preconnected`,
    under `[NeZero (bodyHingeMult n)]`), licensing the `collapseTo r V(H)` vertex-collapse.
    Green, axiom-clean (`Deficiency.lean`); cut-partition contradiction reusing
    `two_le_crossingEdges_of_isKDof_zero`'s structure.
  - [x] **N4b** cycleMatroid under the vertex-collapse `map` (Whitney contraction):
    `cycleMatroid_mulTilde_rigidContract` (+ bricks `mulTilde_rigidContract`,
    `rigidContract_eq_contract'`, `rigidContract_collapseTo_isRepFun`), all green/axiom-clean
    in `Induction.lean`. The recon's "`cycleMatroid_contract` does not apply" call was **wrong**
    — it applies at the `mulTilde` level (N4a ⟹ `IsRepFun`); see *Decisions*. Needs `r ∈ V(H)`.
  - [x] **N4c** union-level independence bridge `matroidMG_rigidContract_eq_contract`
    (`M((G/E(H))̃) = M(G̃) ／ E(H̃)`). **GREEN** (axiom-clean). Reduction bricks
    (`edgeSet_mulTilde_rigidContract`, `matroidMG_contract_eq_restrict`,
    `matroidMG_rigidContract_eq`) + saturation specialization
    (`union_cycleMatroid_rk_saturated_of_isKDof_zero`) + the new abstract crux
    `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` (saturation ⟹ `Union (M／C)` and
    `(Union M)／C` agree on indep sets, via the count route). The prior crux *input*
    `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (basis split) is **unused** by the count
    route but kept (abstract, green, may serve a future matching-style consumer).
- [ ] **N5** `lem:case-I-splice-placement` — splice the inductive legs `(H,p₁)`,
  `(G/E',p₂)` along boundary hinges at panel intersections (eq. 6.6); needs a
  *panel-transversality* lemma + block-triangular independence (Lemma 5.1). Three
  KT sub-cases (6.2/6.3/6.5). Research-shaped — decompose math-first.
- [ ] **N6** `lem:case-I-realization` — compose N4 + N5 + the green glue
  (`isInfinitesimallyRigidOn_union_of_inter`) + device ⇒ discharges
  `theorem_55.hcontract`.

**Track B — Case II/III producer at `d=3` (the crux, KT §6.3 + §6.4.1).**
- [ ] eq. (6.12) degenerate placement (`p1(vb)=q(ab)` reproduces the `e₀` row;
  the green N7b-0/1/2/3 + glue feed it) — gives `+(D−1)`, one short.
- [ ] **Lemma 6.10** (`d=3`, 3 candidates): Claim 6.11 (combinatorial↔linear,
  redundant `ab`-row), Claim 6.12 (extensor-span genericity via Lemma 2.1).

**Assembly (may defer to Phase 23 with Thm 5.5's completion).**
- [ ] `prop:rigidity-matrix-prop11` `hub` brick (Phase-19 partition count).
- [ ] `thm:theorem-55` flips green once the producers land.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **N4a stated about `Preconnected`, regime `[NeZero (bodyHingeMult n)]`.** The
  "`H̃` connected on `V(H)`" target is `(G.mulTilde n).Preconnected` (mathlib `Graph`
  preconnectedness; `V(G̃) = V(G)` definitionally). The deficiency machinery
  (`crossingEdges`/`partitionDef`/`deficiency`) is all phrased on `G`'s edges in `β`,
  so the proof never touches `G̃`'s edge type except to lift one `G`-edge to its copy-`0`
  in `G̃` (`mulTilde_isLink`) for the crossing-free-cut step — which forces the `D ≥ 2`
  regime (a copy must exist). Matches `spanningVerts_edgeMultiply`'s `[NeZero …]`. No
  nonemptiness hypothesis: the contradiction extracts its two vertices from
  `¬ Preconnected` itself, and `Preconnected` is vacuous on the empty graph.
- **N4 constructibility recon (2026-06-04, before any build).** Ran the producer
  recon (`blueprint/CLAUDE.md` *the honesty gate*, second half) on N4. **Finding:
  N4 is the graph↔matroid correspondence Phase 20 deliberately deferred, and the
  underlying matroid fact is non-trivial — not the one-commit "build-shaped" node
  the launch plan implied.** The target equality is
  `matroidMG (G.rigidContract H r) = matroidMG G ／ E(H̃)`. Edge-set check: both
  grounds equal `(E(G) \ E(H)) × Fin D`, so the ground sets *do* match. But:
  - `M(G̃)` is the `D`-fold *union* of cycle matroids restricted to `E(G̃)`
    (`Deficiency.lean:141`). **`Matroid.Union` does not commute with contraction**
    in general (`Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`), so the per-cycle-matroid fact
    `cycleMatroid_contract` (vendored `Matroid/Graphic.lean:177`,
    `(G/[E(H),φ]).cycleMatroid = G.cycleMatroid ／ E(H)`) does **not** push
    through the union to give the whole-`matroidMG` equality directly.
  - **Refinement (2026-06-04, second recon — sharper than the bullet above).**
    `cycleMatroid_contract` does not even *apply* to the per-cycle-matroid step,
    let alone fail to push through the union. The recon above pictured the matroid
    side as `cycleMatroid ／ E(H̃)` (a genuine matroid contraction by the
    contracted-out fibers) and the graph side as the same contraction. But the
    *graph* `rigidContract` is `(G ＼ E(H)).map (collapseTo r V(H))` — a pure
    **vertex-relabel `map`** with the contracted edges `E(H)` *deleted* (so on the
    cycle-matroid side those fibers are gone, not contracted). On the matroid side,
    `M(G̃) ／ E(H̃)` *contracts* those same fibers. Reconciling a graph that
    *deletes* `E(H)` and *relabels vertices* with a matroid that *contracts* `E(H̃)`
    is the classical Whitney fact "contracting a connected edge set in the cycle
    matroid = collapsing its vertex set in the graph" — and there is **no vendored
    `cycleMatroid`-under-`map`/iso lemma** (checked: `Matroid/Graphic.lean` has
    `cycleMatroid_{restrict,deleteEdges,contract,deleteVerts_isolatedSet}`, no
    `cycleMatroid_map`). `cycleMatroid_contract`'s own hypothesis
    `(G ＼ E(H) ↾ E(H)).connPartition.IsRepFun (collapseTo r V(H))` is *false* here:
    `G ＼ E(H) ↾ E(H)` has empty edge set (discrete connPartition), so collapsing all
    of `V(H)` to `r` is not a rep-fun. So the per-cycle-matroid step is itself a
    from-scratch build (cycleMatroid under vertex-collapse map), and it bottoms out
    on **connectivity of `H̃`** (rigid ⟹ packs `D` spanning trees ⟹ connected on
    `V(H)`, so the collapse is the legitimate connected-contraction).
  - The whole green substrate (`contract_matroidMG_deficiency_eq`,
    `contract_minimality_transport`, `contraction_isMinimalKDof`) reasons
    *directly on the matroid contraction* `M(G̃)／E(H̃)` and explicitly says "No
    graph↔matroid `map` correspondence is needed" — precisely because the
    correspondence is the deferred hard part.
  - The viable route is **independence-level** (`Matroid.ext_indep`), mirroring
    how `matroidMG_restrict_mulTilde` (`Deficiency.lean:212`) handled *restriction*
    via the sparsity characterization `matroidMG_indep_iff` rather than a union
    identity. The graph side is favorable: `rigidContract = (G.deleteEdges
    E(H)).map (collapseTo r V(H))`, and `contract_eq_map_of_disjoint`
    (`Matroid/Graph/GraphLike/Contract.lean:78`) gives `G/[C,φ] = φ ''ᴳ G` when
    `Disjoint E(G) C` — which holds after `deleteEdges E(H)` (already green as
    `rigidContract_eq_contract`). But the `ext_indep` is **not** a `restrict`-style
    one-screen proof: contraction-independence (`Matroid.Indep.contract_indep_iff` /
    the basis form) reads `(M(G̃) ／ E(H̃)).Indep I ↔ I ⊓ E(H̃) = ∅ ∧ M(G̃).Indep (I ∪ J)`
    for an `M(G̃)`-basis `J` of `E(H̃)`, i.e. `(G̃ ↾ (I ∪ J))` is `(D,D)`-sparse;
    the RHS wants `(rigidContract.mulTilde ↾ I)` `(D,D)`-sparse. Equating those two
    sparsities is the **Whitney rank-of-contraction identity** at the `(D,D)`
    boundary regime (the collapse changes `spanningVerts` counts by `|V(H)|−1`),
    *not* a congruence like `isSparse_restrict_mulTilde_congr`. **Budget N4 as a
    several-node sub-build** (connectivity-of-`H̃` brick → cycleMatroid-under-collapse
    → union-level independence bridge), not one commit; or pivot to **Track A's N5 /
    Track B** (N4 gates only N6, the Case-I composer).
- **N4b correction (2026-06-04, on building): `cycleMatroid_contract` DOES apply — the
  second recon mis-read its hypothesis.** The recon (refinement bullet above) claimed the
  per-cycle-matroid step needs a from-scratch `cycleMatroid`-under-collapse build because
  `cycleMatroid_contract`'s `IsRepFun` hypothesis was "false here, on `(G ＼ E(H) ↾ E(H))`".
  That graph is wrong: `cycleMatroid_contract {φ} (hφ : H.connPartition.IsRepFun φ) (hHG : H ≤ G)`
  takes the rep-fun on the **subgraph being contracted**, and that subgraph is `H.mulTilde n`
  (whose `connPartition` is *not* discrete). N4a (`(H̃).Preconnected`) makes `H̃`'s `connPartition`
  a **single class** `V(H)`, so `collapseTo r V(H)` (sends `V(H) ↦ r`, else id) is a genuine
  rep-fun — `rigidContract_collapseTo_isRepFun`. The graph side then needs only
  `rigidContract_eq_contract'` (the direct `G̃ /[E(H̃), φ]` form, no inner `＼`, via
  `map_deleteEdges_comm`) + `mulTilde_rigidContract` (edge mult. commutes with contraction).
  So N4b is **three short lemmas, one commit**, not a from-scratch Whitney build. **What
  remains genuinely hard is N4c** (lifting the per-cycle-matroid identity through `Matroid.Union`
  to `matroidMG`): there the union↔contraction non-commutation (first recon bullet) still bites,
  so N4c routes via `ext_indep` + contraction-independence at the `(D,D)` boundary, as planned.
  **Lesson:** the constructibility recon under-checked the *exact vendored hypothesis* — read the
  lemma's binder, not a paraphrase, before declaring it inapplicable.

- **N4c crux input is abstract: rank-saturation ⟹ per-factor `M`-basis split (2026-06-04).**
  The genuinely-hard crux (union↔contraction non-commutation) bottoms out on a clean *abstract*
  matroid fact, isolated as `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (under
  `namespace Matroid`, not `Graph` — it has no graph content). The rigidity input enters only as
  the saturation hypothesis `N.rk c = k·M.rk c`, supplied (next commit) by the def=corank bridge
  for a rigid `H`. The proof is a tight counting chain `|B| = k·M.rk c = ∑|Jᵢ| ≤ k·M.rk c`
  forcing each `|Jᵢ| = M.rk c` (basis). Both directions of the crux's `ext_indep` will consume it.

- **N4c saturation specialization: split (a) `rank M(H̃)` + (b) connected cycle rank (2026-06-04).**
  `union_cycleMatroid_rk_saturated_of_isKDof_zero` proves `N.rk E(H̃) = D · G̃.cyc.rk E(H̃)` as the
  product of two `|V(H)|−1` computations. (a) `N.rk E(H̃) = rank M(H̃)`: `matroidMG = N ↾ E(G̃)` and
  `E(H̃) ⊆ E(G̃)` give `N.rk E(H̃) = (matroidMG G).rk E(H̃)`, then `matroidMG_restrict_mulTilde` +
  `restrict_rk_eq` give `= rank M(H̃) = D(|V(H)|−1)` (def=corank, `def(H̃)=0`). (b) `G̃.cyc.rk E(H̃)
  = |V(H)|−1` via the new bridge `cycleMatroid_mulTilde_eq_restrict` (`H̃.cyc = G̃.cyc ↾ E(H̃)`, so
  the rank moves to `H̃`) + `Connected.eRk_cycleMatroid_restrict_add_one` (whose conclusion lands on
  `V(H̃) = V(H)`, *not* `V(G̃)` — the reason the rank must be moved into `H̃` first). The bridge
  lesson is in FRICTION `[resolved] [matroid] H.cycleMatroid = G.cycleMatroid ↾ E(H) …`.
- **N4c reduced, not closed, via the restrict↔contract commutation (2026-06-04).** Rather than
  fight `Union ／ C` head-on, both sides of N4c are rewritten over the common ground
  `S = E(G̃)\E(H̃)`: the contraction side uses mathlib's
  `Matroid.restrict_contract_eq_contract_restrict` (the *restrict*↔contract commutation, which
  **does** hold, unlike *union*↔contract), and the contracted side pushes N4b under the `Union`
  via `funext`. This isolates the irreducible union↔contraction crux to one matroid equality on
  `S` — a clean, honest, single-commit reduction that does not yet need the rigidity/forest-packing
  input (that input is what the *remaining* crux equality consumes). The three bricks are infra
  below the `lem:rigidContract-isMinimalKDof` blueprint node, so no `\leanok` flip.
- **N4c crux closed via the COUNT route, not the matching re-decomposition (2026-06-04).** The
  prior hand-off planned the crux `ext_indep` reverse via `union_indep_iff` + per-factor basis
  re-alignment — but that realignment is genuine matroid-union *matching* augmentation (an
  arbitrary `Ks` decomposition of `I ∪ J` is not factor-aligned with the `Jᵢ`, and naive fixes
  all fail; see FRICTION). The abstract crux `Union_pow_contract_eq_contract_of_rk_saturated`
  instead expands *both* matroids to their count conditions via `Union_pow_indep_iff_count`
  (`N.Indep E' ↔ ∀ Y ⊆ E', |Y| ≤ k·M.rk Y`), making the equivalence a symmetric `rk_submod` +
  `rk_mono` + `contract_rk_cast_int_eq` ℤ-arithmetic. Saturation enters only as `|J| = k·M.rk C`.
  The split lemma `Union_pow_isBasis'_split_of_rk_saturated` is thereby unused but kept. Full
  lesson + the matching obstruction in FRICTION `[resolved] [matroid] Union↔contraction …`.

- **N4 reconciliation closed in one commit, as the prior hand-off predicted (2026-06-04).** With
  N4c green, `rigidContract_isMinimalKDof` is a clean assembly, not a sub-build: unfold
  `IsMinimalKDof` into its two halves and transport each across N4c
  (`matroidMG_rigidContract_eq_contract`, `K.matroidMG = M(G̃)／E(H̃)`). The minimality half is a
  one-liner (`hN4c ▸ hB` + `edgeSet_rigidContract`'s `E(K) = E(G)\E(H)`). The deficiency half is
  the only arithmetic: `rank_add_deficiency_eq` on `K` gives `rank(K) + def(K) = D(|V(K)|−1)`;
  `rw [hN4c]` swaps `rank(K)` for `rank(M(G̃)／E(H̃))`, `hcons` (k=0) makes that `= D(|V(G)|−|V(H)|)`,
  and the exact count `|V(K)| = (|V(G)|−|V(H)|)+1` makes the ambient match, so `linarith` forces
  `def(K) = 0`. The two new bricks (`edgeSet_rigidContract`, `rigidContract_vertexSet_ncard`) are
  general structural facts about `rigidContract`, placed by its definition. The *exact* count
  (vs. `rigidContract_vertexSet_ncard_lt`'s `≤`) is the genuine new fact: `r ∈ V(H)` makes the
  collapse image *equal* `(V(G)\V(H)) ∪ {r}`, not just contained in it.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *N4 recon lesson* → `DESIGN.md` *Constructibility recon before a producer build*
  (its first post-21b application). The N4b *correction* sharpens it: the recon must
  read the vendored lemma's **exact binder**, not a paraphrase, before declaring it
  inapplicable — captured in the N4b correction entry above.
- *`@[simps!]` projection name not resolving; bare-term field is `rfl`* → FRICTION
  [resolved] *`edgeMultiply`'s `@[simps! vertexSet]` lemma does not resolve …*.
- *`Set.ncard_iUnion_le_of_fintype` for `|⋃| ≤ ∑ ncard` — don't hand-roll via `toFinset`* →
  FRICTION [resolved] *The `Set.ncard` of a finite-index `iUnion` is `≤ ∑ ncard` …*.
- *`H.cycleMatroid = G.cycleMatroid ↾ E(H)` for `H ≤ G` via `cycleMatroid_isRestriction_of_le` +
  `exists_eq_restrict` + ground pin* → FRICTION [resolved] *`[matroid]` `H.cycleMatroid =
  G.cycleMatroid ↾ E(H)` …*.
- *Union↔contraction equality via the count condition `Union_pow_indep_iff_count`, not the
  matching re-decomposition* → FRICTION [resolved] *`[matroid]` Union↔contraction equality: prove
  via the *count condition* … not … matching re-decomposition*.
- *The `V(...)` graph-vertex-set macro is greedy with a trailing binary operator (`V(H).ncard + 1`
  fails to parse, not just `: ℤ`-coerced double-subtraction); parenthesize the leading `V(…)` term* →
  FRICTION [resolved] *A `have h : … = … := by ring` whose type embeds `(V(G).ncard : ℤ) - 1 - 1`
  fails to parse* (Broadening bullet).

## Blockers / open questions

- **N4 is fully green; Track A's reduction infra is done.** The whole N4 chain — N4a (preconnected),
  N4b (cycleMatroid under collapse), N4c (union↔contraction bridge), and now the N4 reconciliation
  (`rigidContract_isMinimalKDof`) — is closed and axiom-clean. What gates `lem:case-I-realization`
  (N6) is now only the **producers** N5 + N6, not any more matroid/contraction infrastructure.
- **N5 is research-shaped** (its blueprint proof note already says so); **Track B** (the
  Case II/III producer) is a multi-node crux. So there is still no clean single-commit
  *producer* node — the remaining Track-A path (N5 → N6) and Track B both require math-first
  decomposition before a build.

## Hand-off / next phase

**N4 is GREEN** (`rigidContract_isMinimalKDof`, `Induction.lean`; axiom-clean, `\leanok` flipped on
`lem:rigidContract-isMinimalKDof` in `algebraic-induction.tex`): `G.IsMinimalKDof n 0 ∧ H proper rigid
∧ r ∈ V(H) ⟹ (G.rigidContract H r).IsMinimalKDof n 0`, under `[NeZero (bodyHingeMult n)]`. The
reconciliation assembled the green `contraction_isMinimalKDof` + N4c
(`matroidMG_rigidContract_eq_contract`) via two new graph-side bricks (`edgeSet_rigidContract`,
`rigidContract_vertexSet_ncard`) and the def=corank bridge — see *Current state* + *Decisions*. This
closes all of Track A's contraction-minimality reduction infrastructure (N4a–N4c + N4).

**Recommended next concrete commit: N5 `lem:case-I-splice-placement`** — the first *producer* node,
decomposed math-first per its blueprint proof note (the boundary-panel intersection + the combined
block-triangular independence each break into sub-lemmas). Start with the **panel-transversality**
lemma (two generic `(d−1)`-panels meet in a `(d−2)`-hinge), the one genuinely new geometry. The KT
math is in `notes/Phase21b.md` *Finding A* (Case I tractable) and the `algebraic-induction.tex`
`lem:case-I-splice-placement` proof sketch. Once N5 lands, **N6** (`lem:case-I-realization`) composes
N4 + N5 + the green glue (`isInfinitesimallyRigidOn_union_of_inter`) + the device to discharge
`theorem_55.hcontract`. (N4 — the reduction step N6 needs to name `G/E(H)` and invoke the IH — is now
in hand, so N6's only remaining inputs are the N5 producer + the already-green device/glue.)

*If Track B is preferred:* it remains a multi-node crux (eq. 6.12 degenerate placement + Lemma 6.10
at `d=3`); see the Track-B checklist + `notes/MolecularConjecture.md` *Phase 22* for the node plan.
