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

**N4c crux input landed green** (`Matroid.Union_pow_isBasis'_split_of_rk_saturated`,
`Induction.lean`, axiom-clean, no `\leanok` flip — abstract-matroid infra below the N4 blueprint
node): the rigidity-content fact the union↔contraction crux consumes. When the `k`-fold union
`N = Union (fun _ : Fin k ↦ M)` saturates its rank on `c` (`N.rk c = k · M.rk c`), an `N`-basis
of `c` splits as `k` per-factor sets, each itself an `M`-basis of `c`. Counting argument: an
`N`-basis `B` decomposes (`union_indep_iff`) into per-factor `M`-independent `Jᵢ ⊆ c`; then
`|B| = N.rk c = k·M.rk c` and `|B| ≤ ∑|Jᵢ| ≤ k·M.rk c` (each `|Jᵢ| ≤ M.rk c`), so the chain is
tight and every `|Jᵢ| = M.rk c`, making each `Jᵢ` an `M`-basis of `c`. For the molecular crux
`M = G̃.cyc`, `k = D`, and the saturation `rk M(H̃) = D(|V(H)|−1) = D·r_cyc(E(H̃))` is the
def=corank bridge (`isBase_ncard_add_deficiency_eq`) for a rigid `H` with `H̃` connected (N4a).
**Remaining:** wire the saturation specialization, then the crux `ext_indep` itself. See *Hand-off*.

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
- [ ] **N4** `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction-
  minimality bridge: `G.IsMinimalKDof n 0 ∧ H proper rigid ⟹ (G.rigidContract H
  r).IsMinimalKDof n 0`. Matroid side (`contraction_isMinimalKDof`) green; the
  content is the `matroidMG`-of-`(map ∘ deleteEdges)` correspondence — a
  **several-node Whitney-style build** (see the refined N4 recon below; the
  per-cycle-matroid `cycleMatroid_contract` does *not* apply). Sub-bricks:
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
  - [~] **N4c** union-level independence bridge. **Reduction bricks green**
    (`edgeSet_mulTilde_rigidContract`, `matroidMG_contract_eq_restrict`,
    `matroidMG_rigidContract_eq`): both sides over the same ground `S = E(G̃)\E(H̃)`, each a
    restriction of a `D`-fold-union over `G̃.cycleMatroid`. **Crux input green**
    (`Matroid.Union_pow_isBasis'_split_of_rk_saturated`): rank-saturation ⟹ an `N`-basis of `c`
    splits into `k` per-factor `M`-bases of `c` — the rigidity-content the crux consumes.
    **Remaining:** (i) the saturation specialization `N.rk(E(H̃)) = D·r_cyc(E(H̃))` for rigid `H`
    (def=corank `isBase_ncard_add_deficiency_eq` + `G̃.cyc`/`H̃.cyc` agreement on `E(H̃)` + N4a
    connectivity), (ii) the crux `ext_indep` itself (forward via the split, reverse via the
    `N`-basis re-decomposition), then assemble N4c. *See Hand-off.*
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

- **N4c reduced, not closed, via the restrict↔contract commutation (2026-06-04).** Rather than
  fight `Union ／ C` head-on, both sides of N4c are rewritten over the common ground
  `S = E(G̃)\E(H̃)`: the contraction side uses mathlib's
  `Matroid.restrict_contract_eq_contract_restrict` (the *restrict*↔contract commutation, which
  **does** hold, unlike *union*↔contract), and the contracted side pushes N4b under the `Union`
  via `funext`. This isolates the irreducible union↔contraction crux to one matroid equality on
  `S` — a clean, honest, single-commit reduction that does not yet need the rigidity/forest-packing
  input (that input is what the *remaining* crux equality consumes). The three bricks are infra
  below the `lem:rigidContract-isMinimalKDof` blueprint node, so no `\leanok` flip.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *N4 recon lesson* → `DESIGN.md` *Constructibility recon before a producer build*
  (its first post-21b application). The N4b *correction* sharpens it: the recon must
  read the vendored lemma's **exact binder**, not a paraphrase, before declaring it
  inapplicable — captured in the N4b correction entry above.
- *`@[simps!]` projection name not resolving; bare-term field is `rfl`* → FRICTION
  [resolved] *`edgeMultiply`'s `@[simps! vertexSet]` lemma does not resolve …*.
- *`Set.ncard_iUnion_le_of_fintype` for `|⋃| ≤ ∑ ncard` — don't hand-roll via `toFinset`* →
  FRICTION [resolved] *The `Set.ncard` of a finite-index `iUnion` is `≤ ∑ ncard` …*.

## Blockers / open questions

- **The union↔contraction crux is the last content of N4c; its rigidity-content input is now
  green.** With the reduction bricks + the crux input
  (`Matroid.Union_pow_isBasis'_split_of_rk_saturated`) green, the crux is the single matroid
  equality `Union (fun _ ↦ G̃.cyc ／ E(H̃)) ↾ S = (Union (fun _ ↦ G̃.cyc) ／ E(H̃)) ↾ S` on
  `S = E(G̃)\E(H̃)`. In general `Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`; the equality holds *here* because
  `C = E(H̃)` is the full edge set of the rigid `H̃`, so it rank-saturates and the crux input gives
  the per-factor `G̃.cyc`-basis split `J = ⋃ Jᵢ`. **Remaining:** (i) the saturation specialization
  `N.rk(E(H̃)) = D·r_cyc(E(H̃))`, (ii) the `ext_indep` (forward via the split + `IsBasis'.contract_indep_iff`;
  reverse via the `N`-basis `J` and `union_indep_iff`). **There is no vendored Union↔contract lemma**
  (checked `Matroid/Constructions/Union.lean`). After it, the rank/ambient reconciliation assembles
  `(G.rigidContract H r).IsMinimalKDof n 0` from the green `contraction_isMinimalKDof` (→ N4 → N6).
- **N5 is research-shaped** (its blueprint proof note already says so); **Track B** (the
  Case II/III producer) is a multi-node crux. So there is still no clean single-commit
  *producer* node — the infra route (finish N4c's crux) remains the lowest-risk forward path.

## Hand-off / next phase

**N4c crux input is green** (`Matroid.Union_pow_isBasis'_split_of_rk_saturated`, `Induction.lean`;
axiom-clean, no `\leanok` flip — abstract-matroid infra below the N4 node): rank-saturation
`N.rk c = k·M.rk c` ⟹ an `N`-basis of `c` splits into `k` per-factor `M`-bases of `c`. With the three
reduction bricks (`edgeSet_mulTilde_rigidContract`, `matroidMG_contract_eq_restrict`,
`matroidMG_rigidContract_eq`), both sides of N4c sit over the common ground `S = E(G̃)\E(H̃)`.

**Recommended next concrete commit: the saturation specialization for a rigid `H`** —
`(Union (fun _ : Fin D ↦ G̃.cyc)).rk E(H̃) = D · G̃.cyc.rk E(H̃)`. This is the hypothesis the crux
input wants. Two pieces: (a) `(Union (fun _ : Fin D ↦ G̃.cyc)).rk E(H̃) = (matroidMG H).rank` — on
`E(H̃)` the union over `G̃.cyc` restricts to the union over `H̃.cyc` (`cycleMatroid_restrict`-style
agreement, since `E(H̃) ⊆ E(G̃)`), then `= D(|V(H)|−1)` by def=corank
(`isBase_ncard_add_deficiency_eq`, using `H.IsKDof n 0`); (b) `G̃.cyc.rk E(H̃) = |V(H)|−1` since
`H̃` is connected (N4a `mulTilde_preconnected_of_isKDof_zero`), so the cycle matroid of the
connected `H̃` has rank `|V(H)|−1`. Then `D(|V(H)|−1) = D·(|V(H)|−1)`. This is one focused commit.

**After that: the crux `ext_indep` itself** — prove
`Union (fun _ : Fin D ↦ G̃.cyc ／ E(H̃)) ↾ S = (Union (fun _ : Fin D ↦ G̃.cyc) ／ E(H̃)) ↾ S`, then
`(matroidMG_rigidContract_eq …).trans <crux> |>.trans (matroidMG_contract_eq_restrict …).symm` gives
N4c. Route `Matroid.ext_indep` over `S`, per `I ⊆ S` (so `Disjoint I E(H̃)`); take `J = ⋃ Jᵢ` the
crux-input split (`Jᵢ` each a `G̃.cyc`-basis of `E(H̃)`, `J` an `N`-basis of `E(H̃)`):
- **Forward** (LHS→RHS): per-factor `(G̃.cyc ／ E(H̃)).Indep (Is i)` ⟹ (`IsBasis'.contract_indep_iff`
  with `Jᵢ`) `G̃.cyc.Indep (Is i ∪ Jᵢ)`; then `Ks i := Is i ∪ Jᵢ`, `⋃ Ks = I ∪ J`, `union_indep_iff`
  ⟹ `N.Indep (I ∪ J)` ⟹ (`IsBasis'.contract_indep_iff` with `J`) `(N ／ E(H̃)).Indep I`.
- **Reverse** (RHS→LHS): `(N ／ E(H̃)).Indep I` ⟹ `N.Indep (I ∪ J)` ⟹ `union_indep_iff` `Ks`; the
  subtlety is re-decomposing so each factor is `(G̃.cyc ／ E(H̃))`-indep — the per-factor basis `Jᵢ`
  re-aligns it. Budget the `ext_indep` its own commit; it is the last from-scratch content of N4c.
After N4c: rank/ambient reconciliation + `contraction_isMinimalKDof` ⟹ N4
(`lem:rigidContract-isMinimalKDof`), then N6.

*If a producer is preferred over infrastructure:* **N5**
`lem:case-I-splice-placement`, decomposed math-first per its blueprint proof note
(boundary-panel intersection + block-triangular independence each break into
sub-lemmas) — start with the **panel-transversality** lemma (two generic
`(d−1)`-panels meet in a `(d−2)`-hinge), the one genuinely new geometry. The KT
math is in `notes/Phase21b.md` *Finding A* (Case I tractable) and the
`algebraic-induction.tex` `lem:case-I-splice-placement` proof sketch.
