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

**N4c reduction bricks landed green** (`Induction.lean`, three lemmas, axiom-clean, no
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
    restriction of a `D`-fold-union over `G̃.cycleMatroid`. **Remaining:** the lone
    union↔contraction crux `Union (fun _ ↦ G̃.cyc ／ E(H̃)) ↾ S = (Union (fun _ ↦ G̃.cyc) ／ E(H̃)) ↾ S`
    (where rigidity/forest-packing enters), then `ext_indep` against `matroidMG_indep_iff` +
    `Matroid.Indep.contract_indep_iff`. *See Hand-off.*
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

## Blockers / open questions

- **The union↔contraction crux is the last content of N4c.** With the reduction bricks green,
  N4c is now the single matroid equality
  `Union (fun _ ↦ G̃.cyc ／ E(H̃)) ↾ S = (Union (fun _ ↦ G̃.cyc) ／ E(H̃)) ↾ S` on `S = E(G̃)\E(H̃)`.
  In general `Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`; the equality holds *here* because `C = E(H̃)` is the
  full edge set of the rigid (⟹ `D`-spanning-tree-packing) `H̃`, so an `N`-basis of `C` splits as one
  `G̃.cycleMatroid`-basis per factor. The route is `ext_indep` + per-factor / union-level
  `Matroid.Indep.contract_indep_iff`, reading both sides through `matroidMG_indep_iff` (or the
  forest-packing form `matroidMG_indep_iff_exists_forest_packing`). **There is no vendored
  Union↔contract lemma** (checked `Matroid/Constructions/Union.lean`), so it is a from-scratch
  argument needing the rigidity input. After it, the rank/ambient reconciliation assembles
  `(G.rigidContract H r).IsMinimalKDof n 0` from the green `contraction_isMinimalKDof` (→ N4 → N6).
- **N5 is research-shaped** (its blueprint proof note already says so); **Track B** (the
  Case II/III producer) is a multi-node crux. So there is still no clean single-commit
  *producer* node — the infra route (finish N4c's crux) remains the lowest-risk forward path.

## Hand-off / next phase

**N4c reduction bricks are green** (`edgeSet_mulTilde_rigidContract`,
`matroidMG_contract_eq_restrict`, `matroidMG_rigidContract_eq`, `Induction.lean`; axiom-clean,
no `\leanok` flip — infra below the N4 blueprint node). They put both sides of N4c
(`matroidMG (G.rigidContract H r) = matroidMG G ／ E(H̃)`) over the common restricted ground
`S = E(G̃)\E(H̃)`, each as a restriction of a `D`-fold union over `G̃.cycleMatroid`.

**Recommended next concrete commit: the union↔contraction crux of N4c.** Prove the single matroid
equality (on the common ground `S`):
`Union (fun _ : Fin D ↦ G̃.cyc ／ E(H̃)) ↾ S = (Union (fun _ : Fin D ↦ G̃.cyc) ／ E(H̃)) ↾ S`.
Then N4c follows by `(matroidMG_rigidContract_eq …).trans <crux> |>.trans (matroidMG_contract_eq_restrict …).symm`.
Route: `Matroid.ext_indep` over `S`. Per `I ⊆ S` (so `Disjoint I E(H̃)`):
- **RHS** via union-level `Matroid.Indep.contract_indep_iff` with an `N`-basis `J` of `E(H̃)`
  (`N = Union (fun _ ↦ G̃.cyc)`): `N.Indep (I ∪ J)`, i.e. `I ∪ J` packs into `D` `G̃.cyc`-forests.
- **LHS** via union independence (`matroidMG_indep_iff_exists_forest_packing`-style): `I` packs into
  `D` sets each `(G̃.cyc ／ E(H̃))`-independent, each lifting (per-factor `contract_indep_iff`) by a
  `G̃.cyc`-basis `Jᵢ` of `E(H̃)`.
The bridge is the **rigidity input**: `E(H̃)` is the full edge set of the rigid (`H.IsKDof n 0`)
`H̃`, so it packs into exactly `D` `G̃.cyc`-spanning-trees — `J = ⋃ Jᵢ` with each `Jᵢ` a `G̃.cyc`-basis
of `E(H̃)`. `rank_matroidMG_of_isKDof_zero` (`rank M(H̃) = D(|V(H)|−1)`) is the rank fact behind the
split. No vendored Union↔contract lemma exists, so this is from-scratch — budget it its own
(possibly multi-) commit. Needs `r ∈ V(H)` + `H̃` preconnected (N4a, since proper rigid ⟹
`H.IsKDof n 0`). After the crux: rank/ambient reconciliation + `contraction_isMinimalKDof` ⟹ N4
(`lem:rigidContract-isMinimalKDof`), then N6.

*If a producer is preferred over infrastructure:* **N5**
`lem:case-I-splice-placement`, decomposed math-first per its blueprint proof note
(boundary-panel intersection + block-triangular independence each break into
sub-lemmas) — start with the **panel-transversality** lemma (two generic
`(d−1)`-panels meet in a `(d−2)`-hinge), the one genuinely new geometry. The KT
math is in `notes/Phase21b.md` *Finding A* (Case I tractable) and the
`algebraic-induction.tex` `lem:case-I-splice-placement` proof sketch.
