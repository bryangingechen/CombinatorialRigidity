# Phase 22i — the honest all-`k` Theorem 5.5 (work log)

**Status:** in progress (opened 2026-06-11 at the 22h close, per `notes/Phase22h.md`
*Hand-off*).

Discharges the five 22h carries {`h622`, `h65`, `hbase`, `hsplit`, `hcontract`} by restating
the realization motive at KT's strength — **genuine hinges** (the free-hinge carrier + panel
containment) and the **all-`k` induction** (KT's four-case `|V|`-recursion with IH (6.1) over
every dof) — then re-running the spine and building the KT cases the weak motive skipped.
**The motive design is canonical in `notes/Phase22-realization-design.md` §1.56** (motives
M1–M5, the reduction principle, the case-producer map (d), bridges B1/B2, verification items
V1–V10, the layer plan (h)) — point at it, don't duplicate. Structural-edit mode: no new
blueprint chapter; the existing `algebraic-induction/*` chapters restate per slice (the
statement-grep gate per `CLAUDE.md` *Structural-edit phases*).

## Current state

**L1a–L1h complete.** Both edge-splitting arms are green:
`splitOff_indep_extend_of_fiber_subset` (KT 4.2(ii) full-fiber) and
`splitOff_indep_extend_of_fiber_lt` (KT 4.2(i) partial-fiber). **L1i** (KT 4.4-eq /
4.3(ii)-rev) is now unblocked; the smallest next forward commit is the KT 4.4-equality
producer `exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof` (= 4.2(i) at `h'=0`, a
direct consumer of the landed case i — see Hand-off).
**L0 is fully complete** (motives M1–M5 live on the conditioned spine;
bridges B1/B2 landed; `def:genuine-hinge-realization` green — per-slice detail in the
layer plan below and §1.57). **The L1 signature pin is landed (§1.58):** V2 resolved
(labeling-free `cutEdges` + `TwoEdgeConnected`, connectivity included), V3 resolved
(in-place all-`k` restates), V4 resolved (mechanical); KT 3.6 pinned as a pure partition
argument (no matroid direct sum); the KT-4.8(ii) cluster decomposed (the reverse forest
direction KT 4.2 is the one new engine); KT numbering corrected against the PDF
(`splitOff_isMinimalKDof` = KT 4.8(i), not 4.7). L1 is sliced **L1a–L1j** with build
order in §1.58(i).

The phase-open red-node consistency gate was run on the five target nodes
(`lem:case-III-nested-rank-lower`, `lem:case-I-dispatch`, `def:genuine-hinge-realization`,
`def:rank-hypothesis`, `thm:theorem-55` + the green `thm:theorem-55-d3-instance`): each
statement and proof routes through the same 22i discharge plan §1.56 now details; no
live-route reference points at a superseded node (`blueprint/lint.sh` green, supersession
gate included).

## The carries table (the §1.55(b) structural fix for orphaned deferrals)

| Carry | Blueprint red node | Lean consumption site | Discharge sub-plan (§1.56) |
|---|---|---|---|
| `h622` (KT eq. (6.22), the nested-IH rank lower bound at the `k'`-dof `G_v`) | `lem:case-III-nested-rank-lower` (case-iii.tex) | `case_III_realization` (CaseI.lean:6750) and `theorem_55_d3` (:6817); consumed at the one W6b call inside `case_III_candidate_dispatch` | **L7**: replace the hypothesis by a derivation from the all-`k` IH at `G_v` — IH gives the generic realization at rank `D(m−1) − k'`; extract the rational rank-polynomial witness (V8); transfer to the given `(ends, q)` by the landed footnote-6 bridge (`lem:case-III-seed-rank-bridge`) |
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex) | `theorem_55_d3` (:6831), the negative branch of the L5c′ `by_cases` | **L8**: §1.54(a3) steps 1–2 — Claim 6.6 graph side (~2–3 commits) + the Π°-placement producer (own signature pin first); the dispatch itself landed in 22h. Claim 6.6 concludes inside the `k = 0` stratum, no all-`k` generality needed |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` (panel-layer.tex; + `lem:theorem-55-base` as the rank engine) | `theorem_55_d3` (:6802), passed to `theorem_55_generic`'s `hbase` slot | **L3**: the `\|V\| = 2` trichotomy (KT p. 671: `E = ∅` / one edge / parallel pair, `k ∈ {D, 1, 0}`) + the graph-level Lemma-5.3 coincident-panel brick (two non-proportional extensors in a common panel, M1 pointwise form) re-aimed into Pinning.lean's `theorem_55_base` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6804) | **L9 wiring, no new build**: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`; forgetful (M4) ∘ the GP Case-III producer |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | `theorem_55_d3` (:6809) | **L5**: dispatch on `G.Simple` — simple → forgetful (M4) ∘ the 6.3/6.5 GP arm; non-simple → KT Lemma 6.2 (NEW: the coincident-panel splice; the parallel-pair subgraph + the Lemma-5.3 leg at the contraction panel + the eq. (6.3)–(6.5) rank addition; N6a re-aimed, V6) |

Beyond the carries, the all-`k` restructure itself adds the structural deliverables of
§1.56(c)/(e): the new reduction cases (Lemma 6.1 not-2-edge-connected; Lemma 6.8 `k > 0`
split), the motive restate of every producer, and the Thm-5.6 `d = 3` push (the `def > 0`
`prop:rigidity-matrix-prop11` feed).

## Layer plan (each layer opens with its own §1.57+ signature pin)

- [x] **L0** — motives M1–M5 + bridges B1/B2 + the blueprint def-node flips; signatures
  pinned in §1.57, sliced **L0a–L0e** (§1.57(e)):
  - [x] **L0a** — `ExtensorInPanel` + the `k = 2` meet-decomposition lemma (additive).
  - [x] **L0b** — the coannihilator complement brick + B1 (additive).
  - [x] **L0c** — the partition bricks + the relative hub + B2 (additive).
  - [x] **L0d** — `HasPanelRealization` (M2) + the forgetful map (M4) +
    `def:genuine-hinge-realization` pinned + green (`checkdecls`).
  - [x] **L0e** (M3-first) — M3 rank form + `n`; producer seams through B1; old forgetful
    deleted; `def:rank-hypothesis` re-prosed. Pair-swap sub-commit still pending.
  - [x] **L0e** (pair-swap) — swap `theorem_55_generic`/`theorem_55_d3` second slot to
    `HasPanelRealization k n G`; re-type three bare carries; update d3-instance prose.
- [ ] **L1** — the combinatorial bricks; signatures pinned in §1.58, sliced **L1a–L1j**
  (V2 predicate; the `|V| ≤ 2` trichotomy; V3/V4/G0 in-place all-`k` restates; the KT 3.6
  cut decomposition; KT 4.5(ii)/4.2/4.4-eq/4.7/4.3(ii)/4.8(ii)). Build order §1.58(i):
  L1a → {L1b, L1c, L1d, L1f, L1g} → L1e, L1h → L1i → L1j. **{L1a–L1h} done;
  L1i is the open task.**
  - [x] **L1a** — `cutEdges` + `TwoEdgeConnected` + three bridge lemmas
    (`cutEdges_eq_crossingEdges_cutLabeling`, `twoEdgeConnected_of_isKDof_zero`,
    `two_le_degree_of_twoEdgeConnected`) in `Deficiency.lean` + `def:cut-edges-2ec` blueprint
    node. The two singleton-cut bridge lemmas (`crossingEdges_cutLabeling_singleton_subset` +
    `crossingEdges_cutLabeling_singleton_ncard_le`) moved from `ReducibleVertex.lean` to
    `Deficiency.lean` (their natural home next to `cutLabeling`); call sites unchanged.
  - [x] **L1c** — in-place all-`k` restates of V3/V4/G0: `no_rigid_edge_count`,
    `exists_degree_le_two`, `exists_degree_eq_two` (gains `TwoEdgeConnected` explicit
    hypothesis), `simple_of_isMinimalKDof_of_noRigid`, `rigidContract_isMinimalKDof`
    (in `ReducibleVertex.lean` / `Contraction.lean`); call site update in `ForestSurgery.lean`;
    blueprint nodes restated in `molecular-induction.tex` + `algebraic-induction/case-i.tex`.
  - [x] **L1d** — KT 3.6 part 1: `partitionDef_congr`, `partitionDef_comp_of_injOn`,
    `partitionDef_split_of_sides` in `Deficiency.lean` (section after `mulTilde_preconnected_of_isKDof_zero`).
    Two private helpers (`crossingEdges_congr`, `crossingEdges_induce`) avoid re-proving
    membership equivalences inline. Requires `[Finite α] [Finite β]` on split (needed for
    `Set.ncard_union_eq` on image/crossingEdges sets). Split statement uses explicit ℤ
    arithmetic `((bodyBarDim n : ℤ) - 1)` to avoid ℕ-subtraction/`ring` mismatch.
  - [x] **L1e** — KT 3.6 part 2: `exists_sides_separated_partitionDef_le` (the refinement
    bound) + `deficiency_eq_of_cutEdges_ncard_le_one` (KT Lemma 3.6) + the ¬2EC packaging
    `exists_cut_decomposition_of_not_twoEdgeConnected` in `Deficiency.lean` (**complete**,
    all per the §1.58(f) pins — the commit message's "partial stub, pending L4" clause is
    wrong: the L4 producer only *consumes* it, deriving `0 ≤ k₁, k₂` at the use site per
    the design); `lem:cut-edge-decomposition` blueprint node (green) in `deficiency.tex`.
    `[Finite β]` added to `exists_sides_separated_partitionDef_le` (theorem false without it
    for `n=0`; call site already had it). `Classical.propDecidable` for the `let h` decidable-if.
    `nlinarith` + nonnegativity hints for the nonlinear `D * numParts` arithmetic close.
  - [x] **L1f** — `indep_edgeSet_mulTilde_of_noRigid_of_pos` + `isBase_eq_edgeSet_mulTilde_of_noRigid_of_pos`
    in `ReducibleVertex.lean` + `lem:edge-set-indep-pos` blueprint node in `molecular-induction.tex`.
  - [x] **L1b** — `deficiency_of_edgeSet_empty` + `deficiency_of_single_edge` +
    `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two` +
    `isMinimalKDof_ncard_le_two_trichotomy` in `Deficiency.lean` (after the corank bridge)
    + `lem:two-vertex-trichotomy` blueprint node in `deficiency.tex`. Note:
    `deficiency_of_edgeSet_empty` drops the `hne` parameter (not needed by the proof; holds
    for empty `V(G)` too). Section placed after `isBase_ncard_add_deficiency_eq` to avoid
    forward references to `rank_add_deficiency_eq` / `isBase_ncard_add_deficiency_eq`.
  - [x] **L1g** — `isAcyclicSet_mulTilde_of_splitOff_reroute` (the reverse through-`v` swap,
    the one new engine) + `isAcyclicSet_mulTilde_insert_vfiber_of_splitOff` (the pendant
    insert) in `ForestSurgery.lean` + `lem:reverse-reroute-cycle-lift` / `lem:reverse-pendant-insert`
    blueprint nodes (both green) in `molecular-induction.tex`.
  - [x] **L1h** — KT 4.2(i)/(ii) edge-splitting extension in `ForestSurgery.lean` +
    `lem:edge-splitting` in `molecular-induction.tex` (both arms green;
    `splitOff_indep_extend_of_fiber_subset` = full-fiber 4.2(ii),
    `splitOff_indep_extend_of_fiber_lt` = partial-fiber 4.2(i)).
- [ ] **L2** — `minimal_kdof_reduction_all_k` (the four-case principle, §1.56(c)).
- [ ] **L3** — the base producer (`hbase` carry discharged).
- [ ] **L4** — Lemma 6.1, the cut-edge case (V5: the fixed-seed transversality route).
- [ ] **L5** — Lemma 6.2 (non-simple Case I, V6) + the 6.3/6.5 all-`k` restate of
  `case_I_realization` (`hcontract` carry discharged).
- [ ] **L6** — Lemma 6.8, the `k > 0` split (reuses `case_II_placement_eq612` = KT eqs.
  (6.13)–(6.17); the Lemma-5.2 shear transfer via the 22h W-suite, V7).
- [ ] **L7** — the Case-III rewire: `case_III_realization` restated, `h622` derived from
  the all-`k` IH (V8) (`h622` carry discharged).
- [ ] **L8** — the Lemma-6.5 arm: Claim 6.6 + the Π°-placement (§1.54(a3)) (`h65` carry
  discharged).
- [ ] **L9** — the spine + instance: `theorem_55_all_k`, `theorem_55_d3` restated with zero
  carries (`hsplit` discharged here), `theorem_55` deleted/re-pinned, blueprint restates.
- [ ] **L10** — Theorem 5.6 at `d = 3`: the deficiency-preserving spanning-strip brick +
  re-add edges + the `def > 0` `prop:rigidity-matrix-prop11` feed (V9: the homogeneous
  projective move).

## Blockers / open questions

- The ten verification items **V1–V10** (§1.56(g)) — each is gated to its layer's design
  pass, none blocks the L0 pin from starting. None is research-shaped; V8 (subfamily
  extraction at rank form) and V10 (the relative hub bound B2) are the two with real
  proof-shape uncertainty.

## Hand-off / next phase

**L0 fully complete. L1a–L1h complete (both edge-splitting arms green).**
**Smallest next forward commit: L1i, the KT 4.4-equality producer**
`exists_isBase_vb_fiber_eq_one_of_removeVertex_isKDof` in `ForestSurgery.lean` (pin §1.58(f)
/ design notes §4920) — the cleanest first L1i node and a direct consumer of the landed case
i. Statement: given degree-2 data + `(hG : G.IsKDof n k)` + `(hGv : (G.removeVertex v).IsKDof
n k)`, `∃ B, (G.matroidMG n).IsBase B ∧ (B ∩ edgeFiber e_b n).ncard = 1`. Proof: a base `B'`
of `M(G̃ᵥ)` is `M(G̃ᵥᵃᵇ)`-independent (`mulTilde_removeVertex_le_splitOff` +
`matroidMG_restrict_mulTilde`) with `B' ∩ ẽ₀ = ∅` (so `h' = 0 < D−1`); feed it to
`splitOff_indep_extend_of_fiber_lt` to lift to `M(G̃)`-independent `I` of size `|B'| + D =
D(|V|−1) − k = rank M(G̃)` (`rank_add_deficiency_eq` both sides), so `I` is a base
(`Indep.isBase_of_ncard`) with `|I ∩ ẽ_b| = h' + 1 = 1` (the case-i `e_b`-count conjunct).
Then L1i's remaining nodes (KT 4.3(ii)-reverse `splitOff_isKDof_of_exists_base_inter_fiber_lt`
+ the in-place forward 4.3(ii) restate; design §4951), then L1j (4.7/4.8(ii)).

At phase close:
Phase 23 (general `d`, KT Lemma 6.13) opens with its own recon (KT eqs. (6.46)–(6.67) vs the
`d = 3` Lean, §1.33 (C) reuse map) and adds the general-`d` row to
`notes/AlgebraicIndependence.md`.

## Decisions made during this phase

- **L1h, both arms (2026-06-12, opus):** the edge-splitting extension
  (`splitOff_indep_extend_of_fiber_{subset,lt}`, KT 4.2(ii)/(i)) in `ForestSurgery.lean`,
  green; `lem:edge-splitting` restated to cover both arms. Case i reuses case ii's disjointed
  packing + `S`-reroute, adding two pendant kinds for the `D−h'` copy-free forests: `(eₐ, pc
  i)` on `Ta = Sᶜ.erase i_b` and `(e_b, cb)` on `i_b = Sᶜ.min'`, both via
  `isAcyclicSet_mulTilde_insert_vfiber_of_splitOff`. **Fresh-coord device:** `pc` injects `Ta`
  into the unused pool `U = univ \ Simg` (`Simg = (rOf ·).2 '' S`, `|Ta| = |U| = D−1−h'`) via
  `(Ta.orderIsoOfFin rfl).symm.trans (U.orderIsoOfFin _)`, `cb = U.min'`; `Simg`-vs-`U`
  disjointness keeps all `eₐ`/`e_b` coords distinct. **Disjointness golf:** `eₐ`/`e_b`-coord
  classifiers + `hcore_of_ne` collapse the 5×5 family split to three `by_cases p.1 = eₐ/e_b`
  branches. Every forest grows by one (`hshrink`), so case i's count is `|I| = |I'| + D`;
  `e_b`-count `h'+1` via `I ∩ ẽ_b = pbOf '' S ∪ {qb}`.
  - *Build snags (low):* `Finset.card_sdiff` takes no subset hyp (`(t\s).card = t.card −
    (s∩t).card`; bridge `Finset.inter_univ`); `Set.ncard_coe_finset` (lowercase `f`); a
    `have : … = bodyBarDim n - 1 - h'` next to a `set`-bound `h'` tripped a spurious
    "unexpected token '-'" — inline the equation into its consumer.
- **L1g build (2026-06-12, opus retry after the sonnet BLOCK):** two reverse-acyclicity bricks in
  `ForestSurgery.lean`. (B) `isAcyclicSet_mulTilde_of_splitOff_reroute` (the one new engine): a
  `G̃`-cycle `C` in `(F'∖{r})∪{pa,pb}` is killed by case split on `pa∈C` / `pb∈C` — both-absent
  lifts `C` to a `G̃ᵥᵃᵇ`-cycle in `F'` (`F'∖{r}` avoids ã̃b by `fiber_inter_subsingleton…`, lives in
  `(G_v)̃`; `IsTour.of_le_of_subset` ∘ `.of_le mulTilde_removeVertex_le_splitOff`), both-present
  substitutes the `a—pa—v—pb—b` 2-path back by `r` (rotate-`pa`-first, `pb` = `lastEdge` via
  `concat_dropLast`, build the `Ksp` tour `w₂.concat r a`, `exists_isCyclicWalk`), exactly-one ruled
  out by running the swap from `pb` (forced other-end = `pa`, ⊥). (A)
  `isAcyclicSet_mulTilde_insert_vfiber_of_splitOff` (pendant): composes the landed
  `isAcyclicSet_mulTilde_of_splitOff_of_disjoint` ∘ `acyclicSet_insert_vfiber_of_not_inc`. The
  salvaged `prefixUntilVertex`/`deleteEdges` route notes went unused — the `concat_dropLast` +
  `reverse`-unify route was cleaner. Both bricks green in the blueprint
  (`lem:reverse-{reroute-cycle-lift,pendant-insert}`). Idiom additions over the forward §29 →
  FRICTION `[matroid] Reverse cycle-lift swap`. `hpab : pa≠pb` dropped (unused; derivable from
  `a≠b`). `mulTilde n = edgeMultiply (bodyHingeMult n)` not `edgeMultiply n` (feed `_`).
- **L1f build (2026-06-12):** `indep_edgeSet_mulTilde_of_noRigid_of_pos` + uniqueness corollary
  in `ReducibleVertex.lean`. Core argument: dependence → circuit `C` →
  `circuit_induces_isRigidSubgraph` + looplessness + `hnp` → `V(H) = V(G)` → rank lower bound
  via `matroidMG_restrict_mulTilde` (restrict direction is `.symm` of the stated form) + base of
  restricted matroid is independent in `G.matroidMG n` + `ncard_le_rank`; combined with
  `rank_add_deficiency_eq` to contradict `k > 0`. `Matroid.rankFinite_of_finite` needed (from
  `finite_of_finite`) to discharge `[RankFinite M]` on `ncard_le_rank`. `vertexSet_mono` is the
  correct field for `H ≤ G → V(H) ⊆ V(G)` (not `left_mem`; `left_mem` is on `IsLink`).
  `mulTilde_isLink G n |>.mp` to convert `(G.mulTilde n).IsLink` to `G.IsLink` for `ne`.
  `Set.insert_subset_iff.mpr` for `{x,y} ⊆ S` membership check.
  `Set.Subset.ssubset_of_ne` (dot notation on `hVHsub : V(H) ⊆ V(G)`) for strict subset.
- **L1d build (2026-06-12):** three `partitionDef` lemmas in `Deficiency.lean`.
  `partitionDef_congr`: `simp [partitionDef, numParts, Set.image_congr h, crossingEdges_congr h]`
  closes in one line via a private `crossingEdges_congr` helper.
  `partitionDef_comp_of_injOn`: ncard equality via `Set.InjOn.ncard_image` (not `ncard_image_of_injOn`,
  which is deprecated); crossingEdges equality via iff-on-g. `Set.ncard_union_eq` requires finiteness
  (`[Finite α] [Finite β]` added to split); `Set.toFinite _` auto-params fail on image sets —
  pass `((Set.toFinite _).union (Set.toFinite _))` for the union of two crossingEdge sets.
  Split statement: use `((bodyBarDim n : ℤ) - 1)` (ℤ subtraction, not ℕ→ℤ) so `ring` closes;
  the ℕ form `(bodyBarDim n - 1)` produces `↑(n-1 : ℕ)` which `ring` can't equate with `↑n - 1`.
  `crossingEdges_induce` helper + `numParts` additivity via `have hkey := ncard_union_eq` then
  `rw [← image_union, ← hVun] at hkey; exact hkey` (avoids `change`/simp-on-vertex-set).
  `Disjoint.union_left` not `union_right` for `Disjoint (A ∪ B) C`. `eq_and_eq_or_eq_and_eq`
  second swap case (`x'=y, y'=x`) needs both `hxV₁, hyV₁` from the first element's pattern.
- **L1c build (2026-06-12):** in-place all-`k` restates of V3/V4/G0 across three files.
  `no_rigid_edge_count`: the `X ∩ ẽ ≠ ∅` step re-routes via `k ≤ 0` (from `|X-ej| ≤ |B'| = D(|V|-1)−k`)
  then `deficiency_nonneg` pins `k = 0`, then `subst hk0` before the base-meets-fiber contradiction;
  the `E(G) = ∅` case needs `rank_add_deficiency_eq` + `Nat.zero_le rank` as `nlinarith` hints.
  `exists_degree_le_two`: add `hk0 : 0 ≤ k := hG.1 ▸ deficiency_nonneg` as `nlinarith` hint.
  `exists_degree_eq_two`: gains `{k : ℤ}` + `(htec : G.TwoEdgeConnected)` explicit hypothesis;
  body replaces the 3-step cut-count route with `two_le_degree_of_twoEdgeConnected htec hvG hV2`.
  `simple_of_isMinimalKDof_of_noRigid`: gains `{k : ℤ}`, body unchanged (already k-independent).
  `rigidContract_isMinimalKDof`: gains `{k : ℤ}`, `change ... = k`, `linarith [hbridge, hcons]`.
  Call site `minimal_kdof_reduction` (ForestSurgery.lean) gains
  `(twoEdgeConnected_of_isKDof_zero hD1 hG.1)` argument. Blueprint nodes
  `lem:no-rigid-edge-count`, `lem:low-degree-vertex`, `lem:reducible-vertex`,
  `lem:simple-minimal-noRigid`, `lem:rigidContract-isMinimalKDof` restated in place.
  `Nat.mul_sub` + `ring_nf` needed for `D*(|V|-1) = D*|V|-D` in ℕ (omega can't handle).
- **L1b build (2026-06-12):** four theorems in `Deficiency.lean` (after the corank bridge,
  to avoid forward refs to `rank_add_deficiency_eq`/`isBase_ncard_add_deficiency_eq`).
  `deficiency_of_edgeSet_empty` drops `hne : V(G).Nonempty` (proof is valid for empty `V`).
  `hf₀img` proof: avoid `rintro (rfl | rfl)` on a disjunction that eliminates a free var
  still referenced later (§ 4 quirk); use `Set.image_insert_eq`/`Set.image_singleton` instead.
  `hEH`: `Set.inter_eq_right.mpr` (not `_left`) for `E(G) ∩ S = S`. `hBsize`: need
  `push_cast at heq` before `linarith` (numeric cast). Blueprint `lem:two-vertex-trichotomy`
  added; `\begin{enumerate}[(i)]` unsupported — use inline `(i)/(ii)/(iii)` prose.
- **L1a build (2026-06-12):** `cutEdges`/`TwoEdgeConnected` defs + transfer lemma
  `cutEdges_eq_crossingEdges_cutLabeling` (forward: `if_pos`/`if_neg` on `cutLabeling`;
  backward: case-split on `x ∈ V'`, swap to `hlink.symm` when `x ∉ V' ∧ y ∈ V'`) +
  `twoEdgeConnected_of_isKDof_zero` + `two_le_degree_of_twoEdgeConnected` in `Deficiency.lean`.
  `crossingEdges_cutLabeling_singleton_subset` + `…_ncard_le` moved from `ReducibleVertex.lean`
  to `Deficiency.lean` (natural home; downstream callers unchanged). Blueprint `def:cut-edges-2ec`
  added; `lem:two-edge-conn` gains a pointer sentence.
- **L1 signature pin (2026-06-11):** V2 → labeling-free `cutEdges` count, connectivity
  included (the disconnected Lemma-6.1 arm routes through the same ¬2EC case); V3 →
  in-place all-`k` (the landed swap proof needs one re-routed contradiction, no case
  split); V4 → mechanical. KT 3.6 by pure partition argument (refinement + straddle-free
  split — no matroid direct sum). KT 4.8(ii) decomposed: the reverse forest direction
  (KT 4.2) is the one new engine; 4.5(ii)/4.4-eq/4.7/4.3(ii)-rev ride on it. Numbering
  corrected against the PDF (`splitOff_isMinimalKDof` = KT 4.8(i)); the L2 floor flag
  recorded (conclude at `V(G).Nonempty`, base `1 ≤ ncard ≤ 2`). Canonical: §1.58.
- **Phase-open (2026-06-11):** the §1.56 motive design pass — carrier split (honest bare on
  `BodyHingeFramework` + panels; generic stays on `PanelHingeFramework`), ℤ-cast
  rank-deficiency equality as the shared rank form, the four-case all-`k` reduction, KT
  pp. 669–679 re-verified against the PDF. Canonical: §1.56.
- **L0 signature pin (2026-06-11):** V1 → pointwise `ExtensorInPanel` (coercion-fixed; meet
  lemma at `k = 2` only — its engine is the `Fin 4` duality suite, every M4 consumer is
  `d = 3`); V10 → B2 by relative re-derivation (the hub bound's all-`e` `hC` is an artifact;
  the real gap is the ambient `D·|V(G)ᶜ|`, closed by a complement-separating partition
  refinement — `finrank_partitionConstant` is already range-exact); M5 re-timed (weak-motive
  deletion = L9 invariant, L0 only de-spines it); two L9/L10 flags (`hD` tightens to
  `bodyBarDim n = screwDim 2`; `rigidityMatrix_prop11` keeps `reaim`). Canonical: §1.57.
- **L0a build (2026-06-11):** `ExtensorInPanel` in `RigidityMatrix.lean`; in `PanelLayer.lean`:
  `exists_two_perp_of_linearIndependent_normals` (rank-nullity on the `2×4` pairing map via
  `Matrix.of_apply` to unblock `mulVec`), `exists_extensor_eq_panelSupportExtensor` (double-
  annihilator via `Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff` + `(Submodule.
  mem_dualAnnihilator r).mp`, scalar absorption via `ιMulti (M := Fin 4 → ℝ).map_update_smul`),
  `extensorInPanel_panelSupportExtensor`. Ordering: the three lemmas placed *after*
  `panelSupportExtensor_join_eq_zero_of_eq_zero` (which they call). FRICTION §
  `ιMulti (M := …)` annotation added.
- **L0b build (2026-06-11):** in `GenericityDevice.lean` beside W2:
  `finrank_span_rigidityRows_add_finrank_infinitesimalMotions` (complement brick, stated with
  `Nat.card α` to avoid `[Fintype α]` in the signature; `rw [Nat.card_eq_fintype_card]` bridges
  to `finrank_screwAssignment`; `linarith` closes);
  `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows` (B1; forward = W2;
  reverse uses the complement brick + `zify [h1]` / `linarith` to handle the Nat subtraction
  in `hcount`, then `isInfinitesimallyRigidOn_vertexSet_of_finrank_le`).
- **L0e pair-swap (2026-06-11):** `def HasPanelRealization` moved from `GenericityDevice.lean`
  to `PanelHinge.lean` (import constraint: `GenericityDevice` imports `PanelHinge`, not the
  reverse; M4 stays in GenericityDevice). `theorem_55_generic` second-slot type → `HasPanelRealization k n G`;
  `hbase`/`hsplit`/`hcontract` params in `theorem_55_generic` + `theorem_55_d3` updated;
  IH-threading signatures in `case_I_realization`, `case_III_hsplit_producer`,
  `case_III_realization`, `h65` updated. All `.2`-uses in bodies were `.1`-only extractions —
  zero proof changes. Build+lint+verify.sh all green.
- **L0e M3-first build (2026-06-11):** M3 gains `(k n : ℕ)` + rank conjunct
  `(finrank ℝ … : ℤ) = screwDim k * (ncard - 1) - G.deficiency n`. Root producer seam
  pattern (GenericityDevice / CaseI root producers): tactic-mode with W2 +
  `zify [h1] + exact_mod_cast`. Extract-site pattern (all functions obtaining rigidity from
  M3): B1.mpr via `rw [hdef, sub_zero]` + `zify [h1_in] ... exact_mod_cast`. ~16 functions
  in CaseI.lean updated. `hasPanelRealization_of_generic` (M4) drops `hdef` (rank direct
  transfer). `hasFullRankRealization_of_generic` deleted (no live consumers; design doc
  confirmed). Pair unswapped by design (§1.57(e) M3-first cut).
- **L0d build (2026-06-11):** M2 `HasPanelRealization` + M4 `hasPanelRealization_of_generic`
  placed in `GenericityDevice.lean` (not `PanelHinge.lean` per the design): M4 needs W2
  `finrank_span_rigidityRows_of_rigidOn`, which is in GenericityDevice; PanelHinge can't
  import it. Temporary M4 signature has `hdef : G.deficiency n = 0` to bridge from the
  pre-L0e `IsInfinitesimallyRigidOn` slot to M2's ℤ rank form (discharged at call sites by
  `hG.1 : G.IsKDof n 0`). Congr-arg pattern `congr_arg Subtype.val hsupp ▸ hp` threads the
  `ScrewSpace 2` → `ExteriorAlgebra ℝ _` coercion for `ExtensorInPanel` witnesses.
- **L0c build (2026-06-11):** five bricks. In `PanelLayer.lean` under `section Classical_L0c`
  (after `screwDim_mul_numParts_sub_le_finrank_partitionMotions`): range-exact bound via same
  rank-nullity route using `finrank_partitionConstant` (`D·|range f|` exact);
  `crossingEdges_complement_sep` + `range_complement_sep_card` as helpers (both need `open
  Classical in` before their docstring — parser restriction, FRICTION §); relative hub via
  normalization: `Set.Finite.exists_injOn_of_encard_le` gives injection `ι₀` from `f₀ '' VG`
  into `VG`; `if_pos` closes `g u = ι₀ (f₀ u)` directly as a term proof (set-binding is
  definitionally the if-expression); `sᶜ.ncard` vs `s.compl.ncard` bridge via `rfl` for
  `linarith` (FRICTION §). B2 placed in `GenericityDevice.lean` (needs L0b's complement
  brick; `PanelLayer` doesn't import it).
