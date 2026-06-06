# Phase 22d — Claim 6.11's first green-machinery prerequisite (the matroid-base 4.3(ii) leaf) (work log)

**Status:** in progress. Opened 2026-06-05 design-pass-first; re-scoped 2026-06-05 to
attack KT Claim 6.11 **bottom-up** (build its leaf-most missing-green prerequisites, not
an axiomatized claim). Gap-2 leaf + Gap-3 combinatorial shell landed green 2026-06-06; the
footnote-6 recon (2026-06-06) settled the analytic kernel's shape; the kernel-route
decision (2026-06-06, user) is to build the algebraic-independence route directly. The full
Gap-1 chain — incl. the corank-gap discharge (eq. (6.23), node `lem:case-III-claim-6-11`) — is
green as of 2026-06-06; Claim 6.11 (eq. (6.23)) is now fully proven. The **candidate-completion**
(eqs. (6.24)–(6.29)) is now decomposing: its column-support LA core (eq. (6.28)) landed green; the
row-op construction of the output row `w` is the open crux. Recon detail lives in the design doc
(§1.30/§1.31/§1.26); this note carries the forward plan + a compressed verdict log.

## Current state

**Next concrete commit:** **Candidate-completion, next leaf — the row-op *construction* of the
`v`-column output row `w` (KT eq. (6.24)→(6.27))** from the now-green redundant `ab`-row. This
commit landed the *first* candidate-completion leaf: the **column-support LA core**
`BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`), KT eq. (6.28)
— a rigidity row vanishing on every screw assignment supported off `v` (`S v = 0 ⟹ f S = 0`) factors
as `f = (f ∘ₗ single v) ∘ₗ proj v`, i.e. is a *pure `v`-column* row. This is the structural fact that
turns the eq. (6.24)→(6.27) row-op output (whose `V∖{v}` part is all zero) into a `v`-column row that
then joins the `va`-block in the pin-a-body new block (`linearIndependent_sum_pinned_block`, already a
`D`-row-capable split), lifting `v`'s column from `D−1` to `D` — the missing `+1` to full `D(|V|−1)`.

**The remaining candidate-completion chain (the crux KT calls out, strata 2–3 / now decomposing).**
The hard, research-shaped step is the eq. (6.24)→(6.27) row-op *construction*: the redundant
`ab`-row gives `r i₀ ∈ W ⊔ span(r '' {j≠i₀})` (`W = span(R(G_v,q)-rows)`); lifting that combination to
`R(G,p₁)` via `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` yields a row `w` of `span(R(G,p₁)-rows)` whose
`V∖{v}` part vanishes, with `v`-part `Σⱼ λ(ab)j rⱼ(q(ab))` (eq. (6.28)). Then `w` extends the `va`-block
to a `D`-row new block (`linearIndependent_sum_pinned_block`), giving the `D(|V|−1)`-family **iff** the
top-left `D×D` block is full rank — KT's eq. (6.29) condition, which is exactly what the Claim-6.12
`D`-candidate disjunction supplies (Lemma 2.1, green). The next leaf is constructing `w` and its two
properties (`w ∈ span(R(G,p₁)-rows)`; `w` vanishes off `v` ⟹ feed the column-support core); the
eq. (6.18)/(6.22) finrank hypotheses of `exists_redundant_panelRow_ab_of_finrank_eq` are wired from the
green `lem:case-III-seed-rank-bridge`/`lem:case-III-rank-attainment` through rank-nullity
(`dim Z + dim span(rigidityRows) = D|α|`) in that same assembly.

**The Gap-1 corank-gap discharge is GREEN (this commit).** Two bricks:
- **Row-set identity** `BodyHingeFramework.span_rigidityRows_eq_sup_span_panelRow_edge` (`Pinning.lean`):
  for two frameworks agreeing on every `supportExtensor` (the `ofNormals Gab/Gv ends q` case — same
  seed/selector, only the graph differs) whose links differ by exactly one edge `e₀`,
  `span(R(Gab)-rows) = span(R(Gv)-rows) ⊔ e₀-block`. The only `Gab`-rows not already `Gv`-rows are the
  `e₀`-rows, which span the `e₀`-block (`span_panelRow_edge_eq`). Axiom-clean; no blueprint node (span
  bookkeeping, folded into the discharge node's prose, as `span_panelRow_edge_eq` is).
- **Corank-gap discharge** `BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq`
  (`CaseI.lean`): feeds the row-set identity + eq. (6.18)/(6.22) into
  `exists_redundant_panelRow_of_edge_of_finrank_lt` (last commit's LA core). Eq. (6.18) gives
  `dim(W ⊔ e₀-block) = D(m−1)`, eq. (6.22) gives `dim W = D(m−1) − k'`, so the `e₀`-block raises
  `dim W` by `k' < D−1` (`omega` on the truncated-ℕ finranks + `W ≤ W ⊔ block`). Node
  `lem:case-III-claim-6-11` (green; `\uses` the redundant-row pigeonhole + the eq.-(6.18)/(6.22)
  nodes). Axiom-clean.

The full `hub` construction (all green now): `partitionMotions` foundation + `def`-free floor (653f902),
`W_f` count (75c8fcc), dimension lower bound (a413308, `screwDim_mul_numParts_sub_le_finrank_partitionMotions`),
maximize-into-`hub` (bfafb7f). The dimension lower bound runs rank-nullity on the **full Pi** map +
`finrank_sup_add_finrank_inf_eq` (NOT the `W_f`-restricted map — heavy-carrier instance-diamond timeout,
QUIRKS § 39).

All three analytic prerequisites (i)/(ii)/(iii), the upper bound, the rank-attainment packaging, the
full `hub`, the redundant-row pigeonhole's LA core, the **full Gap-1 corank-gap discharge** (row-set
identity + the discharge, this commit), and both **combinatorial** factors of Claim 6.11
(`ForestSurgery.lean`: Gap-2 `splitOff_exists_base_inter_fiber_lt`, Gap-3 shell
`splitOff_removeVertex_minimalKDof`) are green + axiom-clean. Blueprint green:
`lem:case-III-claim-6-11-base`, `lem:case-III-gap3-minimalKDof`, `lem:case-III-seed-rank-bridge`,
`lem:case-III-seed-rank-upper`, `lem:case-III-rank-attainment`, `lem:case-III-claim-6-11-redundant-row`,
`lem:case-III-claim-6-11` (the eq.-(6.23) discharge), `lem:trivial-motions-rank-bound` (carries
`hub`); red: `lem:case-III`, `lem:case-II-realization`, `prop:rigidity-matrix-prop11` (the
`thm:theorem-55` half).

## Claim 6.11 discharge — the Gap 2 → 3 → 1 map

Claim 6.11 (KT p. 684, eq. (6.23)): `R(G_v^{ab}, q)` has a redundant row among its `D−1`
`ab`-rows — the `+1` that lifts 22c's stratum-1 `D(|V|−1)−1` brick to full `D(|V|−1)`.
KT's proof (pp. 684–685) factors, in dependency order:

1. **Gap 2 — matroid-base 4.3(ii)** (✓ landed): a base `B'` of `M(G̃_v^{ab})` with
   `h := |ãb ∩ B'| < D−1`. Pure combinatorial `M(G̃)`; all inputs green.
2. **Gap 3 — the nested IH-at-restriction.** `G_v := G_v^{ab} − ab = removeVertex v`;
   `B' ∖ ãb` independent in `M(G̃_v)` ⟹ `def(G̃_v) ≤ h ≤ D−2` ⟹ `G_v` minimal `k'`-dof.
   Apply the geometric IH (6.1) to `G_v` at the restricted seed `q|_{E_v}` ⟹
   `rank R(G_v, q|_{E_v}) = D(|V∖v|−1) − k'` (eq. (6.22)). **SPLIT (✓ shell + ✓ kernel
   `0`-dof core):** the combinatorial shell `splitOff_removeVertex_minimalKDof` and the
   seed-rank bridge (`..._of_algebraicIndependent`, the rigidity-transfer-to-fixed-seed
   core) are green; what remains is the `def>0` form of eq. (6.22) (`RankHypothesis (def)`,
   composing the transfer with `rigidityMatrix_prop11` + `rank_add_deficiency_eq`).
3. **Gap 1 — the `M(G̃)`↔row bridge** (✓ landed): eq. (6.18) `rank R(G_v^{ab},q) = D(|V∖v|−1)`
   at the fixed seed (seed-rank bridge — `G_v^{ab}` is `0`-dof, so rigid); with Gap 3's eq. (6.22),
   the `k' ≤ D−2 < D−1` corank over the `D−1` `ab`-rows forces one redundant (pigeonhole). Step ③
   is pure LA *given* (6.18)+(6.22): the abstract leaf, its geometric instantiation
   (`exists_redundant_panelRow_of_edge_of_finrank_lt`), and the **discharge**
   (`exists_redundant_panelRow_ab_of_finrank_eq`, this commit, via the row-set identity
   `span_rigidityRows_eq_sup_span_panelRow_edge`) are all green. eq. (6.18)/(6.22) enter the discharge
   as the two `finrank` hypotheses (the honest "(6.18) ∧ (6.22) ⟹ (6.23)" step).

The eq. (6.18) full rank lifts 22c's `case_II_placement_eq612` `−1` to the `+1` Claim 6.11 supplies.

## Lemma checklist

- [x] `Graph.forest_surgery_count` — strengthened with the `|ãb ∩ ⋃ Fs'i| < D−1` conjunct
  (KT Lemma 4.1's second conclusion). Caller `forest_surgery_split` re-destructures.
- [x] `Graph.splitOff_exists_base_inter_fiber_lt` — Gap-2 leaf (above), green +
  axiom-clean. Node `lem:case-III-claim-6-11-base`.
- [x] `Graph.splitOff_removeVertex_minimalKDof` — Gap-3 combinatorial shell, green +
  axiom-clean: `G_v = removeVertex v` minimal `k'`-dof with `0 ≤ k' = def(G̃_v) ≤ D−2`.
  Minimality via `subgraph_minimality` (`G_v ≤ G`); bound via the Gap-2 base count
  (`B'∖ãb` indep in `M(G̃_v) = M(G̃_v^{ab})↾E(G̃_v)`, `rank ≥ |B'|−h`, def=corank). Did
  **not** need `removeVertex_deficiency_ge`. Node `lem:case-III-gap3-minimalKDof`.
- [x] `AlgebraicIndependent.aeval_ne_zero` — kernel leaf (i): an alg.-independent family `x` sends
  every nonzero `p : MvPolynomial ι R` to a nonzero `aeval x p` (contrapositive of mathlib's
  `eq_zero_of_aeval_eq_zero`). Upstream-eligible; mirrored at
  `Mathlib/RingTheory/AlgebraicIndependent/Defs.lean`, axiom-clean. The `R=ℚ`, `A=ℝ` instance is
  what footnote 6 needs (`q` real, rank-poly over ℚ); the same-ring `eval` form is vacuous (forces
  `ι` empty), so only the `aeval` form ships. No blueprint node yet (kernel `\lean{}` lands with (iii)).
- [x] `MvPolynomial.eval_map_algebraMap` / `map_algebraMap_ne_zero_iff` — (ii-b) leaf-most: the
  evaluation descent (`eval q (map (algebraMap R A) Q₀) = aeval q Q₀`, via `aeval_map_algebraMap` +
  `aeval_eq_eval`) and the nonzero transfer along a faithful `algebraMap`. Upstream-eligible,
  axiom-clean; mirrored at `Mathlib/RingTheory/MvPolynomial/Tower.lean`. No blueprint node (kernel
  `\lean{}` lands with (iii)).
- [x] `MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` — (ii-b) consumed
  assembly (`Tower.lean`): nonzero `Q : MvPolynomial σ A` with `(Q.coeffs : Set A) ⊆ range
  (algebraMap R A)`, evaluated at `AlgebraicIndependent R`-seed `q`, is nonzero. Packages the descent
  pair + leaf (i) over mathlib's `mem_range_map_iff_coeffs_subset`. Axiom-clean. No blueprint node yet.
- [x] (ii-b) the `complementIso`-rational-entries leaf + propagation — **green this commit.**
  `Meet.lean`: `wedgePairing_ιMulti_family_mem_range_intCast` (the diagonal pairing is `±1` via
  `ιMulti_family_mul_of_disjoint` = signed top basis vector + `topEquiv_ιMulti_family_default`,
  off-diagonal `0`) ⟹ `complementIso_exteriorPower_repr_mem_range_{intCast,algebraMap}` (the
  matrix entry `repr (complementIso (e_S)) t` is rational). `PanelLayer.lean`:
  `{normalsJoinPoly,panelSupportPoly,annihRowPoly,annihRowPoly_smul_sign}_mem_range_map`
  propagate it as `(map (algebraMap ℚ ℝ)).range` membership. `Rank.lean`:
  `Matrix.det_mem_range_of_entries` + `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`
  certify `Q.coeffs ⊆ range (algebraMap ℚ ℝ)` from rational `c`. All axiom-clean. Mirror helper:
  `ExteriorAlgebra.ιMulti_family_congr` (cardinality cast). No blueprint node yet (kernel `\lean{}`
  lands with (iii)).
- [x] **wire (ii-b) into the device `Q`** — all three producers
  `PanelHingeFramework.exists_rankPolynomial_of_rigidOn{,_linking,_linking_set}`
  (`GenericityDevice.lean`) route through
  `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`, discharging `hc` from
  `annihRowPoly_smul_sign_mem_range_map`, so each produced `Q` carries
  `Q.coeffs ⊆ range (algebraMap ℚ ℝ)`. Axiom-clean. The `_proj` producer's rationality (deferred
  here) landed with (ii-a) below.
- [x] (ii-a) first sub-step — the moment-curve alg-independence question, **settled NO**. Mirror
  `exists_injective_algebraicIndependent_real` (+ `infinite_index_of_transcendenceBasis_real`,
  `Mathlib/RingTheory/AlgebraicIndependent/TranscendenceBasis.lean`): a finite injective alg-indep-over-ℚ
  seed `q : σ → ℝ` from a transcendence basis. The moment curve was NOT alg-indep; alg-independence is
  now a separate point from general position. Axiom-clean. FRICTION *[mirrored]*; QUIRKS § 37.
- [x] (ii-a) motive-conjunct wiring (this commit) — `HasGenericFullRankRealization` carries a fifth
  conjunct `AlgebraicIndependent ℚ (fun p ↦ Q.normal p.1 p.2)`; every generic producer selects the
  alg-indep seed (`exists_injective_algebraicIndependent_real`) and discharges each rigid leg's rational
  rank-poly non-root via `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`. Required:
  `exists_generalPosition_polynomial` + `exists_rankPolynomial_of_rigidOn_linking_set_proj` now carry
  `Q.coeffs ⊆ range` (the latter via the generic `dualMap_matrix_entry_eq`: `extProj`'s dual-map matrix
  entry is `0`/`1`). `case_I_realization` discharges the block-triangular composer's `hQc_rat`. Green +
  axiom-clean.
- [x] (iii) `lem:case-III-seed-rank-bridge` — the seed-rank bridge, green + axiom-clean
  (`PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`, `CaseI.lean`):
  rigid `ofNormals G ends q₀` ⟹ rigid at any alg-indep-over-ℚ `q`, via (rational-`Q` producer) →
  (footnote-6 non-root) → (device consumer). This is the eq. (6.18)/(6.22) transfer **at the `0`-dof
  level** (rigidity); the `def>0` form (`RankHypothesis (def G̃_v)`) + Gap-1 pigeonhole are the next leaf.
- [x] **Gap 1 — eq. (6.22) rank *upper* bound**:
  `PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`
  (`CaseI.lean`) — a rational rank polynomial `Q` witnessing an independent `panelRow`-subfamily `s`
  bounds `dim Z(G,q) ≤ D|α| − |s|` at any alg-indep-over-ℚ `q`. Green + axiom-clean. Node
  `lem:case-III-seed-rank-upper`.
- [x] **Gap 1 — eq. (6.22) rank-attainment packaging** (this commit):
  `PanelHingeFramework.rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent` (`CaseI.lean`)
  — assembles the upper bound with the matroid-predicted count (`#s ≥ D(|V|−1) − def`), the spanning
  split `D|V| = D(|V|−1) + D`, and `hub` into `RankHypothesis (def G̃)` (`dim Z = D + def`) at the fixed
  seed. Axiom-clean; carries `hub` undischarged ⟹ red node `lem:case-III-rank-attainment` (honest
  green-modulo per the honesty gate). The omega cast/product/truncation dance: QUIRKS § 2 (three-way variant).
- [x] **Gap 1 — the `hub` foundation** (commit 653f902): `partitionMotions f` (`PanelLayer.lean`,
  `BodyHingeFramework` namespace) — motions constant on each part of a labeling `f`,
  `= Z ⊓ partitionConstant f`; `partitionMotions_le_infinitesimalMotions`,
  `trivialMotions_le_partitionMotions`, and the `def`-free floor
  `screwDim_le_finrank_infinitesimalMotions` (`D ≤ dim Z`, every realization). Axiom-clean. No
  blueprint node (internal `hub`-construction infra; the node lands with the full `hub`).
- [x] **Gap 1 — the `W_f` count** (this commit): `partitionConstant f` (`PanelLayer.lean`) — the
  part-constant space *without* the motion constraint, `= range (funLeft ℝ (ScrewSpace k)
  (rangeFactorization f))` (`partitionConstant_eq_range_funLeft`), so `finrank W_f = D·|range f|`
  (`finrank_partitionConstant`, via `funLeft_injective_of_surjective` + `finrank_screwAssignment`)
  and `D·|P| ≤ finrank W_f` (`mul_numParts_le_finrank_partitionConstant`, `numParts = |f''V(G)| ≤
  |range f|`). `partitionMotions` rewired to `Z ⊓ partitionConstant f`. Axiom-clean. No blueprint node.
- [x] **Gap 1 — the `hub` dimension lower bound** (this commit): `D·|P| − (D−1)·d_G(P) ≤
  finrank (partitionMotions f)` (`screwDim_mul_numParts_sub_le_finrank_partitionMotions`,
  `PanelLayer.lean`, ℤ-form, axiom-clean). The per-crossing-edge cut `partitionCutMap`
  (`= crossingSpanPi.mkQ ∘ₗ` the relative-screw-center pi-map) has `ker ⊓ W_f = partitionMotions f`
  (`partitionCutMap_ker_inf`) and codomain dim `(D−1)·d_G(P)` (`finrank_partitionCutMap_codomain`,
  via `Submodule.quotientPi`, needs `C(e) ≠ 0`). Run rank-nullity on the **full Pi** map (not the
  `W_f`-restricted one) + `finrank_sup_add_finrank_inf_eq` to dodge a heavy-carrier instance-diamond
  `whnf` timeout. Promoted: QUIRKS § 39. No blueprint node (internal `hub` infra).
- [x] **Gap 1 — maximize into `hub`** (this commit): `screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  (`PanelLayer.lean`) — `D + def(G̃) ≤ dim Z` at `n = k+1` given `∀ e, supportExtensor e ≠ 0`. Picks
  the `def`-attaining `f` (`exists_eq_ciSup_of_finite`), reconciles `screwDim k = bodyBarDim (k+1)`,
  rewrites the lower bound's LHS to `D + partitionDef(f)`, transfers via `partitionMotions f ≤ Z`.
  **Discharged** into `rigidityMatrix_prop11` + the rank-attainment packaging (both now take
  `hn`/`hC` not `hub`); flipped `lem:case-III-rank-attainment` green. Axiom-clean.
- [x] **Gap 1 — the abstract pigeonhole leaf** (this commit):
  `Submodule.exists_mem_sup_span_image_compl_of_finrank_lt` + the helper
  `Submodule.finrank_map_mkQ` (`Mathlib/LinearAlgebra/Dimension/Constructions.lean`,
  upstream-eligible mirrors, axiom-clean). The pure-LA `finrank (W ⊔ span g) < finrank W + |ι|` ⟹
  a redundant family member. No blueprint node (mirrors).
- [x] **Gap 1 — the redundant-row pigeonhole's LA core** (this commit):
  `BodyHingeFramework.exists_redundant_panelRow_of_edge_of_finrank_lt` (`CaseI.lean`) — given a
  transversal hinge `e`, a subspace `W`, and the corank gap `finrank (W ⊔ span(e-block)) < finrank W
  + (D−1)`, produces the `Fin (D−1)`-indep `e`-row family `r` (`span (range r) = e-block`) with a
  redundant member `r i₀ ∈ W ⊔ span(r '' {j≠i₀})`. The geometric instantiation of the abstract leaf
  at one edge's `D−1` rows. Green + axiom-clean. Node `lem:case-III-claim-6-11-redundant-row`. Fused
  helper `finrank_span_panelRow_edge` (`Pinning.lean`, dedups the per-edge finrank-`D−1` chain).
- [x] **Gap 1 — the row-set identity** (this commit):
  `BodyHingeFramework.span_rigidityRows_eq_sup_span_panelRow_edge` (`Pinning.lean`) — for two
  frameworks agreeing on every `supportExtensor` whose links differ by exactly one edge `e₀`,
  `span(R(Fab)-rows) = span(R(Fv)-rows) ⊔ e₀-block`. The genuine geometric input KT's eq. (6.23) needs.
  Axiom-clean; no blueprint node (span bookkeeping, folded into the discharge node's prose).
- [x] **Gap 1 — discharge the corank gap at `e = ab`** (commit fc2ea7b):
  `BodyHingeFramework.exists_redundant_panelRow_ab_of_finrank_eq` (`CaseI.lean`) — feeds the row-set
  identity + eq. (6.18) (`dim span(R(Gab)-rows) = D(m−1)`) + eq. (6.22) (`= D(m−1) − k'`, `k' ≤ D−2`)
  into `exists_redundant_panelRow_of_edge_of_finrank_lt` ⟹ the redundant `ab`-row (eq. (6.23)). The
  two finrank equations are taken as hypotheses (the honest "(6.18) ∧ (6.22) ⟹ (6.23)" step). Green +
  axiom-clean. Node `lem:case-III-claim-6-11`.
- [x] **Candidate-completion — column-support LA core** (this commit):
  `BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`, KT eq. (6.28))
  — a rigidity row `f` vanishing on every screw assignment supported off `v` (`S v = 0 ⟹ f S = 0`)
  factors as `f = (f ∘ₗ single v) ∘ₗ proj v`, i.e. is a pure `v`-column row. The structural fact that
  turns the eq. (6.24)→(6.27) row-op output (`V∖{v}` part all zero) into a `v`-column row joining the
  `va`-block in `linearIndependent_sum_pinned_block`'s `D`-row-capable pin-a-body split. Axiom-clean.
  No blueprint node (internal LA infra, like `span_panelRow_edge_eq` / the row-set identity — folds
  into the eventual candidate-completion discharge node's prose).
- [ ] **Candidate-completion — the row-op construction of `w`** (next): lift the redundant `ab`-row to
  `R(G,p₁)` via `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)` ⟹ `w ∈ span(R(G,p₁)-rows)` vanishing off `v`
  (eq. (6.24)→(6.27)). The crux KT calls out (p. 680); likely its own sub-phase.
- [ ] **Candidate-completion — the conditional rank lift** (after `w`): `w` extends the `va`-block to a
  `D`-row new block ⟹ `D(|V|−1)`-family conditional on the top-left `D×D` block full rank (eq. (6.29)),
  discharged by the Claim-6.12 disjunction (Lemma 2.1, green).

## Deferred sub-phases (future work in the phase)

Parked until the leaf's shape is clear; a sub-letter is minted when its turn comes.

- **Candidate-completion + Claim 6.12 disjunction.** With the redundant `ab`-row, lift
  22c's `case_II_placement_eq612` `≥ D(|V|−1)−1` to `= D(|V|−1)` on one candidate (eq.
  (6.24)–(6.29) row-op), then the Claim-6.12 extensor-span contradiction via the **green**
  Lemma 2.1 (`omitTwoExtensor_linearIndependent`) + the eq. (6.44) degree-2 forcing picks
  the full-rank candidate. Claim 6.12 **de-risked** (Lemma 2.1 green). Candidate normal
  form: **abstract one per-candidate lemma, instantiate ×3** (`p₂=p₁` with `a↔b`;
  `p₃=p₁∘ρ`); `case_II_placement_eq612` is already this shape (22c recon, design doc §1.26). The
  product-route *relaxation* (pick `q` as a non-root of the finite product of the nested IH rank
  polynomials, avoiding alg-independence at `d=3`; ~70% confidence) is tracked in
  `notes/AlgebraicIndependence.md`.
- **The `d=3` assembly** — `prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55`
  flip + wiring the green `case_I_realization`. Unlettered.
- **General `d`** (Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 — Phase 23.

## Blockers / open questions

- **The full Gap-1 chain is green** (closed commit fc2ea7b): seed-rank bridge (`def=0`, eq. (6.18)),
  upper bound `lem:case-III-seed-rank-upper` + rank-attainment packaging `lem:case-III-rank-attainment`
  (`def>0`, eq. (6.22)), the genericity-free `hub` lower bound (discharged), the abstract pigeonhole
  leaf + its per-edge instantiation, the row-set identity, and the corank-gap discharge
  (`exists_redundant_panelRow_ab_of_finrank_eq`, node `lem:case-III-claim-6-11`) are all green +
  axiom-clean. No open Gap-1 blocker remains.
- **Candidate-completion — the row-op construction of `w` (eq. (6.24)→(6.27)) is the open crux.** Its
  column-support LA core (eq. (6.28), `dualMap_eq_comp_single_proj_of_vanish_off`) is green (this
  commit); the *construction* of `w` (lifting the redundant `ab`-row's combination to `R(G,p₁)` and
  showing the `V∖{v}` part vanishes) is research-shaped — KT p. 680. The rank lift past it is then
  conditional on the top-left `D×D` block (eq. (6.29)), discharged by Claim 6.12.
- **Claim 6.12 — de-risked** (bottoms on the green Lemma 2.1).
- **Recurring Lean traps** (carry from 22a–c, FRICTION): heavy `IsInfinitesimallyRigidOn`
  defeq across `ofNormals`/`withGraph` graph-swaps can `isDefEq`-timeout — make the two
  frameworks *syntactically* equal before `convert`; transfer rigidity via a
  `mem_infinitesimalMotions` round-trip. (Bites in the candidate-completion assembly.)

## Hand-off / next phase

**Next concrete commit:** **Candidate-completion, the row-op construction of `w` (KT eq.
(6.24)→(6.27)).** This commit landed the candidate-completion's first leaf, the column-support LA core
`dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`, KT eq. (6.28)): a rigidity row
vanishing off `v`'s column is a pure `v`-column row `(f ∘ₗ single v) ∘ₗ proj v`. The next leaf builds
the row-op output `w` itself — lift the redundant `ab`-row's combination
(`exists_redundant_panelRow_ab_of_finrank_eq`, green) to `R(G,p₁)` via
`R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)`, producing `w ∈ span(R(G,p₁)-rows)` vanishing off `v`; the
column-support core then makes `w` a `v`-column row, which joins the `va`-block in the
`D`-row-capable pin-a-body split (`linearIndependent_sum_pinned_block`), lifting `case_II_placement_eq612`'s
`D(|V|−1)−1` to `D(|V|−1)` **conditional on** the top-left `D×D` block being full rank (eq. (6.29)).
That conditional is then discharged by the Claim-6.12 `D`-candidate disjunction (extensor-span
contradiction via the green Lemma 2.1). The assembly also converts the green
`lem:case-III-seed-rank-bridge`/`lem:case-III-rank-attainment` conclusions (rigidity / `RankHypothesis
(def)`) into the eq. (6.18)/(6.22) `finrank (span rigidityRows)` hypotheses
`exists_redundant_panelRow_ab_of_finrank_eq` consumes, via rank-nullity
`dim Z + dim span(rigidityRows) = D|α|` (already used in `finrank_..._le_of_rankPolynomial_...`).
`lem:case-III` stays red until the assembly lands.

After candidate-completion: the Claim-6.12 disjunction, the `d=3` assembly, and general-`d`
(Phase 23). The row-op construction of `w` is the crux KT calls out (p. 680); it likely earns its own
dedicated sub-phase — name it when the construction's shape is clear (the same defer-the-finer-cut
discipline as 22a→22b, 22c→22d).

KT math: KT §6.4.1 (Lemma 6.10, Claims 6.11/6.12, eqs. (6.22)–(6.45)), §4 (Lemmas
4.3(ii)/4.4/4.7/4.8). Recon detail: design doc §1.30 (footnote-6 kernel) + §1.31
(kernel-route) + §1.26 (candidate structure); also `notes/Phase20.md`
(`splitOff_isMinimalKDof`), `notes/Phase21b.md` *Finding A/B*, `notes/Phase22c.md`,
`notes/AlgebraicIndependence.md` (the alg-independence tracker).

## Decisions & recon log (compressed)

The finished-work tail — one-line verdicts; the blow-by-blow is in the cited commits /
design-doc arcs (per `notes/CLAUDE.md` *Forward-weighted note*).

- **Candidate-completion column-support core — eq. (6.28) (this commit).**
  `dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`): a rigidity row `f` with
  `S v = 0 ⟹ f S = 0` equals `(f ∘ₗ single v) ∘ₗ proj v` — split `S = single v (S v) + (S − single v
  (S v))`, `f` kills the off-`v` summand. The first candidate-completion leaf: KT's eq. (6.24)→(6.27)
  row-op output has `V∖{v}` part zero, so this makes it a pure `v`-column row that extends the `va`-block
  to a `D`-row pin-a-body block (`linearIndependent_sum_pinned_block`). No blueprint node (internal LA
  infra). Axiom-clean. No new friction (standard `Pi.single`/`map_sub` algebra).
- **Gap-1 corank-gap discharge — eq. (6.23) (commit fc2ea7b).** Two bricks close the Gap-1 chain. (1)
  Row-set identity `span_rigidityRows_eq_sup_span_panelRow_edge` (`Pinning.lean`): two frameworks
  agreeing on every `supportExtensor` (the `ofNormals Gab/Gv ends q` case) with links differing by one
  edge `e₀` have `span(R(Fab)-rows) = span(R(Fv)-rows) ⊔ e₀-block` (the only extra `Fab`-rows are the
  `e₀`-rows, spanning the block via `span_panelRow_edge_eq`; the swap branch uses the new
  `hingeRow_swap`). (2) Discharge `exists_redundant_panelRow_ab_of_finrank_eq` (`CaseI.lean`): feeds the
  identity + eq. (6.18) (`= D(m−1)`) + eq. (6.22) (`= D(m−1) − k'`, `k' ≤ D−2`) into the LA core ⟹ the
  redundant `ab`-row. The two finrank equations are hypotheses (honest "(6.18) ∧ (6.22) ⟹ (6.23)"; the
  green seed-rank-bridge / rank-attainment nodes supply them via rank-nullity). Node
  `lem:case-III-claim-6-11`, green + axiom-clean. Fused the thrice-repeated `hingeRow u v r = hingeRow
  v u (-r)` inline orientation flip into `hingeRow_swap` (`RigidityMatrix.lean`), FRICTION *[resolved]*.
- **Gap-1 redundant-row pigeonhole's LA core (commit b82c269).**
  `BodyHingeFramework.exists_redundant_panelRow_of_edge_of_finrank_lt` (`CaseI.lean`): the geometric
  instantiation of the abstract leaf at the `D−1` panel rows of one transversal hinge `e`. Given any
  subspace `W` and the corank gap `finrank (W ⊔ span(e-block)) < finrank W + (D−1)`, produces the
  `Fin (D−1)`-indep `e`-row family `r` (N7b-1 `exists_independent_panelRow_of_edge`; `span (range r) =
  e-block` by `eq_of_le_of_finrank_eq`), then applies the abstract leaf. Green + axiom-clean. Node
  `lem:case-III-claim-6-11-redundant-row` (`\uses` the eq.-(6.18)/(6.22) gap-suppliers + N7b-1). Fused
  the duplicated per-edge finrank-`D−1` chain into `finrank_span_panelRow_edge` (`Pinning.lean`),
  FRICTION *[resolved]*.
- **Gap-1 abstract pigeonhole leaf (commit 893e83f).** `Submodule.exists_mem_sup_span_image_compl_of_finrank_lt`
  (`Mathlib/LinearAlgebra/Dimension/Constructions.lean`): `finrank (W ⊔ span (range g)) < finrank W + |ι|`
  ⟹ `∃ i, g i ∈ W ⊔ span (g '' {j ≠ i})` (a redundant family member). Contrapositive in `V ⧸ W`: no
  redundant member ⟹ `W.mkQ ∘ g` LI (`linearIndependent_iff_notMem_span`) ⟹ span finrank `|ι|` ⟹
  `finrank (W ⊔ span g) = finrank W + |ι|` via the helper `Submodule.finrank_map_mkQ` (rank–nullity on
  `W.mkQ ∘ S.subtype`, range `S.map mkQ`, kernel `W ⊓ S`). Both upstream-eligible mirrors, axiom-clean,
  no blueprint node. FRICTION *[mirrored]*.
- **Gap-1 `hub` maximized + discharged (commit bfafb7f).** `BodyHingeFramework.screwDim_add_deficiency_le_finrank_infinitesimalMotions`
  (`PanelLayer.lean`): `D + def(G̃) ≤ dim Z` for `n = k+1` given `∀ e, supportExtensor e ≠ 0`. Picks the
  `def`-attaining `f` (`exists_eq_ciSup_of_finite`), reconciles `screwDim k = bodyBarDim (k+1)`
  (FRICTION), rewrites the dimension lower bound's LHS to `D + partitionDef(f)`, transfers via
  `partitionMotions f ≤ Z`. **Discharged into** `rigidityMatrix_prop11` (`PanelHinge.lean`) + the
  rank-attainment packaging (`CaseI.lean`), both now taking `hn : n=k+1` + `hC : ∀ e, supportExtensor e ≠ 0`
  not `hub`. Blueprint: `lem:case-III-rank-attainment` → green; `hub` lower bound pinned on
  `lem:trivial-motions-rank-bound`; `prop:rigidity-matrix-prop11` proof prose records the discharge
  (still red on `thm:theorem-55`). Axiom-clean.
- **Gap-1 `hub` dimension lower bound landed (commit a413308).** `PanelLayer.lean`:
  `screwDim_mul_numParts_sub_le_finrank_partitionMotions` (ℤ-form `D·|P| − (D−1)·d_G(P) ≤
  dim (partitionMotions f)`, axiom-clean). The per-crossing-edge cut `partitionCutMap` (=
  `crossingSpanPi.mkQ ∘ₗ` the relative-screw-center pi-map; codomain a **single** `Submodule.pi`
  quotient) has `ker ⊓ W_f = partitionMotions f` (`partitionCutMap_ker_inf` — automatic at
  non-crossing edges by part-constancy, `eq_and_eq_or_eq_and_eq` endpoint-swap at crossing) and
  codomain dim `(D−1)·d_G(P)` (`finrank_partitionCutMap_codomain`, via `Submodule.quotientPi` split
  + `finrank_span_singleton`, needs `C(e) ≠ 0`). **Route lesson:** run rank-nullity on the *full Pi*
  map + `finrank_sup_add_finrank_inf_eq`, **not** the `W_f`-restricted map — the latter's
  `Submodule`/`Submodule.Quotient` `AddCommMonoid`-vs-`AddCommGroup` reconciliation over `ScrewSpace`
  `whnf`-times-out even at `maxHeartbeats 1.6M`. Promoted: QUIRKS § 39; new import
  `Mathlib.LinearAlgebra.Quotient.Pi`. Remaining `hub`: maximize over `f` (one step).
- **Gap-1 `hub` `W_f` count landed (commit 75c8fcc).** `partitionConstant f = range (funLeft f')`
  (`partitionConstant_eq_range_funLeft`), `finrank W_f = D·|range f|`, `D·|P| ≤ finrank W_f`;
  `partitionMotions` rewired to `Z ⊓ partitionConstant f`. Axiom-clean.
- **Gap-1 `hub` foundation — `partitionMotions` landed (commit 653f902).** The subspace `Z ⊓ W_f`,
  `≤ Z`, `trivialMotions ≤ ·`, and the `def`-free floor `D ≤ dim Z`
  (`screwDim_le_finrank_infinitesimalMotions`, the `partitionDef = 0` instance of `hub`).
- **Gap-1 rank-attainment packaging landed (commit 9c58954).** `lem:case-III-rank-attainment` =
  `PanelHingeFramework.rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent` (`CaseI.lean`):
  the upper bound's `dim Z ≤ D|α| − #s`, the matroid-predicted count `#s ≥ D(|V|−1) − def`, the
  spanning split `D|V| = D(|V|−1) + D`, and the `hub` lower bound assemble (via `rigidityMatrix_prop11`)
  into `RankHypothesis (def G̃)`. Axiom-clean. Carries `hub` undischarged ⟹ **red** node (honest
  green-modulo per the honesty gate); breaks the would-be dep-graph cycle by *not* `\uses`-ing
  `prop:rigidity-matrix-prop11` (whose proof uses `thm:theorem-55` ⟶ Case III). omega friction
  (cast/product/truncation) → QUIRKS § 2 three-way variant.
- **Gap-1 eq. (6.22) rank *upper* bound landed (commit b4299eb).** `lem:case-III-seed-rank-upper` =
  `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`: a rational rank polynomial
  `Q` witnessing an independent `panelRow`-subfamily `s` bounds `dim Z(G,q) ≤ D|α| − #s` at any
  alg-indep `q` (footnote-6 non-root makes `s` LI at `q`; rank-nullity bounds `dim Z`). Axiom-clean,
  honest (input `Q` is an unrelated rigid seed's witness, not the rank concluded).
- **(iii) seed-rank bridge landed (commit 0d71f44).** `lem:case-III-seed-rank-bridge` =
  `isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`: rigid `ofNormals G ends q₀` ⟹ rigid at
  any alg-indep-over-ℚ `q`, via `exists_rankPolynomial_of_rigidOn` → footnote-6 non-root → device
  consumer. The eq. (6.18)/(6.22) transfer at the `0`-dof level. Green, axiom-clean, honest.
- **(ii-a) motive-conjunct wiring landed (commit 9caa1a1).** `HasGenericFullRankRealization` gained a
  fifth conjunct `AlgebraicIndependent ℚ (fun p ↦ Q.normal p.1 p.2)` (paralleling GP/link-recording;
  `hasFullRankRealization_of_generic` forgets it). Every generic producer now picks the alg-indep seed
  `exists_injective_algebraicIndependent_real` over `MvPolynomial.exists_eval_ne_zero` and discharges
  each rigid leg's rational rank-poly non-root via `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`
  (the same seed lands rigidity+GP+conjunct). This forced the **`_proj` rationality** the (ii-b)
  checklist had deferred: `exists_rankPolynomial_of_rigidOn_linking_set_proj` now carries
  `Qc.coeffs ⊆ range` (its `cD = ∑ C(M j l)·c i l` rational because `extProj`'s dual-map matrix entry
  `M j l ∈ {0,1}`), via the new generic `dualMap_matrix_entry_eq`; `exists_generalPosition_polynomial`
  likewise gained `Qgp.coeffs ⊆ range`. The block-triangular composer takes `hQc_rat`;
  `case_I_realization` supplies it. Promoted: QUIRKS § 38 (extract a generic helper to dodge the
  heavy-dual `whnf`), FRICTION (`Subring.foo _` stuck `CommRing ?m`). Green + axiom-clean.
- **(ii-a) first sub-step — moment-curve alg-independence settled.** Verdict: the moment curve is NOT
  alg-indep over ℚ (`q(a,0)=1`, `q(a,2)=q(a,1)²`); substitute the transcendental seed
  `exists_injective_algebraicIndependent_real` (mirror, off an ℝ/ℚ transcendence basis, infinite by
  `infinite_index_of_transcendenceBasis_real`). Alg-independence and general position are now separate
  points. Axiom-clean; cross-universe embedding via `Cardinal.lift_mk_le'` (QUIRKS § 37).
- **Kernel (ii-b) wired into the device `Q` (this commit).** The three producers
  `exists_rankPolynomial_of_rigidOn{,_linking,_linking_set}` (`GenericityDevice.lean`) now route
  through `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range`, with `hc`
  discharged by `annihRowPoly_smul_sign_mem_range_map` against the shared `c i j` shape (one-line
  `_ _ _ _ _ _` unification). Conclusion gains the `Q.coeffs ⊆ range (algebraMap ℚ ℝ)` conjunct;
  the nine CaseI destructures re-pattern with a `_`. Mechanical, axiom-clean, no friction. The
  `_proj` variant is out of scope (its projected `Q` needs `M` rational too; not the direct kernel
  route).
- **Re-scope (2026-06-05).** User overrode the opening "axiomatize Claim 6.11" verdict
  (commit 4e6a7bb): build Claim 6.11's leaf-most missing prerequisite bottom-up rather
  than deferring onto Claim 6.12.
- **Green substrate richer than the opening recon credited.** Gap 2 is buildable from green
  Phase-20 infra — `splitOff_isMinimalKDof`'s proof already builds the `ãb`-base count (and
  discarded it); `isBase_vfiber_ncard_ge` is a near-verbatim template. (Detail in the Gap-2
  leaf's proof + commit 13d2464.)
- **Gap-2 leaf (commit 13d2464).** Two bricks: (1) strengthen `forest_surgery_count` with
  the `< D−1` conjunct (the inserted `r i` are the only `e₀`-copies, `h' ≤ D−2`); (2) the
  `k=0` base assembly (`def = 0` ⟹ a full-rank independent set is a base,
  `Indep.isBase_of_ncard`). KT 4.3(ii) is an **existence** statement (a base with `<D−1`),
  not "every base" — matching the Claim-6.11 use.
- **Gap-3 recon (commit 0f7ef2a).** Gap 3 **splits**: green combinatorial shell
  + research-shaped analytic kernel; the combinatorial glue (`def(G̃_v) ≤ h` ⟹ `G_v`
  minimal `k'`-dof) is all green Phase-19/20.
- **Gap-3 shell (commit d218fa0).** `splitOff_removeVertex_minimalKDof` green: minimality via
  `subgraph_minimality` (`G_v ≤ G`), bound via the Gap-2 base (`B'∖ãb` indep in the
  restriction `M(G̃_v) = M(G̃_v^{ab})↾E(G̃_v)`, so `rank ≥ |B'|−h`; def=corank at `def=0`
  gives `def(G̃_v) ≤ h < D−1`). The route did **not** need `removeVertex_deficiency_ge` (the
  splitting-off side carries the count). `isBase_vfiber_ncard_ge` was the structural template.
- **Footnote-6 kernel recon (commit 892f44c; design doc §1.30).** eq. (6.22) is NOT a green
  re-exposure of 21b/22b machinery. Confirmed two of the user's three structural claims
  (matroid↔row link = the IH `rigidityMatrix_prop11`, green-modulo; step ③ pure LA);
  refuted the bottom line — the motive is existence-only (`∃ Q`), `IsGeneralPosition` is
  only pairwise transversality, not non-root-ness of `Q`. Named the missing brick:
  `non-root-from-algebraic-independence`.
- **Kernel-route decision (commit 3f0ea8e; design doc §1.31).** Build the alg-independence
  route directly to green (the certain path); product-route relaxation tracked in
  `notes/AlgebraicIndependence.md`.
- **Kernel leaf (i) (commit fb635d9).** `AlgebraicIndependent.aeval_ne_zero` — one-line
  contrapositive of mathlib's `eq_zero_of_aeval_eq_zero`, mirrored under
  `Mathlib/RingTheory/AlgebraicIndependent/`; the `R=ℚ`, `A=ℝ` footnote-6 instance ships (the
  same-ring `eval` form is vacuous). Wired into the root aggregator as a leaf awaiting (iii).
- **Kernel (ii-b) descent mirror (commit b21b239).** `MvPolynomial.eval_map_algebraMap` (`eval q
  (map (algebraMap R A) Q₀) = aeval q Q₀` — `aeval_map_algebraMap` at the self-tower `A=B` through
  `aeval_eq_eval`) + `map_algebraMap_ne_zero_iff` (nonzero transfer via the injective faithful
  `algebraMap`). All pieces already in mathlib; the leaf packages them in the consumed form. Mirrored
  at `Mathlib/RingTheory/MvPolynomial/Tower.lean`, axiom-clean. A true leaf — no geometry; FRICTION
  *[mirrored]* entry filed.
- **Kernel (ii-b) consumed assembly (commit 58cfd93).**
  `MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` (`Tower.lean`) — the
  shape (iii) fires: nonzero `Q` with `coeffs ⊆ range (algebraMap ℚ ℝ)` at an `AlgebraicIndependent ℚ`
  seed is `eval`-nonzero. The "coeffs in range ⟹ `Q = map (algebraMap) Q₀`" descent was already in
  mathlib (`mem_range_map_iff_coeffs_subset`, *found by search, not re-mirrored*), so the assembly is
  3 lines over it + the descent pair + leaf (i). Axiom-clean.
- **Kernel (ii-b) rationality leaf + propagation (this commit).** The geometric crux: the
  `complementIso` change-of-basis matrix is rational. Diagonal wedge-pairing value `= ±1` via
  mathlib's `ExteriorAlgebra.ιMulti_family_mul_of_disjoint` (the product of two complementary
  standard basis vectors is a `permOfDisjoint`-signed top basis vector) + `topEquiv_…_default`;
  off-diagonal `0`. The cardinality cast `j+(k+2−j) → k+2` needed a mirror helper
  `ExteriorAlgebra.ιMulti_family_congr` (subst-able `m=n` + `Subtype.ext`; QUIRKS § 36). Propagated
  as `(map (algebraMap ℚ ℝ)).range` membership (GOLF § 14) up `normalsJoinPoly → panelSupportPoly →
  annihRowPoly → c`, then `Rank.lean`'s `Matrix.det_mem_range_of_entries` +
  `exists_polynomial_ne_zero_of_linearIndependent_at_coeffs_subset_range` certify
  `Q.coeffs ⊆ range`. Three mirror entries filed (FRICTION *[mirrored]*). Axiom-clean. Route (b2)
  (post-hoc descent on the ℝ-polynomial) confirmed correct — no device re-typing needed.
- **Kernel sub-phase (ii) recon (commit 7202bfd; design doc §1.32).** The math-first recon at the
  (ii) open: traced what (iii) must compose against the *real* device signatures. **(ii) splits.**
  (ii-a) = a seed-genericity motive conjunct (carry "realizing seed alg-indep over ℚ"; 22b-shaped,
  the anticipated third motive form). (ii-b) = a *rationality bridge* the §1.30 cut missed: leaf (i)
  needs the rank polynomial over **ℚ**, but the device builds `Q : MvPolynomial σ ℝ` (its
  `panelSupportPoly` coefficients are ℝ-typed `complementIso` constants — rational but not
  manifestly so; zero `algebraMap ℚ ℝ` scaffolding tree-wide), so `Q` must be exhibited as an
  `algebraMap ℚ ℝ`-image. Next build = (ii-b)'s upstream-eligible `eval = aeval ∘ descend` mirror.
- **22c left off** at `case_II_placement_eq612` (`CaseI.lean:2331`) = the `≥ D(|V|−1)−1`
  brick; its `e_a=va` link is carried as `_hG_ea`. 22d supplies the `+1`.
