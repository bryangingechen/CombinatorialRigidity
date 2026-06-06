# Phase 22d — KT Claim 6.11 (the redundant `ab`-row) + its green-machinery prerequisites (work log)

**Status:** ✓ Complete (archived). Opened 2026-06-05 design-pass-first; re-scoped 2026-06-05
(user) to attack KT Claim 6.11 **bottom-up** — build its leaf-most missing-green prerequisites,
not an axiomatized claim. Closed at the **Claim 6.11 / eq. (6.23) milestone**: the redundant
`ab`-row of `R(G_v^{ab}, q)` (`lem:case-III-claim-6-11`) and its full prerequisite chain are
green + axiom-clean. ROADMAP §22d carries the one-paragraph summary; the dep-graph chapter
`algebraic-induction/case-iii.tex` (`sec:molecular-algebraic-induction-caseIII`) is the lemma
index.

## Hand-off / next sub-phase (UNLETTERED until opened): the candidate-completion + Claim 6.12

With Claim 6.11 green, the successor lifts 22c's stratum-1 `D(|V|−1)−1` brick
(`case_II_placement_eq612`) to full `D(|V|−1)`:

- **The open crux — the row-op construction of `w` (KT p. 680, eq. (6.24)→(6.27)).** Lift the
  redundant `ab`-row's combination (`exists_redundant_panelRow_ab_of_finrank_eq`, green) to
  `R(G,p₁)` via `R(G,p₁;E∖{vb},V∖{v}) = R(G_v^{ab},q)`, producing `w ∈ span(R(G,p₁)-rows)`
  vanishing off `v`. The eq. (6.18)/(6.22) finrank hypotheses of
  `exists_redundant_panelRow_ab_of_finrank_eq` are wired from the green seed-rank-bridge /
  rank-attainment via rank-nullity `dim Z + dim span(rigidityRows) = D|α|`.
- **First leaf already landed (commit e8e7753), fold it in:** the column-support LA core
  `BodyHingeFramework.dualMap_eq_comp_single_proj_of_vanish_off` (`RigidityMatrix.lean`, eq.
  (6.28)) — a rigidity row vanishing on every screw assignment supported off `v` is a pure
  `v`-column row `(f ∘ₗ single v) ∘ₗ proj v`. It turns the row-op output `w` (whose `V∖{v}` part
  is zero) into a `v`-column row that joins the `va`-block in `linearIndependent_sum_pinned_block`'s
  `D`-row-capable pin-a-body split.
- **Then the conditional rank lift + Claim 6.12.** `w` extends the `va`-block to a `D`-row new
  block ⟹ `D(|V|−1)`-family **conditional** on the top-left `D×D` block being full rank (eq.
  (6.29)), discharged by the Claim-6.12 `D`-candidate disjunction (extensor-span contradiction via
  the green Phase-17 Lemma 2.1; the degree-2 eq. (6.44) forces all candidates to test the same `r`).

`lem:case-III` / `lem:case-II-realization` stay red until the candidate-completion assembly lands.
The `d=3` assembly (`prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55` flip + the Case-I
wiring) and general-`d` (Lemma 6.13, Phase 23) are further deferred cuts. KT math: KT §6.4.1
(Lemma 6.10, Claims 6.11/6.12, eqs. (6.22)–(6.45)); `notes/AlgebraicIndependence.md` (the
alg-independence tracker, risk #8); `notes/Phase21b.md` *Finding A/B*; `notes/Phase22c.md`.

**Recurring Lean trap (carry from 22a–c, FRICTION):** heavy `IsInfinitesimallyRigidOn` defeq across
`ofNormals`/`withGraph` graph-swaps can `isDefEq`-timeout — make the two frameworks *syntactically*
equal before `convert`; transfer rigidity via a `mem_infinitesimalMotions` round-trip. (Bites in the
candidate-completion assembly.)

## Claim 6.11 discharge — the Gap 2 → 3 → 1 map (the durable account)

Claim 6.11 (KT p. 684, eq. (6.23)): `R(G_v^{ab}, q)` has a redundant row among its `D−1` `ab`-rows —
the `+1` that lifts 22c's stratum-1 `D(|V|−1)−1` brick toward full `D(|V|−1)`. KT's proof factors,
in dependency order (all three green + axiom-clean at close):

1. **Gap 2 — matroid-base 4.3(ii) at `k=0`** (`splitOff_exists_base_inter_fiber_lt`,
   `lem:case-III-claim-6-11-base`): a base `B'` of `M(G̃_v^{ab})` with `h := |ãb ∩ B'| < D−1`. Pure
   combinatorial `M(G̃)`; reroute a balanced `D`-forest packing across `v` (`forest_surgery_count`
   strengthened with the `< D−1` conjunct = KT 4.1's two conclusions), `def=0` ⟹ a full-rank
   independent set is a base.
2. **Gap 3 — the nested IH-at-restriction** (`splitOff_removeVertex_minimalKDof`,
   `lem:case-III-gap3-minimalKDof`): `G_v := G−v = G_v^{ab}−ab` is minimal `k'`-dof with
   `0 ≤ k' = def(G̃_v) ≤ D−2`. Minimality via `subgraph_minimality` (`G_v ≤ G`); bound via the Gap-2
   base (`B'∖ãb` indep in `M(G̃_v) = M(G̃_v^{ab})↾E(G̃_v)`, `rank ≥ |B'|−h`, def=corank). The
   *analytic* half it feeds — applying the geometric IH to `G_v` at the fixed seed (eq. (6.22)) — is
   the seed-rank kernel below.
3. **Gap 1 — the `M(G̃)`↔row bridge** (eq. (6.23)): eq. (6.18) `rank R(G_v^{ab},q) = D(m−1)` at the
   fixed seed (`G_v^{ab}` is `0`-dof, hence rigid) + Gap-3's eq. (6.22) `= D(m−1) − k'` give a
   `k' ≤ D−2 < D−1` corank over the `D−1` `ab`-rows ⟹ one redundant (pigeonhole). The row-set
   identity `span_rigidityRows_eq_sup_span_panelRow_edge` instantiates the abstract pigeonhole leaf
   at the specific graphs `G_v^{ab}` / `G_v` (they differ by exactly the `ab`-edge), and
   `exists_redundant_panelRow_ab_of_finrank_eq` (`lem:case-III-claim-6-11`) feeds the two finrank
   equations through it (the honest "(6.18) ∧ (6.22) ⟹ (6.23)" step).

The **analytic seed-rank kernel** (Gaps 3+1's shared content, KT footnote 6) is the project's first
algebraic-independence use: *one nonparallel realization attaining the rank ⟹ the inductively-fixed
alg-indep-over-ℚ seed attains it too* — a rank-of-a-given-seed statement, the opposite direction from
the 21b genericity device. It bottoms on a rational rank polynomial `Q` (coefficients in
`range(ℚ→ℝ)` via the `complementIso` change-of-basis being `±1`-valued) being nonzero at every
alg-indep seed (`AlgebraicIndependent.aeval_ne_zero`, footnote-6 leaf). The `def=0` rigidity form
(`lem:case-III-seed-rank-bridge`), the `def>0` upper bound (`-seed-rank-upper`), and the exact-rank
packaging (`-rank-attainment`, pairing the upper bound with the green `hub` lower bound `D+def ≤ dim Z`)
all landed green.

## Lemma checklist (all green + axiom-clean)

- [x] `Graph.forest_surgery_count` — strengthened with the `|ãb ∩ ⋃ Fs'i| < D−1` conjunct (KT 4.1's
  second conclusion).
- [x] `Graph.splitOff_exists_base_inter_fiber_lt` — Gap-2 leaf. `lem:case-III-claim-6-11-base`.
- [x] `Graph.splitOff_removeVertex_minimalKDof` — Gap-3 combinatorial shell. `lem:case-III-gap3-minimalKDof`.
- [x] `AlgebraicIndependent.aeval_ne_zero` — footnote-6 leaf (i), mirror.
- [x] `MvPolynomial.eval_map_algebraMap` / `map_algebraMap_ne_zero_iff` + the consumed assembly
  `eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent` — descent bridge (ii-b), mirror.
- [x] `complementIso` rationality leaf + propagation (`wedgePairing_ιMulti_family_mem_range_intCast`
  → `complementIso_exteriorPower_repr_mem_range_*` → `{normalsJoin,panelSupport,annihRow}Poly_mem_range_map`)
  — the geometric crux that makes the device's `Q` rational. Wired into the three rank-poly producers.
- [x] `exists_injective_algebraicIndependent_real` — the alg-indep-over-ℚ seed, mirror (the moment
  curve is NOT alg-indep; alg-independence ≠ general position). Motive-conjunct wiring on
  `HasGenericFullRankRealization`.
- [x] `isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent` — (iii) seed-rank bridge,
  `def=0`. `lem:case-III-seed-rank-bridge`.
- [x] `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent` — eq. (6.22) upper
  bound. `lem:case-III-seed-rank-upper`.
- [x] `rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent` — eq. (6.22) rank attainment.
  `lem:case-III-rank-attainment`.
- [x] the full `hub`: `partitionMotions` + `partitionConstant` `W_f` count + the dimension lower
  bound `screwDim_mul_numParts_sub_le_finrank_partitionMotions` (rank-nullity on the **full Pi** map,
  QUIRKS § 39) + `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (`D+def ≤ dim Z`,
  discharged into `rigidityMatrix_prop11` + the rank-attainment packaging). Carried by
  `lem:trivial-motions-rank-bound`.
- [x] `Submodule.exists_mem_sup_span_image_compl_of_finrank_lt` (+ `Submodule.finrank_map_mkQ`) —
  abstract pigeonhole leaf, mirror.
- [x] `exists_redundant_panelRow_of_edge_of_finrank_lt` — the per-edge geometric instantiation.
  `lem:case-III-claim-6-11-redundant-row`.
- [x] `span_rigidityRows_eq_sup_span_panelRow_edge` — the row-set identity (no blueprint node).
- [x] `exists_redundant_panelRow_ab_of_finrank_eq` — the corank-gap discharge. **`lem:case-III-claim-6-11`** (the eq.-(6.23) milestone).
- [x] `dualMap_eq_comp_single_proj_of_vanish_off` — candidate-completion eq. (6.28) column-support
  core (landed early under 22d's tail, commit e8e7753; belongs to the successor's work).

## Decisions made during this phase (compressed verdict record)

The blow-by-blow is in the cited commits / `case-iii.tex` proofs / `notes/AlgebraicIndependence.md`.

### Phase-local choices and proof techniques
- **Re-scope (2026-06-05, user).** Overrode the opening "axiomatize Claim 6.11" verdict (commit
  4e6a7bb): build the leaf-most missing prerequisite bottom-up rather than deferring onto Claim 6.12.
- **Gap 2 (13d2464).** Strengthen `forest_surgery_count` with `< D−1`; `k=0` base assembly. KT 4.3(ii)
  is an *existence* statement (a base with `<D−1`), not "every base".
- **Gap 3 (d218fa0).** Minimality via `subgraph_minimality`; bound via the Gap-2 base + def=corank.
  Did not need `removeVertex_deficiency_ge` (the splitting-off side carries the count).
- **Footnote-6 kernel recon (892f44c).** eq. (6.22) is NOT a re-exposure of 21b/22b machinery; the
  motive is existence-only, so the missing brick is `non-root-from-algebraic-independence`. Route
  decision (3f0ea8e): build the alg-independence route directly to green; product-route relaxation
  deferred (`notes/AlgebraicIndependence.md`).
- **Kernel (ii-b) rationality (d4e0840 + propagation).** The `complementIso` matrix is rational
  (diagonal wedge-pairing `= ±1` via `ιMulti_family_mul_of_disjoint`, off-diagonal `0`), so the
  device's `Q` has rational coefficients; route-(b2) post-hoc descent on the ℝ-polynomial, no device
  re-typing. (ii-a): the moment curve is not alg-indep; substitute a transcendental seed.
- **Gap-1 discharge (fc2ea7b).** Row-set identity + the eq.-(6.18)/(6.22)⟹(6.23) discharge close the
  Gap-1 chain; node `lem:case-III-claim-6-11`. The two finrank equations enter as hypotheses (honest).
- **`hub` lower bound (a413308 + bfafb7f).** Rank-nullity on the full Pi map + `finrank_sup_add_finrank_inf_eq`
  (NOT the `W_f`-restricted map — heavy-carrier instance-diamond timeout); maximize the `def`-attaining
  partition into `D+def ≤ dim Z` and discharge both consumers.

### Promoted to TACTICS-QUIRKS / FRICTION / DESIGN
- *Heavy-carrier `W_f`-restricted rank-nullity `whnf`-timeout → run on the full Pi map* → QUIRKS § 39.
- *Extract a generic helper to dodge the heavy-dual `whnf`* → QUIRKS § 38; *three-way omega cast/product/truncation* → QUIRKS § 2; *cardinality-cast `ιMulti_family_congr`* → QUIRKS § 36; *cross-universe embedding via `Cardinal.lift_mk_le'`* → QUIRKS § 37.
- *`(map (algebraMap ℚ ℝ)).range` membership propagation* → GOLF § 14.
- Several mirror lemmas (alg-independence, descent, pigeonhole, rationality) → FRICTION *[mirrored]*.
- *Algebraic-independence relaxation question + usage tracker* → `notes/MolecularConjecture.md` risk #8 + `notes/AlgebraicIndependence.md` (the single source for the relaxation question + every site).
- *Where the Claim-6.11 difficulty sits (Gap-2→3→1, footnote-6 kernel)* → `notes/BlueprintExposition.md` (`lem:case-III-claim-6-11`, exposition written into `case-iii.tex` at this close).
