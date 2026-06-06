# Phase 22d — Claim 6.11's first green-machinery prerequisite (the matroid-base 4.3(ii) leaf) (work log)

**Status:** in progress. Opened 2026-06-05 design-pass-first; re-scoped 2026-06-05 to
attack KT Claim 6.11 **bottom-up** (build its leaf-most missing-green prerequisites, not
an axiomatized claim). Gap-2 leaf + Gap-3 combinatorial shell landed green 2026-06-06; the
footnote-6 recon (2026-06-06) settled the analytic kernel's shape; the kernel-route
decision (2026-06-06, user) is to build the algebraic-independence route directly. Recon
detail lives in the design doc (§1.30/§1.31); this note carries the forward plan + a
compressed verdict log.

## Current state

**Gap 1's eq. (6.22) rank *upper* bound at the fixed seed is green this commit**
(`PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`,
`CaseI.lean`, after the seed-rank bridge): given a nonzero *rational* rank polynomial `Q` whose
non-roots witness an independent `panelRow`-subfamily `s` (edges linking in `G`), at any
alg-indep-over-ℚ seed `q` the null space is bounded `dim Z(G,q) ≤ D|α| − |s|`. The footnote-6 non-root
device (`eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`) makes the alg-indep `q` a
non-root, so `s` is independent *at `q` itself*; the rank-nullity core of
`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (panel rows ⊆ rigidity rows,
`dim Z + finrank(span rigidityRows) = D|α|`) then bounds `dim Z`. Built green first try, axiom-clean,
no friction. This is the eq. (6.22) `def>0` *upper* half (the `def=0` full-rigidity transfer is the
prior commit's seed-rank bridge); paired with the genericity-free *lower* bound
`D + def ≤ dim Z` (`rigidityMatrix_prop11`'s `hub`) it pins `dim Z(G_v,q) = D + k'`, i.e.
`RankHypothesis k'`. Blueprint node `lem:case-III-seed-rank-upper` green; `lem:case-III` `\uses` it.

The two **combinatorial** factors of Claim 6.11 remain green + axiom-clean (`ForestSurgery.lean`):
Gap-2 `Graph.splitOff_exists_base_inter_fiber_lt` and Gap-3's shell
`Graph.splitOff_removeVertex_minimalKDof` (`G_v` minimal `k'`-dof, `0 ≤ k' ≤ D−2`). All three analytic
prerequisites (i)/(ii)/(iii) green; the seed-rank bridge + this upper bound are the analytic core of
Gap 1. Blueprint: `lem:case-III-claim-6-11-base`, `lem:case-III-gap3-minimalKDof`,
`lem:case-III-seed-rank-bridge`, `lem:case-III-seed-rank-upper` green; `lem:case-III` /
`lem:case-II-realization` red.

**Next concrete commit:** the **eq. (6.22) `def>0` rank-attainment packaging** — assemble the just-landed
upper bound with `rigidityMatrix_prop11`'s genericity-free lower bound `hub` (`D + def ≤ dim Z`) into
the exact rank `dim Z(G_v,q) = D + k'` (`RankHypothesis (def G̃_v)`) for the nested-IH subgraph `G_v` at
the fixed alg-indep seed. Inputs: the upper bound needs `G_v`'s rational rank polynomial `Q` (from
`G_v`'s minimal-`k'`-dof IH realization via the device producer); the lower bound `hub` is the genericity-free
codimension brick `rigidityMatrix_prop11` carries as a hypothesis (still to be bricked from the
Phase-19 partition machinery — likely lands here or alongside). Then the `k' ≤ D−2 < D−1` pigeonhole
over the `D−1` `ab`-rows (the rest of Gap 1) extracts the redundant row, lifting 22c's
`case_II_placement_eq612` `≥ D(|V|−1)−1` to `= D(|V|−1)`.

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
3. **Gap 1 — the `M(G̃)`↔row bridge** (next leaf). eq. (6.18) `rank R(G_v^{ab},q) = D(|V∖v|−1)`
   is now in hand at the fixed seed (the seed-rank bridge applies directly — `G_v^{ab}` is `0`-dof,
   so rigid); with Gap 3's eq. (6.22), the `k' ≤ D−2 < D−1` corank over the `D−1` `ab`-rows forces
   one redundant (pigeonhole). Step ③ is pure LA *given* (6.18)+(6.22).

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
- [x] **Gap 1 — eq. (6.22) rank *upper* bound** (this commit):
  `PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`
  (`CaseI.lean`) — a rational rank polynomial `Q` witnessing an independent `panelRow`-subfamily `s`
  bounds `dim Z(G,q) ≤ D|α| − |s|` at any alg-indep-over-ℚ `q`. Green + axiom-clean. Node
  `lem:case-III-seed-rank-upper`; `lem:case-III` `\uses` it.
- [ ] **Gap 1 — eq. (6.22) rank-attainment + pigeonhole** (next leaf): assemble the upper bound with
  `rigidityMatrix_prop11`'s genericity-free lower bound `hub` (`D + def ≤ dim Z`) into the exact
  `RankHypothesis (def G̃_v)` for `G_v` at the fixed seed (needs `G_v`'s rational rank polynomial from
  its minimal-`k'`-dof IH; `hub` still to be bricked from Phase-19 partition machinery), then the
  `k' ≤ D−2 < D−1` pigeonhole over the `D−1` `ab`-rows ⟹ one redundant row (eq. (6.23)). Then lift
  22c's `case_II_placement_eq612` `≥ D(|V|−1)−1` to `= D(|V|−1)`.

## Deferred sub-phases (future work in the phase)

Parked until the leaf's shape is clear; a sub-letter is minted when its turn comes.

- **Gap 1 — eq. (6.22) rank-attainment + the `M(G̃)`↔row pigeonhole** (next leaf, see *Hand-off*).
  The analytic core is green (seed-rank bridge `lem:case-III-seed-rank-bridge` = `def=0` transfer +
  `lem:case-III-seed-rank-upper` = `def>0` upper bound, both ✓; leaves (i)/(ii-a)/(ii-b) all green).
  Remaining: assemble the upper bound with `rigidityMatrix_prop11`'s `hub` lower bound into the exact
  `RankHypothesis (def G̃_v)` for `G_v`, then the `k' ≤ D−2 < D−1` pigeonhole over the `D−1` `ab`-rows
  ⟹ one redundant row (eq. (6.23)). The product-route *relaxation* (pick `q` as a non-root of the
  finite product of the nested IH rank polynomials, avoiding alg-independence at `d=3`; ~70%
  confidence) is the deferred TODO in the tracker `notes/AlgebraicIndependence.md`.
- **Candidate-completion + Claim 6.12 disjunction.** With the redundant `ab`-row, lift
  22c's `case_II_placement_eq612` `≥ D(|V|−1)−1` to `= D(|V|−1)` on one candidate (eq.
  (6.24)–(6.29) row-op), then the Claim-6.12 extensor-span contradiction via the **green**
  Lemma 2.1 (`omitTwoExtensor_linearIndependent`) + the eq. (6.44) degree-2 forcing picks
  the full-rank candidate. Claim 6.12 **de-risked** (Lemma 2.1 green). Candidate normal
  form: **abstract one per-candidate lemma, instantiate ×3** (`p₂=p₁` with `a↔b`;
  `p₃=p₁∘ρ`); `case_II_placement_eq612` is already this shape (22c recon, design doc §1.26).
- **The `d=3` assembly** — `prop:rigidity-matrix-prop11` `hub` brick + `thm:theorem-55`
  flip + wiring the green `case_I_realization`. Unlettered.
- **General `d`** (Lemma 6.13) → Thm 5.5 → Thm 5.6 → Conjecture 1.2 — Phase 23.

## Blockers / open questions

- **Do the Gap-3 kernel and Gap-1 row bridge merge into one node? — mostly resolved.** The
  rigidity-transfer core is now TWO green nodes serving both: the seed-rank bridge (`def=0`, eq.
  (6.18) is its direct application) and the upper bound `lem:case-III-seed-rank-upper` (the `def>0`
  half of eq. (6.22)). What stays separate is the rank-*attainment* assembly (the upper bound + the
  genericity-free lower bound `hub` of `rigidityMatrix_prop11`, giving `RankHypothesis (def G̃_v)`)
  and the pigeonhole; these are the next leaf. The `hub` brick (codimension lower bound from the
  Phase-19 partition machinery) is the one piece `rigidityMatrix_prop11` still carries as a hypothesis.
- **Claim 6.12 — de-risked** (bottoms on the green Lemma 2.1).
- **Recurring Lean traps** (carry from 22a–c, FRICTION): heavy `IsInfinitesimallyRigidOn`
  defeq across `ofNormals`/`withGraph` graph-swaps can `isDefEq`-timeout — make the two
  frameworks *syntactically* equal before `convert`; transfer rigidity via a
  `mem_infinitesimalMotions` round-trip. (Bites once Gap 1 lands, not the matroid-only shell.)

## Hand-off / next phase

**Next concrete commit:** **Gap 1 — the eq. (6.22) `def>0` rank-attainment packaging.** The two
analytic halves are green (the `def=0` seed-rank bridge transfers full rigidity; the `def>0` upper
bound `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent` bounds `dim Z ≤ D|α| −
|s|` at the fixed alg-indep seed). The remaining content: assemble the upper bound with
`rigidityMatrix_prop11`'s genericity-free lower bound `hub` (`D + def ≤ dim Z`) into the exact
`RankHypothesis (def G̃_v)` for the nested-IH subgraph `G_v` at the fixed seed. The upper bound's input
is `G_v`'s rational rank polynomial — obtained by running the device producer on `G_v`'s
minimal-`k'`-dof IH realization; `hub` is the codimension lower bound `rigidityMatrix_prop11` still
carries as a hypothesis, to be bricked from the Phase-19 partition machinery (likely lands here). Then
the `k' ≤ D−2 < D−1` pigeonhole over the `D−1` `ab`-rows ⟹ one redundant row (eq. (6.23)), lifting
22c's `case_II_placement_eq612` `≥ D(|V|−1)−1` to `= D(|V|−1)`. All three analytic prerequisites
(i)/(ii)/(iii) and both combinatorial factors (Gap-2/Gap-3) are green; `lem:case-III` stays red until
the candidate-completion assembly lands.

After Gap 1: the candidate-completion + Claim-6.12 disjunction, the `d=3` assembly, and
general-`d` (Phase 23).

KT math: KT §6.4.1 (Lemma 6.10, Claims 6.11/6.12, eqs. (6.22)–(6.45)), §4 (Lemmas
4.3(ii)/4.4/4.7/4.8). Recon detail: design doc §1.30 (footnote-6 kernel) + §1.31
(kernel-route) + §1.26 (candidate structure); also `notes/Phase20.md`
(`splitOff_isMinimalKDof`), `notes/Phase21b.md` *Finding A/B*, `notes/Phase22c.md`,
`notes/AlgebraicIndependence.md` (the alg-independence tracker).

## Decisions & recon log (compressed)

The finished-work tail — one-line verdicts; the blow-by-blow is in the cited commits /
design-doc arcs (per `notes/CLAUDE.md` *Forward-weighted note*).

- **Gap-1 eq. (6.22) rank *upper* bound landed (this commit).** `lem:case-III-seed-rank-upper` =
  `PanelHingeFramework.finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`
  (`CaseI.lean`, after the seed-rank bridge): a nonzero *rational* rank polynomial `Q` witnessing an
  independent `panelRow`-subfamily `s` (edges linking in `G`) bounds `dim Z(G,q) ≤ D|α| − |s|` at any
  alg-indep-over-ℚ `q`. The footnote-6 non-root device makes `q` a non-root (so `s` is LI at `q`); the
  rank-nullity core of `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (panel rows ⊆
  rigidity rows; `dim Z + finrank(span rigidityRows) = D|α|`) bounds `dim Z`. Green first try,
  axiom-clean, no friction; honest (the input is `Q`, an unrelated rigid seed's rank witness, not the
  rank concluded). The `def>0` upper half of eq. (6.22); pairs with `rigidityMatrix_prop11`'s `hub`
  lower bound for the exact `RankHypothesis k'`. One statement wrinkle: `Fintype.card α` in a
  `[Finite α]` statement needs `Nat.card α` + `rw [Nat.card_eq_fintype_card]` (standard project idiom).
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
