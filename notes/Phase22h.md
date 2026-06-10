# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge) and §1.49 (G5, G4a–G4e, G0, the (β) branch shape) — point at them, don't duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**G5 is DONE.** `IsProperRigidSubgraph` requires `2 ≤ V(H).ncard`; `loopless_of_isMinimalKDof`
brick shared with G0. Done.

**G4b-impl is DONE.** `minimal_kdof_reduction_full` + `theorem_55_generic` (β) restate. Done.

**G4a-i + G0 are DONE (single commit).** `simple_of_isMinimalKDof_of_noRigid` (ReducibleVertex.lean:
loopless + no parallel pair; `isKDof_zero_of_parallel_pair` from Deficiency.lean as the K₂ brick)
and `exists_adjacent_degree_two_pair` (ReducibleVertex.lean: the `D ≥ 6` double-count via
`incFun`/`Finset.sum_comm`, KT Lemma 4.6 at `d = 3`). Blueprint nodes `lem:two-vertex-zero-dof`,
`lem:simple-minimal-noRigid`, `lem:adjacent-degree-two-pair` added; build green, lint + verify.sh
clean.

**G4a-ii is DONE.** `exists_chain_data_of_noRigid` (ForestSurgery.lean; blueprint node
`lem:chain-data-of-noRigid` added; build + lint + verify.sh clean). 4-way case split on which of
the two splitOff-data pairs at v and a contains eₐ; `same_right` helper for endpoint uniqueness;
`triangle_isProperRigidSubgraph + hnp` for `b ≠ c`.

**T1 is DONE.** `exists_isLink_of_isMinimalKDof_card_three` (Operations.lean; blueprint node
`lem:triangle-third-edge` added; build + lint + verify.sh clean). Vertex pin via `ncard = 3`;
edge count via `rank_matroidMG_of_isKDof_zero` + `edgeMultiply_edgeSet_ncard` + ℤ cast;
case split on endpoint membership eliminates all non-`a–b` cases via `unique_edge`.

**T2 is DONE.** `theorem_55_triangle` (Pinning.lean; blueprint node `lem:theorem-55-triangle` in
panel-layer.tex; build + lint + verify.sh clean). Three-body cycle argument: each hinge constraint
puts `S u − S v`, `S v − S w`, `S w − S u` in the matching span; they sum to 0;
`eq_zero_of_mem_span_singleton_of_sum_eq_zero` forces each to 0; 9-case dispatch closes the
`IsInfinitesimallyRigidOn {u,v,w}` goal.

**T3 is DONE.** `exists_triangle_normals` (PanelLayer.lean; blueprint node `lem:triangle-normals`
added; build + lint + verify.sh clean). Witness: `e₀, e₁, e₂ ∈ ℝ^(k+2)`. Pairwise nonvanishing via
`normalsJoin_basisFun_ne_zero_of_lt`; extensor LI via `units_smul` decomposition + `ιMulti_family`
basis LI + 3-index injection.

**T4 is DONE.** `hasGenericFullRankRealization_of_triangle` (CaseI.lean; blueprint node
`lem:triangle-realization` added to case-iii.tex; build + lint + verify.sh clean). Seed `q₀`
assigns `v↦n₀, a↦n₁, b↦n₂`; each triangle-edge extensor is ±Cᵢ from T3's cyclic LI family
(unit scalar from `endsOf` orientation via `endsOf_eq_or_swap`); T2 closes rigidity on `{v,a,b}`;
`hasGenericFullRankRealization_of_rigidOn_ofNormals` upgrades to generic motive.

**G4c-i is DONE.** `splitOff_isLink_relabel` (Operations.lean; blueprint node
`lem:splitOff-isLink-relabel` added to case-iii.tex; build + lint + verify.sh clean). The
`ρ = (a v)` vertex-transposition iff between `splitOff a v c e₁` and `splitOff v a b e₀`; proved
by case analysis using degree-2 closures at `v` and `a`. Key derived facts: `hba : b ≠ a`
(from `hcla` + `heab` + `he_b_ne_e_c`); after `subst he_eq_eb` in the backward fresh-edge case,
`e_b` is replaced by `e` in context.

**G4c-ii is DONE.** `hasGenericFullRankRealization_of_splitOff_relabel` (CaseI.lean; blueprint
node `lem:splitOff-ofNormals-relabel` added to case-iii.tex; build warning-clean). The
`ofNormals` framework transport: GP via `ρ.injective.ne`; rigidity via `S ∘ ρ` pull-back using
`splitOff_isLink_relabel` forward + `hρρ` double-application; link-recording via `splitOff_isLink_relabel`
backward + `hρρ` roundtrip; alg-indep via `AlgebraicIndependent.comp` + injective reindex. Key
tricks: `set Q'` to avoid `.toBodyHinge\n.supportExtensor` parse error; `change` to expose
`ofNormals` form for `simp only` (bypasses `let`-binding opacity); `Equiv.Perm.inv_def` +
`Equiv.symm_apply_apply` to reduce `σ⁻¹ (σ f)`; `simp only [Equiv.Perm.inv_def] at h1 h2`
to normalize before `rw [h1]` in link-recording.

**Next concrete step: G4d-i** (§1.49(4)), the eq.(6.43)→(6.44) `a`-column identity.

**Build order (design §1.49(6); estimated 11–16 commits remaining):** G4b-impl ✓ → in parallel:
{G4a-i/ii + G0 ∥ T1–T4 ∥ G4c-i/ii} → G4d-i/ii → the (β)-shaped `hsplit` producer (the §38-trap
concrete-seed assembly with the G4e `M₁/M₂/M₃` dispatch) → Leaf 4 → Leaf 5.

## Lemma checklist

- [x] **G5** — the `IsProperRigidSubgraph` predicate repair (`2 ≤ V(H).ncard`) + producer-site
  re-proofs (incl. the uncensused `splitOff_isMinimalKDof` site, which gained `hV3`) +
  `loopless_of_isMinimalKDof` brick + blueprint `def:rigid-subgraph` sync (§1.49(0)). Done.
- [x] **G4b-impl** — `minimal_kdof_reduction_full` (ForestSurgery.lean, full-IH strong induction)
  + `theorem_55_generic` (β) restate (PanelHinge.lean; `hsplit`/`hsplitGP` → full conditioned IH
  shape, dropping per-vertex data and `hD`/`hfresh`). Done.
- [x] **G4a-i + G0** — `exists_adjacent_degree_two_pair` (the `D ≥ 6` double-count) +
  `simple_of_isMinimalKDof_of_noRigid` (loopless + no parallel pair; `isKDof_zero_of_parallel_pair`
  K₂ brick). Blueprint nodes added (`lem:two-vertex-zero-dof`, `lem:simple-minimal-noRigid`,
  `lem:adjacent-degree-two-pair`). Done.
- [x] **G4a-ii** — `exists_chain_data_of_noRigid` (§1.49(2)): `exists_splitOff_data_of_degree_eq_two`
  at `v` and `a`, `b ≠ c` via `triangle_isProperRigidSubgraph` + `hnp` at `|V| ≥ 4`. Done.
- [x] **T1** — `exists_isLink_of_isMinimalKDof_card_three` (Operations.lean): vertex pin +
  third-edge existence via edge-count lower bound. Blueprint node `lem:triangle-third-edge`. Done.
- [x] **T2** — `theorem_55_triangle` (Pinning.lean; blueprint `lem:theorem-55-triangle`). Done.
- [x] **T3** — `exists_triangle_normals` (PanelLayer.lean; blueprint node `lem:triangle-normals`).
  Done.
- [x] **T4** — `hasGenericFullRankRealization_of_triangle` (CaseI.lean; blueprint node
  `lem:triangle-realization`; §1.48(1)). Done.
- [x] **G4c-i** — `splitOff_isLink_relabel` (Operations.lean; blueprint node
  `lem:splitOff-isLink-relabel`; §1.49(3) graph side). Done.
- [x] **G4c-ii** — `hasGenericFullRankRealization_of_splitOff_relabel` (CaseI.lean; blueprint
  node `lem:splitOff-ofNormals-relabel`; §1.49(3) framework side). Done.
- [ ] **G4d-i/ii** — the (6.43)→(6.44) `a`-column identity + the `M₃` `hcand_mem` (§1.49(4)).
- [ ] **The (β)-shaped `hsplit` producer** (the G4e spine; the §38 trap; §1.49(5)): G4a chain
  dichotomy → `|V|=3 ↦ T4`; chain arm: its own split data + `splitOff_isMinimalKDof` + measure ⟹
  IH at the `v`-split; R3 ⟹ the GP `.1` conjunct ⟹ `q` + `hgab` (via
  `hasGenericRealization_transport_ends`) + the triple-LI-from-alg-indep bridge (§1.48(2));
  GAP-3 good-`t`; the G4e `M₁/M₂/M₃` dispatch (`M₃` via G4c/G4d); compose the GAP-2 upgrade
  `hasGenericFullRankRealization_of_rigidOn_ofNormals` onto the bare candidate, supplying its
  `hne` from the candidate completion.
- [ ] **Leaf 4** — the `theorem_55_generic (n:=2) (k:=2)` instance node over the (β) shape,
  projecting `.2` (R2 verdict (B), §1.41); the `hcontractGP` wiring gains `hVH2` from G5. A small
  green blueprint node, not a standalone `theorem_55_dim3`.
- [ ] **Leaf 5** — the `lem:case-II-realization` / `lem:case-III` flips + the Thm 5.5→5.6 push
  feeding `rigidityMatrix_prop11`'s `hgen`; unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **GAP 3 (bounded, folded into the producer):** `hnewtrans : LinearIndependent ![n_a + t•n', n_b]`
  — the bad-`t` set is ≤ 1 value (the affine line `t ↦ n_a + t•n'` meets `span{n_b}` at most once,
  from `hgab`), so a good `t ≠ 0` exists. `Fin(k+2)→ℝ` linear algebra.
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites every
  carrier-instantiating leaf (the producer body, the T3/T4 seeds). Keep reasoning over abstract
  `F`; instantiate only at the seed.
## Hand-off / next phase

**Smallest next forward commit — G4d-i** (§1.49(4)): the eq.(6.43)→(6.44) `a`-column identity
(`candidateRow_ac_eq_neg` in BodyHingeFramework; consumes `exists_redundant_panelRow_ab_decomposition_acolumn_zero` and
`hingeRow_comp_single_tail`/`hingeRow_comp_single_off`; blueprint node `lem:case-III-claim612-eq644` already green).
After G4d-i, G4d-ii (the `M₃` `hcand_mem`), then the (β)-shaped `hsplit` producer (G4e spine).
After 22h closes (the molecular conjecture at `d=3`, Cor 5.7 unblocked → Phases 24–26):
**Phase 23** = general `d` (KT Lemma 6.13), scoped with the §1.33 (C) reuse map; open it
with its own recon (KT eqs. (6.46)–(6.67) vs the `d=3` Lean) and add the general-`d`
alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

- **G4b-impl (β) interface:** `minimal_kdof_reduction_full` adds `classical` to the proof body
  (for `by_cases` on the prop-valued `∃ H, IsProperRigidSubgraph G n`); `[DecidableEq β]` must
  remain in the signature because `IsMinimalKDof` bakes it in. `theorem_55` (bare reduction)
  is untouched. The `theorem_55_generic` `hsplit`/`hsplitGP` no longer carry split-vertex data or
  `hD`/`hfresh` — those are internalized by the future producer (G4e). `[Finite β]` was also
  dropped from `theorem_55_generic` (the old version called `minimal_kdof_reduction` which needed
  it; the new version calls only `minimal_kdof_reduction_full` which doesn't). The `hsplit`
  wiring lambda in the new proof projects `.2` (bare) from the full IH, mirroring `hcontract`.
- **Model-tier dispatch experiment running on this phase** —
  coordinator sessions rate each dispatch and pick the subagent model
  rung per `notes/model-experiment-protocol.md`, logging to
  `notes/model-experiment.md` (the repo-local config + log).
- **G5 census correction (one site beyond §1.49(0)):** `splitOff_isMinimalKDof`'s KT-4.7 step
  offers `Gv = G.removeVertex v` to `hnp`, needing `2 ≤ |V(Gv)|` — so the lemma gained
  `hV3 : 3 ≤ V(G).ncard`. Not a formality: at `|V(G)|=2` (double edge, hnp now satisfiable) the
  splitOff is a one-vertex loop graph whose empty base misses the fresh fiber, so the old
  statement is *false* under the corrected predicate. Lesson reinforces §1.49(0)'s: census
  `hnp`-*applications*, not just `exact hnp …` greps — `refine hnp Gv ⟨…⟩` was the missed shape.
- **Loopless route over minimality-hypothesis route for the circuit sites:** the two circuit-site
  lemmas take `[G.Loopless]` (derived by callers via `loopless_of_isMinimalKDof`) rather than a
  full `IsMinimalKDof` hypothesis — (4.10) and the fundCircuit spanning step need only
  looplessness, keeping the statements at their honest strength.
- **G0 parallel-pair brick:** G0 constructs `H = (G.induce {x,y}).restrict {e,f}` (not
  `G.induce {x,y}` directly, which would require G simple) so `E(H) = {e,f}` is literal, and
  `isKDof_zero_of_parallel_pair` applies. The `restrict_le + induce_le` chain gives `H ≤ G`.
- **G4a-i incFun double-count:** `Finset.sum_comm` swaps Σ_v Σ_e to Σ_e Σ_v; per-edge the X₂
  endpoint count is ≤ 1 (any X₂–X₂ adjacency would be the pair we want, contradicting `hno'`),
  proved via `Finset.sum_le_one_iff` + `IsLink.eq_and_eq_or_eq_and_eq` for the case-split; then
  `Finset.single_le_sum` carries `1 ≤ Σ_{X₃₊} incFun e`. The numeric finale needs `zify` +
  `nlinarith` to combine the two lower bounds with the edge bound and `D ≥ 6`.
- **G4a-ii endpoint disambiguation:** `same_right` local helper extracts unique right endpoint
  from two same-edge same-left-endpoint IsLink facts (via `eq_and_eq_or_eq_and_eq`; second case
  is the loop case, killed by the `y ≠ x` hypothesis). The 4-way `(g₁/g₂ = eₐ) × (f₁/f₂ = eₐ)`
  case split avoids `subst` on shared names; closures are reindexed via `Or.imp_left` +
  `Eq.trans` + `.symm` rather than `▸` rewrites in term position.
- **T3 proof decomposition (`exists_triangle_normals`):** extracted 4 private helpers to avoid
  `whnf`-context explosion: `normalsJoin_basisFun_ne_zero_of_lt`, `normalsJoin_eq_ιMulti_family_pair`,
  `basisFun3_normalsJoin_cyclic_eq_units_smul`, `basisFun3_normalsJoin_sorted_family`. The last uses
  `let`-bound `h01/h12/h02` in the statement (not explicit args) so that after `intro`, the proof
  terms in the goal match `Finset.card_pair (Fin.ne_of_lt hXX)` exactly, enabling direct `exact`
  application. Proof-term mismatch pattern → TACTICS-QUIRKS § 42.
- **G4c-i `subst` naming caveat:** `subst he_eq_eb` (where `he_eq_eb : e = e_b`) replaces `e_b`
  with `e` in the context — after that, writing `e_b` in a tactic gives "unknown identifier". Use
  `e` in the backward fresh-edge branch. Also: `hba : b ≠ a` must be derived explicitly (from
  `hcla e_b v (hba' ▸ hG_eb.symm)` + `heab.symm` + `he_b_ne_e_c`); it is not a direct hypothesis.
  The `hσe_ne_ec` short proof: `σ e = e_c` and `σ e₁ = e_c` → `e = e₁` by injectivity, contradicts
  `he₁e`. Similarly `he_ne_ec`/`he_ne_e₀` use explicit `calc` chains over `swap_apply_right` +
  `swap_apply_of_ne_of_ne` to avoid `simp_all` whnf timeouts.
- **G4c-ii `let`-opacity and `.toBodyHinge\n.field` parse hazards:** `set Q'` avoids the
  `.toBodyHinge\n.supportExtensor` newline-parse bug (line 2 is parsed as argument, not field).
  `change (ofNormals ...).toBodyHinge.supportExtensor _ = _` exposes the `ofNormals` form so
  `simp only` can unfold `ofNormals_ends`/`ofNormals_normal` (plain `set`-bound `Q'` is opaque to
  `simp only`). `Equiv.Perm.inv_def` rewrites `σ⁻¹` to `Equiv.symm σ`; then `Equiv.symm_apply_apply`
  reduces `σ.symm (σ f) = f` (the `HInv` form blocks `Equiv.symm_apply_apply` directly). Link-recording:
  `simp only [Equiv.Perm.inv_def] at h1 h2` normalizes `h1`/`h2` to the `.symm` form before
  `rw [h1]` finds its pattern. Promoted to TACTICS-QUIRKS (§ 35 extension or new entry for the
  `let`-opacity/`change`-before-simp pattern). → See also FRICTION.md [let-opacity].
- **T4 sign-flip dispatch (`hasGenericFullRankRealization_of_triangle`):** each triangle-edge
  extensor equals ±Cᵢ via `endsOf_eq_or_swap` (2 cases × 3 edges = 8-way `rcases` dispatch).
  The `hLI_neg` helper builds LI for `![ε₀•C₀, ε₁•C₁, ε₂•C₂]` via `units_smul_iff` + the
  `Pi.smul` form (`![ε₀,ε₁,ε₂] • ![C₀,C₁,C₂]`); each of the 8 cases is closed by
  `convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)` (the `1 • X = X` goals
  close by `rfl`; the `mk0(-1) • X = -X` goals close by default `simp`; the all-negative case
  closes by `convert h using 1` alone because `neg_one_smul` is a simp lemma used by `congr`).
