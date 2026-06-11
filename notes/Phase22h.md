# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge), §1.49 (G5, G4a–G4e, G0, the (β) branch shape), and §1.50 (the `hcand` discharge: the
discriminator, the rank-transfer re-route W1–W10, GAP 6) — point at them, don't duplicate.**
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

**G4c-ii is DONE (corrected to the fixed-seed shape; commit b6a66de's existential→existential
transport was a design deviation, replaced).** Now three lemmas in CaseI.lean:
- `ofNormals_relabel` — the **load-bearing** fixed-seed transport in the **producer's direction**:
  from the concrete v-split `ofNormals (splitOff v a b e₀) ends₀ q₀` four conjuncts (GP, rigid on
  V∖{v}, links, alg-indep) to the same four for the relabeled a-split `ofNormals (splitOff a v c e₁)
  endsσρ qρ` at the SAME seed `qρ (x,i) = q₀ (ρ x, i)`, ρ = swap a v, σ = swap e_b e₀ * swap e₁ e_c,
  `endsσρ e = (ρ (ends₀ (σ e)).1, ρ (ends₀ (σ e)).2)`. The relabeled construction is exposed
  (named in the statement) so the producer / G4d-ii can consume the concrete framework.
- `rigidityRows_ofNormals_relabel` — the **row-space correspondence §1.49(4) says G4d-ii consumes**:
  `(a-split).rigidityRows = (LinearMap.funLeft ℝ _ ρ).dualMap '' (v-split).rigidityRows`
  (each `hingeRow u w r` ↤ `hingeRow (ρ u) (ρ w) r`, via `ρρ = id` + the hinge-block coincidence).
- `hasGenericFullRankRealization_of_splitOff_relabel` — short existential corollary in the
  producer direction (v-split realization ⟹ a-split realization at `q₀∘ρ`); derived from
  `ofNormals_relabel`. (The old reversed-direction existential is gone — no two parallel transports.)
Graph side G4c-i (`splitOff_isLink_relabel`) reused verbatim, both `.mp`/`.mpr`. Build + lint +
verify.sh clean; axiom-clean. Blueprint `lem:splitOff-ofNormals-relabel` restated + new node
`lem:splitOff-rigidityRows-relabel`.

**G4d-i/ii are DONE** (Phase 22h). Two new lemmas in CaseI.lean:
- `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (G4d-i): `wGv ∈ span Fv.rigidityRows` + degree-2-at-`a`
  ⟹ `wGv.comp(single a) ∈ Fab.hingeRowBlock e_c`; proof by span-induction, three cases on endpoint.
- `hingeRow_acolumn_mem_span_rigidityRows` (G4d-ii): short corollary producing `hingeRow a c r̂ ∈ span Fv.rigidityRows`
  directly from G4d-i + `hingeRow_mem_rigidityRows`. Build + lint clean.

**Producer spine is DONE (corrected to the `hsplitGP` shape).** `case_III_hsplit_producer`
(CaseI.lean) is stated at the **`theorem_55_generic.hsplitGP` callback shape** (R2 verdict (B),
design §1.41(5)): premises `hG`/`hV3`/`hnoRigid`/`G.Simple` + the **full conditioned IH**
(`(Simple → generic) ∧ bare`) + `hfresh` + the carried core `hcand`; conclusion
`HasGenericFullRankRealization 2 G`. Body = G4a dichotomy: `=3 ↦` T4 returned directly (no
forgetful — the conclusion is generic); `≥4 ↦` chain arm (`exists_chain_data_of_noRigid` → fresh
`e₀` → `splitOff_isMinimalKDof` + measure drop → **R3** `splitOff_simple_of_noRigid_of_card`
discharges the GP `.1` antecedent at `|V|≥4` → the **generic** `v`-split realization feeds
`hcand`). `hcand` consumes the chain data + the generic `v`-split realization and yields
`HasGenericFullRankRealization 2 G` (its M-dispatch arms end bare; the discharge composes the
GAP-2 upgrade `hasGenericFullRankRealization_of_rigidOn_ofNormals`, §1.49(5)). `G.Simple`,
`hnoRigid`, `hfresh` stay producer-level, available to the discharge leaf at the application site.
Build + lint clean; no live callers, no blueprint pin.

**The triple-LI bridge is LANDED** (§1.48(2)): `linearIndependent_normals_of_algebraicIndependent`
(private, CaseI.lean) — `AlgebraicIndependent ℚ q` + distinct `a,b,c` →
`LinearIndependent ℝ ![q(a,·),q(b,·),q(c,·)]`. Proof: `mvPolynomialX_mapMatrix_aeval` +
`AlgHom.map_det` + `AlgebraicIndependent.aeval_ne_zero` on the generic 3×3 det polynomial;
`Matrix.linearIndependent_rows_of_det_ne_zero` + `LinearIndependent.of_comp`. (A `sorry`'d
discharge skeleton landed alongside it in af7f42b was removed by the coordinator — sorries
don't ride on master; the discharge lands as complete lemmas, assembled at the end.)

**GAP-3 good-`t` is LANDED** (Blockers, below): `exists_shear_linearIndependent_pair` (PanelLayer.lean)
— given `hgab : LinearIndependent ![n_a, n_b]`, `∃ t ≠ 0, LinearIndependent ![n_a + t•n', n_b]`. The
bad set is a subsingleton (two distinct bad `t`s put `n'`, then `n_a`, in `span {n_b}`, against
`hgab`), so among `t = 1, 2` one is good. Graph-free `Fin(k+2)→ℝ` linear algebra (no `ofNormals`
carrier ⟹ no §38 trap); supplies the `hnewtrans` input `case_III_old_new_blocks_of_line` requires.
Blueprint `lem:case-III-claim612-line-in-panel-union` pin + prose extended. Build + lint +
verify.sh clean; axiom-clean.

**The Claim-6.12 → witness-meet glue is LANDED** (the line-data → `r̂(C(L)) ≠ 0` clean cut, §1.49(5)):
`exists_complementIso_ne_zero_of_homogeneousIncidence` (RigidityMatrix.lean, `BodyHingeFramework`
namespace; added to blueprint `lem:case-III-claim612-line-in-panel-union`'s `\lean` pin + prose). The
**forward (existence) dual** of `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`: from
`r ≠ 0` + `LinearIndependent ℝ pbar` + three LI panel normals `n` + the homogeneous incidence
(`h0`–`h3`), it composes `case_III_claim612` (witness join `r̂(pᵢ∨pⱼ) ≠ 0`) with
`exists_line_data_of_homogeneousIncidence` (the join's line data) and the contrapositive of the
per-line duality to produce a witness panel `{n_u, n'}` with `r̂(complementIso (n_u ∧ n')) ≠ 0` — the
nonzero-candidate-row input the eq.-(6.12) candidate placement's row-space criterion is gated on.
Graph-free (`Fin 4` / `⋀²ℝ⁴`, off the §38 trap); build + lint + verify.sh clean; axiom-clean.

**The `hcand`-discharge recon is DONE (design §1.50; supersedes the §1.49(5) M-arm route).** Three
findings, full detail + exact signatures in §1.50: **(1)** the witness-normal discriminator is a
free statement-level restate of `exists_line_data_of_homogeneousIncidence` + the a9f191e glue, in
place, proofs reused (`∃ u : Fin 3` returning the real normal `n u`). **(2)** The §1.49(5) M-arm
route as scoped is **not dischargeable**: the sheared `ofNormals` placement breaks KT's
(6.26)–(6.28) row transport (`hro_mem`/`hcand_mem` of `case_III_realization_of_line` fail for
`n' ≠ n_b`; at `n' = n_b` the gate fails) — dissolved by the KT-Lemma-5.2 **rank-transfer
re-route**: certify the KT-(6.29) count at the `t = 0` hinge-level `BodyHingeFramework` `F₀`
(where all memberships hold by construction) and transfer along the one-parameter shear by a
one-variable minor polynomial. The planned sheared-support step
(`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` feed) is obsolete under the re-route.
**(3) GAP 6 (genuinely open, needs adjudication):** the eq.-(6.22) rank lower bound at the
`k'`-dof `G − v` is KT's nested IH (6.1), which the 0-dof-only induction cannot supply; interim =
carry the single reduced inequality as an explicit `h…` hypothesis (§1.50(b)).

**Next concrete step:** W1 — the discriminator restate (§1.50(a), RigidityMatrix.lean, both
lemmas in place). Then W2 (`finrank_span_rigidityRows_of_rigidOn` micro-leaf), W3 (one-variable
rank transfer), W4 (restriction-bottom augment) — all unconditionally buildable and independent
of the GAP-6 adjudication.

**Build order (design §1.50(f); supersedes §1.49(6) item 5's discharge clause):** W1 discriminator
→ W2 `h618` micro-leaf → W3 leaf B → W4 leaf A0 → W5 redundancy packaging (carries the GAP-6
hypothesis) → W6/W7 M₁ → W8 M₂ → W9 M₃ → W10 dispatch + discharge assembly (matches `hcand`'s
shape) → Leaf 4 → Leaf 5. Parallel: adjudicate GAP 6 (coordinator/user).

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
- [x] **G4c-ii** — `ofNormals_relabel` (fixed-seed producer-direction transport, §1.49(3)) +
  `rigidityRows_ofNormals_relabel` (the row-space correspondence G4d-ii consumes, §1.49(4)) +
  `hasGenericFullRankRealization_of_splitOff_relabel` (existential corollary, producer direction)
  (CaseI.lean; blueprint `lem:splitOff-ofNormals-relabel` restated + `lem:splitOff-rigidityRows-relabel`).
  Corrected from b6a66de's existential→existential transport (the design-deviation §1.49(3)
  excludes). Done.
- [x] **G4d-i/ii** — `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (span-induction; three endpoint
  cases) + `hingeRow_acolumn_mem_span_rigidityRows` (short corollary) (CaseI.lean; §1.49(4)). Done.
- [x] **Producer spine (corrected to the `hsplitGP` shape)** — `case_III_hsplit_producer`
  (CaseI.lean) at the `theorem_55_generic.hsplitGP` callback shape (R2 verdict (B), §1.41(5)):
  `hG`/`hV3`/`hnoRigid`/`G.Simple` + full conditioned IH + `hfresh` + carried `hcand`; concludes
  the **generic** motive. Body = `|V(G)|` dichotomy (`=3 ↦` T4 directly; `≥4 ↦` chain arm with the
  R3 split-simplicity discharge unlocking the IH's GP `.1` conjunct). Build + lint clean; no
  blueprint pin (the producer isn't `\lean`-pinned). Done.
- [~] **Discharge `hcand`** (the candidate-placement core; **§1.50 is now canonical** —
  supersedes the §1.49(5) arm route): landed feeds = the triple-LI bridge (§1.48(2)), the GAP-3
  good-`t` core `exists_shear_linearIndependent_pair`, the Claim-6.12 → witness-meet glue
  `exists_complementIso_ne_zero_of_homogeneousIncidence`. Remaining, as complete lemmas (no
  `sorry` on master), per §1.50(f): W1 discriminator restate → W2 `h618` micro-leaf → W3
  one-variable rank transfer → W4 restriction-bottom augment → W5 redundancy packaging (carries
  the GAP-6 inequality as an explicit hypothesis pending adjudication) → W6/W7 M₁ (`t = 0`
  certification at `F₀` + closer) → W8 M₂ → W9 M₃ (G4c/G4d + `candidateRow_ac_eq_neg`) → W10
  dispatch + assembly matching the `hcand` signature.
- [ ] **Leaf 4** — the `theorem_55_generic (n:=2) (k:=2)` instance node over the (β) shape,
  projecting `.2` (R2 verdict (B), §1.41); the `hcontractGP` wiring gains `hVH2` from G5. A small
  green blueprint node, not a standalone `theorem_55_dim3`.
- [ ] **Leaf 5** — the `lem:case-II-realization` / `lem:case-III` flips + the Thm 5.5→5.6 push
  feeding `rigidityMatrix_prop11`'s `hgen`; unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **GAP 6 — OPEN, needs coordinator/user adjudication (§1.50(b)).** The eq.-(6.22) rank lower
  bound at the `k'`-dof `G − v` (`rank ≥ D(m−1) − (D−2)` at the IH seed) is KT's nested IH (6.1),
  unreachable from the project's 0-dof-only induction motive. Options: (i) all-`k` motive
  restructure (phase-sized) vs (ii) carry the single reduced inequality as the explicit `h…` crux
  through W5–W10 and Leaf 4/5 (recommended interim). W1–W4 don't depend on the call.
- **GAP 3 — core LANDED** (`exists_shear_linearIndependent_pair`, PanelLayer.lean): consumed by
  leaf B's good-`t` choice (§1.50(c), the `bad`-set input).
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites every
  carrier-instantiating leaf (the producer body, the T3/T4 seeds). Keep reasoning over abstract
  `F`; instantiate only at the seed. The §1.50 re-route helps: `F₀` and leaves A0/B are abstract /
  graph-free.
## Hand-off / next phase

**Smallest next forward commit — W1, the discriminator restate (§1.50(a)).** Restate
`exists_line_data_of_homogeneousIncidence` and `exists_complementIso_ne_zero_of_homogeneousIncidence`
(both RigidityMatrix.lean, no outside consumers) **in place** at the discriminating level
`∃ u : Fin 3, …` with the witness normal returned as the real `n u` — the `Fin 3`-valued
M₁/M₂/M₃ dispatch input. Statement-level change; both proofs reuse verbatim (every builder branch
already supplies a concrete `u`). Exact signatures in §1.50(a). **No `sorry` placeholders.**
Then W2–W4 (each one commit, §1.50(f)), W5 onward per the build order; the GAP-6 adjudication
(Blockers) runs in parallel and gates only W5+.

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
- **G4c-ii corrected to fixed-seed (design-deviation fix; replaced b6a66de).** The deviation:
  b6a66de stated G4c-ii as an existential→existential transport in the *reversed* direction (a-split
  ⟹ v-split), which §1.49(3) explicitly excludes ("transporting the existential loses the seed
  identity (6.44) requires — state everything at the ofNormals level") and which omitted the
  rigidityRows row-space correspondence §1.49(4) says G4d-ii consumes. Fix: (a) `ofNormals_relabel`
  states the transport in the **producer direction** at the **fixed seed** `q₀∘ρ`, exposing the
  relabeled `ofNormals` construction in the statement (so consumers name it); (b)
  `rigidityRows_ofNormals_relabel` adds the `(funLeft ρ).dualMap`-image row correspondence; (c) the
  existential is a short *producer-direction* corollary (no two parallel transports).
- **Statement-level `Equiv.swap` opacity (the fix's main friction).** Putting `let ρ := Equiv.swap
  a v` etc. in the *statement* requires `[DecidableEq α/β]` and makes the `let`-locals opaque after
  `intro` (`exact Equiv.swap_apply_self …` fails against the `let`-bound `ρ (ρ x) = x`). Resolution:
  *inline* the explicit terms (`Equiv.swap a v`, …) in the statement (consumers name them via the
  same expression; the docstring carries the `ρ/σ/qρ/endsσρ` abbreviations), then `set ρ := Equiv.swap
  a v` in the proof body to fold them back into nameable locals. `change` (not `show`) is the
  warning-clean tactic for the defeq goal changes that expose the `ofNormals` form for `simp only`
  / `exact`. → FRICTION.md [let-opacity].
- **T4 sign-flip dispatch (`hasGenericFullRankRealization_of_triangle`):** each triangle-edge
  extensor equals ±Cᵢ via `endsOf_eq_or_swap` (2 cases × 3 edges = 8-way `rcases` dispatch).
  The `hLI_neg` helper builds LI for `![ε₀•C₀, ε₁•C₁, ε₂•C₂]` via `units_smul_iff` + the
  `Pi.smul` form (`![ε₀,ε₁,ε₂] • ![C₀,C₁,C₂]`); each of the 8 cases is closed by
  `convert h using 1; funext i; fin_cases i <;> (first | rfl | simp)` (the `1 • X = X` goals
  close by `rfl`; the `mk0(-1) • X = -X` goals close by default `simp`; the all-negative case
  closes by `convert h using 1` alone because `neg_one_smul` is a simp lemma used by `congr`).
- **Producer corrected to the `hsplitGP` shape (corrective commit replacing 9c5879c's bare-IH
  restate).** 9c5879c read "(β) branch shape" as bare IH + bare conclusion — a misread ((β) hands
  the no-rigid branch the **full conditioned IH**, §1.49(1)) that re-enacted the §1.46 GAP-1
  dissolution the §1.47/R2/R3 verdicts overturned: it orphans `hgab` (only the GP `.1` conjunct
  supplies the placement transversal + alg-indep; a bare rigid realization may have parallel
  panels, §1.41(1)). Fix: `G.Simple` + full conditioned IH in, generic motive out; chain arm
  discharges the split's GP `.1` antecedent via R3 (`splitOff_simple_of_noRigid_of_card`, needs
  `|V|≥4` — the `|V|=3` branch goes to T4 and never splits, §1.46 finding 2); `hcand` is
  generic-in/generic-out. 9c5879c's dichotomy spine, `hfresh` ownership rationale, and
  `hGv2`-via-`Set.ncard_diff` pattern are kept; G0 is no longer called in the body (`G.Simple` is
  now a premise). T4 stays above the producer in CaseI.lean.
- **GAP-3 good-`t` (`exists_shear_linearIndependent_pair`, PanelLayer.lean):** the bad-`t` set is a
  subsingleton, proved via `LinearIndependent.pair_iff'` at the nonzero `n_b` (swap to `![n_b, ·]`
  since `n_a + t•n'` may be zero) — each bad `t` gives `c, c•n_b = n_a + t•n'`; two distinct bad
  `t`s subtract to put `n'`, then `n_a`, in `span {n_b}`, against `hgab`. With ≤ 1 bad value, `t = 1`
  or `t = 2` is good (closed by `by_cases` + `norm_num`, no infinite-set machinery). The `∃ c` needs
  `: ℝ` (HSMul-metavar stuck, §31-family). Graph-free, no §38 trap; pinned to the existing node
  `lem:case-III-claim612-line-in-panel-union` (the line-in-panel-union group).
- **`hcand`-discharge recon (design §1.50; docs-only).** Verdicts: discriminator restate free
  (statement-level, proofs reuse); the §1.49(5) sheared-placement arm route undischargeable (the
  KT (6.26)–(6.28) transport needs `p₁(vb) = q(ab)`, lost at `n' ≠ n_b`) → re-routed via KT
  Lemma 5.2 (certify at the `t = 0` hinge-level `F₀`, transfer by a one-variable minor
  polynomial; `annihRow`'s linearity in `C` makes the `e_a`-rows `t`-constant after rescaling);
  GAP 6 surfaced (eq.-(6.22) nested-IH rank bound, open). All detail + signatures in §1.50.
- **Claim-6.12 → witness-meet glue (`exists_complementIso_ne_zero_of_homogeneousIncidence`,
  RigidityMatrix.lean, `BodyHingeFramework`):** the forward (existence) dual of the green
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` — a clean three-line composition of
  `case_III_claim612` (witness join `r̂(pᵢ∨pⱼ)≠0`), `exists_line_data_of_homogeneousIncidence` (line
  data), and the duality's contrapositive (`r̂(C(L))=0 ⟹ r̂(join)=0`, against the witness). The one
  idiom: `rw [show ⟨omitTwoExtensor pbar …, _⟩ = ⟨extensor ![pi,pj], _⟩ from Subtype.ext hkept]`
  lifts the line-data underlying-value identity to the `ScrewSpace 2` subtype. Graph-free, no §38;
  added to the existing node's `\lean` pin + prose (the witness `r̂(C(L))≠0` the producer is gated on).
