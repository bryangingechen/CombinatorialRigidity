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

**Next concrete step: T3** (`exists_triangle_normals`, §1.48(1)), the cyclic-seed existence lemma.

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
- [ ] **T3** — `exists_triangle_normals` (PanelLayer.lean; §1.48(1)): 3 pairwise-LI standard-basis
  normals + cyclic join LI. ~1 commit; parallel-safe after G4b-impl.
  (Ledger entry: `notes/BlueprintExposition.md`, writes at this phase's close.)
- [ ] **T4** — `hasGenericFullRankRealization_of_triangle` (CaseI.lean; §1.48(1)): triangle
  assembly through `hasGenericFullRankRealization_of_rigidOn_ofNormals`. ~1–2 commits.
- [ ] **G4c-i/ii** — the fixed-seed `ρ = (a v)` relabel transport (graph iso + `ofNormals`
  framework transport; the existential motive is NOT transported — eq. (6.44) needs the SAME
  seed; genericity free, same coordinate set) (§1.49(3)).
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

**Smallest next forward commit — T3** (`exists_triangle_normals`, §1.48(1)):
3 pairwise-LI standard-basis normals + cyclic join LI (PanelLayer.lean).
Parallel-safe with G4c-i/ii (§1.49(3)).
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
