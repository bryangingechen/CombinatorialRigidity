# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge), §1.49 (G5, G4a–G4e, G0, the (β) branch shape), §1.50 (the `hcand` discharge: the
discriminator, the rank-transfer re-route W1–W10, GAP 6), and §1.51 (the W6-concrete
decomposition W6a–W6f + W7, exact signatures) — point at them, don't duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**All §1.48/§1.49 leaves are landed** — G5, G4b-impl, G4a-i/ii + G0, T1–T4, G4c-i/ii, G4d-i/ii,
the (β)-shaped producer spine `case_III_hsplit_producer` (CaseI.lean; carries the open core as
its `hcand` parameter), the triple-LI bridge, the GAP-3 good-`t` core
`exists_shear_linearIndependent_pair`, and the Claim-6.12 → witness-meet glue
`exists_complementIso_ne_zero_of_homogeneousIncidence`. Per-leaf detail: the checklist below
(lemma + file + blueprint node), *Decisions made* (proof techniques), and the design §refs.
Build + lint + verify.sh clean throughout; axiom-clean.

**The `hcand`-discharge recon is DONE (design §1.50, its W6-remainder build-out decomposed in
§1.51; together canonical for ALL remaining work — supersedes the §1.49(5) M-arm route).** (1) The witness-normal discriminator is a free in-place
restate of the line-data lemma + the glue (proofs reuse). (2) The sheared-placement arm route is
undischargeable (it breaks KT's (6.26)–(6.28) row transport) — re-routed via KT Lemma 5.2:
certify the (6.29) count at the `t = 0` hinge-level `BodyHingeFramework` `F₀` (memberships hold
by construction), transfer along the shear by a one-variable minor polynomial; the previously
planned sheared-support step is obsolete. (3) GAP 6 surfaced and **adjudicated** — see Blockers.
Coordinator independently verified all three verdicts against KT pp. 681–684 + the Lean
(model-experiment row 20).

**Next concrete step (W6 done → W7): design §1.51 is now canonical** — the monolithic
"W6-concrete/W7" slot is decomposed into seven exact-signature one-commit leaves **W6a–W6f + W7**
(two opus builders had sized the undivided slot as un-carvable, model-experiment rows 26–27).
§1.51(a) also *refines* §1.50(c): the certified `t = 0` mixed family is not itself transferable
(its candidate row and `(vb)ⱼ`-transports are not sheared-candidate rows at `t ≠ 0`); the route is
**certify-then-rebase** — certify the (6.29) count at `F₀` (W6c+W6d), convert to a rank lower
bound and re-extract a literal `F₀.panelRow` family (W6e), transfer that along the `t`-family
(W6f), close through the span core + GAP-2 (W7). **All of W6a–W6f, W7, AND W8 are landed** — the
certify-then-rebase arm (M₁) and the M₂ arm (a pure W7 instantiation) are complete. Smallest next
commit: **W9** (the M₃ arm, §1.50(e)/§1.51(i)) — W7 at the *relabeled* `a`-split data (the
`caseIIICandidate` def takes the relabeled seed `qρ` as its `q`; W7's `(v,a,b,e_a,e_b,n')`-slots at
`(a,c,v,e_c,e_a,n''')`), with the candidate functional arriving as the same `ρ` through
`candidateRow_ac_eq_neg` + the `rigidityRows_ofNormals_relabel` row-space transport. Then per
§1.51(j): W10 (dispatch + discharge matching `hcand`) → Leaf 4 → Leaf 5 → phase close
green-modulo-GAP-6.

**W7 (the M₁ arm closer) is landed** — `PanelHingeFramework.case_III_arm_realization` (CaseI.lean):
the role-parametric arm yielding `HasGenericFullRankRealization k G` from the unpacked split context
+ W6b's `ρ`/`w` package. Route: (i) W6d → the rank bound at `F₀`; (ii) W6e re-extracts a literal
`F₀.panelRow` linking family of size `D(|V(G)|−1)`; (iii) W6f transfers it to a good `t^* ≠ 0`
outside the GAP-3 bad set, forcing `![n_a + t^*·n', n_b]` LI; (iv) each `F(t^*)`-slot lies in
`span (ofNormals G ends q₀).rigidityRows` (`q₀` shears `v` along `n_a + t^*·n'`): the `e_b`/`Gᵥ`-slots
have *equal* extensors (genuine rows), the candidate `e_a`-slot is `(-1/t^*) •` a genuine row
(`panelSupportExtensor_add_smul_left` + `annihRow_smul`); (v)
`isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` + GAP-2 close. §38: the heavy
`Ft.panelRow`-family is generalized to an opaque `f` (`set` + `clear_value`) before the rigidity
lemma (else `whnf`-timeout even at 4M heartbeats — TACTICS-QUIRKS §38 *Row-family-argument
variant*); `[DecidableEq α/β]` dropped (`classical` supplies them). Build + lint + axiom-clean
([propext, Classical.choice, Quot.sound]); no `\lean` pin (internal infra). GAP-6-clean (W6b carries
`h622lb`).

**Build order (§1.51(j); supersedes §1.50(f) item 6):** W1–W5 + W6-core + W6a–W6f + **W7** + **W8**
all landed (M₁ certify-then-rebase + M₂ instantiation; `h622lb` GAP-6 carry entered at W5, rides
through W6b) → W9 (M₃ wiring) → W10 (dispatch + discharge assembly, matches `hcand`'s shape) →
Leaf 4 → Leaf 5 → phase close, **green-modulo-GAP-6**. Exact signatures + per-leaf
consumes/consumed-by/§38 notes: §1.51 (design doc). Per-leaf landing detail is in git history +
*Decisions made* below.

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
  `exists_complementIso_ne_zero_of_homogeneousIncidence`, and **W1 the discriminator restate**
  (`exists_line_data_of_homogeneousIncidence` + the witness-meet glue now return the dispatch index
  `u : Fin 3`, witness normal `n u`), and **W2 the `h618` micro-leaf**
  (`finrank_span_rigidityRows_of_rigidOn`, GenericityDevice.lean: `finrank (span rigidityRows) =
  D(|V|−1)` from `IsInfinitesimallyRigidOn V(F.graph)`; the inline `hfin` extract, the two
  `…_subfamily_of_rigidOn` sites now call it), and **W3 leaf B**
  (`LinearIndependent.exists_notMem_of_polynomial_repr` + the general-polynomial matrix engine
  `Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial`, Rank.lean — the KT-Lemma-5.2
  one-variable rank transfer, graph-free), and **W4 leaf A0**
  (`linearIndependent_sum_restriction_block`, RigidityMatrix.lean — the restriction-bottom
  block-triangular augment, the transposed sibling of `linearIndependent_sum_pinned_block`;
  graph-free), and **W5 the redundancy-data packaging**
  (`exists_redundant_panelRow_ab_lam_of_rigidOn`, CaseI.lean — the consumer-level
  `exists_redundant_panelRow_ab_lam` with `h618` from `hrig`/W2 and `h622` by-construction; the
  carried GAP-6 lower bound `h622lb` is its `hk'`), and **W6-core the restriction-form candidate
  augment** (`linearIndependent_sum_augment_candidateRow_restriction`, RigidityMatrix.lean — the
  abstract A1 core: the restriction-bottom sibling of `linearIndependent_sum_augment_candidateRow`,
  using W4 instead of `_pinned_block_augment`; graph-free, axiom-clean, no `\lean` pin), and **W6a
  the `caseIIICandidate` `t`-family + infra bricks** (`PanelHingeFramework.caseIIICandidate` + its
  three support-extensor evals + the affine `caseIIICandidate_panelRow_eq_add_smul`, CaseI.lean;
  `panelSupportExtensor_add_left`/`_smul_left` + `annihRow_add`/`_smul` +
  `setOf_not_shear_linearIndependent_subsingleton` (refactored out of
  `exists_shear_linearIndependent_pair`), PanelLayer.lean; the two restriction-transport bricks
  `hingeRow_comp_columnOp_comp_offProj` / `comp_columnOp_comp_offProj_of_single_eq_zero`,
  RigidityMatrix.lean; all graph-free / abstract, axiom-clean, no `\lean` pin), and **W6e the
  rank-bound panelRow re-extraction** (`exists_independent_panelRow_subfamily_of_le_finrank`,
  GenericityDevice.lean — the rank-input generalization of `_of_rigidOn_linking`: feed a rank lower
  bound `N ≤ finrank(span F.rigidityRows)`, get `N` literal linking `F.panelRow`s, by transporting
  the bound to `span T` via `span_panelRow_linking_eq_rigidityRows` and cutting the
  `exists_fun_fin_finrank_span_eq` family to `Fin N` via `Fin.castLE`; `_of_rigidOn_linking`
  refactored to its 3-line corollary via W2; axiom-clean, no `\lean` pin), and **W6c the
  restriction-form full family** (`PanelHingeFramework.case_III_full_family_restriction`,
  CaseI.lean — the restriction-bottom sibling of `case_III_full_family_of_line`: the same NEW block
  (`exists_independent_panelRow_subfamily_of_edge` + the criterion at the witness `r(C(e_a)) ≠ 0`)
  closed against W4's restriction-bottom contract `hbotrestrict` via the W6-core augment instead of
  the v-vanishing selector; the two W6-core inputs are the selector's inline `hnewpinaug` two-liner
  + `hrnvanish` via `panelRow_eq_hingeRow_annihRow_of_ends` + `hingeRow_comp_columnOp_vanish_off`;
  graph-free, axiom-clean, no `\lean` pin), and **W6b the candidate/bottom data packaging**
  (`BodyHingeFramework.exists_candidateRow_bottomRows_of_rigidOn`, CaseI.lean — one W5 invocation
  gives the candidate functional `ρ` (`r̂ = hingeRow … ρ` via `span_panelRow_edge_eq` + `mem_hingeRowBlock_iff`;
  `ρ ≠ 0`, `ρ(C(e₀)) = 0`, `hingeRow … ρ ∈ span Gv-rows`) **and** the `D(m−1)` bottom rows `w`
  extracted by `exists_fun_fin_finrank_span_eq` from `span(Gv-rows ∪ r '' {≠ i^*})` — which equals
  `span Gab-rows` of finrank `D(m−1)` since `r i^* = r̂ − ∑_{≠ i^*} λ_j r_j`, both addends in the
  union span — each `w j` per-tagged as a `Gv`-row or a block `hingeRow … ρ'` (`ρ'(C(e₀)) = 0`);
  **this is W5's sole caller, so `h622lb` enters the Lean here**; axiom-clean, no `\lean` pin),
  and **W6f the one-variable transfer at the `t`-family**
  (`PanelHingeFramework.caseIIICandidate_exists_good_shear`, CaseI.lean — W3's basis-free
  KT-Lemma-5.2 rank transfer specialized to `caseIIICandidate`: from a `t = 0`-LI panel-row
  subfamily + a finite `bad` set, picks `t ∉ bad`, `t ≠ 0` keeping the family LI at `t`, via the
  affine `caseIIICandidate_panelRow_eq_add_smul` (W6a) → degree-`≤ 1` coordinate polynomials over
  `Module.finBasis ℝ (Module.Dual …)` → W3; consumes only W6a/W3, GAP-6-clean; axiom-clean, no
  `\lean` pin), and **W6d the `t = 0` rank certification at `F₀`**
  (`PanelHingeFramework.case_III_rank_certification`, CaseI.lean — the (6.29) count at
  `F₀ := caseIIICandidate G ends q e_a e_b na n' nb 0`, concluded as the consumable rank lower
  bound `D(|V(G)|−1) ≤ finrank(span F₀.rigidityRows)`. Route: (i) transport W6b's bottom rows `w`
  to W6c's `hbotrestrict` per-tag — genuine `G_v`-rows survive brick 2 (off-`v`, `hingeRow_comp_
  single_off`), the `ρ'`-rows enter as `hingeRow v b ρ'` whose `Φ∘P_v`-composite is `hingeRow a b
  ρ' = w j` (brick 1); (ii) feed W6c at `F := F₀`; (iii) memberships in `span F₀.rigidityRows` —
  `sn`-rows genuine `e_a`-links, candidate via the eq.-(6.27) collapse `hingeRow v a ρ = hingeRow
  v b ρ − hingeRow a b ρ` (`hingeRow v b ρ` a genuine `e_b`-row at `t=0`, `hingeRow a b ρ ∈ span
  Fv-rows ≤ span F₀-rows`), bottom per-tag; (iv) count `((D−1)+1)+D(m_v−1) = D(|V(G)|−1)` via
  `finrank_span_eq_card` + `finrank_mono`. GAP-6-clean (W6b carries `h622lb`); axiom-clean, no
  `\lean` pin), and **W7 the M₁ arm closer** (`case_III_arm_realization`, CaseI.lean — W6d→W6e→W6f
  certify-then-rebase + the `q₀`-membership + GAP-2 close; see *Current state* + *Decisions made*
  for the route and the §38 row-family generalization), and **W8 the M₂ arm closer**
  (`case_III_arm_realization_M2`, CaseI.lean — a pure instantiation of W7 at the swapped roles with
  `ρ' := −ρ`; candidate at `e_b`/line `n_b ∧ n''`, hypotheses convert by `hingeRow_swap` /
  `panelSupportExtensor_swap` / `LinearMap.neg_apply` / `LinearIndependent.pair_symm_iff`;
  graph-free, axiom-clean, no `\lean` pin). Remaining, as complete lemmas (no `sorry` on master),
  per §1.51(i)/(j): W9 M₃ (G4c/G4d + `candidateRow_ac_eq_neg`) → W10 dispatch + assembly matching
  the `hcand` signature. Exact per-leaf signatures: §1.51(c)–(i).
- [ ] **Leaf 4** — the `theorem_55_generic (n:=2) (k:=2)` instance node over the (β) shape,
  projecting `.2` (R2 verdict (B), §1.41); the `hcontractGP` wiring gains `hVH2` from G5. A small
  green blueprint node, not a standalone `theorem_55_dim3`.
- [ ] **Leaf 5** — the `lem:case-II-realization` / `lem:case-III` flips + the Thm 5.5→5.6 push
  feeding `rigidityMatrix_prop11`'s `hgen`; unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **GAP 6 — ADJUDICATED (user, 2026-06-10): carry as explicit hypothesis (§1.50(b) option (ii)).**
  The eq.-(6.22) rank lower bound at the `k'`-dof `G − v` is KT's nested IH (6.1), unreachable
  from the 0-dof-only motive (verified against KT p. 684 + the Lean). The single reduced
  inequality rides as the honestly-named `h…` crux: it enters at W5 (its one consumption site)
  and rides up through W10 and Leaf 4/5, so **22h closes green-modulo this one hypothesis**. The
  successor sub-phase implements the all-`k` motive restructure (§1.50(b) option (i), est.
  ~10–17 commits) and discharges it with a small wiring commit. How the 0-dof narrowing happened:
  DESIGN.md *Narrowing an induction motive requires an IH-application census*.
- **GAP 3 — core LANDED + subsingleton extracted (W6a)** (`exists_shear_linearIndependent_pair`,
  PanelLayer.lean): the inline bad-set bound is now the standalone
  `setOf_not_shear_linearIndependent_subsingleton` (the existence lemma consumes it); W7 feeds it
  to the W6f transfer as the `bad`-set (§1.51(b)/(h)).
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites every
  carrier-instantiating leaf (the producer body, the T3/T4 seeds). Keep reasoning over abstract
  `F`; instantiate only at the seed. The §1.50 re-route helps: `F₀` and leaves A0/B are abstract /
  graph-free.
## Hand-off / next phase

**Smallest next forward commit — W9 (the M₃ arm, §1.50(e)/§1.51(i)).** W7
(`case_III_arm_realization`) is landed and **role-parametric**, and W8
(`case_III_arm_realization_M2`) instantiated it for M₂; W9 is the third arm — W7 at the
*relabeled* `a`-split data. The `caseIIICandidate` def takes the relabeled seed `qρ` as its
`q`-argument, and W7's `(v,a,b,e_a,e_b,n')`-slots are instantiated at `(a,c,v,e_c,e_a,n''')`
(re-inserted body `a`, candidate hinge `e_c = ac` on the line `L'' ⊂ Π(c)` — the `u = 2` witness;
reproduced hinge `e_a = av` at the relabeled split's `vc`-hinge; `Gv`-slot the relabeled split minus
its short-circuit edge). The candidate functional arrives as the *same* `ρ` through
`candidateRow_ac_eq_neg` + the `rigidityRows_ofNormals_relabel` row-space transport; pin the
residual sign/wiring shapes at the W9 design moment (the producer-direction `ofNormals_relabel` /
G4c/G4d leaves are landed). Unlike W8 (a pure type-level instantiation), W9 has the relabel
transport to wire, so budget it as its own commit. Then per §1.51(i)/(j): W10 (dispatch +
discharge matching `hcand`) → Leaf 4 → Leaf 5 → phase close green-modulo-GAP-6. **No `sorry`** at
any step (carry GAP-6 as the named `h622lb`, never a `sorry`).

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
- **W2 `h618` micro-leaf (`finrank_span_rigidityRows_of_rigidOn`):** placed in GenericityDevice.lean,
  *not* RigidityMatrix.lean as §1.50(b) aspired — the proof's sole non-trivial dependency
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet` is itself in GenericityDevice
  (downstream of RigidityMatrix), so beside it is the honest home (moving the support lemma upstream
  was out of scope for a micro-leaf). Body = the inline `hfin` rank-nullity computation verbatim
  minus the `span_panelRow_eq_rigidityRows` conversion (so no `hends`/`hne`); the two
  `…_subfamily_of_rigidOn`(`_linking`) sites now `rw [span_panelRow…]; exact …`, dropping the
  duplicated `hZ`/`h1`/`hsplit`/`hcompl` boilerplate. No `\lean` pin (internal infra). No friction.
- **W3 leaf B (`LinearIndependent.exists_notMem_of_polynomial_repr`, Rank.lean):** the basis-free
  KT-Lemma-5.2 transfer. Factored into a reusable general-polynomial matrix engine
  `Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial` (the `P : Matrix m n (Polynomial ℝ)`
  generalization of the affine `…_along_affine_path` — same Gram-det `Q := det (P·Pᵀ)`,
  `Polynomial.finite_setOf_isRoot` argument, just a general `P` rather than `X • C(B) + C(A)`), then
  leaf B pulls `g t` back along `φ := b.equivFun` (so `φ ∘ g t` is the `evalRingHom t`-row of
  `Matrix.of P`) and picks `t` from `ℝ ∖ ({dependent t} ∪ bad ∪ {0})` via `Set.Finite.infinite_compl`.
  Both land in the `Mathlib/` mirror (upstream `Matrix`/`LinearIndependent` namespaces). No friction.
- **W4 leaf A0 (`linearIndependent_sum_restriction_block`, RigidityMatrix.lean):** the transposed
  sibling of `linearIndependent_sum_pinned_block` — same block-triangular argument, roles swapped on
  the *kind* of restriction. Hypotheses: `top` pure-`v` (`htopvanish : S v = 0 → top i S = 0`) with
  pinned-independent `v`-forms (`htoppin`), and `bot` restricted to `V∖{v}` independent (`hbotrestrict`
  on the composites `bot j ∘ₗ P_v`, `P_v := id − single v ∘ₗ proj v`). Proof mirrors the sibling:
  evaluate at `P_v S` (`(P_v S) v = 0`) to kill `top`, recover `bot`-coeffs by `hbotrestrict`, then
  pin to `v` (`comp (single v)`) to recover `top`-coeffs by `htoppin`. The `(∑ tᵢ).comp single =
  ∑ (tᵢ.comp single)` step has no fused lemma (`LinearMap.sum_comp` doesn't exist) — done pointwise
  via `LinearMap.ext` + `LinearMap.congr_fun`, the same idiom the sibling's `hnew0` already uses
  (not new friction). No `\lean` pin (internal infra). Build/lint/axiom-clean.
- **W6-core (`linearIndependent_sum_augment_candidateRow_restriction`, RigidityMatrix.lean):** the
  abstract A1 core — the restriction-bottom sibling of `linearIndependent_sum_augment_candidateRow`.
  Same column op `Φ = columnOp hva` + `Φ.dualMap` transport-back, but the operated family is fed to
  W4 (`linearIndependent_sum_restriction_block`) instead of `_pinned_block_augment`: the operated
  top block (`va`-rows + operated candidate, pure-`v`-column) meets W4's `htopvanish`/`htoppin`, the
  operated bottom meets `hbotrestrict`. The abstract `rn` block carries its own
  `hrnvanish` (the v-vanishing the candidate gets free from `hingeRow_comp_columnOp_vanish_off`).
  No `change`/glue chains — a clean mirror of the sibling; no `\lean` pin (internal infra, like W4).
- **W5 redundancy packaging (`exists_redundant_panelRow_ab_lam_of_rigidOn`, CaseI.lean):** the
  `_ab_lam` consumer wrapper whose two `finrank` inputs ride at their natural shape. `h618` ← `hrig`
  (`Gab` rigid on `Gab.vertexSet`) via W2; the `Gab.vertexSet`-stated `hnev`/`hrig` bridge into W2's
  `F.graph.vertexSet` form by the `Fab.graph = Gab := rfl` `ofNormals` graph defeq (the established
  idiom, not new friction). `h622` is **by construction**: `k' := D(m−1) − fGv` makes `fGv = D(m−1)
  − k'` hold by `omega` once the free upper bound `fGv ≤ D(m−1)` (from
  `span_rigidityRows_eq_sup_span_panelRow_edge` + `finrank_mono le_sup_left`); then `hk' : k' ≤ D−2`
  is the carried GAP-6 lower bound `h622lb` rearranged by `omega`. Clean three-step composition; no
  `change`/`show`, no glue chains. No `\lean` pin (internal infra). Build/lint/axiom-clean.
- **W6-concrete decomposed (design §1.51; docs-only).** The slot two opus builders sized as
  un-carvable is cut into seven exact-signature one-commit leaves W6a–W6f + W7, pinned against
  the landed source + KT pp. 668–669/681–686. One §1.50(c) correction: the certified `t = 0`
  mixed family is *not* directly transferable (its candidate row / `(vb)ⱼ`-transports aren't
  sheared-candidate rows at `t ≠ 0`); the fixed route is **certify-then-rebase** (rank-bound at
  `F₀` → re-extract literal `F₀.panelRow`s → transfer those). GAP-6 isolation fell out: only W6b
  and W10 carry `h622lb`. M₂ = W7 at swapped roles with `ρ' := −ρ` (orientation artifact; KT
  p. 681 has `r' = r`).
- **W6a the `caseIIICandidate` `t`-family + infra bricks (§1.51(b)).** `caseIIICandidate` is a
  `BodyHingeFramework` overriding two `(ofNormals …).toBodyHinge.supportExtensor` slots via
  `Function.update` (not a `PanelHingeFramework` — the two hinges aren't normals of one
  coordinatization); the eval lemmas need `change Function.update …` to project the structure
  literal (FRICTION line-564 rule). `caseIIICandidate_panelRow_eq_add_smul` (rows affine in `t`)
  routes through the new PanelLayer first-column linearity (`panelSupportExtensor_add_left`/
  `_smul_left` + `annihRow_add`/`_smul`) and `hingeRow_eq_dualMap` for `hingeRow`'s `r`-linearity.
  RigidityMatrix brick 2: `columnOp_apply` `rw` didn't fire post-coercion → `unfold columnOp` +
  pointwise (new FRICTION [resolved]). All axiom-clean; no `\lean` pins.
- **W6e the rank-bound panelRow re-extraction (§1.51(f); `exists_independent_panelRow_subfamily_of_le_finrank`,
  GenericityDevice.lean).** The honest "rank ⟹ that many literal panel rows" converter: feed a rank
  lower bound `N ≤ finrank(span F.rigidityRows)`, get `N` linking `F.panelRow`s. Body = the
  `_of_rigidOn_linking` skeleton with two changes — transport the bound to `span T` via
  `span_panelRow_linking_eq_rigidityRows`, then cut the `exists_fun_fin_finrank_span_eq` family to
  `Fin N` by precomposing the re-index with `Fin.castLE hNle` (`Fin.castLE_injective` for the
  injectivity, `hfindep.comp (Fin.castLE …)` for LI of the subfamily). Placed it *above*
  `_of_rigidOn_linking` and refactored the latter to its 3-line corollary (feed
  `(finrank_span_rigidityRows_of_rigidOn …).ge` as the bound — same extract-and-refactor move W2
  made). Clean mirror, no `change`/glue; axiom-clean, no `\lean` pin (internal infra). No friction.
- **W6b the candidate/bottom data packaging (§1.51(c); `exists_candidateRow_bottomRows_of_rigidOn`,
  CaseI.lean).** One W5 call → `ρ` (factor `r̂ = ∑ λ_j r_j` through `span(range r) = E_b = map
  (screwDiff …).dualMap (hingeRowBlock e₀)` via `span_panelRow_edge_eq`; `ρ ≠ 0` since `r̂ ≠ 0`;
  `ρ(C(e₀)) = 0` by `mem_hingeRowBlock_iff`) and `D(m−1)` bottom rows from
  `span(Gv-rows ∪ r '' {≠ i^*})` (`Submodule.exists_fun_fin_finrank_span_eq`, finrank via W2 +
  `span_rigidityRows_eq_sup_span_panelRow_edge`; `r i^* = r̂ − ∑_{≠ i^*}` puts the span = Gab-rows),
  re-indexed `Fin (finrank) → Fin (D(m−1))` by `Fin.cast hfin.symm`. **W5's sole caller → `h622lb`
  enters here.** Friction: `set Eb := span(range r)` folded W5's `hrspan` into `Eb = …`, breaking a
  later `rw` (→ FRICTION / TACTICS-QUIRKS § 43). Axiom-clean; no `\lean` pin.
- **W6f the one-variable transfer (§1.51(g); `caseIIICandidate_exists_good_shear`, CaseI.lean).**
  Near-verbatim instantiation of W3 at `caseIIICandidate`: `set g/A/B`, `hsplit` from W6a's affine
  `caseIIICandidate_panelRow_eq_add_smul`, `b := Module.finBasis ℝ (Module.Dual …)` (finite-dim
  resolves automatically, the :2223 idiom), `P i j := C (b.repr (A i) j) + X * C (b.repr (B i) j)`,
  `hP` by pushing `b.repr` through the affine combo. The `hP` finale: the design's `simp [P]` left a
  `t * X = X * t` residual — `simp only [P, eval_add, eval_C, eval_mul, eval_X]` closes it warning-
  clean (the `eval_mul`/`eval_X` normal form lines up both sides; `mul_comm` was unused). No new
  friction (no build-failure→mirror cycle; a one-edit golf, not an API gap). Axiom-clean; no `\lean`
  pin.
- **W6d the `t = 0` rank certification (§1.51(e); `case_III_rank_certification`, CaseI.lean).** The
  certify step: feed W6c at `F := F₀` with W6b's data. (i) The bottom transport rides as a `choose`
  over `∀ j, ∃ wt, ((wt ∘ₗ Φ) ∘ₗ Pv = w j) ∧ wt ∈ span F₀.rigidityRows` — per-tag: a genuine
  `G_v`-row `hingeRow u w' r'` (`v ≠ u, w'` from `hvVc` + `IsLink.left/right_mem`) stays fixed by
  brick 2 (`comp_columnOp_comp_offProj_of_single_eq_zero` ∘ `hingeRow_comp_single_off`), a `ρ'`-row
  enters as `hingeRow v b ρ'` with composite `hingeRow a b ρ' = w j` (brick 1); `hbotrestrict` is
  then `hw` after `funext`. (ii)/(iii) memberships built with the `hrow_mem` explicit-witness idiom
  (§38-clean — `F₀`'s extensors only via the W6a simp lemmas + `caseIIICandidate_supportExtensor_*`);
  the candidate collapses via `← hingeRow_sub_hingeRow_eq v a b ρ` (the `Sum.elim` projection exposed
  by `change`, not `show`). `span Fv-rows ≤ span F₀-rows` proved once by membership (every `G_v`-edge
  `≠ e_a, e_b` since its endpoints avoid `v`, so `caseIIICandidate_supportExtensor_of_ne` collapses
  the block to `Fv`'s). (iv) The index `(sn ⊕ Unit) ⊕ ιb` is `Finite` via `hfam.finite`; count
  `((D−1)+1)+D(m_v−1) = D·m_v` via `obtain ⟨m', …⟩` + `Nat.mul_succ` + `omega` (`D ≥ 1` =
  `Nat.choose_pos`). GAP-6-clean (carried in W6b); axiom-clean; no `\lean` pin.
- **W7 the M₁ arm closer (§1.51(h); `case_III_arm_realization`, CaseI.lean).** The five-step route
  (W6d rank → W6e re-extract → W6f shear → `q₀`-membership → rigidity + GAP-2) is summarized in
  *Current state*. Two friction points: (1) the `q₀`-membership of each `F(t^*)`-slot splits by
  `hsplitG` into the `e_a` slot (`(-1/t^*) •` a genuine row via `panelSupportExtensor_add_smul_left`
  + `annihRow_smul` + `hingeRow` linearity, `t^* ≠ 0` inverts), the `e_b`/`Gᵥ` slots (extensors
  *equal* the sheared seed's, so genuine rows — a small `hFG₀_eq_panelRow` "equal extensors ⟹ equal
  panelRows" helper via `panelRow_eq_hingeRow_annihRow_of_ends`); all dispatched with named `he`
  equalities + `rw [he]`, never `rcases … rfl` (avoids the §4 `e_a`/`e_b` subst-direction trap). (2)
  the closing `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` `whnf`-timed-out (even at
  4M heartbeats) on its heavy `Ft.panelRow`-family argument — fixed by `set f := <family>;
  clear_value f` (→ TACTICS-QUIRKS §38). `[DecidableEq α/β]` dropped (the `unusedDecidableInType`
  lint; `classical` + `caseIIICandidate`'s own instances suffice). Axiom-clean; no `\lean` pin.
- **W8 the M₂ arm closer (§1.51(i); `case_III_arm_realization_M2`, CaseI.lean).** A one-`refine`
  instantiation of W7 at the swapped roles `(a,b,e_a,e_b,n') := (b,a,e_b,e_a,n'')` with `ρ' := −ρ`.
  Signature is W7's mirror: candidate gate at the `b`-side (`ρ(panelSupportExtensor n_b n'') ≠ 0`),
  `hLn` at `![n_b, n'']`; everything tied to the inductive `(ab)`-row (`ρ`, `hρe₀`, `hρGv` at
  `hingeRow a b ρ`, the `w` family) is **identical** to W7's, so W10 feeds both arms from one W6b
  invocation. The seven W7 hypotheses needing conversion all close in one tactic each: `hsplitG`
  reorders the first two disjuncts (`rcases … <;> exacts […]`); `hgab` swaps via
  `LinearIndependent.pair_symm_iff`; `hingeRow b a (−ρ) = hingeRow a b ρ` via `← hingeRow_swap`;
  the dual-evaluation gates via `LinearMap.neg_apply` + `panelSupportExtensor_swap` + `map_neg`
  (NOT `map_neg` alone — the `−` sits on the functional `(−ρ)`, see §44 below). Graph-free,
  axiom-clean, no §38 (the trap lives inside W7); no `\lean` pin.

### Promoted to TACTICS-QUIRKS / FRICTION
- *`rw [map_neg]` fails on `(-f) x` (functional-side negation) — use `LinearMap.neg_apply`* →
  TACTICS-QUIRKS § 44.
- *`set X := e with hX` folds `e` in pre-existing hypotheses too, so a later `rw [h]` (LHS was `e`)
  finds nothing* → TACTICS-QUIRKS § 43 (FRICTION [resolved] pointer).
- *A span/rigidity lemma applied with a heavy-carrier row-family argument `whnf`-times-out —
  `set f := <family>; clear_value f` first* → TACTICS-QUIRKS § 38 (*Row-family-argument variant*) +
  FRICTION [resolved].
