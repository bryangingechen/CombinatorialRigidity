# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** ✓ complete (closed 2026-06-11; opened 2026-06-09 at the 22g close).
**Close shape (user-adjudicated 2026-06-11): green-modulo the named carry family
{`h622`, `h65`, `hbase`, `hsplit`, `hcontract`} per §1.55(b)** — all five discharged by the
successor sub-phase 22i.

Took the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge), §1.49 (G5, G4a–G4e, G0, the (β) branch shape), §1.50 (the `hcand` discharge: the
discriminator, the rank-transfer re-route W1–W10, GAP 6), §1.51 (the W6-concrete
decomposition W6a–W6f + W7, exact signatures), §1.52 (W9a–W9c), §1.53 (W10a/W10b: the
ends-congruence pre-brick + the dispatch assembly, exact signatures), §1.54 (the Leaf-5
feed audit), and §1.55 (the user adjudications + the revised L5a′–L5e′ cut) — point at them,
don't duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**Closed.** Delivered, in order: G5 (predicate repair) → G4b-impl ((β) restate) → the §1.48/§1.49
leaves (T1–T4 triangle floor, G4a/G0/G4c/G4d) → the producer spine + the full `hcand` discharge
(W1–W10b, one W6b invocation feeding the three arm closers M₁/M₂/M₃) → Leaf 4 (`theorem_55_d3`)
→ the §1.54 feed audit + §1.55 adjudications → L5a′–L5d′ (blueprint honesty repairs, vacuity
discharge + `case_III_realization` wrapper, the 6.3-vs-6.5 dispatch,
`rankHypothesis_deficiency_of_theorem_55_d3` + `reaim`) → L5e′ (the blueprint close:
`thm:theorem-55-d3-instance` minted green; `lem:case-II-realization` / `lem:case-III` pinned to
`case_III_realization` and flipped; GAP-6 red node `lem:case-III-nested-rank-lower` minted;
`thm:theorem-55` stays red, re-summarized). All Lean axiom-clean
([propext, Classical.choice, Quot.sound]); build + lint + verify.sh green throughout.

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
- [x] **Discharge `hcand`** (the candidate-placement core; **§1.50/§1.51/§1.52/§1.53 canonical** —
  supersede the §1.49(5) arm route). **Landed** (per-leaf proof technique in *Decisions made*; exact
  signatures in design §1.51(c)–(i)/§1.52(c)–(d)/§1.53(c)): **W1**–**W6f**, **W7**
  `case_III_arm_realization` (M₁), **W8** `case_III_arm_realization_M2`, **W9a/W9b/W9c** (the M₃
  arm: `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` + `case_III_bottom_relabel` +
  `case_III_arm_realization_M3`), **W10a** `rigidityRows_ofNormals_congr_ends`, and **W10b**
  `case_III_candidate_dispatch` (the dispatch + discharge assembly matching the `hcand` signature;
  one W6b invocation feeds all three arms W7/W8/W9c off the `fin_cases u` discriminator). All
  axiom-clean ([propext, Classical.choice, Quot.sound]), no `\lean` pins (internal infra). GAP-6
  rides as the quantified `h622lb` hypothesis (consumed once, at the W6b call inside W10b).
- [x] **Leaf 4 (partial)** — `PanelHingeFramework.theorem_55_d3` (CaseI.lean): `theorem_55_generic
  (k:=2)` instance, `hsplitGP` wired via `case_III_hsplit_producer` +
  `case_III_candidate_dispatch`; projects `.2`; GAP-6 as quantified `h622`. The other five
  callbacks ride as hypotheses (their wiring + the blueprint instance node moved to Leaf 5 — see
  *Current state*). Build + lint clean.
- [x] **Leaf-5 feed audit (design §1.54, docs-only).** The five carried callbacks audited
  against the landed Lean; three hand-off expectations corrected (no graph-level base layer
  exists; the bare motive is degenerately satisfiable for every connected `0`-dof graph —
  one brick feeds `hbase`/`hsplit`/`hcontract`; `hcontractGP` needs the unformalized KT
  6.3-vs-6.5 dispatch + Lemma-6.5 arm). Leaf 5 re-cut into L5a–L5e below.
- [x] **L5a′** — the blueprint honesty repairs (docs-only; §1.55(c)): `def:rank-hypothesis`
  re-prosed to the Lean's actual strength (bare rank; welded-witness note; 22i obligation) +
  `def:genuine-hinge-realization` red node (KT honest form); `lem:case-I-realization` restated
  to carry `hcSimple` as the KT-6.3 case hypothesis + `lem:case-I-dispatch` red node (the 6.5
  arm). Lint + bp + web + checkdecls green. Done.
- [x] **L5b′** — `not_simple_of_isMinimalKDof_of_ncard_two` (§1.54(a1)) + the `theorem_55_d3`
  re-shape: `hbaseGP` discharged by vacuity; conclusion restated to `(Simple → GP) ∧ bare`;
  `case_III_realization` wrapper minted (§1.55(c)). Build + lint clean. Done.
- [x] **L5c′** — `hcontractGP` dispatch in `theorem_55_d3`: `by_cases` on simple-contraction
  existence; positive → `case_I_realization` (6.3 arm); negative → `h65` carry. `hcontractGP`
  param dropped; `h65` param added. Build + lint clean. Done.
- [x] **L5d′** — `rankHypothesis_deficiency_of_theorem_55_d3` + `reaim` micro-brick
  (CaseI.lean; §1.54(b)). Build + lint clean. Done.
- [x] **L5e′** — the blueprint close commit: instance node `thm:theorem-55-d3-instance`
  (pins `theorem_55_generic` + `theorem_55_d3` + the vacuity brick +
  `rankHypothesis_deficiency_of_theorem_55_d3`), `lem:case-II-realization`/`lem:case-III`
  both pinned to `case_III_realization` + flipped (§1.54(c)2 — the hand-off's
  `hasGenericFullRankRealization_of_case_II_realization` name never existed), the GAP-6 red
  node `lem:case-III-nested-rank-lower`, `thm:theorem-55` stays red (re-summarized, points at
  the instance node); the carried bare family presented per §1.55(b). Phase-close surfaces
  synced. Done.

## Blockers / open questions

None — the phase is closed. The five carries and their adjudications (GAP 6 / `h622`,
user 2026-06-10, §1.50(b) option (ii); the §1.54 decisions / `h65` + the bare family,
user 2026-06-11, §1.55 + `DESIGN.md` *Statement faithfulness to the source*) are recorded
in §1.55(b) and tracked by the blueprint red nodes `lem:case-III-nested-rank-lower`,
`lem:case-I-dispatch`, and `def:genuine-hinge-realization`.

## Hand-off / next phase

**Smallest next forward commit — open sub-phase 22i** ("the honest all-`k` Theorem 5.5"):
create `notes/Phase22i.md` **seeded with the carries table** (carry / red node / Lean
consumption site / discharge sub-plan — §1.55(b)'s structural fix for orphaned deferrals)
and run the single **motive design pass** (a §1.56-style block in
`notes/Phase22-realization-design.md`) pinning the all-`k` + genuine-hinge motive together.
22i scope (§1.55(a)): the all-`k` restructure + the genuine-hinge conjunct + the Lemma-5.3
graph-level base + the Lemma-6.2 non-simple branch + the Lemma-6.5 arm + the
`h622`/`h65`/bare-family discharges — delivering the KT-strength Thm 5.5 → 5.6 → Cor 5.7 at
`d=3`, unblocking Phases 24–26. Then **Phase 23** = general `d` (KT Lemma 6.13), scoped with
the §1.33 (C) reuse map; open it with its own recon (KT eqs. (6.46)–(6.67) vs the `d=3`
Lean) and add the general-`d` alg-independence row to `notes/AlgebraicIndependence.md`.

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
- **G4a-i** `exists_adjacent_degree_two_pair`: incFun double-count via `Finset.sum_comm`;
  numeric finale `zify` + `nlinarith`. Settled; detail in git + the Lean.
- **G4a-ii** `exists_chain_data_of_noRigid`: `same_right` endpoint helper; 4-way case split
  avoiding `subst` on shared names. Settled.
- **T3** `exists_triangle_normals`: 4 private helpers against `whnf`-context explosion;
  proof-term-mismatch pattern promoted (TACTICS-QUIRKS § 42). Settled.
- **G4c-i** `splitOff_isLink_relabel`: `subst`-direction caveat (promoted, § 4); explicit
  `calc` chains over `swap_apply_*` instead of `simp_all`. Settled.
- **G4c-ii corrected to fixed-seed (design-deviation fix; replaced b6a66de):** producer-direction
  transport at the fixed seed `q₀∘ρ` + the `rigidityRows` row correspondence, per §1.49(3)/(4)
  (the reversed existential transport b6a66de built is excluded there). Settled.
- **Statement-level `Equiv.swap` opacity:** inline explicit terms in statements, `set` them back
  in the body; `change` (not `show`) for the defeq exposures. → FRICTION.md [let-opacity].
- **T4** `hasGenericFullRankRealization_of_triangle`: ±Cᵢ 8-way sign dispatch via
  `endsOf_eq_or_swap` + a `Pi.smul`-form LI helper. Settled.
- **Producer corrected to the `hsplitGP` shape (corrective commit replacing 9c5879c):** (β) hands
  the no-rigid branch the **full conditioned IH** (§1.49(1)); bare-IH restate orphans `hgab`
  (§1.41(1)/§1.47). `G.Simple` + conditioned IH in, generic motive out; R3 discharges the split's
  GP antecedent at `|V| ≥ 4`; `|V| = 3` routes to T4. Settled.
- **GAP-3 good-`t`** `exists_shear_linearIndependent_pair` (PanelLayer.lean): bad-`t` set is a
  subsingleton; `t = 1` or `2` is good. Settled (see also *Blockers* GAP 3).
- **`hcand`-discharge recon (design §1.50; docs-only):** discriminator restate free; §1.49(5) arm
  route undischargeable → KT-Lemma-5.2 rank-transfer re-route; GAP 6 surfaced. Canonical: §1.50.
- **Claim-6.12 → witness-meet glue** `exists_complementIso_ne_zero_of_homogeneousIncidence`
  (RigidityMatrix.lean): three-line composition; `Subtype.ext` lift idiom. Settled.
- **W2** `finrank_span_rigidityRows_of_rigidOn` (GenericityDevice.lean — the honest home, beside
  its sole dependency); the two `_subfamily_of_rigidOn` sites refactored onto it. Settled.
- **W3** `LinearIndependent.exists_notMem_of_polynomial_repr` + the general-polynomial engine
  `Matrix.finite_setOf_not_linearIndependent_rows_of_polynomial` (`Mathlib/` mirror). Settled.
- **W4** `linearIndependent_sum_restriction_block` (RigidityMatrix.lean): transposed sibling of
  `_pinned_block`; pointwise `LinearMap.ext` for the missing `sum_comp`. Settled.
- **W6-core** `linearIndependent_sum_augment_candidateRow_restriction`: the restriction-bottom
  sibling, fed to W4 through the same `columnOp` transport. Settled.
- **W5** `exists_redundant_panelRow_ab_lam_of_rigidOn` (CaseI.lean): `h618` ← W2; `h622` by
  construction (`k' := D(m−1) − fGv`, `omega` against the carried `h622lb`). Settled.
- **W6-concrete decomposed (design §1.51; docs-only):** seven exact-signature leaves W6a–W6f + W7;
  the §1.50(c) route corrected to **certify-then-rebase**; GAP-6 isolated to W6b + W10.
  Canonical: §1.51.
- **W6a** `caseIIICandidate` (a `BodyHingeFramework` with two `Function.update`d extensor slots)
  + the affine-in-`t` row lemma + infra bricks. Settled; `columnOp_apply` post-coercion
  friction → FRICTION [resolved].
- **W6e** `exists_independent_panelRow_subfamily_of_le_finrank` (GenericityDevice.lean); the
  `_of_rigidOn_linking` consumer refactored to its 3-line corollary. Settled.
- **W6b** `exists_candidateRow_bottomRows_of_rigidOn` (CaseI.lean) — **W5's sole caller; `h622lb`
  enters here.** `set`-folding friction → TACTICS-QUIRKS § 43. Settled.
- **W6f** `caseIIICandidate_exists_good_shear`: near-verbatim W3 instantiation. Settled.
- **W6d** `case_III_rank_certification`: W6c at `F₀` with W6b's data; consumed by W7. Settled.
- **W7** `case_III_arm_realization` (the M₁ arm closer): five-step route; the named-`he`
  dispatch discipline (never `rcases … rfl`, § 4) and the row-family `whnf` rescue
  (`set f := <family>; clear_value f`, § 38). Settled.
- **W8** `case_III_arm_realization_M2`: one-`refine` W7 instantiation at swapped roles with
  `ρ' := −ρ`; `LinearMap.neg_apply` for the functional-side negation (§ 44). Settled.
- **W9 relabel bridge** `hingeRow_funLeft_dualMap` (RigidityMatrix.lean; the live-route leaf) +
  `mem_span_rigidityRows_ofNormals_relabel` (landed, off the route per §1.52(e)). Settled.
- **W9 design pass (§1.52, docs-only):** W9 IS a W7-instantiation at `Gv := G.removeVertex a`,
  seed `qρ`; M₃ data transports pointwise from the one v-split W6b invocation (no second GAP-6).
  Canonical: §1.52.
- **W9a** `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`: heavy-carrier `span_induction`
  bundled as one `LinearMap` transport (§ 38, *span_induction variant*). Settled.
- **W9b** `case_III_bottom_relabel`: disjunction-in/out per-tag transport; explicit-witness
  membership discipline throughout. Settled.
- **W9c** `case_III_arm_realization_M3`: one-`refine` W7 instantiation at the relabeled roles;
  `hρe₀` via G4d-i, `hρGv` via W9a, `hwmem` via W9b. Settled.
- **W10 design pass (§1.53, docs-only):** W10a/W10b signatures + three §1.51(i) corrections
  (normalize W6b outputs, never rename `(a,b)`; `h622lb` quantified; M₃'s third selector
  override). Canonical: §1.53.
- **W10a** `rigidityRows_ofNormals_congr_ends`: link-agreeing selectors give equal row sets.
  First-try clean. Settled.
- **W10b** `case_III_candidate_dispatch`: the `hcand`-matching dispatch assembly; one W6b
  invocation, W8-pattern normalization, `fin_cases u` → W7/W8/W9c; M₁/M₂ rows via the W10a
  congruence. Friction promoted (§§ 45/46/38). Settled.

- **L5e′ phase-close re-read catch — `lem:case-II-realization-placement` restated honest:** the
  red node claimed the *full* `D(|V|−1)` family while the landed Lean (`case_II_placement_eq612`,
  22c) and every live consumer treat it as the one-row-short `D(|V|−1)−1` brick; restated at
  stratum-1 strength, pinned + flipped green. Also collapsed accreted status narration in the
  case-iii candidate-completion intro and the genericity-and-count device intro ("deferred to
  Phase 22b" rot).
- **L5b′ vacuity discharge of `hbaseGP`:** `not_simple_of_isMinimalKDof_of_ncard_two` proves a
  simple minimal-`0`-dof graph on 2 vertices cannot exist (two-edge-connectivity gives ≥2 crossing
  edges; simplicity forces them equal — contradiction). Discharged in `theorem_55_generic`'s
  `hbaseGP` slot as `fun G hG hV2 hSimple => absurd hSimple (not_simple … (by omega) hG hV2)`.
  `case_III_realization` extracts the inline `hsplitGP` wiring from `theorem_55_d3` into a named
  declaration (§1.55(c)). Conclusion restated from bare `.2`-projection to the full conditioned
  pair `(Simple → GP) ∧ bare`; `hbase`/`hsplit`/`hcontract`/`hcontractGP` still ride as carries.
- **L5d′ `reaim` + `prop11` feed:** `reaim` rebuilds `Q′ = ⟨G, Q.normal, ends′⟩` with
  `ends′ = Q.ends` on links and `(x₀, y₀)` on non-links (classical decidability via `haveI`).
  `reaim_infinitesimalMotions` via `infinitesimalMotions_eq_of_isLink_supportExtensor` (motion
  space = links only). `hC` from GP + link-recording (`rcases hQrec`) + looplessness (`hle.ne`)
  on links, GP on `(x₀, y₀)` off-links. `hgen` from `finrank_…_of_isInfinitesimallyRigidOn_vertexSet`
  + `hspan` (complement ncard = 0 → `dim Z = D`). `_hSimple` carried but mechanically unused
  (GP witness already embeds the simple-case entry). No friction.
- **L5c′ dispatch shape:** `hcontractGP` in `theorem_55_d3` wired via `by_cases hd : ∃ H r,
  H.IsProperRigidSubgraph G n ∧ r ∈ V(H) ∧ (G.rigidContract H r).Simple`; positive →
  `case_I_realization (by omega) G hG hH hr hH.2.1 hSimple hcSimple hIH`; negative →
  `h65 G hG hV3 hrig hSimple (fun H hH r hr hcs => hd ⟨H, r, hH, hr, hcs⟩) hIH`. `h65`
  type carries the "all-rigid-subgraph-contractions-are-non-simple" antecedent. No friction.
- **Leaf-5 feed audit (§1.54, docs-only; supersedes the §1.41(5) "six green/green-modulo branch
  args" expectation).** Verdicts: no graph-level base layer exists (Pinning.lean's
  `theorem_55_base` is framework-level); `hbaseGP` vacuous (parallel-pair cut bound);
  `HasFullRankRealization` is degenerately satisfiable for every connected `0`-dof graph (zero
  extensors weld — adjudicated: strengthen at 22i, carry the bare slots; §1.55);
  `hcontractGP` needs the unformalized KT 6.3-vs-6.5 dispatch (`hcSimple` is a *case
  hypothesis`; dispatch lands L5c′; the 6.5 arm defers to 22i behind `h65`); the Thm
  5.5→5.6 push at 22h-close is the `def = 0`/simple/spanning stratum (full Thm 5.6 = the
  all-`k` GAP-6 successor). Exact wiring/signatures + the blueprint plan: §1.54(a)–(d).

### Promoted to TACTICS-QUIRKS / FRICTION
- *A multi-branch `span_induction` over a heavy `Module.Dual` span hits the cumulative heartbeat
  budget — bundle the transport as one `LinearMap` `T` + per-branch `simp only`* → TACTICS-QUIRKS § 38
  (*`span_induction` variant*) / FRICTION [resolved].
- *`rw [map_neg]` fails on `(-f) x` (functional-side negation) — use `LinearMap.neg_apply`* →
  TACTICS-QUIRKS § 44.
- *`set X := e with hX` folds `e` in pre-existing hypotheses too, so a later `rw [h]` (LHS was `e`)
  finds nothing* → TACTICS-QUIRKS § 43 (FRICTION [resolved] pointer).
- *`subst h` (h : x = a) eliminates the section body `a`, not the local `x`; use the named-variable
  form `subst x` to steer the direction* → TACTICS-QUIRKS § 4 (FRICTION [resolved] pointer).
- *A span/rigidity lemma applied with a heavy-carrier row-family argument `whnf`-times-out —
  `set f := <family>; clear_value f` first* → TACTICS-QUIRKS § 38 (*Row-family-argument variant*) +
  FRICTION [resolved].
- *A combining-diacritic identifier (`ρ̂` = base char + U+0302, vs the precomposed glyph) is
  rejected mid-proof — "expected token"; rename to ASCII-decorated (`ρ0`)* → TACTICS-QUIRKS § 45.
- *`Matrix.cons_val_*` won't fire on `![…] ⟨0, ⋯⟩` after `fin_cases` (a `Fin.mk`, not the literal) —
  add `show (⟨0,_⟩ : Fin n) = 0 from rfl` to the `simp only` set first, per branch* → TACTICS-QUIRKS § 46.
