# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge), §1.49 (G5, G4a–G4e, G0, the (β) branch shape), §1.50 (the `hcand` discharge: the
discriminator, the rank-transfer re-route W1–W10, GAP 6), §1.51 (the W6-concrete
decomposition W6a–W6f + W7, exact signatures), §1.52 (W9a–W9c), §1.53 (W10a/W10b: the
ends-congruence pre-brick + the dispatch assembly, exact signatures), and §1.54 (the Leaf-5
feed audit + the L5a–L5e cut) — point at them, don't duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**Next concrete step: obtain the two §1.54 user decisions** (the degenerate-bare-motive
sign-off + the Lemma-6.5 (A)-build-vs-(B)-carry scope call — see *Blockers*), **then L5a**
(the two base/degenerate bricks). The Leaf-5 feed audit (§1.54, 2026-06-11) corrected three
hand-off expectations and re-cut Leaf 5 into **L5a–L5e** (≈5 commits on route (B), ≈9–11 on
route (A)); phase close stays green-modulo-`h622` (+ `h65` on route (B)).

**Leaf 4 landed PARTIALLY instantiated** (`PanelHingeFramework.theorem_55_d3`, CaseI.lean):
instantiates `theorem_55_generic` at `k = 2` with `hsplitGP` wired via `case_III_hsplit_producer`
+ `case_III_candidate_dispatch`; projects `.2` for the bare motive; GAP-6 carries as the
quantified `h622` hypothesis (exact form per §1.53(f), quantifying over `(G,v,a,b,e₀,ends,q)`).
Build + lint clean. **Two pinned sub-clauses of the original Leaf-4 item were NOT delivered and
now belong to the L5 leaves:** (i) the five remaining callbacks (`hbase`/`hbaseGP`/`hsplit`/
`hcontract`/`hcontractGP`) ride as *hypotheses* — feeds now audited and pinned in §1.54(a);
(ii) no blueprint instance node was minted (→ L5e).

**All §1.48/§1.49 leaves AND the entire `hcand` discharge (W1–W10b) are landed** — the producer
spine `case_III_hsplit_producer` (CaseI.lean; carries the open core as its `hcand` parameter) and
the dispatch assembly `case_III_candidate_dispatch` that matches and discharges it. The discharge
is the discriminator (`fin_cases u` over the §1.53 selector, KT eqs. (6.24)–(6.44)) dispatching to
the three role-parametric arm closers (`case_III_arm_realization` M₁ / `_M2` / `_M3`), all fed off
*one* W6b invocation (one redundancy, one GAP-6 consumption). Per-leaf proof technique:
*Decisions made* + git history; exact signatures: design §1.51–§1.53. Build + lint + verify.sh
clean throughout; axiom-clean ([propext, Classical.choice, Quot.sound]). GAP-6 rides as the
quantified `h622lb` hypothesis (§1.50(b) option (ii); see Blockers).

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
- [ ] **L5a** — the two base/degenerate bricks (`hasFullRankRealization_of_isKDof_zero`,
  `not_simple_of_isMinimalKDof_of_ncard_two`; §1.54(a1)/(a2)). **Gated on the user's (a2)
  sign-off.**
- [ ] **L5b** — rewire `theorem_55_d3`: feed `hbase`/`hbaseGP`/`hsplit`/`hcontract`; restate
  the conclusion to the full `(Simple → GP) ∧ bare` pair; mint the named
  `case_III_realization` wrapper (§1.54(d)).
- [ ] **L5c** — the `hcontractGP` arm per the user's scope call: (A) Claim 6.6 + the
  Π°-placement producer + dispatch (~4–6 commits, §1.54(a3)) or (B) one commit carrying the
  named `h65` hypothesis + the 6.3-arm feed.
- [ ] **L5d** — the Thm 5.5→5.6 push, `def = 0`/simple/spanning stratum
  (`rankHypothesis_deficiency_of_theorem_55_d3` + the off-edge selector re-aim micro-brick;
  §1.54(b)). The `def > 0` push is post-22h (needs the all-`k` GAP-6 successor, already
  adjudicated).
- [ ] **L5e** — the blueprint commit: instance node `thm:theorem-55-d3-instance`,
  `lem:case-II-realization`/`lem:case-III` pins + flips, the GAP-6 red node
  `lem:case-III-nested-rank-lower`, `thm:theorem-55` stays red (§1.54(c)).

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
- **USER DECISION 1 (§1.54(a2)) — the degenerate bare-motive route.** `HasFullRankRealization`
  carries no genuine-hinge condition, so a zero-extensor (welded) framework discharges
  `hbase`/`hsplit`/`hcontract` in one brick — sound Lean, but it makes `thm:theorem-55`'s bare
  conjunct mathematically vacuous (the content lives in the GP conjunct, which is all the
  capstone consumes). §1.54 recommends landing it now and folding the genuine-hinge motive
  strengthening into the all-`k` GAP-6 successor re-design. Awaiting sign-off.
- **USER DECISION 2 (§1.54(a3)) — the Lemma-6.5 arm scope.** `hcontractGP` is NOT
  `case_I_realization` alone: the KT 6.3-vs-6.5 dispatch on `(G.rigidContract H r).Simple` is
  unformalized, and the 6.5 arm (Claim 6.6 + the Π°-placement) is bounded new work (~4–6
  commits, no research risk — bricks all landed). Option (A) build in-phase; option (B) close
  green-modulo a second named carry `h65`. Changes the phase-close estimate.

## Hand-off / next phase

**Smallest next forward commit — L5a (the two base/degenerate bricks, §1.54(a1)/(a2),
exact signatures pinned there), once the two §1.54 user decisions land** (see *Blockers*:
the degenerate-bare-motive sign-off gates L5a; the Lemma-6.5 (A)-vs-(B) scope call sizes
L5c). The feed audit is done (§1.54, 2026-06-11): all five callback feeds are pinned or
gap-recorded against the landed Lean — `hbase`/`hsplit`/`hcontract` off the one degenerate
brick, `hbaseGP` by the parallel-pair vacuity, `hcontractGP` = the 6.3 arm
(`case_I_realization`, exact adaptor in §1.54(a3)) + the open 6.5 arm/dispatch. Build order
L5a → L5b → L5c → L5d → L5e per the checklist above; the Π°-placement producer (L5c route
(A) only) needs its own §1.53-style signature pin before building. Phase close
green-modulo-`h622` (+ `h65` on route (B)). **No `sorry`** at any step.

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

- **Leaf-5 feed audit (§1.54, docs-only; supersedes the §1.41(5) "six green/green-modulo branch
  args" expectation).** Verdicts: no graph-level base layer exists (Pinning.lean's
  `theorem_55_base` is framework-level); `hbaseGP` vacuous (parallel-pair cut bound);
  `HasFullRankRealization` is degenerately satisfiable for every connected `0`-dof graph (zero
  extensors weld — one brick feeds all three bare callbacks, user sign-off pending);
  `hcontractGP` needs the unformalized KT 6.3-vs-6.5 dispatch (`hcSimple` is a *case
  hypothesis*; the 6.5 arm = Claim 6.6 + Π°-placement, bounded, ~4–6 commits); the Thm
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
