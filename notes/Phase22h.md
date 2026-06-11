# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge), §1.49 (G5, G4a–G4e, G0, the (β) branch shape), §1.50 (the `hcand` discharge: the
discriminator, the rank-transfer re-route W1–W10, GAP 6), §1.51 (the W6-concrete
decomposition W6a–W6f + W7, exact signatures), §1.52 (W9a–W9c), and §1.53 (W10a/W10b: the
ends-congruence pre-brick + the dispatch assembly, exact signatures) — point at them, don't
duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**Next concrete step: Leaf 4** — the `theorem_55_generic (n:=2) (k:=2)` instance node over the
(β) shape, whose `hsplitGP` wiring lambda is the positional application of W10b's
`case_III_candidate_dispatch` (the §1.53(c) lambda) and whose statement gains the fully-quantified
GAP-6 hypothesis (quantifying additionally over `(v,a,b,e₀)` + the graph; exact form pinned at the
Leaf-4 moment from §1.53(c)). Then Leaf 5 → phase close **green-modulo-GAP-6**. Design §1.53(f) is
canonical for both leaves; the per-arm wiring of the now-landed dispatch is §1.53(d).

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

**Smallest next forward commit — Leaf 4, the `theorem_55_generic (n:=2) (k:=2)` instance node over
the (β) shape.** Its `hsplitGP` wiring lambda is the positional application of the now-landed
`case_III_candidate_dispatch` (the §1.53(c) lambda); the leaf's *statement* gains the
**fully-quantified GAP-6 hypothesis** — quantifying additionally over `(v,a,b,e₀)` + (per its
wiring shape) the graph — whose exact form is pinned at the Leaf-4 moment from §1.53(c)'s
per-instantiation `h622lb` shape. Build against §1.53(f). **No `sorry`** at any step (carry GAP-6
as the named `h622lb`, never a `sorry`). Then Leaf 5 (the `lem:case-II-realization`/`lem:case-III`
flips + Thm 5.5→5.6 push) → phase close **green-modulo-GAP-6**.

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
- **W6d the `t = 0` rank certification (§1.51(e); `case_III_rank_certification`, CaseI.lean).** Feed
  W6c at `F := F₀` with W6b's data: bottom transport per-tag through bricks 1/2, candidate/sn
  memberships via the `hrow_mem` explicit-witness idiom (§38-clean), the eq.-(6.27) collapse
  (`← hingeRow_sub_hingeRow_eq`, `Sum.elim` projection by `change`), and the
  `((D−1)+1)+D(m_v−1) = D·m_v` count (`Nat.mul_succ` + `omega`). Consumed by W7; full route in git +
  the Lean. GAP-6-clean (carried in W6b); axiom-clean; no `\lean` pin.
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
- **W9 relabel row-transport bridge (§1.50(e) step (3); `hingeRow_funLeft_dualMap` +
  `mem_span_rigidityRows_ofNormals_relabel`).** Two abstract leaves. (1) `hingeRow_funLeft_dualMap`
  (RigidityMatrix.lean, after `hingeRow_swap`): `(funLeft ρ).dualMap (hingeRow u v r) =
  hingeRow (ρ u)(ρ v) r` for **any** `ρ : α → α` (no involution needed — cleaner than the `ρ∘ρ=id`
  `hdual` inlined in `rigidityRows_ofNormals_relabel`); proof = `LinearMap.ext` + 4-`rw`
  (`dualMap_apply`/`hingeRow_apply`×2/`funLeft_apply`×2). (2)
  `mem_span_rigidityRows_ofNormals_relabel` (CaseI.lean, with the relabel group): `φ ∈ span(v-split
  rows) → (funLeft (swap a v)).dualMap φ ∈ span(a-split rows)`, by rewriting through
  `rigidityRows_ofNormals_relabel` (rows = dualMap-image) + `Submodule.span_image` (span of image =
  `map` of span) + `Submodule.mem_map_of_mem`. Both first-try clean (no friction); both
  axiom-clean, no `\lean` pin. *Consumption correction (§1.52(e)):* the live W9 route consumes
  only `hingeRow_funLeft_dualMap` (via W9a/W9b); the span-level bridge's `span(a-split)` target is
  the wrong home (the `e₁`-block can't be stripped post hoc) — it stays landed, off the route.
- **W9 design pass (§1.52, docs-only; supersedes the 365740b "not-a-W7-instantiation" finding).**
  W9 IS a W7-instantiation: `Gv`-slot `G.removeVertex a` (the §1.51(i) "relabeled split minus its
  short-circuit edge", a subgraph of `G`), seed `qρ`, `ρ̃ := −ρ`. The M₃ data transports pointwise
  from the one v-split W6b invocation (KT (6.35)–(6.41): `R(G,p₃)`'s bottom block IS the v-split
  matrix; no a-split realization, no second GAP-6; re-derivation routes are strictly dominated —
  §1.52(a)). New leaves W9a/W9b/W9c with exact signatures in §1.52(b)–(d); `hρe₀` via G4d-i,
  `hρGv` via W9a; `ofNormals_relabel` suite / G4d-ii / `candidateRow_ac_eq_neg` off the live
  route (ledger + phase-close blueprint obligation: §1.52(e)).
- **W9a the short-circuit-free relabel span-induction (§1.52(b);
  `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, CaseI.lean, beside G4d-i).** The §1.52(b)
  signature, minus the listed `hva : v ≠ a` (the proof doesn't use it — the `x=a`/`y=a` branch
  contradictions close on `Ne.symm hca`/`hxa`; a discretionary signature tweak per CLAUDE.md, not a
  design deviation). The heavy carrier `Module.Dual ℝ (α → ScrewSpace k)` made the naive 3-branch
  `span_induction` with chained big-carrier `rw`s exhaust the 200000 cumulative budget; fixed §38-style
  by (1) bundling the transport as one `LinearMap` `T` (light predicate `T ψ ∈ span …`, so
  `zero/add/smul` close by `map_*` + `Submodule.*_mem`) and (2) consolidating each generator sub-case's
  post-substitution rewrites into a single `simp only`. Axiom-clean ([propext, Classical.choice,
  Quot.sound]); no `\lean` pin.
- **W9b the per-member bottom tag transport (§1.52(c); `PanelHingeFramework.case_III_bottom_relabel`,
  CaseI.lean, after W9a).** Disjunction-in / disjunction-out: the input tag is a genuine `Fv`-row or
  an `(ab)`-block `hingeRow a b ρ'`; output is a genuine `Fva = ofNormals (G−a) ends₃ qρ`-row or a
  `(c,v)`-block `hingeRow c v ρ'`. The `(ab)`-tag relabels (`hingeRow_funLeft_dualMap`, swap fixes
  `b`) to the genuine `e_b`-row (`ends₃ e_b = (v,b)`, `qρ(v,·)=q(a,·)`, `qρ(b,·)=q(b,·)`). The
  `Fv`-row tag case-splits on `a ∈ {x,y}` (the G4d-i skeleton; `hdeg2` *derived* from `hGv_le` +
  `hcla`, the `f=e_a` branch killed by link-uniqueness vs `hG_ea` + `hnov`): the `x=a`/`y=a` cases
  go RIGHT (`ρ' = ∓r`, annihilation from `r ⊥ Fv.supportExtensor e_c` + `hrecGv` + an even number of
  `panelSupportExtensor_swap`/`neg`); the off-case goes LEFT (swap fixes `x,y∉{a,v}`, the genuine row
  survives `removeVertex` and its `Fva`/`Fv`-extensors coincide via `hends₃_off` + `hrecGv`). The
  output LEFT disjunct is *set* membership in `Fva.rigidityRows` (not `span`). §38: every membership
  an explicit `⟨e,u,v,…⟩` witness; every extensor eval through `toBodyHinge_supportExtensor` /
  `ofNormals_{ends,normal}` + the swap lemmas, never `whnf`. Axiom-clean; no `\lean` pin.
- **W9c the M₃ arm closer (§1.52(d); `PanelHingeFramework.case_III_arm_realization_M3`, CaseI.lean,
  after G4d-ii).** One-`refine` instantiation of W7 at roles `(v,a,b,e_a,e_b,n') :=
  (a,c,v,e_c,e_a,n''')`, `Gv := G.removeVertex a`, `q := qρ`, `ρ̃ := −ρ`,
  `w̃ := (funLeft (swap a v)).dualMap ∘ w`; W7's 22 hyps discharged in `case` blocks. Seed slots by
  `swap_apply_of_ne_of_ne`/`_right`; `hρe₀` (`ρ ⊥ C(q(ac))`) via **G4d-i** + `mem_hingeRowBlock_iff`
  + the `hrecGv` sign split; `hρGv` via **W9a** at `φ := hingeRow a b ρ` (image `hingeRow v b ρ`,
  then `Submodule.sub_mem` vs the genuine `e_b`-row + `sub_sub_cancel`; W9a's `htrans` off-case = the
  `hends₃_off`/`hrecGv` agreement of W9b's); `hwmem̃ := W9b ∘ hwmem` after `simp [Function.comp_apply,
  hqρc, hqρv]`; `hw̃` by `LinearIndependent.map'` + `funLeft`/`dualMap` swap-injectivity; `hwcard` by
  `ncard_diff_singleton_of_mem` + `Nat.sub_sub`. `[DecidableEq α]` kept (statement `Equiv.swap a v`).
  Axiom-clean; no `\lean` pin.
- **W10 design pass (§1.53, docs-only; canonical for W10a/W10b — supersedes §1.51(i)'s prose route,
  resolves §1.52(e)'s deferral).** Two leaves: W10a `rigidityRows_ofNormals_congr_ends` (own
  micro-commit; needed only by the M₁/M₂ `hρGv`/`hwmem` feeds — `hends_Gv`/`hne_Gv` reduce by
  `update_of_ne`, W9c needs no congruence) + W10b `case_III_candidate_dispatch` (matches `hcand` +
  `hsimple` + GAP-6). Three §1.51(i) corrections: recorded-`(b,a)` order → *normalize* the W6b
  outputs (`ρ̂ := -ρ`, the W8 pattern), never rename `(a,b)` (chain roles are `u`-dispatch-pinned);
  `h622lb` enters *quantified* over `(ends, q)`, conditioned on {recordsLinks, seed-GP, alg-indep}
  (the seed is bound inside `hsplitGP`); M₃'s `ends₃` overrides *three* edges (`e_c ↦ (a,c)` too).
- **W10a the ends-congruence pre-brick (§1.53(b); `PanelHingeFramework.rigidityRows_ofNormals_congr_ends`,
  CaseI.lean, before the triple-LI bridge).** Two `ofNormals` frameworks on the *same* `G`/`q`
  whose `ends`/`ends'` agree on every `G`-link have equal `rigidityRows` sets. Proof = a `hsupp`/
  `hblock` pair (on links the support extensor — read through `toBodyHinge_supportExtensor` +
  `ofNormals_ends`/`ofNormals_normal` + `rw [hagree …]` — hence the `(span C)^⊥` block coincide) then
  `Set.eq_of_subset_of_subset`, each direction re-providing the same `⟨e,u,v,hlink,r,…⟩` witness
  (`hingeRow u v r` is `ends`-free; the framework-graph `IsLink` is defeq to `G.IsLink`). No
  `change`/glue, no §38; first-try clean, no friction. Axiom-clean; no `\lean` pin.
- **W10b the dispatch + discharge assembly (§1.53(c)/(d); `PanelHingeFramework.case_III_candidate_dispatch`,
  CaseI.lean, file tail after the triple-LI bridge).** Matches `hcand`'s shape (+ `hsimple` + the
  quantified `h622lb` GAP-6 carry), concludes the generic motive. Route per §1.53(d): unpack
  `hsplitGP` via the `hQeq` idiom; inline graph facts (`he₀ab`/`hle`/`hsplit`/`hGv_off`/`hV4`/
  `hcard`/`hgp_seed`); **one** W6b invocation (`h622lb Q.ends q …` the single GAP-6 consumption);
  normalize the W6b outputs to chain order `(a,b)` (the W8 sign-swap pattern, `ρ0 := ±ρ` per
  `rcases hrec' e₀ a b he₀ab`); the discriminator (`linearIndependent_normals_of_algebraicIndependent`
  → `exists_homogeneousIncidence_of_normals` → `exists_complementIso_ne_zero_…`, then `←
  panelSupportExtensor_eq_complementIso_extensor`); `fin_cases u` → W7 (`u=0`) / W8 (`u=1`) /
  W9c (`u=2`). M₁/M₂ consume the W6b row sets at the override `ends₁` via the W10a congruence
  `rw [← hcongr]`; M₃ at `Q.ends` directly. Two `Gv`/`(G−a)` `Loopless` instances (from `hsimple`
  via `Loopless.mono`) feed the `hne_Gv*` nonvanishing (`.ne`). Friction: the `ρ̂`/`ŵ` combining-
  diacritic rename (§45), the `fin_cases`-index `Fin.mk` normalization (§46), and the M₃
  `hGPva` `simp only [ofNormals_normal, hqρ]` (not `rw` — §38 whnf trap on the relabeled carrier).
  Axiom-clean ([propext, Classical.choice, Quot.sound]); no `\lean` pin (internal infra).

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
