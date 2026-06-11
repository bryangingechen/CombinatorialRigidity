# Phase 22h — the corrected `d=3` assembly (work log)

**Status:** in progress (opened 2026-06-09 at the 22g close).

Takes the two producer nodes `lem:case-II-realization` / `lem:case-III` green at `d=3` by building
the corrected remaining-work picture the 22g recon program scoped (GAPs 1–5). **Per-leaf
signatures stay canonical in `notes/Phase22-realization-design.md` §1.48 (T1–T4, the triple-LI
bridge), §1.49 (G5, G4a–G4e, G0, the (β) branch shape), and §1.50 (the `hcand` discharge: the
discriminator, the rank-transfer re-route W1–W10, GAP 6) — point at them, don't duplicate.**
22g's archive (delivered leaves + settled verdicts): `notes/Phase22g.md`.

## Current state

**All §1.48/§1.49 leaves are landed** — G5, G4b-impl, G4a-i/ii + G0, T1–T4, G4c-i/ii, G4d-i/ii,
the (β)-shaped producer spine `case_III_hsplit_producer` (CaseI.lean; carries the open core as
its `hcand` parameter), the triple-LI bridge, the GAP-3 good-`t` core
`exists_shear_linearIndependent_pair`, and the Claim-6.12 → witness-meet glue
`exists_complementIso_ne_zero_of_homogeneousIncidence`. Per-leaf detail: the checklist below
(lemma + file + blueprint node), *Decisions made* (proof techniques), and the design §refs.
Build + lint + verify.sh clean throughout; axiom-clean.

**The `hcand`-discharge recon is DONE (design §1.50 — canonical for ALL remaining work;
supersedes the §1.49(5) M-arm route).** (1) The witness-normal discriminator is a free in-place
restate of the line-data lemma + the glue (proofs reuse). (2) The sheared-placement arm route is
undischargeable (it breaks KT's (6.26)–(6.28) row transport) — re-routed via KT Lemma 5.2:
certify the (6.29) count at the `t = 0` hinge-level `BodyHingeFramework` `F₀` (memberships hold
by construction), transfer along the shear by a one-variable minor polynomial; the previously
planned sheared-support step is obsolete. (3) GAP 6 surfaced and **adjudicated** — see Blockers.
Coordinator independently verified all three verdicts against KT pp. 681–684 + the Lean
(model-experiment row 20).

**Next concrete step:** W5 — the redundancy-data packaging at the unpacked IH framework (§1.50(b)/(f)):
`exists_redundant_panelRow_ab_lam` + W2's `finrank_span_rigidityRows_of_rigidOn` + the (b)
`k''`-reduction, **taking the GAP-6 inequality as an explicit hypothesis** (adjudicated carry —
Blockers). Output the redundancy data `r`/`lam`/`i*`/`r̂ ≠ 0`/`hingeRow a b r̂ = wGv ∈ span(Gv-rows)`.
W4 (leaf A0, the restriction-bottom block-triangular augment) is **landed** —
`BodyHingeFramework.linearIndependent_sum_restriction_block` (RigidityMatrix.lean): the transposed
sibling of `linearIndependent_sum_pinned_block` — `Sum.elim top bot` LI when the `top` rows are
pure-`v` (`htopvanish`, vanish on every `S v = 0`) with pinned-independent `v`-forms (`htoppin`) and
the `bot` rows' restrictions to `V∖{v}` are independent (`hbotrestrict`, composites with the off-`v`
projection `P_v = id − single v ∘ proj v`). Proof: evaluate a vanishing combination at `P_v S` to kill
`top`, recover the `bot` coefficients by `hbotrestrict`; pin to `v`'s column to recover the `top`
coefficients by `htoppin`. Graph-free, no §38 trap; no `\lean` pin (internal infra). W3/W2/W1 landed
before it.

**Build order (§1.50(f); supersedes §1.49(6) item 5's discharge clause):** ~~W1 discriminator~~ (done)
→ ~~W2 `h618` micro-leaf~~ (done) → ~~W3 leaf B (rank transfer)~~ (done) → ~~W4 leaf A0 (restriction-bottom
augment)~~ (done) → W5 redundancy packaging (**introduces the carried GAP-6 hypothesis**) → W6/W7 M₁ →
W8 M₂ → W9 M₃ → W10 dispatch + discharge assembly (matches `hcand`'s shape) → Leaf 4 → Leaf 5 →
phase close, **green-modulo-GAP-6**.

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
  graph-free). Remaining, as complete lemmas (no `sorry` on master),
  per §1.50(f): W5 redundancy packaging (carries the GAP-6 inequality as the adjudicated explicit
  hypothesis — Blockers) → W6/W7 M₁ (`t = 0` certification at `F₀` + closer) → W8 M₂ → W9 M₃ (G4c/G4d +
  `candidateRow_ac_eq_neg`) → W10 dispatch + assembly matching the `hcand` signature.
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
- **GAP 3 — core LANDED** (`exists_shear_linearIndependent_pair`, PanelLayer.lean): consumed by
  leaf B's good-`t` choice (§1.50(c), the `bad`-set input).
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites every
  carrier-instantiating leaf (the producer body, the T3/T4 seeds). Keep reasoning over abstract
  `F`; instantiate only at the seed. The §1.50 re-route helps: `F₀` and leaves A0/B are abstract /
  graph-free.
## Hand-off / next phase

**Smallest next forward commit — W5, the redundancy-data packaging (§1.50(b)/(f)).** At the
unpacked IH framework, combine `exists_redundant_panelRow_ab_lam` + W2's
`finrank_span_rigidityRows_of_rigidOn` + the (b) `k''`-reduction (`k'' := D(m−1) − finrank (span
Gv-rows)`, `Gv := G.removeVertex v`), **taking the GAP-6 inequality as an explicit hypothesis** (the
adjudicated carry — Blockers; `screwDim k * (m−1) − (screwDim k − 2) ≤ finrank (span (ofNormals Gv
…).rigidityRows)`). Output the redundancy data `r`/`lam`/`i*`/`r̂ ≠ 0`/`hingeRow a b r̂ = wGv ∈
span(Gv-rows)` that W6 (the M₁ `t = 0` certification at `F₀`) consumes. GAP 6 is adjudicated (carry,
not block), so nothing gates W5+. **No `sorry` placeholders** at any step (carry the GAP-6 inequality
as a named `h…` hypothesis, never a `sorry`).

All four abstract/graph-free leaves (W1 discriminator, W2 `h618`, W3 leaf B, W4 leaf A0) are landed;
W5 is the first leaf at the unpacked IH framework (where the GAP-6 hypothesis enters).

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
