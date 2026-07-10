# Phase 30 — Algebraic-independence relaxation (RELAX) (work log)

**Status:** in progress (opened 2026-07-09; refactor **user-sanctioned
2026-07-10** — now in the structural-edit build stage).

## Current state

**Next step: slice (c)** — delete the motive fifth conjunct + drop the
`halg` hypotheses/clauses + switch the ~9 chooser sites (see *Refactor
slice tracker*). **Slice (b) is CLOSED** (2026-07-10): all three
IH-seed-reuse compositions are device-seed product-routed, so the fifth
conjunct is **consumed nowhere on the live spine** — its remaining Lean
consumers are exactly the spine-dead slice-(d) deletion targets (the LI
bridges via the callerless alg-indep pick, the alg-indep nested-rank
pair, the seed-rank-bridge family,
`exists_ofNormals_finrank_span_rigidityRows_eq_of_hsplitGP`).

**Slice (b) route summary** (all three landed 2026-07-10; details in git
+ the reshaped decls' docstrings): factors fixed at the IH's q-free
selector *before* the seed, one `exists_eval_ne_zero` shot, gates
re-derived at the device seed (eq.-6.18 rigidity = rank-polynomial lower
bound + B2 upper at `def = 0`). Device elements beyond the recon routes:
(1) the IH's `Q.ends` is q-free — no `endsOf` swap needed anywhere;
(2) `chainData_split_w6b_gates` (which owns its seed choice) gained a
caller-supplied factor slot `(Pu, hPu)` re-emitting `eval q Pu ≠ 0` in
place of its alg-indep output conjunct — the discriminator threads the
`exists_tupleLI_polynomial` factor through it and fires the `_of_LI`
pick; `chainData_split_realization` passes `Pu := 1`;
(3) `case_I_realization_h65_gen`'s OLD block re-runs the W6e subfamily
extraction on the device-seed framework `ofNormals Gv Q_v.ends q`
(re-derived rigid from `P_v` + B2) instead of on the IH's `Q_v` — the
H3/H4 transports close at the shared seed by two
`case_I_h65_ofNormals_supportExtensor` rewrites; the statement is
unchanged (both callers unaffected; node `lem:case-I-realization-h65`
stays green, proof prose restated).

**Slice (a) landed** (2026-07-10): the four pure det/rank-polynomial
leaves — `exists_tripleLI_polynomial`, `exists_tupleLI_polynomial`,
`exists_nested_rankPolynomial_lower_all_k`,
`exists_chainData_discriminator_pick_of_LI` (all in
`CaseIII/Realization.lean`, beside their alg-indep siblings; build +
lint clean, nothing existing changed). These are the polynomial-form /
LI-form predecessors the product route consumes at slices (b)–(d).

**Both recons were GO** (2026-07-10, each compiler-witnessed by a
sorry-free general-`k` spike; durable routes below). The product route
replaces every algebraic-independence use on the spine with non-root
conditions of **the same four base polynomial factors at every `d`** —
zero per-candidate factors (R2's favorable refutation of the "family
grows with `d`" worry). The refactor (deleting the motive fifth
conjunct `AlgebraicIndependent ℚ` in `HasGenericFullRankRealization`
and product-routing the spine) is **user-sanctioned including the
optional slice (e)** — see *User adjudication* below.

## User adjudication (2026-07-10, verbatim)

> The user sanctioned the RELAX refactor — delete the
> `AlgebraicIndependent ℚ` fifth conjunct from
> `HasGenericFullRankRealization` and product-route the spine, per the
> (a)–(e) slice order in notes/Phase30.md, INCLUDING the optional final
> sweep (e) (drop the now-unconsumed rationality clauses across the
> `exists_rankPolynomial_*` family). The refactor runs as Phase 30's
> structural-edit build stage, tracked in notes/Phase30.md.

## Architectural choices made up front

- **Investigation phase, not a build phase.** The first deliverable is
  a **recon verdict**, not Lean. No blueprint chapter opens at phase
  open (the dep-graph is fully green — there are no red/deferred target
  nodes, so the phase-open red-node consistency gate is vacuous). The
  follow-on refactor is a **structural-edit-mode** change (restate
  existing green nodes as the alg-independence content is deleted),
  planned after the recons — not now.
- **The live site is at general grade.** §2's hypothesis was written at
  `d=3` (pre-Phase-23); the footnote-6 seed-rank transfer landed at
  general grade (`case_III_nested_rank_lower_all_k`, on the live A2/A5
  spine). R1 settled §2's risks (a)+(b) against that landed spine; R2
  settled the general-`d` chain/relabel question. (The phase-open claim
  that §3 site 107(a) was the *only* live consumer was an undercount —
  see *composition-point pins* below; all extra consumers are
  product-routable.)

## Investigation checklist

- [x] **R1 — the §2 product-route recon at `d=3`**: **GO-WITH-RESHAPINGS**
  (2026-07-10; compiler-witnessed sorry-free at general `k`). **(a)** no
  circularity — every `q`-condition at the composition is a non-root
  condition of one of four polynomials fixed before `q`; but `q` is *not*
  free as landed (it is the IH seed of `G_v^{ab}` from the `hsplitGP`
  unpack) — the freedom is created by a local reshape of that unpack.
  **(b)** the nested-IH rank polynomial is already landed as the
  deficiency-aware `exists_rankPolynomial_of_IH_linking` (not §2's
  def=0 pair) and feeds the device. Pins + route below.
- [x] **R2 — the general-`d` question**: **GO** (2026-07-10;
  compiler-witnessed sorry-free at general `k`). The expected "fold
  ≤ `d` per-candidate factors" shape is refuted **favorably**: the
  interior/relabel machinery consumes **zero** `q`-conditions beyond
  the base bundle, so the general-`d` product is the **same four base
  factors at every `d`**; the discriminator's alg-indep use reduces to
  one `(k+1)`-row LI factor, and no factor depends on the pick `i` or
  on the `q`-dependent `ρ₀` (the composed witness quantifies over all
  `ρ ≠ 0`). Table + spike route + full-tree sweep below.
- [x] **user adjudication** — **SANCTIONED 2026-07-10, incl. slice (e)**
  (see *User adjudication* above). The refactor now runs as the
  structural-edit build stage (*Refactor slice tracker* below).

## R1 composition-point pins (2026-07-10)

Live `AlgebraicIndependent ℚ q` consumers (all product-routable):

- `case_III_nested_rank_lower_all_k` (`CaseIII/Realization.lean`) — the
  ∀-statement's alg-indep hypothesis, consumed once via
  `MvPolynomial.eval_ne_zero_of_coeffs_subset_range_of_algebraicIndependent`;
  instantiated at the IH seed by `chainData_split_w6b_gates` and
  `case_III_candidate_dispatch`.
- the LI bridges `linearIndependent_normals_of_algebraicIndependent`
  (+ `_triple`, `_general`) — consumed by the `d=3` dispatch's
  discriminator, `case_I_realization_h65_gen` (`Theorem55.lean`), and
  the general-grade `exists_chainData_discriminator_pick`.
- the motive fifth conjunct (`HasGenericFullRankRealization`,
  `PanelHinge.lean`) — produced by GAP-2
  (`hasGenericFullRankRealization_of_rigidOn_ofNormals`) and ~9 sibling
  `exists_injective_algebraicIndependent_real` chooser sites
  (Coupling/CaseI/CaseII/Theorem55), transported by
  `CaseIII/Relabel/Basic.lean`. The shared rank-polynomial cores discard
  it (`obtain ⟨Q, hQg, hQgp, hQrank, hQrec, _⟩`), so deletion doesn't
  break the producers.

**Where the product-route choice of `q` happens:** the `hsplitGP`-unpack
(step 1 of `chainData_split_w6b_gates` / `case_III_candidate_dispatch`),
replaced by polynomial extraction + one `MvPolynomial.exists_eval_ne_zero`
shot — below the motive's existential, so no IH-interface change beyond
the conjunct deletion.

## R1 spike route (the refactor's route; re-derivable without re-running the recon)

Two theorems, compiled sorry-free at general `k` (scratch deleted; this
is the durable record).

**`exists_tripleLI_polynomial`** — the one genuinely-new brick.
Statement: for `1 ≤ k` and pairwise-distinct `a b c : α`,
`∃ P : MvPolynomial (α × Fin (k+2)) ℝ, P ≠ 0 ∧ ∀ q, eval q P ≠ 0 →
LinearIndependent ℝ ![q(a,·), q(b,·), q(c,·)]`. Construction:
`P := rename f (map (algebraMap ℚ ℝ) (det (mvPolynomialX (Fin 3) (Fin 3) ℚ)))`
with `f (i,j) = (![a,b,c] i, Fin.castLE h3 j)` (injective from the
distinctness + `Fin.castLE_injective`). Nonzero:
`Matrix.det_mvPolynomialX_ne_zero` + `MvPolynomial.map_injective` (at
`(algebraMap ℚ ℝ).injective`) + `MvPolynomial.rename_injective`.
Consumer direction: `eval q P = aeval (q ∘ f) (det …)` via
`MvPolynomial.eval_rename` + `MvPolynomial.eval_map` +
`MvPolynomial.aeval_def`, then the landed tail of
`linearIndependent_normals_of_algebraicIndependent_triple` verbatim
(`Matrix.mvPolynomialX_mapMatrix_aeval` + `AlgHom.map_det` →
`Matrix.linearIndependent_rows_of_det_ne_zero` →
`LinearIndependent.of_comp` at the `Fin.castLE h3` projections).

**`product_route_spike`** — the composition. Hypotheses: `hQab/hQv :
HasGenericFullRankRealization k n G_v^{ab}/G_v` (both already held by
the landed callers from `hIH`), a `q`-free link-recording `ends` for
`G_v^{ab}` (hence for `G_v`), `hdef_Gab`, `hk'le : def(G_v,n) ≤ D−2`
(landed: `splitOff_removeVertex_minimalKDof`), `2 ≤ |V(G_v^{ab})|`,
looplessness, `a,b,c` distinct. Four product factors, all fixed before
`q`:

1. `P_ab` := `exists_rankPolynomial_of_IH_linking G_v^{ab} ends hQab`
   (the deficiency-aware Phase-22k L7a producer);
2. `P_v` := the same at `G_v` — this IS the eq.-(6.22) input
   (`case_III_nested_rank_lower_all_k` already calls it internally);
3. `Qgp` := `exists_generalPosition_polynomial G_v^{ab} ends` (nonzero
   via its moment-curve witness at an injective
   `Countable.exists_injective_nat` param);
4. `Ptri` := the brick above.

One `MvPolynomial.exists_eval_ne_zero` shot on the product
(`mul_ne_zero`; factor nonvanishing recovered through `map_mul`). The
four `q`-dependent gates delivered at the chosen `q` — exactly the
dispatch's two `hQalg` uses plus GP:

- GP of `ofNormals G_v^{ab} ends q` (from `Qgp`);
- **eq. (6.18)**: `IsInfinitesimallyRigidOn V(G_v^{ab})` — `P_ab`'s
  `N ≤ finrank` + `finrank_span_rigidityRows_add_deficiency_le` (B2) at
  `def = 0` → equality →
  `isInfinitesimallyRigidOn_vertexSet_iff_finrank_span_rigidityRows`;
- **eq. (6.22)**: `D(|V(G_v^{ab})|−1) − (D−2) ≤ finrank (span R(G_v, q))`
  — `P_v`'s transfer + the landed arithmetic (`two_le_screwDim`,
  `screwDim_sub_two_le_mul`, the `vertexSet_splitOff` /
  `vertexSet_removeVertex` card equality, `hk'le`);
- triple LI of `![q(a,·), q(b,·), q(c,·)]` (from `Ptri`).

Rationality clauses (`coeffs ⊆ range (algebraMap ℚ ℝ)`) are **unused** —
they served only the alg-indep transfer. Downstream of the four gates,
the dispatch machinery (W6b, discriminator, arm closers, GAP-2) imposes
no further conditions on `q` (verified end-to-end on
`case_III_candidate_dispatch`).

**Genuine build residuals** (wiring, not open math): (i) the
`(k+1)`-row sibling of the brick — **now drafted and compiled by the R2
spike** (`exists_tupleLI_polynomial` below). (ii) the `ends`-selector
wiring — replace the IH's `Q.ends` with the `q`-free canonical
`Gab.endsOf` + the landed `ofNormals_recordsLinks_of_hends` /
`recordsLinks_agree_swap` transport.

## R2 record (2026-07-10): general `d` — the `q`-condition table

All `q`-conditions on the general-`d` spine off the base w6b bundle,
each a factor fixed before `q`:

| condition | landed consumption | pre-fold |
|---|---|---|
| `G_v^{ab}` full rank (eq. 6.18, in w6b via `hsplitGP`) | IH seed's rank conjunct | `P_ab` (R1-witnessed) |
| `G_v` rank lower bound (eq. 6.22, `h622lb`) | alg-indep at `case_III_nested_rank_lower_all_k` | `P_v` (R1-witnessed) |
| GP / pairwise LI (`hgp`, `hgp_seed`) | IH seed's GP conjunct | `Qgp` (landed; R1-witnessed) |
| `(k+1)`-panel LI for the discriminator pick | alg-indep at `exists_chainData_discriminator_pick` via `…_general` | tuple factor (R2-witnessed) |

**Interior branch (`2 ≤ i`): zero additional `q`-conditions.**
`chainData_dispatch_interior(_of_discriminator)` + the engine
`chainData_interior_realization_hρGv` consume only bundle outputs
(`ρ₀`-gates, `w`, the eq.-(6.66) widening, `hLI`/`hgate`) plus
`hgp_seed`; the relabeled seed `q ∘ shiftPerm`'s GP derives from
`hgp_seed` at the permuted pair (`shiftPerm` is an `Equiv`;
`IsGeneralPosition` quantifies over all of `α`, so one `Qgp` covers
every relabel); the bottom family relabels as **rows** via
`(funLeft shiftPerm.symm).dualMap`, not as polynomial conditions.
Grep-witnessed: zero `AlgebraicIndependent` in `Relabel/Chain.lean`,
`Relabel/ChainColumn.lean`, `Relabel/Arm.lean`, `Relabel/ForkedArm.lean`,
`Candidate.lean`. Floor branch (`i ≤ 1`): the M₁/M₂ arms, alg-indep-free
(R1-verified). So the product is **the same four factors at every `d`**.

### R2 spike route (three theorems, compiled sorry-free; scratch deleted)

1. **`exists_tupleLI_polynomial`** — for injective
   `cand : Fin (k+1) → α`: `∃ P ≠ 0, ∀ q, eval q P ≠ 0 →
   LinearIndependent ℝ (fun i j => q (cand i, j))`. Same
   `rename f (map (algebraMap ℚ ℝ) (det (mvPolynomialX (Fin (k+1))
   (Fin (k+1)) ℚ)))` construction as the R1 brick, with
   `f (i,j) = (cand i, Fin.castSucc j)` and the landed
   `linearIndependent_normals_of_algebraicIndependent_general` tail
   (projection via `Fin.castSucc`, `Matrix.mvPolynomialX_mapMatrix_aeval`
   + `AlgHom.map_det` + `Matrix.linearIndependent_rows_of_det_ne_zero` +
   `LinearIndependent.of_comp`).
2. **`exists_chainData_discriminator_pick_of_LI`** — the landed pick
   body (`exists_homogeneousIncidence_of_normals_gen` +
   `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` + the
   `panelSupportExtensor_eq_complementIso_extensor` bridge) with
   `hn : LinearIndependent …` in place of `hq : AlgebraicIndependent ℚ q`
   — witnessing that the landed pick consumes alg-indep ONLY through the
   one LI derivation.
3. **`discriminator_pick_of_tuple_factor`** — one `q`-free factor whose
   non-root fires the pick **for every `ρ ≠ 0`**: no factor depends on
   the pick's output `i` or on the `q`-dependent `ρ₀`, killing the
   "chosen after `q`" ordering worry.

### R2 full-tree sweep (consumers outside the R1 pins: none; precise names)

- **`case_I_realization_h65_gen`** (`Theorem55.lean`, the KT Lemma-6.5
  arm; use at its `htriLI` step) — the second IH-seed-reuse composition;
  needs the same reshape at three factors (`P_v` + `Qgp` + triple).
- Splice producers `hasGenericFullRankRealization_of_splice_ofNormals`
  (`GenericityDevice.lean`) / `…_splice_set_ofNormals` (`Coupling.lean`)
  — their `halg` hypotheses exist solely to emit the output conjunct;
  deleted with it.
- Relabel transports (`ofNormals_relabel`, `ofNormals_relabel_perm`,
  `hasGenericFullRankRealization_of_splitOff_relabel`,
  `Relabel/Basic.lean`) — consume the conjunct only to re-emit it;
  GP/rigidity/recording transport untouched by its deletion.
- Seed-rank-bridge family
  (`isInfinitesimallyRigidOn_ofNormals_of_algebraicIndependent`,
  `finrank_infinitesimalMotions_le_of_rankPolynomial_algebraicIndependent`,
  `rankHypothesis_ofNormals_of_rankPolynomial_algebraicIndependent`,
  `CaseI.lean`) — **spine-dead** (zero callers outside their own
  internal chain; blueprint-pin-only). Delete + restate nodes.
- `Pinning.lean` / `PanelLayer.lean` — doc-comment mentions only.

### Refactor slice tracker (the structural-edit Layer plan)

**Scope: ~8–14 slices, ~12 Lean files touched, 3 mirror files deleted**
(`Mathlib/RingTheory/AlgebraicIndependent/{Defs,TranscendenceBasis}.lean`,
the `Tower.lean` transfer lemma), plus blueprint restates. Green at
every commit via:

- [x] **(a)** land the two det-factor bricks + primed variants as pure
  leaves — nothing breaks. **DONE 2026-07-10**: `exists_tripleLI_polynomial`,
  `exists_tupleLI_polynomial` (the two det-factor bricks),
  `exists_chainData_discriminator_pick_of_LI` (LI-form of the pick),
  `exists_nested_rankPolynomial_lower_all_k` (polynomial-form of
  `case_III_nested_rank_lower_all_k`) — all in `CaseIII/Realization.lean`.
- [x] **(b)** reshape the three IH-seed-reuse compositions to
  device-chosen seeds via the primed variants — the fifth conjunct is
  then *emitted but consumed nowhere*. **DONE 2026-07-10**, in three
  commits: the `d=3` `case_III_candidate_dispatch` (product route;
  `h622lb` → polynomial form, `hn` added); the general-`d`
  `chainData_split_w6b_gates` chain (the caller-supplied factor slot
  `Pu`; tuple factor → the `_of_LI` pick; alg-indep output conjuncts
  deleted through `chainData_fire_discriminator`);
  `case_I_realization_h65_gen` (statement-preserving internal reshape —
  the OLD-block W6e extraction re-run on the device-seed `Gv` framework,
  re-derived rigid from `P_v` + B2). Route summary: *Current state*.
- [ ] **(c)** delete the conjunct + drop the `halg` hypotheses/clauses
  (splice producers, relabel transports) + switch the ~9 chooser sites
  to `exists_eval_ne_zero` on their existing rational products — purely
  subtractive;
- [ ] **(d)** delete the LI bridges, the spine-dead seed-rank-bridge
  family, and the mirrors, with blueprint restates per the
  deletion-variant grep discipline;
- [ ] **(e)** last sweep (**sanctioned**, not optional): the
  then-unconsumed `coeffs ⊆ range (algebraMap ℚ ℝ)` rationality clauses
  across the `exists_rankPolynomial_*` family (incl. slice (a)'s
  `exists_nested_rankPolynomial_lower_all_k`) — zero risk.

### Repin debt (additive-successor gate, opened at slice (a))

The slice-(a) leaves are additive predecessors of supersessions at
slices (b)–(d). Blueprint nodes to repin when the superseded decl
retires:

- `case-iii.tex` node `lem:case-III-nested-rank-lower` — **pin extended
  2026-07-10** (the additive-successor repin fired: both spine callers
  of `case_III_nested_rank_lower_all_k` switched to the polynomial
  form). The node now pins all three
  (`case_III_nested_rank_lower_all_k`, `case_III_nested_rank_lower`,
  `exists_nested_rankPolynomial_lower_all_k`) with a fmlnote naming the
  polynomial-form variant as the one the chain discriminator consumes.
  The two alg-indep forms are now **callerless** (pin-only); retire
  them at slice (d) with the node restate to the polynomial form.
- `exists_chainData_discriminator_pick` (alg-indep form) is now
  **callerless and unpinned** (the spine fires the `_of_LI` sibling);
  its docstring carries the supersession note — delete at slice (d)
  with the LI bridges it consumes.
- `panel-layer.tex:244` pins `HasGenericFullRankRealization` — restate
  the node when slice (c) reshapes the definition (fifth conjunct
  deleted).
- The two det-factor bricks + `…_pick_of_LI` carry **no** `\lean` pin
  (internal infra, matching their alg-indep siblings) — no repin debt.

## Blockers / open questions

- None. The refactor is sanctioned and in its build stage.

## Hand-off / next phase

**Next concrete commit: slice (c)** — delete the `AlgebraicIndependent ℚ`
fifth conjunct from `HasGenericFullRankRealization` (`PanelHinge.lean`,
the def + its docstring's alg-independence paragraph) and repair the
producers/transports in the same commit: (i) the ~9
`exists_injective_algebraicIndependent_real` chooser sites
(Coupling/CaseI/CaseII/Theorem55 — grep that name) switch to
`MvPolynomial.exists_eval_ne_zero` on their existing rational products,
dropping the emitted conjunct; (ii) the splice producers'
(`hasGenericFullRankRealization_of_splice_ofNormals` /
`…_splice_set_ofNormals`) `halg` hypotheses are deleted with the
conjunct they fed; (iii) the relabel transports (`Relabel/Basic.lean`,
`ofNormals_relabel`, `ofNormals_relabel_perm`,
`hasGenericFullRankRealization_of_splitOff_relabel`) drop their
consume-and-re-emit of the conjunct; (iv) the destructuring sites that
bind it positionally (`obtain ⟨Q, …, _⟩` patterns — grep
`hsplitGP`/`hGP` unpacks) lose one component. Blueprint:
`panel-layer.tex:244` (`def:rank-hypothesis` area) restates the
definition node per the repin debt; the statement-change grep applies to
every producer whose signature drops `halg`. If one commit is too big,
split (i)+(iv) [the def + choosers] from (ii)+(iii) [producer-hypothesis
drops] — but note the def change itself forces (iv) everywhere, so the
def + all consumers must land together; (ii)/(iii) hypothesis drops are
separable. Slice (d) (delete the now-dead alg-indep family + mirrors)
follows.

## Decisions made during this phase

- **Slice (b) — `case_I_realization_h65_gen` landed (2026-07-10, closes
  slice (b)):** statement-preserving internal reshape (no caller breaks,
  no blueprint statement edit; `lem:case-I-realization-h65` proof prose
  restated to the common-non-root derivation). Three factors before the
  seed; `Gv`-rigidity re-derived from `P_v` + B2; the W6e OLD-block
  extraction re-run on `ofNormals Gv Q_v.ends q`; H3/H4 transports close
  at the shared seed via two `case_I_h65_ofNormals_supportExtensor`
  rewrites. The sizing worry (H3/H4 rewiring) did not materialize —
  compiled first-build. Details: *Current state* route summary.
- **Slice (b) — the general-`d` pair landed (2026-07-10):** device-seed
  product route through `chainData_split_w6b_gates` (which owns the seed
  choice, so it gained the caller-supplied factor slot `Pu` — the device
  pattern for a producer whose caller needs an extra `q`-condition at the
  internally-chosen seed). Discriminator fires the `_of_LI` pick from the
  tuple det factor; alg-indep output conjuncts deleted downstream.
  Blueprint: `lem:case-III-nested-rank-lower` pin extended (repin fired);
  `lem:case-III-chain-discriminator` proof prose restated. Details:
  *Current state*; h65 sizing note: *Refactor slice tracker*.
- **Slice (b) — `case_III_candidate_dispatch` (`d=3`) landed (2026-07-10):**
  device-seed product route. `h622lb` reshaped alg-indep → polynomial form;
  `hn : bodyBarDim n = screwDim 2` added (B2 needs it for the eq.-6.18 upper
  bound). Four factors built at the IH's q-free `Q.ends` before `q`; one
  `exists_eval_ne_zero` shot; gates re-derived at the device seed. Two
  findings for the remainder: (1) `Q.ends` is q-free, so the R1 `endsOf`
  residual is unnecessary — reuse the IH selector directly; (2) the arm
  closers (`case_III_arm_realization` → `case_III_realization_of_rank`) take
  **no** alg-indep hypothesis (the genericity device re-realizes the output
  at a fresh alg-indep seed internally), so the device seed drives them
  fine. Blueprint node `lem:case-III-candidate-dispatch-d3` unchanged (its
  prose abstracts `h622lb` as "the eq.-6.22 bound holds" and `hn` as "Fix
  d=3, D=6"). Build + lint clean, axiom-clean.
- **Slice (a) landed (2026-07-10):** the four pure det/rank-polynomial
  leaves (`exists_tripleLI_polynomial`, `exists_tupleLI_polynomial`,
  `exists_nested_rankPolynomial_lower_all_k`,
  `exists_chainData_discriminator_pick_of_LI`) in
  `CaseIII/Realization.lean`, built from their landed alg-indep siblings'
  proof tails + `MvPolynomial.{rename,map,eval_rename,eval_map,aeval_def}`
  extraction (bricks) / `exists_rankPolynomial_of_IH_linking` (rank
  sibling). Pure additive; build + lint clean. Repin debt opened (above).
- **R1 verdict (2026-07-10): GO-WITH-RESHAPINGS** at `d=3` (and the
  single-split composition at general `k`), compiler-witnessed
  sorry-free. §2's two wrong premises corrected in
  `notes/AlgebraicIndependence.md` (producer pair; `q` not free as
  landed); §3's "only live site" undercount corrected (LI bridges +
  motive conjunct are also live, all product-routable). Route + pins:
  this file, *R1 spike route* / *R1 composition-point pins*.
- **R2 verdict (2026-07-10): GO at general `d`**, compiler-witnessed
  sorry-free. The "≤ `d` per-candidate factors" expectation refuted
  favorably: zero per-candidate factors; the same four base factors at
  every `d`. Full-tree sweep found no consumer outside the R1 pins
  (extra names recorded above). Record: this file, *R2 record*.
