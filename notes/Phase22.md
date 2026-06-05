# Phase 22 — Realization layer (Case I + Case III at `d=3`) (work log)

**Status:** in progress (opened 2026-06-04).

Stratum 5 of the molecular-conjecture program, continued: the Theorem-5.5 *case
producers* that the Phase-21b genericity device feeds. Phase 21b closed the
genericity-free reductions (the accounting iffs, the `V(G)`-relative count
bridges, the device, the reusable row/glue infra) and re-scoped the realization
*producers* here after a math-first feasibility pass. The KT math for both
producers is worked out in `notes/Phase21b.md` *Finding A/B* + *Hand-off to
Phases 22–23* — **Phase 22 formalizes it, it does not re-derive it.**

Forward-mode / **structural-edit** discipline (`blueprint/CLAUDE.md`): Phase 22
does *not* open a new blueprint chapter. Its producers (N4/N5/N6, the Case II/III
producer) **extend the existing `algebraic-induction.tex`** — their nodes are
already stubbed red there. Program plan / reuse map / citations:
`notes/MolecularConjecture.md` *Phase 22*. Lean lands in
`Molecular/{Induction,AlgebraicInduction}.lean`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative*, *Constructibility recon
before a producer build*, *Phase Case-naming vs. KT's k-bookkeeping*.

## Current state

**Leg-restricted rank polynomial GREEN — the genuine N6b brick the recon named; the per-leg
rank-polynomial route now applies to *proper-subgraph* legs** (this commit; four axiom-clean
declarations in `AlgebraicInduction.lean`, no `\leanok` flip — infra below the still-red Case-I
nodes). The recon (prior commit) found the all-edges `exists_rankPolynomial_of_rigidOn` inapplicable
to a leg `GH ≤ G`: its `span_panelRow_eq_rigidityRows` chain needs `hends : ∀ e : β, GH.IsLink e …`,
which the parent's selector cannot supply on non-`GH` edges. **Fix: restrict the whole chain to the
*linking* edges.** Built (i) the leg-restricted span lemma
`BodyHingeFramework.span_panelRow_linking_eq_rigidityRows` — the panel rows of the *linking* edges
span the rigidity-row space, requiring `hends`/`hne` only on edges that link (the form a leg
supplies); (ii) the leg-restricted subfamily extractor
`BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking` — a rigid leg carries
`D(|V|−1)` independent panel rows *every member of which links* (`hsupp`); (iii) the leg-restricted
producer `PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking` — a rigid leg ⟹ a nonzero
Gram-det `MvPolynomial` whose witnessed subfamily lies on the leg's linking edges; and (iv) the
matching consumer `…_rankPolynomial_ne_zero_linking` — a non-root with `hsupp` ⟹ the leg rigid at
that point, drawing each `⊆`-inclusion link witness from `hsupp` rather than the all-edges `hends`.
Same coordinatization + rank-nullity as the all-edges forms; the only change is restricting the
spanning identity to linking edges so the leg-restricted `hends` (link of every *linking* edge,
automatic for a leg via `infinitesimalMotions_ofNormals_eq_of_ends_swap`) suffices. **The N6b/N6c
coupling itself stays red** (no `sorry` committed — only the leg-restricted per-leg bricks land). The
substantive Lean state below (N4/N5/N6a/two-motive split/(G2)) is unchanged. See *Decisions* /
*Blockers* / *Hand-off*.

**N6b recon (prior commit): the simple Case-I coupling is NOT a clean assembly — the all-edges
per-leg rank-polynomial route needs `hends : ∀ e : β, GH.IsLink e …`, which a proper-subgraph leg
cannot supply.** Landed the first decomposable green brick toward the leg-restricted route,
`PanelHingeFramework.infinitesimalMotions_ofNormals_eq_of_ends_swap` (+ `panelSupportExtensor_swap`
and the span-keyed `infinitesimalMotions_eq_of_isLink_span_supportExtensor`): a leg's rigidity is
invariant under swapping an edge's endpoints, beginning to re-express a leg's IH rigidity (own
`ends_H`) at the parent's `ends`. See *Decisions* / *Blockers* + the leg-restricted-chain entry above
that discharges this recon.

**(G2) general-position `MvPolynomial` factor GREEN — the bounded analytic brick the Case-I coupling
was missing** (prior commit; `PanelHingeFramework.exists_generalPosition_polynomial` + the two helper
bricks `pair_linearIndependent_of_leading_minor_ne_zero` + `pairLeadingMinorPoly` /
`eval_pairLeadingMinorPoly`, `AlgebraicInduction.lean`, axiom-clean, no `\leanok` flip — infra below
the still-red Case-I nodes). The design build-order's node after the two-motive split
(`notes/Phase22-realization-design.md` §3 Track A, §2 row "(G2)"): a single nonzero
`MvPolynomial (α × Fin (k+2)) ℝ` whose non-roots are exactly the *general-position* normal
assignments. Concretely the product over distinct body pairs `Finset.univ.offDiag` of the leading
`2 × 2` minor polynomial `pairLeadingMinorPoly a b := X_{(a,0)}·X_{(b,1)} − X_{(a,1)}·X_{(b,0)}`:
a non-root makes every pair's leading minor nonzero (`Finset.prod_ne_zero_iff`), which forces each
pair of panel normals independent (the new minor helper, the coordinate-level generalization of
`momentCurve_pair_linearIndependent`), i.e. general position of `ofNormals G ends q`. **Genuinely
nonzero, witnessed:** at any injective `param` the moment-curve assignment `q(a,i)=(param a)^i` makes
each factor evaluate to the Vandermonde determinant `param b − param a ≠ 0`, so the product is
nonzero there — the explicit non-root the design names, ready to multiply into the triple product
`Q_H · Q_c · Q_gp`. **This closes gap (G2);** (G1) was already dissolved by the two-motive split. So
the only missing analytic bricks across the whole layer are now the *simple Case-I cases* N6b/N6c
(assemble the triple product + the green splice) + the *Case-III row* (Track B, via Lemma 2.1). The
three new declarations were first-try; the only deprecation (`push_neg`) is already-documented
FRICTION, avoided via `rw [not_or, not_not, not_not]`. The substantive Lean state below
(N4/N5/N6a/two-motive split) is unchanged from the prior commit. See *Hand-off*.

**Two-motive split GREEN — the general-position realization motive + forgetful map** (prior commit;
`PanelHingeFramework.HasGenericFullRankRealization` + `hasFullRankRealization_of_generic`,
`AlgebraicInduction.lean`, axiom-clean, no `\leanok` flip — infra below the still-red Case-I nodes).
The design build-order's node after N6a (`notes/Phase22-realization-design.md` §5): add the *separate*
unconditional-general-position motive
`HasGenericFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧ Q rigid on V(G)`
(carried only through the simple Case-I cases, KT's "nonparallel, if simple") + the one-line
forgetful map `hasFullRankRealization_of_generic : HasGenericFullRankRealization → HasFullRankRealization`
(drop the GP conjunct). **`theorem_55`'s bare-motive statement is untouched** — the GP motive is a
parallel scaffold, not a strengthening of the reduction principle (the `Simple`-threading spike ruled
out the single-conjunct option (A): `splitOff` does not preserve simplicity, so an `(G.Simple → GP)`
conjunct's IH lands on the wrong graph at `hsplit`). This **dissolves gap (G1) at the source**: the
splice/rank-polynomial producers need a *general-position* rigid seed, which a bare rigid IH does not
supply; the GP motive now carries it, and a general-position parent seed is GP for every leg
(`withGraph` keeps the same normals), so the producers' `hgp`/`hne` are discharged for free.

**N6a GREEN — the non-simple Case I splice producer (general-position-free)** (prior commit;
`PanelHingeFramework.hasFullRankRealization_of_splice_of_supportExtensor` + its leg-native form
`…_of_supportExtensor_ofNormals`, `AlgebraicInduction.lean`, axiom-clean, no `\leanok` flip — infra
below the still-red `lem:case-I-splice-placement` / `lem:case-I-realization`). The motive-independent
first node of the two-motive build order: the splice producer parameterized by *transversal hinges*
(`hsupp : ∀ e, supportExtensor e ≠ 0`) directly, rather than by *general position* (`hgp`). It is a
strict generalization of `hasFullRankRealization_of_splice` (which now factors through it, deriving
`hsupp` from `hgp` via `supportExtensor_ne_zero_of_isGeneralPosition`). General position implies
transversal hinges, so the two coincide when `G` is simple; they part ways exactly in KT's non-simple
Lemma 6.2 case, where two boundary panels are set *equal* (parallel normals ⟹ general position fails)
while every retained hinge stays transversal. So the non-simple Case I consumes a *bare*
(non-general-position) realization, supplying the bare `HasFullRankRealization` motive back — **no
motive strengthening, touches no Phase-20 node, `theorem_55`'s bare statement untouched.** Composes
the three green pieces verbatim (splice seed → N7b-0 under the explicit `hsupp` → device closure); the
leg-native form swaps `withGraph`→`ofNormals` by the `rfl` bridge (`ofNormals_withGraph` +
`toBodyHinge_withGraph`), no `rw` needed. Honesty gate met: inputs are the satisfiable per-leg
rigidities + per-hinge transversality at the common seed `q₀`; the parent rank is concluded. The
remaining red content of `lem:case-I-splice-placement` (exhibiting `q₀`) is unchanged. The substantive
Lean state below is unchanged from the prior commit.

**N5 per-leg rank-polynomial CONSUMER GREEN — a non-root of the rank polynomial ⟹ the leg is rigid
*at that point*** (`PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`,
`AlgebraicInduction.lean`, axiom-clean, no `\leanok` flip — infra below the still-red
`lem:case-I-splice-placement` / `lem:case-I-realization`). The *forward* half of
`exists_rankPolynomial_of_rigidOn`: at any `q` with `eval q Q ≠ 0`, the leg `ofNormals G ends q` is
infinitesimally rigid on `V(G)`. Proved **at the seed `q` itself** (not at a generic point): the
non-root clause gives the full-size `D(|V|−1)` `panelRow`-subfamily LI at `q`, which forces
`finrank (span rigidityRows) ≥ #s` (the subfamily span sits inside the rigidity-row span — `⊆` needs
*no* transversality, `annihRow_apply_self`), hence by rank–nullity
(`infinitesimalMotions_eq_dualCoannihilator` + `finrank_dualCoannihilator_eq` +
`finrank_screwAssignment`) `dim Z(G,q) = D|V| − finrank(span rigidityRows) ≤ D|V| − D(|V|−1) = D ≤
D(|V(G)ᶜ|+1)`, so N3 reads off rigidity at `q`. This is the per-leg brick the shared-seed coupling
consumes (each leg rigid *at the common non-root* `q₀`), not at a separately-generic point.

**Constructibility recon on the coupling (this commit, key finding): the coupling is NOT the
one-commit "tight assembly" the prior hand-off claimed — two real gaps remain.** Running the
producer-scrutiny recon (`DESIGN.md` *Constructibility recon …*) on the planned coupling
(product of the two legs' rank polynomials → shared non-root `q₀` → splice) found two genuine
obstructions the type-level "feed the green bricks together" plan was blind to: **(G1) per-leg
transversal-rigid *seed*** — `exists_rankPolynomial_of_rigidOn` (the polynomial *producer*) needs the
leg rigid at a seed with *all hinges transversal* (`hne`), but the IH supplies only a *bare* rigid
`HasFullRankRealization` (no general position); a rigid framework can have a degenerate hinge, and the
whole `panelRow`/N7b-0 span argument needs transversal hinges. **(G2) general position at the shared
seed** — the splice `hasFullRankRealization_of_splice_ofNormals` needs `hgp` (general position at
`q₀`), but the product `Q_H · Q_c`'s non-root is not general-position; coupling general position into
the shared-non-root search needs a *third* nonzero factor whose non-roots are general-position
assignments (a Vandermonde-type brick that does not yet exist). Both are the genuine KT §6.2
panel-intersection geometry (eq. 6.6) — the construction does *not* take an arbitrary rigid IH
realization, it *builds* a specific general-position one. See *Blockers* / *Hand-off*.

**N5 per-leg rank polynomial GREEN — a rigid leg ⟹ a nonzero Gram-det `MvPolynomial`**
(`PanelHingeFramework.exists_rankPolynomial_of_rigidOn`, `AlgebraicInduction.lean`, axiom-clean,
no `\leanok` flip — infra below the still-red `lem:case-I-splice-placement` / `lem:case-I-realization`).
The genuine next brick of the seed witness-transfer (option (b)) the prior hand-off named: turn one
leg's rigidity at a seed into a *single* `MvPolynomial (α × Fin (k+2)) ℝ` `Q` that is **nonzero at
that seed** (`eval q₀ Q ≠ 0`) and at every non-root `q` of which the leg's full-size `D(|V(G)|−1)`
`panelRow`-subfamily is linearly independent. Built on green infra by reusing
`exists_good_realization_ofParam`'s coordinatization verbatim (the `panelRow` family's `⋀^k`-coords
against `Pi.basis (fun _ => screwBasis k)` are the degree-2 `annihRowPoly`s scaled by the
body-incidence sign, `hg`) and feeding it to the **new mirror**
`exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) — the
constructive refinement of `exists_le_finrank_span_polynomial` that *exposes* the witnessing
Gram-determinant minor rather than consuming it inside `MvPolynomial.exists_eval_ne_zero`. The
independent full-size subfamily `s` is N7b-0 (`exists_independent_panelRow_subfamily_of_rigidOn`).
Honest per the gate: the input is the satisfiable single-seed rigidity `hrig`; the deliverable is the
*polynomial* witnessing that seed's rank, not a generic rank. **Remaining (red):** take the product
of *two* legs' polynomials, apply `MvPolynomial.exists_eval_ne_zero` to the product for one shared
`q₀`, re-derive both legs' rigidity at `q₀` (via N3 / `hasFullRankRealization_of_independent_panelRow`),
and feed `hasFullRankRealization_of_splice_ofNormals` (green). FRICTION two resolved entries +
TACTICS-QUIRKS § 4 cross-ref. See *Hand-off*.

**N5 witness-transfer prerequisite GREEN — non-empty rigid `ofNormals` locus from the IH**
(`PanelHingeFramework.exists_rigidOn_ofNormals_of_hasFullRankRealization`, `AlgebraicInduction.lean`,
axiom-clean, no `\leanok` flip — infra below the still-red `lem:case-I-splice-placement` /
`lem:case-I-realization`). The **first decomposable brick of the seed witness-transfer (option (b))**,
the prerequisite the prior hand-off named: bridge the realization motive `HasFullRankRealization k G`
(the form the IH supplies — an *arbitrary*-normal rigid framework `Q` on `G`) to the *`ofNormals`
shape* the transfer must couple across legs: `∃ ends q, (ofNormals G ends q).toBodyHinge` rigid on
`V(G)`. Three-line proof: the IH's witness `Q` is *literally* an `ofNormals` —
`ofNormals Q.graph Q.ends (fun p => Q.normal p.1 p.2) = Q` is `rfl` (the constructor writes exactly
`Q`'s three fields) — so `subst hQg` (the `Q.graph = G` conjunct) makes both the framework equality
and the `V(G)`-vs-`V(Q.graph)` rigidity argument line up, and `exact ⟨Q.ends, …, hQrig⟩` closes by
defeq. Carries **no rank assumption** (honest: its sole input is the IH's existence statement,
repackaged — not the generic rank a producer concludes). With each leg's rigid locus now non-empty in
`ofNormals` form, the remaining content of the transfer is the *non-zero-product / `MvPolynomial.funext`
step* coupling the two loci onto one shared seed `q₀`, fed to `hasFullRankRealization_of_splice_ofNormals`
(green). FRICTION `[resolved]` *Repackaging a `HasFullRankRealization` witness as an `ofNormals` …*.
See *Hand-off*.

**N5 splice + seed scaffolding, all GREEN (earlier commits; full entries in *Decisions* / *Lemma
checklist*).** The math-first decomposition found N5 narrower than "splice two placements": panel
transversality is already green (`panelSupportExtensor_ne_zero_iff` + `isGeneralPosition_ofParam`),
and `withGraph` keeps the same normals (`withGraph_normal`), so there is no literal placement-gluing
— the only obstruction is the **common seed** at which both legs are rigid. The scaffolding that
isolates it, all axiom-clean, no `\leanok` flip: the splice brick `hasFullRankRealization_of_splice`
(composes splice-seed → N7b-0 → device on satisfiable common-placement legs); its leg-native
restatement `hasFullRankRealization_of_splice_ofNormals` (+ `ofNormals_withGraph`, the `rfl`
graph-swap); the moment-curve specialization `hasFullRankRealization_of_splice_ofParam`; the
single-leg bridge `hasFullRankRealization_of_rigidOn_seed`; and the rigid-block `D`-fold base packing
`Graph.IsKDof.exists_isBase_isForestPacking` (a rigid `H` has an `M(H̃)`-base packing `D` forests,
`|B| = D(|V(H)|−1)`). The "row-stacking" follow-up to the packing was **ruled out** by a
constructibility recon (over-counts by `(D−1)`, off-path — N7b-0 already gives the full count from
rigidity-on-`V`); the `_ofParam` *seed* was ruled out (subvariety-genericity gap vs. the free-normal
`∃ Q, …` motive). So both options collapsed to the free-`ofNormals` witness-transfer (option (b)).

**N4 is fully GREEN — Track A's reduction infra is complete** (`rigidContract_isMinimalKDof`,
`Induction.lean`, axiom-clean; `lem:rigidContract-isMinimalKDof` `\leanok` in `algebraic-induction.tex`):
`G.IsMinimalKDof n 0 ∧ H proper rigid ∧ r ∈ V(H) ⟹ (G.rigidContract H r).IsMinimalKDof n 0`. The whole
chain landed across earlier commits — N4a (`mulTilde_preconnected_of_isKDof_zero`, `Deficiency.lean`),
N4b (`cycleMatroid_mulTilde_rigidContract` under the collapse), N4c (the union↔contraction bridge
`matroidMG_rigidContract_eq_contract` via the new abstract crux
`Matroid.Union_pow_contract_eq_contract_of_rk_saturated`, count route), and the reconciliation
(`rigidContract_isMinimalKDof` from the green `contraction_isMinimalKDof` + N4c + the two graph-side
bricks `edgeSet_rigidContract` / `rigidContract_vertexSet_ncard`). Per-node detail in the *Lemma
checklist* + *Decisions*; what gates `lem:case-I-realization` (N6) is now only the **producers**
N5 + N6.

## Architectural choices made up front

- **Two tracks; Track A first.** Track A (Case I producer, full-rank, KT §6.2) is
  the tractable entry point and independent of Case III. Track B (Case II/III
  reducible-vertex producer at `d=3`, KT §6.3 + §6.4.1) is the crux (Lemma 6.10,
  ~12 pages, the single largest proof in KT). See `notes/MolecularConjecture.md`
  *Phase 22* for the node-by-node plan.
- **The motive is `V(G)`-relative** (`DESIGN.md` *Realization motive must be
  V(G)-relative*; carried from Phase 21b). `HasFullRankRealization` is the
  `V(G)`-relative rank `D(|V(G)|−1)`; the absolute null-space form is
  unsatisfiable for non-spanning inductive subgraphs.

## Lemma checklist

**Track A — Case I producer (full-rank, KT §6.2).**
- [x] **N4** `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction-
  minimality bridge: `G.IsMinimalKDof n 0 ∧ H proper rigid ∧ r ∈ V(H) ⟹ (G.rigidContract H
  r).IsMinimalKDof n 0`. **GREEN** (`rigidContract_isMinimalKDof`, axiom-clean, `\leanok` flipped).
  The rank/ambient reconciliation assembled the green `contraction_isMinimalKDof` (corank +
  base-meets-fiber on `M(G̃)／E(H̃)`) through N4c (`matroidMG_rigidContract_eq_contract`) into the
  graph-level minimality, using the two new graph-side bricks `edgeSet_rigidContract`
  (`E(G/E(H)) = E(G)\E(H)`) and `rigidContract_vertexSet_ncard` (exact collapse count
  `|V(G/E(H))| = (|V(G)|−|V(H)|)+1`) + the def=corank bridge. Sub-bricks:
  - [x] **N4a** rigid subgraph's multiplied graph is connected
    (`mulTilde_preconnected_of_isKDof_zero`: `G.IsKDof n 0 ⟹ (G.mulTilde n).Preconnected`,
    under `[NeZero (bodyHingeMult n)]`), licensing the `collapseTo r V(H)` vertex-collapse.
    Green, axiom-clean (`Deficiency.lean`); cut-partition contradiction reusing
    `two_le_crossingEdges_of_isKDof_zero`'s structure.
  - [x] **N4b** cycleMatroid under the vertex-collapse `map` (Whitney contraction):
    `cycleMatroid_mulTilde_rigidContract` (+ bricks `mulTilde_rigidContract`,
    `rigidContract_eq_contract'`, `rigidContract_collapseTo_isRepFun`), all green/axiom-clean
    in `Induction.lean`. The recon's "`cycleMatroid_contract` does not apply" call was **wrong**
    — it applies at the `mulTilde` level (N4a ⟹ `IsRepFun`); see *Decisions*. Needs `r ∈ V(H)`.
  - [x] **N4c** union-level independence bridge `matroidMG_rigidContract_eq_contract`
    (`M((G/E(H))̃) = M(G̃) ／ E(H̃)`). **GREEN** (axiom-clean). Reduction bricks
    (`edgeSet_mulTilde_rigidContract`, `matroidMG_contract_eq_restrict`,
    `matroidMG_rigidContract_eq`) + saturation specialization
    (`union_cycleMatroid_rk_saturated_of_isKDof_zero`) + the new abstract crux
    `Matroid.Union_pow_contract_eq_contract_of_rk_saturated` (saturation ⟹ `Union (M／C)` and
    `(Union M)／C` agree on indep sets, via the count route). The prior crux *input*
    `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (basis split) is **unused** by the count
    route but kept (abstract, green, may serve a future matching-style consumer).
- [ ] **N5** `lem:case-I-splice-placement` — splice the inductive legs `(H,p₁)`,
  `(G/E',p₂)` onto one parent placement (eq. 6.6 panel intersections). **Decomposed
  math-first (this commit):** the panel-transversality "lemma" is already green
  (`isGeneralPosition_ofParam`); `withGraph` keeps the same normals so there is no
  two-placement splice; the genuine obstruction is producing *one seed `q₀` with
  both legs rigid* (the witness-transfer) + the count `hmatch` coupling the block
  pin to the contraction's inductive rank. **First brick GREEN:**
  `hasFullRankRealization_of_splice` (axiom-clean) composes the three green pieces
  (splice seed → N7b-0 → device closure) and isolates the seed obstruction into
  satisfiable common-placement hypotheses. **Leg-native restatement GREEN (this commit):**
  `hasFullRankRealization_of_splice_ofNormals` + the graph-swap bridge `ofNormals_withGraph`
  re-state the two legs in the form a seed construction produces —
  `(ofNormals GH/Gc ends q₀).toBodyHinge` rigid on its own vertex set, at one `q₀` — so the
  gap is now exactly "exhibit `q₀`", with the `withGraph` graph-swap dissolved into a `rfl`.
  **Moment-curve seed GREEN:** `hasFullRankRealization_of_splice_ofParam` further
  specializes the seed to `ofParam GH/Gc ends param` at an injective `param : α → ℝ`, discharging
  the general-position hypothesis `hgp` for free (`isGeneralPosition_ofParam`) so it leaves the
  consumer's obligation. **H-leg single-leg producer GREEN (this commit):**
  `hasFullRankRealization_of_rigidOn_seed` — the single-leg analogue (drop the gluing, piece
  (i)): a leg-native `ofNormals G ends q₀` rigid on `V(G)` at one seed ⟹ `HasFullRankRealization k G`,
  via N7b-0 + the device closure. This is the *single-seed-rigidity ⟹ full-rank-realization* bridge the
  witness-transfer consumes per leg. **Scoping correction:** *producing* the rigid seed for `H` from
  forest data is multi-commit/research-shaped (a single spanning forest is `(D−1)/D` short of full
  rank; needs the `D`-fold `M(H̃)`-base packing). **Forest-packing brick GREEN (this commit):**
  `Graph.IsKDof.exists_isBase_isForestPacking` (`Deficiency.lean`) — the `D`-fold `M(H̃)`-base packing
  itself: a rigid `H` has a base `B` of `M(H̃)` packing into `D` edge-disjoint forests of `H̃ ↾ B`
  with `|B| = D(|V(H)|−1)`. A true structural fact (may serve a future Track-B consumer). **Row-stacking
  ruled OUT (this commit, recon):** stacking the `D` forests' rows over-counts by `(D−1)` and isn't
  jointly independent (research-shaped extensor-span genericity), *and* is off-path (N7b-0 extracts the
  full count directly from rigidity-on-`V`). **Witness-transfer prerequisite GREEN (this commit):**
  `exists_rigidOn_ofNormals_of_hasFullRankRealization` — the IH's `HasFullRankRealization k G` gives a
  *non-empty rigid `ofNormals` locus* (`∃ ends q, (ofNormals G ends q).toBodyHinge` rigid on `V(G)`),
  the first decomposable brick of option (b). **Per-leg rank polynomial GREEN:**
  `exists_rankPolynomial_of_rigidOn` — a rigid leg ⟹ a nonzero (at the seed) Gram-det
  `MvPolynomial` whose every non-root gives the leg's full `D(|V|−1)` `panelRow`-subfamily LI; built on
  the reused `exists_good_realization_ofParam` coordinatization + the new mirror
  `exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`,
  exposes the witnessing minor). **Rank-polynomial CONSUMER GREEN (this commit):**
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` — the forward half: any non-root `q`
  of the leg's rank polynomial gives the leg rigid on `V(G)` *at `q`* (subfamily LI at `q` ⟹
  `dim Z(G,q) ≤ D` ⟹ N3), the per-leg brick the shared-seed coupling consumes at the common `q₀`.
  **Coupling RED — recon found two gaps (this commit), not a one-commit assembly:** **(G1)** building
  each leg's rank polynomial needs a *transversal*-rigid seed, which the bare IH does not supply;
  **(G2)** the splice needs general position at the shared non-root, which `Q_H·Q_c` does not give
  (needs a third general-position factor). Both are the genuine KT §6.2 panel-intersection geometry —
  see *Decisions* / *Blockers* / *Hand-off*.
- [ ] **N6** `lem:case-I-realization` — compose N4 + N5 + the green glue
  (`isInfinitesimallyRigidOn_union_of_inter`) + device ⇒ discharges
  `theorem_55.hcontract`. **Largely subsumed by `hasFullRankRealization_of_splice`**
  (which already ends at `HasFullRankRealization`); N6 = feed it the seed N5 builds
  + the IH realizations (via N4).
  - [x] **N6a** non-simple Case I producer (KT Lemma 6.2), general-position-free. **GREEN**
    (`hasFullRankRealization_of_splice_of_supportExtensor` + leg-native
    `…_of_supportExtensor_ofNormals`, axiom-clean, no `\leanok` — infra below the red Case-I nodes).
    The motive-independent first node of the two-motive build order: the splice producer takes
    *transversal hinges* (`hsupp`) directly instead of *general position* (`hgp`), strictly
    generalizing `hasFullRankRealization_of_splice` (now a thin GP corollary of it). General
    position implies transversal hinges; they part ways in the non-simple equal-panel case (parallel
    boundary normals ⟹ GP fails, hinges stay transversal). So non-simple Case I consumes the *bare*
    motive and supplies it back — no motive strengthening, no Phase-20 touch. De-risks the splice
    plumbing on the bare motive, as the design's build order intended. The remaining red content
    (the shared seed `q₀`) is unchanged.
  - [x] **Two-motive split** — the general-position realization motive + forgetful map. **GREEN**
    (`HasGenericFullRankRealization` + `hasFullRankRealization_of_generic`, axiom-clean, no `\leanok` —
    infra below the red Case-I nodes). The design build-order's node after N6a
    (`notes/Phase22-realization-design.md` §5): a *separate* unconditional-GP motive
    `∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧ Q rigid on V(G)` carried only through the simple Case-I
    cases, + the one-line `HasGenericFullRankRealization → HasFullRankRealization` forgetful map.
    `theorem_55` untouched (the spike ruled out the `(G.Simple → GP)` single-conjunct: `splitOff`
    doesn't preserve simplicity). **Dissolves gap (G1) at the source**: the GP motive carries the
    general-position seed the producers need; a GP parent seed is GP for every leg (`withGraph` keeps
    the same normals), discharging `hgp`/`hne`. Gates N6b/N6c (now also need (G2)).
  - [x] **(G2) general-position polynomial factor**. **GREEN** (`exists_generalPosition_polynomial`
    + helpers `pair_linearIndependent_of_leading_minor_ne_zero`, `pairLeadingMinorPoly` /
    `eval_pairLeadingMinorPoly`, axiom-clean, no `\leanok` — infra below the red Case-I nodes). The
    design build-order's node after the two-motive split (`notes/Phase22-realization-design.md` §3
    Track A, §2 row "(G2)"): a single nonzero `MvPolynomial (α × Fin (k+2)) ℝ` whose non-roots are
    exactly the general-position assignments — the product over `Finset.univ.offDiag` of the leading
    `2 × 2` minor `pairLeadingMinorPoly a b := X_{(a,0)}·X_{(b,1)} − X_{(a,1)}·X_{(b,0)}`. Non-root ⟹
    every pair's leading minor `≠ 0` (`Finset.prod_ne_zero_iff`) ⟹ pair LI (the minor helper, the
    coordinate-level generalization of `momentCurve_pair_linearIndependent`) ⟹ GP. Nonzero witnessed:
    the moment-curve seed makes each factor the Vandermonde det `param b − param a ≠ 0`. **Closes gap
    (G2).** Gates N6b/N6c (the triple-product assembly + green splice).
  - [ ] **N6b/N6c** simple Case I (KT Lemma 6.3/6.5) — the shared-seed coupling. **RED, but the
    leg-restricted per-leg bricks are now GREEN** (this commit): the recon (prior commit) found the
    all-edges `exists_rankPolynomial_of_rigidOn` inapplicable to a proper-subgraph leg (`hends :
    ∀ e : β, GH.IsLink e …` unsatisfiable). **Fixed by the leg-restricted chain (this commit):**
    `span_panelRow_linking_eq_rigidityRows` (linking-edge panel rows span the rigidity rows, `hends`/
    `hne` on linking edges only) → `exists_independent_panelRow_subfamily_of_rigidOn_linking` (rigid
    leg ⟹ `D(|V|−1)` independent panel rows, all linking, `hsupp`) → `exists_rankPolynomial_of_rigidOn_linking`
    (the leg-restricted producer: rigid leg ⟹ nonzero Gram-det `MvPolynomial` supported on linking
    edges) → `…_rankPolynomial_ne_zero_linking` (the matching consumer: non-root + `hsupp` ⟹ leg rigid
    at that point). The `ends`-swap brick `infinitesimalMotions_ofNormals_eq_of_ends_swap` (prior
    commit) supplies the leg's `hends` (link of every linking edge, automatic up to swap). **What
    remains red for N6b/N6c:** the *coupling assembly* — multiply the two legs' leg-restricted rank
    polynomials × the (G2) factor `exists_generalPosition_polynomial`, take a shared non-root via
    `MvPolynomial.exists_eval_ne_zero`, re-derive each leg rigid (`…_ne_zero_linking`) + GP at it, feed
    `hasFullRankRealization_of_splice_ofNormals`. See *Decisions* / *Blockers* / *Hand-off*.

**Track B — Case II/III producer at `d=3` (the crux, KT §6.3 + §6.4.1).**
- [ ] eq. (6.12) degenerate placement (`p1(vb)=q(ab)` reproduces the `e₀` row;
  the green N7b-0/1/2/3 + glue feed it) — gives `+(D−1)`, one short.
- [ ] **Lemma 6.10** (`d=3`, 3 candidates): Claim 6.11 (combinatorial↔linear,
  redundant `ab`-row), Claim 6.12 (extensor-span genericity via Lemma 2.1).

**Assembly (may defer to Phase 23 with Thm 5.5's completion).**
- [ ] `prop:rigidity-matrix-prop11` `hub` brick (Phase-19 partition count).
- [ ] `thm:theorem-55` flips green once the producers land.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Leg-restricted rank-polynomial chain — restrict the spanning identity to *linking* edges
  (2026-06-04).** Discharged the N6b recon's `hends`-over-all-`β` obstruction by mirroring the
  whole `exists_rankPolynomial_of_rigidOn` chain with the panel-row family and rigidity-row span
  restricted to the *linking-edge* subtype `{i // GH.IsLink i.1 (ends i.1).1 (ends i.1).2}`. The
  spanning identity `span_panelRow_linking_eq_rigidityRows` then needs `hends`/`hne` only on linking
  edges (`hends : ∀ e u v, IsLink e u v → IsLink e (ends e).1 (ends e).2` + `hne` on linking edges)
  — the form a proper-subgraph leg supplies (its `ends` is the parent's, recording the link of every
  edge that links, automatic up to swap via `infinitesimalMotions_ofNormals_eq_of_ends_swap`). The
  four bricks (`span_…_linking`, `…_subfamily_of_rigidOn_linking`, `…_rankPolynomial_of_rigidOn_linking`
  producer, `…_rankPolynomial_ne_zero_linking` consumer) carry a `hsupp` (every witnessed index
  links) so each downstream `⊆`-inclusion draws its per-index link witness from `hsupp`, not the
  all-edges `hends`. Coordinatization + rank-nullity verbatim from the all-edges forms. All
  axiom-clean, no `\leanok` flip, no blueprint entry (infra below the red Case-I nodes). One FRICTION
  recurrence note (the subtype-coerced `panelRow` `rw` failing on the build side). See *Hand-off*.
- **N6b recon: the simple Case-I coupling is not a clean assembly; the `ends`-swap brick is the
  first decomposable step (2026-06-04).** Ran the producer recon (`DESIGN.md` *Constructibility
  recon …*) on the hand-off's projected N6b ("the assembly commit, no new analytic brick"). **Finding:
  it is not a clean assembly.** The plan applies `exists_rankPolynomial_of_rigidOn` per leg, but that
  brick (whole `panelRow`/`span_panelRow_eq_rigidityRows` chain) needs `hends : ∀ e : β, GH.IsLink e …`
  — *every* edge label of the realized graph must link, so the panel rows span all rigidity rows — which
  a proper-subgraph leg `GH ≤ G` does not satisfy, and the `IsLink` subgraph direction is the *wrong way*
  to derive it. The type-level plan was blind to the *quantifier domain* of the brick's hypotheses
  (a fresh sharpening of the recon rule). N6b needs a *leg-restricted* rank polynomial. **First green
  brick toward it:** `infinitesimalMotions_ofNormals_eq_of_ends_swap` — leg rigidity is invariant under
  swapping an edge's two endpoints (support extensor flips sign by `panelSupportExtensor_swap`, but the
  hinge constraint references only its span, closed by the span-keyed sibling
  `infinitesimalMotions_eq_of_isLink_span_supportExtensor`), the start of re-expressing a leg's IH
  rigidity (own `ends_H`) at the parent's `ends`. No `sorry` committed; the coupling stays red. See
  FRICTION `[resolved] The Case-I N6b coupling is NOT a clean assembly …` + *Hand-off*.
- **(G2) general-position polynomial factor — the off-diagonal product of leading `2×2` minors
  (2026-06-04).** Built the design build-order's node after the two-motive split
  (`notes/Phase22-realization-design.md` §3 Track A): `exists_generalPosition_polynomial` — a nonzero
  `MvPolynomial (α × Fin (k+2)) ℝ` whose non-roots are exactly the general-position assignments,
  taken as `∏_{(a,b) ∈ Finset.univ.offDiag} pairLeadingMinorPoly a b` with
  `pairLeadingMinorPoly a b := X_{(a,0)}·X_{(b,1)} − X_{(a,1)}·X_{(b,0)}`. **Why fixed coords 0,1, not
  a general minor:** the design suggested "some `2×2` minor `≠ 0`"; but the *leading* (0,1) minor is
  exactly the one the moment-curve seed makes nonzero (its Vandermonde det `param b − param a`), so
  fixing 0,1 matches `momentCurve_pair_linearIndependent`'s own proof and the witnessed non-root drops
  out for free — no need to range over minors. The minor⟹LI helper
  `pair_linearIndependent_of_leading_minor_ne_zero` is the coordinate-level generalization of
  `momentCurve_pair_linearIndependent` (`linear_combination` on the 0,1 evaluations, then the nonzero
  minor rules out the degenerate `c₂` branch). First-try, axiom-clean; the only deprecation
  (`push_neg`, already-documented FRICTION) avoided via `rw [not_or, not_not, not_not]`. Closes gap
  (G2). Infra below the red Case-I nodes, no `\leanok` flip; no blueprint entry. See *Hand-off*.
- **Two-motive split — the general-position realization motive + forgetful map (2026-06-04).** Built
  the design build-order's node after N6a (`notes/Phase22-realization-design.md` §1.4 / §5): added a
  *separate* unconditional-general-position motive
  `HasGenericFullRankRealization k G := ∃ Q, Q.graph = G ∧ Q.IsGeneralPosition ∧ Q rigid on V(G)`
  (placed next to `HasFullRankRealization`) + the one-line forgetful map
  `hasFullRankRealization_of_generic` (drop the GP conjunct). **Why the split, not the single-conjunct
  (A):** the `Simple`-threading spike (prior commit) ruled out `(G.Simple → GP)` — `splitOff` does not
  preserve simplicity (KT Lemma 6.7), so that conjunct's IH lands on the wrong graph at `hsplit`. The
  separate motive is carried only through the simple Case-I cases (KT's "nonparallel, if simple"),
  `theorem_55`'s bare statement untouched, no Phase-20 node touched. **Dissolves gap (G1) at the
  source:** the GP motive carries the general-position seed the producers (`_splice_ofNormals`,
  `exists_rankPolynomial_of_rigidOn`) need; a GP parent seed is GP for every leg (`withGraph` keeps the
  same normals). Infra below the red Case-I nodes, no `\leanok` flip; no blueprint entry. First-try,
  axiom-clean; no friction. Gates N6b/N6c (which also need (G2)). See *Hand-off*.
- **N6a — non-simple Case I producer via the `hsupp`-direct splice (2026-06-04).** Built the
  motive-independent first node of the two-motive build order: factored
  `hasFullRankRealization_of_splice`'s `hgp`→`hsupp` derivation out into a strictly-more-general
  producer `hasFullRankRealization_of_splice_of_supportExtensor` taking *transversal hinges*
  (`∀ e, supportExtensor e ≠ 0`) directly; the original `hasFullRankRealization_of_splice` is now a
  one-line corollary feeding it `supportExtensor_ne_zero_of_isGeneralPosition`. **Why this is the
  honest N6a:** N7b-0 (`exists_independent_panelRow_subfamily_of_rigidOn`) only ever needed `hsupp`,
  not `hgp` — general position was over-strong. KT's non-simple Lemma 6.2 sets two boundary panels
  *equal* (parallel normals ⟹ general position fails) while the retained hinges stay transversal, so
  the non-simple case consumes the *bare* motive and supplies it back, no motive strengthening,
  `theorem_55` untouched. The leg-native form `…_of_supportExtensor_ofNormals` swaps
  `withGraph`→`ofNormals` by the `rfl` bridge (`ofNormals_withGraph` + `toBodyHinge_withGraph`), no
  `rw` — recurrence of the documented defeq (TACTICS-QUIRKS § 25). No new friction. The remaining red
  content (the shared seed `q₀` of `lem:case-I-splice-placement`) is unchanged.
- **`Graph.Simple`-threading spike — `Simple` does NOT thread cleanly; take the two-motive split
  (2026-06-04, docs-only spike).** The design-pass decision was to strengthen the
  `HasFullRankRealization` motive to carry general position (KT's "nonparallel, if simple"), with two
  candidate shapes: **(A)** one motive with a `G.Simple → Q.IsGeneralPosition` conjunct (needs `Simple`
  threaded through the reduction), or the **two-motive split** (a separate unconditional-GP motive
  carried only through the simple cases + a one-line forgetful map). The spike determines (A) vs. the
  split. **Finding: (A) is not viable; take the two-motive split.** Decisive structural fact:
  **`splitOff` does not preserve simplicity.** `G.splitOff v a b e₀` (`Induction.lean:572`) adds the
  fresh edge `e₀` linking `a`-`b` *unconditionally*; if simple `G` already carries an `a`-`b` edge `f`
  with `a, b ≠ v` (which survives — `f ≠ e₀`, avoids `v`), the result has two `a`-`b` edges. This is
  exactly KT Lemma 6.7's caveat and the reason KT splits Case I three ways by simplicity. Hence even
  the *no-threading* read of (A) (`P G := … ∧ (G.Simple → GP)`, which needs no `Simple` through
  `minimal_kdof_reduction`) fails: at `hsplit` a *simple* parent `G` recurses on
  `P (G.splitOff v a b e₀)`, whose split-off child may be **non**-simple, so the IH's conditional
  `(child.Simple → GP)` delivers nothing for the simple parent — the conditional is on the wrong graph.
  Confirmed no existing simplicity-preservation lemma on `splitOff`/`rigidContract`. The split also
  touches no Phase-20 node (`minimal_kdof_reduction` unchanged) and mirrors KT's own Lemma-6.2-bare /
  6.3-6.5-nonparallel bifurcation. Spike is docs-only (no Lean / `\leanok` / blueprint edits); it
  re-points the hand-off. Build green on `AlgebraicInduction`. See *Hand-off*; design doc
  `notes/Phase22-realization-design.md` §1.4.
- **N5 rank-polynomial consumer + coupling constructibility recon (2026-06-04).** Built
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (`AlgebraicInduction.lean`,
  axiom-clean), the forward half of `exists_rankPolynomial_of_rigidOn`: a non-root `q` of the leg's
  rank polynomial ⟹ the leg rigid on `V(G)` *at `q` itself* (subfamily LI at `q` forces
  `finrank(span rigidityRows) ≥ #s`, so `dim Z(G,q) ≤ D` by rank–nullity, then N3) — the per-leg brick
  the shared-seed coupling consumes at the common `q₀`. **But the recon
  (`DESIGN.md` *Constructibility recon …*) on the planned coupling found it is NOT the one-commit
  assembly the prior hand-off claimed:** two real gaps the type-level plan was blind to. **(G1)**
  `exists_rankPolynomial_of_rigidOn` (the polynomial *producer*) needs a *transversal*-rigid seed
  (`hne`), but the IH gives only a *bare* rigid `HasFullRankRealization` (no general position) — a rigid
  framework can have a degenerate hinge, and the whole `panelRow`/N7b-0 span argument needs transversal
  hinges. **(G2)** the splice needs `hgp` (general position) at the shared non-root, which `Q_H·Q_c`
  does not give — coupling it in needs a third nonzero factor whose non-roots are general-position
  (a Vandermonde-type brick that does not exist yet). Both are the genuine KT §6.2 panel-intersection
  geometry (eq. 6.6): the construction *builds* a specific general-position rigid realization, it does
  not take an arbitrary rigid IH one. The consumer brick is honest (input is the satisfiable
  non-root LI clause, deliverable is rigidity at that point); the producer node stays red.
- **N5 per-leg rank polynomial via a new constructive multivariate mirror (2026-06-04).** Built
  `exists_rankPolynomial_of_rigidOn` (`AlgebraicInduction.lean`), the genuine next brick of the seed
  witness-transfer (option (b)): a rigid leg ⟹ a single `MvPolynomial` nonzero at the seed, every
  non-root of which gives the leg's full `D(|V|−1)` `panelRow`-subfamily LI. The existing
  multivariate device bricks (`exists_le_finrank_span_polynomial` etc.) only return `∃ p, good`,
  consuming the polynomial inside `MvPolynomial.exists_eval_ne_zero`; coupling *two* legs needs the
  polynomial *exposed* (multiply them, funext the product once). So mirrored a constructive sibling
  `exists_polynomial_ne_zero_of_linearIndependent_at` (`Mathlib/LinearAlgebra/Matrix/Rank.lean`) that
  returns the witnessing Gram-det minor `Q` + the `eval q Q ≠ 0 → rows LI` upgrade. The molecular
  brick reuses `exists_good_realization_ofParam`'s coordinatization (`annihRowPoly` coords, body-sign
  scale) verbatim, plugged into the mirror; N7b-0 supplies the full-size `s`. Honest per the gate
  (input is the satisfiable `hrig`; deliverable is the seed's rank polynomial). Two FRICTION resolved
  entries (`rcases hej : e j with ⟨a,t⟩` destructure-then-`simp`; `RingHom.id ℝ` in the specialized-
  minor LI lemma) + TACTICS-QUIRKS § 4 cross-ref. See *Hand-off*.
- **N5 witness-transfer prerequisite: non-empty rigid `ofNormals` locus from the IH (2026-06-04).**
  Built `exists_rigidOn_ofNormals_of_hasFullRankRealization` (`AlgebraicInduction.lean`), the first
  decomposable brick of the seed witness-transfer (option (b)) the prior hand-off recommended and
  demanded be decomposed math-first. The decomposition: the transfer needs each leg's IH (`∃ Q,
  Q.graph = G ∧ Q rigid on V(G)`) repackaged in `ofNormals` shape, since the legs must be coupled on
  *one* free-normal seed. The repackaging is trivial geometry but a real Lean brick: `Q` is *literally*
  an `ofNormals` (`ofNormals Q.graph Q.ends (fun p ↦ Q.normal p.1 p.2) = Q`, `rfl`), so `subst` the
  graph conjunct and the existence closes by defeq. Honest per the gate (no rank assumed — the IH's
  existence statement is the only input). The remaining red content of option (b) is now exactly the
  multivariate non-zero-product / `MvPolynomial.funext` coupling step. Infra below the red Case-I
  nodes, no `\leanok` flip; no blueprint entry (a small bridge producer, like its
  `_ofNormals`/`_ofParam`/`_rigidOn_seed` siblings). See *Hand-off*.
- **N5 row-stacking brick FAILS the constructibility recon — skip it (2026-06-04, docs-only).** Ran
  the producer-scrutiny recon the prior hand-off + the `exists_isBase_isForestPacking` doc-comment
  demanded before scheduling the "stack the `D` forests' rows to `D(|V(H)|−1)`" brick. Two findings,
  both fatal: (i) the arithmetic doesn't close — naive stacking over-counts by a factor `(D−1)` and the
  rows aren't jointly independent, so the real content is the KT §6.2 extensor-span genericity
  (research-shaped); (ii) it's off-path — N7b-0 already gives the full count from rigidity-on-`V`, so
  the forest packing only ever fed the per-leg *seed*. Options (a)/(b) thus collapse to one obstruction:
  the seed witness-transfer (hand-off re-pointed there). Forest-packing brick stays green (structural).
  Full arithmetic → FRICTION dead-end #4; rule → `DESIGN.md` *Constructibility recon before a producer
  build*.
- **N5 rigid-block forest-packing brick (2026-06-04).** Built `Graph.IsKDof.exists_isBase_isForestPacking`
  (`Deficiency.lean`), the first decomposable step of Hand-off option (a) — the `D`-fold `M(H̃)`-base
  packing the prior hand-off named as option (a)'s genuine new content. A rigid `H` (`def(H̃)=0`) has a
  base `B` of `M(H̃)` packing into `D` edge-disjoint forests of `H̃ ↾ B`, `|B| = D(|V(H)|−1)`. Clean
  three-step proof on green infra: `exists_isBase` → `matroidMG_indep_iff` + `tutte_nash_williams` (base
  independent ⟹ sparse ⟹ forest packing) → `isBase_ncard_add_deficiency_eq` with `def=0` (count). The
  `↾ B` is forced (over-braced rigid `H` has extra edges, so whole `H̃` not sparse). Formalizes the
  prose-only "`G̃` packs `D` spanning trees" from the `IsKDof`/`IsRigidSubgraph` doc-comments. Placed in
  `Deficiency.lean` (about `matroidMG`/`IsKDof`/`mulTilde`), infra below the red Case-I nodes, no
  `\leanok` flip. No friction (every step first-try; `rw [hrig]` def-unfold per TACTICS-GOLF § 4).
- **N5 H-leg single-leg producer + scoping correction (2026-06-04).** Built
  `hasFullRankRealization_of_rigidOn_seed`, the single-leg analogue of
  `hasFullRankRealization_of_splice_ofNormals` (pieces (ii)+(iii), gluing dropped): one leg-native
  `ofNormals G ends q₀` rigid on `V(G)` at a seed ⟹ `HasFullRankRealization k G`. Honest per the gate
  (concludes the generic realization from the *satisfiable* single-seed rigidity `hrig`, doesn't assume
  it). **Correction to the prior hand-off:** the recommended "H-leg witness via
  `ofParam_rankHypothesis_iff_pinnedMotionsOn` + forest data + count" is *not* a one-commit producer of
  the rigid seed — a single spanning forest gives `(D−1)·(|V(H)|−1)` rows, `(D−1)/D` short of full
  `D(|V(H)|−1)`; full rank needs a `D`-fold `M(H̃)`-base packing (≈ `theorem_55` on `H`). The seed
  construction stays research-shaped; this brick packages it honestly. Infra below the red producer
  nodes, no `\leanok` flip; no blueprint entry (a small bridge producer, like its `_ofNormals`/`_ofParam`
  siblings). See *Hand-off*.
- **Case-I seed route: free `ofNormals`, not moment-curve `ofParam` (2026-06-04, coordinator + user
  decision at the "assess the math" pause).** The three N5 scaffolding commits kept deferring the seed
  because the `_ofParam` specialization (3rd commit) silently needs the IH's *free-normal* realization
  coerced onto the moment-curve subvariety — an extra genericity sub-lemma the `∃ Q, …` motive does not
  supply (a Zariski-open rigidity locus in the full normal space need not contain a moment-curve point).
  Decision: build the witness-transfer in the full free-normal space via the device's non-zero-product
  polynomial engine — both legs' rank-determinants are non-zero polynomials in the shared normals, so
  their product (× general position) has a common non-root `q₀` by `MvPolynomial.funext` — consuming the
  green `_ofNormals` brick; the `_ofParam` brick is kept but bypassed. Turns the seed into a ~2–3-commit
  sub-build on green infra (device, B0 row coordinatization, splice glue, Lemma 5.1, funext mirror), not
  a sub-phase. See *Hand-off*.
- **N5 moment-curve seed specialization (2026-06-04).** Specialized the leg-native splice
  `hasFullRankRealization_of_splice_ofNormals`'s free seed `q₀` (+ its `hgp`) to the moment-curve
  assignment `ofParam GH/Gc ends param` at injective `param`. `isGeneralPosition_ofParam` discharges
  general position for free, so `hgp` leaves the consumer's obligation: the remaining Track-A gap is
  exactly "exhibit one injective `param` making both legs rigid" — the genericity collapsed to a
  single injective real assignment, KT's eq. (6.6) read off the moment curve. The leg hypotheses are
  stated in the explicit `ofNormals`-at-moment-curve form (not `ofParam`): the framework defeq across
  the heavy `IsInfinitesimallyRigidOn` term heartbeat-times-out by `rw`/lazy application, so the heavy
  term must match syntactically and only the cheap `IsGeneralPosition` defeq goes through a `have`
  (FRICTION). Infra below the still-red producer nodes, no `\leanok` flip; the seed stays red.
- **N5 leg-native restatement (2026-06-04).** The prior splice brick stated each leg as
  `withGraph GH` of the *parent* `ofNormals G ends q₀`; but a seed construction builds each
  leg as its *own* `ofNormals GH ends q₀` (same `q₀`, different graph). `ofNormals_withGraph`
  (`(ofNormals G ends q).withGraph G' = ofNormals G' ends q`, `rfl` — `withGraph`/`ofNormals`
  keep the same graph-independent `normal`/`ends`) bridges the two, so the leg-native variant
  `hasFullRankRealization_of_splice_ofNormals` is a one-line corollary. Net: the remaining
  Case-I gap is now stated in the exact shape a witness-transfer must hit, with no graph-swap
  noise. The bricks are infra below the still-red `lem:case-I-splice-placement`/`-realization`,
  no `\leanok` flip; the seed `q₀` itself stays red (honesty gate). The `rw`→defeq lesson is in
  FRICTION (sibling of the `map_eq_zero_iff` entry; TACTICS-QUIRKS § 25).
- **N5 decomposition recon (2026-06-04, before/with the first brick).** Ran the producer
  recon the blueprint/hand-off demanded before scheduling N5 as a build. **Finding: N5 is
  much narrower than "splice two placements."** (a) The "panel-transversality lemma" is
  already green — a panel is its normal `n_v`, transversal ⟺ independent normals
  (`panelSupportExtensor_ne_zero_iff`), and `momentCurve` gives general position for any
  `|α|`. (b) `withGraph` keeps the same `normal`, so both legs ride one normal assignment —
  no literal placement-gluing. (c) The genuine remaining obstruction is the **common-placement
  witness-transfer**: exhibit one seed `q₀` with both legs rigid (eq. 6.6). The first brick
  `hasFullRankRealization_of_splice` composes three green pieces (splice seed → N7b-0 → device)
  and isolates that obstruction into *satisfiable* hypotheses, honest per the producer-scrutiny
  gate (concludes `HasFullRankRealization`, doesn't assume it). N6 is now mostly this brick.
- **N4a stated about `Preconnected`, regime `[NeZero (bodyHingeMult n)]`.** The
  "`H̃` connected on `V(H)`" target is `(G.mulTilde n).Preconnected` (mathlib `Graph`
  preconnectedness; `V(G̃) = V(G)` definitionally). The deficiency machinery
  (`crossingEdges`/`partitionDef`/`deficiency`) is all phrased on `G`'s edges in `β`,
  so the proof never touches `G̃`'s edge type except to lift one `G`-edge to its copy-`0`
  in `G̃` (`mulTilde_isLink`) for the crossing-free-cut step — which forces the `D ≥ 2`
  regime (a copy must exist). Matches `spanningVerts_edgeMultiply`'s `[NeZero …]`. No
  nonemptiness hypothesis: the contradiction extracts its two vertices from
  `¬ Preconnected` itself, and `Preconnected` is vacuous on the empty graph.
- **N4 constructibility recon (2026-06-04, before any build).** Ran the producer
  recon (`blueprint/CLAUDE.md` *the honesty gate*, second half) on N4. **Finding:
  N4 is the graph↔matroid correspondence Phase 20 deliberately deferred, and the
  underlying matroid fact is non-trivial — not the one-commit "build-shaped" node
  the launch plan implied.** The target equality is
  `matroidMG (G.rigidContract H r) = matroidMG G ／ E(H̃)`. Edge-set check: both
  grounds equal `(E(G) \ E(H)) × Fin D`, so the ground sets *do* match. But:
  - `M(G̃)` is the `D`-fold *union* of cycle matroids restricted to `E(G̃)`
    (`Deficiency.lean:141`). **`Matroid.Union` does not commute with contraction**
    in general (`Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`), so the per-cycle-matroid fact
    `cycleMatroid_contract` (vendored `Matroid/Graphic.lean:177`,
    `(G/[E(H),φ]).cycleMatroid = G.cycleMatroid ／ E(H)`) does **not** push
    through the union to give the whole-`matroidMG` equality directly.
  - **Refinement (2026-06-04, second recon — sharper than the bullet above).**
    `cycleMatroid_contract` does not even *apply* to the per-cycle-matroid step,
    let alone fail to push through the union. The recon above pictured the matroid
    side as `cycleMatroid ／ E(H̃)` (a genuine matroid contraction by the
    contracted-out fibers) and the graph side as the same contraction. But the
    *graph* `rigidContract` is `(G ＼ E(H)).map (collapseTo r V(H))` — a pure
    **vertex-relabel `map`** with the contracted edges `E(H)` *deleted* (so on the
    cycle-matroid side those fibers are gone, not contracted). On the matroid side,
    `M(G̃) ／ E(H̃)` *contracts* those same fibers. Reconciling a graph that
    *deletes* `E(H)` and *relabels vertices* with a matroid that *contracts* `E(H̃)`
    is the classical Whitney fact "contracting a connected edge set in the cycle
    matroid = collapsing its vertex set in the graph" — and there is **no vendored
    `cycleMatroid`-under-`map`/iso lemma** (checked: `Matroid/Graphic.lean` has
    `cycleMatroid_{restrict,deleteEdges,contract,deleteVerts_isolatedSet}`, no
    `cycleMatroid_map`). `cycleMatroid_contract`'s own hypothesis
    `(G ＼ E(H) ↾ E(H)).connPartition.IsRepFun (collapseTo r V(H))` is *false* here:
    `G ＼ E(H) ↾ E(H)` has empty edge set (discrete connPartition), so collapsing all
    of `V(H)` to `r` is not a rep-fun. So the per-cycle-matroid step is itself a
    from-scratch build (cycleMatroid under vertex-collapse map), and it bottoms out
    on **connectivity of `H̃`** (rigid ⟹ packs `D` spanning trees ⟹ connected on
    `V(H)`, so the collapse is the legitimate connected-contraction).
  - The whole green substrate (`contract_matroidMG_deficiency_eq`,
    `contract_minimality_transport`, `contraction_isMinimalKDof`) reasons
    *directly on the matroid contraction* `M(G̃)／E(H̃)` and explicitly says "No
    graph↔matroid `map` correspondence is needed" — precisely because the
    correspondence is the deferred hard part.
  - The viable route is **independence-level** (`Matroid.ext_indep`), mirroring
    how `matroidMG_restrict_mulTilde` (`Deficiency.lean:212`) handled *restriction*
    via the sparsity characterization `matroidMG_indep_iff` rather than a union
    identity. The graph side is favorable: `rigidContract = (G.deleteEdges
    E(H)).map (collapseTo r V(H))`, and `contract_eq_map_of_disjoint`
    (`Matroid/Graph/GraphLike/Contract.lean:78`) gives `G/[C,φ] = φ ''ᴳ G` when
    `Disjoint E(G) C` — which holds after `deleteEdges E(H)` (already green as
    `rigidContract_eq_contract`). But the `ext_indep` is **not** a `restrict`-style
    one-screen proof: contraction-independence (`Matroid.Indep.contract_indep_iff` /
    the basis form) reads `(M(G̃) ／ E(H̃)).Indep I ↔ I ⊓ E(H̃) = ∅ ∧ M(G̃).Indep (I ∪ J)`
    for an `M(G̃)`-basis `J` of `E(H̃)`, i.e. `(G̃ ↾ (I ∪ J))` is `(D,D)`-sparse;
    the RHS wants `(rigidContract.mulTilde ↾ I)` `(D,D)`-sparse. Equating those two
    sparsities is the **Whitney rank-of-contraction identity** at the `(D,D)`
    boundary regime (the collapse changes `spanningVerts` counts by `|V(H)|−1`),
    *not* a congruence like `isSparse_restrict_mulTilde_congr`. **Budget N4 as a
    several-node sub-build** (connectivity-of-`H̃` brick → cycleMatroid-under-collapse
    → union-level independence bridge), not one commit; or pivot to **Track A's N5 /
    Track B** (N4 gates only N6, the Case-I composer).
- **N4b correction (2026-06-04, on building): `cycleMatroid_contract` DOES apply — the
  second recon mis-read its hypothesis.** The recon (refinement bullet above) claimed the
  per-cycle-matroid step needs a from-scratch `cycleMatroid`-under-collapse build because
  `cycleMatroid_contract`'s `IsRepFun` hypothesis was "false here, on `(G ＼ E(H) ↾ E(H))`".
  That graph is wrong: `cycleMatroid_contract {φ} (hφ : H.connPartition.IsRepFun φ) (hHG : H ≤ G)`
  takes the rep-fun on the **subgraph being contracted**, and that subgraph is `H.mulTilde n`
  (whose `connPartition` is *not* discrete). N4a (`(H̃).Preconnected`) makes `H̃`'s `connPartition`
  a **single class** `V(H)`, so `collapseTo r V(H)` (sends `V(H) ↦ r`, else id) is a genuine
  rep-fun — `rigidContract_collapseTo_isRepFun`. The graph side then needs only
  `rigidContract_eq_contract'` (the direct `G̃ /[E(H̃), φ]` form, no inner `＼`, via
  `map_deleteEdges_comm`) + `mulTilde_rigidContract` (edge mult. commutes with contraction).
  So N4b is **three short lemmas, one commit**, not a from-scratch Whitney build. **What
  remains genuinely hard is N4c** (lifting the per-cycle-matroid identity through `Matroid.Union`
  to `matroidMG`): there the union↔contraction non-commutation (first recon bullet) still bites,
  so N4c routes via `ext_indep` + contraction-independence at the `(D,D)` boundary, as planned.
  **Lesson:** the constructibility recon under-checked the *exact vendored hypothesis* — read the
  lemma's binder, not a paraphrase, before declaring it inapplicable.

- **N4c crux input is abstract: rank-saturation ⟹ per-factor `M`-basis split (2026-06-04).**
  The genuinely-hard crux (union↔contraction non-commutation) bottoms out on a clean *abstract*
  matroid fact, isolated as `Matroid.Union_pow_isBasis'_split_of_rk_saturated` (under
  `namespace Matroid`, not `Graph` — it has no graph content). The rigidity input enters only as
  the saturation hypothesis `N.rk c = k·M.rk c`, supplied (next commit) by the def=corank bridge
  for a rigid `H`. The proof is a tight counting chain `|B| = k·M.rk c = ∑|Jᵢ| ≤ k·M.rk c`
  forcing each `|Jᵢ| = M.rk c` (basis). Both directions of the crux's `ext_indep` will consume it.

- **N4c saturation specialization: split (a) `rank M(H̃)` + (b) connected cycle rank (2026-06-04).**
  `union_cycleMatroid_rk_saturated_of_isKDof_zero` proves `N.rk E(H̃) = D · G̃.cyc.rk E(H̃)` as the
  product of two `|V(H)|−1` computations. (a) `N.rk E(H̃) = rank M(H̃)`: `matroidMG = N ↾ E(G̃)` and
  `E(H̃) ⊆ E(G̃)` give `N.rk E(H̃) = (matroidMG G).rk E(H̃)`, then `matroidMG_restrict_mulTilde` +
  `restrict_rk_eq` give `= rank M(H̃) = D(|V(H)|−1)` (def=corank, `def(H̃)=0`). (b) `G̃.cyc.rk E(H̃)
  = |V(H)|−1` via the new bridge `cycleMatroid_mulTilde_eq_restrict` (`H̃.cyc = G̃.cyc ↾ E(H̃)`, so
  the rank moves to `H̃`) + `Connected.eRk_cycleMatroid_restrict_add_one` (whose conclusion lands on
  `V(H̃) = V(H)`, *not* `V(G̃)` — the reason the rank must be moved into `H̃` first). The bridge
  lesson is in FRICTION `[resolved] [matroid] H.cycleMatroid = G.cycleMatroid ↾ E(H) …`.
- **N4c reduced, not closed, via the restrict↔contract commutation (2026-06-04).** Rather than
  fight `Union ／ C` head-on, both sides of N4c are rewritten over the common ground
  `S = E(G̃)\E(H̃)`: the contraction side uses mathlib's
  `Matroid.restrict_contract_eq_contract_restrict` (the *restrict*↔contract commutation, which
  **does** hold, unlike *union*↔contract), and the contracted side pushes N4b under the `Union`
  via `funext`. This isolates the irreducible union↔contraction crux to one matroid equality on
  `S` — a clean, honest, single-commit reduction that does not yet need the rigidity/forest-packing
  input (that input is what the *remaining* crux equality consumes). The three bricks are infra
  below the `lem:rigidContract-isMinimalKDof` blueprint node, so no `\leanok` flip.
- **N4c crux closed via the COUNT route, not the matching re-decomposition (2026-06-04).** The
  prior hand-off planned the crux `ext_indep` reverse via `union_indep_iff` + per-factor basis
  re-alignment — but that realignment is genuine matroid-union *matching* augmentation (an
  arbitrary `Ks` decomposition of `I ∪ J` is not factor-aligned with the `Jᵢ`, and naive fixes
  all fail; see FRICTION). The abstract crux `Union_pow_contract_eq_contract_of_rk_saturated`
  instead expands *both* matroids to their count conditions via `Union_pow_indep_iff_count`
  (`N.Indep E' ↔ ∀ Y ⊆ E', |Y| ≤ k·M.rk Y`), making the equivalence a symmetric `rk_submod` +
  `rk_mono` + `contract_rk_cast_int_eq` ℤ-arithmetic. Saturation enters only as `|J| = k·M.rk C`.
  The split lemma `Union_pow_isBasis'_split_of_rk_saturated` is thereby unused but kept. Full
  lesson + the matching obstruction in FRICTION `[resolved] [matroid] Union↔contraction …`.

- **N4 reconciliation closed in one commit, as the prior hand-off predicted (2026-06-04).** With
  N4c green, `rigidContract_isMinimalKDof` is a clean assembly, not a sub-build: unfold
  `IsMinimalKDof` into its two halves and transport each across N4c
  (`matroidMG_rigidContract_eq_contract`, `K.matroidMG = M(G̃)／E(H̃)`). The minimality half is a
  one-liner (`hN4c ▸ hB` + `edgeSet_rigidContract`'s `E(K) = E(G)\E(H)`). The deficiency half is
  the only arithmetic: `rank_add_deficiency_eq` on `K` gives `rank(K) + def(K) = D(|V(K)|−1)`;
  `rw [hN4c]` swaps `rank(K)` for `rank(M(G̃)／E(H̃))`, `hcons` (k=0) makes that `= D(|V(G)|−|V(H)|)`,
  and the exact count `|V(K)| = (|V(G)|−|V(H)|)+1` makes the ambient match, so `linarith` forces
  `def(K) = 0`. The two new bricks (`edgeSet_rigidContract`, `rigidContract_vertexSet_ncard`) are
  general structural facts about `rigidContract`, placed by its definition. The *exact* count
  (vs. `rigidContract_vertexSet_ncard_lt`'s `≤`) is the genuine new fact: `r ∈ V(H)` makes the
  collapse image *equal* `(V(G)\V(H)) ∪ {r}`, not just contained in it.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *Building a subtype-indexed `panelRow` membership: `by rw [panelRow, …]` fails on the
  anonymous-constructor index's unreduced coercion — pin it with `show F.panelRow ends (e,t₁,t₂) = _`*
  → FRICTION [resolved] *A `panelRow ends i` membership `rfl` whnf-times-out …* (Recurrence, build
  side; instance of TACTICS-QUIRKS § 4).
- *The N6b Case-I coupling is not a clean assembly — `exists_rankPolynomial_of_rigidOn` needs
  `hends : ∀ e : β, GH.IsLink e …`, which a proper-subgraph leg cannot satisfy; recon must read the
  hypothesis *quantifier domain*, not just the conclusion shape* → FRICTION [resolved] *The Case-I N6b
  coupling is NOT a clean assembly …*; DESIGN.md *Constructibility recon before scheduling a producer build* (fresh
  application).
- *`rw […]` won't close a defeq goal whose two sides differ only in a proof-term argument — finish with
  `exact lemma _ _`* → FRICTION [resolved] *`rw […]` won't close a defeq goal whose two sides differ only
  in a proof-term argument …* (sibling of TACTICS-QUIRKS § 25).
- *`obtain ⟨a,t⟩ := e j` on a bare term doesn't rewrite `(e j).1`/`(e j).2` occurrences — `rcases hej :
  e j with ⟨a,t⟩` then `simp only [hej]`* → FRICTION [resolved] *`obtain ⟨a, t⟩ := e j` on a term …* +
  TACTICS-QUIRKS § 4 (Related sub-note).
- *`linearIndependent_rows_of_specialized_submatrix_det_ne_zero` on rows already over `ℝ` — pass
  `φ := RingHom.id ℝ`, not the polynomial `eval`* → FRICTION [resolved] *…specialized minor on rows
  already over `ℝ` …*.
- *`exists_polynomial_ne_zero_of_linearIndependent_at` — constructive rank-witnessing polynomial mirror
  (exposes the Gram-det minor for cross-family coupling)* → FRICTION [mirrored]
  *`exists_polynomial_ne_zero_of_linearIndependent_at` …*; `Mathlib/LinearAlgebra/Matrix/Rank.lean`.
- *A `panelRow ends i` membership `rfl` whnf-times-out with `i` a coerced subtype — `rintro
  ⟨⟨e',t₁,t₂⟩, hi⟩` to expose a bare triple so the `rfl` is syntactic* → FRICTION [resolved] *A
  `panelRow ends i` membership `rfl` whnf-times-out …* (instance of TACTICS-QUIRKS § 4).
- *Repackaging a `HasFullRankRealization` witness as an `ofNormals` — `subst` the `Q.graph = G`
  conjunct, don't `rw` both sides (the `V(G)`-vs-`V(Q.graph)` mismatch)* → FRICTION [resolved]
  *Repackaging a `HasFullRankRealization` witness as an `ofNormals` …* (sibling of TACTICS-QUIRKS § 25).
- *A hypothesis on `(ofNormals GH ends q₀).toBodyHinge` passes directly to a brick wanting
  `…withGraph GH` — defeq, no `rw` bridge* → FRICTION [resolved] *A hypothesis stated on
  `(ofNormals GH ends q₀).toBodyHinge` …* (recurrence of TACTICS-QUIRKS § 25).
- *`ofParam`↔`ofNormals` defeq across a heavy `IsInfinitesimallyRigidOn` term heartbeat-times-out
  by `rw`/lazy application — state the hypothesis pre-converted, isolate the cheap defeq in a typed
  `have`* → FRICTION [resolved] *But: `ofParam`↔`ofNormals` defeq across a heavy
  `IsInfinitesimallyRigidOn` term times out …* (refinement of TACTICS-QUIRKS § 25).
- *N4 recon lesson* → `DESIGN.md` *Constructibility recon before scheduling a producer build*
  (its first post-21b application). The N4b *correction* sharpens it: the recon must
  read the vendored lemma's **exact binder**, not a paraphrase, before declaring it
  inapplicable — captured in the N4b correction entry above.
- *`@[simps!]` projection name not resolving; bare-term field is `rfl`* → FRICTION
  [resolved] *`edgeMultiply`'s `@[simps! vertexSet]` lemma does not resolve …*.
- *`Set.ncard_iUnion_le_of_fintype` for `|⋃| ≤ ∑ ncard` — don't hand-roll via `toFinset`* →
  FRICTION [resolved] *The `Set.ncard` of a finite-index `iUnion` is `≤ ∑ ncard` …*.
- *`H.cycleMatroid = G.cycleMatroid ↾ E(H)` for `H ≤ G` via `cycleMatroid_isRestriction_of_le` +
  `exists_eq_restrict` + ground pin* → FRICTION [resolved] *`[matroid]` `H.cycleMatroid =
  G.cycleMatroid ↾ E(H)` …*.
- *Union↔contraction equality via the count condition `Union_pow_indep_iff_count`, not the
  matching re-decomposition* → FRICTION [resolved] *`[matroid]` Union↔contraction equality: prove
  via the *count condition* … not … matching re-decomposition*.
- *The `V(...)` graph-vertex-set macro is greedy with a trailing binary operator (`V(H).ncard + 1`
  fails to parse, not just `: ℤ`-coerced double-subtraction); parenthesize the leading `V(…)` term* →
  FRICTION [resolved] *A `have h : … = … := by ring` whose type embeds `(V(G).ncard : ℤ) - 1 - 1`
  fails to parse* (Broadening bullet).

## Blockers / open questions

- **N4 is fully green; Track A's reduction infra is done.** The whole N4 chain — N4a (preconnected),
  N4b (cycleMatroid under collapse), N4c (union↔contraction bridge), and now the N4 reconciliation
  (`rigidContract_isMinimalKDof`) — is closed and axiom-clean. What gates `lem:case-I-realization`
  (N6) is now only the **producers** N5 + N6, not any more matroid/contraction infrastructure.
- **N5's remaining content is the common free-normal seed `q₀`** (the witness-transfer / eq. 6.6).
  The single-leg *single-seed-rigidity ⟹ full-rank-realization* bridge is now GREEN
  (`hasFullRankRealization_of_rigidOn_seed`); what remains red is the genuinely-hard part:
  (1) **per-leg rigid seed** — *produce* a seed `q₀` at which a rigid block `H` (or the contraction) is
  rigid on its vertex set. This is **not** the one-commit step the prior hand-off implied: a single
  spanning forest gives only `(D−1)·(|V(H)|−1)` independent rows (`exists_independent_rigidityRows_of_forest`),
  short of the full `D(|V(H)|−1)`; reaching full rank needs a `D`-fold `M(H̃)`-base packing, i.e.
  essentially `theorem_55` recursed onto `H` (research-shaped). **The `D`-fold base packing is
  GREEN** (`Graph.IsKDof.exists_isBase_isForestPacking`): a rigid `H` has a base of `M(H̃)` packing
  into `D` edge-disjoint forests, `|B| = D(|V(H)|−1)`. **But the "row-stacking" follow-up is ruled out**
  (recon, this commit): stacking the `D` forests' rows over-counts by `(D−1)` and isn't jointly
  independent (extensor-span genericity, research-shaped), *and* is off-path — N7b-0
  (`exists_independent_panelRow_subfamily_of_rigidOn`, green) extracts the full count directly from
  rigidity-on-`V`. So option (a) bottoms out on the same seed obstruction as (b), not on a separable
  linear-algebra brick. (2) The **simultaneous witness-transfer**
  (both legs' rank-determinant polynomials non-zero in the shared normals ⇒ a common non-root `q₀` by
  `MvPolynomial.funext`, fed to `hasFullRankRealization_of_splice_ofNormals`). **Both per-leg inputs
  now GREEN:** the IH-repackaging `exists_rigidOn_ofNormals_of_hasFullRankRealization` (non-empty rigid
  `ofNormals` locus) and — this commit — the per-leg **rank polynomial**
  `exists_rankPolynomial_of_rigidOn` (a rigid leg ⟹ a nonzero-at-the-seed Gram-det `MvPolynomial`,
  every non-root of which gives the leg's full-size `panelRow`-subfamily LI). What remains red is
  exactly the **coupling**, and the forward half is now GREEN:
  `isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero` (this commit) turns a non-root of a
  leg's rank polynomial into the leg rigid *at that point*. The `_ofParam` seed was ruled out
  (subvariety-genericity gap vs. the free-normal `∃ Q, …` motive); see *Decisions*.
- **The coupling is NOT a one-commit assembly — the recon (this commit) found two real gaps that the
  prior "fully decomposed to one assembly commit" framing missed.** **(G1) per-leg transversal-rigid
  seed:** `exists_rankPolynomial_of_rigidOn` (the polynomial producer) needs the leg rigid at a seed
  with all hinges *transversal* (`hne`); the IH gives only a *bare* rigid `HasFullRankRealization`,
  and a rigid framework can have a degenerate hinge — the `panelRow`/N7b-0 span argument that builds
  the polynomial genuinely needs transversal hinges. **(G2) general position at the shared seed:** the
  splice `hasFullRankRealization_of_splice_ofNormals` needs `hgp` at `q₀`, but the product `Q_H·Q_c`'s
  non-root is not general-position; coupling general position in needs a *third* nonzero factor whose
  non-roots are general-position assignments (a Vandermonde-type brick that does not exist yet). Both
  gaps are the genuine KT §6.2 panel-intersection geometry (eq. 6.6): the construction *builds* a
  specific general-position rigid realization per leg, it does not consume an arbitrary rigid IH one.
  The green forward half (consumer brick) is real progress, but the producer remains red and needs a
  *math-first decomposition* of (G1)+(G2) before its build. **Track B** (the Case II/III producer)
  remains a separate multi-node crux (eq. 6.12 degenerate placement + Lemma 6.10 at `d=3`).
- **(G1) and (G2) are BOTH now dissolved/closed — the two analytic gaps of the Case-I coupling are
  gone.** (G1) was dissolved at the source by the two-motive split (prior commit): general position is
  carried in the motive rather than re-proved (option (b) is circular — it needs
  `exists_rankPolynomial_of_rigidOn`'s own `hne`); the spike ruled out the single-conjunct option (A)
  (`splitOff` doesn't preserve simplicity, KT Lemma 6.7). The split landed
  `HasGenericFullRankRealization` + the forgetful map `hasFullRankRealization_of_generic`, carried only
  through the simple Case-I cases, bare `theorem_55` untouched. **(G2) is now CLOSED (this commit):**
  `exists_generalPosition_polynomial` is the general-position `MvPolynomial` factor (the
  off-diagonal product of leading `2×2` minors), nonzero (witnessed at the moment-curve seed) and with
  non-roots exactly the general-position assignments. So neither (G1) nor (G2) is a blocker any more.
  **N6a is GREEN:** the *non-simple* Case-I branch needs neither the GP motive nor (G2) — its hinges
  are transversal even though general position fails, so `hasFullRankRealization_of_splice_of_supportExtensor`
  closes it on the bare motive. **What remains for the simple cases N6b/N6c** is the *assembly* (no new
  analytic brick): multiply the two legs' rank polynomials (`exists_rankPolynomial_of_rigidOn`, green)
  by the (G2) factor, apply `MvPolynomial.exists_eval_ne_zero` to the triple product for one shared
  seed, re-derive each leg rigid at it (`isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero`,
  green) + general position at it (the (G2) factor), and feed `hasFullRankRealization_of_splice_ofNormals`
  (green). See *Hand-off* build order.
- **CORRECTION (prior commit, recon): N6b is NOT that clean assembly with the *all-edges* bricks.**
  The "multiply the two legs' rank polynomials" step needs `exists_rankPolynomial_of_rigidOn GH ends …`
  per leg, which requires `hends : ∀ e : β, GH.IsLink e …` (every edge label of the realized graph must
  link). A *proper-subgraph* leg `GH ≤ G` does not satisfy this, so the all-edges per-leg rank
  polynomial is not applicable to the legs; N6b needs a *leg-restricted* rank polynomial (rigidity-row
  span over the leg's linking edges only).
- **RESOLVED (this commit): the leg-restricted rank polynomial is GREEN — the recon's blocker is gone.**
  Built the four-brick leg-restricted chain (`span_panelRow_linking_eq_rigidityRows` →
  `exists_independent_panelRow_subfamily_of_rigidOn_linking` → `exists_rankPolynomial_of_rigidOn_linking`
  producer → `…_rankPolynomial_ne_zero_linking` consumer), all axiom-clean. Each brick weakens
  `hends`/`hne` to the *linking* edges and tracks a `hsupp` (every witnessed index links), so the chain
  applies to a proper-subgraph leg `GH ≤ G` whose `ends` is the parent's (recording the link of every
  edge that links, automatic up to swap via `infinitesimalMotions_ofNormals_eq_of_ends_swap`). **What
  remains red:** the N6b/N6c *coupling assembly* itself (multiply the two leg-restricted polynomials ×
  the (G2) factor → shared non-root → re-derive each leg rigid + GP → splice) — now a genuine assembly
  of green bricks, no new analytic content. See *Hand-off* build order.

## Hand-off / next phase

**This commit: the leg-restricted rank polynomial GREEN — the genuine N6b brick the prior recon
named.** The prior commit's recon found the all-edges `exists_rankPolynomial_of_rigidOn` inapplicable
to a proper-subgraph leg (`hends : ∀ e : β, GH.IsLink e …` unsatisfiable) and called for a
*leg-restricted* rank polynomial (rigidity-row span over the leg's *linking* edges only). This commit
delivers it as four axiom-clean bricks in `AlgebraicInduction.lean` (no `\leanok` flip, no blueprint
entry — infra below the red Case-I nodes):
1. `BodyHingeFramework.span_panelRow_linking_eq_rigidityRows` — the panel rows of the *linking* edges
   span the rigidity-row space, requiring `hends`/`hne` only on edges that link.
2. `BodyHingeFramework.exists_independent_panelRow_subfamily_of_rigidOn_linking` — a rigid leg carries
   `D(|V|−1)` independent panel rows *every member of which links* (`hsupp`).
3. `PanelHingeFramework.exists_rankPolynomial_of_rigidOn_linking` — the leg-restricted producer: rigid
   leg ⟹ nonzero Gram-det `MvPolynomial` whose witnessed subfamily lies on the leg's linking edges.
4. `PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_of_rankPolynomial_ne_zero_linking` — the
   matching consumer: a non-root with `hsupp` ⟹ the leg rigid at that point.
Same coordinatization + rank-nullity as the all-edges forms; the lever is restricting the spanning
identity to linking edges, so the leg-restricted `hends` (link of every *linking* edge, automatic up
to swap via the prior commit's `infinitesimalMotions_ofNormals_eq_of_ends_swap`) suffices. **No
`sorry` committed:** the N6b/N6c *coupling assembly* and `lem:case-I-splice-placement` stay red.

**Recommended next concrete commit: the N6b/N6c shared-seed coupling assembly** — now a genuine
assembly of green bricks (the recon's blocker is dissolved). For the two Case-I legs `GH`, `Gc`
(both `≤ G`, arriving GP via the `HasGenericFullRankRealization` motive): (a) feed each leg's IH
rigidity (own `ends_H`) into `exists_rankPolynomial_of_rigidOn_linking` at the parent's `ends`, using
`infinitesimalMotions_ofNormals_eq_of_ends_swap` to re-express the IH rigidity at the parent selector
and supplying the leg-restricted `hends` (every linking edge of the leg links, automatic since the
leg's `ends` is the parent's and the IH leg links it); (b) multiply the two leg-restricted rank
polynomials `Q_GH · Q_Gc` × the (G2) factor `exists_generalPosition_polynomial`; (c) take a shared
non-root `q₀` via `MvPolynomial.exists_eval_ne_zero`; (d) re-derive each leg rigid at `q₀` via
`…_rankPolynomial_ne_zero_linking` (consuming each leg's `hsupp`) + GP at `q₀` via the (G2) factor;
(e) feed `hasFullRankRealization_of_splice_ofNormals`. Math-first check before building: confirm the
two legs' `hends`-into-the-producer step composes cleanly with the `ends`-swap brick — that is the
one place the per-leg link witness must be threaded. Recurring trap (FRICTION): the heavy
`IsInfinitesimallyRigidOn` defeq across `ofNormals`/`withGraph` graph-swaps — state hypotheses
pre-converted. Build order from there: N6b/N6c coupling → **N6** the Case-I composer
(`lem:case-I-realization`, dispatches on simplicity: N6a for non-simple, N6b/N6c for simple; the
simple cases conclude the GP motive via `hasFullRankRealization_of_generic` for `theorem_55`'s bare
`hcontract`) → the **Case-III row** (Track B) via the green Lemma 2.1
(`omitTwoExtensor_linearIndependent`).

Honesty-gate: `lem:case-I-splice-placement` / `lem:case-I-realization` stay red — the deliverable
(shared-seed full-rank realization) is not produced; only the decomposable bricks are green.

*Alternatively*, the genericity-free `prop:rigidity-matrix-prop11` `hub` brick (`screwDim k + def ≤
dim Z(G,p)`, the Phase-19 partition-contraction count) is a Track-independent closable target — but it
is itself a multi-commit build (construct `D(|P|−1)−(D−1)·d_G(P)` motions of `R(G,p)` from a deficiency-
attaining partition, connecting the Phase-18 motion space to the Phase-19 partition machinery), not a
one-commit node; decompose it math-first before scheduling.

*If Track B is preferred:* it remains a multi-node crux (eq. 6.12 degenerate placement + Lemma 6.10
at `d=3`); see the Track-B checklist + `notes/MolecularConjecture.md` *Phase 22* for the node plan.
