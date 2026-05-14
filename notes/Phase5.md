# Phase 5 — Laman's theorem, (⇐) direction (work log)

**Status:** complete.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

**All milestones complete.** Milestone 0 (named-theorem layout +
`d = 2` specialization + iso transports); milestone 1 (reverse
decomposition with Laman preservation, Henneberg blocker route);
milestone 2 (Type I and Type II rigidity preservation in dim 2, both
unconditional); milestone 3 (strong-induction closing the iff's `mpr`
arm). The Type II collinearity gap (the milestone 2 closure point
flagged in earlier hand-offs) is discharged via openness of
infinitesimal rigidity (`IsInfinitesimallyRigid.eventually`) plus a
perpendicular perturbation of the bridge-edge endpoint's third
neighbor, packaged as the private helper
`Henneberg.exists_nonCollinear_rigid_placement_dim_two`.

The (⇐) direction `IsLaman.isGenericallyRigid_two` is fully proved.
The iff's `mp` arm reduces to Phase 6's `IsGenericallyRigid.
exists_isLaman_le` (Lovász–Yemini), the sole remaining `sorry` in the
project.

**The degree-3 contradiction-unification refactor landed.** The two
`(k, ℓ)`-shaped primitives `IsTightOn.union_with_bonus` and
`IsTightOn.insert_vertex_with_edges` (originally planned in the
appendix; now in `Sparsity.lean` and blueprinted in
`chapter/sparsity.tex`) absorb the singleton-intersection bookkeeping
that the per-pair contradiction templates used to carry inline; the
14-branch `by_cases` dispatcher collapsed to three per-pair Or's plus
one call to a new unified `IsLaman.False_of_pairwise_blocker_or_edge`.
The appendix overestimated the LoC savings: the three private
contradiction templates stayed (the 3-pair singleton chain produces a
1-deficient intermediate that doesn't shape-match the primitives),
and the new unified-contradiction lemma is itself ~70 LoC. Net effect
(after the post-landing review cleanup that dropped
`False_of_three_neighbor_squeeze` and added two small companion
helpers): modest LoC growth (~+60), but the dispatcher and 1/2-pair
templates are substantially cleaner, the two primitives are reusable
and blueprint-eligible (potentially upstream alongside `IsTightOn`),
and `typeII_reverse_witness_or_blocker` is now invoked exactly once
per pair instead of up to 8 times across the dispatcher.

Phase 5 target — the (⇐) direction of Laman's theorem
(`IsLaman.isGenericallyRigid_two`) — plus the iff composition with
Phase 6's `IsGenericallyRigid.exists_isLaman_le`. The proof is a
Henneberg induction on `Fintype.card V`, broken into three milestones:
**1.** Reverse decomposition (`IsLaman.exists_typeI_or_typeII_reverse`);
**2.** Move preservation (`typeI` / `typeII_isGenericallyRigidInj_two`);
**3.** Induction (fills `IsLaman.isGenericallyRigid_two`). Milestones
1 and 2 are independent; per-milestone names and proof techniques are
under *Lemma checklist* and *Decisions made* below.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **(⇐) only; (⇒) is Phase 6.** ROADMAP §5 commits to the iff
  statement — that lands in `LamanTheorem.lean` from the first commit
  with the (⇒) arm as `sorry`. (⇒) needs the Lovász–Yemini equality
  "rigidity matroid = (2,3)-count matroid in dim 2," which is its own
  multi-session sub-project on top of a `RigidityMatroid.lean`. Phase 4
  *Architectural choices* explicitly kept the rigidity matroid out of
  scope; reversing that within Phase 5 would balloon the phase. Phase 6
  picks it up if and when warranted.

- **Henneberg-blocker route, not matroid bypass.** The reverse lemma
  is proved combinatorially via the classical Whiteley/Jordán argument:
  if every non-adjacent neighbor pair of a degree-3 vertex `v` blocks
  the Type II reverse, a `(2, 3)`-tight set in `G` is forced to violate
  sparsity. Pure graph theory; matches the project's existing
  `IsSparse` / `IsTight` / `edgesIn` style. Path 2 (matroid bypass)
  was rejected for the same reason as the (⇒) deferral above.
  ROADMAP §5 *Carryover from Phase 3* and DESIGN.md *Why Henneberg*.

- **Specialize to `d = 2` at the Phase 5 boundary.** Per
  Phase 4 *Architectural choices*, every Phase 4 result is general
  in `d`. Phase 5 is responsible for the `d = 2` specializations:
  `IsGenericallyRigid.card_mul_le_two` (`2 * #V ≤ #E + 3`, one-line
  corollary of `IsGenericallyRigid.card_mul_le`) and the per-move
  rigidity-preservation lemmas. The move-rigidity proofs are
  intrinsically d=2 — the "place new vertex off the line through
  neighbors" / rotation-trick arguments are dimension-2 facts.
  General-`d` Henneberg is mathematically harder and not on the
  critical path.

- **Reverse lemma signature.** Same shape as
  `exists_typeI_or_typeII_iso` plus a `G'.IsLaman` conjunct on the
  decomposed graph (full statement under *Milestone 1* below). The
  iso version is *not* superseded — it stays as the natural building
  block; the strengthened version composes the Laman-claim on top.

- **Move-preservation lemmas live in `Henneberg.lean`.** The
  `typeI_isLaman` / `typeII_isLaman` lemmas already live there; the
  `_isGenericallyRigid_two` companions land alongside, exposing the
  per-move parallel structure. Cost: `Henneberg.lean` will need to
  import `Framework.lean` (today it doesn't); `Framework.lean` is a
  leaf in the import DAG so this is a forward edge, not a cycle. An
  alternative was a separate `HennebergRigidity.lean`; rejected
  because the lemma counts are small.

## Lemma checklist

Listed by milestone. Items live in `LamanTheorem.lean` unless tagged
otherwise. See *Decisions made* for proof-technique discussion and the
named theorems' own docstrings for the full statement.

### Milestone 0 — done

- [x] `LamanTheorem.lean` created with the three named theorems per the
  structured-`sorry` layout (`IsLaman.isGenericallyRigid_two`,
  `IsGenericallyRigid.exists_isLaman_le`, composed iff
  `isGenericallyRigid_two_iff_exists_isLaman_le`).
- [x] `IsGenericallyRigid.card_mul_le_two` — `d = 2` specialization
  of `IsGenericallyRigid.card_mul_le` (one-liner).
- [x] `IsGenericallyRigid.iso` / `IsInfinitesimallyRigid.iso` in
  `Framework.lean` — direct kernel-iso route, ~30 lines.

### Milestone 1 — Reverse decomposition (`Henneberg.lean`) — done

Target: `IsLaman.exists_typeI_or_typeII_reverse` — strengthened
decomposition asserting `G'.IsLaman` (Tay–Whiteley 1985; Jordán 2016
§2.2).

- [x] `typeI_reverse_isLaman` / `typeI_isLaman_iff` — typeI half.
- [x] (Helper) `edgesIn_ncard_add_le` in `EdgesIn.lean` — modular
  inequality `e(S) + e(T) ≤ e(S ∪ T) + e(S ∩ T)`, plus `edgesIn_inter`.
- [x] `IsTightOn G k ℓ s` + `IsTightOn.union_inter` in `Sparsity.lean`
  — `(k, ℓ)`-tight-subset union closure with `ℓ ≤ k · |s ∩ t|` proviso.
- [x] `IsSparse.isTightOn_of_le` in `Sparsity.lean` — squeeze:
  `k · #s ≤ e(s) + ℓ` plus sparsity forces tightness.
- [x] `IsLaman.typeII_reverse_blocker` (`Henneberg.lean`) — per-pair
  tight-blocker witness from a failed typeII candidate.
- [x] (Private) `IsLaman.no_isTightOn_excluding_three_neighbors` —
  overshoot contradiction primitive.
- [x] (Private) `IsLaman.typeII_reverse_witness_or_blocker` — per-pair
  witness-or-blocker dispatcher.
- [x] (Private) `IsLaman.False_of_three_neighbor_squeeze` — single
  squeeze-form primitive consumed by every contradiction template.
- [x] (Private) `IsLaman.contradiction_{one,two,three}_pair` —
  1/2/3-pair contradiction templates. Slimmed in the degree-3 refactor:
  `_one_pair` uses `IsTightOn.insert_vertex_with_edges`; `_two_pair`'s
  singleton-intersection branch uses `IsTightOn.union_with_bonus`;
  `_three_pair` drops its unused `_nadj` arguments.
- [x] `IsTightOn.union_with_bonus` / `IsTightOn.insert_vertex_with_edges`
  in `Sparsity.lean` — refinements of `IsTightOn.union_inter`'s union
  half (drop the size proviso in exchange for an explicit bonus-edge
  set `F`) and a vertex-extension tightness primitive. Both
  upstream-eligible alongside `IsTightOn`.
- [x] (Private) `IsLaman.False_of_pairwise_blocker_or_edge` — unified
  contradiction dispatcher across the 8 leaves of the three-pair
  case-split.
- [x] `IsLaman.exists_typeI_or_typeII_reverse` — degree-2 via
  `typeI_isLaman_iff`, degree-3 via three per-pair Or's plus a single
  call to `False_of_pairwise_blocker_or_edge`.

### Milestone 2 — Move preservation in dim 2 (`Henneberg.lean`) — done

- [x] (Helper) `eq_zero_of_orthogonal_dim_two` — perp to two LI vectors
  is zero in `EuclideanSpace ℝ (Fin 2)`.
- [x] `typeI_isInfinitesimallyRigid_extend` — rank-nullity core for
  typeI rigidity preservation (`LinearIndependent ℝ ![q - p a, q - p b]`).
- [x] `IsGenericallyRigidInj` predicate + API
  (`.toIsGenericallyRigid`, `.mono`, `.iso`) in `Framework.lean`.
- [x] `top_fin_two_isGenericallyRigidInj` — K₂ injective base case.
- [x] (Private) `exists_off_line_off_finite_dim_two` — produces `q`
  off a line and off a finite set, with `![q - pa, q - pb]` LI.
- [x] `typeI_isGenericallyRigidInj_two` — unconditional typeI
  preservation in the strong form.
- [x] `typeII_isInfinitesimallyRigid_extend` — rank-nullity core for
  typeII (input: `q` collinear with `(p a, p b)`; `(q - p a, q - p c)`
  LI).
- [x] (Private) `exists_typeII_q_on_line_dim_two` — produces `q` on
  the line through `(pa, pb)` (with `α ≠ 0, 1`) realizing both LI
  conditions, off a finite set.
- [x] `typeII_isGenericallyRigidInj_two_of_nonCollinear` — conditional
  typeII preservation; takes non-collinearity of `(p a, p b, p c)` as
  input.
- [x] `IsInfinitesimallyRigid.eventually` in `Framework.lean` —
  openness of IR via a basis-lift of `range (RigidityMap p₀)` plus
  `LinearIndependent.eventually` and continuity of
  `p ↦ ⟪p u - p v, x u - x v⟫`.
- [x] (Private) `exists_nonCollinear_rigid_placement_dim_two` in
  `Henneberg.lean` — perturbation `Function.update p₀ c (p₀ c + t • w)`
  with `w ∉ span {p₀ b - p₀ a}`; openness of IR + continuity of
  injectivity give an open `t`-nhd of 0; non-collinearity strict for
  `t ≠ 0` via `pair_add_smul_add_smul_iff` row-op; extract witness from
  `𝓝[≠] 0` (NeBot in `ℝ`).
- [x] `typeII_isGenericallyRigidInj_two` — *unconditional* typeII
  preservation. Composes the perturbation helper with
  `_of_nonCollinear`.

### Milestone 3 — Induction (fills milestone-0 sorry) — done

- [x] `IsLaman.eq_top_of_card_eq_two` in `Laman.lean` — base-case
  helper: Laman + `card V = 2` ⇒ `G = ⊤`.
- [x] (Private) `IsLaman.isGenericallyRigidInj_two_of_card` in
  `LamanTheorem.lean` — strong induction on `Fintype.card V`. Base
  (`card V = 2`): `eq_top_of_card_eq_two` + iso transport via
  `Iso.completeGraph (Fintype.equivFinOfCardEq ·).symm` applied to
  `top_fin_two_isGenericallyRigidInj 1`. Step (`card V ≥ 3`):
  `Henneberg.IsLaman.exists_typeI_or_typeII_reverse` + IH at
  `Fintype.card {w // w ≠ v}` (via `Fintype.card_subtype_lt`) +
  per-move strong-form preservation (`typeI_isGenericallyRigidInj_two`
  / `typeII_isGenericallyRigidInj_two`) + iso transport. Both branches
  fully closed.
- [x] `IsLaman.isGenericallyRigid_two` — wired through
  `isGenericallyRigidInj_two_of_card.toIsGenericallyRigid`. Closes the
  iff's `mpr` arm.

## Decisions made during this phase

### Phase-local choices and proof techniques

*Milestone 0 / 2 architectural choices.*

- **`IsInfinitesimallyRigid.iso`: build the kernel iso directly, not via
  `Submodule.map`.** The `Submodule.map`-route stalls on `SetLike`
  membership-form mismatches (see FRICTION). Direct `LinearEquiv`
  between the kernel subtypes is ~30 lines and the membership obligations
  are `q'.2`-typed; `LinearMap.mem_ker.mp/mpr` works without bridging.

- **K₂ rigidity refactored to expose the injective form.** Split
  `top_fin_two_isGenericallyRigid`'s `d ≥ 1` branch into a dedicated
  `top_fin_two_isGenericallyRigidInj` (the placement at `0, e₀` is
  already injective); the unrefined version delegates `d ≥ 1` via
  `.toIsGenericallyRigid`. The `d = 0` case stays inline (can't be
  injective on `Fin 2 → EuclideanSpace ℝ (Fin 0) = {0}`). Zero new proof
  text; the injective form is milestone 3's base case.

- **typeII rigidity preservation: conditional core + non-collinearity-
  conditioned wrapper.** The rank-nullity argument places `q` on the
  line through `p a, p b` so the two new edges at `none ↔ some a/b`
  yield the deleted edge by subtraction; the third new edge at
  `none ↔ some c` closes injectivity *iff* `q - p a, q - p c` LI, i.e.,
  `(p a, p b, p c)` non-collinear. Collinear inputs genuinely fail
  rigidity (free perpendicular motion at the new vertex). Two-layer
  API: `_of_nonCollinear` takes non-collinearity explicitly; the
  *unconditional* wrapper is deferred — see *Blockers*.

- **typeII conditional theorem doesn't need `G.Adj a b`.** The
  deleted-edge case-split is vacuous if `s(a, b) ∉ G.edgeSet`. So
  `hG_ab` is omittable from `typeII_isInfinitesimallyRigid_extend` and
  its non-collinear wrapper. The milestone-3 reverse decomposition
  *will* supply `G'.Adj a b`, but stripping it from the wrapper API
  keeps the rigidity signatures minimal. The Laman-preservation version
  `typeII_isLaman` still needs `G.Adj a b` (where the deletion is
  non-vacuous).

*Milestone 1 — typeII blocker proof techniques.*

- **typeI reverse Laman via `typeI_edgesIn_ncard_decomp`.** Lift
  `s' : Finset V` to `s := s'.image some`; apply
  `(typeI G a b).IsLaman.isSparse` at `s`; the Phase 3
  `typeI_edgesIn_ncard_decomp` plus `Finset.eraseNone_image_some`
  collapse the fresh-edge term to zero. ~15 lines, structurally dual
  to `typeI_isLaman`.

- **`IsTightOn` predicate up front.** The Phase 5 plan punted the
  predicate-vs-unpredicated choice; chose predicate because in the
  union-closure lemma alone it appears 4× in the signature, and the
  blocker instantiates it per candidate set. `IsTightOn` is `def := eqn`
  (not `And`), so `refine ⟨?_, ?_⟩` doesn't split it; the proof uses
  `unfold IsTightOn at hs ht ⊢` to surface the equation for `omega`.

- **Modular `edgesIn` inequality requires `[Finite V]`.** Without it,
  `ncard = 0` on infinite sets lets the supermodular bound fail
  (counter-example: disjoint `S, T` with infinitely many cross-edges).
  Picked `[Finite V]` over an explicit Finite arg so
  `Set.ncard_union_add_ncard_inter` and `Set.ncard_le_ncard` autoparams
  fire (TACTICS § 2). `edgesIn_inter` lifted out as a named lemma since
  the `∩` equality is independently useful.

- **typeII reverse blocker: edge count via the Phase 3 iso, not by
  hand.** The blocker proof reuses `typeII_iso_of_three_neighbors` to
  get `h_iso : G ≃g typeII G' xs ys cs`, transfers `G.IsLaman` via
  `IsLaman.iso`, and reads the count off `typeII_edgeSet_ncard` plus
  `Finite.card_option`. Saves ~20 lines and the direct `comap`-edge-count
  helper. Cost: signature carries the third neighbor and full neighbor
  predicate, but both are in scope from `Finset.card_eq_three`.

- **Per-pair blocker case structure: split on `xs, ys ∈ s'`.** The
  sparsity violation on `G'` gives a Finset `s'`; lift to
  `S = s'.image Subtype.val ⊆ V \ {v}`. Two cases differ in the
  bridge-edge contribution. Both `xs, ys ∈ s'`: bridge contributes ≤ 1,
  squeeze gives `IsTightOn 2 3 S` via `IsSparse.isTightOn_of_le`. One
  out: bridge contributes 0, direct sparsity contradiction. The
  edge-set bookkeeping uses the private `image_edgesIn_comap`.

- **Single squeeze-form primitive `False_of_three_neighbor_squeeze`.**
  Every contradiction template (1/2/3-pair) ends with the same tail:
  assemble `T`, verify `2 * #T ≤ #(edgesIn T) + 3` (the squeeze), apply
  `IsSparse.isTightOn_of_le`, apply
  `no_isTightOn_excluding_three_neighbors`. Factored as one primitive;
  templates differ only in `T` assembly and the squeeze inequality.

- **Degree-3 main theorem: 8-leaf flat `by_cases` over each pair's
  adjacency.** First skeleton used outer `rcases
  exists_nonadj_among_three_neighbors` + `exfalso` + sub-case analysis;
  failed because additional dispatcher invocations inside `exfalso` can
  return witnesses that should bubble out. Flat `by_cases` per pair
  invokes `typeII_reverse_witness_or_blocker` only on confirmed
  non-adjacent pairs and returns witnesses at the leaf. ~120 lines
  straight-line; flatter than the alternatives. All-adjacent leaf
  contradicts `exists_nonadj_among_three_neighbors`.

- **`Sym2.eq_iff` destructure trap.** `Sym2.eq_iff.mp` on
  `s(x, z) = s(y, z)` gives second-disjunct `x = z ∧ z = y` (both
  reference `z`), not `x = y ∧ z = z`. Forgetting this produced a
  confusing type mismatch in `contradiction_one_pair`. A one-line trap.

*Milestone 2 — Henneberg rigidity preservation proof techniques.*

- **Helper `eq_zero_of_orthogonal_dim_two`.** In `EuclideanSpace ℝ
  (Fin 2)`, a vector orthogonal to two LI vectors is zero. Pulled out
  as a 15-line lemma to keep `typeI_isInfinitesimallyRigid_extend`'s
  main proof focused on rigidity-map plumbing. Uses
  `LinearIndependent.span_eq_top_of_card_eq_finrank` +
  `Submodule.top_orthogonal_eq_bot` + a `span_induction` over the
  two-element generating set. Dim-2-specific.

- **`set p_ext := fun w => w.elim q p with hp_ext_def` keeps the new
  placement evaluable by `change`.** Two new-edge constraints come out
  with `p_ext none` and `p_ext (some _)`; these are defeq to `q` and
  `p _` (via `Option.elim`). `change` surfaces the unfolded form for
  the inner-product subtraction step. Pure `let` works equally well —
  what matters is that `set` doesn't block defeq.

- **Dim-2 off-line construction via row-op on
  `LinearIndependent ℝ ![v, pb - pa]`.**
  `exists_off_line_off_finite_dim_two` proves
  `LinearIndependent ℝ ![q - pa, q - pb]` for `q := pa + t • v` (with
  `v ∉ span {pb - pa}`, `t ≠ 0`) via
  `LinearIndependent.pair_add_smul_add_smul_iff` with coefficients
  `(t, 0, t, -1)`. Determinant `-t ≠ 0`, so LI transfers. Cleaner than
  `linearIndependent_fin2` case-analysis.

- **`SetLike.exists_not_mem_of_ne_top` is the canonical "pick a
  non-member" lemma.** Searching for "exists element outside a proper
  submodule" doesn't surface a `Submodule.*` form; the general
  `SetLike` lemma applies, and the `h_top` autoparam fires by `simp`
  for standard cases. Used to extract `v ∉ span {pb - pa}` in the
  off-line construction.

*Milestone 3 — strong-induction proof techniques.*

- **Strong induction signature carries `Fintype.card V = n`.** The
  predicate must quantify over `V` (and `[Fintype V]`) inside the
  per-`n` body, so the IH applies to any smaller type. Signature:
  `∀ n, ∀ {V} [Fintype V], Fintype.card V = n → ∀ {G}, G.IsLaman →
  G.IsGenericallyRigidInj 2`. IH at the step is
  `ih (Fintype.card {w // w ≠ v}) hcard_lt rfl hG'_lam`; `rfl` for the
  card-eq closes when we instantiate `n` to the new card directly, and
  `hcard_lt` is `Fintype.card_subtype_lt (p := · ≠ v) (x := v) (by
  simp)`. Inducting on `Fintype.card V` directly with
  `Nat.strong_recOn` is no cleaner — the type generalization stays.

- **Milestone 3 typeII gap closure: openness of IR + perturbation.**
  The Phase 5 milestone 3 granular `sorry` (the typeII branch's
  `LinearIndependent ℝ ![p b - p a, p c - p a]` requirement) lifts as
  soon as the *unconditional* `typeII_isGenericallyRigidInj_two` lands.
  That unconditional theorem uses `IsInfinitesimallyRigid.eventually`
  (openness of IR in `Framework V d`) plus a perpendicular perturbation:
  pick `w ∉ span {p₀ b - p₀ a}`, update `p₀ c ↦ p₀ c + t • w`, take the
  intersection of the open IR-nhd, the open Inj-nhd, and `t ≠ 0`
  (non-collinearity is strict for any `t ≠ 0`). All three sets meet
  thanks to `NeBot (𝓝[≠] 0)` for `ℝ` (densely ordered + nontrivial).

- **`IsInfinitesimallyRigid.eventually` proof structure.** Sets `r :=
  Module.finrank ℝ (LinearMap.range (G.RigidityMap p₀))` and lifts a
  basis of the range via `Module.finBasis` and `Classical.choose` on
  `LinearMap.mem_range` to preimages `preimg : Fin r → Framework V d`.
  By `LinearIndependent.eventually` on `Mathlib.Analysis.Normed.Module.
  FiniteDimension` and continuity of `p ↦ (G.RigidityMap p (preimg i))_i`
  (which factors through per-edge continuity of
  `p ↦ ⟪p u - p v, preimg i u - preimg i v⟫`), the lifted images stay LI
  on an open nhd of `p₀`. Lifting back to the range submodule via
  `Submodule.subtype.of_comp` and applying
  `LinearIndependent.fintype_card_le_finrank` gives the rank lower
  bound, which combines with rank-nullity on both `p₀` and `p` to
  bound `dim ker (G.RigidityMap p) ≤ d * (d + 1) / 2`. Needs
  `Fintype G.edgeSet` (instantiated locally) for the codomain's
  finite-dim normed-space structure.

- **Perturbation continuity: `Function.update` + per-vertex
  case-split.** The map `p_t : ℝ → Framework V 2 :=
  fun t => Function.update p₀ c (p₀ c + t • w)` is `Continuous` by
  `continuous_pi` over `V`, splitting on `v = c` vs `v ≠ c`. Helpers
  `h_p_t_c t : p_t t c = p₀ c + t • w` (via `Function.update_self`)
  and `h_p_t_ne t v hvc : p_t t v = p₀ v` (via `Function.update_of_ne`)
  let each per-vertex branch reduce to either
  `continuous_const.add (continuous_id.smul continuous_const)` or
  `continuous_const`.

- **Non-collinearity for `t ≠ 0` via `pair_add_smul_add_smul_iff`.**
  In the collinear branch, extract the coefficient
  `γ • (p₀ c - p₀ a) = p₀ b - p₀ a` (with `γ ≠ 0`) from
  `¬ LinearIndependent ℝ ![p₀ b - p₀ a, p₀ c - p₀ a]` via
  `linearIndependent_fin2` + `push Not`. Then
  `p₀ c - p₀ a = γ⁻¹ • (p₀ b - p₀ a)`. Stage the perturbed pair
  `![p₀ b - p₀ a, (p₀ c - p₀ a) + t • w]` as
  `![0 • w + 1 • (p₀ b - p₀ a), t • w + γ⁻¹ • (p₀ b - p₀ a)]`; apply
  `LinearIndependent.pair_add_smul_add_smul_iff`. The auxiliary LI
  `![w, p₀ b - p₀ a]` follows from `linearIndependent_fin2` plus
  `hw_outside : w ∉ span {p₀ b - p₀ a}`. The mixed-coefficient
  condition `0 * γ⁻¹ ≠ 1 * t` reduces to `t ≠ 0`.

### Promoted to TACTICS / FRICTION / DESIGN

- *`Exists.imp` doesn't transport across changing-binder-type
  existentials* → FRICTION [resolved].
- *`rw [LinearMap.mem_ker]` fails on `SetLike`-coerced membership
  after `Submodule.mem_map` destructure* → FRICTION [resolved].
- *omega doesn't see through distributivity on `k * #` atoms* →
  FRICTION [wontfix] *omega doesn't see through nonlinear algebra on
  opaque atoms* (extended the existing commutativity entry with the
  distributivity case the `IsTightOn.union_inter` proof hit).
- *`set name := expr` creates a fresh atom for omega: hypotheses
  derived from upstream lemmas after the `set` still mention `expr`,
  not `name`, and omega treats `{name}` and `{expr}` as distinct
  atoms* → FRICTION [wontfix] *omega treats `set`-aliased terms as
  opaque atoms*.
- *Dot notation skips sub-namespaces (`h.typeII_reverse_blocker`
  fails when the helper lives in `Henneberg.IsLaman.*` and `h`'s
  type is `SimpleGraph.IsLaman`)* → FRICTION [resolved] *Dot notation
  skips sub-namespaces*. Inside a sub-namespace, call by explicit
  name; the partial-prefix lookup handles the rest.
- *`simp_all` rewrites backwards using equality hypotheses* →
  FRICTION [resolved] *simp_all rewrites backwards with equality
  hypotheses*.
- *`congr_fun` does not apply to `EuclideanSpace`* → FRICTION
  [resolved] *`congr_fun` does not apply to `EuclideanSpace`*.
- *`rcases ⟨rfl, rfl⟩` on `Sym2.eq_iff` eliminates the section-level
  variable, not the case-split variable* → FRICTION [resolved]
  *`rcases ⟨rfl, rfl⟩` on `Sym2.eq_iff` eliminates the section-level
  variable*.
- *`simp only [rigidityMap_apply, Pi.zero_apply]` leaves `he` in the
  elaborated goal, blocking later `rw`* → FRICTION [resolved] *`simp
  only [rigidityMap_apply, Pi.zero_apply]` leaves `he` in the
  elaborated goal*.
- *`interval_cases (Fintype.card V)` enumerates cases but does not
  substitute the value into the goal context — `rfl` can't close
  `Fintype.card V = 2` afterwards* → FRICTION [resolved]
  *`interval_cases` on non-variable expression doesn't substitute*.
- *`subst h` on `h : v = c` between two local variables can remove the
  *wrong* variable (kept `v`, removed `c`)* → FRICTION [resolved]
  *`subst h` on `h : v = c` between two local vars can substitute the
  variable you want to keep*.
- *`set p_t := fun t => …` + `simp [p_t]` doesn't unfold the let-binding
  cleanly when the body is a lambda — produces `⊢ sorry () c = …`* →
  FRICTION [resolved] *`set p_t := fun t => …` + `simp [p_t]` doesn't
  unfold the let-binding cleanly*.
- *`linearIndependent_fin2` leaves `![v₀, v₁] 0` / `![v₀, v₁] 1`
  unsimplified — follow-up `rw` fails until paired with
  `simp only [Matrix.cons_val_zero, Matrix.cons_val_one]`* → FRICTION
  [resolved] *`linearIndependent_fin2` leaves indexing unsimplified*.
- *`push_neg` is deprecated in favor of `push Not`* → FRICTION
  [resolved] *`push_neg` deprecated in favor of `push Not`*.

## Blockers / open questions

None — all milestone blockers resolved.

*Resolved blockers (chronological):*
- *Placement-construction side condition for typeI* — closed by
  `IsGenericallyRigidInj` + `exists_off_line_off_finite_dim_two`
  (milestone 2 typeI half).
- *Affine-spanning side condition* — superseded by the injective
  predicate `IsGenericallyRigidInj`.
- *Milestone-1 proof length* — landed in 2 sessions; templates kept
  private in `Henneberg.lean`.
- *Unconditional typeII rigidity preservation / collinearity gap* —
  closed by `IsInfinitesimallyRigid.eventually` (openness of IR) and
  the `exists_nonCollinear_rigid_placement_dim_two` perturbation
  helper. Chose option A from the prior hand-off (openness +
  perturbation), executed in ~250 LoC across `Framework.lean` and
  `Henneberg.lean`. The conditional `_of_nonCollinear` theorem stays
  as a named building block; the unconditional
  `typeII_isGenericallyRigidInj_two` composes the perturbation helper
  with it.

### Cleanup pass summaries

*Third post-closure cleanup pass — performance audit.* Driven by an observation
that a from-scratch build of `Framework.lean`, `HennebergRigidity.lean`, and
`Laman.lean` runs ~40 s on the user's machine (~80–100 s wall on this machine).
The pass quickly bottomed out on noise and structural import overhead:

- **Established the perf floor.** Loading the imports of `Framework.lean`
  (`Mathlib.Analysis.Normed.Module.FiniteDimension` + `…InnerProductSpace.PiL2`
  + cohorts) takes ~27 s by itself (`lake env lean` on a stub file with only
  the imports); `HennebergRigidity.lean`'s import closure is identical and
  takes ~27 s; `Laman.lean`'s is smaller at ~11 s. The within-file
  elaboration is small (Framework ~6 s, HR ~19 s, Laman ~11 s of work
  beyond the import load). Anything we change in source affects only the
  within-file part; the bulk of build time is the import floor.
- **`set_option profiler true` captures only ~5 s of the 19 s HR elaboration.**
  The cumulative profile (typeclass inference 1.7 s, linting 1.25 s, tactic
  execution 1.0 s, `.olean` serialization 0.7 s, simp 0.3 s, type checking
  0.2 s, elaboration 0.15 s) sums to ~5.3 s; the remaining ~14 s is
  process-level work the profiler doesn't expose (likely instance
  resolution, linker, IR generation that is not under `compilation (IR)`,
  etc.). The per-declaration profile threshold was lowered to 0 with the
  same result.
- **Build timings are dominated by variance.** Repeated full rebuilds of the
  same file (forced via a content-changing nudge) returned wall-clocks in
  the 10–50 s range with no source change. A/B-comparing optimization
  candidates requires several runs per branch *and* still leaves the result
  ambiguous in the noise band. Net: the most reliable improvement is to
  remove provably-unused work.
- **Tried and reverted (no measurable benefit, or borderline regression
  under noise):**
  - `set p_ext := … with hp_ext_def` → `let p_ext := …` in the two
    `_isInfinitesimallyRigid_extend` proofs. `hp_ext_def` is unreferenced,
    so the cleanup is cosmetic; under noise the `let` form trended
    *slightly slower* (median ~36 s vs ~25 s for `set`), probably because
    `set`'s named alias short-circuits unification more than the
    transparent `let` body does. Reverted.
  - Replace the four `change ⟪q - p a, …⟫ at hxa hxb hya hyb` lines with a
    single
    `simp only [rigidityMap_apply, Pi.zero_apply, hp_ext_def, Option.elim_none,
    Option.elim_some]`. Trended slower under noise too (~24 s vs ~16 s
    median on `lake env lean`); the `simp` has to chase the lambda
    explicitly while four `change` calls each just check defeq. Reverted.
  - Extract `kerRestrict` helper (the `LinearMap.funLeft … codRestrict …`
    block at the head of typeI/typeII injectivity). Drops ~5 lines of
    duplicated builder text, but four-run sample after the change ran
    ~46 s mean vs ~30 s baseline — another suspected regression in noise.
    Reverted; the duplication is mild (one identical 4-line block per
    move) and the proof line numbers are stable enough that the readability
    win is small.
  - Replace `nlinarith [Nat.le_mul_self d]` in
    `top_fin_two_isGenericallyRigidInj` with
    `have h_sq := Nat.le_mul_self d; have h_eq : (d+1)*(d+2) = d*d + 3*d + 2 := by ring; omega`.
    Saves ~120 ms in the profile but the file timing didn't move out of
    the noise band; left as the original `nlinarith` for now since
    `nlinarith [Nat.le_mul_self d]` is the more idiomatic one-liner for
    "linear-after-hinting-a-square" goals.
  - Convert `Framework.lean` (and transitively the dependency closure)
    from plain `import` to the new `module` + `public import` system used
    by upstream Mathlib. Mathlib commit pinned here already uses the
    module system (e.g. `Mathlib.Analysis.Normed.Module.FiniteDimension`
    has `module`-header), but a `module` file *cannot* import a non-`module`
    file, so converting `Framework.lean` requires first converting our
    four `Mathlib/…` mirrors plus `EdgesIn.lean`, `Sparsity.lean`,
    `Laman.lean`, `Henneberg.lean`. The build-time benefit accrues to
    *downstream* importers of the converted file (smaller interface to
    load), and our only downstream importer is `LamanTheorem.lean`. Not
    worth the multi-file refactor for one file's load time. Marked as a
    Phase 6 candidate if the rigidity-matroid work adds more downstream
    files.
- **Kept (safe, ambiguous-but-not-worse).** Removed two redundant imports
  from `Framework.lean`: `Mathlib.LinearAlgebra.Dimension.Finrank` and
  `Mathlib.LinearAlgebra.Dimension.Free`. Both are transitively pulled in
  via `Mathlib.Analysis.InnerProductSpace.PiL2` /
  `Mathlib.Analysis.Normed.Module.FiniteDimension`; with them gone the
  file builds and `Module.finrank_pi_fintype` remains in scope. No
  measurable timing change but the imports were dead code.

Net effect: −2 LoC (`Framework.lean`); no measurable build-time change.
The takeaway recorded in FRICTION below: durable performance work on
these files requires either (a) a smaller import closure for the Lean
*kernel* (i.e. module-system conversion of the full Archive dependency
chain) or (b) shipping a `RigidityMap` API that doesn't pull in the
finite-dimension normed-module machinery for files that only need the
combinatorial half.

*Second post-closure cleanup pass.* Eight small simplifications driven by a
cold-eyes audit of the Phase 5 files:

- **Inline `restrict` LinearMap → `LinearMap.funLeft` + `codRestrict`** in
  `typeI_isInfinitesimallyRigid_extend` and
  `typeII_isInfinitesimallyRigid_extend` (closes deferred audit #1). The
  anonymous-constructor LinearMap (`toFun/map_add'/map_smul'`) is replaced by
  `(funLeft ℝ _ some).comp _.subtype |>.codRestrict _ h_into`.
- **Affine-line `Function.Injective` → `smul_left_injective`** in
  `exists_off_line_off_finite_dim_two` and `exists_typeII_q_on_line_dim_two`
  (closes deferred audit #2). The 6-line hand proof collapses to
  `fun _ _ h => smul_left_injective ℝ hv (add_left_cancel h)`.
- **`continuous_rigidityMap_apply` tagged `@[fun_prop]`** + per-edge
  `simp only [rigidityMap_apply]; fun_prop` lets downstream continuity
  goals close via `fun_prop`. Cascades to three call sites:
  `IsInfinitesimallyRigid.eventually` (multi-line `continuous_pi` block →
  `by fun_prop`), the perturbation continuity in
  `exists_nonCollinear_rigid_placement_dim_two`'s `h_p_t_cont`
  (replaced with `by fun_prop`; uses `Continuous.update`), and the
  difference continuity in `h_inj_ev` (replaced with `by fun_prop`).
- **`inner_sub_perp_of_eq` helper** (`HennebergRigidity.lean`).
  Factors the duplicated 5-line "orthogonal-difference recovery via shared
  target" block at the bottom of both `typeI_isInfinitesimallyRigid_extend`
  and `typeII_isInfinitesimallyRigid_extend`'s injectivity proofs. Each
  call site collapses from 5 lines to 1.
- **Sym2-symmetry inline simplification.** In
  `typeII_isInfinitesimallyRigid_extend`'s deleted-edge case-split, replaced
  the two `show … from by abel` rewrites with `← neg_sub` rewrites; pure
  cosmetic readability win.
- **`Finset.eq_singleton_of_mem_of_card_le_one`** in
  `Mathlib/Data/Finset/Card.lean` (mirror). Collapses the
  `Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr _)`
  + `Finset.card_singleton` boilerplate at 4 call sites in
  `Henneberg.lean`'s milestone-1 contradiction templates.
- **`nlinarith [Nat.le_mul_self d]`** for the quadratic bound
  `4 * d + 2 ≤ (d + 1) * (d + 2)` in `top_fin_two_isGenericallyRigidInj`,
  replacing a 3-line `ring`/`omega` chain.

Net effect: −36 LoC across `Framework.lean`, `Henneberg.lean`, and
`HennebergRigidity.lean`; one new mirror file
(`Mathlib/Data/Finset/Card.lean`).

*First post-closure cleanup pass.* Three small extractions plus a file split:

- **`SimpleGraph.mk_mem_edgesIn`** in `EdgesIn.lean`. Specialised
  constructor for `mem_edgesIn` at an explicit pair `s(x, y)`. Collapses
  the `mem_edgesIn.mpr ⟨_, by rw [Sym2.coe_mk]; exact
  Set.insert_subset_iff.mpr ⟨_, Set.singleton_subset_iff.mpr _⟩⟩`
  boilerplate at ~6 call sites in the milestone-1 blocker proofs
  (`no_isTightOn_excluding_three_neighbors`, `contradiction_one_pair`,
  `contradiction_two_pair`, `typeII_isLaman`).
- **`injective_option_elim`** (private, `HennebergRigidity.lean`).
  Factors the identical 4-way `rintro` injectivity proof at the bottom
  of `typeI_isGenericallyRigidInj_two` and
  `typeII_isGenericallyRigidInj_two_of_nonCollinear`.
- **`exists_not_mem_span_singleton_dim_two`** (private,
  `HennebergRigidity.lean`). Consolidates the
  `finrank_span_singleton` / `finrank_euclideanSpace_fin` /
  `SetLike.exists_not_mem_of_ne_top` chain that occurs in both
  `exists_off_line_off_finite_dim_two` and
  `exists_nonCollinear_rigid_placement_dim_two`.
- **File split**: `Henneberg.lean` → `Henneberg.lean` (1411 lines, was
  2002) + `HennebergRigidity.lean` (616 lines). The milestone-2
  rigidity-preservation work (everything from
  `eq_zero_of_orthogonal_dim_two` onward) moved out. `Henneberg.lean`
  no longer imports `Framework`, `FiniteDimensional.Lemmas`, or
  `IntervalCases`; `LamanTheorem.lean` now imports both. Reverses the
  *Architectural choices* decision that put move-rigidity in
  `Henneberg.lean` — "the lemma counts are small" stopped being true.

## Hand-off / next phase

Phase 5 is closed. `IsLaman.isGenericallyRigid_two` is fully proved;
the iff's `mpr` arm reduces to it directly. The only remaining `sorry`
in the project is `IsGenericallyRigid.exists_isLaman_le` (the iff's
`mp` arm), which is Phase 6's responsibility (Lovász–Yemini matroid
duality).

**Deferred audits (small leftover cleanups, can land alongside Phase 6
work or independently):** none. Both audits flagged at first-cleanup-pass
close (inline `restrict` LinearMap; affine-line injectivity) were resolved
in the second cleanup pass — see *Cleanup pass summaries* above.

**Remaining candidate audits — judgment calls, not blockers.** Each is
documented in the second-pass audit transcript and was deferred either
because (a) the savings are marginal vs. the abstraction cost or (b) the
unifying helper would have to cover too many shape variations:

- *`pair_add_smul_add_smul_iff` staging.* Three call sites
  (`exists_off_line_off_finite_dim_two`, `exists_typeII_q_on_line_dim_two`,
  `h_LI_perturbed` in `exists_nonCollinear_rigid_placement_dim_two`) build
  a 4-coefficient `h_form : ![…] = ![a • x + b • y, c • x + d • y]` block
  with `ext i; fin_cases i <;> simp; abel`. The coefficient sets differ
  enough that a unified helper would carry 4 scalars + 2 vectors + the
  determinant condition.
- *`IsInfinitesimallyRigid.iso` kernel iso.* The hand-built `LinearEquiv`
  between the two kernel subtypes could plausibly be factored through
  `LinearEquiv.funCongrLeft ℝ _ φ.symm.toEquiv` plus
  `LinearEquiv.ofSubmodules`. Investigated; the per-vertex coercion +
  Subtype packaging is roughly equal in line count, so left as-is.
- *`top_fin_two_isGenericallyRigidInj` range-pos.* The "exhibit a nonzero
  witness motion to bound `1 ≤ finrank range`" pattern would generalize to
  *any* `IsInfinitesimallyRigid` proof that goes via rank-nullity; extract
  if Phase 6 needs more `K_n`-style base cases.

**Next concrete commit (Phase 6 start):** seed `notes/Phase6.md` and
plan the rigidity matroid. `RigidityMatroid.lean` stands up on top of
the now-stable `Framework.lean` API (note: `IsInfinitesimallyRigid.
eventually` is available if rank-stability arguments are needed
upstream of the (⇒) direction). Lovász–Yemini's "rigidity matroid =
(2, 3)-count matroid in dim 2" is the deep step; Tay's 1993 short
proof of Laman's theorem is one alternative route to the same
identity. See ROADMAP §6.

## Appendix: degree-3 contradiction unification (post-mortem)

Originally proposed at the close of the Phase 1–5 blueprint review
(commit `bb9da0c`); executed in a follow-up session. The original
proposal text — the $(\star)$ analysis, the proposed primitive
signatures, the appendix's execution plan — landed largely as
written, but the LoC savings underestimated the cost of keeping the
three private contradiction templates around as scaffolding.

### What landed

- **`IsTightOn.union_with_bonus`** in `Sparsity.lean` — refinement of
  the union half of `IsTightOn.union_inter` that drops the
  `ℓ ≤ k · |s ∩ t|` size proviso in exchange for an explicit
  finite set `F` of bonus edges in `edgesIn (S₁ ∪ S₂)` disjoint from
  `edgesIn S₁ ∪ edgesIn S₂`, with a close-the-gap inequality on
  `|F| + k · |S₁ ∩ S₂|`. Specializes to `union_inter`'s union half at
  `F = ∅`.
- **`IsTightOn.insert_vertex_with_edges`** in `Sparsity.lean` —
  tight extension by a vertex `w ∉ S` with `≥ k` boundary edges (the
  `|F| ≥ k` hypothesis is the exact edge count needed to absorb the
  extra vertex while staying on the sparsity locus).
- **`IsLaman.False_of_pairwise_blocker_or_edge`** in `Henneberg.lean`
  (private) — unified contradiction dispatcher taking the three
  per-pair `Adj ∨ blocker` Or's plus the `¬ Adj` disjunction from
  `exists_nonadj_among_three_neighbors`; case-splits across 8 leaves
  and calls the relevant template internally.
- **Slimmed contradiction templates.** `contradiction_one_pair` calls
  `insert_vertex_with_edges`; `contradiction_two_pair`'s
  singleton-intersection branch calls `union_with_bonus` (the
  branch's 80-LoC inline supermodularity bookkeeping collapsed to
  ~40 LoC). `contradiction_three_pair` lost its unused `_nadj`
  arguments (only `hbc_nadj` is consumed in the proof body).
- **Small companion API helpers** added in the post-landing cleanup
  pass: `notMem_edgesIn_mk_of_left_notMem` /
  `notMem_edgesIn_mk_of_right_notMem` in `EdgesIn.lean` (companions to
  the existing `mk_mem_edgesIn`, collapsing 4 inline "vertex outside
  set ⇒ edge containing it outside `edgesIn`" blocks); and
  `three_le_card_of_three_distinct_mem` in
  `Mathlib/Data/Finset/Card.lean` (replacing two inline copies of the
  3-distinct-elements card bound).
- **Dropped `False_of_three_neighbor_squeeze`** (a 26-LoC private
  helper that bridged squeeze-form inequalities to `IsTightOn`). After
  the refactor, every caller produces `IsTightOn` directly via
  `union_with_bonus`, `union_inter`, or `insert_vertex_with_edges`, so
  the squeeze→tight upgrade is wasted work. All callers now feed
  `IsTightOn` straight to `no_isTightOn_excluding_three_neighbors`;
  the one branch (3-pair singleton chain) that still needed
  `isTightOn_of_le` got the upgrade inlined.
- **Collapsed dispatcher.** The degree-3 branch of
  `IsLaman.exists_typeI_or_typeII_reverse` reduced from a 14-branch
  `by_cases` (calling `typeII_reverse_witness_or_blocker` up to 8
  times) to three per-pair Or's (one call per pair) plus one
  `False_of_pairwise_blocker_or_edge` invocation.

### Where the original plan was wrong

The appendix predicted the three private templates would disappear in
favor of a single ~80-LoC unified lemma backed by primitive calls.
That under-delivered for the **3-pair singleton chain**: step 1
(`Sab ∪ Sac` with `|Sab ∩ Sac| = 1`) produces a set that is
genuinely 1-deficient (not tight), so `union_with_bonus` — which
returns *tightness* as its conclusion — cannot be applied. Step 2
then closes via `|S_1 ∩ S_2| = 2, e = 0`, "using up" the deficiency.
The two steps' deficiencies cancel only when chained, and the
primitive's API isn't shape-matched to that pattern: closing it
would require a "1-deficient intermediate" variant primitive whose
abstraction cost exceeds the savings.

The risks section had flagged this exact concern (*"If it does need a
variant, the savings shrink"*). It did. The 3-pair template stayed
as a private helper, using direct `edgesIn_ncard_add_le`
supermodularity at both chain steps (the existing inline argument);
the unified contradiction dispatches into it via three permuted
calls (rcases on `h_some_nonadj`, relabel `(a, b, c)` so the chosen
non-adj pair sits in the "outer" `(b, c)` slot the template expects).

### Updated size budget

Approximate line counts (each entry includes the lemma's docstring,
signature, and proof body), reflecting the cleanup pass that followed
the initial landing:

|                                       | Before | After |
|---------------------------------------|--------|-------|
| `contradiction_one_pair`              | ~61    | ~47   |
| `contradiction_two_pair`              | ~107   | ~68   |
| `contradiction_three_pair`            | ~122   | ~120  |
| `False_of_three_neighbor_squeeze`     | ~26    | —     |
| `False_of_pairwise_blocker_or_edge`   | —      | ~69   |
| Degree-3 dispatcher                   | ~98    | ~65   |
| `notMem_edgesIn_mk_of_{left,right}_notMem` (EdgesIn) | — | ~14 |
| `three_le_card_of_three_distinct_mem` (Mathlib mirror)| — | ~16 |
| `union_with_bonus` (Sparsity)         | —      | ~49   |
| `insert_vertex_with_edges` (Sparsity) | —      | ~26   |
| **Total (across files)**              | **~414**| **~474** |

Net ~+60 LoC, not the ~−210 the appendix predicted. The qualitative
wins remain: the two new primitives are reusable
(blueprint-eligible, potentially upstream alongside `IsTightOn`),
`typeII_reverse_witness_or_blocker` is invoked once per pair instead
of up to 8 times, and the per-pair Or pattern in the dispatcher is a
flat case-analysis instead of nested `by_cases`. Future work that
needs `(k, ℓ)`-tight set operations (Lovász–Yemini in Phase 6 is a
candidate) can lean on the primitives rather than reinventing the
bookkeeping.

### Cross-references

- Primitives: `IsTightOn.union_with_bonus`,
  `IsTightOn.insert_vertex_with_edges` in
  `CombinatorialRigidity/Sparsity.lean`. Blueprinted under
  `thm:isTightOn-union-with-bonus` and
  `thm:isTightOn-insert-vertex-with-edges` in
  `blueprint/src/chapter/sparsity.tex`.
- Unified contradiction: `IsLaman.False_of_pairwise_blocker_or_edge`
  in `CombinatorialRigidity/Henneberg.lean` (private; consumed by
  `IsLaman.exists_typeI_or_typeII_reverse`'s degree-3 branch).
- Blueprint-review origin of the proposal: commit `bb9da0c`.

