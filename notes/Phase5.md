# Phase 5 — Laman's theorem, (⇐) direction (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

## Current state

Milestones 0, 1, and 2's typeI half are fully complete. Milestone 2's
typeII half is *conditionally* complete (rank-nullity core
`typeII_isInfinitesimallyRigid_extend` and conditional wrapper
`typeII_isGenericallyRigidInj_two_of_nonCollinear`, with non-collinearity
passed in as hypothesis). Milestone 3 is *structurally complete*: the
strong induction lands in `LamanTheorem.lean` as the private helper
`IsLaman.isGenericallyRigidInj_two_of_card` (base case and typeI step
fully proved); `IsLaman.isGenericallyRigid_two` derives via
`.toIsGenericallyRigid`. The **sole remaining sorry** is the granular
typeII collinearity gap inside the inductive step: the IH supplies
*some* injective rigid placement, but
`typeII_isGenericallyRigidInj_two_of_nonCollinear` requires the placement
to be non-collinear on the specific `(a, b, c)` chosen by the reverse
decomposition. Closure routes (openness-of-IR / perturbation; or a
strengthened inductive invariant) are unchanged from milestone 2 — see
*Blockers* and *Hand-off*. Phase 6 (⇒ direction) is unstarted.

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
decomposition asserting `G'.IsLaman` (Whiteley §3 / Jordán §3.1).

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
  1/2/3-pair contradiction templates.
- [x] `IsLaman.exists_typeI_or_typeII_reverse` — degree-2 via
  `typeI_isLaman_iff`, degree-3 via 8-leaf `by_cases` per pair.

### Milestone 2 — Move preservation in dim 2 (`Henneberg.lean`) — typeI done, typeII conditional

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
- [ ] `typeII_isGenericallyRigidInj_two` — *unconditional* typeII
  preservation. Open. See *Blockers* (typeII collinearity).

### Milestone 3 — Induction (fills milestone-0 sorry) — structurally complete, granular sorry

- [x] `IsLaman.eq_top_of_card_eq_two` in `Laman.lean` — base-case
  helper: Laman + `card V = 2` ⇒ `G = ⊤`.
- [x] (Private) `IsLaman.isGenericallyRigidInj_two_of_card` in
  `LamanTheorem.lean` — strong induction on `Fintype.card V`. Base
  (`card V = 2`): `eq_top_of_card_eq_two` + iso transport via
  `Iso.completeGraph (Fintype.equivFinOfCardEq ·).symm` applied to
  `top_fin_two_isGenericallyRigidInj 1`. Step (`card V ≥ 3`):
  `Henneberg.IsLaman.exists_typeI_or_typeII_reverse` + IH at
  `Fintype.card {w // w ≠ v}` (via `Fintype.card_subtype_lt`) +
  per-move strong-form preservation + iso transport. **Granular
  `sorry` on the typeII branch's `LinearIndependent
  ℝ ![p b - p a, p c - p a]`** — see *Blockers*.
- [x] `IsLaman.isGenericallyRigid_two` — wired through
  `isGenericallyRigidInj_two_of_card.toIsGenericallyRigid`. Inherits
  the granular sorry; the iff's `mpr` arm now reduces to it.

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

- **Milestone 3 typeII gap: granular sorry, not whole-theorem sorry.**
  Replaced the milestone-0 single sorry on
  `IsLaman.isGenericallyRigid_two` with the strong-induction proof,
  leaving exactly one granular `sorry` inside the typeII branch (for
  `LinearIndependent ℝ ![p b - p a, p c - p a]`). Benefits: base case
  + typeI step + iso transport all land; the obstruction crystallizes
  at a precise location; the iff's `mpr` arm now reduces to that single
  sorry. Closure (openness-of-IR / perturbation) merits its own commit
  cluster — see *Blockers* / *Hand-off*.

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

## Blockers / open questions

- **Unconditional typeII rigidity preservation needs non-collinear
  `(p a, p b, p c)`.** The conditional rank-nullity argument
  (`typeII_isInfinitesimallyRigid_extend`) places `q` on the line
  through `p a, p b`: the deleted edge `s(a, b)` is recovered because
  the two new edges at `none ↔ some a` and `none ↔ some b` both lie in
  the `p b - p a` direction (subtracting them yields the deleted-edge
  inner product). Injectivity of the kernel restriction `x ↦ x ∘ some`
  then uses the third new edge at `none ↔ some c`, which pins `x none`
  *iff* `q - p c` is LI from `q - p a` — equivalent to `(p a, p b, p c)`
  being non-collinear when `q` is on the `(p a, p b)`-line. Collinear
  placements genuinely fail rigidity (1-dim free perpendicular motion of
  `none`); no choice of `q` works (off-line breaks deleted-edge recovery,
  on-line fails injectivity).

  Two resolution routes:
  - **(a) Openness of IR + perturbation.** Show
    `{p : G.IsInfinitesimallyRigid p}` is open in `Framework V 2` (rank
    of `RigidityMap p` as a continuous function of `p` is lower-
    semicontinuous), then perturb `p c` perpendicular to `p b - p a`.
    Substantial: needs the `LinearMap.toMatrix` view of `RigidityMap`
    (Phase 4 deferred) + the matrix-rank lower-semicontinuity argument.
    Estimated ~200 LoC.
  - **(b) Strengthen milestone-3 induction invariant.** Maintain a
    predicate stronger than `IsGenericallyRigidInj` that guarantees
    non-collinearity at the specific `(a, b, c)` triple chosen by
    `exists_typeI_or_typeII_reverse`. Tricky because a single placement
    can't be non-collinear for every triple simultaneously (typeII
    forces a collinear triple by construction); a refined invariant
    needs to be more local than "no three collinear", and the typeI
    wrapper would need to avoid finitely many lines.

  See *Hand-off* for the decision posture and option C (defer to
  Phase 6's matroid bypass).

- *Resolved blockers (carryover from earlier milestones):*
  Placement-construction side condition for typeI (closed by
  `IsGenericallyRigidInj` + `exists_off_line_off_finite_dim_two`);
  Affine-spanning side condition (superseded by the injective predicate);
  Milestone-1 proof length (landed in 2 sessions; templates kept private
  in `Henneberg.lean`).

## Hand-off / next phase

Milestone 3 ships *structurally complete*: the strong-induction skeleton,
base case, and typeI step all land. The proof of
`IsLaman.isGenericallyRigid_two` is wired through the private strong-form
helper `IsLaman.isGenericallyRigidInj_two_of_card` (strong induction on
`Fintype.card V`, IH applied at `Fintype.card {w // w ≠ v}` via
`Fintype.card_subtype_lt`) and `.toIsGenericallyRigid`. The remaining
sorry is granular — a single `sorry` for
`LinearIndependent ℝ ![p b - p a, p c - p a]` inside the typeII branch
of the inductive step, exactly the milestone-2 collinearity gap.

**Next concrete commit (option A — close the gap):** implement
openness of `IsInfinitesimallyRigid` in `Framework V 2` and the
perturbation step. The proof builds the rigidity-matrix view
(Phase 4's deferred `LinearMap.toMatrix` of `RigidityMap`), then
applies lower semi-continuity of matrix rank: there's an open set
of placements containing `p` on which rank stays ≥ the rank at `p`,
hence kernel dimension stays ≤ `d(d+1)/2`. With openness, perturb
`p c` along a direction perpendicular to `p b - p a` to break
collinearity. Expected size: ~200 LoC across `Framework.lean`
(matrix view + openness lemma) and `Henneberg.lean` (the
`typeII_isGenericallyRigidInj_two` unconditional wrapper).

**Next concrete commit (option B — strengthen the invariant):** widen
the inductive predicate from `IsGenericallyRigidInj` to a variant
that records enough non-collinearity to feed the typeII step. The
challenge from milestone 2 stands: a single placement can't be
non-collinear at every triple post-typeII (typeII forces a collinear
triple by construction). Look for a relaxed invariant that only
records non-collinearity for the *bridge-edge endpoints' third
neighbor* — i.e., the Henneberg structure of derivable typeII reverses
from this placement. Doable but invasive to the typeI wrapper.

**Option C — defer to Phase 6.** Phase 6's matroid duality
(`IsGenericallyRigid.exists_isLaman_le`) gives the (⇒) direction
unconditionally; it might also subsume the typeII gap by exhibiting
a rigid placement directly from the matroid basis without needing a
Henneberg-induction witness. If Phase 6's matroid-bypass route is
substantially less work than option A's openness argument, switching
phases may be the better marginal investment.

Decision deferred to whichever next session opens the file. The
`IsLaman.isGenericallyRigid_two` body has exactly one sorry; the iff
statement's `mpr` arm reduces to that sorry; Phase 6's
`exists_isLaman_le` sorry covers the `mp` arm.
