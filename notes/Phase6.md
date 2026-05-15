# Phase 6 — Laman's theorem, (⇒) direction (work log)

**Status:** ✓ complete.

This file is the per-phase work record. See `../ROADMAP.md` §6 for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 6 ran in **forward blueprint mode** (Option C,
hybrid skeleton) per `../blueprint/DESIGN.md`. The blueprint chapter
`chapter/laman-theorem.tex` (its $\Rightarrow$-direction subsection)
was the authoritative dep-graph and lemma index throughout; this file
does **not** duplicate it.

## Current state

Phase 6 closes. The two final substantive lemmas — the sparsity step
`isSparse_of_edgeSetRowIndependent_dim_two` and the assembly
`IsGenericallyRigid.exists_isLaman_le` — landed in commit 19. The iff
`isGenericallyRigid_two_iff_exists_isLaman_le` in
`LamanTheorem.lean` (Phase 5's composed statement) is now `sorry`-free,
and Laman's theorem is fully formalized. The project carries no
unproved declarations.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Forward-mode blueprint authoring** (Option C). The blueprint
  chapter's $\Rightarrow$-direction subsection is the authoritative
  dep-graph; `\lean{...}` and `\leanok` get added as each Lean lemma
  lands. We do **not** maintain a parallel lemma checklist here.
  Rationale: `../blueprint/DESIGN.md` *Recommendation for Phase 6*.

- **New file `RigidityMatroid.lean`** (per ROADMAP §6, DESIGN.md
  *Notion- and matroid-agnostic core*). Imported by `LamanTheorem.lean`.

- **Stay matroid-agnostic in the proof body; defer the abstract
  `Matroid` packaging.** Two linear-algebra ingredients (rank lower
  bound at generically-rigid placement; $(2,3)$-sparsity-from-
  row-independence) suffice for `exists_isLaman_le`; neither needs
  `Mathlib.Combinatorics.Matroid`. Defer; revisit at phase end.

- **Lovász–Yemini's "easy direction" only.** Phase 6 ships
  "row-LI $\Rightarrow$ $(2,3)$-sparse subgraph". The deep converse
  is a separate milestone.

- **`TrivialMotions` Phase 4 deferred API landed here** (commits
  7–8, 10): d-general `trivialMotions` submodule, the d-general
  finrank lower bound from affine-spanning, and the kernel bound
  feeding the d-general rank upper bound.

## Lemma checklist

**Maintained in the blueprint, not here.** The authoritative checklist
is `chapter/laman-theorem.tex`'s $\Rightarrow$-direction subsection,
visible as a dep-graph at `blueprint/web/dep_graph_document.html`
after `inv bp && inv web`. A red node = not yet formalized; a green
node = formalized and `\leanok`-tagged. Pick leaf-most red.

Two red nodes remain: `lem:isSparse-of-rowIndependent-two` (sparsity,
the next substantial step) and the assembly target
`thm:isGenericallyRigid-exists-isLaman-le`. Sparsity stacks on the
d-general rank upper bound (at `d = 2`) plus the affinely-spanning
placement; assembly stacks on sparsity plus the basis-pick.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **d-general only; no d=2 corollary surface.** Commit 10 retired the
  d=2 corollaries of the rank bounds and kernel bound; callers at
  `d = 2` consume d-general lemmas directly via `rfl` on
  `2 * (2 + 1) / 2 → 3`. See *Design pattern established* (file end)
  for the forward-looking rule. *Asymmetry:* `exists_edgeSetRowIndependent_basis_dim_two`
  stays dim-2-shaped because its conclusion `|I| = 2 * #V - 3` is
  structurally dim-2.

- **Dual-bridge for the basis-pick.** `EdgeSetRowIndependent` is
  stated in the function module (blueprint shape), but rank
  identities need the dual module. Proof works in the dual via
  `rigidityRow` / `span_range_rigidityRow`, transports back via
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`; envelope is
  `LinearMap.ltoFun ℝ _ ℝ ℝ` + `DFunLike.coe_injective`.

- **TrivialMotions API in its own file, d-general** (commit 7
  design pivot). Lives in `CombinatorialRigidity/TrivialMotions.lean`
  parallel to `Framework.lean`; submodule formulation lets
  `trivialMotions_le_ker` ship unconditionally and the finrank bound
  as a `Submodule.finrank_mono` one-liner.

- **Skew-sum + affine-spanning route for the d-general LI.**
  `trivialMotionFamily_linearIndependent` (commit 8) routes through a
  skew-sum endomorphism `S` on `EuclideanSpace ℝ (Fin d)`: vanishing
  combination at `v` gives `t + S(p v) = 0`; subtracting at two
  vertices kills `t`; affine spanning + `LinearMap.eqOn_span` extends
  `S = 0` from differences to all of $\R^d$. The named-linear-map
  abstraction is doing the affine-spanning step's work.

- **Matrix-determinant route for the d-general analysis leaf**
  (commit 17). Difference matrices `M₀, M₁` of shape `Fin d × Fin d`;
  the polynomial `P := (X • M₁.map C + M₀.map C).det ∈ ℝ[X]` has
  `coeff P d = det M₁ = ∏_{i<j} (φ vⱼ - φ vᵢ) ≠ 0`
  (`coeff_det_X_add_C_card` + `det_powerDifferences`); `P.eval t =
  (t • M₁ + M₀).det` via `RingHom.map_det` on `evalRingHom t`. The
  AI↔det bridge is private helper
  `affineIndependent_of_difference_det_ne_zero` (~10 LoC).

- **Sparsity (commit 19) routes through `SimpleGraph.induce` rather
  than building a custom restricted rigidity map.** The induced
  subgraph `H.induce ↑s : SimpleGraph ↥(↑s : Set V)` plus the
  framework restriction `LinearMap.funLeft ℝ _ Subtype.val :
  Framework V 2 →ₗ[ℝ] Framework ↥(↑s) 2` gives a clean factoring:
  `G.rigidityRow p (lift e') = restrict.dualMap ((H.induce ↑s).rigidityRow p_s e')`
  for each induced-graph edge `e'` (where `lift e' : G.edgeSet` is
  `Sym2.map Subtype.val e'.val`). `LinearIndependent.of_comp` on
  `restrict.dualMap` transports LI of V-side rows (subfamily of `hI`
  via injectivity of `lift`) to LI of `H.induce ↑s`-rows. The
  helper `ncard_edgesIn_eq_ncard_induce_edgeSet` in `EdgesIn.lean`
  bridges `H.edgesIn ↑s` and `(H.induce ↑s).edgeSet` via
  `Sym2.map.injective Subtype.val_injective`. The `|s| = 2` corner
  uses `card_edgeFinset_le_card_choose_two` on the induced subgraph
  (≤ `2.choose 2 = 1`) — no separate combinatorial branch needed.

- **Assembly (commit 19) splits the basis-pick.** The existing
  `exists_edgeSetRowIndependent_basis_dim_two` (existence form: from
  `IsGenericallyRigid`, produce both `p` and the basis) factored into
  the placement-fixed `exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`
  (from a rank lower bound at a specific `p`, produce the basis) plus
  a two-line wrapper. The assembly proof uses the placement-fixed
  version with the IR + affinely-spanning `p` from
  `exists_affinelySpanning_rigid_placement`, then applies sparsity
  at that `p`. The whole assembly is ~25 lines.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *`apnelson1/Matroid` investigated, not adopted* → DESIGN.md
  *Notion- and matroid-agnostic core* (rationale recorded there).
- *`rotJTwo` defined directly, not via `Matrix.toEuclideanLin`* →
  FRICTION *Defining the 2×2 90° rotation via `Matrix.toEuclideanLin`
  blocks coordinate simp*.
- *Dim-2 → d-general lift discipline* → *Design pattern established*
  (file end) plus FRICTION resolved entries (commit-17 d-general lift).

### Cleanup pass summaries

- *Commit 15 (`TrivialMotions.lean`):* TACTICS-GOLF § 1 grind-default golf.
  37 lines deleted, no logic changes. `elemSkewMap_ofLp_inr_apply`
  body collapses to a one-liner `rcases ... <;> split_ifs <;> grind`;
  `inner_elemSkewMap_self`'s `i ≠ j` branch closes with `grind`;
  `trivialMotionFamily_linearIndependent`'s Steps 1–5 rewritten in
  term-mode `simpa` style.
- *Commit 18 (`Sparsity.lean`, `Laman.lean`):* project-wide
  grind-default sweep on Phase 1–5 files. 6 lines net. Four wins,
  all of shape "multi-step `unfold P at h; ...; omega` body collapses
  to `grind only [P]`": `IsSparse.isTightOn_of_le` (4→2),
  `IsTightOn.union_with_bonus` final block (3→2),
  `IsTightOn.insert_vertex_with_edges` final block (4→3),
  `IsLaman.eq_top_of_card_eq_two`'s `hG_card` have-body (4→2). Most
  bare `omega`/`simp` closers in Phases 1–5 are correctly `omega`
  per TACTICS-GOLF § 1 (pure linear arithmetic after staged `have`s);
  the sweep yield concentrated where the def `IsTightOn` had to be
  unfolded to expose arithmetic. See *Future polish — resolved
  (continued)* below for the calibration note.

## Blockers / open questions

All four phase-start blockers resolved: linear-algebra basis-pick
(commit 6), `TrivialMotions` Phase 4 deferred API (commit 7),
d-general finrank lower bound (commit 8), and generic-placement
affine-spanning lemma (commit 11). See the corresponding *Done*
entries for resolution details.

## Hand-off / next phase

**Done.** Commits 0–19. Setup (0–2): notes seeded, forward-mode
blueprint skeleton, bibliography. Linear-algebra infrastructure
(3–10): `EdgeSetRowIndependent`; basis-pick
`exists_edgeSetRowIndependent_basis_dim_two` via the dual bridge;
`TrivialMotions.lean` with d-general translation/rotation submodules,
the unconditional `trivialMotions_le_ker`, the d-general finrank
lower bound via skew-sum + affine-spanning; rank upper and lower
bounds for `G.RigidityMap p`. Commit 10 lifted everything in this
group to d-general statements, retiring the d=2 corollary surface
(see *Design pattern established*). Analysis leaf (11, 17):
affinely-spanning rigid placement via moment-curve perturbation;
commit 11 shipped dim-2; commit 17 lifted to d-general via
matrix-determinant route. Four mirrors landed: `Pi.basisFun_dualBasis`
and `LinearMap.range_dualMap_eq_span_image_dualBasis` (13);
`Matrix.det_powerDifferences` (16). Three cleanup/golf passes:
`elemSkewMap_ofLp_inr_apply` cross-term lemma (14); TACTICS-GOLF § 1
grind-default golf on `TrivialMotions.lean` (15); project-wide
grind-default sweep on `Sparsity.lean` and `Laman.lean` (18).
**Closing commit (19): sparsity + assembly.**
`isSparse_of_edgeSetRowIndependent_dim_two` in `RigidityMatroid.lean`
(routes through `H.induce ↑s`, factors V-side rows through the
framework-restriction map, applies the d-general rank upper bound at
the affinely-spanning restricted placement). The basis-pick factored
into a placement-fixed `_of_finrank_range_ge_dim_two` companion plus
a two-line existence wrapper. The assembly
`IsGenericallyRigid.exists_isLaman_le` in `LamanTheorem.lean` is ~25
lines: IR + affinely-spanning placement, rank lower bound at it via
rank-nullity, basis-pick at it, sparsity at it, then assemble Laman
via the `Subtype.val '' I` transport (encoding-choice rationale below).
The Phase 5 iff `isGenericallyRigid_two_iff_exists_isLaman_le` is now
`sorry`-free. EdgesIn.lean gained the bridge
`ncard_edgesIn_eq_ncard_induce_edgeSet` (and
`edgesIn_eq_image_induce_edgeSet`) connecting our `edgesIn` to
mathlib's `induce` via `Sym2.map Subtype.val`. See
`git log --oneline --grep='phase6'` for commit-level detail.

**Encoding choice rationale (`I : Set G.edgeSet`).** The index type
sits inside `G.edgeSet`, matching the blueprint's "$I \subseteq E(G)$".
Downstream, the spanning-subgraph construction needs `Set (Sym2 V)`
not `Set G.edgeSet`, so the assembly proof will transport via
`Subtype.val '' I`. We pay that adapter cost once at assembly rather
than carry it through the basis lemma + sparsity lemma + every
intermediate API.

**Lean-simplification pass — resolved.** A session-start
blueprint↔Lean review flagged four points where the Lean was more
involved than the blueprint prose suggested. All four landed: (1)
the dim-2 AI ↔ det reindex via `finSuccAboveEquiv` +
`linearIndependent_equiv` (later subsumed by task 4); (2) the
basis-pick "small dual bridge" collapsed to `LinearMap.ltoFun` (commits
12–13); (3) the `trivialMotionFamily_linearIndependent` cross-term
case-split hoisted to `elemSkewMap_ofLp_inr_apply` (commit 14); (4)
the d-general lift of the analysis leaf (commits 16–17). Per-task
detail preserved in FRICTION resolved entries and commit messages.

**Future polish — resolved.** Three of the four originally-deferred
cleanups landed (see FRICTION resolved/mirrored entries for details):
the `Polynomial.eval_det_X_add_C` mirror (collapses `hP_eval` to a
one-liner), the `Set.exists_injective_fin_of_le_ncard` mirror
(collapses the `q`-construction in the assembly step to one `obtain`,
and ready to reuse in the upcoming sparsity lemma), and the
`LinearMap.ext_on` retargeting in `trivialMotionFamily_linearIndependent`
(no mirror needed — the lemma was already upstream).

**Future polish — resolved (continued).** The project-wide
grind-default sweep landed in commit 18 (`Sparsity.lean` and
`Laman.lean`; 6 lines net). The yield was much smaller than
commit-15's 37 lines on `TrivialMotions.lean` because the Phase 1–5
files were already written with cleaner staging discipline: most
bare `omega` closers in those files sit at the end of pure
arithmetic chains where TACTICS-GOLF § 1 explicitly prefers `omega` over
`grind` (faster and more readable). The wins concentrated in three
spots where a multi-step `unfold IsTightOn at h; ...; omega` body
collapsed to `grind only [IsTightOn]` (`IsSparse.isTightOn_of_le`,
`IsTightOn.union_with_bonus`, `IsTightOn.insert_vertex_with_edges`)
plus one 4-line `have ...; rw ...; omega` body in
`IsLaman.eq_top_of_card_eq_two`'s `hG_card`. Other candidates
(`Henneberg.lean`'s tightly-staged branch closers, `Framework.lean`'s
rank-nullity omegas, the `Sym2`-induction `<;> simp` patterns) were
tested with `lean_multi_attempt` and rejected — either grind
couldn't subsume the staging, or the body was already minimal. The
calibration lesson: the sweep is worth running once per heavy file
(commit 15's pattern was specific to `TrivialMotions.lean`), and
the per-commit friction review remains the right ongoing mechanism
to catch new pre-grind patterns as they're written.

**Encoding-choice payoff at assembly (commit 19).** Carrying
`I : Set G.edgeSet` through Phase 6 (instead of `Set (Sym2 V)`) cost
one adapter at assembly: `H := fromEdgeSet (Subtype.val '' I)` with
the two-line lemma `H.edgeSet = Subtype.val '' I` (the `\ diagSet`
collapses because `I ⊆ G.edgeSet` excludes diagonals) and a one-line
`H ≤ G`. `H.edgeSet.ncard = I.ncard = 2|V| - 3` follows from
`Set.ncard_image_of_injective` on `Subtype.val_injective`. The
adapter is contained and the rest of the assembly worked with the
clean `Set G.edgeSet` API.

**Phase complete.** Laman's theorem is fully formalized; the project
has no `sorry`s. No "next phase" in the Phase 6 sense; future work
options live in the *Phase-7 candidates* section below.

**Design pattern established (commit 10).** When a Phase 6 helper has
a d-general statement that holds verbatim with no extra hypotheses
beyond what the d=2 critical path already provides, ship it
d-general and skip the d=2 corollary. The `rfl` reduction
`2 * (2 + 1) / 2 → 3` on `Nat` literals means callers consume
d-general lemmas at `d = 2` with zero specialisation ceremony.
Dim-2-shaped statements that *do* deserve a dedicated d=2 surface are
those where the dim-2 conclusion is structurally specific (e.g.,
`exists_edgeSetRowIndependent_basis_dim_two`'s `|I| = 2 * #V - 3`).

## Phase-7 candidates

The Lovász–Yemini identification of the rigidity matroid with the
$(2, 3)$-count matroid in dim 2 has only its *easy direction* shipped
(row-LI ⇒ $(2, 3)$-sparse). The deep converse — $(2, 3)$-sparse
⇒ row-LI at some generic placement — is a separate milestone and
would package the rigidity matroid as a `Mathlib.Combinatorics.Matroid`
object. Other natural extensions: Whiteley's polarity route, the
$d \ge 3$ rigidity-matroid theory (Maxwell counting + extra
constraints), or generic-rigidity decidability via the Henneberg
moves.
