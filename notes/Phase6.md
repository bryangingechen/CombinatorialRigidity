# Phase 6 — Laman's theorem, (⇒) direction (work log)

**Status:** in progress.

This file is the per-phase work record. See `../ROADMAP.md` §6 for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 6 runs in **forward blueprint mode** (Option C,
hybrid skeleton) per `../blueprint/DESIGN.md`. The blueprint chapter
`chapter/laman-theorem.tex` (its $\Rightarrow$-direction subsection)
is the authoritative dep-graph and lemma index; this file does **not**
duplicate it. Each Lean session picks a leaf-most red node from the
dep-graph, formalizes it, and adds `\lean{...}` + `\leanok` to its
blueprint entry. Phase-end pass: write 1–3-sentence prose proofs per
entry against the now-stable Lean.

## Current state

Phase 5 closed with the iff statement
`isGenericallyRigid_two_iff_exists_isLaman_le` composed but
`sorry`-blocked on `IsGenericallyRigid.exists_isLaman_le`
(`LamanTheorem.lean:122`). That one `sorry` is the entire Phase 6
target — the project has no other unproved declarations.

The linear-algebra side is closed d-general (rank bounds, kernel
bound, basis-pick) and the analysis side is closed d-general
(affinely-spanning rigid placement). All four Lean-simplification
tasks (the session-start blueprint↔Lean review found four spots where
the Lean was heavier than the math) are resolved. The remaining red
nodes in `chapter/laman-theorem.tex` are
`lem:isSparse-of-rowIndependent-two` (the substantive sparsity step)
and the assembly target `thm:isGenericallyRigid-exists-isLaman-le`.
See *Next session* for the sparsity sketch.

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

### Promoted to TACTICS / FRICTION / DESIGN

- *`apnelson1/Matroid` investigated, not adopted* → DESIGN.md
  *Notion- and matroid-agnostic core* (rationale recorded there).
- *`rotJTwo` defined directly, not via `Matrix.toEuclideanLin`* →
  FRICTION *Defining the 2×2 90° rotation via `Matrix.toEuclideanLin`
  blocks coordinate simp*.
- *Dim-2 → d-general lift discipline* → *Design pattern established*
  (file end) plus FRICTION resolved entries (commit-17 d-general lift).

### Cleanup pass summaries

- *Commit 15 (`TrivialMotions.lean`):* TACTICS § 1 grind-default golf.
  37 lines deleted, no logic changes. `elemSkewMap_ofLp_inr_apply`
  body collapses to a one-liner `rcases ... <;> split_ifs <;> grind`;
  `inner_elemSkewMap_self`'s `i ≠ j` branch closes with `grind`;
  `trivialMotionFamily_linearIndependent`'s Steps 1–5 rewritten in
  term-mode `simpa` style.

## Blockers / open questions

All four phase-start blockers resolved: linear-algebra basis-pick
(commit 6), `TrivialMotions` Phase 4 deferred API (commit 7),
d-general finrank lower bound (commit 8), and generic-placement
affine-spanning lemma (commit 11). See the corresponding *Done*
entries for resolution details.

## Hand-off / next phase

**Done.** Commits 0–17. Setup (0–2): notes seeded, forward-mode
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
`Matrix.det_powerDifferences` (16). Two cleanup/golf passes:
`elemSkewMap_ofLp_inr_apply` cross-term lemma (14); TACTICS § 1
grind-default golf on `TrivialMotions.lean` (15). See `git log
--oneline --grep='phase6'` for commit-level detail.

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

**Future polish (low-priority, not blocking).** One cleanup remains
deferred behind the sparsity lemma:

- *Project-wide grind-default sweep.* TACTICS § 1's "default to
  `grind` for closing `simp`/`omega`/`linarith`" rule landed (in
  current form) after most Phases 1–5 work was written. The
  commit-15 pass on `TrivialMotions.lean` netted 37 lines deleted
  with no logic changes; a similar pass on other phase files
  (`Sparsity.lean`, `Henneberg.lean`, `Framework.lean`, …) is
  likely to find comparable wins. Method: `grep -n` for bare
  `omega` / `simp` / `simp; ring` / `linarith` closers, then
  `lean_multi_attempt` with `["grind", "grind only", <current>]`
  at each, and apply when grind succeeds and the current tactic
  is multi-line. Cost: ~1 session; risk: low (every change is
  verified by `lake build` and `lake lint`).

**Next session — the sparsity-side lemma
`lem:isSparse-of-rowIndependent-two`.** With the affinely-spanning
placement existence landed (commits 11 and 17, the latter generalising
to dimension `d`), the remaining substantial work is the combinatorial
sparsity argument: for `I ⊆ G.edgeSet` row-independent at `p` (where
`p` affinely spans on every size-`≥ 3` subset, as supplied by
`exists_affinelySpanning_rigid_placement` at `d = 2`), show the spanning subgraph
`H = fromEdgeSet (Subtype.val '' I)` is `(2, 3)`-sparse. The argument
splits by `|s|`:

- `|s| = 2`: `H.edgesIn ↑s` has at most one edge (simple graph), so
  `1 + 3 ≤ 4 = 2 * 2`.
- `|s| ≥ 3`: the rows of `G.RigidityMap p` indexed by
  `H.edgesIn ↑s` are LI (subset of `I`) and supported on `s`-columns,
  hence factor through `H[s].RigidityMap p|_s` and are LI there too.
  The d-general rank upper bound
  `rigidityMap_finrank_range_le_of_affinelySpanning` at `d = 2`
  applied to `H[s]` at `p|_s` (using the affine-span hypothesis at
  `↑s`) bounds the rank by `2|s| - 3`, hence `|H.edgesIn ↑s| ≤ 2|s| - 3`.

The technical bridge is the "row supported on columns of `s` factors
through `Framework s 2`" argument; this likely needs a custom
restriction linear map and the precomposition factoring trick.
`SimpleGraph.induce` can supply `H[s]`.

After the sparsity lemma, the assembly theorem
`thm:isGenericallyRigid-exists-isLaman-le` combines it with the
basis-pick and affinely-spanning placement to close the iff. Sparsity
is the last step with genuine combinatorial content; assembly is
mechanical glue. Reassess phase scope once sparsity's first attempt
lands.

**Design pattern established (commit 10).** When a Phase 6 helper has
a d-general statement that holds verbatim with no extra hypotheses
beyond what the d=2 critical path already provides, ship it
d-general and skip the d=2 corollary. The `rfl` reduction
`2 * (2 + 1) / 2 → 3` on `Nat` literals means callers consume
d-general lemmas at `d = 2` with zero specialisation ceremony.
Dim-2-shaped statements that *do* deserve a dedicated d=2 surface are
those where the dim-2 conclusion is structurally specific (e.g.,
`exists_edgeSetRowIndependent_basis_dim_two`'s `|I| = 2 * #V - 3`).
