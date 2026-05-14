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

**Through commit 8 (this commit):** `CombinatorialRigidity/RigidityMatroid.lean`
ships the rank lower bound, `EdgeSetRowIndependent` predicate, and the
basis-pick `exists_edgeSetRowIndependent_basis_dim_two` (commit 6).
`CombinatorialRigidity/TrivialMotions.lean` ships the full d-general
trivial-motions API: translations, infinitesimal rotations, the
`trivialMotions` submodule (commit 7), and the d-general finrank lower
bound `trivialMotions_finrank_ge_of_affinelySpanning` (commit 8) —
`d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` at any
affinely-spanning placement, with the dim-2 lemma a one-line
corollary. The blueprint chapters `chapter/laman-theorem.tex` and
`chapter/trivial-motions.tex` carry the forward-mode dep-graph, with
all landed lemmas tagged `\lean{...}` + `\leanok`; see
`blueprint/web/dep_graph_document.html` after `inv bp && inv web`.
Citations chain (Laman 1970 → Asimow–Roth 1978 → Jordán 2016) was
researched and added in commit 2; we stay matroid-agnostic per the
commit-5 investigation.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Forward-mode blueprint authoring** (Option C). The blueprint
  chapter's $\Rightarrow$-direction subsection becomes the
  authoritative dep-graph from Phase 6 commit 1; `\lean{...}` and
  `\leanok` get added as each Lean lemma lands. Prose proofs are
  deferred to a phase-end pass. Rationale lives in
  `../blueprint/DESIGN.md` *Recommendation for Phase 6*. We do
  **not** maintain a parallel lemma checklist in this file — the
  dep-graph is the single source of truth, and parallel lists rot.

- **New file `RigidityMatroid.lean`.** Per ROADMAP §6 and DESIGN.md
  *Notion- and matroid-agnostic core* / *Why Henneberg, not matroid*.
  Phase 4 deliberately kept the abstract rigidity matroid out of
  `Framework.lean`; Phase 6 stands the file up alongside it. Lives
  at `CombinatorialRigidity/RigidityMatroid.lean`; imported by
  `LamanTheorem.lean`.

- **Stay matroid-agnostic in the proof body; defer the abstract
  `Matroid` packaging.** The honest minimum surface area for closing
  `exists_isLaman_le` is two linear-algebra ingredients
  (a rank lower bound for generically-rigid placements, and a
  $(2,3)$-sparsity-from-row-independence lemma); neither requires
  `Mathlib.Combinatorics.Matroid`. Building the `Matroid` instance is
  reusable infrastructure but not on the critical path. Defer; revisit
  at end of Phase 6 if it ends up trivial once the supporting
  lemmas land.

- **Lovász–Yemini's "easy direction" only.** Closing
  `exists_isLaman_le` needs only *row-independent in rigidity matroid
  $\Rightarrow$ $(2,3)$-sparse subgraph*. The harder converse
  $(2,3)$-sparse $\Rightarrow$ row-independent at a generic placement
  is the deep half of Lovász–Yemini and is **not needed** for the iff;
  Phase 6 ships without it. If a future phase wants the full
  equality, that's a separate milestone.

- **`TrivialMotions` Phase 4 deferred API may need to land here.**
  The $(2,3)$-sparsity argument uses the rank bound
  $\rk\,R_{H[S]}(p|_S) \le 2|S| - 3$ for $|S| \ge 3$, which goes
  through the affinely-spanning-implies-$\dim\,\mathrm{TrivialMotions} = 3$
  identity (Phase 4 *Lemma checklist*, deferred). Exact form is TBD;
  flagged under *Blockers* below.

## Lemma checklist

**Maintained in the blueprint, not here.** The authoritative checklist
is `chapter/laman-theorem.tex`'s $\Rightarrow$-direction subsection,
visible as a dep-graph at `blueprint/web/dep_graph_document.html`
after `inv bp && inv web`. A red node = not yet formalized; a green
node = formalized and `\leanok`-tagged. Pick leaf-most red.

Status snapshot at commit-8 (d-general trivial-motions API):
`chapter/trivial-motions.tex` now covers the full d-general
finrank lower bound `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)`
at any affinely-spanning placement, with the dim-2 lemma reduced to
a one-line corollary. Four new green nodes vs. commit 7:
`def:elemSkewMap`, `lem:inner-elemSkewMap-self`,
`def:trivialMotionFamily`, `lem:trivialMotionFamily-mem-trivialMotions`,
`lem:trivialMotionFamily-linearIndependent`, and
`lem:trivialMotions-finrank-ge-of-affinelySpanning`. The remaining
red nodes —
`lem:rigidityMap-finrank-range-le-of-affinelySpanning-two`,
`lem:exists-affinelySpanning-rigid-placement-two`,
`lem:isSparse-of-rowIndependent-two` — and the target
`thm:isGenericallyRigid-exists-isLaman-le` stay red. The remaining
leaf is `lem:exists-affinelySpanning-rigid-placement-two`; everything
else stacks above it or the rank upper bound (which is now a
one-liner from rank-nullity plus the trivial-motions kernel bound).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Dual-bridge for the basis-pick.** `EdgeSetRowIndependent` is stated
  as `LinearIndepOn` of a family of plain functions `Framework V d →
  ℝ` (matching the blueprint), but the rank identities we need
  (`LinearMap.finrank_range_dualMap_eq_finrank_range`,
  `Pi.basisFun.dualBasis`) require viewing the rows as linear
  functionals (`Module.Dual ℝ (Framework V d)`). The basis-pick proof
  works in the dual module throughout (via `rigidityRow` and
  `span_range_rigidityRow`), then transports the resulting LI back to
  the function-module form via `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`.
  The bridge needed a private `dualToFunₗ : Module.Dual ℝ M →ₗ[ℝ] (M
  → ℝ)` since mathlib doesn't ship the `ℝ`-linear envelope of
  `FunLike.coe` directly (see FRICTION *No packaged ℝ-linear
  injection*).

- **`apnelson1/Matroid` investigated, not adopted.** The external repo
  ships `Module.matroid` (in `Matroid/Representation/Map.lean`) — a
  `Matroid W` whose ground set is a vector space and whose
  independence is linear independence — and the derived `Matroid.ofFun
  𝔽 E f` for an arbitrary function `f : α → W`, both built on top of
  `IndepMatroid.ofFinitaryCardAugment`. Toolchain pin
  (`leanprover/lean4:v4.30.0-rc2`) matches ours exactly. *Not adopted*
  because the abstraction does not collapse the hard step: the
  basis-pick lemma needs column-rank-to-row-rank
  (`LinearMap.finrank_range_dualMap_eq_finrank_range`,
  `Mathlib/LinearAlgebra/Dual/Lemmas.lean:918`) either way, and going
  through `Matroid.ofFun` would only hide that step inside
  `Matroid.ofFun`'s rank API rather than remove it. Branch (c) of the
  *Hand-off* plan wins on cost: ~30 lines of pure linear algebra, no
  new dep, no new mirror.

- **TrivialMotions API in its own file, d-general.** Per the user's
  Phase 6 design-pivot (commit 7), the trivial-motions API lives in
  its own `CombinatorialRigidity/TrivialMotions.lean` (parallel to
  `Framework.lean`) rather than buried inside `RigidityMatroid.lean`.
  Three reasons. (a) The motions are *general* infrastructure on
  frameworks, not specifically a matroid concept. (b) The definitions
  (`translationMotion`, `infinitesimalRotation`, `trivialMotions`) are
  d-general; only the finrank lower bound (`rotJTwo` + the LI of three
  motions) is dim-2-specific, and it's natural to keep the d-general
  surface separate from the dim-2 specialisation. (c) The submodule
  formulation lets `trivialMotions_le_ker` ship as one unconditional
  lemma and `3 ≤ finrank ker` as a clean one-liner from
  `Submodule.finrank_mono`, rather than inlining three motion-checks
  in the kernel lemma. The blueprint chapter
  `chapter/trivial-motions.tex` mirrors the Lean file's structure
  one-to-one. The finrank lower bound is shipped dim-2-specific in
  commit 7; *Blockers* records the d-general generalisation as
  deferred follow-up work (the dim-2 lemma is the `d = 2` instance).

- **`rotJTwo` defined directly, not via `Matrix.toEuclideanLin`.** First
  attempt routed `rotJTwo := Matrix.toEuclideanLin !![0, -1; 1, 0]`,
  which left downstream `simp` calls fighting `Matrix.mulVec` /
  `Matrix.dotProduct` / `Matrix.vecHead` unfolding. Switched to a
  direct `LinearMap.mk' (fun v => !₂[-(v 1), v 0])` so that
  `rotJTwo_apply_zero/one` are `rfl`-simp lemmas; downstream proofs
  then close coordinates without matrix-unfolding hints. FRICTION
  entry filed (*Defining the 2×2 90° rotation via `Matrix.toEuclideanLin`
  blocks coordinate simp*).

- **Skew-sum + affine-spanning route for the d-general LI.** The
  d-general LI argument
  (`trivialMotionFamily_linearIndependent`, commit 8) uses an
  intermediate `set S := ∑ s, c_R s • elemSkewMap s.1 (cast s.2)` as
  a linear endomorphism of `EuclideanSpace ℝ (Fin d)`. The vanishing
  combination at vertex `v` then reads `t + S(p v) = 0`; subtracting
  at two vertices kills `t` and shows `S(p v - p w) = 0`. Affine
  spanning + `vectorSpan_def` + `LinearMap.eqOn_span` extends this to
  `S = 0` everywhere. Rotation coefficient extraction is via
  `(S (PiLp.single 2 j' 1)).ofLp i = c_R ⟨i, j⟩`, where the
  ordered-pair index range (`j.val < i.val`) forces the off-diagonal
  cross-terms to vanish. The alternative pure-coordinate route
  (no named linear map, just `congrFun hc v ; congrFun ... m` and
  matrix-style bookkeeping) was rejected as too fiddly: the
  abstraction `S` is doing real work because the affine-spanning step
  is naturally stated about a linear map vanishing on a spanning set.
  The dim-2 lemma (commit 7's `_three_le_finrank_of_affinelySpanning_two`)
  was redone as a one-line `:= trivialMotions_finrank_ge_of_affinelySpanning hp`
  corollary; its ~100 LoC of direct-coord argument is now subsumed.

### Promoted to TACTICS / FRICTION / DESIGN

*(none yet — the trivial-motions specifics stay phase-local; the FRICTION
entries opened in commit 7 are the cross-cutting record.)*

### Cleanup pass summaries

*(none yet)*

## Blockers / open questions

- ~~**`TrivialMotions` Phase 4 deferred API.**~~ Resolved in commit 7
  via path (2): the `TrivialMotions` API landed d-general in its own
  file `CombinatorialRigidity/TrivialMotions.lean` with the
  dim-2 specialisation
  `trivialMotions_three_le_ker_of_affinelySpanning_two`. See the
  *Done* list under *Hand-off* and the blueprint chapter
  `chapter/trivial-motions.tex`.

- ~~**D-general finrank lower bound (deferred).**~~ Resolved in
  commit 8. `trivialMotions_finrank_ge_of_affinelySpanning` ships
  `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` for an
  arbitrary affinely-spanning placement in any dimension. Built on
  `elemSkewMap (i j : Fin d)` and `trivialMotionFamily` indexed by
  `Fin d ⊕ Σ i : Fin d, Fin i.val`; the LI proof routes through a
  skew sum `S : Eucl d →ₗ[ℝ] Eucl d`, kills it on differences
  `p v - p w`, extends to `S = 0` via `LinearMap.eqOn_span` against
  `vectorSpan ℝ (Set.range p) = ⊤`, then extracts each rotation
  coefficient as `(S e_{j'}).ofLp i`. Cardinality reshuffled to
  `∑_{i ∈ range (d + 1)} i = d (d + 1) / 2`. The dim-2 lemma
  `trivialMotions_three_le_finrank_of_affinelySpanning_two` is now a
  one-line corollary at `d = 2`.

- **Generic-placement affine-spanning lemma.** Phase 4 ships
  `IsInfinitesimallyRigid.eventually` (openness of IR). We may need
  a companion "the IR placements that *also* affinely span on every
  size-$\ge$-3 subset form a dense / nonempty set." Subtlety: an IR
  placement might collapse a subset to a line. Probably true
  generically (the bad set is a finite union of hyperplanes, hence
  meagre); the proof goes through `IsOpen` intersected with the open
  "affinely spanning" set. Mitigation: if the witness placement
  produced by the rank-lower-bound lemma is *customisable* (return
  one that's also affinely-spanning-on-all-subsets), the
  sparsity-side lemma can use that same placement.

- ~~**Linear-algebra basis-pick.**~~ Resolved in commit 6 via the
  matroid-agnostic path: `exists_linearIndepOn_extension` plus
  `LinearMap.finrank_range_dualMap_eq_finrank_range` plus the
  standard-basis-of-dual identification via `Pi.basisFun.dualBasis`.
  See `exists_edgeSetRowIndependent_basis_dim_two` in
  `RigidityMatroid.lean` and the *Done* list under *Hand-off*.

## Hand-off / next phase

**Done:**
- *Commit 0 (`fdbcbd9`):* Phase 6 notes seeded; ROADMAP Status row
  flipped; forward-mode workflow surfaced in top-level `CLAUDE.md`.
- *Commit 1 (`39b2152`):* forward-mode blueprint skeleton for the
  $\Rightarrow$ direction — six red nodes in `chapter/laman-theorem.tex`
  with `\uses{...}` chains.
- *Commit 2 (`cd0398f`):* bibliography + attribution chain
  (Laman 1970 / Asimow–Roth 1978 / Jordán 2016 §1.3.1; Lovász–Yemini
  1982 acknowledged for the matroid framing).
- *Commit 3 (`93908d8`):* `RigidityMatroid.lean` +
  `rigidityMap_finrank_range_ge_of_isGenericallyRigid_two`
  (one-liner via rank-nullity + `Framework.finrank` + `omega`).
- *Commit 4 (`e3918d1`):* `EdgeSetRowIndependent G p I` plus
  `.mono` / `_empty` helpers.
- *Commit 5 (`5f11c6b`):* `apnelson1/Matroid` investigation (notes-only)
  → branch (c), matroid-agnostic. See *Decisions*.
- *Commit 6 (`7a687fa`):* basis-pick
  `exists_edgeSetRowIndependent_basis_dim_two` plus
  `rigidityRow` / `span_range_rigidityRow` /
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow` and the
  private `dualToFunₗ` bridge (FRICTION entry filed).
- *Commit 7 (`49c693a`):* `TrivialMotions.lean` — d-general
  `translationMotion`, `infinitesimalRotation`, `trivialMotions`,
  `trivialMotions_le_ker`; dim-2 `rotJTwo` (direct `LinearMap.mk'`,
  not `Matrix.toEuclideanLin`), `inner_rotJTwo_self`,
  `trivialMotions_three_le_finrank_of_affinelySpanning_two`, and
  `trivialMotions_three_le_ker_of_affinelySpanning_two`. New
  blueprint chapter `chapter/trivial-motions.tex` mirrors the
  file 1:1. Three FRICTION entries.
- *Commit 8 (this commit):* d-general finrank lower bound. Added
  `elemSkewMap (i j : Fin d) : Eucl d →ₗ[ℝ] Eucl d` and
  `inner_elemSkewMap_self`. Built the d-general `trivialMotionFamily`
  indexed by `Fin d ⊕ Σ i : Fin d, Fin i.val`, proved
  `_mem_trivialMotions` and joint LI
  `trivialMotionFamily_linearIndependent` (skew-sum + affine-spanning
  route; see *Decisions*). Cardinality
  `fintype_card_trivialMotionFamilyIndex = d(d+1)/2` via
  `Finset.sum_range_succ` + `Finset.sum_range_id`. Main lemma
  `trivialMotions_finrank_ge_of_affinelySpanning` lifts via
  `LinearIndependent.fintype_card_le_finrank`. Dim-2 lemma
  `trivialMotions_three_le_finrank_of_affinelySpanning_two` reduced
  to a one-line corollary (~100 LoC of direct-coord argument
  retired). Six new green blueprint nodes in
  `chapter/trivial-motions.tex`. No new FRICTION entries.

**Encoding choice rationale (`I : Set G.edgeSet`).** The index type
sits inside `G.edgeSet`, matching the blueprint's "$I \subseteq E(G)$".
Downstream, the spanning-subgraph construction needs `Set (Sym2 V)`
not `Set G.edgeSet`, so the assembly proof will transport via
`Subtype.val '' I`. We pay that adapter cost once at assembly rather
than carry it through the basis lemma + sparsity lemma + every
intermediate API.

**Next session — rank upper bound, then the remaining leaf.** The
architectural asymmetry of commit 7 (definitions d-general, finrank
lemma dim-2-specific) is resolved in commit 8. The remaining work
is mechanical except for one lemma.

The natural next step on the critical path is
`lem:rigidityMap-finrank-range-le-of-affinelySpanning-two`, the rank
$\le 2|V| - 3$ bound at an affinely-spanning placement. It now reduces
to rank-nullity plus the dim-2 kernel bound from commit 7: ~5 lines
of `omega` on top of `Framework.finrank` and
`trivialMotions_three_le_ker_of_affinelySpanning_two`. No new ideas
required.

The remaining genuine leaf is
`lem:exists-affinelySpanning-rigid-placement-two` — the
affinely-spanning-on-all-subsets refinement of
`IsInfinitesimallyRigid.eventually`. Likely closes via `IsOpen`
intersection plus density of the affinely-spanning set (the
*Generic-placement affine-spanning lemma* blocker has the details).
That one is the mathematically substantial step that remains, and is
a prereq for `lem:isSparse-of-rowIndependent-two` (the
sparsity-from-row-independence lemma carrying the actual $(2, 3)$
combinatorics).

Suggested order: rank-upper-bound (one short commit, almost mechanical
now), then the affinely-spanning-placement existence, then the
sparsity-side lemma, then the assembly theorem.

**Phase 6 completion remains uncertain in scope** as of commit 8. Most
remaining work is mechanical, except the affinely-spanning placement
existence lemma, whose tactic-shape is plausible but not pre-validated.
Plan to assess scope after that lemma's first attempt lands; do not
commit to a one-session full Phase 6 close.
