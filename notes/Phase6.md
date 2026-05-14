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

**Forward-mode skeleton landed** (commit `39b2152`): the
$\Rightarrow$ subsection of `chapter/laman-theorem.tex` now carries
six new red nodes laying out the intended proof — `def:edgeSet-rowIndependent`,
`lem:rigidityMap-finrank-range-ge-of-isGenericallyRigid-two`,
`lem:exists-rowIndependent-edge-basis`,
`lem:trivialMotions-three-le-ker-of-affinelySpanning-two`,
`lem:rigidityMap-finrank-range-le-of-affinelySpanning-two`,
`lem:exists-affinelySpanning-rigid-placement-two`,
`lem:isSparse-of-rowIndependent-two` — plus the rewritten proof
sketch of the target theorem referencing them. The dep-graph at
`blueprint/web/dep_graph_document.html` is the authoritative view.

**Three leaves landed:** `CombinatorialRigidity/RigidityMatroid.lean`
exists, imported from `LamanTheorem.lean`, carrying (i) the rank
lower bound `SimpleGraph.rigidityMap_finrank_range_ge_of_isGenericallyRigid_two`,
(ii) the row-independence predicate `SimpleGraph.EdgeSetRowIndependent`
(`LinearIndepOn` of the edge-row family on `I : Set G.edgeSet`) with
`.mono` and `_empty` helpers, and (iii) the basis-pick lemma
`SimpleGraph.exists_edgeSetRowIndependent_basis_dim_two` extracting an
edge set of size `2 * #V - 3` that is row-independent at some
generically rigid placement, via `exists_linearIndepOn_extension` +
`finrank_range_dualMap_eq_finrank_range`. The supporting infrastructure
(`rigidityRow`, `span_range_rigidityRow`,
`edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`) lives in the
same file. Blueprint entries `lem:rigidityMap-finrank-range-ge-of-isGenericallyRigid-two`,
`def:edgeSet-rowIndependent`, and `lem:exists-rowIndependent-edge-basis`
all carry `\lean{...}` + `\leanok`.

**Linear-matroid investigation closed.** We stay matroid-agnostic;
see *Decisions made* for the rationale and *Hand-off / next phase*
for the linear-algebra-only plan for `lem:exists-rowIndependent-edge-basis`.

**Attribution research and prose refinement landed.** Jordán 2016
§1.3.1 + §2.2 cross-checked the citation chain (local PDF, see
`../CLAUDE.md` *Reading PDFs in `.refs/`*):
- **Asimow–Roth 1978** (Trans. AMS **245**, 279–289) added to
  `bibliography.bib`; cited at the `frameworks.tex` section preamble
  (covers `def:rigidityMap`, `def:isInfinitesimallyRigid`, and the
  trivial-motions identification all at once) and again in the
  trivial-motions lemma preamble.
- The $\Rightarrow$ section preamble of `chapter/laman-theorem.tex`
  now attributes the necessary direction to Laman 1970 in its
  Asimow–Roth 1978 linear-algebraic formulation; Lov\'asz--Yemini
  1982 is acknowledged as the matroid framing (the easy direction
  of their identity is what facts (a) and (b) together prove).
  Jord\'an 2016 Lemma 1.3.1 is cited as the modern presentation we
  follow for the sparsity-from-row-independence step.
- Maxwell 1864 is the historical primary for the counting argument;
  Jord\'an treats it as classical without citing it. We follow
  Jord\'an and skip Maxwell unless the user wants historical depth.

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

Status snapshot at commit-7 (TrivialMotions API): the dim-2
$\dim\,\ker \ge 3$ lemma at affinely-spanning placements has landed in
a new chapter `chapter/trivial-motions.tex` covering the d-general
trivial-motions API (translations, infinitesimal rotations, the
`trivialMotions` submodule, `_le_ker`) plus the dim-2 specialisation
(`rotJTwo`, $\ge 3$ lower bound, kernel corollary). The dep-graph now
shows nine green nodes: the three from commit 6 plus the six new ones
(`def:translationMotion`, `def:infinitesimalRotation`,
`def:trivialMotions`, `def:rotJTwo`, all `_mem_ker` lemmas,
`lem:trivialMotions-le-ker`, `lem:inner-rotJTwo-self`,
`lem:trivialMotions-three-le-finrank-of-affinelySpanning-two`, and
`lem:trivialMotions-three-le-ker-of-affinelySpanning-two`). The
remaining red nodes —
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

- **D-general finrank lower bound (deferred).** Commit 7 ships only
  the dim-2 finrank lemma
  `trivialMotions_three_le_finrank_of_affinelySpanning_two`. The
  natural d-general statement is
  `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` at any
  affinely-spanning placement; our dim-2 lemma is the `d = 2` instance.
  The d-general proof needs:
  1. An explicit elementary skew-adjoint map
     `elemSkewMap (i j : Fin d) : EuclideanSpace ℝ (Fin d) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin d)` with `x ↦ x[j] • e_i - x[i] • e_j`
     (so it satisfies `⟪x, elemSkewMap i j x⟫_ℝ = 0`).
  2. A joint LI argument for the family
     `Fin d ⊕ Σ i : Fin d, Fin i → Framework V d`
     (translations indexed by `Fin d`, rotations indexed by the
     lower-triangle pairs) under affine spanning. The key step:
     suppose the linear combination vanishes; build the matrix `M` of
     rotation coefficients and the translation vector `T`; then for
     all `v, w : V`, `M(p_v - p_w) = 0`, so `M = 0` by affine
     spanning, hence rotation coefficients vanish; then `T = 0` from
     any single `v`.
  3. Cardinality computation
     `Fintype.card (Fin d ⊕ Σ i : Fin d, Fin i) = d * (d + 1) / 2`
     via `Fintype.card_sum`, `Fintype.card_sigma`,
     `Fin.sum_univ_eq_sum_range`, and `Finset.sum_range_id`.
  4. Final `LinearIndependent.fintype_card_le_finrank` gives the
     bound; the existing dim-2 lemma becomes
     `simpa using trivialMotions_finrank_ge_of_affinelySpanning hp`.

  Scope estimate ~150–200 LoC. Not on the critical path for closing
  Laman (⇒): the dim-2 case suffices for the rank upper bound that
  feeds the $(2, 3)$-sparsity argument. Treat as an architectural
  cleanup separable from the remaining Phase 6 leaves.

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
  $\Rightarrow$ direction. Six new red nodes in
  `chapter/laman-theorem.tex` with `\uses{...}` chains; no
  `\lean{...}` or `\leanok` yet.
- *Commit 2 (`cd0398f`):* bibliography + prose refinement.
  `asimowRoth1978` added to `bibliography.bib` and cited in
  `frameworks.tex` (section preamble) and `laman-theorem.tex` (both
  the $\Rightarrow$ section preamble and the trivial-motions lemma
  preamble). The $\Rightarrow$ section preamble retitled the
  attribution chain: Laman 1970 (the result we prove), Asimow--Roth
  1978 (the linear-algebraic formulation), Jord\'an 2016 Lemma
  1.3.1 (the sparsity step), and Lov\'asz--Yemini 1982 acknowledged
  for the matroid framing of which our (a)+(b) is the easy
  direction. Renders cleanly; [AR78] resolves in both web and print.
- *Commit 3 (`93908d8`):* first leaf Lean lemma —
  `CombinatorialRigidity/RigidityMatroid.lean` with
  `SimpleGraph.rigidityMap_finrank_range_ge_of_isGenericallyRigid_two`.
  One-liner from `IsInfinitesimallyRigid` + rank-nullity + the
  `Framework.finrank` fact already proved in `Framework.lean`; closes
  via `omega`. Wired through `LamanTheorem.lean`'s import list.
  Blueprint entry `lem:rigidityMap-finrank-range-ge-of-isGenericallyRigid-two`
  flipped green (`\lean{...}` + `\leanok` on statement and proof).
- *Commit 4 (`e3918d1`):* row-independence definition. Added
  `SimpleGraph.EdgeSetRowIndependent G p I` as `LinearIndepOn ℝ
  (fun e : G.edgeSet => fun motion : Framework V d => G.RigidityMap p
  motion e) I`, indexed by `I : Set G.edgeSet`. `EdgeSetRowIndependent.mono`
  + `edgeSetRowIndependent_empty` round out the trivial helpers.
  Blueprint entry `def:edgeSet-rowIndependent` flipped green.
- *Commit 5 (`5f11c6b`):* `apnelson1/Matroid` investigation
  (notes-only). Confirmed the repo ships `Module.matroid` /
  `Matroid.ofFun` (`Matroid/Representation/Map.lean` lines 132 and
  188), toolchain pin matches, and the underlying
  `IndepMatroid.ofFinitaryCardAugment` is already in mathlib
  (`Mathlib/Combinatorics/Matroid/IndepAxioms.lean:215`). Decision:
  branch (c) — stay matroid-agnostic.
- *Commit 6 (`7a687fa`):* basis-pick lemma —
  `SimpleGraph.exists_edgeSetRowIndependent_basis_dim_two` plus its
  supporting infrastructure (`rigidityRow`, `span_range_rigidityRow`,
  `edgeSetRowIndependent_iff_linearIndepOn_rigidityRow`, private
  `dualToFunₗ`). Implements the 5-step plan via mathlib only:
  `exists_linearIndepOn_extension` → dual-bridge to the row family →
  `LinearMap.finrank_range_dualMap_eq_finrank_range` →
  `linearIndependent_iff_card_eq_finrank_span` (`Set.finrank` form)
  → `Set.exists_subset_card_eq` truncation. Blueprint entry
  `lem:exists-rowIndependent-edge-basis` flipped green (`\lean{...}`
  + `\leanok`, both on statement and proof) and re-rendered (graph
  spot-checked). FRICTION entry filed for the missing packaged
  `Module.Dual ℝ M →ₗ[ℝ] (M → ℝ)` injection
  (`dualToFunₗ`).
- *Commit 7 (this commit):* TrivialMotions API +
  `lem:trivialMotions-three-le-ker-of-affinelySpanning-two`. New file
  `CombinatorialRigidity/TrivialMotions.lean` (d-general API):
  `translationMotion`, `infinitesimalRotation`, `trivialMotions`,
  `trivialMotions_le_ker`. Dim-2 specialisation: `rotJTwo` (90°
  rotation, defined directly via `LinearMap.mk'`),
  `inner_rotJTwo_self`,
  `trivialMotions_three_le_finrank_of_affinelySpanning_two`
  (LI of three motions via affine-span hypothesis), and the
  one-liner corollary
  `trivialMotions_three_le_ker_of_affinelySpanning_two`.
  `RigidityMatroid.lean` now imports the new file. New blueprint
  chapter `chapter/trivial-motions.tex` mirrors the file 1:1 (9 new
  green nodes); `chapter/laman-theorem.tex` rewired to point at it.
  Three FRICTION entries filed: explicit `(k V P)` args for
  `AffineSubspace.nonempty_of_affineSpan_eq_top`, `fin_cases i`
  leaves `⟨n, ⋯⟩` blocking `rw`, and the `Matrix.toEuclideanLin`
  coordinate-simp issue. **Deferred:** the natural d-general
  finrank lower bound (the dim-2 lemma is its `d = 2` instance) is
  flagged under *Blockers* below and in the Lean / blueprint files;
  it's ~150–200 LoC of LI bookkeeping plus a cardinality
  computation and is not on the critical path for the iff.

**Encoding choice rationale (`I : Set G.edgeSet`).** The index type
sits inside `G.edgeSet`, matching the blueprint's "$I \subseteq E(G)$".
Downstream, the spanning-subgraph construction needs `Set (Sym2 V)`
not `Set G.edgeSet`, so the assembly proof will transport via
`Subtype.val '' I`. We pay that adapter cost once at assembly rather
than carry it through the basis lemma + sparsity lemma + every
intermediate API.

**Next session — rank upper bound, then the remaining leaf.** Two
independent next tasks are available; either is a reasonable starting
point.

The natural next step on the critical path is
`lem:rigidityMap-finrank-range-le-of-affinelySpanning-two`, the rank
$\le 2|V| - 3$ bound at an affinely-spanning placement. It now reduces
to rank-nullity plus the dim-2 kernel bound we just landed: ~5 lines
of `omega` on top of `Framework.finrank` and
`trivialMotions_three_le_ker_of_affinelySpanning_two`. No new ideas
required.

An architectural cleanup also waits: the d-general finrank lower
bound `d * (d + 1) / 2 ≤ finrank ℝ (trivialMotions p)` (see *Blockers*
above). Not blocking — the dim-2 case suffices for the iff — but
addresses the design asymmetry that the definitions are d-general
while the finrank bound is dim-2-specific.

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

**Phase 6 completion remains uncertain in scope** as of commit 7. Most
remaining work is mechanical, except the affinely-spanning placement
existence lemma, whose tactic-shape is plausible but not pre-validated.
Plan to assess scope after that lemma's first attempt lands; do not
commit to a one-session full Phase 6 close.
