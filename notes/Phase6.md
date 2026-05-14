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

Status snapshot at commit-6 (basis-pick): three green nodes
(`lem:rigidityMap-finrank-range-ge-of-isGenericallyRigid-two`,
`def:edgeSet-rowIndependent`, `lem:exists-rowIndependent-edge-basis`);
the remaining four nodes —
`lem:trivialMotions-three-le-ker-of-affinelySpanning-two`,
`lem:rigidityMap-finrank-range-le-of-affinelySpanning-two`,
`lem:exists-affinelySpanning-rigid-placement-two`,
`lem:isSparse-of-rowIndependent-two` — and the target
`thm:isGenericallyRigid-exists-isLaman-le` stay red. Of the red ones,
`lem:trivialMotions-three-le-ker-of-affinelySpanning-two` and
`lem:exists-affinelySpanning-rigid-placement-two` are leaves; both
hit the *Blockers* list below.

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

### Promoted to TACTICS / FRICTION / DESIGN

*(none yet)*

### Cleanup pass summaries

*(none yet)*

## Blockers / open questions

- **`TrivialMotions` Phase 4 deferred API.** The
  $(2,3)$-sparsity-from-row-independence proof needs
  $\rk\,R_{H[S]}(p|_S) \le 2|S| - 3$ for $|S| \ge 3$ via the
  affinely-spanning identification of trivial motions
  ($\dim\,\mathrm{TrivialMotions} = 3$ when the affine span is 2-dim).
  Three resolution paths in increasing scope:
  1. **Direct lemma**: prove
     $\rk\,\mathrm{range}\,R_G(p) \le 2|V| - 3$ when $p$ affinely
     spans, by exhibiting 3 LI motions in the kernel (translations + one
     rotation), without naming `TrivialMotions`. Smallest scope; mirrors
     the K$_2$ proof shape.
  2. **Resurrect Phase 4's `TrivialMotions` API.** The original
     Phase 4 plan (`notes/Phase4.md` *Lemma checklist*) had
     `trivialMotionAction`, `trivialMotions_le_ker`,
     `finrank_trivialMotions_eq_of_affinelySpanning`. Cost ~60 LoC per
     the Phase 4 estimate; ships a named abstraction.
  3. **Specialize via a concrete placement.** Use the moment-curve
     $p_v = (h\,v, (h\,v)^2)$ for an injection $h : V \to \R$; verify
     all subsets of size $\ge 3$ affinely span. Closed-form linear
     algebra.

  No commitment yet — choose when milestone-2-equivalent dep-graph
  nodes get attempted.

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
- *Commit 6 (this commit):* basis-pick lemma —
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

**Encoding choice rationale (`I : Set G.edgeSet`).** The index type
sits inside `G.edgeSet`, matching the blueprint's "$I \subseteq E(G)$".
Downstream, the spanning-subgraph construction needs `Set (Sym2 V)`
not `Set G.edgeSet`, so the assembly proof will transport via
`Subtype.val '' I`. We pay that adapter cost once at assembly rather
than carry it through the basis lemma + sparsity lemma + every
intermediate API.

**Next session — pick one of the two remaining leaves.** Both are
genuinely mathematical (vs.\ the basis-pick which was plumbing) and
sit on the *Blockers* list above:

- `lem:trivialMotions-three-le-ker-of-affinelySpanning-two` — the
  $\dim\,\mathrm{TrivialMotions} = 3$ identification under affine
  spanning. Three implementation paths in *Blockers*:
  (1) direct LI-witness of three motions (translations + rotation);
  (2) resurrect the Phase-4-deferred `TrivialMotions` API;
  (3) specialise to a concrete moment-curve placement. (1) is the
  smallest scope and probably the best first attempt; (2) buys reuse
  for a hypothetical Lovász--Yemini full equality but is over-engineered
  for what the iff needs.
- `lem:exists-affinelySpanning-rigid-placement-two` — the
  affinely-spanning-on-all-subsets refinement of
  `IsInfinitesimallyRigid.eventually`. Likely closes via
  `IsOpen` intersection plus density of the affinely-spanning set; the
  *Generic-placement affine-spanning lemma* blocker has the details.

Either can land independently of the other; they only meet at
`lem:isSparse-of-rowIndependent-two` (the substantive content of the
$\Rightarrow$ direction, two layers down). Suggested order: try (1)
of `lem:trivialMotions-...` first (fewest moving parts; the explicit
basis matches the K$_2$ proof shape already in
`top_fin_two_isGenericallyRigid`).

**Phase 6 completion is uncertain in scope.** Honest read: the rank
lower bound (done), the definition (done), and the basis-pick (done)
were linear-algebra plumbing and closed cleanly. The
$(2,3)$-sparsity-from-row-independence lemma contains the only
genuinely new mathematical content and depends on a to-be-chosen
path through the *Blockers* list (`TrivialMotions` API, generic
affine-spanning placement) — that's where most risk lives. Plan
to assess scope after the sparsity-side lemma's first sub-node
lands; do not commit to a one-session full Phase 6 close.
