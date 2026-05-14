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

**Attribution research done** (this session, not yet reflected in
the chapter): the proof strategy is the necessary direction of
Laman's theorem in its rigidity-matrix formulation. Attributions
verified against Jordán 2016 §1.3.1 + §2.2 (local PDF, see
`../CLAUDE.md` *Reading PDFs in `.refs/`*):
- **Asimow–Roth 1978** (Trans. AMS **245**, 279–289) is the
  standard ref for the linear-algebra framework — to be added to
  `bibliography.bib` and cited on `def:rigidityMap`,
  `def:isInfinitesimallyRigid`, and the trivial-motions lemma.
- **Laman 1970** is the primary attribution for the existence of
  the Laman spanning subgraph (necessary direction of his theorem).
- The current "Following Lovász–Yemini" framing in the section
  preamble overstates LY's role: LY's contribution is the harder
  converse direction, which we do *not* prove. The prose will be
  revised to call out Laman + Asimow–Roth + an acknowledgement of
  LY for the matroid framing.
- Maxwell 1864 is the historical primary for the counting argument
  but Jordán treats it as classical; we follow Jordán and skip it
  unless the user wants historical depth.

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

The first Phase 6 code commit lays out the dep-graph structure; until
then, the only red node is `thm:isGenericallyRigid-exists-isLaman-le`
(the Phase 6 target) and its proof sketch references no intermediate
forward-mode entries yet.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(none yet — populated as lemmas land)*

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

- **Linear-algebra basis-pick.** Standard `LinearIndependent.extend`
  or `Basis.extend` should let us pick $2|V| - 3$ LI rows out of the
  rigidity matrix's edge-indexed row family. No-op until the rank
  lower bound lands.

## Hand-off / next phase

**Done:**
- *Commit 0 (`fdbcbd9`):* Phase 6 notes seeded; ROADMAP Status row
  flipped; forward-mode workflow surfaced in top-level `CLAUDE.md`.
- *Commit 1 (`39b2152`):* forward-mode blueprint skeleton for the
  $\Rightarrow$ direction. Six new red nodes in
  `chapter/laman-theorem.tex` with `\uses{...}` chains; no
  `\lean{...}` or `\leanok` yet. Renders cleanly under
  `inv bp && inv web`; static checks pass.

**Next concrete commit candidates** (either order; both are
docs-only and human-reviewable):

- **Bibliography + prose refinement.** Add `asimowRoth1978` to
  `bibliography.bib`; cite it on `def:rigidityMap`,
  `def:isInfinitesimallyRigid`, and
  `lem:trivialMotions-three-le-ker-of-affinelySpanning-two`. Rewrite
  the $\Rightarrow$-section preamble in `chapter/laman-theorem.tex`
  to attribute the necessary direction to Laman 1970 + Asimow–Roth
  1978 rather than the current overstated "Following Lovász–Yemini"
  framing. Verification path: Jordán 2016 §1.3.1 + bib (already
  cross-checked this session — see *Current state*).
- **First leaf Lean lemma.** Pick the leaf-most red node and
  formalize. Candidates by likely cost:
  - `lem:rigidityMap-finrank-range-ge-of-isGenericallyRigid-two` —
    one-liner from `IsInfinitesimallyRigid` + rank-nullity. Lives
    in `RigidityMatroid.lean` (new file).
  - `def:edgeSet-rowIndependent` — definition only, no proof
    obligation. Probably bundled with the rank-ge lemma.

**Phase 6 completion is uncertain in scope.** Honest read: the rank
lower bound and the basis-pick are linear-algebra plumbing and
likely close in one session each. The $(2,3)$-sparsity-from-
row-independence lemma contains the only genuinely new mathematical
content and depends on a to-be-chosen path through the *Blockers*
list — that's where most risk lives. Plan to assess scope after the
sparsity-side lemma's first sub-node lands; do not commit to a
one-session full Phase 6 close.
