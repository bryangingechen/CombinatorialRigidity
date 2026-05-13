# blueprint/DESIGN.md — workflow and selectivity notes

This file holds the cross-cutting **rationale** for how the blueprint
integrates with the rest of the project: when to write the blueprint
relative to the Lean (backfill vs forward), what to include vs. skip,
and open questions about the workflow.

It is the blueprint's analogue of the top-level `DESIGN.md` — notes
and discussion rather than operational rules. Operational rules
(authoring conventions, static checks, local build) live in
`blueprint/CLAUDE.md`.

This is also a "living" file. Decisions made here can — and should —
be revisited as we get more experience with forward-mode authoring
in Phase 6 and beyond.

## What the blueprint is for

The blueprint serves two audiences and produces three artefacts:

- **Mathematician readers** browsing the project for the first time
  see the *web rendering* (`bryangingechen.github.io/.../blueprint/`):
  a hyperlinked LaTeX document explaining the formalization's content
  in mathematical English, with `\lean{...}` pointers down to the API
  docs for each formalized lemma.
- **The maintainer / contributors** see the *dep-graph view*
  (`dep_graph_document.html`): a visual map of which lemmas depend on
  which, color-coded by formalization status.
- **A PDF rendering** for offline reading and citation.

The blueprint is not a 1:1 mirror of the Lean. It records the
**mathematical structure** the formalization is built around, not
every engineering detail.

## Two workflow modes

The blueprint can be written either after the Lean lands (backfill)
or before it (forward). Both produce the same final artefact; the
difference is when the writing happens and what role the blueprint
plays during Lean work.

### Backfill mode (used for Phases 1–5)

Lean is the source of truth. The blueprint chapter is written from
the Lean as raw material, after the phase is complete. Every entry
has `\leanok` from the start; the dep-graph for the new chapter is
all-green when committed.

When to use:
- A phase has already landed and there is no blueprint chapter for it.
- A phase's Lean is small or structurally simple enough that an
  upfront dep-graph adds no planning value.

Concrete recipe lives in `blueprint/CLAUDE.md` (and the Phase 1
chapter `chapter/sparsity.tex` is the canonical example).

### Forward mode (proposed for Phase 6)

The blueprint chapter is written as a *plan* before the Lean exists:
target definitions and theorems, intermediate lemma statements, and
`\uses{...}` chains based on the mathematical dependency graph. Each
entry starts **without** `\leanok`. As Lean lemmas land, the agent
adds `\lean{...}` and flips `\leanok` on. The dep-graph then doubles
as a live progress tracker — non-green nodes are the actual
remaining work.

When to use:
- A phase has not yet started and its proof structure is non-trivial
  enough that a visual dependency plan beats a flat ROADMAP list.
- A phase will span multiple sessions, so a shared visual plan
  amortizes the upfront cost across sessions.
- The mathematical reference (e.g. Graver–Servatius–Servatius for
  Phase 6) is solid enough to write a credible plan from.

## Three options for forward mode

Within "forward mode" there are three concrete recipes, differing in
how much you write upfront:

| | Upfront cost | Mid-phase churn | End-of-phase cost |
|---|---|---|---|
| **A. Full forward** — chapter + prose proofs + `\lean{}` pins, all before any Lean | High | High (every Lean rename / split / merged lemma is a 2-file edit) | Low |
| **C. Hybrid skeleton** — chapter structure only: definitions, target theorems, intermediate lemma names, `\uses{}` chains. No `\lean{}`, no `\leanok`, no prose proofs | Medium | Low (mostly one-line additions as Lean lands) | Medium (prose proofs written at end, against stable Lean) |
| **B. Pure backfill** — chapter written end-to-end after the Lean is done | Zero | Zero | High |

(Letters are inherited from earlier discussion; A/B/C is not an
ordering.)

The **highest-churn pieces of the blueprint** are the `\lean{...}`
pins and the prose proofs. Lean names change as the API stabilizes;
prose proofs are most efficient to write once, against the final
shape of the Lean argument. Option A pays both costs twice; Option C
defers both to when the Lean is stable. The **dep-graph** is the
most valuable forward-mode artefact independently of those, and you
get it with just definitions + statements + `\uses{...}`.

**Selectivity (see below) further reduces Option C's churn**, because
the lemmas most prone to renaming are exactly the small API helpers
we would not blueprint in the first place. The Phase 1 chapter is a
calibration data point: of the 31 declarations in `EdgesIn.lean` +
`Sparsity.lean`, 22 made it into the blueprint after applying the
carleson-style selectivity criteria. The 9 excluded entries split
cleanly along the bar in `blueprint/CLAUDE.md`: a tautology
(`edgesIn_subset_edgeSet`), two pure accessors (`IsTight.isSparse`,
`IsTight.edgeSet_ncard`), a boilerplate constructor
(`mk_mem_edgesIn`), a trivial one-line corollary
(`IsSparse.deleteEdges`), a definitional membership unfolding
(`mem_edgesIn`), a finiteness fact (`edgesIn_finite`), and two
base-case characterizations (`bot_isSparse`, `bot_isTight_iff`).
The case for selectivity is **strongest in forward mode**: when you
haven't yet written the small bridge helpers, the question of
whether to blueprint them doesn't arise. Phase 6 should plan to
blueprint ~10–20 mathematical landmarks (definitions, key
intermediate lemmas, the final theorem) and let the supporting Lean
infrastructure stay out of the doc.

### Recommendation for Phase 6: Option C (hybrid skeleton)

- Phase 6's mathematical structure (planar rigidity matroid, generic
  dimension, rank function for the (⇒) direction) is complex enough
  that an upfront dep-graph beats a flat ROADMAP list as a planning
  artefact.
- Phase 6 will likely span multiple sessions; a shared visual plan
  across sessions amortizes the upfront cost.
- Deferring `\lean{...}` and prose proofs to the moment of landing
  means each piece is written once, against stable artefacts.
- The human (project owner) can audit the skeleton dep-graph at
  phase start — higher signal than auditing prose ROADMAP bullets.

Proposed workflow if Phase 6 adopts C:

1. **Phase 6 kickoff.** Agent drafts `chapter/laman-theorem-mp.tex`
   (or similar) covering only the (⇒) direction. Draft carries:
   target theorem statement, intermediate definitions/lemmas,
   `\uses{...}` populated from the math, **no** `\lean{...}`,
   **no** `\leanok`, **no** prose proofs (or one-line gestures
   only). Commit, render dep-graph, human reviews.
2. **Each Lean session.** Agent picks a leaf-most red node in the
   dep-graph (a lemma whose `\uses{...}` chain bottoms out in green
   nodes or in axioms / mathlib facts), formalizes it in Lean, then
   adds `\lean{Namespace.name}` and `\leanok` to the blueprint
   entry. The dep-graph node turns green. One-line edit.
3. **Phase end pass.** Single focused pass to write 1- to 3-sentence
   prose proofs per blueprint entry, against the now-stable Lean.

## Selectivity: what goes in the blueprint

The blueprint is a reader's doc, not a 1:1 mirror of the Lean. The
default presumption is **exclude**; an entry must earn its slot by
clearing one of these bars:

- Defines a project-level concept (`IsSparse`, `IsLaman`, `IsTight`,
  `IsTightOn`, etc.).
- States a theorem a reader would name out loud ("Laman's theorem",
  "tight-subset union closure", "supermodularity of edge counts").
- States a lemma with non-trivial mathematical content used at a
  phase boundary or feeding a main theorem.

Categories that are typically **excluded**:

- **Tautologies.** `edgesIn_subset_edgeSet` is `A ∩ B ⊆ A`. Zero
  reader benefit.
- **Constructors and accessors.** `mk_mem_edgesIn`,
  `IsLaman.isSparse`, `IsLaman.edgeSet_ncard`, etc. Their content is
  visible in the type signature and they only exist to absorb
  `Sym2`-membership or And-projection boilerplate at use sites.
- **Mirror lemmas under `CombinatorialRigidity/Mathlib/`.** These
  are upstream-eligible facts about `Sym2`, `Set.ncard`, `Finset`,
  etc. They are not project results; they belong upstream
  (and are tracked separately by the upstreaming dashboard).
- **Small bridge / glue lemmas.** Anything whose name or statement
  is likely to change as the API stabilizes. These are the
  **highest-churn** artefacts in the codebase, and including them in
  the blueprint creates two-file edits on every refactor.

### Why selectivity matters beyond reader experience

Selectivity is not just about readability — it also makes forward-
mode authoring much cheaper. The lemmas most prone to renaming /
restating during Lean work are exactly the bridge helpers we would
already exclude. So in principle, **a hybrid-skeleton forward chapter
should churn very little** during Lean work: the included entries
are the mathematical landmarks, which are stable by design.

The Phase 1 chapter is a *partial* test of this claim. When the
blueprint was written (after Phase 5 had already added auxiliary
lemmas like `edgesIn_inter`, `edgesIn_ncard_add_le`,
`IsSparse.iso`, `IsTightOn.union_inter`, etc. to the Phase 1 files),
many of those Phase-5-prep additions cleared the inclusion bar and
got blueprinted — they were mathematically significant
(supermodularity, iso preservation, tight-set lattice closure). So
the blueprint was *not* invariant under the Phase 5 prep work. The
takeaway: a written blueprint chapter is robust against pure
infrastructure churn (renaming a constructor, splitting a glue
lemma), but **not** against the addition of new mathematically
significant lemmas. Forward-mode skeletons should be sized to
accommodate growth in the latter.

### Heuristic for unclear cases

If you find yourself wondering whether a lemma deserves a blueprint
entry, ask: *would a reader thinking about the proof at a whiteboard
ever name this lemma?* If yes, include it. If no, it's API
infrastructure — leave it out.

## Open questions

A decision to revisit when Phase 6 kicks off:

1. **Does `notes/Phase6.md` shrink under forward mode?** If the
   blueprint chapter is the authoritative todo list and dep-graph,
   then `notes/PhaseN.md`'s "Lemma checklist" section becomes
   redundant for that phase. Lean recommendation: shrink to just
   *Current state* / *Decisions made* / *Blockers* / *Hand-off*,
   with a pointer to the blueprint chapter as the lemma index.
   Parallel checklists rot.

## Resolved questions

These were open at the start of the Phase 1–5 backfill series; the
backfill produced enough evidence to close them.

- **How do we mark "blocked / in progress" inside the blueprint?**
  Resolved: follow carleson — absence of `\leanok` carries the signal,
  no `\notready` needed. The Phase 5 backfill stated the two Phase 6
  results (`IsGenericallyRigid.exists_isLaman_le` and the composed
  iff) with `\lean{...}` (the Lean declaration exists, body is
  `sorry`) but \emph{no} `\leanok` on either the theorem environment
  or the proof. The dep-graph correctly colors them red; the
  encoding is a clean fit for "stated in Lean, proof not yet
  formalized." Revisit only if Phase 6 wants to distinguish "not
  attempted" from "attempted, blocked on a specific subgoal" —
  `\notready` is then an option, but the case has not arisen yet.
- **Should `chapter/intro.tex` reference the dep-graph?** Resolved:
  yes. With Phase 6's red nodes now visible after the Phase 5
  backfill landed, the intro points readers at
  `dep_graph_document.html` as the in-progress / not-yet-formalized
  view. Update applied alongside this close-out.
- **At what point does a backfilled chapter get re-touched?**
  Resolved by experience: Phase 5's backfill commit interleaved 7
  new entries into the existing `frameworks.tex` and 4 new entries
  into the existing `henneberg.tex`, ordered topically (by
  subsection) rather than appended at end. The reader does not care
  about phase origin; the chapter reads as a coherent document.
  Convention: chapter additions live in the same commit as the
  phase that introduces them, interleaved into the existing
  topical structure of the chapter. Documented in `CLAUDE.md`
  under *Adding a new chapter*.
- **One chapter file or two for Phases 5/6?** Resolved: one file.
  `chapter/laman-theorem.tex` was created during the Phase 5
  backfill and carries both the Phase 5 `⇐` direction (fully
  formalized) and the Phase 6 `⇒` direction (stated as a
  sorry-blocked theorem, rendered red in the dep-graph). The
  biconditional structure stays together; the workflow-state
  difference is signalled by the per-entry `\leanok` (or its
  absence) rather than by file boundaries. The alternative
  one-file-per-direction split is not adopted; revisit only if
  Phase 6 turns out to need substantial restructuring of the
  combined chapter.

## Project-history note

Phases 1–5 of the Lean were complete before the blueprint scaffold
was added (May 2026). The Phase 1 chapter (`chapter/sparsity.tex`)
was authored first as the canonical backfill-mode example; the
Phase 2–5 chapters were backfilled in a series of one-commit-per-phase
sessions later that month. Phase 5's backfill was the largest:
it touched four chapter files (extending `frameworks.tex` and
`henneberg.tex` with new entries, and creating
`henneberg-rigidity.tex` and `laman-theorem.tex` from scratch),
landing 20 new entries plus two Phase 6 sorry-blocked statements.

After the Phase 1–5 backfill series, the blueprint is in sync
with the Lean: every Lean declaration that meets the selectivity
bar in `blueprint/CLAUDE.md` has a corresponding green entry, and
the two intentionally-red entries are exactly the Phase 6
deliverable. Phase 6 is the natural place to try forward mode;
the recommendation under *Recommendation for Phase 6* is based on
the backfill experience and the Phase 6 plan in `notes/Phase5.md`'s
hand-off section, and should be revised after the first Phase 6
forward-mode session lands.
