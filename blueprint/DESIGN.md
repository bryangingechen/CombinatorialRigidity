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
be revisited as we get more experience with forward-mode authoring.
Phase 6 was the first forward-mode phase; the outcomes are folded
back into *Resolved questions* below.

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

### Forward mode (used for Phase 6)

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
whether to blueprint them doesn't arise. Phase 6 (the project's
first forward-mode phase) blueprinted ~20 mathematical landmarks
(definitions, the row-independence relation, the rank lemmas, the
two named facts, the assembly theorem, and the Laman's-theorem
biconditional) and left the supporting infrastructure — coordinate
unfoldings, small bridge helpers, mirror lemmas — out of the doc.

### Hybrid skeleton (Option C) — the forward-mode default

Phase 6 adopted Option C and the recipe below worked end-to-end with
no mid-phase restructuring. The pattern is now the project's default
for any forward-mode phase.

- The phase's mathematical structure (planar rigidity matroid, generic
  dimension, rank function for the (⇒) direction) was complex enough
  that an upfront dep-graph beat a flat ROADMAP list as a planning
  artefact.
- The phase spanned multiple sessions; the shared visual plan
  amortized the upfront cost.
- Deferring `\lean{...}` and prose proofs to the moment of landing
  meant each piece was written once, against stable artefacts.
- The human (project owner) could audit the skeleton dep-graph at
  phase start — higher signal than auditing prose ROADMAP bullets.

Workflow:

1. **Phase kickoff.** Agent drafts the chapter (Phase 6 extended the
   existing `chapter/laman-theorem.tex` rather than creating a new
   file) covering the phase's target direction. Draft carries:
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

(None currently open. Forward-mode questions resolved after Phase 6;
see *Resolved questions* below.)

## Resolved questions

These were open at the start of the Phase 1–5 backfill series; the
backfill produced enough evidence to close them.

- **How do we mark "blocked / in progress" inside the blueprint?**
  Resolved: follow carleson — absence of `\leanok` carries the signal,
  no `\notready` needed. The Phase 5 backfill stated the two Phase 6
  results (`IsGenericallyRigid.exists_isLaman_le` and the composed
  iff) with `\lean{...}` (the Lean declaration exists, body is
  `sorry`) but \emph{no} `\leanok` on either the theorem environment
  or the proof. The dep-graph correctly colored them red; the
  encoding is a clean fit for "stated in Lean, proof not yet
  formalized." Phase 6's forward-mode session used the same encoding
  for every newly-stated intermediate lemma; the case for a
  `\notready` macro distinguishing "not attempted" from "attempted,
  blocked on a specific subgoal" did not arise.
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
  backfill and carries both the Phase 5 `⇐` direction (formalized
  first) and the Phase 6 `⇒` direction (stated first as
  sorry-blocked, then filled in across the Phase 6 sessions). The
  biconditional structure stays together; the workflow-state
  difference is signalled by the per-entry `\leanok` (or its
  absence) rather than by file boundaries. Phase 6 did *not* need
  to restructure the combined chapter; the one-file convention
  held end-to-end.
- **Does `notes/Phase6.md` shrink under forward mode?** Resolved:
  yes. `notes/Phase6.md` omits the per-lemma checklist (a pointer
  to the blueprint chapter's $\Rightarrow$-direction subsection
  takes its place) and carries only *Current state*, *Decisions
  made*, *Blockers*, and *Hand-off*. The blueprint dep-graph was
  the authoritative todo list throughout the phase; the parallel
  checklist would have rotted. Convention now documented in the
  top-level `CLAUDE.md` *Forward-mode blueprint phases*.

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

Phase 6 ran in forward mode (Option C, hybrid skeleton) per the
recipe above: the blueprint chapter
`chapter/laman-theorem.tex`'s $\Rightarrow$-direction subsection was
extended with the dep-graph skeleton at phase start, and lemmas
acquired `\lean{...}` + `\leanok` as they landed across the phase's
sessions. The new chapter `chapter/trivial-motions.tex` (developing
the $d$-general trivial-motions API) was created mid-phase when the
material outgrew its inlined slot in `frameworks.tex`. Phase 6
closed with every blueprint node green; the blueprint and the Lean
are in sync.
