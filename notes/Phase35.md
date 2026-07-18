# Phase 35 — COPLANAR: multigraph KT Conjecture 1.2 (work log)

**Status:** in progress (opened 2026-07-18, recon-first).

Planning input: `notes/Coplanar.md` (the 2026-07-18 user-proposed survey;
its content moved here at open, the file is now a thin pointer). Target:
recover the **full multigraph strength** of KT Conjecture 1.2 and
Theorem 5.6 by stating the panel side in KT's own hinge-coplanar panel
model, retiring the PROSPECT K1 wall (`notes/Prospect.md` K1). Primary
source: Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete
Comput. Geom. **45** (2011) — project-canonical; the specific pointers
used here are under *Citations* below.

## Current state

Phase just opened; nothing is built and no blueprint chapter is open.
The next concrete step is the **opening recon dispatch on R0** (stated
verbatim under *Hand-off / next phase*), with **R1–R3 riding the same
dispatch or the next**. R0 gates all builds: the candidate route below
is a session derivation, not a compiler-checked one (the
transcribed-proof-vs-carrier discipline, top-level `CLAUDE.md`) — no
Lean work before R0 returns GO on the W2 route. Everything below is
transcribed from `notes/Coplanar.md`'s survey (2026-07-18, verified
against decl bodies, not docstrings), not re-derived this commit.

## Why this is additive (survey findings, 2026-07-18)

The formalized `molecular_conjecture` is the simple-graph case because
its panel side is the meet-model `PanelHingeFramework` — parallel edges
are forced to share a hinge, and KT Lemma 5.3's coincident-panel
double-edge realization is inexpressible (blueprint
`fmlnote:molecular-conjecture-multigraph`; the multigraph iff is
**false** in that model, verified 2026-07-04). The K1 verdict ("a
different hinge encoding, i.e. a re-architecture") is **partially
stale**: the KT-faithful encoding already exists in-tree, and the hard
theorem already holds at multigraph strength in it. What remains is
additive, localized to the 5.6 assembly and the statement layer.

- **F1. The M2 motive *is* the KT model.** `HasPanelRealization`
  (`Molecular/AlgebraicInduction/PanelHinge.lean`) quantifies a free
  `BodyHingeFramework` (per-edge extensor data) plus a normal assignment
  with per-link `ExtensorInPanel` containment
  (`Molecular/RigidityMatrix/Basic.lean`: the extensor is decomposable
  with every factor in the panel hyperplane). That is KT's
  hinge-coplanar panel-hinge framework, not the meet model.
- **F2. Bare Theorem 5.5 is already multigraph.**
  `theorem_55_minimalKDof_gen` concludes
  `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization`
  for **every** minimal `c`-dof multigraph (`IsMinimalKDof` carries no
  simplicity; looplessness is derived). Only the GP conjunct is
  Simple-gated. The base arm
  `theorem_55_base_producer_parallel_pair_gen` (`Theorem55.lean`)
  realizes the two-vertex double edge with **coincident panels + two
  linearly independent in-panel extensors at rank `D`** — KT Lemma 5.3,
  formalized.
- **F3. The Simple gate is localized to the 5.6 re-add assembly.**
  `rankHypothesis_genuine_of_theorem_55_gen` strips `G` to a minimal
  spanning `G'` (`exists_isMinimalKDof_spanning_subgraph`,
  multigraph-general) and realizes `G'` via the **GP conjunct**
  (`.1 hG'Simple`), then re-adds deleted edges as panel meets
  (`reaimSub`). That one consumption is the entire reason Theorem 5.6
  and the conjecture are simple-only.
- **F4. The extension's rank arithmetic is model-free.** The re-add
  upper bound runs at body-hinge level
  (`finrank_infinitesimalMotions_le_of_graph_le` +
  `reaimSub_withGraph_infinitesimalMotions`-style restriction identity),
  and the lower bound is the genericity-free
  `screwDim_add_deficiency_le_finrank_infinitesimalMotions` (needs only
  nondegenerate hinges) — reusable for an M2-level extension.

## Candidate route (work items; R0 gates the builds)

- **W1 — statement layer.** Mint the KT-faithful coplanar realization
  notion for *statements* (the M2 `∃ F, ∃ normal, …` pattern, named; or
  a faithful redefinition of `BodyHingeFramework.IsHingeCoplanar`, which
  is currently "arises as a `toBodyHinge`" — the meet model again).
  Decide the statement-design points in R1 before building.
- **W2 — the coplanar extension lemma** (the one genuinely new brick).
  From an M2 realization of a minimal spanning `G' ≤ G`, extend to `G`:
  each re-added edge gets a nonzero extensor in both endpoint panels —
  the meet when the normals are independent, any nonzero decomposable
  extensor in the shared hyperplane when coincident (both exist; no
  genericity anywhere). Rank via F4's two bounds. New motion-space
  restriction identity for the M2 extension is the expected main cost.
- **W3 — multigraph Theorem 5.6, M2 form.** Strip (F3's lemma, already
  multigraph) + bare spine conjunct (F2) + W2. Every deficiency, every
  spanning multigraph, nondegenerate hinges.
- **W4 — the multigraph molecular conjecture.** Iff with the W1 panel
  side. (⇐) elementary (a coplanar realization *is* a body-hinge
  realization — the forgetful direction). (⇒) rigid nondegenerate
  body-hinge ⇒ `def(G̃) = 0` (existing genericity-free bound) ⇒ W3 at
  deficiency zero.
- **W5 — blueprint + status-surface reconciliation.** Rescope
  `fmlnote:molecular-conjecture-multigraph` (the meet-model falsity
  *stands* as a remark — it is true and load-bearing exposition; the
  KT-faithful multigraph form becomes a theorem alongside), the
  `thm:theorem-55-6` fmlnote, the "simple-graph case" attributions
  (intro.tex / README / home_page), and the Prospect K1 entry.

## Work-item checklist

- [ ] **R0 — the opening recon** (route verification; gates everything.
  Question verbatim under *Blockers*; dispatch named under *Hand-off*).
- [ ] **R1–R3** — statement design / KT-faithfulness / witness forms
  (ride the R0 dispatch or the next).
- [ ] Adjudicate scope + statement design on the recon verdicts; open
  the blueprint chapter (forward mode) only then.
- [ ] **W1–W5** — sliced after the chapter-open; do not pre-plan slices
  here.

## Blockers / open questions

No build work is sanctioned until R0 returns. The recon questions,
verbatim from the planning survey:

- **R0 — route verification (gates everything).** This note's route is
  a session derivation, not a compiler-checked one: verify W2
  end-to-end at statement level — the M2 extension's motion-space
  restriction identity, whether `reaimSub`-analogous machinery adapts
  or is built fresh, and that the M2 rank conjunct (`rigidityRows` span
  form) composes with the F4 bounds as claimed.
- **R1 — statement design.** (i) Off-`E(G)` labels: the current
  conjecture quantifies nondegeneracy over all of `β` (essential for
  the ≥2-body clause) — what is the coplanar side's analogue? (ii)
  Loops: KT state Conjecture 1.2 for multigraphs (KT p. 648) — check
  their loop convention against the `.refs` copy; loops look harmless
  on both sides (zero rows) but the strip drops them, so W2 re-adds
  them. (iii) Spanning + `hfresh` label-headroom plumbing: same
  repackaging as the current wrapper?
- **R2 — KT-faithfulness cross-check.** Verify the W3/W4 statements
  against KT's §5 multigraph conventions (`.refs` copy), so the
  blueprint claim "this is KT's Conjecture 1.2, full strength" is
  honest — including whether KT's panel-hinge requires the panel
  assignment on all bodies or only those meeting edges.
- **R3 — witness forms.** Does the conjecture assembly need an M2
  analogue of the link-recording / genuine-hinge witness forms
  (`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`), or does
  the M2 per-link conjunct already carry everything W4 consumes?

## Sizing / phase grouping

Expected **small-to-medium and additive** — no refactor of the landed
meet-model surface, no genericity work, no new induction. Single phase;
if a seam is needed, split at W2‖W3 (the new brick) vs W4‖W5 (assembly +
docs), codes-until-open discipline. Contrast with K1's original sizing:
the wall was assessed against re-architecting the *meet-model
statement*; the reclassification is that the alternative encoding and
its hard theorem (multigraph 5.5 bare, incl. the Lemma-5.3 base) landed
with Phase 22i's M2 motive and the 22h/23 base producers — only the
last assembly step ever consumed the Simple gate.

## Hand-off / next phase

Next concrete step: **dispatch the opening recon on R0** (question
verbatim under *Blockers / open questions*), with **R1–R3 riding the
same dispatch or the next**. Read-only recon against the tree (the
F1–F4 declarations, from their bodies) and the `.refs` KT copy; the
verdicts come back to this note and drive the scope / statement-design
adjudication and the chapter-open. No Lean work before R0 returns GO on
the W2 route.

## Decisions made during this phase

- **Blueprint chapter-opening deferred until the R0/R1 verdicts land**
  (2026-07-18, at open; the Phase-32/Phase-34 precedent). A chapter
  written before the recon would transcribe this note's session-derived
  route as settled math against the carrier — exactly the
  transcribed-proof trap `CLAUDE.md` pins. Until the chapter exists,
  this note's checklist is the phase's to-do list.
- **The meet-model simple-graph theorems are retained, no refactor**
  (2026-07-18, from the planning survey, W5): for simple graphs they
  are the stronger, more concrete statements; the
  `fmlnote:molecular-conjecture-multigraph` meet-model falsity stands
  as load-bearing exposition, with the KT-faithful multigraph form to
  land alongside it.

## Citations (verified for this note)

- Katoh, Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011) — project-canonical (ROADMAP
  *References*); the specific pointers used here (Conjecture 1.2 for
  multigraphs p. 648; Lemma 5.3 coincident-panel realizations
  pp. 669–670; §5.2 strip-realize-re-add) were verified during the
  Phase-23-cleanup multigraph disclosure (2026-07-04,
  `notes/Phase23-cleanup.md`) and re-checked against
  `fmlnote:molecular-conjecture-multigraph` in the 2026-07-18 planning
  session.
