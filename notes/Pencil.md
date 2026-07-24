# PENCIL — hinge-pencil molecular conjecture (planning note)

**Status:** queued (user-queued 2026-07-23); unopened — number minted
on open. Same editing discipline as phase notes (≤8-line entries,
lift cross-cutting lessons).

## The question

KT's theorem (formalized: `molecular_conjecture`, Phases 17–26; the
multigraph/coplanar-model strengthening, Phase 35) says the generic
body-hinge rank in `ℝ³` is already achieved on the *panel* stratum —
each body's hinges coplanar — and, by projective duality (Phase 25),
on the *molecular* stratum — each body's hinges concurrent. PENCIL
asks about the **intersection stratum**: each body's hinges both
concurrent *and* coplanar, i.e. a **pencil** of lines through a point
in a plane. Does a pencil realization generic in that stratum still
achieve the generic body-hinge rank (Tay's tree-packing count;
`5G` ⊇ 6 edge-disjoint spanning trees at `d = 3` via KT Cor. 5.7)?

In the `G²` molecular reading (Phase 25/26 modelling), the hinges at
the body of atom `v` are the bond lines through `p(v)` — concurrency
is automatic — so the pencil condition says **`v`'s bond-star is
coplanar** (its neighbors lie in a plane through `p(v)`). Chemically:
sp²/planar-bonded atoms. So PENCIL reads: *does the molecular count
stay valid for molecules with planar-bonded atoms?* The condition
only bites at bodies of degree ≥ 3 (two coplanar lines are
automatically projectively concurrent).

Trivial direction: pencil ⇒ panel per body, so pencil rank ≤ generic
(KT). The content is the lower bound. The all-bodies statement is the
strongest form: any mixed version (pencil on a subset of bodies,
generic elsewhere) follows by rank lower-semicontinuity, since the
all-pencil stratum sits inside every mixed stratum.

Why it's queued as a warmup: no new carrier material — extensor
algebra, panel model, deficiency matroid, and the contraction
induction (Thm 4.9) are all in-tree. The work is an analog of the
algebraic induction step (Thm 5.5) that maintains the pencil
constraint through the split, or a reduction to the formalized
statements. As of 2026-07-23 no literature result on this stratum was
found (searched; Jordán 2016 and the KT paper are silent) — **this
would be new mathematics**, so the phase opens recon-first and a
refutation is a legitimate close.

## Open recon questions (opening dispatch settles these first)

- **R1 — statement + satisfiability.** On the panel side, *distinct*
  panels force each hinge to be the line `Π_u ∩ Π_v`, and per-body
  concurrency becomes extra codimension conditions — the honest
  stratum likely needs KT's containment/coincident-panel freedom
  (Phase 35's `HasCoplanarPanelRealization` model, not the meet
  model). The molecular-side formulation (bond-stars coplanar) is
  clean and obviously satisfiable; pin the panel-side dual statement
  and check the two sides are still projectively dual on-stratum.
- **R2 — truth sanity.** Small-case witnesses (single body and
  two-body cases are near-trivial; first interesting case is a
  degree-3 body). Known negative data lives *deeper* in the stratum
  (e.g. all atoms in one common plane is rank-deficient), so the
  claim is generic-in-stratum only — KT-style relative-genericity
  bookkeeping is essential, and a counterexample hunt should respect
  that.
- **R3 — which KT case breaks.** The Case I/II/III splitting places
  the new hinge inside the merged panel; the added concurrency
  constrains that choice. Does Lemma 6.13's extensor-span argument
  survive with the hinge pinned through the body's point? Identify
  the first inequality that consumes panel-only freedom.

## Prerequisites

None beyond in-tree material (Phases 17–26, 35). Blueprint chapter
opens forward-mode on phase open, per `PHASE-BOUNDARIES.md`.

## Adjacent directions (not queued; for orientation only)

ORIGAMI (`notes/Origami.md`) is the bar-joint-side analog. Further
KT-template subvariety questions (symmetric molecular conjecture,
identified hinges, frameworks with boundaries) were surveyed in the
2026-07-23 discussion that queued this phase; queue them separately
if wanted.
