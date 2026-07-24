# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress (opened 2026-07-23, recon-first).

## Current state

Phase just opened: no recon has run, no Lean or blueprint work exists,
and **no formal statement of the pencil conjecture is pinned** — R1
below adjudicates the statement before anything builds on it. Next
concrete step: **dispatch the opening recon** (R1–R3 below; R1 gates
the other two). A grounded refutation is a legitimate close for this
phase. This note's content is transcribed from the planning note
`notes/Pencil.md` (user-queued 2026-07-23; now a thin pointer here),
not re-derived.

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

Why it was queued as a warmup: no new carrier material — extensor
algebra, panel model, deficiency matroid, and the contraction
induction (Thm 4.9) are all in-tree. The work is an analog of the
algebraic induction step (Thm 5.5) that maintains the pencil
constraint through the split, or a reduction to the formalized
statements. As of 2026-07-23 no literature result on this stratum was
found (searched; Jordán 2016 and the KT paper are silent) — **this
would be new mathematics**, hence recon-first with refutation a
legitimate close.

## Opening recon questions (R1 gates R2/R3)

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

## Blockers / open questions

- The R1–R3 recon verdicts are the phase's open questions; nothing
  else blocks. Prerequisites are all in-tree (Phases 17–26, 35).

## Hand-off / next phase

**Next concrete dispatch: the opening recon** — one recon deliverable
covering R1–R3 (R1 first: pin the panel-side statement, check
on-stratum projective duality and satisfiability; R2 truth sanity and
R3 which-KT-case-breaks ride the same dispatch, splitting to a
follow-on only if R1 exhausts it). No build dispatches and no
blueprint chapter before the R1 verdict (see *Decisions made*).

## Adjacent directions (orientation only, not this phase)

ORIGAMI (`notes/Origami.md`, next queued) is the bar-joint-side
analog; the wider unqueued survey — incl. IDENT-PANEL, the nearest
neighbor — is `notes/IdeaBacklog.md`.

## Decisions made during this phase

- **Recon-first; no pinned statement at open** (2026-07-23, per the
  queue entry + `notes/Pencil.md`): R1's statement/satisfiability
  questions are genuinely open, so the open commit pins no Lean
  signature and no blueprint node.
- **Blueprint chapter deferred to the R1 verdict** (2026-07-23):
  `notes/Pencil.md` planned the forward-mode chapter opening with the
  phase, but with R1 unsettled a chapter-open red node risks the
  known plausible-"corrected"-statement failure mode (dispatch-log
  2026-07-11); the Phase-32/34/35 precedent — chapter opens on the
  recon verdicts — applies instead. Re-flagged here rather than
  silently dropped.
- **Higher-`d` pencil hierarchy may fold into the recon**
  (`notes/IdeaBacklog.md` Tier A): the per-body strata between panel
  and molecular in general dimension. The opening recon may note
  whether the question generalizes past `d = 3`, but it is not an
  R1–R3 deliverable.

## Citations (transcribed, project-canonical sources)

- Katoh–Tanigawa, *A proof of the molecular conjecture*, Discrete
  Comput. Geom. **45** (2011) — the KT pointers in this note
  (Cor. 5.7, Thm 4.9, Thm 5.5, Lemma 6.13, the Case I/II/III split)
  are transcribed from `notes/Pencil.md`'s 2026-07-23 survey against
  the project-canonical source (ROADMAP *References*); KT pointer
  verification history: `notes/Phase35.md` *Citations*,
  `notes/Phase23-cleanup.md`.
- Jordán 2016 (MSJ Memoirs 34) — checked silent on the pencil stratum
  in the 2026-07-23 survey (the no-literature-result finding).
