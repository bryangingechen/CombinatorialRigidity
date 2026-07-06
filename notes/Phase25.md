# Phase 25 — projective duality + the molecule modelling equivalence (work log)

**Status:** in progress (opened 2026-07-06).

## Current state

Phase just opened. The next concrete commit is a **layer-level design
recon** (design-pass-first, per `DESIGN.md` *Scale-up: design the
LAYER, not just the node*), written to a new `notes/Phase25-design.md`:
read KT §1.2 (pp. 650–651) and the p.671 reconciliation against
Crapo–Whiteley [4] and Jackson–Jordán [13], and settle the phase's two
scoping questions before any Lean:

1. **Formalize-vs-cite the projective-invariance external.** KT cite
   Crapo–Whiteley [4] §3.6 for projective invariance of infinitesimal
   rigidity in `ℝ³` (`thm:projective-invariance`). Decide whether to
   reuse the existing rigidity-matrix rank API for a from-scratch
   account or to axiomatize/cite it as an external the way Lemma 5.4's
   cycle content was handled — the risk-#4 formalize-vs-cite call, now
   for the projective half.
2. **The bar-joint-of-`G²` ↔ molecular-framework dictionary**
   (`thm:molecular-iff-square-bar-joint`, Whiteley [35] / JJ [13]) —
   the precise correspondence between the bar-joint infinitesimal
   motions of `G²` and the body-hinge motions of `G` at min degree ≥ 2.
   This is the harder of the two equivalences and likely the crux of
   the phase.

The recon also decides whether Phase 25 stays a **single integer
phase** or sub-letters (see *Decisions made*). The forward-mode
blueprint chapter `blueprint/src/chapter/molecule-modelling.tex`
(`sec:molecule-modelling`, 6 red nodes) is the authoritative dep-graph
/ lemma index; this note carries state, decisions, blockers, hand-off.

## Architectural choices made up front

- **Scope is `ℝ³` only.** KT §1.2 and the p.671 reconciliation are
  specific to three dimensions (projective dual transposes points and
  planes; the molecule model lives there). The Phase-24 matroid is
  read at `d = 3` for the same reason. No dimension-general statement
  is attempted here.
- **Reuse targets.** Phase 16 `def:body-hinge-framework`, the
  Phase-21+ `def:panel-hinge-framework` and `thm:theorem-55-6`
  (Thm 5.6), Phase 4 `def:framework` / `def:isInfinitesimallyRigid` /
  `def:isGenericallyRigid`, and Phase 24's `sec:bar-joint-3d` matroid +
  `def:genericRank`. Phase 25 adds the two modelling equivalences that
  Phase 26 (Cor 5.7) assembles with Thm 5.6 and the matroid.

## Blueprint chapter (forward mode) — the dep-graph / lemma index

`blueprint/src/chapter/molecule-modelling.tex` (`sec:molecule-modelling`),
all 6 nodes red (no `\lean`, no `\leanok`):

- `def:hinge-concurrent` — hinge-concurrent (molecular) framework: all
  hinges at each body pass through the body's centre `c(v)` ([13, 34]).
- `def:square-graph` — the square `G²` (distance-≤-2 graph).
- `thm:projective-invariance` — projective invariance of infinitesimal
  rigidity in `ℝ³` (Crapo–Whiteley [4] §3.6).
- `lem:panel-hinge-dual-molecular` — the `ℝ³` projective dual carries a
  nonparallel panel-hinge framework to a hinge-concurrent body-hinge
  framework and back (a bijection on the same graph).
- `thm:panel-hinge-iff-molecular` — G has a rigid panel-hinge
  realization iff a rigid molecular one (projective invariance + the
  dual correspondence).
- `thm:molecular-iff-square-bar-joint` — at min degree ≥ 2, G has a
  rigid molecular realization iff `G²` has a rigid bar-joint one
  (Whiteley [35] / JJ [13]).

## Lemma checklist

The dep-graph above IS the checklist (forward mode). None formalized
yet; the recon reorders/refines before any Lean lands.

## Blockers / open questions

- OD-25-1: formalize-vs-cite for `thm:projective-invariance` (risk #4).
- OD-25-2: the `G²`-bar-joint ↔ molecular dictionary at min degree ≥ 2.
- Both are the recon's job; neither blocks the open.

## Hand-off / next phase

**Next concrete commit:** the layer-level design recon →
`notes/Phase25-design.md` (settle OD-25-1, OD-25-2, and the
single-phase-vs-sub-lettered question; do not build Lean before it).
Phase 25 is the last gate before the capstone: **Phase 26 (Cor 5.7)
gates only on Phase 25** (Thm 5.6 from Phase 23 and the `d=3` matroid
from Phase 24 are in hand). Phase 26 is NOT opened by this commit.

Also still open, for a future cleanup round at a phase boundary (not
Phase-25/26 work): the molecular-layer dead-code/liveness sweep
deferred from `notes/Phase23-cleanup.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Opened as a single integer phase, design-recon first.** Unlike the
  sub-lettered Phases 22–23 (which bundled several large independent
  work bodies discovered mid-phase), KT §1.2 is one coherent argument
  — the projective-duality chain plus the square-graph modelling
  equivalence. The key uncertainty is the formalize-vs-cite scope of
  the projective-invariance external, a scoping question the recon
  settles, not evidence of multiple large chunks. Per the
  codes-until-open / re-cut-on-contact discipline
  (`PHASE-BOUNDARIES.md` *When this commit opens a phase*), a single
  integer phase is the lower-commitment default (matching Phase 24's
  open); if the recon shows it needs sub-lettering, the next agent
  mints letters + `notes/Phase25a.md` then, at no renumber cost. So
  this open mints a normal umbrella `notes/Phase25.md`, not a
  design-doc-plus-`25a` pair.
- **Design-pass-first.** The phase is research-shaped genuine
  projective geometry (the hardest of Phases 24–26 per
  `notes/MolecularConjecture.md`); per `DESIGN.md` *Scale-up: design
  the LAYER, not just the node*, the recon runs before any node build,
  as Case III (Phase 22c) opened.
