# Phase 31 — PROSPECT round 1: simplifications + restructuring recon (work log)

**Status:** in progress (opened 2026-07-10).

Planning input: `notes/Prospect.md` (the PROSPECT survey + adjudicated
phase order); this phase is its grouping 1. Blueprint mode:
structural-edit style — no new chapter; each slice's blueprint edits
(node restates, prose sync) ride the slice's commit.

## Current state

S2 landed. Next concrete step: the **S3 slice** — the full KT Lemma 3.4
tightness equality (see the work-item entry below). The two recons (R1,
G2) are dispatchable independently of the S3 Lean work. The S2 rider
(one-line retention docstrings on the d=3 dispatch decls) is still open;
bundle it with S3 or another Lean-touching commit.

## Work items (from `notes/Prospect.md`, grouping 1)

- [x] **S2 — rationality-conjunct fold-in.** Dropped the middle
  `(Q.coeffs : Set ℝ) ⊆ Set.range (algebraMap ℚ ℝ)` conjunct from
  `exists_generalPosition_polynomial` (`PanelHinge.lean`) and
  `exists_generalPosition4_polynomial` (`GeneralPosition4.lean`); every
  caller only ever destructured it into `_` (13 sites across
  Coupling/Theorem55/CaseI/CaseII/CaseIII/Realization.lean, 2 in
  Theorem56.lean), each reduced from a 4- to a 3-component pattern.
  Deletion-variant: `leadMinorPoly_mem_range_map` (private, its sole
  consumer) deleted outright. No blueprint node claims rationality for
  either decl's own conclusion (checked); the "rational minor/rank
  polynomial" mentions still in `molecule-modelling.tex`,
  `molecular-induction.tex`, `panel-layer.tex` are pre-existing
  genericity-device debt from Phase 30 slice (e), not this decl pair —
  left untouched, out of this slice's scope. Docstrings + one FRICTION
  entry (the `Subring.prod_mem` idiom) noted the drop. Build + `lake
  lint` clean.
- [ ] **S2 rider (optional, still open)** — one-line retention
  docstrings on the intentionally-kept d=3 dispatch decls (`Prospect.md`
  S1: the `theorem_55_d3`-style wrappers, `case_III_candidate_dispatch`
  chain — `Theorem55.lean`, `CaseIII/Realization.lean`,
  `RigidityMatrix/Claim612.lean`), so a future liveness sweep doesn't
  re-flag them. Sized separately from S2 proper (a fresh survey of the
  dispatch chain, not a 1-line add) — bundle with the next Lean-touching
  commit.
- [ ] **S3 — full KT Lemma 3.4 tightness equality.** The formalized form
  is the upper-bound/basis half; the full conclusion (`G[V(X)]` rigid,
  `|X − e| = D(|V(X)| − 1)` exactly) was deferred on the then-red
  `def = corank` bridge, which is long green. Genuinely unbuilt piece: a
  vertex-induced-subgraph-from-edge-set construction (pointers:
  `notes/Phase19.md` *Deferred*). Same commit: restate the
  `deficiency.tex` node and fix its stale "deferred with
  `thm:def-eq-corank`" remark.
- [ ] **R1 — speculative restructuring recon** (time-boxed). Seed
  questions + deliverable shape in `notes/Prospect.md` (R1): graded
  restructuring-candidate memo, compiler-witnessed probes only where
  cheap, "no candidates" an acceptable verdict. Verdict lands here and
  in `Prospect.md`; any GO candidate becomes its own adjudicated slice
  or phase, not an in-recon refactor.
- [ ] **G2 sizing recon** — settle `Graph.exists_adjacent_degree_two_pair`
  (`Molecular/Induction/ReducibleVertex.lean`) at `D = 3`: provable by a
  smarter count, or false (making the Case-III degeneration essential)?
  Record the verdict in `notes/Prospect.md` (it gates whether the planar
  G2 phase ever opens).

## Blockers / open questions

- None at open.

## Hand-off / next phase

Next concrete commit: the S3 slice (*Work items*) — the
vertex-induced-subgraph-from-edge-set construction plus the full KT
Lemma 3.4 tightness equality. At phase close: the queued PROSPECT
continuation (`notes/Prospect.md` *Hand-off*) — next up the new-math
phase (L1 Jacobs' conjecture + L2 degree-1 rank formula), then G1 field
generality (recon-first), then G3; G2 planar only on a favorable sizing
verdict from this phase.

## Decisions made during this phase

- **S2 landed** (see *Work items*): the general-position family's
  rationality conjunct is gone; the `exists_rankPolynomial_*` family
  (RELAX slice (e)) and the general-position-avoidance family (this
  slice) now share the same shape — no producer in the molecular tree
  carries a live rationality clause.
