# Phase 31 — PROSPECT round 1: simplifications + restructuring recon (work log)

**Status:** in progress (opened 2026-07-10).

Planning input: `notes/Prospect.md` (the PROSPECT survey + adjudicated
phase order); this phase is its grouping 1. Blueprint mode:
structural-edit style — no new chapter; each slice's blueprint edits
(node restates, prose sync) ride the slice's commit.

## Current state

Phase just opened. Next concrete step: the **S2 slice** — drop the
live-but-unconsumed rationality conjunct from
`exists_generalPosition_polynomial`
(`Molecular/AlgebraicInduction/PanelHinge.lean`) and
`exists_generalPosition4_polynomial`
(`Molecular/Molecule/GeneralPosition4.lean`) and sweep their callers,
Phase-30 slice-(e) discipline (build + `lake lint` green; blueprint
prose sync in the same commit if any node claims rationality for these;
deletion-variant grep on any decl that goes callerless). The two recons
(R1, G2) are dispatchable independently of the S2/S3 Lean work.

## Work items (from `notes/Prospect.md`, grouping 1)

- [ ] **S2 — rationality-conjunct fold-in.** As above. Optional rider
  riding this slice's Lean commit: one-line retention docstrings on the
  intentionally-kept d=3 dispatch decls (`Prospect.md` S1), so a future
  liveness sweep doesn't re-flag them.
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

Next concrete commit: the S2 slice (*Current state*). At phase close:
the queued PROSPECT continuation (`notes/Prospect.md` *Hand-off*) —
next up the new-math phase (L1 Jacobs' conjecture + L2 degree-1 rank
formula), then G1 field generality (recon-first), then G3; G2 planar
only on a favorable sizing verdict from this phase.

## Decisions made during this phase

- (none yet)
