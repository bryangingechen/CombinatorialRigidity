# Phase 43d — EXPO: a road map of the pencil proof (work log)

**Status:** ✓ closed 2026-11-08 (opened the same day with the PI), the fourth and last sub-phase
of Phase 43 (PENCIL-NATURAL), whose close is Phase 43's: Phase 43 is complete. Layer EXPO as one
sub-phase, at the PI's word, with the PI's three answers on where the road map goes, how much
intuition it carries and how flatness is treated (design doc §1). Eight commits: the open, slices
1–5, the coordinator's dispatch-log entry and the close. What comes next is *Hand-off*. Plan:
`notes/Phase43-design.md`.

## Current state

**Closed, and Phase 43 with it.** `pencil.tex` opens with a road map of the proof
(`sec:pencil-roadmap`): the three parts in every dimension, KT's Cases (I)–(III) and Lemmas
4.5–4.6 against them, why each split is forced, and the recon's intuitions I1–I4 as restated.
`main-component.tex` has an unpinned remark that a planar-rigid set lies in one plane over a main
picture (`rem:pencil-x0-flatness`). At the PI's word the two `d = 3` main-component statements went
(`X0Dist`, `X0Gen`, `x0Dist`, `x0Gen` and three lemmas only they used; `Pencil/X0.lean` whole), and
the duplicate attaining theorem folded into the coverage. The three chapters' introductions point at
the road map. Measured against the open (`83b8dc03`): 7 declarations went and none came (10 Lean
files, +31 / −190 lines); 4 dep-graph nodes went and none came, and 2 labels came (the road map's
section and the remark). At the close the 21 `formalization.yaml` main results print the standard
three axioms, byte-identical to 43c's close run net of the harness path, and their statements read
as at Phase 43's open (`08898a01`).

**Records left as they are.** The banked spikes under `notes/pencil-natural/` (`N1Spike.lean`,
`PremiseClosure.lean`, `SprimeSpike.lean`, `sprime_walk.py`) name declarations Phase 43 deleted,
`x0Dist` and `x0Gen` among them; they are the records of their pins. The 43d record of what was
checked at the open (KT's pages, (F), the degeneracy in one direction, I1–I4, the forcing reasons) is
`git show 0f7dad8a:notes/Phase43d.md`, *Verified at the open*; the road map and the remark carry its
conclusions.

## Architectural choices made up front

- **No main result changes; Lean code and node statements only in slice 2** (held; the PI's later
  word). Slice 4's fold deleted one node and edited one Lean docstring, no code.
- **One home for the route** (held, the PI, Q1): the road map; the chapters keep their section
  guides and point at it.
- **Every claim cites a landed node or a KT page** (held); probe evidence stays in the notes.

## Lemma checklist

- [x] **1. Slice 1 — the road map** (`be73e28a`; `pencil.tex`, `sec:pencil-roadmap`).
- [x] **2. Slice 2 — the main-component statements go** (`47116a52`; the PI, D-c).
- [x] **3. Slice 3 — the flatness remark** (`17692c54`; `rem:pencil-x0-flatness`).
- [x] **4. Slice 4 — two chapters point at the road map, and the fold** (`f7b0f36f`; the PI, D-c).
- [x] **5. Slice 5 — `pencil-d.tex` points at the road map** (`0f7dad8a`; D-b).
- [x] **6. Close (43d, and with it Phase 43).** `PHASE-BOUNDARIES.md`'s full-phase close (this
  commit; *Decisions*).

## Blockers / open questions

None.

## Hand-off / next phase

Phase 43 is closed, and no phase is open. The next concrete step is PENCIL-SCENES' read-only
recon, then its open with the PI (queued 2026-11-09 ahead of ORIGAMI; ROADMAP *Queued
post-program phases*; planning note `notes/PencilScenes.md`). ORIGAMI follows.

## Decisions made during this phase

The PI's answers of 2026-11-08 (where the road map goes, structure and intuitions, the flatness
remark unpinned, open now; the removal of the statements; the fold) are design doc §1, verbatim.

- **D-a.** `thm:pencil-reduction` stays in `pencil.tex`, where the road map introduces part A.
- **D-b.** `sec:pencil-d-reduction` keeps a `d = 3` sentence that states a route fact or reads a
  polar object, and cuts one that compares with a `d = 3` proof (slice 5).
- **D-c.** The main-component statements go (the PI; slice 2), and `thm:pencil-x0-generic-attains`
  folds into `thm:pencil-x0-coverage` (the PI again; slice 4).
- **D-d.** The KT Theorem 4.9 correspondence is the road map's; `sec:pencil-reduction` keeps one
  glue sentence with a pointer.
- **D-e.** Not "heir of KT Lemmas 4.5–4.6": part (1) of `lem:pencil-x0-sparse-count` is KT's degree
  count, and `lem:pencil-d-chain-count` Lemma 4.6's count along the chains (KT p. 664).
- **D-f.** The chapter introductions keep their section guides; route sentences across chapters
  became one pointer each.
- **D-g.** The flatness remark sits after the `K_{2,3}` paragraphs of `main-component.tex`; its
  pair is "two pencil hubs adjacent or with a common neighbour", the same condition (`17692c54`).
- **D-h.** The road map's dependency sentence, measured against the `\uses` closure: A reaches B
  only through `lem:pencil-d-distinct-statement`; C uses B's conclusion only without a
  planar-rigid set, and lemmas of B's chapter; nothing in B or C reaches A; B reaches nothing of C.
- **D-i.** `sec:main-component-statements` is retitled *Nondegeneracy* and
  `sec:pencil-main-component-route` *Lifting planar pictures, and the theorem*, labels kept.
- **The close**: no exposition-ledger entry (`notes/BlueprintExposition.md`, Phase 43d and Phase 43
  as a whole); the end-to-end re-read of the prose slices 1–5 wrote found nothing to change; the
  design doc compressed to verdicts (no Lean doc-comment anchor into it).
