# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** in progress, opened 2026-11-12 with the PI. Exposition of the three pencil chapters
against their classical sources; in the Lean, one rename, docstrings and the flat split in every
dimension. No main result's statement changes. Slices 1–8 of 10 done: the flat split holds in
every dimension, the three chapters cite their classical pieces, `liftSpace` is `baseLiftSpace`,
the docstrings cite, and calls 2 and 3 are added. Next: slice 9, the road map and the three
introductions, attended: it waits for the PI. Plan, the PI's words and the recon record:
`notes/PencilScenes.md`.

## Current state

**Next concrete step: slice 9, the road map and the three introductions** (item 9). It is
**attended: it waits for the PI**, and no `/coordinate-phase` dispatch runs it. Slices 1–8 have
landed: the flat split in every dimension is in `Grade/GluedEnds.lean`, the three chapters cite
their sources, every dep-graph node is green, the Lean's `liftSpace` is `baseLiftSpace`, and
`main-component.tex` has the second derivation (`rem:pencil-jj-count`), the Maxwell–Cremona remark
(`rem:pencil-maxwell-cremona`), the worked example `ex:pencil-theta` with the `C₇` sentence, O6
at the polar reading, and ledger rows M10, M18, M22–M24; O2 is a sentence in `pencil-d.tex`.

## Architectural choices made up front

- **No main result's statement changes.** One node's statement does: `lem:pencil-flat-split`,
  restated in every dimension if slice 1 holds (the PI, `notes/PencilScenes.md` §8).
- **The verification rule** (planning note §7): each slice re-reads, in the PDF, every page it
  cites. A derivation that is an agent's and unchecked goes into a chapter only once checked in
  its slice, or weakened to what was checked. The unchecked ones are listed under *Blockers*.
- **A bibliography entry lands with the slice that first cites it** (`lint.sh` check 2), and so
  does a `formalization.yaml` `sources` entry, if the slice's source is one a main result's
  description should name (none expected).
- **Labels and `liftingSpace` keep their names.** `thm:pencil-jj-equality` and the other labels
  stay; the prose around them changes (call 5). `liftingSpace`, `affineLifts` and
  `IsTrivialLift` are not renamed (planning note §7, *The Lean*).
- **The run.** Slices 1–8 under `/coordinate-phase`; slice 9 attended, as it sets the framing.

## Lemma checklist

One commit each, in this order. The chapter's order of slices 4–6 is free; 3 follows 1, and 9
follows all of 2–8.

- [x] **1. The flat-split spike** (2026-11-12): yes; files `notes/pencil-scenes/flat-*-spike.lean`.
- [x] **2. The carrier section** (2026-11-12): ledger rows M2–M9, M11, M14, M15, M17.
- [x] **3. The flat split in every dimension** (2026-11-12, two commits).
- [x] **4. The flat rank and the equality** (2026-11-12): calls 5 and 6; M1, M13, M16, M19–M21.
- [x] **5. `pencil-d.tex`** (2026-11-12): §3's rows; Part C's lifts as scenes; O4; call 5; M12.
- [x] **6. `pencil.tex`** (2026-11-12): the flat pencil, the polarity, call 5; P8–P11.
- [x] **7. The rename and the docstrings** (2026-11-12): `liftSpace` to `baseLiftSpace`; docstrings.
- [x] **8. The additions of calls 2 and 3** (2026-11-12): M10, M18, M22–M24; *Decisions*.
- [ ] **9. The road map and the three introductions** (attended): a lineage paragraph and what
  is classical and what is new (planning note §3, last paragraph; `ledger-main.md` rows P1–P7);
  O7 and O1 among the road map's observations (call 3); the history of call 7.
- [ ] **10. The close** (`PHASE-BOUNDARIES.md` *When this commit closes a phase*).

## Blockers / open questions

Slice 9 waits for the PI: it is attended, as it sets the framing. No derivation is left
unchecked (O2 and O6 settled in slice 8, *Decisions*).

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.

## Hand-off / next phase

The next commit is slice 9 (item 9), **attended by the PI**: the road map and the three
introductions get a lineage paragraph and what is classical and what is new (planning note §3,
last paragraph; `ledger-main.md` rows P1–P7), O7 and O1 among the road map's observations
(call 3), and the history of call 7. The PI sets its framing; no dispatch runs it. Then slice 10,
the close. After the phase: ORIGAMI's open, with the PI (`notes/Origami.md`).

## Decisions made during this phase

- **The open (2026-11-12).** The PI's four answers are `notes/PencilScenes.md` §8, verbatim; the
  nine calls of §7 stand.
- **Slice 1.** Yes, with three corrections: constant on `V(G)` only, onto without
  connectedness, the kernel at every heights.
- **Slice 2.** The carrier is cited, not restated; `whiteley1989` is the hypergraph paper.
- **Slice 3a.** `gradeEmbed` (`ι`); W84 §5.1 credited with the image half at `d = 3` only.
- **PI, 2026-11-12:** asked how the prose proof of `thm:pencil-flat-rank` should read once its
  Lean goes through the padding proof, the PI chose "Forward reference (Recommended)": the
  proof says the rank is the every-dimension flat rank at one height and points forward to
  `thm:pencil-d-flat-rank`, with a sentence on what the flat split adds.
- **PI, 2026-11-12:** asked where the restated `lem:pencil-flat-split` should live, the PI
  chose "Move to pencil-d.tex (Recommended)": the node keeps its label and moves to
  `sec:pencil-d-flat`; `main-component.tex` keeps a sentence crediting Whiteley 1984 §5.1 and
  pointing at it, and the `d = 3` splitting text moves into `lem:pencil-join-flat`.
- **Slices 3b–7.** `pencilConfigPointGrade_flat` stays (FRICTION); the equality is "the dimension
  of the lifting space"; slice 5 weakened two recon readings; call 1 **weakened** to "not found
  stated" (RP-I Thm 4.1 is sheetwork statics); `liftSpace` renamed outright, no shim.
- **Slice 8.** The second derivation is over the reals, the rank formula cited as W96 Thm A.1.4
  with Edmonds and Rota named. O2 in (checked from the definitions). O6's section by z = 0 in;
  its section-projection reading **dropped**: W91 Def. 5.2 is for spherical polyhedra, and P_q's
  pin at uv is the pole of the line q_u q_v, not on it. `C₇`'s 59 and 60 follow from the
  chapters' lemmas; the θ figures re-run (`example.py`). Five new bibliography keys.
