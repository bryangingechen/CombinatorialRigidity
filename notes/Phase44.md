# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** in progress, opened 2026-11-12 with the PI. Exposition of the three pencil chapters
against their classical sources; in the Lean, one rename, docstrings and the flat split in every
dimension. No main result's statement changes. Slices 1–6 of 10 done: the flat split holds in
every dimension, the `d = 3` motion count retired; the three chapters cite the sources of their
classical pieces, the road map's lineage left to slice 9. Next: slice 7, the rename and the
docstrings. Plan, the PI's words and the recon record: `notes/PencilScenes.md`.

## Current state

**Next concrete step: slice 7, the rename and the docstrings** (item 7, Lean). Slices 7–8 wait
on nothing. Slices 1–6 have landed: the flat split in every dimension is in
`Grade/GluedEnds.lean`, the `d = 3` flat rank (`MainComponent/FlatRank.lean`) follows from the
every-dimension one, `main-component.tex` credits the flat rank and the equality (now the
dimension of the lifting space), `pencil-d.tex` cites its rows' sources and reads Part C's lifts
as Whiteley's scenes, `pencil.tex` cites the flat pencil and the polarity and sets the
self-duality beside Whiteley's sheetworks, and every dep-graph node is green.

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
- [x] **6. `pencil.tex`** (2026-11-12): the flat pencil, the polarity, call 5; P8–P11; call 1
  weakened (*Decisions*).
- [ ] **7. The rename and the docstrings** (Lean, with the blueprint pins): `liftSpace` to
  `baseLiftSpace`, with `mem_liftSpace`, `liftSpaceTilde` and the lemma names that contain them
  (39 uses of `liftSpace` in 6 files at the open; count again in the slice); the docstrings of
  `liftingSpace`, `liftingPlanes`, `affineLifts`, the renamed space and `IsTrivialLift` cite
  their sources; call 5's prose in the Lean docstrings (7 files at the open). No statement or
  proof changes.
- [ ] **8. The additions of calls 2 and 3**: the second derivation as a short remark (the
  equality is Whiteley 1989's count on `S_G`; the face merge is Berg and Jordán's; the identity
  follows from published theorems and is not found stated); one remark on Maxwell–Cremona (O3
  and O5); `θ(2,2,3)` as a worked example in the carrier section and `C₇` as a sentence; O2 and
  O6 only if their unchecked parts check. Also `ledger-main.md` rows M10, M18 and M22–M24, minor
  citations in `main-component.tex` (the coordinator's assignment, 2026-11-12).
- [ ] **9. The road map and the three introductions** (attended): a lineage paragraph and what
  is classical and what is new (planning note §3, last paragraph; `ledger-main.md` rows P1–P7);
  O7 and O1 among the road map's observations (call 3); the history of call 7.
- [ ] **10. The close** (`PHASE-BOUNDARIES.md` *When this commit closes a phase*).

## Blockers / open questions

Nothing blocks slices 7–8.

Unchecked derivations, each to be checked in the slice named or weakened:

- O2's projection claim, and `(q, P_q)` as a section-projection figure in Whiteley 1991's sense
  (O6): slice 8.

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.

## Hand-off / next phase

The next commit is slice 7 (item 7), Lean comments and names only: `liftSpace` to
`baseLiftSpace`, with `mem_liftSpace`, `liftSpaceTilde` and the lemma names that contain them
(count the uses again; 39 in 6 files at the open), and the blueprint pins that name them; the
docstrings of `liftingSpace`, `liftingPlanes`, `affineLifts`, the renamed space and
`IsTrivialLift` cite their sources; call 5's prose in the Lean docstrings, in the chapters'
wording ("the dimension of the lifting space"). No statement or proof changes. After the phase:
ORIGAMI's open, with the PI (`notes/Origami.md`).

## Decisions made during this phase

- **The open (2026-11-12).** The PI's four answers are `notes/PencilScenes.md` §8, verbatim:
  the name `baseLiftSpace`; both of the simplification recon's additions to `pencil-d.tex`; the
  flat motion count retired for the flat split in every dimension, a spike first; docstrings
  change with the rename. The nine calls of §7 stand.
- **Slice 1.** Yes, with three corrections: constant on `V(G)` only, onto without
  connectedness, the kernel at every heights.
- **Slice 2.** The carrier is cited, not restated. Keys: `whiteley1989` is the hypergraph paper;
  Rigidity and polarity II, if cited, takes a suffix (I is `whiteley1987`, slice 6).
- **Slice 3a.** `gradeEmbed` (`ι`); W84 §5.1 credited with the image half at `d = 3` only.
- **PI, 2026-11-12:** asked how the prose proof of `thm:pencil-flat-rank` should read once its
  Lean goes through the padding proof, the PI chose "Forward reference (Recommended)": the
  proof says the rank is the every-dimension flat rank at one height and points forward to
  `thm:pencil-d-flat-rank`, with a sentence on what the flat split adds.
- **PI, 2026-11-12:** asked where the restated `lem:pencil-flat-split` should live, the PI
  chose "Move to pencil-d.tex (Recommended)": the node keeps its label and moves to
  `sec:pencil-d-flat`; `main-component.tex` keeps a sentence crediting Whiteley 1984 §5.1 and
  pointing at it, and the `d = 3` splitting text moves into `lem:pencil-join-flat`.
- **Slice 3b.** `pencilConfigPointGrade_flat` stays (FRICTION, the `gradeEmbed` idiom).
- **Slice 4.** The equality is "the dimension of the lifting space" in titles and prose, labels
  kept: JJ TR Thm 7.1 (`jacksonJordan2006pin`) over the reals, W84 Remark 2 (p. 287) for the
  gap, W89 Thms 3.1 and 5.4 for the independent cases; "not in his account" (W84 p. 288).
- **Slice 5.** Weakened: recon (ii)'s "special to plane pictures" to "undefined at K = 3" (W84
  p. 293); recon (i)'s lifts as scenes, at configuration bases only. O4 its own sentence.
  Dropped: Crapo 1984 p. 295 (concurrences, undeveloped). Crapo–Ryan §8 without O2's projection.
- **Slice 6 (2026-11-12).** Pages re-read: CW82 pp. 56, 67, 68; TW84 pp. 33–34 and RP-I
  pp. 344–345 on the images; JJ TR p. 21. Call 1 **weakened**: RP-I Thm 4.1 is the statics of
  jointed sheetworks (sheets braced in their planes, Def. 4.4), not of body-hinge frameworks, so
  the self-duality is not its consequence. Written: "not found stated"; RP-I §4's self-polar
  class as the pattern, the polar sheetwork on the closed neighbourhoods being the polar
  realization's (any pencil realization); the rank by CW82 §3.6. New key `whiteley1987`
  (Springer's citation record; Crossref has no pages). P8 points at the carrier section.
