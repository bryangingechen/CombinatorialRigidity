# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** ✓ complete, opened 2026-11-12 with the PI and closed 2026-11-13. Exposition of the
three pencil chapters against their classical sources; in the Lean, one rename, docstrings and
the flat split in every dimension. No main result's statement changed. All ten slices landed.
Next: ORIGAMI's open, with the PI (`notes/Origami.md`). Plan, the PI's words and the recon
record: `notes/PencilScenes.md`; summary: ROADMAP §44.

## Current state

**Closed. Next concrete step: ORIGAMI's open, with the PI** (`notes/Origami.md`;
`PHASE-BOUNDARIES.md` *When this commit opens a phase*). The phase's ten slices have landed. The
flat split in every dimension is in `Grade/GluedEnds.lean`, the three chapters cite their
sources, every dep-graph node is green, and the Lean's `liftSpace` is `baseLiftSpace`.
`main-component.tex` has the second derivation (`rem:pencil-jj-count`), the Maxwell–Cremona
remark (`rem:pencil-maxwell-cremona`), the worked example `ex:pencil-theta`, and ledger rows M10,
M18, M22–M24. The road map (`sec:pencil-roadmap`) says what is classical, in four paragraphs,
and what is new, in one, and has six observations; each of the three introductions names its
classical share and points at the road map. At the close the 21 main results' axioms are the
standard three, byte-identical to Phase 43's close run (`lake lean` on the harness of
`PHASE-BOUNDARIES.md`), and their statements were not touched.

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
- **The run.** Slices 1–8 under `/coordinate-phase`; slice 9's framing set by the PI (*Decisions*).

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
- [x] **9. The road map and the three introductions** (2026-11-13; framing approved by the PI):
  a lineage paragraph and what is classical and what is new (planning note §3, last paragraph;
  `ledger-main.md` rows P1–P5; P6 and P7 are cited at their nodes since slices 2 and 4);
  O7 and O1 among the road map's observations (call 3); the history of call 7.
- [x] **10. The close** (2026-11-13): the re-read, two small fixes, the status surfaces.

## Blockers / open questions

None. No derivation is left unchecked (O2 and O6 settled in slice 8, O7 and O1 re-derived in
slice 9, *Decisions*).

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.
A general scene space is ORIGAMI's opening recon's to decide (`notes/PencilScenes.md` §6).

Left for the coordinator at this close: the grooming of `notes/dispatch-log.md`, which a
builder does not edit (`PHASE-BOUNDARIES.md` *When this commit closes a phase*).

## Hand-off / next phase

The phase is closed. The next commit is ORIGAMI's open, with the PI: it mints the phase's number,
with `notes/Origami.md` as its planning note (`PHASE-BOUNDARIES.md` *When this commit opens a
phase*; ROADMAP *Queued post-program phases*). That note records a candidate first layer from
this phase, unchecked: a placement with each block's boundary coplanar is a picture with a scene
over it, so a general scene space may serve both. The opening recon decides it. The two items
under *Blockers* wait for a cleanup round of their own, at the PI's word.

## Decisions made during this phase

- **The open (2026-11-12).** The PI's four answers are `notes/PencilScenes.md` §8, verbatim; the
  nine calls of §7 stand.
- **Slices 1–3a.** The spike held; the carrier is cited, not restated; W84 §5.1 is credited with
  the flat split's image half at `d = 3` only.
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
- **Slice 8.** The second derivation is over the reals. O2 in; O6's section by z = 0 in, its
  section-projection reading **dropped** (W91 Def. 5.2 is for spherical polyhedra).
- **PI, 2026-11-13:** shown the coordinator's framing for slice 9 (one paragraph pair in the
  road map, on what is classical and on what is new; six observations, O7 and O1 added; one
  sentence of history, on Maxwell; one or two sentences in each introduction) and its four
  calls, the PI answered: "OK, this looks good. Let's proceed and add bibliiography keys for the
  papers we cite as we go."
- **Slice 9.** Keys `whiteley1982`, `maxwell1864reciprocal`, `maxwell1870`. "The classical
  statements are over the reals" became "the sources work over the real numbers", which is what
  the pages show. O7 is stated at `d = 3`; O1's linear algebra (`ledger-d.md` §4) re-derived.
- **Slice 10, the close.** The re-read covered `pencil.tex` whole and, in the two long chapters,
  every passage the phase wrote or changed, in context, with their introductions; the passages
  the phase left alone were last re-read at Phase 43's close. Two fixes: the road map's
  paragraph on what is classical split in four, no word changed; the flat split's section
  renamed `τ`, as `σ` is the chapter's map of affine heights. No exposition-ledger entry.
