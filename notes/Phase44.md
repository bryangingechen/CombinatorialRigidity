# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** in progress, opened 2026-11-12 with the PI. Exposition of the three pencil chapters
against their classical sources; in the Lean, one rename, docstrings and the flat split in every
dimension. No main result's statement changes. Slices 1–4 of 10 done: the spike says yes; the
carrier section cites its sources; the flat split holds in every dimension, and the `d = 3`
motion count is retired; the flat rank and the equality are credited. Next: slice 5,
`pencil-d.tex` (or slice 6 first). Plan, the PI's words and the recon record:
`notes/PencilScenes.md`.

## Current state

**Next concrete step: slice 5, `pencil-d.tex`** (item 5); slice 6 (`pencil.tex`) may go first.
Slices 5–8 wait on nothing. Slices 1–4 have landed: the flat split in every dimension is in
`Grade/GluedEnds.lean`, the `d = 3` flat rank (`MainComponent/FlatRank.lean`) follows from the
every-dimension one, `main-component.tex` credits the flat rank and the equality to their
sources and calls the equality the dimension of the lifting space, and every dep-graph node is
green.

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

- [x] **1. The flat-split spike** (2026-11-12, read-only recon): yes to both; the spike files
  are banked in `notes/pencil-scenes/` (`flat-*-spike.lean`) and landed in slice 3.
- [x] **2. The carrier section** (2026-11-12, `sec:main-component-carrier`): `S_G` and its
  scenes (call 4), the two eliminations, `P_q` as W84's reduced plate framework, pin-collinear.
  Ledger rows M3–M9, M11, M14, M15, M17 done; M2 points at it; M10 is slice 8's, M12 slice 5's.
- [x] **3. The flat split in every dimension** (2026-11-12, two commits): `lem:pencil-flat-split`
  in every dimension (`Grade/GluedEnds.lean`, node in `sec:pencil-d-flat`); the `d = 3` motion
  count deleted, the `d = 3` flat rank (`MainComponent/FlatRank.lean`) the every-dimension one at
  `m = 1`, its proof referring forward.
- [x] **4. The flat rank and the equality** (2026-11-12, `main-component.tex`): the credits, the
  equality renamed in prose (call 5), the EGRES report's entry (call 6). Ledger rows M1, M13, M16
  and M19–M21 done.
- [ ] **5. `pencil-d.tex`**: the sources of §3's rows; `def:pencil-d-lift` no longer presented
  as new; recon (i)'s two sentences at `def:pencil-d-lift` and `lem:pencil-d-ear-free`, and
  recon (ii)'s paragraph in Part C's introduction (the PI, §8), each derivation checked first;
  O4 as a sentence at `def:pencil-d-configuration`; call 5's prose. With the scale-shift row,
  Sugihara 1984 eq. (10) (p. 85) at `main-component.tex`'s `lem:pencil-rank-scale-shift` too
  (`ledger-main.md` M12), if it is cited at the `d` twin.
- [ ] **6. `pencil.tex`**: "pencil" (Crapo–Whiteley 1982's flat pencil) and the polarity's
  attribution; the self-duality of the pencil class in call 1's wording, if its derivation
  checks; call 5's prose.
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
  O6 only if their unchecked parts check.
- [ ] **9. The road map and the three introductions** (attended): a lineage paragraph and what
  is classical and what is new (planning note §3, last paragraph); O7 and O1 among the road
  map's observations (call 3); the history of call 7.
- [ ] **10. The close** (`PHASE-BOUNDARIES.md` *When this commit closes a phase*).

## Blockers / open questions

Nothing blocks slices 5 and 6.

Unassigned: `ledger-main.md` rows M18 (JJ TR Lemma 4.1 beside the partition bound) and M22–M24
(W84 Cor. 4.2(i), pp. 273–274, W89 Def. 3.2), minor citations in `main-component.tex` that no
item names. The coordinator gives them a slice or drops them.

Unchecked derivations, each to be checked in the slice named or weakened:

- Recon (i)'s and (ii)'s derivations (planning note §7a, *Not checked*): slice 5.
- Crapo 1984 p. 295 as the polar form of `def:pencil-d-configuration`: slice 5, if cited.
- The self-duality from Rigidity and polarity I, Theorem 4.1: slice 6.
- O2's projection claim, and `(q, P_q)` as a section-projection figure in Whiteley 1991's sense
  (O6): slice 8.

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.

## Hand-off / next phase

The next commit is slice 5 (item 5), in `pencil-d.tex`: the sources of §3's rows,
`def:pencil-d-lift` no longer presented as new, recon (i)'s and (ii)'s text each checked first,
O4 at `def:pencil-d-configuration`, and call 5's prose. Its six "Jackson and Jordán's equality"
now point at a theorem titled "The dimension of the lifting space", the prose slice 4 settled in
`main-component.tex` (cite JJ TR Thm 7.1 as `jacksonJordan2006pin`). Slice 6 (`pencil.tex`, two
uses) may go first. After the phase: ORIGAMI's open, with the PI (`notes/Origami.md`).

## Decisions made during this phase

- **The open (2026-11-12).** The PI's four answers are `notes/PencilScenes.md` §8, verbatim:
  the name `baseLiftSpace`; both of the simplification recon's additions to `pencil-d.tex`; the
  flat motion count retired for the flat split in every dimension, a spike first; docstrings
  change with the rename. The nine calls of §7 stand.
- **Slice 1 (2026-11-12).** The spike says yes, with three corrections to the question as posed:
  constant on `V(G)` only, onto without connectedness, the kernel at every heights.
- **Slice 2 (2026-11-12).** The carrier is cited, not restated: nodes keep their statements and
  proofs. `\cite` keys: `whiteley1989` is the hypergraph paper; Rigidity and polarity II, if
  cited, takes a suffix.
- **Slice 3a (2026-11-12).** `gradeEmbed` (`ι`) in place of the spike's `gradePlanarIncl`. W84
  §5.1 credited with the image half at `d = 3` only; the kernel and `d > 3` are not in W84.
- **PI, 2026-11-12:** asked how the prose proof of `thm:pencil-flat-rank` should read once its
  Lean goes through the padding proof, the PI chose "Forward reference (Recommended)": the
  proof says the rank is the every-dimension flat rank at one height and points forward to
  `thm:pencil-d-flat-rank`, with a sentence on what the flat split adds.
- **PI, 2026-11-12:** asked where the restated `lem:pencil-flat-split` should live, the PI
  chose "Move to pencil-d.tex (Recommended)": the node keeps its label and moves to
  `sec:pencil-d-flat`; `main-component.tex` keeps a sentence crediting Whiteley 1984 §5.1 and
  pointing at it, and the `d = 3` splitting text moves into `lem:pencil-join-flat`.
- **Slice 3b (2026-11-12).** Layout built in place: `Bridge` sees `Grade/ZeroHeights` through
  `FlatRank`; `pencilConfigPointGrade_flat` stays (FRICTION, the `gradeEmbed` idiom); the
  forward `\uses` to `thm:pencil-d-flat-rank` makes no cycle.
- **Slice 4 (2026-11-12).** The equality is the dimension of the lifting space in titles and
  prose (labels kept). Credited to JJ TR Thm 7.1 (`jacksonJordan2006pin`, checked against the
  EGRES series record), the published version through its bar-and-joint model; W84 Remark 2
  (p. 287) for the gap; W89 Thms 3.1 and 5.4 for the independent cases. "The three in-plane
  dimensions ours" is written as "not in his account" (W84 p. 288), what was checked; W84 §5.3
  beside CW82's tetrahedron. Every cited page re-read in the PDF.
