# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** in progress, opened 2026-11-12 with the PI. Exposition of the three pencil chapters
against their classical sources; in the Lean, one rename, docstrings and the flat split in every
dimension. No main result's statement changes. Slices 1–3 of 10 done: the spike says yes; the
carrier section cites its sources; the flat split holds in every dimension, and the `d = 3`
motion count is retired. Next: slice 4, the flat rank and the equality attributed. Plan, the PI's
words and the recon record: `notes/PencilScenes.md`.

## Current state

**Next concrete step: slice 4, the flat rank and the equality** (item 4, `main-component.tex`).
Slices 5–8 wait on nothing. Slices 1–3 have landed: the flat split in every dimension is in
`Grade/GluedEnds.lean`, the `d = 3` flat rank (`MainComponent/FlatRank.lean`) follows from the
every-dimension one and its proof refers forward, and every dep-graph node is green.

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

- [x] **1. The flat-split spike** (2026-11-12, read-only recon): **yes to both.** The three
  spike files are banked in `notes/pencil-scenes/` (`flat-split-spike.lean`,
  `flat-rank-spike.lean`, `flat-deps-spike.lean`), re-run by the coordinator with `lake lean`.
  (a) Onto is by an explicit section of `gradePi`, with no dimension count and no use of
  connectedness; the kernel is the assignments constant **on `V(G)`** and killed by `⋀²π`, at
  every heights `z`. (b) No cycle: the every-dimension flat rank uses none of the `d = 3` chain,
  and the `d = 3` flat rank follows from it at `m = 1`. Both landed in slice 3.
- [x] **2. The carrier section** (`main-component.tex`, `sec:main-component-carrier`, with its
  bibliography entries): `S_G` named, `L(q)` introduced once as its scene space (Whiteley 1984,
  Sugihara 1984; call 4); `lem:pencil-lifting-planes-dim` as two eliminations of one system
  (§5a); `lem:pencil-lifting-planes-motions` as Whiteley 1984's reduced plate framework of
  `S_G`, which is pin-collinear. (2026-11-12: the carrier's introduction, a sentence each at
  `def:pencil-lifting-system` and `def:pencil-main-picture` (W84 Def. 2.4), a paragraph before
  `lem:pencil-lifting-planes-dim` and one after `lem:pencil-lifting-planes-motions`; no node's
  statement or proof route changed. Ledger rows M3–M9, M11, M14, M15 and M17 done; M2, the
  notation list, points at the new introduction; M10 is O6's, slice 8; M12 joins slice 5.)
- [x] **3. The flat split in every dimension** (2026-11-12, two commits). **3a:** the spike's
  lemmas in `Grade/GluedEnds.lean`; `lem:pencil-flat-split` restated in every dimension and moved
  to `sec:pencil-d-flat`, crediting Whiteley 1984 §5.1 for the image half at `d = 3` only; the
  `flatScrewEquiv` pin and the `W'`, `W_Π` splitting text in `lem:pencil-join-flat`. **3b:**
  `mem_span_extensor_flat_iff`, `Graph.linkConstants`, `Graph.finrank_linkConstants` and
  `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` deleted; the `d = 3` rank block in
  the new `MainComponent/FlatRank.lean` (it imports `Grade/Flat.lean`, and
  `MainComponent/Bridge.lean` imports it), `Graph.finrank_span_rigidityRows_ofNormals_flat` now
  the every-dimension rank at `m = 1`; `Grade/Flat.lean` imports `MainComponent/Flat.lean` in
  place of `Bridge`, and `Graph.x0AttainsGrade_of_deficiency_two_eq` moved to
  `Grade/ContractAdditive.lean`.
  `thm:pencil-flat-rank` keeps three pins, and its proof refers forward with one sentence on the
  flat split (the PI); `thm:pencil-d-flat-rank`'s `d = 3` sentence, no longer circular;
  `fmlnote:pencil-lifting-planes` counts the plane framework's motions.
- [ ] **4. The flat rank and the equality** (`main-component.tex`): the flat split credits
  Whiteley 1984 §5.1, the three in-plane dimensions ours; `sec:main-component-jj` and
  `thm:pencil-jj-equality` attributed as in §5a, "Jackson and Jordán's equality" renamed in
  prose to the dimension of the lifting space (call 5), with the second bibliography entry for
  the 2006 EGRES report (call 6).
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

Nothing blocks slice 4.

Unchecked derivations, each to be checked in the slice named or weakened:

- Recon (i)'s and (ii)'s derivations (planning note §7a, *Not checked*): slice 5.
- Crapo 1984 p. 295 as the polar form of `def:pencil-d-configuration`: slice 5, if cited.
- The self-duality from Rigidity and polarity I, Theorem 4.1: slice 6.
- O2's projection claim, and `(q, P_q)` as a section-projection figure in Whiteley 1991's sense
  (O6): slice 8.

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.

## Hand-off / next phase

The next commit is slice 4 (item 4), in `main-component.tex`: the flat split's credit to
Whiteley 1984 §5.1, the three in-plane dimensions ours; `sec:main-component-jj` and
`thm:pencil-jj-equality` attributed as in the planning note §5a; "Jackson and Jordán's equality"
renamed in prose to the dimension of the lifting space (call 5); the second bibliography entry,
for the 2006 EGRES report (call 6). `sec:main-component-flat`'s introduction now ends on the
forward route of `thm:pencil-flat-rank`'s proof (slice 3b); the rewording keeps it. Slices 5 and
6 may go in any order with it.
After the phase: ORIGAMI's open, with the PI
(`notes/Origami.md`).

## Decisions made during this phase

- **The open (2026-11-12).** The PI's four answers are `notes/PencilScenes.md` §8, verbatim:
  the name `baseLiftSpace`; both of the simplification recon's additions to `pencil-d.tex`; the
  flat motion count retired for the flat split in every dimension, a spike first; docstrings
  change with the rename. The nine calls of §7 stand.
- **Slice 1 (2026-11-12).** The spike says yes to both questions (item 1), with three
  corrections to the question as posed: constant on `V(G)` only, onto without connectedness,
  the kernel at every heights. The coordinator chose the layout that keeps `MainComponent/`
  from importing the every-dimension rank into its own flat file (item 3).
- **Slice 2 (2026-11-12).** The carrier is cited, not restated: the nodes keep their statements
  and proofs, and the classical reading sits in prose beside them. `P_q` is W84's reduced plate
  framework with each body's own face first in the reduction (its two bars per edge act as one
  pin); every page cited was re-read in the PDF, and the three new entries checked against
  Crossref. `\cite` keys: `whiteley1989` is the hypergraph paper; Rigidity and polarity II,
  if cited, takes a suffix.
- **Slice 3a (2026-11-12).** The spike's lemmas landed with one shortening: `gradeEmbed` (`ι`,
  `def:pencil-d-embedding`) in place of the spike's `gradePlanarIncl`, so no new definition
  duplicates it, and the spike's kernel lemma folded into its iff. Whiteley 1984 §5.1 (pp. 287–288,
  re-read) is credited with the image half at `d = 3` only: plates in a plane, each rotating about
  a line, `(u, v, w)` an affine velocity, a joint equating two of them. The kernel and `d > 3` are
  not in W84. The node's statement is in `⋀²` (`joinMotions`), as `lem:pencil-d-glued-ends` is.
- **PI, 2026-11-12:** asked how the prose proof of `thm:pencil-flat-rank` should read once its
  Lean goes through the padding proof, the PI chose "Forward reference (Recommended)": the
  proof says the rank is the every-dimension flat rank at one height and points forward to
  `thm:pencil-d-flat-rank`, with a sentence on what the flat split adds.
- **PI, 2026-11-12:** asked where the restated `lem:pencil-flat-split` should live, the PI
  chose "Move to pencil-d.tex (Recommended)": the node keeps its label and moves to
  `sec:pencil-d-flat`; `main-component.tex` keeps a sentence crediting Whiteley 1984 §5.1 and
  pointing at it, and the `d = 3` splitting text moves into `lem:pencil-join-flat`.
- **Slice 3b (2026-11-12).** Item 3's layout built in place, with no fallback: `Grade/ZeroHeights`
  and `MainComponent/Flat` reach neither `Bridge` nor `GluedEnds`. `Bridge` now sees
  `Grade/ZeroHeights` through `FlatRank`, and so does every file after it;
  `pencilConfigPointGrade_flat` stays (FRICTION, the `gradeEmbed` idiom). The forward `\uses`
  from `thm:pencil-flat-rank` to `thm:pencil-d-flat-rank` makes no cycle: the latter's `\uses`
  closure (36 nodes) does not reach the former. The proof's `\uses` are what its Lean uses:
  `thm:pencil-d-flat-rank`, `def:pencil-d-configuration`, `lem:pencil-lifting-space-deficiency`.
