# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** in progress, opened 2026-11-12 with the PI. Exposition of the three pencil chapters
against their classical sources; in the Lean, one rename, docstrings and the flat split in every
dimension. No main result's statement changes. Slices 1 and 2 of 10 done: the spike says yes;
the carrier section names `S_G` and cites its sources. Next: slice 3, in two commits, the PI's
two calls on it answered. Plan, the PI's words and the recon record:
`notes/PencilScenes.md`.

## Current state

**Next concrete step: slice 3a, the every-dimension flat split and its node** (item 3). The PI
answered the two calls on 2026-11-12 (*Decisions*): the node moves to `pencil-d.tex`, and
`thm:pencil-flat-rank`'s proof refers forward. Slice 3b, the retirement, follows; then slice 4.
Slices 5–8 wait on nothing. Slices 1 and 2 have landed; no Lean file has changed, and every
dep-graph node is green.

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
  `flat-rank-spike.lean`, `flat-deps-spike.lean`); the coordinator re-ran the first two with
  `lake lean`: no error, no warning, no `sorry`, the standard three axioms. They import as
  non-`module` files, so slice 3 builds them in place.
  (a) Onto is by an explicit section of `gradePi`, with no dimension count and no use of
  connectedness; the kernel is the assignments constant **on `V(G)`** and killed by `⋀²π`, at
  every heights `z`, not only the flat ones. The statements slice 3 lands, from the spike:
  `exists_mem_joinMotions_gradePi_eq` (at `z = 0`, from `hq : G.IsAdmissiblePicture q` and
  `h ∈ G.liftingPlanes q`, some `S ∈ joinMotions G (pencilConfigPointGrade q 0)` has
  `gradePi (S v) = h v` for all `v`) and `mem_joinMotions_iff_of_gradePi_eq_zero` (for
  connected `G` and `gradePi (S v) = 0` for all `v`: `S` is a motion iff it is constant on
  `V(G)`), with the packaged `joinMotionsPlanes`, `joinMotionsPlanes_surjective` and
  `mem_ker_joinMotionsPlanes_iff`. About 110 lines, for `Grade/GluedEnds.lean` beside `gradePi`.
  No `finrank` corollary: it has no consumer.
  (b) No cycle: the every-dimension flat rank and what it rests on use none of the `d = 3`
  chain (the dependency closures, `flat-deps-spike.lean`; the recon's run, not re-run). The
  `d = 3` statement `Graph.finrank_span_rigidityRows_ofNormals_flat` follows verbatim from
  `Graph.finrank_span_rigidityRows_ofNormals_flat_grade` at `m = 1` in 8 lines; its corollaries
  keep statements and proofs. Retired: `mem_span_extensor_flat_iff`, `Graph.linkConstants`,
  `Graph.finrank_linkConstants`, `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat`
  (`MainComponent/Flat.lean` 478–600), each used only there. Kept: `flatScrewEquiv`,
  `flatSigma`, `flatRebuild`, `flatStdBiv`, `flatPi`, `planarProj` (the joins and
  `MainComponent/Lines.lean` use them).
- [x] **2. The carrier section** (`main-component.tex`, `sec:main-component-carrier`, with its
  bibliography entries): `S_G` named, `L(q)` introduced once as its scene space (Whiteley 1984,
  Sugihara 1984; call 4); `lem:pencil-lifting-planes-dim` as two eliminations of one system
  (§5a); `lem:pencil-lifting-planes-motions` as Whiteley 1984's reduced plate framework of
  `S_G`, which is pin-collinear. (2026-11-12: the carrier's introduction, a sentence each at
  `def:pencil-lifting-system` and `def:pencil-main-picture` (W84 Def. 2.4), a paragraph before
  `lem:pencil-lifting-planes-dim` and one after `lem:pencil-lifting-planes-motions`; no node's
  statement or proof route changed. Ledger rows M3–M9, M11, M14, M15 and M17 done; M2, the
  notation list, points at the new introduction; M10 is O6's, slice 8; M12 joins slice 5.)
- [ ] **3. The flat split in every dimension** (Lean and `lem:pencil-flat-split`; only if slice 1
  says yes to both). The new lemma; the node restated and re-pinned, its `\uses` and the two
  nodes that cite its proof (`main-component.tex` near line 2237, `pencil-d.tex` near line 3135)
  re-read; the `d = 3` motion count retired (`Graph.linkConstants`,
  `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` and what only they use).
  **The layout** (the coordinator's call, not built in place): `Grade/Flat.lean` drops its
  `MainComponent/Bridge` import, its last theorem `Graph.x0AttainsGrade_of_deficiency_two_eq`
  moving to `Grade/ContractAdditive.lean`, a user of it; the `d = 3` rank block
  (`MainComponent/Flat.lean` 602–713) moves to a new file that imports `Grade/Flat.lean` and
  that `MainComponent/Bridge.lean` imports, Bridge's line 391 being the block's one use outside
  `MainComponent/Flat.lean`. If that meets a cycle, the fallback: `MainComponent/Flat.lean`
  imports `Grade/ZeroHeights.lean` and the every-dimension flat rank moves there.
  **The chapter**, beyond the node: the `flatScrewEquiv` pin and the `W'`, `W_Π` splitting text
  move to `lem:pencil-join-flat`, which uses them; the paragraph near `main-component.tex` 842
  and `fmlnote:pencil-lifting-planes` are reworded; `thm:pencil-d-flat-rank`'s second paragraph
  (`pencil-d.tex` near 1373) points at the restated node; `lem:pencil-d-glued-ends` is not
  contradicted.
  **Two commits.** **3a:** the spike's lemmas into `Grade/GluedEnds.lean`; `lem:pencil-flat-split`
  keeps its label, moves to `sec:pencil-d-flat` of `pencil-d.tex`, restated (onto `F(q)`, kernel
  constant on `V(G)` and killed by `⋀²π`) and pinned to them, crediting Whiteley 1984 §5.1 only
  as far as the page re-read supports; `main-component.tex` keeps a sentence pointing at it;
  the `flatScrewEquiv` pin and the splitting text go to `lem:pencil-join-flat`. The two count
  pins (`Graph.finrank_linkConstants`, `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat`)
  need a home until 3b: `thm:pencil-flat-rank`, whose Lean still uses them. **3b:** the
  retirement and the layout above; `thm:pencil-flat-rank`'s proof becomes the every-dimension
  flat rank at one height, referring forward to `thm:pencil-d-flat-rank`, with a sentence on
  what the flat split adds; the deletion grep, tree-wide (the retired names also stand in
  `notes/pencil-scenes/simplify-ii.md`, a banked report, which stays, and in
  `notes/FRICTION-archive.md` and `notes/Prose-findings.md`, archives).
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

Nothing blocks slice 3: the PI's two calls are under *Decisions*.

Unchecked derivations, each to be checked in the slice named or weakened:

- Recon (i)'s and (ii)'s derivations (planning note §7a, *Not checked*): slice 5.
- Crapo 1984 p. 295 as the polar form of `def:pencil-d-configuration`: slice 5, if cited.
- The self-duality from Rigidity and polarity I, Theorem 4.1: slice 6.
- O2's projection claim, and `(q, P_q)` as a section-projection figure in Whiteley 1991's sense
  (O6): slice 8.

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.

## Hand-off / next phase

The next commit is slice 3a (item 3, *Two commits*): the spike's lemmas
(`notes/pencil-scenes/flat-split-spike.lean`) into `Grade/GluedEnds.lean`, and the node moved
to `pencil-d.tex` and restated. Then 3b, then slice 4; slices 5 and 6 may go in any order with
them.
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
- **PI, 2026-11-12:** asked how the prose proof of `thm:pencil-flat-rank` should read once its
  Lean goes through the padding proof, the PI chose "Forward reference (Recommended)": the
  proof says the rank is the every-dimension flat rank at one height and points forward to
  `thm:pencil-d-flat-rank`, with a sentence on what the flat split adds.
- **PI, 2026-11-12:** asked where the restated `lem:pencil-flat-split` should live, the PI
  chose "Move to pencil-d.tex (Recommended)": the node keeps its label and moves to
  `sec:pencil-d-flat`; `main-component.tex` keeps a sentence crediting Whiteley 1984 §5.1 and
  pointing at it, and the `d = 3` splitting text moves into `lem:pencil-join-flat`.
