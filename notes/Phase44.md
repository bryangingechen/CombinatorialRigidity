# Phase 44 — PENCIL-SCENES: the pencil proof against its sources (work log)

**Status:** in progress, opened 2026-11-12 with the PI. Exposition of the three pencil chapters
against their classical sources; in the Lean, one rename, docstrings and the flat split in every
dimension. No main result's statement changes. Next: slice 1, the flat-split spike. Plan, the
PI's words and the recon record: `notes/PencilScenes.md`.

## Current state

**Next concrete step: slice 1, the read-only spike on the flat split in every dimension.**
Nothing but the open has landed: no chapter, bibliography or Lean file has changed, and every
dep-graph node is green.

The phase has one work log and no sub-phases. Its inputs are all in `notes/PencilScenes.md`:
what each source says (§2), each node against its source (§3's table), the observations O1–O7 and
the worked examples (§4), the recons (§5–§5c, §7a), the scope (§6), the plan and the nine calls
(§7) and the PI's answers at the open (§8). The per-row citation changes are the tables that end
`notes/pencil-scenes/merging-lemma-provenance.md`, `refs-liftings.md` and `refs-polarity.md`,
with the two ledgers (`ledger-main.md`, `ledger-d.md`): the worklist of slices 2 and 4–6.

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

- [ ] **1. The flat-split spike** (read-only recon, no commit but its verdict here). Two
  questions. (a) Does this hold, and how long is its Lean: at the flat configuration with any
  number of zero heights, on a connected graph over an admissible picture, the map of
  `gradePi_comp_mem_liftingPlanes` (`Grade/GluedEnds.lean`) from the motions to `F(q)` is onto,
  and its kernel is the constant assignments killed by `⋀²π`? The coordinator's sketch, unchecked:
  the kernel by `eq_of_gradePi_eq_of_mem_span` and connectedness, then onto by the count of
  `Graph.finrank_span_rigidityRows_ofNormals_flat_grade`. (b) Can the `d = 3` flat rank and its
  corollaries (`MainComponent/Flat.lean`, from `Graph.finrank_span_rigidityRows_ofNormals_flat`
  on), used at `MainComponent/Bridge.lean:391`, come from the padding proof, given that
  `Grade/Flat.lean` imports `MainComponent/Bridge.lean`? Deliverable: yes or no to each, the
  statement to land, the files that move, and a line estimate. A `lake lean` witness of (a) is
  welcome and is banked under `notes/pencil-scenes/` if written.
- [ ] **2. The carrier section** (`main-component.tex`, `sec:main-component-carrier`, with its
  bibliography entries): `S_G` named, `L(q)` introduced once as its scene space (Whiteley 1984,
  Sugihara 1984; call 4); `lem:pencil-lifting-planes-dim` as two eliminations of one system
  (§5a); `lem:pencil-lifting-planes-motions` as Whiteley 1984's reduced plate framework of
  `S_G`, which is pin-collinear.
- [ ] **3. The flat split in every dimension** (Lean and `lem:pencil-flat-split`; only if slice 1
  says yes to both). The new lemma; the node restated and re-pinned, its `\uses` and the two
  nodes that cite its proof (`main-component.tex` near line 2237, `pencil-d.tex` near line 3135)
  re-read; the `d = 3` motion count retired (`Graph.linkConstants`,
  `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` and what only they use).
  **If slice 1 says no to either:** the count stays, this slice is a sentence in slice 4 that the
  every-dimension flat rank does not go through the flat split, and the PI is told.
- [ ] **4. The flat rank and the equality** (`main-component.tex`): the flat split credits
  Whiteley 1984 §5.1, the three in-plane dimensions ours; `sec:main-component-jj` and
  `thm:pencil-jj-equality` attributed as in §5a, "Jackson and Jordán's equality" renamed in
  prose to the dimension of the lifting space (call 5), with the second bibliography entry for
  the 2006 EGRES report (call 6).
- [ ] **5. `pencil-d.tex`**: the sources of §3's rows; `def:pencil-d-lift` no longer presented
  as new; recon (i)'s two sentences at `def:pencil-d-lift` and `lem:pencil-d-ear-free`, and
  recon (ii)'s paragraph in Part C's introduction (the PI, §8), each derivation checked first;
  O4 as a sentence at `def:pencil-d-configuration`; call 5's prose.
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

None blocks slice 1. Unchecked derivations, each to be checked in the slice named or weakened:

- The every-dimension flat split (the coordinator's sketch): slice 1.
- Recon (i)'s and (ii)'s derivations (planning note §7a, *Not checked*): slice 5.
- Crapo 1984 p. 295 as the polar form of `def:pencil-d-configuration`: slice 5, if cited.
- The self-duality from Rigidity and polarity I, Theorem 4.1: slice 6.
- O2's projection claim, and `(q, P_q)` as a section-projection figure in Whiteley 1991's sense
  (O6): slice 8.

Left for a later round, not this phase's: the `x0` in names and labels, and the six
duplications between `MainComponent/` and `Grade/` of `notes/pencil-scenes/simplify-ii.md`.

## Hand-off / next phase

The next commit is slice 1's verdict: dispatch one read-only recon with the two questions of
item 1, check its answer against the Lean, and record yes or no to each at item 1, with the
statement slice 3 lands. It changes no chapter and no Lean. Whether slice 3 is one session's
work is not known until the spike sizes it. After the phase: ORIGAMI's open, with the PI
(`notes/Origami.md`).

## Decisions made during this phase

- **The open (2026-11-12).** The PI's four answers are `notes/PencilScenes.md` §8, verbatim:
  the name `baseLiftSpace`; both of the simplification recon's additions to `pencil-d.tex`; the
  flat motion count retired for the flat split in every dimension, a spike first; docstrings
  change with the rename. The nine calls of §7 stand.
