# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** ✓ closed 2026-10-24 (opened the same day), a sub-phase of Phase 41, which stays in
progress. The phase's design, the PI's decisions and the open's recon are in
`notes/Phase41-design.md`. Every checklist item landed: the API (1–3a), the build-time detour
(P1–P5), the spike (4), the switch (5a, 5b), `withGraph` restricted with `reaim` deleted (6) and
the two genuine forms merged (7). Next concrete task: RESTATE's open as 41b, with the PI (see
*Hand-off*).

## Current state

**Closed.** The field `isLink_ends` is on `PanelHingeFramework` (design A,
`notes/Phase41-design.md` §1.1): a framework whose selector does not give each edge of its graph
its two ends cannot be built. No main result's statement changed, and the 19 main results' axioms
are unchanged (`[propext, Classical.choice, Quot.sound]`, identical to RECONCILE round 3's last
run). The commits: item 1 `reaimSub` retired; items 2–3a the API (`RecordsLinks`, `link_tac`, the
R statements); P1–P5 the whole project to `module`s (a proof-only edit at `CaseIII/Realization`
rebuilds that file alone, 10–14 s); item 4 the spike (`c2bad1ed`); 5a the switch (`afcff8fd`, 123
declarations in 27 files, `def:panel-hinge-framework` and `panel-layer.tex`'s selector notes
restated); 5b the footprint's docstrings (`8460b351`); 6 `withGraph` restricted and `reaim`
deleted (`a22d989c`); 7 the genuine forms merged (`f4bc4cb5`). Mode: structural edit, no red
target nodes; each slice restated the nodes it reached.

## Architectural choices made up front

- **The field** is `isLink_ends : ∀ e ∈ E(graph), graph.IsLink e (ends e).1 (ends e).2`
  (`notes/Phase41-design.md` §2 *The field*), not the total form and not a derived selector.
- **The constructors take the link proof as their last argument, filled in by a small tactic**
  (the witness's `link_tac`), so the common sites need no edit.
- **API first, switch last** (Phase 22l): the predicate, its lemmas, the tactic and the R fixes
  land before the field, which arrives in one build-green commit.
- **Ledger.** As in RECONCILE's rounds (`notes/Reconcile.md` §2): each commit names the ledger IDs
  it acts on (S2: `F-122`, `F-125`, `F-128`; the footprint's docstrings: `F-123`, `F-130`, `F-220`
  and the parts of `F-122`, `F-126`, `F-133`, `F-210`, `F-215`, `F-225`, `F-237`, `F-243` that
  round 3 moved here) and gives each entry its `done (<sha>)` disposition.

## Lemma checklist

- [x] **1–3a. The API**: `reaimSub` retired (1); `RecordsLinks`, its lemmas and `link_tac` (2);
  the four R statements on the splitting-off (3), their duplicate conjuncts dropped (3a).
- [x] **P1–P5. The build-time detour**: the import trim, the `module` recon, and the whole project
  to `module` in three layers (`notes/PERFORMANCE.md` *The import trim* to *The conversion,
  layers 19–38*).
- [x] **4. The spike**: 123 declarations in 27 of the 32 carrier files (FRICTION *The link field…*).
- [x] **5. The switch**, two commits:
  - [x] **5a, the switch** (`afcff8fd`): the spike's patch, the record binders named `hlinks`, the
    docstrings and blueprint notes it made false (fix classes: TACTICS-QUIRKS § 120).
    `case_III_candidate_dispatch`'s `hGvGab` stays: `hrecGv₁` uses it by name.
  - [x] **5b, the footprint's docstrings** (`8460b351`; docs only), and the selector half of the
    status surfaces' scope sentences.
- [x] **6. `withGraph` restricted** to `G' ≤ P.graph` (`def:framework-with-graph`), and **`reaim`
  deleted**, with `rigidityMatrix_prop11`'s `hC` asked only at links; 5b's docstring wraps
  reflowed. S18 is not discharged: the conditional statement, or a repin on the generic forms, is
  RESTATE's, after S1 (`notes/Phase41-design.md` §3).
- [x] **7. The two genuine forms merged**: under the field,
  `rankHypothesis_genuine_of_theorem_55_gen` and its link-recording form coincide; the first keeps
  the proof, and `thm:theorem-55-6-genuine` pins it alone.
- [x] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the 19
  main results' axioms unchanged; RESTATE named as 41b, to open with the PI.

## Blockers / open questions

Both carried to RESTATE (`notes/Phase41-design.md` §3):
- **The status surfaces' degenerate-hinge sentences** stay true until RESTATE: Theorem 5.6's
  `main_results` row and `alignment` note, README, the home page, `intro.tex` and ROADMAP §23 say
  that `rankHypothesis_of_theorem_55_gen` allows degenerate hinges, so at deficiency zero the
  all-zero-normals framework meets it.
- **Link conjuncts the field makes redundant** (no main result): the rows form
  `finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`,
  `exists_rankHypothesis_isGeneralPosition4_of_two_le` (`Theorem56.lean`), and
  `exists_independent_normalRow_of_le_finrank`'s `hQends` (`PanelGeneric.lean`), in RESTATE's row;
  `HasGenericFullRankRealization`'s last conjunct, seen at the close, is the design doc's §4
  question.

## Hand-off / next phase

**RESTATE opens next, as 41b, with the PI** (the coordinator confirms with the PI first; nothing is
opened here). Its contents and estimate are `notes/Phase41-design.md` §3's RESTATE row; its open
settles §1.3's stronger forms and §4's open questions, and its first commit creates
`notes/Phase41b.md` (`PHASE-BOUNDARIES.md` *When this commit opens a phase*). MULTIGRAPH and
UNSTATED follow by code.

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.

- **The build-time detour** (P1–P5; PI): the whole project made `module`s before the spike
  (`notes/PERFORMANCE.md`).
- **The link predicate** (items 2, 5a): `RecordsLinks G ends`, the field's type; `:= by link_tac`;
  the record binders are `hlinks` (TACTICS-QUIRKS § 120).
- **The R statements** (items 3, 3a): `RecordsLinks (G.splitOff …) ends`, four statements.
- **The selector sentences** (item 5b; coordinator): the surfaces drop the free selector and keep
  the degenerate hinges, which RESTATE removes.
- **`withGraph` and `hC`** (item 6): `withGraph` takes `hle : G' ≤ P.graph`; `hC` at links; the
  d = 3 corollary's unused `2 ≤ |V(G)|` binds `_hV` until RESTATE restates its node.
- **One genuine form** (item 7; coordinator): `rankHypothesis_genuine_of_theorem_55_gen` survives.
- **The redundant link conjuncts go to RESTATE** (close; coordinator): it restates their
  declarations anyway, S1's panel theorems in `PanelGeneric` and §1.3's general-position form in
  Theorem 5.6's.
