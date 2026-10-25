# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Items 1 to 4, the build-time detour P1 to P5, and item 5a,
the switch, and item 5b, the footprint's docstrings, have landed. Next concrete task: item 6,
`withGraph` restricted and `reaim` deleted.

## Current state

Opened with the PI on 2026-10-24, after the design recon (`notes/Phase41-design.md` §2). The
sub-phase builds S2's field `isLink_ends` into the carrier (design A, `notes/Phase41-design.md`
§1.1) and leaves every main result's statement as it is: the restatements are RESTATE's. Items 1–3a
laid the API (`RecordsLinks`, `link_tac`, the R statements); the build-time detour P1–P5 made the
whole project `module`s (a proof-only edit at `CaseIII/Realization` rebuilds that file alone,
10–14 s); item 4's spike and item 5a landed the switch: the field is on the structure, 123
declarations in 27 files follow it, the record binders are `hlinks`, and
`def:panel-hinge-framework`'s formal note and `panel-layer.tex`'s selector notes are restated. Mode:
structural edit. There are no red target nodes, so the red-node consistency gate has nothing to
read; the nodes a slice reaches are restated in that slice (`CombinatorialRigidity/CLAUDE.md`
*Forward-mode slices*).

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
  - [x] **5b, the footprint's docstrings** (docs only; ledger dispositions "(item 5b)", whose sha
    item 6 writes), and the selector half of the status surfaces' scope sentences.
- [ ] **6. `withGraph` restricted** to `G' ≤ P.graph` (`def:framework-with-graph`), and **`reaim`
  deleted**, with `rigidityMatrix_prop11`'s `hC` asked only at links.
- [ ] **7. The two genuine forms merged**: under the field,
  `rankHypothesis_genuine_of_theorem_55_gen` and its link-recording form coincide.
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the 19
  main results' axioms unchanged; RESTATE opens as 41b.

## Blockers / open questions

- **The status surfaces' degenerate-hinge sentences** stay true until RESTATE: Theorem 5.6's
  `main_results` row and `alignment` note, README, the home page, `intro.tex` and ROADMAP §23 say
  that `rankHypothesis_of_theorem_55_gen` allows degenerate hinges, so at deficiency zero the
  all-zero-normals framework meets it. RESTATE's table removes them (`notes/Phase41-design.md` §3).

## Hand-off / next phase

Item 6 next: `withGraph` restricted to `G' ≤ P.graph` (`def:framework-with-graph`) and `reaim`
deleted, with `rigidityMatrix_prop11`'s `hC` asked only at links. Its commit also writes 5b's sha
into the ledger entries that read "(item 5b)" (`F-122`, `F-123`, `F-125`, `F-126`, `F-128`,
`F-130`, `F-133`, `F-210`, `F-215`, `F-220`, `F-225`, `F-237`, `F-243`), and lowers
`DOCSTRING_LABEL_BASELINE` further if it fixes the two `HingeGeneric.lean` findings left. Items 6
and 7 are the multi-commit trial's next arc (`.claude/commands/coordinate-phase.md` *Multi-commit arcs*;
the PI kept its rules unchanged for two more arcs, 2026-10-24).

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.

- **The build-time detour** (P1–P5; PI): the whole project converted before the spike; `lake lint
  -- X` per file; `lake shake --fix` not applied (`notes/PERFORMANCE.md`).
- **The link predicate** (item 2, 5a): `RecordsLinks G ends` is the field's type, with the forms
  `recordsLinks_iff_forall_isLink`, `_iff_eq_or_swap`, `.of_forall`, `.of_pair`.
- **The field defaults to `:= by link_tac`** (5a; coordinator); the record binders are `hlinks`
  (`hlinks'`, `hlinks₁`, `hlinks₂`; the chain-step defs take it explicitly, TACTICS-QUIRKS § 120).
- **The R statements** (items 3, 3a): `RecordsLinks (G.splitOff …) ends`, four statements.
- **The selector sentences on the status surfaces** (item 5b; coordinator, 2026-10-24): since the
  field, every panel-hinge framework's selector gives each edge of its graph its ends, so the
  surfaces and docstrings no longer say that it is free; they keep the degenerate hinges (the
  all-zero-normals framework at selector `G.endsOf` meets Theorem 5.6 at deficiency zero) and
  `molecular_conjecture`'s nonzero hinge at every label, which RESTATE changes.
