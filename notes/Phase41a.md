# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Items 1 to 4, the build-time detour P1 to P5, and item 5a,
the switch, have landed. Next concrete task: item 5b, the footprint's docstrings.

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
- [x] **4. The spike**, a throwaway worktree: 123 declarations (100 statements) in 27 of the 32
  carrier files, +418/−139; **H** 65 record binders, **P** 13, **T** 6, **R** 6, 10 graph
  rewrites. The classes: FRICTION *The link field…*.
- [ ] **5. The switch**, two commits:
  - [x] **5a, the switch** (Lean and blueprint): the spike's patch, its ten `SPIKE:` docstrings
    written, the record binders named `hlinks` (*Decisions made*), the docstrings it made false in
    the files it touches (`finrank_span_rigidityRows_pencilConfigFramework`,
    `HasFullRankRealization`, `rigidityRows_ofNormals_relabel`), `def:panel-hinge-framework`'s
    formal note and the selector notes of `panel-layer.tex` restated, two `case-iii.tex` notes
    on new hypotheses; the 31 nodes pinned to a changed statement re-checked. The fix classes:
    FRICTION *The link field…*, lifted to TACTICS-QUIRKS § 120. `case_III_candidate_dispatch`'s
    `hGvGab` stays: `hrecGv₁` uses it by name.
  - [ ] **5b, the footprint's docstrings** (docs only), file by file, with their ledger
    dispositions (*Architectural choices*, *Ledger*), and item 5a's sha written into the
    dispositions of `F-122`, `F-123`, `F-125` and `F-128`, which read "(item 5a)".
- [ ] **6. `withGraph` restricted** to `G' ≤ P.graph` (`def:framework-with-graph`), and **`reaim`
  deleted**, with `rigidityMatrix_prop11`'s `hC` asked only at links.
- [ ] **7. The two genuine forms merged**: under the field,
  `rankHypothesis_genuine_of_theorem_55_gen` and its link-recording form coincide.
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the 19
  main results' axioms unchanged; RESTATE opens as 41b.

## Blockers / open questions

- **The status surfaces' scope sentences are false from 5a** (for the coordinator):
  `molecular_conjecture`'s and `rankHypothesis_of_theorem_55_gen`'s `main_results` rows and three
  `alignment` notes in `formalization.yaml`, README (the molecular conjecture), the home page,
  `intro.tex`'s scope paragraph and ROADMAP §23 say that the panel-hinge framework's selector is
  free, which the field now rules out. RESTATE's table removes them (`notes/Phase41-design.md` §3);
  folding their selector half into 5b would close the window. Their degenerate-hinge half stays
  true until RESTATE.

## Hand-off / next phase

Item 5b next, one builder run, docs only: the footprint's docstrings, file by file (`F-123`,
`F-130`, `F-220` and the parts of `F-122`, `F-126`, `F-133`, `F-210`, `F-215`, `F-225`, `F-237`,
`F-243` that round 3 moved here), each with its ledger disposition, and 5a's sha in the four
"(item 5a)" dispositions; and the blocker above, if the coordinator folds it in. Items 6 and 7 are
the multi-commit trial's next arc (`.claude/commands/coordinate-phase.md` *Multi-commit arcs*;
the PI kept its rules unchanged for two more arcs, 2026-10-24).

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.

- **The build-time detour** (P1–P5; PI, 2026-10-24): the whole project converted before the
  spike ("Now, before the spike"); `lake lint -- X` adopted per file; `lake shake --fix` not
  applied (`notes/PERFORMANCE.md` *Build critical path*).
- **The link predicate's API** (item 2): `RecordsLinks G ends` is the field's type; its forms at
  links are `recordsLinks_iff_forall_isLink` and `recordsLinks_iff_eq_or_swap`, and 5a added the
  total and pair forms (`.of_forall`, `.of_pair`), which `link_tac` tries too.
- **The field defaults to `:= by link_tac`** (item 5a; coordinator, 2026-10-24): the up-front
  choice (*Architectural choices*) applied to structure literals.
- **The record binders are `hlinks`** (item 5a): `hlinks'` for a second in one statement, `hlinks₁`,
  `hlinks₂` where the statement numbers its graphs; the named antecedents and `∃` binders too. The
  chain-step defs take it explicitly (TACTICS-QUIRKS § 120).
- **The R statements** (items 3, 3a): the conjunct is `RecordsLinks (G.splitOff …) ends`, four
  statements, not the recon's five (:1751's `hrecGab` was already on the splitting-off).
