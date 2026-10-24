# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Items 1 to 4 and the build-time detour, P1 to P5, have
landed. Next concrete task: item 5, the switch, as one commit from the spike's patch.

## Current state

Opened with the PI on 2026-10-24, after the design recon (`notes/Phase41-design.md` §2). Item 1
retired `reaimSub`: `rankHypothesis_genuine_of_theorem_55_gen` is now the link-recording form with
its link conjunct dropped, so both Theorem-5.6 assemblies (the genuine and the row-rank forms)
re-add through `reaimSubLink`. Item 2 added the link predicate `PanelHingeFramework.RecordsLinks`
(`PanelHinge.lean`, above the structure) with its lemmas and the fill-in tactic `link_tac`, and
gathered the four scattered link lemmas onto it (*Decisions made*). Item 3 moved the R statements'
link conjunct from `G − v` to the splitting-off, and item 3a dropped the up-to-order conjunct
that then restated it. The sub-phase builds S2's field `isLink_ends` into the carrier (design A,
`notes/Phase41-design.md` §1.1) and leaves every main result's statement as it is: the
restatements are RESTATE's. Before the spike, the PI scheduled a build-time detour (items P1–P5),
since each commit's full build took ~5 min: P1 trimmed the chain's imports, and P3–P5 converted
the whole project to `module`. A proof-only edit at `CaseIII/Realization` now rebuilds that file
alone (10–14 s), and a statement edit rebuilds 48 modules in 72–77 s (*Decisions made*). Item 4,
the spike, built the whole switch in a throwaway worktree: sorry-free, 0 warnings, `lake lint`
clean, 123 declarations in 27 files. Its patch is kept locally (`scratch/41a/spike.patch`,
gitignored) and item 5 lands it. Mode: structural edit.
There are no red target nodes, so the red-node consistency gate has nothing to read; the nodes a
slice reaches are restated in that slice (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*).

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

- [x] **1. Retire `reaimSub`**: `rankHypothesis_genuine_of_theorem_55_gen` is proved from its
  link-recording form; `reaimSub` and its lemma are deleted.
- [x] **2. The link predicate** `RecordsLinks`, with `.update_splitOff`, `.induce`, `.map`,
  `.swap_endsOf`, `.mono` and `link_tac`; the four scattered link lemmas moved onto it.
- [x] **3. The four R statements** in `CaseIII/Realization.lean`: the link conjuncts of :823,
  :1330 and :1430, and :1943's hypothesis `hends'`, are `RecordsLinks (G.splitOff …) ends`; no
  node restated.
- [x] **3a. Item 3's duplicate conjuncts**: the up-to-order conjunct is gone from all three;
  `chainData_dispatch` gets `hrecGab` from `RecordsLinks.eq_or_swap`.
- [x] **P1. The import trim**: 36 files, 42 imports removed and 33 added, by
  `scripts/ImportShake.lean` (`notes/PERFORMANCE.md` *The import trim*).
- [x] **P2. The `module` recon** (`notes/PERFORMANCE.md` *The `module` conversion recon*): a
  proof-only edit spares only `module` importers; 90 files in 39 layers; `lake lint -- X`
  adopted; the PI chose to convert now (*Decisions made*).
- [x] **P3. Layers 0–8 to `module`** (21 files): four files needed fixes, a private name in a
  public body among them (`notes/PERFORMANCE.md` *The conversion, layers 0–8*).
- [x] **P4. Layers 9–18 to `module`** (23 files): two files unfolded mathlib's
  `Graph.deleteVerts` by a bare `exact` (`notes/PERFORMANCE.md` *The conversion, layers 9–18*).
- [x] **P5. Layers 19–38 to `module`** (46 files, the root included), and the measurement:
  every file is a `module`; three files needed fixes (`notes/PERFORMANCE.md` *The conversion,
  layers 19–38*).
- [x] **4. The spike** (worktree under `scratch/41a/`, removed; nothing landed): with the field, the
  whole project builds, 0 warnings, `lake lint` clean, no `sorry`; the 39 results of
  `formalization.yaml` use the three standard axioms only. 27 of the 32 carrier files, +418/−139
  lines, 123 declarations (100 statements). By class (they overlap): core 20 in `PanelHinge.lean`
  (the field, `link_tac`, 3 constructors, 10 simp lemmas, 5 new lemmas); **H 65** (the scan's bound
  of 56 was low): an implicit record binder in 58 (an autoParam in 4, an explicit argument in the 3
  chain-step defs), which callers fill by unification but for 7 cascades (a named argument at one
  caller, two for the chain-step defs); 6 are `G − v` frameworks no hypothesis records; **P** 13;
  **T** 6 (a named arrow antecedent); `rw`/`▸` on a graph argument 10 (of ~71 such lines); **R** 6;
  binder order 2 (:1751, :1943, confirmed); literals 3. By file: `PanelHinge` 28, `Candidate` 16,
  `Realization` 11, `Theorem55` 9, `Relabel/Basic` 8, `Relabel/Chain` 6, `Duality` 5, `CaseI` 5,
  `Coupling` 4, `Bridge` 4, `ForkedArm` 3, sixteen files 2 or 1 (`scratch/41a/sites.tsv`, local).
- [ ] **5. The switch**: its Lean side is one commit, since every H binder needs the field (unused,
  it fails `unusedArguments`) and the H binders are most of the diff. Two commits, one builder run
  each:
  - **5a, the switch** (Lean and blueprint): `git apply scratch/41a/spike.patch` (or redo it from
    item 4 and the fix list below); replace its ten `SPIKE:` docstrings (the field, `link_tac` and
    its two helpers, the six new lemmas: `RecordsLinks.of_forall`, `.of_pair`, `.of_split`,
    `.congr`, `ofNormals_eq_self_of_graph_eq`, `recordsLinks_splitOff_relabel`); give the new
    binders one name; restate `def:panel-hinge-framework` (definition-faithfulness gate) and
    re-check the ~28 nodes pinned to a changed statement; FRICTION entries for the classes below.
  - **5b, the footprint's docstrings** (docs only), file by file, with their ledger dispositions,
    and the docstrings the switch made false (e.g.
    `finrank_span_rigidityRows_pencilConfigFramework`, "asks nothing of ends").
  - A field-independent commit before 5a (the new lemmas, `link_tac`'s branches, the R reorders,
    the binder-order swaps) is possible, about a fifth of the diff; not recommended, as its named
    but unused binders would need the linters checked before the field exists.
  - **The fixes, by class** (the spike's, for a builder who redoes it): the field itself defaults to
    `by link_tac`, so the constructor bodies and `where` literals need no edit; `link_tac` becomes
    `syntax` plus `macro_rules` after the structure (hygiene), tries the hypothesis forms before
    `P.isLink_ends` in its `mono` branch (one alternative per form), and gains the total and pair
    forms, `update_splitOff`, `induce`, `map`, and `removeVertex_le_splitOff` (from `he₀` or
    `ChainData.e₀_fresh`), which reach the `G − v₁` frameworks; it must return a term typed
    `RecordsLinks …`, or a later `rw` fails at instance transparency. New classes: an anonymous
    arrow antecedent is out of scope (name it); a conjunct cannot serve an earlier one (R: the
    record becomes an `∃` binder first, pattern-compatible when it was already first); an autoParam
    on a function-valued def swallows the applied argument (`shiftBodyFrameworkAscTotal`: an
    explicit record argument); an implicit record binder is not inferred by `have := lemma …`, by
    `rw [← lemma]` or `simp [lemma]` when it sits on one side only, or behind `?_` holes (pass it by
    name); `rw [← hQg]; rfl` becomes `ofNormals_eq_self_of_graph_eq`, and `rw`/`▸` under a framework
    becomes `rw` on the whole term or `simp only`.
- [ ] **6. `withGraph` restricted** to `G' ≤ P.graph` (`def:framework-with-graph`), and **`reaim`
  deleted**, with `rigidityMatrix_prop11`'s `hC` asked only at links.
- [ ] **7. The two genuine forms merged**: under the field,
  `rankHypothesis_genuine_of_theorem_55_gen` and its link-recording form coincide.
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the 19
  main results' axioms unchanged; RESTATE opens as 41b.

## Blockers / open questions

- None. The spike's patch is local and gitignored; if it is lost, item 4 and item 5's fix list
  redo it.

## Hand-off / next phase

Item 5a next, one builder run: apply `scratch/41a/spike.patch`, write the docstrings its `SPIKE:`
markers hold, restate `def:panel-hinge-framework`, re-check the nodes pinned to changed statements,
and land the switch after `lake build` (0 warnings) and `lake lint`; the spike took 15 build-and-fix
rounds. Then 5b, the footprint's docstrings. Items 6 and 7, after the switch, are the multi-commit
trial's next arc (`.claude/commands/coordinate-phase.md` *Multi-commit arcs*; the PI kept its rules
unchanged for two more arcs, 2026-10-24).

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.

- **The build-time detour, done** (items P1–P5; PI, 2026-10-24, verbatim: "Let's schedule the
  build-time detour for the next session"). P1 trimmed the chain's imports (26 links to 22,
  `scripts/ImportShake.lean`); P2's recon led the PI to convert the whole project before the
  spike ("Now, before the spike", over the agent's after-41a); P3–P5 did it, with the file-wide
  `@[expose]`. Measured at `CaseIII/Realization`: a proof-only edit 10–14 s, a statement edit
  72–77 s, against ~5 min (`notes/PERFORMANCE.md` *The conversion, layers 19–38*).
- **A per-file lint check before the full build** (P2; PI, 2026-10-24): `lake lint -- X`, in
  `CombinatorialRigidity/CLAUDE.md` *Before each commit — build and lint gates*.
- **`lake shake --fix` not applied** (P5): it proposes edits to 151 files; the PI's call, lever 4
  of `notes/PERFORMANCE.md` *Build critical path*.

- **The link predicate's API** (item 2). `RecordsLinks G ends` is `∀ e ∈ E(G), G.IsLink e (ends
  e).1 (ends e).2`, so the field of item 5 is it by `Iff.rfl`. Its two forms at links are
  `recordsLinks_iff_forall_isLink` (the tree's `hends`) and `recordsLinks_iff_eq_or_swap`
  (`HasGenericFullRankRealization`'s conjunct); `.isLink` and `.eq_or_swap` apply it at one link,
  `.of_isLink_imp` is the core of `.mono` and `.induce`. `link_tac` tries a hypothesis in either
  form, `recordsLinks_endsOf`, and `.mono` with `G' ≤ G` in scope; item 5 adds a branch for the
  field. The callers convert their link-form `hends` (FRICTION [open] *The tree's link
  hypotheses are in the form at links…*), which the H binders of item 5 can avoid.
- **The R statements** (item 3). The strengthened conjunct takes the predicate form,
  `RecordsLinks (G.splitOff …) ends`. In :823, :1330 and :1430 it restated the last conjunct
  (the same record, up to order, `recordsLinks_iff_eq_or_swap`), which item 3a dropped. R is
  4, not the recon's 5: :1751's only selector hypothesis, `hrecGab`, was already on the
  splitting-off (the `G − v` links in its `hedgeGv` are of the edges `evGv`, not of `ends`), so
  it is unchanged. :1943 derives the record on `G − v₁` by `.mono` and
  `Graph.removeVertex_le_splitOff`.
