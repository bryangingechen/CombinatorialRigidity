# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Items 1 to 3a, P1 and P2 have landed.
Next concrete task: item P3, the first slice of the project's `module` conversion (layers
0–8); then P4 and P5, then item 4, the spike.

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
restatements are RESTATE's. Before the spike, the PI scheduled a build-time detour (items P1–P5):
each commit's full build is ~5 min and chain-bound (`notes/PERFORMANCE.md` *Build critical
path*), and the switch will need several. P1 trimmed the chain's imports, which shortens the
critical path by 15–20% at fixed module times. P2's recon found that a proof-only edit spares
`module` importers only, so the PI scheduled the whole project's conversion, P3–P5 (*Decisions
made*). Mode: structural edit. There are no red target nodes, so the
red-node consistency gate has nothing to read; the nodes a slice reaches are restated in that
slice (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*).

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
- [ ] **P3. Convert layers 0–8 to `module`** (21 files, 18,964 lines; `python3
  scripts/module-conversion-plan.py --layers`). `--convert` the files, build them alone, and
  fix what breaks (`CombinatorialRigidity/LEAN-OPS.md` *What a conversion breaks*), the trial's
  four fixes first: `import Mathlib.Tactic.Ring` in `Matroid/Constructions/Submodular`, `import
  Mathlib.Algebra.BigOperators.Ring.Finset` in `Union`, `@[expose]` on
  `SimpleGraph.rigidityMatroid`, `setOfPred_minimal_antichain`. Keep the file-wide `@[expose]
  public section` (narrowing was perf-neutral, Phase 9-perf F1); no `backward.privateInPublic`,
  so a `private` declaration that a public statement or exposed body names stops being private.
  Then the full gates; layer 0 is under nearly every file, so the build rebuilds most of the
  tree. If the fixes outrun one builder run, land a prefix of the layers.
- [ ] **P4. Layers 9–18** (23 files, 22,587 lines, up to `Theorem55`), as P3. `link_tac`, a
  `macro`, is in `PanelHinge`.
- [ ] **P5. Layers 19–38** (46 files, 29,202 lines, the root included), as P3. Then measure a
  proof-only and a statement edit at `CaseIII/Realization` against *Build critical path*'s
  figures, in `notes/PERFORMANCE.md`; `lake shake` then runs, and can retire
  `scripts/ImportShake.lean`; `CombinatorialRigidity/CLAUDE.md`, `LEAN-OPS.md` and
  *Module system* stop calling the conversion in progress.
- [ ] **4. The spike** (a throwaway worktree, nothing landed): add the field, build, and list what
  breaks. Record the figure here and slice the switch by it.
- [ ] **5. The switch**: the field; the constructors with the filled-in proof; the H binders (at
  most 56 declarations); `rw [hG]` on graph arguments to `subst`/`simp only`; the footprint's
  docstrings, file by file; `def:panel-hinge-framework` restated (the definition-faithfulness
  gate). May take 2–3 builder runs. Binder order: `chainData_dispatch_interior_of_discriminator`
  (:1751) states `hgp`, on `ofNormals (G.splitOff …) ends q`, before its link hypothesis
  `hrecGab`, and `chainData_dispatch_floor_of_discriminator` (:1943) before `hends'`, so a
  filled-in proof cannot reach them there. The frameworks on `G − v₁` in item 3's statements get
  their record from the splitting-off only through `e₀ ∉ E(G)` (`Graph.removeVertex_le_splitOff`),
  which `link_tac` does not try.
- [ ] **6. `withGraph` restricted** to `G' ≤ P.graph` (`def:framework-with-graph`), and **`reaim`
  deleted**, with `rigidityMatrix_prop11`'s `hC` asked only at links.
- [ ] **7. The two genuine forms merged**: under the field,
  `rankHypothesis_genuine_of_theorem_55_gen` and its link-recording form coincide.
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the 19
  main results' axioms unchanged; RESTATE opens as 41b.

## Blockers / open questions

- The switch's size is unknown until the spike (commit 4).
- The H count (at most 56) is an upper bound from a regex scan.
- The conversion's fix count is a trial's: four fixes in six files of the simplest layers.

## Hand-off / next phase

P3 first: convert layers 0–8 (checklist item P3), one commit, or a prefix of the layers if the
fixes outrun one builder run. Then P4 and P5 the same way. Then item 4, the spike,
in a throwaway worktree with nothing landed: add the field `isLink_ends :
RecordsLinks graph ends` (with `link_tac`'s branch for it and the constructors' `autoParam`), build,
and record here the count of what breaks, by file and by class (T, P, H, R), with item 5's
binder-order note. Then slice item 5, the switch, by that count. Items 6 and 7, after the switch,
are the multi-commit trial's next arc (`.claude/commands/coordinate-phase.md` *Multi-commit arcs*;
the PI kept its rules unchanged for two more arcs, 2026-10-24).

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.

- **A build-time detour before the spike** (PI, 2026-10-24, verbatim: "Let's schedule the
  build-time detour for the next session"). Items P1 (the import trim) and P2 (the `module`
  recon) run before item 4, and so do P3–P5, the conversion P2 led to.
- **The whole project converts to `module`, before the spike** (P2; PI, 2026-10-24, choosing
  "Now, before the spike" over the agent's recommendation, after 41a). A proof-only edit spares
  only `module` importers, the chain's closure is 89 of the 90 files, and the root must convert,
  so the chain's conversion is the project's. The switch's edits change public statements, so
  its builds gain only the smaller import loads. File-wide `@[expose]`, sliced by layer.
- **A per-file lint check before the full build** (P2; PI, 2026-10-24): `lake lint -- X`, in
  `CombinatorialRigidity/CLAUDE.md` *Before each commit — build and lint gates*.
- **The import trim** (item P1). `lake shake` refuses any closure with a non-`module` file, so
  `scripts/ImportShake.lean` does its analysis for them. The trim drops four links from the
  chain an edit at `CaseIII/Realization.lean` rebuilds (26 to 22), 15–20% of the critical path
  at fixed module times; the wall clock was swamped by swap. The 22 links left use each other,
  so imports cannot shorten the chain further.

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
