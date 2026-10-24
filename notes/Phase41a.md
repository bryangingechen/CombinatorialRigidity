# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Items 1 to 3a have landed. Next concrete task: item 4,
the spike, in a throwaway worktree with nothing landed.

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
restatements are RESTATE's. Mode: structural edit. There are no red target nodes, so the
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

- [x] **1. Retire `reaimSub`** (`Theorem55.lean` only). Move
  `rankHypothesis_genuine_of_theorem_55_gen` (:2179) below
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (:2272) and prove it from that form by
  dropping its link conjunct. Delete the private `reaimSub` (:846) and
  `reaimSub_withGraph_infinitesimalMotions` (:860). Repoint the docstrings that name it (:873–878,
  :2259, :2267, :2520). No statement or pin changes.
- [x] **2. The link predicate** with its graph-operation lemmas: one name for "the selector records
  every link of `G`", gathering `Graph.isLink_update_splitOff` (`Short.lean:341`),
  `Graph.isLink_ends_induce` (`Cut.lean:172`), `recordsLinks_map_of_records` (`CaseI.lean:52`) and
  `recordsLinks_swap_endsOf` (`Coupling.lean:66`), plus `recordsLinks_mono` and the fill-in tactic.
  Landed as `RecordsLinks.update_splitOff`, `.induce`, `.map`, `.swap_endsOf`, `.mono` and
  `link_tac`; all four moved, none left in place.
- [x] **3. The four R statements** in `CaseIII/Realization.lean` (:823, :1330, :1430, :1943):
  the link conjunct on the splitting-off, not `G − v`. :1430 is pinned to
  `lem:case-III-chain-discriminator`, whose statement is restated if it reaches it. The recon's
  fifth, :1751, is not one: its selector hypothesis `hrecGab` is already on the splitting-off.
  Landed: the conjunct of :823, :1330 and :1430 and the hypothesis `hends'` of :1943 are
  `RecordsLinks (G.splitOff …) ends`. The node never states the selector, so it is unchanged.
- [x] **3a. Item 3's duplicate conjuncts** (coordinator verification, 2026-10-24). The three
  strengthened conclusions in `CaseIII/Realization.lean` (now :854, :1349, :1444) state
  `RecordsLinks (G.splitOff …) ends` beside the equivalent up-to-order conjunct
  `∀ e u w, (G.splitOff …).IsLink e u w → ends e = (u, w) ∨ ends e = (w, u)`
  (`recordsLinks_iff_eq_or_swap`). Keep `RecordsLinks`, drop the up-to-order conjunct, and
  repair the callers' destructuring. No blueprint node states either conjunct.
  Landed: the conjunct is gone from all three; `chainData_dispatch` gives :1751's `hrecGab` from
  `RecordsLinks.eq_or_swap`. The two pinned nodes (:1430's and `chainData_dispatch`'s) state
  neither form.
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

## Hand-off / next phase

Item 4, the spike, in a throwaway worktree with nothing landed: add the field `isLink_ends :
RecordsLinks graph ends` (with `link_tac`'s branch for it and the constructors' `autoParam`), build,
and record here the count of what breaks, by file and by class (T, P, H, R), with item 5's
binder-order note. Then slice item 5, the switch, by that count.

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.

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
