# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Items 1 and 2 have landed. Next concrete task: item 3 below
(the five R statements), the second commit of the multi-commit arc that landed item 2
(`.claude/commands/coordinate-phase.md` *Multi-commit arcs*).

## Current state

Opened with the PI on 2026-10-24, after the design recon (`notes/Phase41-design.md` §2). Item 1
retired `reaimSub`: `rankHypothesis_genuine_of_theorem_55_gen` is now the link-recording form with
its link conjunct dropped, so both Theorem-5.6 assemblies (the genuine and the row-rank forms)
re-add through `reaimSubLink`. Item 2 added the link predicate `PanelHingeFramework.RecordsLinks`
(`PanelHinge.lean`, above the structure) with its lemmas and the fill-in tactic `link_tac`, and
gathered the four scattered link lemmas onto it (*Decisions made*). The sub-phase builds S2's field `isLink_ends` into the carrier (design A,
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
- [ ] **3. The five R statements** in `CaseIII/Realization.lean` (:823, :1330, :1430, :1751,
  :1943): the link conjunct on the splitting-off, not `G − v`. :1430 is pinned to
  `lem:case-III-chain-discriminator`, whose statement is restated if it reaches it.
- [ ] **4. The spike** (a throwaway worktree, nothing landed): add the field, build, and list what
  breaks. Record the figure here and slice the switch by it.
- [ ] **5. The switch**: the field; the constructors with the filled-in proof; the H binders (at
  most 56 declarations); `rw [hG]` on graph arguments to `subst`/`simp only`; the footprint's
  docstrings, file by file; `def:panel-hinge-framework` restated (the definition-faithfulness
  gate). May take 2–3 builder runs.
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

Item 3, the five R statements in `CaseIII/Realization.lean`: strengthen each link conjunct from
`G − v` to the splitting-off, whose links the proof's `Q.ends` already records, and repair the
callers; the conjunct pinned to `lem:case-III-chain-discriminator` restates that node if its text
states the old form. Then item 4, the spike.

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
