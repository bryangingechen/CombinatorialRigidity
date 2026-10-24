# Phase 41a — CARRIER: the link condition as a field of `PanelHingeFramework` (work log)

**Status:** in progress (opened 2026-10-24). The phase's design, the PI's decisions and the open's
recon are in `notes/Phase41-design.md`. Next concrete task: commit 1 below, retiring `reaimSub`
in `Theorem55.lean` with no statement or pin changed.

## Current state

Opened with the PI on 2026-10-24, after the design recon (`notes/Phase41-design.md` §2). No Lean has
changed yet. The sub-phase builds S2's field `isLink_ends` into the carrier (design A,
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

- [ ] **1. Retire `reaimSub`** (`Theorem55.lean` only). Move
  `rankHypothesis_genuine_of_theorem_55_gen` (:2179) below
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (:2272) and prove it from that form by
  dropping its link conjunct. Delete the private `reaimSub` (:846) and
  `reaimSub_withGraph_infinitesimalMotions` (:860). Repoint the docstrings that name it (:873–878,
  :2259, :2267, :2520). No statement or pin changes.
- [ ] **2. The link predicate** with its graph-operation lemmas: one name for "the selector records
  every link of `G`", gathering `Graph.isLink_update_splitOff` (`Short.lean:341`),
  `Graph.isLink_ends_induce` (`Cut.lean:172`), `recordsLinks_map_of_records` (`CaseI.lean:52`) and
  `recordsLinks_swap_endsOf` (`Coupling.lean:66`), plus `recordsLinks_mono` and the fill-in tactic.
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

Commit 1: retire `reaimSub` in `Theorem55.lean` (checklist item 1). It is needed under every
design and changes no statement, pin or blueprint node.

## Decisions made during this phase

The decisions of the open are `notes/Phase41-design.md` §1.
