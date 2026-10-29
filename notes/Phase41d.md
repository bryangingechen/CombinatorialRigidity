# Phase 41d — RELABEL: the bound on the edge labels dropped from the main results (work log)

**Status:** in progress (opened 2026-10-29 with the PI), a sub-phase of Phase 41. The phase's
design, the PI's decisions (here §1h.2 and §1i, the open) and RELABEL's recon are in
`notes/Phase41-design.md`; the recon's Lean witness is `notes/reconcile-formal/RelabelWitness.lean`.
Three build items, one read-only recon and the close (planned 7–10); none has landed. Next: item B1,
`embedEdges` moved up with minimality through deficiencies.

## Current state

**The next concrete commit is item B1** (*Hand-off*); no item has landed. RELABEL's recon (design
doc §2, *RELABEL's recon*) proved route B in a witness against `e51acb76`, with no `sorry`: each
main result applies its landed form at `β ⊕ Fin N`, `N = D(|α| − 1) + 1`, where
`Graph.freshEdgeSupply_of_card_lt` gives the supply, and pulls the framework back along `inl`. The
rows, motions, normals and deficiency come back unchanged, minimality transports through
deficiencies, and genericity needs no transport. KT Theorem 5.5's induction keeps `hfresh` inside,
and no proof in it changes. Six main results lose the bound (`hfresh` on Theorem 5.5; `hcard` on
Theorem 5.6, both molecular conjectures, the generic panel rank formula and M1), and 23
declarations' statements lose a hypothesis. **The witness's one uncompiled claim:** the molecule
chain's three declarations (`Theorem56.lean` 2, `Modelling.lean` 1) follow "by grep the same
pattern, not compiled". Mode: structural edit, no red target nodes; each item restates the nodes
it reaches, in step with its Lean.

## Architectural choices made up front

- **Statements change only as §1i and the arc say** (`notes/Reconcile.md` §2, *Hygiene*): each of
  the 23 declarations of the arc's *Which statements change* loses one hypothesis (`hcard` or
  `hfresh`, with `[DecidableEq β]` where only the supply used it), and nothing else in its
  statement moves. A free strengthening only under §1f.3, recorded in the design doc.
- **The induction keeps `hfresh`** (route B): `theorem_55_minimalKDof_k_all_k`,
  `hasGenericFullRankRealization_of_theorem_55_gen`, `theorem_55_6_multigraph_of_two_le`, Cases II
  and III and the chain extraction are untouched. In `Theorem55.lean`, the zone, only the main
  results' statements and the transports after the induction change.
- **The main results keep their names**; the landed supply-taking forms the transports call are
  renamed, under the deletion gate (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*).
- **Each restated main result lands with its non-vacuity witness check** (its witness rebuilt
  against the new statement, the label-headroom argument deleted) and its `formalization.yaml`
  row, in the same commit.
- **Ledger.** Each commit names the ledger IDs it acts on, if any; RELABEL has none of its own (the
  bound is the design doc's §4(b), the PI's §1h.2, not a PROSE finding). One commit per dispatch
  (dispatch-log F53).
- **The witness is the source.** Each build item transcribes
  `notes/reconcile-formal/RelabelWitness.lean` (no `sorry`; compiler-checked at `e51acb76`),
  checking it first with `lake lean` while it still compiles (it calls the landed forms, which B2
  renames), and looks for a shorter route as it goes; a shorter proof that compiles is taken and
  noted in the commit.
- **The loop** runs under §1h.3's configuration, given for 41d (no run cap, mechanical fixups
  pre-authorized, Sonnet and Opus dispatchable), and stops at 41d's close and when the
  coordinator's context runs low (§1i.4); the PI pushes only at Phase 41's close.

## Lemma checklist

The witness proves each Lean statement below in its `Recon41Relabel` namespaces, the bound-free
forms under primed names; an item transcribes it into the library, with its blueprint and status
surfaces.

- [ ] **B1. `embedEdges` moved up, and minimality through deficiencies (T5).** Into
  `Molecular/Deficiency.lean`, beside `Graph.freshEdgeSupply_of_card_lt`: `Graph.embedEdges` from
  `Molecule/Pencil/MainComponent/Bridge.lean` (or defined as the `Matroid` package's
  `Graph.edgeMap` at an embedding, the witness's `embedEdges_eq_edgeMap`) with its graph lemmas
  `Graph.vertexSet_embedEdges`, `Graph.embedEdges_isLink`, `Graph.edgeSet_embedEdges`,
  `Graph.Simple.embedEdges` and `Graph.deficiency_embedEdges`, names kept (the pencil ones,
  `closedNbhd_embedEdges`, `liftingSpace_embedEdges`, `isAdmissiblePicture_embedEdges_iff`,
  `finrank_liftingSpace_embedEdges` and `isMainPicture_embedEdges_iff`, stay in `Bridge.lean`).
  T5, the only new mathematics, about 90 lines: `deficiency_lt_of_isMinimalKDof`,
  `isMinimalKDof_of_deficiency_lt`, `embedEdges_restrict_diff` and `IsMinimalKDof.embedEdges`, by
  KT eq. (2.4) and `matroidMG_restrict_mulTilde`, as `exists_isMinimalKDof_spanning_subgraph`
  argues (every lemma they call is already in `Deficiency.lean`). And the padded supply, the supply
  at `β ⊕ Fin (D(|α| − 1) + 1)` (the witness proves its bound inline, `rw [Nat.card_sum,
  Nat.card_fin]; omega`). No statement changes. Blueprint: `def:pencil-embed-edges` moved to
  `algebraic-induction/panel-layer.tex`, the chapter of `rem:fresh-edge-supply`, its name kept, and
  `fmlnote:pencil-jj-embed-edges` kept coherent with the move. The arc names no node for T5, and
  does not say whether `lem:pencil-jj-embed-edges`'s simplicity and deficiency clauses move too: the
  item's call, recorded in its commit. No `formalization.yaml` row moves. Source: the witness's
  first and T5 sections, transcribed; look for a shorter route. A full rebuild of the molecular
  chain. S/P/B 1/1/2. 1 commit.
- [ ] **B2. The pullbacks and the spine.** T1 and T2 after the induction, in
  `AlgebraicInduction/Theorem55.lean` or a file it imports that imports `PanelHinge.lean` (not
  `RigidityMatrix/Basic.lean` or `PanelHinge.lean`, which would rebuild the chain): `bhComap` with
  `bhComap_rigidityRows` (an equality of sets) and `bhComap_infinitesimalMotions`, and `phComap`
  (the normals kept, the selector `P'.ends ∘ ι`, its link field three lines) with
  `phComap_toBodyHinge`. Then the spine's five transports, each 10–20 lines: the landed form at
  `β ⊕ Fin N`, pulled back.
  - `PanelHingeFramework.theorem_55_minimalKDof_gen` (KT Theorem 5.5): `hfresh` dropped;
    `[DecidableEq β]` stays, for `IsMinimalKDof`.
  - `PanelHingeFramework.rankHypothesis_genuine_of_theorem_55_gen` and
    `PanelHingeFramework.finrank_span_rigidityRows_genuine_recordsLinks_of_theorem_55_gen`: `hfresh`
    and `[DecidableEq β]` dropped (only the supply used it; the linter flags it).
  - `PanelHingeFramework.rankHypothesis_of_theorem_55_gen` (KT Theorem 5.6) and
    `theorem_55_6_multigraph_gen`: `hcard` dropped. `[Finite β]` stays everywhere, as `β ⊕ Fin N`
    must be finite.
  - **Placed by neither the arc's steps nor the witness:** `theorem_55_6_multigraph`, the `k`-form
    with `hfresh` that the landed `_gen` calls, is one of the 23. B2 drops its `hfresh` with the
    spine (its own transport, as the genuine form's, or derived from the bound-free `_gen`): the
    item's call, recorded in its commit.

  The main results keep their names; the landed supply-taking forms are renamed (the new names are
  the item's). **The deletion gate:** grep the whole repo for each of the five names and repoint,
  in the same commit, every reference that means the supply-taking form: the transports, the
  callers that keep their binder until B3 (the `d = 3` forms, the conjectures, the generic
  theorems, `Theorem56.lean`), docstrings and notes. In `Bridge.lean`,
  `Graph.exists_mvPolynomial_le_finrank_span_rigidityRows_pencilPicturePoint`
  (`lem:pencil-jj-chart`) keeps `hfresh` and calls the renamed rows form (no pencil row moves).
  The evidence files in `notes/reconcile-formal/` check against the commits their headers name and
  are not repointed (none has been after a later restatement). Non-vacuity: `theorem_55_minimalKDof_gen_witness` and
  `rankHypothesis_of_theorem_55_gen_witness` (`CombinatorialRigidity/Nonvacuity.lean`) without the
  label headroom `3 · (2 − 1) < 4` and their docstrings' sentence on it; the two `formalization.yaml`
  rows re-read (neither names the bound today). Blueprint, the changed-statement gate:
  `thm:theorem-55`, `thm:theorem-55-6-genuine`, `thm:theorem-55-6`, `thm:theorem-55-6-rows` and
  `thm:theorem-55-6-multigraph` (both pins) restated where they or their notes state the bound;
  `rem:fresh-edge-supply`'s list loses these nodes (B3 rewrites the remark);
  `fmlnote:pencil-jj-embed-edges`'s "the formal case `d = 2` of KT Theorem 5.6 assumes a supply"
  restated. `python3 scripts/check-docstring-labels.py` diffed against the parent (the moved-pin
  gate): a renamed form whose docstring names its old node is a finding unless the node pins it
  too. Source: the witness's T1, T2 and spine sections, transcribed; look for a shorter route.
  Zone (`Theorem55.lean`), statements and new transports only. S/P/B 1/1/2. 1–2 commits; if it
  splits, cut between Theorem 5.5 and the forms of Theorem 5.6.
- [ ] **B3. The cascade and the texts.** In each declaration below the binder is deleted and the
  call switched to the bound-free form; nothing else in its proof changes (the witness's copies).
  - `Theorem55.lean`: the `d = 3` forms `theorem_55_minimalKDof_k`, `theorem_55_d3`,
    `rankHypothesis_deficiency_of_theorem_55_d3`, `rankHypothesis_of_theorem_55_d3` and
    `theorem_55_6_multigraph_d3`; the conjectures `PanelHingeFramework.molecular_conjecture` and
    `molecular_conjecture_multigraph` (the witness's `molecular_conjecture'` and
    `molecular_conjecture_multigraph'`).
  - `GenericLift/PanelGeneric.lean` (2): `finrank_span_rigidityRows_of_isGenericNormals` and
    `isInfinitesimallyRigidOn_of_isGenericNormals_iff`.
  - `GenericLift/HingeGeneric.lean` (5): `exists_hingePoints_independent_hingePointRow`,
    `finrank_span_rigidityRows_ofHinge_of_isGenericHingePoints`,
    `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff`,
    `isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees` (M1) and
    `tfae_finrank_span_rigidityRows_ofHinge_deficiency` (KT Proposition 2.3). The witness restates
    the private `hingeRow_smul` as `hingeRow_smul'` only because it sits outside the file.
  - `Molecule/Theorem56.lean` (2): `exists_rankHypothesis_isGeneralPosition4` and
    `exists_rankHypothesis_isGeneralPosition4_of_two_le`; `Molecule/Modelling.lean` (1):
    `exists_molecular_rankHypothesis_generalPosition`. **Not compiled by the witness** ("by grep
    the same pattern"): compile them first; a surprise is a BLOCKED return, not an improvised
    change.
  - The callers: `CombinatorialRigidity/Nonvacuity.lean` (the witnesses of the M1, panel-rank and
    multigraph-conjecture rows, their `hcard` and their docstrings' headroom sentences),
    `Molecular/AlgebraicInduction/Nonvacuity.lean` (`molecular_conjecture_witness`, its
    `3 · (1 − 1) < 1`) and `Molecule/Application.lean` (`molecule_rank_lower_bound`, the one
    caller of `card_shadowLabel_lt`). `G.shadowGraph`'s padding stays: dropping it would move
    `lem:molecule-graph-carrier` and UNSTATED's U10; `Molecule/Carrier.lean`'s docstrings, which
    give the padding as the bound's, say what it is for once nothing needs it.

  Blueprint: `rem:fresh-edge-supply` rewritten (the supply is now an assumption of the induction's
  internal forms and of `thm:minimal-kdof-reduction`; the main results relabel at the boundary,
  `def:pencil-embed-edges` with T5), the statements and fmlnotes that state the bound at the arc's
  other nodes (`thm:theorem-55-d3-instance`, `cor:theorem-55-d3-spanning`, `thm:theorem-55-6-d3`,
  `cor:theorem-55-6-multigraph-d3`, `thm:molecular-conjecture`,
  `thm:molecular-conjecture-multigraph`, `thm:panel-generic-rank`, `cor:panel-generic-rigid`,
  `thm:bodyhinge-generic-rank`, `cor:bodyhinge-generic-rigid`,
  `cor:bodyhinge-generic-tree-packing`, `prop:rigidity-matrix-prop11`,
  `thm:panel-hinge-iff-molecular`, `lem:hinge-point-witness`, `lem:theorem-56-general-position`)
  and `rem:molecular-conjecture-nonvacuous`; `lem:pencil-jj-chart` keeps `hfresh`, as its caller
  relabels already. Status: `formalization.yaml`'s M1 and panel rows ("more than D(|V|−1) edge
  labels", "given enough labels"), the JJ 6.1 and 7.2 alignment notes and the fidelity summary's
  last sentence, with the two conjecture rows re-read (neither names the bound today); README's and the home page's "given more edge labels than `D(|V|−1)`",
  `intro.tex`'s two sentences that cite `rem:fresh-edge-supply`, and ROADMAP's BH paragraph.
  Source: the witness's cascade sections, transcribed (all but the molecule chain); look for a
  shorter route. S/P/B 1/1/2, the molecule chain's three uncompiled. 1–2 commits; if it splits, cut
  between `Theorem55.lean` with the molecule chain and the generic theorems with the texts.
- [ ] **R. Recon: dropping `hfresh` from `minimal_kdof_reduction`** (read-only; the PI's §1i.3).
  `Graph.minimal_kdof_reduction` (`Induction/ForestSurgery/Reduction.lean`;
  `thm:minimal-kdof-reduction`, KT Theorem 4.9's principle) is not a main result, and no
  declaration uses it (the algebraic induction runs `minimal_kdof_reduction_all_k`, which takes no
  supply). Route B cannot reach it: its split step names a fresh label for a predicate on
  `Graph α β`, so no pullback applies. The recon sizes route A's combinatorial half, the
  deficiency chain re-proved under the weaker `e₀ ∉ E(G − v)` (the split-off recycling one of
  `v`'s two edge labels), through `splitOff_isMinimalKDof_of_pos` and
  `circuit_splitOff_meets_fiber` (`Reduction.lean`), `dof_tracking` (`SplitOffDeficiency.lean`),
  `edgeSet_mulTilde_splitOff_diff_fiber` (`EdgeSplitting.lean`) and `removeVertex_le_splitOff`
  (`Operations.lean`), as the arc names them, and `splitOff_isMinimalKDof`, the `k = 0` step that
  the principle itself calls. Its questions: which of these use `e₀ ∉ E(G)` beyond
  `e₀ ∉ E(G − v)`; how `hsplit`'s premise `e₀ ∉ E(G)` restates; what then happens to UNSTATED's
  U4 (`minimal_kdof_reduction_sequence`, which carries `hfresh` as the principle does); and the
  estimate in commits. Its verdict is recorded as a §2 arc of the design doc in one docs commit,
  as RELABEL's recon was (`fb566765`), with any Lean evidence in `notes/reconcile-formal/`; no
  library Lean changes, and no build follows before the PI decides. Placed last, so that its
  question reaches the PI at the stop between sub-phases. Off the S/P/B axes: a recon.
- [ ] **Close**: the gates (whole-project build with 0 warnings, `lake lint`, the blueprint gates,
  the 20 main results' axioms), the re-read of the restated chapters, ROADMAP's row and §41, the
  design doc's RELABEL arc compressed to a cited verdict, UNSTATED named next (expected as 41e).
  The loop stops for the PI (§1i.4), with R's question; no push (the PI pushes at Phase 41's
  close).

## Blockers / open questions

- None blocking. Two flags for the builders: `theorem_55_6_multigraph` is one of the 23 but is in
  neither the witness nor the arc's steps (B2 places it); and the molecule chain's three
  declarations are uncompiled in the witness (B3 compiles them first).
- For the PI at the close: item R's estimate for dropping `hfresh` from `minimal_kdof_reduction`.

## Hand-off / next phase

**Item B1**: move `Graph.embedEdges` and its five graph lemmas up to `Deficiency.lean`, beside
`freshEdgeSupply_of_card_lt`, add T5 and the padded supply as the witness's sections do, and move
`def:pencil-embed-edges` to `panel-layer.tex`. One whole-project build (the molecular chain
rebuilds); no statement changes. Then B2, which transcribes the witness's pullbacks and spine.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-29): `notes/Phase41-design.md` §1i, verbatim.
- **Route B, not route A** (RELABEL's recon, design doc §2): recycling a label inside the
  induction breaks at Case III's chain (`ChainData.e₀_fresh`, one fresh label for every interior
  split-off); the transport at the boundary leaves the induction untouched.
