# Phase 41b — RESTATE: the main results restated on the linked carrier (work log)

**Status:** in progress (opened 2026-10-24), a sub-phase of Phase 41. The phase's design, the PI's
decisions (at the phase's open, §1; at this sub-phase's, §1b; after item 1's recon, §1c; on
`F-330`, §1d; on the generic panel theorems' body bound, §1e; in advance, §1f) and the recons are in
`notes/Phase41-design.md`. Items 1–12 done: Theorems 5.5 and 5.6, and their `d = 3`
instances, conclude KT's nonparallel panels for simple `G`, `molecular_conjecture` holds on one
body with nonparallel panels on its panel side, the multigraph rows ask nondegeneracy on `E(G)`,
the `d = 3` spanning corollary derives from `theorem_55_d3`, the generic panel and body-hinge
theorems hold at every generic realization on `G`, one body or more (rows witnessed at the single
edge and the triangle), the status surfaces say so, and KT Proposition 2.3 is stated as KT state
it, in conditional form. The close's re-read is done, its two false sentences fixed in a commit of
their own. Next concrete task: the close.

## Current state

Opened with the PI on 2026-10-24, after the RESTATE open's recon (`notes/Phase41-design.md` §2,
*RESTATE's open recon*). The sub-phase restates S2's and S1's main results on the carrier to which
41a gave the link field, and acts on the PI's decisions at its open (§1b) and after item 1's recon
(§1c). So far: `HasGenericFullRankRealization` lost its link conjunct (item 2); the derivable `hD`
chain is gone (item 3); KT's nonparallel panels are `IsNonparallel` (item 4a); a generic full-rank
realization gives a nonparallel one (item 4b, route B); Theorem 5.5's simple conjunct states it
(item 4c); and Theorem 5.6, its genuine form and the d = 3 wrapper conclude it, the link conjuncts
of the rows form and the wrapper gone (item 5). The d = 3 instance of Theorem 5.6 passes the
conjunct through too (item 5b, `F-329`). `molecular_conjecture` takes `V(G).Nonempty` and asks
nondegenerate hinges on `E(G)` only (item 6), its panel side from Theorem 5.6's nonparallel panels.
The multigraph rows are restated: `molecular_conjecture_multigraph`'s body-hinge side asks nonzero
hinges on `E(G)`, `IsHingeCoplanar` constrains `E(F.graph)` only, both lose `[DecidableEq β]` (item
7). The `d = 3` spanning corollary derives from `theorem_55_d3`, concluding nonparallel panels and
nondegenerate hinges on `E(G)` (item 8). Item 9's design pass (`notes/Phase41-design.md` §2,
*Item 9's recon*) compiled the restated panel theorems in
`notes/reconcile-formal/PanelGenericWitness.lean` and split the item into 9a (the restatement) and
9b (G6's row). Item 9a restated `PanelGeneric.lean`: genericity is the framework's, over the rows at
the edges of its graph; the rank formula and its iff range over every framework on `G` with generic
normals, under Theorem 5.6's `hd`, `hcard` and, by the PI's §1e, `V(G).Nonempty`; their witness is
Theorem 5.6's main form. Item 9b made the rank formula a `main_results` row, witnessed at the
single edge, and narrowed the S1 scope sentences to the body-hinge theorem. The PI answered four
questions in advance (§1f): item 11's form, the stop at RESTATE's close, free strengthenings, M1's
loops. Item 10's design pass (design doc §2, *Item 10's recon*) compiled the restated body-hinge
theorems in `notes/reconcile-formal/HingeGenericWitness.lean` and split the item into 10a and 10b.
Item 10a restated `HingeGeneric.lean` from it: genericity is over `G`, for the rows at its edges at
every selector that records its links; the rank formula and its two corollaries hold at every
generic assignment, on one body or more (§1f.3), under `hcard`, from Theorem 5.6's main form; the
row is witnessed at the triangle. Items 10b and 12, merged into one commit (*Decisions made*),
restated the status surfaces: the scope sentences (README, home page, `intro.tex`, ROADMAP §34)
say that both generic theorems cover every simple graph on one body or more, given enough labels,
the simple minimal graphs included; the degenerate-hinge sentences (the same and ROADMAP §23) say
that Theorems 5.5 and 5.6 give nonparallel panels. `molecular_conjecture`'s docstring and the
prose before its node no longer say that, without the hinge conjunct, each side holds exactly for
connected `G`, false since 6b (`F-130`); of the footprint's docstrings (`F-123`, `F-130`, `F-220`)
none other is left false. Item 11 restated `prop:rigidity-matrix-prop11` as KT state Proposition
2.3, for a body-hinge framework on a multigraph, in conditional form (the bound on the motions
gives the formula), as its pin already proved; the subsection's opening says where the bound holds,
and the pin's docstrings name KT Proposition 2.3, not 1.1. The close's end-to-end re-read of the
restated nodes, in the nine chapter files 41b touched, found no per-commit narration and two false
sentences in `panel-layer.tex`, each left by an earlier item. The prose before `thm:theorem-55`
said that it states a generic full-rank realization of a simple graph, which it states as
nonparallel since item 4c; the prose before `thm:molecular-conjecture-multigraph` said that the
simple case follows from `thm:theorem-55-6-genuine`, which it has followed from `thm:theorem-55-6`
since item 6. Both were fixed in a commit of their own, with `HasCoplanarPanelRealization`'s
docstring (`F-133`'s last process code) and `c26edc57` in the ledger's item-11 dispositions. Next:
the close. Mode: structural edit. There are no red target nodes; each slice restates the nodes it
reaches (`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*).

## Architectural choices made up front

- **Statements change only as the design doc's §1 and §1b–§1f say** (`notes/Reconcile.md` §2,
  *Hygiene*): any other statement change is recorded as an `S` entry and not acted on, except a
  conclusion strengthened at no proof cost or a hypothesis relaxed that the proof does not need,
  which the coordinator may adopt under the PI's standing policy, "Adopt, record it" (design doc
  §1f.3: only the theorem at hand, an approved pattern, recorded there). A prompt that bars an
  edit names the neighbouring edits it allows (dispatch-log F51).
- **Each restated main result lands with its non-vacuity witness** in
  `CombinatorialRigidity/Nonvacuity.lean` (`PHASE-BOUNDARIES.md` *When this commit closes a
  phase*); its `formalization.yaml` row follows in the same commit.
- **Ledger.** Each commit names the ledger IDs it acts on (S2: `F-122`, `F-125`, `F-128`; S1:
  `F-207`, with `F-206`, `F-216`, `F-221`; `F-126`, `F-323`, `F-324`) and gives each entry its
  `done (<sha>)` disposition (`notes/Reconcile.md` §2).
- **One commit per dispatch** (dispatch-log F53). PI entries are never compressed (F50).

## Lemma checklist

Item 1's verdict keeps item 4 after items 2 and 3 and before item 5.

- [x] **1. Recon: KT's nonparallel** (§1b.4): route B, design doc §2; witness `NonparallelWitness.lean`.
- [x] **2.** `HasGenericFullRankRealization`'s last conjunct (`376e3ac3`). **3.** `F-324`: twelve
  derivable `hD`s gone (`b2d0839a`).
- [x] **4a–4c.** `IsNonparallel` (`2c502d08`); nonparallel from generic (`39bc341c`); Theorem 5.5's
  simple conjunct is `HasNonparallelFullRankRealization` (`4960364d`).
- [x] **5, 5b.** Theorem 5.6, its genuine form, the rows form, the wrapper and the `d = 3` instance
  conclude `IsNonparallel`, the link conjuncts gone (`5c70542c`, `da20d498`; `F-323`, `F-329`).
- [x] **6, 6b.** `molecular_conjecture` on `V(G).Nonempty`, hinges on `E(G)`, panel side gains
  `Q.IsNonparallel` (`68d5ea84`, `9f7f73ee`; `F-330`, §1d); its witness restated.
- [x] **7.** The multigraph rows ask nondegeneracy on `E(G)`; `IsHingeCoplanar` constrains `E(G)`
  only (`6d261725`).
- [x] **8. `cor:theorem-55-d3-spanning`** (`F-126`): derived from `theorem_55_d3`, concluding
  `IsNonparallel`, hinges on `E(G)` and the rank; `hV` and `hSimple` used (*Decisions made*); moved
  below `theorem_55_d3`.
- [x] **9a, 9b. S1, the panel theorems** (`PanelGeneric.lean`; S13; design doc §2, *Item 9's
  recon*): over every `Q` on `G` with generic normals, under `hd`, `hcard`, `hne` (§1e)
  (`24d9d0cc`); the rank formula a `main_results` row, witnessed at the single edge (`ce98d5ec`).
- [x] **10a, 10b. S1, the body-hinge theorems** (`HingeGeneric.lean`; design doc §2, *Item 10's
  recon*): genericity over `G`; the rank formula and its iffs under `hk1`, `hn`, `hcard`, `hne`,
  witnessed at the triangle (`96683b73`); the S1 scope sentences (`43f78c5f`, with item 12).
- [x] **11. S18** (`prop:rigidity-matrix-prop11`; `F-121`, `F-331`; §1f.1): KT Proposition 2.3 for a
  body-hinge framework on a multigraph, in conditional form; blueprint and docstrings only
  (*Decisions made*). The unconditional repin is MULTIGRAPH's M1 (design doc §3).
- [x] **12. The degenerate-hinge sentences** (with 10b, `43f78c5f`): README, the home page,
  `intro.tex`, ROADMAP §23; `molecular_conjecture`'s docstring (`F-130`).
- [ ] **Close**: whole-project build with 0 warnings, `lake lint`, the blueprint gates, the main
  results' axioms; MULTIGRAPH or UNSTATED named next. Then the loop **stops for the PI's push**
  (§1f.2), CI's first run of 41a's `module` conversion: no next phase opens.

## Blockers / open questions

- **CI has not run since 2026-10-15**: the PI pushes after RESTATE closes (§1b), so that push is
  CI's first run of 41a's `module` conversion (doc-gen, the upstreaming dashboard). The loop stops
  at the close for that push (§1f.2).

## Hand-off / next phase

**The close** (checklist *Close*; `PHASE-BOUNDARIES.md` *When this commit closes a phase*): a
whole-project `lake build` with 0 warnings and `lake lint`, `blueprint/verify.sh` and
`blueprint/lint.sh`, `#print axioms` for every `main_results` row of `formalization.yaml`, then the
close checklist for 41b (ROADMAP's row and §41, the status surfaces, the end-to-end re-read of the
restated nodes, the working-doc tails, MULTIGRAPH or UNSTATED named next in the design doc's §3).
One commit, unless the re-read finds a false sentence, which is then a commit of its own first.
That re-read is done (*Current state*): its two false sentences landed in their own commit, so the
close needs only a check of the two fixed sentences, then the rest of its checklist in one commit.
After it the loop **stops for the PI's push** (§1f.2): no next phase opens.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-24): `notes/Phase41-design.md` §1b, verbatim.
- **KT's nonparallel, route B** (item 1, 2026-10-24): `IsNonparallel` on the normals' directions,
  reached at Theorem 5.5's end by the genericity device; the induction keeps general position.
  Route A, nonparallel in the motive, was rejected by the PI (design doc §1c).
- **The PI's decisions after item 1's recon** (2026-10-24): `notes/Phase41-design.md` §1c,
  verbatim.
- **The PI's decision on `F-330`** (2026-10-25): `notes/Phase41-design.md` §1d, verbatim.
- **The PI's decision on the generic panel theorems' body bound** (2026-10-25):
  `notes/Phase41-design.md` §1e, verbatim.
- **The PI's answers in advance** (2026-10-25; S18, RESTATE's close, free strengthenings, M1's
  loops): `notes/Phase41-design.md` §1f, verbatim.
- **Item 3** (`F-324`): four lemmas without `1 ≤ k` take `hk` for `hD : 2 ≤ D` (`D = 1` at `k = 0`).
- **Items 5, 5b** (the coordinator's adjudications): the genuine form gains `Q.IsNonparallel`
  (the rows form keeps general position); the `d = 3` instance passes it through, else `F-128`
  stays open at `d = 3`.
- **Item 7** (§1.2, §1.4 the PI's; the totality the coordinator's): `HasCoplanarPanelRealization`
  stays total, the body-hinge side asks `∀ e ∈ E(G)`, `IsHingeCoplanar` constrains `E(F.graph)`.
- **Item 9's design** (design doc §2, *Item 9's recon*): genericity is the framework's, at its
  edges; Theorem 5.6's main form is the witness; no twin.
- **Item 10's design** (design doc §2, *Item 10's recon*): genericity at every selector that
  records the links of `G`; Theorem 5.6's main form is the witness; `hk1` and `hn` stay (§ 48);
  the row's witness is the triangle with the shadow labels.
- **Items 10b and 12 in one commit** (the coordinator's call): the same status surfaces.
- **Item 11, no Lean bridge** (the coordinator's scope-pin): §1f.1 asks the conditional form, which
  `rigidityMatrix_prop11` proves. The statement no longer names genericity, so it drops
  `\uses{def:dof-generic}` (G5's node, now unused), and the proof the Theorem-5.5 route's four
  unbacked edges. Lean: docstrings only, KT Proposition 1.1 (Tay–Whiteley's, KT p. 648) renamed 2.3
  in the pin's header and docstring and `theorem_55_6_multigraph_of_two_le`'s (`F-123`, `F-133`).
- **One body, the coordinator's call under §1f.3** (item 10a): `hne` for `hV` in the witness
  assembly, the rank formula and both iffs, §1e's pattern (design doc §2, *Item 10's recon*).
- **Item 9a's pins**: `def:generic-normals`'s third, `isGenericNormals_iff_of_graph_eq`.
- **The corollary keeps `hV` and `hSimple`** (item 8; the coordinator's scope-pin): without
  `G.Simple` it is false at the double edge (`restated_theorem56_false_at_banana`,
  `notes/reconcile-formal/RestateWitness.lean`); it keeps `[DecidableEq β]` for `IsMinimalKDof`.
