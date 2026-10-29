# Phase 41d — RELABEL: the bound on the edge labels dropped from the main results (work log)

**Status:** ✓ closed 2026-10-29 (opened the same day with the PI), a sub-phase of Phase 41, which
stays in progress. The phase's design, the PI's decisions (here §1h.2 and §1i, the open) and
RELABEL's recon are in `notes/Phase41-design.md`; the recon's Lean witness is
`notes/reconcile-formal/RelabelWitness.lean`. Every checklist item landed, in 7 commits with the
open, a corrective and the close. The PI answered *Blockers* on 2026-10-29 (the design doc's §1j),
and UNSTATED opened the same day as 41e (*Hand-off*).

## Current state

**Closed.** The six main results that carried a bound on the edge labels assume nothing of them:
KT Theorem 5.5's fresh-label supply (`theorem_55_minimalKDof_gen`), and the bound `hcard` of KT
Theorem 5.6, both molecular conjectures, the generic panel rank formula and M1. Each applies its
supply-taking form, renamed and pinned beside it, with the labels embedded in
`β ⊕ Fin (D(|α| − 1) + 1)`, where the supply holds, and pulls the framework back: rows, motions,
normals and deficiency are unchanged, minimality transports through deficiencies, and the induction
keeps the supply inside, untouched. 23 declarations lost one hypothesis each, every one a
strengthening, and the non-vacuity witnesses use fewer labels than the old bound. Item R found that
KT Theorem 4.9's principle can drop its supply in one commit, which goes to the PI. The close's
re-read fixed three pronouns in `panel-layer.tex`'s notes, left singular when B2 and B3 gave the
nodes a second pin. At the close the 20 main results' axioms are `[propext, Classical.choice,
Quot.sound]`, the output identical to 41c's close run net of the harness path. Mode: structural
edit, no red target nodes.

## Architectural choices made up front

- **Statements change only as §1i and the arc say** (`notes/Reconcile.md` §2, *Hygiene*): each of
  the 23 declarations loses one hypothesis; a free strengthening only under §1f.3.
- **Route B, the induction untouched**: Theorem 5.5's induction, Cases II and III and the chain
  extraction keep `hfresh`; in `Theorem55.lean` only the main results' statements and the
  transports after the induction changed.
- **The main results keep their names**; the supply-taking forms are renamed, under the deletion
  gate. **The witness is the source**; the evidence files are not repointed.

## Lemma checklist

- [x] **B1. `embedEdges` moved up, and minimality through deficiencies (T5)**: `c6bc7762`, with the
  corrective `7287795e` (the simplicity and deficiency pins to `lem:embed-edges-simple-deficiency`).
- [x] **B2. The pullbacks, and KT Theorems 5.5 and 5.6 without the bound**
  (`lem:embed-edges-framework`; six forms renamed): `9d6a43d9`.
- [x] **B3. The cascade and the texts** (17 declarations, the witnesses, `rem:fresh-edge-supply`,
  the status surfaces): `953367f0`.
- [x] **R. Recon: dropping `hfresh` from `minimal_kdof_reduction`** (§1i.3; design doc §2, *Item R's
  recon*; witness `notes/reconcile-formal/ReductionWitness.lean`): `8ea9f2b1`.
- [x] **Close**: the gates, the re-read, ROADMAP's row and §41, the design doc's RELABEL arc
  compressed, UNSTATED named next (the commit "Phase 41d CLOSES (RELABEL)").

## Blockers / open questions

For the PI at the stop (§1i.4); none blocks a build. **Answered** on 2026-10-29
(`notes/Phase41-design.md` §1j): 1 taken (form (b), 41e's item R before U4), 2 taken (riding on
41e's U6), and of 3 the padding drop (before U10) and the `\uses` fix (on U6); the pinned forms no
main result calls stay.

1. **Item R's question** (design doc §2, *Item R's recon*, its *For the PI*).
   `minimal_kdof_reduction` (KT Theorem 4.9's principle; not a main result, and nothing calls it)
   can drop `hfresh` in one commit: its chain holds when the new edge of `G_v^{ab}` reuses the
   label of an edge at `v`, the hypothesis becoming `e₀ ∉ E(G − v)`. Placed in UNSTATED before U4,
   it lets U4 assume nothing of the labels (UNSTATED 16–22 commits). The options: drop it, with
   `hsplit` given `P` at every label outside `E(G − v)` (recommended, a strict strengthening); drop
   it, with `hsplit` at one such label (a weaker theorem, at the same cost); or keep `hfresh` (no
   cost, U4 as planned).
2. **`hasGenericFullRankRealization_of_theorem_55_gen`** (the third pin of
   `thm:theorem-55-6-rows`): B2 left its `hfresh`, as the arc counts it internal, though nothing
   calls it. Restated over the bound-free rows form, a three-line repackage, it drops `hfresh` and
   `[DecidableEq β]`, a free strengthening under §1f.3; or leave it (design doc §4).
3. **Reports, no action recommended** (B3's, confirmed by the close's re-read). No main result
   calls the bound-free rows form, the form of item 2 or the bound-free multigraph `k`-form
   `theorem_55_6_multigraph`, all pinned. `card_shadowLabel_lt` is uncalled, while
   `lem:molecule-graph-carrier` still states "more than 6(|V| − 1) labels", which its note says no
   result needs; dropping the padding would move that statement and U10's. And
   `thm:theorem-55-6-rows`'s `\uses` edge to `thm:theorem-55-6-genuine` has no Lean basis (the rows
   forms build from Theorem 5.5), as before 41d.

## Hand-off / next phase

**Next: 41e (UNSTATED)**, opened 2026-10-29 with the PI (the design doc's §1j), work log
`notes/Phase41e.md`: the claims no declaration states, the full list with §4(a) (§1h.1), as U1–U12
with item R's build before U4 and the padding dropped before U10 (17–23 commits); its first item is
U1. It is Phase 41's last sub-phase, and the PI pushes at its close. ORIGAMI opens after Phase 41.

## Decisions made during this phase

- **The PI's decisions at the open** (2026-10-29): `notes/Phase41-design.md` §1i, verbatim.
- **Route B, not route A** (design doc §2, *RELABEL's recon*): recycling a label inside the
  induction breaks at Case III's chain (`ChainData.e₀_fresh`).
- **The relabelling's graph pins on the panel layer** (B1's corrective): `Simple.embedEdges` and
  `deficiency_embedEdges` on `lem:embed-edges-simple-deficiency`, so the main results' closure
  stays out of the pencil chapter.
- **Names** (B2): `_of_supply` and `_of_card_lt` (FRICTION *A suffixed name past the 100-column
  limit*); `theorem_55_6_multigraph` its own transport; T1 and T2 on `lem:embed-edges-framework`.
- **The renamed forms are pinned beside their main results** (B3), backing the `\uses` edges into
  `thm:theorem-55`, `thm:theorem-55-6-genuine` and `thm:theorem-55-6-rows`.
- **The witnesses take fewer labels than the old bound** (B2, B3): the bound shown gone, not met.
- **`G.shadowGraph`'s padding stayed** (B3): dropping it would move `lem:molecule-graph-carrier` and
  UNSTATED's U10. The PI dropped it in 41e, before U10 (§1j.3).
