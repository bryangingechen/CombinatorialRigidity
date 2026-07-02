# Phase 23h — Case III general `d`: ASSEMBLY (producer-site rewire → Thm 5.5 → 5.6 → Conjecture 1.2) (work log)

**Status:** CLOSED (2026-07-02; opened 2026-07-02). The `ASSEMBLY` sub-phase — the **last**
Phase-23 sub-phase, so this close is the **umbrella Phase-23 close** (full-phase checklist run:
ROADMAP row + §23 compressed, status surfaces synced, blueprint re-read + exposition-ledger
write-up, design-doc frozen, GAP-6 verdict below). Authoritative scoping was
`notes/Phase23-design.md` §2 *ASSEMBLY*; program map `notes/MolecularConjecture.md`.

## Outcome

**The Molecular Conjecture is formalized at general `d`.**
`PanelHingeFramework.molecular_conjecture` (`thm:molecular-conjecture`, KT 2011 Conjecture 1.2,
conjectured Tay–Whiteley 1984) is green + axiom-clean (`propext`/`Classical.choice`/`Quot.sound`,
no `sorryAx`) for `6 ≤ bodyBarDim n` (i.e. `n ≥ 3`): a simple spanning graph on ≥ 2 bodies has an
infinitesimally rigid genuine **body-hinge** realization iff it has one as a **panel-hinge**
framework. (⇐) is the `toBodyHinge` coercion; (⇒) pins `def(G̃) = 0` via the genuine-hinge hub
lower bound meeting `dim Z = D` from rigidity, then Theorem 5.6. The genuine-hinge conjunct
(`∀ e, supportExtensor e ≠ 0`) is mathematically essential on both sides (a degenerate hinge welds
two bodies; dropping it makes ⇐ false), and the `≥ 2`-body hypothesis makes the iff true rather
than vacuous (see *Decisions made*).

## Layer plan (all landed 2026-07-02)

- [x] **A1 — producer-site rewire.** ENTRY bricks (`Graph.chainData_extract`,
  `PanelHingeFramework.cycle_realization`) consumed inside `case_III_hsplit_producer_all_k`;
  `hextract`/`hcycle` binders dropped from all four sites; no blueprint edit needed.
- [x] **A2 — Theorem 5.5 at general `d`** (`theorem_55_minimalKDof_gen` + the `c = 0` corollary
  `theorem_55_gen`; `thm:theorem-55` re-pinned/restated). `d = 3` wrapper untouched.
- [x] **A3 — dissolved by the design pass** (design §(4.109)): `rigidityMatrix_prop11` + the
  `hub` family were already grade-general as landed; only a blueprint route-sync rode in A4.
- [x] **A4 — Theorem 5.6 at general `d`** (`rankHypothesis_of_theorem_55_gen` + the arithmetic
  bridge `Graph.eq_add_one_of_bodyBarDim_eq_screwDim`; minted `thm:theorem-55-6`, demoted
  `thm:theorem-55-6-d3` to the specialization).
- [x] **A5 — Conjecture 1.2 stated as a theorem** (`molecular_conjecture`, + the genuine-hinge
  witness form `rankHypothesis_genuine_of_theorem_55_gen` extracted from A4's main case; new
  blueprint node `thm:molecular-conjecture` + verified `tayWhiteley1984` bib entry).
- [x] **Pre-close cleanup:** the orphan-decl sweep + the A5 prose nit (see *Decisions made*).
- [x] **GAP 6 assessment** (the 23g-carried item) — verdict below.

## GAP 6 — VERDICT: discharged (no successor item)

GAP 6 (surfaced 2026-06-10, `notes/Phase22-realization-design.md` §1.50(b)) was the eq.-(6.22)
rank lower bound at the `k'`-dof subgraph `G_v` — KT's nested IH (6.1) — undischargeable from the
*then* 0-dof-only induction motive, adjudicated carry-and-defer (`h622lb`). The carry was retired
by machinery that is now the landed A2/A5 spine: **22i restated the induction all-`k`**
(`Graph.minimal_kdof_reduction_all_k` — the conditioned-pair motive quantified over every dof
`c : ℤ`, so the IH each case receives, `hIH : ∀ (k' : ℤ) (G' : Graph α β), …`, *is* KT hypothesis
(6.1)), and **22k L7 / 23a Leaf 4 derived the bound from that IH**
(`case_III_nested_rank_lower_all_k`, grade-general, via the rank-polynomial extractor + the
footnote-6 non-root device). Against the landed spine: `theorem_55_minimalKDof_gen` passes the
full all-`k` IH through `theorem_55_minimalKDof_k_all_k` to the Case-III arm;
`case_III_realization_all_k` hands it **un-narrowed** to `chainData_dispatch`, whose firing step
derives the nested bound (`chainData_fire_discriminator` → `case_III_nested_rank_lower_all_k`) —
the only `k = 0` narrowing on the route is the producer adapter *alongside* the full IH, exactly
KT's structure. Axiom-clean through A2 and A5. The "vs the project's 0-dof-only motive" phrasing
carried in the 23e–23h notes was itself stale (the motive has been all-`k` since 22i); the one
live residue — `case-iii.tex`'s "carried as an explicitly named hypothesis / tracked by the red
node below" paragraph at `lem:case-III-nested-rank-lower` — is fixed in this close commit.

## Blockers / open questions

- None.

## Hand-off / next phase

**Phase 23 is closed** — the umbrella close ran the full `PHASE-BOUNDARIES.md` checklist (ROADMAP
row ✓ + §23 compressed; README / `home_page/index.md` / `intro.tex` re-summarized —
the conjecture is now the headline, the molecule application (24–26) the frontier;
`notes/MolecularConjecture.md` synced; the general-`d` chain-dispatch exposition written into
`case-iii.tex` and its `notes/BlueprintExposition.md` entry flipped to done; `lem:case-III`
restated at general grade; `notes/Phase23-design.md` frozen as the §-cited archive). Closing
Phase 23 unblocks Phase 26's use of Thm 5.6 (Phases 24–25 don't gate on it). **The next phase is
Phase 24** (the 3-D generic bar-joint rigidity matroid; see `notes/MolecularConjecture.md`
*Opening the next phase* + the Phase-24 detail block) — not opened here; its first commit mints
`notes/Phase24.md` per the phase-open protocol. The `notes/model-experiment.md` archive step for
the 23h rows is **coordinator-owned** (not part of this close).

## Decisions made during this phase

- **GAP 6:** discharged — see the verdict section above.
- **A5 (`molecular_conjecture`):** genuine-hinge conjunct on *both* sides (verified against KT
  p. 648) — essential, not decorative: a welded framework rigidifies a `def > 0` graph, so ⇐
  fails without it. ⇐ = `toBodyHinge`; ⇒ = hub lower bound
  (`screwDim_add_deficiency_le_finrank_infinitesimalMotions`) + `rankHypothesis_zero_iff` ⟹
  `def = 0`, then Thm 5.6 via the extracted witness form
  `rankHypothesis_genuine_of_theorem_55_gen` (A4's `|V| ≥ 2` case delegates to it; no duplication).
- **A5 prose nit (single-body scoping):** on one body the panel-hinge side is genuinely
  impossible (the `∀ e` conjunct is total over the label type; `ends e = (a, a)` forces
  `panelSupportExtensor = 0`) while the body-hinge side is trivially realizable — so dropping
  `2 ≤ V(G).ncard` would make the iff **false**, not vacuous; both prose passages fixed.
- **Orphan-decl sweep:** deleted the three genuine `d=3`-era orphans (`interior_hsplitGP`,
  `case_III_hsplit_producer`, `chainData_extract_d3` + its sole consumer
  `chainData_of_exists_chain_data`); kept `case_III_realization_of_line` (blueprint-pinned) and
  the A2-addendum `d=3` producer duplication (blueprint-pinned; collapse buys only de-dup at the
  cost of re-pinning three nodes); the flagged `ForestSurgery.Reduction`/`ChainExtraction`
  imports were still live (false lead). Dangling doc-comment references updated.
- **A4 (Thm 5.6 general `d`):** mechanical `2 → k`/`3 → n` carrier lift; the one non-mechanical
  spot (the single-body `hnn` positivity through `hD` rather than a closed numeral) was
  design-anticipated §(4.109.C). `rankHypothesis_of_theorem_55_d3` + its `def = 0` companion stay
  as blueprint narrative pins.
- **A3 design pass:** dissolved — prop11 + `hub` born grade-general; lesson re-confirmed: read
  the landed decl before trusting a recon-era "still-`d=3`-pinned" claim.
- **A2 (Thm 5.5 general `d`):** pure composition filling the spine's four carries from the
  grade-general producers; deliberately did **not** re-base the `d=3` spine through it (would
  orphan blueprint-pinned `d=3` sub-producers).
- **A1 (producer-site rewire):** bricks consumed at the deepest site with all inputs in scope;
  binder drops cascaded E4-in-reverse; `Arms.lean` gained the `ForestSurgery.ChainExtraction`
  import (no cycle). Mechanical, zero friction.
- **`lem:case-III` blueprint route-sync (A1 follow-up):** `lem:chain-data-of-noRigid` dropped
  from `\uses` (dead on the live route); `lem:adjacent-degree-two-pair` **stays** — still
  consumed via the `|V| = 3` triangle floor. Lesson: grep every call site of a "dead" declaration
  before trusting a route-change claim.
- **Umbrella close (this commit):** GAP-6 verdict; the general-`d` chain-dispatch exposition
  (the owner-flagged ledger item) written as the three-step narrative preceding `lem:case-III`
  in `case-iii.tex`, with `lem:case-III` restated at general grade (pinned
  `case_III_realization_all_k` + the `d=3` wrapper) and the stale nested-IH-carry paragraph
  fixed; ledger entry flipped done; ROADMAP / README / home_page / intro.tex / program map
  re-summarized; `notes/Phase23-design.md` frozen (archive banner; the Phase-22 precedent —
  inbound §-pointers make blind compression inadvisable).
