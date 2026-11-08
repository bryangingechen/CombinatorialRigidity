# Phase 43c — NORMAL and SPRIME: the reduction on structural cases, then Theorem S′ (work log)

**Status:** in progress (opened 2026-11-08 with the PI), the third sub-phase of Phase 43
(PENCIL-NATURAL): layers NORMAL and SPRIME as one sub-phase, at the PI's choice (design doc §1,
2026-11-08). Slice 1 (NORMAL) landed: the reduction on five structural cases, beside its one
caller, and the minimum-degree lemma in a new appendix of further results. In order next:
SPRIME's pin (a spike and a liveness walk, docs only), SPRIME's slices as the pin cuts them, and
the sub-phase's last commit. The next concrete commit is SPRIME's pin, item 2.

## Current state

**Next concrete commit: SPRIME's pin, checklist item 2** (a recon, docs only; Opus suggested). It
pins item 3 to builder precision and cuts items 3–5 by a liveness walk. Mode: structural edit, no
new chapter and no red target node; each slice reads and restates the nodes it reaches
(`CombinatorialRigidity/CLAUDE.md` *Forward-mode slices*). Plan and inputs:
`notes/Phase43-design.md` §2 SPRIME (its "the move" is read at `n = 3`, the PI's fold of §1).

**After slice 1.** `Graph.pencil_reduction` lives in `Pencil/Grade/Reduction.lean`, with no `n`,
`hD` or finiteness, and its simple two-edge-connected case takes no induction hypothesis;
`Graph.exists_isProperRigidSubgraph_of_three_le_degree` has no Lean user, its node
`lem:pencil-min-degree-rigid` in `blueprint/src/chapter/further-results.tex`
(`sec:further-results`). The four main results' signatures and axioms are unchanged (the
standard three).

## Architectural choices made up front

- **Statements byte-identical:** `pencil_realization_theorem`, `pencilPair_of_nonempty`,
  `Graph.graded_pencil_conditioned_pair`, `Graph.graded_pencil_realization_theorem`. Each Lean
  slice diffs their signature lines and runs `#print axioms` on them in a scratch file
  (`lake lean`): the standard three.
- **Statements that change, by design:** `Graph.pencil_reduction` (slice 1); in SPRIME,
  `Graph.IsX0Graph.exists_additiveCore` (a weaker hypothesis), `Graph.ChainUsable` and
  `Graph.X0Reduces` (two disjuncts, two constructors). None is a main result.
- **S′ at `d = 3` only** (the PI, design doc §1): `thm:pencil-d-theorem-s`,
  `def:pencil-d-usable-chain` and their Lean (`exists_additiveCoreAt`, `ChainUsableAt`, the bridge
  `chainUsable_iff_chainUsableAt_three`) fold into the `d = 3` nodes, not restated in every `d`.
- **Slice boundaries from the bodies** (as 43b): SPRIME's slices are cut by a liveness walk at the
  pin (item 2), not by the 43a line-range sizes.

## Lemma checklist

- [x] **1. Slice 1 — NORMAL: the reduction on five structural cases** (landed 2026-11-08). The
  spike's Lean, unprimed, moved beside its caller; `thm:pencil-reduction` restated, with the glue
  sentence that it plays only the role of KT Theorem 4.9's induction (`pencil.tex`, after the
  `K_4` paragraph); `lem:pencil-min-degree-rigid` moved whole to the new appendix;
  `thm:pencil-d-realization-theorem`'s proof on the five cases. Beyond the list:
  `main-component.tex`'s lead named "the contraction and split cases" of the reduction, now the
  simple two-edge-connected case. The count that finds the bodies of degree two: *Decisions made*.
- [ ] **2. SPRIME's pin** (recon, a docs-only design-pass commit; Opus suggested). A compiler-checked
  spike of S′ at `d = 3` (the fold: `exists_additiveCore`'s blocking hypothesis `¬ ChainUsable`
  without the `k = 2` merged-equality and `k = 1` split-off disjuncts; NEW-1, NEW-2; design doc §2
  SPRIME, whose "the move" was written for the general form) and a kernel liveness walk of the
  deletion set, as 43b's open did with `N1Spike.lean`, banked in `notes/pencil-natural/`. It cuts
  items 3–5 (or re-cuts them) and pins the first to builder precision, with the deleted-name
  list, the dead-docstring sweep (the three files design doc §2 names) and the walk's orphans
  (`lem:deficiency-two-body-chain-d` may lose its only user with `thm:pencil-d-theorem-s`).
- [ ] **3. SPRIME slice A — NEW-1 and NEW-2** (additive, green): `lem:deficiency-two-body-chain`
  restated, `lem:pencil-d-chain-core` gains the form (design doc §2).
- [ ] **4. SPRIME slice B — S′ at `d = 3`**: `exists_additiveCore` on the S′ hypothesis,
  `ChainUsable` and `X0Reduces` less two disjuncts and constructors, the general form and its
  bridge gone; `thm:pencil-x0-theorem-s`, `def:pencil-x0-usable-chain` restated,
  `thm:pencil-d-theorem-s`, `def:pencil-d-usable-chain` and the fmlnote deleted,
  `sec:pencil-d-chains`' lead (`pencil-d.tex:2174–2180`) and the core paragraph (:1079–1095)
  reworded.
- [ ] **5. SPRIME slice C — the deletions**: `SplitOff.lean`, open-ear-two, the two bounds, the
  split-off's own code; `sec:main-component-splitoff`, `thm:pencil-x0-open-ear-two`,
  `lem:deficiency-one-body-chain-d`, two table rows, `rem:pencil-x0-theta`'s `k = 2` step; the 42f
  record's sense named (design doc §2). README (:218) and `home_page/index.md` (:216) list
  "split-off" among the steps: restate.
- [ ] **6. The sub-phase's last commit (43c).** `PHASE-BOUNDARIES.md`'s sub-phase checklist: the
  ROADMAP marker, §43's 43c detail compressed, NORMAL and SPRIME to verdicts in the design doc,
  the ledger's 43c section, the main results' axioms, `formalization.yaml`'s route descriptions;
  the design doc's header says no sub-phase is open (`check-phase-note.py --selftest` reads that
  sentence); then EXPO's open, at the PI's word.

## Blockers / open questions

- **The KT Theorem 4.9 remark** itself is EXPO's (design doc §2, EXPO); slice 1 wrote only the glue
  sentence (`pencil.tex`, `sec:pencil-reduction`'s lead), as design doc §1 (a) asks.
- **Where `thm:pencil-reduction` lives** (`pencil.tex`, its only user in `pencil-d.tex`) is EXPO's.

## Hand-off / next phase

The next concrete commit is *Current state*'s: SPRIME's pin, item 2 (recon-opus, a docs-only
design-pass commit). After it, item 3 as the pin cuts it.

## Decisions made during this phase

The open's decisions are `notes/Phase43-design.md` §1 (the PI's answers of 2026-11-08) and the
choices above.

- **The count that finds the bodies of degree two** (slice 1, read from the nodes): part (1) of
  `lem:pencil-x0-sparse-count` (no planar-rigid set, so sparse, so at least four bodies of degree
  two; used by Theorem S and its every-`d` form). `lem:pencil-d-chain-count` starts from the
  chains and counts the edges along them, the counterpart of KT Lemma 4.6's count of maximal
  chains, not the count that finds the bodies; `pencil.tex` cites each in that role. The recon's
  "heir of KT Lemmas 4.5–4.6" (`notes/PencilNatural.md` §5) is EXPO's to word.
