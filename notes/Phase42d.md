# Phase 42d — PD-ALL: an informal proof in every `Pᵈ`, all three conjuncts (work log)

**Status:** in progress (opened 2026-10-30 with the PI), a research sub-phase of Phase 42. Its
target is an informal proof, at every `d`, of the conditioned pair's three conjuncts (bare,
adjacent-distinct and a generic one), written as red nodes of `pencil-d.tex` before any more
formalization. Three tracks, CERT, NONDEG and WRITE-UP, run in parallel from one central session,
`/coordinate-tracks 42d`, with a Lean track, COUNT, for the coverage's counting at every `D`
(COUNT-A and COUNT-B landed: 11 green nodes; W1–W5 written). CERT is closed; NONDEG, under
the PI's C2-same, works on (W) and O8. **Next:** W6 and NONDEG session 3. Plan and the PI's
decisions:
`notes/Phase42-design.md` (§1, §3 PD-ALL).

## Current state

Opened 2026-10-30. The first `/coordinate-tracks 42d` round dispatched CERT session 1 and NONDEG
session 1, each in its own isolated worktree, and COUNT-A as the `pencil-d.tex` writer (one writer
of that chapter in flight at a time). **COUNT-A has landed**: `pencil-d.tex`'s new section
`sec:pencil-d-deficiency`, five green nodes (*Lean now*). **CERT is closed** after one session and
a review. NONDEG: the PI chose C2-same after session 1; session 2 left one obligation, (W), and
the PI called review 1 early, before session 3 attacks (W).
Slice W1 has landed (`sec:pencil-d-induction`, `sec:pencil-d-flat`: four red nodes and a remark).
**COUNT-B has landed**: six more green nodes in `sec:pencil-d-deficiency` (*Lean now*), which
closes the COUNT track. Slices W2 (`sec:pencil-d-cut`) and W3 (`sec:pencil-d-contract`) have
landed, three red nodes each, and W4 (`sec:pencil-d-splitoff`), one. NONDEG's review 1 said
"continue" with two findings (F1, F2), which session 3 records first (the PI). The next concrete
step is the hub's: merge NONDEG session 3 (in flight). W5 (`sec:pencil-d-chains`, two red nodes)
has landed; dispatch W6.

In place at the open: the hub command (`.claude/commands/coordinate-tracks.md`), the write-up
agent (`.claude/agents/writeup-opus.md`), `worktree.baseRef: head` in `.claude/settings.json`
(isolated worktrees otherwise start at `origin/master`), the two briefs, cleared by the PI, and
the COUNT sizing (*Lean now*). The two briefs were drafted in isolated worktrees and merged by
the hub's procedure, which worked as written.

## Tracks

The hub's registry. Count-free: each attack's status is its `state.md` (`HARNESS.md`).

| Track | Kind | Home | Agent | Status |
|---|---|---|---|---|
| CERT | attack | `notes/attacks/cert/` | `attack-opus` | closed at review 1: R1 proved by hand at every `d` (workbook S1–S9) |
| NONDEG | attack (a question) | `notes/attacks/nondeg/` | `attack-opus` | ready: session 3 repairs S21 (F2), adds O8 (F1), then attacks (W) (review 1) |
| WRITE-UP | write-up | `blueprint/src/chapter/pencil-d.tex`, new sections | `writeup-opus` | ready: slice W6 |
| COUNT | lean | *Lean now* below; nodes in `pencil-d.tex` | `phase-builder-opus` | done: A and B landed; C waits for formalization |

`pencil-d.tex` has one writer in flight at a time: COUNT's commits and the write-up's slices
alternate.

- **CERT**: the certificates behind the cycle, long-ear and open-ear steps (rows 10–12) at every
  `d`. **Closed** (review 1, 2026-10-30): R1 proves (C1)–(C3) by hand at every `d ≥ 3` over
  every field with `|K| ≥ 4` (workbook S1–S8, driver at `d = 3..9`); SHORT-CORE's S53 rests on
  it, and G1 is retired on the PI's word (S9). Slices W7 and W8 take S6 and S7 as red nodes.
- **NONDEG**: a `Pᵈ` nondegeneracy for the generic conjunct (Q0–Q4 of its brief), and the route
  to proving that conjunct. **The PI chose C2-same** after session 1 (every feasible graph of its
  population at the deficiency rank in `d = 3, 4, 5`, S11, S16; feasibility Phase 39's in every
  `d`, S9). Session 2: the carrier is the lifts of a `P³` realization (motive `RL_d`), every arm
  of the reduction lifts, and one obligation is open, (W) (O7; certified on every graph with at most
  nine bodies, S30). Review 1: continue, after F1 (O8, the good-ear lemma returning `W₀`) and F2
  (S21's cut-edge glue) are recorded; session 3 does both first, then attacks (W).

## Write-up

New sections of `blueprint/src/chapter/pencil-d.tex`, after `sec:pencil-d-stable` and COUNT's
section: the induction in every dimension, as red nodes (statements, `\uses`, full prose proofs; no `\lean`).
Conventions, binding on `writeup-opus`:
- Statements at every `d ≥ 3`, `D = C(d+1, 2)`, `def[D]`; `d = 3` is Phase 40's, cited.
- Each node names the `main-component.tex` node it generalizes, re-derives every step against
  `pencil-d.tex`'s carrier, and names each place the `d = 3` proof used its dimension (the step
  table's third column, `notes/Phase42-design.md` §2.1). The step-table rows go in the slice's
  commit message, not the chapter (the PI, 2026-10-30, after W1: asked "Where should later slices
  (W2–W10) record the step-table rows?", answered "Commit message").
- A track's result enters as a red node citing its workbook S-number (SHORT-CORE, CERT, NONDEG),
  in a TeX comment above the node and in the commit message, not in reader-facing text (the PI,
  2026-10-30, after W5: "(a) TeX comments").
- A step that fails stops the slice; the gap goes to the coordinator, and to the PI.

Slices, leaf-first, one session each (a slice's nodes may `\uses` only nodes already written):
- [x] **W1** the setting: configurations at every `d`, the flat rank `D(n − 1) + 3 − dim L(q)`
  (row 5), Jackson–Jordán's equality as consumed (row 6).
- [x] **W2** cut vertices and chains of bridges (rows 7–8).
- [x] **W3** contraction at an additive core (row 9, with its second read).
- [x] **W4** split-off (row 16) and the sparse estimates at `D` (row 17); the estimates are
  COUNT-A's green nodes in `sec:pencil-d-deficiency`, cited, not rewritten.
- [x] **W5** Theorem S at `D` (§2.4 T5), ONE-CLASS (`notes/Strata.md` Result 27) and S53's
  counting (SHORT-CORE's workbook). Theorem S, ONE-CLASS and S52 are COUNT-B's green nodes in
  `sec:pencil-d-deficiency` (`thm:pencil-d-theorem-s`, `lem:pencil-d-core-positive-deficiency`,
  `lem:pencil-d-chain-core`), cited, not rewritten; S53's chain count is left to write, red.
- [ ] **W6** short ears (row 13): SHORT-CORE's `d = 4`, `k = 3, 4, 5`; `k ≥ 4` in every `d`;
  `k = 3` at `d = 5, 6`.
- [ ] **W7** cycles and long ears (rows 10–11), with CERT's statements as red nodes.
- [ ] **W8** open ears, `k = 2` and `3 ≤ k ≤ D − 2` (row 12), with CERT's open ears.
- [ ] **W9** the main-component statements at every `d` for the bare and distinct conjuncts, and
  Phase 39's reduction in `Pᵈ` (row 19).
- [ ] **W10** the generic conjunct, in the form NONDEG's verdict and the PI give it.

## Lemma checklist

- [x] **CERT** closed (review 1, 2026-10-30; workbook S1–S9): (C1)–(C3) at every `d`, by hand,
  with a committed driver.
- [ ] **NONDEG** closed: Q0–Q4 answered; the PI has chosen the `Pᵈ` nondegeneracy (or dropped
  the conjunct at `d ≥ 4`).
- [ ] **WRITE-UP** W1–W10.
- [x] **COUNT-A** and **COUNT-B** (landed; *Lean now*), the PI's call: A and B now, C at
  formalization.

## Lean now

The PI asked whether formalizing some ingredients now would keep the research on track. The
candidates are the coverage's deficiency counting at every `D`, independent of the carrier, CERT
and NONDEG. **The sizing** (2026-10-30, a read-only recon, Claude Opus 5.5; its spikes, checked
through the Lean server only, are in the gitignored `scratch/42d/` on this machine): the API under
them (`partitionDef`, `deficiency`, `deficiencyMerged`, merging, adding a body, `IsX0Graph`) is
already `n`-general, with Lean's `n` the deficiency index (`D = bodyBarDim n`, so `D = 6` is
`n = 3`). Two glue lemmas carry everything to every `D`: a planar value at most zero is at most
zero at `D ≥ 3` (`3·v_D = D·v₃ − (D − 3)·d`), and a set rigid at `n = 3` is rigid at every `n ≥ 3`.
- **COUNT-A** (one commit, low risk): the sparse estimates at `n` (`lem:deficiency-core-bound`,
  the one- and two-body chain lemmas, `+ (D − 1)` in place of `+ 5`), with the two glue lemmas, in
  `Molecular/Induction/SparseDeficiency.lean` as `n`-general siblings; the `deficiency 3` lemmas
  re-proved as one-line specializations, so no statement and no green pin changes.
- **COUNT-B** (one or two commits, low risk): `ChainUsableAt n` and Theorem S at `n ≥ 3`,
  ONE-CLASS (each part of a tight partition has deficiency zero; a core at `n` when
  `def[6] > 0`) and S52, in a new `Pencil/Grade/` file. It protects the most: Theorem S at `D`
  and ONE-CLASS each rest on one author's hand proof.
- **COUNT-C** (two or three commits, moderate risk, not recommended now): the chain count
  `(k + 1)·m ≤ k·|E|` behind S53 (a) and T5's second argument; S53 (b) rests on CERT and S35.
- Hand proofs: none wrong; three under-specified (connectivity before the antitone lemma, twice,
  which the second glue lemma supplies; and S53 (a)'s "subdivides a loopless core multigraph").

**The PI's call** (design doc §1): A and B now, as the COUNT track; C waits for formalization.
Each COUNT commit is one `phase-builder-opus` dispatch in the main checkout, with the builder's
full gates, and writes its own green nodes in a new section of `pencil-d.tex`, "The deficiency at
every screw dimension", after `sec:pencil-d-stable`; slices W4 and W5 then cite them. The builder
starts from the spikes (`scratch/42d/count_spike.lean`, then `theorem_s_spike.lean`), whose
statements it re-reads against the hand proofs (design doc §2.4 T5, §2.3 ONE-CLASS) before
landing them.
- [x] **COUNT-A** (landed 2026-10-30): `sec:pencil-d-deficiency`, five green nodes
  (`lem:deficiency-planar-nonpos`, `-rigid-higher`, `-core-bound-d`, `-one-body-chain-d`,
  `-two-body-chain-d`) in `SparseDeficiency.lean`; the `deficiency 3` lemmas are their `n = 3`
  cases. The second glue lemma is general: rigid at `n ≥ 1` gives rigid at every `m ≥ n`.
- [x] **COUNT-B** (landed 2026-10-30): six green nodes in `sec:pencil-d-deficiency`, in
  `Pencil/Grade/TheoremS.lean` but the first: `lem:deficiency-tight-part`
  (`Graph.IsTightPartition.deficiency_induce_eq_zero`, in `SparseDeficiency.lean`, renamed from the
  spike's `deficiency_induce_part_eq_zero` for dot notation), `def:pencil-d-usable-chain`
  (`Graph.ChainUsableAt`), `lem:pencil-d-maximal-rigid-core` (`…exists_additiveCore_of_rigidAt`, at
  `D ≥ 3`, now also giving `W ∩ X₀ = ∅`), `thm:pencil-d-theorem-s` (`…exists_additiveCoreAt`),
  `lem:pencil-d-core-positive-deficiency` (ONE-CLASS, `…exists_core_of_deficiency_three_pos`) and
  `lem:pencil-d-chain-core` (S52 at `D ≥ 3`, `Graph.IsOpenEar.exists_additiveCoreAt_of_…`).
  `bodyBarDim_mono` not added (it rebuilds nearly everything); FRICTION's entry counts a fourth site.

## Blockers / open questions

- None. The generic conjunct uses C2-same (the PI, after NONDEG session 1); its `Pᵈ` carrier is
  NONDEG's open work.

## Hand-off / next phase

Next concrete step: the `/coordinate-tracks 42d` hub dispatches slice W6 (short ears) as the next
`pencil-d.tex` writer, and merges NONDEG session 3 (F2, O8, then (W)) as it lands (CERT is
closed; COUNT is done). 42d closes when the new sections give an informal proof at every `d` of the conjuncts the PI keeps, with CERT and NONDEG closed. Formalization (PD-CARRIER, PD-STEPS, PD-COVERAGE, PD-REDUCTION, PD-HEAD; design doc
§3) follows at the PI's word.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42d is research toward an informal
  proof at every `d`, the generic conjunct included; the `d = 4` results are not formalized yet;
  three tracks from one central session; the write-up as red nodes of `pencil-d.tex`; the
  coverage counting's Lean sized first, then COUNT-A and COUNT-B taken; both briefs cleared.
- **The harness** (the PI's request, outside `/harness-review`; `notes/harness/incidents.md`,
  2026-10-30; accepted as is): `/coordinate-tracks` (with a *lean* kind for COUNT), `writeup-opus`,
  `worktree.baseRef: head`; `attack.md`, `attack-opus.md`, `harness-review.md` and
  `notes/attacks/README.md` point at it.
