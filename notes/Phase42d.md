# Phase 42d — PD-ALL: an informal proof in every `Pᵈ`, all three conjuncts (work log)

**Status:** in progress (opened 2026-10-30 with the PI), a research sub-phase of Phase 42. Its
target is an informal proof, at every `d`, of the conditioned pair's three conjuncts (bare,
adjacent-distinct and a generic one), written as red nodes of `pencil-d.tex` before any more
formalization. Three tracks, CERT, NONDEG and WRITE-UP, run in parallel from one central session,
`/coordinate-tracks 42d`, with a Lean track, COUNT, for the coverage's counting at every `D`.
**Next:** a `/coordinate-tracks 42d` session runs its first round. Plan and the PI's decisions:
`notes/Phase42-design.md` (§1, §3 PD-ALL).

## Current state

Opened 2026-10-30. The next concrete step is a `/coordinate-tracks 42d` session. Its first round
dispatches CERT session 1 and NONDEG session 1, each in its own isolated worktree, and one
`pencil-d.tex` writer, COUNT-A or slice W1 (one writer of that chapter in flight at a time), and
merges what lands.

In place at the open: the hub command (`.claude/commands/coordinate-tracks.md`), the write-up
agent (`.claude/agents/writeup-opus.md`), `worktree.baseRef: head` in `.claude/settings.json`
(isolated worktrees otherwise start at `origin/master`), the two briefs, cleared by the PI, and
the COUNT sizing (*Lean now*). The two briefs were drafted in isolated worktrees and merged by
the hub's procedure, which worked as written.

## Tracks

The hub's registry. Count-free: each attack's status is its `state.md` (`HARNESS.md`).

| Track | Kind | Home | Agent | Status |
|---|---|---|---|---|
| CERT | attack | `notes/attacks/cert/` | `attack-opus` | ready: session 1 checks R1 (brief §5) |
| NONDEG | attack (a question) | `notes/attacks/nondeg/` | `attack-opus` | ready: session 1 settles §4's `[READING]` items |
| WRITE-UP | write-up | `blueprint/src/chapter/pencil-d.tex`, new sections | `writeup-opus` | ready: slice W1 |
| COUNT | lean | *Lean now* below; nodes in `pencil-d.tex` | `phase-builder-opus` | ready: COUNT-A |

`pencil-d.tex` has one writer in flight at a time: COUNT's commits and the write-up's slices
alternate.

- **CERT**: the certificates behind the cycle, long-ear and open-ear steps (rows 10–12) at every
  `d`; measured by search at `d ≤ 6` only. SHORT-CORE's S53 and its parked G1 hang on it. Its
  drafter's route R1 (a polygon reduction plus edge-by-edge subdivision; KT Theorem 5.6 as an
  alternative for the closed polygons) may settle it at every `d`, unread by anyone else yet.
- **NONDEG**: a `Pᵈ` nondegeneracy for the generic conjunct (Q0–Q4 of its brief), and the route
  to proving that conjunct. The definition is the PI's choice; the track recommends.

## Write-up

New sections of `blueprint/src/chapter/pencil-d.tex`, after `sec:pencil-d-stable` and COUNT's
section: the induction in every dimension, as red nodes (statements, `\uses`, full prose proofs; no `\lean`).
Conventions, binding on `writeup-opus`:
- Statements at every `d ≥ 3`, `D = C(d+1, 2)`, `def[D]`; `d = 3` is Phase 40's, cited.
- Each node names the `main-component.tex` node and the step-table row it generalizes
  (`notes/Phase42-design.md` §2.1), re-derives every step against `pencil-d.tex`'s carrier, and
  names each place the `d = 3` proof used its dimension (the table's third column).
- A track's result enters as a red node citing its workbook S-number (SHORT-CORE, CERT, NONDEG).
- A step that fails stops the slice; the gap goes to the coordinator, and to the PI.

Slices, leaf-first, one session each (a slice's nodes may `\uses` only nodes already written):
- [ ] **W1** the setting: configurations at every `d`, the flat rank `D(n − 1) + 3 − dim L(q)`
  (row 5), Jackson–Jordán's equality as consumed (row 6).
- [ ] **W2** cut vertices and chains of bridges (rows 7–8).
- [ ] **W3** contraction at an additive core (row 9, with its second read).
- [ ] **W4** split-off (row 16) and the sparse estimates at `D` (row 17).
- [ ] **W5** Theorem S at `D` (§2.4 T5), ONE-CLASS (`notes/Strata.md` Result 27) and S53's
  counting (SHORT-CORE's workbook).
- [ ] **W6** short ears (row 13): SHORT-CORE's `d = 4`, `k = 3, 4, 5`; `k ≥ 4` in every `d`;
  `k = 3` at `d = 5, 6`.
- [ ] **W7** cycles and long ears (rows 10–11), with CERT's statements as red nodes.
- [ ] **W8** open ears, `k = 2` and `3 ≤ k ≤ D − 2` (row 12), with CERT's open ears.
- [ ] **W9** the main-component statements at every `d` for the bare and distinct conjuncts, and
  Phase 39's reduction in `Pᵈ` (row 19).
- [ ] **W10** the generic conjunct, in the form NONDEG's verdict and the PI give it.

## Lemma checklist

- [ ] **CERT** closed: (C1)–(C3) at every `d`, by hand, with a committed driver.
- [ ] **NONDEG** closed: Q0–Q4 answered; the PI has chosen the `Pᵈ` nondegeneracy (or dropped
  the conjunct at `d ≥ 4`).
- [ ] **WRITE-UP** W1–W10.
- [ ] **COUNT-A** and **COUNT-B** (*Lean now*), the PI's call: A and B now, C at formalization.

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
- [ ] **COUNT-A**: the two glue lemmas and the sparse estimates at `n`, as above.
- [ ] **COUNT-B**: `ChainUsableAt n`, Theorem S at `n ≥ 3`, ONE-CLASS, and S52 if it fits.

## Blockers / open questions

- None. The generic conjunct's form waits for NONDEG's table and the PI.

## Hand-off / next phase

Next concrete step: a `/coordinate-tracks 42d` session; its first round dispatches CERT session 1,
NONDEG session 1 and one `pencil-d.tex` writer (COUNT-A or W1). 42d closes when
the new sections give an informal proof at every `d` of the conjuncts the PI keeps, with CERT and
NONDEG closed. Formalization (PD-CARRIER, PD-STEPS, PD-COVERAGE, PD-REDUCTION, PD-HEAD; design doc
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
