# Phase 42d — PD-ALL: an informal proof in every `Pᵈ`, all three conjuncts (work log)

**Status:** in progress (opened 2026-10-30 with the PI), a research sub-phase of Phase 42. Its
target is an informal proof, at every `d`, of the conditioned pair's three conjuncts (bare,
adjacent-distinct and a generic one), written as red nodes of `pencil-d.tex` before any more
formalization. Its research tracks are closed: CERT (the certificates at every `d`) and NONDEG
(C2-same, the PI's choice, with (W) proved). COUNT's Lean landed (11 green nodes). What remains
is the write-up: W1–W9 written (the coverage checked by a fresh read), W10 to go. **Next:** W10. Plan
and the PI's decisions: `notes/Phase42-design.md` (§1, §3 PD-ALL).

## Current state

Opened 2026-10-30; the first `/coordinate-tracks 42d` sitting ran every track. **COUNT** is
done: COUNT-A and COUNT-B, 11 green nodes in `sec:pencil-d-deficiency` (*Lean now*). **CERT**
closed at review 1, **NONDEG** at review 2 (*Tracks*). **WRITE-UP**: W1–W9 have landed, one
section of `pencil-d.tex` each (`sec:pencil-d-induction` and `-flat`, `-cut`, `-contract`,
`-splitoff`, `-chains`, `-short`, `-long`, `-ear-deficiency`, `-coverage`, `-reduction`). The next
concrete step is the hub's: dispatch W10, which takes NONDEG's pieces in the form the PI set
(*Write-up*). A read-only fresh read (the PI's call) found `thm:pencil-d-coverage` holds as
stated, with NONDEG's (A) a special case of it.

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
| NONDEG | attack (a question) | `notes/attacks/nondeg/` | `attack-opus` | closed at review 2: C2-same, (W) proved (workbook S32–S38) |
| WRITE-UP | write-up | `blueprint/src/chapter/pencil-d.tex`, new sections | `writeup-opus` | ready: slice W10 |
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
  (S21's cut-edge glue) are recorded. Session 3: S32 repairs S21, S33 states O8 (W10's node), and
  S34–S36 prove (W) at every `W₀`-ear (S37 certifies 6,217 ears on 6–16 bodies). **Closed** at
  review 2, 2026-10-30, which confirmed S32–S36 and S25 by hand. Left outside the track: the
  coverage (A), slice W9's, and W10's write-up.

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
- [x] **W1–W8** written, one section each (`sec:pencil-d-induction` and `-flat`, `-cut`,
  `-contract`, `-splitoff`, `-chains`, `-short`, `-long`, `-ear-deficiency`, `-coverage`,
  `-reduction`); their rows are in their commit messages. W4's `thm:pencil-d-splitoff` and W8's
  `thm:pencil-d-open-ear-deficiency` have no consumer in the coverage and stay as standalone
  results (the PI, 2026-10-30, after W9: "(a) Keep standalone").
- [ ] **W10** the generic conjunct under C2-same: S38's pieces, O8 (S33, the good-ear lemma
  returning `W₀`), and S7 (a), S9 and S14, each a red node or cited by one; (W) by review 2's
  shorter route (S36's base-generic witness placed in `S_L(Y)`, without S34's count or S35 (c)).
  The PI, 2026-10-30, after review 2: "(b) Shorter route"; "Add S7 (a), S9, S14".

## Lemma checklist

- [x] **CERT** closed (review 1); **NONDEG** closed (review 2; C2-same, the PI's).
- [ ] **WRITE-UP** W1–W10.
- [x] **COUNT-A** and **COUNT-B** landed (*Lean now*); COUNT-C waits for formalization.

## Lean now

**Done** (COUNT, the PI's call in design doc §1: A and B now, C at formalization). Eleven green
nodes in `sec:pencil-d-deficiency`: COUNT-A's sparse estimates at every `n` and two glue lemmas
(`SparseDeficiency.lean`; the `deficiency 3` lemmas are their `n = 3` cases), and COUNT-B's
`ChainUsableAt`, Theorem S at `D`, ONE-CLASS and S52 (`Pencil/Grade/TheoremS.lean`). COUNT-C, the
chain count behind S53 (a), is W5's red `lem:pencil-d-chain-count` until formalization.
`bodyBarDim_mono` is not added (it rebuilds nearly everything; FRICTION's entry).

## Blockers / open questions

- None. The generic conjunct (C2-same) rests on the coverage (A), which slice W9 writes.

## Hand-off / next phase

Next concrete step: the `/coordinate-tracks 42d` hub dispatches W10, the generic conjunct under
C2-same; the write-up then closes. CERT, NONDEG and COUNT are done.
42d closes when the new sections give an informal proof at every `d` of the conjuncts the PI keeps.
Formalization (PD-CARRIER, PD-STEPS, PD-COVERAGE, PD-REDUCTION, PD-HEAD; design doc §3) follows
at the PI's word.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42d is research toward an informal
  proof at every `d`, the generic conjunct included; the `d = 4` results are not formalized yet;
  three tracks from one central session; the write-up as red nodes of `pencil-d.tex`; the
  coverage counting's Lean sized first, then COUNT-A and COUNT-B taken; both briefs cleared.
- **The harness** (the PI's request, outside `/harness-review`; `notes/harness/incidents.md`,
  2026-10-30; accepted as is): `/coordinate-tracks` (with a *lean* kind for COUNT), `writeup-opus`,
  `worktree.baseRef: head`; `attack.md`, `attack-opus.md`, `harness-review.md` and
  `notes/attacks/README.md` point at it.
