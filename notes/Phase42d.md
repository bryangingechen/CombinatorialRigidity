# Phase 42d — PD-ALL: an informal proof in every `Pᵈ`, all three conjuncts (work log)

**Status:** in progress (opened 2026-10-30 with the PI), a research sub-phase of Phase 42. Its
target is an informal proof, at every `d`, of the conditioned pair's three conjuncts (bare,
adjacent-distinct and a generic one), written as red nodes of `pencil-d.tex` before any more
formalization. Its research tracks are closed: CERT (the certificates at every `d`) and NONDEG
(C2-same, the PI's choice, with (W) proved). COUNT's Lean landed (11 green nodes). What remains
is the write-up, W1–W10, all landed: an informal proof of all three conjuncts at every `d`, in
draft, checked by two fresh reads. **Next:** W10's three wording repairs, then the close. Plan
and the PI's decisions: `notes/Phase42-design.md` (§1, §3 PD-ALL).

## Current state

Opened 2026-10-30; the first `/coordinate-tracks 42d` sitting ran every track. **COUNT** is
done: COUNT-A and COUNT-B, 11 green nodes in `sec:pencil-d-deficiency` (*Lean now*). **CERT**
closed at review 1, **NONDEG** at review 2 (*Tracks*). **WRITE-UP**: W1–W10 have landed (*Write-up*).
Two read-only fresh reads (the PI's calls) found `thm:pencil-d-coverage` holds as stated (NONDEG's
(A) is a special case), and W10's new parts hold (the S9 quadric step, the (W) proof by the
shorter route, S25's restructuring, the assembly, the one-ear step), with three wording repairs.
The next concrete step: one `writeup-opus` fix-up commit of those repairs (*Lemma checklist*), then
42d's close (`PHASE-BOUNDARIES.md` *When this commit closes a phase*).

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
| WRITE-UP | write-up | `blueprint/src/chapter/pencil-d.tex`, new sections | `writeup-opus` | ready: W10's wording fix-up (the PI), then the close |
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
- [x] **W1–W10** written, one section each (`sec:pencil-d-induction` and `-flat`, `-cut`,
  `-contract`, `-splitoff`, `-chains`, `-short`, `-long`, `-ear-deficiency`, `-coverage`,
  `-reduction`, `-nondegenerate`, `-lift`, `-generic`); their rows are in their commit messages. W4's `thm:pencil-d-splitoff` and W8's
  `thm:pencil-d-open-ear-deficiency` have no consumer in the coverage and stay as standalone
  results (the PI, 2026-10-30, after W9: "(a) Keep standalone").
  W10 follows the PI's form after NONDEG's review 2 ("(b) Shorter route"; "Add S7 (a), S9,
  S14"), and keeps `cor:pencil-d-conditioned-pair`, the three conjuncts at `d`, as the headline
  node (the PI, after W10: "(a) Keep it").

## Lemma checklist

- [x] **CERT** closed (review 1); **NONDEG** closed (review 2; C2-same, the PI's).
- [x] **WRITE-UP** W1–W10.
- [x] **Fresh reads**: the coverage holds; W10 holds, with three wording repairs.
- [ ] **W10 fix-up** (the PI, 2026-10-30: "(a) Fix-up before close"), one commit: add "Let K be
  infinite" to `lem:pencil-d-ear-extend`'s statement (its proof uses it); state
  `lem:pencil-d-ear-free`'s condition (a) as rank at least 3, with the sentence that the upper
  bound holds wherever (a) is read (on Γ_L, and at a realization); and say in
  `def:pencil-d-nondegenerate` that a link includes loops, as the Lean `IsLink` does.
- [ ] **Close** 42d: `PHASE-BOUNDARIES.md`'s close checklist, with the chapter's end-to-end
  re-read; formalization (design doc §3) then waits on the PI's word.
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

Next concrete step: a `/coordinate-tracks 42d` session dispatches W10's wording fix-up (one
`writeup-opus` commit, *Lemma checklist*), then a session closes 42d by `PHASE-BOUNDARIES.md`.
Every track is done. 42d closes when the new sections give an informal proof at every `d` of the
conjuncts the PI keeps.
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
