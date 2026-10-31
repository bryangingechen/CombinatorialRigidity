# Phase 42d — PD-ALL: an informal proof in every `Pᵈ`, all three conjuncts (work log)

**Status:** ✓ closed 2026-10-30 (opened the same day with the PI), a research sub-phase of Phase
42, which stays in progress with 42e. Its target is met: the sections of
`blueprint/src/chapter/pencil-d.tex` from `sec:pencil-d-induction` to `sec:pencil-d-generic`, 65
red nodes and a remark, give an informal proof at every `d ≥ 3` of the conditioned pair's three conjuncts (bare,
adjacent-distinct and generic; headline `cor:pencil-d-conditioned-pair`), checked by two fresh
reads and the close's end-to-end re-read. CERT and NONDEG closed; COUNT's Lean landed (11 green
nodes). 38 commits with the open and the close. **Next** (*Hand-off*): formalizing the proof,
begun as 42e (PD-CARRIER, `notes/Phase42e.md`). Plan and the PI's decisions:
`notes/Phase42-design.md` (§1, §3 PD-ALL).

## Current state

**Closed.** The write-up, one slice per session, leaf-first (each slice's step-table rows are in
its commit message):
- W1 `sec:pencil-d-induction`, `-flat`: the setting, the flat rank, equal deficiencies.
- W2–W4 `-cut`, `-contract`, `-splitoff`: a cut vertex and bridges; contraction at an additive
  core; the split-off.
- W5–W6 `-chains`, `-short`: the chain count and a long chain or a core; open ears with four or
  more interior bodies in every `d`, three at `4 ≤ d ≤ 6`.
- W7–W8 `-long`, `-ear-deficiency`: cycles and long ears on closed polygons; ears with
  `def_d(G[V₁]) ≤ def_d(G)`.
- W9 `-coverage`, `-reduction`: the coverage; the bare and distinct conjuncts on all multigraphs.
- W10 `-nondegenerate`, `-lift`, `-generic`: C2-same; lifts of `P³` realizations; the generic
  conjunct and the conditioned pair.

The close re-read W1–W10 end to end as a domain mathematician and found no step that fails, and no
slice narration or changelog prose in reader text (track S-numbers are in TeX comments only). It
made three wording repairs and reflowed three passages, no statement or `\uses` changed: a
paragraph break after `def:pencil-d-nondegenerate`, a reason clause in `lem:pencil-d-lift-ear`'s
(T1) (one of the two products is nonzero), and "copies" reworded in
`lem:pencil-d-nonsimple-case`'s `d = 3` remark. `notes/BlueprintExposition.md` has a 42d section, no new entry. The
dispatch log has no 42d rows: the hub ran under `/coordinate-tracks`, and the two
`/coordinate-phase` dispatches (W10's fix-up and the close) had no exceptions.

## Tracks

The hub's registry. Count-free: each attack's status is its `state.md` (`HARNESS.md`).

| Track | Kind | Home | Agent | Status |
|---|---|---|---|---|
| CERT | attack | `notes/attacks/cert/` | `attack-opus` | closed at review 1: R1 proved by hand at every `d` (workbook S1–S9) |
| NONDEG | attack (a question) | `notes/attacks/nondeg/` | `attack-opus` | closed at review 2: C2-same, (W) proved (workbook S32–S38) |
| WRITE-UP | write-up | `blueprint/src/chapter/pencil-d.tex`, new sections | `writeup-opus` | done: W1–W10, W10's wording fix-up (`phase-builder-opus`) and the close's re-read |
| COUNT | lean | *Lean now* below; nodes in `pencil-d.tex` | `phase-builder-opus` | done: A and B landed; C waits for formalization |

- **CERT**: the certificates behind the cycle, long-ear and open-ear steps at every `d`. R1 proves
  (C1)–(C3) by hand at every `d ≥ 3` over every field with `|K| ≥ 4` (driver at `d = 3..9`);
  SHORT-CORE's S53 rests on it, and G1 is retired on the PI's word (S9). In W7 and W8.
- **NONDEG**: the PI chose C2-same after session 1 (feasibility Phase 39's in every `d`, S9). The
  carrier is the lifts of a `P³` realization; review 1's F1 (O8, the good-ear lemma returning
  `W₀`) and F2 (S21's cut-edge glue) were recorded, and session 3 proved (W) at every `W₀`-ear,
  confirmed by hand at review 2. In W10.

## Write-up

Conventions, binding on `writeup-opus` and on later edits of these sections:
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

W4's `thm:pencil-d-splitoff` and W8's `thm:pencil-d-open-ear-deficiency` have no consumer in the
coverage and stay as standalone results (the PI, 2026-10-30, after W9: "(a) Keep standalone").
W10 follows the PI's form after NONDEG's review 2 ("(b) Shorter route"; "Add S7 (a), S9, S14"),
and keeps `cor:pencil-d-conditioned-pair`, the three conjuncts at `d`, as the headline node (the
PI, after W10: "(a) Keep it").

## Lemma checklist

- [x] **CERT** closed (review 1); **NONDEG** closed (review 2; C2-same, the PI's).
- [x] **WRITE-UP** W1–W10.
- [x] **Fresh reads**: the coverage holds; W10 holds, with three wording repairs.
- [x] **W10 fix-up** (the PI, 2026-10-30: "(a) Fix-up before close"): `lem:pencil-d-ear-extend`
  assumes `K` infinite; `lem:pencil-d-ear-free`'s (a) is rank at least 3, with the upper bound
  wherever (a) is read; a link includes loops in `def:pencil-d-nondegenerate`. One
  `phase-builder-opus` commit in the main checkout (the PI, asked how to dispatch it:
  "phase-builder-opus, main checkout").
- [x] **Close** 42d, with the chapter's end-to-end re-read (*Current state*).
- [x] **COUNT-A** and **COUNT-B** landed (*Lean now*); COUNT-C waits for formalization.

## Lean now

COUNT, the PI's call in design doc §1 (A and B now, C at formalization): eleven green nodes in
`sec:pencil-d-deficiency`, COUNT-A's sparse estimates at every `n` and two glue lemmas
(`SparseDeficiency.lean`) and COUNT-B's `ChainUsableAt`, Theorem S at `D`, ONE-CLASS and S52
(`Pencil/Grade/TheoremS.lean`). COUNT-C, the chain count behind S53 (a), is the red
`lem:pencil-d-chain-count`. `bodyBarDim_mono` is not added (it rebuilds nearly everything;
FRICTION's entry).

## Blockers / open questions

- None. Formalization opened as 42e (*Hand-off*).

## Hand-off / next phase

Phase 42 continues with **42e** (PD-CARRIER, `notes/Phase42e.md`), opened 2026-10-30 at the PI's
word: formalizing 42d's proof begins with its setting and the flat rank, the four red nodes of
`sec:pencil-d-induction` and `sec:pencil-d-flat`. PD-STEPS, PD-COVERAGE, PD-REDUCTION and PD-HEAD
follow, each at the PI's word, with no letter minted until it opens (design doc §3, which maps the
other red nodes to them by section and carries what PD-RECON, PD-STATE and PD-STABLE handed
on). What 42d leaves them: the
red nodes of `pencil-d.tex` from `sec:pencil-d-induction` on are the dep-graph, leaf-first, each
naming the `main-component.tex` node it generalizes and where the `d = 3` proof used its
dimension; COUNT-C is `lem:pencil-d-chain-count`; the coverage's Lean needs data-returning forms
of `lem:pencil-x0-cut-reduces`, `-cycle-reduces` and `-planar-rigid-reduces` (design doc §3
PD-COVERAGE); `def:pencil-d-nondegenerate` counts a loop as a link, as `IsNondegPencilRealization`
does at `d = 3`. Tier 0's `formalization.yaml` row waits for Phase 42's close (PD-HEAD).

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42d is research toward an informal
  proof at every `d`, the generic conjunct included; the `d = 4` results are not formalized yet;
  three tracks from one central session; the write-up as red nodes of `pencil-d.tex`; the
  coverage counting's Lean sized first, then COUNT-A and COUNT-B taken; both briefs cleared.
- **The harness** (the PI's request, outside `/harness-review`; `notes/harness/incidents.md`,
  2026-10-30; accepted as is): `/coordinate-tracks` (with a *lean* kind for COUNT), `writeup-opus`,
  `worktree.baseRef: head`; `attack.md`, `attack-opus.md`, `harness-review.md` and
  `notes/attacks/README.md` point at it.
- **The close** (the PI, 2026-10-30): asked "For the 42d close after the fix-up, is this the plan
  you want? It is an intermediate sub-phase close: the Phase 42 row stays in progress, 42d is
  marked done, and formalization (PD-CARRIER through PD-HEAD) is named as the next step but not
  opened, since it waits on your word. The close runs PHASE-BOUNDARIES' checklist, including the
  chapter's end-to-end re-read. Nothing gets pushed without asking you.", the PI answered
  "Sanctioned as described (Recommended)".
