# CLEANUP-42 round 1 — the route audit (work log)

**Status:** in progress (opened 2026-11-05 at the PI's word, `notes/Cleanup42.md` §1). Round 1
of CLEANUP-42, the cleanup of `blueprint/src/chapter/pencil-d.tex`'s proofs whose Lean departs
from the chapter's route; its plan, the PI's words and the proof-route ledger are
`notes/Cleanup42.md`. The round compares each of the chapter's 99 green nodes with its pinned Lean
and adds a ledger row for each departure, re-checking R-1 to R-34 at HEAD; it edits no prose,
statement, pin or Lean. The open (task 1, docs only) sliced the nodes by layer into 14
one-dispatch Opus recon tasks, the 47 never-checked nodes of 42b–42f first, then a planned stop
(task 16) at which the PI picks a remedy per `open` row and plans rounds 2+. Tasks 2 to 14
(PD-STATE, PD-STABLE, COUNT-A and COUNT-B, PD-CARRIER, PD-STEPS, PD-COVERAGE, PD-REDUCTION,
PD-HEAD's first half and 42m's cases) added R-35, R-46 and R-48 to R-51 (`open`), R-36 to R-45,
R-47 and R-52 (`no departure`); tasks 8 to 14 re-checked R-1 to R-30, correcting R-7, R-9, R-12,
R-15 to R-17 and R-24 to R-27 in place. **Next concrete task:** task 15, PD-HEAD's second half
(42m), the rest, re-checking R-31 to R-34 (*Lemma checklist*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

CLEANUP-42's row of `.claude/autopilot/queue.toml` is attended, so the autopilot driver stops
before it: the coordinator runs this round, which the PI opened (`notes/Cleanup42.md` §1,
2026-11-05). **One planned stop**, after the audit's last slice: task 16 writes a `NEEDS_PI` entry
here with the ledger's tally, each `open` row and its remedies, and the *Candidates* lines; the PI
picks a remedy per `open` row and plans rounds 2+ (`notes/Cleanup42.md` §3). An unplanned
`NEEDS_PI` entry also goes here, newest first, and the PI answers in an entry that starts
`**PI, <date>:**`. No entries yet.

## Current state

**Tasks 1 to 14 have landed** (task 14 this commit: R-51 `open`, the infinite `K` that
`lem:pencil-d-lift-small`'s three pins drop; R-52 `no departure`, (1)'s lift at `λ = 0` and its
cases on at most two bodies; R-24 to R-27, written from 42m's spike, now name the files it landed
in, their names and steps unchanged at the builds; R-28 to R-30 accurate). The ledger has
52 rows, 33 `open`; the next row is R-53. Nothing is mid-stream; task 15 is next.

**Verified at the open** (2026-11-05, at `a3b80ac4`):
- **The Lean baseline** is the coordinator's run this session, not repeated here: `lake build
  CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Generic` green at `a3b80ac4`, 6108 jobs.
  **The no-Lean-edit base is `a3b80ac4`**: the stop checks that `git diff --stat a3b80ac4.. --
  CombinatorialRigidity/ lakefile.toml lake-manifest.json lean-toolchain` is empty.
- **The chapter, re-counted:** 6 359 lines, 16 subsections, 101 node environments. The 99 nodes
  are all green; the other two, `rem:pencil-d-point-type` and `rem:pencil-d-flat-class`, are
  remarks without `\leanok`, not drawn. `python3 scripts/blueprint-deps.py --chapter pencil-d`
  agrees: 99 nodes, 99 pinned, 236 pins. By layer (the table below) the counts are
  `notes/Phase42-design.md` §3's *The nodes by layer*.
- **The ledger** (`notes/Cleanup42.md` §2): 34 rows, 27 `open`, 6 `aligned` (R-1, R-2, R-7, R-8,
  R-13, R-22) and 1 `no departure` (R-6), on 30 nodes, all of them 42g's to 42m's. The 47 nodes of
  42b–42f have none. The next row is R-35.

| Layer | Sub-phase | Sections (`sec:pencil-d-…`) | Nodes | With a row | Task |
|---|---|---|---|---|---|
| PD-STATE | 42b | `-realization`, `-carrier` | 17 | 0 | 2, 3 |
| PD-STABLE | 42c | `-stable` | 9 | 0 | 4 |
| COUNT-A, COUNT-B | 42d | `-deficiency` | 11 | 0 | 5 |
| PD-CARRIER | 42e | `-induction`, `-flat` | 4 | 0 | 6 |
| PD-STEPS | 42f | `-cut`, `-contract` | 6 | 0 | 7 |
| PD-STEPS | 42g | `-long` | 7 | 5 (R-1 to R-6) | 8 |
| PD-STEPS | 42h | `-short`, 8 of its 12 | 8 | 5 (R-7 to R-12) | 9 |
| PD-STEPS | 42i | `-short`, the other 4 | 4 | 4 (R-13 to R-16) | 10 |
| PD-COVERAGE | 42j | `-chains`, `-coverage` | 4 | 1 (R-17) | 11 |
| PD-REDUCTION | 42k | `-reduction` | 8 | 2 (R-18, R-19) | 12 |
| PD-HEAD | 42l | `-nondegenerate`, `-lift` | 10 | 4 (R-20 to R-23) | 13 |
| PD-HEAD | 42m | `-generic` | 11 | 9 (R-24 to R-34) | 14, 15 |
| | | | **99** | **30** | |

## Scope and standing rules

- **The hygiene rule** (`CLEANUP.md` *Per-round work log*). Round 1 edits no chapter prose, no
  statement, no pin and no Lean: its only product is ledger rows in `notes/Cleanup42.md` §2 and
  their records here (each task's checklist line). A finding that would change a statement or its
  strength goes under *Candidates for the PI*; one outside the audit's scope under *Moved to a later
  round*; each line is mirrored into `notes/Cleanup42.md` §3 in the same commit. Neither is a stop.
- **Writes.** `notes/Cleanup42.md` (§2's rows, its **Status** counts, §3's mirrored lines), this
  log, and, at the open and the stop only, ROADMAP's Status row and CLEANUP-42 bullet.
- **One task, one dispatch.** Tasks 2–15 are each one Opus recon (the PI's "opus recons"),
  read-only, then one docs commit. Probes, if any, go in `scratch/cleanup-42/<task>/`
  (gitignored), run with `lake lean`. A claim about the Lean comes from the declaration's
  statement and body, never its docstring (root `CLAUDE.md` *Docstrings are not evidence*).
- **Gates.** `python3 notes/check-phase-note.py` on every commit; `blueprint/lint.sh` only on a
  commit that touches the blueprint, which none should. The Lean does not change, so no task
  rebuilds it. Every gate runs in the foreground with an explicit `timeout`.

## The audit's criterion

From the 34 rows of `notes/Cleanup42.md` §2, which are its exemplar, and the standing rule that
raised them (`notes/Phase42-design.md` §3). A slice reads each node's statement, proof and `\uses`
against its pins' statements and bodies at HEAD (`python3 scripts/blueprint-deps.py --label
<label>` prints what the pins reach), and gives the node one verdict.

- **A departure** (a row, **open**): (1) a different argument for a step, the same claim by another
  technique (R-1, R-9, R-11, R-20); (2) a step of the chapter's proof that the Lean skips, or one it
  adds or orders otherwise (R-12's factored order, R-14's missing component step, R-17's classes
  for segments, R-32's missing map `g`); (3) a hypothesis of the node that the Lean does not use,
  so the pin is stronger than its node (R-25, R-28, R-30, R-33), or a pin that carries more than
  its node states (R-31's explicit first outcome). A node's parts get a row each when their
  remedies differ (R-7 and R-11, R-27 and R-28).
- **Not a departure** (no row): a carrier encoding of the chapter's own object. An indexing or
  ordering; a restriction to `V(G)` (R-6); the phase's pinned encodings (each body's 3-space as
  data, the grade `k = d − 1` with `m = d − 2` heights, `def[D_d]` as `G.deficiency d`, `σ_v` a
  `def` and `Π_v` its range: `notes/Phase42b.md` *Architectural choices*, the design doc §3); a
  pin at every grade where its node states `d ≥ 3`, each sub-phase's standing generality. A call
  that is close gets a short **no departure** row (R-6), so no later reader raises it again.
- **Not a route row either.** A pin weaker than its node, or a hypothesis neither discharged in
  the pin's body nor the conclusion of a node the proof `\uses`, is an honesty finding: under
  *Candidates for the PI*. A missing `\uses` edge, a stale docstring or a prose slip: under *Moved
  to a later round*. A duplication the plan's §3 already lists (Theorem S's fold, the `d = 3`
  cases' fold) is not raised again.
- **A row** has §2's format: `- **R-<n>** · \`<label>\`[, its part] (\`<Lean names>\`,
  \`<file>\`, round 1 task <N>) · **open**.`, then *Chapter:* the chapter's route in its notation,
  *Lean:* the Lean's, and *Remedies:* the options (the prose to the Lean; a Lean helper so that
  the Lean follows the chapter; keep both), with what each does to the statement and the `\uses`,
  and the recon's lean if it has one. New rows number on from R-35, in landing order.
- **A re-check** reads a row of R-1 to R-34 against the Lean at HEAD. Accurate, it stays as it is
  and the task's line says so. Stale (a declaration renamed or moved, a step misstated), its
  *Chapter* or *Lean* text is corrected in place, its status and any words of the PI untouched, and
  the line says what changed. An `aligned` row is re-checked by confirming that the chapter follows
  the Lean. A departure in a part the row does not cover gets a new row.

## Lemma checklist (the round's task list)

One commit per task, in this order. Each open task names its nodes (each read whole, a node with a
row included), the rows it re-checks and the pinned files it reads (under
`CombinatorialRigidity/Molecular/Molecule/Pencil/` unless the path says otherwise); chapter lines
are as at the open. **On landing, its line is cut to at most three lines** (the register since task
10, for the gate's forward weighting): its number and sub-phase; the commit; under *Open* and *No
departure*, the new rows by number and the nodes judged no departure by label only; under
*Re-checks*, the rows re-checked, accurate or corrected in place; and a pointer to any *Candidates*
or *Moved* line. The reasons stay in the landing commit's message and in the ledger's rows.

- [x] **1. Open** (`b753cace`; docs only): this log, the re-count, the criterion and the task
  list; `notes/Cleanup42.md`'s **Status**, §1 (the PI's entry of 2026-11-05) and §3; ROADMAP's
  Status row, §42's *Next* and the CLEANUP-42 bullet; the queue's comment on the row.

**42b–42f, never checked (47 nodes, no row).**

- [x] **2. 42b, realizations** (`def498ad`). Open: R-35; one *Moved* line. No departure:
  `def:extensor-through-flat`, `lem:extensor-through-flat-point`, `def:pencil-d-realization`,
  `-rank-hypothesis`, `-distinct-motive`, `lem:pencil-d-point-configuration`, `-rank-agrees-three`.
- [x] **3. 42b, configurations** (`d5996bfd`). No departure: R-36;
  `lem:pencil-d-config-realization`, `-x0-attains-three`, `-rank-collineation`, `-rank-scale-shift`,
  `-x0-one-witness`, `-join-independence-open`; `def:pencil-d-configuration`, `-x0-attains`.
- [x] **4. 42c** (`6cd638f4`). No departure: R-37; `def:pencil-d-embedding`,
  `lem:pencil-d-embedding-join`, `-embed-realization`, `-embed-config-rank`, `-x0-attains-of-le`,
  `-x0-attains-distinct`, `lem:screw-embedding-rank`, `thm:pencil-d-deficiency-two-le-three`.
- [x] **5. 42d** (`6cb0f5ad`). No departure: R-38; `lem:deficiency-planar-nonpos`, `-rigid-higher`,
  `-core-bound-d`, `-one-body-chain-d`, `-two-body-chain-d`, `lem:pencil-d-maximal-rigid-core`,
  `-chain-core`, `-core-positive-deficiency`, `def:pencil-d-usable-chain`, `thm:pencil-d-theorem-s`.
- [x] **6. 42e** (`bc4d78c4`). No departure: R-39; `lem:pencil-d-condition-linear`,
  `thm:pencil-d-flat-rank` (its first paragraph), `cor:pencil-d-flat-attains`,
  `cor:pencil-d-jj-flat`.
- [x] **7. 42f** (`a6ea14b9`). No new row. No departure: `lem:pencil-d-lifting-restrict`,
  `lem:pencil-contract-additive-kernel`, `thm:pencil-d-cut`, `-bridge`, `-contract-additive`,
  `cor:pencil-d-contract-rigid`.

**42g–42m, under the standing rule since 42g (52 nodes, 30 with a row).**

- [x] **8. 42g** (`84e4d098`). No departure: R-40; `thm:pencil-d-open-ear-long`. Re-checks: R-1 to
  R-6 accurate (R-1, R-2 `aligned`).
- [x] **9. 42h** (`2d8a3fc4`). No departure: R-41, R-42; `lem:pencil-d-insertion`, `-ear-data-open`,
  `def:pencil-d-ear-data`. Re-checks: R-8 (`aligned`), R-10, R-11 accurate; R-7, R-9, R-12
  corrected.
- [x] **10. 42i** (`f64d5734`). No departure: R-43. Re-checks: R-13 (`aligned`), R-14 accurate;
  R-15, R-16 corrected. One *Moved* line.
- [x] **11. 42j** (`1f20578c`). No departure: R-44, R-45; `lem:pencil-d-distinct-statement`.
  Re-checks: R-17 corrected.
- [x] **12. 42k** (`017581bd`). Open: R-46. No departure: R-47; `lem:pencil-d-projective-transport`,
  `-cut-reposition`, `-cut-case`, `thm:pencil-d-realization-theorem`. Re-checks: R-18, R-19
  accurate.
- [x] **13. 42l** (`5b25294b`). Open: R-48, R-49, R-50. No departure: `def:pencil-d-nondegenerate`,
  `lem:pencil-d-nondegenerate-three`, `def:pencil-d-lift`, `-lift-attains`. Re-checks: R-20 to R-23
  accurate (R-22 `aligned`). One *Moved* line.
- [x] **14. 42m, the cases** (this commit). Open: R-51. No departure: R-52. Re-checks: R-28 to R-30
  accurate; R-24 to R-27 corrected (the spike's declarations, landed in `Grade/LiftSmall.lean` and
  `Grade/LiftCases.lean`).
- [ ] **15. PD-HEAD's second half (42m), the rest.** `lem:pencil-d-lift-no-rigid`, `-good-ear`
  (5747–5932), `-ear-extend`, `-ear-free`, `thm:pencil-d-generic` and
  `cor:pencil-d-conditioned-pair` (6035–6359), 6 heavy nodes. Re-checks R-31 to R-34; fresh: the
  theorem and the corollary. Reads `Grade/LiftNoRigid.lean`, `Grade/GoodEar.lean` (and the core it
  calls, `MainComponent/GoodEar.lean`), `Grade/EarFree.lean`, `Grade/Generic.lean`.
- [ ] **16. The stop** (docs only; the planned stop, *Autopilot: for the PI*). The ledger's tally
  at the audit's end (rows by status, the new rows by task); the no-Lean-edit `git diff --stat`;
  a `NEEDS_PI` entry with each `open` row and its remedies and the *Candidates* lines; round 1
  closed (its whole scope is the audit), with ROADMAP's row, `notes/Cleanup42.md`'s **Status** and
  §3 pointing at the PI's answer, which plans rounds 2+.

## Candidates for the PI

- None yet.

## Moved to a later round

- **A missing `\uses` edge** (task 2; mirrored in `notes/Cleanup42.md` §3).
  `lem:pencil-d-point-configuration`'s statement reads the closed neighbourhood (`Graph.closedNbhd`,
  pinned by `def:pencil-nondegenerate` in `pencil.tex`) and does not `\uses` it;
  `scripts/blueprint-deps.py --label` reports the edge *missing*. The script reports 60 over the
  chapter (`--chapter pencil-d`), so a later round may take them in one sweep.
- **A prose slip** (task 10; mirrored in `notes/Cleanup42.md` §3). `thm:pencil-d-open-ear-four`'s
  proof calls an ear datum `y` ("Take an ear datum $y$ off all three zero sets", then "Keep the
  other points of $y$"), where `def:pencil-d-ear-data` and the same proof's first stage (`s^*`)
  write `s` for ear data, and the section writes `y` for points (`y_1`, `y_3`, …).
- **A prose slip** (task 13; mirrored in `notes/Cleanup42.md` §3).
  `lem:pencil-d-nondegenerate-maps` fixes `p : K^(d+1) → K^(d′+1)`, so (2)'s injective `p` has
  `d ≤ d′`, but its "in particular" embeds a realization in dimension `d′ ≤ d` into dimension `d`
  (`lem:pencil-d-embed-realization`'s letters): `d` and `d′` swap roles within one statement.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** task 15, PD-HEAD's second half (42m), the rest. One Opus recon reads the
six nodes `lem:pencil-d-lift-no-rigid`, `-good-ear`, `-ear-extend`, `-ear-free`,
`thm:pencil-d-generic` and `cor:pencil-d-conditioned-pair` against their pins in
`Grade/LiftNoRigid.lean`, `Grade/GoodEar.lean` (and `MainComponent/GoodEar.lean`),
`Grade/EarFree.lean` and `Grade/Generic.lean`, under *The audit's criterion*: each node read whole,
R-31 to R-34 re-checked at HEAD, the theorem and the corollary fresh (task 15's line), then one
docs commit: any new rows (from R-53), the ledger's **Status**, and task 15's line here, in the
three-line register. The theorem's induction (`liftAttains_of_simple`) calls the five case pins,
which drop hypotheses their nodes take (R-25, R-28 to R-30, R-51), so its case split may read
less than the chapter's. Task 14 found R-50 (task 13) stale in one clause: `mem_liftMaps_iff` has
five callers, not only the cut edge's (T2): also `pendant_T2` and `pendantTri_T2` (at an induced
subgraph, as the cut edge), `ear_T2` (at `G`), and `mem_liftMaps_pencilConfigPoint_iff`
(`Grade/LiftNoRigid.lean`, at any configuration); its correction in place is the coordinator's
call. Then the stop.

## Decisions made during this round

- **The slicing** (the open). By layer, as the PI asked, 42b–42f first; a slice is what one recon
  reads against its pins in one dispatch, so PD-STATE's 17 light nodes are two slices, PD-CARRIER's
  four and 42f's six heavier ones one each, and 42m's eleven two. 42i and 42j stay apart, as two
  layers. Within 42g–42m a node with a row is read whole, so a second departure gets its own row.
- **Round 1 closes at its stop** (task 16): the audit is its whole scope, and the PI's answer and
  the plan of rounds 2+ go to `notes/Cleanup42.md` §1 and §3.
