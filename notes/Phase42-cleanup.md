# CLEANUP-42 round 1 — the route audit (work log)

**Status:** in progress (opened 2026-11-05 at the PI's word, `notes/Cleanup42.md` §1). Round 1
of CLEANUP-42, the cleanup of `blueprint/src/chapter/pencil-d.tex`'s proofs whose Lean departs
from the chapter's route; its plan, the PI's words and the proof-route ledger are
`notes/Cleanup42.md`. The round compares each of the chapter's 99 green nodes with its pinned Lean
and adds a ledger row for each departure, re-checking R-1 to R-34 at HEAD; it edits no prose,
statement, pin or Lean. The open (task 1, docs only) sliced the nodes by layer into 14
one-dispatch Opus recon tasks, the 47 never-checked nodes of 42b–42f first, then a planned stop
(task 16) at which the PI picks a remedy per `open` row and plans rounds 2+. Tasks 2 to 9
(PD-STATE, PD-STABLE, COUNT-A and COUNT-B, PD-CARRIER, 42f's to 42h's PD-STEPS) added R-35
(`open`), R-36 to R-42 (`no departure`); tasks 8 and 9 re-checked R-1 to R-12, correcting R-7, R-9
and R-12 in place. **Next concrete task:** task 10, PD-STEPS (42i), the other four nodes of
`sec:pencil-d-short`, re-checking R-13 to R-16 (*Lemma checklist*). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

CLEANUP-42's row of `.claude/autopilot/queue.toml` is attended, so the autopilot driver stops
before it: the coordinator runs this round, which the PI opened (`notes/Cleanup42.md` §1,
2026-11-05). **One planned stop**, after the audit's last slice: task 16 writes a `NEEDS_PI` entry
here with the ledger's tally, each `open` row and its remedies, and the *Candidates* lines; the PI
picks a remedy per `open` row and plans rounds 2+ (`notes/Cleanup42.md` §3). An unplanned
`NEEDS_PI` entry also goes here, newest first, and the PI answers in an entry that starts
`**PI, <date>:**`. No entries yet.

## Current state

**Tasks 1 to 9 have landed** (task 9 this commit: two `no departure` rows, R-41 and R-42; R-8,
R-10 and R-11 accurate at HEAD, R-7, R-9 and R-12 corrected in place; the three fresh nodes no
departure; no line under *Candidates* or *Moved to a later round*). The ledger has 42 rows, 28
`open`; the next row is R-43. Nothing is mid-stream; task 10 is next.

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

One commit per task, in this order. Each recon task names its nodes (each read whole, a node with
a row included), the rows it re-checks and the pinned files it reads (under
`CombinatorialRigidity/Molecular/Molecule/Pencil/` unless the path says otherwise); chapter lines
are as at the open. On landing, its line gets its commit and its verdicts: the new rows, the
re-checks (accurate or corrected) and the nodes judged no departure, a few words each; the landing
commit's diff keeps the longer reasons (tasks 2–5's lines were cut to this register at task 6, for
the gate's forward weighting).

- [x] **1. Open** (`b753cace`; docs only): this log, the re-count, the criterion and the task
  list; `notes/Cleanup42.md`'s **Status**, §1 (the PI's entry of 2026-11-05) and §3; ROADMAP's
  Status row, §42's *Next* and the CLEANUP-42 bullet; the queue's comment on the row.

**42b–42f, never checked (47 nodes, no row).**

- [x] **2. PD-STATE (42b), the realizations** (`def498ad`). `sec:pencil-d-realization`, 8 light
  nodes, against `Grade/Realization.lean`. **New row:** R-35 (`lem:pencil-d-agrees-three`'s first
  sentence, `open`). **No departure:** `def:extensor-through-flat` (verbatim);
  `lem:extensor-through-flat-point` (the proof's one line); `def:pencil-d-realization` (on `V(G)`);
  `lem:pencil-d-point-configuration` (the proof's steps, "has the rows" as the row space);
  `def:pencil-d-rank-hypothesis` and `def:pencil-d-distinct-motive` (42b's encodings);
  `lem:pencil-d-rank-agrees-three` (one framework; the point form, then the polarity). One line
  under *Moved to a later round*.
- [x] **3. PD-STATE (42b), the configurations** (`d5996bfd`). `sec:pencil-d-carrier`, 9 light
  nodes, against `Grade/Carrier.lean`, `-Configuration`, `-Collineation`, `-Witness`, `-Contract`
  and `-JoinIndependence`. **New row:** R-36 (`lem:pencil-d-contract-magnified-rank`'s `r ∈ W`,
  `no departure`). **No departure:** `def:pencil-d-configuration` (the point by its blocks, `m`
  heights); `lem:pencil-d-config-realization` (the proof's steps); `def:pencil-d-x0-attains` and
  `lem:pencil-d-x0-attains-three` (`def:pencil-x0-attains` at `m` heights; one height);
  `-rank-collineation` (the join under `⋀²g`); `-rank-scale-shift` (the chapter's map);
  `-x0-one-witness` (the `d = 3` proof, one section per height); `-join-independence-open` (the
  `2 × 2` minors).
- [x] **4. PD-STABLE (42c)** (`6cd638f4`). `sec:pencil-d-stable`, 9 light to medium nodes,
  against `Molecular/Deficiency.lean`, `Grade/Embedding.lean`, `-ZeroHeights`, `-Configuration`
  and `-Stable`. **New row:** R-37 (`lem:deficiency-stable`'s equality, by antisymmetry, `no
  departure`). **No departure:** `def:pencil-d-embedding` (`⋀²ι` injective by mathlib, a left
  inverse of `ι` for `π`); `lem:pencil-d-embedding-join` (the one line); `lem:screw-embedding-rank`
  (the chapter's split, then rank–nullity); `lem:pencil-d-embed-realization` (the argument of
  `-point-configuration` (2), so the *unbacked* edge to it); `-embed-config-rank` (`ι` coordinate
  by coordinate); `-x0-attains-of-le`, `-x0-attains-distinct` (the proofs' steps);
  `thm:pencil-d-deficiency-two-le-three` (`d′ = 3`).
- [x] **5. COUNT-A and COUNT-B (42d)** (`6cb0f5ad`). `sec:pencil-d-deficiency`, 11 medium nodes,
  against `Molecular/Induction/SparseDeficiency.lean` and `Grade/TheoremS.lean`. **New row:** R-38
  (`lem:deficiency-tight-part`'s case `Z = V(G)`, `no departure`). **No departure**, each the
  chapter's steps in its order: `lem:deficiency-planar-nonpos`, `-rigid-higher`, `-core-bound-d`,
  `-one-body-chain-d`, `-two-body-chain-d`; `def:pencil-d-usable-chain` (verbatim);
  `lem:pencil-d-maximal-rigid-core`, `thm:pencil-d-theorem-s`, `lem:pencil-d-chain-core`,
  `-core-positive-deficiency` (its two *unbacked* edges the helpers the chapter cites). The two
  dead pins are §3's fold.
- [x] **6. PD-CARRIER (42e)** (`bc4d78c4`). `sec:pencil-d-induction` and `sec:pencil-d-flat`, 4
  medium nodes, against `Grade/ConditionLinear.lean` and `Grade/Flat.lean` (13 pins, 12 distinct).
  **New row:** R-39 (`thm:pencil-d-flat-rank`'s second paragraph, a second proof no Lean follows,
  `no departure`). **No departure:** `lem:pencil-d-condition-linear` (the chapter's steps: `π` an
  isomorphism of `S` onto `K³` when `dim S ≤ 3`; the converse by `S ⊆ range σ_v` and three
  independent points, where the chapter says `π(S) = K³`; `Π_v^⊥` by `finrank_dotPerp`; the "in
  particular" on heights vanishing off `V(G)`, R-6's restriction); `thm:pencil-d-flat-rank`'s first
  paragraph (the Lean's; its equivalence at every `n`, read at `2` and at `d`);
  `cor:pencil-d-flat-attains` and `cor:pencil-d-jj-flat` (the chapter's steps in its order). The
  one missing edge is task 2's sweep; a note for tasks 9 and 10 (now on task 10's line).
- [x] **7. PD-STEPS (42f), the cut and the contraction** (`a6ea14b9`). `sec:pencil-d-cut` and
  `sec:pencil-d-contract`, 6 heavy nodes, against `Grade/Cut.lean`, `MainComponent/Cut.lean`
  (`eval_restrictPoly`) and `Grade/ContractAdditive.lean`. **No new row. No departure:**
  `lem:pencil-d-lifting-restrict` (column by column; (3) one substitution at `α × Fin m`, its dead
  pin the `rfl` bridge to the tuple); `thm:pencil-d-cut` (the three parts in order; the deficiency
  identity's `≥` half, all the one-witness "at least" asks); `thm:pencil-d-bridge` (the same, with
  `lem:block-rank-cut`'s pendant form and parts (3), (1) along the path; hinges by
  `-config-realization`'s pair pin, at any heights); `lem:pencil-contract-additive-kernel` (its two
  chains; `A` the product the proof names); `thm:pencil-d-contract-additive` (its six parts in
  order; `N` the rank at `b′`, then `tgt_d(G/H)`; the *unbacked* edge to
  `lem:pencil-contract-standing` the two lemmas its pin is built of, all JJ's equality asks, as at
  `d = 3`); `cor:pencil-d-contract-rigid` (the steps in order). The `d = 3` inline kernel copy is
  FRICTION's open fold (design doc §3), not raised again.

**42g–42m, under the standing rule since 42g (52 nodes, 30 with a row).**

- [x] **8. PD-STEPS (42g), `-long`** (`84e4d098`). `sec:pencil-d-long`, 7 heavy nodes, against
  `Grade/Polygon.lean` and `Grade/Chain.lean`. **New row:** R-40
  (`lem:pencil-d-polygon-collapse`'s pins at index level, no `Y` and no join, `no departure`; its
  distinctness pin dead, as independent joins need no distinct edges). **No departure:**
  `thm:pencil-d-open-ear-long` (the chapter's steps; the placement, then a certificate as at the
  cycle; the rank's `≥` half, `D` independent hinges in `ρ + Λ`; the lift height by height).
  **Re-checks, all accurate:** R-1, R-2 (`aligned`: the star's two cases, the insertion's line off
  `A`, are the chapter's proofs); R-3 (`g₁`, then the transvection; part (1) and the joins under
  `⋀²g` the chapter's); R-4 (the three minors; the step and the move at `i = 0` the chapter's); R-5
  (`N = min(m, D)`, `polygonCollapse N m`); R-6 (`z` restricted to `V(G)`; the rest of the cycle
  the chapter's count, the singletons' value as a bound).
- [x] **9. PD-STEPS (42h), `-short-four`** (this commit). `sec:pencil-d-short` less 42i's four, 8
  heavy nodes, against `Grade/Stars.lean`, `-EarData` and `-Short`. **New rows,** `no departure`:
  R-41 (`lem:pencil-d-ear-data` (1) reads the base data at `q`, the move from `q₁` by
  `lem:pencil-picture-local` its caller's); R-42 (the open ear's planes: `σ_v` at `z*`'s affine
  coefficients, no span; the condition lemma's citation). **No departure:** `lem:pencil-d-insertion`
  (its steps, the gain `lem:pencil-insertion`'s proof); `def:pencil-d-ear-data` (`σ_a` as
  `gradeSigma`, the conditions where used); `lem:pencil-d-ear-data-open` (its steps, the minors
  `normalsJoinPoly`). **Re-checks:** R-8 (aligned), R-10, R-11 accurate; corrected in place: R-7
  (stars-three cites on forms since 42i), R-9 (a basis `M(y₀)u_j`, not columns of `A`), R-12 (the
  stages in 42i's `_of_base`).
- [ ] **10. PD-STEPS (42i), `-short-three`.** The other four nodes of `sec:pencil-d-short`, heavy,
  each with a row: re-checks R-13 (`lem:pencil-d-stars-three`), R-14
  (`thm:pencil-d-open-ear-three`), R-15 (`lem:pencil-d-planes-meet`), R-16
  (`lem:pencil-d-glued-ends`). Reads `Grade/StarsThree.lean`, `Grade/GluedEnds.lean`,
  `Grade/PlanesMeet.lean`, `Grade/ShortThree.lean`. Task 6's note: the condition lemma's pins
  other than `gradeSigma` are dead; `-planes-meet` and the theorem reach it for `σ_v` and its facts
  (`gradeSigma_injective`, `pencilConfigPointGrade_eq_gradeSigma_iff`), not its equivalences, so
  their proofs' citations of it are read against those (task 9 did the four-body pair, R-42).
- [ ] **11. PD-COVERAGE (42j).** `sec:pencil-d-chains` (2117–2299) and `sec:pencil-d-coverage`
  (3934–4139), 4 medium to heavy nodes (the coverage's proof is 131 lines). Re-checks R-17
  (`lem:pencil-d-chain-count`); fresh: `thm:pencil-d-chain-or-core`, `thm:pencil-d-coverage`,
  `lem:pencil-d-distinct-statement`. Reads `Grade/Chains.lean`, `Grade/Coverage.lean`, and the
  `MainComponent/` reductions the coverage calls.
- [ ] **12. PD-REDUCTION (42k).** `sec:pencil-d-reduction` (4141–4629), 8 medium nodes. Re-checks
  R-18 (`lem:pencil-d-base-case`), R-19 (`lem:pencil-d-nonsimple-case`); fresh:
  `lem:pencil-d-two-pencil-extension`, `lem:pencil-d-projective-transport`,
  `lem:pencil-d-cut-reposition`, `lem:pencil-d-loop-case`, `lem:pencil-d-cut-case`,
  `thm:pencil-d-realization-theorem`. Reads `Grade/TwoPencil.lean`, `Grade/Arms.lean`,
  `Grade/Reduction.lean`.
- [ ] **13. PD-HEAD's first half (42l).** `sec:pencil-d-nondegenerate` and `sec:pencil-d-lift`
  (4631–5392), 10 nodes, heavy (feasibility's proof is 96 lines). Re-checks R-20
  (`lem:pencil-d-nondegenerate-feasible`), R-21 (`-lift-one-witness`), R-22 (`-steer`), R-23
  (`-lift-transfer`); fresh: `def:pencil-d-nondegenerate`, `lem:pencil-d-nondegenerate-three`,
  `lem:pencil-d-nondegenerate-maps`, `def:pencil-d-lift`, `lem:pencil-d-lift-realization`,
  `def:pencil-d-lift-attains`. Reads `Grade/Nondegenerate.lean`, `Grade/Feasible.lean`,
  `Grade/Lift.lean`, `Grade/LiftWitness.lean`, `Grade/Generic.lean` (one pin).
- [ ] **14. PD-HEAD's second half (42m), the cases.** `lem:pencil-d-lift-small`,
  `-lift-cut-edge`, `-lift-pendant`, `-lift-pendant-triangle` (5424–5742) and `-lift-ear`
  (5936–6013), 5 heavy nodes, each with rows: re-checks R-24 to R-30. Reads
  `Grade/LiftSmall.lean`, `Grade/LiftCutEdge.lean`, `Grade/LiftCases.lean`.
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

## Blockers / open questions

- None.

## Hand-off / next phase

**Next concrete task:** task 10, PD-STEPS (42i), `-short-three`. One Opus recon reads the other
four heavy nodes of `sec:pencil-d-short` (`lem:pencil-d-stars-three`, `-glued-ends`,
`-planes-meet`, `thm:pencil-d-open-ear-three`) against their pins in `Grade/StarsThree.lean`,
`Grade/GluedEnds.lean`, `Grade/PlanesMeet.lean` and `Grade/ShortThree.lean` under *The audit's
criterion*: it re-checks R-13 to R-16 at HEAD (R-13 `aligned`, by confirming that the chapter
follows the Lean), and reads the citations of the condition lemma in `-planes-meet` and the
theorem against task 6's note on its line, as R-42 did at four bodies, then lands one docs commit:
any new rows in `notes/Cleanup42.md` §2 (from R-43), its **Status**, and task 10's line here with
its re-checks. Then tasks 11–15 in order, and the stop.

## Decisions made during this round

- **The slicing** (the open). By layer, as the PI asked, 42b–42f first; a slice is what one recon
  reads against its pins in one dispatch, so PD-STATE's 17 light nodes are two slices, PD-CARRIER's
  four and 42f's six heavier ones one each, and 42m's eleven two. 42i and 42j stay apart, as two
  layers. Within 42g–42m a node with a row is read whole, so a second departure gets its own row.
- **Round 1 closes at its stop** (task 16): the audit is its whole scope, and the PI's answer and
  the plan of rounds 2+ go to `notes/Cleanup42.md` §1 and §3.
