# CLEANUP-42 round 1 — the route audit (work log)

**Status:** in progress (opened 2026-11-05 at the PI's word, `notes/Cleanup42.md` §1). Round 1
of CLEANUP-42, the cleanup of `blueprint/src/chapter/pencil-d.tex`'s proofs whose Lean departs
from the chapter's route; its plan, the PI's words and the proof-route ledger are
`notes/Cleanup42.md`. The round compares each of the chapter's 99 green nodes with its pinned Lean
and adds a ledger row for each departure, re-checking R-1 to R-34 at HEAD; it edits no prose,
statement, pin or Lean. The open (task 1, docs only) sliced the nodes by layer into 14
one-dispatch Opus recon tasks, the 47 never-checked nodes of 42b–42f first, then a planned stop
(task 16) at which the PI picks a remedy per `open` row and plans rounds 2+. Tasks 2 to 4
(PD-STATE, PD-STABLE) added R-35 (`open`), R-36 and R-37 (`no departure`). **Next concrete task:**
task 5, COUNT-A and COUNT-B, the eleven nodes of `sec:pencil-d-deficiency` (*Lemma checklist*).
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

CLEANUP-42's row of `.claude/autopilot/queue.toml` is attended, so the autopilot driver stops
before it: the coordinator runs this round, which the PI opened (`notes/Cleanup42.md` §1,
2026-11-05). **One planned stop**, after the audit's last slice: task 16 writes a `NEEDS_PI` entry
here with the ledger's tally, each `open` row and its remedies, and the *Candidates* lines; the PI
picks a remedy per `open` row and plans rounds 2+ (`notes/Cleanup42.md` §3). An unplanned
`NEEDS_PI` entry also goes here, newest first, and the PI answers in an entry that starts
`**PI, <date>:**`. No entries yet.

## Current state

**Tasks 1 to 4 have landed** (task 4 this commit: one `no departure` row, R-37, the other eight
nodes no departure, no line under *Candidates* or *Moved to a later round*). The ledger has 37
rows, 28 `open`; the next row is R-38. Nothing is mid-stream; task 5 is next.

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
re-checks (accurate or corrected) and the nodes judged no departure.

- [x] **1. Open** (`b753cace`; docs only): this log, the re-count, the criterion and the task
  list; `notes/Cleanup42.md`'s **Status**, §1 (the PI's entry of 2026-11-05) and §3; ROADMAP's
  Status row, §42's *Next* and the CLEANUP-42 bullet; the queue's comment on the row.

**42b–42f, never checked (47 nodes, no row).**

- [x] **2. PD-STATE (42b), the realizations** (`def498ad`). `sec:pencil-d-realization` (lines
  69–298), 8 light nodes, against `Grade/Realization.lean` (all 16 pins). No re-checks. **New row:**
  R-35, `lem:pencil-d-agrees-three`'s first sentence (the pin drops the nonzero points and adds
  `dim q^⊥ = 3 ⇔ q ≠ 0`). **No departure:** `def:extensor-through-flat` (the definition verbatim);
  `lem:extensor-through-flat-point` (`span_singleton_le_iff_mem`, the proof's one line);
  `def:pencil-d-realization` (its conditions on `V(G)`, `dotPerp` the section's `Π^⊥`, the `d = 2`
  remark's pin at `Π_v = K³`); `lem:pencil-d-point-configuration` (the proof's steps: the join of
  `lem:panel-support-extensor-join`, `lem:decomposable-extensor-span-unique`'s argument at `d − 1`
  vectors, `lem:meet-two-hyperplanes`; "has the rows" as the row space, the carrier's reading
  throughout; (2)'s second part without independence, as the proof says);
  `def:pencil-d-rank-hypothesis` (the
  deficiency's `n` a parameter read at `k + 1`, 42b's encoding); `def:pencil-d-distinct-motive`
  (the rank hypothesis inlined, one realization with the independence);
  `lem:pencil-d-rank-agrees-three` (one framework for the first; the point form, then the polarity
  at one rank, for the second). One line under *Moved to a later round*.
- [x] **3. PD-STATE (42b), the configurations** (`d5996bfd`). `sec:pencil-d-carrier` (300–525),
  9 light nodes, against `Grade/Carrier.lean`, `Grade/Configuration.lean`,
  `Grade/Collineation.lean`, `Grade/Witness.lean`, `Grade/Contract.lean` and
  `Grade/JoinIndependence.lean` (all 20 pins). No re-checks. **New row:** R-36, **no departure**,
  `lem:pencil-d-contract-magnified-rank`'s `r ∈ W` (the pin takes any `r`, the curve being total
  in it; `r ∈ W` is the setting of `def:pencil-contract-lifting-system`, which the proof never
  reads); its proof is otherwise the chapter's map, with its inverse, at the bodies of `W`. **No
  departure:** `def:pencil-d-configuration` (the point `(x, y, z, 1)` by its blocks in `K^(m+3)`,
  `m = d − 2` heights, the rank that of `ofNormals` at grade `m + 1`; the `d = 2` and `d = 3`
  remarks pinned); `lem:pencil-d-config-realization` (the proof's steps: `dim Π_v ≤ 3` as the image
  of `K³` under the affine lift, `≥ 3` by the projection to the kept coordinates, the chapter's
  injectivity, on admissibility's three independent picture points; adjacent points independent as
  at `d = 3`; then `lem:pencil-d-point-configuration` (1), on the patched framework of its note; the
  normals nonzero by their last coordinate, which the proof leaves implicit);
  `def:pencil-d-x0-attains` (`def:pencil-x0-attains` at `m` heights: `L(q)^m` column by column, the
  Zariski-open set the non-roots in `L(q)^m` of one height polynomial, a selector `ends`, the
  deficiency at `m + 2`); `lem:pencil-d-x0-attains-three` (one height, the same rank, the
  polynomials renamed along `α × Fin 1 ≃ α`); `lem:pencil-d-rank-collineation` (the join under
  `⋀²g`, the complement isomorphism's law giving `det g · Λ_h`, one automorphism at every link,
  `lem:screw-map-rows`); `lem:pencil-d-rank-scale-shift` (the chapter's map, `a^i` read on `V(G)`
  from its coefficients, `T` a linear automorphism); `lem:pencil-d-x0-one-witness` (the `d = 3`
  proof with one section per height: `P = A · ∏ D_i · Q(q, Z(q))`, `R = Q(q, ·)`);
  `lem:pencil-d-join-independence-open` (the `2 × 2` minors, polynomial in the picture or in the
  heights, and a nonzero maximal minor). No line under *Candidates* or *Moved to a later round*:
  the script's two missing edges on these nodes are in task 2's sweep.
- [x] **4. PD-STABLE (42c)** (this commit). `sec:pencil-d-stable` (527–841), 9 light to medium
  nodes, against `CombinatorialRigidity/Molecular/Deficiency.lean` (its two pins),
  `Grade/Embedding.lean`, `Grade/ZeroHeights.lean`, `Grade/Configuration.lean` (one pin) and
  `Grade/Stable.lean` (all 22 pins). No re-checks. **New row:** R-37, **no departure**,
  `lem:deficiency-stable` (the equality by antisymmetry, `lem:deficiency-antitone` for one half and
  the chapter's case split on `c(P)` for the other, not as the common maximum over `c(P) = 0`; the
  "in particular" by `D′ ≥ d′ + 1`). **No departure:** `def:pencil-d-embedding` (`ι` the extension
  by zero along an index map fixing the last index, `φ = * ∘ ⋀²ι ∘ *⁻¹`, at every `k′ ≤ k`; `⋀²ι`
  injective by mathlib's `exteriorPower.map_injective_field`, the chapter's argument with a chosen
  left inverse of `ι` in place of the deletion `π`); `lem:pencil-d-embedding-join` (the proof's one
  line: `*⁻¹ C(u, w) = u ∨ w`, then `⋀²ι (u ∨ w) = ιu ∨ ιw`); `lem:screw-embedding-rank` (the
  chapter's `Z(G, φp) = φZ(G, p) + Z₀` with intersection `φZ₀′`, `Z₀` the motions of the framework
  with zero hinges, then rank–nullity at both grades; no `d′ ≤ d`, which the injectivity of `φ`
  forces); `lem:pencil-d-embed-realization` (the hinge `C(w₁, w₂)` for a basis of `A^⊥` by the
  argument of `lem:pencil-d-point-configuration` (2), the scalar absorbed in `w₁`; `b_v ∈ A^⊥` and
  `A^⊥ ⊆ Π_v` read as `b_v ∈ span {w₁, w₂}` and `w₁, w₂ ∈ Π_v`, at both grades; the per-link
  independence `linearIndependent_gradeEmbed_pair`, a step of the third pin; the deficiency
  parameter fixed, 42b's encoding); `lem:pencil-d-embed-config-rank` (the point of `(q, z)` is `ι`
  of that of `(q, z′)` coordinate by coordinate, so the framework is `(q, z′)`'s mapped along `φ`;
  `L(q)` a subspace); `lem:pencil-d-x0-attains-of-le` (the proof's steps: a non-root of `P`, so no
  loop and three members in each closed neighbourhood, a main picture off the product, the padded
  heights, `lem:pencil-d-x0-one-witness`); `lem:pencil-d-x0-attains-distinct` (a non-root `q`,
  heights off `R`, `lem:pencil-d-config-realization`); `thm:pencil-d-deficiency-two-le-three` (the
  dimension-three case through `x0AttainsGrade_one_iff`, `def₂ + 3 ≤ 6 = bodyBarDim 3`, `d′ = 3`,
  `m ≥ 1` for `d ≥ 3`). No line under *Candidates* or *Moved to a later round*: the script's two
  missing edges on these nodes are in task 2's sweep, and its *unbacked* edge from
  `-embed-realization` to `-point-configuration` is to the argument the proof cites, whose helper
  (`exists_smul_panelSupportExtensor_eq_of_extensorInPanel`) the Lean shares with that node's pin.
- [ ] **5. COUNT-A and COUNT-B (42d).** `sec:pencil-d-deficiency` (843–1204), 11 medium nodes
  (Theorem S's proof is 42 lines). COUNT-A: `lem:deficiency-planar-nonpos`,
  `lem:deficiency-rigid-higher`, `lem:deficiency-core-bound-d`, `lem:deficiency-one-body-chain-d`,
  `lem:deficiency-two-body-chain-d`, `lem:deficiency-tight-part`. COUNT-B:
  `def:pencil-d-usable-chain`, `lem:pencil-d-maximal-rigid-core`, `thm:pencil-d-theorem-s`,
  `lem:pencil-d-core-positive-deficiency`, `lem:pencil-d-chain-core`. Reads
  `CombinatorialRigidity/Molecular/Induction/SparseDeficiency.lean` (its six pins) and
  `Grade/TheoremS.lean`.
- [ ] **6. PD-CARRIER (42e).** `sec:pencil-d-induction` and `sec:pencil-d-flat` (1206–1551), 4
  medium nodes (proofs of 13 to 46 lines): `lem:pencil-d-condition-linear`,
  `thm:pencil-d-flat-rank`, `cor:pencil-d-flat-attains`, `cor:pencil-d-jj-flat`. Reads
  `Grade/ConditionLinear.lean`, `Grade/Flat.lean`.
- [ ] **7. PD-STEPS (42f), the cut and the contraction.** `sec:pencil-d-cut` and
  `sec:pencil-d-contract` (1553–2115), 6 heavy nodes (`thm:pencil-d-contract-additive`'s proof is
  149 lines): `lem:pencil-d-lifting-restrict`, `thm:pencil-d-cut`, `thm:pencil-d-bridge`,
  `lem:pencil-contract-additive-kernel`, `thm:pencil-d-contract-additive`,
  `cor:pencil-d-contract-rigid`. Reads `Grade/Cut.lean`, `MainComponent/Cut.lean` (one pin,
  `eval_restrictPoly`) and `Grade/ContractAdditive.lean`.

**42g–42m, under the standing rule since 42g (52 nodes, 30 with a row).**

- [ ] **8. PD-STEPS (42g), `-long`.** `sec:pencil-d-long` (3424–3932), 7 heavy nodes. Re-checks
  R-1 (`lem:pencil-d-polygon-star`), R-2 (`-polygon-insert`), R-3 (`-polygon-normal`), R-4
  (`-polygons`), R-5 and R-6 (`thm:pencil-d-cycle`); fresh: `lem:pencil-d-polygon-collapse`,
  `thm:pencil-d-open-ear-long`. Reads `Grade/Polygon.lean`, `Grade/Chain.lean`.
- [ ] **9. PD-STEPS (42h), `-short-four`.** `sec:pencil-d-short` (2301–3422) less 42i's four, 8
  heavy nodes. Re-checks R-7 and R-11 (`lem:pencil-d-two-stars`), R-8 (`-stars-four`), R-9
  (`-kernel-curve`), R-10 (`lem:pencil-d-ear-data`), R-12 (`thm:pencil-d-open-ear-four`); fresh:
  `lem:pencil-d-insertion`, `def:pencil-d-ear-data`, `lem:pencil-d-ear-data-open`. Reads
  `Grade/Stars.lean`, `Grade/EarData.lean`, `Grade/Short.lean`.
- [ ] **10. PD-STEPS (42i), `-short-three`.** The other four nodes of `sec:pencil-d-short`, heavy,
  each with a row: re-checks R-13 (`lem:pencil-d-stars-three`), R-14
  (`thm:pencil-d-open-ear-three`), R-15 (`lem:pencil-d-planes-meet`), R-16
  (`lem:pencil-d-glued-ends`). Reads `Grade/StarsThree.lean`, `Grade/GluedEnds.lean`,
  `Grade/PlanesMeet.lean`, `Grade/ShortThree.lean`.
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

**Next concrete task:** task 5, COUNT-A and COUNT-B (42d). One Opus recon reads the eleven nodes
of `sec:pencil-d-deficiency` (Theorem S's proof is 42 lines) against their pins in
`CombinatorialRigidity/Molecular/Induction/SparseDeficiency.lean` (its six pins) and
`Grade/TheoremS.lean` under *The audit's criterion*, then lands one docs commit: any new rows in
`notes/Cleanup42.md` §2 (from R-38), its **Status** counts, and task 5's line here with its
verdicts. Theorem S's fold is §3's, not raised again. Then tasks 6–15 in order, and the stop.

## Decisions made during this round

- **The slicing** (the open). By layer, as the PI asked, 42b–42f first; a slice is what one recon
  reads against its pins in one dispatch, so PD-STATE's 17 light nodes are two slices, PD-CARRIER's
  four and 42f's six heavier ones one each, and 42m's eleven two. 42i and 42j stay apart, as two
  layers. Within 42g–42m a node with a row is read whole, so a second departure gets its own row.
- **Round 1 closes at its stop** (task 16): the audit is its whole scope, and the PI's answer and
  the plan of rounds 2+ go to `notes/Cleanup42.md` §1 and §3.
