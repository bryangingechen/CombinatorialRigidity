# Phase 42m — PD-HEAD: the generic conjunct and the headline in every dimension (work log)

**Status:** ✓ closed 2026-11-05 (opened the same day at the PI's word, "All 11 as written", design
doc §1), the second and last sub-phase of Phase 42's last layer, PD-HEAD, so its close closed Phase
42 (PENCIL-D). Forward mode, the Lean under `/coordinate-phase`: the eleven nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-generic` are green, as the chapter states
them, in 14 commits: the open, the recon, eight builds and the close in four parts. With them every
node of the chapter is green, and the headline, `Graph.graded_pencil_conditioned_pair`, is Phase
42's one `main_results` row (the PI's (A)). The route differences, `notes/Cleanup42.md` R-24 to
R-34, wait for CLEANUP-42. Next (*Hand-off*): CLEANUP-42, then ORIGAMI, each opening with the PI.

## Current state

**Closed.** Over every infinite field and in every dimension `d ≥ 3`, the generic conjunct
(`thm:pencil-d-generic`: `hasGradedGenericPencilRealization_of_simple`, by the strong induction
`liftAttains_of_simple` on `V(G).ncard`, with the remark
`LiftAttains.hasGradedGenericPencilRealization`) and the headline (`cor:pencil-d-conditioned-pair`:
`Graph.graded_pencil_conditioned_pair`, three conjuncts, the first two
`Graph.graded_pencil_realization_theorem`'s) are formalized, in `Pencil/Grade/`: `LiftSmall.lean`
(build 1: at most two bodies, the triangle, no cut edge), `LiftCases.lean` (build 2: the pendant,
the ear with `EarLiftCondition`, the pendant triangle), `LiftCutEdge.lean` (build 3: the cut edge,
its glue new), `GoodEar.lean` (build 4: `Graph.IsPencilGoodEar` and
`Graph.IsX0Graph.exists_goodEar_or_pendantTriangle`, the core in `MainComponent/GoodEar.lean`),
`LiftNoRigid.lean` (build 5: no planar-rigid set, with the shared steps), `EarFree.lean` (builds 6a
and 6b: `exists_earExtend_poly`, `holdsGenerally_earFree`) and `Generic.lean` (build 7). The close:
part 1 ran the whole-project `lake build` (6247 jobs, 0 warnings) and `lake lint` on the final Lean
tree, found the 20 main results' `#print axioms` byte-identical to 41e's close and Phase 42's seven
candidates on `[propext, Classical.choice, Quot.sound]`, and fixed `Grade/Generic.lean`'s docstring;
part 2 re-read the chapter end to end, gave the exposition ledger 42m's and Phase 42's judgment (no
entry), compressed the design doc and this note's *Decisions made* and reviewed the project's
organization; part 3 added the headline's `main_results` row and `alignment` entry, with its witness
`graded_pencil_conditioned_pair_witness` in `Nonvacuity.lean` (the distinct conjunct at `K₁,₃`,
`m = 2`, dimension four), and ran the 21 rows' axioms check; part 4 flipped ROADMAP's row and §42
and re-summarized the user-facing surfaces, the program map, the queue row and the design doc's
header. No Lean changed after part 3. The recon's spike, the gitignored `scratch/42m/Spike.lean`, is
no longer needed.

**Statement faithfulness** (no pin weaker than its node): `-lift-pendant` drops "whose neighbour `u`
has another neighbour" and `-lift-ear` drops "not adjacent" (both unused, R-25 and the ear's rank by
`lem:block-rank-ear`, which needs no non-adjacency); `-lift-small`'s two-body pin adds the ambient
`[Nonempty α]`, as at no body over an empty `α` with labels the carrier's `LiftAttains` asks for a
selector `β → α × α` that does not exist (the chapter's proof treats one and two bodies; the theorem
always has a body; reported to the PI as an encoding, no objection); `-lift-small` (2) is pinned
without `G.Simple` and without `[Infinite K]` (build 1's proof needs neither; `notes/Cleanup42.md`
R-28); `-lift-cut-edge` drops `|V₁|, |V₂| ≥ 2` (unused, R-30); `-lift-no-rigid` is pinned as its
node states it (R-32); `-ear-extend` drops `G` simple and the neighbour selector (unused, R-33);
`-ear-free` is pinned as its node states it (R-34); encodings: "a triangle" as three pairwise
adjacent bodies, "at a general nondegenerate realization" as `HoldsGenerally` at the given
selectors, `Γ_L` inside `Γ(G)`'s parameter type, "a nonzero polynomial" as one with a non-root.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eleven nodes of `-generic` as the chapter
  states them; its close is Phase 42's full close, where Tier 0's `main_results` row and the
  headline's are decided (design doc §3).
- **Encoding** as 42b–42l: grade `k = d − 1`, Lean's `m = d − 2`; a lift's `r = d − 3` coordinates.
- **What 42l and 42k hand on**: `Grade/Nondegenerate.lean`, `Feasible.lean`, `Lift.lean`,
  `LiftWitness.lean`, and `Graph.graded_pencil_realization_theorem` (`Grade/Reduction.lean`).
- **The standing rule** (design doc §3): every recon and build adds a `notes/Cleanup42.md` §2 row
  where its Lean departs from the chapter's proof, in the same commit. Open: R-3 to R-5, R-9 to
  R-12, R-14 to R-21, R-23 to R-34; aligned: R-1, R-2, R-7, R-8, R-13, R-22; R-6 no departure.

## Lemma checklist

- [x] **Open** `64c2fc88`; **pre-build recon** `305aa023` (eleven signatures pinned, three spiked).
- [x] `lem:pencil-d-lift-small`, both parts: build 1, `3a1fe6ed` (R-27, R-28).
- [x] `lem:pencil-d-lift-pendant`, `-lift-ear`, `-lift-pendant-triangle`: build 2, `fd5e8726` (R-24
  to R-26, R-29).
- [x] `lem:pencil-d-lift-cut-edge`: build 3, `f56ac39c` (R-30).
- [x] `lem:pencil-d-good-ear`: build 4, `3185ddae` (R-31).
- [x] `lem:pencil-d-lift-no-rigid`: build 5, `8b872304` (R-32).
- [x] `lem:pencil-d-ear-extend`: build 6a, `e2d13219` (R-33); `lem:pencil-d-ear-free`: build 6b,
  `505070b1` (R-34).
- [x] `thm:pencil-d-generic` and `cor:pencil-d-conditioned-pair`: build 7, `21608ae6` (no new row).
- [x] **Close**, the full close of 42m and Phase 42 together: part 1 `e186a885`, part 2 `be462b0c`,
  part 3 `c1d39783`, and part 4, the commit "Phase 42m CLOSES, and with it Phase 42". The
  dispatch-log grooming is the coordinator's, after it.

## Blockers / open questions

- None. Two instances no `main_results` witness exhibits, the generic conjunct's feasibility
  hypothesis at a small graph (likely `K₂`) and the predicates `Graph.IsPencilGoodEar` and
  `EarLiftCondition` (candidate `K_{2,3}`), are CLEANUP-42's (`notes/Cleanup42.md` §3).

## Hand-off / next phase

**Phase 42 is closed; no phase is active.** The next concrete task is opening CLEANUP-42 with the
PI (attended; planning note `notes/Cleanup42.md`, whose input is the proof-route ledger, 34 rows,
27 `open`, and whose §3 lists what else is left to it; ROADMAP *Queued post-program phases*). Its
place ahead of ORIGAMI is the coordinator's proposal, which its open settles with the PI; ORIGAMI
follows, with the PI. Neither is opened here, and their queue rows stay as they are until their
opens. **Deferred, where it lands:** design doc §3, the *Deferred to …* paragraphs of each layer,
42m's among them (*Deferred to CLEANUP-42 and after from 42m*: build 6's helpers and two mirror
candidates); FRICTION's `[open]` entries for 42b–42l carry the same home debts.

## Decisions made during this phase

Compressed to one-line verdicts at the close's part 2 (the full entries are in git up to `e186a885`).
- **PI, 2026-11-05 (42m's open):** the PI answered "All 11 as written (Recommended)", whose option
  read: "An Opus open commit, then a pre-build recon that spikes all 11 against Phase 39's d = 3
  Lean and 42l's Lean. Then roughly 4–7 builds (my estimate) and the close of 42m and Phase 42
  together." The question as put, the other options and a note on them: design doc §1.
- **The open:** all eleven nodes passed the consistency read; their 46 outside dependencies green.
- **Recon, the `d = 3` Lean:** the steer lemma, `PencilNondegFeasible`'s API and the assembly's case
  split reused; `GoodEar.lean`'s proof re-opened; Pair.lean's reposition not transcribable.
- **Recon, the induction:** `liftAttains_of_simple`, strong induction on `V(G).ncard`; each case
  `lift_transfer` then `liftAttains_of_holdsGenerally`, (T1)'s `E` by `exists_minorPoly` minors.
- **Recon, the ear:** one predicate, `EarLiftCondition`, at the same selectors on both sides; the
  good ear returns `W₀` (`Graph.IsPencilGoodEar`); the headline a three-conjunct theorem.
- **Recon, shared steps:** `exists_holdsGenerally_finrank_liftSpaceTilde_le` exposed; R-24 to R-27.
- **Build 3:** the cut edge's glue by one frame map and one minor, no normal changed (R-30).
- **Build 5:** the least `dim L̃` through the lifting system's kernel, no map `g`, no `ℓ₀` (R-32).
- **Build 6a:** `E_L` by one witness per condition, the `n_u` chosen greedily (R-33).
- **Build 6b:** every lift of `Y` trivial by an embedding (`liftTildeOfTrivial`), no count of
  `L(b⁰)` (R-34).
- **Close, part 1:** every gate clean on the final tree; the 20 rows' axioms byte-identical to 41e's
  close; the seven candidates on the three standard axioms; `Grade/Generic.lean`'s docstring fixed.
- **Close, part 2 (2026-11-05, docs only):** the chapter's re-read found no step that fails and no
  formalization aside; the opening now states the theorem as proved, naming
  `cor:pencil-d-conditioned-pair`. The ledger's 42m section judges 42m and Phase 42: no entry. The
  design doc 1304 → 1111 lines (one Lean anchor, into §2.3; §1 and §2 byte-identical, §2 frozen;
  42m's deferrals moved to its §3). The organization review: the `CLAUDE.md` suite unchanged since
  2026-10-25, no extraction due; FRICTION's three `[resolved]` entries swept to the archive; no
  *Choices to revisit* entry answered; ROADMAP's directory layout names `Molecule/Pencil/`.
- **PI, 2026-11-05 (Phase 42's main_results rows):** the PI answered "(A) headline only
  (Recommended)", whose option read: "One row: the headline. Its description and a new alignment
  entry name the route (the coverage, the reduction, the generic theorem), the way Phase 40's rows
  name x0Dist and x0Gen without rows of their own. Witness: the distinct conjunct at the star K₁,₃
  in dimension four, as the d = 3 witnesses do." The question as put, the other options and a note
  on them (the coordinator's words; (A) without (C), so the generic conjunct's hypothesis stays
  unwitnessed by a row, an open item in `notes/Cleanup42.md` §3): design doc §1.
- **Close, part 3 (2026-11-05):** one `main_results` row and one `alignment` entry, the headline,
  naming the route; `graded_pencil_conditioned_pair_witness` at `K₁,₃`, `m = 2`; the harness's 21
  rows, the first 20 byte-identical to part 1's run, the new one on the three standard axioms.
- **Close, part 4 (2026-11-05, docs only):** ROADMAP's row ✓ and §42 one paragraph; README, the
  home page, `intro.tex`, `formalization.yaml`'s `status.scope` (the new row named) and
  `fidelity.divergences` (the `[Nonempty α]` pin, the ledger), the program map,
  `notes/Cleanup42.md`'s status, the queue row `done`; this note and the design doc's header closed.
