# Phase 42l — PD-HEAD: nondegenerate realizations and their lifts in every dimension (work log)

**Status:** in progress, opened 2026-11-04 at the PI's word ("Nondegenerate + lift only", design
doc §1), the first sub-phase of Phase 42's last layer, PD-HEAD. Forward mode, the Lean under
`/coordinate-phase`: the ten red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-nondegenerate` and `sec:pencil-d-lift`, as the chapter states them. The eleven nodes
of `sec:pencil-d-generic` stay red for a later sub-phase at the PI's word, so 42l's close does not
close Phase 42. The pre-build recon spiked all ten complete, with no `sorry`, and pinned four
builds (*Current state*); four route differences go to the cleanup (`notes/Cleanup42.md` R-20 to
R-23). Builds 1 to 3 landed (8 nodes green, 2 red left). Next (*Hand-off*): build 4, `Grade/LiftWitness.lean`.

## Current state

**Build 1 landed** (`Grade/Nondegenerate.lean`, 3 nodes green, 0 warnings; imports `Grade.Embedding` only; the spike's lines 16–278, its one `show` now `change`). **Build 2 landed** (`Grade/Feasible.lean`, `lem:pencil-d-nondegenerate-feasible` green, 0 warnings, `lake lint` clean; also imports `Mathlib.Algebra.MvPolynomial.Monad`, the project mirror, for `eval_bind₁`; the spike's polynomial and feasibility ranges, with `finrank_dotPerp_span_singleton_of_ne_zero` and `isZariskiOpen_linearIndependent_univ` pulled from its steer section, which build 3 therefore no longer carries; the node pins `gradedPencilNondegFeasible_iff`, `exists_rowsMap_two`, `exists_rowsMap_three`, `exists_injOn_finrank_iInf_map_le`). **Build 3 landed** (`Grade/Lift.lean`, the four nodes green, 0 warnings, `lake lint` clean, `verify.sh` green; the spike's lines 278–599 and 740–932 less the two helpers, with `HoldsGenerally` from line 2044; the lift's subspaces are `liftSubspace`, since `liftPlane` is `MainComponent/Lines.lean`'s; the steer node also pins `PencilSeed.toGamma` and `mem_steerSet_iff`). **Next: build 4** (*Hand-off*). The recon's
spike, gitignored
`scratch/42l/Spike.lean` (2610 lines), is `lake lean` clean with no error and no `sorry`; its 22
checked declarations depend on the three standard axioms; it passes the `unusedArguments` and
`docBlame` lints; its 33 warnings are style (deprecated names, long lines, a `show`). The builds
transcribe it by section, leaf-first; namespace `CombinatorialRigidity.Molecular`, `r` the number
of new coordinates (the chapter's `m = d − 3`, so grade `k = r + 2`, Lean's `m = r + 1`):
1. **`Grade/Nondegenerate.lean`** (imports `Grade.Embedding`; 3 nodes, ~270 lines).
   `def:pencil-d-nondegenerate`: `PencilNondegConditions G b Π` (the three conditions on `Fin N`,
   the third `finrank (⨅ w ∈ S, Π w) + S.card ≤ 4` over `Finset`s `S`),
   `IsNondegPencilPlaneRealization G F b Π` (`HasPencilPlaneRealization` and the conditions),
   `GradedPencilNondegFeasible K k G`, `HasGradedGenericPencilRealization K k n G`.
   `-three`: `finrank_iInf_dotPerp_add_card_le_iff`, `pencilNondegConditions_dotPerp_iff`,
   `isNondegPencilPlaneRealization_two_iff` (with `finrank_span_rigidityRows_mapExtensor`, the
   rank), `gradedPencilNondegFeasible_two_iff`, `hasGradedGenericPencilRealization_two_iff`.
   `-maps`: `PencilNondegConditions.of_map` (1), `.map` (2),
   `IsNondegPencilPlaneRealization.map_gradeEmbed` ("in particular").
2. **`Grade/Feasible.lean`** (imports `Grade.Nondegenerate`, `Pencil.Steer`; 1 node, ~720
   lines): the API `IsPolyFun`, `IsZariskiOpen` (pointwise, `Graph.X0AttainsGrade`'s form) and
   their closure lemmas; `exists_hasPencilPlaneRealization` (point-configuration (1), any `α`);
   `exists_rowsMap_two`/`_three` (one `π` per set), `exists_proj_of_pencilNondegConditions`;
   `gradedPencilNondegFeasible_iff (hk : 2 ≤ k)` (`[Infinite K] [Finite α]`).
3. **`Grade/Lift.lean`** (imports `Grade.Feasible`; 4 nodes, ~600 lines). `lem:pencil-d-steer`:
   `PencilSeed.ofGamma`, `steerPoint`, `steerNormal`, `steerSet` (`U(G)`),
   `isPolyFun_steerPoint`/`Normal`, `steerPoint_dotProduct_steerNormal`, `isZariskiOpen_steerSet`,
   `exists_mem_steerSet_of_isNondeg`, `steerSet_nonempty_iff`, with `HoldsGenerally` (the remark's
   "general"). `def:pencil-d-lift`: `liftVec`, `liftSpace`, `IsTrivialLift`, `liftMaps`,
   `liftNormal`, `liftPlane`. `-lift-realization`: `IsNondegPencilPlaneRealization.lift` (1),
   `mem_liftMaps_iff` (2), `liftSmul_mem_liftSpace_iff`, `liftTransport_mem_liftSpace_iff`,
   `finrank_span_rigidityRows_ofNormals_smul`, `finrank_liftNormal_transport` (3).
   `def:pencil-d-lift-attains`: `LiftAttains K r G`.
4. **`Grade/LiftWitness.lean`** (imports `Grade.Lift`; 2 nodes, ~880 lines): `liftSpaceTilde`
   (`L̃`), `liftMatrixPoly`, the homogenization, `liftAttains_of_least` (one-witness (1)),
   `liftAttains_of_holdsGenerally` (2); `lift_transfer`.

Every dependency outside the ten is green; outside them only `sec:pencil-d-generic` uses any.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the ten nodes of `-nondegenerate` and `-lift` as
  the chapter states them. PD-HEAD stays the layer's code; its halves are named by their sections,
  `-nondegenerate` with `-lift` (42l) and `-generic` (eleven nodes, no letter), as PD-STEPS's were
  across 42f–42i. 42l's close is an intermediate sub-phase close; the `main_results` row is decided
  at Phase 42's close, with `-generic` (design doc §3).
- **Encoding** as 42b–42k: grade `k = d − 1`, Lean's `m = d − 2`, so `d ≥ 3` is `1 ≤ m`, the
  deficiency at `n = m + 2`. The chapter's lift has `d − 3` new coordinates, `m − 1` at the Lean's
  `m`, inserted before the last coordinate as `gradeEmbed` inserts its zeros.
- **What 42k hands on** (`notes/Phase42k.md` *Hand-off*): `Graph.graded_pencil_realization_theorem`,
  the headline's first two conjuncts, which no node of the ten uses.
- **The standing rule** (design doc §3): the recon and every build add a row to `notes/Cleanup42.md`
  §2 where their Lean departs from the chapter's proof, in the same commit.

## Lemma checklist

- [x] **Pre-build recon**: all ten spiked complete, four builds pinned (*Current state*).
- [x] Build 1: `def:pencil-d-nondegenerate`, `lem:pencil-d-nondegenerate-three`, `-maps`.
- [x] Build 2: `lem:pencil-d-nondegenerate-feasible`.
- [x] Build 3: `lem:pencil-d-steer`, `def:pencil-d-lift`, `lem:pencil-d-lift-realization`,
  `def:pencil-d-lift-attains`.
- [ ] Build 4: `lem:pencil-d-lift-one-witness`, `lem:pencil-d-lift-transfer`.
- [ ] **Close** 42l, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`); `-generic` opens after
  it at the PI's word.

## Blockers / open questions

- None blocking. The open's questions, settled by the recon (*Decisions made*): the `d = 3` Lean
  reused, the chart, the definition's form, the lift's spaces, the remarks, the consumers.
- **For `-generic`** (no node of the ten): the remark after `def:pencil-d-lift-attains` that an
  attaining general lift gives a generic realization is `IsNondegPencilPlaneRealization.lift` with
  `PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge` at a realization with `Q ≠ 0`; it lands
  with `thm:pencil-d-generic`, which cites it.
- **Files.** A deferral naming a file a build edits rides with it (design doc §3); none of the four
  new files is named by one.

## Hand-off / next phase

The next concrete commit is **build 4**: `Grade/LiftWitness.lean` (imports `Grade.Lift`; the spike's
sections `Homogeneous in each body`, `One lift suffices` and `Lifts restrict to a subgraph`, lines
1553–2499, less `HoldsGenerally` (line 2044, in `Grade/Lift.lean`), with `isZariskiOpen_eval_ne_zero`
(line 2054) staying here), with `\lean{}` and `\leanok` on `lem:pencil-d-lift-one-witness` and
`lem:pencil-d-lift-transfer` and the rows R-21 and R-23 of `notes/Cleanup42.md`. The spike's
`liftPlane` is `liftSubspace` in the landed file. The spike's corrected ranges are above; if the 947
lines are more than one sitting, split at `Lifts restrict to a subgraph` and say so. Builds 1 to 3 are done.
- **The standing rule** (*Architectural choices*): each build whose Lean departs from the chapter's
  proof sets or keeps its `notes/Cleanup42.md` row (R-20 with build 2, R-22 with build 3, R-21 and
  R-23 with build 4).
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42k are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42k.md` *Hand-off* lists 42k's four).
- **After 42l:** `-generic` (11 red nodes, ending in `thm:pencil-d-generic` and the headline
  `cor:pencil-d-conditioned-pair`) opens at the PI's word as a later sub-phase; its close is Phase
  42's, where Tier 0's `main_results` row is decided (design doc §3).

## Decisions made during this phase

- **The recon (design pass):** all ten spiked complete on the landed carrier (*Current state*).
  The `d = 3` Lean reused: the polarity and `IsNondegPencilRealization` (three), the chart
  `pencilChartPoint`/`pencilChartNormal` and `exists_pencilSeed_of_nondeg_of_selectors` (steer),
  `cross₃Poly`, the polynomial section `Matrix.exists_mvPolynomial_section_mulVec_eq_zero` and the
  rank polynomial `exists_rankPolynomial_of_le_finrank_linking` (one-witness, transfer). Not reused:
  `Steer.lean`, `Witness.lean`, `MainComponent/GenericSteer.lean`, `PencilSeed.ofCoord`.
- **The chart** (steer): the `d = 3` chart at `PencilSeed.ofGamma s`, `s : α × Fin 7 × Fin 4 → K`
  (`m_v`, three hub pads, three neighbour pads at the selectors' slots), so `ofGamma ∘ toGamma = id`
  and every realization is a point; "the fixed order" is the selectors, parameters of the lemma.
  `Γ(G)` has six auxiliary vectors where the chapter has five (R-22). "General" is
  `HoldsGenerally` (a polynomial on `Γ(G)` nonzero somewhere on `U(G)`).
- **The lift's spaces:** `𝓛(b⁰, Π⁰)` is `liftSpace`, forms on `Π⁰_v` (`Module.Dual`), its condition
  asked when `b⁰_w ∈ Π⁰_v`; `L(b⁰)` is `liftMaps`; `L̃(b⁰)` is `liftSpaceTilde`, forms on `K⁴` by
  coordinates, `= ker A(b⁰)` (`liftSpaceTilde_eq_ker`). The lift's normal is
  `gradeMk b₁ b₂ (b₃ :: ζ) b₄`, so a lift of a configuration is one. `LiftAttains` asks
  `Q.vars` in `V(G)` and `Q` weighted homogeneous for `p ↦ single p.1 1` (one degree per body).
- **No pin is weaker than its node:** three takes no `n_v ≠ 0` (the realization gives it), maps no
  `b_v ≠ 0` or `Π_v ∋ b_v`, one-witness and transfer neither simplicity nor feasibility (unused);
  feasibility takes `[Finite α]`, the chapter's finite multigraph. Transfer's open set is open in
  the maps' coordinates, polynomials on `𝓛(r⁰)^m` through `λ ↦ ζ`.
- **The routes** (`notes/Cleanup42.md`): feasibility's set-by-set map by three forms chosen off two
  proper subspaces each, no induction or quadric (R-20); one-witness through the polynomial section,
  not a Cramer basis with coefficients `γ` (R-21); the chart's sixth vector (R-22); transfer's open
  set by the rank polynomial at each `λ`, not as a preimage (R-23).
- **PI, 2026-11-04 (42l's open):** the PI answered "Nondegenerate + lift only", whose option read:
  "Open on the 10 nodes of -nondegenerate and -lift (roughly 3–5 builds, my estimate). The 11
  generic nodes and the headline would wait for a later sub-phase." The question as put, the other
  options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1): the build estimates are the
  coordinator's; the counts and the sections' descriptions hold, with qualifiers (`-generic`'s "the
  reduction's cases" only loosely); the line counts are the three whole files, which serve
  `-generic` (`Pair.lean`, `Pair2.lean`) or are one of six files of the `d = 3` parametrization
  (`Steer.lean`); no node of the ten uses a node of `-generic`, so the split is consistent.
- **Consistency read at the open:** all ten PASS, each read in full against the nodes it cites; no
  wording needs a repair. With every `\uses` parsed whole, the 18 outside dependencies (8
  definitions, 10 lemmas; 18 with the `\cref`s) are green, proofs too, none superseded. From
  `sec:pencil-d-induction` on, 62 nodes, 21 red, all in PD-HEAD (recounted).
- **The read's checks, re-derived:** three, `dim ⋂ n_w^⊥ = 4 − dim span(n_w)`; feasible,
  `πΠ_w = Ke₄ ⊕ π̄A_w` (meets in dimension 2 or 1), and the bad `c` in finitely many proper
  subspaces and the quadric `det[u, u′] = 0`; steer, `b⁰_w · n_v = 0` by hub or not; lift (3),
  hinges scaled by `c_u c_v`; one-witness, `N = c − |J|` Cramer vectors; transfer, a body of degree
  at most one in `H` is no hub, so its subspace enters no condition.
