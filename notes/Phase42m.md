# Phase 42m — PD-HEAD: the generic conjunct and the headline in every dimension (work log)

**Status:** in progress, opened 2026-11-05 at the PI's word ("All 11 as written", design doc §1),
the second and last sub-phase of Phase 42's last layer, PD-HEAD. Forward mode, the Lean under
`/coordinate-phase`: the eleven red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-generic`, as the chapter states them. They were the blueprint's last red nodes, so
42m's close is Phase 42's. The pre-build recon and **builds 1 to 7 landed** (2026-11-05): all
eleven nodes green, the blueprint has none red. **The close runs in parts** (*Hand-off*): parts 1
(the gates and the axioms on the final tree) and 2 (the re-read, the ledger, the compressions, the
organization review) landed; next, part 3, once the PI answers the question on Phase 42's
`main_results` rows (*Blockers*), then part 4, the last.

## Current state

**Next: the close's part 3, once the PI answers (*Blockers*), then part 4** (*Hand-off*); parts 1
and 2 landed (*Decisions made*). In the tree,
`Grade/Generic.lean` (build 7: `LiftAttains.hasGradedGenericPencilRealization`, the remark, pinned
at `def:pencil-d-lift-attains`; `liftAttains_of_simple`, the strong induction;
`hasGradedGenericPencilRealization_of_simple`, which is `thm:pencil-d-generic`;
`Graph.graded_pencil_conditioned_pair`, `cor:pencil-d-conditioned-pair`, the three conjuncts, the
first two `Graph.graded_pencil_realization_theorem`'s; the pins on the three standard axioms), and,
each file on the three standard axioms with the whole-project build, `lake lint`,
`blueprint/lint.sh` and `blueprint/verify.sh` clean at its commit:
`Grade/EarFree.lean` (build 6b: `holdsGenerally_earFree`, from its four steps
`earFree_of_finrank_liftSpaceTilde_le` (the algebra at one realization, on
`isTrivialLift_of_finrank_liftSpaceTilde_le`, `liftTildeOfTrivial`, `earLift_of_isTrivialLift`),
`exists_earFree_config` (on `span_pencilConfigPoint_eq_top`, with the trace
`Graph.IsPencilGoodEar.rest`), `exists_earFree_gammaL` (on `linearIndepOn_planeNormal_of_subset`,
`exists_steerPoint_eq_smul`) and the transfer's `isZariskiOpen_earFreeCond`,
`isZariskiOpen_finrank_liftSpaceTilde_le`, `earFreeCond_of_smul`,
`finrank_span_image_of_linearIndepOn`; build 6a: `exists_earExtend_poly`, with `exists_earExtend_cond_poly` (the
polynomial `E_L`) and `exists_linearIndepOn_of_finrank` (the greedy choice of the `n_u`); helpers
`hubSlotPos`, `exists_gamma_eq_of_injective`, `isPolyFun_dotProduct`, `exists_mem_notMem_of_finrank`
and the any-selector forms `dotProduct_pencilChartPoint_hubNormal_of_selector`,
`linearIndepOn_hubNormal_of_selector`), `Grade/LiftNoRigid.lean` (build 5: `liftAttains_of_forall_deficiency_two_ne_zero`; the shared steps
`exists_planeDiff_ne_zero_poly`, `mem_liftMaps_pencilConfigPoint_iff` and
`finrank_liftSpaceTilde_pencilConfigPoint` (`_ker`), with `liftFreeCoords`, `planeForm`,
`liftTildeToLk`, `liftTildeToFree`, `liftTildeOfLk` and their `_mem`/`eq_zero_of_` lemmas;
`exists_pencilConfigPoint_of_dotProduct`, `sum_smul_pencilConfigPoint_eq_zero`,
`liftNormal_pencilConfigPoint`; and in `Grade/LiftWitness.lean`
`exists_holdsGenerally_finrank_liftSpaceTilde_le`, `HoldsGenerally.of_isZariskiOpen`,
`isZariskiOpen_ne_zero_of_isPolyFun`, `liftAttains_of_holdsGenerally` now on the first),
`Grade/GoodEar.lean` (build 4: `Graph.IsPencilGoodEar`,
`Graph.IsX0Graph.exists_goodEar_or_pendantTriangle`; the core
`Graph.IsX0Graph.exists_minimalRigid_ear_or_pendantTriangle` in `MainComponent/GoodEar.lean`),
`Grade/LiftCutEdge.lean` (build 3: `liftAttains_of_cutEdge`, the glue `exists_cutEdge_glue`,
`HoldsGenerally.and`), `Grade/LiftCases.lean` (build 2: `liftAttains_of_pendant`,
`liftAttains_of_ear`, `liftAttains_of_pendantTriangle`, `EarLiftCondition`,
`HoldsGenerally.of_forall`, `.mono`, `IsNondegPencilRealization.toPlane`) and
`Grade/LiftSmall.lean` (build 1: `liftAttains_of_ncard_le_two`, `liftAttains_of_triangle`,
`liftAttains_of_cutEdges_eq_empty`). The recon's spike is the gitignored `scratch/42m/Spike.lean`
(`lake lean` clean; its `sorry`s are the lemma statements, now all built); what it holds for build 7
is under *Hand-off*. `scratch/42m/B6bChain.lean` chains the landed `holdsGenerally_earFree` into
`liftAttains_of_ear` under `lake lean` (*Blockers*).

**The eleven signatures** (namespace `CombinatorialRigidity.Molecular`; every one carries
`{K : Type*} [Field K] {α β : Type*}`, `[Finite α] [Finite β]`, `[Infinite K]` unless noted, and
`(r : ℕ)` for `d = r + 3` where a lift is meant; full text in the spike):
- `lem:pencil-d-lift-small`: `liftAttains_of_ncard_le_two [Nonempty α] (r) (hS : G.Simple)
  (hfeas : PencilNondegFeasible K G) (h2 : V(G).ncard ≤ 2) : LiftAttains K r G` and
  `liftAttains_of_triangle (r) hS hfeas (h3 : V(G).ncard = 3) (hadj : ∀ u ∈ V(G), ∀ v ∈ V(G),
  u ≠ v → G.Adj u v) : LiftAttains K r G` (neither needs `[Infinite K]`);
  `liftAttains_of_cutEdges_eq_empty (r) hfeas (hne : V₁.Nonempty) (hssub : V₁ ⊂ V(G))
  (hC0 : G.cutEdges V₁ = ∅) : PencilNondegFeasible K (G.induce V₁) ∧ PencilNondegFeasible K
  (G.induce (V(G) \ V₁)) ∧ (LiftAttains K r (G.induce V₁) → LiftAttains K r (G.induce (V(G) \ V₁))
  → LiftAttains K r G)`.
- `lem:pencil-d-lift-cut-edge`: `liftAttains_of_cutEdge (r) hS hfeas (he : G.IsLink e u v)
  (hu : u ∈ V₁) (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1)`, concluding
  the feasibility of `G.induce (V₁ ∪ {v})` and `G.induce ((V(G) \ V₁) ∪ {u})` and that their
  `LiftAttains` give `G`'s (the spike's `h₁ h₂ : 2 ≤ …ncard` dropped by build 3, unused).
- `lem:pencil-d-lift-pendant`: `liftAttains_of_pendant (r) hS hfeas (hv : G.degree v = 1)
  (hvu : G.Adj v u) : PencilNondegFeasible K (G.induce (V(G) \ {v})) ∧ (LiftAttains K r
  (G.induce (V(G) \ {v})) → LiftAttains K r G)`.
- `lem:pencil-d-lift-pendant-triangle`: `liftAttains_of_pendantTriangle (r) hS hfeas
  (h₁ : G.degree x₁ = 2) (h₂ : G.degree x₂ = 2) (h₁₂ : G.Adj x₁ x₂) (h₁c : G.Adj x₁ c)
  (h₂c : G.Adj x₂ c) (hc : 4 ≤ G.degree c)`, the same shape at `G.induce (V(G) \ {x₁, x₂})`.
- `lem:pencil-d-lift-no-rigid`: `liftAttains_of_forall_deficiency_two_ne_zero (r)
  (hG : G.IsX0Graph) hfeas (hrig : ∀ Y ⊆ V(G), 2 ≤ Y.ncard → (G.induce Y).deficiency 2 ≠ 0)
  (hatt : G.X0AttainsGrade K (r + 1)) : LiftAttains K r G`.
- `lem:pencil-d-good-ear` (no `[Infinite K]`, no `K`): `Graph.IsX0Graph.exists_goodEar_or_pendantTriangle
  hG htec (h4 : 4 ≤ V(G).ncard) hF1 hF2 hrig`, with `exists_oneEar_or_pendantTriangle`'s
  hypotheses, concluding `(∃ x₁ x₂ c, G.degree x₁ = 2 ∧ G.degree x₂ = 2 ∧ G.Adj x₁ x₂ ∧
  G.Adj x₁ c ∧ G.Adj x₂ c ∧ 4 ≤ G.degree c) ∨ ∃ W₀ x a b, G.IsPencilGoodEar W₀ x a b`; the new
  structure `Graph.IsPencilGoodEar` has one field per clause of (i) to (v).
- `lem:pencil-d-lift-ear`: `liftAttains_of_ear (r) hS hfeas (hx : G.degree x = 2)
  (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : a ≠ b) (ha : G.PencilHub a) (hb : G.PencilHub b)
  (hdef : (G.induce (V(G) \ {x})).deficiency (r + 1 + 2) ≤ G.deficiency (r + 1 + 2)) :
  PencilNondegFeasible K (G.induce (V(G) \ {x})) ∧ ∀ {hubSel nbrSel}, (selectors of `G`) →
  EarLiftCondition (K := K) G hubSel nbrSel x a b → LiftAttains K r (G.induce (V(G) \ {x})) →
  LiftAttains K r G`, where the new `EarLiftCondition G hubSel nbrSel x a b :=
  HoldsGenerally G hubSel nbrSel fun b0 P0 => ∀ lam ∈ liftSpace (G.induce (V(G) \ {x})) b0 P0,
  ∀ (ha : b0 x ∈ P0 a) (hb : b0 x ∈ P0 b), lam.2 a ⟨b0 x, ha⟩ = lam.2 b ⟨b0 x, hb⟩`.
- `lem:pencil-d-ear-extend` (landed without `hS`, `nbrSel`, `hNbrSel`, R-33): `exists_earExtend_poly
  hfeas (hW : G.IsPencilGoodEar W₀ x a b) hHubSel (hL : ∀ v ∈ W₀ \ {x}, IsFin3SelectorOf {h | h ∈ (G.induce (W₀ \ {x})).closedNbhd v
  ∧ G.PencilHub h} (hubSelL v)) : ∃ E : MvPolynomial (α × Fin 7 × Fin 4) K, (∃ t, eval t E ≠ 0) ∧
  ∀ t, eval t E ≠ 0 → ∃ s, ∀ v ∈ W₀ \ {x}, ∃ c ≠ 0, steerPoint hubSel s v = c • steerPoint hubSelL t v`.
- `lem:pencil-d-ear-free` (landed as pinned): `holdsGenerally_earFree hS hfeas hW` (selectors of `G`) `:
  HoldsGenerally G hubSel nbrSel (fun b0 P0 => (∀ v ∈ W₀ \ {x}, finrank (span (b0 '' (G.induce
  (W₀ \ {x})).closedNbhd v)) = 3) ∧ span (b0 '' (W₀ \ {x})) = ⊤ ∧ ∀ lam ∈ liftSpace (G.induce
  (W₀ \ {x})) b0 P0, IsTrivialLift (G.induce (W₀ \ {x})) b0 P0 lam) ∧ EarLiftCondition G hubSel
  nbrSel x a b`.
- `thm:pencil-d-generic`: `liftAttains_of_simple (r) hS (hne : V(G).Nonempty) hfeas :
  LiftAttains K r G` (the induction) and `hasGradedGenericPencilRealization_of_simple (hm : 1 ≤ m)
  hS hne (hfeas : GradedPencilNondegFeasible K (m + 1) G) : HasGradedGenericPencilRealization K
  (m + 1) (m + 2) G`, with the remark `LiftAttains.hasGradedGenericPencilRealization`.
- `cor:pencil-d-conditioned-pair`: `Graph.graded_pencil_conditioned_pair (hm : 1 ≤ m) (hne) :
  HasGradedPencilRealization K (m + 1) (m + 2) G ∧ (G.Simple → HasGradedDistinctPencilRealization
  …) ∧ (G.Simple → GradedPencilNondegFeasible K (m + 1) G → HasGradedGenericPencilRealization …)`.

**Statement faithfulness** (no pin weaker than its node): `-lift-pendant` drops "whose neighbour
`u` has another neighbour" and `-lift-ear` drops "not adjacent" (both unused, R-25 and the ear's
rank by `lem:block-rank-ear`, which needs no non-adjacency); `-lift-small`'s two-body pin adds the
ambient `[Nonempty α]`, as at no body over an empty `α` with labels the carrier's `LiftAttains` asks
for a selector `β → α × α` that does not exist (the chapter's proof treats one and two bodies; the
theorem always has a body); `-lift-small` (2) is pinned without `G.Simple` and without `[Infinite K]`
(build 1's proof needs neither; `notes/Cleanup42.md` R-28); `-lift-cut-edge` drops `|V₁|, |V₂| ≥ 2`
(unused, R-30); `-lift-no-rigid` is pinned as its node states it (R-32); `-ear-extend` drops `G`
simple and the neighbour selector (unused, R-33); `-ear-free` is pinned as its node states it
(R-34); encodings: "a triangle" as three
pairwise adjacent bodies, "at a general nondegenerate realization" as `HoldsGenerally` at the given
selectors, `Γ_L` inside `Γ(G)`'s parameter type, "a nonzero polynomial" as one with a non-root.

## Lemma checklist

Build numbers are *Hand-off*'s. "Spiked" means sorry-free in `scratch/42m/Spike.lean`.
- [x] **Pre-build recon** (this commit; *Decisions made*).
- [x] `lem:pencil-d-lift-small`: both parts, sorry-free (build 1; R-28).
- [x] `lem:pencil-d-lift-cut-edge`: sorry-free, the glue new (build 3; R-30).
- [x] `lem:pencil-d-lift-pendant`: sorry-free (build 2; R-24 to R-26).
- [x] `lem:pencil-d-lift-pendant-triangle`: sorry-free, on the pendant's template (build 2; R-29).
- [x] `lem:pencil-d-lift-no-rigid`: sorry-free, with the two shared steps (build 5; R-32).
- [x] `lem:pencil-d-good-ear`, both outcomes, parts (i) to (v), sorry-free (build 4; R-31).
- [x] `lem:pencil-d-lift-ear`: sorry-free, with `EarLiftCondition` (build 2; R-24, R-26).
- [x] `lem:pencil-d-ear-extend`: sorry-free, `E_L` and the greedy choice (build 6a; R-33).
- [x] `lem:pencil-d-ear-free`: sorry-free in one session, its four steps and the transfer (build 6b;
  R-34).
- [x] `thm:pencil-d-generic`, with the remark after `def:pencil-d-lift-attains`: sorry-free (build 7;
  no departure from the chapter's proof, no new row).
- [x] `cor:pencil-d-conditioned-pair`: sorry-free (build 7).
- **Close** 42m and Phase 42 together, the full close (`PHASE-BOUNDARIES.md`), in parts
  (*Hand-off* carries each part's checklist):
  - [x] Part 1: the gates and the 20 main results' axioms on the final tree, Phase 42's seven
    candidate declarations' axioms, `Grade/Generic.lean`'s docstring fix (*Decisions made*).
  - [x] Part 2: the chapter's end-to-end re-read and `notes/BlueprintExposition.md`; the design
    doc's compression; the phase note's *Decisions made* tail; the project-organization review
    (*Decisions made*).
  - [ ] Part 3 (needs the PI's answer, *Blockers*): `formalization.yaml`'s `main_results` and
    `alignment` (Tier 0 unless the headline subsumes it, design doc §3: subsumed, so no Tier 0
    row), each new row's closed non-vacuity witness in `CombinatorialRigidity/Nonvacuity.lean`,
    and the headline-axioms check with the new rows.
  - [ ] Part 4, the last: the ROADMAP row to ✓ and §42 compressed; the user-facing surfaces
    re-summarized; `.claude/autopilot/queue.toml`'s PENCIL-D row `done = true`. (The
    dispatch-log grooming is the coordinator's, after the close.)

## Blockers / open questions

- **For the PI (blocks part 3 only): Phase 42's `main_results` rows.** Settled: no Tier 0 row
  (design doc §3: the coverage subsumes it, and at the same `1 ≤ m` the headline's second conjunct
  gives its distinct form, `IsX0Graph` being simple with a body); the headline
  `Graph.graded_pencil_conditioned_pair` (`Grade/Generic.lean`) joins (`PHASE-BOUNDARIES.md`: the
  phase's headline theorem). Not settled by the design doc or the PI's answers: whether it is the
  only row, and how much its witness exercises. All seven candidates are on the three standard
  axioms (part 1).
  - **(A), recommended: one row, the headline.** Its description and a new `alignment` entry name
    the route, the coverage `Graph.IsX0Graph.x0AttainsGrade`, the reduction
    `Graph.graded_pencil_realization_theorem` and `hasGradedGenericPencilRealization_of_simple`, as
    Phase 40's rows name `x0Dist` and `x0Gen`, which got no row. Witness as the `d = 3` rows':
    the star `K₁,₃` in dimension four (`m = 2`), its distinct conjunct.
  - **(B): two rows, the headline and the coverage.** The coverage is design doc §0's target (at
    every simple connected graph of minimum degree two, a general picture with general heights
    attains, which the headline's existence claims do not say) and what subsumes Tier 0's first
    claim (`Graph.x0AttainsGrade_of_deficiency_two_le_three`). Its witness at the triangle `K₃`.
  - **(C), with (A) or (B): the headline's witness also exercises the generic conjunct**, its one
    hypothesis no input might meet (F-207, F-252): feasibility at a small simple graph, likely
    `K₂` by `PencilNondegFeasible.mono` from `exists_isNondegPencilRealization_parallel_pair`
    through `gradedPencilNondegFeasible_iff` (not spiked). The `d = 3` rows' witnesses do not.
  - Recommendation: (A) with (C). The builds' `K_{2,3}` instance of `Graph.IsPencilGoodEar` and
    `EarLiftCondition` (below) would witness an inner arm, not a hypothesis of the headline, so no
    option needs it; CLEANUP-42's unless the PI wants it in part 3.
- Nothing else blocks the close. What the builds still carry:
  - **`-ear-free`'s leaves, traced against their consumer (build 6b):** each step's hypotheses are
    what the assembly has: (1) `earFree_of_finrank_liftSpaceTilde_le` takes `G.Simple`, the good ear,
    points in subspaces of dimension at most three on every closed neighbourhood of `G` (at any
    `s ∈ U(G)` and any selectors of `G`: `steerPoint_dotProduct_steerNormal`,
    `finrank_dotPerp_span_singleton_of_ne_zero`) and (a), (b), (c), which the transfer supplies;
    (2) `exists_earFree_config`'s hypotheses on `Y = G[X]` are `Graph.IsPencilGoodEar.rest hS hW`
    (machine-checked: the instance `G[X].Simple`, part (iii)'s degrees through
    `Graph.three_le_ncard_closedNbhd`, `deficiency_ne` through `Graph.induce_induce_of_subset`,
    `deficiency_eq`, `three_le`); (3) `exists_earFree_gammaL` takes `hfeas`, the good ear, selectors
    of `H_L[v]` (chosen in the proof by `exists_isFin3SelectorOf_of_ncard_le_three`, as `H_L[v] ⊆`
    the closed hub-neighbourhood) and (2)'s output; (4) the transfer's `E_L` is build 6a's at the same
    selectors. The headline statement chains into `liftAttains_of_ear` with
    `hdef := (hW.deficiency_delete _ _).le` (`scratch/42m/B6bChain.lean`, `lake lean` clean).
  - **What build 5's shared steps ask of `Y = G[X]`** is now `Graph.IsPencilGoodEar.rest` (above).
  - **Instances of the two new predicates**: none closed yet. `Graph.IsPencilGoodEar` is produced
    by build 4 and `EarLiftCondition` by build 6b (`holdsGenerally_earFree`); the candidate witness
    is `K_{2,3}` (`W₀` all five bodies, `x` a body of degree two; `s(W₀) = 3·4 − 2·6 = 0`, `X` a
    four-cycle with `s = 1`); not a row's witness (the PI question above).
  - **Build 7's honesty gate** (read, not assumed): `liftAttains_of_simple`'s hypotheses are the
    node's (`G.Simple`, a body, feasibility, `[Infinite K]`, finiteness); `EarLiftCondition` comes
    from `holdsGenerally_earFree` at the selectors `exists_steer_selectors` gives and
    `liftAttains_of_ear` receives; `X0AttainsGrade` is `Graph.IsX0Graph.x0AttainsGrade` (42j's
    coverage); the cut-edge call drops `h₁ h₂` (R-30) and they stay as local facts for `omega`.
    The spike's `bnPoint_zero` is not needed.

## Hand-off / next phase

Builds 1 to 7 landed (`Grade/LiftSmall.lean`; `Grade/LiftCases.lean`, three nodes;
`Grade/LiftCutEdge.lean`, R-30; `Grade/GoodEar.lean`, R-31; `Grade/LiftNoRigid.lean`, R-32;
`Grade/EarFree.lean`, R-33 and R-34; `Grade/Generic.lean`, the theorem and the headline, no new row).
No blueprint node is red. The close of 42m and Phase 42 together (`PHASE-BOUNDARIES.md` *When this
commit closes a phase*, the full close) runs in parts, one commit each, on Phase 41's precedent;
parts 1 and 2 landed (*Decisions made*). **The next concrete commit is part 3, once the PI answers
the question under *Blockers***; part 4 flips the row, so it comes last and waits for part 3.
- **Part 3 (Lean; after the PI's answer, *Blockers*):** the rows and `alignment` entries the PI
  picks, `review.notes`' count of main results ("all twenty"), each new row's witness in
  `CombinatorialRigidity/Nonvacuity.lean` (named `<declaration>_witness`; the module docstring's
  list and its paragraph on dimensions gain it; the import `Grade.Generic`, and `Grade.Coverage`
  under (B)); the headline-axioms harness `scratch/42m-close/Axioms.lean` (gitignored; the 20 rows,
  byte-identical to 41e's close net of the path) re-run with the new rows; every gate.
- **Part 4, the last (docs only; flips the row):** the ROADMAP row to ✓, re-thinned, and §42
  compressed to one paragraph plus pointers (sub-phases by stable code); README *Project status*,
  `home_page/index.md` (status and phase table), `intro.tex`'s *Organization* enumerate and
  *Reading this blueprint* paragraph, `formalization.yaml`'s `status.scope` and
  `fidelity.divergences` (each says Phase 42 is in progress), `notes/MolecularConjecture.md`'s
  Phase 42 entry, all re-summarized, not appended to; what they carry on the pins: every pin equals
  or is stronger than its node except build 1's two-body pin, whose ambient `[Nonempty α]` is a
  carrier artifact at zero bodies (reported to the PI as an encoding, no objection), and the route
  departures are `notes/Cleanup42.md` R-24 to R-34; `.claude/autopilot/queue.toml`'s PENCIL-D row
  `done = true`; this note and the design doc's header in closed form. Open no successor.
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands:** design doc §3, the *Deferred to …* paragraphs of each layer, 42m's
  build 6 helpers and mirror candidates now among them (*Deferred to CLEANUP-42 and after from
  42m*); FRICTION's `[open]` entries for 42b–42l carry the same home debts.
- **After 42m:** Phase 42 is closed; CLEANUP-42 (`notes/Cleanup42.md`) and then ORIGAMI follow,
  each opening with the PI (ROADMAP *Queued post-program phases*).

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
