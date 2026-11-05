# Phase 42m — PD-HEAD: the generic conjunct and the headline in every dimension (work log)

**Status:** in progress, opened 2026-11-05 at the PI's word ("All 11 as written", design doc §1),
the second and last sub-phase of Phase 42's last layer, PD-HEAD. Forward mode, the Lean under
`/coordinate-phase`: the eleven red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-generic`, as the chapter states them (six cases of an induction on the bodies, the
lemmas that find the good ear and supply its condition, the generic theorem and the headline).
They are the blueprint's last red nodes, so 42m's close is Phase 42's. The pre-build recon landed
(2026-11-05, *Decisions made*); seven builds planned, build 6 split. **Builds 1 to 6a landed**
(2026-11-05): `Grade/LiftSmall.lean`, `Grade/LiftCases.lean` (three nodes), `Grade/LiftCutEdge.lean`,
`Grade/GoodEar.lean`, `Grade/LiftNoRigid.lean` and `Grade/EarFree.lean` (`lem:pencil-d-ear-extend`),
eight of the eleven red nodes green; three remain. Next (*Hand-off*): build 6b,
`lem:pencil-d-ear-free` in `Grade/EarFree.lean`.

## Current state

**Next: build 6b** (*Hand-off*). In the tree, each file on the three standard axioms with the
whole-project build, `lake lint`, `blueprint/lint.sh` and `blueprint/verify.sh` clean at its commit:
`Grade/EarFree.lean` (build 6a: `exists_earExtend_poly`, with `exists_earExtend_cond_poly` (the
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
(`lake lean` clean; its `sorry`s are the unspiked lemma statements, one still to build); what
it holds for later builds is under *Hand-off*. Build 6a's spike `scratch/42m/Build6.lean` chains
`holdsGenerally_earFree` (stated, `sorry`) into `liftAttains_of_ear` (*Blockers*).

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
- `lem:pencil-d-ear-free`: `holdsGenerally_earFree hS hfeas hW` (selectors of `G`) `:
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
simple and the neighbour selector (unused, R-33); encodings: "a triangle" as three
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
- [ ] `lem:pencil-d-ear-free`: new (build 6b, maybe 6c; *Hand-off*).
- [ ] `thm:pencil-d-generic`, with the remark after `def:pencil-d-lift-attains`: spiked on the
  lemma statements (build 7).
- [ ] `cor:pencil-d-conditioned-pair`: spiked (build 7).
- [ ] **Close** 42m and Phase 42 together, the full close (`PHASE-BOUNDARIES.md`): the ROADMAP row
  to ✓ and §42 compressed; the user-facing surfaces re-summarized; `formalization.yaml`'s
  `main_results` and `alignment` (Tier 0 unless the headline subsumes it, design doc §3), each new
  row with a closed non-vacuity witness in `CombinatorialRigidity/Nonvacuity.lean`, and the
  headline-axioms check; the chapter's end-to-end re-read and `notes/BlueprintExposition.md`; the
  dispatch-log grooming; the design doc's compression; the project-organization review; and
  `.claude/autopilot/queue.toml`'s PENCIL-D row `done = true`.

## Blockers / open questions

- None blocking build 6b. What the builds still carry:
  - **`-ear-free`, re-derived against the bodies (build 6a):** satisfiable, and no weaker than its
    node. The first conjunct's `≤ 3` holds on all of `U(G)` (the points of a closed neighbourhood in
    `Y` lie in the three-dimensional `Π⁰_v`, `n_v ≠ 0`), `≥ 3` generally; `span = ⊤` needs
    `|X| ≥ 4`, which `deficiency_ne` gives (three bodies of degree two in `Y` form a triangle,
    `def₂ = 0`), and the chapter's distinct planes give it without the count; `U(G) ≠ ∅` is
    `steerSet_nonempty_iff` with `hfeas`. `EarLiftCondition` follows from the third conjunct at
    `a, b ∈ X` (a lift of `G − x` restricts to `Y`).
  - **Composition, spiked (build 6a):** `holdsGenerally_earFree`'s selectors are exactly those
    `liftAttains_of_ear` receives; `scratch/42m/Build6.lean` chains its `.2` into it, with
    `hdef := (hW.deficiency_delete _ _).le`, under `lake lean`.
  - **What build 5's shared steps ask of `Y = G[X]`, `X = W₀ \ {x}`** (traced against
    `Graph.IsPencilGoodEar`): `exists_planeDiff_ne_zero_poly` asks `Y.Simple` (the instance
    `G[X].Simple`), three members in every closed neighbourhood of `Y` (`two_le_degree` and
    `Graph.three_le_ncard_closedNbhd`) and `def₂(Y[Z]) ≠ 0` for `Z ⊆ X`, `|Z| ≥ 2`
    (`deficiency_ne`, through `Graph.induce_induce_of_subset`; `V(Y) = X` by `subset`);
    `finrank_liftSpaceTilde_pencilConfigPoint` asks only an admissible `q` and `z ∈ L_Y(q)`. Neither
    asks the standing hypotheses or attaining heights, so `G[X]` has all they need; `dim L_Y(q) = 4`
    at a main picture is `Graph.IsMainPicture.finrank_liftingSpace_eq` with `deficiency_eq`.
  - **Instances of the two new predicates**: none closed yet. `Graph.IsPencilGoodEar` is produced
    by build 4 and `EarLiftCondition` by build 6b; the candidate witness is `K_{2,3}` (`W₀` all
    five bodies, `x` a body of degree two; `s(W₀) = 3·4 − 2·6 = 0`, `X` a four-cycle with `s = 1`),
    for build 6b or the close's non-vacuity row.
  - **A call, for build 7:** the spike's assembly passes `h₁ h₂` to `liftAttains_of_cutEdge`,
    which build 3 dropped (R-30); build 7 drops them from the call.

## Hand-off / next phase

Builds 1 to 6a landed (`Grade/LiftSmall.lean`; `Grade/LiftCases.lean`, three nodes;
`Grade/LiftCutEdge.lean`, R-30; `Grade/GoodEar.lean`, R-31; `Grade/LiftNoRigid.lean`, the least
`dim L̃` with no map `g`, R-32; `Grade/EarFree.lean`, `-ear-extend`, R-33). What the spike still
holds for later builds, each to land in its build's file: `holdsGenerally_earFree`'s statement
(build 6b), `bnPoint_zero` and the assembly (build 7, whose call of `liftAttains_of_cutEdge` drops
`h₁ h₂`). The next concrete commit is build 6b:
- **Build 6b**, `lem:pencil-d-ear-free` (`holdsGenerally_earFree`) in `Grade/EarFree.lean`,
  probably more than one session. Land its two independent halves first, as statement-level
  sub-lemmas, and assess the rest once they close (a 6c if needed):
  (1) *the algebra at one realization:* points of every closed neighbourhood of `Y = G[X]` of
  rank 3 inside `Π⁰_v`, points of `X` spanning `K⁴` and `dim L̃_Y(b⁰) ≤ 4 + finrank (liftFreeCoords
  Y)` make every lift of `Y` trivial (lifts to `L̃` and back:
  `exists_mem_liftSpaceTilde_of_mem_liftSpace`, `exists_mem_liftSpace_of_mem_liftSpaceTilde`; the
  trivial lifts' maps are four-dimensional by the spanning), and give `EarLiftCondition`'s
  predicate there; (2) *the configuration of `Y`:* `q` off `exists_planeDiff_ne_zero_poly`'s, the
  main-picture and the determinant polynomials for `Y` (*Blockers* has what they ask), `z ∈ L_Y(q)`
  with distinct planes, and the three conditions at `pencilConfigPoint q z` (`dim L̃_Y = 4 + free`
  by `finrank_liftSpaceTilde_pencilConfigPoint`, `Graph.IsMainPicture.finrank_liftingSpace_eq`).
  Then (3) `t₀ ∈ Γ_L`: `planeNormal` at the hubs of `X`, independent on each `H_L[v]` as in
  `lem:pencil-x0-conjunct-three`, completed by `exists_fill_cross₃_eq_smul_of_selector` at a
  selector `hubSelL v` (`exists_isFin3SelectorOf_of_ncard_le_three`; `H_L[v] ⊆ closedHubNbhd v`).
  (4) The transfer: rank 3 and spanning open as the independence of fixed triples and a fixed
  quadruple, (c) as `dim L̃ ≤` its value at `t₀` (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`
  on `liftMatrixPoly Y`, as in `exists_holdsGenerally_finrank_liftSpaceTilde_le`), times `E_L`;
  `exists_earExtend_poly` into `Γ(G)`, `finrank_liftSpaceTilde_smul` for the rescaling,
  `IsZariskiOpen.exists_mem_inter` with `steerSet`, and `HoldsGenerally.of_isZariskiOpen`.
- **Build 7**, `Grade/Generic.lean`: the remark, `liftAttains_of_simple` and the two statements,
  transcribed. Two nodes, the last; then the close.
- **Build tips, from the spike:** in a `change` to `panelSupportExtensor (liftNormal b0 ζ …) …`,
  give `ζ` explicitly (a `_` there ran `whnf` out of heartbeats); the frameworks
  `(ofNormals (G.induce V') ends q).toBodyHinge` and `⟨F.graph.induce V', F.supportExtensor⟩` are
  defeq, but `rw` against `Bricks.lean`'s lemmas needs the `F.graph.induce` spelling.
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` 42k and 42l entries): the six
  `dotPerp` lemmas of `Grade/Feasible.lean` move to `Grade/Realization.lean` beside
  `finrank_dotPerp`, with 42k's `dotPerp_map_eq`, riding the next commit that edits
  `Grade/Realization.lean` (no build above plans to); the home debts of 42b–42k ride with the next
  commit that edits their files (`notes/Phase42k.md` *Hand-off*); build 6a's helpers, each with the
  next commit that edits its home (`isPolyFun_dotProduct` to `Grade/Feasible.lean`, `hubSlotPos`
  and its three lemmas to `Grade/Lift.lean`, the any-selector chart lemmas to `Chart.lean`); at a
  cleanup round, the mirror candidates `finrank_map_of_injOn` and `exists_mem_notMem_of_finrank`.
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
  R-12, R-14 to R-21, R-23 to R-33; aligned: R-1, R-2, R-7, R-8, R-13, R-22; R-6 no departure.

## Decisions made during this phase

- **PI, 2026-11-05 (42m's open):** the PI answered "All 11 as written (Recommended)", whose option
  read: "An Opus open commit, then a pre-build recon that spikes all 11 against Phase 39's d = 3
  Lean and 42l's Lean. Then roughly 4–7 builds (my estimate) and the close of 42m and Phase 42
  together." The question as put, the other options and a note on them: design doc §1.
- **The open** (2026-11-05): the consistency read passed all eleven; their 46 outside `\uses`
  dependencies (53 with the `\cref`s) are green, and they are the blueprint's only red nodes. The
  open's questions for the recon are answered below.
- **Recon: the `d = 3` Lean, file by file.** Reused directly: the steer lemma
  (`exists_isNondegPencilRealization_restrict_of_demoted`, every case's (T1) realization),
  `PencilNondegFeasible.mono`, `.induce_union_singleton`, `.hub_conditions`, the case split of
  `pencilPair_of_not_twoEdgeConnected` and `hasGenericPencilRealization_of_IH`, and `GenericBase`'s
  configuration. Re-opened: `GoodEar.lean`'s proof. Not transcribable: Pair.lean's reposition (it
  fixes neither end's normal). New: every case's extension of a realization of `H` and its (T2).
- **Recon: the induction and the cases.** `liftAttains_of_simple` is a strong induction on
  `V(G).ncard` over simple feasible graphs with a body; a disconnected graph is a nonempty proper
  cut with no crossing edge (no `Connected` test), a side of one body a pendant. Each case is
  `lift_transfer` then `liftAttains_of_holdsGenerally`, the rank from the transferred one; (T1)'s `E`
  is a product of `exists_minorPoly` minors over every closed hub-neighbourhood in `G` (times, at
  the ear, one of `b_a·n_b`, `b_b·n_a`); (T2) is on the maps (`mem_liftMaps_iff`).
- **Recon: the ear's condition** is one predicate, `EarLiftCondition`, at the same selectors on
  both sides: `-lift-ear` takes it at any selectors of `G`, `-ear-free` proves it at every one, and
  the theorem picks them by `exists_steer_selectors`. `-ear-extend`'s `Γ_L` is `Γ(G)`'s parameter
  type read at a selector of `H_L[v]` (R-22's places left empty); no new chart. The good ear
  returns `W₀` in `Graph.IsPencilGoodEar`. The headline is a three-conjunct theorem, no new `def`.
- **Recon: shared steps.** `dim L̃`'s least value is exposed
  (`exists_holdsGenerally_finrank_liftSpaceTilde_le`, spiked from `liftAttains_of_holdsGenerally`'s
  proof); `-ear-free`'s two steps of `-lift-no-rigid`'s proof become one lemma each in build 5.
  Departures: `notes/Cleanup42.md` R-24 to R-27.
- **Build 3: the cut edge's glue** (`Grade/LiftCutEdge.lean`): the recon's frame map, re-derived
  against the current bodies and kept: `t ∈ {b_u, b_v}^⊥` off `K n_u` and, when `v` is a hub, off
  the span `N` of the rest of `u`'s closed hub-neighbourhood in `G`; `E₁` is one minor (that
  hub-neighbourhood independent in `n`), whose non-roots put `r₁`'s own `n_v` off `N`, so the plane
  is not in `N`. `E₁` and the fixed `r₂` are restrictions of one realization of `G`, so no normal is
  changed. The bound `rank G_i ≤ rank G[V_i] + D − 1` was in the tree
  (`BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`). R-30.
- **Build 5: the least `dim L̃` without a map `g`** (`Grade/LiftNoRigid.lean`): at every
  configuration with `z ∈ L(q)`, `dim L̃ = dim L(q) + finrank (liftFreeCoords G)` (two injective
  maps through the lifting system's kernel); a general realization has points of nonzero last
  coordinate, normals of nonzero third coordinate and `q`'s admissible triples independent (each
  open, witnessed at `r*`), so its rescaled points are a configuration over an admissible `q'`;
  `q` off the main-picture polynomial, not Jackson and Jordán's (no `ℓ₀`). The chapter's `g` and
  the transport lemma it would need are not used. R-32.
- **Build 6a: `E_L` by one witness per condition, the `n_u` greedily** (`Grade/EarFree.lean`):
  (a) and (b) are each open and witnessed where their slots are the standard basis at distinct
  places of `Γ(G)`, `E_L` the product (no moment curve). Each `A_u` has dimension at least three,
  or at least two and misses `m_v` (by (b) at a second neighbour of `u`, never adjacent to `v`: no
  triangle with two hubs), so the normals of each closed hub-neighbourhood are chosen one at a time
  in any order, and `exists_mem_forall_eval_ne_zero` takes one point of `∏ A_u` for all. Build 6
  split; `-ear-free` is 6b. R-33.
