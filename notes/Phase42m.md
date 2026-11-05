# Phase 42m — PD-HEAD: the generic conjunct and the headline in every dimension (work log)

**Status:** in progress, opened 2026-11-05 at the PI's word ("All 11 as written", design doc §1),
the second and last sub-phase of Phase 42's last layer, PD-HEAD. Forward mode, the Lean under
`/coordinate-phase`: the eleven red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-generic`, as the chapter states them (six cases of an induction on the bodies, the
lemmas that find the good ear and supply its condition, the generic theorem and the headline).
They are the blueprint's last red nodes, so 42m's close is Phase 42's. The pre-build recon landed
(2026-11-05, *Decisions made*): all eleven signatures kernel-checked, `lem:pencil-d-lift-small`
(1), `-lift-pendant` and `-lift-ear` spiked complete, and the theorem and headline assembled on the
nine lemma statements; seven builds planned. **Build 1 landed** (2026-11-05):
`Grade/LiftSmall.lean`, `lem:pencil-d-lift-small` green. **Build 2 landed** (2026-11-05):
`Grade/LiftCases.lean`, `lem:pencil-d-lift-pendant`, `-lift-ear` (with `EarLiftCondition`) and
`-lift-pendant-triangle` green (four of the eleven red nodes; seven remain).
Next (*Hand-off*): build 3, `Grade/LiftCutEdge.lean`.

## Current state

**Next: build 3** (*Hand-off*). In the tree: `Grade/LiftCases.lean` (build 2: `liftAttains_of_pendant`,
`liftAttains_of_ear`, `liftAttains_of_pendantTriangle`, `EarLiftCondition`, with `pendant_*`, `ear_*`,
`pendantTri_*`, `exists_minorPoly`, `HoldsGenerally.of_forall`, `.mono`,
`IsNondegPencilRealization.toPlane`, `closedNbhd_induce_sdiff`, `LinearIndepOn.pair_of_mem`; all on
the three standard axioms, whole-project build, `lake lint`, `blueprint/lint.sh` and
`blueprint/verify.sh` clean) and `Grade/LiftSmall.lean` (build 1: `liftAttains_of_forall`,
`liftAttains_of_ncard_le_two`, `liftAttains_of_triangle`, `liftAttains_of_cutEdges_eq_empty` and
their helpers `finrank_triangle`, `linearIndependent_normalsJoin_triangle`, `exists_dual_three`,
`LinearIndepOn.triple`, `HasPencilPlaneRealization.restrict`, `PencilNondegConditions.congr_on`,
`.of_induce`, `.induce`, `IsNondegPencilPlaneRealization.induce` and
`exists_isNondegPencilPlaneRealization_glue`; whole-project build, `lake lint`, `blueprint/lint.sh`
and `blueprint/verify.sh` clean). The recon's spike is the gitignored
`scratch/42m/Spike.lean` (1726 lines, `lake lean` clean: no error, 45 warnings, 7 of them the
`sorry`s of the seven lemma statements unspiked then, six still to build, the rest deprecations,
long lines and unused names); `scratch/42m/SpikeAxioms.lean` is it plus `#print axioms`. Sorry-free, on the three
standard axioms: `liftAttains_of_ncard_le_two`, `liftAttains_of_triangle`, `liftAttains_of_pendant`,
`liftAttains_of_ear`, `LiftAttains.hasGradedGenericPencilRealization` (the remark),
`exists_holdsGenerally_finrank_liftSpaceTilde_le`, and every helper above them. The assembly
(`liftAttains_of_simple`, `hasGradedGenericPencilRealization_of_simple`,
`Graph.graded_pencil_conditioned_pair`) compiles and depends on `sorryAx` only through the seven
statements.

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
  (hu : u ∈ V₁) (hv : v ∉ V₁) (hV₁ : V₁ ⊆ V(G)) (hcut : (G.cutEdges V₁).ncard ≤ 1)
  (h₁ : 2 ≤ V₁.ncard) (h₂ : 2 ≤ (V(G) \ V₁).ncard)`, concluding the feasibility of
  `G.induce (V₁ ∪ {v})` and `G.induce ((V(G) \ V₁) ∪ {u})` and that their `LiftAttains` give `G`'s.
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
- `lem:pencil-d-ear-extend`: `exists_earExtend_poly hS hfeas (hW : G.IsPencilGoodEar W₀ x a b)`
  (selectors of `G`) `(hL : ∀ v ∈ W₀ \ {x}, IsFin3SelectorOf {h | h ∈ (G.induce (W₀ \ {x})).closedNbhd v
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
(build 1's proof needs neither; `notes/Cleanup42.md` R-28); encodings: "a triangle" as three
pairwise adjacent bodies, "at a general nondegenerate realization" as `HoldsGenerally` at the given
selectors, `Γ_L` inside `Γ(G)`'s parameter type, "a nonzero polynomial" as one with a non-root.

## Lemma checklist

Build numbers are *Hand-off*'s. "Spiked" means sorry-free in `scratch/42m/Spike.lean`.
- [x] **Pre-build recon** (this commit; *Decisions made*).
- [x] `lem:pencil-d-lift-small`: both parts, sorry-free (build 1; R-28).
- [ ] `lem:pencil-d-lift-cut-edge`: new (build 3).
- [x] `lem:pencil-d-lift-pendant`: sorry-free (build 2; R-24 to R-26).
- [x] `lem:pencil-d-lift-pendant-triangle`: sorry-free, on the pendant's template (build 2; R-29).
- [ ] `lem:pencil-d-lift-no-rigid`: new (build 5).
- [ ] `lem:pencil-d-good-ear`, both outcomes, parts (i) to (v): a transcription (build 4).
- [x] `lem:pencil-d-lift-ear`: sorry-free, with `EarLiftCondition` (build 2; R-24, R-26).
- [ ] `lem:pencil-d-ear-extend`: new (build 6).
- [ ] `lem:pencil-d-ear-free`: new (build 6).
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

- None blocking build 3. What the builds still carry:
  - **Unspiked new math** (the routes are under *Hand-off*; the chapter's proofs were re-read
    against the carrier and none is false): the cut edge's glue, the least `dim L̃` at the
    configuration (`-lift-no-rigid`), and `-ear-extend` with `-ear-free`. Each is one build; a
    build that finds it larger than one session splits it (a statement-level sub-lemma per step)
    and says so.
  - **Instances of the two new predicates**: none closed yet. `Graph.IsPencilGoodEar` is produced
    by build 4 and `EarLiftCondition` by build 6; the candidate witness is `K_{2,3}` (`W₀` all five
    bodies, `x` a body of degree two; `s(W₀) = 3·4 − 2·6 = 0`, `X` a four-cycle with `s = 1`),
    for build 6 or the close's non-vacuity row.
  - **A dependency edge, for build 3:** `-lift-cut-edge`'s rank step `\cref`s
    `lem:pencil-x0-fibre-intersection`, which its proof does not `\uses`; build 3 adds the edge.
  - **A pin, for build 5:** `exists_holdsGenerally_finrank_liftSpaceTilde_le` goes into
    `Grade/LiftWitness.lean` (and `liftAttains_of_holdsGenerally` can then use it); its node is
    `lem:pencil-d-lift-one-witness`, whose proof the chapter's `-lift-no-rigid` cites.

## Hand-off / next phase

Builds 1 and 2 landed (`Grade/LiftSmall.lean`; `Grade/LiftCases.lean`, three nodes). Build 2
transcribed the spike's pendant and ear sections and the shared steps they use; its pendant triangle
is new, on the pendant's template (R-29): (T1) `pendantTri_T1`, `b'_{xᵢ}` in `n_c^⊥` completing `b_c`
to an independent triple, `n'_{xᵢ} = n_c`; (T2) `pendantTri_T2`, one form `ψ_c` at `x₁`, `x₂`, `c`;
the rank `pendantTri_rank` by `finrank_span_rigidityRows_cutVertex_eq` at `c`, `finrank_triangle` and
`deficiency_eq_add_of_cutVertex`, the triangle's deficiency zero by `finrank_liftNormal_le`. What the
spike still holds for later builds, each to land in its build's file: `HoldsGenerally.and`
(build 3), `bnPoint_zero`, `exists_holdsGenerally_finrank_liftSpaceTilde_le` (build 5, its
`Grade/LiftWitness.lean` pin), and the assembly (build 7). Build 3 imports `LiftCases` for
`exists_minorPoly`, `HoldsGenerally.of_forall`, `.mono` and `closedNbhd_induce_sdiff`.
Then:
- **Build 3**, `Grade/LiftCutEdge.lean`: sides feasible by `PencilNondegFeasible.induce_union_singleton`;
  two `lift_transfer`s, combined by `HoldsGenerally.and` and `MvPolynomial.exists_mem_eval_ne_zero₂`
  on the image of the lifts in the maps' coordinates; the rank by
  `le_finrank_span_rigidityRows_of_cut` and a bound `rank G_i ≤ rank G[V_i] + D − 1` (not found in
  the tree; one edge's rows span at most `D − 1`); the deficiencies by
  `deficiency_eq_of_cutEdges_ncard_le_one` and `deficiency_induce_union_singleton`. (T2): `ψ`
  extending `φ_{1,v}`. (T1), the glue, is new: Phase 39's `exists_reposition_cross_incidences_avoiding`
  does not transcribe (it fixes neither end's normal, where (T1) keeps `r₁`'s normals on
  `V₁ ∪ {v}`). Proposed (not spiked): pick `t ∈ P = {b_u, b_v}^⊥` off `K n_u` and the subspaces
  `N_S ∩ P`, proper when `E₁ ≠ 0`, and `t′ ∈ P′` likewise; then a frame map (`Module.Basis.equiv`,
  as Arms.lean) with `g b′_u = b_u`, `g b′_v = b_v`, `gᵀ t = n′_v`, `gᵀ n_u = t′` exists, the four
  pairings agreeing; the chapter's generic `g` is the alternative. `E₂ ≠ 0` at some realization of
  `G₂` by the chapter's change of `u`'s normal. One node.
- **Build 4**, `Grade/GoodEar.lean` (graph theory; may go first): `Graph.IsPencilGoodEar` and
  `exists_goodEar_or_pendantTriangle`, re-opening `exists_oneEar_or_pendantTriangle`'s proof to
  return `W₀`; (iii) by `Graph.exists_eq_triple_of_minimal` at `x` and `a`,
  `partitionDef_two_induce_insert_id` and `Graph.partitionDef_add_partitionDef_induce_id_le`; (iv)
  by `deficiency_three_induce_eq_zero_of_tight`, `deficiency_eq_zero_of_deficiency_eq_zero_of_le`
  (`3 → n`), `deficiencyMerged_eq_deficiency_of_mem` and `IsOpenEar.deficiency_induce_le` at `n`,
  and `partitionDef_induce_insert` for `≥`; (v) from (i) and `hF1`. One node.
- **Build 5**, `Grade/LiftNoRigid.lean` (and the least-value lemma into `Grade/LiftWitness.lean`):
  the configuration as `GenericBase.lean`'s `d = 3` proof (`q` off `hatt`'s `P`, the
  Jackson–Jordán polynomial, `exists_det_poly`, `exists_planes_separate`; `z ∈ L(q)^{r+1}` with
  `R(z) ≠ 0` and the planes of its first column distinct, by `exists_mem_eval_ne_zero₂`;
  `isNondeg_pencilConfig_of_planeDiff`, `toPlane`); the lift by the other columns
  (`mem_liftMaps_iff`, `liftNormal = pencilConfigPointGrade`); `liftAttains_of_least` with the
  least value: spanning holds generally, and at a spanning realization a map `g` (last coordinates
  nonzero, `gΠ_v ∌ e₃`) and a rescaling (`finrank_liftSpaceTilde_smul`, a new transport lemma for
  `L̃`) make the points a configuration with `dim L̃ ≥ ℓ₀ + c`; `c` counts the free coordinates,
  as `liftSpaceTilde` lives on all of `α`. The two steps `-ear-free` re-runs (distinct planes in
  `L(q)`; `L(b⁰) = L(q)`) as one lemma each for any standing graph with no planar-rigid set. One node.
- **Build 6**, `Grade/EarFree.lean`: `exists_earExtend_poly` (the chapter's (a), (b), `E_L` at the
  moment curve; `n_u ∈ A_u` by an `n`-ary `exists_mem_eval_ne_zero₂` on `∏ A_u`; `cross₃` of a basis
  of `b_v^⊥`) and `holdsGenerally_earFree` (condition (c) open by
  `Matrix.exists_mvPolynomial_section_mulVec_eq_zero`, with `L̃`'s free coordinates counted; the
  configuration of `Y` by build 5's lemmas; `t₀` by `planeNormal`; `U(G) ≠ ∅` and
  `IsZariskiOpen.exists_mem_inter`). Two nodes; split if long.
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
  commit that edits their files (`notes/Phase42k.md` *Hand-off*); at a cleanup round, the mirror
  candidate `finrank_map_of_injOn`.
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
  R-12, R-14 to R-21, R-23 to R-29; aligned: R-1, R-2, R-7, R-8, R-13, R-22; R-6 no departure.

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
