> **Cleared for session 1 on the PI's word, 2026-10-30, with the coordinator's defaults for the
> draft's seven choices** (answer: "Clear with these defaults"; the defaults as put, verbatim:
> "Q1(a) means agreement at d = 3 realization by realization, through the polarity, with the
> minimal candidate (N1 + N3) kept in the table as the 'what N2 buys' baseline even though it
> fails (a); whether a conjunct that reduces to distinct + N3 is acceptable waits for the table;
> survival under the lower-dimension embedding is a reported column, not a requirement; a
> configuration-space family may be a candidate, with its misses (e.g. K_{2,3} at d = 3)
> recorded; d = 3, 4, 5; workbook at notes/attacks/nondeg/workbook.md; reviews every three
> sessions; keep 229 lines."). Session 1 starts by settling §4's four `[READING]` items.
> After session 1, 2026-10-30, on the PI's word (the question put: "Which nondegeneracy should the
> Pᵈ generic conjunct use?"; the answer: "(A) C2-same", whose option read "N1 and N3 on the
> points, and the hub planes around each body meet as in P³ (dim ⋂_{w∈S} Π_w ≤ 4 − |S|).
> Feasibility is Phase 39's word for word in every d (S9). Cost: an irreducible carrier in Pᵈ for
> the planar-rigid case and the pendant-body and cut-edge arms (R-L, S13), the next sessions'
> work."). Session 2 takes C2-same as the definition and works on its carrier.
> After session 2, 2026-10-30, on the PI's word: asked "Who proves (W), the one remaining piece of
> new mathematics for the Pᵈ generic conjunct under C2-same?", the PI answered "(a) NONDEG s3
> attacks", whose option read "NONDEG session 3 attacks (W): extend a realization of G[W₀] that is
> general for G[X] to a nondegenerate realization of G, one condition at a time, and hunt for
> counterexamples beyond nine bodies." Asked whether review 1 runs early, the PI answered "Review
> now": `/review-attack nondeg` runs before session 3.
> Review 1, 2026-10-30, verdict "continue", with two findings: F1, S24 (1) and S29 need the minimal
> planar-rigid set W₀ from the good-ear lemma's statement, which returns only the ear (O8); F2,
> S21's (T1) is false as written (the cut-edge glue), with a one-paragraph repair. On the PI's word
> (asked "May NONDEG session 3 record F1 and F2 in its state before attacking (W)?", answered "(a)
> Yes, both first"): session 3's first results are the S21 repair and O8 in the state, then (W).
> After session 3, 2026-10-30, on the PI's word (asked "S36 claims (W) at every W₀-ear, the last
> piece of new mathematics in NONDEG's scope; with it the Pᵈ generic conjunct under C2-same needs
> only (A) and O8's write-up (S38). What next?", answered "(a) Review 2 now", whose option read
> "Review 2 now on S32–S38 (/review-attack nondeg). If it passes, stop the track and hand S38's five
> pieces to the write-up as red nodes, with O8 as W10's node.").
> Written 2026-10-30 by an agent (Claude
> Opus 5.5) against the tree at `947fa75d`, from the owning sections: `notes/Phase42-design.md`
> §2.1 rows 19–22, §2.2, §2.3 ONE-EAR, CARRIER and GENERIC, §2.4 T4 and §2.5; `pencil.tex`'s
> duality and nondegeneracy subsections, `pencil-d.tex`'s introduction and first two subsections,
> and `main-component.tex`'s last subsection (all in `blueprint/src/chapter/`); and the Lean of
> §1, read from definition bodies. Its claims are the writer's readings; a session re-derives what
> it builds on (`HARNESS.md` *Evidence*). Rewritten only at milestones or by the PI's word.
>
> **Where it runs.** Session by session, dispatched by the central session `/coordinate-tracks
> 42d`, each in an isolated git worktree. No `lake build` or Lean server: the Lean is read as
> text, and a needed Lean witness is a question to the coordinator. By hand and in exact Python;
> nested subagents are blocked. Results S1, S2, … in `notes/attacks/nondeg/workbook.md`, drivers
> in `notes/attacks/nondeg/drivers/`, status in `state.md`.

# NONDEG: what "nondegenerate" means in `Pᵈ`, and what proving it would take

## 0. Where this sits

PENCIL-D (Phase 42) asks whether the pencil realization theorem holds in every `Pᵈ`. Its headline
is Phase 39's conditioned pair there: bare, adjacent-distinct when `G` is simple, and generic
(nondegenerate at the deficiency rank) when `G` is simple and has a nondegenerate realization.
42d aims at informal proofs of all three at every `d`; 42b stated the first two in `Pᵈ`. The third
has no `Pᵈ` statement because nondegeneracy has none: two of its `P³` conditions are "at most
three" bounds from 3-spaces of `K⁴` (step table row 21), and its `P³` proof, route B, fails as
written at `d ≥ 4` (row 22). This track settles what it should say and sizes its proof (§6).

## 1. The consumer

**Phase 39** (grade 2, `K⁴`):
- `HasPencilPanelRealization G F n p`, in
  `CombinatorialRigidity/Molecular/Molecule/Pencil/Statement.lean`:
  `HasCoplanarPanelRealization G F n` (in
  `CombinatorialRigidity/Molecular/AlgebraicInduction/Theorem55.lean`: `F.graph = G`; `n v ≠ 0`
  on `V(G)`; every supporting extensor nonzero, at every label; each link's hinge in both ends'
  panels); `p v ≠ 0` and `p v ⬝ n v = 0` on `V(G)`; each link's hinge through `p` at both ends.
- `IsNondegPencilRealization G F n p`, in
  `CombinatorialRigidity/Molecular/Molecule/Pencil/Motive.lean` as are the next three: a pencil
  realization, and
  - **N1**: `![p u, p v]` linearly independent at every link `uv`;
  - **N2**: at every `v ∈ V(G)`, `n` linearly independent on `G.closedHubNbhd v`, the hubs
    (degree at least 3) among `v` and its neighbours; `v` need not be a hub;
  - **N3**: at every `v ∈ V(G)` that is not a hub, `p` linearly independent on `G.closedNbhd v`.
- `PencilNondegFeasible K G`: `∃ F n p, IsNondegPencilRealization G F n p`.
- `HasGenericPencilRealization K n G`: `∃ F n p`, nondegenerate, whose rows span
  `screwDim 2 · (|V(G)| − 1) − G.deficiency n` dimensions (in `ℤ`).
- `PencilPair K n G`: `(G.Simple → PencilNondegFeasible K G → HasGenericPencilRealization K n G)
  ∧ (G.Simple → HasDistinctPencilRealization K n G) ∧ HasPencilRealization K n G`. **The generic
  conjunct is the first**; the second asks N1 alone.

**42b's carrier** (`CombinatorialRigidity/Molecular/Molecule/Pencil/Grade/Realization.lean`;
grade `k`, `d = k + 1`, `K^{d+1}`):
- `HasPencilPlaneRealization G F b Π`: `HasCoplanarPanelRealization G F b`; `dim Π_v = 3` and
  `b_v ∈ Π_v` on `V(G)`; each link's hinge passes through `Π_u^⊥` and `Π_v^⊥`
  (`ExtensorThroughSubspace`; `dotPerp` is the dot product's orthogonal).
- `HasGradedDistinctPencilRealization K k n G`: `∃ F b Π`, a plane realization with `![b u, b v]`
  independent at every link, whose rows span `screwDim k · (|V(G)| − 1) − G.deficiency n`.
- At grade 2, `hasGradedPencilRealization_two_iff` holds on one framework with `Π_v = q_v^⊥`, and
  `hasGradedDistinctPencilRealization_two_iff` through the polarity `screwComplementIso`,
  `(F, n, p) ↦ (F′, p, n)`, which keeps the rank (`lem:pencil-d-rank-agrees-three`).

**The `P³` consumers.** `X0Gen K α β` (`CombinatorialRigidity/Molecular/Molecule/Pencil/X0.lean`):
every simple two-edge-connected `G` on at least three bodies with `PencilNondegFeasible K G` has
`HasGenericPencilRealization K 3 G`; a hypothesis of `pencil_realization_theorem_of_X0`. Its
proof `x0Gen` (`CombinatorialRigidity/Molecular/Molecule/Pencil/MainComponent/Statements.lean`) is
a corollary of `pencilPair_of_nonempty`; the producer, there too, is
`hasGenericPencilRealization_of_IH`:
- `[Infinite K] [Finite α] [Finite β]`; `hS : G.Simple`; `hV : 3 ≤ V(G).ncard`;
  `htec : G.TwoEdgeConnected`; `hfeas : PencilNondegFeasible K G`;
- `hIH`: every nonempty graph on fewer bodies satisfies `PencilPair K 3`, whose generic conjunct
  is consumed at the graph left by the removed bodies;
- conclusion: `HasGenericPencilRealization K 3 G`.

Its proof, route B (`main-component.tex`'s last subsection): without a planar-rigid set the
general configuration is nondegenerate; otherwise, given the two hub conditions, a body of degree
two with hub ends or a pendant triangle extends the smaller graph's generic realization. Both
extensions, and the cut-edge arm of `pencil.tex`'s `lem:pencil-pair-loop-base-cut`, steer through
`lem:pencil-generic-steer`, an irreducible parametrization of the nondegenerate realizations.

## 2. Setting

**Grade 2.** The polarity exchanges normals and points of a pencil *realization*
(`lem:pencil-self-dual`), but nondegeneracy is not self-dual: N1 and N3 constrain points, N2
normals. On one framework `b_v` is Phase 39's normal and `Π_v^⊥ = ⟨q_v⟩` its point, so 42b's N1
on the `b`'s matches Phase 39's only through the polarity, whose image has points `b`, normals `q`.

**Grade `k`, the polar picture** (`pencil-d.tex`'s introduction): `b_v` is a point of `Pᵈ`, `Π_v`
a plane through it, and the hinge of `uv` is polar to a line in `Π_u ∩ Π_v`, `b_u ∨ b_v` when the
two points are independent.
- (F1) `b_w ∈ Π_v` for every `w` in the closed neighbourhood `N[v]`
  (`HasPencilPlaneRealization.normal_mem_plane_of_mem_closedNbhd`). So the `b`'s of `N[v]` span
  at most 3 dimensions, and `Π_w^⊥ ⊆ b_v^⊥` for every `w ∈ N[v]`.
- (F2) At a link `uw`, the flats `Π_u^⊥` and `Π_w^⊥`, of dimension `d − 2`, lie in the hinge's
  span, of dimension `d − 1`, so they meet in dimension at least `d − 3`; equivalently
  `dim(Π_u ∩ Π_w) ≥ 2`. Nothing is forced at `d = 3`; adjacent flats meet from `d = 4` on.
- (F3) Two general 3-spaces of `K^{d+1}` meet in dimension `max(0, 5 − d)`.

**The polar transcription** reads N1–N3 on the polar image at grade 2.
- N1: `b_u, b_v` independent at every link, 42b's condition. It lifts verbatim.
- N3: at a non-hub, the `b`'s of `N[v]` independent. It lifts verbatim by (F1); at a hub of a
  simple graph it is impossible in every `d`, as at `d = 3`.
- N2: at every `v`, with `S = closedHubNbhd v`, the `q_w` (`w ∈ S`) independent; equivalently the
  planes `Π_w`, all through `b_v`, meet in dimension `4 − |S|`. In `Pᵈ` it bears on the flats
  `Π_w^⊥ ⊆ b_v^⊥`, or the planes `Π_w ∋ b_v`. Both verbatim readings, a direct sum of flats and
  planes meeting in the general-position dimension, fail at every adjacent pair from `d = 4` on
  (F2). So N2 needs a new reading, and what is forced depends on the graph.

**The direct transcription**, a foil, reads N1–N3 on one framework: normals `b`, points `Π^⊥`.
N2 lands on the `b`'s and lifts verbatim by (F1); N1 and N3 land on the flats, and N1 is
unsatisfiable from `d = 4` on (F2). As existential statements both transcriptions agree with
Phase 39's at `d = 3`, since the polarity is a rank-preserving bijection of realizations. So
agreement alone does not choose between them; implying the distinct conjunct does.

## 3. The questions

For each `d ≥ 3` let `Nondeg_d(G, F, b, Π)` be a predicate on pencil realizations in dimension
`d`, `Feasible_d(G)` be `∃ F b Π, Nondeg_d`, and `Generic_d(G)` add the rank. The `Pᵈ` generic
conjunct is `G.Simple → Feasible_d(G) → Generic_d(G)`.

- **Q0, the consumers.** What consumes the `P³` generic conjunct: the Lean (§1 and anything else),
  the blueprint, `formalization.yaml`'s descriptions, the molecule reading of the theorem. What is
  lost if `Nondeg_d` keeps only N1 and N3, and what if the `Pᵈ` headline drops the conjunct.
- **Q1, the candidates,** each required:
  - (a) to agree at `d = 3` through the polarity: `Nondeg_3(G, F, b, q^⊥)` exactly when
    `IsNondegPencilRealization G F′ q b`, `F′` the polar framework. Then `Feasible_3` is
    `PencilNondegFeasible` and `Generic_3` is `HasGenericPencilRealization`, as
    `hasGradedDistinctPencilRealization_two_iff` has it for the distinct conjunct;
  - (b) to imply N1 on the `b`'s, so that a generic realization is adjacent-distinct;
  - (c) to be open: each condition is a minor's nonvanishing in the coordinates of `b`, `Π` and
    the hinges.

  At least these three:
  - **C1, minimal:** N1 and N3 on the `b`'s.
  - **C2, the planes meet no more than forced:** N1, N3, and at every `v` and
    `S ⊆ closedHubNbhd v` with `|S| ≥ 2`, `dim ⋂_{w∈S} Π_w ≤ f_d(G, v, S)`. The track names `f_d`
    from `G` and `d` alone, with `f_3(G, v, S) = 4 − |S|`, which is N2.
  - **C3, configuration-based:** `(b, Π)` lies in a named irreducible family `𝓡_d(G)` of
    realizations, off a named proper closed subset.

  Also: does each survive the embedding of a lower dimension (`pencil-d.tex`'s last section),
  which keeps the dimension of every span and meet, as Tier 0's distinct conjunct does?
- **Q2, feasibility,** per candidate: the `Pᵈ` analogues of the two hub conditions (at most three
  members in each closed hub-neighbourhood; no triangle with two hubs) and of the obstruction from
  two hubs with three common neighbours; then the feasible graphs at `d = 4, 5`, with `d = 3` the
  control, among `K₄`, `K_{2,3}`, `θ(2,2,2,k)`, D's candidate witness (design doc §2.3 GENERIC),
  §2.5's content-range graphs and the `--d4` population (`notes/scripts/README.md`, `strata/`).
  An exhibited exact realization proves feasibility; infeasibility needs an argument.
- **Q3, the rank.** At feasible graphs, does a nondegenerate realization reach the deficiency
  rank? Exact, seeded, committed driver; each draw a lower bound only (`HARNESS.md` *Evidence*). A
  miss needs an obstruction argument, as T4's `θ(2,2,2,10)` had (design doc §2.4). A forced miss
  at a feasible graph refutes that candidate's conjunct.
- **Q4, the route** for the leading candidate: (R-B) route B, an irreducible parametrization of the
  `Nondeg_d` realizations in place of the steer; (R-C) a corollary, the general configuration
  being nondegenerate wherever `G` is feasible, so the bare and distinct proof gives it; (R-E)
  ONE-EAR's step at `d ≥ 5` (design doc §2.3: the motive, the insertion, X2). Size each piece of
  new mathematics as a possible attack track: statement, first `d` where it bites, evidence.

## 4. What is known

`[PROVED]` cites its node, `[MEASURED]` its population; a `[READING]` is the writer's, unverified,
and a session proves or refutes it before building on it. (F2), (F3) and §2's transcriptions are
readings, by dimension counts.
- `[PROVED]` In `P³`, in Lean: the hub conditions; the two-hubs obstruction (no configuration over
  a general picture of `K_{2,3}` is nondegenerate, though the prose after it shows `K_{2,3}`
  feasible); route B. In every `d`: (F1); a configuration over an admissible picture is a plane
  realization with N1 (`lem:pencil-d-config-realization`); Tier 0's distinct conjunct, from
  attaining configurations (`Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three`).
- `[READING]` **Under C1 the conjunct is a corollary at the main component.** Over an admissible
  picture the three members of `N[v]` at a body of degree two have independent picture points,
  and their `b`'s are an injective linear image of them. So attaining configurations satisfy N1
  and N3 in every `d`, and C1's main-component statement follows from the coverage, Tier 0
  included; at `d = 3` this is the half of `lem:pencil-x0-conjunct-three` that needs no hub
  condition. C1 loses N2: at `K_{2,3}` its generic realization may have the hubs' planes equal.
- `[READING]` **`K₄` separates the readings of `f_d`.** Every `N[v]` of `K₄` is all four bodies,
  so by (F1) and N1 either the four `b`'s span 3 dimensions and the four planes are equal, or the
  `b`'s lie on a line `L`, every plane contains `L` and the six hinges coincide. There the rank is
  `3D − 3`, below the target `3D` (`def_D(K₄) = 0`). An `f_d` that lets three planes meet in `L`,
  as "forced by the shared points" would read, makes `K₄` feasible and its conjunct false.
  `f_3 = 4 − |S|` rules this out at `d = 3`.
- `[READING]` **The two-hubs obstruction lifts in polar form.** Hubs `a ≠ b` with three common
  neighbours whose `b`'s are independent have `Π_a = Π_b` by (F1). A candidate keeping apart the
  planes of two hubs in one closed hub-neighbourhood then rejects every configuration over a
  general picture of such a graph, so R-C fails there under C2, as at `d = 3`.
- `[READING]` (row 22, checked against the text by 42a's coordinator) The steer writes a point as
  the cross product of at most three hub normals in `K⁴`; in polar form `b_v` lies in the meet of
  its hub-neighbourhood's planes, free only at `d = 3` (F3). The one-ear step puts `b_x` in
  `Π_a ∩ Π_b`, generically 0 from `d = 5` on.
- `[MEASURED]` T4 (design doc §2.4): on `θ(2,2,2,10)` at `d = 4`, `G − x` misses its target by one
  where `b_x, b_y, b_w` are independent, a forced miss (`Π_a = Π_b`), on a locus polar N2 calls
  degenerate. §2.5's 85 content-range cells reach the rank at a drawn configuration (lower bounds,
  populations and caps as there); none checks N2. D's witness's feasibility is unchecked.
- `[READING]` Q0's start: at `947fa75d` no Lean file outside `Pencil/` and `Nonvacuity.lean` names
  the generic API; `CombinatorialRigidity/Molecular/Molecule/Application.lean` (KT Corollary 5.7)
  does not name the pencil; Nonvacuity's two pencil witnesses take the distinct conjunct.

## 5. A suggested order (session 1 chooses; `HARNESS.md` binds)

1. The consumer diff of §1 against the Lean (`HARNESS.md` *Evidence*); Q0 by reading.
2. Q1 by hand, one result per candidate and criterion, settling §4's readings first on `K₄` and
   `K_{2,3}`. C2 is the crux: name `f_d`, or show none meets (a)–(c) and keeps `K₄` infeasible.
3. Q2 by hand per surviving candidate; then a driver whose exact nondegenerate realizations
   certify feasibility at `d = 3, 4, 5`, matching the `P³` lemmas at `d = 3`.
4. Q3's driver on the feasible graphs, with an obstruction argument for every miss.
5. Q4's sizing; the deliverable; stop for the PI.

Drivers reuse `notes/scripts/strata/strata.py` read-only (`content_graphs`, `pd_pencil`,
`deficiency`, `def_certified`); `w4/flanks.py`'s `nondeg_conjuncts` checks N1–N3 at `d = 3`.

## 6. Deliverable, and what it settles

In the workbook as numbered results, and in `state.md`, whose obligations are its open cells:
- **A candidates table.** Rows C1, C2 (one per `f_d` tried), C3, and the direct transcription as a
  control. Columns (a), (b), (c), the embedding, the feasible class at `d = 3, 4, 5` on the named
  population, Q3's verdict and Q4's route, each cell citing an S-number.
- **A verdict on Q0–Q4** (confirmed with its witness, refuted, open) and **a recommendation**:
  which candidate, at what cost, each piece of new mathematics sized as a possible attack track.

The choice of definition is the PI's; proving the generic conjunct, and any Lean, are out of
scope. A candidate whose conjunct fails at a feasible graph, certified exactly, is a result.

## 7. Pointers

- `notes/Phase42-design.md` §2.1 rows 19–22, §2.2, §2.3, §2.4 T4, §2.5; `notes/Strata.md` Results
  7, 12–15, 22, 23, 25; `notes/Phase42b.md`.
- `pencil.tex`: `lem:pencil-self-dual`; `def:pencil-nondegenerate` to
  `lem:pencil-pair-loop-base-cut`. `main-component.tex`: `lem:pencil-feasible-hub-conditions` to
  `thm:pencil-x0-generic-attains`. `pencil-d.tex`: `def:pencil-d-realization` to
  `lem:pencil-d-config-realization`, and the embedding section.
- Route B's Lean, beyond §1: `Pencil/MainComponent/Generic{Base,Steer,Ear,Triangle}.lean`,
  `Pencil/Reseed.lean`, `Pencil/Pair2.lean`, under `CombinatorialRigidity/Molecular/Molecule/`.
