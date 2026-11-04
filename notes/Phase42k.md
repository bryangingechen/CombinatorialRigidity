# Phase 42k — PD-REDUCTION: Phase 39's reduction in every dimension (work log)

**Status:** in progress, opened 2026-11-04 at the PI's word ("All 8 nodes as written
(Recommended)", design doc §1), a sub-phase of Phase 42 that takes its layer PD-REDUCTION whole.
Forward mode, the Lean under `/coordinate-phase`: the eight red nodes of
`blueprint/src/chapter/pencil-d.tex`'s `sec:pencil-d-reduction`, three on linear algebra
(`lem:pencil-d-two-pencil-extension`, `lem:pencil-d-projective-transport`,
`lem:pencil-d-cut-reposition`), four cases (`lem:pencil-d-loop-case`, `lem:pencil-d-base-case`,
`lem:pencil-d-cut-case`, `lem:pencil-d-nonsimple-case`) and the theorem
`thm:pencil-d-realization-theorem`, on the `Pencil/Grade/` carrier, Phase 39's
`Graph.pencil_reduction` and 42j's distinct statement. The open's consistency read found every
proof routing through the argument its statement claims and every outside dependency green
(*Decisions made*); its questions for the recon are under *Blockers*. Next (*Hand-off*): the
pre-build recon of the eight nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The eight targets, leaf-first:
- *The linear algebra.* `lem:pencil-d-two-pencil-extension` rests on
  `def:genuine-hinge-realization`, `def:extensor-through-flat`, `def:extensor` and
  `lem:decomposable-extensor-span-unique`;
  `lem:pencil-d-projective-transport` on `def:pencil-d-realization`, `def:induced-screw-map` and
  `lem:screw-map-rows`; `lem:pencil-d-cut-reposition` on no node (no `\uses`: a choice of bases).
- *The cases.* The loop case on two-pencil (1); the base case on two-pencil (1) and (3) and
  `lem:theorem-55-base`; the cut case on the three linear-algebra nodes, `lem:block-rank-cut`,
  `lem:cut-edge-decomposition` (1) and `lem:relative-deficiency-rank-bound`; the nonsimple case on
  two-pencil (1) and (3), `lem:theorem-55-base`, `def:rigid-contraction`, `lem:reduction-measure`
  and `lem:pencil-contraction-deficiency`.
- *The theorem*, on `thm:pencil-reduction` (`Graph.pencil_reduction`), the four cases and
  `lem:pencil-d-distinct-statement` (42j).

Every dependency outside the eight is green. Outside them only `cor:pencil-d-conditioned-pair`
(PD-HEAD) uses one, the theorem; `lem:pencil-d-lift-small`'s proof cites the base case's one-edge
count without a `\uses` edge. The chapter is the lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eight nodes as the chapter states them.
  Their close ends PD-REDUCTION; PD-HEAD (21 nodes) comes next, at the PI's word.
- **Encoding** as 42b–42j: grade `k = d − 1`, so the targets are `HasGradedPencilRealization K
  (m + 1) (m + 2)` and `HasGradedDistinctPencilRealization K (m + 1) (m + 2)` at `m = d − 2`, with
  `d ≥ 3` as `1 ≤ m` and the deficiency at `n = m + 2`, `bodyBarDim (m + 2) = screwDim (m + 1)`,
  the form of 42j's `Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`.
- **What 42j hands on** (`notes/Phase42j.md` *Hand-off*): that distinct statement, at `1 ≤ m`, for
  the simple 2-edge-connected graphs on at least three bodies, the theorem's third case.
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof, in the same commit
  (R-9 to R-12 and R-14 to R-17 open; R-7, R-8 and R-13 aligned).

## Lemma checklist

- [ ] **Pre-build recon**: the eight spiked against Phase 39's `d = 3` Lean and the landed carrier,
  exact Lean signatures, their files, and the questions under *Blockers*.
- [ ] `lem:pencil-d-two-pencil-extension`, parts (1) to (3).
- [ ] `lem:pencil-d-projective-transport`.
- [ ] `lem:pencil-d-cut-reposition`.
- [ ] `lem:pencil-d-loop-case`.
- [ ] `lem:pencil-d-base-case`, both forms.
- [ ] `lem:pencil-d-cut-case`, both forms.
- [ ] `lem:pencil-d-nonsimple-case`.
- [ ] `thm:pencil-d-realization-theorem`, by `Graph.pencil_reduction`.
- [ ] **Close** 42k, an intermediate sub-phase close that ends PD-REDUCTION (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking the recon. Its questions, from the open's consistency read:
  - **The `d = 3` Lean, file by file**, all at grade 2 with points (`BodyHingeFramework K 2`,
    `Fin 4`), where the targets are at grade `m + 1` with planes (`HasPencilPlaneRealization`).
    `Pencil/Arms.lean`: the loop case (`hasPencilRealization_of_isLoopAt`), the transport
    (`hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`), the reposition
    (`exists_reposition_cross_incidences`) and the cut case
    (`hasPencilRealization_of_not_twoEdgeConnected{,_core}`,
    `hasDistinctPencilRealization_of_not_twoEdgeConnected`, the glue
    `exists_hasPencilPanelRealization_glue`). Its lines 352–604
    (`exists_reposition_cross_incidences_avoiding` and three dimension lemmas) serve only the
    conditioned pair's generic cut case (`Pair.lean`). `ArmsAssembly.lean`: the base case
    (`hasPencilRealization_of_ncard_le_two`). `X0.lean`: the nonsimple case
    (`hasPencilRealization_of_not_simple`, lines 68–335) and the three-way split the theorem's
    proof follows (`pencilPair_of_X0`). `Statement.lean`: the two-pencil lemma and its converse at
    `Fin 4`, by cross-incidences (`exists_extensor_two_pencils{,_iff}`). `Pair2.lean`: the
    reduction's assembly (`pencilPair_loop_base_cut`, `pencilPair_of_arms`). Which transcribe to
    grade `k` with planes, and which are new.
  - **The two-pencil lemma.** The cases use only parts (1) and (3): the loop and cut cases part
    (1), the base and nonsimple cases both. Part (2), the converse, has no consumer among the eight
    but is in the node as stated. Landed tools at every grade:
    `span_range_eq_of_extensor_eq_grade` (`Grade/Realization.lean`, a nonzero extensor determines
    its span), `exists_extensor_in_two_panels_grade` (`AlgebraicInduction/PanelLayer.lean`); `C_B`
    as the extensor of a basis of `dotPerp B`.
  - **The transport and the reposition.** At every grade:
    `BodyHingeFramework.screwEquivOfLinearEquiv`,
    `BodyHingeFramework.finrank_span_rigidityRows_mapExtensor` and
    `exists_contragredient_linearEquiv` (`Arms.lean`, at every `n`); the plane goes to its image
    under `g`. The reposition needs no contragredient, only two independent pairs extended to
    bases. FRICTION's open `contragredientEquiv` (`Meet.lean`) rides with any commit that edits
    `Meet.lean`.
  - **Where the chapter's route is not the `d = 3` Lean's** (the standing rule decides the rows).
    The base case's one-edge rank: the `d = 3` Lean counts `D − 1` independent rows
    (`exists_independent_rigidityRows_of_edge`) under the deficiency bound, the chapter counts
    motions. Its adjacent-distinct form: at `d = 3` it comes from the generic conjunct
    (`pencilPair_of_ncard_le_two`, `Pair.lean`), with no direct Lean; the chapter builds it. The
    nonsimple case: the `d = 3` Lean adds the rows by the splice
    (`le_finrank_span_rigidityRows_of_splice`) under the deficiency bound and keeps the other
    parallel edges' hinges from `G/H`; the chapter counts motions and gives them `C_{B_2}`.
  - **The theorem's form.** `Graph.pencil_reduction` at `n = m + 2` (`hD` by the public
    `Graph.six_le_bodyBarDim`, `BodyBar/Framework.lean`) or at `n = 3`: its property is
    arbitrary, `n` enters only the proper rigid subgraph, and the proof reads neither that nor the
    degree-two body, so `hcontract` and `hsplit` are one function, as in
    `pencil_realization_theorem_of_X0`. The property (rank, and adjacent-distinct when simple), as
    `cor:pencil-d-conditioned-pair` (PD-HEAD) will consume it.
  - **Files.** New `Grade/` file(s), at the recon's choice. A deferral naming a file a build edits
    rides with it (design doc §3).

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice), as `fe5baf0f` (42h), `3ab48a47` (42i) and
`661f0382` (42j) were. It spikes the eight against Phase 39's `d = 3` Lean (*Blockers*) and the
landed carrier (`Pencil/Grade/Realization.lean`, `Collineation.lean`, `Coverage.lean`), pins the
eight Lean signatures and the file plan, each spiked under `lake lean`, settles *Blockers*, and
records the signatures here. Then build leaf-first, roughly 4–8 commits by the coordinator's
estimate in the option the PI chose. Each build adds its node's `\lean{}` and `\leanok`.
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): the home debts of
  42b–42i are unchanged, each riding with the next commit that edits its target file
  (`notes/Phase42i.md` *Hand-off* lists 42i's; 42j added none).
- **After 42k:** PD-HEAD (`-nondegenerate`, `-lift`, `-generic`; 21 red nodes, ending in the
  headline `cor:pencil-d-conditioned-pair`) opens at the PI's word (design doc §3).

## Decisions made during this phase

- **PI, 2026-11-04 (42k's open):** the PI answered "All 8 nodes as written (Recommended)", whose
  option read: "Close PD-REDUCTION. An Opus open commit, then a pre-build recon that spikes the
  cases against Phase 39's d = 3 Lean and the landed carrier, then roughly 4–8 builds (my
  estimate). PD-HEAD (21 nodes) would come next, at your word." The question as put, the other
  options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1): the theorem as put leaves
  out the chapter's infinite field, `d ≥ 3` and "with at least one body"; `Graph.pencil_reduction`
  takes `n` with `6 ≤ bodyBarDim n`, that is `n ≥ 3`, and the proof reads nothing `n` decides;
  "about 1,160 lines" is the two whole files, of which about 250 lines of `Arms.lean` serve only
  the generic conjunct, and it leaves out the nonsimple case and the two-pencil lemma.
- **Consistency read at the open:** all eight PASS, each read in full against the nodes it cites;
  no wording needs a repair. With every `\uses` parsed whole, the 23 outside dependencies (13
  definitions, 9 lemmas, 1 theorem; 41 with the `\cref`s) are green, proofs too, none superseded,
  and every `\cref` resolves. From `sec:pencil-d-induction` on, 62 nodes, 29 red (recounted).
- **The read's checks, re-derived:** two-pencil (2): `B = A^⊥` has dimension 2, holds `b_u, b_v`,
  and lies in `Π_u ∩ Π_v` as `(Π^⊥)^⊥ = Π`. Transport: `h x · g y = x · y` gives
  `h(Π^⊥) = (gΠ)^⊥` by dimension. Base: one edge, rank `D − 1`, deficiency 1; `m ≥ 2` edges,
  `D − (D − 1)m < 0`, rank `D`. Cut: `tgt(G) = tgt(G₁) + tgt(G₂) + (D − 1)c`. Nonsimple: the
  motions are `G/H`'s with `S(w) = S(u)`, codimension `D`, so rank `tgt(G)`.
