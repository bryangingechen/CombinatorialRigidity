# Phase 42k — PD-REDUCTION: Phase 39's reduction in every dimension (work log)

**Status:** in progress, opened 2026-11-04 at the PI's word ("All 8 nodes as written (Recommended)",
design doc §1), a sub-phase of Phase 42 that takes its layer PD-REDUCTION whole. Forward mode, the
Lean under `/coordinate-phase`: the eight red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-reduction`, three on linear algebra (`lem:pencil-d-two-pencil-extension`,
`lem:pencil-d-projective-transport`, `lem:pencil-d-cut-reposition`), four cases
(`lem:pencil-d-loop-case`, `lem:pencil-d-base-case`, `lem:pencil-d-cut-case`,
`lem:pencil-d-nonsimple-case`) and the theorem `thm:pencil-d-realization-theorem`, on the
`Pencil/Grade/` carrier, Phase 39's `Graph.pencil_reduction` and 42j's distinct statement. The
pre-build recon spiked all eight complete, with no `sorry`, and pinned three builds; build 1
(`Grade/TwoPencil.lean`) made the three linear-algebra nodes green, 3 of 8. Next: build 2,
`Grade/Arms.lean`, the loop, base and cut-edge cases (*Hand-off*).

## Current state

**Next: build 2, `Grade/Arms.lean`** (*Hand-off*). Green: 3 of the 8 nodes.
- **Build 1, landed:** `Pencil/Grade/TwoPencil.lean` (imports `Grade/Realization`):
  `lem:pencil-d-two-pencil-extension` (`perpExtensor`, `C_B`, and its three parts),
  `lem:pencil-d-projective-transport` and `lem:pencil-d-cut-reposition`, with their helpers and
  `exists_two_planes_of_mem`, transcribed from the recon's spike.

The pre-build recon (design pass, 2026-11-04) spiked the whole layer on the landed carrier, with no
`sorry`: `scratch/42k/Spike.lean` (gitignored, 1167 lines; `lake lean` clean with no warning, the
three standard axioms at the nine declarations checked, the `unusedArguments` and `docBlame` lints
clean). Its sections are the three builds, in order, each a mechanical transcription:
- the linear algebra (build 1, landed);
- the loop, base and cut-edge cases (build 2);
- the nonsimple case and the theorem (build 3).

Two `example`s at its end check, at `d = 4` over `ℚ`, that the adjacent-distinct form is
satisfiable on one body and on two bodies with one edge (by the base case). The chapter is the
lemma index (forward mode). The pinned signatures, the files and the build order are under
*Hand-off*; the recon's verdicts under *Decisions made*.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eight nodes as the chapter states them.
  Their close ends PD-REDUCTION; PD-HEAD (21 nodes) comes next, at the PI's word.
- **Encoding** as 42b–42j: grade `k = d − 1`, so the targets are `HasGradedPencilRealization K
  (m + 1) (m + 2)` and `HasGradedDistinctPencilRealization K (m + 1) (m + 2)` at `m = d − 2`, with
  `d ≥ 3` as `1 ≤ m` and the deficiency at `n = m + 2`, `bodyBarDim (m + 2) = screwDim (m + 1)`,
  the form of 42j's `Graph.hasGradedDistinctPencilRealization_of_twoEdgeConnected`. The linear
  algebra and the loop case are at every grade `k` (and the loop at every `n`).
- **What 42j hands on** (`notes/Phase42j.md` *Hand-off*): that distinct statement, at `1 ≤ m`, for
  the simple 2-edge-connected graphs on at least three bodies, the theorem's third case.
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof, in the same commit
  (R-9 to R-12 and R-14 to R-19 open; R-7, R-8 and R-13 aligned; R-18 and R-19 are 42k's recon's).

## Lemma checklist

- [x] **Pre-build recon** (design pass): all eight spiked complete; *Decisions made*.
- [x] `lem:pencil-d-two-pencil-extension`, parts (1) to (3), build 1, `Grade/TwoPencil.lean`.
- [x] `lem:pencil-d-projective-transport`, build 1, same file.
- [x] `lem:pencil-d-cut-reposition`, build 1, same file.
- [ ] `lem:pencil-d-loop-case`, build 2, `Grade/Arms.lean`.
- [ ] `lem:pencil-d-base-case`, both forms, build 2, same file.
- [ ] `lem:pencil-d-cut-case`, both forms, build 2, same file.
- [ ] `lem:pencil-d-nonsimple-case`, build 3, `Grade/Reduction.lean`.
- [ ] `thm:pencil-d-realization-theorem`, by `Graph.pencil_reduction`, build 3, same file.
- [ ] **Close** 42k, an intermediate sub-phase close that ends PD-REDUCTION (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None. The open's questions for the recon are settled (*Decisions made*, *The recon's verdicts*):
  no node's statement is false against the carrier, each node's Lean is at least as strong as its
  statement, and no choice waits on the PI. Two cases keep the `d = 3` Lean's rank counts where
  the chapter counts motions (`notes/Cleanup42.md` R-18, R-19, open for the cleanup).

## Hand-off / next phase

The next concrete commit is **build 2**: a new `Pencil/Grade/Arms.lean`, importing
`Grade/TwoPencil`, transcribed from `scratch/42k/Spike.lean`'s sections *Two planes through a
normal, and the loop case* (less `exists_two_planes_of_mem`, landed in build 1), *The base case*
and *The cut-edge case* (about 500 lines; splittable into the loop and base cases, then the cut),
with its line in `CombinatorialRigidity.lean` and the `\lean{}` and `\leanok` of three nodes, and
R-18's Lean as recorded. In `CombinatorialRigidity.Molecular`:
- `lem:pencil-d-loop-case` pins `hasGradedPencilRealization_of_isLoopAt {k n} (hloop : G.IsLoopAt
  e v) (hrec : HasGradedPencilRealization K k n (G ＼ {e})) : HasGradedPencilRealization K k n G`.
- At `[Finite α] [Finite β] {m}`, to `HasGraded(Distinct)PencilRealization K (m + 1) (m + 2) G`:
  `lem:pencil-d-base-case` pins `hasGradedPencilRealization_of_ncard_le_two (hloop : G.Loopless)
  (hne : V(G).Nonempty) (hV2 : V(G).ncard ≤ 2)` and `hasGradedDistinctPencilRealization_of_ncard_le_two
  (hS : G.Simple) (hne) (hV2)`; `lem:pencil-d-cut-case` pins `hasGradedPencilRealization_of_cutEdges
  (hssub : V₁ ⊂ V(G)) (hne : V₁.Nonempty) (hcut : (G.cutEdges V₁).ncard ≤ 1) (h₁ : … (G.induce V₁))
  (h₂ : … (G.induce (V(G) \ V₁)))` and its `Distinct` twin, both from the core
  `exists_hasPencilPlaneRealization_of_cutEdges` and the glue `exists_hasPencilPlaneRealization_glue`
  (at `k`, with `hk : 1 ≤ k`, `hn`).
- Helpers: `exists_plane_single_zero_one`, `finrank_span_rigidityRows_of_single_edge`,
  `exists_pair_of_ncard_le_two_of_edgeSet_nonempty`. The glue's plane dimension goal sits under
  `↥(if …)`, where `simp` cannot rewrite: `beta_reduce`, then `rw [ite_eq_left h]` (the spike's).

Then, a transcription of the spike's last two sections:
- **Build 3**, `Grade/Reduction.lean` (imports `Grade/Arms` and `Grade/Coverage`; about 310
  lines). `hasGradedPencilRealization_of_not_simple (G) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard)
  (hs : ¬ G.Simple) (hIH : ∀ G', V(G').Nonempty → V(G').ncard < V(G).ncard →
  HasGradedPencilRealization K (m + 1) (m + 2) G')`, with R-19's Lean as recorded, and
  `Graph.graded_pencil_realization_theorem [Infinite K] [Finite α] [Finite β] {m} (hm : 1 ≤ m) {G}
  (hne : V(G).Nonempty) : HasGradedPencilRealization K (m + 1) (m + 2) G ∧ (G.Simple →
  HasGradedDistinctPencilRealization K (m + 1) (m + 2) G)`. Then the close.
- **The standing rule**: builds 2 and 3 land R-18 and R-19's Lean as recorded; a build that aligns
  one sets its status.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` entries): no build edits a file
  that carries a home debt of 42b–42i (`notes/Phase42i.md` *Hand-off*), so none rides; 42j added
  none. Build 1 added three, each with the next commit that edits its file (FRICTION *42k's home
  debts*): `exists_smul_extensor_eq_of_mem_span_range_grade` to `Meet.lean` (with
  `contragredientEquiv`), `ExtensorInPanel.smul` to `RigidityMatrix/Basic.lean`, `dotPerp_map_eq`
  to `Grade/Realization.lean`; and a mirror candidate (`finrank_span_pair_eq_two`,
  `exists_mem_linearIndependent_pair`).
- **After 42k:** PD-HEAD (`-nondegenerate`, `-lift`, `-generic`; 21 red nodes, ending in the
  headline `cor:pencil-d-conditioned-pair`, which takes its first two claims from the theorem's two
  conjuncts) opens at the PI's word (design doc §3).

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

### The recon's verdicts (2026-11-04, design pass)

- **The `d = 3` Lean, file by file.** Transcribed to grade `k` with planes: from `Arms.lean` the
  loop case, the transport (roles exchanged: `g` on the normals and planes, its contragredient `h`
  on the hinges, with the new `dotPerp_map_eq`), the reposition (no contragredient) and the cut
  case's glue and core (lines 352–604 unused, as the open found); from `ArmsAssembly.lean` the bare
  base case; from `X0.lean` the nonsimple case (lines 68–335) and the three-way split
  (`pencilPair_of_X0`); from `Pair2.lean` the reduction's assembly. New: `C_B` and the two-pencil
  lemma (`Statement.lean`'s is at `Fin 4`, by cross-incidences) and the base case's
  adjacent-distinct form (at `d = 3` from the generic conjunct).
- **The two-pencil lemma** follows the chapter: `C_B` is literally the extensor of a basis of
  `B^⊥`; (2)'s multiple is that of two bases of one subspace, by a graded
  `exists_smul_extensor_eq_of_mem_span_range` (the top exterior power is a line), and (3) is (2)'s
  span argument. Of the landed tools, `span_range_eq_of_extensor_eq_grade` carries the span steps
  of (2) and (3); `exists_extensor_in_two_panels_grade` carries none of (1)–(3), as it controls no
  subspace, and is unused. The `d = 3` `hasPencilPanelRealization_mapExtensor_screwEquivOfLinearEquiv`
  is at grade 2 with points only; `BodyHingeFramework.screwEquivOfLinearEquiv`,
  `finrank_span_rigidityRows_mapExtensor` and `exists_contragredient_linearEquiv` are at every grade.
- **The routes** (the standing rule): two departures, both the `d = 3` Lean's rank counts where the
  chapter counts motions: the base case's one-edge rank and `m ≥ 2` deficiency
  (`notes/Cleanup42.md` R-18) and the nonsimple case's rank by the splice, with the other parallel
  edges keeping their hinges in `G/H` (R-19). Every other proof is the chapter's: the transport's
  "onto" by dimension, the base case's adjacent-distinct form (`b_u = e₀`, `b_v = e₁`, one
  three-dimensional `Π`, `B = span {e₀, e₁}`), the cut case's counts (`lem:block-rank-cut`,
  `lem:cut-edge-decomposition` (1), `lem:relative-deficiency-rank-bound`), the loop's zero rows.
- **The theorem's form:** `Graph.pencil_reduction` at `n = m + 2` (`hD` from
  `Graph.six_le_bodyBarDim`, `3 ≤ m + 2`), for `P G := HasGradedPencilRealization K (m + 1) (m + 2)
  G ∧ (G.Simple → HasGradedDistinctPencilRealization K (m + 1) (m + 2) G)`; `hcut`, `hcontract` and
  `hsplit` are one function (cut, distinct statement, nonsimple), as in `pencilPair_of_X0`.
  `cor:pencil-d-conditioned-pair` takes its first two claims as the two conjuncts.
- **Strength:** no pin is weaker than its node. The cases hold at every `m` (`d ≥ 2`), the linear
  algebra and the loop at every grade, without the nodes' unused nonzero or dimension hypotheses
  (part (3) takes `k ≥ 1`); only the theorem takes `1 ≤ m`, for `D ≥ 6` and the distinct statement.
