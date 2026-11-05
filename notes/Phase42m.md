# Phase 42m — PD-HEAD: the generic conjunct and the headline in every dimension (work log)

**Status:** in progress, opened 2026-11-05 at the PI's word ("All 11 as written", design doc §1),
the second and last sub-phase of Phase 42's last layer, PD-HEAD. Forward mode, the Lean under
`/coordinate-phase`: the eleven red nodes of `blueprint/src/chapter/pencil-d.tex`'s
`sec:pencil-d-generic`, as the chapter states them. Six are the cases of an induction on the bodies
(few bodies, a cut edge, a body of degree one, a pendant triangle, no planar-rigid set, a body of
degree two with hub neighbours), three find that body and supply its condition, and the last two
are the generic theorem `thm:pencil-d-generic` and the headline `cor:pencil-d-conditioned-pair`.
They are the blueprint's last red nodes, so 42m's close is Phase 42's, where Tier 0's
`main_results` row is decided. The open's consistency read passed all eleven (*Decisions made*);
its questions for the recon are under *Blockers*. Next (*Hand-off*): the pre-build recon of the
eleven nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The eleven targets, leaf-first,
with the 42l nodes each uses and its `d = 3` Lean (namespace `CombinatorialRigidity.Molecular`,
files under `Pencil/`):
- *Leaves.* `lem:pencil-d-lift-small` on lift-attains and lift-realization (`Pair.lean`'s
  `hasGenericPencilRealization_of_ncard_le_two` and `_of_cutEdges_eq_empty`;
  `MainComponent/GenericTriangle.lean`'s `pencilPair_of_simple_ncard_eq_three`);
  `lem:pencil-d-lift-cut-edge` on lift-attains, transfer, one-witness and lift-realization
  (`Pair.lean`'s `hasGenericPencilRealization_of_isNondegPencilRealization_induce_union_singleton`);
  `lem:pencil-d-lift-pendant` on lift-attains, three, transfer and one-witness (`Pair2.lean`'s
  `hasGenericPencilRealization_pendant_of_IH`); `lem:pencil-d-lift-no-rigid` on lift-attains,
  three, lift-realization and one-witness (`MainComponent/GenericBase.lean`'s
  `Graph.IsX0Graph.hasGenericPencilRealization_of_forall_deficiency_two_ne_zero`);
  `lem:pencil-d-good-ear` on no 42l node (`MainComponent/GoodEar.lean`'s
  `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle`); `lem:pencil-d-lift-ear` on lift-attains,
  three, transfer and one-witness (`MainComponent/GenericEar.lean`'s
  `Graph.IsOpenEar.hasGenericPencilRealization_of_one`).
- *On those.* `lem:pencil-d-lift-pendant-triangle` on lift-small, with lift-attains, three,
  transfer and one-witness (`GenericTriangle.lean`'s `hasGenericPencilRealization_of_closedEar_two`);
  `lem:pencil-d-ear-extend` on good-ear and the steer lemma, and `lem:pencil-d-ear-free` on
  ear-extend, good-ear, the lift, the steer lemma and one-witness (no `d = 3` Lean: at `d = 3` no
  lift is needed).
- *The theorem and the headline.* `thm:pencil-d-generic` on the eight lemmas other than ear-extend,
  with feasibility, three, lift-attains and the coverage (`MainComponent/Statements.lean`'s
  `hasGenericPencilRealization_of_IH`, with `Pair2.lean`'s `pencilPair_of_not_twoEdgeConnected`
  at a cut edge); `cor:pencil-d-conditioned-pair` on it and 42k's
  `thm:pencil-d-realization-theorem` (`Graph.graded_pencil_realization_theorem`; at `d = 3`,
  `Statements.lean`'s `pencilPair_of_nonempty`).

Every `\uses` dependency outside the eleven is green: 46 nodes, 53 with the `\cref`s, nine of
them 42l's (all but `lem:pencil-d-nondegenerate-maps`). No node outside the eleven uses one of
them. The chapter is the lemma index (forward mode).

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the eleven nodes of `-generic` as the chapter
  states them. Its close is Phase 42's full close (`PHASE-BOUNDARIES.md` *When this commit closes a
  phase*), where Tier 0's `main_results` row and the headline's are decided (design doc §3).
- **Encoding** as 42b–42l: grade `k = d − 1`, Lean's `m = d − 2`; a lift's `r = d − 3` new
  coordinates (42l's `LiftAttains K r G`), inserted before the last coordinate.
- **What 42l and 42k hand on**: the ten nodes' Lean in `Grade/Nondegenerate.lean`,
  `Grade/Feasible.lean`, `Grade/Lift.lean` and `Grade/LiftWitness.lean` (`notes/Phase42l.md`
  *Current state*), and `Graph.graded_pencil_realization_theorem`, the headline's first two
  conjuncts (`Grade/Reduction.lean`).
- **The standing rule** (design doc §3): the recon and every build add a row to
  `notes/Cleanup42.md` §2 where their Lean departs from the chapter's proof, in the same commit.
  Open: R-3 to R-5, R-9 to R-12, R-14 to R-21, R-23; aligned: R-1, R-2, R-7, R-8, R-13, R-22; R-6
  no departure.

## Lemma checklist

- [ ] **Pre-build recon**: the eleven spiked against Phase 39's `d = 3` Lean and 42l's Lean,
  exact Lean signatures, their files, and the questions under *Blockers*.
- [ ] `lem:pencil-d-lift-small`, parts (1) and (2).
- [ ] `lem:pencil-d-lift-cut-edge`.
- [ ] `lem:pencil-d-lift-pendant`.
- [ ] `lem:pencil-d-lift-pendant-triangle`.
- [ ] `lem:pencil-d-lift-no-rigid`.
- [ ] `lem:pencil-d-good-ear`, both outcomes, parts (i) to (v).
- [ ] `lem:pencil-d-lift-ear`.
- [ ] `lem:pencil-d-ear-extend`.
- [ ] `lem:pencil-d-ear-free`.
- [ ] `thm:pencil-d-generic`, with the remark after `def:pencil-d-lift-attains` (an attaining
  general lift gives a generic realization), which has no node and lands here (42l's hand-off):
  `IsNondegPencilPlaneRealization.lift` with `PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge`
  at a realization with `Q ≠ 0`.
- [ ] `cor:pencil-d-conditioned-pair`.
- [ ] **Close** 42m and Phase 42 together, the full close (`PHASE-BOUNDARIES.md`): the ROADMAP row
  to ✓ and §42 compressed; the user-facing surfaces re-summarized; `formalization.yaml`'s
  `main_results` and `alignment` (Tier 0 unless the headline subsumes it, design doc §3), each new
  row with a closed non-vacuity witness in `CombinatorialRigidity/Nonvacuity.lean`, and the
  headline-axioms check; the chapter's end-to-end re-read and `notes/BlueprintExposition.md`; the
  dispatch-log grooming; the design doc's compression; the project-organization review; and
  `.claude/autopilot/queue.toml`'s PENCIL-D row `done = true`.

## Blockers / open questions

- None blocking the recon. Its questions, from the open's read:
  - **The `d = 3` Lean, file by file.** `Pair.lean` (967 lines) and `Pair2.lean` (622) carry three
    cases (lift-small on at most two bodies and with no crossing edge, lift-cut-edge, lift-pendant)
    and the cut-edge part of the assembly. The rest is in `Pencil/MainComponent/`:
    `GenericTriangle.lean` (1009: the triangle and the pendant triangle), `GenericBase.lean` (948:
    no planar-rigid set), `GoodEar.lean` (441), `GenericEar.lean` (593: the one-body ear) and
    `Statements.lean` (183: the generic step's case split and the conditioned pair). The (T1)
    realizations of the pendant, pendant-triangle and ear cases come from
    `lem:pencil-generic-steer`(a) read through `-three` (`exists_isNondegPencilRealization_restrict_of_demoted`,
    `MainComponent/GenericSteer.lean`). No `d = 3` Lean: ear-extend, ear-free and every lift step.
  - **The induction's form.** `thm:pencil-d-generic` is a strong induction of its own on the
    bodies, proving `LiftAttains K r G` at every simple nondegeneracy-feasible `G` with a body, then
    the remark above (checklist); feasibility moves between dimensions by
    `gradedPencilNondegFeasible_iff`. The `d = 3` case split runs inside `pencilPair_of_arms`
    instead. The smaller graphs as `G.induce V'`, the form `lift_transfer` takes.
  - **(T1) and (T2) per case**, as `lift_transfer`'s `hT1` (a polynomial `E` at `bnPoint b n`) and
    `hT2` (a `HoldsGenerally` statement for `G`'s selectors). The cut-edge case glues the sides by
    a linear map `g` with `g b′_u = b_u`, `g b′_v = b_v` and its inverse transpose, where the `d = 3`
    Lean moves the second side by a map avoiding finitely many subspaces: what transcribes, and
    what is new.
  - **The good ear.** Its `d = 3` Lean returns the body `x` alone with
    `def₃(G − x) ≤ def₃(G)` (with `Graph.exists_eq_triple_of_minimal` and
    `Graph.exists_closedEar_two_of_triangle`); parts (i), (iii) and (v) are read off its proof, and
    (iv) holds at every `D`. Re-open that proof to return `W₀`, or prove the parts beside it?
  - **The ear's condition.** `lem:pencil-d-lift-ear`'s hypothesis and `lem:pencil-d-ear-free`'s
    conclusion as one predicate; 42l's `HoldsGenerally` depends on the selectors, so the same
    selectors on both sides or a form free of them. `-ear-extend`'s `Γ_L` keeps the members-first
    form, and its proof reads the steer lemma's places left empty (R-22): match `Γ_L`'s product to
    a selector (42l's hand-off).
  - **Shared steps.** `-ear-free` re-runs two steps "as in the proof of"
    `lem:pencil-d-lift-no-rigid` (some `z ∈ L(q)` with the planes pairwise distinct;
    `L(b⁰) = L(q)` at a configuration), with no `\uses` edge, as it uses that proof and not the
    statement: one lemma each for both nodes? And `-no-rigid` uses that `dim L̃` takes its least
    value at a general nondegenerate realization, a step of `lem:pencil-d-lift-one-witness`'s proof,
    not its statement (`liftAttains_of_least` takes the least value as a hypothesis): exposed in
    `Grade/LiftWitness.lean`, or re-derived?
  - **The headline's form.** A dimension-`d` `PencilPair`, or a theorem with three conclusions,
    the first two `Graph.graded_pencil_realization_theorem`; its `formalization.yaml` row and
    non-vacuity witness are the close's.
  - **A dependency edge, for the build that lands the node:** `-lift-cut-edge`'s rank step
    `\cref`s `lem:pencil-x0-fibre-intersection` (a general `r⁰` and a general `λ`), which its
    proof does not `\uses`; that build adds the edge with its `\leanok`.
  - **Steps the read found implicit** (none a repair): at the triangle (`-lift-small` (1)) the
    normals of a lift are independent because their images in dimension three are, dropping the
    inserted coordinates; `-lift-cut-edge`'s `def_d(G_i) = def_d(G[V_i]) + 1` is part (1) of
    `lem:cut-edge-decomposition` in `G_i` at `V′ = V_i`, a single body having deficiency zero.
  - **Files.** New `Grade/` file(s), at the recon's choice. A deferral naming a file a build edits
    rides with it (*Hand-off*).

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice), the same shape as 42l's (`694c9f5a`). It spikes
all eleven against Phase 39's `d = 3` Lean (*Blockers*) and 42l's Lean (`Grade/Nondegenerate.lean`,
`Feasible.lean`, `Lift.lean`, `LiftWitness.lean`), with 42k's `Grade/Reduction.lean` for the
headline, pins the eleven Lean signatures and the file plan, each spiked under `lake lean`, settles
*Blockers*, and records the signatures here. Then build leaf-first, roughly 4–7 commits by the
coordinator's estimate in the option the PI chose, and the close of 42m and Phase 42 together. Each
build adds its node's `\lean{}` and `\leanok`.
- **From 42l's hand-off:** the remark after `def:pencil-d-lift-attains` lands with
  `thm:pencil-d-generic` (checklist); R-22's places for `lem:pencil-d-ear-extend` (*Blockers*, the
  ear's condition).
- **The standing rule** (*Architectural choices*): a row in `notes/Cleanup42.md` §2 per departure.
- **Deferred, where it lands** (design doc §3; FRICTION's `[open]` 42k and 42l entries): the six
  `dotPerp` lemmas of `Grade/Feasible.lean` (`dotPerp_sup`, `dotPerp_inf`, `dotPerp_antitone`,
  `dotPerp_top`, `finrank_dotPerp_add`, `finrank_dotPerp_span_singleton_of_ne_zero`) move to
  `Grade/Realization.lean` beside `finrank_dotPerp`, with 42k's `dotPerp_map_eq`, riding the next
  commit that edits `Grade/Realization.lean`; the home debts of 42b–42k ride with the next commit
  that edits their files (`notes/Phase42k.md` *Hand-off*); at a cleanup round, the mirror candidate
  `finrank_map_of_injOn`.
- **After 42m:** Phase 42 is closed; CLEANUP-42 (`notes/Cleanup42.md`) and then ORIGAMI follow,
  each opening with the PI (ROADMAP *Queued post-program phases*).

## Decisions made during this phase

- **PI, 2026-11-05 (42m's open):** the PI answered "All 11 as written (Recommended)", whose option
  read: "An Opus open commit, then a pre-build recon that spikes all 11 against Phase 39's d = 3
  Lean and 42l's Lean. Then roughly 4–7 builds (my estimate) and the close of 42m and Phase 42
  together." The question as put, the other options and a note on them: design doc §1.
- **The open's question, checked** (not the PI's text; design doc §1): "roughly 4–7 builds" is the
  coordinator's estimate. The counts hold (eleven nodes; nine lemmas, six cases and three helpers;
  the theorem and the headline), the cases' short names with qualifiers; "10 of the 11 use 42l's
  Lean" holds, all but `lem:pencil-d-good-ear`; the line counts of `Pair.lean` and `Pair2.lean`
  hold, re-counted, but the two files are the `d = 3` Lean of three cases, not of all eleven.
- **Consistency read at the open:** all eleven PASS, each read in full against the nodes it cites;
  no wording needs a repair. With every `\uses` parsed whole, the 46 outside dependencies (13
  definitions, 29 lemmas, 4 theorems; 53 with the `\cref`s) are green, proofs too, none superseded.
  From `sec:pencil-d-induction` on, 62 nodes, 11 red, all in `-generic`, and these are the
  blueprint's only red nodes (recounted).
- **The read's checks, re-derived:** small, the targets on two bodies and the triangle
  (`2D − 3(D − 1) < 0`); cut edge, every nonzero `t ∈ {b_u, b_v}^⊥` is `h n′_v`, the obstruction at
  `|S| = 3` is `b_v · n_{w₁} = 0`, and `tgt(G₁) + tgt(G₂) − (D − 1) = tgt(G)`; pendant, `+ D − 1`;
  pendant triangle, `+ 2D`; ear, `rank ≥ rank H + D` at one interior body; ear-extend, both
  exceptional cases force `b_{v₂} · m_v = 0`, against (b); the theorem's case split is exhaustive.
