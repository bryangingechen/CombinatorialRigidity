# Phase 42g — PD-STEPS: cycles and long open ears in every dimension (work log)

**Status:** in progress, opened 2026-10-30 at the PI's word ("-long first (Recommended)", design
doc §1), a sub-phase of Phase 42 and the second of PD-STEPS. Forward mode, the Lean under
`/coordinate-phase`: the seven red nodes of `blueprint/src/chapter/pencil-d.tex` in
`sec:pencil-d-long` (Phase 40's cycle and long-ear steps in `Pᵈ`, on CERT's closed polygons with
independent joins), on the `Pencil/Grade/` carrier. The open's consistency read found every proof
routing through the argument its statement claims, and no `-long` node using a `-short` one
(*Consistency read at the open*). Next (*Hand-off*): the pre-build recon of the seven nodes.

## Current state

**Next: the pre-build recon** (*Hand-off*). Opened; no Lean yet. The seven targets, leaf-first:
`lem:pencil-d-polygon-normal`, `lem:pencil-d-polygon-insert` and `lem:pencil-d-polygon-collapse`
have every dependency green (`def:join`); `lem:pencil-d-polygon-star` rests on the first;
`lem:pencil-d-polygons` on the first two and the star; `thm:pencil-d-cycle` and
`thm:pencil-d-open-ear-long` on `lem:pencil-d-polygons` and `lem:pencil-d-polygon-collapse`, every
other dependency green (the long ear's restriction is 42f's `lem:pencil-d-lifting-restrict`). The
chapter is the lemma index (forward mode). `-short` (12 nodes) stays mapped by section in design
doc §3, with no letter minted.

## Architectural choices made up front

- **Scope** (the PI's, verbatim in design doc §1): the seven nodes above.
- **Encoding** as 42b–42f: `m = d − 2` heights at grade `k = m + 1`, `D = screwDim (m + 1)`
  (`= Graph.bodyBarDim (m + 2)`), `def_d` is `G.deficiency (m + 2)`. Attaining is
  `Graph.X0AttainsGrade K m`, its witness lemma `Graph.x0AttainsGrade_of_exists`. The point
  `pencilConfigPointGrade q z w` is `(x_w, y_w, z_w, 1)`, so a vector with last coordinate `1` is a
  configuration point (`gradeMk_eta`), and the chapter's `P_0`, `P_1`, `P_2` are the points with
  pictures `(0, 0)`, `(1, 0)`, `(0, 1)` and zero heights. As in 42e and 42f, the Lean may hold at
  every `m` while the nodes keep `d ≥ 3`.

## Consistency read at the open

The red-node consistency gate (`PHASE-BOUNDARIES.md`): each node read in full against the landed
carrier (`Pencil/Grade/`, 42b–42f), the `main-component.tex` node it generalizes and the CERT
workbook result it transcribes (`notes/attacks/cert/workbook.md`), with every Lean name below
opened at its declaration. **All seven PASS**; no proof fails against the carrier, no `\uses`
reaches a superseded node (`blueprint/lint.sh`, check 3), and every dependency outside the seven is
green. No wording needs a repair.
- **`lem:pencil-d-polygon-normal`** (S1, S2 (a)). (1): a nonzero join has independent ends, and
  `Y_{i+1}` in the span of `Y_{i−1}, Y_i` gives `J_i + αJ_{i−1} = 0`, nontrivial as `m ≥ 3`. (2):
  `g(x̄, ω) = (M(x̄ − ωȳ_i), ω)` needs `d ≥ 2`; `⋀²g` is invertible. The `d = 3` remark checks:
  `certPt` is `0` in the third coordinate at `Y_5, Y_0, Y_1`, where `Graph.X0Attains.of_openEar`
  puts `x_k`, `a`, `x_1`.
- **`lem:pencil-d-polygon-star`** (S4, without its choice of `u`). `dim W(Y) = m < D`. A vertex
  basis's joins are a basis of `⋀²` (the remark after `def:extensor`); else `W ⊆ ⋀²S`, and `Y_i ∨ u`,
  `u ∉ S`, is a basis join outside it. `Y_i ≠ 0` is part (1), its `\uses`. No last coordinate used.
- **`lem:pencil-d-polygon-insert`** (S5). `y(t) = (Y_i + tu)/(1 + tω)` has last coordinate `1`;
  for `t ≠ 0` and `c(t) ≠ 0` its joins are nonzero multiples of `F(t)`, and an `(m+1)`-minor
  `δ(t) = δ(0) + tδ₁` has at most one root: three exclusions, so `|K| ≥ 4`. At `i = m − 1` the
  index wraps (`Y_{i+1} = Y_0`). The `d = 3` remark holds: `lem:pencil-insertion` at `ρ = 0`
  (`exists_insertion_gain`, which is `⋀²K⁴`-only).
- **`lem:pencil-d-polygons`** (S6 (C1)). Base `(P_0, P_1, P_2)`: `P_0, …, P_d` is a basis, the
  triangle's joins three basis joins up to sign; step `m < D` by the star and the insertion; part
  (2) of the first lemma at `i = 0`. Evidence: S8, exact over ℚ at `d = 3..9`.
- **`lem:pencil-d-polygon-collapse`** (S7; the node's (1) is at `m ≥ D`, S7 (a) at `m > D`). The
  index arithmetic checks: `j + 1 ≤ D − 2 ≤ m − 2`, `c_{m−2}` at `Y_{D−2}`, distinct as
  `D − 3 < m − 2`; in (2) `x_1` at `Y_1`, `x_k` at `Y_{D−1}`, `b` at `Y_0`. The `d = 3` remarks
  match `Graph.X0Attains.of_cycle` and `Graph.X0Attains.of_openEar`.
- **`thm:pencil-d-cycle`** (`Graph.X0Attains.of_cycle`, `…of_cycle_of_certificate`; S6, S7 (a)).
  Heights free (`…exists_dotProduct_of_ncard_closedNbhd_le_three`); picture by
  `exists_mvPolynomial_linearIndependent_join_picture_grade` and
  `Graph.exists_mvPolynomial_isMainPicture`; hinges nonzero (`…supportExtensor_ne_zero_grade`);
  the count `(D−1)m − D + λ` by `BodyHingeFramework.finrank_span_rigidityRows_ear_eq` and the path
  lemmas (every `d`), the singleton partition, `Graph.x0AttainsGrade_of_exists`. `λ ≥ min(m, D)`
  needs the hinge form (*Blockers*).
- **`thm:pencil-d-open-ear-long`** (`Graph.X0Attains.of_openEar` through `…of_openEar_of_cert`;
  S6, S7 (b), S3's consumer reading). `z*` vanishes on `V_1 ∪ {x_1, x_k}`, so lies in `L_G(q)` at
  every admissible `q` (`Graph.mem_liftingSpace_of_ear`, which also asks zero off `V(G)`); the lift
  per height (`Graph.earExtend_mem_liftingSpace`, `Graph.exists_liftingRestrict_preimage_fst_eq`);
  `MvPolynomial.exists_mem_eval_ne_zero₂`; part (2) of the restriction takes two `ends`, covering
  the `d = 3` proof's `lem:pencil-rank-congr`; the count by `Graph.deficiency_induce_add_le_of_ear`.
- **The two sections share no node** (the coordinator's hypothesis, checked): no `-long` `\uses`
  list, parsed across line breaks, and no `\cref` names a `-short` node, nor the reverse. The four
  `\cref{sec:pencil-d-short}` point at `-short`'s opening prose for notation (motions in
  `⋀²K^{d+1}`, `ρ`, `Λ`, the ear rank formula read with joins). That prose is no node: it derives
  the formula from `lem:block-rank-ear` and `def:panel-support-extensor`, which both theorems
  `\uses`. Its Lean is the hinge form, which neither section owns as a node.

## Lemma checklist

- [ ] **Pre-build recon**: exact Lean signatures for the seven nodes, their files, and spikes of
  the polygon carrier, the insertion and the hinge form (*Blockers*).
- [ ] `lem:pencil-d-polygon-normal`, a leaf.
- [ ] `lem:pencil-d-polygon-insert`, a leaf.
- [ ] `lem:pencil-d-polygon-collapse`, a leaf.
- [ ] `lem:pencil-d-polygon-star`, on the first.
- [ ] `lem:pencil-d-polygons`, on the first two and the star.
- [ ] `thm:pencil-d-cycle`, on the polygons and the collapse, with the hinge form.
- [ ] `thm:pencil-d-open-ear-long`, on the same and `lem:pencil-d-lifting-restrict`.
- [ ] **Close** 42g, an intermediate sub-phase close (`PHASE-BOUNDARIES.md`).

## Blockers / open questions

- None blocking. For the recon:
  - The polygon carrier: a closed `m`-gon as `Fin m → Fin (m' + 3) → K` with cyclic successor, its
    joins as `normalsJoin` (the type of `exists_mvPolynomial_linearIndependent_join_*_grade`) or as
    `def:join`'s `join` (`normalsJoin_coe` bridges), "independent joins" as `LinearIndependent`.
  - The basis of `⋀²K^{d+1}` from a basis of `K^{d+1}` (the star, the polygons' base case):
    mathlib's `Module.Basis.exteriorPower`, as `normalsJoin_basis_repr` uses at the standard basis.
  - The insertion's one-parameter step (minor of `F(t)` or a polynomial route), and whether the node's
    `|K| ≥ 4` is kept (a weaker `[Infinite K]` pin would be a changed statement). Whether a
    `d`-general `exists_insertion_gain` also serves `-short`'s `lem:pencil-d-insertion`, its twin.
  - The hinge form (design doc §3, PD-STATE's deferral, its consumer rows 10–11): a grade
    `card_le_finrank_of_linearIndependent_pointJoin`, since `panelSupportExtensor` is
    `complementIso ∘ normalsJoin` at every `k`; a new `Grade/` lemma, no `P³` file edited.
  - The placement as `(q₀, z)` with `z` zero off `V(G)` (`Graph.liftingSpace` asks it), and the
    files (new `Grade/` files importing `MainComponent.Chain`, `Grade.Cut`, `Grade.JoinIndependence`).
  - The deferrals of 42b, 42c, 42e and 42f (design doc §3) ride with a build that edits a file they
    name.

## Hand-off / next phase

The next concrete commit is the **pre-build recon** (a `recon-opus` dispatch, read-only or a
design-pass commit at the coordinator's choice): pin the exact Lean signatures of the seven nodes
against the landed `Pencil/Grade/` API and Phase 40's `MainComponent/Chain.lean`, `Ear.lean` and
`Lines.lean`; spike the polygon carrier, the insertion and the hinge form under `lake lean`; settle
the questions under *Blockers*; and record the signatures here. Then build leaf-first, about 4–7
commits by the coordinator's estimate in the option the PI chose: the polygon lemmas (one or two
commits), the cycle, the long ear. Each build adds its node's `\lean{}` and `\leanok`.

## Decisions made during this phase

- **The open** (the PI, 2026-10-30; verbatim in design doc §1): 42g opens as PD-STEPS's `-long`,
  seven nodes; `-short` stays mapped by section, no letter minted.
- **The open's consistency read:** all seven proofs route through the argument their statements
  claim, on the `Grade/` carrier; the sections share no node, the coordinator's hypothesis now
  checked; no chapter edit.
