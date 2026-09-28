/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Carrier

/-!
# The configuration as a pencil framework, and the linear pencil condition (Phase 40b CARRIER)

The picture-to-normal API, the configuration as a pencil framework, the scale-and-affine-shift rank
invariance, and the linear pencil condition, over the definitions of
`Molecular/Molecule/Pencil/MainComponent/Carrier.lean`
(`blueprint/src/chapter/main-component.tex`, `sec:main-component-carrier`; Phase 40b CARRIER slices
C3, C3 item 5, C4, and C5′, `notes/Phase40b.md`). Split out of `Carrier.lean` at the Phase 40h
`Carrier.lean` split (`notes/Phase40h.md`, PI decision 5, 2026-09-27): no declaration here is
renamed or re-stated, so no blueprint `\lean{...}` pin moved.

## Main definitions

* `pointJoinFramework` — the body-hinge framework whose hinge at each label is the join
  `p_u ∧ p_v` of its two ends' points.
* `pencilConfigFramework` — the point-join framework of a configuration, patched off `E(G)` by a
  fixed nonzero hinge: the framework of the pencil realization a configuration gives.
* `pencilConfigPointPoly` / `pencilNormalOfPicturePoly` — the polynomial mirrors of the
  configuration point and the plane normal, in the height variables at a fixed picture.

## Main statements

* `pencilNormalOfPicture_ne_zero_iff` — the normal is nonzero iff the selected configuration
  triple is independent.
* `linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint` — picture
  independence gives configuration independence, at every height.
* `dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd` — over `z ∈ L(q)`, the plane of a
  valid selector at `v` is orthogonal to the whole closed neighbourhood of `v`, not only the three
  selected bodies (CARRIER's C3, new; consumed by C4).
* `exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd` — two selectors at the same body give
  proportional normals.
* `pencilNormalOfPicturePoly` / `eval_pencilNormalOfPicturePoly` — the polynomial mirror of the
  normal in the height variables, at a fixed picture (`X0Gen`'s fibre-intersection shape).
* `ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework` — `ofNormals` at the points is the
  polarity image of the point-join framework; `finrank_span_rigidityRows_pencilConfigFramework`
  carries the rank to the patched configuration framework.
* `Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework` — over an admissible
  picture and a height in `L(q)`, the configuration is a pencil panel realization.
* `Graph.IsAdmissiblePicture.hasDistinctPencilRealization` — an attaining configuration over an
  admissible picture gives `HasDistinctPencilRealization K 3 G`;
  `Graph.X0Attains.hasDistinctPencilRealization` is the resulting `X0Dist` leg, over an infinite
  field.
* `Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` — the rank is unchanged by
  `z ↦ t • z + a` for `t ≠ 0` and `a ∈ Aff(q)` (the last clause of (MC-3)).
* `Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar` — over an admissible picture, coplanar
  closed neighbourhoods force `z ∈ L(q)` (`lem:pencil-condition-linear`'s converse, CARRIER's C5′).
* `Graph.IsAdmissiblePicture.exists_smul_eq_interpolant` — every nonzero normal of a closed
  neighbourhood is a nonzero scalar multiple of the interpolant `(h₀, h₁, -1, h₂)`
  (`lem:pencil-condition-linear`'s unique non-vertical plane, CARRIER's C5′).

## Design

* **The rank is taken at `ofNormals` of the configuration points, not of the plane normals.**
  `X0Attains` reads `PanelHingeFramework.ofNormals G ends (p_·)`: each body's *point* `p_v` is the
  normal of the polar plane `p_v^⊥`, and the hinge `panelSupportExtensor p_u p_v` is the polar of
  the pencil line `p_u ∧ p_v`, so its row rank is the rank of the point-join framework the pencil
  motives carry (the complement isomorphism is an invertible map of the screw space;
  `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`; the conversion is
  `finrank_span_rigidityRows_pencilConfigFramework`, CARRIER's C4). It is
  nonzero at every link as soon as the picture points differ. `ofNormals` at the *plane normals*
  would be the wrong rank: adjacent planes coincide on the whole fibre whenever the two bodies lie
  in a common planar-rigid subgraph ((MC-13)(c), e.g. every triangle edge at a generic picture,
  and every edge at a flat configuration), `panelSupportExtensor n n = 0` there, and a zero hinge
  welds its bodies (its hinge-row block is every functional).

See `notes/Phase40b.md` (*Decisions made*, 2026-09-26 C1a) and `notes/Phase40-design.md` §3.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The picture-to-normal API (Phase 40b CARRIER slice C3) -/

/-- **The normal is nonzero iff the selected configuration triple is independent** (Phase 40b
CARRIER slice C3, item 1). Direct unfold of `pencilNormalOfPicture` as `cross₃` of the three
selected configuration points, plus `cross₃_ne_zero_iff_linearIndependent`. -/
theorem pencilNormalOfPicture_ne_zero_iff (q : α × Fin 2 → K) (z : α → K) (sel : α → Fin 3 → α)
    (v : α) :
    pencilNormalOfPicture q z sel v ≠ 0 ↔
      LinearIndependent K (fun i => pencilConfigPoint q z (sel v i)) := by
  have heq : (fun i => pencilConfigPoint q z (sel v i)) =
      ![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
        pencilConfigPoint q z (sel v 2)] := by
    funext i; fin_cases i <;> rfl
  rw [heq]
  exact cross₃_ne_zero_iff_linearIndependent _ _ _

/-- **Picture independence gives configuration independence, at every height** (Phase 40b CARRIER
slice C3, item 2). The linear map `f : K⁴ →ₗ K³` dropping the height coordinate (projecting onto
coordinates `0, 1, 3`) sends every configuration point `pencilConfigPoint q z w` to the picture
point `pencilPicturePoint q w`, so an independent family of picture points forces the corresponding
family of configuration points independent (`LinearIndependent.of_comp`, which needs no
injectivity of `f`: a dependency relation among the domain vectors pushes forward to one among
their images, so independent images force independent domain vectors). -/
theorem linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint
    {q : α × Fin 2 → K} (z : α → K) {ι : Type*} {t : ι → α}
    (ht : LinearIndependent K (fun i => pencilPicturePoint q (t i))) :
    LinearIndependent K (fun i => pencilConfigPoint q z (t i)) := by
  set f : (Fin 4 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := fun a => ![a 0, a 1, a 3]
      map_add' := fun a b => by funext i; fin_cases i <;> rfl
      map_smul' := fun c a => by funext i; fin_cases i <;> rfl } with hfdef
  refine LinearIndependent.of_comp f ?_
  have heq : f ∘ (fun i => pencilConfigPoint q z (t i)) = fun i => pencilPicturePoint q (t i) := by
    funext i
    change f (pencilConfigPoint q z (t i)) = pencilPicturePoint q (t i)
    funext j
    fin_cases j <;> rfl
  rwa [heq]

/-- **The plane of a valid selector at `v` contains the whole closed neighbourhood** (Phase 40b
CARRIER slice C3, item 3; new, consumed by C4). Over a height `z ∈ L(q)`, at a body `v ∈ V(G)`
with a selector `sel v` valued in `G.closedNbhd v`, the normal `N = pencilNormalOfPicture q z sel
v` annihilates every configuration point of the closed neighbourhood, not just the three selected
ones. Route: `dotProduct_cross₃` reduces `N ⬝ᵥ p_w` to `det[p_{sel v 0}, p_{sel v 1}, p_{sel v 2},
p_w]`. Membership in `L(q)` gives, at `v`, coefficients `h : Fin 3 → K` with every point over
`G.closedNbhd v` an image of its picture point under the linear map `a ↦ (a 0, a 1, h ⬝ᵥ a, a 2)`
— so all four rows are images, under one linear map, of four vectors in the `3`-dimensional `K³`,
always dependent (`LinearIndependent.fintype_card_le_finrank`), and dependency of the domain
vectors pushes forward through any linear map to the images, so the four rows are dependent too
and the determinant vanishes (`linearIndependent_rows_iff_det_ne_zero`).

No independence hypothesis on the selected triple is needed: a dependent triple has `cross₃ = 0`,
and the conclusion then holds trivially. -/
theorem dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) {v : α} (hv : v ∈ V(G))
    {sel : α → Fin 3 → α} (hsel : ∀ i, sel v i ∈ G.closedNbhd v)
    {w : α} (hw : w ∈ G.closedNbhd v) :
    pencilNormalOfPicture q z sel v ⬝ᵥ pencilConfigPoint q z w = 0 := by
  classical
  obtain ⟨h, hh⟩ := (Graph.mem_liftingSpace.mp hz).2 v hv
  set L : (Fin 3 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun a => ![a 0, a 1, h ⬝ᵥ a, a 2]
      map_add' := fun a b => by funext i; fin_cases i <;> simp [dotProduct_add]
      map_smul' := fun c a => by funext i; fin_cases i <;> simp [dotProduct_smul] } with hLdef
  have hLapply : ∀ a, L a = ![a 0, a 1, h ⬝ᵥ a, a 2] := fun _ => rfl
  have hLp : ∀ x ∈ G.closedNbhd v, pencilConfigPoint q z x = L (pencilPicturePoint q x) := by
    intro x hx
    rw [hLapply]
    funext i
    fin_cases i <;> simp [pencilConfigPoint, pencilPicturePoint, hh x hx]
  have hdep : ¬ LinearIndependent K
      ![pencilPicturePoint q (sel v 0), pencilPicturePoint q (sel v 1),
        pencilPicturePoint q (sel v 2), pencilPicturePoint q w] := by
    intro hli
    have hc := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun] at hc
    simp at hc
  have hnotLI : ¬ LinearIndependent K
      ![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
        pencilConfigPoint q z (sel v 2), pencilConfigPoint q z w] := by
    intro hLI4
    apply hdep
    have heq : (![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
          pencilConfigPoint q z (sel v 2), pencilConfigPoint q z w] : Fin 4 → Fin 4 → K) =
        L ∘ ![pencilPicturePoint q (sel v 0), pencilPicturePoint q (sel v 1),
          pencilPicturePoint q (sel v 2), pencilPicturePoint q w] := by
      funext i
      fin_cases i
      · exact hLp _ (hsel 0)
      · exact hLp _ (hsel 1)
      · exact hLp _ (hsel 2)
      · exact hLp _ hw
    rw [heq] at hLI4
    exact hLI4.of_comp L
  have hdetzero : Matrix.det (Matrix.of ![pencilConfigPoint q z (sel v 0),
      pencilConfigPoint q z (sel v 1), pencilConfigPoint q z (sel v 2),
      pencilConfigPoint q z w]) = 0 := by
    by_contra hne
    exact hnotLI (Matrix.linearIndependent_rows_iff_det_ne_zero (K := K)
      (A := Matrix.of ![pencilConfigPoint q z (sel v 0), pencilConfigPoint q z (sel v 1),
        pencilConfigPoint q z (sel v 2), pencilConfigPoint q z w]) |>.mpr hne)
  change cross₃ (pencilConfigPoint q z (sel v 0)) (pencilConfigPoint q z (sel v 1))
      (pencilConfigPoint q z (sel v 2)) ⬝ᵥ pencilConfigPoint q z w = 0
  rw [dotProduct_cross₃]
  exact hdetzero

/-- **Selector independence up to a scalar** (Phase 40b CARRIER slice C3, item 4). Under item 3's
hypotheses for two selectors `sel, sel'` at the same `v`, each selecting a triple with independent
picture points, the normals differ by a nonzero scalar.
Both normals are nonzero (items 1/2); item 3 puts `N = pencilNormalOfPicture q z sel v` in the perp
of the three (independent, by item 2) configuration points at `sel'`, and `N' =
pencilNormalOfPicture q z sel' v` lies there too (`cross₃`'s own orthogonality to its defining
triple, `cross₃_dotProduct_apply_self`) — a `1`-dimensional perp (`finrank_toDualPerp_triple_eq`),
so it is spanned by the nonzero `N'` (`Submodule.eq_of_le_of_finrank_eq`), and `N` is a scalar
multiple. -/
theorem exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) {v : α} (hv : v ∈ V(G))
    {sel sel' : α → Fin 3 → α}
    (hsel : ∀ i, sel v i ∈ G.closedNbhd v) (hsel' : ∀ i, sel' v i ∈ G.closedNbhd v)
    (hLI : LinearIndependent K (fun i => pencilPicturePoint q (sel v i)))
    (hLI' : LinearIndependent K (fun i => pencilPicturePoint q (sel' v i))) :
    ∃ c : K, c ≠ 0 ∧
      pencilNormalOfPicture q z sel v = c • pencilNormalOfPicture q z sel' v := by
  set N := pencilNormalOfPicture q z sel v with hNdef
  set N' := pencilNormalOfPicture q z sel' v with hN'def
  have hN : N ≠ 0 :=
    (pencilNormalOfPicture_ne_zero_iff q z sel v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hLI)
  have hN' : N' ≠ 0 :=
    (pencilNormalOfPicture_ne_zero_iff q z sel' v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hLI')
  have hLI'config : LinearIndependent K (fun i => pencilConfigPoint q z (sel' v i)) :=
    linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hLI'
  set W : Submodule K (Fin 4 → K) := ⨅ j : Fin 3, LinearMap.ker
      ((Pi.basisFun K (Fin 4)).toDual.flip ((fun i => pencilConfigPoint q z (sel' v i)) j))
    with hWdef
  have hWdim : Module.finrank K W = 1 := finrank_toDualPerp_triple_eq hLI'config
  have hmemW : ∀ x : Fin 4 → K, x ∈ W ↔ ∀ j, x ⬝ᵥ pencilConfigPoint q z (sel' v j) = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
  have hNmem : N ∈ W := by
    rw [hmemW]
    intro j
    exact dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd hz hv hsel (hsel' j)
  have hN'mem : N' ∈ W := by
    rw [hmemW]
    intro j
    exact cross₃_dotProduct_apply_self (fun i => pencilConfigPoint q z (sel' v i)) j
  have hspan : Submodule.span K ({N'} : Set (Fin 4 → K)) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; simpa using hN'mem
    · rw [hWdim, finrank_span_singleton hN']
  rw [← hspan] at hNmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hNmem
  refine ⟨c, ?_, hc.symm⟩
  intro hc0
  exact hN (by rw [← hc, hc0, zero_smul])

/-! ## The polynomial mirror of the picture-to-normal map (Phase 40b CARRIER slice C3, item 5) -/

/-- **The homogeneous configuration point as polynomials in the height variables, at a fixed
picture** (Phase 40b CARRIER slice C3, item 5): the vector `(C q_{w,0}, C q_{w,1}, X_w, 1)`, the
picture coordinates baked in as constants and the height `z_w` a variable indexed by `α` — the
shape `X0Gen`'s fibre-intersection needs, at a fixed picture `q`. -/
noncomputable def pencilConfigPointPoly (q : α × Fin 2 → K) (w : α) : Fin 4 → MvPolynomial α K :=
  ![MvPolynomial.C (q (w, 0)), MvPolynomial.C (q (w, 1)), MvPolynomial.X w, 1]

@[simp]
theorem eval_pencilConfigPointPoly (q : α × Fin 2 → K) (z : α → K) (w : α) (i : Fin 4) :
    MvPolynomial.eval z (pencilConfigPointPoly q w i) = pencilConfigPoint q z w i := by
  fin_cases i <;> simp [pencilConfigPointPoly, pencilConfigPoint]

/-- **The polynomial mirror of `pencilNormalOfPicture`, in the height variables at a fixed
picture** (Phase 40b CARRIER slice C3, item 5): `cross₃Poly` of the three selected configuration
points' polynomial mirrors. Its eval lemma (`eval_pencilNormalOfPicturePoly`) is what lets `X0Gen`
intersect the attaining heights with a nondegeneracy polynomial on `L(q)`. -/
noncomputable def pencilNormalOfPicturePoly (q : α × Fin 2 → K) (sel : α → Fin 3 → α) (v : α) :
    Fin 4 → MvPolynomial α K :=
  cross₃Poly (pencilConfigPointPoly q (sel v 0)) (pencilConfigPointPoly q (sel v 1))
    (pencilConfigPointPoly q (sel v 2))

/-- **`pencilNormalOfPicturePoly` evaluates to the actual `pencilNormalOfPicture` value** (Phase
40b CARRIER slice C3, item 5). -/
theorem eval_pencilNormalOfPicturePoly (q : α × Fin 2 → K) (sel : α → Fin 3 → α) (v : α)
    (z : α → K) (i : Fin 4) :
    MvPolynomial.eval z (pencilNormalOfPicturePoly q sel v i)
      = pencilNormalOfPicture q z sel v i := by
  rw [pencilNormalOfPicturePoly, cross₃Poly_eval]
  have h0 : (fun j => MvPolynomial.eval z (pencilConfigPointPoly q (sel v 0) j)) =
      pencilConfigPoint q z (sel v 0) := funext fun j => eval_pencilConfigPointPoly q z (sel v 0) j
  have h1 : (fun j => MvPolynomial.eval z (pencilConfigPointPoly q (sel v 1) j)) =
      pencilConfigPoint q z (sel v 1) := funext fun j => eval_pencilConfigPointPoly q z (sel v 1) j
  have h2 : (fun j => MvPolynomial.eval z (pencilConfigPointPoly q (sel v 2) j)) =
      pencilConfigPoint q z (sel v 2) := funext fun j => eval_pencilConfigPointPoly q z (sel v 2) j
  rw [h0, h1, h2, pencilNormalOfPicture]

/-! ## The configuration as a pencil framework (Phase 40b CARRIER slice C4) -/

/-- **The point-join framework** (`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice
C4): the body-hinge framework on `G` whose supporting extensor at every label `e` is the join
`p_u ∧ p_v` of the points at `(u, v) = ends e`, the hinge of a pencil realization with concurrency
points `p`. It is unpatched: at a label off `E(G)` the join is whatever `ends` names, possibly
zero; the realization witness `pencilConfigFramework` patches it there. -/
noncomputable def pointJoinFramework (G : Graph α β) (ends : β → α × α) (p : α → Fin 4 → K) :
    BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e := ScrewSpace.mk (extensor ![p (ends e).1, p (ends e).2])
    (extensor_mem_exteriorPower _)

/-- **`ofNormals` at the points is the polarity image of the point-join framework**
(`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice C4). The panel-hinge framework whose
panel normal at each body is its point `p_v` has, at every label, the meet
`panelSupportExtensor p_u p_v` of the two polar planes, which the polarity `screwComplementIso`
takes the join `p_u ∧ p_v` to (`screwComplementIso_mk_extensor`, over every field). -/
theorem ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework (G : Graph α β)
    (ends : β → α × α) (p : α → Fin 4 → K) :
    (PanelHingeFramework.ofNormals (k := 2) G ends (fun x => p x.1 x.2)).toBodyHinge
      = (pointJoinFramework G ends p).mapSupport screwComplementIso := by
  have hsupp : (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor
      = ((pointJoinFramework G ends p).mapSupport screwComplementIso).supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapSupport_supportExtensor, pointJoinFramework,
      screwComplementIso_mk_extensor, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
    rfl
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

open Classical in
/-- **The configuration as a pencil framework** (`lem:pencil-config-point-join-rank`; Phase 40b
CARRIER slice C4): the point-join framework of the configuration points `p_w =
pencilConfigPoint q z w`, patched off `E(G)`. At a label `e ∈ E(G)` the supporting extensor is the
join `p_u ∧ p_v` at `(u, v) = ends e`; off `E(G)` it is the fixed nonzero join of two standard
basis vectors, as in `pencilChartFramework` (`Molecule/Pencil/Chart.lean`), since
`HasCoplanarPanelRealization` asks for a nonzero supporting extensor at every label of `β`. The
endpoints are read from `ends`, not `Graph.endsOf`, so no `[Inhabited α]` is needed. -/
noncomputable def pencilConfigFramework (G : Graph α β) (ends : β → α × α) (q : α × Fin 2 → K)
    (z : α → K) : BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e :=
    if e ∈ E(G) then
      ScrewSpace.mk (extensor ![pencilConfigPoint q z (ends e).1, pencilConfigPoint q z (ends e).2])
        (extensor_mem_exteriorPower _)
    else
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _)

@[simp]
theorem pencilConfigFramework_graph (G : Graph α β) (ends : β → α × α) (q : α × Fin 2 → K)
    (z : α → K) : (pencilConfigFramework G ends q z).graph = G := rfl

/-- The supporting extensor of `pencilConfigFramework` at a label of `E(G)`: the point join. -/
theorem pencilConfigFramework_supportExtensor_of_mem_edgeSet {G : Graph α β} (ends : β → α × α)
    (q : α × Fin 2 → K) (z : α → K) {e : β} (he : e ∈ E(G)) :
    (pencilConfigFramework G ends q z).supportExtensor e =
      ScrewSpace.mk (extensor ![pencilConfigPoint q z (ends e).1, pencilConfigPoint q z (ends e).2])
        (extensor_mem_exteriorPower _) :=
  ite_eq_left he

/-- The supporting extensor of `pencilConfigFramework` off `E(G)`: the standard-basis patch. -/
theorem pencilConfigFramework_supportExtensor_of_not_mem_edgeSet {G : Graph α β}
    (ends : β → α × α) (q : α × Fin 2 → K) (z : α → K) {e : β} (he : e ∉ E(G)) :
    (pencilConfigFramework G ends q z).supportExtensor e =
      ScrewSpace.mk (extensor ![(![1, 0, 0, 0] : Fin 4 → K), (![0, 1, 0, 0] : Fin 4 → K)])
        (extensor_mem_exteriorPower _) :=
  ite_eq_right he

/-- **The patched configuration framework has the rank of `ofNormals` at the configuration
points** (`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice C4, the polar/primal rank
equality). The patch agrees with the unpatched point-join framework on every link, so the two
have the same rigidity-row span (`span_rigidityRows_eq_of_supportExtensor_agree`); the unpatched
one is carried to `ofNormals` by the polarity
(`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`), an invertible map of the screw space,
which leaves the rank unchanged (`BodyHingeFramework.finrank_span_rigidityRows_mapSupport`). No
hypothesis on `ends` is needed: a link's label lies in `E(G)`, where the patch is the join at
whatever `ends` names, exactly as in the unpatched framework. -/
theorem finrank_span_rigidityRows_pencilConfigFramework (G : Graph α β) (ends : β → α × α)
    (q : α × Fin 2 → K) (z : α → K) :
    Module.finrank K (Submodule.span K (pencilConfigFramework G ends q z).rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
  have hspan : Submodule.span K (pencilConfigFramework G ends q z).rigidityRows
      = Submodule.span K (pointJoinFramework G ends (pencilConfigPoint q z)).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun _ _ _ he =>
      pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he.edge_mem
  rw [hspan, ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends (pencilConfigPoint q z),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport]

/-- **The configuration framework's hinges are all nonzero over an admissible picture**
(`lem:pencil-config-point-join-rank`; Phase 40b CARRIER slice C4). At a label of `E(G)`, `ends`
names the two ends of a link, whose picture points differ, so their configuration points are
independent at every height (`linearIndependent_pencilConfigPoint_pair`) and their join is
nonzero; off `E(G)` the patch is nonzero (`extensor_stdBasis_pair_ne_zero`). -/
theorem _root_.Graph.IsAdmissiblePicture.pencilConfigFramework_supportExtensor_ne_zero
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) (z : α → K) (e : β) :
    (pencilConfigFramework G ends q z).supportExtensor e ≠ 0 := by
  intro h0
  have hval := congrArg ScrewSpace.val h0
  by_cases he : e ∈ E(G)
  · rw [pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he, ScrewSpace.val_mk,
      ScrewSpace.val_zero] at hval
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
    exact (extensor_ne_zero_iff_linearIndependent _).mpr
      (linearIndependent_pencilConfigPoint_pair z (hq.1 _ _ _ (hends e x y hxy))) hval
  · rw [pencilConfigFramework_supportExtensor_of_not_mem_edgeSet ends q z he, ScrewSpace.val_mk,
      ScrewSpace.val_zero] at hval
    exact extensor_stdBasis_pair_ne_zero hval

/-- **A configuration over an admissible picture is a pencil panel realization**
(`lem:pencil-config-distinct-realization`; Phase 40b CARRIER slice C4). Over an admissible picture
`q` and a height `z ∈ L(q)`, with a selector `sel` choosing at every body of `G` three members of
its closed neighbourhood with independent picture points, the configuration framework
`pencilConfigFramework G ends q z`, the plane normals `pencilNormalOfPicture q z sel` and the
configuration points `pencilConfigPoint q z` form a pencil panel realization of `G`. The normals
are nonzero (`pencilNormalOfPicture_ne_zero_iff`, with the picture-to-configuration independence
transport); each normal is orthogonal to the points of the whole closed neighbourhood
(`dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`), which contains both ends of every
link at the body and the body itself, giving both panel containments and the incidence; each
point has last coordinate `1`; and a link's join passes through both its ends by construction. -/
theorem _root_.Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework
    {G : Graph α β} {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {z : α → K} (hz : z ∈ G.liftingSpace q) {sel : α → Fin 3 → α}
    (hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i))) :
    HasPencilPanelRealization G (pencilConfigFramework G ends q z)
      (pencilNormalOfPicture q z sel) (pencilConfigPoint q z) := by
  have hperp : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v,
      pencilConfigPoint q z w ⬝ᵥ pencilNormalOfPicture q z sel v = 0 := fun v hv w hw => by
    rw [dotProduct_comm]
    exact dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd hz hv (hsel v hv).1 hw
  -- A link's supporting extensor is the join of its two ends, in one order or the other.
  have hjoin : ∀ e u v, G.IsLink e u v →
      (pencilConfigFramework G ends q z).supportExtensor e =
        ScrewSpace.mk (extensor ![pencilConfigPoint q z u, pencilConfigPoint q z v])
          (extensor_mem_exteriorPower _) ∨
      (pencilConfigFramework G ends q z).supportExtensor e =
        ScrewSpace.mk (extensor ![pencilConfigPoint q z v, pencilConfigPoint q z u])
          (extensor_mem_exteriorPower _) := by
    intro e u v he
    rw [pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he.edge_mem]
    rcases (hends e u v he).eq_and_eq_or_eq_and_eq he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]
    · right; rw [h1, h2]
  -- The join of the two ends of a link, in either order, lies in both panels and passes through
  -- both points.
  have hkey : ∀ e a b, G.IsLink e a b →
      ExtensorInPanel (ScrewSpace.mk (extensor ![pencilConfigPoint q z a, pencilConfigPoint q z b])
          (extensor_mem_exteriorPower _)) (pencilNormalOfPicture q z sel a) ∧
      ExtensorInPanel (ScrewSpace.mk (extensor ![pencilConfigPoint q z a, pencilConfigPoint q z b])
          (extensor_mem_exteriorPower _)) (pencilNormalOfPicture q z sel b) ∧
      ExtensorThroughPoint (ScrewSpace.mk (extensor ![pencilConfigPoint q z a,
          pencilConfigPoint q z b]) (extensor_mem_exteriorPower _)) (pencilConfigPoint q z a) ∧
      ExtensorThroughPoint (ScrewSpace.mk (extensor ![pencilConfigPoint q z a,
          pencilConfigPoint q z b]) (extensor_mem_exteriorPower _)) (pencilConfigPoint q z b) := by
    intro e a b he
    have ha : a ∈ V(G) := he.left_mem
    have hb : b ∈ V(G) := he.right_mem
    refine ⟨⟨_, ScrewSpace.val_mk _ _, Fin.forall_fin_two.mpr
        ⟨hperp a ha a (Or.inl rfl), hperp a ha b (Or.inr ⟨e, he⟩)⟩⟩,
      ⟨_, ScrewSpace.val_mk _ _, Fin.forall_fin_two.mpr
        ⟨hperp b hb a (Or.inr ⟨e, he.symm⟩), hperp b hb b (Or.inl rfl)⟩⟩,
      ⟨_, ScrewSpace.val_mk _ _, Submodule.subset_span ⟨0, rfl⟩⟩,
      ⟨_, ScrewSpace.val_mk _ _, Submodule.subset_span ⟨1, rfl⟩⟩⟩
  refine ⟨⟨rfl, fun v hv => ?_, hq.pencilConfigFramework_supportExtensor_ne_zero hends z,
    fun e u v he => ?_⟩, fun v _ h0 => ?_, fun v hv => hperp v hv v (Or.inl rfl),
    fun e u v he => ?_⟩
  · exact (pencilNormalOfPicture_ne_zero_iff q z sel v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z (hsel v hv).2)
  · rcases hjoin e u v he with h | h <;> rw [h]
    · exact ⟨(hkey e u v he).1, (hkey e u v he).2.1⟩
    · exact ⟨(hkey e v u he.symm).2.1, (hkey e v u he.symm).1⟩
  · simpa [pencilConfigPoint] using congr_fun h0 3
  · rcases hjoin e u v he with h | h <;> rw [h]
    · exact ⟨(hkey e u v he).2.2.1, (hkey e u v he).2.2.2⟩
    · exact ⟨(hkey e v u he.symm).2.2.2, (hkey e v u he.symm).2.2.1⟩

/-- **An attaining configuration over an admissible picture is a distinct pencil realization at
the deficiency rank** (`lem:pencil-config-distinct-realization`; Phase 40b CARRIER slice C4, the
bridge to the distinct statement). If a configuration `(q, z)` with `q` admissible and
`z ∈ L(q)` has row rank `6(|V(G)| − 1) − def₃(G)` at `ofNormals` of its points (the rank
`Graph.X0Attains` reads), then `G` has an adjacent-distinct pencil realization at the deficiency
rank (`HasDistinctPencilRealization`). The witness is the patched configuration framework
(`pencilConfigFramework`) with the configuration points as concurrency points and, as normals,
the plane normals at admissibility's own triple at each body (chosen classically, a dummy off
`V(G)`): a pencil panel realization
(`Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework`), adjacent points
independent since adjacent picture points differ (`linearIndependent_pencilConfigPoint_pair`), at
the rank of `ofNormals` (`finrank_span_rigidityRows_pencilConfigFramework`). -/
theorem _root_.Graph.IsAdmissiblePicture.hasDistinctPencilRealization {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {ends : β → α × α}
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    {z : α → K} (hz : z ∈ G.liftingSpace q)
    (hrank : (Module.finrank K (Submodule.span K
        (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
        = screwDim 2 * ((V(G).ncard : ℤ) - 1) - G.deficiency 3) :
    HasDistinctPencilRealization K 3 G := by
  classical
  let sel : α → Fin 3 → α := fun v => if hv : v ∈ V(G) then (hq.2 v hv).choose else fun _ => v
  have hsel : ∀ v ∈ V(G), (∀ i, sel v i ∈ G.closedNbhd v) ∧
      LinearIndependent K (fun i => pencilPicturePoint q (sel v i)) := by
    intro v hv
    simp only [sel, hv, ↓reduceDIte]
    exact (hq.2 v hv).choose_spec
  refine ⟨pencilConfigFramework G ends q z, pencilNormalOfPicture q z sel, pencilConfigPoint q z,
    hq.hasPencilPanelRealization_pencilConfigFramework hends hz hsel,
    fun e u v he => linearIndependent_pencilConfigPoint_pair z (hq.1 e u v he), ?_⟩
  rw [finrank_span_rigidityRows_pencilConfigFramework]
  exact hrank

/-- **The general configuration attaining gives a distinct pencil realization at the deficiency
rank** (`lem:pencil-x0-attains-distinct`; Phase 40b CARRIER slice C4, the `X0Dist` leg of
`thm:pencil-x0-generic-attains`). Over an infinite field, `Graph.X0Attains K G` forces
`HasDistinctPencilRealization K 3 G`: the nonzero picture polynomial `P` has a non-root `q`
(`MvPolynomial.exists_eval_ne_zero`), which is admissible with a height `z ∈ L(q)` off the
height polynomial's zero set, where the rank is attained; the bridge
`Graph.IsAdmissiblePicture.hasDistinctPencilRealization` finishes. This is the consumer
`Graph.X0Attains` was shaped for: the distinct motive uses only one attaining configuration. -/
theorem _root_.Graph.X0Attains.hasDistinctPencilRealization [Infinite K] {G : Graph α β}
    (h : G.X0Attains K) : HasDistinctPencilRealization K 3 G := by
  obtain ⟨ends, P, hends, hP, hgood⟩ := h
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  obtain ⟨hadm, R, ⟨z, hz, hRz⟩, hall⟩ := hgood q hq
  exact hadm.hasDistinctPencilRealization hends hz (hall z hz hRz)

/-! ## Scaling and affine shifts of the heights keep the rank (Phase 40b CARRIER, (MC-3)) -/

/-- **A collineation of the points is a change of screw coordinates of the point-join framework**
(`lem:pencil-rank-scale-shift`; Phase 40b CARRIER). Applying an invertible linear map `g` of `K⁴`
to every point replaces each join `p_u ∧ p_v` by `g p_u ∧ g p_v`, its image under the induced
screw-space automorphism (`BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor`). -/
theorem pointJoinFramework_comp_eq_mapSupport (G : Graph α β) (ends : β → α × α)
    (p : α → Fin 4 → K) (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    pointJoinFramework G ends (fun v => g (p v))
      = (pointJoinFramework G ends p).mapSupport
          (BodyHingeFramework.screwEquivOfLinearEquiv g) := by
  have hsupp : (pointJoinFramework G ends (fun v => g (p v))).supportExtensor
      = ((pointJoinFramework G ends p).mapSupport
          (BodyHingeFramework.screwEquivOfLinearEquiv g)).supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapSupport_supportExtensor, pointJoinFramework,
      BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor]
    congr 2
    funext i; fin_cases i <;> rfl
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

/-- **The rank of a configuration is unchanged by scaling the heights and shifting them by a
globally affine height** (`lem:pencil-rank-scale-shift`; Phase 40b CARRIER, the last clause of
informal (MC-3)). For `t ≠ 0` and `a ∈ Aff(q)` (`Graph.affineLifts`), the configurations `(q, z)`
and `(q, t • z + a)` have the same row rank at `ofNormals` of their points. With
`a_w = h ⬝ (x_w, y_w, 1)` on `V(G)`, the invertible linear map
`(x, y, ζ, w) ↦ (x, y, t ζ + h ⬝ (x, y, w), w)` of `K⁴` carries `p_w` to the point of
`(q, t • z + a)` at every body of `G`; the ends of every link are bodies of `G` (`hends`), so the
two point-join frameworks agree on links (`span_rigidityRows_eq_of_supportExtensor_agree`), and a
collineation leaves the point-join rank unchanged (`pointJoinFramework_comp_eq_mapSupport`,
`BodyHingeFramework.finrank_span_rigidityRows_mapSupport`), as does the polarity back to
`ofNormals` (`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`). -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts {G : Graph α β}
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin 2 → K) (z : α → K) {t : K} (ht : t ≠ 0) {a : α → K}
    (ha : a ∈ G.affineLifts q) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q (t • z + a) p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
  classical
  obtain ⟨h, rfl⟩ := ha
  let f : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun b => ![b 0, b 1, t * b 2 + (h 0 * b 0 + h 1 * b 1 + h 2 * b 3), b 3]
      map_add' := fun b c => by funext i; fin_cases i <;> simp; ring
      map_smul' := fun c b => by funext i; fin_cases i <;> simp; ring }
  let f' : (Fin 4 → K) →ₗ[K] (Fin 4 → K) :=
    { toFun := fun b => ![b 0, b 1, t⁻¹ * (b 2 - (h 0 * b 0 + h 1 * b 1 + h 2 * b 3)), b 3]
      map_add' := fun b c => by funext i; fin_cases i <;> simp; ring
      map_smul' := fun c b => by funext i; fin_cases i <;> simp; ring }
  let g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K) := LinearEquiv.ofLinearMap f f'
    (LinearMap.ext fun b => funext fun i => by fin_cases i <;> simp [f, f']; field_simp; ring)
    (LinearMap.ext fun b => funext fun i => by fin_cases i <;> simp [f, f']; field_simp)
  have hg : ∀ w ∈ V(G),
      g (pencilConfigPoint q z w) = pencilConfigPoint q (t • z + G.affineLiftMap q h) w := by
    intro w hw
    funext i
    fin_cases i <;> simp [g, f, pencilConfigPoint, pencilPicturePoint, hw, dotProduct,
      Fin.sum_univ_three]
  have hspan : Submodule.span K
        (pointJoinFramework G ends (pencilConfigPoint q (t • z + G.affineLiftMap q h))).rigidityRows
      = Submodule.span K
        (pointJoinFramework G ends (fun w => g (pencilConfigPoint q z w))).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun e u v he => by
      have h0 := hends e u v he
      simp only [pointJoinFramework, hg _ h0.left_mem, hg _ h0.right_mem]
  rw [ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends
      (pencilConfigPoint q (t • z + G.affineLiftMap q h)),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport, hspan,
    pointJoinFramework_comp_eq_mapSupport, BodyHingeFramework.finrank_span_rigidityRows_mapSupport,
    ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework G ends (pencilConfigPoint q z),
    BodyHingeFramework.finrank_span_rigidityRows_mapSupport]

/-! ## The pencil condition is linear in the heights (Phase 40b CARRIER slice C5′,
`lem:pencil-condition-linear`) -/

/-- **Coplanar closed neighbourhoods force `z ∈ L(q)`, over an admissible picture**
(`lem:pencil-condition-linear`; Phase 40b CARRIER, informal (MC-1)'s converse). If a height `z`
vanishes off `V(G)` and, at every body `v` of `G`, some nonzero `n : K⁴` annihilates the
configuration point of every member of the closed neighbourhood of `v`, then `z ∈ L(q)`.

Route: expand `n ⬝ᵥ p_w` as `(n₀, n₁, n₃) ⬝ᵥ (x_w, y_w, 1) + n₂ z_w`. Admissibility gives, at `v`,
three closed-neighbourhood members `t` with independent picture points; if `n₂ = 0` the relation at
each `t i` puts `(n₀, n₁, n₃)` in the kernel of the unit matrix of their picture points
(`Matrix.linearIndependent_rows_iff_isUnit`), forcing it (hence all of `n`, since `n₂ = 0`) to
vanish, contradicting `n ≠ 0`. So `n₂ ≠ 0`, and solving the relation for `z_w` exhibits `L(q)`'s
affine coefficients `h = -(n₂)⁻¹ • (n₀, n₁, n₃)` at `v`. -/
theorem _root_.Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K}
    (hs : ∀ w ∉ V(G), z w = 0)
    (hcop : ∀ v ∈ V(G), ∃ n : Fin 4 → K, n ≠ 0 ∧
      ∀ w ∈ G.closedNbhd v, n ⬝ᵥ pencilConfigPoint q z w = 0) :
    z ∈ G.liftingSpace q := by
  refine ⟨hs, fun v hv => ?_⟩
  obtain ⟨n, hn, hnw⟩ := hcop v hv
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  have hexp : ∀ w, n ⬝ᵥ pencilConfigPoint q z w =
      ![n 0, n 1, n 3] ⬝ᵥ pencilPicturePoint q w + n 2 * z w := by
    intro w
    simp [dotProduct, Fin.sum_univ_four, Fin.sum_univ_three, pencilConfigPoint,
      pencilPicturePoint]
    ring
  have hn2 : n 2 ≠ 0 := by
    intro h2
    have hunit : IsUnit (Matrix.of fun i => pencilPicturePoint q (t i)) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hli
    have hzero : (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ ![n 0, n 1, n 3] =
        (Matrix.of fun i => pencilPicturePoint q (t i)) *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      have := hnw (t i) (ht i)
      rw [hexp, h2, zero_mul, add_zero] at this
      simp only [Matrix.mulVec, Matrix.of_apply, Pi.zero_apply]
      rwa [dotProduct_comm]
    have h3 := Matrix.mulVec_injective_iff_isUnit.mpr hunit hzero
    apply hn
    funext i
    fin_cases i
    · simpa using congr_fun h3 0
    · simpa using congr_fun h3 1
    · exact h2
    · simpa using congr_fun h3 2
  refine ⟨-(n 2)⁻¹ • ![n 0, n 1, n 3], fun w hw => ?_⟩
  have := hnw w hw
  rw [hexp] at this
  rw [smul_dotProduct, smul_eq_mul]
  field_simp
  linear_combination this

/-- **Every nonzero normal of a closed neighbourhood is the interpolant, up to a nonzero scalar**
(`lem:pencil-condition-linear`; Phase 40b CARRIER, informal (MC-1)'s "unique, non-vertical plane",
in interpolant form). Over an admissible picture, at a body `v` where `z` restricts on the closed
neighbourhood to the affine function `h`, any nonzero `n : K⁴` orthogonal to the whole closed
neighbourhood is a nonzero scalar multiple of `(h₀, h₁, -1, h₂)`: in particular its third
coordinate is nonzero (the plane is non-vertical) and it is determined by `h` up to scale (the
plane is unique).

Route, as in `exists_smul_pencilNormalOfPicture_eq_of_mem_closedNbhd`: both `n` and the interpolant
`m = (h₀, h₁, -1, h₂)` lie in the common perp `W` of the three independent configuration points an
admissible selector at `v` supplies (`n` by hypothesis, `m` by direct computation from `hh`); `W` is
one-dimensional (`finrank_toDualPerp_triple_eq`), so it is spanned by the nonzero `m`
(`Submodule.eq_of_le_of_finrank_eq`), and `n` is a scalar multiple. -/
theorem _root_.Graph.IsAdmissiblePicture.exists_smul_eq_interpolant {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K} {v : α} (hv : v ∈ V(G))
    {h : Fin 3 → K} (hh : ∀ w ∈ G.closedNbhd v, z w = h ⬝ᵥ pencilPicturePoint q w)
    {n : Fin 4 → K} (hn : n ≠ 0)
    (hnw : ∀ w ∈ G.closedNbhd v, n ⬝ᵥ pencilConfigPoint q z w = 0) :
    ∃ c : K, c ≠ 0 ∧ n = c • ![h 0, h 1, -1, h 2] := by
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  set m : Fin 4 → K := ![h 0, h 1, -1, h 2] with hmdef
  have hLIc : LinearIndependent K (fun i => pencilConfigPoint q z (t i)) :=
    linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hli
  have hm : m ≠ 0 := fun h0 => by simpa [hmdef] using congr_fun h0 2
  set W : Submodule K (Fin 4 → K) := ⨅ j : Fin 3, LinearMap.ker
      ((Pi.basisFun K (Fin 4)).toDual.flip ((fun i => pencilConfigPoint q z (t i)) j))
    with hWdef
  have hWdim : Module.finrank K W = 1 := finrank_toDualPerp_triple_eq hLIc
  have hmemW : ∀ x : Fin 4 → K, x ∈ W ↔ ∀ j, x ⬝ᵥ pencilConfigPoint q z (t j) = 0 := by
    intro x
    simp only [hWdef, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      piBasisFun_toDual_eq_dotProduct]
  have hnmem : n ∈ W := (hmemW n).mpr fun j => hnw _ (ht j)
  have hmmem : m ∈ W := by
    rw [hmemW]
    intro j
    have := hh _ (ht j)
    simp only [hmdef, pencilConfigPoint, pencilPicturePoint, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_three] at this ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at this ⊢
    rw [this]; ring
  have hspan : Submodule.span K ({m} : Set (Fin 4 → K)) = W := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]; simpa using hmmem
    · rw [hWdim, finrank_span_singleton hm]
  rw [← hspan] at hnmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hnmem
  exact ⟨c, fun hc0 => hn (by rw [← hc, hc0, zero_smul]), hc.symm⟩

end CombinatorialRigidity.Molecular
