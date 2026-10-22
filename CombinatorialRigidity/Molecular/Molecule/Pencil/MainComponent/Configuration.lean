/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.MainComponent.Carrier

/-!
# The configuration as a pencil realization, and coplanarity

The lemmas of `sec:main-component-carrier` that read a configuration as a pencil realization, over
the definitions of `Carrier.lean`, and the configuration form of
`lem:pencil-x0-two-hubs-obstruction` (`sec:main-component-statements`). The plane normal of a body
(`pencilNormalOfPicture`) is nonzero when its three bodies have independent configuration points,
which they have at every height when their picture points are independent; at a height in `L(q)`,
when its three bodies lie in the closed neighbourhood, it is orthogonal to the configuration points
of the whole closed neighbourhood (`lem:pencil-selector-plane-contains-nbhd`).

The point-join framework (`pointJoinFramework`) has at each edge the join `p_u ∧ p_v` of the points
of its ends; with a fixed nonzero hinge off `E(G)`, it is the framework `F_p` of
`lem:pencil-config-point-join-rank` (`pencilConfigFramework`), whose rank is the rank of the
configuration. Over an admissible picture and a height in `L(q)`, `F_p` with the plane normals and
the configuration points is a pencil realization, adjacent-distinct and at the deficiency rank when
the configuration is attaining (`lem:pencil-config-distinct-realization`); so if the general
configuration of `G` attains, `G` has an adjacent-distinct pencil realization
(`lem:pencil-x0-attains-distinct`). An invertible linear map of `K⁴` applied to the points keeps the
rank (`lem:pencil-rank-collineation`), and so do scaling the heights and adding a globally affine
height (`lem:pencil-rank-scale-shift`). Over an admissible picture, a height lies in `L(q)` exactly
when the points of every closed neighbourhood lie in a plane, and if the heights there are
`a x + b y + c`, every nonzero vector orthogonal to these points is a multiple of `(a, b, -1, c)`
(`lem:pencil-condition-linear`).

The rank of a configuration is taken at `PanelHingeFramework.ofNormals G ends` of its points, not of
its plane normals. Each body's point `p_v` is then the normal of the polar plane `p_v^⊥`, and the
hinge `panelSupportExtensor p_u p_v` is the polar of the line `p_u ∧ p_v`, so the rank is that of
the point-join framework (the polarity is an invertible map of the screw space;
`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`;
`finrank_span_rigidityRows_pencilConfigFramework`), and the hinge is nonzero at every link as soon
as the picture points differ. `ofNormals` at the plane normals would give the wrong rank: at a
general picture, adjacent planes coincide on the whole fibre whenever the two bodies lie in a common
planar-rigid set (`thm:pencil-jj-equality` there), as at every edge of a triangle, and at a flat
configuration they coincide at every edge; `panelSupportExtensor n n = 0` there, and a zero hinge
welds its bodies (its hinge-row block is every functional).

## Main definitions

* `pointJoinFramework`: the body-hinge framework whose hinge at each label is the join of the points
  of its two ends.
* `pencilConfigFramework`: the point-join framework of a configuration, with a fixed nonzero hinge
  off `E(G)`; the framework `F_p` of `lem:pencil-config-point-join-rank`.

## Main results

* `pencilNormalOfPicture_ne_zero_iff`: the plane normal is nonzero exactly when its three
  configuration points are independent.
* `linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint`: independent picture
  points give independent configuration points, at every height.
* `dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`:
  `lem:pencil-selector-plane-contains-nbhd`.
* `finrank_span_rigidityRows_pencilConfigFramework` and
  `Graph.IsAdmissiblePicture.pencilConfigFramework_supportExtensor_ne_zero`:
  `lem:pencil-config-point-join-rank`.
* `Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework` and
  `Graph.IsAdmissiblePicture.hasDistinctPencilRealization`:
  `lem:pencil-config-distinct-realization`.
* `Graph.X0Attains.hasDistinctPencilRealization`: `lem:pencil-x0-attains-distinct`.
* `not_isNondeg_pencilConfigPoint_of_two_hubs_three_common`: the configuration form of
  `lem:pencil-x0-two-hubs-obstruction`.
* `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`:
  `lem:pencil-rank-collineation`.
* `Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts`: `lem:pencil-rank-scale-shift`.
* `Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar` and
  `Graph.IsAdmissiblePicture.exists_smul_eq_interpolant`: `lem:pencil-condition-linear`.
-/

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K]
variable {α β : Type*}

/-! ## The plane normals -/

/-- **The plane normal is nonzero exactly when its three configuration points are independent**
(`def:pencil-configuration`): `pencilNormalOfPicture` is the `cross₃` of the three configuration
points, and `cross₃_ne_zero_iff_linearIndependent` applies. -/
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

/-- **Independent picture points give independent configuration points, at every height** (a step of
`lem:pencil-config-distinct-realization`, `lem:pencil-condition-linear`,
`lem:pencil-x0-two-hubs-obstruction` and `lem:pencil-x0-conjunct-three`): the linear map
`f : K⁴ →ₗ[K] K³` that drops the height coordinate (keeping the coordinates `0`, `1` and `3`) takes
each configuration point `pencilConfigPoint q z w` to the picture point `pencilPicturePoint q w`, so
a family of configuration points whose images are independent is independent
(`LinearIndependent.of_comp`, which asks no injectivity of `f`). -/
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
    simp only [Function.comp_apply]
    funext j
    fin_cases j <;> rfl
  rwa [heq]

/-- **The plane of a selector at `v` contains the whole closed neighbourhood**
(`lem:pencil-selector-plane-contains-nbhd`): at a height `z ∈ L(q)` and a body `v` of `G` whose
selector `sel v` names three members of `G.closedNbhd v`, the normal
`N = pencilNormalOfPicture q z sel v` is orthogonal to the configuration point of every member of
the closed neighbourhood, not only to the three it is computed from. By `dotProduct_cross₃`,
`N ⬝ᵥ p_w` is `det[p_{sel v 0}, p_{sel v 1}, p_{sel v 2}, p_w]`. As `z ∈ L(q)`, some `h : Fin 3 → K`
makes the point of every member of the closed neighbourhood the image of its picture point under the
linear map `a ↦ (a 0, a 1, h ⬝ᵥ a, a 2)` of `K³` to `K⁴`. So the four rows are the images of four
vectors of `K³`, which are dependent (`LinearIndependent.fintype_card_le_finrank`); a dependence
among vectors is one among their images, so the four rows are dependent and the determinant vanishes
(`Matrix.linearIndependent_rows_iff_det_ne_zero`).

It asks no independence of the three chosen points: when they are dependent, the normal is zero. -/
theorem dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd {G : Graph α β}
    {q : α × Fin 2 → K} {z : α → K} (hz : z ∈ G.liftingSpace q) {v : α} (hv : v ∈ V(G))
    {sel : α → Fin 3 → α} (hsel : ∀ i, sel v i ∈ G.closedNbhd v)
    {w : α} (hw : w ∈ G.closedNbhd v) :
    pencilNormalOfPicture q z sel v ⬝ᵥ pencilConfigPoint q z w = 0 := by
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
  rw [pencilNormalOfPicture, dotProduct_cross₃]
  exact hdetzero

/-! ## The configuration as a pencil realization -/

/-- **The point-join framework** (the framework of `lem:pencil-config-point-join-rank`, before its
patch): the body-hinge framework on `G` whose supporting extensor at every label `e` is the join
`p_u ∧ p_v` of the points at `(u, v) = ends e`, the hinge of a pencil realization with the points
`p` as concurrency points. At a label off `E(G)` it is the join at whatever `ends` names, possibly
zero; `pencilConfigFramework` patches it there. -/
def pointJoinFramework (G : Graph α β) (ends : β → α × α) (p : α → Fin 4 → K) :
    BodyHingeFramework K 2 α β where
  graph := G
  supportExtensor e := ScrewSpace.mk (extensor ![p (ends e).1, p (ends e).2])
    (extensor_mem_exteriorPower _)

/-- **`ofNormals` at the points is the polarity image of the point-join framework** (a step of
`lem:pencil-config-point-join-rank`, `lem:pencil-rank-collineation` and `thm:pencil-flat-rank`): the
panel-hinge framework whose panel normal at each body is its point `p_v` has, at every label, the
meet `panelSupportExtensor p_u p_v` of the two polar planes, which the polarity `screwComplementIso`
takes the join `p_u ∧ p_v` to (`screwComplementIso_mk_extensor`, over every field). -/
theorem ofNormals_toBodyHinge_eq_mapExtensor_pointJoinFramework (G : Graph α β)
    (ends : β → α × α) (p : α → Fin 4 → K) :
    (PanelHingeFramework.ofNormals (k := 2) G ends (fun x => p x.1 x.2)).toBodyHinge
      = (pointJoinFramework G ends p).mapExtensor screwComplementIso := by
  have hsupp : (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.supportExtensor
      = ((pointJoinFramework G ends p).mapExtensor screwComplementIso).supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapExtensor_supportExtensor, pointJoinFramework,
      screwComplementIso_mk_extensor, PanelHingeFramework.toBodyHinge_supportExtensor,
      PanelHingeFramework.ofNormals_ends, PanelHingeFramework.ofNormals_normal]
    rfl
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

open Classical in
/-- **The configuration as a pencil framework** (`lem:pencil-config-point-join-rank`): the framework
`F_p` of the configuration points `p_w = pencilConfigPoint q z w`, the point-join framework patched
off `E(G)`. At a label `e ∈ E(G)` the supporting extensor is the join `p_u ∧ p_v` at
`(u, v) = ends e`; off `E(G)` it is the fixed nonzero join of two standard basis vectors, as in
`pencilChartFramework` (`Molecule/Pencil/Chart.lean`), since `HasCoplanarPanelRealization` asks for
a nonzero supporting extensor at every label of `β` (`fmlnote:pencil-config-point-join-rank`). The
ends are read from `ends`, not `Graph.endsOf`, so no `[Inhabited α]` is needed. -/
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

/-- **The configuration framework has the rank of `ofNormals` at the configuration points**
(`lem:pencil-config-point-join-rank`): the patch agrees with the point-join framework on every link,
so the two have the same span of rigidity rows (`span_rigidityRows_eq_of_supportExtensor_agree`);
the polarity, an invertible map of the screw space, takes the point-join framework to `ofNormals`
(`ofNormals_toBodyHinge_eq_mapExtensor_pointJoinFramework`) and keeps the rank
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`). It asks nothing of `ends`: the label
of a link lies in `E(G)`, where the patch is the join at whatever `ends` names, as in the point-join
framework. -/
theorem finrank_span_rigidityRows_pencilConfigFramework (G : Graph α β) (ends : β → α × α)
    (q : α × Fin 2 → K) (z : α → K) :
    Module.finrank K (Submodule.span K (pencilConfigFramework G ends q z).rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
          (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
  have hspan : Submodule.span K (pencilConfigFramework G ends q z).rigidityRows
      = Submodule.span K (pointJoinFramework G ends (pencilConfigPoint q z)).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun _ _ _ he =>
      pencilConfigFramework_supportExtensor_of_mem_edgeSet ends q z he.edge_mem
  rw [hspan, ofNormals_toBodyHinge_eq_mapExtensor_pointJoinFramework G ends (pencilConfigPoint q z),
    BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]

/-- **The hinges of the configuration framework are nonzero over an admissible picture**
(`lem:pencil-config-point-join-rank`): at a label of `E(G)`, `ends` names the two ends of a link,
whose picture points differ, so their configuration points are independent at every height
(`linearIndependent_pencilConfigPoint_pair`) and their join is nonzero; off `E(G)` the patch is
nonzero (`extensor_stdBasis_pair_ne_zero`). -/
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

/-- **A configuration over an admissible picture is a pencil realization**
(`lem:pencil-config-distinct-realization`): over an admissible picture `q` and a height `z ∈ L(q)`,
with a selector `sel` that names at every body of `G` three members of its closed neighbourhood with
independent picture points, the configuration framework `pencilConfigFramework G ends q z`, the
plane normals `pencilNormalOfPicture q z sel` and the configuration points `pencilConfigPoint q z`
form a pencil realization of `G`. The normals are nonzero (`pencilNormalOfPicture_ne_zero_iff` and
`linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint`); each normal is
orthogonal to the points of the whole closed neighbourhood
(`dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`), which contains the body itself and
both ends of every link at it, so each hinge lies in the panels of its ends and each point lies in
its panel; each point has last coordinate `1`; and the join at a link passes through the points of
both its ends by construction. -/
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

/-- **An attaining configuration over an admissible picture gives an adjacent-distinct pencil
realization at the deficiency rank** (`lem:pencil-config-distinct-realization`): if a configuration
`(q, z)` with `q` admissible and `z ∈ L(q)` has row rank `6(|V(G)| − 1) − def₃(G)` at `ofNormals` of
its points (the rank `Graph.X0Attains` reads), then `G` has an adjacent-distinct pencil realization
at the deficiency rank (`HasDistinctPencilRealization`). It is the configuration framework
(`pencilConfigFramework`) with the configuration points as concurrency points and, as normals, the
plane normals at the triple that admissibility gives at each body (chosen classically, with a
placeholder off `V(G)`): a pencil realization
(`Graph.IsAdmissiblePicture.hasPencilPanelRealization_pencilConfigFramework`), with adjacent points
independent as adjacent picture points differ (`linearIndependent_pencilConfigPoint_pair`), at the
rank of `ofNormals` (`finrank_span_rigidityRows_pencilConfigFramework`). -/
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

/-- **The configuration form of the two-hubs obstruction** (`lem:pencil-x0-two-hubs-obstruction`):
let `a ≠ b` be pencil hubs of `G` with common neighbours `x`, `y` and `z`. Over a picture at which
the picture points of `x`, `y` and `z` are not collinear, no height `h` gives a nondegenerate
realization with the configuration points as concurrency points, whatever the framework and the
normals: the configuration points of `x`, `y` and `z` are independent at every height
(`linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint`), and
`not_isNondegPencilRealization_of_two_hubs_three_common` applies. -/
theorem not_isNondeg_pencilConfigPoint_of_two_hubs_three_common
    {G : Graph α β} {a b x y z : α} {ea eb fa fb ga gb : β} (hab : a ≠ b)
    (ha : G.PencilHub a) (hb : G.PencilHub b)
    (hxa : G.IsLink ea x a) (hxb : G.IsLink eb x b) (hya : G.IsLink fa y a)
    (hyb : G.IsLink fb y b) (hza : G.IsLink ga z a) (hzb : G.IsLink gb z b)
    {q : α × Fin 2 → K}
    (hq : LinearIndependent K ![pencilPicturePoint q x, pencilPicturePoint q y,
      pencilPicturePoint q z])
    (h : α → K) (F : BodyHingeFramework K 2 α β) (normal : α → Fin 4 → K) :
    ¬ IsNondegPencilRealization G F normal (pencilConfigPoint q h) := by
  have hq' : LinearIndependent K (fun i => pencilPicturePoint q (![x, y, z] i)) := by
    convert hq using 1
    funext i; fin_cases i <;> rfl
  have hLI := linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint h hq'
  refine not_isNondegPencilRealization_of_two_hubs_three_common hab ha hb hxa hxb hya hyb hza hzb
    ?_
  convert hLI using 1
  funext i; fin_cases i <;> rfl

/-- **The general configuration attaining gives an adjacent-distinct pencil realization**
(`lem:pencil-x0-attains-distinct`, `thm:pencil-x0-main-component`'s last claim): over an infinite
field, `Graph.X0Attains K G` gives `HasDistinctPencilRealization K 3 G`. The nonzero picture
polynomial `P` has a non-root `q` (`MvPolynomial.exists_eval_ne_zero`), which is admissible, with a
height `z ∈ L(q)` off the zero set of the height polynomial, where the rank is attained;
`Graph.IsAdmissiblePicture.hasDistinctPencilRealization` applies. It uses one attaining
configuration, as the distinct main-component statement needs (`x0Dist`,
`MainComponent/Statements.lean`). -/
theorem _root_.Graph.X0Attains.hasDistinctPencilRealization [Infinite K] {G : Graph α β}
    (h : G.X0Attains K) : HasDistinctPencilRealization K 3 G := by
  obtain ⟨ends, P, hends, hP, hgood⟩ := h
  obtain ⟨q, hq⟩ := MvPolynomial.exists_eval_ne_zero hP
  obtain ⟨hadm, R, ⟨z, hz, hRz⟩, hall⟩ := hgood q hq
  exact hadm.hasDistinctPencilRealization hends hz (hall z hz hRz)

/-! ## Collineations, and scaling and affine shifts of the heights, keep the rank -/

/-- **A collineation of the points is a change of screw coordinates of the point-join framework** (a
step of `lem:pencil-rank-collineation`): applying an invertible linear map `g` of `K⁴` to every
point replaces each join `p_u ∧ p_v` by `g p_u ∧ g p_v`, its image under the induced automorphism of
the screw space (`BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor`). -/
theorem pointJoinFramework_comp_eq_mapExtensor (G : Graph α β) (ends : β → α × α)
    (p : α → Fin 4 → K) (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    pointJoinFramework G ends (fun v => g (p v))
      = (pointJoinFramework G ends p).mapExtensor
          (BodyHingeFramework.screwEquivOfLinearEquiv g) := by
  have hsupp : (pointJoinFramework G ends (fun v => g (p v))).supportExtensor
      = ((pointJoinFramework G ends p).mapExtensor
          (BodyHingeFramework.screwEquivOfLinearEquiv g)).supportExtensor := by
    funext e
    simp only [BodyHingeFramework.mapExtensor_supportExtensor, pointJoinFramework,
      BodyHingeFramework.screwEquivOfLinearEquiv_mk_extensor]
    congr 2
    funext i; fin_cases i <;> rfl
  exact congrArg (BodyHingeFramework.mk (k := 2) G) hsupp

/-- **A collineation of the normals preserves the rank** (`lem:pencil-rank-collineation`): if the
panel normals `p'` are the images of `p` under one invertible linear map `g` of `K⁴` at every body
of `G`, the panel-hinge frameworks with normals `p` and with normals `p'` have the same row rank.
Both are `ofNormals` frameworks, whose hinge at a link is the polarity image of the join of its two
ends' normals (`ofNormals_toBodyHinge_eq_mapExtensor_pointJoinFramework`); `g` takes one join to the
image of the other under an automorphism of the screw space
(`pointJoinFramework_comp_eq_mapExtensor`), and an automorphism keeps the rank
(`BodyHingeFramework.finrank_span_rigidityRows_mapExtensor`). Scaling the heights and adding a
globally affine height is the case of
`Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` below. -/
theorem PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv {G : Graph α β}
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) {p p' : α → Fin 4 → K}
    (hp : ∀ w ∈ V(G), p' w = g (p w)) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p' x.1 x.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun x => p x.1 x.2)).toBodyHinge.rigidityRows) := by
  have hspan : Submodule.span K (pointJoinFramework G ends p').rigidityRows
      = Submodule.span K (pointJoinFramework G ends (fun w => g (p w))).rigidityRows :=
    span_rigidityRows_eq_of_supportExtensor_agree _ _ rfl fun e u v he => by
      have h0 := hends e u v he
      simp only [pointJoinFramework, hp _ h0.left_mem, hp _ h0.right_mem]
  rw [ofNormals_toBodyHinge_eq_mapExtensor_pointJoinFramework G ends p',
    BodyHingeFramework.finrank_span_rigidityRows_mapExtensor, hspan,
    pointJoinFramework_comp_eq_mapExtensor,
    BodyHingeFramework.finrank_span_rigidityRows_mapExtensor,
    ofNormals_toBodyHinge_eq_mapExtensor_pointJoinFramework G ends p,
    BodyHingeFramework.finrank_span_rigidityRows_mapExtensor]

/-- **Scaling the heights and adding a globally affine height keep the rank**
(`lem:pencil-rank-scale-shift`): for `t ≠ 0` and `a ∈ Aff(q)` (`Graph.affineLifts`), the
configurations `(q, z)` and `(q, t • z + a)` have the same row rank at `ofNormals` of their points.
With `a_w = h ⬝ᵥ (x_w, y_w, 1)` on `V(G)`, the invertible linear map
`(ξ, η, ζ, ω) ↦ (ξ, η, t ζ + h ⬝ᵥ (ξ, η, ω), ω)` of `K⁴` takes `p_w` to the point of
`(q, t • z + a)` at every body `w` of `G`, and
`PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv` applies. -/
theorem _root_.Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts {G : Graph α β}
    {ends : β → α × α} (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin 2 → K) (z : α → K) {t : K} (ht : t ≠ 0) {a : α → K}
    (ha : a ∈ G.affineLifts q) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q (t • z + a) p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := 2) G ends
        (fun p => pencilConfigPoint q z p.1 p.2)).toBodyHinge.rigidityRows) := by
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
  exact PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv hends g
    (fun w hw => (hg w hw).symm)

/-! ## Coplanarity is linear in the heights (`lem:pencil-condition-linear`) -/

/-- **Coplanar closed neighbourhoods force `z ∈ L(q)` over an admissible picture** (the converse
half of `lem:pencil-condition-linear`): if a height `z` vanishes off `V(G)` and, at every body `v`
of `G`, some nonzero `n : K⁴` is orthogonal to the configuration point of every member of the closed
neighbourhood of `v`, then `z ∈ L(q)`.

Write `n ⬝ᵥ p_w` as `(n₀, n₁, n₃) ⬝ᵥ (x_w, y_w, 1) + n₂ z_w`. Admissibility gives, at `v`, three
members of the closed neighbourhood with independent picture points. If `n₂ = 0`, the relation at
each of them puts `(n₀, n₁, n₃)` in the kernel of the unit matrix of their picture points
(`Matrix.linearIndependent_row_iff_isUnit`), so it vanishes, and so does `n`, a contradiction. So
`n₂ ≠ 0`, and solving the relation for `z_w` gives the affine coefficients
`h = -(n₂)⁻¹ • (n₀, n₁, n₃)` of `L(q)` at `v`. -/
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
      Matrix.linearIndependent_row_iff_isUnit.mp hli
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

/-- **`z ∈ L(q)` exactly when every closed neighbourhood is coplanar, over an admissible picture**
(`lem:pencil-condition-linear`, its first claim): a height `z` that vanishes off `V(G)` lies in
`L(q)` exactly when, at every body of `G`, the configuration points of the closed neighbourhood are
orthogonal to a nonzero vector. The converse is
`Graph.IsAdmissiblePicture.mem_liftingSpace_of_coplanar`; the direct implication takes at `v` the
plane normal (`pencilNormalOfPicture`) of the three members that admissibility gives, nonzero by
`linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint` and orthogonal to the
whole closed neighbourhood by `dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd`. -/
theorem _root_.Graph.IsAdmissiblePicture.mem_liftingSpace_iff_coplanar {G : Graph α β}
    {q : α × Fin 2 → K} (hq : G.IsAdmissiblePicture q) {z : α → K}
    (hs : ∀ w ∉ V(G), z w = 0) :
    z ∈ G.liftingSpace q ↔ ∀ v ∈ V(G), ∃ n : Fin 4 → K, n ≠ 0 ∧
      ∀ w ∈ G.closedNbhd v, n ⬝ᵥ pencilConfigPoint q z w = 0 := by
  refine ⟨fun hz v hv => ?_, hq.mem_liftingSpace_of_coplanar hs⟩
  obtain ⟨t, ht, hli⟩ := hq.2 v hv
  refine ⟨pencilNormalOfPicture q z (fun _ => t) v, ?_, fun w hw => ?_⟩
  · exact (pencilNormalOfPicture_ne_zero_iff q z _ v).mpr
      (linearIndependent_pencilConfigPoint_of_linearIndependent_pencilPicturePoint z hli)
  · exact dotProduct_pencilNormalOfPicture_eq_zero_of_mem_closedNbhd hz hv (sel := fun _ => t)
      ht hw

/-- **Every nonzero normal of a closed neighbourhood is a multiple of the interpolant**
(`lem:pencil-condition-linear`, its second claim): over an admissible picture, at a body `v` where
`z` agrees on the closed neighbourhood with the affine function `h`, every nonzero `n : K⁴`
orthogonal to the points of the whole closed neighbourhood is a nonzero multiple of
`(h₀, h₁, -1, h₂)`. So its height coordinate is nonzero (the plane is not vertical), and `h`
determines it up to a scalar (the plane is unique).

Both `n` and the interpolant `m = (h₀, h₁, -1, h₂)` lie in the space `W` of vectors orthogonal to
the three independent configuration points that admissibility gives at `v` (`n` by hypothesis, `m`
from `hh`). `W` is one-dimensional (`finrank_toDualPerp_triple_eq`), so the nonzero `m` spans it
(`Submodule.eq_of_le_of_finrank_eq`), and `n` is a multiple of `m`. -/
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
