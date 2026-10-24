/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.ScrewVelocity
import CombinatorialRigidity.GeneralPositionPlacement

/-!
# The square-graph dictionary

Whiteley's equivalence of two models of a molecule, as an isomorphism of motion spaces at one
placement of the centres (`thm:molecular-iff-square-bar-joint`), as
`sec:molecule-modelling-equivalences` presents it. Katoh and Tanigawa 2011 (pp. 650 and 671) model a
molecule with graph `G`, its atoms as bodies and its bonds as hinges, either as a bar-joint
framework on the square `G²` or as a hinge-concurrent body-hinge framework on `G`, in which the
hinges at each atom pass through its centre; for the equivalence of the two they cite Whiteley's
preprint of 2004.

* The molecular framework `molecularOfCentres G' ends c` (`def:hinge-concurrent`) is the body-hinge
  framework (`BodyHingeFramework.ofHinge`) whose hinge at an edge label `e` is the line through the
  centres of the two bodies `ends e = (u, v)`; its supporting extensor is `ĉ(u) ∨ ĉ(v)`, the join of
  the homogenized centres.
* The map `Φ = molecularVel c` sends a screw assignment `S : V → ScrewSpace ℝ 2` to the velocity
  assignment `v ↦ vel_{S v}(c v)` of the bar-joint framework at `c`.

`Φ` sends the motions of the molecular framework into `ker R(G², c)` (`molecularVel_mem_ker`): every
edge of `G²` lies in a closed neighbourhood `N[w]` (`lem:square-cliques`), on which the velocities
are those of the single screw `S w` (the hinge constraint and `lem:screw-velocity-line`), and a
velocity field is an infinitesimal isometry. For a graph of minimum degree at least two and centres
in general position up to order four, `Φ` is injective on the motions
(`eq_zero_of_molecularVel_eq_zero`) and onto `ker R(G², c)` (`exists_molecularVel_eq`), both by
`lem:screw-determination`, so the two spaces have the same dimension
(`molecular_finrank_motions_eq_square_ker`).
-/

open scoped Matrix InnerProductSpace
open WithLp SimpleGraph

namespace CombinatorialRigidity.Molecular

variable {V β : Type*}

/-! ## The molecular framework from a placement of centres (`def:hinge-concurrent`) -/

/-- **The molecular framework** (`def:hinge-concurrent`) on a multigraph `G` with endpoint selector
`ends` and a placement `c : V → ℝ³` of the centres: the body-hinge framework
(`BodyHingeFramework.ofHinge`) whose hinge at an edge label `e` is the line through the centres
`c (ends e).1` and `c (ends e).2` of the two bodies that the selector gives it. Its supporting
extensor is the join of the homogenized centres (`molecularOfCentres_supportExtensor`), which is
zero when the two centres coincide (a welded hinge). When `ends` gives each link of `G` its ends and
adjacent bodies have distinct centres, every hinge at a body `v` passes through `c v`: the framework
is hinge-concurrent (Katoh and Tanigawa 2011, pp. 650 and 671). -/
noncomputable def molecularOfCentres (G : Graph V β) (ends : β → V × V)
    (c : V → EuclideanSpace ℝ (Fin 3)) : BodyHingeFramework ℝ 2 V β :=
  BodyHingeFramework.ofHinge G (fun e => ![ofLp (c (ends e).1), ofLp (c (ends e).2)])

@[simp] theorem molecularOfCentres_graph (G : Graph V β) (ends : β → V × V)
    (c : V → EuclideanSpace ℝ (Fin 3)) : (molecularOfCentres G ends c).graph = G := rfl

/-- The supporting extensor of a molecular framework's edge is the line extensor of the two
endpoint centres: `C(p(e)) = ĉ(ends e).1 ∨ ĉ(ends e).2`. -/
theorem molecularOfCentres_supportExtensor (G : Graph V β) (ends : β → V × V)
    (c : V → EuclideanSpace ℝ (Fin 3)) (e : β) :
    (molecularOfCentres G ends c).supportExtensor e
      = lineExtensor (ofLp (c (ends e).1)) (ofLp (c (ends e).2)) := by
  apply ScrewSpace.ext
  rw [molecularOfCentres, BodyHingeFramework.ofHinge_supportExtensor_val,
    affineSubspaceExtensor_apply, lineExtensor, ScrewSpace.val_mk]
  congr 1
  funext i
  fin_cases i <;> rfl

/-! ## The dictionary map `Φ = molecularVel` -/

/-- The **screw velocity as a linear map in the screw** (at a fixed point `x`):
`S ↦ vel_S(x) = ω_S ⨯₃ x + t_S`, linear as both coordinate maps are. -/
noncomputable def screwVelL (x : Fin 3 → ℝ) : ScrewSpace ℝ 2 →ₗ[ℝ] (Fin 3 → ℝ) :=
  crossProduct.flip x ∘ₗ screwOmega + screwTau

@[simp] theorem screwVelL_apply (x : Fin 3 → ℝ) (S : ScrewSpace ℝ 2) :
    screwVelL x S = screwVel S x := by
  simp only [screwVelL, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    screwVel_apply]

/-- **The map `Φ`** (a step of `thm:molecular-iff-square-bar-joint`): it sends a screw assignment
`S : V → ScrewSpace ℝ 2` to the velocity assignment `v ↦ vel_{S v}(c v)` of the joints, linearly in
`S`, and the motions of the molecular framework to motions of the bar-joint framework on `G²`
(`molecularVel_mem_ker`). The codomain is `V → EuclideanSpace ℝ (Fin 3)`, the space of the bar-joint
framework, so the velocity `vel_{S v}(c v) : Fin 3 → ℝ` crosses the `WithLp` boundary by `toLp`. -/
noncomputable def molecularVel (c : V → EuclideanSpace ℝ (Fin 3)) :
    (V → ScrewSpace ℝ 2) →ₗ[ℝ] (V → EuclideanSpace ℝ (Fin 3)) :=
  LinearMap.pi fun v =>
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap ∘ₗ
      screwVelL (ofLp (c v)) ∘ₗ LinearMap.proj v

@[simp] theorem molecularVel_apply (c : V → EuclideanSpace ℝ (Fin 3)) (S : V → ScrewSpace ℝ 2)
    (v : V) : molecularVel c S v = toLp 2 (screwVel (S v) (ofLp (c v))) := by
  simp only [molecularVel, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    screwVelL_apply]
  rfl

theorem ofLp_molecularVel_apply (c : V → EuclideanSpace ℝ (Fin 3)) (S : V → ScrewSpace ℝ 2)
    (v : V) : ofLp (molecularVel c S v) = screwVel (S v) (ofLp (c v)) := by
  rw [molecularVel_apply, WithLp.ofLp_toLp]

/-! ## `Φ` sends motions to motions (`molecularVel_mem_ker`)

The real inner product on `EuclideanSpace ℝ (Fin 3)` is the dot product of the underlying vectors,
so the derivative `⟪c u − c v, Φ u − Φ v⟫` of the length of a bar is computed by the identities of
the cross product of `ScrewVelocity.lean`. -/

/-- The real inner product on `EuclideanSpace ℝ (Fin 3)` is the dot product of the underlying
`Fin 3 → ℝ` vectors. -/
theorem euclidean_inner_eq_dotProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ⟪a, b⟫_ℝ = ofLp a ⬝ᵥ ofLp b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, star_trivial]

/-- **A screw in the span of a hinge has a velocity field vanishing at the centres of its ends** (a
step of `thm:molecular-iff-square-bar-joint`): for a screw `D` in the span of the supporting
extensor of the molecular framework at a link `e` from `u` to `v`, whose selector gives `e` its ends
(`hends`), the velocity field of `D` vanishes at `c u` and at `c v`. The hinge is the line through
the two centres, in whichever order `ends` gives them (`screwVel_eq_zero_of_mem_span`,
`lem:screw-velocity-line`). -/
theorem screwVel_eq_zero_of_link {G : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)} {D : ScrewSpace ℝ 2} {e : β} {u v : V}
    (hcons : D ∈ Submodule.span ℝ {(molecularOfCentres G ends c).supportExtensor e})
    (hends : G.IsLink e (ends e).1 (ends e).2) (hlink : G.IsLink e u v) :
    screwVel D (ofLp (c u)) = 0 ∧ screwVel D (ofLp (c v)) = 0 := by
  rw [molecularOfCentres_supportExtensor] at hcons
  obtain ⟨h1, h2⟩ := screwVel_eq_zero_of_mem_span hcons
  rcases hlink.eq_and_eq_or_eq_and_eq hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv]; exact ⟨h1, h2⟩
  · rw [hu, hv]; exact ⟨h2, h1⟩

/-- **`Φ` sends motions to motions** (a step of `thm:molecular-iff-square-bar-joint`): the velocity
assignment `Φ S` of an infinitesimal motion `S` of the molecular framework is a motion of the
bar-joint framework on the square graph `G²`, i.e. lies in `ker R(G², c)`.

`G'` is a multigraph with an edge between distinct `u` and `v` iff `G.Adj u v` (`hshadow`), and
`ends` gives each link of `G'` its ends (`hends`). Neither minimum degree nor general position is
needed here; they enter for injectivity and surjectivity.

Every edge `xy` of `G²` lies in a closed neighbourhood `N[w]` (`lem:square-cliques`). The hinge
constraints at edges of `G'` that join `w` to `x` and to `y` give `vel_{S x}(c x) = vel_{S w}(c x)`
and `vel_{S y}(c y) = vel_{S w}(c y)` (`screwVel_eq_zero_of_link`), so the derivative of the length
of the bar `xy` is `⟪c x − c y, vel_{S w}(c x) − vel_{S w}(c y)⟫`, which vanishes as the velocity
field of `S w` is an infinitesimal isometry (`dotProduct_screwVel_sub`). -/
theorem molecularVel_mem_ker {G : SimpleGraph V} {G' : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)}
    (hshadow : ∀ u v, u ≠ v → ((∃ e, G'.IsLink e u v) ↔ G.Adj u v))
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    {S : V → ScrewSpace ℝ 2}
    (hmem : S ∈ (molecularOfCentres G' ends c).infinitesimalMotions) :
    molecularVel c S ∈ LinearMap.ker (G.square.RigidityMap c) := by
  have hIM : (molecularOfCentres G' ends c).IsInfinitesimalMotion S := hmem
  rw [LinearMap.mem_ker]
  ext ⟨e, he⟩
  induction e with
  | h x y =>
    have hadj : G.square.Adj x y := he
    obtain ⟨w, hxw, hyw⟩ := G.exists_mem_closedNeighborSet_of_square_adj hadj
    rw [mem_closedNeighborSet] at hxw hyw
    -- On `z ∈ N[w]`, body `z`'s velocity at `c z` agrees with body `w`'s.
    have agree : ∀ z, (z = w ∨ G.Adj w z) →
        screwVel (S z) (ofLp (c z)) = screwVel (S w) (ofLp (c z)) := by
      rintro z (rfl | hadjz)
      · rfl
      · obtain ⟨e', hlink⟩ := (hshadow w z hadjz.ne).mpr hadjz
        have hcons : S w - S z ∈
            Submodule.span ℝ {(molecularOfCentres G' ends c).supportExtensor e'} :=
          hIM e' w z hlink
        obtain ⟨_, h2⟩ := screwVel_eq_zero_of_link hcons (hends e' w z hlink) hlink
        rw [screwVel_sub_screw, sub_eq_zero] at h2
        exact h2.symm
    change G.square.RigidityMap c (molecularVel c S) ⟨s(x, y), he⟩ = 0
    rw [rigidityMap_apply G.square c (molecularVel c S) x y he, euclidean_inner_eq_dotProduct,
      ofLp_sub, ofLp_sub, ofLp_molecularVel_apply, ofLp_molecularVel_apply, agree x hxw,
      agree y hyw]
    exact dotProduct_screwVel_sub (S w) (ofLp (c x)) (ofLp (c y))

/-! ## The dictionary isomorphism `Φ` (`thm:molecular-iff-square-bar-joint`)

For a graph of minimum degree at least two and a placement in general position up to order four,
`Φ = molecularVel c` restricts to a linear isomorphism from the motions of the molecular framework
onto those of the bar-joint framework on `(G², c)`, so the two motion spaces have the same
dimension. Injectivity is `eq_zero_of_screwVel_eq_zero` (`lem:screw-determination`) at the centres
of a body and two of its neighbours. Surjectivity builds the screw of each body from the velocities
on its closed neighbourhood, a clique of `G²` (`existsUnique_screwVel_eq`,
`lem:screw-determination`), and checks the hinge constraints by `lem:screw-velocity-line`. -/

/-- **`Φ` is injective on the motions** (a step of `thm:molecular-iff-square-bar-joint`). Let `S` be
a motion with `Φ S = 0`. The velocity field of the screw `S v` of a body vanishes at `c v`, and at
the centre of each neighbour `u`: `S v − S u` is in the span of their hinge, so its velocity field
vanishes at `c u` (`screwVel_eq_zero_of_link`), and that of `S u` does. Minimum degree two gives two
neighbours, and general position makes the three centres non-collinear, so `S v = 0`
(`lem:screw-determination`). -/
theorem eq_zero_of_molecularVel_eq_zero {G : SimpleGraph V} {G' : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)} [Fintype V] [DecidableRel G.Adj]
    (hshadow : ∀ u v, u ≠ v → ((∃ e, G'.IsLink e u v) ↔ G.Adj u v))
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    (hmin : ∀ v, 2 ≤ G.degree v) (hgp : IsGeneralPositionPlacement c) {S : V → ScrewSpace ℝ 2}
    (hmem : S ∈ (molecularOfCentres G' ends c).infinitesimalMotions)
    (h0 : molecularVel c S = 0) : S = 0 := by
  have hIM : (molecularOfCentres G' ends c).IsInfinitesimalMotion S := hmem
  have hvel : ∀ w, screwVel (S w) (ofLp (c w)) = 0 := by
    intro w
    rw [← ofLp_molecularVel_apply]
    simp [congrFun h0 w]
  funext v
  have h2 : 1 < (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree]; have := hmin v; omega
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁u₂⟩ := Finset.one_lt_card_iff.mp h2
  rw [mem_neighborFinset] at hu₁ hu₂
  have hkill : ∀ u, G.Adj v u → screwVel (S v) (ofLp (c u)) = 0 := by
    intro u hadj
    obtain ⟨e, hlink⟩ := (hshadow v u hadj.ne).mpr hadj
    obtain ⟨-, hcu⟩ := screwVel_eq_zero_of_link (hIM e v u hlink) (hends e v u hlink) hlink
    rw [screwVel_sub_screw, hvel u, sub_zero] at hcu
    exact hcu
  refine eq_zero_of_screwVel_eq_zero (q := ![ofLp (c v), ofLp (c u₁), ofLp (c u₂)]) ?_ ?_
  · exact hgp.linearIndependent_vsub_pair hu₁.ne hu₂.ne hu₁u₂
  · intro i
    fin_cases i
    · exact hvel v
    · exact hkill u₁ hu₁
    · exact hkill u₂ hu₂

/-- **The converse of `screwVel_eq_zero_of_link`** (a step of `thm:molecular-iff-square-bar-joint`):
a screw whose velocity field vanishes at the distinct centres of the ends of a link `e` lies in the
span of the hinge at `e`, by `lem:screw-velocity-line` in whichever order `ends` gives the ends. -/
theorem mem_span_supportExtensor_of_link {G' : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)} {D : ScrewSpace ℝ 2} {e : β} {u v : V} (huv : c u ≠ c v)
    (hends : G'.IsLink e (ends e).1 (ends e).2) (hlink : G'.IsLink e u v)
    (h1 : screwVel D (ofLp (c u)) = 0) (h2 : screwVel D (ofLp (c v)) = 0) :
    D ∈ Submodule.span ℝ {(molecularOfCentres G' ends c).supportExtensor e} := by
  have hne : ofLp (c u) ≠ ofLp (c v) := fun h => huv (by
    have := congrArg (toLp 2) h; rwa [toLp_ofLp, toLp_ofLp] at this)
  rw [molecularOfCentres_supportExtensor]
  rcases hlink.eq_and_eq_or_eq_and_eq hends with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [← hu, ← hv]
    exact (screwVel_eq_zero_iff_mem_span hne D).mp ⟨h1, h2⟩
  · rw [← hu, ← hv]
    exact (screwVel_eq_zero_iff_mem_span hne.symm D).mp ⟨h2, h1⟩

/-- **A motion of the bar-joint framework on `G²` determines a screw on each closed neighbourhood**
(a step of `thm:molecular-iff-square-bar-joint`): for a graph of minimum degree at least two, a
placement in general position and a vertex `v`, the velocities `y` on the clique `N[v]` of `G²`
(`lem:square-cliques`) satisfy the bar constraint on every pair, so some screw has the velocity
`y u` at `c u` for every `u` in `N[v]` (`existsUnique_screwVel_eq`, `lem:screw-determination`). -/
theorem exists_screwVel_eq_on_closedNeighborSet [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {c : V → EuclideanSpace ℝ (Fin 3)} (hgp : IsGeneralPositionPlacement c)
    (hmin : ∀ v, 2 ≤ G.degree v) {y : V → EuclideanSpace ℝ (Fin 3)}
    (hy : G.square.RigidityMap c y = 0) (v : V) :
    ∃ Sv : ScrewSpace ℝ 2, ∀ u, (u = v ∨ G.Adj v u) → screwVel Sv (ofLp (c u)) = ofLp (y u) := by
  have h2 : 1 < (G.neighborFinset v).card := by
    rw [G.card_neighborFinset_eq_degree]; have := hmin v; omega
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁u₂⟩ := Finset.one_lt_card_iff.mp h2
  rw [mem_neighborFinset] at hu₁ hu₂
  have hbar : ∀ i j : ↥(G.closedNeighborSet v),
      (ofLp (c i.val) - ofLp (c j.val)) ⬝ᵥ (ofLp (y i.val) - ofLp (y j.val)) = 0 := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · simp
    · have hadj : G.square.Adj i.val j.val :=
        G.isClique_closedNeighborSet_square v i.2 j.2 (fun h => hij (Subtype.ext h))
      have hcomp : G.square.RigidityMap c y ⟨s(i.val, j.val), hadj⟩ = 0 := by
        have := congrFun hy ⟨s(i.val, j.val), hadj⟩; simpa using this
      rw [rigidityMap_apply G.square c y i.val j.val hadj, euclidean_inner_eq_dotProduct,
        ofLp_sub, ofLp_sub] at hcomp
      exact hcomp
  obtain ⟨Sv, hSv, -⟩ := existsUnique_screwVel_eq
    (p := fun i : ↥(G.closedNeighborSet v) => ofLp (c i.val))
    (x := fun i => ofLp (y i.val))
    (i₀ := ⟨v, G.self_mem_closedNeighborSet v⟩)
    (i₁ := ⟨u₁, mem_closedNeighborSet.mpr (Or.inr hu₁)⟩)
    (i₂ := ⟨u₂, mem_closedNeighborSet.mpr (Or.inr hu₂)⟩)
    (hgp.linearIndependent_vsub_pair hu₁.ne hu₂.ne hu₁u₂)
    (fun _ hj0 hj1 hj2 => hgp.linearIndependent_vsub_triple
      (Ne.symm fun h => hj0 (Subtype.ext h)) (Ne.symm fun h => hj1 (Subtype.ext h))
      (Ne.symm fun h => hj2 (Subtype.ext h)) hu₁.ne hu₂.ne hu₁u₂)
    hbar
  exact ⟨Sv, fun u hu => hSv ⟨u, mem_closedNeighborSet.mpr hu⟩⟩

/-- **`Φ` is onto `ker R(G², c)`** (a step of `thm:molecular-iff-square-bar-joint`). Each closed
neighbourhood `N[v]` is a clique of `G²` (`lem:square-cliques`), so a motion `x` of the bar-joint
framework has on it velocities that satisfy the bar constraint on every pair, and these are those of
a screw `S v` (`exists_screwVel_eq_on_closedNeighborSet`, `lem:screw-determination`). The screws of
adjacent bodies agree at the centres of both, so their difference is in the span of the hinge
(`lem:screw-velocity-line`), and `S` is a motion of the molecular framework with `Φ S = x`. -/
theorem exists_molecularVel_eq {G : SimpleGraph V} {G' : Graph V β} {ends : β → V × V}
    {c : V → EuclideanSpace ℝ (Fin 3)} [Fintype V] [DecidableRel G.Adj]
    (hshadow : ∀ u v, u ≠ v → ((∃ e, G'.IsLink e u v) ↔ G.Adj u v))
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    (hmin : ∀ v, 2 ≤ G.degree v) (hgp : IsGeneralPositionPlacement c)
    {x : V → EuclideanSpace ℝ (Fin 3)} (hx : x ∈ LinearMap.ker (G.square.RigidityMap c)) :
    ∃ S ∈ (molecularOfCentres G' ends c).infinitesimalMotions, molecularVel c S = x := by
  rw [LinearMap.mem_ker] at hx
  choose S hS using fun v => exists_screwVel_eq_on_closedNeighborSet hgp hmin hx v
  refine ⟨S, ?_, ?_⟩
  · have H : (molecularOfCentres G' ends c).IsInfinitesimalMotion S := by
      intro e u w hlink
      change S u - S w ∈ Submodule.span ℝ {(molecularOfCentres G' ends c).supportExtensor e}
      rcases eq_or_ne u w with rfl | hne
      · rw [sub_self]; exact Submodule.zero_mem _
      · have hadj : G.Adj u w := (hshadow u w hne).mp ⟨e, hlink⟩
        have huvc : c u ≠ c w := fun h => hne (hgp.injective h)
        have h1 : screwVel (S u - S w) (ofLp (c u)) = 0 := by
          simp only [screwVel_sub_screw, hS u u (Or.inl rfl), hS w u (Or.inr hadj.symm), sub_self]
        have h2 : screwVel (S u - S w) (ofLp (c w)) = 0 := by
          simp only [screwVel_sub_screw, hS u w (Or.inr hadj), hS w w (Or.inl rfl), sub_self]
        exact mem_span_supportExtensor_of_link huvc (hends e u w hlink) hlink h1 h2
    exact H
  · funext v
    rw [molecularVel_apply, hS v v (Or.inl rfl), toLp_ofLp]

/-- **Molecular frameworks and bar-joint frameworks on the square**
(`thm:molecular-iff-square-bar-joint`; Whiteley's equivalence, at one placement). For a graph `G` of
minimum degree at least two and a placement `c` in general position up to order four,
`Φ = molecularVel c` is a linear isomorphism from the motions `Z_mol` of the molecular framework on
`G'` at `c` onto those of the bar-joint framework on `(G², c)`, so the two motion spaces have the
same dimension (whence `rank R(G², c) = 3|V| − dim Z_mol`, by rank–nullity). `G'` is a multigraph
with an edge between distinct `u` and `v` iff `G.Adj u v` (`hshadow`), and `ends` gives each link of
`G'` its ends (`hends`). -/
theorem molecular_finrank_motions_eq_square_ker {G : SimpleGraph V} {G' : Graph V β}
    {ends : β → V × V} {c : V → EuclideanSpace ℝ (Fin 3)} [Fintype V] [DecidableRel G.Adj]
    (hshadow : ∀ u v, u ≠ v → ((∃ e, G'.IsLink e u v) ↔ G.Adj u v))
    (hends : ∀ e u v, G'.IsLink e u v → G'.IsLink e (ends e).1 (ends e).2)
    (hmin : ∀ v, 2 ≤ G.degree v) (hgp : IsGeneralPositionPlacement c) :
    Module.finrank ℝ (molecularOfCentres G' ends c).infinitesimalMotions
      = Module.finrank ℝ (LinearMap.ker (G.square.RigidityMap c)) := by
  have hwd : ∀ S ∈ (molecularOfCentres G' ends c).infinitesimalMotions,
      molecularVel c S ∈ LinearMap.ker (G.square.RigidityMap c) :=
    fun S hS => molecularVel_mem_ker hshadow hends hS
  let Φ : ↥(molecularOfCentres G' ends c).infinitesimalMotions →ₗ[ℝ]
      ↥(LinearMap.ker (G.square.RigidityMap c)) :=
    ((molecularVel c).domRestrict (molecularOfCentres G' ends c).infinitesimalMotions).codRestrict
      (LinearMap.ker (G.square.RigidityMap c)) fun S => hwd S.val S.2
  refine (LinearEquiv.ofBijective Φ ⟨?_, ?_⟩).finrank_eq
  · rw [injective_iff_map_eq_zero]
    intro S hS0
    have hval : molecularVel c S.val = 0 := congrArg Subtype.val hS0
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact eq_zero_of_molecularVel_eq_zero hshadow hends hmin hgp S.2 hval
  · intro y
    obtain ⟨S, hSmem, hSeq⟩ := exists_molecularVel_eq hshadow hends hmin hgp y.2
    exact ⟨⟨S, hSmem⟩, Subtype.ext hSeq⟩

end CombinatorialRigidity.Molecular
