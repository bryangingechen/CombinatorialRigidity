/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.ScrewVelocity
import CombinatorialRigidity.SquareGraph
import CombinatorialRigidity.Framework
import CombinatorialRigidity.GeneralPositionPlacement

/-!
# The square-graph dictionary (`thm:molecular-iff-square-bar-joint`)

Phase 25, leaf W4 (`notes/Phase25-design.md` §2.3). Katoh–Tanigawa 2011 (p. 650, p. 671) model a
molecule --- atoms as bodies, covalent bonds as hinges --- as a bar-joint framework on the square
graph `G²` exactly when it is a body-hinge framework of `G` whose hinges at each atom meet at the
atom's centre. This file builds the underlying **dictionary map** `Φ` between the two motion
spaces, at a placement `c : V → ℝ³` of the atom centres.

* The molecular framework `molecularOfCentres G' ends c` is the affine-hinge body-hinge framework
  (`BodyHingeFramework.ofHinge`) whose hinge at each edge `e = uv` is the line through the two
  endpoint centres --- its supporting `2`-extensor is `ĉ(u) ∨ ĉ(v)`, the join of the homogenized
  centres (`def:hinge-concurrent`).
* `Φ = molecularVel c` sends a screw assignment `S : V → ScrewSpace ℝ 2` to the joint velocity
  assignment `v ↦ vel_{S v}(c v)`, an `ℝ`-linear map into the bar-joint framework space of `G²`.

This slice delivers `Φ` and its **well-definedness**: `Φ` carries infinitesimal motions of the
molecular framework into `ker R(G², c)` (`molecularVel_mem_ker`). Every edge of `G²` lies inside a
closed neighbourhood `N[w]` (`lem:square-cliques`); on such an edge the two endpoint velocities
agree with those of body `w`'s single screw (the hinge constraint plus the line characterization
`lem:screw-velocity-line`, brick (2)), and body `w`'s screw is infinitesimally isometric
(brick (1)), so the bar-length derivative vanishes. Injectivity, surjectivity, and the resulting
`finrank` equality (the remainder of `thm:molecular-iff-square-bar-joint`) are follow-up slices.

See `notes/Phase25.md` and `notes/Phase25-design.md` §2.3, §3 (leaf W4) for the phase plan.
-/

open scoped Matrix InnerProductSpace
open WithLp SimpleGraph

namespace CombinatorialRigidity.Molecular

variable {V β : Type*}

/-! ## The molecular framework from a placement of centres (`def:hinge-concurrent`) -/

/-- **The molecular (hinge-concurrent) framework** on a multigraph `G` with endpoint selector
`ends` and a placement `c : V → ℝ³` of body centres (`def:hinge-concurrent`): the affine-hinge
body-hinge framework whose hinge at each edge `e` is the line through the two endpoint centres
`c (ends e).1`, `c (ends e).2`. Its supporting `2`-extensor is the join of the homogenized
endpoint centres, so every hinge incident to a body `v` passes through `c v` --- Katoh–Tanigawa's
hinge-concurrency (p. 671). When two centres coincide the join degenerates to zero (a welded
hinge). -/
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

/-- The **screw velocity as a linear map in the screw** (fixing the base point `x`):
`S ↦ vel_S(x) = ω_S ⨯₃ x + t_S`. Both graded coordinate maps are linear, so this is a genuine
linear map `ScrewSpace ℝ 2 →ₗ[ℝ] ℝ³`. -/
noncomputable def screwVelL (x : Fin 3 → ℝ) : ScrewSpace ℝ 2 →ₗ[ℝ] (Fin 3 → ℝ) :=
  crossProduct.flip x ∘ₗ screwOmega + screwTau

@[simp] theorem screwVelL_apply (x : Fin 3 → ℝ) (S : ScrewSpace ℝ 2) :
    screwVelL x S = screwVel S x := by
  simp only [screwVelL, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.flip_apply,
    screwVel_apply]

/-- **The dictionary map `Φ`** (`thm:molecular-iff-square-bar-joint`): sends a screw assignment
`S : V → ScrewSpace ℝ 2` (a molecular motion) to the joint-velocity assignment
`v ↦ vel_{S v}(c v)`, a bar-joint framework motion of `G²`. Linear in `S`. The codomain uses the
`EuclideanSpace ℝ (Fin 3)` view of `ℝ³`, so the velocity `vel_{S v}(c v) : Fin 3 → ℝ` is carried
across the `WithLp` boundary by `toLp`. -/
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

/-! ## `Φ` lands in the bar-joint motions of `G²` (`molecularVel_mem_ker`)

The real inner product on `EuclideanSpace ℝ (Fin 3)` is the dot product of the underlying vectors,
which lets a bar-length-derivative equation `⟪c u − c v, Φ u − Φ v⟫ = 0` be discharged by the
cross-product identities of `ScrewVelocity.lean`. -/

/-- The real inner product on `EuclideanSpace ℝ (Fin 3)` is the dot product of the underlying
`Fin 3 → ℝ` vectors. -/
theorem euclidean_inner_eq_dotProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ⟪a, b⟫_ℝ = ofLp a ⬝ᵥ ofLp b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, star_trivial]

/-- **Endpoint velocity agreement.** For a screw `D` in the span of a molecular hinge's supporting
extensor `C(p(e))` and a link `e = uv`, the velocity field of `D` vanishes at both endpoint
centres `c u`, `c v`. (The hinge is the line through the endpoint centres, and `lem:screw-velocity-
line` says the rotation about it fixes both; the endpoint selector `ends` only orders that pair.)
-/
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

/-- **The dictionary map is well-defined** (`thm:molecular-iff-square-bar-joint`, forward
half): the joint-velocity assignment `Φ S` of any infinitesimal molecular motion `S` is a
bar-joint motion of the square graph `G²`, i.e. lies in `ker R(G², c)`.

`G'` is the multigraph carrier of `G` (`hshadow`: an edge exists between distinct `u, v` iff
`G.Adj u v`) with endpoint selector `ends` (`hends`). No minimum-degree or general-position
hypothesis is needed for well-definedness --- those enter for injectivity/surjectivity.

Every edge `xy` of `G²` lies inside a closed neighbourhood `N[w]` (`lem:square-cliques`); the
hinge constraints on the `G`-edges `wx`, `wy` make `vel_{S x}(c x) = vel_{S w}(c x)` and
`vel_{S y}(c y) = vel_{S w}(c y)` (endpoint agreement), so the bar-length derivative on `xy`
reduces to `⟪c x − c y, vel_{S w}(c x) − vel_{S w}(c y)⟫`, which vanishes because body `w`'s
velocity field is infinitesimally isometric (brick (1)). -/
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

With minimum degree at least two and a general-position placement, `Φ = molecularVel c` restricts to
a linear isomorphism between the molecular motions of `G` and the bar-joint motions of `(G², c)`, so
the two motion spaces have equal dimension. Injectivity is the screw-determination kill lemma
(brick (3), `eq_zero_of_screwVel_eq_zero`) applied at each body's `≥ 3` non-collinear neighbours;
surjectivity builds each body's screw from the pairwise-constrained velocity assignment on its
closed-neighbourhood clique (brick (4), `existsUnique_screwVel_eq`) and verifies the hinge
constraints through the line characterization (brick (2)). -/

/-- **`Φ` is injective on molecular motions** (`thm:molecular-iff-square-bar-joint`, injective
half). A molecular motion `S` with `Φ S = 0` has each body's velocity field vanishing at that
body's centre, and — via the hinge line characterization (`lem:screw-velocity-line`) plus that
vanishing at each neighbour — at each neighbour's centre too; minimum degree two gives three such
points, non-collinear by general position, so `lem:screw-determination` (kill half) forces every
screw to zero. -/
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

/-- **Reverse of `screwVel_eq_zero_of_link`.** A screw whose velocity field vanishes at both centres
of a link `e = uv` (with distinct centres) lies in the span of the hinge's supporting extensor — the
line characterization (`lem:screw-velocity-line`) read at whichever endpoint order `ends` picks. -/
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

/-- **A bar-joint motion of `G²` determines a screw on each closed neighbourhood.** For a
general-position placement and a vertex `v` of degree at least two, the velocity assignment `y`
restricted to the `G²`-clique `N[v]` (`lem:square-cliques`) is pairwise bar-constrained, so
`lem:screw-determination` (brick (4)) yields a screw realizing it on all of `N[v]`. -/
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

/-- **`Φ` is surjective onto `ker R(G², c)`** (`thm:molecular-iff-square-bar-joint`, surjective
half). Each closed neighbourhood `N[v]` is a `G²`-clique (`lem:square-cliques`), so a bar-joint
motion `x` restricts to a pairwise-constrained velocity assignment there, determining a body screw
`S v` (`lem:screw-determination`); adjacent bodies' screws agree at both shared endpoint centres, so
their difference is a hinge multiple (`lem:screw-velocity-line`) and `S` is a molecular motion with
`Φ S = x`. -/
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
          rw [screwVel_sub_screw, hS u u (Or.inl rfl), hS w u (Or.inr hadj.symm), sub_self]
        have h2 : screwVel (S u - S w) (ofLp (c w)) = 0 := by
          rw [screwVel_sub_screw, hS u w (Or.inr hadj), hS w w (Or.inl rfl), sub_self]
        exact mem_span_supportExtensor_of_link huvc (hends e u w hlink) hlink h1 h2
    exact H
  · funext v
    rw [molecularVel_apply, hS v v (Or.inl rfl), toLp_ofLp]

/-- **Molecule ⇔ bar-joint of the square** (`thm:molecular-iff-square-bar-joint`). For a graph of
minimum degree at least two and a placement in general position up to order four, the dictionary map
`Φ = molecularVel c` is a linear isomorphism from the molecular motions of `(G, c)` onto the
bar-joint motions of `(G², c)`, so the two motion spaces have equal dimension (whence
`rank R(G², c) = 3|V| − dim Z_mol(G, c)` by rank–nullity). -/
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
    have hval : molecularVel c S.val = 0 := by
      have := congrArg Subtype.val hS0
      simpa [Φ, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] using this
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact eq_zero_of_molecularVel_eq_zero hshadow hends hmin hgp S.2 hval
  · intro y
    obtain ⟨S, hSmem, hSeq⟩ := exists_molecularVel_eq hshadow hends hmin hgp y.2
    exact ⟨⟨S, hSmem⟩, Subtype.ext (by
      simpa [Φ, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] using hSeq)⟩

end CombinatorialRigidity.Molecular
