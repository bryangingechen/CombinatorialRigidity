/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Feasible
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Collineation
public import CombinatorialRigidity.Molecular.Molecule.Pencil.Grade.Carrier
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Steering and lifting nondegenerate realizations in every dimension

The four nodes of `blueprint/src/chapter/pencil-d.tex` that open `sec:pencil-d-lift`:

* `lem:pencil-d-steer`: the dimension-three chart `steerPoint`, `steerNormal` on the parameters
  `Γ(G)` (`PencilSeed.ofGamma`) is polynomial (`isPolyFun_steerPoint`, `isPolyFun_steerNormal`), the
  set `steerSet` (`U(G)`) of its nondegenerate points is Zariski-open (`isZariskiOpen_steerSet`),
  every nondegenerate realization is in it up to scalars (`exists_mem_steerSet_of_isNondeg`), and it
  is nonempty exactly when `G` is nondegeneracy-feasible (`steerSet_nonempty_iff`);
  `HoldsGenerally` is the remark's "general".
* `def:pencil-d-lift`: the lift of a dimension-three realization by maps on its bodies and forms on
  its planes (`liftVec`, `liftSpace`, `IsTrivialLift`, `liftMaps`, `liftNormal`, `liftSubspace`).
* `lem:pencil-d-lift-realization`: a lift is a nondegenerate realization
  (`IsNondegPencilPlaneRealization.lift`), `L(b⁰)` does not depend on `Π⁰` (`mem_liftMaps_iff`), and
  scaling or transporting by an automorphism keeps `𝓛` and the rank (`liftSmul_mem_liftSpace_iff`,
  `liftTransport_mem_liftSpace_iff`, `finrank_span_rigidityRows_ofNormals_smul`,
  `finrank_liftNormal_transport`).
* `def:pencil-d-lift-attains`: `LiftAttains`.
-/

@[expose] public section

open scoped Matrix
open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-! ## A parametrization in dimension three -/

/-- **The parameters of the chart at a point `s ∈ Γ(G)`** (`lem:pencil-d-steer`): at every body
`v`, the vector `m_v` (index `0`), the auxiliary vectors of the three hub slots (`1`–`3`) and of the
three neighbour slots (`4`–`6`). -/
def PencilSeed.ofGamma (s : α × Fin 7 × Fin 4 → K) : PencilSeed K α where
  hubNormal v i := s (v, 0, i)
  fillHub v j i := s (v, ⟨j + 1, by omega⟩, i)
  fillNbr v j i := s (v, ⟨j + 4, by omega⟩, i)

/-- The point of `Γ(G)` of given parameters. -/
def PencilSeed.toGamma (seed : PencilSeed K α) (p : α × Fin 7 × Fin 4) : K :=
  if (p.2.1 : ℕ) = 0 then seed.hubNormal p.1 p.2.2
  else if h : (p.2.1 : ℕ) < 4 then seed.fillHub p.1 ⟨p.2.1 - 1, by omega⟩ p.2.2
  else seed.fillNbr p.1 ⟨p.2.1 - 4, by omega⟩ p.2.2

theorem PencilSeed.ofGamma_toGamma (seed : PencilSeed K α) :
    PencilSeed.ofGamma seed.toGamma = seed := by
  obtain ⟨hn, fh, fn⟩ := seed
  simp only [PencilSeed.ofGamma, PencilSeed.toGamma, PencilSeed.mk.injEq]
  refine ⟨rfl, ?_, ?_⟩ <;> funext v j i <;> fin_cases j <;> rfl

/-- **The points `b⁰_v(s)`** of the chart on `Γ(G)` (`lem:pencil-d-steer`). -/
noncomputable def steerPoint (hubSel : α → Fin 3 → Option α) (s : α × Fin 7 × Fin 4 → K) :
    α → Fin 4 → K :=
  pencilChartPoint (PencilSeed.ofGamma s) hubSel

/-- **The vectors `n_v(s)`** of the chart on `Γ(G)` (`lem:pencil-d-steer`). -/
noncomputable def steerNormal (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β)
    (s : α × Fin 7 × Fin 4 → K) : α → Fin 4 → K :=
  pencilChartNormal (PencilSeed.ofGamma s) hubSel nbrSel G

/-- **The points are polynomials in `s`** (`lem:pencil-d-steer`). -/
theorem isPolyFun_steerPoint (hubSel : α → Fin 3 → Option α) (v : α) (i : Fin 4) :
    IsPolyFun fun s : α × Fin 7 × Fin 4 → K => steerPoint hubSel s v i := by
  have hslot : ∀ j i, IsPolyFun fun s : α × Fin 7 × Fin 4 → K =>
      hubSlotNormal (PencilSeed.ofGamma s) hubSel v j i := by
    intro j i
    rcases h : hubSel v j with _ | w <;> simp only [hubSlotNormal, h] <;> exact isPolyFun_apply _
  exact isPolyFun_cross₃ (hslot 0) (hslot 1) (hslot 2) i

/-- **The vectors `n_v` are polynomials in `s`** (`lem:pencil-d-steer`). -/
theorem isPolyFun_steerNormal (hubSel nbrSel : α → Fin 3 → Option α) (G : Graph α β) (v : α)
    (i : Fin 4) :
    IsPolyFun fun s : α × Fin 7 × Fin 4 → K => steerNormal hubSel nbrSel G s v i := by
  by_cases hv : G.PencilHub v
  · simp only [steerNormal, pencilChartNormal_of_pencilHub _ _ _ hv]
    exact isPolyFun_apply _
  · simp only [steerNormal, pencilChartNormal_of_not_pencilHub _ _ _ hv]
    have hslot : ∀ j i, IsPolyFun fun s : α × Fin 7 × Fin 4 → K =>
        nbrSlotPoint (PencilSeed.ofGamma s) hubSel nbrSel v j i := by
      intro j i
      rcases h : nbrSel v j with _ | w <;> simp only [nbrSlotPoint, h]
      · exact isPolyFun_apply _
      · exact isPolyFun_steerPoint hubSel w i
    exact isPolyFun_cross₃ (hslot 0) (hslot 1) (hslot 2) i

/-- **`b⁰_w · n_v = 0` on every closed neighbourhood** (`lem:pencil-d-steer`), at every `s`. -/
theorem steerPoint_dotProduct_steerNormal {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    (s : α × Fin 7 × Fin 4 → K) {v w : α} (hw : w ∈ G.closedNbhd v) :
    steerPoint hubSel s w ⬝ᵥ steerNormal hubSel nbrSel G s v = 0 := by
  by_cases hv : G.PencilHub v
  · rw [steerNormal, pencilChartNormal_of_pencilHub _ _ _ hv]
    refine dotProduct_pencilChartPoint_hubNormal_of_mem_closedHubNbhd _ (hHubSel w) ⟨hv, ?_⟩
    rcases hw with rfl | ⟨e, he⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he.symm⟩
  · exact dotProduct_pencilChartPoint_pencilChartNormal_of_mem_closedNbhd _ hv (hNbrSel v hv) hw

/-- **The set `U(G)`** (`lem:pencil-d-steer`): the parameters at which every `b⁰_v` and `n_v`,
`v ∈ V(G)`, is nonzero and `(b⁰, n^⊥)` is a nondegenerate realization in dimension three. -/
def steerSet (G : Graph α β) (hubSel nbrSel : α → Fin 3 → Option α) :
    Set (α × Fin 7 × Fin 4 → K) :=
  {s | (∀ v ∈ V(G), steerPoint hubSel s v ≠ 0 ∧ steerNormal hubSel nbrSel G s v ≠ 0) ∧
    ∃ F : BodyHingeFramework K 2 α β, IsNondegPencilPlaneRealization G F (steerPoint hubSel s)
      (fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v))}

/-- `U(G)` by its conditions, each an independence of polynomial vectors. -/
theorem mem_steerSet_iff {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    {s : α × Fin 7 × Fin 4 → K} :
    s ∈ steerSet G hubSel nbrSel ↔
      (∀ v ∈ V(G), steerPoint hubSel s v ≠ 0) ∧
      (∀ v ∈ V(G), steerNormal hubSel nbrSel G s v ≠ 0) ∧
      (∀ u v, G.Adj u v → LinearIndependent K ![steerPoint hubSel s u, steerPoint hubSel s v]) ∧
      (∀ v ∈ V(G), LinearIndepOn K (steerNormal hubSel nbrSel G s) (G.closedHubNbhd v)) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K (steerPoint hubSel s) (G.closedNbhd v)) := by
  constructor
  · rintro ⟨hne, F, hreal, hcond⟩
    obtain ⟨h1, h2, h3⟩ := (pencilNondegConditions_dotPerp_iff fun v hv => (hne v hv).2).1 hcond
    exact ⟨fun v hv => (hne v hv).1, fun v hv => (hne v hv).2,
      fun u v ⟨e, he⟩ => h1 e u v he, h2, h3⟩
  · rintro ⟨hb, hn, h1, h2, h3⟩
    refine ⟨fun v hv => ⟨hb v hv, hn v hv⟩, ?_⟩
    obtain ⟨F, hF⟩ := exists_hasPencilPlaneRealization (k := 2) (G := G) (β := β)
      (b := steerPoint hubSel s) (plane := fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v))
      hb (fun e u v he => h1 u v ⟨e, he⟩)
      (fun v hv => finrank_dotPerp_span_singleton_of_ne_zero (hn v hv))
      (fun v _ w hw => mem_dotPerp_span_singleton.2
        (steerPoint_dotProduct_steerNormal hHubSel hNbrSel s hw))
    exact ⟨F, hF, (pencilNondegConditions_dotPerp_iff hn).2
      ⟨fun e u v he => h1 u v ⟨e, he⟩, h2, h3⟩⟩


/-- **`U(G)` is Zariski-open** (`lem:pencil-d-steer`). -/
theorem isZariskiOpen_steerSet [Finite α] {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    IsZariskiOpen (steerSet (K := K) G hubSel nbrSel) := by
  have heq : steerSet (K := K) G hubSel nbrSel = {s |
      (∀ v ∈ V(G), steerPoint hubSel s v ≠ 0) ∧
      (∀ v ∈ V(G), steerNormal hubSel nbrSel G s v ≠ 0) ∧
      (∀ u v, G.Adj u v → LinearIndependent K ![steerPoint hubSel s u, steerPoint hubSel s v]) ∧
      (∀ v ∈ V(G), LinearIndepOn K (steerNormal hubSel nbrSel G s) (G.closedHubNbhd v)) ∧
      (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K (steerPoint hubSel s) (G.closedNbhd v))} :=
    Set.ext fun s => mem_steerSet_iff hHubSel hNbrSel
  rw [heq]
  refine IsZariskiOpen.and ?_ (IsZariskiOpen.and ?_ (IsZariskiOpen.and ?_
    (IsZariskiOpen.and ?_ ?_)))
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
      isZariskiOpen_ne_zero (K := K) _ (isPolyFun_steerPoint hubSel v)
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
      isZariskiOpen_ne_zero (K := K) _ (isPolyFun_steerNormal hubSel nbrSel G v)
  · refine isZariskiOpen_forall fun u => isZariskiOpen_forall fun v => isZariskiOpen_imp _ ?_
    refine isZariskiOpen_linearIndependent_univ (fun s => ![steerPoint hubSel s u,
      steerPoint hubSel s v]) fun i j => ?_
    fin_cases i
    exacts [isPolyFun_steerPoint hubSel u j, isPolyFun_steerPoint hubSel v j]
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <|
      isZariskiOpen_linearIndependent _ (fun i j => isPolyFun_steerNormal hubSel nbrSel G i j) _
  · exact isZariskiOpen_forall fun v => isZariskiOpen_imp _ <| isZariskiOpen_imp _ <|
      isZariskiOpen_linearIndependent _ (fun i j => isPolyFun_steerPoint hubSel i j) _

/-- Well-formed parameters lie in `U(G)`. -/
theorem mem_steerSet_of_pencilChartWF {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    {s : α × Fin 7 × Fin 4 → K} (hWF : PencilChartWF G (PencilSeed.ofGamma s) hubSel nbrSel) :
    s ∈ steerSet G hubSel nbrSel := by
  refine (mem_steerSet_iff hWF.1 hWF.2.1).2 ⟨fun v _ => pencilChartPoint_ne_zero _ (hWF.2.2.1 v),
    fun v _ => ?_, fun u v ⟨e, he⟩ => hWF.2.2.2.2 e u v he,
    fun v _ => linearIndepOn_pencilChartNormal_closedHubNbhd _ (hWF.1 v) (hWF.2.2.1 v),
    fun v _ hv => linearIndepOn_pencilChartPoint_closedNbhd _ (hWF.2.1 v hv) (hWF.2.2.2.1 v hv)⟩
  by_cases hv : G.PencilHub v
  · rw [steerNormal, pencilChartNormal_of_pencilHub _ _ _ hv]
    exact hubNormal_ne_zero_of_pencilHub _ (hWF.1 v) (hWF.2.2.1 v) hv
  · exact pencilChartNormal_ne_zero_of_not_pencilHub _ hv (hWF.2.2.2.1 v hv)

/-- **Every nondegenerate realization is in the chart, up to scalars** (`lem:pencil-d-steer`). -/
theorem exists_mem_steerSet_of_isNondeg {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v))
    {F : BodyHingeFramework K 2 α β} {b0 : α → Fin 4 → K} {P0 : α → Submodule K (Fin 4 → K)}
    (hnd : IsNondegPencilPlaneRealization G F b0 P0) :
    ∃ s ∈ steerSet G hubSel nbrSel,
      (∀ v ∈ V(G), ∃ c : K, c ≠ 0 ∧ steerPoint hubSel s v = c • b0 v) ∧
      (∀ v ∈ V(G), dotPerp (K ∙ steerNormal hubSel nbrSel G s v) = P0 v) := by
  obtain ⟨n', hn'⟩ := hnd.1.exists_dotPerp
  have hreal' := hnd.1.congr_plane hn'
  have hnd' := (isNondegPencilPlaneRealization_two_iff hreal').1 ⟨hreal', hnd.2.congr_plane hn'⟩
  obtain ⟨seed, hseed, hWF, hpt, hnm⟩ :=
    exists_pencilSeed_of_nondeg_of_selectors hnd' hHubSel hNbrSel
  have hs : PencilSeed.ofGamma seed.toGamma = seed := seed.ofGamma_toGamma
  refine ⟨seed.toGamma, mem_steerSet_of_pencilChartWF (by rw [hs]; exact hWF),
    fun v hv => by simpa only [steerPoint, hs] using hpt v hv, fun v hv => ?_⟩
  rw [hn' v hv, steerNormal, hs]
  by_cases hhub : G.PencilHub v
  · rw [pencilChartNormal_of_pencilHub _ _ _ hhub, hseed]
  · obtain ⟨d, hd, hdeq⟩ := hnm v hv hhub
    rw [hdeq, Submodule.span_singleton_smul_eq hd.isUnit]

/-- **`U(G)` is nonempty exactly when `G` is nondegeneracy-feasible** (`lem:pencil-d-steer`). -/
theorem steerSet_nonempty_iff {G : Graph α β} {hubSel nbrSel : α → Fin 3 → Option α}
    (hHubSel : ∀ v, IsFin3SelectorOf (G.closedHubNbhd v) (hubSel v))
    (hNbrSel : ∀ v, ¬ G.PencilHub v → IsFin3SelectorOf (G.closedNbhd v) (nbrSel v)) :
    (steerSet (K := K) G hubSel nbrSel).Nonempty ↔ PencilNondegFeasible K G := by
  rw [← gradedPencilNondegFeasible_two_iff]
  constructor
  · rintro ⟨s, -, F, hF⟩
    exact ⟨F, _, _, hF⟩
  · rintro ⟨F, b0, P0, hnd⟩
    obtain ⟨s, hs, -⟩ := exists_mem_steerSet_of_isNondeg hHubSel hNbrSel hnd
    exact ⟨s, hs⟩

/-- **A property holds at a general nondegenerate realization in dimension three** (the remark
after `lem:pencil-d-steer`): at `r(s) = (b⁰(s), n(s)^⊥)` for every `s` in a nonempty Zariski-open
subset of `U(G)`, the non-roots in `U(G)` of a polynomial on `Γ(G)` nonzero somewhere on `U(G)`. -/
def HoldsGenerally (G : Graph α β) (hubSel nbrSel : α → Fin 3 → Option α)
    (p : (α → Fin 4 → K) → (α → Submodule K (Fin 4 → K)) → Prop) : Prop :=
  ∃ R : MvPolynomial (α × Fin 7 × Fin 4) K,
    (∃ s ∈ steerSet G hubSel nbrSel, MvPolynomial.eval s R ≠ 0) ∧
    ∀ s ∈ steerSet G hubSel nbrSel, MvPolynomial.eval s R ≠ 0 →
      p (steerPoint hubSel s) (fun v => dotPerp (K ∙ steerNormal hubSel nbrSel G s v))

/-! ## The coordinates of a lift -/

/-- **The coordinates of a lift** (`def:pencil-d-lift`): `(p₁, p₂, p₃, u₁, …, u_r, p₄)`, the `r`
new coordinates inserted before the last one, as `gradeEmbed` inserts its zeros. -/
def liftVec {r : ℕ} (p : Fin 4 → K) (u : Fin r → K) : Fin (r + 1 + 1 + 2) → K :=
  gradeMk (p 0) (p 1) (Matrix.vecCons (p 2) u) (p 3)

/-- The four old coordinates of a vector of `K^(r+4)`: the map `π` that deletes the inserted
ones. -/
def liftProj {r : ℕ} : (Fin (r + 1 + 1 + 2) → K) →ₗ[K] (Fin 4 → K) where
  toFun b := ![b 0, b 1, gradeHeights b 0, b (Fin.last _)]
  map_add' b b' := by funext i; fin_cases i <;> rfl
  map_smul' c b := by funext i; fin_cases i <;> rfl

theorem liftProj_liftVec {r : ℕ} (p : Fin 4 → K) (u : Fin r → K) : liftProj (liftVec p u) = p := by
  funext i; fin_cases i <;> simp [liftProj, liftVec]

/-- `liftVec` as a linear equivalence `K⁴ × K^r ≃ K^(r+4)`. -/
def liftVecEquiv (r : ℕ) : ((Fin 4 → K) × (Fin r → K)) ≃ₗ[K] (Fin (r + 1 + 1 + 2) → K) where
  toFun x := liftVec x.1 x.2
  invFun b := (liftProj b, Fin.tail (gradeHeights b))
  map_add' x y := by
    simp only [liftVec, Prod.fst_add, Prod.snd_add, gradeMk_add, Pi.add_apply]
    rw [Matrix.cons_add_cons]
  map_smul' c x := by
    simp only [liftVec, Prod.smul_fst, Prod.smul_snd, gradeMk_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [Matrix.smul_cons, smul_eq_mul]
  left_inv x := by
    obtain ⟨p, u⟩ := x
    simp only [liftProj_liftVec, Prod.mk.injEq, true_and]
    simp [liftVec]
  right_inv b := by
    simp only
    conv_rhs => rw [gradeMk_eta b]
    simp only [liftVec, liftProj, LinearMap.coe_mk, AddHom.coe_mk]
    refine gradeMk_ext rfl rfl ?_ rfl
    exact Fin.cons_self_tail (gradeHeights b)

theorem liftVecEquiv_apply {r : ℕ} (x : (Fin 4 → K) × (Fin r → K)) :
    liftVecEquiv r x = liftVec x.1 x.2 := rfl

/-! ## Lifts -/

/-- **The lift space** `𝓛(b⁰, Π⁰)` (`def:pencil-d-lift`): pairs `(ζ, φ)` of a map `ζ` on the bodies
and a linear form `φ_v` on `Π⁰_v` at every body, with `ζ_w = φ_v(b⁰_w)` for every body `v` and
every `w` in its closed neighbourhood (asked when `b⁰_w ∈ Π⁰_v`, which a realization gives). -/
def liftSpace (G : Graph α β) (b0 : α → Fin 4 → K) (P0 : α → Submodule K (Fin 4 → K)) :
    Submodule K ((α → K) × ((v : α) → Module.Dual K (P0 v))) where
  carrier := {lam | ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, ∀ h : b0 w ∈ P0 v,
    lam.1 w = lam.2 v ⟨b0 w, h⟩}
  add_mem' {x y} hx hy v hv w hw h := by
    simp [hx v hv w hw h, hy v hv w hw h]
  zero_mem' v _ w _ h := by simp
  smul_mem' c x hx v hv w hw h := by simp [hx v hv w hw h]

theorem mem_liftSpace {G : Graph α β} {b0 : α → Fin 4 → K} {P0 : α → Submodule K (Fin 4 → K)}
    {lam : (α → K) × ((v : α) → Module.Dual K (P0 v))} :
    lam ∈ liftSpace G b0 P0 ↔ ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, ∀ h : b0 w ∈ P0 v,
      lam.1 w = lam.2 v ⟨b0 w, h⟩ := Iff.rfl

/-- **A trivial lift** (`def:pencil-d-lift`): one form `ψ` on `K⁴` with `ζ_v = ψ(b⁰_v)` and
`φ_v = ψ|Π⁰_v` at every body. -/
def IsTrivialLift (G : Graph α β) (b0 : α → Fin 4 → K) (P0 : α → Submodule K (Fin 4 → K))
    (lam : (α → K) × ((v : α) → Module.Dual K (P0 v))) : Prop :=
  ∃ ψ : Module.Dual K (Fin 4 → K), ∀ v ∈ V(G), lam.1 v = ψ (b0 v) ∧ lam.2 v = ψ.domRestrict (P0 v)

/-- **The maps of the lifts** `L(b⁰)` (`def:pencil-d-lift`). -/
def liftMaps (G : Graph α β) (b0 : α → Fin 4 → K) (P0 : α → Submodule K (Fin 4 → K)) :
    Submodule K (α → K) :=
  (liftSpace G b0 P0).map (LinearMap.fst K _ _)

/-- **The normals of a lift** (`def:pencil-d-lift`), from the maps `ζ^i` of its `r` parameters. -/
def liftNormal {r : ℕ} (b0 : α → Fin 4 → K) (ζ : Fin r → α → K) (v : α) :
    Fin (r + 1 + 1 + 2) → K :=
  liftVec (b0 v) fun i => ζ i v

/-- The map `p ↦ (p₁, p₂, p₃, φ¹(p), …, φ^r(p), p₄)` on `Π⁰_v`. -/
def liftPlaneMap {r : ℕ} (P : Submodule K (Fin 4 → K)) (φ : Fin r → Module.Dual K P) :
    P →ₗ[K] (Fin (r + 1 + 1 + 2) → K) :=
  (liftVecEquiv r).toLinearMap ∘ₗ (P.subtype.prod (LinearMap.pi φ))

theorem liftPlaneMap_apply {r : ℕ} (P : Submodule K (Fin 4 → K)) (φ : Fin r → Module.Dual K P)
    (x : P) : liftPlaneMap P φ x = liftVec x fun i => φ i x := rfl

theorem liftProj_comp_liftPlaneMap {r : ℕ} (P : Submodule K (Fin 4 → K))
    (φ : Fin r → Module.Dual K P) : liftProj ∘ₗ liftPlaneMap P φ = P.subtype := by
  ext x; simp [liftPlaneMap_apply, liftProj_liftVec]

/-- **The subspaces of a lift** (`def:pencil-d-lift`). -/
def liftSubspace {r : ℕ} {P0 : α → Submodule K (Fin 4 → K)}
    (lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v))) (v : α) :
    Submodule K (Fin (r + 1 + 1 + 2) → K) :=
  LinearMap.range (liftPlaneMap (P0 v) fun i => (lam i).2 v)

theorem map_liftProj_liftSubspace {r : ℕ} {P0 : α → Submodule K (Fin 4 → K)}
    (lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v))) (v : α) :
    (liftSubspace lam v).map liftProj = P0 v := by
  rw [liftSubspace, ← LinearMap.range_comp, liftProj_comp_liftPlaneMap, Submodule.range_subtype]

theorem injOn_liftProj_liftSubspace {r : ℕ} {P0 : α → Submodule K (Fin 4 → K)}
    (lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v))) (v : α) :
    Set.InjOn liftProj (liftSubspace lam v : Set (Fin (r + 1 + 1 + 2) → K)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
  have h := congrArg (fun f => f x) (liftProj_comp_liftPlaneMap (P0 v) fun i => (lam i).2 v)
  have h' := congrArg (fun f => f y) (liftProj_comp_liftPlaneMap (P0 v) fun i => (lam i).2 v)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h h' hxy
  rw [Subtype.ext (h.symm.trans (hxy.trans h'))]

/-! ## Lifts are nondegenerate realizations -/

/-- **Lifts are nondegenerate realizations** (`lem:pencil-d-lift-realization`, part (1)): the lift
by `λ`, with the hinges `C(b_u, b_v)` (`toPatchedBodyHinge` of the panel-hinge framework with the
normals of the lift; its rows are those of the panel-hinge framework,
`PanelHingeFramework.span_rigidityRows_toPatchedBodyHinge`), is a nondegenerate pencil realization
in dimension `r + 3`. -/
theorem IsNondegPencilPlaneRealization.lift {r : ℕ} {G : Graph α β}
    {F : BodyHingeFramework K 2 α β} {b0 : α → Fin 4 → K} {P0 : α → Submodule K (Fin 4 → K)}
    (hnd : IsNondegPencilPlaneRealization G F b0 P0)
    {lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v))}
    (hlam : ∀ i, lam i ∈ liftSpace G b0 P0) {ends : β → α × α}
    (hlinks : Graph.RecordsLinks G ends) :
    IsNondegPencilPlaneRealization G
      (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 (fun i => (lam i).1) p.1 p.2)).toPatchedBodyHinge
      (liftNormal b0 (fun i => (lam i).1)) (liftSubspace lam) := by
  set ζ : Fin r → α → K := fun i => (lam i).1 with hζ
  have hP0 : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b0 w ∈ P0 v := fun v hv w hw =>
    hnd.1.normal_mem_plane_of_mem_closedNbhd hv hw
  have hproj : ∀ v, liftProj (liftNormal b0 ζ v) = b0 v := fun v => liftProj_liftVec _ _
  have hinj : ∀ v, Function.Injective (liftPlaneMap (P0 v) fun i => (lam i).2 v) := by
    intro v x y hxy
    have h := congrArg (fun f => f x) (liftProj_comp_liftPlaneMap (P0 v) fun i => (lam i).2 v)
    have h' := congrArg (fun f => f y) (liftProj_comp_liftPlaneMap (P0 v) fun i => (lam i).2 v)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h h'
    exact Subtype.ext (h.symm.trans ((congrArg liftProj hxy).trans h'))
  have hmem : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, liftNormal b0 ζ w ∈ liftSubspace lam v := by
    intro v hv w hw
    refine ⟨⟨b0 w, hP0 v hv w hw⟩, ?_⟩
    rw [liftPlaneMap_apply]
    simp only [liftNormal, hζ]
    congr 1
    funext i
    exact ((hlam i) v hv w hw (hP0 v hv w hw)).symm
  have hreal := PanelHingeFramework.hasPencilPlaneRealization_toPatchedBodyHinge
    (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends (fun p => liftNormal b0 ζ p.1 p.2))
    (plane := liftSubspace lam) (fun v hv h0 => ?_) (fun e u v huv => ?_) (fun v hv => ?_)
    (fun v hv w hw => hmem v hv w hw)
  · refine ⟨hreal, PencilNondegConditions.of_map liftProj
      (fun v _ => injOn_liftProj_liftSubspace lam v) ?_⟩
    have e1 : (fun v => liftProj (liftNormal b0 ζ v)) = b0 := funext hproj
    have e2 : (fun v => (liftSubspace lam v).map liftProj) = P0 :=
      funext (map_liftProj_liftSubspace lam)
    rw [e1, e2]
    exact hnd.2
  · have h1 : liftProj (liftNormal b0 ζ v) = 0 := by
      rw [show liftNormal b0 ζ v = fun i => liftNormal b0 ζ v i from rfl]
      simp only [PanelHingeFramework.ofNormals_normal] at h0
      rw [h0, map_zero]
    exact hnd.1.1.2.1 v hv (by rwa [hproj] at h1)
  · refine LinearIndependent.of_comp liftProj ?_
    convert hnd.2.1 e u v huv using 1
    funext i; fin_cases i <;> exact hproj _
  · rw [liftSubspace, LinearMap.finrank_range_of_inj (hinj v)]
    exact hnd.1.2.1 v hv

/-- **The maps of the lifts** (`lem:pencil-d-lift-realization`, part (2)): `ζ ∈ L(b⁰)` exactly when
at every body `v` some form `ψ_v` on `K⁴` has `ζ_w = ψ_v(b⁰_w)` on the closed neighbourhood of
`v`. So `L(b⁰)` does not depend on `Π⁰`, and the normals of a lift (`liftNormal`) read only the
maps `ζ^i`. -/
theorem mem_liftMaps_iff {G : Graph α β} {b0 : α → Fin 4 → K} {P0 : α → Submodule K (Fin 4 → K)}
    (hP0 : ∀ v ∈ V(G), ∀ w ∈ G.closedNbhd v, b0 w ∈ P0 v) {ζ : α → K} :
    ζ ∈ liftMaps G b0 P0 ↔ ∀ v ∈ V(G), ∃ ψ : Module.Dual K (Fin 4 → K),
      ∀ w ∈ G.closedNbhd v, ζ w = ψ (b0 w) := by
  classical
  constructor
  · rintro ⟨⟨ζ', φ⟩, hmem, rfl⟩ v hv
    obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (φ v)
    refine ⟨ψ, fun w hw => ?_⟩
    change ζ' w = _
    exact (hmem v hv w hw (hP0 v hv w hw)).trans (by
      change φ v _ = _
      rw [← hψ]; rfl)
  · intro h
    choose! ψ hψ using h
    refine ⟨(ζ, fun v => (ψ v).domRestrict (P0 v)), fun v hv w hw _ => hψ v hv w hw, rfl⟩

/-- Scaling the maps of a lift by `c_v` (`lem:pencil-d-lift-realization`, part (3)). -/
def liftSmul {P0 : α → Submodule K (Fin 4 → K)} (c : α → K)
    (lam : (α → K) × ((v : α) → Module.Dual K (P0 v))) :
    (α → K) × ((v : α) → Module.Dual K (P0 v)) :=
  (fun v => c v * lam.1 v, lam.2)

/-- **Scaling the normals** (`lem:pencil-d-lift-realization`, part (3), first map): with `c_v ≠ 0`,
`(ζ, φ) ↦ ((c_v ζ_v), φ)` maps `𝓛(b⁰, Π⁰)` onto `𝓛(cb⁰, Π⁰)` (it is a bijection of the ambient
space, with inverse at `c⁻¹`). -/
theorem liftSmul_mem_liftSpace_iff {G : Graph α β} {b0 : α → Fin 4 → K}
    {P0 : α → Submodule K (Fin 4 → K)} {c : α → K} (hc : ∀ v ∈ V(G), c v ≠ 0)
    {lam : (α → K) × ((v : α) → Module.Dual K (P0 v))} :
    liftSmul c lam ∈ liftSpace G (fun v => c v • b0 v) P0 ↔ lam ∈ liftSpace G b0 P0 := by
  simp only [mem_liftSpace, liftSmul]
  refine forall₂_congr fun v hv => forall₂_congr fun w hw => ?_
  have hcw : c w ≠ 0 := hc w (Graph.closedNbhd_subset_vertexSet hv hw)
  constructor
  · intro h hb
    have := h ((P0 v).smul_mem (c w) hb)
    have e : (⟨c w • b0 w, (P0 v).smul_mem (c w) hb⟩ : P0 v) = c w • ⟨b0 w, hb⟩ := rfl
    rw [e, map_smul, smul_eq_mul] at this
    exact mul_left_cancel₀ hcw this
  · intro h hb
    have hb' : b0 w ∈ P0 v := by
      simpa [hcw] using (P0 v).smul_mem (c w)⁻¹ hb
    have e : (⟨c w • b0 w, hb⟩ : P0 v) = c w • ⟨b0 w, hb'⟩ := rfl
    rw [e, map_smul, smul_eq_mul, h hb']

/-- Scaling the normals of a panel-hinge framework by nonzero scalars keeps its rank. -/
theorem finrank_span_rigidityRows_ofNormals_smul {k : ℕ} {G : Graph α β} {ends : β → α × α}
    (hlinks : Graph.RecordsLinks G ends)
    {c : α → K} (hc : ∀ v ∈ V(G), c v ≠ 0) (b : α → Fin (k + 2) → K) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun p => (c p.1 • b p.1) p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := k) G ends
        (fun p => b p.1 p.2)).toBodyHinge.rigidityRows) := by
  set F₁ := (PanelHingeFramework.ofNormals (k := k) G ends (fun p => b p.1 p.2)).toBodyHinge
  set F₂ := (PanelHingeFramework.ofNormals (k := k) G ends
    (fun p => (c p.1 • b p.1) p.2)).toBodyHinge
  have hprop : ∀ e u v, F₁.graph.IsLink e u v →
      ∃ c' : K, c' ≠ 0 ∧ c' • F₁.supportExtensor e = F₂.supportExtensor e := by
    intro e u v he
    have h0 := hlinks.isLink he
    refine ⟨c (ends e).1 * c (ends e).2, mul_ne_zero (hc _ h0.left_mem) (hc _ h0.right_mem), ?_⟩
    change _ = panelSupportExtensor (c (ends e).1 • b (ends e).1) (c (ends e).2 • b (ends e).2)
    rw [panelSupportExtensor_smul_left, panelSupportExtensor_swap (c (ends e).2 • _),
      panelSupportExtensor_smul_left, ← smul_neg, ← panelSupportExtensor_swap, smul_smul]
    rfl
  rw [span_rigidityRows_eq_of_supportExtensor_proportional F₁ F₂ rfl hprop]

theorem liftNormal_smul {r : ℕ} (b0 : α → Fin 4 → K) (ζ : Fin r → α → K) (c : α → K) (v : α) :
    liftNormal (fun v => c v • b0 v) (fun i v => c v * ζ i v : Fin r → α → K) v =
      c v • liftNormal b0 ζ v := by
  simp only [liftNormal, liftVec, gradeMk_smul, Pi.smul_apply, smul_eq_mul, Matrix.smul_cons]
  rfl

/-- Transporting the forms of a lift along `g` (`lem:pencil-d-lift-realization`, part (3)). -/
def liftTransport {P0 : α → Submodule K (Fin 4 → K)} (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K))
    (lam : (α → K) × ((v : α) → Module.Dual K (P0 v))) :
    (α → K) × ((v : α) → Module.Dual K ((P0 v).map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)))) :=
  (lam.1, fun v => lam.2 v ∘ₗ (g.submoduleMap (P0 v)).symm.toLinearMap)

/-- **Transporting by an automorphism** (`lem:pencil-d-lift-realization`, part (3), second map):
`(ζ, φ) ↦ (ζ, φ ∘ g⁻¹)` maps `𝓛(b⁰, Π⁰)` onto `𝓛(gb⁰, gΠ⁰)` (it is a bijection, with inverse at
`g⁻¹`). -/
theorem liftTransport_mem_liftSpace_iff {G : Graph α β} {b0 : α → Fin 4 → K}
    {P0 : α → Submodule K (Fin 4 → K)} (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K))
    {lam : (α → K) × ((v : α) → Module.Dual K (P0 v))} :
    liftTransport g lam ∈ liftSpace G (fun v => g (b0 v))
        (fun v => (P0 v).map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K))) ↔
      lam ∈ liftSpace G b0 P0 := by
  simp only [mem_liftSpace, liftTransport]
  refine forall₂_congr fun v hv => forall₂_congr fun w hw => ?_
  have key : ∀ hb : b0 w ∈ P0 v, ((g.submoduleMap (P0 v)).symm
      ⟨g (b0 w), Submodule.mem_map_of_mem hb⟩) = ⟨b0 w, hb⟩ := by
    intro hb
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (g.submoduleMap_apply (P0 v) ⟨b0 w, hb⟩).symm
  have hmem : g (b0 w) ∈ (P0 v).map (g : (Fin 4 → K) →ₗ[K] (Fin 4 → K)) ↔ b0 w ∈ P0 v := by
    refine ⟨fun ⟨x, hx, hxe⟩ => ?_, Submodule.mem_map_of_mem⟩
    rwa [← g.injective hxe]
  constructor
  · intro h hb
    have := h (Submodule.mem_map_of_mem hb)
    rwa [LinearMap.comp_apply, LinearEquiv.coe_coe, key hb] at this
  · intro h hb
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, key (hmem.1 hb), h (hmem.1 hb)]

/-- The automorphism of `K^(r+4)` that acts by `g` on the old coordinates and fixes the new ones. -/
def liftAut (r : ℕ) (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) :
    (Fin (r + 1 + 1 + 2) → K) ≃ₗ[K] (Fin (r + 1 + 1 + 2) → K) :=
  (liftVecEquiv r).symm ≪≫ₗ (g.prodCongr (LinearEquiv.refl K (Fin r → K))) ≪≫ₗ liftVecEquiv r

theorem liftAut_liftVec {r : ℕ} (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (p : Fin 4 → K)
    (u : Fin r → K) : liftAut r g (liftVec p u) = liftVec (g p) u := by
  simp only [liftAut, LinearEquiv.trans_apply]
  rw [← liftVecEquiv_apply (p, u), LinearEquiv.symm_apply_apply]
  rfl

/-- **Both maps keep the rank** (`lem:pencil-d-lift-realization`, part (3)): the lift of
`(gb⁰, gΠ⁰)` by the transported maps has the normals `g̃ b_v` (`liftAut`), and a collineation
keeps the rank (`lem:pencil-d-rank-collineation`); scaling is
`finrank_span_rigidityRows_ofNormals_smul`. -/
theorem finrank_liftNormal_transport {r : ℕ} {G : Graph α β} {ends : β → α × α}
    (hlinks : Graph.RecordsLinks G ends)
    (g : (Fin 4 → K) ≃ₗ[K] (Fin 4 → K)) (b0 : α → Fin 4 → K) (ζ : Fin r → α → K) :
    Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal (fun v => g (b0 v)) ζ p.1 p.2)).toBodyHinge.rigidityRows)
      = Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
        (fun p => liftNormal b0 ζ p.1 p.2)).toBodyHinge.rigidityRows) :=
  PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv_grade hlinks (liftAut r g)
    fun w _ => (liftAut_liftVec g (b0 w) _).symm

/-! ## The general lift attains -/

/-- **The general lift attains in dimension `r + 3`** (`def:pencil-d-lift-attains`): a polynomial
`Q` in the coordinates of the normals `b⁰_v`, `v ∈ V(G)`, homogeneous in each, nonzero at the
normals of some nondegenerate realization in dimension three, such that every nondegenerate
realization in dimension three with `Q(b⁰) ≠ 0` has a lift of rank
`tgt = D(|V(G)| − 1) − def_d(G)`, the rank of the panel-hinge framework with the normals of the lift
(at a selector `ends` of the links; the rank does not depend on it). -/
def LiftAttains (K : Type*) [Field K] (r : ℕ) (G : Graph α β) : Prop :=
  ∃ (ends : β → α × α) (_ : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2)
    (Q : MvPolynomial (α × Fin 4) K),
    (∀ p ∈ Q.vars, p.1 ∈ V(G)) ∧
    (∃ d : α →₀ ℕ, MvPolynomial.IsWeightedHomogeneous (fun p : α × Fin 4 => Finsupp.single p.1 1)
      Q d) ∧
    (∃ (F : BodyHingeFramework K 2 α β) (b0 : α → Fin 4 → K) (P0 : α → Submodule K (Fin 4 → K)),
      IsNondegPencilPlaneRealization G F b0 P0 ∧ MvPolynomial.eval (fun p => b0 p.1 p.2) Q ≠ 0) ∧
    ∀ (F : BodyHingeFramework K 2 α β) (b0 : α → Fin 4 → K) (P0 : α → Submodule K (Fin 4 → K)),
      IsNondegPencilPlaneRealization G F b0 P0 → MvPolynomial.eval (fun p => b0 p.1 p.2) Q ≠ 0 →
      ∃ lam : Fin r → (α → K) × ((v : α) → Module.Dual K (P0 v)),
        (∀ i, lam i ∈ liftSpace G b0 P0) ∧
        (Module.finrank K (Submodule.span K (PanelHingeFramework.ofNormals (k := r + 1 + 1) G ends
          (fun p => liftNormal b0 (fun i => (lam i).1) p.1 p.2)).toBodyHinge.rigidityRows) : ℤ)
          = screwDim (r + 1 + 1) * ((V(G).ncard : ℤ) - 1) - G.deficiency (r + 1 + 2)


end CombinatorialRigidity.Molecular
