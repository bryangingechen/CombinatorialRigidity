/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.Basic

/-!
# Case III: renaming the bodies along a chain

Lemmas for Case III of KT Theorem 5.5 (Katoh and Tanigawa 2011, *A proof of the molecular
conjecture*, Discrete Comput. Geom. **45**, §6.4), presented in
`sec:molecular-algebraic-induction-caseIII`. For a chain `v₀ ⋯ v_d`, `2 ≤ i ≤ d − 1`,
`σ_i = shiftPerm i.castSucc` and `q_i = q ∘ σ_i`, the file proves:

* that the moves of `CaseIII/Relabel/Basic.lean` along the chain take the row space of `G − v₁` into
  that of `G − v_i`, with the normals renamed by one transposition at each step
  (`shiftBodyListAsc_foldl_mem_span_rigidityRows`): a step of `lem:case-III-chain-eq666`;
* that renaming the bodies along `σ_i` takes the rows of `R(G − v₁, q)` and the forms at the new
  edge `v₀v₂` of `G_1` to rows of `R(G − v_i, q_i)` and forms at the new edge `v_{i−1} v_{i+1}` of
  `G_i` (`chainData_bottom_relabel`, `lem:case-III-chain-relabel-rows`), and that the selectors give
  the links their ends (`candidateEnds_records_splitOff_isLink`,
  `fullLink_recording_of_splitOff_recording`): steps of `lem:case-III-chain-dispatch`;
* in the case `d = 3`, the renaming of the bottom rows along the transposition of `a` and `v`
  (`case_III_bottom_relabel`), and that the restriction to `a` of a form in the row space of `G − v`
  lies in the block of rows of the edge `ac` (`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, the
  span form of KT eq. (6.44)): steps of `lem:case-III-candidate-dispatch-d3`.

`CaseIII/Relabel/Arm.lean` and `ChainColumn.lean` use the file.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-! ## The frameworks of a chain with renamed normals

Steps of `lem:case-III-chain-eq666`. For `s = 0, …, i − 1`, the frameworks
`ofNormals (G − v_{s+1}) ends (shiftSeedAdv q s)` have one selector, and normals renamed at each
step by the transposition of `v_{s+2}` and `v_{s+1}`, so that after `i − 1` steps they are `q ∘ σ_i`
(`shiftSeedAdv_eq_funLeft_shiftPerm`, `CaseIII/Relabel/ChainColumn.lean`). The moves
`wstep v_{s+1} v_{s+2} v_{s+3}` along them take the row space of `G − v₁` into that of `G − v_i`
(`shiftBodyListAsc_foldl_mem_span_rigidityRows`). -/

/-- **The transposition of step `s`** (a step of `lem:case-III-chain-eq666`): for `s + 2 ≤ d`, the
transposition of `v_{s+2}` and `v_{s+1}`, the `(a v)` of the move at the step
`(v, a, c) = (v_{s+1}, v_{s+2}, v_{s+3})` of `shiftBodyListAsc`; the identity for larger `s`. -/
noncomputable def _root_.Graph.ChainData.shiftSeedSwap [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (s : ℕ) : Equiv.Perm α :=
  if h : s + 2 < cd.d + 1 then
    Equiv.swap (cd.vtx ⟨s + 2, h⟩) (cd.vtx ⟨s + 1, by omega⟩) else 1

/-- For `s + 2 ≤ d`, `shiftSeedSwap s` is the transposition of `v_{s+2}` and `v_{s+1}`. -/
theorem _root_.Graph.ChainData.shiftSeedSwap_eq [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) {s : ℕ} (hs : s + 2 < cd.d + 1) :
    cd.shiftSeedSwap s = Equiv.swap (cd.vtx ⟨s + 2, hs⟩) (cd.vtx ⟨s + 1, by omega⟩) := by
  rw [Graph.ChainData.shiftSeedSwap, dite_eq_left hs]

/-- **The normals after `s` steps** (a step of `lem:case-III-chain-eq666`): `shiftSeedAdv q 0 = q`,
and `shiftSeedAdv q (s + 1)` reads `shiftSeedAdv q s` at the image of each body under
`shiftSeedSwap s`. So `shiftSeedAdv q s` is `q` composed, on the bodies, with the product of the
transpositions of `v₂` and `v₁`, …, of `v_{s+1}` and `v_s` (`shiftSeedAdv_eq_prod_shiftSeedSwap`),
and for `1 ≤ i ≤ d − 1`, `shiftSeedAdv q (i − 1)` is `q ∘ σ_i`, the normals `q_i` of KT eq. (6.55)
(p. 694; `shiftSeedAdv_eq_funLeft_shiftPerm`, `CaseIII/Relabel/ChainColumn.lean`). -/
noncomputable def _root_.Graph.ChainData.shiftSeedAdv [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (q : α × Fin (k + 2) → K) : ℕ → α × Fin (k + 2) → K
  | 0 => q
  | s + 1 => fun p => cd.shiftSeedAdv q s (cd.shiftSeedSwap s p.1, p.2)

omit [Field K] in
@[simp] theorem _root_.Graph.ChainData.shiftSeedAdv_zero [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (q : α × Fin (k + 2) → K) : cd.shiftSeedAdv q 0 = q := rfl

omit [Field K] in
theorem _root_.Graph.ChainData.shiftSeedAdv_succ [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (q : α × Fin (k + 2) → K) (s : ℕ) :
    cd.shiftSeedAdv q (s + 1)
      = fun p => cd.shiftSeedAdv q s (cd.shiftSeedSwap s p.1, p.2) := rfl

/-- **The framework of step `s`, with the normals renamed** (a step of `lem:case-III-chain-eq666`):
for `s + 1 ≤ d`, the body-hinge framework of `ofNormals (shiftBodyGraph s) ends (shiftSeedAdv q s)`,
where `shiftBodyGraph s` is `G − v_{s+1}`. The selector does not depend on `s`; the normals do. -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkAsc [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → K) :
    BodyHingeFramework K k α β :=
  (PanelHingeFramework.ofNormals (cd.shiftBodyGraph hs) ends (cd.shiftSeedAdv q s)).toBodyHinge

/-- **The frameworks of the steps, as a sequence** (a step of `lem:case-III-chain-eq666`):
`shiftBodyFrameworkAsc s` for `s + 1 ≤ d`, and `shiftBodyFrameworkAsc 0` for larger `s`, so that
`wstep_foldl_mem_span_rigidityRows` applies. At every `s` the moves reach, it is the first
(`shiftBodyFrameworkAscTotal_eq`). -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkAscTotal [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → K) :
    ℕ → BodyHingeFramework K k α β :=
  fun s => if h : s + 1 < cd.d + 1 then cd.shiftBodyFrameworkAsc h ends q
    else cd.shiftBodyFrameworkAsc (s := 0) (by have := cd.hd; omega) ends q

/-- For `s + 1 ≤ d`, `shiftBodyFrameworkAscTotal s` is `shiftBodyFrameworkAsc s`. -/
theorem _root_.Graph.ChainData.shiftBodyFrameworkAscTotal_eq [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → K) {s : ℕ}
    (hs : s + 1 < cd.d + 1) :
    cd.shiftBodyFrameworkAscTotal ends q s = cd.shiftBodyFrameworkAsc hs ends q := by
  rw [Graph.ChainData.shiftBodyFrameworkAscTotal, dite_eq_left hs]

/-- **The moves along the chain, from `G − v₁` to `G − v_i`** (a step of
`lem:case-III-chain-eq666`): for `i ≤ d − 1` and a selector `ends` that gives each link of `G` its
ends in some order (`hrec`), the moves `wstep v_{s+1} v_{s+2} v_{s+3}`, for `s = 0, …, i − 2` in
this order, take the span of the rows of `ofNormals (G − v₁) ends q` into that of the rows of
`ofNormals (G − v_i) ends (shiftSeedAdv q (i − 1))`.

`wstep_foldl_mem_span_rigidityRows` applies to the frameworks `shiftBodyFrameworkAscTotal`, the
labels of the edges `v_{s+2} v_{s+3}` and the steps `shiftBodyListAsc i`, and
`seedAdvance_wstep_hstep` gives the hypotheses of each step, with the selector `ends` on both sides.
`chainData_freshEdge_slot_mem` (`CaseIII/Relabel/ChainColumn.lean`) applies it to the form
`hingeRow v₀ v₂ ρ₀`. Katoh and Tanigawa make this step with the row correspondence of KT eq. (6.62)
(p. 696). -/
theorem _root_.Graph.ChainData.shiftBodyListAsc_foldl_mem_span_rigidityRows
    [DecidableEq α] {G : Graph α β} {n : ℕ} (cd : G.ChainData n) (i : Fin cd.d)
    (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (hrec : ∀ f x y, G.IsLink f x y → ends f = (x, y) ∨ ends f = (y, x))
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ Submodule.span K
      (cd.shiftBodyFrameworkAsc (s := 0) (by have := i.2; omega) ends q).rigidityRows) :
    ((cd.shiftBodyListAsc i).foldl
        (fun T b => (BodyHingeFramework.wstep (k := k) b.1 b.2.1 b.2.2).comp T) LinearMap.id) φ
      ∈ Submodule.span K
          (cd.shiftBodyFrameworkAsc (s := (i : ℕ) - 1) (by have := i.2; omega) ends q).rigidityRows
            := by
  have hiv : (i : ℕ) < cd.d := i.2
  -- The frameworks `shiftBodyFrameworkAscTotal`, and the label `edge (s + 2)` at step `s` (any
  -- label past the range: the moves reach only `s ≤ i − 2 < d`).
  have hF0 : cd.shiftBodyFrameworkAscTotal ends q 0
      = cd.shiftBodyFrameworkAsc (s := 0) (by omega) ends q :=
    cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)
  have hFlen : cd.shiftBodyFrameworkAscTotal ends q (cd.shiftBodyListAsc i).length
      = cd.shiftBodyFrameworkAsc (s := (i : ℕ) - 1) (by omega) ends q := by
    rw [cd.length_shiftBodyListAsc, cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)]
  rw [← hFlen]
  refine BodyHingeFramework.wstep_foldl_mem_span_rigidityRows
    (F := cd.shiftBodyFrameworkAscTotal ends q)
    (ec := fun s => if h : s + 2 < cd.d then cd.edge ⟨s + 2, h⟩
      else cd.edge ⟨0, by have := cd.hd; omega⟩)
    (bodies := cd.shiftBodyListAsc i) (hstep := fun s hs => ?_) (hφ := hF0 ▸ hφ)
  -- Step `s < i − 1`: the body `vₛ₊₂` is interior, as `s + 2 ≤ i < d`. Read the frameworks, the
  -- label and the step at `s`, and apply `seedAdvance_wstep_hstep`.
  rw [cd.length_shiftBodyListAsc] at hs
  have hsd : s + 2 < cd.d := by omega
  have hFs : cd.shiftBodyFrameworkAscTotal ends q s
      = cd.shiftBodyFrameworkAsc (s := s) (by omega) ends q :=
    cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)
  have hFs1 : cd.shiftBodyFrameworkAscTotal ends q (s + 1)
      = cd.shiftBodyFrameworkAsc (s := s + 1) (by omega) ends q :=
    cd.shiftBodyFrameworkAscTotal_eq ends q (by omega)
  have hbody : (cd.shiftBodyListAsc i)[s]'(by rw [cd.length_shiftBodyListAsc]; omega)
      = (cd.vtx ⟨s + 1, by omega⟩, cd.vtx ⟨s + 2, by omega⟩, cd.vtx ⟨s + 3, by omega⟩) :=
    cd.getElem_shiftBodyListAsc i s (by rw [cd.length_shiftBodyListAsc]; omega)
  have hec : (if h : s + 2 < cd.d then cd.edge ⟨s + 2, h⟩
      else cd.edge ⟨0, by have := cd.hd; omega⟩) = cd.edge ⟨s + 2, hsd⟩ := dite_eq_left hsd
  -- The frameworks at `s` and `s + 1`, the label, and the step
  -- `(shiftBodyListAsc i)[s] = (vₛ₊₁, vₛ₊₂, vₛ₊₃)`, the `(v, a, c)` of the move.
  simp only [hFs1, hFs, hbody, hec]
  -- `F (s+1) = shiftBodyFrameworkAsc (s+1) = ofNormals (G − vₛ₊₂) ends (Q (s+1))`, where
  -- `Q (s+1) = fun p => (Q s)(shiftSeedSwap s p.1, p.2)` and `shiftSeedSwap s = (vₛ₊₂ vₛ₊₁)`
  -- (`hsd`): the normals of `seedAdvance_wstep_hstep`.
  have hQ : cd.shiftSeedAdv q (s + 1)
      = fun p => cd.shiftSeedAdv q s
          (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) p.1, p.2) := by
    rw [cd.shiftSeedAdv_succ, cd.shiftSeedSwap_eq (by omega)]
  -- The six hypotheses of the move at step `s` (`seedAdvance_wstep_hstep`), at the normals `Q s`
  -- and the selector `ends` on both sides (so `hends'_off` is `rfl`), with `hrec` on the links of
  -- `G − vₛ₊₁`. Unfold the frameworks to the `ofNormals (G − vₛ₊₁)` and `ofNormals (G − vₛ₊₂)` that
  -- it states, with `Q (s+1)` rewritten (`hQ`).
  simp only [Graph.ChainData.shiftBodyFrameworkAsc, Graph.ChainData.shiftBodyGraph, hQ]
  exact cd.seedAdvance_wstep_hstep hsd ends ends (cd.shiftSeedAdv q s) (fun _ _ _ => rfl)
    (fun f x y hl => hrec f x y ((Graph.removeVertex_isLink.mp hl).1))

/-! ## The rows of `(G_i, q_i)` (`lem:case-III-chain-relabel-rows`)

For `2 ≤ i ≤ d − 1`, renaming the bodies along `σ_i` and the labels along `shiftEdgePerm i` takes a
link of `G − v₁` to a link of `G − v_i` or to the new edge of `G_i`
(`removeVertex_genuine_shiftRelabel`), and the rows of `R(G − v₁, q)` and the forms at the new edge
of `G_1` to rows of `R(G − v_i, q_i)` and forms at the new edge of `G_i`
(`chainData_bottom_relabel`). Two steps of `lem:case-III-chain-dispatch` show that selectors give
the links their ends: the renamed selector those of `G_i` (`candidateEnds_records_splitOff_isLink`),
and a selector set at the two edges at `v₁` those of `G`
(`fullLink_recording_of_splitOff_recording`). -/

/-- **A link of `G − v₁`, renamed along `σ_i`** (a step of `lem:case-III-chain-relabel-rows`; the
row correspondence of KT eq. (6.62), p. 696): for `2 ≤ i ≤ d − 1`, `σ_i = shiftPerm i.castSucc` and
the permutation `shiftEdgePerm i` of the labels, let `f` join `x` and `y` in `G`, neither of them
`v₁`. Then `(shiftEdgePerm i)⁻¹ f` joins `σ_i⁻¹ x` and `σ_i⁻¹ y` in `G − v_i`, or `σ_i⁻¹ x` and
`σ_i⁻¹ y` are `v_{i+1}` and `v_{i−1}`, in either order; the second when `f` is the edge
`v_i v_{i+1}`, whose renaming is the new edge `v_{i−1} v_{i+1}` of `G_i`.

As `e₀` is not an edge of `G`, `f` is a link of `G_1 = G.splitOff v₁ v₂ v₀ e₀`. The isomorphism
`splitOff_isLink_shiftRelabel_iff` from `G_i = G.splitOff v_i v_{i+1} v_{i−1} e₀` to `G_1`, Katoh
and Tanigawa's `ρ_i` (KT eq. (6.54), p. 694), makes its renaming a link of `G_i`: a link of
`G − v_i`, or the new edge, whose ends are `v_{i+1}` and `v_{i−1}`. -/
lemma _root_.Graph.ChainData.removeVertex_genuine_shiftRelabel
    [DecidableEq α] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {f : β} {x y : α} (hG : G.IsLink f x y)
    (hx1 : x ≠ cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
    (hy1 : y ≠ cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) :
    (G.removeVertex (cd.vtx i.castSucc)).IsLink ((cd.shiftEdgePerm i)⁻¹ f)
        ((cd.shiftPerm i.castSucc)⁻¹ x) ((cd.shiftPerm i.castSucc)⁻¹ y) ∨
      (((cd.shiftPerm i.castSucc)⁻¹ x = cd.vtx i.succ ∧
          (cd.shiftPerm i.castSucc)⁻¹ y
            = cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ∨
        ((cd.shiftPerm i.castSucc)⁻¹ x
            = cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc ∧
          (cd.shiftPerm i.castSucc)⁻¹ y = cd.vtx i.succ)) := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  -- `e₀` is not an edge of `G`, so the link `f x y` is a link of `G_1`.
  have hfe₀ : f ≠ cd.e₀ := fun he => cd.e₀_fresh (he ▸ hG.edge_mem)
  -- `f x y` as a link of `G_1`, then renamed to a link of `G_i` by the isomorphism.
  have hbase : (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ) (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
      cd.e₀).IsLink f x y :=
    Graph.splitOff_isLink.mpr (Or.inl ⟨hfe₀, hG, hx1, hy1⟩)
  -- The isomorphism at the renamed link: `σ (σ⁻¹ f) = f`, and likewise at the ends.
  have hcand := (cd.splitOff_isLink_shiftRelabel_iff i hi
      (e := (cd.shiftEdgePerm i)⁻¹ f) (x := (cd.shiftPerm i.castSucc)⁻¹ x)
      (y := (cd.shiftPerm i.castSucc)⁻¹ y)).mpr (by
    simpa using hbase)
  -- A link of `G_i` is a link of `G − v_i`, or the new edge `e₀`, whose ends are `v_{i+1}` and
  -- `v_{i−1}`.
  rw [Graph.splitOff_isLink] at hcand
  rcases hcand with ⟨hne₀, hGcand, hxv, hyv⟩ | ⟨_, _, _, _, _, hxy⟩
  · exact Or.inl (Graph.removeVertex_isLink.mpr ⟨hGcand, hxv, hyv⟩)
  · exact Or.inr hxy

/-- **The renamed selector gives each link of `G_i` its ends** (a step of
`lem:case-III-chain-dispatch`; KT eq. (6.54), p. 694): for `2 ≤ i ≤ d − 1`, if `ends₀` gives each
link of `G_1 = G.splitOff v₁ v₂ v₀ e₀` its ends in some order (`hrec`), then `candidateEnds i ends₀`
gives each link of `G_i = G.splitOff v_i v_{i+1} v_{i−1} e₀` its ends in some order. A link `e` of
`G_i` with ends `u` and `w` is, under `splitOff_isLink_shiftRelabel_iff`, the link
`shiftEdgePerm i e` of `G_1` with ends `σ_i u` and `σ_i w`, to which `ends₀` gives them, and
`candidateEnds i ends₀` applies `σ_i⁻¹` to both. `chainData_interior_realization_hρGv`
(`CaseIII/Realization.lean`) uses it. -/
lemma _root_.Graph.ChainData.candidateEnds_records_splitOff_isLink
    [DecidableEq α] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {ends₀ : β → α × α}
    (hrec : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).succ)
        (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink f x y →
      ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    {e : β} {u w : α}
    (hlink : (G.splitOff (cd.vtx i.castSucc) (cd.vtx i.succ)
      (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink e u w) :
    cd.candidateEnds i ends₀ e = (u, w) ∨ cd.candidateEnds i ends₀ e = (w, u) := by
  -- The link `(σ e) (ρ u) (ρ w)` of `G_1` (`splitOff_isLink_shiftRelabel_iff`).
  have hbase := (cd.splitOff_isLink_shiftRelabel_iff i hi).mp hlink
  -- `ends₀` gives it its ends; `candidateEnds` applies `ρ.symm`, which gives back `(u, w)` or
  -- `(w, u)`.
  rw [Graph.ChainData.candidateEnds]
  rcases hrec _ _ _ hbase with he | he <;> rw [he] <;>
    simp only [Equiv.symm_apply_apply, Prod.mk.injEq, true_or, or_true]

/-- **A selector that gives each link of `G` its ends** (a step of `lem:case-III-chain-dispatch`):
for `d ≥ 3`, if `ends₀` gives each link of `G.splitOff v₁ v₀ v₂ e₀` its ends in some order
(`hrec'`), and gives the edges `v₀v₁` and `v₁v₂` their ends in some order (`he0`, `he1`), then it
gives each link of `G` its ends in some order. A link of `G` that meets `v₁` is one of the two
edges, as `v₁` is interior (`ChainData.deg_two`); any other link is not `e₀`, which is not an edge
of `G`, so it is a link of the split. `chainData_dispatch_interior_of_discriminator`
(`CaseIII/Realization.lean`) applies it to the selector that `chainData_fire_discriminator` gives,
set at the two edges. -/
lemma _root_.Graph.ChainData.fullLink_recording_of_splitOff_recording
    {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (h3 : 3 ≤ cd.d) {ends₀ : β → α × α}
    -- `ends₀` gives each link of the split at `v₁` its ends:
    (hrec' : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink f x y →
      ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    -- and the edges `edge 0`, which joins `vtx 0` and `vtx 1`, and `edge 1`, which joins `vtx 1`
    -- and `vtx 2`, theirs:
    (he0 : ends₀ (cd.edge ⟨0, by omega⟩) = (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc) ∨
      ends₀ (cd.edge ⟨0, by omega⟩) = (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc))
    (he1 : ends₀ (cd.edge ⟨1, by omega⟩) = (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc) ∨
      ends₀ (cd.edge ⟨1, by omega⟩) = (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)) :
    ∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ ends₀ f = (y, x) := by
  classical
  intro f x y hG
  -- `edge 0` links `vtx 0`–`vtx 1`, `edge 1` links `vtx 1`–`vtx 2` (the `link` field, indices
  -- read out of `Fin (cd.d + 1)`).
  have hl0 : G.IsLink (cd.edge ⟨0, by omega⟩) (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc) := by
    have h := cd.link ⟨0, by omega⟩
    rwa [show (⟨0, by omega⟩ : Fin cd.d).succ = (⟨1, by omega⟩ : Fin cd.d).castSucc from
      Fin.ext rfl] at h
  have hl1 : G.IsLink (cd.edge ⟨1, by omega⟩) (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc) := by
    have h := cd.link ⟨1, by omega⟩
    rwa [show (⟨1, by omega⟩ : Fin cd.d).succ = (⟨2, by omega⟩ : Fin cd.d).castSucc from
      Fin.ext rfl] at h
  by_cases hxy1 : x = cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc ∨
      y = cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc
  · -- `f` is a `G`-edge at the interior base body `vtx 1`: degree-2 closure ⇒ `edge 0` or `edge 1`.
    have hdt := cd.deg_two ⟨1, by omega⟩ (show 0 < (1 : ℕ) by omega)
    have hcl : f = cd.edge ⟨0, by omega⟩ ∨ f = cd.edge ⟨1, by omega⟩ := by
      rcases hxy1 with hx | hy
      · subst hx
        rcases hdt f y hG with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
      · subst hy
        rcases hdt f x hG.symm with h | h
        · exact Or.inl (by simpa using h)
        · exact Or.inr (by simpa using h)
    rcases hcl with rfl | rfl
    · -- `f = edge 0`: `{x, y} = {vtx 0, vtx 1}`; match the recorded `he0` orientation up to swap.
      rcases hl0.eq_and_eq_or_eq_and_eq hG with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · subst hx; subst hy; rcases he0 with h | h
        · exact Or.inl h
        · exact Or.inr h
      · subst hx; subst hy; rcases he0 with h | h
        · exact Or.inr h
        · exact Or.inl h
    · -- `f = edge 1`: `{x, y} = {vtx 1, vtx 2}`; match the recorded `he1` orientation up to swap.
      rcases hl1.eq_and_eq_or_eq_and_eq hG with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · subst hx; subst hy; rcases he1 with h | h
        · exact Or.inl h
        · exact Or.inr h
      · subst hx; subst hy; rcases he1 with h | h
        · exact Or.inr h
        · exact Or.inl h
  · -- Both endpoints survive `vtx 1`: `f` is a `Gab`-link (`f ≠ e₀` since `e₀ ∉ E(G)`).
    rw [not_or] at hxy1
    obtain ⟨hxv1, hyv1⟩ := hxy1
    have hfe₀ : f ≠ cd.e₀ := fun he => cd.e₀_fresh (he ▸ hG.edge_mem)
    exact hrec' f x y (Graph.splitOff_isLink.mpr (Or.inl ⟨hfe₀, hG, hxv1, hyv1⟩))

/-- **The rows of `(G_i, q_i)`** (`lem:case-III-chain-relabel-rows`; KT eqs. (6.55), p. 694, and
(6.62), p. 696): for `2 ≤ i ≤ d − 1`, `σ_i = shiftPerm i.castSucc` and `q_i = q ∘ σ_i`, let `ends₀`
give each link of `G − v₁` its ends in some order (`hrec`) and `e₀` the ends `(v₂, v₀)` (`he₀rec`).
Let `φ` be a row of `ofNormals (G − v₁) ends₀ q`, or a form `hingeRow v₂ v₀ ρ'` with `ρ'` vanishing
on `C(q(v₂), q(v₀))`. Then the form `S ↦ φ (S ∘ σ_i⁻¹)` is a row of
`ofNormals (G − v_i) endsσρ q_i`, for the selector `endsσρ` that renames `ends₀` along `σ_i` and the
permutation `shiftEdgePerm i` of the labels (`Graph.ChainData.candidateEnds`), or a form
`hingeRow v_{i+1} v_{i−1} ρ'` with `ρ'` vanishing on `C(q_i(v_{i+1}), q_i(v_{i−1}))`.

A row `hingeRow x y r` at a link `f` of `G − v₁` goes to `hingeRow (σ_i⁻¹ x) (σ_i⁻¹ y) r`. When
`(shiftEdgePerm i)⁻¹ f` joins `σ_i⁻¹ x` and `σ_i⁻¹ y` in `G − v_i`, this is a row there
(`rigidityRow_relabel_to_genuine`), as the renamed framework has at `(shiftEdgePerm i)⁻¹ f` the
hinge of `ofNormals (G − v₁) ends₀ q` at `f`; otherwise `f` is the edge `v_i v_{i+1}`, and the form
is `±hingeRow v_{i+1} v_{i−1} r` (`removeVertex_genuine_shiftRelabel`). The form `hingeRow v₂ v₀ ρ'`
goes to `hingeRow v₁ v₀ ρ'`, a row at the edge `v₀v₁`, whose renamed hinge is that of `e₀`
(`blockRow_relabel_perm`, `shiftEdgePerm_apply_edge_zero`). `chainData_dispatch_interior`
(`CaseIII/Realization.lean`) applies it to the bottom rows. -/
theorem PanelHingeFramework.chainData_bottom_relabel
    [DecidableEq α] [DecidableEq β] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (i : Fin cd.d) (hi : 1 < (i : ℕ))
    {ends₀ : β → α × α} {q : α × Fin (k + 2) → K}
    (hrec : ∀ e x y, (G.removeVertex
          (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)).IsLink e x y →
      ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (he₀rec : ends₀ cd.e₀ =
      (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc,
        cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals
        (G.removeVertex (cd.vtx (⟨1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc))
        ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor
            (fun j => q (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))
            (fun j => q (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc, j))) = 0 ∧
        φ = BodyHingeFramework.hingeRow
            (cd.vtx (⟨2, by have := i.isLt; omega⟩ : Fin cd.d).castSucc)
            (cd.vtx (⟨0, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ') :
    (LinearMap.funLeft K (ScrewSpace K k) (cd.shiftPerm i.castSucc).symm).dualMap φ ∈
      (PanelHingeFramework.ofNormals (G.removeVertex (cd.vtx i.castSucc))
        (fun e => ((cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).1,
          (cd.shiftPerm i.castSucc).symm (ends₀ (cd.shiftEdgePerm i e)).2))
        (fun p => q (cd.shiftPerm i.castSucc p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor
            (fun j => q (cd.shiftPerm i.castSucc (cd.vtx i.succ), j))
            (fun j => q (cd.shiftPerm i.castSucc
              (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc), j))) = 0 ∧
        (LinearMap.funLeft K (ScrewSpace K k) (cd.shiftPerm i.castSucc).symm).dualMap φ =
          BodyHingeFramework.hingeRow (cd.vtx i.succ)
            (cd.vtx (⟨(i : ℕ) - 1, by have := i.isLt; omega⟩ : Fin cd.d).castSucc) ρ' := by
  classical
  have hid : (i : ℕ) < cd.d := i.isLt
  -- `ρ.symm = ρ⁻¹` for an `Equiv.Perm` (`removeVertex_genuine_shiftRelabel` is stated with `⁻¹`).
  have hsymm : (cd.shiftPerm i.castSucc).symm = (cd.shiftPerm i.castSucc)⁻¹ := rfl
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- A row `hingeRow x y r` at a link `f x y` of `G − vtx 1`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
      Graph.removeVertex_isLink] at hlink
    obtain ⟨hG, hx1, hy1⟩ := hlink
    -- `r` vanishes on `C(q x, q y)`, the hinge at `f` up to the order of the ends that `ends₀`
    -- gives (`hrec`).
    have hperp : r (panelSupportExtensor (fun j => q (x, j)) (fun j => q (y, j))) = 0 := by
      have hr' := (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
      rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
      rcases hrec f x y (Graph.removeVertex_isLink.mpr ⟨hG, hx1, hy1⟩) with he | he
      · rw [he] at hr'; exact hr'
      · rw [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hr'; exact hr'
    -- The renamed link `(σ⁻¹ f, ρ⁻¹ x, ρ⁻¹ y)`: a link of `G − v_i`, or the new edge of `G_i`.
    rcases cd.removeVertex_genuine_shiftRelabel i hi hG hx1 hy1 with
      hgenuine | (⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · -- A link of `G − v_i`: a row at `(u', w', f') = (ρ⁻¹ x, ρ⁻¹ y, σ⁻¹ f)`
      -- (`rigidityRow_relabel_to_genuine`).
      refine Or.inl ?_
      refine PanelHingeFramework.rigidityRow_relabel_to_genuine (cd.shiftPerm i.castSucc)
        (Gt := G.removeVertex (cd.vtx i.castSucc)) hr rfl rfl hgenuine ?_
      -- `hsupp`: the renamed hinge at `σ⁻¹ f` is the hinge at `f`, as `ρ (ρ.symm ·) = ·` and
      -- `σ (σ⁻¹ f) = f` cancel.
      simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
        Equiv.apply_symm_apply, Equiv.Perm.coe_inv]
    · -- The edge `edge i`, whose renamed ends are `(vᵢ₊₁, vᵢ₋₁)` in the order that `ends₀` gives: a
      -- form at the new edge with `ρ' := r`. `qρ (vtx (i+1)) = q x` (`hxa`) and
      -- `qρ (vtx (i−1)) = q y` (`hyb`), so the hinge is `C(q x, q y)`, on which `r` vanishes
      -- (`hperp`), and the renamed row is `hingeRow (vtx (i+1)) (vtx (i−1)) r`.
      refine Or.inr ⟨r, ?_, ?_⟩
      · have hax : cd.shiftPerm i.castSucc (cd.vtx i.succ) = x := by
          rw [← hxa]; exact Equiv.apply_symm_apply _ _
        have hby : cd.shiftPerm i.castSucc
            (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) = y := by
          rw [← hyb]; exact Equiv.apply_symm_apply _ _
        simp only [hax, hby]; exact hperp
      · simp only [BodyHingeFramework.hingeRow_funLeft_dualMap, hsymm, hxa, hyb]
    · -- The other order: `ρ' := -r`. Here `qρ (vtx (i+1)) = q y` and `qρ (vtx (i−1)) = q x`, so the
      -- hinge is `C(q y, q x) = -C(q x, q y)`, on which `r` vanishes (`hperp`), and the renamed row
      -- `hingeRow (vtx (i−1)) (vtx (i+1)) r` is `hingeRow (vtx (i+1)) (vtx (i−1)) (-r)`
      -- (`hingeRow_swap`).
      refine Or.inr ⟨-r, ?_, ?_⟩
      · have hbx : cd.shiftPerm i.castSucc (cd.vtx i.succ) = y := by
          rw [← hya]; exact Equiv.apply_symm_apply _ _
        have hay : cd.shiftPerm i.castSucc
            (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) = x := by
          rw [← hxb]; exact Equiv.apply_symm_apply _ _
        rw [hbx, hay, LinearMap.neg_apply, panelSupportExtensor_swap, map_neg, neg_neg]
        exact hperp
      · rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hsymm, hxb, hya,
          BodyHingeFramework.hingeRow_swap]
  · -- The form `hingeRow (vtx 2) (vtx 0) ρ'` at the new edge of `G_1`: renamed, a row at `edge 0`,
    -- which joins `vtx 1` and `vtx 0` in `G − v_i` (`blockRow_relabel_perm`).
    refine Or.inl ?_
    refine PanelHingeFramework.blockRow_relabel_perm (cd.shiftPerm i.castSucc)
      (Gt := G.removeVertex (cd.vtx i.castSucc)) (q₀ := q)
      (e_t := cd.edge ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) hid⟩) ?_ ?_ hρ'e₀
    · -- `edge 0 = vtx 0 — vtx 1`, surviving `removeVertex (vtx i.castSucc)`, at
      -- `(ρ⁻¹ (vtx 2), ρ⁻¹ (vtx 0)) = (vtx 1, vtx 0)`.
      have hpos2 : (cd.shiftPerm i.castSucc).symm
            (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc)
          = cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc := by
        rw [hsymm]
        exact cd.shiftPerm_inv_apply_interior i.castSucc (j := 1) le_rfl
          (by simp only [Fin.val_castSucc]; omega)
      have hpos0 : (cd.shiftPerm i.castSucc).symm
            (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
          = cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc := by
        rw [hsymm]
        exact cd.shiftPerm_inv_apply_vtx_off i.castSucc (by omega) (Or.inl rfl)
      rw [hpos2, hpos0, Graph.removeVertex_isLink]
      refine ⟨(cd.isLink_edge ⟨0, by omega⟩).symm, ?_, ?_⟩
      · exact cd.vtx_ne (m := 1) (m' := (i : ℕ)) (by omega) (by omega) (by omega)
      · exact cd.vtx_ne (m := 0) (m' := (i : ℕ)) (by omega) (by omega) (by omega)
    · -- `hsupp`: the renamed hinge at `edge 0` is the hinge at `σ (edge 0) = e₀`, whose ends
      -- `he₀rec` gives as `(vtx 2, vtx 0)`.
      simp only [PanelHingeFramework.ofNormals_supportExtensor_relabel_perm
        (cd.shiftPerm i.castSucc) (cd.shiftEdgePerm i),
        cd.shiftEdgePerm_apply_edge_zero i (by omega),
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_ends, he₀rec]

/-! ## The case `d = 3`

Steps of `lem:case-III-candidate-dispatch-d3`, for the third framework that
`case_III_arm_realization_M3` (`CaseIII/Relabel/Arm.lean`) builds: the renaming of the bottom rows
along the transposition of `a` and `v`, and the restriction to `a` of a form in the row space of
`G − v`, the span form of KT eq. (6.44) (p. 691). -/

/-- **The bottom rows of the third framework** (a step of `lem:case-III-candidate-dispatch-d3`; KT
pp. 686–688): let `v`, `a` and `b` be distinct and `c` neither `a` nor `v`, let `e_a`, `e_b` and
`e_c` join `v` and `a`, `v` and `b`, and `a` and `c` in `G`, with `e_a` and `e_c` the only edges at
`a` (`hcla`), let the links of `Gv` be links of `G` that do not meet `v` (`hGv_le`, `hnov`), with
`ends₀` giving each its ends in some order (`hrecGv`), and let `ends₃` give `e_b` the ends `(v, b)`
and agree with `ends₀` off `e_a`, `e_b` and `e_c`. For the transposition `τ` of `a` and `v`, let `φ`
be a row of `ofNormals Gv ends₀ q`, or a form `hingeRow a b ρ'` with `ρ'` vanishing on
`C(q(a), q(b))`. Then `S ↦ φ (S ∘ τ)` is a row of `ofNormals (G − a) ends₃ (q ∘ τ)`, or a form
`hingeRow c v ρ'` with `ρ'` vanishing on `C(q(c), q(a))`.

This is the renaming along Katoh and Tanigawa's isomorphism from `G_a^{vc}` to `G_v^{ab}` (KT
pp. 686–687), read on the rows as in their row correspondence after KT eq. (6.39) (p. 688): the form
`hingeRow a b ρ'` goes to `hingeRow v b ρ'`, the row of `e_b`, as `q ∘ τ` gives `v` the normal
`q(a)`; a row at `e_c`, the only link of `Gv` at `a`, goes to a form `hingeRow c v ρ'` at the new
edge `vc` of `G_a^{vc}`; and any other row is fixed by `τ` and is a row of `G − a`.
`case_III_arm_realization_M3` (`CaseIII/Relabel/Arm.lean`) applies it to the bottom rows. Every row
is shown to be one from its link, and every hinge is read through `toBodyHinge_supportExtensor`,
`ofNormals_ends` and `ofNormals_normal`, not by `whnf` (TACTICS-QUIRKS §38). -/
theorem PanelHingeFramework.case_III_bottom_relabel
    [DecidableEq α] {G Gv : Graph α β} {ends₀ ends₃ : β → α × α}
    {q : α × Fin (k + 2) → K}
    {v a b c : α} {e_a e_b e_c : β}
    (hva : v ≠ a) (hab : a ≠ b) (hvb : v ≠ b) (hca : c ≠ a) (hcv : c ≠ v)
    (hG_ea : G.IsLink e_a v a) (hG_eb : G.IsLink e_b v b) (hG_ec : G.IsLink e_c a c)
    (hcla : ∀ e x, G.IsLink e a x → e = e_a ∨ e = e_c)
    (hGv_le : ∀ e x y, Gv.IsLink e x y → G.IsLink e x y)
    (hnov : ∀ e x y, Gv.IsLink e x y → x ≠ v ∧ y ≠ v)
    (hrecGv : ∀ e x y, Gv.IsLink e x y → ends₀ e = (x, y) ∨ ends₀ e = (y, x))
    (hends₃_eb : ends₃ e_b = (v, b))
    (hends₃_off : ∀ e, e ≠ e_a → e ≠ e_b → e ≠ e_c → ends₃ e = ends₀ e)
    {φ : Module.Dual K (α → ScrewSpace K k)}
    (hφ : φ ∈ (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun i => q (a, i)) (fun i => q (b, i))) = 0 ∧
        φ = BodyHingeFramework.hingeRow a b ρ') :
    (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap φ ∈
      (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃
        (fun p => q (Equiv.swap a v p.1, p.2))).toBodyHinge.rigidityRows ∨
      ∃ ρ' : Module.Dual K (ScrewSpace K k),
        ρ' (panelSupportExtensor (fun i => q (c, i)) (fun i => q (a, i))) = 0 ∧
        (LinearMap.funLeft K (ScrewSpace K k) (Equiv.swap a v)).dualMap φ
          = BodyHingeFramework.hingeRow c v ρ' := by
  classical
  set qρ : α × Fin (k + 2) → K := fun p => q (Equiv.swap a v p.1, p.2) with hqρ
  set Fv := (PanelHingeFramework.ofNormals Gv ends₀ q).toBodyHinge with hFv
  set Fva := (PanelHingeFramework.ofNormals (G.removeVertex a) ends₃ qρ).toBodyHinge with hFva
  -- The renamed normals at the body `x` are `q` at the swapped body: `qρ(x,·) = q(swap a v x, ·)`.
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- The `G_v`-row tag: destructure the generator and case on `a ∈ {x, y}`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
    obtain ⟨hxv, hyv⟩ := hnov f x y hlink
    have hGflink := hGv_le f x y hlink
    -- `r` vanishes on the hinge of `Fv` at `f` (the normals `q` at `ends₀ f`).
    have hr' : r (Fv.supportExtensor f) = 0 := (Fv.mem_hingeRowBlock_iff f r).1 hr
    rw [hFv, PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
      PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
    by_cases hxa : x = a
    · -- x = a: `hcla` forces `f = e_c` (the `e_a` branch links `v`, contradiction), then `y = c`.
      -- `subst x` (eliminate the local `x`, keeping the section body `a` / `c`).
      subst x
      have hfe : f = e_c := by
        rcases hcla f y hGflink with rfl | rfl
        · -- f = e_a: G.IsLink e_a a y and G.IsLink e_a v a, but a ≠ v (hva) and y ≠ v (hyv).
          rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact absurd h1 hva
          · exact absurd h1.symm hyv
        · rfl
      -- `c = y` (flip so `subst` eliminates `y`, keeping the section variable `c`).
      have hcy : c = y := by
        rw [hfe] at hGflink
        rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2
        · exact absurd h2 hca
      subst hcy
      -- relabel `hingeRow a c r → hingeRow v c r = hingeRow c v (-r)`; tag RIGHT with `ρ' := -r`.
      refine Or.inr ⟨-r, ?_, ?_⟩
      · -- annihilation: `r ⊥ C(q(ends₀ e_c))`, and `ends₀ e_c ∈ {(a,c),(c,a)}` (hrecGv).
        rw [hfe] at hr' hlink
        rw [LinearMap.neg_apply, neg_eq_zero]
        rcases hrecGv e_c a c hlink with he | he
        · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [he] at hr'; exact hr'
      · rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcv]
        exact BodyHingeFramework.hingeRow_swap v c r
    · by_cases hya : y = a
      · -- y = a, x ≠ a: `hcla` forces `f = e_c`, then `x = c`.
        subst y
        have hfe : f = e_c := by
          rcases hcla f x hGflink.symm with rfl | rfl
          · rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨h1, _⟩ | ⟨h1, _⟩
            · exact absurd h1.symm hxv
            · exact absurd h1 hva
          · rfl
        have hcx : c = x := by
          rw [hfe] at hGflink
          rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨_, h2⟩ | ⟨_, h2⟩
          · exact absurd h2 hca
          · exact h2
        subst hcx
        -- relabel `hingeRow c a r → hingeRow c v r`; tag RIGHT with `ρ' := r`.
        refine Or.inr ⟨r, ?_, ?_⟩
        · rw [hfe] at hr' hlink
          rcases hrecGv e_c c a hlink with he | he
          · rw [he] at hr'; exact hr'
          · rw [he] at hr'; rw [panelSupportExtensor_swap, map_neg, hr', neg_zero]
        · rw [Equiv.swap_apply_of_ne_of_ne hca hcv, Equiv.swap_apply_left]
      · -- x ≠ a, y ≠ a: the swap fixes both ends; the image is the row itself, a row of `G − a` at
        -- the selector `ends₃`.
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv]
        -- the image `hingeRow x y r` is a row of `Fva`: the link survives `removeVertex a`, and the
        -- hinge of `Fva` at `f` is that of `Fv`, on which `r` vanishes.
        refine Or.inl ⟨f, x, y, ?_, r, ?_, rfl⟩
        · -- the link survives `removeVertex a` (endpoints `≠ a`).
          rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
            Graph.removeVertex_isLink]
          exact ⟨hGflink, hxa, hya⟩
        · -- block: the `f`-extensor at `Fva` equals the `f`-extensor at `Fv` (off `{e_a,e_b,e_c}`,
          -- `ends₃ f = ends₀ f`, and the swap fixes the recorded endpoints `∉ {a, v}`).
          have hfne_a : f ≠ e_a := by
            rintro rfl
            rcases hG_ea.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxv hh.symm
            · exact hyv hh.symm
          have hfne_b : f ≠ e_b := by
            rintro rfl
            rcases hG_eb.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxv hh.symm
            · exact hyv hh.symm
          have hfne_c : f ≠ e_c := by
            rintro rfl
            rcases hG_ec.eq_and_eq_or_eq_and_eq hGflink with ⟨hh, _⟩ | ⟨hh, _⟩
            · exact hxa hh.symm
            · exact hya hh.symm
          rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
            PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
            PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
            hends₃_off f hfne_a hfne_b hfne_c]
          -- `ends₀ f ∈ {(x,y),(y,x)}` (hrecGv); the swap fixes `x, y ∉ {a, v}`, so `qρ = q` and
          -- the `Fva`-extensor matches the `Fv`-extensor `r` annihilates (`hr'`).
          rcases hrecGv f x y hlink with he | he <;> rw [he] at hr' ⊢ <;>
            simp only [hqρ, Equiv.swap_apply_of_ne_of_ne hxa hxv,
              Equiv.swap_apply_of_ne_of_ne hya hyv] <;> exact hr'
  · -- The form `φ = hingeRow a b ρ'`: renamed, the row of `e_b`.
    have hba : b ≠ a := Ne.symm hab
    have hbv : b ≠ v := Ne.symm hvb
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne hba hbv]
    refine Or.inl ⟨e_b, v, b, ?_, ρ', ?_, rfl⟩
    · rw [hFva, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
        Graph.removeVertex_isLink]
      exact ⟨hG_eb, hva, hba⟩
    · -- block: `Fva.supportExtensor e_b = panelSupportExtensor n_a n_b` (`ends₃ e_b = (v,b)`,
      -- `qρ(v,·) = q(a,·)`, `qρ(b,·) = q(b,·)`); the input gives `ρ' ⊥` it.
      rw [BodyHingeFramework.mem_hingeRowBlock_iff, hFva,
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends, hends₃_eb]
      simp only [hqρ, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbv]
      exact hρ'e₀

/-- **The restriction to a body with one edge of a form in the row space** (a step of
`lem:case-III-candidate-dispatch-d3`; the span form of KT eq. (6.44), p. 691): let `e_c` join `a`
and `c ≠ a` in `Fv` and be the only link of `Fv` at `a` (`hdeg2`, `hdeg2r`), and let `Fv` and `Fab`
have the same block of rows at `e_c` (`hblock`). Then for `wGv` in the span of the rows of `Fv`, the
restriction `wGv ∘ single a` lies in the block of rows of `Fab` at `e_c`.

The proof is by induction on the span. A row `hingeRow u w ρ` at a link `f` restricts to `ρ` when
`u = a`, as then `f = e_c` and `w = c` (`hingeRow_comp_single_tail`), to `−ρ` when `w = a`
(`hingeRow_swap`), and to `0` otherwise (`hingeRow_comp_single_off`); each lies in the block, a
subspace. `case_III_arm_realization_M3` (`CaseIII/Relabel/Arm.lean`) applies it to `G − v`, in which
`ac` is the only edge at `a`. -/
theorem BodyHingeFramework.acolumn_mem_hingeRowBlock_of_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework K k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual K (α → ScrewSpace K k)}
    (hwGv : wGv ∈ Submodule.span K Fv.rigidityRows) :
    wGv.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a) ∈ Fab.hingeRowBlock e_c := by
  -- Apply span_induction with the transported predicate `φ.comp(single a) ∈ Fab.hingeRowBlock e_c`.
  apply Submodule.span_induction (p := fun ψ _ =>
    ψ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a) ∈ Fab.hingeRowBlock e_c)
      _ _ _ _ hwGv
  · -- generator case: hingeRow u w ρ ∈ Fv.rigidityRows
    rintro ψ ⟨f, u, w, hlink, ρ, hρ, rfl⟩
    by_cases hau : u = a
    · -- u = a: hdeg2 forces f = e_c; use links to get w = c
      have hfe : f = e_c := by rw [hau] at hlink; exact hdeg2 f w hlink
      -- hlink rewritten: IsLink e_c a w; use eq_and_eq_or_eq_and_eq with hlink_ec
      have hwc : w = c := by
        rw [hau, hfe] at hlink
        -- hlink : IsLink e_c a w; hlink_ec : IsLink e_c a c → a = a ∧ w = c ∨ a = c ∧ w = a
        rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd h hac
      rw [hau, hwc, hingeRow_comp_single_tail hac]
      exact hblock ▸ hfe ▸ hρ
    · by_cases haw : w = a
      · -- w = a, u ≠ a: hdeg2r forces f = e_c; use links to get u = c
        have hfe : f = e_c := by rw [haw] at hlink; exact hdeg2r f u hlink
        have huc : u = c := by
          rw [haw, hfe] at hlink
          -- hlink : IsLink e_c u a; hlink_ec : IsLink e_c a c → u = a ∧ a = c ∨ u = c ∧ a = a
          rcases hlink.eq_and_eq_or_eq_and_eq hlink_ec with ⟨h, -⟩ | ⟨h, -⟩
          · exact absurd h hau
          · exact h
        -- hingeRow u w ρ = hingeRow u a ρ; rewrite via hingeRow_swap, then
        -- hingeRow_comp_single_tail
        rw [hfe] at hρ
        rw [haw, hingeRow_swap u a ρ, huc, hingeRow_comp_single_tail hac]
        exact (Fab.hingeRowBlock e_c).neg_mem (hblock ▸ hρ)
      · -- u ≠ a, w ≠ a: off-column; restricts to 0
        rw [hingeRow_comp_single_off (Ne.symm hau) (Ne.symm haw)]
        exact (Fab.hingeRowBlock e_c).zero_mem
  · -- zero
    simp [(Fab.hingeRowBlock e_c).zero_mem]
  · -- add
    intro x y _ _ hx hy
    rw [LinearMap.add_comp]
    exact (Fab.hingeRowBlock e_c).add_mem hx hy
  · -- smul
    intro r x _ hx
    rw [LinearMap.smul_comp]
    exact (Fab.hingeRowBlock e_c).smul_mem r hx

end CombinatorialRigidity.Molecular
