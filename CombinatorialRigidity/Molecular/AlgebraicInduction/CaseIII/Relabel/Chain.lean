/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.AlgebraicInduction.CaseIII.Relabel.Basic

/-!
# The algebraic induction — Case III relabel: the ascending seed-advancing chain + bottom transport

Phase 22 (molecular-conjecture program). Second file of the `CaseIII/Relabel/` subdirectory (the
Phase-23c split of `CaseIII/Relabel.lean`, `notes/Phase23c.md`). The ascending (base→candidate)
seed-advancing chain (`shiftSeedAdv` / `shiftEndsAdv` / `shiftBodyFrameworkAsc*`), the per-member
genuine transport `chainData_bottom_relabel`, the candidate-row bottom relabel
`case_III_bottom_relabel`,
the `acolumn`/`hingeRow` block bridges, and the candidate-perp incidence lemmas (eq.~(6.43) A-2).
Built on `Relabel/Basic`; consumed by the M₃ arm in `Relabel/Arm`.

See `ROADMAP.md` §22 and the `sec:molecular-algebraic-induction-caseIII` dep-graph in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`.
-/

namespace CombinatorialRigidity.Molecular

variable {k : ℕ}

open scoped Graph

variable {α β : Type*}

variable {K : Type*} [Field K]

/-! ### The ascending (base→candidate) seed-advancing chain (CHAIN-2c-ii-arm)

The corrected-Fix-A relabel arm needs the cycle-W9a transport in the **base→candidate** orientation
with the seed *advancing* one swap per step (`notes/Phase23-design.md` §(o‴)(H.10)) — the opposite
of the seed-fixed candidate→base `shiftBodyFramework` chain above (which is orphaned for the arm: it
proves the converse span implication). The single-step de-risk gate
`funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` already discharges one rise
`F s = ofNormals (G − vₛ₊₁) ends qₛ` → `F (s+1) = ofNormals (G − vₛ₊₂) ends q_{s+1}` (single bound
`s + 2 < cd.d`, covering every step — interior and the candidate-vertex top step). This block is the
concrete seed-advancing chain it iterates: the seed `Q s = q ∘ (the first s cycle swaps)` advances
one swap per step (`shiftSeedAdv`), the moved-body list is the ascending `shiftBodyListAsc i`, and
the membership theorem `shiftBodyListAsc_foldl_mem_span_rigidityRows` feeds the `foldl` core
`wstep_foldl_mem_span_rigidityRows`, with the per-step gate applied at the last element of each
`reverseRec` step. The selector `ends` is **fixed** across the chain (only the seed advances), so
the gate's `hends'_off` is trivially `rfl`. -/

/-- The per-step seed swap of the ascending chain: at step `s` the swap `(vₛ₊₂ vₛ₊₁)` (the gate's
`(a v)`), made total over `ℕ` by defaulting to the identity off the chain-vertex range
(`s + 2 < cd.d + 1`). The seed accumulator `shiftSeedAdv` composes these. -/
noncomputable def _root_.Graph.ChainData.shiftSeedSwap [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (s : ℕ) : Equiv.Perm α :=
  if h : s + 2 < cd.d + 1 then
    Equiv.swap (cd.vtx ⟨s + 2, h⟩) (cd.vtx ⟨s + 1, by omega⟩) else 1

/-- On an in-range step `s + 2 < cd.d + 1`, the per-step seed swap resolves to `(vₛ₊₂ vₛ₊₁)`. -/
theorem _root_.Graph.ChainData.shiftSeedSwap_eq [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) {s : ℕ} (hs : s + 2 < cd.d + 1) :
    cd.shiftSeedSwap s = Equiv.swap (cd.vtx ⟨s + 2, hs⟩) (cd.vtx ⟨s + 1, by omega⟩) := by
  rw [Graph.ChainData.shiftSeedSwap, dif_pos hs]

/-- **The ascending (base→candidate) seed accumulator** (CHAIN-2c-ii-arm; KT 2011 §6.4.2 eq.~(6.62),
the seed-advance recursion). The seed at chain step `s`: the base seed `q` post-composed (on the
vertex slot `p.1`) with the
first `s` cycle swaps `(v₂ v₁), …, (v_{s+1} vₛ)`, advancing one swap per step. `Q 0 = q`;
`Q (s+1) p = (Q s) (shiftSeedSwap s p.1, p.2)` (the gate's `qρ = q ∘ swap` at one step). -/
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

/-- **The ascending (base→candidate) selector accumulator** (CHAIN-2c-ii-arm, ROUTE α leaf 1;
KT 2011 §6.4.2 eq.~(6.62), the selector cousin of `shiftSeedAdv`). The edge-endpoint selector at
chain step `s`: the base selector `ends₀` with each endpoint pair relabelled by the first `s`
per-step cycle swaps `(v₂ v₁), …, (v_{s+1} vₛ)`, advancing one swap per step — the SAME per-step
swap `shiftSeedSwap s` the seed accumulator uses, so selector and seed advance in lockstep.
`E 0 = ends₀`; `E (s+1) e = (shiftSeedSwap s (E s e).1, shiftSeedSwap s (E s e).2)` (KT's iso `ρᵢ`
applied step-by-step on the panel selector, never pre-applied to the base redundancy). -/
noncomputable def _root_.Graph.ChainData.shiftEndsAdv [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends₀ : β → α × α) : ℕ → β → α × α
  | 0 => ends₀
  | s + 1 => fun e => let p := cd.shiftEndsAdv ends₀ s e
                      ((cd.shiftSeedSwap s) p.1, (cd.shiftSeedSwap s) p.2)

@[simp] theorem _root_.Graph.ChainData.shiftEndsAdv_zero [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends₀ : β → α × α) : cd.shiftEndsAdv ends₀ 0 = ends₀ := rfl

theorem _root_.Graph.ChainData.shiftEndsAdv_succ [DecidableEq α] {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (ends₀ : β → α × α) (s : ℕ) :
    cd.shiftEndsAdv ends₀ (s + 1)
      = fun e => ((cd.shiftSeedSwap s) (cd.shiftEndsAdv ends₀ s e).1,
                  (cd.shiftSeedSwap s) (cd.shiftEndsAdv ends₀ s e).2) := rfl

/-- **The ascending (base→candidate) seed-advancing chain** (CHAIN-2c-ii-arm, the framework layer;
`notes/Phase23-design.md` §(o‴)(H.10)). The seed-advancing analogue of `shiftBodyFramework`: the
panel framework `ofNormals (G − vₛ₊₁) ends (Q s)` (turned into a `BodyHingeFramework` via
`toBodyHinge`) over the intermediate graph `shiftBodyGraph s = G − vₛ₊₁`, with the selector `ends`
fixed but the seed `Q s = shiftSeedAdv q s` advancing one swap per step. The chain runs
source-at-bottom `F 0 = ofNormals (G − v₁) ends q` up to target-at-top
`F (i−1) = ofNormals (G − vᵢ) ends (Q (i−1))` — the orientation the relabel arm's `hρGv`/`hwmem`
slots need (the seed-fixed `shiftBodyFramework` runs the converse direction). -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkAsc [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → K) :
    BodyHingeFramework K k α β :=
  (PanelHingeFramework.ofNormals (cd.shiftBodyGraph hs) ends (cd.shiftSeedAdv q s)).toBodyHinge

/-- The graph of the ascending chain `shiftBodyFrameworkAsc s` is `shiftBodyGraph s = G − vₛ₊₁`
(independent of the seed). -/
@[simp]
theorem _root_.Graph.ChainData.shiftBodyFrameworkAsc_graph [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) {s : ℕ} (hs : s + 1 < cd.d + 1) (ends : β → α × α)
    (q : α × Fin (k + 2) → K) :
    (cd.shiftBodyFrameworkAsc hs ends q).graph = cd.shiftBodyGraph hs := rfl

/-- **The total ascending seed-advancing chain** (the membership half; the `foldl` core
`wstep_foldl_mem_span_rigidityRows` runs over a total `F : ℕ → BodyHingeFramework`). Packages the
partial `shiftBodyFrameworkAsc` (valid at `s + 1 < cd.d + 1`) into that total function, filling the
out-of-range tail with the always-valid `s = 0` member. On the in-range indices the fold touches
(`0, …, i − 1` for a cycle top `i ≤ cd.d`) it agrees by `shiftBodyFrameworkAscTotal_eq`. -/
noncomputable def _root_.Graph.ChainData.shiftBodyFrameworkAscTotal [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → K) :
    ℕ → BodyHingeFramework K k α β :=
  fun s => if h : s + 1 < cd.d + 1 then cd.shiftBodyFrameworkAsc h ends q
    else cd.shiftBodyFrameworkAsc (s := 0) (by have := cd.hd; omega) ends q

/-- On an in-range index `s + 1 < cd.d + 1`, the total ascending chain agrees with the partial
`shiftBodyFrameworkAsc`. -/
theorem _root_.Graph.ChainData.shiftBodyFrameworkAscTotal_eq [DecidableEq α] {G : Graph α β}
    {n : ℕ} (cd : G.ChainData n) (ends : β → α × α) (q : α × Fin (k + 2) → K) {s : ℕ}
    (hs : s + 1 < cd.d + 1) :
    cd.shiftBodyFrameworkAscTotal ends q s = cd.shiftBodyFrameworkAsc hs ends q := by
  rw [Graph.ChainData.shiftBodyFrameworkAscTotal, dif_pos hs]

/-- **The concrete ascending (base→candidate) seed-advancing fold** (CHAIN-2c-ii-arm, the membership
half feeding the `foldl` core; `notes/Phase23-design.md` §(o‴)(H.10)). The seed-advancing analogue
of `shiftBodyList_foldr_mem_span_rigidityRows` (which runs candidate→base, seed-fixed): the iterated
W9a transport over the ascending moved-body list `shiftBodyListAsc i` carries a source row span at
the **bottom** of the chain — `span (G − v₁)`-rows on seed `q` (`shiftBodyFrameworkAsc 0`) — **up**
to the target row span at the **top** — `span (G − vᵢ)`-rows on the advanced seed `Q (i−1)`
(`shiftBodyFrameworkAsc (i−1)`).

This is the membership content of KT eq.~(6.62) in the base→candidate direction: the `i − 1`
per-body `a`-column subtractions compose along the chain while the seed advances one swap per step
(`Q s = q ∘ (the first s cycle swaps)`). The proof feeds the `foldl` fold core all six per-step
`hstep` conjuncts by applying the **single-step de-risk gate**
`funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (which proves the full rise — graph
inclusion, degree-2 closures, and the seed-advancing block agreement — at the single bound
`s + 2 < cd.d`, covering both interior and top steps). The selector `ends` is fixed (so the gate's
`hends'_off` is `rfl`), and the canonical `G`-link-recording hypothesis `hrec` weakens per step to
the `removeVertex` form the gate needs. The relabel side (rewriting the `wstep` fold's leading
`funLeft`-of-swap product to `funLeft (shiftPerm i)`) is the separate `wstep_foldl_funLeft_eq` +
`shiftPerm_eq_prod_map_swap_shiftBodyListAsc` bridge, applied by the arm closer. Graph-free over the
carrier, inheriting W9a's §38-clean discipline. -/
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
  -- Feed the `foldl` fold core the total ascending chain `F = shiftBodyFrameworkAscTotal` and the
  -- per-step edge `ec s = edge (s+2)` (out-of-range tail arbitrary; the fold touches only
  -- `s ≤ i − 2 < cd.d`).
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
  -- The per-step `hstep` (step `s < length = i − 1`, so the body `vₛ₊₂` is interior, `s + 2 ≤ i`,
  -- hence `s + 2 < cd.d` since `i < cd.d`). Resolve `F (s+1)`/`F s`/`ec s`/the moved-body triple to
  -- the partial chain and the de-risk gate's roles, then apply the gate as the whole step.
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
      else cd.edge ⟨0, by have := cd.hd; omega⟩) = cd.edge ⟨s + 2, hsd⟩ := dif_pos hsd
  -- Resolve the total chain `F (s+1)`/`F s`/`ec s` to the partial chain and read the moved-body
  -- triple `(shiftBodyListAsc i)[s] = (vₛ₊₁, vₛ₊₂, vₛ₊₃)`. The `foldl` core's per-step `hstep` then
  -- reads the gate's `(v, a, c) = (vtx (s+1), vtx (s+2), vtx (s+3))` roles.
  simp only [hFs1, hFs, hbody, hec]
  -- `F (s+1) = shiftBodyFrameworkAsc (s+1) = ofNormals (G − vₛ₊₂) ends (Q (s+1))`, and
  -- `Q (s+1) = fun p => (Q s)(shiftSeedSwap s p.1, p.2)`, with `shiftSeedSwap s = (vₛ₊₂ vₛ₊₁)`
  -- in range (`hsd`) — so `Q (s+1)` is exactly the de-risk gate's `hstep`-bundle target seed.
  have hQ : cd.shiftSeedAdv q (s + 1)
      = fun p => cd.shiftSeedAdv q s
          (Equiv.swap (cd.vtx ⟨s + 2, by omega⟩) (cd.vtx ⟨s + 1, by omega⟩) p.1, p.2) := by
    rw [cd.shiftSeedAdv_succ, cd.shiftSeedSwap_eq (by omega)]
  -- The six per-step W9a conjuncts (the gate's `hstep` bundle) at the chain step `s`: seed `Q s`,
  -- fixed selector `ends` (so `hends'_off` is `rfl`), the `G`-link-recording `hrec` weakened to the
  -- `removeVertex` form. Unfold the chain frameworks to the `ofNormals (G − vₛ₊₁)`/`(G − vₛ₊₂)`
  -- forms the bundle states, rewriting `Q (s+1)` to the gate's target seed (`hQ`).
  simp only [Graph.ChainData.shiftBodyFrameworkAsc, Graph.ChainData.shiftBodyGraph, hQ]
  exact cd.seedAdvance_wstep_hstep hsd ends ends (cd.shiftSeedAdv q s) (fun _ _ _ => rfl)
    (fun f x y hl => hrec f x y ((Graph.removeVertex_isLink.mp hl).1))

/-- **The removeVertex-level genuine-link transport classification (CHAIN-2c-ii-arm, the genuine-row
`hwmem` make-or-break)** (`lem:case-III` general-`d`, KT 2011 §6.4.2 the (6.62) one-step-down row
correspondence; Phase 23b). A genuine `G`-link `f x y` whose endpoints survive
`removeVertex (vtx 1)` (the `v₁`-base split body, `x ≠ vtx 1`, `y ≠ vtx 1`) transports, under the
inverse index-shift `((shiftPerm i.castSucc)⁻¹, (shiftEdgePerm i)⁻¹)`, to **either** a genuine link
of the candidate-`i` split's `removeVertex (vtx i.castSucc)` graph (the off-cycle /
interior-chain-edge images, both endpoints surviving `removeVertex vᵢ`), **or** the candidate
fresh-edge endpoint pair `{vtx (i+1), vtx (i−1)}` in one of the two orders (the wrap edge `edge i`,
whose endpoints relabel to the candidate's fresh `e₀ = (vtx (i+1)) (vtx (i−1))` short-circuit, so
the image is **not** a `removeVertex vᵢ` link but the candidate `(a,b)`-block).

This is the make-or-break the genuine-row `hwmem` disjunct bottoms out on (design §(o‴)(I.6)): the
**degree-2 closure** `deg_two` (interior chain vertices carry only their two chain edges) rules out
a "homeless interior block" — every genuine `G`-link at a cycle vertex is a chain edge, so it maps
to another chain edge (genuine) or the wrap (the candidate fresh pair), never a stray block. Rather
than re-run the degree-2 case analysis at the removeVertex level, the proof **lifts** the genuine
base row to a link of the `v₁`-base `splitOff` (a survivor, since `f ∈ E(G)` and `e₀ ∉ E(G)`),
applies the landed split-level intertwiner `splitOff_isLink_shiftRelabel_iff` (`.mpr`,
base→candidate via the inverse shift), and reads the resulting candidate-split link back: a
candidate survivor is a genuine `removeVertex vᵢ` link (the fresh-edge label `e₀` cannot be the
survivor edge), while the candidate fresh edge `e₀` records exactly the `{vtx (i+1), vtx (i−1)}`
pair. At the d=3 `M₃` instance `i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the single swap and this
is the
`case_III_bottom_relabel` genuine-row branch's three sub-cases. -/
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
  -- The fresh `e₀` is not a `G`-edge, so the genuine link `f x y` is a base-split survivor.
  have hfe₀ : f ≠ cd.e₀ := fun he => cd.e₀_fresh (he ▸ hG.edge_mem)
  -- Lift `f x y` to a link of the v₁-base split, then push base→candidate via the inverse shift.
  have hbase : (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
      (cd.vtx (⟨1, by omega⟩ : Fin cd.d).succ) (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
      cd.e₀).IsLink f x y :=
    Graph.splitOff_isLink.mpr (Or.inl ⟨hfe₀, hG, hx1, hy1⟩)
  -- The intertwiner `.mpr` at the inverse-shifted candidate data: σ((σ)⁻¹f) = f etc.
  have hcand := (cd.splitOff_isLink_shiftRelabel_iff i hi
      (e := (cd.shiftEdgePerm i)⁻¹ f) (x := (cd.shiftPerm i.castSucc)⁻¹ x)
      (y := (cd.shiftPerm i.castSucc)⁻¹ y)).mpr (by
    simpa using hbase)
  -- `hcand` is a candidate-split link. Read it back: survivor ⇒ removeVertex link; fresh ⇒ wrap.
  rw [Graph.splitOff_isLink] at hcand
  rcases hcand with ⟨hne₀, hGcand, hxv, hyv⟩ | ⟨_, _, _, _, _, hxy⟩
  · exact Or.inl (Graph.removeVertex_isLink.mpr ⟨hGcand, hxv, hyv⟩)
  · exact Or.inr hxy

/-- **The `candidateEnds` selector records every candidate-`i`-split link** (CHAIN-2c-iii LEAF-1,
the interior arm's `hends_ea`/`hends_eb`/`hends_Gv` supplier; `notes/Phase23-design.md` §(4.10)
LEAF-1; Katoh–Tanigawa 2011 §6.4.2 eq.~(6.54)). For an interior candidate index `2 ≤ i ≤ d−1`
(`1 < i`), if the base selector `ends₀` records every link of the `v₁`-base split
`G.splitOff (vtx 1) (vtx 2) (vtx 0) e₀` (the discriminator's `hends'`), then the relabel-image
selector `candidateEnds i ends₀` records every link of the candidate-`i` interior split
`G.splitOff (vtx i.castSucc) (vtx i.succ) (vtx (i−1).castSucc) e₀`.

This is the single combinatorial fact the chain dispatch (`chainData_dispatch`) feeds the interior
arm `chainData_interior_realization_hρGv` for its three selector slots — the two re-inserted chain
hinges (`hends_ea`/`hends_eb`) and the surviving `Gv = G − vᵢ` links (`hends_Gv`) all reduce to this
recording: every such link IS a candidate-split link. Proof: the index-shift intertwiner
`splitOff_isLink_shiftRelabel_iff` (`.mp`) carries the candidate link `e u w` to the base link
`(σ e) (ρ u) (ρ w)` (`(ρ, σ) = (shiftPerm i.castSucc, shiftEdgePerm i)`); `ends₀` records that as
`(ρ u, ρ w)` or `(ρ w, ρ u)`; and `candidateEnds e` applies `ρ.symm` to each, so it
recovers `(u, w)`/`(w, u)` by `Equiv.symm_apply_apply`. Generic in `ends₀`; no `d = 3` content,
no new linear algebra, no motive/IH/contract change. No `\lean` pin (internal infra; the chain
dispatch carries the blueprint node). -/
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
  -- Carry the candidate link to the base link `(σ e) (ρ u) (ρ w)` via the intertwiner `.mp`.
  have hbase := (cd.splitOff_isLink_shiftRelabel_iff i hi).mp hlink
  -- `ends₀` records that base link; `candidateEnds` applies `ρ.symm` to recover `(u, w)`/`(w, u)`.
  rw [Graph.ChainData.candidateEnds]
  rcases hrec _ _ _ hbase with he | he <;> rw [he] <;>
    simp only [Equiv.symm_apply_apply, Prod.mk.injEq, true_or, or_true]

/-- **The full `G`-link recording from the `v₁`-base `splitOff` recording + the two base-body
chain-edge orientations** (CHAIN-2c-iii LEAF-1′, the interior arm's `hrec` supplier;
`notes/Phase23-design.md` §(4.100)/§(4.102); Katoh–Tanigawa 2011 §6.4.2). The crux-leaf
`chainData_relabel_arm_hρGv` needs its base selector `ends₀` to record **every** `G`-link
(`∀ f x y, G.IsLink f x y → ends₀ f = (x, y) ∨ (y, x)`), but the discriminator
(`exists_shared_redundancy_and_matched_candidate`) only exposes the `Gab = G.splitOff (vtx 1)
(vtx 0) (vtx 2) e₀`-link recording `hrec'` — `Gab` is a realization of the *split*, so it has no
edges at the removed base body `vtx 1`, and the discriminator's `Q.ends` records nothing there.

The two missing `G`-edges are exactly the two chain edges at the interior base body `vtx 1`: by the
degree-2 closure (`deg_two` at index `1`, valid since `3 ≤ d`) every `G`-edge at `vtx 1` is `edge 0`
(`vtx 0`–`vtx 1`) or `edge 1` (`vtx 1`–`vtx 2`). So this lemma takes the `Gab`-link recording
(`hrec'`, either neighbour order via `splitOff_swap_ab`) and the two chain-edge orientations
(`he0`/`he1`, the dispatch supplies them by a `Function.update` override of the discriminator's
`ends`) and produces the full `G`-link recording: an arbitrary `G`-link `f x y` either touches
`vtx 1` (so `f ∈ {edge 0, edge 1}`, recorded by `he0`/`he1`) or has both endpoints surviving (so
`f ≠ e₀` — `f ∈ E(G)`, `e₀ ∉ E(G)` — making it a `Gab`-link, recorded by `hrec'`).

This is the `hrec` slot the chain dispatch (`chainData_dispatch`) feeds the interior arm's crux
leaf; the override edges `{edge 0, edge 1}` are NOT `Gv = G − vtx 1`-links (each links `vtx 1`), so
they leave the arm's `hφ`/`hρe₀` `Gv`-rows untouched. Generic in `ends₀`; no `d = 3` content, no new
linear algebra, no motive/IH/contract change. No `\lean` pin (internal infra; the chain dispatch
carries the blueprint node). -/
lemma _root_.Graph.ChainData.fullLink_recording_of_splitOff_recording
    {G : Graph α β} {n : ℕ}
    (cd : G.ChainData n) (h3 : 3 ≤ cd.d) {ends₀ : β → α × α}
    -- the `Gab`-link recording the discriminator exposes (its `hrec'` conjunct, base split
    -- `(v, a, b) = (vtx 1, vtx 0, vtx 2)`):
    (hrec' : ∀ f x y, (G.splitOff (cd.vtx (⟨1, by omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨0, by omega⟩ : Fin cd.d).castSucc)
        (cd.vtx (⟨2, by omega⟩ : Fin cd.d).castSucc) cd.e₀).IsLink f x y →
      ends₀ f = (x, y) ∨ ends₀ f = (y, x))
    -- the two base-body chain-edge orientations (the dispatch supplies them by a `Function.update`
    -- override; `edge 0` links `vtx 0`–`vtx 1`, `edge 1` links `vtx 1`–`vtx 2`):
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

/-- **The per-member `(shiftPerm i)⁻¹` cycle transport of the `v₁`-base bottom-row disjunction
(CHAIN-2c-ii-arm, the genuine-row `hwmem` leaf `chainData_bottom_relabel`)** (`lem:case-III`
general-`d`, KT 2011 §6.4.2 eqs.~(6.54)/(6.62) the one-step-down row correspondence; Phase 23b).
The cycle generalization of the d=3 `M₃` arm's `case_III_bottom_relabel` from the single swap
`Equiv.swap a v` to the whole `(i−1)`-cycle relabel `(shiftPerm i.castSucc)⁻¹`: it takes the
`v₁`-base `removeVertex (vtx 1)` bottom-row disjunction — a member is either a genuine rigidity row
of the base framework `ofNormals (G.removeVertex (vtx 1)) ends₀ q`, or a `(vtx 2, vtx 0)`-block tag
`hingeRow (vtx 2) (vtx 0) ρ'` (the base split's fresh-edge candidate pair) — to the candidate-`i`
arm's `hwmem` disjunction, under `(funLeft (shiftPerm i.castSucc)⁻¹).dualMap`: a member of the
candidate framework's rigidity rows
`ofNormals (G.removeVertex (vtx i.castSucc)) endsσρ qρ` (with `qρ = q ∘ shiftPerm i.castSucc` the
candidate seed and `endsσρ` the `(shiftPerm i.castSucc)⁻¹`-shifted selector), or a
`(vtx (i+1), vtx (i−1))`-block tag (the candidate split's fresh-edge pair).

This is the genuine-row `hwmem` slot the relabel arm `chainData_relabel_arm` (2c-ii) feeds the
engine `case_III_arm_realization` at the per-`i` roles, exactly as `case_III_arm_realization_M3`'s
`hwmem` case feeds `case_III_bottom_relabel` at `d = 3`. The dispatch (design §(o‴)(I.6)):
* **genuine base row** `hingeRow x y r` at link `f x y` (a `removeVertex (vtx 1)` survivor) — the
  make-or-break crux `removeVertex_genuine_shiftRelabel` classifies the relabelled link as
  **either** a genuine `removeVertex (vtx i.castSucc)` link (off-cycle / interior-chain-edge images,
  both endpoints surviving — `rigidityRow_relabel_to_genuine`) **or** the candidate fresh pair
  `{vtx (i+1), vtx (i−1)}` in one of the two orders (the wrap edge `edge i`, sent to the candidate's
  fresh short-circuit, dispatched to the inline `±r` block tag by the recorded orientation);
* **base `(vtx 2, vtx 0)`-block tag** `hingeRow (vtx 2) (vtx 0) ρ'` — the relabel carries the base
  fresh pair to a *surviving* candidate link, a genuine target row (`blockRow_relabel_perm`),
  exactly as the d=3 `(ab)`-block tag maps to the genuine `e_b`-row.

The per-branch `hsupp`/`hlinkGt` ingredients are supplied by
`ofNormals_supportExtensor_relabel_perm`
(support extensors are graph-independent, so the relabel coincidence holds at the candidate split's
`removeVertex` graph) and the inverse-cycle action lemmas (`seedShift_*`, `shiftPerm_inv_*`,
`shiftEdgePerm_inv_*`). At the d=3 `M₃` instance `i = 2` the cycle `shiftPerm 2 = (v₁ v₂)` is the
single swap and this is exactly `case_III_bottom_relabel`. -/
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
  -- `ρ.symm = ρ⁻¹` for an `Equiv.Perm` (the crux states its classification in `⁻¹` form).
  have hsymm : (cd.shiftPerm i.castSucc).symm = (cd.shiftPerm i.castSucc)⁻¹ := rfl
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- Genuine base row `hingeRow x y r` at a `removeVertex (vtx 1)` survivor link `f x y`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph,
      Graph.removeVertex_isLink] at hlink
    obtain ⟨hG, hx1, hy1⟩ := hlink
    -- `r` annihilates the `(x, y)`-panel extensor (the base `f`-extensor up to the recorded
    -- orientation, so this absorbs the wrap-edge ±-orientation in one fact).
    have hperp : r (panelSupportExtensor (fun j => q (x, j)) (fun j => q (y, j))) = 0 := by
      have hr' := (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
      rw [PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends] at hr'
      rcases hrec f x y (Graph.removeVertex_isLink.mpr ⟨hG, hx1, hy1⟩) with he | he
      · rw [he] at hr'; exact hr'
      · rw [he, panelSupportExtensor_swap, map_neg, neg_eq_zero] at hr'; exact hr'
    -- The make-or-break classification of the relabelled link `(σ⁻¹ f, ρ⁻¹ x, ρ⁻¹ y)`.
    rcases cd.removeVertex_genuine_shiftRelabel i hi hG hx1 hy1 with
      hgenuine | (⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
    · -- Genuine `removeVertex (vtx i.castSucc)` image (off-cycle / interior-chain-edge): the moving
      -- genuine-row brick at `(u', w', f') = (ρ⁻¹ x, ρ⁻¹ y, σ⁻¹ f)`.
      refine Or.inl ?_
      refine PanelHingeFramework.rigidityRow_relabel_to_genuine (cd.shiftPerm i.castSucc)
        (Gt := G.removeVertex (cd.vtx i.castSucc)) hr rfl rfl hgenuine ?_
      -- `hsupp`: `Q'.supportExtensor (σ⁻¹ f) = Q.supportExtensor f` (graph-independent; the relabel
      -- coincidence cancels `ρ (ρ.symm ·) = ·` and `σ (σ⁻¹ f) = f`).
      simp only [PanelHingeFramework.toBodyHinge_supportExtensor,
        PanelHingeFramework.ofNormals_normal, PanelHingeFramework.ofNormals_ends,
        Equiv.apply_symm_apply, Equiv.Perm.coe_inv]
    · -- Wrap edge `edge i`: relabelled endpoints land on the candidate fresh pair `(vᵢ₊₁, vᵢ₋₁)`
      -- in the recorded order → `(a,b)`-block, tag `ρ' := r`. `qρ (vtx (i+1)) = q (ρ (vtx (i+1)))`
      -- `= q x` (`hxa`), `qρ (vtx (i−1)) = q y` (`hyb`), so the candidate panel is `C(q x, q y)`,
      -- which `r` annihilates (`hperp`). The relabelled row is `hingeRow (vtx (i+1)) (vtx (i−1))`
      -- `r`, the candidate block tag.
      refine Or.inr ⟨r, ?_, ?_⟩
      · have hax : cd.shiftPerm i.castSucc (cd.vtx i.succ) = x := by
          rw [← hxa]; exact Equiv.apply_symm_apply _ _
        have hby : cd.shiftPerm i.castSucc
            (cd.vtx (⟨(i : ℕ) - 1, by omega⟩ : Fin cd.d).castSucc) = y := by
          rw [← hyb]; exact Equiv.apply_symm_apply _ _
        simp only [hax, hby]; exact hperp
      · simp only [BodyHingeFramework.hingeRow_funLeft_dualMap, hsymm, hxa, hyb]
    · -- Wrap edge, swapped recorded order → `(a,b)`-block, tag `ρ' := -r`. Here `ρ` sends the
      -- candidate fresh pair the other way (`qρ (vtx (i+1)) = q y`, `qρ (vtx (i−1)) = q x`), so the
      -- candidate panel is `C(q y, q x) = -C(q x, q y)`, annihilated by `r` (`hperp`); the
      -- relabelled row `hingeRow (vtx (i−1)) (vtx (i+1)) r` is `hingeRow (vtx (i+1)) (vtx (i−1))`
      -- `(-r)` (by `hingeRow_swap`).
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
  · -- Base `(vtx 2, vtx 0)`-block tag: relabel carries the base fresh pair to the surviving
    -- candidate link `edge 0` (link `vtx 1 — vtx 0`), a genuine target row (via
    -- `blockRow_relabel_perm`).
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
    · -- `hsupp`: `Q'.supportExtensor (edge 0) = base extensor at σ (edge 0) = e₀`, recorded by
      -- `he₀rec` at the base candidate pair `(vtx 2, vtx 0)`.
      simp only [PanelHingeFramework.ofNormals_supportExtensor_relabel_perm
        (cd.shiftPerm i.castSucc) (cd.shiftEdgePerm i),
        cd.shiftEdgePerm_apply_edge_zero i (by omega),
        PanelHingeFramework.toBodyHinge_supportExtensor, PanelHingeFramework.ofNormals_normal,
        PanelHingeFramework.ofNormals_ends, he₀rec]

/-- **A relabel-image genuine row lands in the candidate's rigidity-row span** (`lem:case-III
general-d`, the option-(A) chain arm's per-summand `±r`-row routing brick, Phase 23c §I.8.24(4.6);
Katoh–Tanigawa 2011 §6.4.2 the (6.62) one-step-down row correspondence carried into the candidate
framework). The atomic per-summand step of the chain arm's `±r`-row `hg` membership: a base genuine
rigidity row `hingeRow u w r` (`r ∈ (ofNormals Gs ends₀ q₀).hingeRowBlock f`) whose relabel `ρ`
sends its endpoints to a surviving candidate-`(G − vᵢ)` link `f'` **off the two candidate-overridden
slots `{e_c, e_r}`** transports under `(funLeft ρ.symm).dualMap` into the span of the candidate
framework `caseIIICandidate (G − vᵢ) endsσρ qρ e_c e_r n_u n' n_r t`'s rigidity rows.

This composes the two landed bricks the §I.8.24(4.6) Hand-off names: the relabel image is a genuine
row of the *seed* framework `ofNormals (G − vᵢ) endsσρ qρ` (member-MOVING, KT (6.62)) carried into
the candidate's rigidity rows by the off-slot seed-coincidence row bridge
`hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link`
(`caseIIICandidate_supportExtensor_of_ne`), then `Submodule.subset_span`. The full `±r`-row `hg`
GROUP leaf (`funLeft_dualMap_pmR_group_mem_span_caseIIICandidate` below) `map_sum`s over this brick:
A-1's edge-`i` group is `∑ⱼ cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)`, so its relabel image is the
`cⱼ`-combination of these per-summand candidate-span members, hence in the span (closed under
`+`/`•`). The candidate-link survival + off-slot conditions are discharged by the caller from the
chain edge-correspondence (the arm). NO motive/IH/contract change; member-MOVING, no wall (the `±r`
row enters as a genuine candidate-edge member, never the collapsed fixed member). -/
theorem PanelHingeFramework.funLeft_dualMap_genuineRow_mem_span_caseIIICandidate
    [DecidableEq β] {G : Graph α β} (ρ : Equiv.Perm α)
    {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → K} {vᵢ : α}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → K}
    {e_c e_r : β} {n_u n' n_r : Fin (k + 2) → K} {t : K}
    {f f' : β} {u w u' w' : α} {r : Module.Dual K (ScrewSpace K k)}
    (hr : r ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock f)
    (hu : ρ.symm u = u') (hw : ρ.symm w = w')
    (h1 : f' ≠ e_c) (h2 : f' ≠ e_r)
    (hlinkGt : (G.removeVertex vᵢ).IsLink f' u' w')
    (hsupp : (PanelHingeFramework.ofNormals (G.removeVertex vᵢ) endsσρ
          qρ).toBodyHinge.supportExtensor f'
        = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor f) :
    (LinearMap.funLeft K (ScrewSpace K k) ρ.symm).dualMap (BodyHingeFramework.hingeRow u w r) ∈
      Submodule.span K (PanelHingeFramework.caseIIICandidate (G.removeVertex vᵢ) endsσρ qρ
        e_c e_r n_u n' n_r t).rigidityRows := by
  -- The relabel image is `hingeRow u' w' r` (member-MOVING, `hu`/`hw`).
  rw [BodyHingeFramework.hingeRow_funLeft_dualMap, hu, hw]
  -- The seed-side block membership at the candidate-`(G − vᵢ)` edge `f'`: `r` annihilates the seed
  -- framework's `f'`-extensor, which `hsupp` identifies with the base `f`-extensor (`hr`).
  have hr' : r ∈ (PanelHingeFramework.ofNormals (G.removeVertex vᵢ) endsσρ
      qρ).toBodyHinge.hingeRowBlock f' := by
    rw [BodyHingeFramework.mem_hingeRowBlock_iff, hsupp]
    exact (BodyHingeFramework.mem_hingeRowBlock_iff _ f r).1 hr
  -- The off-slot row bridge carries the genuine seed row into the candidate's rigidity rows.
  exact Submodule.subset_span
    (PanelHingeFramework.hingeRow_mem_caseIIICandidate_rigidityRows_of_ofNormals_link
      (G.removeVertex vᵢ) endsσρ qρ e_c e_r n_u n' n_r t h1 h2 hlinkGt hr')

/-- **The `±r`-row candidate-span `hg` GROUP membership** (`lem:case-III general-d`, the option-(A)
chain arm's `hg` membership for the `±r` corner row, Phase 23c §I.8.24(4.6); Katoh–Tanigawa 2011
§6.4.2 eq. (6.66), the abstract redundancy `r` carried as a GENUINE candidate-edge group, member-
MOVING). The `±r` row of the chain cert's corner block `g` is the relabel image
`(funLeft (shiftPerm i.castSucc)⁻¹).dualMap` of A-1's edge-`i` base group
`∑_{evⱼ = edge i} cⱼ • hingeRow (uvⱼ)(vvⱼ)(rvⱼ)` — KT's GENUINE candidate-edge `(vᵢvᵢ₊₁)ᵢ∗` row, NOT
the collapsed `hingeRow vᵢ₊₁ vᵢ₋₁ (−ρ₀)` of the dead `chainData_relabel_arm_hρGv` (the
member-mapping wall; the collapsed form would force `ρ₀ ⊥ panelSupportExtensor`, contradicting the
discriminator `hgate`, which is exactly why it is the independent `D`-th row). This GROUP leaf is
what the chain arm puts in the cert's `g`-corner as `rRow`, and the cert
`case_III_rank_certification_chain`'s `hg` is its direct consequence (`Submodule.span`-membership).

The proof is the `map_sum`/`map_smul` push of the relabel-image linear map over the filtered group,
landing each summand in the candidate span by the per-summand brick
`funLeft_dualMap_genuineRow_mem_span_caseIIICandidate` (the relabel image of one genuine base hinge
row at an off-slot surviving candidate link is a candidate-span member), then closing the
`cⱼ`-combination by the span's `+`/`•`-closure (`Submodule.sum_mem`/`smul_mem`). The per-summand
transport data — the relabel image endpoints, the candidate-link survival, the off-slot edge —
enters as a bundled hypothesis `htransport` the arm discharges from the chain edge-correspondence
(KT (6.62) the one-step-down link map, plus the off-`{e_c, e_r}` slot condition). NO motive/IH/
contract change; the `±r` row enters as a genuine candidate-edge member, no wall. -/
theorem PanelHingeFramework.funLeft_dualMap_pmR_group_mem_span_caseIIICandidate
    [DecidableEq β] {G : Graph α β} (ρ : Equiv.Perm α)
    {endsσρ : β → α × α} {qρ : α × Fin (k + 2) → K} {vᵢ : α}
    {Gs : Graph α β} {ends₀ : β → α × α} {q₀ : α × Fin (k + 2) → K}
    {e_c e_r : β} {n_u n' n_r : Fin (k + 2) → K} {t : K}
    {m : ℕ} (c : Fin m → K) (ev : Fin m → β) (uv vv : Fin m → α)
    (rv : Fin m → Module.Dual K (ScrewSpace K k)) (e_i : β)
    -- A-1's per-summand base block memberships (the `hrv` of the edge-grouped redundancy):
    (hrv : ∀ j, rv j ∈ (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.hingeRowBlock (ev j))
    -- the per-summand relabel transport data the arm discharges from the chain edge-correspondence:
    (htransport : ∀ j ∈ Finset.univ.filter (fun j => ev j = e_i),
      ∃ f' u' w', ρ.symm (uv j) = u' ∧ ρ.symm (vv j) = w' ∧ f' ≠ e_c ∧ f' ≠ e_r ∧
        (G.removeVertex vᵢ).IsLink f' u' w' ∧
        (PanelHingeFramework.ofNormals (G.removeVertex vᵢ) endsσρ qρ).toBodyHinge.supportExtensor f'
          = (PanelHingeFramework.ofNormals Gs ends₀ q₀).toBodyHinge.supportExtensor (ev j)) :
    (LinearMap.funLeft K (ScrewSpace K k) ρ.symm).dualMap
        (∑ j ∈ Finset.univ.filter (fun j => ev j = e_i),
          c j • BodyHingeFramework.hingeRow (uv j) (vv j) (rv j)) ∈
      Submodule.span K (PanelHingeFramework.caseIIICandidate (G.removeVertex vᵢ) endsσρ qρ
        e_c e_r n_u n' n_r t).rigidityRows := by
  classical
  -- Push the relabel-image map through the `cⱼ`-combination (`map_sum`/`map_smul`).
  rw [map_sum]
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  -- Each summand's relabel image lands in the candidate span by the per-summand brick.
  obtain ⟨f', u', w', hu, hw, h1, h2, hlinkGt, hsupp⟩ := htransport j hj
  exact PanelHingeFramework.funLeft_dualMap_genuineRow_mem_span_caseIIICandidate ρ
    (hrv j) hu hw h1 h2 hlinkGt hsupp

/-- **W9b — the `M₃` bottom-row tag transport** (the per-member relabel of one W6b bottom-family
member, design §1.52(c); Katoh–Tanigawa 2011 §6.4.1 eqs.~(6.39)/(6.41), Phase 22h). One bottom row
`φ` of the v-split W6b package — tagged either a genuine `R(G_v, q)`-row or an `(ab)`-block row
`hingeRow a b ρ'` (`ρ' ⊥ C(q(ab))`) — relabels under `(funLeft (a v)).dualMap` to a row tagged in
the `M₃`-arm shape: either a genuine row of the `G − a` framework at the overridden selector `ends₃`
and the relabeled seed `qρ = q ∘ (a v)`, or a `(c, v)`-block row `hingeRow c v ρ'`
(`ρ' ⊥ C(q(ac))`). This is exactly KT's eq.~(6.39) row correspondence `(vb)_j ↔ (ab)_j`,
`(va)_j ↔ (ac)_j`, `e_j ↔ e_j` read row-wise: the `(ab)`-block row maps to the genuine `e_b`-row of
`G − a` (`ends₃ e_b = (v, b)`, `qρ(v,·) = n_a`, `qρ(b,·) = n_b`); a `G_v`-row at the degree-2 body
`a`'s only edge `e_c = ac` maps to the candidate-shaped `(c, v)`-block row; every other `G_v`-row is
fixed by the swap and survives as a genuine `G − a`-row.

W9c maps this over the bottom family `w` to feed `case_III_arm_realization`'s `hwmem` slot at the
`M₃` roles. **§38:** every membership is built from an explicit link witness (the `hrow_mem` idiom)
and every extensor evaluation goes through `toBodyHinge_supportExtensor`/`ofNormals_ends`/
`ofNormals_normal` plus the `Equiv.swap` evaluation lemmas — never `whnf` on the `ofNormals`
carrier. -/
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
  -- The relabeled seed at body `x` reads `q` at the swapped body: `qρ(x,·) = q(swap a v x, ·)`.
  rcases hφ with hgen | ⟨ρ', hρ'e₀, rfl⟩
  · -- The `G_v`-row tag: destructure the generator and case on `a ∈ {x, y}`.
    obtain ⟨f, x, y, hlink, r, hr, rfl⟩ := hgen
    rw [hFv, PanelHingeFramework.toBodyHinge_graph, PanelHingeFramework.ofNormals_graph] at hlink
    rw [BodyHingeFramework.hingeRow_funLeft_dualMap]
    obtain ⟨hxv, hyv⟩ := hnov f x y hlink
    have hGflink := hGv_le f x y hlink
    -- `r`'s annihilation at `Fv`'s `f`-extensor (the `q`-seed at `ends₀ f`).
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
      · -- x ≠ a, y ≠ a: the swap fixes both endpoints; the image is the generator itself, a
        -- genuine `G − a`-row at the overridden selector `ends₃`.
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxv, Equiv.swap_apply_of_ne_of_ne hya hyv]
        -- the image `hingeRow x y r` is a genuine row of `Fva`: the link survives `removeVertex a`
        -- and the `f`-extensor at `Fva` equals the `Fv`-extensor `r` annihilates.
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
  · -- The `(ab)`-block tag `φ = hingeRow a b ρ'`: relabel to the genuine `e_b`-row.
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

/-- **G4d-i — the `a`-column restriction of a `G_v`-row-span vector lies in `hingeRowBlock e_c`**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). Given `wGv` in the span of a framework
`Fv`'s rigidity rows and the degree-2-at-`a` constraint that `e_c` is the *only* edge of `Fv`
incident to `a` (endpoints `a`, `c` with `a ≠ c`), the column restriction `wGv ∘ single a` lies
in the `e_c`-hinge-row block of a second framework `Fab` whose `e_c`-block agrees with `Fv`'s
(`hblock`).

The proof is a `Submodule.span_induction` on `hwGv`:
- For each generator `hingeRow u w ρ ∈ Fv.rigidityRows` (link `f u w`, `ρ ∈ Fv.hingeRowBlock f`):
  - If `u = a`: then `hdeg2 f w hlink` forces `f = e_c`, so
    `ρ ∈ Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c`
    and `(hingeRow a w ρ) ∘ single a = ρ` (`hingeRow_comp_single_tail hac`).
  - If `w = a` (but `u ≠ a`): `hdeg2r f u hlink` forces `f = e_c`; rewrite via `hingeRow_swap`
    (`hingeRow u a ρ = hingeRow a u (−ρ)`) and `hingeRow_comp_single_tail`; the block is a
    submodule so `−ρ` stays in it.
  - Otherwise `u ≠ a` and `w ≠ a`: `hingeRow_comp_single_off` gives zero, which is in any block.
- The `zero`, `add`, and `smul` cases follow from submodule closure. -/
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

/-- **G4d-ii — the `M₃` candidate hinge row lies in the `a`-split rigidity-row span**
(`lem:case-III-claim612-eq644`, §1.49(4), Phase 22h). From G4d-i
(`acolumn_mem_hingeRowBlock_of_span_rigidityRows`) —
`r̂ := wGv.comp(single a) ∈ Fab.hingeRowBlock e_c`
— together with `hingeRow_mem_rigidityRows` (the membership certificate for a single hinge row),
the row `hingeRow a c r̂` lies in the rigidity-row *set* of the `v`-split framework `Fv` (since
`hlink_ec : Fv.graph.IsLink e_c a c` and `hblock ▸ hr̂`), and hence in the
`Submodule.span` of `Fv.rigidityRows`.

This is the `M₃` analogue of `exists_candidate_row_eq612`'s `hcand_mem` output: the common
candidate vector `r̂` — the `a`-column restriction of the `G_v`-redundant row — serves as the
block functional for a `hingeRow a c r̂` rigidity row, whose `e_c`-hinge lies in `Fv`. -/
theorem BodyHingeFramework.hingeRow_acolumn_mem_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework K k α β}
    {a c : α} {e_c : β}
    (hac : a ≠ c)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hblock : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c)
    {wGv : Module.Dual K (α → ScrewSpace K k)}
    (hwGv : wGv ∈ Submodule.span K Fv.rigidityRows) :
    BodyHingeFramework.hingeRow (k := k) (α := α) a c
        (wGv.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a))
      ∈ Submodule.span K Fv.rigidityRows := by
  apply Submodule.subset_span
  apply hingeRow_mem_rigidityRows Fv hlink_ec
  rw [hblock]
  exact acolumn_mem_hingeRowBlock_of_span_rigidityRows hac hlink_ec hblock hdeg2 hdeg2r hwGv

/-- **G4d-i for a degree-2 vertex with *two* surviving edges — the `a`-column lands in the sum of
the two incident blocks** (`lem:case-III-claim612-eq644` two-edge form; Katoh–Tanigawa 2011 §6.4.2,
eq.~(6.44) iterated, the genuinely-new `hρGv` P2 leaf, CHAIN-2c-ii-arm). The honest analogue of the
one-edge `acolumn_mem_hingeRowBlock_of_span_rigidityRows` (which forces the column into a *single*
block when `a`'s sole surviving edge is `e_c = ac`) for an **interior chain vertex** `a`, which
after the relabel surgery has **two** surviving links `e_c = ac` and `e_d = ad` (`c ≠ d`). For a
span member `wGv ∈ span Fv.rigidityRows`, its `a`-column restriction `wGv ∘ single a` lands in the
**sum** `Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d`: a generator `hingeRow u w ρ` (with
`ρ ∈ Fv.hingeRowBlock f`) touching `a` is, by the two-edge degree-2 field, an `e_c = ac`- or
`e_d = ad`-row, contributing `ρ` (via `hingeRow_comp_single_tail`/`hingeRow_swap`) to the respective
block; a row off `a` contributes `0` (`hingeRow_comp_single_off`). This is KT's eq.~(6.44) two-block
cancellation `∑λ(vₛvₛ₊₁)·r + ∑λ(vₛ₊₁vₛ₊₂)·r = 0` at an interior chain vertex `vₛ₊₁` of degree two —
the carry the `acolumn` one-edge form cannot supply (its `hdeg2` single-edge premise is *false* at a
two-edge vertex). -/
theorem BodyHingeFramework.acolumn_mem_hingeRowBlock_sup_of_span_rigidityRows
    [DecidableEq α] {Fab Fv : BodyHingeFramework K k α β}
    {a c d : α} {e_c e_d : β}
    (hac : a ≠ c) (had : a ≠ d)
    (hlink_ec : Fv.graph.IsLink e_c a c)
    (hlink_ed : Fv.graph.IsLink e_d a d)
    (hblock_c : Fv.hingeRowBlock e_c = Fab.hingeRowBlock e_c)
    (hblock_d : Fv.hingeRowBlock e_d = Fab.hingeRowBlock e_d)
    -- `a` is degree-2 in `Fv`: its only links are `e_c = ac` and `e_d = ad`.
    (hdeg2 : ∀ f x, Fv.graph.IsLink f a x → f = e_c ∨ f = e_d)
    (hdeg2r : ∀ f x, Fv.graph.IsLink f x a → f = e_c ∨ f = e_d)
    {wGv : Module.Dual K (α → ScrewSpace K k)}
    (hwGv : wGv ∈ Submodule.span K Fv.rigidityRows) :
    wGv.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a)
      ∈ Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d := by
  apply Submodule.span_induction (p := fun ψ _ =>
    ψ.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a)
      ∈ Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d) _ _ _ _ hwGv
  · -- generator case: `hingeRow u w ρ ∈ Fv.rigidityRows`, so `ρ ∈ Fv.hingeRowBlock f`.
    rintro ψ ⟨f, u, w, hlink, ρ, hρ, rfl⟩
    by_cases hau : u = a
    · -- `u = a`: `hdeg2` forces `f ∈ {e_c, e_d}`; `IsLink.right_unique` pins `w` accordingly.
      rw [hau] at hlink
      rcases hdeg2 f w hlink with hfc | hfd
      · rw [hfc] at hlink hρ
        have hwc : w = c := hlink.right_unique hlink_ec
        rw [hau, hwc, hingeRow_comp_single_tail hac]
        exact Submodule.mem_sup_left (hblock_c ▸ hρ)
      · rw [hfd] at hlink hρ
        have hwd : w = d := hlink.right_unique hlink_ed
        rw [hau, hwd, hingeRow_comp_single_tail had]
        exact Submodule.mem_sup_right (hblock_d ▸ hρ)
    · by_cases hwa : w = a
      · -- `w = a`, `u ≠ a`: `hdeg2r` forces `f ∈ {e_c, e_d}`; pin `u` via `IsLink.right_unique`.
        rw [hwa] at hlink
        rcases hdeg2r f u hlink with hfc | hfd
        · rw [hfc] at hlink hρ
          have huc : u = c := hlink.symm.right_unique hlink_ec
          rw [hwa, hingeRow_swap u a ρ, huc, hingeRow_comp_single_tail hac]
          exact Submodule.mem_sup_left ((Fab.hingeRowBlock e_c).neg_mem (hblock_c ▸ hρ))
        · rw [hfd] at hlink hρ
          have hud : u = d := hlink.symm.right_unique hlink_ed
          rw [hwa, hingeRow_swap u a ρ, hud, hingeRow_comp_single_tail had]
          exact Submodule.mem_sup_right ((Fab.hingeRowBlock e_d).neg_mem (hblock_d ▸ hρ))
      · -- `u ≠ a`, `w ≠ a`: off-column, restricts to `0`.
        rw [hingeRow_comp_single_off (Ne.symm hau) (Ne.symm hwa)]
        exact (Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).zero_mem
  · simp [(Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).zero_mem]
  · intro x y _ _ hx hy
    rw [LinearMap.add_comp]
    exact (Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).add_mem hx hy
  · intro r x _ hx
    rw [LinearMap.smul_comp]
    exact (Fab.hingeRowBlock e_c ⊔ Fab.hingeRowBlock e_d).smul_mem r hx

/-! ### The interior-vertex eq.~(6.44) two-edge perp carry (CHAIN-2c-ii-arm, the `hρGv` P2 A-2
de-risk core)

The genuinely-new, self-contained carrier of the `hρGv` arm's per-edge perpendicularity obligation
(`i3_freshEdge_surviving_rows_mem_deRisk`'s `hperp0`/`hperp1`, `freshEdge_surviving_row_mem`'s
`hperp`), discharged FOR REAL from the eq.~(6.52) redundancy witness rather than the *refuted*
generic-`ρ₀` isolated implication (`notes/Phase23-design.md` §(o‴)(I.8.3.v-REFUTED): the bare
`ρ₀ ∈ hingeRowBlock (edge s) → ρ₀ ∈ hingeRowBlock (edge (s+1))` over an arbitrary `ρ₀` is FALSE —
the two-edge crux gives only *sup* membership, and for independent consecutive panels
`block e_c ⊔ block e_d = ⊤`, vacuous). The SETTLED route (§(o‴)(I.8.3.v-SETTLED), Route A) routes
the perp through the **specific** redundancy combination `r̂ := ∑_j λ_{(ab)j} r_j`, whose interior
`a`-columns are non-trivial.

This is the interior-chain-vertex instance of KT's eq.~(6.44) `r̂ = −rAC`
(`candidateRow_ac_eq_neg`, the landed `d = 3` single-degree-2-vertex column equation, KT §6.4.1
eq.~(6.44)) — that lemma already takes the per-edge-grouped witness and **applies verbatim at an
interior chain vertex** `a = vₛ₊₁` (degree-2, incident edges `ab = vₛ₊₁vₛ` and `ac = vₛ₊₁vₛ₊₂`),
which is the structural fix the refuted isolated-implication missed. -/

/-- **The interior-vertex eq.~(6.44) two-edge perp carry** (`lem:case-III-claim612-eq644` interior
form; Katoh–Tanigawa 2011 §6.4.1, eq.~(6.44) at an interior chain vertex, the `hρGv` P2 A-2 de-risk
core, CHAIN-2c-ii-arm, `notes/Phase23-design.md` §(o‴)(I.8.3.v-SETTLED) Route A; Phase 23b). At a
**degree-2** body `a` with the two incident edges' hinges read into the distinct bodies `b` and `c`,
the common candidate vector `r̂ := ∑_j λ_{(ab)j} (rab j)` of KT's eq.~(6.42) is perpendicular to
**both** incident panels `C_c = F.supportExtensor e_c` and `C_d = F.supportExtensor e_d`:

* `r̂ ∈ F.hingeRowBlock e_c` is **direct** — each `rab j ∈ F.hingeRowBlock e_c` (the `ab`-rows are
  block functionals of the `e_c = ab`-hinge), and the block is a submodule closed under the
  `λ`-combination.
* `r̂ ∈ F.hingeRowBlock e_d` is **via eq.~(6.44)** — `candidateRow_ac_eq_neg` reads the column
  vanishing `hcol` of the redundancy combination at body `a` (its degree-2 column has only the
  `ab`/`ac` blocks, `hingeRow_comp_single_tail`/`_off`) as `rAC = −r̂` with
  `rAC := ∑_j λ_{(ac)j} (rac j)`; since each `rac j ∈ F.hingeRowBlock e_d`, so is `rAC`, hence so is
  `r̂ = −rAC` (the block's `neg_mem`).

So `r̂` lies in `hingeRowBlock e_c ⊓ hingeRowBlock e_d` — perpendicular to both incident chain-edge
panels at once. This is the iterated-carry's per-vertex step (KT carries the single redundancy `r̂`
`±`-ly across the `d` panels, eq.~(6.66)); chaining it from the W6b `hρe₀` base discharges the
surviving-row perp at every interior chain edge (`freshEdge_surviving_row_mem`'s `hperp`,
`i3_freshEdge_surviving_rows_mem_deRisk`'s `hperp0`/`hperp1`). Self-contained over the explicit
eq.~(6.52) per-edge witness (the `λ`/`r` data + the combination's `a`-column vanishing): **zero
blast radius**, no live caller touched — the W6b producer strengthening that *supplies* this (A-1)
is the next step. The `supportExtensor`-perp form `..._perp` below is the direct `hperp` shape. -/
theorem BodyHingeFramework.candidate_perp_two_incident_panels [DecidableEq α]
    (F : BodyHingeFramework K k α β) {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} {e_c e_d : β} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → K) (rab : ιab → Module.Dual K (ScrewSpace K k))
    (lamAC : ιac → K) (rac : ιac → Module.Dual K (ScrewSpace K k))
    (grest : Module.Dual K (α → ScrewSpace K k))
    (hrab : ∀ j, rab j ∈ F.hingeRowBlock e_c)
    (hrac : ∀ j, rac j ∈ F.hingeRowBlock e_d)
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0)
    (hrest : grest.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0) :
    (∑ j, lamAB j • rab j) ∈ F.hingeRowBlock e_c ∧
      (∑ j, lamAB j • rab j) ∈ F.hingeRowBlock e_d := by
  -- eq.~(6.44): `rAC = −r̂` (the redundancy combination's `a`-column vanishing, regrouped by edge).
  have heq : ∑ j, lamAC j • rac j = -∑ j, lamAB j • rab j :=
    candidateRow_ac_eq_neg hab hac lamAB rab lamAC rac grest hcol hrest
  refine ⟨Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrab j), ?_⟩
  -- `r̂ = −rAC`, and `rAC ∈ block e_d` (the `λ`-combination of the `ac`-block rows).
  rw [← neg_neg (∑ j, lamAB j • rab j), ← heq]
  exact (F.hingeRowBlock e_d).neg_mem
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hrac j))

/-- **The interior-vertex eq.~(6.44) two-edge perp carry, `supportExtensor`-perp form** — the direct
`hperp` shape of `i3_freshEdge_surviving_rows_mem_deRisk` / `freshEdge_surviving_row_mem`
(`lem:case-III-claim612-eq644` interior form; Katoh–Tanigawa 2011 §6.4.1, eq.~(6.44), the
CHAIN-2c-ii-arm `hρGv` P2 A-2 de-risk, Phase 23b). The `mem_hingeRowBlock_iff` restatement of
`candidate_perp_two_incident_panels`: the common candidate vector `r̂ := ∑_j λ_{(ab)j} (rab j)`
annihilates **both** incident panels `F.supportExtensor e_c` and `F.supportExtensor e_d`, given the
per-edge perps in `supportExtensor` form (`hperp_ab`/`hperp_ac`) and the eq.~(6.43) column vanishing
(`hcol`/`hrest`). This is exactly the perp obligation the de-risk gate carries as `hperp0`/`hperp1`
hypotheses — discharged here from the eq.~(6.52) witness, **zero blast radius**. -/
theorem BodyHingeFramework.candidate_perp_two_incident_supportExtensors [DecidableEq α]
    (F : BodyHingeFramework K k α β) {ιab ιac : Type*} [Fintype ιab] [Fintype ιac]
    {a b c : α} {e_c e_d : β} (hab : a ≠ b) (hac : a ≠ c)
    (lamAB : ιab → K) (rab : ιab → Module.Dual K (ScrewSpace K k))
    (lamAC : ιac → K) (rac : ιac → Module.Dual K (ScrewSpace K k))
    (grest : Module.Dual K (α → ScrewSpace K k))
    (hperp_ab : ∀ j, rab j (F.supportExtensor e_c) = 0)
    (hperp_ac : ∀ j, rac j (F.supportExtensor e_d) = 0)
    (hcol : ((∑ j, lamAB j • BodyHingeFramework.hingeRow (k := k) (α := α) a b (rab j))
        + (∑ j, lamAC j • BodyHingeFramework.hingeRow (k := k) (α := α) a c (rac j)) + grest).comp
        (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0)
    (hrest : grest.comp (LinearMap.single K (fun _ : α => ScrewSpace K k) a) = 0) :
    (∑ j, lamAB j • rab j) (F.supportExtensor e_c) = 0 ∧
      (∑ j, lamAB j • rab j) (F.supportExtensor e_d) = 0 := by
  obtain ⟨hc, hd⟩ := F.candidate_perp_two_incident_panels hab hac lamAB rab lamAC rac grest
    (fun j => (F.mem_hingeRowBlock_iff _ _).2 (hperp_ab j))
    (fun j => (F.mem_hingeRowBlock_iff _ _).2 (hperp_ac j)) hcol hrest
  exact ⟨(F.mem_hingeRowBlock_iff _ _).1 hc, (F.mem_hingeRowBlock_iff _ _).1 hd⟩


end CombinatorialRigidity.Molecular
