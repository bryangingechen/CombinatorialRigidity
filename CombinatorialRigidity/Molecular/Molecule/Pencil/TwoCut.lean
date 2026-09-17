/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.RigidityMatrix.Bricks
import CombinatorialRigidity.Molecular.AlgebraicInduction.GenericityDevice

/-!
# The vertex 2-cut loss carriers (Phase 39 PENCIL, item 6, Layer C)

Layer C of the item-6 build (`notes/Phase39.md` *Lemma checklist*, item 6; carrier recon
`notes/Phase39-design.md` § *Item-6 carrier recon (2026-09-16)*): the two **loss** carriers
`pencilLoss` (`a`) and `weldedLoss` (`a_w`) of `notes/pencil/workbook/attack-smark.md` § S10(ii),
and the pure-algebra identity `finrank_relScrews_eq` (`ρ = δ + a − a_w`) relating them to the
combinatorial gap `Graph.pairDelta` (`Molecular/Deficiency.lean`) and the geometric relative-screw
dimension `relScrews` (`Molecular/RigidityMatrix/Bricks.lean`, `section TwoCutCarriers`).

This site is necessarily **non-`module`**: the losses need `Graph.bodyBarDim`, which lives in the
non-`module` `BodyBar/Framework.lean`, and a `module` file can only import other `module` files
(`LEAN-OPS.md`). A non-`module` importer unfolds the Layer-B carriers (`relScrews`, `rigidityRows`,
`weldedRank`) directly by `rfl`/`unfold` — there is no exposure obligation here (settled
2026-09-17, `notes/Phase39.md` *Lemma checklist*, B1–B4 entry).

`pencilLoss` is exactly the negation of `HasPencilRealization`'s rank conjunct (`= 0` iff `G`
attains the deficiency rank): `screwDim k · (|V|−1) − def(G̃) − rank(G,p)`. Its nonnegativity
(**C1ℓ**) is not new mathematics — it is the landed
`BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`
(`Molecular/AlgebraicInduction/GenericityDevice.lean`) re-expressed over this carrier, with the
same three hypotheses carried through unchanged. `weldedLoss` is the same quantity for the
framework *with `u, v` welded*: `screwDim k · (|V|−1) − g − rank_w`, where `g = deficiencyMerged`
is the combinatorial deficiency over labelings that keep `u, v` together, and `rank_w = weldedRank`
is its geometric counterpart — note the coefficient is `|V|−1`, **not** `|V|−2`: the welded space
still sits inside the `|V|`-body assignment space, the weld only adds rows
(`notes/Phase39-design.md` § *Item-6 carrier recon*, the loss carriers; the `(|V|−2)` shape was
the recon's own first guess, caught by the numerics).

`finrank_relScrews_eq` (**C3ℓ**) is pure algebra over the landed welded-rank identity
`weldedRank_eq` (`rank_w = rank + ρ`, Layer B4): unfolding all three carriers, the
`screwDim k · (|V|−1)` term cancels identically between `pencilLoss` and `weldedLoss` (both carry
the same `bodyBarDim`-free coefficient), leaving `δ + a − a_w = rank_w − rank = finrank ρ̄` by
`weldedRank_eq` alone. No `hn : bodyBarDim n = screwDim k` hypothesis is needed for this identity —
it is needed only by the nonnegativity statements, which read the two losses' *sign*, not their
difference.

**C2ℓ** `weldedLoss_nonneg` (`0 ≤ a_w`) is the substantive inequality here, and it is the
transcribed welded bound `ρ ≤ δ + a` in disguise — over C3ℓ the two are interchangeable, which is
what `finrank_relScrews_le` records.  It runs on the **merged** relative hub
`screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions`: the landed hub's counting
argument applied to a labeling that keeps `u, v` together, whose partition-respecting motions are
therefore welded motions (`partitionMotions_le_jointMotions_bot`), turned from a motion lower
bound into a rank upper bound by the Layer-B codimension
`weldedRank_add_finrank_jointMotions_bot`.

The headline target `pencilLoss_vertexTwoCut` (**C4ℓ**) and the deferred general-`U` profile laws
are not in this slice; see `notes/Phase39.md` *Lemma checklist*, item 6.

**Two pinned instances were dead and are dropped** (`lake lint`'s `unusedArguments`, the same
pattern already found throughout Layer B): the two `def`s need no `[Finite α]` — `Module.finrank`
and `Set.ncard` are total, giving junk on an infinite space rather than failing to typecheck — and
`finrank_relScrews_eq` needs no `[Finite β]`, since its one geometric input `weldedRank_eq` (B4)
doesn't either.

See `notes/Phase39.md`, `notes/Phase39-design.md`, and `blueprint/src/chapter/pencil.tex`
(no blueprint node yet for this section — `notes/Phase39.md` *Blockers*, D5).
-/

namespace CombinatorialRigidity.Molecular

open scoped Graph

variable {K : Type*} [Field K]

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-- **`a` — the pencil loss** (Phase 39's `pencilLoss`, `notes/pencil/workbook/attack-smark.md`
§ S10(ii)): the gap between the `D·(|V|−1)` target rank and the rigidity-row span's actual
dimension, corrected by the combinatorial deficiency —
`screwDim k · (|V(G)|−1) − def(G̃) − rank(G,p)`. Exactly the negation of
`HasPencilRealization`'s rank conjunct: `a = 0` iff `G` attains the deficiency rank. -/
noncomputable def pencilLoss (F : BodyHingeFramework K k α β) (n : ℕ) : ℤ :=
  (screwDim k : ℤ) * ((V(F.graph).ncard : ℤ) - 1) - F.graph.deficiency n
    - (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)

/-- **`a_w` — the welded loss** (Phase 39's `weldedLoss`, same reference): `pencilLoss`'s
quantity for the framework with `u, v` welded — `screwDim k · (|V(G)|−1) − g − rank_w`, with
`g = F.graph.deficiencyMerged n u v` the combinatorial deficiency over labelings keeping `u, v`
together and `rank_w = F.weldedRank u v` its geometric counterpart. The coefficient is
`|V(G)|−1`, not `|V(G)|−2`: the welded space still sits inside the `|V|`-body assignment space,
the weld only adjoins rows (`notes/Phase39-design.md` § *Item-6 carrier recon*, the loss
carriers). -/
noncomputable def weldedLoss (F : BodyHingeFramework K k α β) (n : ℕ) (u v : α) : ℤ :=
  (screwDim k : ℤ) * ((V(F.graph).ncard : ℤ) - 1) - F.graph.deficiencyMerged n u v
    - (F.weldedRank u v : ℤ)

/-- **C1ℓ: the pencil loss is nonnegative** (`notes/pencil/workbook/attack-smark.md` § S10(ii)):
`0 ≤ F.pencilLoss n`. Not new mathematics — it is exactly the landed
`finrank_span_rigidityRows_add_deficiency_le`, re-expressed over the `pencilLoss` carrier by
`unfold` and `linarith`; the three hypotheses (`hn`, `hne`, `hC`) carry through unchanged. -/
theorem pencilLoss_nonneg [Finite α] [Finite β] {k n : ℕ}
    (F : BodyHingeFramework K k α β) (hn : Graph.bodyBarDim n = screwDim k)
    (hne : V(F.graph).Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) :
    0 ≤ F.pencilLoss n := by
  have h := F.finrank_span_rigidityRows_add_deficiency_le hn hne hC
  unfold pencilLoss
  linarith

/-- **C3ℓ: the relative-screw dimension is the gap between the deficiency delta and the two
losses** (`notes/pencil/workbook/attack-smark.md` § S10(ii): `ρ = δ + a − a_w`): for `u ≠ v`,

  `finrank (F.relScrews u v) = F.graph.pairDelta n u v + F.pencilLoss n − F.weldedLoss n u v`.

Pure algebra over the landed welded-rank identity `weldedRank_eq` (Layer B4,
`rank_w = rank + ρ`): unfolding all three carriers, the `screwDim k · (|V(G)|−1)` term cancels
identically between `pencilLoss` and `weldedLoss` (both carry the same `bodyBarDim`-free
coefficient), and `pairDelta`'s `deficiency − deficiencyMerged` cancels the two losses' remaining
deficiency terms, leaving `δ + a − a_w = rank_w − rank`, which `weldedRank_eq` identifies with
`finrank ρ̄_{uv}`. No `hn : bodyBarDim n = screwDim k` hypothesis is needed: this identity never
reads the two losses' sign, only their difference. -/
theorem finrank_relScrews_eq [Finite α] {k : ℕ}
    (F : BodyHingeFramework K k α β) (n : ℕ) {u v : α} (huv : u ≠ v) :
    (Module.finrank K (F.relScrews u v) : ℤ)
      = F.graph.pairDelta n u v + F.pencilLoss n - F.weldedLoss n u v := by
  have hw : (F.weldedRank u v : ℤ)
      = (Module.finrank K (Submodule.span K F.rigidityRows) : ℤ)
        + (Module.finrank K (F.relScrews u v) : ℤ) := by
    exact_mod_cast F.weldedRank_eq huv
  unfold pencilLoss weldedLoss Graph.pairDelta
  linarith


/-- **A partition-respecting motion of a labeling that keeps `u, v` together is a welded
motion**: for `f u = f v`, `partitionMotions f ≤ jointMotions ⊥ u v`.

Read straight off the definition body of `IsPartitionConstant`
(`AlgebraicInduction/PanelLayer.lean`), which *is* `∀ u v, f u = f v → S u = S v` — so a screw
assignment carrying one screw center per part of `f` assigns `u` and `v` the same center as soon
as `f` puts them in the same part, which is exactly membership in `comap (screwDiff v u) ⊥`.  The
motion conjunct transfers unchanged.

This is the one step that connects the combinatorial restriction defining
`Graph.deficiencyMerged` (labelings with `f u = f v`) to the geometric restriction defining
`weldedRank` (rows welding `u` to `v`), and it is what lets the merged hull
`screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` reuse the landed hub's counting
argument verbatim. -/
theorem partitionMotions_le_jointMotions_bot (F : BodyHingeFramework K k α β)
    {f : α → α} {u v : α} (hf : f u = f v) :
    F.partitionMotions f ≤ F.jointMotions (⊥ : Submodule K (ScrewSpace K k)) u v := by
  intro S hS
  rw [mem_partitionMotions] at hS
  refine Submodule.mem_inf.2 ⟨(mem_infinitesimalMotions _ _).2 hS.1, ?_⟩
  simp only [Submodule.mem_comap, Submodule.mem_bot, screwDiff_apply, sub_eq_zero]
  exact (hS.2 v u hf.symm)

open Classical in
/-- **The merged relative hub** (the `deficiencyMerged` counterpart of
`screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`,
`AlgebraicInduction/PanelLayer.lean`): for a framework with genuine hinges and a cut pair *inside*
the vertex set,

  `screwDim k · (|V(G)ᶜ| + 1) + g ≤ finrank (jointMotions ⊥ u v)`,

with `g = Graph.deficiencyMerged n u v`.  The landed hub's argument runs **verbatim** with the
deficiency-attaining labeling drawn from the merged subtype `{f // f u = f v}` instead of from all
of `α → α`: pick the attaining `f₀`, normalize it to `g x = if x ∈ V(G) then ι₀ (f₀ x) else x` so
that labels stay inside `V(G)` (`Set.Finite.exists_injOn_of_encard_le`), and apply the
`|range f|`-form bound `screwDim_mul_range_card_sub_le_finrank_partitionMotions` at `g`.  Only two
steps differ from the landed hub: `g u = g v` still holds (below), and the final monotonicity
lands in `jointMotions ⊥ u v` rather than in `infinitesimalMotions`
(`partitionMotions_le_jointMotions_bot`).

**`hu` and `hv` are load-bearing exactly here.** The normalization's `if x ∈ V(G)` guard must fire
at *both* `u` and `v` for `f₀ u = f₀ v` to survive it; a cut vertex outside `V(G)` would be
renormalized to itself and the merge would be lost.  The necessity of the hypotheses for the
*consumer* is separate and sharper — see `weldedLoss_nonneg`.

The ~85 lines this shares with the landed hub are acknowledged duplication, tracked as a
factoring item (`notes/Phase39.md` *Lemma checklist*, item 6, the shared-normalization entry),
deliberately not resolved in this slice. -/
theorem screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : V(F.graph).Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    {u v : α} (hu : u ∈ V(F.graph)) (hv : v ∈ V(F.graph)) :
    (screwDim k : ℤ) * (V(F.graph).compl.ncard + 1) + F.graph.deficiencyMerged n u v
      ≤ (Module.finrank K (F.jointMotions (⊥ : Submodule K (ScrewSpace K k)) u v) : ℤ) := by
  have : Fintype α := Fintype.ofFinite α
  have : Nonempty α := ⟨hne.some⟩
  set VG := V(F.graph) with hVG
  -- The attaining labeling, drawn from the **merged** subtype.
  have : Nonempty {f : α → α // f u = f v} := ⟨⟨fun _ => u, rfl⟩⟩
  obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f u = f v} => F.graph.partitionDef n f.1)
  rw [Graph.deficiencyMerged, ← hf₀]
  -- Normalize so the labels stay inside `V(G)`.
  have hencard : ((f₀ : α → α) '' VG).encard ≤ VG.encard := Set.encard_image_le _ VG
  obtain ⟨ι₀, hι₀maps, hι₀inj⟩ :=
    (Set.toFinite ((f₀ : α → α) '' VG)).exists_injOn_of_encard_le hencard
  set g : α → α := fun x => if x ∈ VG then ι₀ ((f₀ : α → α) x) else x with hg_def
  -- **First of the two steps that differ from the landed hub**: the normalization keeps the cut
  -- pair together, because the `if` guard fires at both `u` and `v`.
  have hguv : g u = g v := by
    simp only [hg_def, ite_eq_left hu, ite_eq_left hv, f₀.2]
  have hg_img : g '' VG ⊆ VG := by
    rintro y ⟨x, hxV, rfl⟩
    simp only [hg_def, ite_eq_left hxV]
    exact hι₀maps (Set.mem_image_of_mem _ hxV)
  have hnumParts : F.graph.numParts g = F.graph.numParts (f₀ : α → α) := by
    simp only [Graph.numParts, hg_def]
    have himg : (fun x => if x ∈ VG then ι₀ ((f₀ : α → α) x) else x) '' VG
        = ι₀ '' ((f₀ : α → α) '' VG) := by
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, hxV, rfl⟩
        rw [ite_eq_left hxV]
        exact Set.mem_image_of_mem ι₀ (Set.mem_image_of_mem _ hxV)
      · rintro ⟨_, ⟨x, hxV, rfl⟩, rfl⟩
        exact ⟨x, hxV, by rw [ite_eq_left hxV]⟩
    rw [himg]
    exact hι₀inj.ncard_image
  have hcross : F.graph.crossingEdges g = F.graph.crossingEdges (f₀ : α → α) := by
    ext e
    simp only [Graph.crossingEdges, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨heE, a, b, hlink, hne'⟩
      refine ⟨heE, a, b, hlink, ?_⟩
      have ha : g a = ι₀ ((f₀ : α → α) a) := ite_eq_left hlink.left_mem
      have hb : g b = ι₀ ((f₀ : α → α) b) := ite_eq_left hlink.right_mem
      rw [ha, hb] at hne'
      exact fun h => hne' (congrArg ι₀ h)
    · rintro ⟨heE, a, b, hlink, hne'⟩
      refine ⟨heE, a, b, hlink, ?_⟩
      have ha : g a = ι₀ ((f₀ : α → α) a) := ite_eq_left hlink.left_mem
      have hb : g b = ι₀ ((f₀ : α → α) b) := ite_eq_left hlink.right_mem
      rw [ha, hb]
      exact fun h => hne' (hι₀inj (Set.mem_image_of_mem _ hlink.left_mem)
        (Set.mem_image_of_mem _ hlink.right_mem) h)
  have hrange_g : Nat.card (Set.range g) = F.graph.numParts g + VGᶜ.ncard := by
    have hrange_eq : Set.range g = g '' VG ∪ VGᶜ := by
      ext y
      simp only [Set.mem_range, Set.mem_union, Set.mem_image, Set.mem_compl_iff]
      constructor
      · rintro ⟨x, rfl⟩
        by_cases hx : x ∈ VG
        · exact Or.inl ⟨x, hx, rfl⟩
        · right; simp only [hg_def, ite_eq_right hx]; exact hx
      · rintro (⟨x, hxV, rfl⟩ | hx)
        · exact ⟨x, rfl⟩
        · exact ⟨y, by simp [hg_def, hx]⟩
    have hdisj : Disjoint (g '' VG) VGᶜ :=
      Set.disjoint_left.mpr fun y hy hyc => hyc (hg_img hy)
    rw [Nat.card_coe_set_eq, hrange_eq,
        Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
    simp only [Graph.numParts]
    rfl
  have hCg : ∀ e ∈ F.graph.crossingEdges g, F.supportExtensor e ≠ 0 := by
    rw [hcross]
    intro e he
    obtain ⟨_, x, y, hlink, _⟩ := he
    exact hC e x y hlink
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions g hCg
  -- **Second of the two steps that differ**: the motions we keep are the *welded* ones.
  have hmono : Module.finrank K (F.partitionMotions g)
      ≤ Module.finrank K (F.jointMotions (⊥ : Submodule K (ScrewSpace K k)) u v) :=
    Submodule.finrank_mono (F.partitionMotions_le_jointMotions_bot hguv)
  rw [hrange_g, hnumParts] at hlb
  rw [hcross] at hlb
  have hDcast : (Graph.bodyBarDim n : ℤ) = (screwDim k : ℤ) := by exact_mod_cast hn
  have hpdef_eq : F.graph.partitionDef n (f₀ : α → α)
      = (screwDim k : ℤ) * ((F.graph.numParts (f₀ : α → α) : ℤ) - 1)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges (f₀ : α → α)).ncard := by
    simp [Graph.partitionDef, hDcast]
  have hcompl_eq : VGᶜ.ncard = VG.compl.ncard := rfl
  zify [hcompl_eq] at hmono hlb ⊢
  linarith [hpdef_eq]

/-- **C2ℓ: the welded loss is nonnegative** (`notes/pencil/workbook/attack-smark.md` § S14(i)'s
`0 ≤ a_w`, the one general-`U` joint-count instance the consumed path uses): `0 ≤ F.weldedLoss n u
v` at a distinct pair of bodies **both inside** `V(F.graph)`.

Two inputs and one linear step.  The Layer-B codimension
`weldedRank_add_finrank_jointMotions_bot` (`Molecular/RigidityMatrix/Bricks.lean`) turns the
merged relative hub's *lower* bound on `finrank (jointMotions ⊥ u v)` into an *upper* bound
`weldedRank u v ≤ screwDim k · (|V(G)|−1) − g`, which is the statement; the vertex-set/complement
split `Set.ncard_add_ncard_compl` reconciles the hub's `|V(G)ᶜ|` with the loss's `|V(G)|`.

Over C3ℓ (`finrank_relScrews_eq`) this is interchangeable with the transcribed welded bound
`ρ ≤ δ + a`, recorded as `finrank_relScrews_le`.

**The pinned `hne : V(F.graph).Nonempty` is dropped**: it is `⟨u, hu⟩`.  The same
dead-instance pattern as B2/B3/C1ℓ/C3ℓ (`notes/Phase39.md` *Lemma checklist*, item 6).

**`hu` and `hv` are not bookkeeping — the statement is FALSE without them.**  Derivation (not a
compiled witness): take `G` a single vertex with no edges and `u, v ∉ V(G)` distinct.  Then
`partitionDef` depends only on the labeling's restriction to `V(G)`, so the merge constraint
`f u = f v` costs nothing and `g = def(G̃) = 0`; the framework has no rows, so
`span F.rigidityRows = ⊥`, while the weld still contributes a full `screwDim k` rows
(`finrank_span_jointRows` at `U = ⊥`), giving `weldedRank u v = screwDim k`.  Hence
`weldedLoss = screwDim k · (1−1) − 0 − screwDim k = −screwDim k < 0`.  A later slice tempted to
drop `hu`/`hv` as "probably dead" should start here. -/
theorem weldedLoss_nonneg [Finite α] [Finite β] {k n : ℕ}
    (F : BodyHingeFramework K k α β) (hn : Graph.bodyBarDim n = screwDim k)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) {u v : α} (huv : u ≠ v)
    (hu : u ∈ V(F.graph)) (hv : v ∈ V(F.graph)) :
    0 ≤ F.weldedLoss n u v := by
  have : Fintype α := Fintype.ofFinite α
  have hcod := F.weldedRank_add_finrank_jointMotions_bot huv
  have hhub := F.screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions hn ⟨u, hu⟩ hC hu hv
  have hsplit : V(F.graph).ncard + V(F.graph).compl.ncard = Nat.card α := by
    have h : V(F.graph).ncard + V(F.graph)ᶜ.ncard = Nat.card α :=
      Set.ncard_add_ncard_compl V(F.graph) (Set.toFinite _) (Set.toFinite _)
    have heq : V(F.graph)ᶜ.ncard = V(F.graph).compl.ncard := rfl
    rw [← heq]; exact h
  have h1 : 1 ≤ V(F.graph).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨u, hu⟩
  unfold weldedLoss
  zify [h1] at hcod hsplit ⊢
  -- `linarith` will NOT close this without `hdist`: `hcod` carries `screwDim k * |α|` and the
  -- goal carries `screwDim k * |V(G)|`, and substituting `hsplit` between them is a nonlinear
  -- step. Do not "simplify" this `have` away.
  have hdist : (screwDim k : ℤ) * (Nat.card α : ℤ)
      = (screwDim k : ℤ) * (V(F.graph).ncard : ℤ)
        + (screwDim k : ℤ) * (V(F.graph).compl.ncard : ℤ) := by
    rw [← hsplit]; ring
  linarith

/-- **The transcribed welded bound `ρ ≤ δ + a`** (`notes/pencil/workbook/attack-smark.md`
§ S10(ii), the inequality form of C2): for a distinct cut pair inside the vertex set,

  `finrank (F.relScrews u v) ≤ F.graph.pairDelta n u v + F.pencilLoss n`.

The workbook's own phrasing of the welded bound, and one `linarith` over C3ℓ
(`finrank_relScrews_eq`, the identity `ρ = δ + a − a_w`) plus C2ℓ (`weldedLoss_nonneg`,
`0 ≤ a_w`) — so over C3ℓ the bound and `0 ≤ a_w` are interchangeable, and this is the face a
consumer reading S14(i)'s `ρ ≤ δ + a` step will look for. -/
theorem finrank_relScrews_le [Finite α] [Finite β] {k n : ℕ}
    (F : BodyHingeFramework K k α β) (hn : Graph.bodyBarDim n = screwDim k)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0) {u v : α} (huv : u ≠ v)
    (hu : u ∈ V(F.graph)) (hv : v ∈ V(F.graph)) :
    (Module.finrank K (F.relScrews u v) : ℤ)
      ≤ F.graph.pairDelta n u v + F.pencilLoss n := by
  have h1 := F.finrank_relScrews_eq n huv (β := β)
  have h2 := F.weldedLoss_nonneg hn hC huv hu hv
  linarith

end BodyHingeFramework

end CombinatorialRigidity.Molecular
