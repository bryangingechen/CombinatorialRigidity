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

**C4ℓ** `pencilLoss_vertexTwoCut` — S10(ii)'s attainment criterion in one statement,
`a = a₁ + a₂ + min (δ₁+δ₂) D − dim (ρ̄₁ ⊔ ρ̄₂)` — closes item 6's headline target by unfolding
`pencilLoss` on both sides and substituting exactly **A5**
`Graph.deficiency_eq_of_vertexTwoCut'` and **B6** `finrank_span_rigidityRows_vertexTwoCut_eq`;
see its own docstring for why C1ℓ/C3ℓ, though listed as dependencies in the checklist, turn out
not to be consumed. The deferred general-`U` profile laws are not in this slice; see
`notes/Phase39.md` *Lemma checklist*, item 6.

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
`weldedRank` (rows welding `u` to `v`), and it is what lets the merged hub
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

/-- **The merged relative hub** (the `deficiencyMerged` counterpart of
`screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`,
`AlgebraicInduction/PanelLayer.lean`): for a framework with genuine hinges and a cut pair *inside*
the vertex set,

  `screwDim k · (|V(G)ᶜ| + 1) + g ≤ finrank (jointMotions ⊥ u v)`,

with `g = Graph.deficiencyMerged n u v`.  The landed hub's argument runs **verbatim** with the
deficiency-attaining labeling drawn from the merged subtype `{f // f u = f v}` instead of from all
of `α → α`: pick the attaining `f₀`, normalize it to `g` by `Graph.exists_normalized_labeling`
(`Molecular/Deficiency.lean`; same parts and crossing edges, and
`|range g| = numParts f₀ + |V(G)ᶜ|`), and apply the `|range f|`-form bound
`screwDim_mul_range_card_sub_le_finrank_partitionMotions` at `g`.  Only two steps differ from the
landed hub: `g u = g v` still holds (below), and the final monotonicity lands in
`jointMotions ⊥ u v` rather than in `infinitesimalMotions` (`partitionMotions_le_jointMotions_bot`).

**`hu` and `hv` are load-bearing exactly here.** The normalization's last conjunct,
`g x = g y ↔ f₀ x = f₀ y`, holds only for `x` and `y` in `V(G)`, so `f₀ u = f₀ v` survives it
only because both cut vertices are inside `V(G)`. Off `V(G)` the normalization promises nothing
(its construction fixes every such vertex), so at a cut vertex outside `V(G)` the merge would be
lost.  The necessity of the hypotheses for the *consumer* is separate and sharper — see
`weldedLoss_nonneg`. -/
theorem screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions
    [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K k α β)
    (hn : Graph.bodyBarDim n = screwDim k)
    (hne : V(F.graph).Nonempty)
    (hC : ∀ e u v, F.graph.IsLink e u v → F.supportExtensor e ≠ 0)
    {u v : α} (hu : u ∈ V(F.graph)) (hv : v ∈ V(F.graph)) :
    (screwDim k : ℤ) * (V(F.graph).compl.ncard + 1) + F.graph.deficiencyMerged n u v
      ≤ (Module.finrank K (F.jointMotions (⊥ : Submodule K (ScrewSpace K k)) u v) : ℤ) := by
  have : Nonempty α := ⟨hne.some⟩
  -- The attaining labeling, drawn from the **merged** subtype, normalized into `V(G)`.
  have : Nonempty {f : α → α // f u = f v} := ⟨⟨fun _ => u, rfl⟩⟩
  obtain ⟨f₀, hf₀⟩ := exists_eq_ciSup_of_finite
    (f := fun f : {f : α → α // f u = f v} => F.graph.partitionDef n f.1)
  rw [Graph.deficiencyMerged, ← hf₀]
  obtain ⟨g, -, -, hcross, hrange_g, hgf⟩ := F.graph.exists_normalized_labeling f₀.1
  -- **First of the two steps that differ from the landed hub**: the normalization keeps the cut
  -- pair together, because `u` and `v` are both inside `V(G)`.
  have hguv : g u = g v := (hgf hu hv).2 f₀.2
  have hCg : ∀ e ∈ F.graph.crossingEdges g, F.supportExtensor e ≠ 0 := fun e he => by
    obtain ⟨_, x, y, hlink, _⟩ := he
    exact hC e x y hlink
  have hlb := F.screwDim_mul_range_card_sub_le_finrank_partitionMotions g hCg
  -- **Second of the two steps that differ**: the motions we keep are the *welded* ones.
  have hmono : Module.finrank K (F.partitionMotions g)
      ≤ Module.finrank K (F.jointMotions (⊥ : Submodule K (ScrewSpace K k)) u v) :=
    Submodule.finrank_mono (F.partitionMotions_le_jointMotions_bot hguv)
  rw [hrange_g, hcross] at hlb
  have hDcast : (Graph.bodyBarDim n : ℤ) = (screwDim k : ℤ) := by exact_mod_cast hn
  have hpdef_eq : F.graph.partitionDef n f₀.1
      = (screwDim k : ℤ) * ((F.graph.numParts f₀.1 : ℤ) - 1)
        - (screwDim k - 1 : ℤ) * (F.graph.crossingEdges f₀.1).ncard := by
    simp [Graph.partitionDef, hDcast]
  have hcompl_eq : V(F.graph)ᶜ.ncard = V(F.graph).compl.ncard := rfl
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

/-- **C4ℓ — item 6's headline target**: `pencilLoss` splits exactly across a vertex 2-cut, which
*is* `notes/pencil/workbook/attack-smark.md` § S10(ii)'s attainment criterion in one statement —

  `a(G) = a₁ + a₂ + min (δ₁+δ₂, D) − dim (ρ̄₁ ⊔ ρ̄₂)`,

with `D = screwDim 2` and `a_i = side_i.pencilLoss n`. The checklist's "Depends on A4/A5, B6,
C1ℓ/C3ℓ" framing overstates it: this proof needs only **two** landed laws, found by unfolding
`pencilLoss` on both sides — **A5** `Graph.deficiency_eq_of_vertexTwoCut'`
(`f = f₁ + f₂ − min (δ₁+δ₂) D`) and **B6** `finrank_span_rigidityRows_vertexTwoCut_eq`
(`rank = rank₁ + rank₂ + dim (ρ̄₁ ⊔ ρ̄₂) − D`). C1ℓ (`pencilLoss_nonneg`) and C3ℓ
(`finrank_relScrews_eq`) are **not** consumed — this route goes through `pencilLoss`'s own
definition directly rather than through the `relScrews` identity, a shorter path than the
checklist's dependency line suggested (dispatch-log F41's "floor, not ceiling").

Both unfolded sides carry the same `D · (|V| − 1)`-shaped term, differing only in `|V|` vs.
`|V₁| + |V₂| − 2`; the **one step that is not substitution** is the vertex count
`|V₁| + |V₂| = |V(G)| + 2`, by inclusion–exclusion (`Set.ncard_union_add_ncard_inter` on
`hcover : V₁ ∪ V₂ = V(G)`, `Set.ncard_pair huv` on `hoverlap : V₁ ∩ V₂ = {u, v}`) — the same
lemma `Graph.partitionDef_split_of_vertexTwoCut` uses. `linarith` needs the `D`-multiple
distributed across that vertex-count sum handed to it explicitly (`hDdist`); this is the same
nonlinear-substitution trap `weldedLoss_nonneg` hit with its own `hdist`.

**`hnonadj` binds only through A5, and that asymmetry is by design, not an oversight.** It is
`Graph.deficiency_eq_of_vertexTwoCut'`'s own hypothesis: the combinatorial deficiency law is
*false* at an adjacent cut pair without it (D1, the 346/2104-instance counterexample family,
`notes/Phase39.md` *Lemma checklist*). B6 needs no such hypothesis — a cut edge is charged to
both sides' rows identically regardless of which side "owns" it, so it cannot disturb a rank
identity the way it disturbs a combinatorial count. This is the one place item 6's combinatorial
and geometric halves' hypothesis sets genuinely differ; see the B5–B6 checklist entry. -/
theorem pencilLoss_vertexTwoCut [Finite α] [Finite β] {n : ℕ}
    (F : BodyHingeFramework K 2 α β) {V₁ V₂ : Set α} {u v : α} (huv : u ≠ v)
    (hnonadj : ¬ F.graph.Adj u v) (hn : Graph.bodyBarDim n = screwDim 2)
    (hcover : V₁ ∪ V₂ = V(F.graph)) (hoverlap : V₁ ∩ V₂ = {u, v})
    (hsep : ∀ e x y, F.graph.IsLink e x y → (x ∈ V₁ ∧ y ∈ V₁) ∨ (x ∈ V₂ ∧ y ∈ V₂)) :
    F.pencilLoss n
      = (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).pencilLoss n
        + (⟨F.graph.induce V₂, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).pencilLoss n
        + min ((F.graph.induce V₁).pairDelta n u v + (F.graph.induce V₂).pairDelta n u v)
              (screwDim 2 : ℤ)
        - (Module.finrank K
            ↥((⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).relScrews u v
              ⊔ (⟨F.graph.induce V₂, F.supportExtensor⟩ :
                  BodyHingeFramework K 2 α β).relScrews u v) : ℤ) := by
  have hD : 1 ≤ Graph.bodyBarDim n := by rw [hn]; decide
  have hdef := Graph.deficiency_eq_of_vertexTwoCut' hD huv hnonadj hcover hoverlap hsep
    (G := F.graph)
  have hrank := F.finrank_span_rigidityRows_vertexTwoCut_eq huv hoverlap hsep
  have hcardsplit : V₁.ncard + V₂.ncard = V(F.graph).ncard + 2 := by
    have hkey := Set.ncard_union_add_ncard_inter V₁ V₂
    rw [hcover, hoverlap, Set.ncard_pair huv] at hkey
    omega
  rw [hn] at hdef
  have hgraph1 : (⟨F.graph.induce V₁, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).graph
      = F.graph.induce V₁ := rfl
  have hgraph2 : (⟨F.graph.induce V₂, F.supportExtensor⟩ : BodyHingeFramework K 2 α β).graph
      = F.graph.induce V₂ := rfl
  have hV₁ : V(F.graph.induce V₁).ncard = V₁.ncard := rfl
  have hV₂ : V(F.graph.induce V₂).ncard = V₂.ncard := rfl
  unfold BodyHingeFramework.pencilLoss
  rw [hgraph1, hgraph2, hV₁, hV₂]
  have hDdist : (screwDim 2 : ℤ) * ((V₁.ncard : ℤ) + (V₂.ncard : ℤ))
      = (screwDim 2 : ℤ) * (V(F.graph).ncard : ℤ) + (screwDim 2 : ℤ) * 2 := by
    have hcast : (V₁.ncard : ℤ) + (V₂.ncard : ℤ) = (V(F.graph).ncard : ℤ) + 2 := by omega
    rw [hcast]; ring
  linarith

end BodyHingeFramework

end CombinatorialRigidity.Molecular
