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

The headline target `pencilLoss_vertexTwoCut` (**C4ℓ**), `weldedLoss_nonneg` (**C2ℓ**, the
substantive inequality `ρ ≤ δ + a` in disguise) and the deferred general-`U` profile laws are not
in this slice; see `notes/Phase39.md` *Lemma checklist*, item 6.

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

end BodyHingeFramework

end CombinatorialRigidity.Molecular
