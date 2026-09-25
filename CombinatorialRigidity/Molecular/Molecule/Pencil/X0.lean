/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.Molecular.Molecule.Pencil.Pair2

/-!
# The `X₀` main-component statements and their conditioned-pair headline (Phase 39/40 PENCIL, L0a)

`X0Dist`/`X0Gen` are the two hypotheses the adopted `X₀` route replaces `hK`/`hbareSplit` with
(`notes/pencil/adjudications.md`, 2026-09-25): a separate strong induction on the pencil-realization
configuration space's main component, bypassing both open kernels of
`thm:pencil-conditional-realization-pair`. Phase 40 discharges them
(`notes/Phase40-design.md` §1). `pencilPair_of_X0` and `pencil_conjecture_of_X0` are the carried
headline built on top, spike-compiled against `22d0f8f8`
(`notes/Phase39-design.md` § "X₀ architecture recon") and transcribed here verbatim. Both still
carry `hW4A`, the non-simple bare case (Phase 39 L0b); Phase 39 closes once L0b lands and drops it
from both.

See `notes/Phase39.md`, `notes/Phase39-design.md` (§ "X₀ architecture recon"), and
`blueprint/src/chapter/pencil.tex` (`def:pencil-main-component-statements`,
`thm:pencil-conditional-realization-main-component`).
-/

open scoped Graph

namespace CombinatorialRigidity.Molecular

variable {K : Type*} [Field K] {α β : Type*}

/-- **The distinct main-component statement** (`def:pencil-main-component-statements`; Phase
39/40 PENCIL, L0a). Every simple two-edge-connected multigraph on at least three bodies has an
adjacent-distinct pencil realization at the deficiency rank at `n = 3`
(`HasDistinctPencilRealization`). Phase 40 discharges this by the main-component induction
(`notes/Phase40-design.md`). -/
def X0Dist (K : Type*) [Field K] (α β : Type*) : Prop :=
  ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
    HasDistinctPencilRealization K 3 G

/-- **The generic main-component statement** (`def:pencil-main-component-statements`; Phase
39/40 PENCIL, L0a). Every simple two-edge-connected multigraph on at least three bodies that is
nondegeneracy-feasible (`PencilNondegFeasible`) has a generic pencil realization at `n = 3`
(`HasGenericPencilRealization`). Phase 40 discharges this alongside `X0Dist`. -/
def X0Gen (K : Type*) [Field K] (α β : Type*) : Prop :=
  ∀ G : Graph α β, G.Simple → 3 ≤ V(G).ncard → G.TwoEdgeConnected →
    PencilNondegFeasible K G → HasGenericPencilRealization K 3 G

/-- **The conditioned pair from the `X₀` statements, one loopless step** (Phase 39 PENCIL, L0a;
the per-graph step `pencil_conjecture_of_X0` reuses at both of `pencil_conjecture_of_arms_pair`'s
arms). Given `X0Dist`, `X0Gen` and the non-simple bare case `hW4A` (Phase 39 L0b), a loopless `G`
on at least three bodies satisfies `PencilPair K 3 G`, given the conditioned pair on every strictly
smaller graph (`hIH`): if `G` is not two-edge-connected, `pencilPair_of_not_twoEdgeConnected`
applies; if `G` is two-edge-connected and simple, `X0Dist`/`X0Gen` give the generic and
adjacent-distinct conjuncts directly and the bare conjunct follows forgetfully
(`hasPencilRealization_of_distinct`); if `G` is two-edge-connected and not simple, the generic and
adjacent-distinct conjuncts are vacuous and `hW4A` gives the bare one. -/
theorem pencilPair_of_X0 [Finite α] [Finite β] [Infinite K]
    (hdist : X0Dist K α β) (hgen : X0Gen K α β)
    (hW4A : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected → ¬ G.Simple →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
      HasPencilRealization K 3 G)
    (G : Graph α β) (hloop : G.Loopless) (hV : 3 ≤ V(G).ncard)
    (hIH : ∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') :
    PencilPair K 3 G := by
  have hD2 : (2 : ℕ) ≤ Graph.bodyBarDim 3 := by
    have := Graph.six_le_bodyBarDim (n := 3) (by norm_num); omega
  have hn : Graph.bodyBarDim 3 = screwDim 2 := Graph.bodyBarDim_eq_screwDim_sub_one (by norm_num)
  by_cases h2ec : G.TwoEdgeConnected
  · by_cases hs : G.Simple
    · have hd := hdist G hs hV h2ec
      exact ⟨fun _ hf => hgen G hs hV h2ec hf, fun _ => hd, hasPencilRealization_of_distinct hd⟩
    · exact ⟨fun h => absurd h hs, fun h => absurd h hs, hW4A G hloop hV h2ec hs hIH⟩
  · exact pencilPair_of_not_twoEdgeConnected hD2 hn h2ec hIH

-- `[DecidableEq β]` is genuinely load-bearing (empirical check per FRICTION.md: removing it
-- makes the `pencil_conjecture_of_arms_pair` call below fail to synthesize the instance it
-- requires) though it's never named in the body; `unusedDecidableInType` false-positives here.
set_option linter.unusedDecidableInType false in
/-- **The pencil conjecture from the two main-component statements**
(`thm:pencil-conditional-realization-main-component`; Phase 39 PENCIL, L0a). Over an infinite
field, given `X0Dist`, `X0Gen` and the non-simple bare case `hW4A`, every multigraph on the whole
ambient body set satisfies the conditioned pair at `n = 3`. Assembles `pencilPair_of_X0` at both
arms of `pencil_conjecture_of_arms_pair`'s reduction — the contraction and split arms feed it the
same per-graph argument, since neither the two-edge-connectivity split nor `X0Dist`/`X0Gen` cares
which arm supplied the induction hypothesis. Still carries `hW4A`; Phase 39 L0b discharges it and
drops it from both this theorem and `pencilPair_of_X0`. -/
theorem pencil_conjecture_of_X0 [Nonempty α] [Finite α] [Finite β] [DecidableEq β] [Infinite K]
    (hdist : X0Dist K α β) (hgen : X0Gen K α β)
    (hW4A : ∀ G : Graph α β, G.Loopless → 3 ≤ V(G).ncard → G.TwoEdgeConnected → ¬ G.Simple →
      (∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard → PencilPair K 3 G') →
      HasPencilRealization K 3 G)
    (G : Graph α β) (hspan : V(G) = Set.univ) :
    PencilPair K 3 G :=
  pencil_conjecture_of_arms_pair
    (fun G hloop hV _ hIH => pencilPair_of_X0 hdist hgen hW4A G hloop hV hIH)
    (fun G hloop hV _ _ _ hIH => pencilPair_of_X0 hdist hgen hW4A G hloop hV hIH) G hspan

end CombinatorialRigidity.Molecular
