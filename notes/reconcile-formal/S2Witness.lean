import CombinatorialRigidity.Molecular.AlgebraicInduction.Theorem55

/-! The Phase 41 design recon's witness (2026-10-24, at commit `95e2f418`; not part of the
library). The proposed link field alone does not exclude S2's zero-normal framework;
nondegenerate hinges on `E(G)` do. The probes below test the field's friction: rewriting the
graph argument, and filling in the link proof at the common construction sites.
`notes/Phase41-design.md` §2 records the verdict. Check it from the repository root with
`lake env lean notes/reconcile-formal/S2Witness.lean`: no errors, and the two `#print axioms`
give `[propext, Classical.choice, Quot.sound]`. -/

open CombinatorialRigidity.Molecular
open scoped Graph

namespace ReconS2

variable {K : Type*} [Field K] {k : ℕ} {α β : Type*}

/-- The proposed carrier: today's structure plus the link field on `E(graph)`. -/
structure LinkedPHF (K : Type*) [Field K] (k : ℕ) (α β : Type*)
    extends PanelHingeFramework K k α β where
  isLink_ends : ∀ e ∈ E(graph), graph.IsLink e (ends e).1 (ends e).2

/-- The zero-normal framework on any graph meets the field, with the canonical selector. -/
noncomputable def zeroPHF [Inhabited α] (G : Graph α β) : LinkedPHF K k α β where
  graph := G
  normal := fun _ => 0
  ends := G.endsOf
  isLink_ends := fun _ he => G.isLink_endsOf he

theorem zeroPHF_hinge [Inhabited α] (G : Graph α β) (e : β) :
    (zeroPHF (K := K) (k := k) G).toBodyHinge.supportExtensor e = 0 := by
  by_contra h
  have hli := (PanelHingeFramework.toBodyHinge_supportExtensor_ne_zero_iff _ e).mp h
  exact hli.ne_zero 0 rfl

/-- S2's counterexample survives the field: at a preconnected spanning graph (every spanning
`0`-dof-graph is one, `Graph.preconnected_of_isKDof_zero`), the zero framework is rigid, so it
meets `RankHypothesis 0`, the conclusion of KT Theorem 5.6 at deficiency zero. -/
theorem zeroPHF_rankHypothesis_zero [Inhabited α] [Finite α] (G : Graph α β)
    (hG : G.Preconnected) (hspan : V(G) = Set.univ) :
    (zeroPHF (K := K) (k := k) G).toBodyHinge.RankHypothesis 0 := by
  rw [BodyHingeFramework.rankHypothesis_zero_iff, ← BodyHingeFramework.isInfinitesimallyRigidOn_univ_iff]
  intro S hS u _ v _
  have hlink : ∀ e x y, G.IsLink e x y → S x = S y := by
    intro e x y he
    have h := hS e x y he
    rw [BodyHingeFramework.hingeConstraint, zeroPHF_hinge] at h
    simpa [sub_eq_zero] using h
  exact hG.eq_of_forall_isLink hlink (by rw [hspan]; trivial) (by rw [hspan]; trivial)

/-- The restated conclusion's extra conjunct excludes it at any graph with an edge. -/
theorem zeroPHF_not_nondegenerate [Inhabited α] (G : Graph α β) {e : β} (he : e ∈ E(G)) :
    ¬ ∀ e ∈ E(G), (zeroPHF (K := K) (k := k) G).toBodyHinge.supportExtensor e ≠ 0 :=
  fun h => h e he (zeroPHF_hinge G e)

/-- `withGraph` to a subgraph keeps the field (the proposed restriction of `withGraph`). -/
theorem isLink_ends_of_le (P : LinkedPHF K k α β) {G' : Graph α β} (hle : G' ≤ P.graph) :
    ∀ e ∈ E(G'), G'.IsLink e (P.ends e).1 (P.ends e).2 := by
  intro e he
  obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have h1 := hxy.mono hle
  have h2 := P.isLink_ends e h1.edge_mem
  rcases h1.eq_and_eq_or_eq_and_eq h2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hxy
  · rw [← hx, ← hy]; exact hxy.symm

end ReconS2

#print axioms ReconS2.zeroPHF_rankHypothesis_zero
#print axioms ReconS2.isLink_ends_of_le

namespace ReconS2
variable {K : Type*} [Field K] {k : ℕ} {α β : Type*}

/-- A proof-carrying `ofNormals`. -/
def ofNormalsL (G : Graph α β) (ends : β → α × α)
    (hends : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2) (q : α × Fin (k + 2) → K) :
    LinkedPHF K k α β where
  graph := G
  normal := fun a i => q (a, i)
  ends := ends
  isLink_ends := hends

-- Friction probe 1: `rw` of the graph argument under a dependent proof fails ("motive is not
-- type correct").
example (G G' : Graph α β) (ends : β → α × α) (h : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin (k + 2) → K) (hG : G = G') (P : Set (Module.Dual K (α → ScrewSpace K k)) → Prop)
    (hP : ∀ (h' : ∀ e ∈ E(G'), G'.IsLink e (ends e).1 (ends e).2),
      P (ofNormalsL G' ends h' q).toBodyHinge.rigidityRows) :
    P (ofNormalsL G ends h q).toBodyHinge.rigidityRows := by
  fail_if_success rw [hG]
  subst hG
  exact hP _

-- Friction probe 2: the same with `subst`.
example (G G' : Graph α β) (ends : β → α × α) (h : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin (k + 2) → K) (hG : G = G') (P : Set (Module.Dual K (α → ScrewSpace K k)) → Prop)
    (hP : ∀ (h' : ∀ e ∈ E(G'), G'.IsLink e (ends e).1 (ends e).2),
      P (ofNormalsL G' ends h' q).toBodyHinge.rigidityRows) :
    P (ofNormalsL G ends h q).toBodyHinge.rigidityRows := by
  subst hG
  exact hP _

-- Friction probe 3: `simp only`.
example (G G' : Graph α β) (ends : β → α × α) (h : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2)
    (q : α × Fin (k + 2) → K) (hG : G = G') (P : Set (Module.Dual K (α → ScrewSpace K k)) → Prop)
    (hP : ∀ (h' : ∀ e ∈ E(G'), G'.IsLink e (ends e).1 (ends e).2),
      P (ofNormalsL G' ends h' q).toBodyHinge.rigidityRows) :
    P (ofNormalsL G ends h q).toBodyHinge.rigidityRows := by
  simp only [hG]
  exact hP _

-- Probe 4: the rows do not see the proof (proof irrelevance), so a rewrite lemma closes it.
theorem ofNormalsL_congr_graph {G G' : Graph α β} (hG : G = G') {ends : β → α × α}
    (h : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2) (q : α × Fin (k + 2) → K) :
    ofNormalsL G ends h q = ofNormalsL G' ends (hG ▸ h) q := by
  subst hG; rfl

end ReconS2

namespace ReconS2
variable {K : Type*} [Field K] {k : ℕ} {α β : Type*}

/-- Discharges a link obligation from a hypothesis in scope or the canonical selector. -/
theorem recordsLinks_mono {G G' : Graph α β} {ends : β → α × α}
    (h : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2) (hle : G' ≤ G) :
    ∀ e ∈ E(G'), G'.IsLink e (ends e).1 (ends e).2 := by
  intro e he
  obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
  have h1 := hxy.mono hle
  rcases h1.eq_and_eq_or_eq_and_eq (h e h1.edge_mem) with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hxy
  · rw [← hx, ← hy]; exact hxy.symm

macro "link_tac" : tactic => `(tactic| first
  | assumption
  | exact LinkedPHF.isLink_ends _
  | exact recordsLinks_mono (by assumption) (by assumption)
  | exact fun _ he => Graph.isLink_endsOf _ he
  | (intro e he
     obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
     solve_by_elim (maxDepth := 4)))

/-- The proof-carrying constructor with the obligation as an `autoParam`, last. -/
def ofNormalsA (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (hends : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2 := by link_tac) :
    LinkedPHF K k α β where
  graph := G
  normal := fun a i => q (a, i)
  ends := ends
  isLink_ends := hends

-- (a) the canonical selector, in a statement: no proof written.
example [Inhabited α] (G : Graph α β) (q : α × Fin (k + 2) → K) :
    (ofNormalsA G G.endsOf q).graph = G := rfl

-- (b) the edge-restricted hypothesis shape the tree uses (38 lines), in a statement.
example (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K)
    (hends : ∀ e u v, G.IsLink e u v → G.IsLink e (ends e).1 (ends e).2) :
    (ofNormalsA G ends q).toBodyHinge.graph = G := rfl

-- (c) a framework's own selector.
example (Q : LinkedPHF K k α β) (q : α × Fin (k + 2) → K) :
    (ofNormalsA Q.graph Q.ends q).graph = Q.graph := rfl

-- (d) structure eta: the framework rebuilt from its own data is itself, by `rfl`.
example (Q : LinkedPHF K k α β) :
    ofNormalsA Q.graph Q.ends (fun p => Q.normal p.1 p.2) Q.isLink_ends = Q := rfl

-- (e) a subgraph with the parent's hypothesis: the macro reaches it through `recordsLinks_mono`.
example (G : Graph α β) (ends : β → α × α) (q : α × Fin (k + 2) → K) (G' : Graph α β)
    (hle : G' ≤ G) (hends : ∀ e ∈ E(G), G.IsLink e (ends e).1 (ends e).2) :
    (ofNormalsA G' ends q).graph = G' := rfl

end ReconS2
