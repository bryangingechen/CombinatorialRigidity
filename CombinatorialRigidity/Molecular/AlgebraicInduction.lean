/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
module

public import CombinatorialRigidity.Molecular.RigidityMatrix

/-!
# The algebraic induction: Theorem 5.5 base, Cases I & II (`sec:molecular-algebraic-induction`)

Phase 21, the fifth proof stratum of the molecular-conjecture program (Phases 17–26; see
`notes/MolecularConjecture.md`). Where the combinatorial induction (Phase 20,
`Molecular/Induction.lean`) reduced every minimal `0`-dof-graph to the two-vertex double
edge (Theorem 4.9, `Graph.minimal_kdof_reduction`), this file *realizes* that reduction at
the rigidity-matrix rank: Katoh–Tanigawa 2011 (*A proof of the molecular conjecture*,
Discrete Comput. Geom. **45**, §5, §6.1–6.3) **Theorem 5.5** — every minimal `k`-dof-graph
`G` with `|V| ≥ 2` has a panel-hinge realization `(G,p)` with `rank R(G,p) = D(|V|−1) − k` —
its base case, Case I (proper rigid subgraph), and Case II (`k > 0` splitting). The crux
Case III (`k = 0`, no proper rigid subgraph) is deferred to Phases 22–23.

This file lands the `sec:molecular-algebraic-induction` dep-graph in dependency order. The
leaf nodes landing here:

* `RankHypothesis` (`def:rank-hypothesis`) — the realization hypothesis (6.1). Carried in
  the basis-free form of Phase 18 (`Molecular/RigidityMatrix.lean`): the panel-hinge rigidity
  matrix `R(G,p)` is the constraint family cutting out the null space
  `Z(G,p) = F.infinitesimalMotions`, and `rank R(G,p) = D|V| − dim Z(G,p)`
  (`def:rigidity-matrix`'s codimension form, `finrank_screwAssignment`). The target rank
  `rank R(G,p) = D(|V|−1) − k = D|V| − (D + k)` is therefore the null-space dimension
  `dim Z(G,p) = D + k`, the form carried here. (`D = screwDim k`.)
* `theorem_55_base` (`lem:theorem-55-base`) — the `|V| = 2`, `k = 0` base case: the
  two-vertex double edge with two non-parallel hinges (independent supporting extensors)
  realizes the full rank `D = D(2−1) − 0`, i.e. `dim Z(G,p) = D`. The framework is
  infinitesimally rigid (`Z(G,p) = trivialMotions`), so its null space is the `D`-dimensional
  trivial-motion space — exactly the parallel-hinges-full Lemma 5.3
  (`eq_of_hingeConstraint_two_parallel`, Phase 18 green) specialized to the two bodies.

## The rank in basis-free form

Phase 18 carries `rank R(G,p)` as a codimension: the column space is the screw-assignment
space `α → ScrewSpace k` of dimension `D|V|` (`finrank_screwAssignment`), and the null space
is `Z(G,p) = F.infinitesimalMotions`, so `rank R(G,p) = D|V| − dim Z(G,p)`. Rather than carry
the `ℤ`-valued rank and re-derive the column count at each node, the realization hypothesis is
stated directly on the null-space dimension: `RankHypothesis F k` asserts
`dim Z(G,p) = D + k`, the rearrangement of `rank R(G,p) = D(|V|−1) − k`. The two forms are
interchanged by `finrank_screwAssignment`; the null-space form is the one the rank lemmas of
Phase 18 (`finrank_pinnedMotions_add_screwDim`, `finrank_trivialMotions`) already speak.
-/

@[expose] public section

namespace CombinatorialRigidity.Molecular

namespace BodyHingeFramework

variable {k : ℕ} {α β : Type*}

/-- **The realization (generic-rank) hypothesis (6.1)** (`def:rank-hypothesis`): a panel-hinge
framework `(G,p)` realizes the target rank of a `k`-dof-graph when its null space has dimension
`dim Z(G,p) = D + k`, i.e. `rank R(G,p) = D|V| − dim Z(G,p) = D(|V|−1) − k`
(`finrank_screwAssignment`; `D = screwDim k`). This is the predicate Katoh–Tanigawa's
Theorem 5.5 establishes by induction on `|V|`; the base case (`theorem_55_base`) and Cases I/II
exhibit such a realization, and the nonparallel-when-simple refinement is supplied alongside by
the linear independence of the supporting extensors used in each construction. -/
def RankHypothesis (F : BodyHingeFramework k α β) (k' : ℤ) : Prop :=
  (Module.finrank ℝ F.infinitesimalMotions : ℤ) = screwDim k + k'

/-- A framework realizes the rank hypothesis at `k' = 0` exactly when it is infinitesimally
rigid (`def:rank-hypothesis`): the rigid case `rank R(G,p) = D(|V|−1)` is `dim Z(G,p) = D`, the
dimension of the trivial-motion space (`finrank_trivialMotions`), attained exactly when
`Z(G,p) = trivialMotions` (`infinitesimalMotions_eq_trivialMotions_iff`). The forward direction
uses that the trivial motions are a `D`-dimensional subspace of the null space
(`trivialMotions_le_infinitesimalMotions`) whose codimension-zero containment forces equality. -/
theorem rankHypothesis_zero_iff [Nonempty α] [Finite α] (F : BodyHingeFramework k α β) :
    F.RankHypothesis 0 ↔ F.IsInfinitesimallyRigid := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [RankHypothesis, ← F.infinitesimalMotions_eq_trivialMotions_iff]
  constructor
  · intro h
    refine (Submodule.eq_of_le_of_finrank_le F.trivialMotions_le_infinitesimalMotions ?_).symm
    rw [F.finrank_trivialMotions]
    rw [add_zero] at h
    exact_mod_cast h.le
  · intro h
    rw [h, F.finrank_trivialMotions, add_zero]

/-- **Theorem 5.5, base case (`|V| = 2`)** (`lem:theorem-55-base`; Katoh–Tanigawa 2011 §5):
the two-vertex double edge realizes the target rank `D(|V|−1) − k = D − 0 = D` of the minimal
`0`-dof case. Concretely, if a body-hinge framework `F` on a two-body set `α` has two edges
`e₁, e₂` whose supporting extensors `C(p(e₁)), C(p(e₂))` are linearly independent (the
non-parallel-hinges, *general-position* hypothesis), and every link of `G` joins the two
distinct bodies `u v` carried by `e₁` and `e₂`, then `F` realizes the rank hypothesis at
`k' = 0` — equivalently `F.IsInfinitesimallyRigid` (`rankHypothesis_zero_iff`).

This is the parallel-hinges-full Lemma 5.3 (`eq_of_hingeConstraint_two_parallel`, Phase 18
green) specialized to the two bodies: the two `(D−1) × D` hinge-row blocks together have full
rank `D`, so the combined kernel on the relative screw is `{0}` and every infinitesimal motion
is trivial. -/
theorem theorem_55_base [Nonempty α] [Finite α] (F : BodyHingeFramework k α β)
    {e₁ e₂ : β} {u v : α} (huv : u ≠ v)
    (hgen : LinearIndependent ℝ ![F.supportExtensor e₁, F.supportExtensor e₂])
    (h₁ : F.graph.IsLink e₁ u v) (h₂ : F.graph.IsLink e₂ u v)
    (hcover : ∀ w, w = u ∨ w = v) :
    F.RankHypothesis 0 := by
  rw [rankHypothesis_zero_iff]
  intro S hS
  -- Both edges constrain the relative screw `S u - S v`; independence forces `S u = S v`.
  have key : S u = S v :=
    F.eq_of_hingeConstraint_two_parallel S hgen (hS e₁ u v h₁) (hS e₂ u v h₂)
  -- Every body is `u` or `v`, so the motion is constant.
  intro a b
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl <;>
    first | rfl | exact key | exact key.symm

/-- **The Case II rank-lift accounting** (`lem:case-II`, skeleton; Katoh–Tanigawa 2011 §6.3
Lemma 6.8): in the basis-free null-space convention, re-inserting a body `v` — equivalently
pinning it — shifts the realization count by exactly `D = screwDim k`. A framework `F` realizes
the target rank at `k'` (`RankHypothesis F k'`, i.e. `dim Z(G,p) = D + k'`) exactly when its
body-`v`-pinned motion subspace has dimension `k'`. This is the `+D` core of the panel-hinge
1-extension: the pinned subspace `pinnedMotions v` is the null space of the rigidity matrix with
`v`'s `D` columns deleted (the smaller framework `G - v`), and `finrank (pinnedMotions v) + D =
dim Z(G,p)` (pin-a-body Lemma 5.1, `finrank_pinnedMotions_add_screwDim`, Phase 18 green). Hence a
realization of the splitting-off `G_v^{ab}` at its inductive count lifts to a realization of `G`
at the same `k'`, the two new hinge-row blocks accounting for the `+D`. The geometric content —
*constructing* the extended framework from a realization of `G_v^{ab}` and the genericity step
(Claim 6.9) ensuring the supporting extensors are in general position — is the remainder of Case
II, deferred with the genericity device. -/
theorem rankHypothesis_iff_finrank_pinnedMotions [Nonempty α] [Finite α]
    (F : BodyHingeFramework k α β) (v : α) (k' : ℤ) :
    F.RankHypothesis k' ↔ (Module.finrank ℝ (F.pinnedMotions v) : ℤ) = k' := by
  rw [RankHypothesis, ← F.finrank_pinnedMotions_add_screwDim v]
  push_cast
  omega

end BodyHingeFramework

end CombinatorialRigidity.Molecular
