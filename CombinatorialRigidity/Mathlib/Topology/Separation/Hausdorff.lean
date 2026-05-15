/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathlib.Topology.Separation.Hausdorff

/-!
# Upstream candidates: openness of injectivity for finite-domain perturbations

Let `V` be a finite type and `α` a Hausdorff topological space. If a continuous family
`F : X → V → α` of `V`-tuples is *injective at one base point* `x₀`, then it is
*injective on a neighborhood* of `x₀`. In other words, `Injective (F ·)` is an open
property of the parameter `x` under componentwise continuity in `x`, provided the index
type is finite and the target is T2.

Mathlib already has `Set.InjOn.exists_mem_nhdsSet` (here, in
`Mathlib.Topology.Separation.Hausdorff`), but that lemma asks for `f : X → Y` injective
on a compact set `s ⊆ X` and produces a *neighborhood of `s`*. The shape needed in
continuous-deformation arguments — a one-parameter family `F : X → V → α` evaluated at
`V`-many points, injective in the second slot at the basepoint — is dual to that, and
does not seem to have a direct upstream form.

## Main results

* `Function.Injective.eventually_of_continuousAt` — the general lemma: a `Finite`-
  indexed family that is componentwise continuous at `x₀` and injective at `x₀` is
  eventually injective.
* `Function.Injective.eventually_update_of_continuousAt` — the `Function.update`
  corollary: if `p₀ : V → α` is injective and `f : X → α` is a continuous deformation
  through `f x₀ = p₀ c` of the `c`-th coordinate, then `update p₀ c (f x)` is injective
  for `x` in a neighborhood of `x₀`. This is the form Henneberg-move generic-placement
  arguments use (cf. `exists_nonCollinear_rigid_placement_dim_two`).

The Lean namespace is the upstream one (`Function.Injective`); promotion to mathlib is
a copy-paste alongside `Set.InjOn.exists_mem_nhdsSet`. See `DESIGN.md`
"Mirror directory".
-/

open Filter Topology

namespace Function

variable {X : Type*} [TopologicalSpace X] {x₀ : X}
  {α : Type*} [TopologicalSpace α] [T2Space α]
  {V : Type*} [Finite V]

/-- If a family `F : X → V → α` of `V`-tuples (with `V` a finite type and `α` Hausdorff)
is *componentwise continuous* at a base point `x₀` and *injective* at `x₀`, then it is
injective on a neighborhood of `x₀`.

Each pair `(u, v)` with `u ≠ v` contributes a `ContinuousAt.prodMk`-driven eventuality
that `(F x u, F x v)` stays off the diagonal (closed in `α × α` by Hausdorffness);
`Finset.eventually_all` aggregates the finitely many pair-eventualities into a single
neighborhood. -/
theorem Injective.eventually_of_continuousAt {F : X → V → α}
    (hcont : ∀ v, ContinuousAt (fun x => F x v) x₀) (hinj : Injective (F x₀)) :
    ∀ᶠ x in 𝓝 x₀, Injective (F x) := by
  haveI : Fintype V := Fintype.ofFinite V
  have h_each : ∀ uv ∈ (Finset.univ : Finset (V × V)),
      ∀ᶠ x in 𝓝 x₀, uv.1 ≠ uv.2 → F x uv.1 ≠ F x uv.2 := by
    rintro ⟨u, v⟩ _
    by_cases huv : u = v
    · exact .of_forall (fun _ h => absurd huv h)
    have h_ne : F x₀ u ≠ F x₀ v := fun h => huv (hinj h)
    have h_prod : ContinuousAt (fun x => (F x u, F x v)) x₀ :=
      (hcont u).prodMk (hcont v)
    have h_compl : (Set.diagonal α)ᶜ ∈ 𝓝 (F x₀ u, F x₀ v) :=
      isClosed_diagonal.isOpen_compl.mem_nhds h_ne
    filter_upwards [h_prod h_compl] with x hx _ using hx
  filter_upwards [Finset.univ.eventually_all.mpr h_each] with x hx u v heq
  by_contra h_uv
  exact hx (u, v) (Finset.mem_univ _) h_uv heq

/-- One-coordinate perturbation form of `Function.Injective.eventually_of_continuousAt`.
If `p₀ : V → α` is injective on a finite type `V` (with `α` Hausdorff) and `f : X → α`
is a continuous deformation through `f x₀ = p₀ c` of the `c`-th coordinate, then
`Function.update p₀ c (f x)` is injective for `x` in a neighborhood of `x₀`.

Used to lift "injective at the base placement" through a one-vertex `Function.update`
perturbation in Henneberg-move generic-placement arguments. -/
theorem Injective.eventually_update_of_continuousAt [DecidableEq V] {p₀ : V → α}
    (hp₀ : Injective p₀) {c : V} {f : X → α}
    (hf : ContinuousAt f x₀) (hf0 : f x₀ = p₀ c) :
    ∀ᶠ x in 𝓝 x₀, Injective (update p₀ c (f x)) := by
  have h_eq0 : update p₀ c (f x₀) = p₀ := by
    funext v
    by_cases hvc : v = c
    · subst hvc; simp [hf0]
    · simp [update_of_ne hvc]
  have hcont : ∀ v, ContinuousAt (fun x => update p₀ c (f x) v) x₀ := by
    intro v
    by_cases hvc : v = c
    · subst hvc; simpa using hf
    · simpa [update_of_ne hvc] using (continuousAt_const : ContinuousAt (fun _ : X => p₀ v) x₀)
  have hinj₀ : Injective (update p₀ c (f x₀)) := by rw [h_eq0]; exact hp₀
  exact Injective.eventually_of_continuousAt (F := fun x => update p₀ c (f x)) hcont hinj₀

end Function
