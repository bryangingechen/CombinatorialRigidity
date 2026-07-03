# Fresh-edge supply (`hfresh`) repair — design recon

**Status:** OPEN (2026-07-02). Blocks R1 of the post-Phase-23 cleanup round
(`notes/Phase23-cleanup.md`) — R1 must not pin fresh prose to the affected
statements. Canonical home for this arc per `notes/CLAUDE.md` (*Live design
recon*); compress to a verdict + pointer once the repair lands.

## The finding (coordinator, 2026-07-02; kernel-checked)

The hypothesis threaded through the Theorem-5.5 spine and
`molecular_conjecture`
(`CombinatorialRigidity/Molecular/AlgebraicInduction/Theorem55.lean` 2522ff)

```lean
hfresh : ∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G')
```

is **unsatisfiable for every nonempty `α` and every `β`** (finite or
infinite): the all-loops-at-one-vertex graph is a legal `Graph α β` with
`edgeSet = Set.univ`. Kernel-checked against the project's mathlib
(compiles as a standalone snippet):

```lean
import Mathlib.Combinatorics.Graph.Basic

open Graph in
example {α β : Type} [Nonempty α] : ¬ (∀ G' : Graph α β, ∃ e₀ : β, e₀ ∉ E(G')) := by
  intro h
  obtain ⟨a⟩ := ‹Nonempty α›
  obtain ⟨e₀, he₀⟩ := h
    { vertexSet := {a}
      IsLink := fun _ x y => x = a ∧ y = a
      edgeSet := Set.univ
      isLink_symm := by intro e _ x y hxy; exact ⟨hxy.2, hxy.1⟩
      eq_or_eq_of_isLink_of_isLink := by
        intro e x y v w hxy hvw; left; rw [hxy.1, hvw.1]
      edge_mem_iff_exists_isLink := by
        intro e; simp only [Set.mem_univ, true_iff]; exact ⟨a, a, rfl, rfl⟩
      left_mem_of_isLink := by intro e x y hxy; exact hxy.1 }
  exact he₀ (Set.mem_univ e₀)
```

Consequences:

- **`molecular_conjecture` is vacuously true**: it assumes `[Nonempty α]`
  and `hfresh`, an inconsistent set. It can never be instantiated.
- The whole `hfresh`-carrying family is effectively vacuous the same way
  (their `2 ≤ V(G).ncard` hypotheses force `α` nonempty). Carriers (grep
  `hfresh`, 2026-07-02): `AlgebraicInduction/Theorem55.lean` (the spine +
  Thm 5.6 forms + `molecular_conjecture`), `AlgebraicInduction/CaseII.lean`,
  `AlgebraicInduction/CaseIII/{Arms,Realization}.lean`,
  `Induction/Operations.lean`,
  `Induction/ForestSurgery/{ChainExtraction,Reduction}.lean`. (The
  `PebbleGame/Algorithm.lean` hit is an unrelated same-named local.)
- **The mathematics is not affected**: every use of `hfresh` draws a fresh
  label for edge surgery (`obtain ⟨e₀, he₀⟩ := hfresh G'` at the ambient
  graph, at `splitOff` variants, and at helper graphs carrying
  `E(G) ∪ {e₀}` — see `notes/Phase22-realization-design.md` §1.49(3)).
  No proof exploits the falsity. This is a statement-packaging error in
  how the fresh-label supply was quantified.
- The cleanup round's S1 audit item proposed deriving `hfresh` from
  `[Infinite β]` — impossible twice over: the family carries `[Finite β]`,
  and `hfresh` is false even for infinite `β`. S1's instinct (the binder
  is wrong) was right; its remedy is dissolved by this finding.
- A Phase-22a design decision **leaned on the false hypothesis**
  (`notes/Phase22a.md` ~440: "Option (ii) `β = E(G)` is ruled out
  (`hfresh` forces spare labels in `β`)"). That seam must be re-examined
  under the repaired supply.

## Facts scoped so far (verify before building on them)

- `rigidityRows` is a `Set (Module.Dual ℝ (α → ScrewSpace k))`
  (`RigidityMatrix/Basic.lean:650`) — the row space is `α`-indexed, not
  `β`-indexed, so `[Finite β]` is *probably* edge-counting/`ncard`
  plumbing rather than framework-layer load-bearing. **Unverified**;
  `Finite β` has ~49 occurrences across 21 `Molecular/` files.
- The "total over `β`" convention (`∀ e, supportExtensor e ≠ 0` quantified
  over all of `β`, not `E(G)`) interacts with the supply: see
  `molecular_conjecture`'s docstring (the `≥ 2`-body discussion).

## Candidate repair routes (recon to settle; none pinned)

1. **`[Infinite β]` restructure** — the mathematically honest form: on the
   `hfresh`-carrying family, replace `[Finite β]` with `[Infinite β]` +
   explicit finiteness of the specific edge sets in play; `hfresh` becomes
   the true, derivable `∀ S : Set β, S.Finite → ∃ e₀ ∉ S`
   (≈ `Set.Finite.exists_not_mem`-shaped). Requires mapping which
   `[Finite β]` uses are genuinely needed and threading per-graph
   edge-finiteness through the surgeries.
2. **Bounded-supply form under `[Finite β]`** — restrict the quantifier to
   graphs actually encountered (edge sets bounded relative to `E(G)`),
   satisfiable under a `Nat.card β` headroom hypothesis. Keeps the
   framework layer untouched; invasive at every application site inside
   the defeq-fragile zone; uglier as a published statement.
3. Anything better the recon finds (e.g. the applications may need only
   labels outside `E(G) ∪ {≤ 2 extras}` at a time, admitting a smaller
   statement change).

## Recon deliverables

- The chosen route with **exact target signatures** for the reshaped
  spine entries and `molecular_conjecture`, and a leaf decomposition
  (buildable commits, sized).
- The `[Finite β]` dependency map for the affected family (genuine vs
  incidental uses).
- A satisfiability witness plan: after the repair, a concrete
  instantiation (e.g. `α := Fin m`, `β := ℕ`) must be exhibitable —
  this is the regression test that vacuity cannot recur.
- The Phase-22a `β = E(G)` seam re-examined under the repaired supply.
- Status-surface plan: what the README / blueprint / ROADMAP honesty
  annotations should say until the repair lands.

## Verdict

*(pending recon)*
