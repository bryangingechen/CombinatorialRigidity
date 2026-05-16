# Phase 7 — Lovász–Yemini matroid identification (work log)

**Status:** ✓ complete (closed by Commit 19).

This file is the per-phase work record. See `../ROADMAP.md` §7 for the
high-level plan and `../DESIGN.md` for cross-cutting design choices.

**Workflow:** Phase 7 ran in **forward blueprint mode** (Option C,
hybrid skeleton) per `../blueprint/DESIGN.md` *Recommendation for
Phase 6*. The blueprint chapters `chapter/rigidity-matroid.tex` +
`chapter/count-matroid.tex` are the authoritative dep-graph and lemma
index; this file does **not** duplicate them.

## Current state

Phase complete in 22 commits across two new Lean files
(`MatroidIdentification.lean`, `CountMatroid.lean`) plus reflows of
`Sparsity.lean`, `RigidityMatroid.lean`, `LamanTheorem.lean`, and
`HennebergRigidity.lean`. Final landscape: the planar rigidity matroid
is packaged as a `Matroid (Sym2 V)` via the abstract $(k, \ell)$-count
matroid in the matroidal regime $\ell < 2k$ (Whiteley 1996; Lee–Streinu
2008) — `SimpleGraph.rigidityMatroid V := countMatroid V 2 3 (by omega)`
— and its independent sets are characterised both combinatorially
(via `countMatroid_indep_iff`) and linear-algebraically (via
`rigidityMatroid_indep_iff_edgeSetRowIndependent`). The combinatorial
augmentation axiom `IsSparse.exists_aug_of_lt_two_mul` is the bridge
Phase 8's linear-matroid framing will reduce through. Blueprint chapter
split: `chapter/count-matroid.tex` (abstract) +
`chapter/rigidity-matroid.tex` (row-LI + planar); both dep-graphs are
all-green. Per-commit narrative: `git log --oneline 60a2176..`.

*Scope was originally a one-off rigidity matroid; expanded in Commit 16
on user direction. Commit 17's original `union_with_bonus` augmentation
sketch was replaced with the Lee–Streinu component-based proof (Theorem
5(1,2,4)) — the natural bonus $e \in J \setminus I$ aren't I-edges and
so don't satisfy `union_with_bonus`. Split into 17a (block intersection
closure), 17b (I-components, edge-disjointness), 17c (assembly).*

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Statement form: reverse = flat, forward = operation form.** See
  `../DESIGN.md` *Statement-form conventions* and the blueprint aside
  at `chapter/rigidity-matroid.tex` §3.1. `IsSparse.exists_typeI_or_typeII_reverse`
  lands flat; row-LI lifts land in operation form; the inductive
  proof bridges via `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors` per step.

- **`maxBlock` anchored on a Finset, not on a pair** (Commit 17b,
  user-directed). `IsSparse.maxBlock` takes `X : Finset V`; the
  augmentation argument specialises at $X = \{u, v\}$. Reads as math
  (*"the maximal $I$-tight Finset containing $X$"*) and skips
  Sym2-symmetry boilerplate. Body uses `Set` + `Set.Finite.toFinset`
  rather than `Finset.univ.filter` to dodge `DecidablePred` /
  `SemilatticeSup` instance-synthesis friction over `[Finite V]`
  (pattern promoted to TACTICS-QUIRKS § 14).

- **"Some generic placement" formulation.** The hard direction's
  conclusion is $\exists p, \mathrm{EdgeSetRowIndependent}\,p\,I$;
  no "generic placement" notion (Zariski-open, measure-zero).

- **Proof route: Jordán §2.2 induction on $|E|$.** Each step picks a
  min-degree-$\le 3$ vertex in the sparse graph and reverses the
  Henneberg move; reverse-decomposition reuses Phase 5's
  `IsTightOn.union_inter` (Jordán Lemma 2.1.2). Jordán's "critical
  set" ↔ our `IsTightOn` (documented in `rigidity-matroid.tex`
  *Terminology* aside).

- **Lean placement.** Phase 7 content lives in new files
  `MatroidIdentification.lean` + `CountMatroid.lean`;
  `RigidityMatroid.lean` stays as the row-LI predicate /
  easy-direction file. Lemma checklist is the blueprint dep-graph,
  not here.

## Decisions made during this phase

### Phase-local choices and proof techniques

Decisions + rationale only; proof structure lives in each lemma's
Lean doc-comment and the commit history.

- **Generalize, do not duplicate.** Where Phase 5's Laman-only lemmas
  actually use sparsity, lift to `IsSparse` and delete the Laman
  wrapper. Affected: degree helpers, the five blocker-contradiction
  primitives, `typeII_reverse_blocker`, `image_edgesIn_comap`
  (un-privatized).

- **Flat-form sparse reverse: subtype `{w // w ≠ v}` not `Sym2 V`
  predicate.** `IsSparse.exists_typeI_or_typeII_reverse` uses
  `G.comap (Subtype.val : {w // w ≠ v} → V)` for consumer ergonomics:
  downstream row-LI lifts work at that subtype and Phase 5's iso
  constructors are already subtype-shaped.

- **Row-LI conditional cores mirror Phase 5's IR-side `extend`
  lemmas.** `typeI_edgeSetRowIndependent_extend` /
  `typeII_edgeSetRowIndependent_extend` share Phase 5's
  `LinearIndepOn.union` partition + test-motion structure on the
  row-LI/dual side. Type II's deleted-edge row identity is now
  shared with the IR proof as `typeII_collinear_inner_combo`
  (cleanup C3).

- **Row-LI openness (Commit 10).** `EdgeSetRowIndependent.eventually`
  mirrors `IsInfinitesimallyRigid.eventually`. Obstacle:
  `Module.Dual ℝ (Framework V d)` has no canonical norm. Resolution:
  transport along `b.dualBasis.equivFun` to `Fin n → ℝ` (continuity
  via `@[fun_prop]`-tagged `continuous_rigidityMap_apply`).

- **Pendant row-LI lift (Commit 13).**
  `typeI_pendant_edgeSetRowIndependent_{extend, lift}` handles the
  `b = a` degeneracy with a singleton new-edge; no `[Finite V]`
  needed since the pendant path doesn't go through `eventually`.

- **3-way reverse decomposition (Commit 12).**
  `IsSparse.exists_typeI_or_typeII_reverse` splits on
  `G.degree v ∈ {1, 2, 3}` (pendant / Type I / Type II). Degree
  positivity (`≥ 1`) from new helper
  `IsSparse.exists_one_le_degree_le_three`. Laman shell discards the
  pendant branch via `IsLaman.two_le_degree`.

- **Hard-direction `|E|`-induction (Commit 14).**
  `IsSparse.exists_rowIndependent_placement` runs strong induction
  on `Fintype.card V`. New iso lemma `EdgeSetRowIndependent.iso`
  factors `G.rigidityRow (q ∘ φ)` through a precomposition-
  `LinearEquiv`'s `dualMap`; Type I branch routes through
  `exists_distinct_rowIndependent_placement_dim_two` for the
  `p' a ≠ p' b` precondition.

- **Property-polymorphic affinely-spanning + iff (Commit 15).**
  Generalised `exists_affinelySpanning_rigid_placement` to
  `exists_affinelySpanning_of_eventually` (consumes `∀ᶠ p in 𝓝 p₀, P p`);
  retired the IR-specific wrapper (single caller). Iff `(⇐)` bridges
  via `LinearIndependent.comp` along an injective reindex on
  `H = fromEdgeSet (Subtype.val '' I)`.

- **Commits 17a/b/c (augmentation).** See *Current state* /
  *Blockers* for the route resolution; per-commit detail in the Lean
  doc-comments + `Sparsity.lean`'s *IComponents* / *Augmentation*
  section headers.

- **Commits 18–19 (matroid packaging).** `SimpleGraph.countMatroid`
  via `IndepMatroid.ofFinite` (trivial axioms two-line each;
  augmentation axiom is `IsSparse.exists_aug_of_lt_two_mul` directly).
  `SimpleGraph.rigidityMatroid V := countMatroid V 2 3 (by omega)`;
  matroid-form Lovász–Yemini composes `countMatroid_indep_iff` with
  `edgeSet_rowIndependent_iff_isSparse_dim_two`. Blueprint statement
  tightened to drop unused $|V| \ge 2$ (iff is unconditional).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Mirror `LinearIndependent.dualMap_of_surjective`* → FRICTION
  [mirrored] (the post-Phase-5 mirror landed in commit `757e4d5`).
- *Sym2-eq case split in `typeII_isInfinitesimallyRigid_extend`* →
  FRICTION [resolved] + TACTICS-GOLF § 5 *Lifting Subtype-Sym2
  equalities*, subsection "the other direction".
- *Test-motion gadget named in blueprint; Lean tightened* → FRICTION
  [resolved] *"Test motion `x_α` gadget in Phase 7 understated by
  blueprint prose"*.
- *`elemSkewMap_ofLp_inr_apply` proof collapse via wider simp + grind*
  → FRICTION [resolved] + TACTICS-GOLF § 1 *Tricks*.
- *Phase 5 + Phase 7 golf: `γ • _ = _` rewrite chain → `eq_inv_smul_iff₀`*
  → already covered by TACTICS-GOLF § 7's search decision tree.
- *`Finset.univ.filter` of `Finset V` over `[Finite V]` instance friction*
  → TACTICS-QUIRKS § 14 (from the `maxBlock` body decision).
- *Typeclass shape on `V` (`[Finite V]` vs `[Fintype V]`) follows mathlib
  style* → DESIGN.md *Typeclass shape for finiteness on `V`* (resolution
  arc landed in the Phase 7 cleanup round).

### Cleanup pass summaries

Per-file effect of Phase 7's 22 commits.

- **New files.** `MatroidIdentification.lean` (Commit 7+; holds the
  four operation-form row-LI lifts incl. pendant, the perturbation
  helper, the hard-direction `IsSparse.exists_rowIndependent_placement`,
  the iff `edgeSet_rowIndependent_iff_isSparse_dim_two`, and Commit 19's
  `SimpleGraph.rigidityMatroid` + matroid-form Lovász–Yemini).
  `CountMatroid.lean` (Commit 18; `SimpleGraph.countMatroid` via
  `IndepMatroid.ofFinite`).
- **Sparsity-side.** `Sparsity.lean` grew the degree helpers, the five
  blocker-contradiction primitives, `typeII_reverse_blocker`,
  `image_edgesIn_comap` (lifted from `Henneberg.lean`), the flat-form
  3-way `exists_typeI_or_typeII_reverse`, and the Commit 17a/b/c
  augmentation infrastructure (`IsTightOn.union_inter_of_pair`, the
  `IComponents` block of `HasBlock` / `maxBlock` / `maxBlock_isTightOn` /
  `maxBlock_eq_of_subset_maxBlock`, and `exists_aug_of_lt_two_mul`).
  Added import `Mathlib.Data.Set.Card.Arithmetic`.
- **Phase 5 reflows.** `Henneberg.lean` lost ~280 LoC of the old
  Laman-only reverse machinery; `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors` un-privatized, as were
  `exists_off_line_off_finite_dim_two` and
  `exists_not_mem_span_singleton_dim_two` in `HennebergRigidity.lean`.
  `RigidityMatroid.lean` gained `EdgeSetRowIndependent.{eventually, iso}`
  and the property-polymorphic `exists_affinelySpanning_of_eventually`
  (replacing the IR-specific wrapper); `LamanTheorem.lean`'s Phase 6
  caller inlined the IR-witness `obtain`. `TrivialMotions.lean`'s
  `elemSkewMap_ofLp_inr_apply` collapsed to one line.

## Blockers / open questions

- **Pebble game (future-friction).** Lee–Streinu's $(k, \ell)$-pebble
  game is an algorithmic complement to the I-component augmentation
  proof (rejected edges ↔ tight components). Phase 7 does **not**
  depend on it — the component-based proof closes the matroid axiom
  directly. Logged here and in `count-matroid.tex` as future direction;
  referenced from `../DESIGN.md` *Typeclass shape for finiteness on `V`*
  resolution discussion as a deferred motivation.

- **Phase 5 IR + Phase 7 row-LI typeII conditional core unification.**
  Option 1 (extract the shared inner-product row identity) **landed**
  via the Phase 7 cleanup round (C3, 2026-05-16) as
  `SimpleGraph.Henneberg.typeII_collinear_inner_combo` in
  `HennebergRigidity.lean`; both extends consume it. Option 3
  (principled `rank R_typeII = rank R_{G'} + 2`, IR + row-LI as
  corollaries) remains deferred — it wants Phase 8's `Matroid`
  infrastructure to pin down the rank API. Option 2 was subsumed by
  option 3 and never pursued. See `notes/Phase7-cleanup.md`
  *Decisions made → C3* for the full record.

## Hand-off / next phase

Phase 7 closes the matroid-side identification: the planar rigidity
matroid is packaged as a `Matroid (Sym2 V)` via the $(2, 3)$-count
matroid (`SimpleGraph.rigidityMatroid` in `MatroidIdentification.lean`),
and its independent sets are characterised both combinatorially (by
`countMatroid_indep_iff`) and linear-algebraically (by
`rigidityMatroid_indep_iff_edgeSetRowIndependent`).

**Next phase (Phase 8).** The linear-matroid framing of the rigidity
matroid via `apnelson1/Matroid` (`Matroid.ofFun` of the rigidity-row
function at a generic placement). Target:

```
linearRigidityMatroid V 2 ≅ rigidityMatroid V
```

stating Lovász–Yemini is a matroid iso, not just an
independence-iff. Requires adding `apnelson1/Matroid` (or equivalent)
as a project dependency and developing the `Matroid.ofFun`-style
construction. The combinatorial bridge already lands in this phase:
`IsSparse.exists_aug_of_lt_two_mul` is what the linear-matroid
identification reduces through.

**Inter-phase cleanup.** The Phase 7 → Phase 8 cleanup round is logged
in `notes/Phase7-cleanup.md` (buckets A: blueprint/Lean divergence
audit; B: code-smell sweep; C: long-proof audit; D: this notes-
compression bucket).
