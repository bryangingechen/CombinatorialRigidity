# Phase 21a — Grassmann–Cayley meet / projective-duality foundations (work log)

**Status:** complete (opened + closed 2026-06-03). Prerequisite
sub-phase of the Phase-21 algebraic induction, inserted after the
panel-coplanarity modeling correction (DESIGN.md *Panel-hinge =
hinge-coplanar body-hinge: the coplanarity layer*; MolecularConjecture.md
risk #7 + the Phase-21a detail).

## Current state

**All four deliverables (`topEquiv`, `pairingDualEquiv`, `complementIso`, `meet`)
are green; `def:meet` flipped, chapter `meet.tex` complete.** Deliverable 4 landed
`meet` as the Grassmann–Cayley dual of the Phase-17 join — `*(*A ∨ₑ *B)`, three
applications of `complementIso` as the `*`-operator around the general-grade product
`gradedMul : ⋀^p × ⋀^q → ⋀^(p+q)` (the grade-general form of `wedgeProd`). Grades:
`meet : ⋀^(N−a) × ⋀^(N−b) → ⋀^(N−(a+b))` for `a+b ≤ N` (`N=k+2`), via `hA/hB ▸`
transport of the `complementIso` codomains. Scope-bounded: `meet_ne_zero_iff` and the
geometric-reading API are deferred to the panel layer (Phase 21) + Lemma 5.4 that
consume them (none built yet); projective invariance → Phase 25; no metric Hodge star.
Axiom-clean (propext/Classical.choice/Quot.sound). Deliverable 3 closed via ingredients (a)
`wedgeProd`, (b) the bilinear pairing `wedgePairing`, (c) the signed-permutation
basis matrix (off-diagonal `0` for `T ≠ Sᶜ`, diagonal `≠ 0` via
`wedgePairing_ιMulti_family_compl_ne_zero`), and (d) the assembly
`complementIso` — `wedgePairing` is injective (`wedgePairing_injective`, via the
basis-matrix nondegeneracy) and domain/codomain have equal finrank
(`finrank_exteriorPower_eq_finrank_dual`, both `(k+2).choose j`), so
`LinearMap.linearEquivOfInjective` makes it an iso onto the dual, post-composed
with `(…).exteriorPower (k+2−j) |>.toDualEquiv.symm` to land in `⋀^(k+2−j) V`. File
`Molecular/Meet.lean` carries the screw-algebra specializations
(`screwAlgebraTopEquiv : ⋀^(k+2) (Fin (k+2) → ℝ) ≃ₗ ℝ`,
`screwAlgebraPairingDualEquiv j : ⋀ʲ(V*) ≃ₗ (⋀ʲ V)*`), with the general
facts (`exteriorPower.topEquiv` over any `CommRing`;
`exteriorPower.pairingDualEquiv` + `coe_pairingDualEquiv` for any finite
free `M` with an ordered basis) mirrored under
`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`, plus the new graded wedge
product `wedgeProd (hj : j ≤ k+2) : ⋀ʲ V × ⋀^(k+2−j) V → ⋀^(k+2) V` (the
Phase-17 join landed in the top graded piece via `SetLike.GradedMonoid`, with
`coe_wedgeProd` bridging it to the Phase-17 `∨ₑ`). Blueprint chapter
`meet.tex` (`sec:molecular-meet`): `def:meet-top-equiv` and
`def:meet-pairing-dual` green, `def:meet-complement-iso` + `def:meet` red.

**Route (ii) is genuinely multi-commit.** `complementIso` decomposes into:
(a) `wedgeProd` — the graded product (✓); (b) the bilinear pairing
`wedgePairing : ⋀ʲ V →ₗ Module.Dual ℝ (⋀^(k+2−j) V)`, `A ↦ B ↦ topEquiv (wedgeProd
A B)` (✓ this commit) — built as `wedgeProdBilin` (`LinearMap.mk₂` of `wedgeProd`,
bilinearity of `↑A * ↑B` reflected through `Subtype.ext` + `simp [wedgeProd]`)
post-composed on its output slot with `screwAlgebraTopEquiv` via
`LinearMap.compr₂`; (c)
nondegeneracy via the signed-permutation basis computation
`topEquiv (wedgeProd e_S e_T) = ±1` if `T = Sᶜ` else `0` (the off-diagonal
vanishing is `extensor_eq_zero_of_not_injective`; the diagonal `≠ 0` is
`wedgePairing_ιMulti_family_compl_ne_zero`, via injective-append linear
independence — the sign value itself is not needed, see *Decisions*); (d) `complementIso :=
(LinearMap.linearEquivOfInjective wedgePairing wedgePairing_injective …) ≪≫ₗ
(b.exteriorPower (k+2−j)).toDualEquiv.symm` (✓). Mathlib
exposes no graded `⋀ʲ × ⋀ᵏ → ⋀^(j+k)` map, so (a) was built by hand from the
graded-monoid instance.

**(d) used injectivity, not the abstract `pairingDualEquiv` route.** The
checklist drafted (d) as "pairing-as-equiv via `pairingDualEquiv` ≪≫
`toDualEquiv.symm`", routing the grade-swap sign through `pairingDualEquiv`. The
realized route is cheaper: prove `wedgePairing` injective (`ker_eq_bot'`: evaluate
the zero functional at the complementary basis vector `e_{Sᶜ}` to read off each
coordinate, killed by the (c) lemmas), then `LinearMap.linearEquivOfInjective` +
equal finrank (`finrank_exteriorPower_eq_finrank_dual`) gives the iso onto the dual
directly. `pairingDualEquiv` (deliverable 2) stays the Phase-25 projective-duality
entry but is **not** on the `complementIso` path; the blueprint `\uses` dropped it
accordingly. No sign computation needed (consistent with the deferred-sign decision).

Phase 21 (algebraic induction) is **paused**: its
realization-existence statements need a *panel* layer (coplanar hinges,
DESIGN.md), and the panel layer + Lemma 5.4 + Phase 25 all rest on the
**meet** (regressive product) — the dual half of the Grassmann–Cayley
algebra, which Phase 17 did not build (Phase 17 built the *join* +
a coordinatized Plücker bridge). This sub-phase builds that dual half on
the concrete `V = ℝ^(k+2)`, after which Phase 21 resumes with the panel
layer on top.

## Architectural choices made up front

- **Sibling of Phase 17.** Phase 17 built the *join* (progressive
  product, `join` / `join_extensor`) + the coordinatized bridge; 21a
  builds the *meet* (regressive product) + the duality dictionary. Same
  module family (`Molecular/`), same `ExteriorAlgebra ℝ (Fin (k+2) → ℝ)`
  carrier.
- **Route (ii) for `complementIso`** (user decision 2026-06-03): build it
  via the duality pairing (`pairingDual`-as-iso + the perfect wedge
  pairing), *not* the combinatorial `e_S ↦ ±e_(Sᶜ)` route. Chosen for the
  Phase-25 payoff — the `⋀ʲ(V*) ≃ (⋀ʲ V)*` step is the projective-duality
  dictionary entry Phase 25 reuses.
- **Regressive product only — no metric Hodge star.** Projective geometry
  is metric-free; the meet needs only the top-power volume form
  (orientation), not an inner product. Holds the line against risk #1
  (over-build).
- **Upstream-eligible facts → mirror directory.** The top-power iso,
  `pairingDual`-as-iso, and the perfect-pairing nondegeneracy are general
  free-module facts; mirror under `CombinatorialRigidity/Mathlib/
  LinearAlgebra/ExteriorPower/…` (potential mathlib PRs), per DESIGN.md
  *Mirror directory*.

## Lemma checklist (forward-mode; all red — planning)

Dependency order (route (ii); `N = k+2`, `V = Fin (k+2) → ℝ`):
1. [x] `topEquiv : ⋀ᴺ V ≃ₗ R` — canonical top-power iso via the standard
   basis (`Module.Basis.exteriorPower (Pi.basisFun …)` +
   `LinearEquiv.funUnique` on the singleton top-power index). Mathlib has
   only `zeroEquiv` / `oneEquiv`; landed as the mirror `exteriorPower.topEquiv`
   + the project specialization `screwAlgebraTopEquiv`.
2. [x] `pairingDualEquiv : ⋀ʲ(V*) ≃ₗ (⋀ʲ V)*` (free finite `V`) — upgraded
   mathlib's `exteriorPower.pairingDual` (a bare `→ₗ`) to an iso. **The
   projective-duality dictionary entry reused by Phase 25.** Built as the
   `Basis.equiv` carrying `b.dualBasis.exteriorPower n` onto
   `(b.exteriorPower n).dualBasis` (via `coe_dualBasis` + `basis_coord`),
   with `coe_pairingDualEquiv` identifying it with `pairingDual` in place;
   landed as the mirror `exteriorPower.pairingDualEquiv` + the project
   specialization `screwAlgebraPairingDualEquiv`. The basis-to-iso idiom is
   in FRICTION *Mirrored* under this entry.
3. [x] `complementIso : ⋀ʲ V ≃ₗ ⋀^(N−j) V` — from the perfect wedge
   pairing `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V ≅ R` (via `join` + `topEquiv`), shown
   nondegenerate for free `V`. The genuinely new core. Ingredients
   (a) `wedgeProd` + `coe_wedgeProd`, (b) `wedgePairing` (+ `wedgeProdBilin`),
   **both halves of (c)**, and (d) the assembly all green. Off-diagonal:
   `coe_wedgeProd_ιMulti_family` (the `wedgeProd` of two standard basis vectors is
   the extensor of the concatenated index family) feeds
   `wedgePairing_ιMulti_family_eq_zero_of_not_disjoint` and its `T ≠ Sᶜ` form
   `…_of_ne_compl` (overlap ⇒ repeated basis vector ⇒ vanishing). Diagonal:
   `wedgePairing_ιMulti_family_compl_ne_zero` (`T = Sᶜ` ⇒ append family is a
   permutation of the standard basis ⇒ linearly independent ⇒ extensor `≠ 0` ⇒
   pairing `≠ 0`). The pairing matrix is thus a signed-permutation matrix; (d)
   `wedgePairing_injective` + `finrank_exteriorPower_eq_finrank_dual` +
   `LinearMap.linearEquivOfInjective` + `toDualEquiv.symm` assemble the iso.
4. [x] `meet` (regressive product) — thin layer above `complementIso` +
   Phase-17 `join`: `meet = * ∘ gradedMul ∘ (* × *)` with `* = complementIso`
   the `*`-operator `⋀ʲ → ⋀^(N−j)` (so `meet A B = *(*A ∨ₑ *B)`, **not**
   `complementIso⁻¹` — the dual operator applied three times). Added the
   general-grade product `gradedMul : ⋀^p × ⋀^q → ⋀^(p+q)` (+ `coe_gradedMul`)
   as the grade-general form of `wedgeProd`; `∧ₑ` notation. Grades
   `⋀^(N−a) × ⋀^(N−b) → ⋀^(N−(a+b))` (`a+b ≤ N`). `meet_ne_zero_iff` and the
   geometric reading (*meet of two hyperplane normals = supporting `k`-extensor
   of their codim-2 intersection, landing in `ScrewSpace k`*) are **deferred to
   the consumers** (panel layer Phase 21 + Lemma 5.4) per the scope boundary —
   build only what those consume; neither is built yet.

Scope boundary: build only the meet-properties the panel layer + Lemma
5.4 consume. Projective *invariance* (Crapo–Whiteley) → Phase 25. No
metric Hodge star.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **Diagonal half of (c): nonzero, not the sign value.** The deliverable was
  drafted as "compute `topEquiv (wedgeProd e_S e_{Sᶜ}) = ±1` (the interleaving
  permutation sign)", with a flagged sign-convention check against
  `supportExtensor` / KT's `C(·)`. Resolved more cheaply: nondegeneracy needs only
  `≠ 0`, and the `T = Sᶜ` append family is a permutation of the standard basis,
  hence linearly independent (`Basis.linearIndependent.comp` + `Fin.append_injective_iff`
  with disjoint ranges `S`, `Sᶜ`), so its extensor is `≠ 0`
  (`extensor_ne_zero_iff_linearIndependent`) and `screwAlgebraTopEquiv` injective
  preserves that. The sign value (and the convention question) is not needed for
  `complementIso`; defer any honest-sign computation to where the panel hinge
  extensor actually consumes it (FRICTION *No mathlib `g ∘ Fin.append …`*).
- **`topEquiv` via the singleton top-power index, not `finrank_eq`.** The
  cleanest route is `(Pi.basisFun ℝ (Fin N)).exteriorPower N).equivFun ≪≫ₗ
  LinearEquiv.funUnique …`: the top-power basis is indexed by
  `Set.powersetCard (Fin N) N`, which is a singleton (`Unique`, only
  `Finset.univ`), so `funUnique` collapses the `pi`-type to `ℝ`
  canonically. The mirror adds the `Set.powersetCard.instUniqueTop`
  instance to enable this; stated over a general `CommRing` for maximal
  upstream eligibility. The characterizing simp lemma
  `topEquiv_ιMulti_family_default` sends the all-basis wedge to `1`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *Panel-coplanarity gap; coplanarity layer; meet front-loaded; route
  (ii) for `complementIso`; this sub-phase* → DESIGN.md *Panel-hinge =
  hinge-coplanar body-hinge: the coplanarity layer*; MolecularConjecture.md
  risk #7.

## Blockers / open questions

- **Abstract vs concrete carrier for the mirror lemmas.** Whether
  `pairingDual`-as-iso and the perfect-pairing nondegeneracy are cleanest
  over an abstract free finite `V` (more upstream-eligible) or directly on
  `ℝ^(k+2)` (matches the consumer). Lean on the abstract form for the
  mirror, specialize at the consumer; confirm on contact.
- **Sign / orientation bookkeeping in `complementIso`** *(deferred, not on the
  critical path).* The `j` ↔ `N−j` grade swap carries a permutation sign. The
  diagonal-of-(c) step was drafted to pin this sign and check it against
  `supportExtensor` / KT's `C(·)`, but `complementIso` only needs the diagonal
  pairing `≠ 0`, so the diagonal half landed as nonzero (not the sign) and the
  convention check is deferred to wherever the panel hinge extensor consumes an
  oriented meet (Phase 21 panel layer / Lemma 5.4). No user decision needed now.
  **Forward flag (Phase-22a Stage-3 KT audit, 2026-06-05):** everything 21a–22a consumes
  needs only `≠ 0`, so the deferral remains correct; but **verify before Phase 25**
  (Crapo–Whiteley projective invariance) / Phase 26 (molecule modelling equivalence) whether
  an *oriented* meet (KT's sign convention on `C(·)`) is consumed there — if so, the deferred
  diagonal-(c) sign computation has to land then. See `notes/Phase22-realization-design.md` §1.15.

## Hand-off / next phase

**Phase 21a is complete.** All four deliverables green: `screwAlgebraTopEquiv` /
`screwAlgebraPairingDualEquiv` / `complementIso` / `meet` in `Molecular/Meet.lean`,
chapter `meet.tex` fully green. `meet = *(*A ∨ₑ *B)` (`* = complementIso`, three
applications) over the general-grade product `gradedMul`; axiom-clean.

**Phase 21 now resumes** with the panel layer in `Molecular/AlgebraicInduction.lean`
(it was paused for this sub-phase). Smallest concrete next commit: the panel-hinge
framework `PanelHingeFramework` → `toBodyHinge` → the one-time hinge-coplanarity
constraint `IsHingeCoplanar` (DESIGN.md *Panel-hinge = hinge-coplanar body-hinge*),
consuming `meet` for the coplanarity layer. Then Lemma 5.4 (panel cycle), then the
re-scoped Cases I/II/III. See `notes/Phase21.md` (still ◷ in progress) for the paused
realization-existence nodes and the panel re-scope plan; the meet-properties those
nodes need (`meet_ne_zero_iff` / geometric reading) land in Phase 21 alongside the
first consumer, not here (scope boundary).
