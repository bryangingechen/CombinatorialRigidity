# Phase 21a — Grassmann–Cayley meet / projective-duality foundations (work log)

**Status:** in progress (opened 2026-06-03). Prerequisite
sub-phase of the Phase-21 algebraic induction, inserted after the
panel-coplanarity modeling correction (DESIGN.md *Panel-hinge =
hinge-coplanar body-hinge: the coplanarity layer*; MolecularConjecture.md
risk #7 + the Phase-21a detail).

## Current state

**Deliverables 1–2 (`topEquiv`, `pairingDualEquiv`) are green; deliverable 3
(`complementIso`) is started — ingredients (a) `wedgeProd` and (b) the bilinear
pairing `wedgePairing` are green.** File
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
vanishing is `extensor_eq_zero_of_not_injective`; the diagonal sign is the
*open sign subproblem* in *Blockers*); (d) `complementIso :=
(pairing-as-equiv) ≪≫ₗ (b.exteriorPower (k+2−j)).toDualEquiv.symm`. Mathlib
exposes no graded `⋀ʲ × ⋀ᵏ → ⋀^(j+k)` map, so (a) was built by hand from the
graded-monoid instance.

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
3. [ ] `complementIso : ⋀ʲ V ≃ₗ ⋀^(N−j) V` — from the perfect wedge
   pairing `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V ≅ R` (via `join` + `topEquiv`), shown
   nondegenerate for free `V`. The genuinely new core. *In progress:* ingredients
   (a) `wedgeProd` + `coe_wedgeProd` and (b) `wedgePairing` (+ `wedgeProdBilin`)
   landed; nondegeneracy (c) / `toDualEquiv.symm` composition (d) remain (see
   *Current state* for the (a)–(d) decomposition).
4. [ ] `meet` (regressive product) — thin layer above `complementIso` +
   Phase-17 `join` (`meet = complementIso⁻¹ ∘ join ∘ (complementIso ×
   complementIso)`); + `meet_ne_zero_iff` (⟺ transversal / independent),
   the grade arithmetic, and the geometric reading: *meet of two
   hyperplane normals = supporting extensor of their codim-2 intersection*,
   landing in `ScrewSpace k`.

Scope boundary: build only the meet-properties the panel layer + Lemma
5.4 consume. Projective *invariance* (Crapo–Whiteley) → Phase 25. No
metric Hodge star.

## Decisions made during this phase

### Phase-local choices and proof techniques
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
- **Sign / orientation bookkeeping in `complementIso`.** The `j` ↔ `N−j`
  grade swap carries a permutation sign; route (ii) routes it through
  `pairingDual`'s `det` form, which should absorb it — verify the sign
  convention matches what the panel hinge extensor needs (`supportExtensor`
  sign vs KT's `C(·)`).

## Hand-off / next phase

Deliverable 3 (`complementIso`) is in progress: ingredients (a) `wedgeProd` +
`coe_wedgeProd` and (b) the bilinear wedge pairing
`wedgePairing k hj : ⋀ʲ V →ₗ[ℝ] Module.Dual ℝ (⋀^(k+2−j) V)` (+ `wedgeProdBilin`,
`wedgePairing_apply`) are green; `def:meet-complement-iso` stays red. **Next
concrete commit: ingredient (c)**, the basis
computation `screwAlgebraTopEquiv (wedgeProd hj e_S e_T) = ±1` if `T = Sᶜ`
else `0` (off-diagonal = `extensor_eq_zero_of_not_injective` via a repeated
basis vector; **the diagonal sign is the open sign subproblem in *Blockers*** —
verify against `supportExtensor` / KT's `C(·)`), giving nondegeneracy. *Then*
(d): `complementIso := (pairing-as-equiv) ≪≫ₗ
(Pi.basisFun …).exteriorPower (k+2−j) |>.toDualEquiv.symm`, flipping
`def:meet-complement-iso` green. Then `meet` + its lemmas (deliverable 4).
**Route (ii) is multi-commit** — budget (b)/(c)/(d) as separate commits; the
sign subproblem in (c) is the one place that may need a user decision if the
orientation convention conflicts with the panel hinge extensor. When 21a's
deliverables are green, **Phase 21 resumes** with the panel layer
(`PanelHingeFramework` → `toBodyHinge` → `IsHingeCoplanar` once; DESIGN.md
*Panel-hinge = hinge-coplanar body-hinge*), then Lemma 5.4 (panel cycle),
then the re-scoped Cases I/II/III.
