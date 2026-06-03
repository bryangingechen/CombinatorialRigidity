# Phase 21a — Grassmann–Cayley meet / projective-duality foundations (work log)

**Status:** planning (recorded 2026-06-03; no Lean yet). Prerequisite
sub-phase of the Phase-21 algebraic induction, inserted after the
panel-coplanarity modeling correction (DESIGN.md *Panel-hinge =
hinge-coplanar body-hinge: the coplanarity layer*; MolecularConjecture.md
risk #7 + the Phase-21a detail).

## Current state

Plan only. Phase 21 (algebraic induction) is **paused**: its
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
1. [ ] `topEquiv : ⋀ᴺ V ≃ₗ R` — canonical top-power iso via the standard
   basis (`Module.Basis.exteriorPower (Pi.basisFun …)` +
   `exteriorPower.finrank_eq`). Mathlib has only `zeroEquiv` / `oneEquiv`;
   this is a mirror lemma.
2. [ ] `pairingDualEquiv : ⋀ʲ(V*) ≃ₗ (⋀ʲ V)*` (free finite `V`) — upgrade
   mathlib's `exteriorPower.pairingDual` (a bare `→ₗ`) to an iso via its
   dual-basis lemmas (`pairingDual_apply_apply_eq_one` / `_one_zero`) +
   `Module.Basis.exteriorPower`. Mirror lemma. **The projective-duality
   dictionary entry reused by Phase 25.**
3. [ ] `complementIso : ⋀ʲ V ≃ₗ ⋀^(N−j) V` — from the perfect wedge
   pairing `⋀ʲ V × ⋀^(N−j) V → ⋀ᴺ V ≅ R` (via `join` + `topEquiv`), shown
   nondegenerate for free `V`. The genuinely new core.
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
*(none yet — planning)*

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

Plan only; no Lean yet (plan-first, per the panel re-scope). When work
resumes, the first Lean commit is **deliverable 1, `topEquiv`** — the
smallest leaf, a mirror lemma `⋀ᴺ (Fin (k+2) → ℝ) ≃ₗ ℝ`. Then
`pairingDualEquiv` (2), `complementIso` (3), `meet` + its lemmas (4); a
forward-mode blueprint chapter opens with that first commit. When 21a's
deliverables are green, **Phase 21 resumes** with the panel layer
(`PanelHingeFramework` → `toBodyHinge` → `IsHingeCoplanar` once; DESIGN.md
*Panel-hinge = hinge-coplanar body-hinge*), then Lemma 5.4 (panel cycle),
then the re-scoped Cases I/II/III.
