# Phase 22f — N3b: point-join ↔ panel-meet duality assembly (KT §6.4.1, eq. (6.45)) (work log)

**Status:** in progress (opened 2026-06-07 design-pass-first; opening recon landed). Discharges
Phase 22e's single green-modulo-N3b obligation — the one red leaf
`lem:case-III-claim612-line-in-panel-union` (N3b, the point-join ↔ panel-meet duality assembly).
**Research-shaped / structural-edit:** no new blueprint chapter — the target node is stubbed red in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`; the assembly's three operational sub-leaves
(N3b-dict / step (i) / step (ii)) are already green in `Molecular/Meet.lean` (Phase 22e). 22f lands
the *assembly* on top of those green leaves: the bounded/concrete `⋀²ℝ⁴` exterior-algebra infra
(NOT general Hodge theory) placing both `p̄ᵢ ∨ p̄ⱼ` and `C(L)` in a common `⋀²W` and extracting the
scalar. KT math: `notes/Phase22e.md` *22f plan* + KT §6.4.1 (eq. (6.45)); 22f **formalizes** it.

## Current state

**Next concrete commit: N3b-2b-β, the 5-dim span count** `finrank (n_u ∧ ℝ⁴ + n' ∧ ℝ⁴) = 5`. The
N3b-2b-α *building block* landed this commit — `wedgeFixedLeft`/`coe_wedgeFixedLeft`/
`ker_wedgeFixedLeft`/`finrank_range_wedgeFixedLeft` in `Molecular/Meet.lean`: the
wedge-with-a-fixed-vector map `v ↦ a ∧ v : ℝ⁴ →ₗ ⋀²ℝ⁴`, with kernel the line `span{a}` (`a ∧ v = 0
⟺ a, v` dependent ⟺ `v ∈ span{a}`, via `extensor_ne_zero_iff_linearIndependent` +
`LinearIndependent.pair_iff'`) and so range `finrank = 4 − 1 = 3` (rank–nullity). This is the
`a ∧ ℝ⁴` summand of the shared-direction span. Smallest next sub-commit: **N3b-2b-β** — assemble two
such summands into `finrank (range (wedgeFixedLeft n_u) ⊔ range (wedgeFixedLeft n')) = 5` via
`Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`), with the intersection
`= span{n_u ∧ n'}` (`finrank = 1`) the genuine sub-content (the decomposable-intersection fact:
`a ∧ v = b ∧ w` with `{a, b}` independent forces the element into `span{a ∧ b}`).

**Route caveat found this commit — the membership *assembly* (old N3b-2b-α / N3b-3) needs its route
re-examined; the phase-open Route A-finrank as written does not close.** Re-reading green step (i)
(`complementIso_toDual_extensor_eq_zero_of_shared_vector`): its `b.toDual M (extensor c) = 0` is the
*wedge pairing* `vol(extensor n ∨ₑ extensor c)` (via `complementIso_toDual`, valid only because
`M = complementIso(extensor n)`), **not** the coordinate dot product `b.toDual` gives on a generic
pair. The phase-open `Φ = span{b.toDual(extensor c)}` route needs `Ψ = range (map 2 W.subtype) ≤
dualCoannihilator Φ`, i.e. every point-join `J = extensor ![w₀,w₁]` (with `w₀,w₁ ∈ W`) annihilated by
every shared-direction `extensor c`. Under **either** pairing this is false: `vol(J ∨ₑ extensor c) =
vol(![w₀,w₁,c₀,c₁])` is nonzero for generic `c` sharing one normal (e.g. `c = ![n_u, t]`, `t`
generic). So the shared-direction extensors are **not** a common annihilator of `J` and `M` — the
"both lie in `dualCoannihilator Φ`, count to 1-dim" framing has a real gap. The *mathematics*
(Hodge: `complementIso(n_u ∧ n') = λ·(w₀ ∧ w₁)` for `W = {n_u,n'}^⊥`) is true; what is wrong is the
specific `Φ`-via-shared-extensors finrank route. **The 5-dim span count N3b-2b-β is route-independent
and correct** (it is the honest dimension of `n_u ∧ ℝ⁴ + n' ∧ ℝ⁴`); the membership assembly above it
must be re-derived — likely directly identifying `complementIso(n_u ∧ n')` with the wedge of a basis
of `W` (the genuine Hodge-star content), or via a correct annihilator object. **Resolve the assembly
route before the node flip** (see *Blockers*).

The green leaves still reused once the assembly route is fixed:

1. **N3b-2b-line (landed):** `exists_smul_eq_of_mem_range_map_subtype` — for a 2-dim `W ⊆ ℝ⁴`,
   `range (map 2 W.subtype)` is 1-dim (`LinearMap.finrank_range_of_inj` on the injective N3b-1 map +
   `finrank_exteriorPower_two_eq_one`), so any two members with one nonzero are proportional. Realized
   in `⋀²ℝ⁴` directly, so once `complementIso(n_u ∧ n') ∈ range` lands it *is* the proportionality.
2. **The membership** `complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)` (the re-routed
   old N3b-2b-α): with step 1 this subsumes the old N3b-3 proportionality. Its honest derivation is
   the open assembly above; the 5-dim span count N3b-2b-β is the route-independent leaf below it.

N3b-3 then has no separate work beyond the final node flip on
`lem:case-III-claim612-line-in-panel-union` (retiring the green-modulo-N3b on N9 `case_III_claim612`
and the candidate-completion chain), once the membership lands.

**N3b-2a landed** (this commit, the point-join half): `extensor_mem_range_map_subtype_of_mem` in
`Molecular/Meet.lean` — for `v : Fin 2 → ℝ⁴` with each `v i ∈ W`, the grade-2 extensor `extensor v`
lies in `range (exteriorPower.map 2 W.subtype)`, via `exteriorPower.map_apply_ιMulti` +
`exteriorPower.ιMulti_apply_coe`. The `extensor`/`ιMulti` coercion bridge the Blockers flagged was a
single routine `Subtype.ext` + one coercion `rw` + `rfl` (under the one-bridge threshold, so no
FRICTION entry). This places the point-join `p̄ᵢ ∨ p̄ⱼ` in the line `⋀²W` at `W = span{p̄ᵢ, p̄ⱼ}`.
Pure Lean infra feeding N3b-3; no blueprint node flip (the target `lem:case-III-claim612-line-in-
panel-union` stays red until N3b-3, and range-membership plumbing is below the blueprint
include-bar). Build warning-clean, `lake lint` clean, `#print axioms` = the three standard axioms.

**N3b-1 landed** earlier: `exteriorPower_map_subtype_injective` in `Molecular/Meet.lean` — the
one-liner `exteriorPower.map_injective_field W.injective_subtype`, over a general
`W : Submodule ℝ (Fin 4 → ℝ)`. Blueprint node `lem:complement-iso-exterior-map-injective` green in
`chapter/meet.tex`.

**Nothing mid-stream.**

## Architectural choices made up front

- **Design-pass-first** (`DESIGN.md` *Scale-up: design the LAYER, not just the node*). N3b's assembly
  is research-shaped (it bottoms on regressive-duality-on-decomposables / Hodge-star content that was
  not in the project or mathlib at 22e's close). Opened on a real mathlib spike + the red-node
  consistency gate, not a build — exactly as 22c/22d/22e opened.
- **Concrete at `⋀²ℝ⁴`, not general Hodge theory** (carried from the 22e *22f plan*). The duality
  `p̄ᵢ ∨ p̄ⱼ = λ·C(L)` is needed only for a line `L ⊂ Π(u)` at `d = 3` (`N = 4`, `k = 2`,
  `ScrewSpace 2 = ⋀²ℝ⁴`). The infra is bounded — the exterior square of the *specific* 2-dim
  `W = {n_u, n'}^⊥` — so the assembly is a pull-back along one injective `exteriorPower.map`, not a
  general regressive-product / star-operator development.
- **The point-join-direct framing does NOT work** (confirmed at 22e). The candidate criterion is
  intrinsically a panel-meet `C(L) = complementIso(n_u ∧ n')`; the duality has to identify the
  *meet* extensor with the *join* extensor of the same line. That identification is exactly the
  assembly N3b-1/2/3 build.

## Design recon — verdict (2026-06-07, opening commit)

Spiked mathlib (lean-lsp MCP: `lean_loogle`, `lean_local_search`; NOT `lean_leansearch`) for the
N3b-1 injectivity lemma and sanity-checked that N3b-1/2/3 compose. **Verdict: all three are genuine
buildable leaves; N3b-1 is a one-liner, no retraction to design.**

- **N3b-1 (`exteriorPower.map 2 W.subtype` injective) — mathlib has the exact lemma.**
  `exteriorPower.map_injective_field {f : M →ₗ[K] N} (hf : Function.Injective f) :
  Function.Injective (exteriorPower.map n f)` (`Mathlib.LinearAlgebra.ExteriorPower.Basic`) gives
  injectivity over a **field** directly from injectivity of `f`. With `f = W.subtype` and
  `Submodule.injective_subtype W` (= `W.injective_subtype`), the leaf is
  `exteriorPower.map_injective_field W.injective_subtype`. Verified: both
  `exteriorPower.map_injective_field (Submodule.injective_subtype W)` and the dot-notation form
  type-check at the end of `Meet.lean` with **no goals** (only a cosmetic long-line warning).
  - *No retraction needed.* The 22e plan's fallback was "concrete retraction; spike mathlib first."
    The spike resolved it to the field lemma — the `CommRing`-level `exteriorPower.map_injective`
    (which *does* require an explicit retraction `g` with `g ∘ₗ f = id`) is available as a fallback
    but is unnecessary since the base ring is `ℝ`, a field. `Meet.lean` already imports
    `CombinatorialRigidity.Mathlib.LinearAlgebra.ExteriorPower.Basis`, which transitively pulls in
    `ExteriorPower.Basic` where `map_injective_field` lives — reachable as-is.
- **N3b-2 (both members land in `range (exteriorPower.map 2 W.subtype)`) — direct mathlib API.**
  `exteriorPower.map_apply_ιMulti_family` / `exteriorPower.map_apply_ιMulti` express
  `map n f` applied to an in-`W` wedge as the wedge of the `f`-images, and
  `exteriorPower.ιMulti_family_span` states
  `(map n (span R (range v)).subtype).range = span R (range (ιMulti_family R n v))`. The project's
  `extensor`/`join` are `ιMulti`-style products of the homogenized points; the incidence
  `⟨p̄ᵢ, n_u⟩ = ⟨p̄ᵢ, n'⟩ = 0` (both panels through the line) places each `p̄ᵢ ∈ W = {n_u, n'}^⊥`, so
  `p̄ᵢ ∨ p̄ⱼ` is (the image under `map 2 W.subtype` of) a wedge of two vectors-in-`W`, hence in range.
  `C(L) ∈ ⋀²W` is the *non-operational upgrade* of the green step (i)
  (`complementIso_toDual_extensor_eq_zero_of_shared_vector`): step (i) proved
  `complementIso(n_u ∧ n')` is annihilated by every 2-extensor sharing a normal (the operational dual
  reading of "lands in `⋀²W`"); N3b-2 turns that into an honest range membership.
- **N3b-3 (proportionality + annihilation transfer) — composes on the green step (ii).** Pull both
  members back along the injective `map 2 W.subtype` into `⋀²W`, apply the green step (ii)
  `exteriorPower_finrank_eq_one_proportional` (`dim ⋀²W = 1`, so two members of a line, one nonzero,
  are scalar multiples) to get the pull-backs proportional, push forward along `map` to get
  `p̄ᵢ ∨ p̄ⱼ = λ·C(L)` in `⋀²ℝ⁴`; then `r(C(L)) = 0 ⟹ r(p̄ᵢ ∨ p̄ⱼ) = λ·r(C(L)) = 0`. The
  proportionality leaf (step (ii)) is already green; N3b-3 is the transfer wiring + the final node
  flip on `lem:case-III-claim612-line-in-panel-union`.

**No new mirror anticipated** (the injectivity, range, and proportionality facts are all mathlib or
already green); the residual content is the pull-back/push-forward bookkeeping. Re-classify if the
range-membership step (N3b-2) needs a `change`/coercion bridge between the project's `extensor`
presentation and mathlib's `ιMulti_family` (a possible FRICTION candidate — flag at build).

## N3b-2b route — Route B rejected, Route A-finrank overturned at build (2026-06-07)

- **Route (B) — direct decomposability — REJECTED (stands).** "`complementIso (n_u ∧ n')` *is* a
  decomposable `w₁ ∧ w₂`, `w₁,w₂ ∈ W`, then apply N3b-2a." Mathlib has **no** Hodge-star /
  decomposable-dual API (`ExteriorPower/` is exactly `{Basic, Basis, Pairing}.lean`), so the
  decomposability is not cheap; and `complementIso` is `noncomputable` (`linearEquivOfInjective` ≪≫
  `toDualEquiv.symm`), so `decide` on a standard basis is a non-starter (verified). Its premise (cheap
  decomposability) is false in mathlib's current state.
- **Route (A) — `Φ`-via-shared-extensors finrank count — OVERTURNED at build.** The recon adopted it,
  but building N3b-2b surfaced that the `Ψ ≤ dualCoannihilator Φ` step is *false*: the shared-direction
  extensors are not a common annihilator of the point-join and the panel-meet (green step (i)'s
  vanishing is the wedge pairing `vol(extensor n ∨ₑ ·)`, valid only for the panel-meet, not the
  coordinate dot product `b.toDual` gives generically — and `vol(J ∨ₑ extensor c) ≠ 0` for generic
  shared-direction `c`). Full arc in *Blockers* / *Current state*. The recon's *true* residue: the two
  grade-2 summands `n_u ∧ ℝ⁴`, `n' ∧ ℝ⁴` are each 3-dim (the landed building block), and their span is
  the genuinely-new 5-dim content (N3b-2b-β) — that span count is route-independent and correct; what
  the gap kills is only the *membership assembly via `Φ`*, which must be re-derived (likely the direct
  Hodge-star identification, *Blockers* candidate (a)). The decomposable-intersection / Hodge-star
  content is genuinely-new (no mathlib API), consistent with the blueprint's framing.

## Red-node consistency gate — recon verdict (2026-06-07, opening commit)

Read the N3b target node `lem:case-III-claim612-line-in-panel-union`
(`algebraic-induction/case-iii.tex`) end-to-end (statement + proof) and ran the supersession gate
over `algebraic-induction/*.tex` + the chapters. **Consistent; gate clean.**

- **Statement** claims exactly what N3b-1/2/3 build: `p̄ᵢ ∨ p̄ⱼ` and `C(L) = complementIso(n_u ∧ n')`
  are scalar multiples in `⋀²ℝ⁴` (both the Plücker vector of the same line `L`), so an `r`
  annihilating every panel-meet `C(L)` annihilates each spanning join `p̄ᵢ ∨ p̄ⱼ`.
- **Proof** routes through the same argument: the green dictionary entry
  `lem:complement-iso-toDual` → step (i) `lem:complement-iso-decomposable-wedge-perp` (places
  `complementIso(n_u ∧ n')` in `⋀²W`) → step (ii) `lem:complement-iso-line-one-dim` (`⋀²W` is a line)
  → the **assembly** (the one explicitly-named remaining step: "placing both … in `⋀²W` … and
  applying step (ii) … the regressive-duality-on-decomposables content … not yet in the project") →
  annihilation transfer. The proof's "one remaining step" is precisely the assembly 22f builds; no
  step routes through a dead-end.
- **`\uses` (statement):** `def:join, def:meet, def:meet-complement-iso, def:panel-support-extensor,
  lem:extensor-independence, lem:case-III-claim612-extensor-span, lem:complement-iso-toDual,
  lem:complement-iso-decomposable-wedge-perp, lem:complement-iso-line-one-dim` — all green
  (Phase 17 / 21a / 22e) or green operational leaves; **none superseded**.
- **Supersession gate:** superseded labels = {`-disjoint-line-meet`, `-e0-recovery`,
  `-motion-side-assembly`, `-pin-vertex`}; `comm -12` against the live-`\uses` set = ∅. The N3b node's
  `\uses` touches none of them.

**Verdict: the build is safe to scope.** N3b's statement routes through the same argument it claims;
its `\uses` reach only green/operational nodes; the assembly is the genuine remaining content (the
green sub-leaves are real inputs, no smuggled hypothesis, no dead-end on the live route).

## Lemma checklist

The three green operational sub-leaves N3b builds on (Phase 22e, in `Molecular/Meet.lean`):
`complementIso_toDual` (N3b-dict), `complementIso_toDual_extensor_eq_zero_of_shared_vector` (step (i)),
`finrank_exteriorPower_two_eq_one` + `exteriorPower_finrank_eq_one_proportional` (step (ii)). The 22f
build:

- [x] **N3b-1** — `exteriorPower_map_subtype_injective` in `Molecular/Meet.lean`: `exteriorPower.map
  2 W.subtype` injective for `W : Submodule ℝ (Fin 4 → ℝ)` (the general `⋀²ℝ⁴` shape, so N3b-2/3
  instantiate at `W = {n_u, n'}^⊥`). One-liner `exteriorPower.map_injective_field W.injective_subtype`
  as recon-predicted; no retraction. Blueprint `lem:complement-iso-exterior-map-injective` (green).
- [x] **N3b-2a** (point-join half) — `extensor_mem_range_map_subtype_of_mem`: for `v : Fin 2 → ℝ⁴`
  with each `v i ∈ W`, `extensor v ∈ range (exteriorPower.map 2 W.subtype)`. Direct mathlib API
  (`map_apply_ιMulti`, `ιMulti_apply_coe`); one routine `Subtype.ext` coercion bridge. Places the
  point-join `p̄ᵢ ∨ p̄ⱼ` in `⋀²W`. Pure Lean infra (no blueprint node — below the include-bar).
- [x] **N3b-2b-line** (landed) — `exists_smul_eq_of_mem_range_map_subtype`: for a 2-dim `W ⊆ ℝ⁴`,
  any two members of `range (map 2 W.subtype)` with one nonzero are proportional (`∃ c, c • x = y`).
  `range` is 1-dim (`LinearMap.finrank_range_of_inj` ∘ N3b-1 + `finrank_exteriorPower_two_eq_one`),
  so `span{x} = range` (`Submodule.eq_of_le_of_finrank_eq`) and `mem_span_singleton` closes.
  Stated as the proportionality producer **in `⋀²ℝ⁴`** (not the literal `= span{x}` form, nor a
  pull-back to `⋀²W`), so it makes the point-join and panel-meet proportional in place — N3b-3's
  push-forward wiring is gone. Pure Lean infra (no blueprint node — below the include-bar).
- [x] **N3b-2b-α building block** (landed) — `wedgeFixedLeft`/`coe_wedgeFixedLeft`/
  `ker_wedgeFixedLeft`/`finrank_range_wedgeFixedLeft` in `Molecular/Meet.lean`: the
  wedge-with-a-fixed-vector map `v ↦ a ∧ v : ℝ⁴ →ₗ ⋀²ℝ⁴` (`(mulLeft (ι a)).comp ι` corestricted to
  `⋀²`), kernel `= span{a}` for `a ≠ 0`, hence range `finrank = 3` (rank–nullity). The `a ∧ ℝ⁴`
  summand of the shared-direction span. Pure Lean infra (no blueprint node — below the include-bar).
  Build warning-clean, `lake lint` clean, `#print axioms` = the three standard axioms.
- [ ] **N3b-2b-β** (next) — the 5-dim span count `finrank (range (wedgeFixedLeft n_u) ⊔
  range (wedgeFixedLeft n')) = 5` via `Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`); the
  genuine sub-content is `intersection = span{n_u ∧ n'}` (`finrank = 1`), the decomposable-intersection
  fact. Route-independent and correct regardless of how the membership assembly is finally derived.
- [ ] **The membership** `complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)` (re-routed) — the old
  N3b-2b-α / N3b-3. **Route OPEN** (Current state / Blockers): the phase-open `Φ`-via-shared-extensors
  finrank route does not close (the shared-direction extensors are not a common annihilator of the
  point-join and the panel-meet). Re-derive — likely the direct Hodge-star identification
  `complementIso(n_u ∧ n') = λ·(w₀ ∧ w₁)` for a basis `w₀,w₁` of `W`. With N3b-2b-line this membership
  *is* the proportionality, so it still **subsumes N3b-3**.
- [ ] **N3b-3** (collapsed) — no separate proportionality work (it falls out of the membership); only
  the annihilation transfer `r(C(L)) = 0 ⟹ r(p̄ᵢ ∨ p̄ⱼ) = 0` (one `smul`-linearity step) + the final
  node flip on `lem:case-III-claim612-line-in-panel-union`, retiring the green-modulo-N3b on N9
  (`case_III_claim612`) and the candidate-completion chain.

## Blockers / open questions

- **The membership assembly route is OPEN — phase-open Route A-finrank does not close** (found this
  commit; full arc in *Current state*). The plan put the point-join `J` and the panel-meet
  `M = complementIso(n_u ∧ n')` in a common 1-dim `dualCoannihilator Φ`, `Φ = span` of the
  `b.toDual`-images of the shared-direction extensors. **But the shared-direction extensors are not a
  common annihilator of `J` and `M`:** green step (i)'s vanishing is `vol(extensor n ∨ₑ extensor c)`
  (a wedge pairing, valid only for `M`), and `vol(J ∨ₑ extensor c) = vol(![w₀,w₁,c₀,c₁])` is nonzero
  for generic `c` sharing one normal — so `Ψ = range (map 2 W.subtype) ≤ dualCoannihilator Φ` is
  false. The Hodge fact `complementIso(n_u ∧ n') = λ·(w₀ ∧ w₁)` (`W = {n_u,n'}^⊥`) is *true*; the
  finrank-via-`Φ` *route to it* is wrong. **First task next: settle the correct assembly route** —
  candidates: (a) directly identify `complementIso(n_u ∧ n')` with `w₀ ∧ w₁` up to scalar via the
  wedge-pairing characterization `complementIso_toDual` (show both have the same `wedgePairing`-pairing
  against a basis of `⋀²W`, then `eq_of_le_of_finrank_eq`); (b) build a correct annihilator object
  (the *wedge*-perp of `W`'s extensor line, using the green step (i) reading consistently for both).
- **N3b-2b-β span count — the one route-independent open math leaf.** `finrank (n_u ∧ ℝ⁴ + n' ∧ ℝ⁴)
  = 5` (= the next concrete commit). Above the landed building block (`finrank_range_wedgeFixedLeft`,
  each summand 3-dim) via `Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`); the genuine
  sub-content is the intersection `range (wedgeFixedLeft n_u) ⊓ range (wedgeFixedLeft n') =
  span{n_u ∧ n'}` (`finrank = 1`) — the decomposable-intersection fact `a ∧ v = b ∧ w`, `{a,b}`
  independent ⟹ element ∈ `span{a ∧ b}`. No decomposable / Hodge-star API in mathlib to lean on; this
  is genuinely-new content. (Whether N3b-2b-β actually feeds the *final* membership depends on the
  assembly route settled above — but the span count is correct and reusable either way.)
- **N3b-2a coercion bridge — resolved, one routine step (not FRICTION).** The project's
  `extensor`/`join` live in `ExteriorAlgebra ℝ (Fin 4 → ℝ)` (graded into `⋀[ℝ]^2` via
  `extensor_mem_exteriorPower`), while mathlib's range API is phrased via `ιMulti`. The point-join
  half bridged the two with a single `Subtype.ext` + `rw [exteriorPower.ιMulti_apply_coe]` + `rfl` —
  under the one-bridge threshold, so no FRICTION entry. The panel-meet half (N3b-2b) is not a
  coercion question; it is the finrank-count argument (Current state).
- **The `ofNormals` defeq-timeout trap does NOT bite 22f** (carry from 22a–e, FRICTION). 22f is pure
  exterior-algebra / `Module.Dual` content with no graph-swap; the trap bites the *deferred `d=3`
  assembly* (the consumer that extracts `rn`/`ro` and wires real graph data), not N3b.

## Hand-off / next phase

**Next concrete commit: N3b-2b-β, the 5-dim span count** `finrank (range (wedgeFixedLeft n_u) ⊔
range (wedgeFixedLeft n')) = 5` (Blockers / Lemma checklist). The building block landed this commit
(`wedgeFixedLeft` + kernel + `finrank_range_wedgeFixedLeft` = 3 per summand); N3b-2b-β assembles two
summands via `Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`), the genuine sub-content being
the decomposable-intersection `range ⊓ range = span{n_u ∧ n'}` (`finrank = 1`). It is route-
independent and correct.

**But before flipping the node, settle the membership assembly route** — the phase-open Route
A-finrank *does not close* (found this commit; the shared-direction extensors are not a common
annihilator of the point-join and the panel-meet — *Blockers* / *Current state*). The Hodge fact is
true; re-derive the membership `complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)` correctly
(candidate (a): identify it with `w₀ ∧ w₁` up to scalar via the `complementIso_toDual` wedge-pairing
characterization against a basis of `⋀²W`). With N3b-2b-line that membership *is* the proportionality
`complementIso (n_u ∧ n') = λ·(p̄ᵢ ∨ p̄ⱼ)`, *subsuming* N3b-3. Then **N3b-3** is the `smul`-transfer +
the per-line duality lemma (N3b-2a placing the point-join, the membership placing the panel-meet,
N3b-2b-line making them proportional) + the node flip on `lem:case-III-claim612-line-in-panel-union`;
run `blueprint/verify.sh` on that flip. Route (B) — direct decomposability — stays rejected (no
Hodge/decomposable API in mathlib; `complementIso` noncomputable → no `decide`).

**After 22f closes** (N3b green → N9 + the candidate-completion chain fully green): the next
deferred-**unlettered** cut is the **`d=3` realization assembly** — `prop:rigidity-matrix-prop11` `hub`
partition brick (Track-independent, Phase-19-partition) + the `thm:theorem-55` flip + wiring the
fully-green `case_I_realization` into `theorem_55_generic`'s Case-I branch — which is what finally takes
the two producer nodes `lem:case-II-realization` / `lem:case-III` themselves green (and where the
`ofNormals` defeq-timeout trap bites). Then **general-`d`** (Lemma 6.13) is **Phase 23**. KT math:
`notes/Phase22e.md` *22f plan* / *Hand-off*, `notes/Phase22d.md` *Hand-off*, KT §6.4.1 (eq. (6.45));
`notes/AlgebraicIndependence.md` (N3b stays alg-independence-free, pure Grassmann–Cayley).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **N3b-2b building block: the wedge-with-fixed-vector map (2026-06-07).** Landed `wedgeFixedLeft`
  (`v ↦ a ∧ v : ℝ⁴ →ₗ ⋀²ℝ⁴`, as `(mulLeft (ι a)).comp ι` corestricted to `⋀²`) with kernel
  `= span{a}` for `a ≠ 0` (`extensor_ne_zero_iff_linearIndependent` + `LinearIndependent.pair_iff'`)
  and range `finrank = 3` (rank–nullity). The `a ∧ ℝ⁴` summand of the shared-direction span; feeds the
  route-independent 5-dim span count N3b-2b-β.
- **N3b-2b route overturn: Route A-finrank does NOT close (2026-06-07, found at build — *N3b-2b route*
  / *Blockers*).** Route (B) direct decomposability stays *rejected* (no Hodge API; `complementIso`
  noncomputable → no `decide`). Route (A) `Φ`-via-shared-extensors finrank count was *adopted at recon*
  but is *overturned*: its `Ψ = range (map 2 W.subtype) ≤ dualCoannihilator Φ` step is false — the
  shared-direction extensors are not a common annihilator of the point-join and panel-meet (green
  step (i)'s vanishing is the wedge pairing, valid only for the panel-meet). The Hodge fact
  `complementIso(n_u ∧ n') = λ·(w₀ ∧ w₁)` is true; the membership *assembly* must be re-derived. The
  recon's true residue (the two 3-dim summands → a 5-dim span) is route-independent and stands.
- **N3b-2b + N3b-3 collapse via the line identity (2026-06-07).** N3b-2b-line landed as the
  proportionality producer `exists_smul_eq_of_mem_range_map_subtype` (two members of the 1-dim
  `range (map 2 W.subtype)`, one nonzero, are proportional) **in `⋀²ℝ⁴` directly** — not the literal
  `range = span{x}` form, and not pulled back to `⋀²W`. So once the membership
  `complementIso (n_u ∧ n') ∈ range` lands (the re-routed old N3b-2b-α), it *is* the proportionality
  N3b-3 was scoped to extract — the phase-open "pull-back to `⋀²W` / step (ii) / push-forward" wiring
  is unnecessary; N3b-3 shrinks to the `smul`-transfer + per-line duality assembly + node flip.
- **N3b-2 split into a point-join half (2a) and a panel-meet half (2b) (2026-06-07).** The 22f open
  scoped N3b-2 as one commit putting *both* `p̄ᵢ ∨ p̄ⱼ` and `C(L)` in `range (map 2 W.subtype)`.
  Building it surfaced an asymmetry: the point-join (2a, `extensor_mem_range_map_subtype_of_mem`) is
  a direct `map_apply_ιMulti` image (the recon-anticipated mathlib API + one coercion `Subtype.ext`),
  but the panel-meet (2b) is *not* a direct image — step (i) gives only the dual reading (annihilated
  by sharing-direction extensors), and the honest range membership is the finrank-count argument
  above. That is genuinely heavier, so 2b is its own leaf. 2a is pure Lean infra below the blueprint
  include-bar (no node).
- **N3b-1 resolved to a mathlib one-liner at open — no retraction (2026-06-07, design recon).** The
  22e plan flagged N3b-1 as "concrete retraction; spike mathlib first." The spike found
  `exteriorPower.map_injective_field` (injectivity of `⋀ⁿ f` from injectivity of `f`, over a field),
  so over `ℝ` the leaf is just `exteriorPower.map_injective_field W.injective_subtype`
  (`Submodule.injective_subtype` supplies the hypothesis). Verified via `lean_multi_attempt` (no
  goals). The `CommRing`-level `exteriorPower.map_injective` (needs an explicit retraction) is the
  fallback, unneeded here. N3b-2/3 then compose on direct mathlib range API + the green step (ii).
