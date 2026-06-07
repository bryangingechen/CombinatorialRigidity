# Phase 22f — N3b: point-join ↔ panel-meet duality assembly (KT §6.4.1, eq. (6.45)) (work log)

**Status:** in progress (opened 2026-06-07 design-pass-first; membership route settled — route
A-corrected, the coordinate-pairing dualCoannihilator; pivot infra N3b-recon landed; node still
red). Discharges
Phase 22e's single green-modulo-N3b obligation — the one red leaf
`lem:case-III-claim612-line-in-panel-union` (N3b, the point-join ↔ panel-meet duality assembly).
**Research-shaped / structural-edit:** no new blueprint chapter — the target node is stubbed red in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`; the assembly's three operational sub-leaves
(N3b-dict / step (i) / step (ii)) are already green in `Molecular/Meet.lean` (Phase 22e). 22f lands
the *assembly* on top of those green leaves: the bounded/concrete `⋀²ℝ⁴` exterior-algebra infra
(NOT general Hodge theory) placing both `p̄ᵢ ∨ p̄ⱼ` and `C(L)` in a common `⋀²W` and extracting the
scalar. KT math: `notes/Phase22e.md` *22f plan* + KT §6.4.1 (eq. (6.45)); 22f **formalizes** it.

## Current state

**N3b-recon LANDED this commit** — `exteriorPower_basis_toDual_eq_pairingDual_comp_map` in
`Molecular/Meet.lean`: `(b.exteriorPower n).toDual = pairingDual ℝ (Fin 4 → ℝ) n ∘ₗ map n b.toDual`
for `b = Pi.basisFun ℝ (Fin 4)` (stated for general `n`, used at `n = 2`). The single new infra that
turns the opaque coordinate pairing `b.toDual` into a computable Gram determinant. Proof: double
`Module.Basis.ext` → `Module.Basis.toDual_apply` (LHS Kronecker) and `map_apply_ιMulti_family` +
`pairingDual_ιMulti_ιMulti` (RHS det) → the det-of-Kronecker `det (i j ↦ if σ_s j = σ_t i then 1
else 0) = if s = t then 1 else 0`, closed by `Matrix.det_one` (diagonal, `σ_s` injective) /
`Matrix.det_eq_zero_of_row_eq_zero` (off-diagonal: equal card forces `x ∈ t \ s`, a zero row). **No
`Mathlib/` mirror needed** — the fiddly det closer fell out of `det_one` + `det_eq_zero_of_row_eq_zero`
on the standard `ofFinEmbEquiv.symm` order-embedding indices, as the recon predicted.

**Next concrete commit: N3b-2b-β + the point-join Gram-det orthogonality** (facts 3 + 2 of route
A-corrected) — both now ride on the landed N3b-recon. The membership route is otherwise SETTLED:
route A-corrected (coordinate-pairing dualCoannihilator). The corrected leaf sequence is in *Hand-off*.

**The settled route (a, corrected — coordinate-pairing dualCoannihilator).** The membership
`complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)` for `W = {n_u, n'}^⊥` is proved by placing both
`complementIso(n_u ∧ n')` and a nonzero `range`-member (e.g. the point-join `w₀ ∧ w₁`, `w_i ∈ W`) in
a common **1-dim** space and invoking N3b-2b-line. The common space is
`Ω := {Z : ⋀²ℝ⁴ | ∀ c sharing a normal, (b.exteriorPower 2).toDual Z (extensor c) = 0}` — the
`b.toDual`-orthogonal complement of the 5-dim shared-direction span `Φ̃ = n_u ∧ ℝ⁴ + n' ∧ ℝ⁴`. Three
load-bearing facts; the pivot infra they all ride on (the reconciliation N3b-recon) is now **landed**:

1. `complementIso(n_u ∧ n') ∈ Ω` — this is **green step (i)**
   (`complementIso_toDual_extensor_eq_zero_of_shared_vector`), verbatim.
2. `w₀ ∧ w₁ ∈ Ω` for `w_i ∈ W` (the genuinely-new fact, the next commit) — via the **Gram
   determinant**: N3b-recon rewrites `b.toDual (w₀ ∧ w₁) (extensor ![n_u, t]) = det [[w₀·n_u, w₀·t],
   [w₁·n_u, w₁·t]]`, and `w_i·n_u = 0` (the incidence `w_i ∈ W = {n_u,n'}^⊥`) makes a **column of
   zeros**, so the det is `0`. This is the `range ≤ Ω` inclusion the *prior* recon got wrong (it
   checked the count `5+1=6` while asserting a false annihilation under the *volume* pairing) — the
   exact failure mode the prompt warns of, resolved the right way: `b.toDual` is the *coordinate*
   pairing, a Gram det, not the volume form.
3. `dim Ω = 1` — `b.toDual` is a perfect pairing (`Basis.toDual` is an iso in finite dim), so
   `dim Ω = 6 − dim Φ̃ = 6 − 5 = 1`. **This is exactly N3b-2b-β** (`dim Φ̃ = 5`): the landed building
   block is reused, NOT orphaned.

The membership, once landed, **subsumes N3b-3** (it *is* the proportionality, via N3b-2b-line).

**N3b-2a landed** earlier (the point-join half): `extensor_mem_range_map_subtype_of_mem` in
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

## Membership route — settled verdict (2026-06-07 design-pass)

**Route A-corrected (coordinate-pairing dualCoannihilator) is the one that closes.** The full route
(and the landed pivot infra N3b-recon) is in *Current state*; the leaf sequence is in *Hand-off*. The
two earlier candidates are closed:

- **Route (B) — direct decomposability — REJECTED.** "`complementIso (n_u ∧ n')` *is* a decomposable
  `w₁ ∧ w₂`, then apply N3b-2a." Mathlib has **no** Hodge-star / decomposable-dual API
  (`ExteriorPower/` is exactly `{Basic, Basis, Pairing}.lean`), and `complementIso` is `noncomputable`,
  so `decide` is a non-starter. Premise (cheap decomposability) false in mathlib's current state.
- **Route A IS route A-corrected** — there is no separate dead "Route A". The pivot is reading the
  pairing in `Ω := dualCoannihilator Φ̃` as the **coordinate inner product** `b.toDual`, which expands
  (via the reconciliation `b.toDual = pairingDual ∘ map toDual`) as a **Gram determinant of dot
  products**, killing the point-join by a column of zeros. The prior commit's "Route A overturned"
  call was a *mis-diagnosis* (it tested `vol(J ∨ₑ c)`, the volume/wedge pairing, where route A actually
  uses `b.toDual`, the coordinate pairing — two different bilinear forms; see *Decisions*).

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
- [x] **N3b-recon** (landed) — `exteriorPower_basis_toDual_eq_pairingDual_comp_map` in
  `Molecular/Meet.lean`: `(b.exteriorPower n).toDual = pairingDual ℝ (Fin 4 → ℝ) n ∘ₗ map n b.toDual`
  for `b = Pi.basisFun ℝ (Fin 4)`, general `n`. Double `Module.Basis.ext` →
  `Module.Basis.toDual_apply` (LHS Kronecker) + `map_apply_ιMulti_family` + `pairingDual_ιMulti_ιMulti`
  (RHS det) → det-of-Kronecker `det (i j ↦ if σ_s j = σ_t i then 1 else 0) = if s = t then 1 else 0`,
  closed by `Matrix.det_one` / `Matrix.det_eq_zero_of_row_eq_zero` (no `Mathlib/` mirror needed). The
  single new infra unlocking the membership; feeds facts 2 + 3 of route A-corrected (*Current state*).
  Build warning-clean, `lake lint` clean, `#print axioms` = the three standard axioms.
- [ ] **N3b-2b-β** (**next concrete commit**, with fact 2) — the 5-dim span count `finrank (range (wedgeFixedLeft n_u) ⊔
  range (wedgeFixedLeft n')) = 5` via `Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`); the
  genuine sub-content is `intersection = span{n_u ∧ n'}` (`finrank = 1`), the decomposable-intersection
  fact. **Confirmed needed by route A-corrected** (it is fact 3, `dim Ω = 6 − dim Φ̃ = 1`); NOT
  orphaned. The intersection step itself rides on N3b-recon (Gram-det).
- [ ] **The membership** `complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)` — the old N3b-2b-α /
  N3b-3. **Route SETTLED: A-corrected** (*Current state*): place both `complementIso(n_u ∧ n')`
  (green step (i)) and the point-join `w₀ ∧ w₁` (N3b-recon Gram-det column-of-zeros) in the 1-dim
  `Ω = dualCoannihilator Φ̃`, then N3b-2b-line. With N3b-2b-line this membership *is* the
  proportionality, so it still **subsumes N3b-3**.
- [ ] **N3b-3** (collapsed) — no separate proportionality work (it falls out of the membership); only
  the annihilation transfer `r(C(L)) = 0 ⟹ r(p̄ᵢ ∨ p̄ⱼ) = 0` (one `smul`-linearity step) + the final
  node flip on `lem:case-III-claim612-line-in-panel-union`, retiring the green-modulo-N3b on N9
  (`case_III_claim612`) and the candidate-completion chain.

## Blockers / open questions

- **Membership route SETTLED (route A-corrected; *Current state*).** No longer open. N3b-recon
  **landed this commit** (the det-of-Kronecker closer fell out of `Matrix.det_one` /
  `Matrix.det_eq_zero_of_row_eq_zero` — no `Mathlib/` mirror, no FRICTION entry). The residual build
  is: N3b-2b-β (fact 3, `dim Φ̃ = 5`) + the point-join Gram-det orthogonality (fact 2), then the
  dualCoannihilator assembly + N3b-2b-line.
- **N3b-2b-β still needed (not orphaned), next commit.** `finrank (n_u ∧ ℝ⁴ + n' ∧ ℝ⁴) = 5` is fact 3
  of route A-corrected. Above the landed building block (`finrank_range_wedgeFixedLeft`, each summand
  3-dim) via `Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`); the genuine sub-content is the
  intersection `range (wedgeFixedLeft n_u) ⊓ range (wedgeFixedLeft n') = span{n_u ∧ n'}`
  (`finrank = 1`) — the decomposable-intersection fact `a ∧ v = b ∧ w`, `{a,b}` independent ⟹ element
  ∈ `span{a ∧ b}`. That intersection step rides on the now-landed N3b-recon Gram-det.
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

**N3b-recon landed this commit** (`exteriorPower_basis_toDual_eq_pairingDual_comp_map`), the single
new infra. The remaining leaf sequence to the node flip on `lem:case-III-claim612-line-in-panel-union`:

1. **N3b-2b-β + point-join Gram-det orthogonality (next concrete commit):** N3b-2b-β is `dim Φ̃ = 5`
   (fact 3, via `Submodule.finrank_sup_add_finrank_inf_eq` `3 + 3 − 1` on the landed
   `finrank_range_wedgeFixedLeft`, sub-content `intersection = span{n_u ∧ n'}`); the point-join
   orthogonality is `b.toDual (w₀ ∧ w₁) (extensor c) = 0` for `w_i ∈ W`, shared `c` (fact 2,
   column-of-zeros determinant). Both ride on the now-landed N3b-recon Gram-det.
2. **The membership** `complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)`: place both
   `complementIso(n_u ∧ n')` (green step (i), fact 1) and the point-join `w₀ ∧ w₁` (fact 2) in the
   1-dim `Ω = dualCoannihilator Φ̃` (fact 3 gives `dim Ω = 1`), then N3b-2b-line makes them
   proportional. This membership *is* the proportionality `complementIso (n_u ∧ n') = λ·(p̄ᵢ ∨ p̄ⱼ)`,
   *subsuming* N3b-3.
3. **N3b-3 / node flip:** the `smul`-transfer `r(C(L)) = 0 ⟹ r(p̄ᵢ ∨ p̄ⱼ) = 0` + the per-line duality
   lemma (N3b-2a placing the join, the membership placing the meet, N3b-2b-line proportional) + flip
   `lem:case-III-claim612-line-in-panel-union` green (retiring green-modulo-N3b on N9 + the
   candidate-completion chain). Run `blueprint/verify.sh` on that flip.

Route (B) — direct decomposability — stays rejected (no Hodge/decomposable API in mathlib;
`complementIso` noncomputable → no `decide`).

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
- **N3b-recon: the coordinate `toDual` of `⋀ⁿℝ⁴` is the Gram-det pairing (2026-06-07).** Landed
  `exteriorPower_basis_toDual_eq_pairingDual_comp_map`: `(b.exteriorPower n).toDual = pairingDual ∘ₗ
  map n b.toDual`. Double `Module.Basis.ext` reduces it to `det (i j ↦ if σ_s j = σ_t i then 1 else
  0) = if s = t then 1 else 0`, where `σ_s = ofFinEmbEquiv.symm s` is the order-embedding indexing
  basis subset `s`. The det closed cleanly: `Matrix.det_one` (diagonal — `σ_s` injective makes the
  matrix the identity) / `Matrix.det_eq_zero_of_row_eq_zero` (off-diagonal — `card s = card t` forces
  `x ∈ t \ s`, whose row vanishes). The recon's "fiddly det closer" worry (FRICTION/mirror candidate)
  did **not** materialize — no `Mathlib/` mirror, no FRICTION entry.
- **N3b-2b building block: the wedge-with-fixed-vector map (2026-06-07).** Landed `wedgeFixedLeft`
  (`v ↦ a ∧ v : ℝ⁴ →ₗ ⋀²ℝ⁴`, as `(mulLeft (ι a)).comp ι` corestricted to `⋀²`) with kernel
  `= span{a}` for `a ≠ 0` (`extensor_ne_zero_iff_linearIndependent` + `LinearIndependent.pair_iff'`)
  and range `finrank = 3` (rank–nullity). The `a ∧ ℝ⁴` summand of the shared-direction span; feeds the
  route-independent 5-dim span count N3b-2b-β.
- **Membership route SETTLED: route A-corrected (coordinate-pairing dualCoannihilator) (2026-06-07
  design-pass — *Current state*, *Membership route — settled verdict*).** Both members
  (`complementIso(n_u ∧ n')` by green step (i); the point-join `w₀ ∧ w₁` by a Gram-det column-of-zeros)
  lie in the 1-dim `Ω = dualCoannihilator Φ̃` (`Φ̃ = n_u ∧ ℝ⁴ + n' ∧ ℝ⁴`, `dim = 5`, the landed building
  block), so N3b-2b-line makes them proportional. The pivot infra is the reconciliation
  `b.toDual = pairingDual ∘ map toDual` (N3b-recon, landed), turning `b.toDual` into a Gram
  determinant (`pairingDual_ιMulti_ιMulti`). Route (B) direct decomposability stays *rejected* (no
  Hodge API; `complementIso` noncomputable → no `decide`).
- **The prior commit's "Route A overturned" was a mis-diagnosis — pairing confusion (2026-06-07).**
  It declared `Ψ ≤ dualCoannihilator Φ` false by exhibiting `vol(J ∨ₑ extensor c) ≠ 0` for generic
  shared `c`. But that tests the **volume/wedge** pairing `vol(· ∧ ·)`; route A's `Ω` uses the
  **coordinate inner product** `b.toDual` (the `Module.Basis.exteriorPower` `toDual`, a Kronecker
  pairing, NOT a volume). Under `b.toDual` the point-join *is* annihilated — Gram det
  `det [[w₀·n_u, w₀·t],[w₁·n_u, w₁·t]] = 0` (the `w_i ∈ {n_u,n'}^⊥` rows zero a column). Step (i)
  reads as a `vol` only because its first arg is a `complementIso` image (`complementIso_toDual`); for
  a raw decomposable, `b.toDual` stays the coordinate pairing. **Lesson:** `b.exteriorPower.toDual` and
  the wedge/`vol` pairing are *different bilinear forms* on `⋀²ℝ⁴` — they coincide only through
  `complementIso`; never substitute one counterexample for the other.
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
