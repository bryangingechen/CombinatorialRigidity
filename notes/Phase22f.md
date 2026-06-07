# Phase 22f — N3b: point-join ↔ panel-meet duality assembly (KT §6.4.1, eq. (6.45)) (work log)

**Status:** ✓ Complete (closed 2026-06-07). The target red leaf
`lem:case-III-claim612-line-in-panel-union` (N3b, the point-join ↔ panel-meet duality assembly) is
green, discharging Phase 22e's single green-modulo-N3b obligation. **Research-shaped /
structural-edit:** no new blueprint chapter — the target node was stubbed red in
`blueprint/src/chapter/algebraic-induction/case-iii.tex`; 22f landed the *assembly* on top of the
three green operational sub-leaves (N3b-dict / step (i) / step (ii), Phase 22e) using the
bounded/concrete `⋀²ℝ⁴` exterior-algebra infra (NOT general Hodge theory). KT math:
`notes/Phase22e.md` *22f plan* + KT §6.4.1 (eq. (6.45)).

## Current state

**Phase complete.** The membership/duality capstone landed this commit (`Molecular/Meet.lean`),
flipping `lem:case-III-claim612-line-in-panel-union` green and retiring the green-modulo-N3b
language on the N9 / candidate-completion nodes.

The capstone is two theorems (route A-corrected, coordinate-pairing annihilator):
- `complementIso_smul_eq_extensor_join` — the **proportionality**: `∃ c, c • complementIso(n_u ∧ n')
  = extensor ![pi, pj]` for `{n_u, n'}` independent and `pi, pj` `toDual`-orthogonal to both
  normals. Both members lie in the **1-dim** `Ω = (dualAnnihilator Φ̃).comap b.toDualEquiv` (the
  perfect-pairing transport of the annihilator of the 5-dim `Φ̃ = n_u ∧ ℝ⁴ + n' ∧ ℝ⁴`); the
  point-join by fact 2 (Gram-det orthogonality, each `n_u ∧ v` / `n' ∧ v` summand), the panel-meet
  by green step (i) (the `n'` summand via the appended-family shared `n'` and the general dictionary
  half), the panel-meet nonzero by `{n_u, n'}` independent. Two members of a line, one nonzero, are
  proportional (`Submodule.eq_of_le_of_finrank_eq` + `mem_span_singleton`, the
  `exists_smul_eq_of_mem_range_map_subtype` pattern reused on `Ω`).
- `extensor_join_eq_zero_of_complementIso_eq_zero` — the **annihilation transfer**: `r(C(L)) = 0 ⟹
  r(p̄ᵢ ∨ p̄ⱼ) = 0`, the node's headline. One `map_smul` off the proportionality.

`dim Ω = 1` is `6 − 5` via `Subspace.finrank_add_finrank_dualAnnihilator_eq` (fact 3,
`finrank_sup_range_wedgeFixedLeft`, supplied `dim Φ̃ = 5`) and the perfect pairing
`Submodule.comap_equiv_eq_map_symm` + `LinearEquiv.finrank_map_eq`. Build warning-clean, `lake lint`
clean, `#print axioms` = the three standard axioms.

**The `range (map 2 W.subtype)` route was not needed.** The phase-open plan placed both members in
`range (map 2 W.subtype)` (1-dim) via N3b-2a + N3b-2b-line; the landed proof routes the
proportionality directly through `Ω` (the dual-annihilator line), which is cleaner — `Ω` is where
both green step (i) and fact 2 already deposit their members. N3b-1 / N3b-2a / N3b-2b-line / the
N3b-recon Gram-det reconciliation / facts 2 & 3 all remain landed, green Lean infra in `Meet.lean`
(N3b-1 keeps its blueprint node `lem:complement-iso-exterior-map-injective`); fact 2 and the recon
are the load-bearing inputs the final proof actually uses.

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
- [x] **Fact 2** (landed) — `extensor_toDual_extensor_eq_zero_of_perp` in `Molecular/Meet.lean`: for
  `w, c : Fin 2 → ℝ⁴` with `∀ j, b.toDual (w j) (c i₀) = 0`, the point-join `extensor w` is
  `b.toDual`-annihilated by `extensor c`. N3b-recon rewrites to the Gram det `det (i j ↦ b.toDual
  (w j) (c i))` (`map_apply_ιMulti` + `pairingDual_ιMulti_ιMulti`); `hperp` zeros row `i₀`
  (`det_eq_zero_of_row_eq_zero`). Pure Lean infra (no blueprint node — below the include-bar).
- [x] **N3b-2b-β** (landed) — `finrank_sup_range_wedgeFixedLeft` (fact 3): `dim (a ∧ ℝ⁴ ⊔ b ∧ ℝ⁴) =
  5` for `{a,b}` independent via `Submodule.finrank_sup_add_finrank_inf_eq` (`3 + 3 − 1`). Genuine
  sub-content: the decomposable intersection `inf_range_wedgeFixedLeft`: `a ∧ ℝ⁴ ⊓ b ∧ ℝ⁴ =
  span{a ∧ b}` — `⊇` via `ι_add_mul_swap` (anticommutativity); `⊆` by left-multiplying `a ∧ v =
  b ∧ w` by `b` (`extensor ![b,a,v] = 0` ⟹ `v ∈ span{a,b}` via `linearIndependent_finSnoc`), so
  `a ∧ v ∈ span{a ∧ b}`. Pure Lean infra (no blueprint node — below the include-bar).
- [x] **The membership / proportionality + transfer** (the capstone, this commit) — in
  `Molecular/Meet.lean`: `complementIso_smul_eq_extensor_join` (`∃ c, c • complementIso(n_u ∧ n') =
  extensor ![pi, pj]`) + `extensor_join_eq_zero_of_complementIso_eq_zero` (the `r(C)=0 ⟹ r(join)=0`
  transfer). Both members in the 1-dim `Ω = (dualAnnihilator Φ̃).comap b.toDualEquiv` (the panel-meet
  by green step (i), the point-join by fact 2); two members of a line, one nonzero, proportional.
  **Routes through `Ω` directly, not `range (map 2 W.subtype)`** — cleaner than the phase-open plan
  (which is why N3b-2a / N3b-2b-line, while still landed green infra, are not on the final route).
  Flips `lem:case-III-claim612-line-in-panel-union` green; retires green-modulo-N3b on N9
  (`case_III_claim612`) and the candidate-completion chain.

## Blockers / open questions

- **None — phase complete.** The N3b node is green; the only deferred dependent is the next-phase
  `d=3` realization assembly (*Hand-off*), unchanged by 22f.
- **The `ofNormals` defeq-timeout trap does NOT bite 22f** (carry from 22a–e, FRICTION). 22f was pure
  exterior-algebra / `Module.Dual` content with no graph-swap; the trap bites the *deferred `d=3`
  assembly* (the consumer that extracts `rn`/`ro` and wires real graph data), not N3b.

## Hand-off / next phase

**22f is complete.** N3b green ⟹ Claim 6.12 (N9) and the candidate-completion chain are fully green;
the green-modulo-N3b language is retired across `case-iii.tex` / `case-ii.tex`.

The next deferred-**unlettered** cut is the **`d=3` realization assembly**, **design-reconned
2026-06-07 in `notes/Phase22-realization-design.md` §1.33** (read (A)/(B) before opening). The
recon re-scoped it off the older "hub brick + flip + wiring" framing: `rigidityMatrix_prop11`'s
`hub` is already **green** and `theorem_55` is a green *conditional*, so the real gap is the
**`d=3` `hsplit` producer** — wire `case_II_placement_eq612` ⊕ candidate-row ⊕ `case_III_claim612`
into `linearIndependent_sum_augment_candidateRow` at real graph data (where the `ofNormals`
defeq-timeout trap bites), then instantiate `theorem_55 (n:=2)` — taking the two producer nodes
`lem:case-II-realization` / `lem:case-III` green. Two open items at phase-open (§1.33 (B)): the
red `lem:cycle-realization` dependency status (B.1) and the `theorem_55` `d=3`-instance
architecture (B.2). Then **general-`d`** (Lemma 6.13, reuse map §1.33 (C)) is **Phase 23**. KT math: `notes/Phase22e.md` *Hand-off*,
`notes/Phase22d.md` *Hand-off*, KT §6.4; `notes/AlgebraicIndependence.md` (N3b stayed
alg-independence-free, pure Grassmann–Cayley).

Route (B) — direct decomposability — stays rejected (no Hodge/decomposable API in mathlib;
`complementIso` noncomputable → no `decide`).

## Decisions made during this phase

### Phase-local choices and proof techniques
- **The capstone routes through `Ω` directly, not `range (map 2 W.subtype)` (2026-06-07, close).**
  `complementIso_smul_eq_extensor_join` places both members in the 1-dim
  `Ω = (dualAnnihilator Φ̃).comap b.toDualEquiv` and proportionalizes there. `Ω` is where green
  step (i) (panel-meet) and fact 2 (point-join) already deposit their members, so no `range`
  framing or pull-back is needed. `dim Ω = 1` is `6 − 5` via
  `Subspace.finrank_add_finrank_dualAnnihilator_eq` + the perfect pairing
  (`comap_equiv_eq_map_symm` + `LinearEquiv.finrank_map_eq`); the `n'`-summand panel-meet kill uses
  the general dictionary half `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` (explicit `X`/`B`
  to dodge a `whnf` timeout) + a shared-`n'` `wedgeProd`-vanishing. N3b-1 / N3b-2a / N3b-2b-line /
  the recon / facts 2 & 3 all stay landed green infra; fact 2 + the recon are the load-bearing ones.
- **Fact 2 (point-join orthogonality) collapses to one `det_eq_zero_of_row_eq_zero` (2026-06-07).**
  `extensor_toDual_extensor_eq_zero_of_perp`: after the two `⟨extensor ·, _⟩ = ιMulti ·` coercion
  bridges (`Subtype.ext; rw [ιMulti_apply_coe]; rfl`, the N3b-2a idiom), N3b-recon + `map_apply_ιMulti`
  + `pairingDual_ιMulti_ιMulti` turn the pairing into `det (i j ↦ b.toDual (w j) (c i))`, and `hperp`
  (the incidence) zeros **row `i₀`** (a row, not the column the route prose first guessed). No more
  machinery than the recon predicted.
- **Fact 3 (`dim Φ̃ = 5`) — the decomposable intersection via left-multiply, not a basis extension
  (2026-06-07).** `inf_range_wedgeFixedLeft`: `a ∧ ℝ⁴ ⊓ b ∧ ℝ⁴ = span{a ∧ b}` proved without extending
  `{a,b}` to a basis — for `z = a ∧ v = b ∧ w`, left-multiplying by `b` gives `extensor ![b,a,v] = 0`
  (`join_extensor` + repeated-factor `extensor_eq_zero_of_eq`), so `v ∈ span{a,b}`
  (`linearIndependent_finSnoc`), whence `a ∧ v = β·(a ∧ b)`. `finrank_sup_range_wedgeFixedLeft` is then
  `3 + 3 − 1` (`finrank_sup_add_finrank_inf_eq`). The wedge-factor-swap micro-friction (`a∧b = b∧(−a)`
  via `ι_add_mul_swap`) → FRICTION.
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
