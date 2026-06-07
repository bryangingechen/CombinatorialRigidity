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

**Next concrete commit: N3b-2b** — the panel-meet half: `C(L) = complementIso (n_u ∧ n') ∈
range (exteriorPower.map 2 W.subtype)` for `W = {n_u, n'}^⊥`. This is the *non-operational*
range-membership upgrade of green step (i)
(`complementIso_toDual_extensor_eq_zero_of_shared_vector`, which gives only the *dual* reading —
annihilated by every 2-extensor sharing a normal). Honest range membership is a perfect-pairing
double-orthogonal argument: identify `range (map 2 W.subtype)` (the line `⋀²W`) with the
`b.toDual`-annihilator of `span{2-extensors sharing a direction with span{n_u, n'}}`, then step (i)
puts `complementIso (n_u ∧ n')` in that annihilator. This is genuinely heavier than the point-join
half (it needs the orthogonal-of-`⋀²W` identification), so it is its own leaf — spike mathlib for a
`Submodule.dualAnnihilator`/double-orthogonal exterior-power API before building. N3b-3
(proportionality via step (ii) + annihilation transfer) then composes on top of N3b-2a + N3b-2b,
flipping `lem:case-III-claim612-line-in-panel-union` green and retiring the green-modulo-N3b on N9
(`case_III_claim612`) and the candidate-completion chain (`lem:case-III-candidate-row`).

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
- [ ] **N3b-2b** (panel-meet half) — `C(L) = complementIso (n_u ∧ n') ∈ range (map 2 W.subtype)`,
  the non-operational range-membership upgrade of green step (i). Perfect-pairing double-orthogonal
  argument (identify `range (map 2 W.subtype)` with the `b.toDual`-annihilator of the
  shared-direction 2-extensors; step (i) lands `complementIso (n_u ∧ n')` in it). Heavier than
  N3b-2a — spike mathlib for double-orthogonal / `dualAnnihilator` exterior-power API first.
- [ ] **N3b-3** — proportionality via the green step (ii) `exteriorPower_finrank_eq_one_proportional`
  (pull back along the injective N3b-1 map into `⋀²W`, proportional there, push forward) + the
  annihilation transfer `r(C(L)) = 0 ⟹ r(p̄ᵢ ∨ p̄ⱼ) = 0`. Flips
  `lem:case-III-claim612-line-in-panel-union` green; retires the green-modulo-N3b on N9
  (`case_III_claim612`) and the candidate-completion chain.

## Blockers / open questions

- **N3b-2a coercion bridge — resolved, one routine step (not FRICTION).** The project's
  `extensor`/`join` live in `ExteriorAlgebra ℝ (Fin 4 → ℝ)` (graded into `⋀[ℝ]^2` via
  `extensor_mem_exteriorPower`), while mathlib's range API is phrased via `ιMulti`. The point-join
  half bridged the two with a single `Subtype.ext` + `rw [exteriorPower.ιMulti_apply_coe]` + `rfl` —
  under the one-bridge threshold, so no FRICTION entry. The panel-meet half (N3b-2b) is not a
  coercion question; it is the double-orthogonal argument (Current state).
- **The `ofNormals` defeq-timeout trap does NOT bite 22f** (carry from 22a–e, FRICTION). 22f is pure
  exterior-algebra / `Module.Dual` content with no graph-swap; the trap bites the *deferred `d=3`
  assembly* (the consumer that extracts `rn`/`ro` and wires real graph data), not N3b.

## Hand-off / next phase

**Next: land N3b-2b** — the panel-meet membership `C(L) = complementIso (n_u ∧ n') ∈
range (exteriorPower.map 2 W.subtype)` (see *Current state* for the double-orthogonal route; spike
the `dualAnnihilator`/double-orthogonal exterior-power API first), then N3b-3 (proportionality + the
annihilation transfer) to flip `lem:case-III-claim612-line-in-panel-union` green. The point-join half
N3b-2a is done. Both N3b-2b and N3b-3 are pure-Lean infra except N3b-3's final node flip; run
`blueprint/verify.sh` on the N3b-3 `\lean`/`\leanok` flip.

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
- **N3b-2 split into a point-join half (2a) and a panel-meet half (2b) (2026-06-07).** The 22f open
  scoped N3b-2 as one commit putting *both* `p̄ᵢ ∨ p̄ⱼ` and `C(L)` in `range (map 2 W.subtype)`.
  Building it surfaced an asymmetry: the point-join (2a, `extensor_mem_range_map_subtype_of_mem`) is
  a direct `map_apply_ιMulti` image (the recon-anticipated mathlib API + one coercion `Subtype.ext`),
  but the panel-meet (2b) is *not* a direct image — step (i) gives only the dual reading (annihilated
  by sharing-direction extensors), and the honest range membership is a perfect-pairing
  double-orthogonal argument identifying `range (map 2 W.subtype) = ⋀²W` with the annihilator of the
  shared-direction 2-extensors. That is genuinely heavier, so 2b is its own leaf. 2a is pure Lean
  infra below the blueprint include-bar (no node).
- **N3b-1 resolved to a mathlib one-liner at open — no retraction (2026-06-07, design recon).** The
  22e plan flagged N3b-1 as "concrete retraction; spike mathlib first." The spike found
  `exteriorPower.map_injective_field` (injectivity of `⋀ⁿ f` from injectivity of `f`, over a field),
  so over `ℝ` the leaf is just `exteriorPower.map_injective_field W.injective_subtype`
  (`Submodule.injective_subtype` supplies the hypothesis). Verified via `lean_multi_attempt` (no
  goals). The `CommRing`-level `exteriorPower.map_injective` (needs an explicit retraction) is the
  fallback, unneeded here. N3b-2/3 then compose on direct mathlib range API + the green step (ii).
