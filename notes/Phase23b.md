# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. CHAIN-3's three `_grade` bricks landed (the membership brick
`extensor_mem_range_map_subtype_of_mem_grade`, the **proportionality engine**
`exists_smul_eq_of_mem_range_map_subtype_grade`, the **`toDual=Gram` bridge**
`exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`). CHAIN-3's finish is the
**`⋀^{d−1}W`-is-a-line** route — point-join (`d−1` points) + panel-meet (`complementIso
(k:=d−1)(j:=2)`, **2** normals) both in the line `range(⋀^{d−1}W ↪)` — established by the
**CHAIN-3-finish recon** (`notes/Phase23-design.md` §"CHAIN"(f)/(g), 2026-06-17), which
**withdrew** the dead d=3-only `Φ̃` route (`finrank_sup_range_wedgeFixedLeft` /
`extensor_toDual_extensor_eq_zero_of_perp` + the lifted `wedgeFixedLeft` / `inf_range_wedgeFixedLeft`
infrastructure stay green at d=3, do NOT generalize: `dim Ω = C(d−1,2) = 1` only at `d=3`). The one
genuinely-new leaf is the **panel-meet range-membership** `complementIso_extensor_mem_range_map_subtype`
(route OPEN, OD-8); its **standard-frame** base case `complementIso_exteriorPower_basis_eq_smul_compl`
and standard-frame **range-membership** `complementIso_exteriorPower_basis_mem_range_map_subtype` have
landed (2026-06-17), leaving the **general-decomposable** (non-coordinate `W = {n₀,n₁}^⊥`) lift; the
assembly then reuses the THREE landed `_grade` bricks (zero new count). The integer Phase 23 stays
**in progress** — ENTRY / ASSEMBLY remain (coordinator owns the sub-phase boundary; codes-until-open).

**Orientation.** This is the **23b (CHAIN layer)** sub-phase work log — the
*rolling* state + hand-off for the active layer only. The cross-phase
**plan/guidance** (sub-phase division, sequence, open decisions, sources) is the
canonical job of `notes/Phase23-design.md`; the **detailed leaf-level recon of
CHAIN** is its §"CHAIN — detailed leaf-level recon" ((a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions). The
program map is `notes/MolecularConjecture.md`. **Sub-phase naming convention:**
the layers are tracked by stable **codes** — `CARRIER`(=23a, closed), `CHAIN`(=
this 23b), `ENTRY`, `ASSEMBLY`; a letter + work log is minted when a layer
opens, so a later split costs no renumber-churn. `23b` is the minted letter for
CHAIN; ENTRY/ASSEMBLY stay code-only until their turn.

## Current state

**CHAIN-3's OD-8 route-(α) (h-1) wedge-pairing-covariance core has landed (2026-06-17, this commit):**
the change-of-frame transformation laws of the perfect wedge pairing under `exteriorPower.map` —
`wedgeProd_map` (`wedgeProd (map f A) (map f B) = map f (wedgeProd A B)`, the graded wedge product is
covariant) and `wedgePairing_map` (`wedgePairing (map f A) (map f B) = (det f) • wedgePairing A B`,
the pairing scales by the determinant) — both in `Meet.lean`. The covariance rests on the new mirror
`exteriorPower.map_coe_eq_exteriorAlgebra_map` (`↑(map n f X) = ExteriorAlgebra.map f ↑X`,
`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`), which pushes the multiplicativity of the algebra
morphism `ExteriorAlgebra.map f` through `wedgeProd`'s underlying product `↑A*↑B`; then `wedgePairing_map`
composes that with the LANDED (h-0) `screwAlgebraTopEquiv_map_eq_det_smul`. This is the *join/volume*
half of (h-1) — the genuine algebraic content `complementIso`'s O(n)-equivariance is built on.
**Next buildable sub-step = the dot-product half of (h-1)**: the exterior-power **Gram pairing's
O-invariance**, `b.toDual (map O Z) (map O B) = b.toDual Z B` for orthogonal `O` (`b =
(Pi.basisFun).exteriorPower`). `complementIso`'s second factor is the standard `toDualEquiv.symm`, so
converting `wedgePairing_map` into the `complementIso` equivariance `complementIso (map₂ O X) = det O •
map_k O (complementIso X)` needs that O-invariance to handle the free `B`-slot — the from-scratch piece
that did not fit this sitting. **`complementIso` IS the Hodge star `⋆`** (standard volume form
`screwAlgebraTopEquiv = topEquiv` + dot product `Pi.basisFun.toDual`), O(n)-natural but NOT GL-natural;
(h-1)'s full statement is "`⋆(map O X) = det O • map O (⋆X)`" for orthogonal `O`. Route then: (h-2)
Gram–Schmidt alignment, (h-3) assemble with the LANDED standard-frame membership
`complementIso_exteriorPower_basis_mem_range_map_subtype`, closing
`complementIso_extensor_mem_range_map_subtype`; then the assembly
`extensor_join_proportional_complementIso_meet` (h-4) via the `⋀^k W`-is-a-line route (reusing the
three landed `_grade` bricks; zero new count). **Route β rejected** (the annihilation→membership
upgrade is the withdrawn `dim Φ̃` count, not a free dimension match). **NOT**
`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp` — the CHAIN-3-finish
recon withdrew those (dead d=3-only `Φ̃` route; see checklist + Hand-off + §"CHAIN"(f)/(h)).
The recon
(`notes/Phase23-design.md` §"CHAIN") source-verified — against KT §6.4.2 (eqs.
6.46–6.67, read end-to-end) and the landed tree — that **the arm-realization
engine is already general-`k`** (the M₁/M₂/M₃ closers `case_III_arm_realization`
/ `_M2` / `_M3` in `CaseIII/{Arms,Relabel}.lean` were authored `(k:ℕ)`); the
genuinely-`d=3` surface is **only the dispatch** (`case_III_candidate_dispatch`,
`Realization.lean:201`) — its fixed-3-candidate count + the `⋀²ℝ⁴` discriminator
(`exists_homogeneousIncidence_of_normals` / `…complementIso…` in `Claim612.lean`,
the `Meet.lean` duality lemmas). CHAIN's job: replace that dispatch with the
`d`-candidate chain dispatch + the `⋀^{d−1}(ℝ^{d+1})` duality finish.

**The load-bearing flag (recon (b)) — SETTLED 2026-06-17.** The 23a-carried
`hdispatch` (`Theorem55.lean:2225`) takes a **fixed `v,a,b,c` 4-tuple**, faithful
at `d=3` (the chain `v₀v₁v₂v₃` *is* `b—v—a—c`) but **too short at `d≥4`** — KT's
general-`d` Lemma 6.13 needs the whole length-`d` chain. The CHAIN↔ENTRY
chain-data contract is now **frozen** (`notes/Phase23-design.md` §"CHAIN↔ENTRY
contract"): a `G.ChainData n` `structure` (length-`d` chain `vtx`/`edge`/`e₀` +
degree-2 closures) is the shared shape; the reshape is **three decls in
lockstep** — the ENTRY extractor (`exists_chain_data_of_noRigid` → a `ChainData`
producer), the producer `case_III_hsplit_producer_all_k.hcand` (which calls the
extractor inline, C.0), and the CHAIN-5 dispatch `hdispatch`. **No motive/IH
change forced** (clause (ii), C.6): the chain data is combinatorial, the base
`(G₁,q₁)` stays the existing general-`k` realization premise from the same 0-dof
IH conjunct, the `d` candidate splits are smaller 0-dof graphs. CHAIN-5's
signature is now authorable; the `d=3` line is a zero-regression wrapper (C.4).

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)). Five leaves, **one** sub-phase (OD-6).
CHAIN-1/3 are buildable now (no ENTRY-contract dependency); CHAIN-5 is gated by
the (b) flag (its signature is the CHAIN↔ENTRY contract).

- [◐] **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks** (`Meet.lean`).
      Re-state at `⋀[ℝ]^{d−1}(Fin (d+1)→ℝ)` with the general
      `finrank(⋀^{d−1}W)=(finrank W).choose (d−1)`. Build LAZILY at concrete grade
      — NO general Hodge-star. Unblocks CHAIN-4 + the four-producer lift (OD-7).
      - [x] `extensor_mem_range_map_subtype_of_mem_grade` — the membership brick
        (grade-generic verbatim; `d=3` `extensor_mem_range_map_subtype_of_mem`
        re-derived as the `(d:=3)` instance). Landed 2026-06-17.
      - [x] `exists_smul_eq_of_mem_range_map_subtype_grade` — the proportionality
        engine at general grade, the genuine `finrank` count via two further
        grade-generic bricks `finrank_exteriorPower_self_eq_one` (top-grade `⋀^n W`
        is a line for `dim W = n`, `exteriorPower.finrank_eq`+`Nat.choose_self`)
        and `exteriorPower_map_subtype_injective_grade`. The three `d=3` names
        (`exists_smul_…`, `finrank_exteriorPower_two_eq_one`,
        `exteriorPower_map_subtype_injective`) survive as `(d:=3)` instances
        (blueprint pins on the latter two untouched). Landed 2026-06-17.
      - [x] `exteriorPower_basis_toDual_eq_pairingDual_comp_map` — the `toDual=Gram`
        bridge, lifted to `…_grade {d}` over `Fin (d+1)` (the proof is ambient-/
        grade-generic verbatim; the `d=3` name survives as the `(d:=3)` instance,
        line-1003 internal consumer untouched, no blueprint pin on this decl).
        Landed 2026-06-17.
      - [◐] `complementIso_smul_eq_extensor_join` at general grade. **The heavier
        generalization** — `complementIso`/`toDual` built over `k+2` / `Fin 4`, not
        a verbatim grade-lift. Its dependency chain must lift first:
        - [x] `wedgeFixedLeft` (the `def`) + `coe_wedgeFixedLeft` / `ker_wedgeFixedLeft`
          / `finrank_range_wedgeFixedLeft` lifted `Fin 4` → ambient `{d} (Fin (d+1))`,
          grade `2`, range count `3 → d`. Ambient-generic verbatim; implicit `{d}` so
          the `Fin 4` consumers unify `d=3` by defeq (no instance decls). Landed
          2026-06-17. (One friction: `finrank_sup_range`'s `omega` mis-atomized the
          `(d:=3)`-vs-`Fin 4` elaborations → `simpa using hsum`; QUIRKS § 58.)
        - [x] `inf_range_wedgeFixedLeft` (`Fin 4` → ambient `{d}`, the decomposable intersection)
          — ambient-generic verbatim; the `Fin 2`/`Fin 3` `decide`/`fin_cases`/
          `linearIndependent_finSnoc` are fixed family arities, `d` enters only the ambient type.
          Implicit `{d}`, no `d=3` instance (the in-file consumer unifies `d=3` by defeq).
          Landed 2026-06-17.
        - [~] **WITHDRAWN — `finrank_sup_range_wedgeFixedLeft` does NOT generalize and is
          NOT needed** (CHAIN-3-finish recon, `notes/Phase23-design.md` §"CHAIN"(f),
          2026-06-17). Its `Φ̃ = dualAnnihilator`/`dim Ω = 1` route is sound only at
          `d=3` (`dim Ω = C(d−1,2) = 1` ⟺ `d=3`). The d=3 lemma stays as the GREEN d=3
          route — do NOT touch. Same for `extensor_toDual_extensor_eq_zero_of_perp`.
        - [◐] `complementIso_extensor_mem_range_map_subtype` — **the one genuinely-new leaf**
          (panel-meet `complementIso(k:=d−1)(j:=2)⟨n_u∧n',_⟩ ∈ range(⋀^{d−1}W ↪)`, the
          never-completed N3b-2b-α). Route is OPEN — OD-8 §(g) (α Hodge-direct vs. β
          annihilator=range; neither needs a new mathlib fact). Consumes the LANDED
          general `complementIso_toDual_eq_zero_of_wedgeProd_eq_zero` + `finrank_exteriorPower
          _self_eq_one`.
          - [x] `complementIso_exteriorPower_basis_eq_smul_compl` — the **route-(α) base case**
            (standard-frame): `complementIso hj (e_S) = (wedgePairing e_S e_{Sᶜ}) • e_{Sᶜ}`, the
            complement of a coordinate blade is the complementary blade. Fully general (`{k}`,
            `{j}`, any `S`), no `d=3` pin. Off-diagonal coords vanish
            (`wedgePairing_ιMulti_family_eq_zero_of_ne_compl`) so only the `Sᶜ` term survives.
            Landed 2026-06-17.
          - [x] `complementIso_exteriorPower_basis_mem_range_map_subtype` — the **route-(α)
            standard-frame range-membership** (`j=2`): for `W` containing every complementary
            coordinate vector `eₜ` (`t ∈ Sᶜ`), `complementIso (j:=2) e_S ∈ range(⋀^k W ↪)`. The
            range-membership packaging of the base case (`= (±1) • e_{Sᶜ}`, `e_{Sᶜ}` is the
            `k`-extensor of the `Sᶜ` standard basis vectors, in `range` by
            `extensor_mem_range_map_subtype_of_mem_grade (d:=k+1)`; scalar stays in the submodule).
            The coordinate-subspace instance of the OD-8 leaf. Landed 2026-06-17.
          - [◐] the **general-decomposable** step `complementIso_extensor_mem_range_map_subtype`:
            lift to an arbitrary grade-2 decomposable `extensor n` (`n : Fin 2`) with
            `W = {n₀,n₁}^⊥`. **Route DECIDED (OD-8, `notes/Phase23-design.md` §"CHAIN"(h)): route α
            via `complementIso` O(n)-equivariance.** `complementIso` IS the Hodge `⋆` (standard
            volume form + dot product), O(n)-natural but NOT GL-natural — so the lift is a genuine
            **orthogonal** change of frame, not a GL transport. Sub-leaves:
            - [x] **(h-0)** `screwAlgebraTopEquiv_map_eq_det_smul` — the volume-form-by-det fact
              `screwAlgebraTopEquiv (map (k+2) f X) = (det f) • screwAlgebraTopEquiv X` (`Meet.lean`),
              the `N=k+2` corollary of the new general mirror `exteriorPower.topEquiv_map_eq_det_smul`
              (`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`; `Basis.ext` to the top-power generator
              + the `det = (toMatrix' f)ᵀ` computation). Landed 2026-06-17.
            - [◐] **(h-1) `complementIso_map_orthogonal_eq` — the substantive new leaf + clause-(ii)
              flag.** Its **wedge-pairing-covariance core has LANDED** (2026-06-17, this commit):
              `wedgeProd_map` (the graded wedge product is covariant — `wedgeProd (map f A) (map f B)
              = map f (wedgeProd A B)`, via the new mirror `exteriorPower.map_coe_eq_exteriorAlgebra_map`
              pushing `ExteriorAlgebra.map f`'s multiplicativity through `↑A*↑B`) and `wedgePairing_map`
              (the pairing scales by `det f` — `wedgePairing (map f A) (map f B) = det f • wedgePairing A B`,
              `wedgeProd_map` + (h-0)). **Remaining:** the *dot-product side* — `complementIso`'s second
              factor is `(Pi.basisFun).exteriorPower.toDualEquiv.symm`, so converting `wedgePairing_map`
              into the `complementIso` equivariance `complementIso (map₂ O X) = det O • map_k O
              (complementIso X)` needs the exterior-power Gram pairing's O-invariance
              (`b.toDual (map O Z)(map O B) = b.toDual Z B`, `O` orthogonal) to handle the free `B`-slot.
              That Gram-O-invariance is the from-scratch piece that did not fit this sitting.
            - [ ] (h-2) Gram–Schmidt alignment of `span{n₀,n₁}` to a coordinate plane.
            - [ ] (h-3) assemble (h-1)+(h-2)+the LANDED standard-frame membership.
            Route β (annihilator=range) is **rejected** (it re-introduces the withdrawn `dim Φ̃`
            count). Fallback: carry (h-3) green-modulo if (h-1) is a long pole. (h-1) is the one
            genuinely-open math obligation of the CHAIN-3 finish.
        - [ ] `extensor_join_proportional_complementIso_meet` — the general-`d` assembly
          (replaces `complementIso_smul_eq_extensor_join`; d=3 line stays as wrapper). The
          **`⋀^{d−1}W`-is-a-line** route: point-join (`d−1` points) + panel-meet (**2**
          normals), both in `range(⋀^{d−1}W ↪)` a line, proportional. Consumes the new leaf
          above + the THREE LANDED `_grade` bricks (`extensor_mem_range_…_grade`,
          `exists_smul_eq_…_grade`, `exteriorPower_map_subtype_injective_grade`). Zero new count.
- [ ] **CHAIN-1 — the `d`-fold candidate augment** (`RigidityMatrix/Basic.lean`).
      Generalize `linearIndependent_sum_augment_candidateRow` (one `Unit`) to a
      `Fin d`-indexed augment. Graph-free over `ScrewSpace k`; no `d=3` content.
- [ ] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
      (`Claim612.lean`). Re-state `exists_homogeneousIncidence_of_normals` (the
      `d+1`-point incidence pattern, eq. 6.67), the dispatch-internal bricks,
      `case_III_claim612` (reusing the general `span_omitTwoExtensor_eq_top`
      (23a Leaf 2) + Lemma 2.1), and `exists_complementIso_ne_zero_…` at
      `ScrewSpace (d−1)` / `Fin d` candidates. Consumes CHAIN-3. **OD-4 sub-leaf
      (the eq. 6.67 `d+1`-points step) lands here — flagged open.**
- [ ] **CHAIN-2 — the chain matrix bookkeeping (eqs. 6.59–6.64)** (`CaseIII/`).
      The per-candidate-`i` reduction of `R(G,pᵢ)` to `Mᵢ ⊕ R(G₁∖(v₀v₂)_{i*},q₁)`
      + the ±r chain (6.66). Reuses Claim 6.11 `exists_redundant_panelRow_…`
      (general & GREEN). Heaviest mechanical leaf ("exactly the same as `d=3`").
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`).
      Replace `case_III_candidate_dispatch`; feed the (general-`k`) arm closers.
      **Signature now FROZEN** by the CHAIN↔ENTRY contract (`notes/Phase23-design.md`
      §"CHAIN↔ENTRY contract" C.3): `hdispatch` consumes a `G.ChainData n` record
      (the length-`d` chain) + the `splitOff (vtx 1)(vtx 0)(vtx 2) e₀` deficiency-0
      fact + the IH-generic base realization on that split. Keep the `d=3` dispatch
      as a `k=2`/length-3 wrapper (no `d=3` regression — C.4 zero-regression map).
- [ ] **CHAIN tail — lift the four 23a-carried producers** (OD-7 fold). After
      CHAIN-3: `hforget_k` (M4 forget, `exists_extensor_eq_panelSupportExtensor`
      routes through CHAIN-3's duality), then through it `hbase_k`/`hcut_k`/
      `hcontract_k`. Direct corollary of CHAIN-3 + numeral pass — caveat (e)
      OD-7: confirm the *only* genuinely-`d=3` reach-in is the duality at build.

## Blockers / open questions

The OD resolutions (full text in `notes/Phase23-design.md` §"CHAIN"(e)/(g)):

- **OD-8 — ROUTE DECIDED 2026-06-17 (route α via `complementIso` O(n)-equivariance;
  the O(n)-equivariance is itself a flagged substantial leaf).** The panel-meet
  range-membership `complementIso(j:=2)⟨n_u∧n',_⟩ ∈ range(⋀^k W ↪)` for
  `W = {n_u,n'}^⊥`. **Decision (full text `notes/Phase23-design.md` §"CHAIN"(h)):**
  `complementIso` IS the Hodge star `⋆` for the standard volume form
  (`screwAlgebraTopEquiv = topEquiv`) + dot product (`Pi.basisFun.toDual`), so the
  target is the genuine Hodge fact "`⋆` of a decomposable = decomposable of the
  orthogonal complement". The in-hand annihilation does **NOT** give membership for
  free — the annihilator-=-range dimension match (route β) is the **withdrawn
  `dim Φ̃` count** (`= C(d−1,2) > 1` for `d≥4`), so **β is rejected, not a fallback**.
  Route α leaf chain (h-0…h-4): (h-0) volume-form-by-determinant
  (`screwAlgebraTopEquiv (map f ·) = det f · …`, mathlib has pieces not the fused
  lemma), (h-1) `complementIso_map_orthogonal_eq` — **the O(n)-equivariance, the
  substantive new leaf + clause-(ii) flag** (Hodge `⋆` is O(n)-natural not GL-natural),
  (h-2) orthonormal alignment of `span{n_u,n'}` to a coordinate plane (Gram–Schmidt),
  (h-3) assemble with the LANDED standard-frame membership, (h-4) the assembly. **No
  missing mathlib *API*** (clause (ii)), but a genuine new *project* sub-lemma (h-1).
  **Genuine fallback if (h-1) is a long pole:** carry (h-3) as an explicit
  green-modulo `h…` premise (standing idiom), never a `sorry`.
- **OD-6 — DECIDED: five leaves within ONE sub-phase 23b** (no separate duality
  letter). The arm-realization engine they feed is already general-`k`, so
  neither hard core stands alone as a deliverable. Split at contact only if
  CHAIN-2's index bookkeeping proves larger than estimated.
- **OD-7 — DECIDED: the four 23a-carried producers fold into CHAIN's tail**
  (after CHAIN-3), not a dedicated successor — the M4-forget reach-in *is*
  CHAIN-3's duality, and the conditioned-pair producers route through M4.
  Caveat: confirm at build that the duality is their *only* `d=3` reach-in.
- **OD-4 — FLAGGED (genuinely open; do NOT pre-commit a route).** KT eq. (6.67)
  states the `d+1`-points step **via algebraic independence** (p. 698 verbatim);
  the `d=3` N3a was AVOIDED via an explicit construction (`AlgebraicIndependence.md`
  row #106) that does **not** obviously generalize. Whether general `d` takes
  the existence route or forces the alg-independence hammer is unresolved — the
  CHAIN-4 detailed-build recon decides. Cross-checked `AlgebraicIndependence.md`
  row #107(b) (already scopes this as "uncertain whether a NEW site", defers to
  CHAIN open); this recon confirms the question is real and routes it to build.
- **(b) producer-shape mismatch — SETTLED 2026-06-17** (the docs-only
  contract-settle pass). The CHAIN↔ENTRY interface is frozen in
  `notes/Phase23-design.md` §"CHAIN↔ENTRY contract": a `G.ChainData n` `structure`
  (length-`d` chain `vtx : Fin (d+1) → α`, `edge : Fin d → β`, `e₀`, the deg-2
  closures) is the shared shape. **No motive/IH change forced** (C.6): the chain
  data is purely combinatorial, the base `(G₁,q₁)` is the existing general-`k`
  `HasGenericFullRankRealization` premise pulled from the same 0-dof IH conjunct,
  the `d` candidate splits are smaller 0-dof graphs (no higher-dof `G_v` GAP-6).
  The reshape is **three decls in lockstep** (extractor / producer-`hcand` /
  dispatch-`hdispatch`); the `d=3` line is a zero-regression wrapper (C.4 map:
  chain `v₀v₁v₂v₃ = b—v—a—c`). CHAIN-5's signature is now authorable.
- **OD-1 (re-confirmed for CHAIN/ENTRY).** KT Lemma 5.4 short-cycle base is a
  real branch of the general-`d` chain entry (unlike `d=3`'s inline triangle
  floor); whether CHAIN's dispatch assumes the chain branch (ENTRY discharging
  the cycle branch) is an ENTRY-contract question.

## Hand-off / next phase

**Next buildable sub-step = the dot-product half of (h-1): the exterior-power Gram pairing's
O-invariance** — `b.toDual (map O Z) (map O B) = b.toDual Z B` for orthogonal `O` (`b =
(Pi.basisFun).exteriorPower`, the standard dot product lifted to `⋀ᵏ`). **(h-1)'s wedge-pairing-
covariance core (the volume/join half) landed this commit** (`wedgeProd_map` / `wedgePairing_map`,
`Meet.lean`, on the new mirror `exteriorPower.map_coe_eq_exteriorAlgebra_map`). With that O-invariance
in hand, the `complementIso` equivariance `complementIso_map_orthogonal_eq`
(`complementIso (map₂ O X) = det O • map_k O (complementIso X)`) closes by `b'.toDual`-injectivity:
pair both sides against `B = map_k O B'`; the LHS is `wedgePairing_map` (= `det O • wedgePairing X B'`)
and the RHS is `det O • b.toDual (map O (complementIso X)) (map O B')` = `det O • wedgePairing X B'`
by Gram-O-invariance + `complementIso_toDual`. The target leaf
`complementIso_extensor_mem_range_map_subtype` (signature §(f) item 2):
`complementIso (j:=2) ⟨extensor n,_⟩ ∈ range(exteriorPower.map k W.subtype)` for `W = {n₀,n₁}^⊥`.
**Route decision (§(h)):** `complementIso` IS the Hodge star `⋆` for the standard volume form
(`screwAlgebraTopEquiv = topEquiv`) + dot product (`Pi.basisFun.toDual`) — so the target is the
genuine Hodge fact "`⋆` of a decomposable = decomposable of the orthogonal complement", which is
**O(n)-natural but NOT GL-natural**. The route lifts via an **orthogonal** change of frame:
- **(h-0)** volume-form-by-determinant — **LANDED** as
  `screwAlgebraTopEquiv_map_eq_det_smul` (`Meet.lean`) + the general mirror
  `exteriorPower.topEquiv_map_eq_det_smul` (`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`):
  `screwAlgebraTopEquiv (map (k+2) f X) = det f • screwAlgebraTopEquiv X`.
- **(h-1)** `complementIso_map_orthogonal_eq` — **the substantive new leaf + the clause-(ii) flag.**
  For orthogonal `O` (`det O = ±1`), `complementIso (map 2 O X) = det O • map k O (complementIso X)`.
  **Its wedge-pairing-covariance core LANDED this commit** (`wedgeProd_map` / `wedgePairing_map`,
  consuming (h-0)); the **remaining** piece is the dot-product Gram-O-invariance above — *the one
  genuinely-open math obligation.*
- **(h-2)** `exists_orthogonal_map_span_pair_eq_coordPlane` — Gram–Schmidt alignment of `span{n₀,n₁}`
  to a coordinate `2`-plane (mathlib orthonormal-extension API), carrying `W` to a coordinate subspace.
- **(h-3)** the target leaf — assemble (h-1)+(h-2)+the LANDED
  `complementIso_exteriorPower_basis_mem_range_map_subtype`. **In hand for the case split:** when
  `extensor n = 0` (dependent `n`), `complementIso 0 = 0 ∈ range` trivially; the work is the
  `n`-independent case, where `dim W = k` (rank–nullity on the 2 functionals).

**Why NOT route β:** the in-hand annihilation (`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`)
puts `complementIso n` in an annihilator `Ann(Φ)`; upgrading that to range-membership needs
`dim Ann(Φ) = 1`, i.e. the **withdrawn `dim Φ̃` count** (`= C(d−1,2) > 1` for `d≥4`). So β is
**rejected, not a fallback**. **Genuine fallback if (h-1) is a long pole:** carry (h-3) as an
explicit green-modulo `h…` premise on CHAIN-4's discriminator (standing idiom), land (h-1) in a
dedicated sitting — never a `sorry`. (`Meet.lean`; still no ENTRY-contract dependency.)
The CHAIN-3-finish recon (`notes/Phase23-design.md` §"CHAIN"(f)/(g), 2026-06-17, source-verified
against KT §6.4.1/§6.4.2 + the landed bodies) **overturned the prior pin** and corrected the
geometry:
- **`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp` do
  NOT generalize and are NOT needed.** They are the d=3-only `Φ̃ = dualAnnihilator` /
  `dim Ω = 1` route; `Φ̃` is built from the **2** line-normals, so `dim Ω = C(d−1,2)`,
  which is `1` only at `d=3`. The d=3 lemmas stay as the GREEN d=3 route — do NOT touch.
- **The route that DOES generalize: `⋀^{d−1}W`-is-a-line.** Point-join (the `(d−1)`-
  extensor of the **`d−1`** points spanning the line `L`) and panel-meet (`complementIso
  (k:=d−1)(j:=2)` of the **2** hyperplane normals — `j=2`, not `j=d−1`) both lie in
  `range(⋀^{d−1}W ↪ ⋀^{d−1}ℝ^{d+1})` for `W = span(L) = {n_u,n'}^⊥` (`dim W = d−1`), a
  **line** (`finrank_exteriorPower_self_eq_one`). This is exactly what the THREE landed
  `_grade` bricks (`extensor_mem_range_…_grade`, `exists_smul_eq_…_grade`,
  `exteriorPower_map_subtype_injective_grade`) were built for — they have NO consumers in
  tree (grep-confirmed), landed forward for this.

Leaf sequence (§(f)+§(h)): (1) `complementIso_extensor_mem_range_map_subtype` — the new leaf, route
**(α) DECIDED** via O(n)-equivariance (§(h) leaves h-0…h-3). Its **standard-frame base case
`complementIso_exteriorPower_basis_eq_smul_compl` and the standard-frame range-membership
`complementIso_exteriorPower_basis_mem_range_map_subtype` have LANDED** (2026-06-17); the remaining
content is the general-decomposable lift to a non-coordinate `W = {n₀,n₁}^⊥` — the genuine
**orthogonal** change-of-frame step (h-1/h-2/h-3), **not** a GL-equivariance corollary (`complementIso`
is the Hodge `⋆`, O(n)- but not GL-natural). Route (β) is **rejected** (re-introduces the withdrawn
`dim Φ̃` count). Then (2) `extensor_join_proportional_complementIso_meet` — the assembly (h-4; zero
new count, consumes (1) + the three `_grade` bricks); (3) the d=3 wrapper stays green (h-5). Closing
(1)+(2) closes CHAIN-3 and feeds CHAIN-4's discriminator. **The O(n)-equivariance (h-1) is the one
genuinely-open math obligation of the CHAIN-3 finish.**

**The CHAIN↔ENTRY contract is now settled** (`notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", 2026-06-17) — the (b) build-recon gate is discharged:
CHAIN-5's `hdispatch`/`hcand` signature is frozen against the `G.ChainData n`
record (C.1/C.3), so it is now authorable. The next buildable leaf is still in
**CHAIN-3** (its `complementIso`/`toDual` tail — no chain-data dependency;
finishing CHAIN-3 unblocks CHAIN-4 + the four-producer lift). CHAIN-1/3/4 remain
buildable independently of the contract; CHAIN-5 is unblocked once CHAIN-1/2/4
land **and** ENTRY's extractor is reshaped.

**ENTRY obligation — PINNED (signature frozen; minted/built when its turn
comes).** ENTRY reshapes `Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`)
from the fixed `v,a,b,c` 4-tuple to the `G.ChainData n` producer
`exists_chainData_of_noRigid` (contract C.2 — KT Lemma 4.6 chain + Lemma 4.8
split-off minimality at general `d`, the "new combinatorial leaf" of the
OD-2/OD-3 verdict), and lifts the `6 ≤ bodyBarDim n` floor to the general
chain-length floor. The chain/cycle dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4)
is **ENTRY's to resolve at build** (contract C.5): the dispatch always consumes
a `ChainData` and never sees the cycle branch, so ENTRY's choice between
"chain-only extractor + cycle folded into base" (default) vs. "disjunction +
Lemma 5.4 short-cycle realization brick" is invariant for CHAIN-5's signature.
**The producer `case_III_hsplit_producer_all_k` (`Arms.lean:777`) is the chain
extractor's only consumer** (it calls the extractor inline at the `|V|≥4` arm,
Arms.lean:828–857) — its `hcand` slot is the third lockstep decl (C.0).

**Green-modulo boundary CHAIN hands downstream** (`notes/Phase23-design.md`
§"CHAIN"(d)): CHAIN discharges the general-`k` `hdispatch` (now against the frozen
`ChainData` contract) and lifts the four producers (OD-7). **ASSEMBLY** composes
the honest general-`d` Theorem 5.5, re-greens `prop:rigidity-matrix-prop11` +
`hub`, derives Thm 5.6, states Conjecture 1.2.

## Decisions made during this phase

(Phase-local choices land here as CHAIN leaves build. The opening recon's
decisions — OD-6/OD-7 resolved, OD-4 + (b) flagged — live in
`notes/Phase23-design.md` §"CHAIN"(e); the chain-data contract lives in its
§"CHAIN↔ENTRY contract".)

### Phase-local choices and proof techniques

Settled entries are one-line verdicts (decision + Lean name); proof techniques live
in git + `notes/FRICTION.md` + the design doc §"CHAIN"(f)/(g)/(h) + §"CHAIN↔ENTRY
contract". The forward detail (route to close the open leaves) is in *Current state*
/ *Hand-off* above.

**Recons / design decisions (detail in `notes/Phase23-design.md`):**
- **Opened on a leaf-level recon, not a build** — found the arm-engine already
  general-`k`, only the dispatch `d=3`; surfaced flag (b) → §"CHAIN"(a)–(e).
- **CHAIN↔ENTRY chain-data contract settled** — `G.ChainData n` structure +
  producer/`hdispatch` signatures; no motive/IH change forced (clause ii) →
  §"CHAIN↔ENTRY contract" C.0–C.6.
- **CHAIN-3-finish recon: the `⋀^{d−1}W`-is-a-line route, NOT the d=3 `Φ̃` route**
  (a line has **2** normals at every `d`, **d−1** points); `finrank_sup_range_wedgeFixedLeft`
  / `extensor_toDual_extensor_eq_zero_of_perp` **withdrawn** (dead d=3-only, kept green
  as the d=3 wrapper) → §"CHAIN"(f). KT-route-checked (the join=meet duality KT leaves
  implicit) → §"CHAIN"(f) *Coordinator KT-route check*.
- **OD-8 route DECIDED: route α via `complementIso` O(n)-equivariance; β + γ rejected**
  — `complementIso` IS the Hodge `⋆`; β rests on the withdrawn `dim Φ̃` count. (h-1)
  the O(n)-equivariance is the one genuinely-open obligation (green-modulo escape: carry
  h-3) → §"CHAIN"(h).

**Landed CHAIN-3 bricks** (all keep the `d=3` name as a `(d:=3)` instance or unify
`d=3` by defeq; no blueprint pin moved; the `_grade` lifts are verbatim — the route is
general mathlib, grade enters nothing):
- membership `extensor_mem_range_map_subtype_of_mem_grade`; proportionality
  `exists_smul_eq_of_mem_range_map_subtype_grade` + the count
  `finrank_exteriorPower_self_eq_one` / `exteriorPower_map_subtype_injective_grade`;
  `toDual=Gram` `exteriorPower_basis_toDual_eq_pairingDual_comp_map_grade`.
- `wedgeFixedLeft` block (`def`+`coe`/`ker`/`finrank_range`, range count 3→d) +
  `inf_range_wedgeFixedLeft` — ambient-generic verbatim, implicit `{d}`, no instance
  (no external consumers). **Dead-route machinery** (the `Φ̃` count the CHAIN-3-finish
  recon withdrew): harmlessly over-general (d=3 instances still used) — **cleanup-round
  candidate to revert to `Fin 4`**.
- OD-8 route-α sub-leaves: base case `complementIso_exteriorPower_basis_eq_smul_compl`
  (complement of a coordinate blade = the complementary blade) → coordinate-`W`
  membership `complementIso_exteriorPower_basis_mem_range_map_subtype` → (h-0)
  `exteriorPower.topEquiv_map_eq_det_smul` (mirror) + `screwAlgebraTopEquiv_map_eq_det_smul`
  → (h-1a) `wedgeProd_map`/`wedgePairing_map` (on mirror `map_coe_eq_exteriorAlgebra_map`).
  The general-decomposable case is NOT a GL-equivariance corollary (`complementIso` is
  Hodge, O(n)- not GL-natural) — needs h-1b (dot-product Gram-O-invariance), the next step.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *To use the mirrored `Finset.univ_orderEmbOfFin` on a `powersetCard` `default` index,
  surface `↑default = univ` with a `rfl`-`have` first (it won't `simp` out on its own)*
  → FRICTION [idiom] *To use the mirrored `Finset.univ_orderEmbOfFin` on a `powersetCard`…*.
- *A `-/` inside a docstring word (`grade-/ambient`) closes the doc comment early
  → "unexpected identifier; expected 'lemma'" inside the prose* → TACTICS-QUIRKS § 57.
- *After lifting an in-place numeral-pinned `def` to implicit `{d}`, a numeral
  consumer's `omega` mis-atomizes the `(d:=3)`-vs-numeral elaborations of one term
  (free-variable counterexample, never reads the bridging hyp) — use `linarith` /
  `simpa using h`* → TACTICS-QUIRKS § 58 / FRICTION [idiom] *Generalizing an in-place
  numeral-pinned `def`…*.
- *`Set.powersetCard.compl` inside a hypothesis (no expected `powersetCard _ m` type)
  leaves the target cardinality `m` a stuck metavariable — pin `(m := …)` explicitly*
  → FRICTION [idiom] *`Set.powersetCard.compl` inside a hypothesis…*.
