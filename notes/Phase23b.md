# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. CHAIN-3's three `_grade` bricks + the entire OD-8 route-(α) leaf chain (h-0…h-3)
have landed. **The OD-8 crux — the panel-meet range-membership `complementIso_extensor_mem_range_map_
subtype` (h-3, `MeetHodge.lean`) — is now CLOSED** (2026-06-17): `complementIso (j:=2) ⟨extensor n,_⟩
∈ range(⋀^k W ↪)` for `W = {n 0, n 1}^⊥`, via the orthogonal change-of-frame route (`complementIso`
is the Hodge `⋆`). The **only remaining CHAIN-3 leaf** is the assembly **(h-4)
`extensor_join_proportional_complementIso_meet`** (the per-line join=meet duality, **zero new count**:
reuses the three landed `_grade` bricks + the (h-3) leaf — point-join + panel-meet both in the line
`range(⋀^{d−1}W ↪)`). CHAIN-3's route is the **`⋀^{d−1}W`-is-a-line** route (point-join `d−1` points +
panel-meet 2 normals) of the CHAIN-3-finish recon (`notes/Phase23-design.md` §"CHAIN"(f)/(g)/(h)),
which **withdrew** the dead d=3-only `Φ̃` route (`finrank_sup_range_wedgeFixedLeft` /
`extensor_toDual_extensor_eq_zero_of_perp` + `wedgeFixedLeft` / `inf_range_wedgeFixedLeft` stay green
at d=3, do NOT generalize: `dim Ω = C(d−1,2) = 1` only at `d=3`). After (h-4), CHAIN-1/2/4/5 remain
(CHAIN-5 gated by the ENTRY-contract reshape). The integer Phase 23 stays **in progress** — ENTRY /
ASSEMBLY remain (coordinator owns the sub-phase boundary; codes-until-open).

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

**CHAIN-3's OD-8 route-(α) (h-3) panel-meet range-membership leaf `complementIso_extensor_mem_range_
map_subtype` has LANDED (2026-06-17, this commit) — the OD-8 crux is now fully closed.** This was the
one genuinely-new leaf of the CHAIN-3 finish: `complementIso (j:=2) ⟨extensor n,_⟩ ∈ range(map k
W.subtype)` for `W = {n 0, n 1}^⊥` (`hWperp` + `hWdim = k`). Proved in `MeetHodge.lean` by the
orthogonal change-of-frame route (`complementIso` is the Hodge `⋆`, O(n)-natural not GL-natural):
the Gram–Schmidt frame `b` (h-2) aligns `span{n 0, n 1}` to the coordinate `2`-plane, the frame map
`O = ofLinearIsometryEquiv b.repr.symm` carries `extensor n` to the coordinate blade (up to scalar,
via the input proportionality `exists_smul_extensor_eq_of_mem_span_range`) and the coordinate
complement into `W`, so the LANDED standard-frame membership transports through `O` by (h-1)
`complementIso_map_orthogonal_eq` + the new metric-free range-pushforward
`exteriorPower_map_mem_range_map_subtype_of_mapsTo` (`Meet.lean`). The `W = {n 0,n 1}^⊥` dimension
step: `W ≤ Q` (the `toDual`-perp), both `k`-dim (`Q` via `Submodule.finrank_add_finrank_orthogonal`
transported across `EuclideanSpace.equiv` by `inner_eq_basisFun_toDual` + `real_inner_comm`), so
`W = Q`. `extensor n = 0` (dependent) case trivial. Gates green (full build + lint clean,
no warnings/sorry).

**Next buildable sub-step = (h-4) the assembly `extensor_join_proportional_complementIso_meet`**
(signature §(f) item 1, `notes/Phase23-design.md`) — the per-line point-join↔panel-meet duality, in
`MeetHodge.lean` (consumes the (h-3) leaf, so downstream of the metric layer). **Zero new count**: the
`⋀^{d−1}W`-is-a-line route reuses the three LANDED `_grade` bricks (`extensor_mem_range_…_grade`,
`exists_smul_eq_…_grade`, `exteriorPower_map_subtype_injective_grade`) — point-join (`k = d−1` points)
and panel-meet (the (h-3) leaf) both land in the line `range(⋀^k W ↪)`, proportional. Closing (h-4)
closes CHAIN-3 and feeds CHAIN-4's discriminator; the `d=3` `complementIso_smul_eq_extensor_join`
stays green as the wrapper (h-5).

**Prior-commit recaps (one-line; full bricks landed):** (h-2) `exists_orthonormalBasis_span_pair_eq`
(Gram–Schmidt span-control, `MeetHodge.lean`) + transport bridge `EuclideanSpace.{inner_eq_basisFun_
toDual, toDualOrthogonal_ofLinearIsometryEquiv}` (mirror); (h-3)-input `exists_smul_extensor_eq_of_mem_
span_range` + `extensor_mem_range_map_subtype_of_mem_jgrade` (`Meet.lean`); (h-1)
`complementIso_map_orthogonal_eq`; (h-0) `screwAlgebraTopEquiv_map_eq_det_smul`.

**Architectural constraint (standing).** The metric-using Hodge leaves live in `MeetHodge.lean`, never
`Meet.lean`: importing `Mathlib.Analysis.InnerProductSpace.PiL2` into the metric-free `Meet.lean`
regresses `complementIso_smul_eq_extensor_join` to a `whnf` timeout (TACTICS-QUIRKS § 59). Pure
`EuclideanSpace`↔`toDual` glue stays in the `Mathlib/` mirror; (h-4) also belongs in `MeetHodge.lean`.

**(h-1) recap (landed prior commit).** O(n)-equivariance of `complementIso` (the Hodge `⋆`): for
orthogonal `O` (`hO : ∀ x y, b.toDual (O x)(O y) = b.toDual x y`),
`complementIso hj (map j O X) = det O • map (k+2−j) O (complementIso hj X)`, assembled by
`(b.exteriorPower (k+2−j)).toDual`-injectivity from the two transformation halves.

**Next buildable sub-step = (h-2) the Gram–Schmidt span-control existence** — an
`OrthonormalBasis (Fin (k+2)) ℝ (EuclideanSpace ℝ (Fin (k+2)))` whose first two vectors span a
prescribed independent pair `{n₀,n₁}` (so `b.repr` is the frame-alignment isometry, and
`EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` converts it to the `toDual`-orthogonal `O`).
Build via `gramSchmidtOrthonormalBasis` on a family whose first two entries are `n₀,n₁`
(`span_gramSchmidt_Iic` + `gramSchmidtOrthonormalBasis_apply` on the nonzero-`gramSchmidtNormed`
initial segment); **must live in the new downstream file** per the finding above. Then (h-3) the
target leaf `complementIso_extensor_mem_range_map_subtype` assembles (h-1)+(h-2)+the LANDED
standard-frame membership `complementIso_exteriorPower_basis_mem_range_map_subtype`; then the assembly
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
            - [x] **(h-1) `complementIso_map_orthogonal_eq` — the substantive new leaf + clause-(ii)
              flag — LANDED 2026-06-17.** O(n)-equivariance of `complementIso` (the Hodge `⋆`):
              `complementIso hj (map j O X) = det O • map (k+2−j) O (complementIso hj X)` for `O`
              orthogonal (`hO : ∀ x y, b.toDual (O x)(O y) = b.toDual x y`). Assembled by
              `(b.exteriorPower (k+2−j)).toDual`-injectivity from the two landed transformation halves
              (the *join/volume* half `wedgePairing_map` scaling by `det O`, the *dot-product* Gram-
              O-invariance `exteriorPower_basis_toDual_map_orthogonal_eq`): `O` orthogonal ⟹ injective
              (`hO`+`toDual_injective`) ⟹ surjective ⟹ `map O` surjective, so pair against
              `B = map O B'`; both sides collapse to `det O • wedgePairing X B'` via `complementIso_toDual`.
              Grade-generic `{j}`; no `d=3` pin, no new mathlib fact.
            - [◐] (h-2) frame alignment — split into the metric→`toDual` transport bridge (LANDED
              2026-06-17) + the Gram–Schmidt span-control existence (next).
              - [x] **transport bridge** `EuclideanSpace.inner_eq_basisFun_toDual` +
                `EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` (new mirror
                `Mathlib/Analysis/InnerProductSpace/PiL2.lean`): L²-inner = `toDual` dot-product
                pairing, so an L²-`LinearIsometryEquiv` transports to a `toDual`-orthogonal equiv of
                `ι → ℝ` — the `hO`-feeder for (h-1). Axiom-clean. Landed 2026-06-17.
              - [x] **span-control existence** `exists_orthonormalBasis_span_pair_eq` — an
                `OrthonormalBasis (Fin (k+2)) ℝ (EuclideanSpace …)` whose first two vectors span
                `{n₀,n₁}` (via `gramSchmidtOrthonormalBasis` + `span_gramSchmidtNormed` +
                `span_gramSchmidt_Iic`; per-index nonzero from `linearIndepOn_range_iff` +
                `linearIndependent_restrict_iff`). Lives in the NEW DOWNSTREAM file
                `Molecular/MeetHodge.lean` (`PiL2` cannot import into metric-free `Meet.lean`,
                TACTICS-QUIRKS § 59). Landed 2026-06-17.
              - [x] **(h-3) input proportionality** `exists_smul_extensor_eq_of_mem_span_range` +
                prerequisite `extensor_mem_range_map_subtype_of_mem_jgrade` (`Meet.lean`, this commit).
                Lets `extensor n` be replaced (up to scalar) by the `2`-extensor of the orthonormal
                frame pair spanning the same plane. Both metric-free. See *Current state*.
            - [x] (h-3) **assembly** `complementIso_extensor_mem_range_map_subtype` (`MeetHodge.lean`) —
              LANDED 2026-06-17. Composes input proportionality + (h-1) O(n)-equivariance + (h-2)
              `exists_orthonormalBasis_span_pair_eq` + the LANDED standard-frame membership + the new
              metric-free range-pushforward `exteriorPower_map_mem_range_map_subtype_of_mapsTo`
              (`Meet.lean`, `LinearMap.subtype_comp_codRestrict` + `exteriorPower.map_comp`). The
              `W = {n}^⊥` dimension argument discharged via `Submodule.finrank_add_finrank_orthogonal`
              transported to the `toDual`-perp `Q` across `EuclideanSpace.equiv` (`inner_eq_basisFun_toDual`
              + `real_inner_comm`): `W ≤ Q`, both `k`-dim, so `W = Q`; `extensor n = 0` case trivial.
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

- **OD-8 — RESOLVED 2026-06-17.** The panel-meet range-membership
  `complementIso(j:=2)⟨n_u∧n',_⟩ ∈ range(⋀^k W ↪)` for `W = {n_u,n'}^⊥` is CLOSED via route α
  (the entire leaf chain h-0…h-3 LANDED): `complementIso` IS the Hodge `⋆`, O(n)-natural; the
  target transports the standard-frame membership along an orthogonal change of frame. Route β
  stays **rejected** (the annihilation→membership upgrade is the withdrawn `dim Φ̃` count
  `= C(d−1,2) > 1` for `d≥4`). Full text `notes/Phase23-design.md` §"CHAIN"(h); landed leaf in
  *Decisions made* below.
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

**Next buildable sub-step = (h-4) the assembly `extensor_join_proportional_complementIso_meet`**
(signature §(f) item 1, `notes/Phase23-design.md`), in `Molecular/MeetHodge.lean` (consumes the (h-3)
leaf, so downstream of the metric layer). The per-line point-join↔panel-meet duality:
`∃ c, c • complementIso (j:=2) ⟨extensor n,_⟩ = ⟨extensor p,_⟩` for `n` the two line-normals and
`p : Fin k → …` the `k = d−1` points spanning the line (`hperp : toDual (p i) (n j) = 0`). **Zero new
count** — the `⋀^{d−1}W`-is-a-line route, all ingredients LANDED:
1. `W := {n 0, n 1}^⊥` (`dim k`); point-join `⟨extensor p,_⟩ ∈ range(⋀^k W ↪)` by
   `extensor_mem_range_map_subtype_of_mem_grade` (each `p i ∈ W` from `hperp`; `(d := k+1)` form).
2. Panel-meet `complementIso ⟨extensor n,_⟩ ∈ range(⋀^k W ↪)` by **(h-3)
   `complementIso_extensor_mem_range_map_subtype`** (this commit) — needs `hWperp` (`W ⊆ {n}^⊥`,
   immediate) + `hWdim = k` (from `hperp` giving the `p` independent in `W`, `dim W = k`).
3. Point-join `≠ 0` by `hp` + `extensor_ne_zero_iff_linearIndependent`; close by
   `exists_smul_eq_of_mem_range_map_subtype_grade` (`(d := k+1)` form) — the line-proportionality.
The `d=3` `complementIso_smul_eq_extensor_join` then becomes `:= …_meet (k := 2) …` (or stays as the
green wrapper — re-point is a CHAIN-4 decision, not forced; h-5).

Closing (h-4) **closes CHAIN-3** and feeds CHAIN-4's discriminator
(`exists_complementIso_ne_zero_of_homogeneousIncidence`) the join=meet proportionality (the step KT
leaves implicit — a BlueprintExposition-grade node, ledger candidate). **Route β stays rejected**
(the annihilation→membership upgrade is the withdrawn `dim Φ̃` count); **genuine fallback** if (h-4)
is a long pole: carry it as an explicit green-modulo `h…` premise on CHAIN-4, never a `sorry`. Still
no ENTRY-contract dependency.

The full OD-8 route-(α) leaf chain (§(h)) is now **(h-0)…(h-3) all LANDED**: (h-0)
`screwAlgebraTopEquiv_map_eq_det_smul`; (h-1) `complementIso_map_orthogonal_eq`; (h-2)
`exists_orthonormalBasis_span_pair_eq` + transport bridge; (h-3)-input
`exists_smul_extensor_eq_of_mem_span_range`; (h-3) assembly `complementIso_extensor_mem_range_map_subtype`
(`MeetHodge.lean`, this commit). The CHAIN-3-finish geometry (the `⋀^{d−1}W`-is-a-line route, NOT the
withdrawn d=3-only `Φ̃` route) lives canonically in `notes/Phase23-design.md` §"CHAIN"(f)/(h).

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
- **OD-8 RESOLVED: route α (`complementIso` O(n)-equivariance); β rejected** — the whole
  leaf chain h-0…h-3 landed, the panel-meet range-membership is closed. `complementIso` IS the
  Hodge `⋆`; β rests on the withdrawn `dim Φ̃` count → §"CHAIN"(h).

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
  → (h-1a) `wedgeProd_map`/`wedgePairing_map` (volume/join half, on mirror
  `map_coe_eq_exteriorAlgebra_map`) → (h-1b) `exteriorPower_basis_toDual_map_orthogonal_eq` (the
  dot-product Gram-O-invariance: through the N3b-recon Gram determinant `pairingDual_ιMulti_ιMulti`,
  `hO` collapses each entry, lifted off decomposables by a double `LinearMap.ext_on` over the `ιMulti`
  generators; grade-/ambient-generic, no new mathlib fact) → (h-1) `complementIso_map_orthogonal_eq`
  (the O(n)-equivariance: assembled from h-1a+h-1b by `(b.exteriorPower (k+2−j)).toDual`-injectivity,
  `O` orthogonal ⟹ injective ⟹ surjective ⟹ `map O` surjective; grade-generic `{j}`). The
  general-decomposable case (h-3) is NOT a GL-equivariance corollary (`complementIso` is Hodge, O(n)-
  not GL-natural) — the remaining route is (h-2) frame alignment + (h-3) the assembly.
- (h-2) **metric→`toDual` transport bridge** (new mirror
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean`): `EuclideanSpace.inner_eq_basisFun_toDual` (L²
  inner = standard-basis `toDual` dot-product pairing through `EuclideanSpace.equiv`) +
  `EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` (an L²-`LinearIsometryEquiv` transports to
  a `toDual`-orthogonal equiv of `ι → ℝ` — the `hO`-feeder for (h-1)). Axiom-clean, self-contained
  (no exterior-algebra dep, copy-paste-promotable). The metric-vs-algebraic "orthogonal"
  reconciliation.
- (h-2) **Gram–Schmidt span-control existence** `exists_orthonormalBasis_span_pair_eq` (new
  downstream file `Molecular/MeetHodge.lean`): an `OrthonormalBasis` of `EuclideanSpace ℝ (Fin (k+2))`
  whose first two vectors span an independent pair `{n₀,n₁}`. `gramSchmidtOrthonormalBasis` on the
  zero-extended family; the span chain runs `{b 0,b 1} → gramSchmidtNormed f '' Iic 1` (nonzero via
  `gramSchmidtNormed_unit_length_coe`) `→ span(gramSchmidt f '' Iic 1)` (`span_gramSchmidtNormed`)
  `→ span(f '' Iic 1)` (`span_gramSchmidt_Iic`) `→ span{n₀,n₁}`. Per-index nonzero hyp from
  `LinearIndepOn ℝ f (Iic 1)` = `hn` reindexed (`linearIndepOn_range_iff` on `![0,1]` +
  `linearIndependent_restrict_iff`). `MeetHodge.lean` wired into `CombinatorialRigidity.lean`.
- (h-3) **input proportionality** `exists_smul_extensor_eq_of_mem_span_range` + prerequisite
  `extensor_mem_range_map_subtype_of_mem_jgrade` (`Meet.lean`). `extensor n` matched up-to-scalar to
  the `2`-extensor of the orthonormal frame pair (line-is-1-dim idiom `finrank_exteriorPower_self_eq_one`
  at grade 2); prerequisite **decouples** the grade `j` from the ambient `d` in `…_of_mem_grade`
  (`_grade` re-derived as the `j := d−1` instance, callers untouched). Both metric-free.
- (h-3) **assembly** `complementIso_extensor_mem_range_map_subtype` (`MeetHodge.lean`, this commit) —
  the OD-8 crux. `complementIso (j:=2) ⟨extensor n,_⟩ ∈ range(⋀^k W ↪)`, `W = {n 0,n 1}^⊥`. The
  orthogonal change-of-frame: `b := exists_orthonormalBasis_span_pair_eq` aligns `span{n 0,n 1}` to the
  coordinate plane, `O := ofLinearIsometryEquiv b.repr.symm` (`toDual`-orthogonal via the transport
  bridge) sends the coordinate complement into `W` and the coordinate blade to `extensor ![bf 0,bf 1]`
  (∝ `extensor n`); push the LANDED standard-frame membership through `O` by (h-1)
  `complementIso_map_orthogonal_eq` + the new metric-free **range-pushforward**
  `exteriorPower_map_mem_range_map_subtype_of_mapsTo` (`Meet.lean`,
  `LinearMap.subtype_comp_codRestrict` + `exteriorPower.map_comp`). `W = {n 0,n 1}^⊥` dimension step:
  `W ≤ Q` (the `toDual`-perp), both `k`-dim (`Q` via `finrank_add_finrank_orthogonal` transported across
  `EuclideanSpace.equiv` by `inner_eq_basisFun_toDual` + `real_inner_comm`), so `W = Q`. Two FRICTION
  idioms surfaced (`span_induction` on an applied subject; `EuclideanSpace.equiv` is a CLE). No
  blueprint pin (intermediate brick; the duality node `lem:case-III-claim612-line-in-panel-union`
  stays green via its d=3 route until (h-4) lands the general one).

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
- *`set b := e` folds `e` out of the goal too, so a later `rw`/`simp only [lib_lemma]`
  whose LHS pattern mentions `e` silently fails (`simp only` reports args "unused") —
  the goal-side / library-lemma variant of the `set` fold; drop the `set`* →
  TACTICS-QUIRKS § 43 (goal-side / library-lemma variant).
- *A new `InnerProductSpace`/`EuclideanSpace` import poisons a pre-existing exterior-algebra proof
  in the same file to a `whnf` timeout (the `PiLp 2` instances become defeq-visible to `⋀`-term
  elaboration) — keep the bridge in a `Mathlib/` mirror, house metric-using leaves in a downstream
  file* → TACTICS-QUIRKS § 59 / FRICTION [mirrored] *`EuclideanSpace.inner_eq_basisFun_toDual`…*.
- *`induction h using Submodule.span_induction` fails on an applied membership subject (`n j`) —
  hoist a `∀ y ∈ span, …` helper, induct on the bound `y`* → FRICTION [idiom] *`induction h using
  Submodule.span_induction` fails …*.
- *`EuclideanSpace.equiv` is a `ContinuousLinearEquiv`, not a `LinearEquiv` — round-trips need the
  `ContinuousLinearEquiv.*` forms (a `LinearEquiv.apply_symm_apply` `simp only` no-ops)* → FRICTION
  [idiom] *`EuclideanSpace.equiv` is a `ContinuousLinearEquiv`…*.
