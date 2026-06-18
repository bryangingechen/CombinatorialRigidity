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
(route OPEN, OD-8); its **standard-frame** base case `complementIso_exteriorPower_basis_eq_smul_compl`,
standard-frame **range-membership** `complementIso_exteriorPower_basis_mem_range_map_subtype`, the
**O(n)-equivariance** `complementIso_map_orthogonal_eq` (h-1), and the **frame-alignment transport
bridge** `EuclideanSpace.{inner_eq_basisFun_toDual, toDualOrthogonal_ofLinearIsometryEquiv}` (h-2,
new Analysis mirror) have landed (2026-06-17), leaving the **(h-2) Gram–Schmidt span-control
existence** + **general-decomposable assembly** (h-3) of the lift — both to live in a NEW DOWNSTREAM
file (`PiL2` poisons metric-free `Meet.lean`, QUIRKS § 59); the final assembly then reuses the THREE
landed `_grade` bricks (zero new count). The integer Phase 23 stays **in progress** — ENTRY /
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

**CHAIN-3's OD-8 route-(α) (h-3) input-side proportionality has LANDED (2026-06-17, this commit) —
two metric-free bricks in `Meet.lean`.** Building the (h-3) assembly surfaced a step the design
doc's §(h) prose glossed (`extensor n = c • blade` as if trivial): the panel-meet input `extensor n`
(grade-2 in ambient `Fin (k+2)`) must be matched — up to a nonzero scalar — to the `2`-extensor of
the *orthonormal* pair an orthogonal change-of-frame carries to a coordinate blade, and that needed a
genuine proportionality lemma plus a grade-decoupled membership brick:
- `exists_smul_extensor_eq_of_mem_span_range` (the input proportionality leaf): for `v : Fin 2 →
  Fin (d+1) → ℝ` independent and `u : Fin 2 → …` with both vectors in `span(range v)`,
  `∃ c, c • extensor v = extensor u`. Both extensors lie in the line `range(map 2 P.subtype)`
  (`P = span(range v)`, `dim 2`, so `⋀²P` is a line via `finrank_exteriorPower_self_eq_one`), with
  `extensor v ≠ 0`; close by the same line-proportionality idiom as
  `exists_smul_eq_of_mem_range_map_subtype_grade`. Grade-2-specific (count needs grade = `dim P = 2`);
  ambient `Fin (d+1)` general (the `Fin (k+2)` site is `d := k+1`).
- `extensor_mem_range_map_subtype_of_mem_jgrade` (the prerequisite): `extensor_mem_range_map_subtype_
  of_mem_grade` with the grade `j` **decoupled** from the ambient `d` (the `_grade` form ties it to
  `d − 1`; grade `2 ≠ (k+1)−1 = k`). Proof verbatim; `_grade` re-derived as the `j := d−1` instance
  (signature unchanged, callers untouched — the line-1517/d:=k+1 + d=3 instances both still close).

Both metric-free, in `Meet.lean`. Gates green (full build + lint clean, no warnings/sorry).

**(h-2) recap (landed prior commit).** `exists_orthonormalBasis_span_pair_eq` (`MeetHodge.lean`): for
a linearly independent pair `n : Fin 2 → EuclideanSpace ℝ (Fin (k+2))`, an `OrthonormalBasis` whose
first two vectors span `span{n 0, n 1}` (Gram–Schmidt on the zero-extended family). Its `b.repr` is
the frame-alignment L²-isometry the LANDED transport bridge
`EuclideanSpace.toDualOrthogonal_ofLinearIsometryEquiv` converts to the `toDual`-orthogonal `O` that
(h-1) `complementIso_map_orthogonal_eq` consumes.

**Architectural finding (cost a build cycle; → TACTICS-QUIRKS § 59 + FRICTION).** Importing
`Mathlib.Analysis.InnerProductSpace.PiL2` into the metric-free `Meet.lean` **regresses a
pre-existing untouched proof** (`complementIso_smul_eq_extensor_join`) to a `whnf` timeout — the
`PiLp 2`/`EuclideanSpace` instances on `Fin (k+2) → ℝ` become defeq-visible to `⋀`-term
elaboration. **Decision: the metric-using Hodge leaves ((h-2) Gram–Schmidt construction, (h-3))
must live in a NEW DOWNSTREAM file** (imports `Meet.lean` + the metric layer), never in `Meet.lean`;
pure `EuclideanSpace`↔`toDual` glue stays in the mirror. The (h-1) O(n)-equivariance
`complementIso_map_orthogonal_eq` stays green in `Meet.lean` (landed prior commit).

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
            - [ ] (h-3) **assembly** `complementIso_extensor_mem_range_map_subtype` (`MeetHodge.lean`) —
              compose the input proportionality (this commit) with (h-1) O(n)-equivariance + (h-2)
              `exists_orthonormalBasis_span_pair_eq` + the LANDED standard-frame membership + the
              range-pushforward (validated in scratch: `O(W')⊆W ⟹ map g O sends range(map g W'.subtype)
              into range(map g W.subtype)`, via `LinearMap.subtype_comp_codRestrict` + `map_comp`).
              **Remaining untested risk = the `W = {n}^⊥` dimension argument** (`hWperp` + `hWdim=k` ⟹
              `W = {n}^⊥` so `b̄ i ∈ W` for `i ≥ 2`); the cleanest handle is
              `Submodule.finrank_add_finrank_orthogonal` transported across `EuclideanSpace.equiv` via
              `inner_eq_basisFun_toDual`. `extensor n = 0` case trivial. Route β rejected (withdrawn
              `dim Φ̃` count).
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
  (`screwAlgebraTopEquiv (map f ·) = det f · …` — LANDED `screwAlgebraTopEquiv_map_eq_det_smul`),
  (h-1) `complementIso_map_orthogonal_eq` — **the O(n)-equivariance, the substantive new leaf +
  clause-(ii) flag — now LANDED** (Hodge `⋆` is O(n)-natural not GL-natural; assembled from the two
  transformation halves by `toDual`-injectivity), (h-2) orthonormal alignment of `span{n_u,n'}` to a
  coordinate plane (Gram–Schmidt — **the next open leaf**), (h-3) assemble with the LANDED
  standard-frame membership, (h-4) the assembly.
  **No missing mathlib *API*** (clause (ii)); the one genuinely-new *project* sub-lemma (h-1) is now
  closed. **Genuine fallback if (h-2) is a long pole:** carry (h-3) as an explicit
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

**Next buildable sub-step = (h-3) the *assembly* `complementIso_extensor_mem_range_map_subtype`**
(signature §(f) item 2), in `Molecular/MeetHodge.lean`:
`complementIso (j:=2) ⟨extensor n,_⟩ ∈ range(exteriorPower.map k W.subtype)` for `W` with
`hWperp : W ⊆ {n}^⊥` and `hWdim : finrank W = k`. The full leaf chain (h-0)…(h-2) **and** the (h-3)
input proportionality (this commit) are LANDED; the remaining work is the metric composition. Plan,
all ingredients in hand:
1. `extensor n = 0` (dependent `n`): `complementIso 0 = 0 ∈ range` trivially.
2. `n`-independent case. Get `b := exists_orthonormalBasis_span_pair_eq n` (`span{b 0,b 1} =
   span{n}`); set `O := (EuclideanSpace.ofLinearIsometryEquiv b.repr.symm).toLinearMap` —
   `O (Pi.basisFun _ i) = ⇑(b i)` (probed: `rw [EuclideanSpace.ofLinearIsometryEquiv]; simp` after
   unfolding), `toDual`-orthogonal by the LANDED `toDualOrthogonal_ofLinearIsometryEquiv`.
3. `W = {n}^⊥` (the one untested step): `hWperp` gives `W ⊆ {n}^⊥`, `hWdim` + `finrank {n}^⊥ = k`
   (via `Submodule.finrank_add_finrank_orthogonal` transported across `EuclideanSpace.equiv` using
   `inner_eq_basisFun_toDual`, `finrank span{n} = 2`) ⟹ `W = {n}^⊥`; hence `b̄ i ∈ W` for `i ≥ 2`
   (`b i ⊥ b 0,b 1`, orthonormal). So `O(coordinate-complement) ⊆ W`.
4. Input proportionality (this commit): `extensor n = c • map 2 O (e_{01})` (since
   `map 2 O e_{01} = extensor ![b̄0,b̄1]`, same plane). `complementIso` linearity + submodule-`•`
   absorb `c`.
5. (h-1) `complementIso_map_orthogonal_eq` pushes `complementIso` through `O`; the LANDED
   standard-frame membership `complementIso_exteriorPower_basis_mem_range_map_subtype` gives the
   coordinate-blade case; the **range-pushforward** (validated in scratch this session, reusable —
   consider lifting to `Meet.lean`: `O(W')⊆W ⟹ map g O sends range(map g W'.subtype) into
   range(map g W.subtype)` via `LinearMap.subtype_comp_codRestrict` + `exteriorPower.map_comp`)
   transports to `range(map k W.subtype)`.
Watch the `EuclideanSpace`↔`Fin (k+2)→ℝ` carrier round-trip feeding `O` into (h-1) (whose `hO` is
`toDual`-orthogonality).

The full OD-8 route-(α) leaf chain (§(h)), now (h-0)…(h-2) + (h-3)-input all LANDED:
- **(h-0)** volume-form-by-determinant — **LANDED** (`screwAlgebraTopEquiv_map_eq_det_smul` + mirror
  `exteriorPower.topEquiv_map_eq_det_smul`).
- **(h-1)** `complementIso_map_orthogonal_eq` — **the substantive new leaf — LANDED** (`Meet.lean`).
- **(h-2)** frame alignment — **transport bridge + span-control existence LANDED**
  (`EuclideanSpace.{inner_eq_basisFun_toDual, toDualOrthogonal_ofLinearIsometryEquiv}` mirror +
  `exists_orthonormalBasis_span_pair_eq`, `MeetHodge.lean`).
- **(h-3) input proportionality** — **LANDED this commit** (`exists_smul_extensor_eq_of_mem_span_range`
  + `extensor_mem_range_map_subtype_of_mem_jgrade`, `Meet.lean`).
- **(h-3) assembly** `complementIso_extensor_mem_range_map_subtype` — **the next open leaf** (the
  metric composition; the `W = {n}^⊥` dimension step is the one untested piece).

**Why NOT route β:** the in-hand annihilation (`complementIso_toDual_eq_zero_of_wedgeProd_eq_zero`)
puts `complementIso n` in an annihilator `Ann(Φ)`; upgrading that to range-membership needs
`dim Ann(Φ) = 1`, i.e. the **withdrawn `dim Φ̃` count** (`= C(d−1,2) > 1` for `d≥4`). So β is
**rejected, not a fallback**. **Genuine fallback if the (h-3) assembly is a long
pole:** carry (h-3) as an explicit green-modulo `h…` premise on CHAIN-4's discriminator (standing
idiom), land it in a dedicated sitting — never a `sorry`. (`MeetHodge.lean`; still no
ENTRY-contract dependency.)

The CHAIN-3-finish recon's geometry (the `⋀^{d−1}W`-is-a-line route, NOT the withdrawn d=3-only `Φ̃`
route — a line has **2** normals + **d−1** points at every `d`) is recorded in *Decisions made* and
lives canonically in `notes/Phase23-design.md` §"CHAIN"(f)/(h). Closing the (h-3) assembly + the
(h-4) `extensor_join_proportional_complementIso_meet` (zero new count, consumes (h-3) + the three
`_grade` bricks) closes CHAIN-3 and feeds CHAIN-4's discriminator; the d=3 wrapper stays green (h-5).

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
  `extensor_mem_range_map_subtype_of_mem_jgrade` (`Meet.lean`). Building the assembly surfaced a step
  §(h) glossed: `extensor n` must be matched up-to-scalar to the `2`-extensor of the orthonormal frame
  pair. The proportionality reuses the line-is-1-dim idiom (`finrank_exteriorPower_self_eq_one` at
  grade 2 = `dim P`) of `exists_smul_eq_of_mem_range_map_subtype_grade`; the prerequisite **decouples**
  the grade `j` from the ambient `d` in `extensor_mem_range_map_subtype_of_mem_grade` (which tied it to
  `d−1`; grade `2 ≠ k`). `_grade` re-derived as the `j := d−1` instance, signature + callers untouched.
  Both metric-free.

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
