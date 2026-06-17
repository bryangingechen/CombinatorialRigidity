# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open (docs-only phase-open + detailed leaf-level recon, 2026-06-17).
No CHAIN Lean leaf built yet. The integer Phase 23 stays **in progress** —
ENTRY / ASSEMBLY remain (coordinator owns the sub-phase boundary; codes-until-open).

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

**CHAIN is open on a detailed leaf-level recon (no build).** The recon
(`notes/Phase23-design.md` §"CHAIN") source-verified — against KT §6.4.2 (eqs.
6.46–6.67, read end-to-end) and the landed tree — that **the arm-realization
engine is already general-`k`** (the M₁/M₂/M₃ closers `case_III_arm_realization`
/ `_M2` / `_M3` in `CaseIII/{Arms,Relabel}.lean` were authored `(k:ℕ)`); the
genuinely-`d=3` surface is **only the dispatch** (`case_III_candidate_dispatch`,
`Realization.lean:201`) — its fixed-3-candidate count + the `⋀²ℝ⁴` discriminator
(`exists_homogeneousIncidence_of_normals` / `…complementIso…` in `Claim612.lean`,
the `Meet.lean` duality lemmas). CHAIN's job: replace that dispatch with the
`d`-candidate chain dispatch + the `⋀^{d−1}(ℝ^{d+1})` duality finish.

**The load-bearing flag (recon (b)).** The 23a-carried `hdispatch`
(`Theorem55.lean:2225`) takes a **fixed `v,a,b,c` 4-tuple**, faithful at `d=3`
(the chain `v₀v₁v₂v₃` *is* `c—a—v—b`) but **too short at `d≥4`** — KT's general-`d`
Lemma 6.13 needs the whole length-`d` chain. So CHAIN is **not** a pure
"discharge `hdispatch` at general `k`": the producer/extractor supplying its
premises (`exists_chain_data_of_noRigid` → `case_III_hsplit_producer_all_k`) must
be reshaped to extract+pass a length-`d` chain, which **couples CHAIN to ENTRY**
(the chain-data record is the CHAIN↔ENTRY contract). Co-design the
`hdispatch`/`hcand` signature with ENTRY; do **not** freeze the dispatch
signature before the chain-data shape is agreed. This is a genuine motive/
producer-shape change, surfaced for coordinator/user adjudication (recon (b)).

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)). Five leaves, **one** sub-phase (OD-6).
CHAIN-1/3 are buildable now (no ENTRY-contract dependency); CHAIN-5 is gated by
the (b) flag (its signature is the CHAIN↔ENTRY contract).

- [ ] **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks** (`Meet.lean`).
      Re-state `extensor_mem_range_map_subtype_of_mem`,
      `exists_smul_eq_of_mem_range_map_subtype`,
      `exteriorPower_basis_toDual_eq_pairingDual_comp_map`,
      `complementIso_smul_eq_extensor_join` at `⋀[ℝ]^{d−1}(Fin (d+1)→ℝ)` with the
      general `finrank(⋀^{d−1}W)=(finrank W).choose (d−1)`. Build LAZILY at
      concrete grade — NO general Hodge-star. **First buildable leaf (see
      Hand-off);** unblocks CHAIN-4 + the four-producer lift (OD-7).
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
      **Gated by the (b) flag** — signature = CHAIN↔ENTRY contract. Keep the
      `d=3` dispatch as a `k=2`/length-3 wrapper (no `d=3` regression).
- [ ] **CHAIN tail — lift the four 23a-carried producers** (OD-7 fold). After
      CHAIN-3: `hforget_k` (M4 forget, `exists_extensor_eq_panelSupportExtensor`
      routes through CHAIN-3's duality), then through it `hbase_k`/`hcut_k`/
      `hcontract_k`. Direct corollary of CHAIN-3 + numeral pass — caveat (e)
      OD-7: confirm the *only* genuinely-`d=3` reach-in is the duality at build.

## Blockers / open questions

The OD resolutions (full text in `notes/Phase23-design.md` §"CHAIN"(e)):

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
- **(b) producer-shape mismatch — FLAGGED (motive/producer-level).** The
  `hdispatch` carry is a fixed 4-tuple; general `d` needs a length-`d` chain →
  the producer/extractor must reshape, coupling CHAIN to ENTRY. The dispatch
  signature is the CHAIN↔ENTRY contract; co-design it at CHAIN open. *For
  coordinator/user adjudication* (recon (b)/(e)OD-1).
- **OD-1 (re-confirmed for CHAIN/ENTRY).** KT Lemma 5.4 short-cycle base is a
  real branch of the general-`d` chain entry (unlike `d=3`'s inline triangle
  floor); whether CHAIN's dispatch assumes the chain branch (ENTRY discharging
  the cycle branch) is an ENTRY-contract question.

## Hand-off / next phase

**First buildable CHAIN leaf = CHAIN-3, sub-leaf the dimension-generic range
membership** (no ENTRY-contract dependency; unblocks CHAIN-4 + the four-producer
lift). The cleanest grounded first commit re-states the `Meet.lean:648`
membership brick at general grade:

```
theorem extensor_mem_range_map_subtype_of_mem_grade {d : ℕ}
    (W : Submodule ℝ (Fin (d + 1) → ℝ)) (v : Fin (d - 1) → Fin (d + 1) → ℝ)
    (hv : ∀ i, v i ∈ W) :
    (⟨extensor v, extensor_mem_exteriorPower v⟩ : ⋀[ℝ]^(d - 1) (Fin (d + 1) → ℝ))
      ∈ LinearMap.range (exteriorPower.map (d - 1) W.subtype)
```

The `d=3` `extensor_mem_range_map_subtype_of_mem` (`W : Submodule ℝ (Fin 4 → ℝ)`,
`v : Fin 2 → …`, `⋀[ℝ]^2`) becomes the `d=3` instance (`d−1 = 2`, `d+1 = 4`).
The proof is grade-generic verbatim (`exteriorPower.map_apply_ιMulti` +
`exteriorPower.ιMulti_apply_coe` + `Subtype.ext`/`rfl`; no `finrank` count, no
`fin_cases`) — it is the easiest CHAIN-3 sub-leaf and a clean first contact with
the symbolic-grade exterior-algebra surface. Then the proportionality engine
`exists_smul_eq_of_mem_range_map_subtype` needs the genuine new count
`finrank(⋀^{d−1}W) = (finrank W).choose (d−1)` (`exteriorPower.finrank_eq`; at
`finrank W = d−1`, `= 1`) — the real arithmetic of CHAIN-3.

**Build-recon gate before CHAIN-5 (the dispatch):** the detailed-build recon
must first agree the **length-`d` chain-data record** with ENTRY (the (b) flag);
CHAIN-5's `hdispatch`/`hcand` signature is that contract, so do not author it
before. CHAIN-1/3/4 are buildable independently of that contract.

**Green-modulo boundary CHAIN hands downstream** (`notes/Phase23-design.md`
§"CHAIN"(d)): CHAIN discharges the general-`k` `hdispatch` (modulo the (b)
reshape it co-owns with ENTRY) and lifts the four producers (OD-7). **ENTRY**
owns the length-`d` chain extraction (reshaped `exists_chain_data_of_noRigid`,
Lemma 4.6/4.8 + the Lemma 5.4 cycle branch) + the `hD : 6 ≤ bodyBarDim n` floor
lift; the chain-data record is the CHAIN↔ENTRY contract. **ASSEMBLY** composes
the honest general-`d` Theorem 5.5, re-greens `prop:rigidity-matrix-prop11` +
`hub`, derives Thm 5.6, states Conjecture 1.2.

## Decisions made during this phase

(Phase-local choices land here as CHAIN leaves build. The opening recon's
decisions — OD-6/OD-7 resolved, OD-4 + (b) flagged — live in
`notes/Phase23-design.md` §"CHAIN"(e); this section stays a pointer until the
first leaf lands.)

### Phase-local choices and proof techniques

- **Opened on a detailed leaf-level recon, not a build** (the design-pass-first
  discipline, `DESIGN.md` *Scale-up: design the LAYER*; the Case-I node-by-node
  precedent). The recon source-verified the central scoping fact — the
  arm-realization engine is already general-`k`, only the dispatch is `d=3` —
  and surfaced the producer-shape flag (b) before any leaf builds.
