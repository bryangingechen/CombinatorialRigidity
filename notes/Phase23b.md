# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git; all four 23a producers + both M4 halves general-`k`).
**Remaining: CHAIN-2 (the `Fin d` reduction layer — T-W9a/T-W9b transport machinery LANDED; the W9b
MEMBERSHIP is BLOCKED on a fold-invariant reshape, the KT §6.4.2 telescoping crux — next is a
comprehensive telescoping-structure DESIGN-PASS, **user-adjudicated 2026-06-19**; see *Hand-off* for the
design-pass guidance) + CHAIN-5 (the dispatch assembly, gated by the ENTRY-contract reshape).**
The integer Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain (coordinator owns the sub-phase
boundary; codes-until-open).

**Orientation.** The **23b (CHAIN layer)** rolling state + hand-off. Cross-phase plan/guidance + the
detailed leaf-level recon live in `notes/Phase23-design.md` (§"CHAIN": (a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions); program map
`notes/MolecularConjecture.md`. **Sub-phase codes** (a letter + work log minted when a layer opens, so
a later split costs no renumber-churn): `CARRIER`(=23a, closed), `CHAIN`(=23b), `ENTRY`/`ASSEMBLY`
(code-only until their turn).

## Current state

**Route B LOCKED (§(o″)). T-W9a + T-W9b single-step/fold core LANDED; the W9b MEMBERSHIP is BLOCKED on
a fold-invariant reshape — the conjecture's hardest crux (KT §6.4.2, the "12-page proof"). Next = a
comprehensive telescoping-structure DESIGN-PASS (**user-adjudicated 2026-06-19**; the global
accumulating-`Tag` invariant, NOT a local leaf — see *Hand-off* for the design-pass guidance + clauses).**

The row-272 build found the iteration-11 *frozen* `Tag`-signature (design §(o″) *DESIGN-PASS*) is
**UNPROVABLE — INVALIDATED**: with a single-pinned block tag `Tag s ψ := … ∨ ψ = hingeRow vₛ₊₁ vₛ₊₂ ρ`,
the carry `(funLeft (swap vₛ₊₁ vₛ₊₂)).dualMap` sends `Tag(s+1)`'s block `hingeRow vₛ₊₂ vₛ₊₃ ρ ↦
hingeRow vₛ₊₁ vₛ₊₃ ρ` (`hingeRow_funLeft_dualMap`, coordinator-verified), but the target tag is
`hingeRow vₛ₊₁ vₛ₊₂ ρ` — they differ by a generically-nonzero residual `hingeRow vₛ₊₂ vₛ₊₃ ρ` no
hypothesis constrains. So a single carried block row does **not** chain: **KT eq. (6.66)'s ±r-chain
*telescopes*** — the residuals must accumulate in the fold-invariant (an accumulating *sum* of block
rows, or a span-membership tag), NOT a single pinned functional. This reshape is design-decomposition
work, not a one-sitting build.

**The piecemeal recon→build loop has mis-pinned this crux 4× (iter 3/7/9/11 design-passes): the bridge
`redundancy_panel_carry` is an orphan, the landed single-step is terminal-only, the `Tag` is
non-telescoping.** Landed + still-usable: the transport machinery (T-W9a span-transport, the *terminal*
single-step, the fold core `bottomTag_foldr_mem_rigidityRows` over an **abstract** `Tag` — reusable, the
`Tag` shape is its parameter, G4d-i panel-match). To confirm-and-delete once the reshape lands: the
orphan bridge `redundancy_panel_carry` + `candidateRow_ac_eq_neg` (both zero live callers).
Tracker (CHAIN-2c-ii-transport): T-W9a ✓ → W9b-step ✓ → W9b fold core ✓ (abstract `Tag`, reusable) →
**telescoping fold-invariant reshape [next — design]** → W9b membership → 2c-ii-arm → 2c-iii → CHAIN-5.

**Route β — LOCKED** (user-adjudicated, row 242): ONE `v₁`-base + the uniform `Fin (k+1)` relabel arm;
route B is **within** β. (Blueprint-clarity obligation: *Hand-off* CHAIN-2c bullet + §(o″).)

**Context (closed/landed):** CHAIN-1/3/4 + OD-7 CLOSED; `G.ChainData n` + 7 accessors; CHAIN-2a
CLOSED; 2c-i + 2c-ii-α/β/graphiso + T-W9a + T-W9b step/fold core + the bridge LANDED (the tracker
above + *Decisions made* one-liners). Remaining (tracker): block-carrying single-step → W9b membership
→ 2c-ii-arm → 2c-iii → CHAIN-5 + ENTRY's extractor reshape.

**Standing context (settled; full detail in the design doc).** (1) *Architectural:* metric-using Hodge
leaves live in `MeetHodge.lean`, never metric-free `Meet.lean` (a `PiL2` import → `whnf` timeout) —
TACTICS-QUIRKS § 59. (2) *Orientation:* the arm-engine is already general-`k`; CHAIN replaced only the
d=3 dispatch + its `⋀²ℝ⁴` discriminator with the `d`-candidate chain + `⋀^{d−1}` duality finish. (3)
*Contract (SETTLED):* the CHAIN↔ENTRY `G.ChainData n` shape is frozen — three lockstep decls (ENTRY
extractor / producer `…hcand` / CHAIN-5 `hdispatch`), no motive/IH change (C.6), `d=3` zero-regression
(design §"CHAIN↔ENTRY contract").

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)/(l)/(m)/(n)/(o)/(o′)/(o″)). **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 +
CHAIN-2a CLOSED; CHAIN-2c-i + 2c-ii-α/β + 2c-ii-graphiso COMPLETE.** Remaining in **CHAIN-2c-ii**:
**2c-ii-transport** (route B, §(o″); T-W9a's linear-algebra layer landed, **(T-W9a-chain)** next) →
**2c-ii-arm** (the closer) — then
**CHAIN-2c-iii** (assembly), and **CHAIN-5** (signature frozen by the CHAIN↔ENTRY contract; gated on
the rest of CHAIN-2 + ENTRY's extractor reshape).

- [x] **CHAIN-3 — the `⋀^{d−1}(ℝ^{d+1})` duality bricks + Hodge panel-meet membership**
      (`Meet.lean` + `MeetHodge.lean`). **CLOSED 2026-06-17** (route = `⋀^{d−1}W`-is-a-line, NOT the
      withdrawn d=3-only `Φ̃`; the OD-8 route-α leaf chain h-0…h-4 closing on the join=meet duality
      `extensor_join_proportional_complementIso_meet`). Detail: design §"CHAIN"(f)/(g)/(h) + git +
      *Decisions made* → *Landed CHAIN-3 bricks*.
      - [~] **Cleanup-round candidates (forward, low-priority):** (1) the lifted `wedgeFixedLeft`
        block + `inf_range_wedgeFixedLeft` (ambient `{d}`) served the `Φ̃` route the CHAIN-3-finish
        recon **withdrew** (`finrank_sup_range_wedgeFixedLeft` / `extensor_toDual_extensor_eq_zero_of_perp`
        do NOT generalize — `dim Ω = C(d−1,2) = 1` only at `d=3`; the d=3 lemmas stay GREEN, **do NOT
        touch**) — revert the lifted infra to `Fin 4`. (2) The `finrank {n}^⊥ = k` metric transport is
        duplicated between (h-3) and (h-4) — factor a shared `finrank_toDualPerp_pair_eq` helper.
- [x] **CHAIN-1 — the `d`-fold candidate machinery** (`RigidityMatrix/Basic.lean`). **CLOSED
      2026-06-18.** Graph-free over `ScrewSpace k`, no `d=3` content: the eq.-6.62 row-correspondence
      swap + the `ιc`-block candidate augment (the per-candidate column-op heterogeneity is CHAIN-2's
      bookkeeping). Detail: *Decisions made* → *Landed CHAIN-1 bricks* + git.
- [x] **CHAIN-4 — the `Fin (d+1)` incidence + Claim-6.12 discriminator**
      (`RigidityMatrix/Claim612.lean`). **CLOSED 2026-06-18** (4a–4d all landed; consumes CHAIN-3;
      OD-4 RESOLVED — existence/homogeneous, not alg-independence). Capstone = the discriminator
      `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (assembly of 4b line-data + 4c
      witness-join + CHAIN-3 (h-4)). Detail: design §(i)/(j) + git + *Decisions made* → *Landed
      CHAIN-4 bricks*.
- [ ] **CHAIN-2 — the `Fin d`-indexed candidate-reduction layer (eqs. 6.59–6.67)** (`CaseIII/`).
      Zeroth leaf (`G.ChainData n` record + 7 interior-split accessors, `Induction/Operations.lean`)
      + **CHAIN-2a** (per-candidate single-`i` reduction: `chainData_split_w6b_gates` +
      `chainData_split_realization`, both axiom-clean) **LANDED/CLOSED 2026-06-18.** Remaining:
      **CHAIN-2c — the single-base `Fin (k+1)` family dispatch** (route β, design §(n)/(o)): ONE base,
      ONE `ρ₀`, ONE discriminator → `fin_cases u`; eq. (6.66) absorbed. **2c-i**
      (`exists_chainData_discriminator_pick`) LANDED. **2c-ii** (the genuinely-new relabel arm, NOT a
      numeral pass — KT's `ρᵢ` is a `(i−1)`-cycle): foundation (`shiftPerm` / `ofNormals_relabel_perm` /
      graphiso `splitOff_isLink_shiftRelabel_iff`) + transport **T-W9a**
      (`shiftBodyList_foldr_mem_span_rigidityRows`, span-only) + **T-W9b step + fold core**
      (`funLeft_dualMap_bottomTag_mem_rigidityRows` / `bottomTag_foldr_mem_rigidityRows`) + the bridge
      `redundancy_panel_carry` (now orphan-in-waiting) all LANDED →
      **block-carrying single-step `funLeft_dualMap_pinnedBlock_carry` [next, SIGNATURE FROZEN]** (the
      `(a,v)`-block→`(c,v)`-block carry the landed terminal step cannot do interior; panel-match via
      G4d-i — §(o″) *DESIGN-PASS*) → W9b membership fold (`Tag` pinned to `ρ`) → **2c-ii-arm**
      `chainData_relabel_arm` (closer; d=3 M₃ = `i=2` instance) → **2c-iii** `chainData_dispatch`. Live
      status: *Current state* tracker; full detail: design §(o″) *DESIGN-PASS* + *Decisions made*.
- [ ] **CHAIN-5 — the `d`-chain dispatch assembly** (`CaseIII/Realization.lean`).
      Replace `case_III_candidate_dispatch`; feed the (general-`k`) arm closers.
      **Signature now FROZEN** by the CHAIN↔ENTRY contract (`notes/Phase23-design.md`
      §"CHAIN↔ENTRY contract" C.3): `hdispatch` consumes a `G.ChainData n` record
      (the length-`d` chain) + the `splitOff (vtx 1)(vtx 0)(vtx 2) e₀` deficiency-0
      fact + the IH-generic base realization on that split. Keep the `d=3` dispatch
      as a `k=2`/length-3 wrapper (no `d=3` regression — C.4 zero-regression map).
- [x] **CHAIN tail — lift the four 23a-carried producers (OD-7 fold). CLOSED 2026-06-18.** After
      CHAIN-3, all four 23a-carried producers (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`) + both M4
      halves are general-`k`; the *one* genuinely-new piece was LEAF-0
      `linearIndependent_normals_of_algebraicIndependent_triple`. Detail: design §(k) + git +
      *Decisions made* → *Landed OD-7 bricks*.

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
- **OD-4 — RESOLVED 2026-06-18 (design-pass): existence/homogeneous route,
  alg-independence NOT forced.** Verdict + reasoning: Decisions-made below +
  `notes/Phase23-design.md` §(i). KT eq. (6.67) phrases the `d+1`-points step via
  alg-independence (p. 698 verbatim, confirmed against the `.refs/` PDF), but the
  landed d=3 formalization sidesteps it: the D-span runs off the already-general
  `span_omitTwoExtensor_eq_top` (only hyp `LinearIndependent ℝ pbar`, via Lemma
  2.1), driven by **linear** independence of `d+1` **homogeneous** vectors, not
  KT's affine points / `(d−j)`-flat fact. The row #106 cross-product construction
  is **dead (zero live call sites)**. CHAIN-4 lifts as a numeral generalization of
  green bricks; one build-time residual (per-join panel-membership, CHAIN-4b).
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

**Route B LOCKED (design §(o″)); no motive/IH/spine-carry change (C.3/C.6 unmoved). T-W9a + T-W9b
single-step/fold core LANDED. The W9b MEMBERSHIP is BLOCKED on a fold-invariant reshape (KT §6.4.2's
telescoping ±r-chain — see *Current state*).**

**NEXT STEP — USER-ADJUDICATED (2026-06-19): a comprehensive telescoping-structure DESIGN-PASS first,
then resume builds only if its verdict is coordinator-verifiable.** Dispatch a docs-only design-pass
(opus) whose deliverable is the **GLOBAL** fold-invariant for KT §6.4.2's ±r-chain — the accumulating
block-row *sum* (or span-membership) `Tag` for the *whole* `shiftBodyList i` fold — **NOT** another
local per-step leaf signature (a local pin is exactly what the piecemeal loop mis-pinned **4×**: iters
3/7/9/11; each was mechanically plausible but globally wrong, caught only when a build read the fold's
arithmetic end-to-end). The design-pass must: (a) be source-verified against a **close read of KT
§6.4.2** (pp. 696–698, the eqs. (6.62)–(6.67) ±r-chain; REFS.md for the PDF page offset); (b) carry the
two mandatory design-pass clauses — *verify every load-bearing claim against the landed Lean bodies*,
and *flag-don't-force* (if the right invariant needs a motive/IH/carried-hypothesis change or
genuinely-new math, SAY SO and stop for adjudication rather than pin a 5th wrong structure); (c) pin the
exact `Tag`/invariant shape, how each `hstep` discharges, and how the accumulated residual telescopes
to `0` (or into a genuine `F 0`-row) at the chain bottom. **Coordinator: scrutinize the verdict HARD
before dispatching any build** — read the proposed fold's arithmetic end-to-end (the 4× mis-pin history
is precisely that a plausible local pin keeps being globally wrong); a boundary-pair / second
independent design read is warranted here.
⚠ **The iteration-11 frozen signature + its §(o″) *DESIGN-PASS* (A)–(D) detail are INVALIDATED** (row
272: the single-pinned `Tag` does not chain — the carry leaves a generically-nonzero residual
`hingeRow vₛ₊₂ vₛ₊₃ ρ`) — preserved in §(o″) + git as the source-verified record of what the *terminal*
single-step / the G4d-i panel-match / the d=3 M₃ structure provide (still-usable inputs, below).

(The superseded iteration-11 spec — the block-carrying single-step's exact `(a,v)`→`(c,v)` arm, the
G4d-i `hcol`-supply correction, and the single-pinned `Tag` membership fold — is preserved in §(o″)
*DESIGN-PASS* (A)–(D) + git as the source-verified record. **Still-usable inputs to the reshape:** the
G4d-i panel-match (`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, the d=3 M₃ route at
`Relabel.lean:1532`) + the W6b `ρ ⊥ C(q(ab))` gate (`Realization.lean:799`) for the per-step panel
annihilations, and the **abstract-`Tag`** fold core `bottomTag_foldr_mem_rigidityRows` (the `Tag` shape
is its parameter — the reshape supplies an accumulating-sum/span-membership `Tag`, not a single
functional). **Confirm-and-delete** at the reshape: the orphan bridge `redundancy_panel_carry` +
`candidateRow_ac_eq_neg` (zero live callers).)
**`d=3` zero-regression CONFIRMED:** `shiftBodyList i` has length `i−1` (`length_shiftBodyList`); the M₃
arm is `i=2` → length-1 list → single *terminal* step, zero interior carries (the carry fires only for
`s+1 < i`, `i ≥ 3`). The landed M₃ + `case_III_bottom_relabel` + d=3 dispatch are untouched. **Per-leaf
tracker** (checklist CHAIN-2): T-W9a-chain ✓ → T-W9a ✓ → W9b-step ✓ → W9b fold core ✓ →
redundancy_panel_carry ✓ (orphan-in-waiting) → **block-carrying single-step [next, frozen]** → W9b
membership fold → 2c-ii-arm → 2c-iii → CHAIN-5.

**Three orphaned lemmas to confirm-and-delete at the carry/2c-ii-arm/cleanup commit** (all zero live
callers; full detail §(o″)): (1) `redundancy_panel_carry` (the eq.-6.44 bridge, replaced by G4d-i — this
pass); (2) `ofNormals_relabel_perm` (2c-ii-β, REJECTED route A); (3)
`funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows` (binary composition, superseded by the `wstep`
fold). The graph-iso `splitOff_isLink_shiftRelabel_iff` is **NOT** orphaned — consumed at the **arm**
(`chainData_relabel_arm`'s `hiso`), NOT by T-W9a (which uses `shiftBodyGraph_isLink_of_off_body`).

- **CHAIN-2c — the single-base `Fin (k+1)` family dispatch (design §(n)/§(o)/§(o′)).** Route β LOCKED
  (user-adjudicated 2026-06-18, KT-source-verified): ONE base `(G₁,q₁)` (the `v₁`-split = `M₀`), ONE
  `ρ₀`, ONE W6b call, ONE discriminator call, then `fin_cases u`; eq. (6.66)'s ±r chain absorbed into
  reusing one `ρ₀`. The relabel arm (2c-ii) covers the interior candidates `2 ≤ i ≤ d−1` (a
  genuinely-new construction, NOT a numeral pass — KT's `ρᵢ` is a `(i−1)`-cycle, the d=3 engines are
  transposition-only); **M₀-arm reuse SETTLED:** 2a-ii (`chainData_split_realization`) is the `i=1`/`M₀`
  arm (its per-`i` split at `i=1` IS the `v₁`-split), the uniform arm does not subsume it (they are the
  `fin_cases`'s direct / relabel legs). The 2c-ii leaf decomposition + the §(o′)(B) fork (**adjudicated
  → route B**) live in **checklist CHAIN-2** (the single tracker) + design §(o″). No motive/IH or
  spine-carry change. The `G.ChainData n` record + 7 accessors (C.1) are landed; ENTRY owns the
  extractor (C.2).

  **Blueprint-clarity obligation (owner-flagged 2026-06-18 — "absolutely clear").** Route β **absorbs**
  KT's explicit index-shift isos (6.54–6.56) + ±r chain (6.66) into the Lean `shiftPerm` relabel arm —
  so the `lem:case-III` general-`d` node's prose MUST materialize them explicitly (§(o)/§(o′) pin the
  four ordered points): (1) the single-`v₁`-base construction; (2) the index-shift iso `ρᵢ` (the
  `(i−1)`-cycle) and "exactly the same framework" via it; (3) the single redundancy `r` (eq. 6.52)
  carried ±-ly across the `d` panels (eq. 6.66) — the §(o′)(B) route-A eq.-(6.66) identity / route-B
  degree-2 mechanism is exactly this step; (4) the (6.67) discriminator (Lemma 2.1 on the `d+1`
  points). The Lean economizes; the exposition must not. Tracked in BlueprintExposition (the
  `lem:case-III` general-`d` entry, extending the d=3 `lem:case-III-claim612-eq644`); written as
  2c-ii/CHAIN-5 land + at phase-close.

Re-pointing the d=3 discriminator `exists_complementIso_ne_zero_of_homogeneousIncidence` at CHAIN-4d's
`k:=2` instance (h-5) is now an available but **not-forced** simplification — the d=3 body + its
`complementIso_smul_eq_extensor_join` wrapper stay green meanwhile; defer to ASSEMBLY/cleanup. **The
OD-8 route β stays rejected** (the annihilation→membership upgrade is the withdrawn `dim Φ̃` count —
distinct from the CHAIN-2c "route β" just locked above; this is the CHAIN-3/OD-8 duality route). The CHAIN-3-finish
geometry (the `⋀^{d−1}W`-is-a-line route, NOT the withdrawn d=3-only `Φ̃` route) lives canonically in
`notes/Phase23-design.md` §"CHAIN"(f)/(h); the join=meet duality KT leaves implicit is captured in the
BlueprintExposition ledger (the CHAIN-3 entry).

**The CHAIN↔ENTRY contract is now settled** (`notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", 2026-06-17) — the (b) build-recon gate is discharged:
CHAIN-5's `hdispatch`/`hcand` signature is frozen against the `G.ChainData n`
record (C.1/C.3), so it is now authorable. **CHAIN-2's *linear algebra* is independent
of the contract, but its *indexing* is contract-coupled** (recon §(l) overturned the
old "CHAIN-2 fully independent" claim): the `ChainData` record it indexes **is now authored
in Lean** (`Induction/Operations.lean`, 2026-06-18, the zeroth leaf — `deg_two` settled), so
the indexing prereq is discharged. CHAIN-5 is unblocked once the rest of CHAIN-2 lands
**and** ENTRY's extractor is reshaped.

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
- **OD-4 RESOLVED 2026-06-18: existence/homogeneous route, alg-independence NOT forced**
  (overturns the prior "forced" lean). The landed d=3 N3a works homogeneously (§1.42 R1-affine):
  the eq.-(6.67) D-span runs off `span_omitTwoExtensor_eq_top` (already general-`k`, only hyp
  `LinearIndependent ℝ pbar`, via Lemma 2.1) — **linear** independence of `d+1` **homogeneous**
  vectors, never KT's affine points / `(d−j)`-flat-in-union (the alg-independence consequence is on
  the route the formalization sidesteps). Source-verified: KT p.698 verbatim (`.refs/` PDF) vs. the
  landed bodies; the row #106 cross-product construction is **dead (zero live call sites)**. No new
  `AlgebraicIndependent` lemma; site (b) is not a site (only site (a), nested seed-rank, stays live).
  Per-join panel-membership generalizes combinatorially (join `{a,b}`⊂`Πᵢ` iff `i+1∈{a,b}`). One
  build residual flagged (CHAIN-4b). CHAIN-4 decomposed into 4a–4d → §"CHAIN"(i)/(j).
- **CHAIN-2 decomposition (recon 2026-06-18, read-only Plan + coordinator source-verify) — overturns
  §(c)'s framing.** The named `caseIIICandidate`/`case_III_old_new_blocks`/`case_III_rank_certification`
  chain is **already general-`k`** (the only `d=3`-pin in `CaseIII/` is `Realization.lean`'s dispatch =
  CHAIN-5); §(c)'s "(now `q : α × Fin 4`-shaped)" was false. CHAIN-2 = the `Fin d`-indexed reduction
  *layer* (2a per-`i` / 2b ±r-chain / 2c family) on top of that chain + closed CHAIN-1 →
  §"CHAIN"(l).
- **CHAIN-2a design-pass (2026-06-18) — VERDICT: re-index, gates threaded from above** (settles the
  session-#7 open question against the landed bodies). CHAIN-2a's per-`i` reduction is a
  `case_III_arm_realization` (general-`k`) re-index, NOT a from-scratch gate construction: the gate
  family is carried as hypotheses by both the certification (`Candidate.lean:1403`) and the arm closer
  (`Arms.lean:72`), and supplied from above by two general-`k` producers (W6b
  `exists_candidateRow_bottomRows_of_rigidOn` + CHAIN-4d discriminator, fed by
  `case_III_nested_rank_lower_all_k`). Sub-leaves: CHAIN-2a-i `chainData_split_arm_gates` (the two
  producer calls) → CHAIN-2a-ii `chainData_split_realization` (the arm-closer re-index). One
  build-time wiring flag (arm form + `h622lb`/`hIH` instantiation), no motive change → §"CHAIN"(m).
- **CHAIN-2a CLOSED 2026-06-18 — the complete single-`i` reduction (re-index verdict CONFIRMED).**
  Two axiom-clean leaves in `CaseIII/Realization.lean`: `chainData_split_w6b_gates` (the `{k}`-general
  flat-tuple W6b half) + `chainData_split_realization` (the re-index core, reads the per-`i` split off
  the `ChainData` accessors and calls `case_III_arm_realization` directly — no `_M3` relabel). **The
  transversal half stays a hypothesis `htrans`** — the single-`i` slot CHAIN-2c fills via the
  discriminator (the arbitrary-panel `u`↔candidate `i` match is the family glue). Internals + §(m)
  clause-(ii) resolution in git/design §(m). No FRICTION.
- **CHAIN-2b/2c design-pass (2026-06-18) — VERDICT: single-base `Fin (k+1)` dispatch (route β), ±r
  chain absorbed (no separate 2b lemma).** Single base `(G₁,q₁)` / one `ρ₀` / one discriminator /
  `fin_cases u`; reuse 2a-ii only at `M₀`. Route β LOCKED (user-adjudicated, row 242). Detail
  `notes/Phase23-design.md` §(n).
- **CHAIN-2c-ii design-pass (§(o)/§(o′)/§(o″)) — VERDICT: a genuinely-new relabel arm (NOT a numeral
  pass), route B.** Leaf chain: 2c-ii-α (`shiftPerm`) → 2c-ii-β (`ofNormals_relabel_perm`) → graphiso →
  transport (T-W9a-chain → T-W9a → T-W9b) → arm; M₀-arm (2a-ii) reused at `i=1` only. **§(o″) adjudicated
  the §(o′)(B) fork → route B** (shared-`ρ₀` row-span); **route A REJECTED** (its eq.-6.66 identity
  equates two `Classical.choice` existentials — unprovable; KT p.698 carries ONE `r` + the ±r chain,
  the landed d=3 M₃ is route B). No motive/IH/spine-carry change. Detail §"CHAIN"(o)/(o′)/(o″).
- **W9b-MEMBERSHIP sharpened recon 2026-06-19 — VERDICT: a NEW block-carrying single-step is the
  irreducible next leaf, NOT a fold over the landed single-step.** Source-verified: the terminal step
  `funLeft_dualMap_bottomTag_mem_rigidityRows` (`Relabel.lean:1181`) *terminates* the block into a
  genuine `e_b`-row (`:1246–1252`), structurally impossible interior (`e_b = edge(s+1)` cut by
  `removeVertex vₛ₊₁`). The carry needs `(a,v)`-block→`(c,v)`-block re-pinned to the single `ρ`. The
  landed step is the *d=3 terminal* form (M₃/`i=2`, zero-regression). Detail §(o″) *DESIGN-PASS*.
- **CARRYING-STEP DESIGN-PASS 2026-06-19 (docs-only, row 270 BLOCKED → frozen; §(o″) *DESIGN-PASS*) —
  VERDICT: signature frozen, panel-match supply CORRECTED to G4d-i (NOT the eq.-6.44 bridge).** The
  carrying step `funLeft_dualMap_pinnedBlock_carry` (sig §(o″)(A)) is buildable, one commit; its `hρ_ac`
  comes from **G4d-i** (`acolumn_mem_hingeRowBlock_of_span_rigidityRows`, landed + already in d=3 M₃ use
  at `Relabel.lean:1532`) off the W6b `hρGv`, NOT `redundancy_panel_carry` — whose `hcol`/`hrest`
  (ab/ac/grest decomposition) is un-suppliable (`_acolumn_zero` gives only the trivial zero-functional
  vanishing; the data is out of W6b scope). So `redundancy_panel_carry` + `candidateRow_ac_eq_neg` join
  the orphan list (zero live callers, grep-confirmed). NOT new math (G4d-i landed); no motive/IH/spine
  change; d=3 vacuous (carry fires `s+1<i`, `i≥3`). Detail §(o″) *DESIGN-PASS* (A)–(D).
**Landed CHAIN-2 leaves (all axiom-clean; detail = git + design §(o)/(o′)/(o″) + FRICTION).** One-line
verdicts (settled; nothing downstream leans on the internals): **`G.ChainData n` record + accessors**
(`Induction/Operations.lean`, the contract-C.1 length-`d` chain + the interior-split `(v,a,b,e_a,e_b)`
geometry accessors; `Fin d`-index idiom in FRICTION). **CHAIN-2c-i** `exists_chainData_discriminator_pick`
(`Realization.lean`, the route-β single-discriminator pick, verbatim generalization of the d=3
region). **2c-ii-α** `ChainData.shiftPerm` (KT eq. 6.54) + recursion handle
`shiftCycle_eq_cons`/`shiftPerm_eq_swap_mul`. **2c-ii-graphiso** `splitOff_isLink_shiftRelabel_iff` +
`shiftEdgePerm` (the `hiso` supplier, consumed at the **arm**). **2c-ii-transport-W9a** (route B, the
genuinely-new crux) `shiftBodyList_foldr_mem_span_rigidityRows` (fold core +
`shiftBodyFramework`/`_htrans` removeVertex chain; span-only, endpoints removeVertex NOT splits).
**2c-ii-transport-W9b** the single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` (abstract-`Fv`/`Fva`
restatement of `case_III_bottom_relabel`, the *terminal* d=3 form) + fold core
`bottomTag_foldr_mem_rigidityRows` (`Tag : ℕ → Dual → Prop` threaded through the pure-relabel fold).
**2c-ii-β** `ofNormals_relabel_perm` + **`redundancy_panel_carry`** (eq.-6.44 bridge) — both **⚠ orphans**
(route A REJECTED / eq.-6.44 route superseded by G4d-i per the carrying-step design-pass;
confirm-and-delete at the carry/2c-ii-arm build, *Hand-off* orphan flag). **OD-7 `hcontract_k`** = 5 leaves (mostly numeral passes; the
one genuinely-new piece LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple`).

**Landed CHAIN-1/3/4/OD-7 bricks (all CLOSED 2026-06-18, axiom-clean; canonical homes = git +
`notes/Phase23-design.md` §(f)/(h)/(i)/(j)/(k) + the BlueprintExposition CHAIN-3 entry).** One-line
verdicts (the closed forward sequence, nothing downstream leans on the internals): **CHAIN-1**
(`RigidityMatrix/Basic.lean`) the eq.-6.62 row-swap + `ιc`-block augment, graph-free over `ScrewSpace k`
(single-`Unit` predecessors as `ιc:=Unit` corollaries; the per-candidate column-op heterogeneity is
CHAIN-2's bookkeeping). **CHAIN-3** (`Meet`/`MeetHodge.lean`) the `⋀^{d−1}W`-is-a-line duality (the
two `[~]` forward cleanup-candidates are the checklist CHAIN-3 sub-bullet). **CHAIN-4**
(`RigidityMatrix/Claim612.lean`) the discriminator (4d's `MeetHodge` import did NOT regress the `⋀²ℝ⁴`
proofs; 4b stays its own green body — off-one-panel hyp + `LI ℝ p` via `hpbar` — not a `k:=2` wrapper).
**OD-7** (the four producers + both M4 halves general-`k`): verbatim numeral passes (§58 idiom) except
LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI, genuinely-new); the
M4-forget reach-in routes solely through CHAIN-3 (h-4) + `extensor_update_smul`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Referencing a `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData`
  decl needs its full path including the inner `BodyHingeFramework` namespace (the ambient `namespace` is
  out of scope under `_root_.`; bare and `…Molecular.` both fail "Unknown identifier")* → FRICTION [idiom]
  *Referencing a `CombinatorialRigidity.Molecular`-namespace lemma from inside a `_root_.Graph.ChainData`
  decl…*.
- *Feeding a partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold:
  package via `dite` + a `dif_pos` `_eq` lemma, then `simp only` (not `rw`) the per-step resolutions
  (`rw` chokes on the proof-irrelevant `getElem` bound + the un-beta-reduced `dite` redex)* → FRICTION
  [idiom] *Feeding a partial proof-bearing-index family into a `ℕ → _` total-function-consuming fold…*.
- *Composing two `(funLeft σ).dualMap` relabel transports: both `funLeft` and `dualMap` are
  contravariant, so the rewrite chain is `← comp_apply` → `dualMap_comp_dualMap` → `← funLeft_comp`
  (the two contravariances cancel to `funLeft (σ₂ ∘ σ₁)`); group the corrections with `sub_sub` on
  the hypothesis only* → FRICTION [idiom] *Composing two `(funLeft σ).dualMap` relabel transports…*.
- *Recovering the other endpoint of a `Graph.IsLink` from a same-edge / same-left-endpoint pair: use
  `IsLink.right_unique` (`y = z` from `IsLink e x y`/`IsLink e x z`), not `eq_and_eq_or_eq_and_eq` +
  disjunct elimination* → FRICTION [idiom] *Recovering the other endpoint of a `Graph.IsLink`…*.
- *`rcases … with rfl` / `subst` fails when the equation's subject is a function application
  (`σ e = edge 0`), not a free local — name the eq and `rw … at` the link instead* → FRICTION [idiom]
  *`rcases hmem with rfl | …` / `subst` fails when the equation's subject is a function application…*.
- *A finite-`i`-cycle permutation over an indexed family `vtx : Fin n → α` as `Equiv.Perm α`:
  `List.formPerm (List.ofFn …)` (needs `[DecidableEq α]`); `Nodup` via `nodup_ofFn`, action lemmas
  via `formPerm_apply_lt_getElem` / `…_getElem` + `Nat.mod_self` / `…_of_notMem`* → FRICTION [idiom]
  *A `Fin n → α` indexed-family cycle as an `Equiv.Perm`…*.
- *Dropping the involution from a `ρ = Equiv.swap`-relabel transport to a general `Equiv.Perm ρ`: the
  `ρ`/`ρ.symm` placement is forced — `qρ` keeps forward `ρ`, but `endsσρ` + the rigidity-pullback
  motion `S∘ρ.symm` flip to `.symm`; the vertex-region transport stays forward `ρ`* → FRICTION
  [idiom] *Dropping the involution from a `ρ = Equiv.swap`-relabel transport…*.
- *`rw [hidx]` on a `getElem` index `l[k]`/`l[k]'h` (the bounds proof depends on `k`) trips "motive
  is not type correct" — re-apply the indexing lemma at the new index, don't rewrite the index in
  place; the `List.ofFn _ = x :: …` head-peel sibling sidesteps it via `List.ext_getElem` + `match`*
  → TACTICS-QUIRKS § 61 (+ variant).
- *A `Fin d`-index relabel proof: destructure `m = m'+1` early so `m-1` reduces to `m'` by `rfl` (kills
  the §61 in-place index rewrites), and bridge `(i.castSucc:ℕ)` to `(i:ℕ)` in `omega` args with `simp
  only [Fin.val_castSucc]` — not `show` (style linter) or `rw [hicv]` (`hicv := rfl` errors)* → FRICTION
  [idiom] *A `Fin d`-index relabel proof over general `d`…*.
- *`Fin d`-index arithmetic at general `d` (no `+1`): a `0 < i` guard / `i - 1` predecessor wants
  `OfNat (Fin d)` literals that don't synth — for plain index bookkeeping (not a `d=0`-false slot),
  guard `0 < (i:ℕ)` + build `⟨(i:ℕ)-1, _⟩` rather than carry `[NeZero d]`* → FRICTION [idiom]
  *`Fin d`-index arithmetic (general `d`): guard `0 < (i:ℕ)`…*.
- *Index a `Fin`-parametrized `def` (e.g. `shiftBodyGraph`) by its *minimal* validity bound (the
  vertex-index range `s+1 < d+1`), not the looser step-/cycle-level bound the consumers carry —
  coupling them re-derives the wrong arithmetic obligation at every instantiation offset* → FRICTION
  [idiom] *Index a `Fin`-parametrized `def` by its minimal validity bound…*.
- *Lifting a `Fin (k+2)`-point-family lemma to general `k` may need `[NeZero k]` (the `0 : Fin k`
  literal in a slot-`0` rescale; the statement is genuinely false at `k=0`) — carry the hypothesis,
  don't fight the `OfNat (Fin k) 0` synthesis* → FRICTION [idiom] *Lifting a `Fin (k+2)`-point-family
  lemma to general `k`…*.
- *`map_update_smul` on `ExteriorAlgebra.ιMulti` at general grade: `(M := Fin (d+1) → ℝ)` annotation +
  the `have … := …map_update_smul v i c (v i)` term form (not `rw`, which leaves `Module ℝ …`
  un-synthesized) + `Function.update_eq_self` to clear the `update v i (v i)` residual* → FRICTION
  [idiom] *`ExteriorAlgebra.ιMulti ℝ n` needs `(M := ...)`…* (Phase 23b reuse).
- *The `⧸` quotient notation (`M ⧸ P`) needs a direct `import Mathlib.LinearAlgebra.Quotient.Basic`
  even when `Submodule.mkQ` resolves by name (a notation must be imported, not merely reachable) —
  or drop the type ascription and let `set π := P.mkQ` infer the codomain* → TACTICS-QUIRKS § 60 /
  FRICTION [mirrored] *`linearIndependent_sumElim_block_swap`…* (Gotcha).
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
- *Re-orienting a proportionality `c • x = y` into `c⁻¹ • y = x` — use `inv_smul_eq_iff₀ hcne` on the
  goal, not `rw [← hc, smul_smul]` (the nested-`•` `rw` chain fails on `⋀`-subtype elements)* →
  TACTICS-GOLF § 19.
- *Recovering a permuted-incidence `Fin n` wrapper from a general `_gen` lemma — feed `_gen` the
  reordered indexed family (`n ∘ ![…]`, LI via `hn.comp _ (by decide)`) and read the pairings back
  through the (definitional) reorder, rather than re-proving the d=3 body* → FRICTION [idiom]
  *Recovering a permuted-incidence `Fin n` wrapper…*.
- *Pushing a functional through `c • x` on an `abbrev`'d carrier (`ScrewSpace k = ⋀^k …`): `rw
  [map_smul]` (even a concrete `rw [hsmul]`) mis-fires on the smul instance — close with `exact
  (r.map_smul c _).trans …`* → TACTICS-GOLF § 19 (companion) / FRICTION [idiom] *Pushing a functional
  through a `c • x` on an `abbrev`'d carrier…*.
