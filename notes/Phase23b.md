# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git): all four 23a-carried producers + both M4 halves are
general-`k`; CHAIN-4's discriminator capstone `exists_complementIso_ne_zero_of_homogeneousIncidence_gen`
landed. **Remaining: CHAIN-2 (the `Fin d` reduction layer — 2c-ii-transport next) + CHAIN-5 (the
dispatch assembly, gated by the ENTRY-contract reshape).** The integer Phase 23 stays **in progress** —
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

**§(o′)(B) fork ADJUDICATED → route B; next = the cycle-W9a transport
`ChainData.funLeft_shiftPerm_dualMap_sub_acolumns_mem_span_rigidityRows` (2c-ii-transport, first
buildable).** Design **§(o″)** (2026-06-19, source-verified + KT-cross-checked) decides the §(o′)
route-A/B fork: **route B (shared-`ρ₀` row-span transport); route A REJECTED as unprovable.** Canonical
verdict + the rejection argument + the route-B leaf decomposition + signatures are in *Hand-off* below
+ design §(o″); the graph-iso brick (A) LANDED (`splitOff_isLink_shiftRelabel_iff`, `Operations.lean:2122`).

**Route β — LOCKED** (user-adjudicated 2026-06-18, KT-source-verified row 242): ONE `v₁`-base, the
uniform `Fin (k+1)` relabel arm; the §(o″) route-B verdict is **within** route β. The
**blueprint-clarity obligation** (route β absorbs KT's isos 6.54–6.56 + ±r chain 6.66, so the
`lem:case-III` general-`d` prose must materialize them): *Hand-off* + design §(n)/§(o)/§(o′)/§(o″).

**Context (closed/landed):** CHAIN-1/3/4 + OD-7 CLOSED; `G.ChainData n` record + 7 accessors landed;
**CHAIN-2a CLOSED**; **CHAIN-2c-i** + **2c-ii-α** + **2c-ii-β** + **2c-ii-graphiso COMPLETE**
(`shiftEdgePerm` + 6 action lemmas + forward + backward + the packaged iff
`splitOff_isLink_shiftRelabel_iff`) landed. Remaining in CHAIN-2c (decomposition + §(o′)(B) fork in
the checklist + *Hand-off*): **2c-ii-transport** (route A/B) → **2c-ii-arm** → **2c-iii** →
**CHAIN-5** + the ENTRY extractor reshape.

**Architectural constraint (standing, CHAIN-3-era).** Metric-using Hodge leaves live in
`MeetHodge.lean`, never the metric-free `Meet.lean` (the `PiL2` import regresses
`complementIso_smul_eq_extensor_join` to a `whnf` timeout) — TACTICS-QUIRKS § 59.

**CHAIN orientation (standing).** The arm-realization engine is already general-`k`; the only
genuinely-`d=3` surface was the dispatch (`case_III_candidate_dispatch`) + its `⋀²ℝ⁴` discriminator —
CHAIN replaces it with the `d`-candidate chain dispatch + the `⋀^{d−1}(ℝ^{d+1})` duality finish (LANDED).
Full source-verified orientation: design §"CHAIN".

**The load-bearing flag (recon (b)) — SETTLED 2026-06-17.** The CHAIN↔ENTRY chain-data contract is
**frozen** (design §"CHAIN↔ENTRY contract"): `G.ChainData n` is the shared shape, reshaped via three
lockstep decls (ENTRY extractor / producer `…hcand` / CHAIN-5 `hdispatch`); no motive/IH change (C.6);
CHAIN-5's signature authorable, the `d=3` line a zero-regression wrapper (C.4).

## CHAIN leaf checklist

The buildable-leaf sequence (exact signatures + dependency order in
`notes/Phase23-design.md` §"CHAIN"(c)/(l)/(m)/(n)/(o)/(o′)). **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 +
CHAIN-2a are CLOSED; CHAIN-2c-i + 2c-ii-α + 2c-ii-β are LANDED.** Remaining: **CHAIN-2c-ii** — §(o′)
decomposed it into **2c-ii-graphiso** (the `shiftPerm`-relabel `splitOff_isLink` brick, next) →
**2c-ii-transport** (route A or B, adjudicated at contact) → **2c-ii-arm** (the closer) — then
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
      **CHAIN-2c — the single-base `Fin (k+1)` family dispatch** (design §(n)+§(o)). KT/d=3 use ONE
      base, ONE `ρ₀`, ONE discriminator → `fin_cases u`; eq. (6.66) is absorbed (no separate 2b under
      route β). Sub-leaves: **CHAIN-2c-i** (`exists_chainData_discriminator_pick`, the panel-LI + the
      one-shot discriminator pick — **LANDED 2026-06-18**, axiom-clean) → **CHAIN-2c-ii** (the uniform
      `Fin d` relabel arm = the genuinely-new crux; **§(o)/§(o′) resolved the route flag: a
      genuinely-new construction, NOT a numeral pass** — KT's `ρᵢ` is a `(i−1)`-cycle, the
      transposition-only engine does not scale). 2c-ii itself decomposes (foundation LANDED, closer
      re-pinned by §(o′)): **2c-ii-α** `ChainData.shiftPerm` (the cycle iso — **LANDED**, axiom-clean)
      → **2c-ii-β** the general-`Equiv.Perm` framework-transport `ofNormals_relabel_perm` (**LANDED**,
      axiom-clean) → **2c-ii-graphiso** the `shiftPerm`/`shiftEdgePerm`-relabel `splitOff_isLink` brick
      (§(o′)(A), the `hiso` supplier) — **COMPLETE 2026-06-19** (axiom-clean): edge cycle
      `ChainData.shiftEdgePerm` + 6 action lemmas (incl. the closure `apply_edge_{top,pred}`) +
      `mem_shiftCycle` + forward + backward + the packaged iff `splitOff_isLink_shiftRelabel_iff` →
      **2c-ii-transport** (**§(o″) ADJUDICATED → route B**, the shared-`ρ₀` row-span transport; route
      A REJECTED as unprovable). Two leaves: **(T-W9a)** the cycle a-column span transport
      `ChainData.funLeft_shiftPerm_dualMap_sub_acolumns_mem_span_rigidityRows` [first buildable; the
      genuinely-new piece, ~2–4 commits — a cycle-induction generalization of W9a
      `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`, one a-column subtraction per moved degree-2
      body] → **(T-W9b)** the cycle bottom-tag transport (mirror `case_III_bottom_relabel`) →
      **2c-ii-arm** `chainData_relabel_arm` (the closer, instantiating `case_III_arm_realization` at
      the relabelled roles with `−ρ₀`; d=3 M₃ is the `i=2` instance) → **CHAIN-2c-iii**
      (`chainData_dispatch` assembly, d=3 a zero-regression wrapper). Full signatures + decomposition:
      design §(o″).
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

**§(o′)(B) fork ADJUDICATED 2026-06-19 → route B (design §(o″)); next = the cycle-W9a transport
`ChainData.funLeft_shiftPerm_dualMap_sub_acolumns_mem_span_rigidityRows` (2c-ii-transport, first
buildable).** CLOSED/LANDED so far (full detail in *Current state* + *Decisions made* + the
checklist): CHAIN-1/3/4 + OD-7 + CHAIN-2a CLOSED; CHAIN-2c-i (`exists_chainData_discriminator_pick`) +
2c-ii-α (`ChainData.shiftPerm`) + 2c-ii-β (`ofNormals_relabel_perm`) + **2c-ii-graphiso**
(`splitOff_isLink_shiftRelabel_iff` + `shiftEdgePerm` + action lemmas, `Operations.lean`) LANDED, all
axiom-clean. The graphiso iff is the `(ρ,σ) = (shiftPerm i.castSucc, shiftEdgePerm i)` intertwiner of
the candidate-`i` split with the `i:=1` base split, for interior `1 < i`.

**The route decision (design §(o″), the canonical adjudication).** The §(o′)(B) arm-closer-transport
fork is **resolved to route B** (the shared-`ρ₀` M₃-style row-span transport). **Route A REJECTED — it
is unprovable as stated:** its required eq.-(6.66) identity `ρᵢ = shiftPerm`-image-of-`ρ₀` equates two
independent `Classical.choice` existentials. The per-`i` candidate `ρ` is extracted via
`Submodule.mem_map` (`Candidate.lean:434`) off the triple existential `(r,lam,i*)` of
`exists_redundant_panelRow_ab_lam_of_rigidOn` (`Candidate.lean:309`); 2a-ii runs its **own** W6b on the
candidate split (`Realization.lean:1005`) producing candidate `i`'s own `ρᵢ`, and `htrans`
(`Realization.lean:961`) is quantified over **that** `ρᵢ` — there is no provable bridge to `ρ₀`. KT
(p. 698, eqs. 6.66–6.67, `.refs/` PDF verified) carries **ONE** `r` and runs the **±r chain** (the
degree-2 fact "similar to (6.44)") to test it against every candidate's panel-meet `C(Lᵢ)` — no
per-candidate W6b. The landed d=3 M₃ (`case_III_arm_realization_M3`, `Relabel.lean:923`; dispatch call
`Realization.lean:588`) is route B at the degenerate `i=2`: one `ρ0`, fed `−ρ0` to M₃, relabel on the
*seed* `qρ = q ∘ swap a v`. **Route B is faithful to both KT and the tree.**

**Route B's genuinely-new piece (FLAGGED — ~2–4 commits, a real construction).** Route B's transport is
the **cycle-generalization of W9a** (`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`,
`Relabel.lean:546`) + W9b (`:653`). The d=3 W9a is a **single** a-column subtraction cancelling the lone
surviving edge of the *single* degree-2 body `a`; KT's `ρᵢ` is the `(i−1)`-cycle moving a **chain of
`i−1` degree-2 bodies**, so it needs a per-step (inductive) subtraction — one stripped column per moved
body (cleanest shape: induction on cycle length; the `shiftPerm` is a `List.formPerm`, the graphiso
brick proves the per-step link correspondence). Leaves: **(T-W9a)** cycle a-column transport [first
buildable] → **(T-W9b)** cycle bottom-tag transport → **2c-ii-arm** `chainData_relabel_arm` (`−ρ₀`,
roles `(vtx i.succ, vtx (i−1).castSucc, vtx i.castSucc)`) → **CHAIN-2c-iii** (`chainData_dispatch`,
`fin_cases u`: `i=1` arm = 2a-ii, interior = `chainData_relabel_arm`; d=3 a zero-regression wrapper) →
**CHAIN-5**. **No motive/IH or spine-carry change (C.6/C.3 unmoved); route β LOCKED.** Caveat: the
commit-count is an estimate — if the per-step subtraction does not telescope cleanly, (T-W9a) splits
further. Full signatures + decomposition: design §(o″).

**Route-A rejection orphans 2c-ii-β `ofNormals_relabel_perm` (row 246) — confirm-and-delete at the
2c-ii-arm build.** Route B is M₃-style (the landed M₃ uses no `ofNormals_relabel`), so the whole-frame
transport `ofNormals_relabel_perm` (built for route A) is very likely unused — grep shows zero callers.
At 2c-ii-arm: confirm `chainData_relabel_arm` doesn't use it (mirroring M₃), then delete it + reword its
2 Operations.lean docstring refs (or keep+re-pin if the arm wants its GP/algindep conjuncts). The
graph-iso `splitOff_isLink_shiftRelabel_iff` (rows 248–250) is **NOT** orphaned — T-W9a is stated
against it. Canonical: design §(o″) coordinator addendum.

- **CHAIN-2c — the single-base `Fin (k+1)` family dispatch (design §(n)/§(o)/§(o′)).** Route β LOCKED
  (user-adjudicated 2026-06-18, KT-source-verified): ONE base `(G₁,q₁)` (the `v₁`-split = `M₀`), ONE
  `ρ₀`, ONE W6b call, ONE discriminator call, then `fin_cases u`; eq. (6.66)'s ±r chain absorbed into
  reusing one `ρ₀`. The relabel arm (2c-ii) covers the interior candidates `2 ≤ i ≤ d−1` (a
  genuinely-new construction, NOT a numeral pass — KT's `ρᵢ` is a `(i−1)`-cycle, the d=3 engines are
  transposition-only); **M₀-arm reuse SETTLED:** 2a-ii (`chainData_split_realization`) is the `i=1`/`M₀`
  arm (its per-`i` split at `i=1` IS the `v₁`-split), the uniform arm does not subsume it (they are the
  `fin_cases`'s direct / relabel legs). The 2c-ii leaf decomposition + the §(o′)(B) fork (**adjudicated
  → route B**, design §(o″)) are in the *Hand-off* lead above (canonical) + design §(o′)/§(o″). No
  motive/IH or spine-carry change. The `G.ChainData n` record + 7 accessors (C.1) are landed; ENTRY owns
  the extractor (C.2).

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
  Two axiom-clean leaves in `CaseIII/Realization.lean`: `chainData_split_w6b_gates` (the W6b half — a
  `{k}`-general flat-tuple lift of the d=3 dispatch's W6b region: one
  `exists_candidateRow_bottomRows_of_rigidOn` call fed `h622lb`, producing the chain-order
  `hρe₀`/`hρGv`/`hw`/`hwmem` bundle; flat-tuple so it is reusable AND callable at `k=2`) and
  `chainData_split_realization` (the re-index core — reads the per-`i` split tuple off the `ChainData`
  accessors, produces `h622lb` from `case_III_nested_rank_lower_all_k`, consumes the W6b bundle, builds
  the `ends₁`-override congruence, calls `case_III_arm_realization`). The §(m) clause-(ii) flag resolved
  to `case_III_arm_realization` directly (no `_M3` relabel — chain `v—a`/`v—b` matches the arm closer's
  `(v,a,b)` roles). **The transversal half stays a hypothesis `htrans`** (single-`i` slot CHAIN-2c
  fills via the discriminator, whose arbitrary panel `u`↔candidate `i` match is the family glue). No
  FRICTION (verbatim d=3-dispatch template re-use over the accessors; the `Fin d`-index `.symm`s and
  the `Gv.Loopless` `haveI` are landed idioms).
- **CHAIN-2b/2c design-pass (2026-06-18) — VERDICT: single-base `Fin (k+1)` dispatch (route β), ±r
  chain absorbed (no separate 2b lemma).** Single base `(G₁,q₁)` / one `ρ₀` / one discriminator /
  `fin_cases u`; reuse 2a-ii only at `M₀`. Route β LOCKED (user-adjudicated, row 242). Detail
  `notes/Phase23-design.md` §(n).
- **CHAIN-2c-ii design-pass (§(o)/§(o′)/§(o″)) — VERDICT: a genuinely-new relabel arm (NOT a numeral
  pass), route B for the transport.** §(o)/§(o′) decomposed 2c-ii-α (`shiftPerm`, LANDED) → 2c-ii-β
  (`ofNormals_relabel_perm`, LANDED) → graphiso (LANDED) → transport → arm; M₀-arm (2a-ii) reused at
  `i=1` only. **§(o″) (2026-06-19) adjudicated the §(o′)(B) route-A/B fork → route B** (shared-`ρ₀`
  row-span, the cycle-W9a/W9b transport); **route A REJECTED** (its eq.-6.66 identity equates two
  `Classical.choice` existentials — unprovable; KT p. 698 carries ONE `r` + the ±r chain, the landed
  d=3 M₃ is route B). No motive/IH/spine-carry change. Detail §"CHAIN"(o)/(o′)/(o″) + *Hand-off* lead.
- **CHAIN-2c-i LANDED 2026-06-18 — the single-discriminator pick (steps 1–3, route β):**
  `exists_chainData_discriminator_pick` (`CaseIII/Realization.lean`, axiom-clean) — the `Fin (k+1)`-panel
  LI feeds the one CHAIN-4d discriminator call → `(u, n')`; verbatim generalization of the green d=3
  discriminator region (`case_III_candidate_dispatch` 435–442), `u` arbitrary. Detail in git + §(o).
- **CHAIN-2c-ii-α LANDED 2026-06-18 — `ChainData.shiftPerm` (KT eq. 6.54)**, the vertex `i`-cycle
  `vtx 1 → ⋯ → vtx i → vtx 1` + action lemmas (`Induction/Operations.lean`, axiom-clean; `formPerm ∘
  ofFn` idiom in FRICTION). Git + §(o).
- **CHAIN-2c-ii-graphiso COMPLETE 2026-06-19** (`Induction/Operations.lean`, axiom-clean) — the
  `hiso` supplier. `ChainData.shiftEdgePerm` (`σ`, edge-side `i`-cycle, `formPerm` on a
  `head::head::head::ofFn` list) + 6 action lemmas (4 interior/fresh + 2 closure `apply_edge_{top,pred}`)
  + `mem_shiftCycle`; the forward leg `splitOff_isLink_shiftRelabel_forward` (candidate→base, cycle
  analogue of d=3 `splitOff_isLink_relabel`), the backward leg `…_backward` (base→candidate: expand the
  base `splitOff`, on-cycle survivor ⇒ `σ e` a base chain edge via `deg_two`, pull `e`/`y` back by
  `σ⁻¹`/`ρ⁻¹` using the 2 closure values + `right_unique`; both-off ⇒ `σ e = e` by injectivity; fresh
  `e₀ ↦ edge 0`), and the packaged iff `…_shiftRelabel_iff` = the §(o′)(A) `hiso`. Internals + 2 new
  golf idioms (`IsLink.right_unique`; `subst`-fails-on-application) → FRICTION.
- **CHAIN-2c-ii-β LANDED 2026-06-18 — `ofNormals_relabel_perm`** (the general-`Equiv.Perm`
  framework-transport, `CaseIII/Relabel.lean`, axiom-clean). **⚠ Built for route A, which §(o″)
  REJECTED — now very likely orphaned** (route B is M₃-style row-span, uses no whole-frame transport;
  zero callers). Confirm-and-delete at the 2c-ii-arm build (*Hand-off* + design §(o″) addendum). Idiom
  (the forced `ρ.symm`/`σ.symm` placement) preserved in FRICTION regardless. Git + §(o)/§(o″).
- **`G.ChainData n` record LANDED 2026-06-18 (CHAIN-2 zeroth leaf)** — the contract-C.1 length-`d`
  chain `structure` (`Induction/Operations.lean`, the `splitOff` home) + accessors `pred_edge_ne`/
  `isLink_edge`. `deg_two` interior vertices guarded by `0 < (i:ℕ)` (no `OfNat (Fin d)` literal),
  predecessor `edge ⟨(i:ℕ)-1,_⟩`; d=3-map (C.4) `rfl`/`decide`-verified; `n` a phantom index. Plus the
  **interior-split geometry accessors** (`{pred_succ_eq_castSucc, isLink_pred_edge, isLink_succ_edge,
  succ_ne_pred_castSucc, deg_two_split}`) exposing the per-`i` `(v,a,b,e_a,e_b)` split tuple. All
  axiom-clean; the `Fin d`-index idiom is in FRICTION.
- **OD-7 `hcontract_k` decomposition (recon 2026-06-18):** 5 leaves, mostly numeral passes; the *one*
  genuinely-new piece LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI
  at `Fin (k+2)`). No motive/IH change → §"CHAIN"(k) + the *Landed OD-7 bricks* paragraph below.

**Landed CHAIN-3 bricks** (the `_grade` lifts are verbatim — the route is general mathlib, grade
enters nothing; `d=3` names kept as `(d:=3)` instances, no blueprint pin moved). CHAIN-3 is CLOSED;
construction internals live in git + `notes/Phase23-design.md` §"CHAIN"(f)/(h) + the
BlueprintExposition CHAIN-3 entry (the duality KT leaves implicit,
`extensor_join_proportional_complementIso_meet`). The two forward cleanup-candidates are the `[~]`
sub-bullet under the *CHAIN leaf checklist* CHAIN-3 entry.

**Landed OD-7 (four-producer tail) bricks** (OD-7 CLOSED 2026-06-18; per-brick names + the `hcontract_k`
five-leaf split + construction internals live in git + commit messages + `notes/Phase23-design.md`
§(k), the canonical home; all axiom-clean).
All four producers + both M4 halves are now general-`k` via verbatim numeral passes over the d=3 bodies
(`screwDim/ScrewSpace 2→k`, `Fin 4→Fin (k+2)`, dof `k→c`; d=3 lemmas now `k:=2` wrappers/instances,
blueprint pins unmoved, §58 idiom). Two settled cross-cutting notes: the *one* genuinely-new piece was
LEAF-0 `linearIndependent_normals_of_algebraicIndependent_triple` (fixed-3-row LI, **not** a numeral
pass — the landed `…_general` gives `k+1` rows, h65 has only 3 vertices); the M4-forget reach-in routes
solely through the CHAIN-3 (h-4) duality + the new slot-0 rescale `extensor_update_smul` (confirming
caveat (e): the duality *is* the only M4-forget d=3 reach-in).

**Landed CHAIN-4 bricks** (CHAIN-4 CLOSED 2026-06-18, `RigidityMatrix/Claim612.lean`; leaf names + per-leaf
verdicts + construction internals live in git + `notes/Phase23-design.md` §(i)/(j), the canonical home;
all axiom-clean). Two settled cross-cutting notes:
4d's `MeetHodge` import did NOT regress the file's `⋀²ℝ⁴` proofs to a §59 whnf timeout; 4b has two faithful
divergences from the d=3 body (off-one-panel hyp + `LinearIndependent ℝ p` conclusion via the new `hpbar`),
so the d=3 lemma stays its own green body, not a `k:=2` wrapper.

**Landed CHAIN-1 bricks** (CHAIN-1 CLOSED 2026-06-18, `RigidityMatrix/Basic.lean`, graph-free over
`ScrewSpace k`, axiom-clean; both single-`Unit` predecessors re-derived as `ιc := Unit` corollaries,
blueprint pins unmoved): the eq.-6.62 row-correspondence swap `linearIndependent_sumElim_candidateBlock_swap`
(+ mirror `…_block_swap`) and the `ιc`-block candidate augment `linearIndependent_sum_pinned_block_augment_block`
(+ `…_augment_candidateRow_block`). The per-candidate column-op heterogeneity (each `i` its own `Φᵢ`) is
**CHAIN-2's** bookkeeping (augment fires one body at a time).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

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
  place* → TACTICS-QUIRKS § 61.
- *A `Fin d`-index relabel proof: destructure `m = m'+1` early so `m-1` reduces to `m'` by `rfl` (kills
  the §61 in-place index rewrites), and bridge `(i.castSucc:ℕ)` to `(i:ℕ)` in `omega` args with `simp
  only [Fin.val_castSucc]` — not `show` (style linter) or `rw [hicv]` (`hicv := rfl` errors)* → FRICTION
  [idiom] *A `Fin d`-index relabel proof over general `d`…*.
- *`Fin d`-index arithmetic at general `d` (no `+1`): a `0 < i` guard / `i - 1` predecessor wants
  `OfNat (Fin d)` literals that don't synth — for plain index bookkeeping (not a `d=0`-false slot),
  guard `0 < (i:ℕ)` + build `⟨(i:ℕ)-1, _⟩` rather than carry `[NeZero d]`* → FRICTION [idiom]
  *`Fin d`-index arithmetic (general `d`): guard `0 < (i:ℕ)`…*.
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
