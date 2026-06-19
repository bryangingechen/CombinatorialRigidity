# Phase 23b — general-`d` Case-III chain dispatch + `⋀^{d−1}` duality [CHAIN] (work log)

**Status:** open. **CHAIN-1 + CHAIN-3 + CHAIN-4 + OD-7 (the four-producer tail) CLOSED** (per-leaf
detail in the checklist + *Decisions made* + git; all four 23a producers + both M4 halves general-`k`).
**Remaining: CHAIN-2 (the `Fin d` reduction layer — T-W9a LANDED, T-W9b single-step + fold core LANDED,
**W9b membership next**) + CHAIN-5 (the dispatch assembly, gated by the ENTRY-contract reshape).** The integer
Phase 23 stays **in progress** — ENTRY / ASSEMBLY remain (coordinator owns the sub-phase boundary;
codes-until-open).

**Orientation.** The **23b (CHAIN layer)** rolling state + hand-off. Cross-phase plan/guidance + the
detailed leaf-level recon live in `notes/Phase23-design.md` (§"CHAIN": (a) per-file reach-ins, (c)
buildable-leaf sequence, (d) green-modulo boundary, (e) OD resolutions); program map
`notes/MolecularConjecture.md`. **Sub-phase codes** (a letter + work log minted when a layer opens, so
a later split costs no renumber-churn): `CARRIER`(=23a, closed), `CHAIN`(=23b), `ENTRY`/`ASSEMBLY`
(code-only until their turn).

## Current state

**Route B LOCKED (§(o″)). T-W9a LANDED; T-W9b STARTED — the single-step framework form + the fold core
LANDED, next commit = (W9b membership).** T-W9b is the cycle bottom-tag transport (per-`i`
generalization of the d=3 `case_III_bottom_relabel`); it has its OWN cycle treatment (a tagged-member
transport, NOT a `wstep` fold reuse), so it decomposes (mirroring how T-W9a split into a
framework-level step → fold core → membership half): **(W9b-step) LANDED** the framework-level
single-step `funLeft_dualMap_bottomTag_mem_rigidityRows` (`Relabel.lean`, axiom-clean) — the
abstract-`Fv`/`Fva` restatement of `case_III_bottom_relabel` (carrier facts as hypotheses, the W9b
analogue of W9a's `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`) → **(W9b fold core) LANDED** the
`List`-induction `bottomTag_foldr_mem_rigidityRows` (`Relabel.lean`, axiom-clean) — a per-step `Tag : ℕ
→ Dual → Prop` threaded through the pure-relabel fold, iterating the single-step at each head-peel
(mirrors `wstep_foldr_mem_span_rigidityRows`; pure relabel, no a-column) → **(W9b membership)** [next]
the `ChainData`/`shiftBodyFramework` instantiation (the `Tag`-shape disjunction from the chain
accessors, `getElem_shiftBodyList` triples + `shiftBodyFramework_supportExtensor` block extensors). The
(T-W9a) membership half `shiftBodyList_foldr_mem_span_rigidityRows` (axiom-clean)
transports `span (G − vᵢ)`-rows → `span (G − v₁)`-rows for `2 ≤ i`; **span-only** — the
`funLeft (shiftPerm i)` relabel bridge stays separate for the arm. Endpoints are **removeVertex**
frameworks, NOT splits (splits enter at the arm). After T-W9b: **2c-ii-arm** → **2c-iii** →
**CHAIN-5** remain. Full decomposition: design §(o″).

**Route β — LOCKED** (user-adjudicated, row 242): ONE `v₁`-base + the uniform `Fin (k+1)` relabel arm;
route B is **within** β. (Blueprint-clarity obligation: *Hand-off* CHAIN-2c bullet + §(o″).)

**Context (closed/landed):** CHAIN-1/3/4 + OD-7 CLOSED; `G.ChainData n` record + 7 accessors;
**CHAIN-2a CLOSED**; **CHAIN-2c-i** + **2c-ii-α/β** + **2c-ii-graphiso COMPLETE**
(`splitOff_isLink_shiftRelabel_iff`) + head-peel + fold core + `shiftBodyList` landed;
**2c-ii-transport-W9a-chain COMPLETE** (`shiftBodyFramework` + `shiftBodyFramework_htrans`);
**T-W9a membership half COMPLETE** (`shiftBodyList_foldr_mem_span_rigidityRows`); **T-W9b single-step
framework form + fold core COMPLETE** (`funLeft_dualMap_bottomTag_mem_rigidityRows` +
`bottomTag_foldr_mem_rigidityRows`). Remaining in CHAIN-2c (full decomposition in the checklist +
*Hand-off*): **2c-ii-transport** (route B: T-W9b membership) → **2c-ii-arm** → **2c-iii** → **CHAIN-5**
+ the ENTRY extractor reshape.

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
      A REJECTED as unprovable). Recursion handle **LANDED:** `ChainData.shiftCycle_eq_cons` +
      `shiftPerm_eq_swap_mul` (`Operations.lean`, axiom-clean) — `shiftPerm i = swap (vtx 1)(vtx 2) *
      (tail formPerm)` via `List.formPerm_cons_cons`, the single-transposition peel the cycle-W9a
      induction composes. T-W9a is now 2 leaves (corrected 2026-06-19 recon, §(o″) addendum): the
      *linear-algebra* layer (fold core, `shiftBodyList`, perm bridge, `wstep_foldr_funLeft_eq`) is
      LANDED; **(T-W9a-chain)** [NEW] — the removeVertex intermediate-framework chain
      `F = ofNormals ∘ shiftBodyGraph` (`shiftBodyGraph s := G − vₛ₊₁`) + its per-step un-relabelled
      link correspondence (the fold core's `hstep` shape) — is **COMPLETE** (`G`-level substrate +
      intermediate-graph layer + the framework chain `shiftBodyFramework` + the per-step `htrans`
      `shiftBodyFramework_htrans`, all LANDED, axiom-clean); **(T-W9a)** the membership half is
      **COMPLETE 2026-06-19** (`shiftBodyList_foldr_mem_span_rigidityRows` + `shiftBodyFrameworkTotal`
      (+ `_eq`), axiom-clean): the fold core gets the six per-step `hstep` conjuncts off the landed
      accessors, transporting `span (G − vᵢ)`-rows → `span (G − v₁)`-rows for `2 ≤ i` (span-only; the
      `funLeft (shiftPerm i)` relabel bridge stays separate for the arm closer)
      → **(T-W9b)** the cycle bottom-tag transport (per-`i` generalization of
      `case_III_bottom_relabel`; decomposed design §(o″): a pure-relabel `(funLeft (shiftPerm
      i)).dualMap` of a *tagged* member, its OWN cycle induction on `shiftBodyList i` — NOT a `wstep`
      fold reuse — re-tagging `(ab)`→`(cv)` per moved body). T-W9b decomposes (mirroring T-W9a's
      step→fold→membership): **(W9b-step) COMPLETE 2026-06-19** — the framework-level single-step
      `funLeft_dualMap_bottomTag_mem_rigidityRows` (`Relabel.lean`, axiom-clean; abstract `Fv`/`Fva`,
      carrier facts as hypotheses) → **(W9b fold core) COMPLETE 2026-06-19** — the `List`-induction
      `bottomTag_foldr_mem_rigidityRows` (`Relabel.lean`, axiom-clean; a per-step `Tag : ℕ → Dual →
      Prop` threaded through the pure-relabel fold, head-peel iterating the single-step) → **(W9b
      membership)** [next] the `ChainData`/`shiftBodyFramework` instantiation →
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

**Route B LOCKED (design §(o″)); no motive/IH/spine-carry change (C.3/C.6 unmoved). T-W9a LANDED;
T-W9b STARTED — single-step framework form + fold core LANDED. next commit = (W9b membership)** the
`ChainData`/`shiftBodyFramework` instantiation of the landed fold core. T-W9b is the cycle bottom-tag
transport — the per-`i`-cycle generalization of the d=3 `case_III_bottom_relabel`
(`CaseIII/Relabel.lean`), a *pure relabel* `(funLeft (shiftPerm i)).dualMap φ` (NO a-column
subtraction) of a **tagged** bottom-family member (genuine `Gv`-row ∨ `(ab)`-block redundancy
disjunct), so it cannot be a `wstep` fold; it is its OWN cycle treatment, re-tagging `(ab)`→`(cv)`
**once per moved body** (KT eq. 6.62 row correspondence + the ±r carry eq. 6.66 — the shared `r`
carried `±r` "because `vᵢ` is degree two", cf. 6.44). It decomposes (mirroring T-W9a's
step→fold→membership): **(W9b-step) LANDED** the framework-level single-step
`funLeft_dualMap_bottomTag_mem_rigidityRows` (`Relabel.lean`, axiom-clean) — the abstract-`Fv`/`Fva`
restatement of `case_III_bottom_relabel` with the carrier facts (degree-2 closure, off-`v`, off-`a`
`htrans`, the `e_c`/`e_b` support-extensor relations) lifted to hypotheses; the W9b analogue of W9a's
`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows` → **(W9b fold core) LANDED** the `List`-induction
`bottomTag_foldr_mem_rigidityRows` (`Relabel.lean`, axiom-clean): a per-step `Tag : ℕ → Dual → Prop`
threaded through the pure-relabel fold `bodies.foldr (fun b T => (funLeft (swap b.2.1 b.1)).dualMap.comp
T) id` (the same swap product as `wstep`'s leading term, `wstep_foldr_funLeft_eq`-identifiable with
`funLeft (shiftPerm i)`); the per-step `hstep` is "the single-step maps `Tag (s+1)` to `Tag s`", the
chaining automatic, head-peel reusing the single-step (mirrors `wstep_foldr_mem_span_rigidityRows`,
generalized over `Tag` instead of carrying `F`) → **(W9b membership)** [next] the
`ChainData`/`shiftBodyFramework` instantiation: define `Tag s` as the bottom-tag disjunction at the
chain step `s` (the `(ab)`/`(cv)` block extensors off `shiftBodyFramework_supportExtensor`, the body
triples off `getElem_shiftBodyList`), supply each `hstep` by `funLeft_dualMap_bottomTag_mem_rigidityRows`
reading the carrier facts off the landed graph/framework accessors. The genuine-row disjunct reuses
T-W9a's `shiftBodyFramework` removeVertex chain. It feeds `case_III_arm_realization`'s `hwmem` slot at
the relabelled roles; the arm closer 2c-ii-arm wires T-W9a's span half + its deferred relabel bridge
(`wstep_foldr_funLeft_eq` + `shiftPerm_eq_prod_map_swap_shiftBodyList`, exposing `funLeft (shiftPerm
i)`) + T-W9b's bottom tags into `chainData_relabel_arm`. **Per-leaf tracker** (checklist CHAIN-2):
T-W9a-chain ✓ → T-W9a ✓ → W9b-step ✓ → W9b fold core ✓ → W9b membership → 2c-ii-arm → 2c-iii →
CHAIN-5. Full decomposition: design §(o″).

**Two orphaned lemmas to confirm-and-delete at the 2c-ii-arm/cleanup commit** (both zero callers; full
detail §(o″)): (1) `ofNormals_relabel_perm` (2c-ii-β, built for the REJECTED route A — route B is
M₃-style); (2) `funLeft_dualMap_sub_acolumn_comp_mem_span_rigidityRows` (the binary composition step,
superseded by the `wstep` fold). The graph-iso `splitOff_isLink_shiftRelabel_iff` is **NOT** orphaned —
it is consumed at the **arm** (`chainData_relabel_arm`'s `hiso`), NOT by T-W9a (which uses the
un-relabelled `shiftBodyGraph_isLink_of_off_body`, not the whole-cycle iff).

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
- **T-W9b decomposed 2026-06-19 (docs-only, §(o″) *T-W9b decomposition*; the stale §(o″)
  pinned-signatures block corrected to the LANDED T-W9a shape).** VERDICT: T-W9b is a genuinely-new
  cycle construction (~1–2 commits, NOT a numeral pass) that does **NOT** reuse the T-W9a `wstep` fold
  core — W9b is a *pure relabel* of a *tagged* bottom member (genuine `Gv`-row ∨ `(ab)`-block), so it
  is its OWN cycle induction on `shiftBodyList i`, re-tagging `(ab)`→`(cv)` once per moved body (KT
  eq. 6.62/6.66 ±r carry, source-verified p.696–698). `chainData_relabel_arm` shape unchanged. The
  dead `funLeft_shiftPerm_dualMap_sub_acolumns_…` pin (never built) is removed. Detail §(o″).
- **T-W9b single-step framework form LANDED 2026-06-19** (`Relabel.lean`, axiom-clean) —
  `BodyHingeFramework.funLeft_dualMap_bottomTag_mem_rigidityRows`, the framework-level restatement of
  `case_III_bottom_relabel`: abstract `Fv`/`Fva`, the carrier facts (degree-2 closure, off-`v`, off-`a`
  `htrans`, the `e_c`/`e_b` support-extensor relations `Fv.supportExtensor e_c = Cca`,
  `Fva.supportExtensor e_b = Cab`) as hypotheses. The W9b analogue of W9a's
  `funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`; the per-step the (next) W9b fold core iterates.
  Genuine-row disjunct: three-way split (`x=a`/`y=a`/off, the degree-2 case landing the `(cv)`-tag);
  `(ab)`-tag → genuine `e_b`-row of `Fva`. No `eq_and_eq_or_eq_and_eq` disjunct-order friction beyond
  the known idiom.
- **T-W9b fold core LANDED 2026-06-19** (`Relabel.lean`, axiom-clean) —
  `BodyHingeFramework.bottomTag_foldr_mem_rigidityRows`: the `List`-induction iterating the single-step
  W9b over a framework chain, threading a per-step `Tag : ℕ → Dual → Prop` so the `(ab)`/`(cv)`
  block-tag chaining is automatic (each `hstep` = "single-step maps `Tag (s+1)` to `Tag s`"). The fold
  is the pure-relabel `bodies.foldr (fun b T => (funLeft (swap b.2.1 b.1)).dualMap.comp T) id` (same
  swap product as `wstep`'s leading term, `wstep_foldr_funLeft_eq`-identifiable with `funLeft (shiftPerm
  i)`; no a-column, unlike W9a). Proof = the same head-first-fold + shifted-chain `List` induction as
  `wstep_foldr_mem_span_rigidityRows`, generalized over `Tag` instead of carrying `F`; `simpa` handles
  all fold/index bookkeeping (no new friction).
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
**2c-ii-β** `ofNormals_relabel_perm` — **⚠ orphaned** (route A REJECTED; confirm-and-delete at the
2c-ii-arm build, *Hand-off* orphan flag). **OD-7 `hcontract_k`** = 5 leaves (mostly numeral passes; the
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
