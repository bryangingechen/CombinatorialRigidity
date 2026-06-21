# Phase 23c — Case III general `d`: the redundancy-carry re-architecture + chain-dispatch completion (work log)

**Status:** open (opened 2026-06-21 at a user-adjudicated clean-break close of 23b). The integer **Phase 23
stays in progress**; ENTRY + ASSEMBLY remain later sub-phases (codes; the cross-phase plan + the
detailed route history live in `notes/Phase23-design.md`, program map `notes/MolecularConjecture.md`).

**What 23c picks up.** 23b (CHAIN) landed the CHAIN bricks (CHAIN-1/3/4, OD-7, CHAIN-2a, the `hρGv`
algebraic core + chain-induction + perp + slot machinery — all axiom-clean) but **could not reach** the
`hρGv` Case-III chain arm + `chainData_dispatch` (CHAIN-2c-iii) + CHAIN-5, because the arm's `hρGv` slot ran
into a hard core: the **member-mapping wall**, now decisively characterized as **intrinsic to KT's argument**
(not a Lean artifact — design §(o‴)(I.8.18)–(I.8.20), 2026-06-21). The **(A)-feasibility recon is DONE**
(design §(o‴)(I.8.21), 2026-06-21): (A) escapes the wall but requires a rank-certification re-architecture
(below the contract/motive). The user adjudicated the fork → **OPEN OPTION (A), de-risk-first**.

**FIRST build LANDED — `case_III_rank_certification_chain` (2026-06-21, §I.8.24(3)).** The forked general-`d`
Case-III rank cert is in tree (`Candidate.lean`, after `finrank_span_rigidityRows_ge_of_corner`), axiom-clean,
build/lint clean. It consumes the corner data `(W, hWS, hWcard, ι/hιcard, g, hg, hLI)` and wires the de-risk leaf
`finrank_span_rigidityRows_ge_of_corner` to the target rank `D(|V(G)|−1)` via the count `finrank W + D =
D(m_v−1) + D = D·m_v = D(|V(G)|−1)` (`hVone`/`hVcard` + `Nat.mul_succ`). **NO `hρGv` slot** — the wall is gone:
the cert is selector-agnostic and reads off the corner block, so KT's `±r` row (eq. (6.66)) enters as a member of
`g` (a genuine candidate-edge row), never as the collapsed fixed-member `hingeRow v a ρ`. This is the make-or-break
§I.8.24(1) step proved in Lean: the `W`/`g`/`hLI` shapes type-check against the actual de-risk-leaf signature, (A)
escapes the wall. The cert carries the corner data `(hWS, hWcard, hg, hLI)` as hypotheses (the project's
explicit-`h…`-hypothesis idiom); the chain ARM produces them — that is the next sub-step.

**De-risk spike landed (2026-06-21, the §I.8.21(2b)(α) hardest leaf).** The genuinely-new + cost-unknown
hardest leaf — the **basis-free block-rank-additivity lower bound** — is **DONE and axiom-clean**, with a
**clean POSITIVE de-risk verdict: the `ScrewSpace ≃ₗ`/§38-defeq friction did NOT bite.** Two decls:
(α) the abstract LA lemma `Submodule.finrank_add_card_le_of_linearIndependent_mkQ`
(`Mathlib/LinearAlgebra/Dimension/Constructions.lean`, the mirror) — `W ≤ S`, a family `g` in `S` with
`W.mkQ ∘ g` linearly independent ⟹ `finrank W + |ι| ≤ finrank S` — proved in ~10 lines off the *existing*
`finrank_map_mkQ` + `finrank_span_eq_card`; and (β) the carrier instantiation
`BodyHingeFramework.finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean`, right after
`case_III_rank_certification`) on the *actual* `Module.Dual ℝ (α → ScrewSpace k)` carrier, which goes through
by `inferInstance` on the ambient finite-dimensionality — **the `ScrewSpace` carrier is never unfolded**. So
the STOP-and-escalate-to-an-explicit-`Matrix`-model branch is NOT triggered: the basis-free `finrank (span …)`
carrier *does* admit KT's `rank Mᵢ + rank(base∖row)` block lower bound (6.64–6.65), with the corner block `Mᵢ`
entering as the `|ι|` rows of `g` independent modulo the base `W`. See *Hand-off*.

> **Orientation for the next agent.** Read this *Current state* + the *Hand-off* (the FIRST build commit
> `case_III_rank_certification_chain` is LANDED; the next build is `case_III_arm_realization_chain`, which produces
> the cert's corner-data hypotheses) in full, then the design doc §(o‴)(I.8.24) (the cert-re-shape pin, with (3)
> the buildable-leaf decomposition) — the `M₃` arm `case_III_arm_realization_M3` (`Relabel.lean:2537`) is the
> closest template for the arm (it produces the analogous corner data at the single-swap `d=3` instance). Do
> **not** re-attempt any of the four dead route families (below) — they are exhausted and adversarially verified.
> The standing decision is the user-adjudicated fork in *Hand-off*; the next moves are BUILDS, no longer
> architectural decisions.

## Current state — the architectural decision 23c must make first

The Case-III chain arm `case_III_arm_realization` needs its `hρGv` slot filled at the **candidate** framework
`(G−vᵢ, endsσρ, qρ)`: `hingeRow vᵢ₊₁ vᵢ₋₁ ρ0 ∈ span (ofNormals (G−vᵢ) endsσρ qρ).rigidityRows`, for the
**single shared** `ρ0` the dispatch establishes once at the base and feeds the discriminator
(`case_III_candidate_dispatch`, `Realization.lean:388–441`: A-1 fired once → one `ρ0` → discriminator once
on `ρ0`, threaded into every arm; the capstone `Claim612.lean:1462` takes ONE `r`). **Producing that fixed
`ρ0`-member at the relabelled candidate is the wall.** Every route to it is dead, and the reason is now
source-verified: **KT itself carries a *moving* redundant row** — KT (6.62, p. 696) maps the redundant row
`(v₀v₂)ᵢ∗ ⇔ (v₀v₁)ᵢ∗`, so in KT the candidate-side redundancy sits on the *moved* `(v₀v₁)` pair, never a
fixed `(v₀v₂)`. **No fixed-member transport could ever have existed.** (Full verdict: design §(o‴)(I.8.20).)

**Why `d=3` succeeded and is NOT a template.** At `d=3` the relabel `ρᵢ` is a **single swap** (M₃, `i=2`).
`case_III_arm_realization_M3` (`Relabel.lean:2562`) consumes the base redundancy at the **genuine** base
`(ends₀, q)`, applies **one** W9a step (`funLeft_dualMap_sub_acolumn_mem_span_rigidityRows`) that moves the
member once (`a↦v`, scalar `ρ0` kept), and the moved member `hingeRow v b ρ0` *is a genuine candidate row* —
closed by `sub_mem`. There is **no fold, no intermediate framework, no fixed-member demand**: the wall is an
*emergent obstruction of the multi-step composition*, absent at length 1. `d=3` is the degenerate case
(`DESIGN.md` *A degenerate headline case is a target, not a template*); its single-step move-and-recombine is
not a template for the general cycle.

**The gate.** At general `d`, `ρᵢ` is an `(i−1)`-**cycle**. Composing the moves needs the (6.66) ±r chain —
which 23b *built correctly* (the telescope `wstep_foldl_hingeRow_telescope` + LEAVES 1–4). The defect is the
*anchoring*: the seed-advancing fold pre-applies the whole relabel to the **selector** (`endsσρ`) and advances
only the **seed**, manufacturing the artifact framework `(endsσρ, q)` (relabelled selector + un-advanced base
seed — `Relabel.lean:4671`) that KT never forms and that demands the fixed base member. The per-step move that
*could* keep the fold anchored at the genuine base — the "gate" lemma
`funLeft_dualMap_sub_acolumn_seedAdvance_mem_span_rigidityRows` (`Relabel.lean:1201`) — carries a hypothesis
`hends'_off` (`:1204`) permitting the selector to change only on the two edges `{edge(s+1), edge(s+2)}` local
to that step's swap (the support-extensor coincidence needs it). So `(i−1)` gated steps can move the selector
only on `⋃ₛ {edge(s+1),edge(s+2)} = {edge 1,…,edge i}`, but the cycle `shiftEdgePerm i` moves `edge 0`/`e₀`
(*outside* that window) — **an `(i−1)`-cycle has no adjacent-transposition factorization** (design §I.8.15).
At `d=3` one swap *is* trivially adjacent, so the gate handles it; only the *cycle accumulation* defeats it.

**The four dead route families (do not re-attempt; adversarially verified):** (1) seed-advancing fold —
infeasible (§I.8.15); (2) base→candidate transport — the member-mapping wall (§I.8.12); (3) source-production
/ re-fire the existential A-1 at the candidate — refuted, yields a fresh `ρ_cand ≠ ρ0`, re-introduces the
design-rejected Fix B (§I.8.19-ADDENDUM); (4) column-op / whole-matrix submatrix-containment — the wall is
KT's own (6.62), it offers only the member-*moving* relabel-image inclusion (§I.8.20).

## The architectural fork (user-adjudication; the (A)-recon verdict is in — §I.8.21)

**(A) Re-architect KT-faithfully — the only root-attacking route; feasibility RECON DONE (§I.8.21).** Carry
the redundancy as KT does: the abstract `r ∈ ℝ^D` of (6.66) — which §I.8.21 found **IS already the project's
`ρ₀`** (A-1's `ρ₀ = ∑ⱼ lamAB j • rab j`, `Candidate.lean:432`) — and the **`Mᵢ`-block / `±r` decomposition**
`rank R(G,pᵢ) ≥ rank Mᵢ + rank(R(G₁∖row,q₁))` (6.64–6.65), where the redundancy is a `±r` ℝ^D-EQUALITY (6.66),
never a fixed dual-functional transported across the relabel. **VERDICT (§I.8.21): (A) escapes the wall, but
does NOT feed the existing engine** — the engine's `hρGv` slot IS the wall (the rank-cert consumes it once as
a fixed-member candidate membership, `Candidate.lean:1606–1611`), so (A) requires **re-shaping
`case_III_rank_certification` + `case_III_arm_realization`** (below contract C.0–C.6 + motive; `d=3` M₃
zero-regression preserved by forking the rank-cert). Sub-route *non-gate composition* is DEAD (collapses to
the wall); sub-route *matrix/abstract-`r`* is the live route. **Both de-risk spikes are CLOSED POSITIVE:**
(2b)(α) block-rank-additivity LANDED (axiom-clean, no carrier friction); **(2b)(γ) the (6.66) `±r` ℝ^D-vector
identity** (the wall-escape: redundancy carried as a fixed abstract `r` while the member moves) was found
**already built** in tree (the 23b chain induction `candidateRow_ac_eq_neg` + `interior_group_acolumn_eq_neg_
baseRedundancy`, both axiom-clean; §I.8.23) — the column read-off localizes cleanly, KT proves (6.66) "in a
manner similar to (6.44)". **Remaining cost band: ~5–9c**, all of it the cert/arm re-shape consuming the landed
`±r` (NO `hρGv`) + wire-up + cleanup (see *Current state* / *Hand-off* / design §I.8.21–§I.8.23).

**(B) Carry `ρ0`/`hφ@endsσρ` to ENTRY — LEAST KT-faithful, likely-dead, does NOT attack the root.** Add
`hφ@endsσρ` as a hypothesis on the arm/dispatch (the landed `chainData_relabel_arm_hρGv` shape) and confront
the wall at ENTRY. Flagged likely-dead (§I.8.20: the wall is a property of the relabel-image map, not of what
is in scope; the only non-circular escape is ENTRY re-deriving the redundancy *natively* against `endsσρ` — a
graph-construction question, unexplored). Only the residue if (A) is held / its de-risk fails.

**Status: (A) is OPEN, de-risk-first (user-adjudicated). Both de-risk spikes LANDED POSITIVE; the cert-re-shape
design-pass is DONE.** (2b)(α) block-rank-additivity is axiom-clean (no carrier friction); (2b)(γ) the (6.66)
`±r` ℝ^D-vector identity is POSITIVE + already built (LEAF 1–4, axiom-clean; §I.8.23). **The §(I.8.24)
cert-re-shape design-pass (2026-06-21) RESOLVED the §I.8.22-vs-§I.8.23 tension: (A) escapes the wall.** The
make-or-break — does the re-shaped cert use only the buildable relabel-image inclusion (for `W` + base) + the
member-free `±r` value (for the `Mᵢ` row), or does some `hWS`/`hg`/`hLI` smuggle in a fixed-member dependency? —
was settled per-hypothesis against the landed de-risk-leaf signature + §I.8.20(e): **each of `hWS`/`hg`/`hLI` is
the buildable kind.** The wall lived ONLY in the landed cert's COLLAPSED `Unit` row (`hingeRow v a ρ`, needing
`hρGv`); the re-shape sources the `±r` row as KT's GENUINE candidate-edge `(vᵢvᵢ₊₁)ᵢ∗` row, killing the `hρGv`
slot. The cert is FORKED (d=3 keeps the landed `hρGv`-collapse engine verbatim; general-`d` got the new
`±r`-cert). **The FIRST build `case_III_rank_certification_chain` is LANDED** (2026-06-21, axiom-clean; *Current
state*); the next concrete commit is `case_III_arm_realization_chain` (produce + consume the cert's corner-data
hypotheses). See *Hand-off*.

## What 23b delivered (the foundation 23c builds on)

All axiom-clean; full inventory + verdicts in `notes/Phase23b.md` *Landed-leaf inventory* + design
§(o‴)(I.6)/(I.8). Headlines:
- **CHAIN-1** (`RigidityMatrix/Basic.lean`) — the eq.-6.62 row-correspondence swap + `ιc`-block augment +
  `columnOp` (the LI-side column op; *not* a span-membership identity — F4).
- **CHAIN-3** (`Meet`/`MeetHodge.lean`) — the `⋀^{d−1}W`-is-a-line duality.
- **CHAIN-4** (`Claim612.lean`) — the `Fin (d+1)` incidence + Claim-6.12 discriminator capstone
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (takes ONE `r`).
- **OD-7** — the four reduction producers (`hbase_k`/`hcut_k`/`hcontract_k`/`hforget_k`) + M4, all general-`k`.
- **CHAIN-2a** — `chainData_split_w6b_gates` + `chainData_split_realization`.
- **CHAIN-2c-i/ii** — the `ChainData` record + accessors; `shiftPerm`/`shiftEdgePerm` + graph-iso; the
  `hwmem` genuine-row brick `chainData_bottom_relabel`; the **(6.66) telescope**
  `wstep_foldl_hingeRow_telescope` + LEAVES 1–4 (the composed moves — KT-faithful *output*); the per-edge
  perp leaves + STEP-2 transport; and `chainData_relabel_arm_hρGv` (a **correct carried-hypothesis lemma**
  whose `hφ@endsσρ` slot is the wall).

**Salvageable vs orphan-candidate (decide at the architecture-settle).** The telescope + LEAVES 1–4 (the
composed moves) and the perp sub-tree have **KT-faithful output** and are likely reusable under (A); the
**seed-advancing fold spine** (slot core `chainData_freshEdge_slot_mem`, fold
`shiftBodyListAsc_foldl_mem_span_rigidityRows`, the gate `:1201`, `chainData_relabel_arm_hρGv`) is the
**orphan-candidate** (dead-for-the-fixed-member-route, but its fate is the architecture decision's to make —
do NOT delete until 23c settles the route). The ROUTE-α leaf 1 `shiftEndsAdv` + `_zero`/`_succ` + T-1/T-2 are
already orphaned (confirm-and-delete at the settle commit). `d=3` M₃ (`i=2`) is **zero-regression** — no
`hφ` slot, no fold — and must stay green throughout.

## Remaining work in Phase 23 (after the arm settles)

1. **The forked general-`d` chain cert + arm** (§I.8.24) → the `±r`-based engine, NO `hρGv` (replaces the dead
   `hρGv` chain arm). d=3 keeps the landed engine. **Cert `case_III_rank_certification_chain` ✓ LANDED**
   (2026-06-21); the arm `case_III_arm_realization_chain` (discharges the cert's corner-data hypotheses) is the
   next build (*Hand-off*).
2. **CHAIN-2c-iii `chainData_dispatch`** (replaces `case_III_candidate_dispatch`; the general-`k` dispatch;
   routes interior `2 ≤ i < d` through the chain arm, d=3 floor on the landed engine).
3. **CHAIN-5** — wire the dispatch into the spine to discharge `hdispatch`.
4. **ENTRY** — reshape `Graph.exists_chain_data_of_noRigid` (`Reduction.lean:383`) to the `G.ChainData n`
   producer `exists_chainData_of_noRigid` (KT Lemma 4.6 chain + Lemma 4.8 split-off, general `d`); lift the
   `6 ≤ bodyBarDim n` floor; resolve the chain/cycle dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4). Consumer:
   `case_III_hsplit_producer_all_k` (`Arms.lean:777`). The CHAIN↔ENTRY `G.ChainData n` contract is **frozen**
   (design §"CHAIN↔ENTRY contract", C.0–C.6; no motive/IH change; `d=3` zero-regression).
5. **ASSEMBLY** — compose the honest general-`d` Theorem 5.5, re-green `prop:rigidity-matrix-prop11` + `hub`,
   derive Thm 5.6, state Conjecture 1.2.

**Contract/motive note.** The wall is machinery *below* the contract — no C.0–C.6/motive change is forced by
it. §I.8.21 confirmed: option (A)'s rank-cert re-architecture re-shapes `case_III_rank_certification` +
`case_III_arm_realization` only — it does **not** touch the dispatch's `hdispatch` consume-shape (C.3), the
`ChainData` record (C.1), or the 0-dof motive/IH (the dispatch threads one `ρ₀` either way).

## Blueprint-clarity obligation (carried from 23b — owner-flagged)

The `lem:case-III` general-`d` node's exposition must materialize KT's index-shift isos (6.54–6.56) + ±r chain
(6.66) explicitly (the Lean economizes; the prose must not), and — per this session's `BlueprintExposition.md`
sharpening — present the redundancy-carry as **whole-matrix bookkeeping with `r` abstract and the member
moving**, flagging the fixed-functional-transport shape as the trap. Written at phase-close once the arm is
`sorry`-free.

## Hand-off / next phase

**FIRST build LANDED: `case_III_rank_certification_chain` (2026-06-21, axiom-clean, build/lint clean).** The
forked general-`d` Case-III rank cert is in tree (`Candidate.lean`, after
`finrank_span_rigidityRows_ge_of_corner`), proving §I.8.24(1) type-checks in Lean: it consumes the corner data
`(W, hWS, hWcard, ι/hιcard, g, hg, hLI)`, applies `finrank_span_rigidityRows_ge_of_corner` (`finrank W + |ι| ≤
finrank (span candidate.rigidityRows)`), and closes the count `finrank W + D = D(m_v−1) + D = D·m_v =
D(|V(G)|−1)` (`hVone`/`hVcard` + `Nat.mul_succ`). **NO `hρGv`** — the wall is gone. The supporting de-risk decls
already in tree: `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` + `…exists_le_finrank_eq_card_of_
injective_map` (mirror, `Mathlib/LinearAlgebra/Dimension/Constructions.lean`),
`BodyHingeFramework.finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean`), the `±r` identity
`interior_group_acolumn_eq_neg_baseRedundancy = −ρ₀` (`Relabel.lean:4039`).

**Next concrete commit — `case_III_arm_realization_chain` (`Arms.lean`, beside the engine; §I.8.24(3)).** It
consumes `case_III_rank_certification_chain` and DISCHARGES its corner-data hypotheses from the in-scope chain
data, the way `case_III_arm_realization_M3` (`Relabel.lean:2537`, the closest template) produces the engine's
`hρGv` at the single-swap `d=3` instance. The four obligations:
- **`hWS : W ≤ span candidate.rigidityRows` + `hWcard : finrank W = D(m_v−1)`** — instantiate
  `Submodule.exists_le_finrank_eq_card_of_injective_map` at `L = (funLeft (shiftPerm)⁻¹).dualMap` (injective; the
  M₃ arm's `hw` route `Relabel.lean:2729`), `f = the base LI family` of card `D(m_v−1)`, `hS` = the span-level
  `chainData_bottom_relabel` (genuine→genuine, member-MOVING; §I.8.20(e)). Gives `W` with the right `finrank`.
- **`g` (the `D` corner rows) + `hg`** — `g` = the `D−1` candidate panel rows `r(Lᵢ)` (`panelRow_mem_rigidityRows`,
  free) ⊕ the `±r` row sourced as A-1's genuine candidate-EDGE group `∑_{ev j = edge i} c j • hingeRow …` of
  `hcombGv` (`Candidate.lean:441`), transported to candidate rows by the same relabel-image map as `hWS`.
- **`hLI : LinearIndependent (W.mkQ ∘ g)`** — the `Mᵢ`-corner full rank mod the base. The `±r` row's class mod `W`
  reads at `vᵢ`'s column as `−ρ₀` (`interior_group_acolumn_eq_neg_baseRedundancy`), so LI-mod-`W` reduces to
  `ρ₀ ⊥ C(Lᵢ)` on the discriminator `hρgate` at the FIXED `ρ₀` (= KT's abstract `r`). The shared W6a–W6f arm tail
  then lifts verbatim (it operates on the rank bound, agnostic to how certified).
- **Then:** the 2c-iii `chainData_dispatch` routing interior `2 ≤ i < d` through the chain arm (d=3 floor stays on
  the landed engine) → CHAIN-5 wire-up → orphan confirm-and-delete (the seed-advancing `hφ`-spine + the
  telescope's *membership* content, §I.8.20/§I.8.21(3); the `±r` chain induction LEAF 1–4 STAYS). **Cost band:
  ~4–8 commits remaining.** Audit trail: design §(o‴)(I.8.24), the `lem:case-III general-d` ledger.

## Decisions made during this phase

- **FIRST build `case_III_rank_certification_chain` LANDED (2026-06-21), §I.8.24(1) type-checks in Lean.**
  The forked general-`d` Case-III rank cert (`Candidate.lean`, after `finrank_span_rigidityRows_ge_of_corner`),
  axiom-clean, build/lint clean. It is a *re-statement consuming landed bricks*: takes the corner data
  `(W, hWS, hWcard : finrank W = D(m_v−1), ι/hιcard : |ι| = D, g, hg, hLI)` as hypotheses (the project's
  explicit-`h…`-hypothesis idiom — the chain ARM discharges them next), applies
  `finrank_span_rigidityRows_ge_of_corner`, and closes the count `finrank W + D = D·m_v = D(|V(G)|−1)` via
  `Nat.mul_succ` (needs `hVone : 1 ≤ |V(Gv)|` + `hVcard`). **NO `hρGv` slot** — the cert is selector-agnostic and
  reads off the corner block, so KT's `±r` row enters as a member of `g`, never the collapsed fixed-member row.
  Confirms (A) escapes the wall in Lean, not just on paper.
- **`hWS` base-block-as-subspace packaging leaf landed (2026-06-21), closing the FIRST-build sub-risk
  §I.8.24(3).** `Submodule.exists_le_finrank_eq_card_of_injective_map` (mirror,
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`): `f` LI + `L` injective + `∀ i, L (f i) ∈ S` ⟹ a
  `W' ≤ S` with `finrank W' = |ι|` (image span; `LinearIndependent.map'` along injective `L` +
  `finrank_span_eq_card` + `span_le`, a 3-line term proof). Axiom-clean, build/lint clean. Instantiated at
  `L = (funLeft (shiftPerm)⁻¹).dualMap` it packages the relabel-image base block as the chain cert's `W` with
  `finrank W = D(m_v−1)` — so the cert's `hWS` is now a consume-landed-brick step, not a wall. Next: the cert
  itself, whose only genuinely-new content is the `hLI` discriminator-mod-`W` reduction.
- **Opened at a user-adjudicated clean-break close of 23b (2026-06-21).** 23b's CHAIN target (the chain
  dispatch) was not reached — the `hρGv`-seam is a hard core (the member-mapping wall, intrinsic to KT). 23b
  closes on its delivered bricks + the decisive hard-core characterization; the arm/dispatch re-architecture
  carries to 23c, whose first move is an architectural decision, not a build. Rationale: design
  §(o‴)(I.8.18)–(I.8.20); the d=3-is-degenerate / read-the-source-early lessons (`DESIGN.md`, model-exp
  Findings 2026-06-21).
- **Option (A) de-risk spike landed POSITIVE (2026-06-21).** The §I.8.21(2b)(α) hardest + cost-unknown leaf —
  basis-free block-rank-additivity — is axiom-clean and the `ScrewSpace`/§38-defeq friction did NOT bite.
  `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` (mirror) proves `W ≤ S` + `g`-in-`S` +
  `W.mkQ ∘ g` LI ⟹ `finrank W + |ι| ≤ finrank S` in ~10 lines off the *existing* `finrank_map_mkQ` +
  `finrank_span_eq_card` (no new LA machinery); `finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean`)
  instantiates it on `Module.Dual ℝ (α → ScrewSpace k)` by `inferInstance`, never unfolding the carrier. So
  the basis-free API carries KT's `rank Mᵢ + rank(base∖row)` (6.64–6.65); the STOP-and-escalate-to-`Matrix`
  branch is closed. Next: re-pointed to (2b)(γ) by the §I.8.22 pin recon (below).
- **(2b)(β)/(2b)(γ) de-risk recons → both settled, subsumed by §I.8.24 (§I.8.22/§I.8.23, 2026-06-21).** (2b)(β):
  the landed cert already realizes KT's `Mᵢ + base` inline (`(sn ⊕ Unit) ⊕ ιb`), the wall is its `hρGv` slot, not
  a missing `Mᵢ` corner. (2b)(γ): the (6.66) `±r` ℝ^D-identity is POSITIVE + already built (LEAF 1–4, axiom-clean,
  `interior_group_acolumn_eq_neg_baseRedundancy = −ρ₀` member-free). Detail: design §(o‴)(I.8.22)/(I.8.23).
- **§(I.8.24) cert-re-shape design-pass → (A) ESCAPES THE WALL; the §I.8.22-vs-§I.8.23 tension RESOLVES
  FAVORABLY (2026-06-21, docs-only).** Settled per-hypothesis against the landed de-risk-leaf signature +
  §I.8.20(e): the de-risk leaf's `hWS`/`hg` are the BUILDABLE relabel-IMAGE inclusion (member-moving) + genuine
  candidate rows, `hLI` the discriminator at the FIXED `ρ₀` + the `±r` value — NONE smuggles a fixed-member
  dependency. The KEY: the cert is selector-AGNOSTIC (parametric in `(G,Gv,ends,q)`, same selector both sides,
  `hFvle` direct `:1551`); the relabel lives in the ARM's arguments (M₃ instantiates the engine `:2624`); the
  wall is ONLY the landed cert's COLLAPSED `Unit` row (`hingeRow v a ρ`, needing `hρGv` `:1606`), which the
  re-shape replaces with KT's genuine candidate-edge row. Pinned: FORK — d=3 keeps the landed engine,
  general-`d` gets `case_III_rank_certification_chain` + `_arm_realization_chain`. FIRST build =
  `case_III_rank_certification_chain` (sub-risk: package the relabel-image base block as a subspace `W` with
  `finrank W = D(m_v−1)`, `LinearIndependent.map'` route). ~5–9c. Detail: design §(o‴)(I.8.24).
