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

> **Orientation for the next agent.** Read this *Current state* + the *Hand-off* (the (A)-recon verdict) in
> full, then the design doc §(o‴)(I.8.18)–(I.8.21) (the dead-route verdicts + the (A) go/no-go) and the
> `BlueprintExposition.md` `lem:case-III general-d` "source-side sharpening" entry (the KT-faithful shape).
> Do **not** re-attempt any of the four dead route families (below) — they are exhausted and adversarially
> verified. The standing decision is the user-adjudicated fork in *Hand-off*.

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
the wall); sub-route *matrix/abstract-`r`* is the live route. **The genuinely-new infra was RE-IDENTIFIED by
the §I.8.22 (2b)(β) pin recon** (the de-risk block-rank lemma LANDED but is NOT the (A) consumer the prior pin
expected; the `Mᵢ` corner is already inline in the landed cert): the genuinely-new, root-attacking leaf is
**(2b)(γ) the (6.66) `±r` ℝ^D-vector identity** (the wall-escape: redundancy carried as a fixed abstract `r`
while the member moves), NOT (2b)(β). **Remaining cost band: ~6–11c**, FIRST genuinely-new commit = (2b)(γ)
(see *Current state* / *Hand-off* / design §I.8.22).

**(B) Carry `ρ0`/`hφ@endsσρ` to ENTRY — LEAST KT-faithful, likely-dead, does NOT attack the root.** Add
`hφ@endsσρ` as a hypothesis on the arm/dispatch (the landed `chainData_relabel_arm_hρGv` shape) and confront
the wall at ENTRY. Flagged likely-dead (§I.8.20: the wall is a property of the relabel-image map, not of what
is in scope; the only non-circular escape is ENTRY re-deriving the redundancy *natively* against `endsσρ` — a
graph-construction question, unexplored). Only the residue if (A) is held / its de-risk fails.

**Status: (A) is OPEN, de-risk-first (user-adjudicated). The de-risk spike is LANDED POSITIVE**, but the
(2b)(β) PIN RECON (§I.8.22, 2026-06-21) RE-POINTED the next leaf: (2b)(β) is **mis-targeted** (the landed cert
already IS KT's `Mᵢ + base` decomposition inline, and the de-risk leaf consumes the dead relabel-image
inclusion, not produces it), the single-panel discriminator is **correct** (not a mismatch), and the genuinely-
new root-attacking leaf is **(2b)(γ) the (6.66) `±r` ℝ^D-vector identity** — NOT a telescope re-statement (the
landed telescope is `hingeRow`-carrier, (6.66) is `ScrewSpace`-vector-carrier). The next concrete commit is the
(2b)(γ) recon-or-spike. See *Hand-off*.

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

1. **The `hρGv` Case-III chain arm** (under the chosen architecture) → fills `case_III_arm_realization`'s slot.
2. **CHAIN-2c-iii `chainData_dispatch`** (replaces `case_III_candidate_dispatch`; the general-`k` dispatch).
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

**The (A) de-risk spike is LANDED with a clean POSITIVE verdict (2026-06-21).** The hardest leaf — the
basis-free block-rank-additivity lower bound — is axiom-clean (both decls; see *Current state* + the
*Decisions made* entry), and it instantiates on the *actual* `Module.Dual ℝ (α → ScrewSpace k)` rigidity-row
carrier with **no `ScrewSpace ≃ₗ`/§38-defeq friction** (the carrier is never unfolded; only the ambient
finite-dimensionality is consumed, by `inferInstance`). **The STOP-and-escalate-to-an-explicit-`Matrix`-model
branch is NOT triggered: the basis-free `finrank (span …)` API carries KT's `rank Mᵢ + rank(base∖row)`
decomposition.** The two new decls:
- `Submodule.finrank_add_card_le_of_linearIndependent_mkQ` (mirror,
  `Mathlib/LinearAlgebra/Dimension/Constructions.lean`) — the abstract LA block-rank-additivity lemma.
- `BodyHingeFramework.finrank_span_rigidityRows_ge_of_corner` (`Candidate.lean`, after
  `case_III_rank_certification`) — the carrier instantiation; the option-(A) rank-cert's intended `finrank
  W + |ι| ≤ finrank (span F.rigidityRows)` shape, fit for the `Mᵢ`-corner certification.

**Next concrete commit — RE-POINTED by the (2b)(β) pin recon §(I.8.22) (2026-06-21): (2b)(γ), NOT (2b)(β).**
The §(I.8.22) recon (read it in full before building) found the prior pin's (2b)(β) **mis-targeted**: the
landed `case_III_rank_certification` (`Candidate.lean:1472`) **already IS** KT's `Mᵢ + base` decomposition —
its combined LI family `(sn ⊕ Unit) ⊕ ιb` (`:1596–1599`) has `sn` = the `D−1` panel rows `r(Lᵢ)`, the `Unit`
row = the `±r` redundancy row, `ιb` = the base block `R(G₁∖row, q₁)` — and the `Mᵢ`-corner-LI-mod-base content
is discharged INLINE on `hρgate` (the single discriminating panel). So (2b)(β) is not genuinely-new, and the
de-risk leaf `finrank_span_rigidityRows_ge_of_corner` *consumes* (does not produce) the dead relabel-image
inclusion `span(base∖row) ≤ span(candidate.rigidityRows)` (§I.8.20). Two more §(I.8.22) verdicts: the
single-panel discriminator is **correct, not a conclusion-shape mismatch** (KT (6.65)/(6.67) need ONE
full-rank `Mᵤ`, which the `fin_cases u` dispatch selects — the other `Mᵢ` are never built); and the wall is
the cert's `hρGv` slot (`:1606–1611`), unchanged by the de-risk leaf.
- **The genuinely-new, root-attacking next leaf is (2b)(γ) — the (6.66) `±r` ℝ^D-vector identity**
  `∑ⱼ λ_(vᵢvᵢ₊₁)ⱼ rⱼ(q(vᵢvᵢ₊₁)) = ±r`, the step that lets KT carry the redundancy as a fixed *abstract
  vector* `r` while the *member moves* (so the `Mᵢ` second row is `±r` WITHOUT a fixed-member candidate
  membership). **It is NOT a telescope re-statement** (§I.8.21's guess refuted): the landed telescope
  `wstep_foldl_hingeRow_telescope` (`Relabel.lean:3209`) is a `hingeRow`-level identity in `Module.Dual ℝ (α →
  ScrewSpace k)`; (6.66) is a `ℝ^D`/`ScrewSpace`-vector identity in `Module.Dual ℝ (ScrewSpace k)` (one
  `Mᵢ`-row entry). The bridge — reading the `vᵢ`-column entry off the telescoped row via the degree-2
  column-vanishing (eq. (6.52)) — is genuinely-new + cost-unknown.
- **(2b)(γ) is a recon-or-spike**: does the hingeRow telescope's `vᵢ`-column read off as a clean ℝ^D `±r`
  equality, or does the degree-2 column-vanishing not localize at the abstract-vector level? Only after (2b)(γ)
  lands is the cert-re-shape signature (consume `±r` as the `Mᵢ` second row, NO `hρGv`) derivable — do **not**
  pin it before (2b)(γ) (a pre-(2b)(γ) cert signature would re-introduce the dead inclusion, §(I.8.22) clause
  (ii)).
Then the cert re-shape (forked so general-`d` uses the `±r`-cert and `d=3` M₃ keeps its single-step-move cert
— zero-regression) + the arm re-shape + the 2c-iii dispatch wire-up + the orphan confirm-and-delete. **The
smallest genuinely-advancing next commit is (2b)(γ)**: the recon-or-spike on whether the telescoped hingeRow's
`vᵢ`-column yields KT's `±r` ℝ^D equality. Audit trail: design §(o‴)(I.8.18)–(I.8.22), the `lem:case-III
general-d` ledger sharpening.

**Reference (the §I.8.21 verdict, source-grounded against the landed engine + KT pp. 697–698):** the abstract
`r` of KT (6.66) IS already the project's `ρ₀` (A-1, `Candidate.lean:432`); the engine's `hρGv` slot IS the
wall (`case_III_rank_certification` uses it once, `Candidate.lean:1606–1611`, as the fixed-member candidate
membership), so (A) cannot feed the existing engine — it re-shapes the rank-cert to KT's `rank Mᵢ +
rank(base∖row)` block decomposition (6.64–6.65), where the redundancy is a `±r` ℝ^D-EQUALITY (6.66), never a
fixed dual-functional transported across the relabel. Sub-route (2a) "non-gate composition" is DEAD (collapses
to the wall); (2b) "matrix/abstract-`r`" is the live route. Route B (carry `ρ₀`/`hφ@endsσρ` to ENTRY) does not
attack the root (LIKELY-DEAD, §I.8.20) and is the residue only if (A) is held. **Honest remaining cost band:
~6–11 more commits** (the de-risk spike, the hardest + cost-unknown part, is now closed POSITIVE).

## Decisions made during this phase

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
- **(2b)(β) pin recon → RE-POINT to (2b)(γ) (§I.8.22, 2026-06-21, docs-only).** A design-pass to pin (2b)(β)'s
  `g/ι/W/hLI` signature instead found it **mis-targeted** (clause (ii) flag-don't-force): the landed
  `case_III_rank_certification` (`Candidate.lean:1472`) already realizes KT's `Mᵢ + base` decomposition inline
  (the `(sn ⊕ Unit) ⊕ ιb` family = `r(Lᵢ)` rows + `±r` row + base block), the `Mᵢ`-corner LI-mod-base is
  discharged on `hρgate`, and `finrank_span_rigidityRows_ge_of_corner` *consumes* (not produces) the dead
  relabel-image inclusion (§I.8.20). The single-panel discriminator is correct (KT needs ONE full-rank `Mᵤ`,
  selected by `fin_cases u`). The genuinely-new leaf is **(2b)(γ) the (6.66) `±r` ℝ^D-identity** — refuted as a
  telescope re-statement (telescope = `hingeRow`-carrier `Module.Dual ℝ (α→ScrewSpace k)`; (6.66) = screw-vector
  `Module.Dual ℝ (ScrewSpace k)`). No cert signature pinned pre-(2b)(γ). See *Hand-off* + design §(o‴)(I.8.22).
