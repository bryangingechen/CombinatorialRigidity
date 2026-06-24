# Phase 23d — Case III general `d`: the CHAIN rank-certification reconsideration (work log)

**Status:** in progress (opened 2026-06-24 at a user-adjudicated clean-break close of 23c, at the
member-mapping-wall phase STOP). The integer **Phase 23 stays in progress**; 23d is the **third
CHAIN-layer sub-phase** (CHAIN spans 23b + 23c + 23d — the layer "split on contact", design §3).
ENTRY + ASSEMBLY remain later sub-phases (codes; the cross-phase plan + route history live in
`notes/Phase23-design.md`, program map `notes/MolecularConjecture.md`).

**What 23d picks up.** 23c built option (A) — the forked general-`d` `±r`-block rank-cert engine (no
`hρGv`) — end-to-end through the arm + corner-data assembly, and **closed the interior-`hρe₀`
conjecture-crux** (`baseRedundancy_perp_interior_reproduced_panel`, the redundancy-carry seam; sound,
axiom-clean, in tree). But 23c **stopped at the rank-certification half** of LEAF-4 step (ii): the
general-`d` interior rank cert is blocked by the **`hρGv` member-mapping wall** (§I.8.18–20, intrinsic to
KT), with **all three escape routes refuted** — (A) static-`W` re-shape, (B′) operated-frame block-rank,
(A′) re-derive-in-the-operated-frame — and a **primary-source KT-§6.4.2 recon confirming there is NO
missed KT route** ((B′)/(A′) *are* KT's own rank-count, kernel-dead). The `±r`-corner reformulation
escapes the wall at the ROW/membership level but NOT in the general-`d` RANK CERTIFICATION. So the
**rank-cert LAYER is the open re-design**; the carrier/motive/contract above it are untouched.

**All landed leaves stay in tree (sound, reusable under a re-architected rank cert).** The full landed
inventory — the forked cert `case_III_rank_certification_chain`, the carrier + concrete-`W` leaf
(LEAF-2), the discriminator-index plumbing (LEAF-1 + `candidatePanel…`), LEAF-3
(`exists_shared_redundancy_and_matched_candidate`), the per-member router (LEAF-4 (c), genuine branch
sound), the corner cert (`±r` via `hρe₀`), and the closed interior-`hρe₀` crux — is the
**`notes/Phase23c.md` *Landed-leaf ledger* + *Decisions made***; 23d does not duplicate it. `d=3` stays
fully green and zero-regression throughout.

## Current state

**THE UNCONDITIONAL CRUX IS RESOLVABLE — route B works (design §I.8.24(4.25)), pending the one carried
hypothesis LEAF-B1.** After the rank cert hit the member-mapping wall (kernel-confirmed 5× for the
*existing* architecture: §(4.18) static-W, §(4.20) member-mapping, §(4.21) KT primary-source, §(4.23)
row-operation, §(4.24) geometry-aware-transport linearity + the A1 concede), a user-directed faithful
re-architecture pass found the escape: an **architectural inversion faithful to KT (6.64)**. Every prior
wall forced the base REDUNDANT row into the base block `W` (→ through-`vᵢ`, breaks `hW`) or transported it
as a covector (→ linearity-moved). KT does NEITHER: the bottom block is `R(G₁∖(v₀v₂)ᵢ*, q₁)` — base with
the redundant row DELETED (still rank `D(|V|−2)`) — and the redundant row's reproduction sits in the CORNER
`Mᵢ`. **Route B follows KT:** `W` = GENUINE rows ONLY (off-`vᵢ`, where the transport provably WORKS; card
`D(|V|−2)`); corner = `D−1` fresh panel rows + the `±r` row (`hρe₀`-sourced, never `hρGv`). The §(4.24)
linearity impossibility does NOT apply (route B never transports the redundant row — it's a direct corner
row); the §(4.19)/(4.23) `htopvanish` scissors does NOT apply (the chain cert needs the corner only
independent-mod-`W`, not pure-`vᵢ`). Q1 (the reproduction is a provable column equality) + Q2 (the bound
assembles for the genuine-only block: Q2-B span-preserved on deleting the redundant row, Q2-C genuine
transport, Q2-D genuine satisfies `hW`) are kernel-spiked sorry-free + axiom-clean. It is a **light
rank-cert REFORMULATION, not a `Matrix` rebuild** — the one rework is LEAF-2 / the `W`-production
(genuine-only basis instead of the full family).

**LEAF-B1 IS LANDED + DE-RISKED (2026-06-24, route-B build OPEN).** The structural-twin risk (the genuine-link
data may not survive a bare basis-extraction, possibly needing a motive strengthening) is **RESOLVED — no
strengthening needed**: the link/block data is recovered **for free** from set-membership in `F.rigidityRows`.
Landed in `RigidityMatrix/Basic.lean` (axiom-clean, warning/lint-clean), CONSTRUCTED not hypothesized:
- **`exists_genuine_linearIndependent_basis_of_rigidityRows_diff`** (LEAF-B1) — for any framework `F` and
  redundant member `rhat`, an LI family `f : Fin (finrank (span (rigidityRows ∖ {rhat}))) → Dual` with each
  `f i ∈ F.rigidityRows` (genuine, carries link data), each `f i ≠ rhat` (redundant EXCLUDED), and
  `span (range f) = span (rigidityRows ∖ {rhat})`. Kernel = mathlib `Submodule.exists_fun_fin_finrank_span_eq`.
- **`span_rigidityRows_diff_singleton_eq_of_mem_span`** (the satisfiability fact §(4.18) flagged, = Q2-B) —
  deleting the redundant row preserves the span when `rhat ∈ span (rigidityRows ∖ {rhat})` (the
  `exists_redundant_panelRow_ab_decomposition` content), so the genuine basis has card = the full base rank
  `D(|V|−2)`. The consumer composes this + the IH `finrank = D(|V|−2)` to fix the family's cardinality.

Salvage judged: Q1-A (±r column equality) SKIPPED (thin instantiation of the landed `interior_group_eq_baseRedundancy`);
Q2-C SKIPPED (thin wrapper of `rigidityRow_relabel_to_genuine`); Q2-D SKIPPED (the chosen LEAF-B2 path via
`span_relabelImage_le_and_finrank_and_acolumn_vanish` takes per-member `hvanish` = `hingeRow_comp_single_off`,
NOT a span-form `hW`, so Q2-D's span lemma would be an orphan).

**Next concrete step = LEAF-B2 (genuine-only `W` producer).** Feed LEAF-B1's `f` into the LANDED
`span_relabelImage_le_and_finrank_and_acolumn_vanish` at `σ = shiftPerm i.castSucc`: `hS` per member from the
genuine-row transport (`chainData_bottom_relabel` genuine branch / `rigidityRow_relabel_to_genuine`), `hvanish`
per member from `hingeRow_comp_single_off`, cardinality from `span_rigidityRows_diff_singleton_eq_of_mem_span`
+ the IH. Then it composes with the LANDED `case_III_rank_certification_chain` (the cert is already wall-free —
takes `W`/`hWS`/`hWcard`/`hg`/`hLI`, no `hρGv`).

**Plan (≈3 sub-phases left to close the rank cert):** ✅ LEAF-B1 (crux, landed) → LEAF-B2 (genuine-only `W`
producer, the LEAF-2 rework) → LEAF-B3 (corner producer, mostly landed) → LEAF-B4 (interior-arm rewire, drop
the dead §(4.17) reproduced branch) → CHAIN-2c-iii dispatch / CHAIN-5, then ENTRY + ASSEMBLY (parallel-safe).
**Route A** (full concrete `Matrix`; KT transfers literally but heavy) is the documented fallback only if
LEAF-B2+ wiring walls — B's diagnosis tells A how to slot the redundant row, so the fallback is real and
informed. **(C)** (honest-conditional) is the fallback-of-the-fallback, not the plan.

**Do NOT** re-attempt the dead route families (§I.8.18–I.8.20) / (A)/(B′)/(A′); re-run the A1 / matrix-level
/ geometry-aware feasibility spikes (the *existing-architecture* wall is kernel-confirmed 5× — route B
escapes by re-architecture, not by re-attempting those); or re-hunt for a "missed KT route" (§(4.21): none).

## The A1 §I.8.21(α) feasibility recon — DONE (verdict INFEASIBLE)

Resolved 2026-06-24 by a read-only compiler-checked spike + a construct-or-concede resume (opus /
OPUS-ONLY, agentId `a8d70da3d32f07ca3`). **VERDICT: INFEASIBLE** — the full verdict, the unsound-FEASIBLE
first pass, the two sorry-free `concede_*` kernel re-derivations, and the no-feasible-route-in-hand
finding for the §I.8.21(α) matrix-level infra are in **design §I.8.24(4.22)**. The *Current state* above
carries the live consequence (the (C)/(D)/ENTRY adjudication). Do not re-run the spike.

## Remaining work in Phase 23

1. **The general-`d` rank certification — route B (§(4.25)), the 23d core.** The cert
   `case_III_rank_certification_chain` is already wall-free (block-additivity, no `hρGv`). ✅ **LEAF-B1
   LANDED** (`exists_genuine_linearIndependent_basis_of_rigidityRows_diff` + `span_rigidityRows_diff_singleton_eq_of_mem_span`,
   `RigidityMatrix/Basic.lean`) — the genuine-only base block source. OPEN: **LEAF-B2** (genuine-only `W`
   producer = the LEAF-2 rework, feeds LEAF-B1's `f` into `span_relabelImage_le_and_finrank_and_acolumn_vanish`),
   **LEAF-B3** (corner producer, mostly landed: the `±r` via `hρe₀`, the panel rows, `linearIndependent_mkQ_corner_of_gate`),
   **LEAF-B4** (interior-arm rewire `case_III_arm_realization_chain` onto B1/B2/B3, drop the dead §(4.17)
   reproduced router branch). The carrier, both `hLI` halves, the (α) bridge, the off-slot row bridge, the arm
   spine, and the corner-data assembly stay LANDED (`notes/Phase23c.md` ledger). The interior `hρe₀` is CLOSED.
2. **CHAIN-2c-iii `chainData_dispatch`** — the general-`k` dispatch (a discriminator-pick + Fin-case ROUTER
   over the two landed arm routes: the OLD engine via `chainData_split_realization` for the base candidate
   `i=1` + the d=3 floor; the option-(A) `case_III_arm_corner_assembly` for interior `2 ≤ i < d`). Blocked
   only on item 1's rank cert; LEAF-1/2/3 + the discriminator-index plumbing + the genuine-branch router are
   landed.
3. **CHAIN-5** — wire the dispatch into the spine to discharge `hdispatch`.
4. **ENTRY** *(parallel-safe; own sub-phase when minted)* — reshape `Graph.exists_chain_data_of_noRigid`
   (`Reduction.lean:383`) to the `G.ChainData n` producer `exists_chainData_of_noRigid` (KT Lemma 4.6 chain
   + Lemma 4.8 split-off, general `d`); lift the `6 ≤ bodyBarDim n` floor; resolve the chain/cycle
   dichotomy (OD-1, KT Lemma 4.6 / Lemma 5.4). Consumer: `case_III_hsplit_producer_all_k`
   (`Arms.lean:777`). The CHAIN↔ENTRY `G.ChainData n` contract is **frozen** (below).
5. **ASSEMBLY** — compose the honest general-`d` Theorem 5.5, re-green `prop:rigidity-matrix-prop11` +
   `hub`, derive Thm 5.6, state Conjecture 1.2.

**Contract/motive note.** The wall is machinery *below* the contract — no C.0–C.6/motive change is forced
by it (§I.8.21 confirmed). The rank-cert re-architecture re-shapes `case_III_rank_certification` +
`case_III_arm_realization` only — it does **not** touch the dispatch's `hdispatch` consume-shape (C.3), the
`ChainData` record (C.1), or the 0-dof motive/IH (the dispatch threads one `ρ₀` either way).

## CHAIN↔ENTRY chain-data contract (frozen)

The `G.ChainData n` contract (the length-`d` chain record) is **frozen** — design `notes/Phase23-design.md`
§"CHAIN↔ENTRY contract", C.0–C.6; no motive/IH change; `d=3` zero-regression. The dispatch's input shape is
the chain extractor's output shape, so ENTRY can be built independently against this frozen contract.

## Blueprint-clarity obligation (carried from 23b/23c — owner-flagged)

The `lem:case-III` general-`d` node's exposition must materialize KT's index-shift isos (6.54–6.56) + ±r
chain (6.66) explicitly (the Lean economizes; the prose must not), and present the redundancy-carry as
**whole-matrix bookkeeping with `r` abstract and the member moving**, flagging the fixed-functional-transport
shape as the trap (the §(4.21) source-recon framing). Written at phase-close once the arm is `sorry`-free.
Ledger entry: `notes/BlueprintExposition.md` (`lem:case-III general-d`).

## Blockers / open questions

- **The member-mapping wall (intrinsic to KT for the EXISTING architecture, 5× kernel-confirmed) is
  ESCAPED by route B's architectural inversion (§(4.25)) — pending LEAF-B1.** The existing static-W /
  member-mapping / row-op / geometry-aware-transport routes are all kernel-dead (§(4.17)–(4.24)) because they
  forced the redundant row into the base block `W`. Route B follows KT (6.64): redundant row → CORNER,
  genuine rows → base block `W`. The remaining open item is **LEAF-B1** (genuine-basis extraction — the one
  carried hypothesis), being de-risked by construction. If LEAF-B1 constructs, the unconditional crux is
  resolved (no honest-conditional needed); if it walls, route A (concrete `Matrix`) is the informed fallback.

## Hand-off / next phase

**Route B (§(4.25)) resolves the unconditional crux, pending the LEAF-B1 de-risk.** Next concrete commit =
**DE-RISK LEAF-B1 by resuming the recon agent `ad8dafc55bcaf21e3`** (spike-salvage resume, rescue §6): it has
the route-B design + its sorry-free spike facts in context. The resume (i) CONSTRUCTS LEAF-B1 (genuine-basis
extraction — the crux + the structural twin of this session's carried-hypothesis false FEASIBLEs, so it gets
the construct-or-concede test: land it sorry-free, or return BLOCKED with the precise obstruction), and (ii)
salvages the genuinely-reusable sorry-free facts (Q1-A ±r column equality, Q2-B span-preservation, Q2-D `hW`)
as real gate-clean lemmas — opening 23d's route-B build. If LEAF-B1 constructs, the rank cert is resolvable
unconditionally via the route-B plan below.

Route-B build plan (≈3–4 sub-phases): **LEAF-B1** (genuine-basis extraction, crux) → **LEAF-B2** (genuine-only
`W` producer, rework of LEAF-2) → **LEAF-B3** (corner producer, mostly landed) → **LEAF-B4** (interior-arm
rewire, drop the dead §(4.17) reproduced branch) → CHAIN-2c-iii dispatch / CHAIN-5, then ENTRY + ASSEMBLY
(parallel-safe). Fallbacks: **route A** (concrete `Matrix`, KT transfers literally but heavy) if LEAF-B1 is
intractable; **(C)** honest-conditional only if both B and A fail (`case_III_arm_realization_chain` already
carries the rank-cert obligation as hypotheses, so (C) stays a cheap wiring+ASSEMBLY exercise).

## Decisions made during this phase

*(Fresh at open. The inherited landed-leaf inventory + the wall-characterization verdicts + the
cross-cutting lessons of building option (A) are the settled archive in `notes/Phase23c.md` *Decisions
made* + *Landed-leaf ledger*; 23d does not duplicate them. New 23d decisions land here.)*

- **Opened 2026-06-24 at a clean-break close of 23c (user-adjudicated), at the member-mapping-wall phase
  STOP.** 23c's chosen architecture (option (A), the `±r`-block engine) is conclusively refuted at the
  rank-cert level; the redundancy-carry re-architecture half succeeded (interior `hρe₀` closed). 23d =
  the rank-certification reconsideration (A1 recon → A2 build / (C) honest-conditional / (D) reconsider),
  still within the CHAIN layer (CHAIN now spans 23b+23c+23d). ENTRY/ASSEMBLY get later letters. Structural
  precedent: the 23b→23c clean-break close at this same wall.
- **A1 §I.8.21(α) feasibility = INFEASIBLE (2026-06-24, design §(4.22)).** A read-only compiler-checked
  spike first returned FEASIBLE; coordinator scrutiny found it unsound — it verified the static-`W` cert
  `case_III_rank_certification_chain` COMPOSES (corner data carried as hypotheses) and re-confirmed the
  already-known row-membership escape, but never confronted that those hypotheses are unsatisfiable for the
  real interior carry (the exact "deferred-hypothesis unsatisfiable for the consumer" trap, DESIGN.md
  *Constructibility recon*). A construct-or-concede resume CONCEDED, building two sorry-free `concede_*`
  kernel re-derivations of §(4.17)/(4.18) for the actual dispatch slot. The §I.8.21(α) matrix-level infra
  has no feasible route in hand (operated-frame variants refuted by §(4.19)/(4.20)). Lesson promoted to
  Findings (model-experiment) + the satisfiability corollary already in DESIGN.md.
- **Matrix-level rework = INFEASIBLE; the wall is intrinsic to KT, 4× kernel-confirmed (2026-06-24, design
  §(4.23)).** User authorized one more swing (the user's "happy to rework landed material"): does KT's
  rank-preserving ROW-OPERATION handling of the redundant row (vs the project's span membership) escape the
  wall? A read-only design+spike (after the coordinator read KT §6.4.2 eqs. 6.60–6.67 from the primary PDF)
  DISPROVED it at the kernel: KT's row operation `r̂ = Σλ rⱼ` IS the `G_v`-row part `wGv ∈ span(R(G_v,q))` —
  documented in the project's OWN Phase-22g `exists_redundant_panelRow_ab_decomposition` (`Candidate.lean:191`,
  `:230`). The "scissors": the pure-`vᵢ` corner satisfies `htopvanish` but needs `hρGv` to enter the span;
  the `hρe₀`-corner enters the span but isn't pure-`vᵢ`; they differ by exactly `hingeRow a b ρ₀` = the wall.
  Decision: the unconditional crux is closed to all routes in hand → option (C) + ENTRY. (D) needs a
  genuinely-new idea. Lesson → Findings (model-experiment).
- **Geometry-aware transport = RELOCATES-TO-WALL (2026-06-24, design §(4.24)); the transport layer is
  confirmed CORRECT, nothing to rework.** User insight (sharp): replace the transport with one that
  "remembers the geometry" so the base redundancy transports faithfully. A scoping recon found the project's
  transport ALREADY does this (`shiftPerm`=KT's ρᵢ 6.54, `qρ`=config relation 6.59,
  `rigidityRow_relabel_to_genuine` absorbs KT's per-edge reproduction as the abstract `hsupp` — the exact
  abstraction hoped for; it works for genuine rows). The redundant row is closed by a LINEARITY IMPOSSIBILITY
  (SPIKE 3): any linear `T` sends `Σcⱼ·gⱼ` to `Σcⱼ·T(gⱼ)`, so the decomposed route lands the redundant row at
  its `ρᵢ`-image (moved member), never the fixed `hφ` — the redundant row has no genuine edge to anchor the
  reproduction to. 5th kernel confirmation. The ONLY escape is a non-linear/explicit-`Matrix` model = the
  §I.8.21(α) infra (no route in hand). → option (C) + ENTRY. Lesson → Findings.
- **Route B WORKS — the unconditional crux is RESOLVABLE via an architectural inversion faithful to KT
  (6.64) (2026-06-24, design §(4.25)); SUPERSEDES the (C)-only recommendation.** User-directed: tackle the
  faithful re-architecture, don't skip the step (and the user's epistemic point — KT's validity IS a route).
  All 5 prior walls forced the redundant row into the base block `W`; KT (6.64) deletes it from the bottom
  block and puts its reproduction in the CORNER. Route B: `W` = GENUINE rows only (off-`vᵢ`, transport works,
  rank `D(|V|−2)`); corner = panel rows + the `±r` row (`hρe₀`, never `hρGv`). §(4.24) linearity impossibility
  doesn't apply (redundant row not transported); §(4.19)/(4.23) `htopvanish` doesn't apply (chain cert needs
  corner only independent-mod-`W`). Q1/Q2 kernel-spiked sorry-free + axiom-clean (CONSTRUCTED Q2-B/C/D, the
  satisfiability §(4.18) called impossible *for the redundant-including block*). A LIGHT rank-cert
  reformulation (rework LEAF-2's `W`-production to a genuine basis), NOT a `Matrix` rebuild. The one carried
  hypothesis = **LEAF-B1** (genuine-basis extraction), being de-risked by construction. → route-B build (plan
  in *Hand-off*); route A / (C) are fallbacks. Lesson (the re-architecture escape + scoping a user's idea) →
  Findings.
