# Phase 23e — Case III general `d`: the KT-faithful rank certificate (work log)

**Status:** in progress. Opened 2026-06-26 (as the general-`k` dispatch + CHAIN-5); **RE-SCOPED the
same day** to the **KT-faithful rank certificate** after the `R(Gab)`-reproduction feasibility spike
returned a kernel-grounded NO-GO and the user chose to pursue the genuinely-new certificate (complete
formalization of KT is the goal; fallback (C) / freeze-at-`d=3` declined). **Phase 23 stays in progress**;
23e is the *fourth* CHAIN-layer sub-phase (CHAIN = 23b + 23c + 23d + 23e). The authoritative recon + plan is
**`notes/Phase23-design.md` §(4.48)** (the spike verdict, the dual-orientation obstruction, the
Schur-complement route, the `mixedBottom` lever, the cert-before-dispatch plan); this note carries the
current state, the leaf checklist, blockers, and hand-off, and points there. Program map:
`notes/MolecularConjecture.md`.

## Current state

**Next step = the forked-cert build (item 3a) — REAL Lean engineering, the de-risking arc is COMPLETE.** All
three de-risk gates are now GREEN (design §(4.49)–(4.52)): the A3-transposed scaffolding is sorry-free, the
union-dimension `Mᵢ`-invertibility is landed general-`d`, and the item-2c wiring spike kernel-confirmed the
`hA'` route-composition. The §(4.50) corner concede is DISSOLVED by the `Gv`-row PIN-ZERO fact: LEAF-3's
widening lands the `±r` `ab`-fill ENTIRELY in `Gv` rows (both endpoints ≠ v), which are pin-zero after the
column op, so the off-`v` zeroing leaves the corner pin `= ρ₀` UNCHANGED. The two load-bearing facts are
sorry-free scratch-confirmed: `corner_hA'_of_gate` (`hA'` ⟸ {`e_a`-block LI} + {the landed discriminator gate},
via `linearIndependent_sumElim_candidateRow_iff` `Claim612.lean:845`) and `Gv_row_pin_zero`
(= `rigidityMatrixEdge_mul_columnOp_apply_pin_zero`).

**The strategic question is resolved into a bounded build.** "Pursue the new certificate" → every mathematical
foundation is landed (the union-dimension discriminator, the `mixedBottom` bottom, the A3-transposed shape, the
corner `hA'` reduction); remaining = ASSEMBLY, NOT open research. The A3-transposed cert dissolves the `hbotmem`
wall that blocked the original 23e dispatch.

Nothing is mid-stream; tree clean. `d=3` stays fully green throughout (zero-regression is a hard constraint).
The landed `chainData_arm_realization_sep` wrapper (the old 23e dispatch work) is SOUND but consumes the
walled `hbotmem`; it parks in **23f** (the dispatch) until the sound cert lands.

## Architectural choices made up front

- **Cert before dispatch.** The dispatch consumes the cert, so the cert (23e) precedes the general-`k`
  dispatch + CHAIN-5 (now **23f**), ENTRY (**23g**), ASSEMBLY (**23h**) — codes-until-open. 23d's "rank-cert
  scope CLOSED" was premature (the §(4.38) `R(Gab)`-dissolves-the-wall claim was unspiked; §(4.44) refuted it),
  so the cert work genuinely re-opens here.
- **Below the CHAIN↔ENTRY contract + the motive/IH.** The cert + arm are infrastructure beneath the dispatch
  (C.3) and the `ChainData` record (C.1); the reshape does not touch the `hdispatch` consume-shape or the
  0-dof motive (§I.8.21 re-verified). The frozen interface (C.0–C.6) + the sanctioned C.3 `hIH` addition stay
  valid for 23f.
- **`d=3` zero-regression via a cert fork if needed.** The new cert must specialize to the `d=3` M₃ arm OR
  the `d=3` wrapper keeps the current cert and only the general-`d` arm uses the new one (the cleaner option;
  decide in the recon).

## Lemma checklist

Per design §(4.48) plan. The cert work (items 1–4); the dispatch/CHAIN-5/ENTRY/ASSEMBLY are 23f+.

- [x] **(1) Cert-shape design recon** (DONE, design §(4.49)) — VERDICT GO: the third shape `fromBlocks A 0 C D`
  (zero UPPER-right, A3-transposed), NOT the Schur-complement route (which zeros `C` and mutates the bottom).
  The bottom is the LANDED full-rank `mixedBottom` block; the row op zeros `B` (corner off-`v`), leaving the
  bottom untouched; the genuinely-new content localizes to the corner `hA'` (union-dimension `Mᵢ`-invertibility).
- [x] **(2) Construct-or-concede de-risk spike** (DONE, design §(4.50)) — the A3-transposed SCAFFOLDING goes
  sorry-free (A3-transposed mirror + the row-op machinery `rowOp_isUnit_det`/`rowOp_zeroes_upperRight` + the
  `mixedBottom` bottom), but the genuinely-new content RELOCATED INTACT into the corner `hA'` (NOT the landed
  `d=3` discriminator). Convergence verdict: the crux is KT's union-dimension `Mᵢ`-invertibility, irreducible.
- [x] **(2b) Focused structural recon on `hA'` / the `Mᵢ` row-structure** (DONE, design §(4.51)) — VERDICT GO,
  and §(4.50)'s "hardest single argument" framing was STALE: KT's union-dimension `Mᵢ`-invertibility (6.65–6.67)
  is ALREADY LANDED at general `d` (the discriminator + callees are `{k : ℕ}`, `Claim612.lean` sorry-free, fired
  by the landed `exists_shared_redundancy_and_matched_candidate`). The §(4.50) collapse was a generic-`L₀`
  artifact; KT's `λ` (LEAF-3) gives the clean `Mᵢ = [r(Lᵢ); ±r]`. Remaining = ASSEMBLY, not new math.
- [x] **(2c) Wiring spike** (DONE — GO, design §(4.52)) — kernel-confirmed the LEAF-3-`λ` → `A' = Mᵢ` →
  discriminator `hA'` route-composition reduces to landed facts + LEAF-3 outputs with no new hypothesis. The
  §(4.50) concede is dissolved by `Gv_row_pin_zero`. Two sorry-free facts built: `corner_hA'_of_gate`,
  `Gv_row_pin_zero`. De-risking arc complete.
- [ ] **(3) Build the forked general-`d` cert** (ASSEMBLY — REAL Lean, the next concrete work) —
  - (3a) `case_III_rank_certification_zero₁₂`: A3-transposed scaffolding (the landed-mirror
    `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows` + the row-op machinery, §(4.50)) + bottom `hD` from the
    `mixedBottom` family (the RANK fact, NOT `hbotmem`) + corner `hA'` from `corner_hA'_of_gate`. `d=3` keeps the
    `_matrix`/M₃ path (zero-regression).
  - (3b) the literal `re`/`L₀` construction: wire LEAF-3's `cGv` edge-grouped widening as the row-op weights +
    the `(row-op'd corner) = ρ₀` identity (composed from the two §(4.52) sorry-free facts).
  - (3c) the candidate-matching gate bridge: `F.supportExtensor e_a` ↔ LEAF-3's
    `panelSupportExtensor (q(candidateVtx i)) n'` via `caseIIICandidate_supportExtensor_candidate`
    (`Candidate.lean:960`) + `candidateVtx i = a` (interior: `= vtx i.succ`).
- [ ] **(4) Wire into the dispatch (the original 23e/23f scope, UNBLOCKED)** — the A3-transposed cert dissolves
  the `hbotmem` wall: LEAF-4 disjoint-block bundle now takes the `mixedBottom` bottom (no membership); LEAF-5
  router (base/`d=3` → `chainData_split_realization`; interior → `chainData_arm_realization_sep`); fire LEAF-3.

## Blockers / open questions

- **Open design question (item (1), not a blocker):** Schur-complement-full-row-rank vs a non-block-triangular
  cert. Leading hypothesis = Schur (KT's row op (6.52) lands `R(G₁∖row)` directly; the `mixedBottom` family is
  most of its bottom side). The recon decides; the item-(2) spike confirms before any build.
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) —
  independent of the cert; tracked separately, lands with 23f/the spine.
- **Downstream (23f+):** the general-`k` dispatch + CHAIN-5, ENTRY's `exists_chain_data_of_noRigid` reshape +
  floor lift + OD-1, ASSEMBLY. The frozen contract (C.5/C.6) is invariant; none touches 23e's cert.

## Hand-off / next phase

**Next concrete commit = item (3a): the forked general-`d` `case_III_rank_certification_zero₁₂`** — the
A3-transposed cert proper (landed-mirror `rank_fromBlocks_zero₁₂_ge…` + the row-op machinery + bottom `hD` from
`mixedBottom` + corner `hA'` from `corner_hA'_of_gate`). This is REAL Lean (the de-risking spikes were
scratch/reverted; item 3 is the first tracked Lean of 23e — full build/lint/warning/no-sorry/friction gates
apply). **What is solid (all sorry-free, kernel-confirmed):** the union-dimension `Mᵢ`-invertibility (the
hardest argument) is LANDED general-`d`; the A3-transposed scaffolding + the `mixedBottom` bottom + the two
§(4.52) wiring facts (`corner_hA'_of_gate`, `Gv_row_pin_zero`) compose the cert. Remaining = ASSEMBLY (3a/3b/3c
→ LEAF-4/LEAF-5/dispatch → 23f), not new math. Then 23g (ENTRY) → 23h (ASSEMBLY proper).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **`R(Gab)`-reproduction is a kernel-grounded NO-GO; pursue the genuinely-new certificate** (2026-06-26,
  session #37, design §(4.48)). The feasibility spike (`Spike48.lean`, reverted, axiom-clean) proved the
  literal-`Matrix` reproduction cannot escape the deficiency wall: L1 `obstruction_bottom_rank_eq_unoperated`
  (operated bottom rank = un-operated `R(Gv)` rank, for ANY unit-det column op — column ops preserve
  fixed-row-subset rank) + L3 `obstruction_hD_unsatisfiable_of_deficient` (so `hD` is FALSE under the landed
  `R(Gv)`-deficiency). The sharper obstruction is a DUAL-ORIENTATION single-row impossibility (the `e_b` row
  fits neither block of any block-triangular `fromBlocks`). The wall is a FORMALIZATION representation-mismatch
  (block-triangular cert vs KT's non-block-triangular argument), NOT open math. User decision: pursue the new
  cert (complete formalization is the goal); fallback (C) / freeze-at-`d=3` declined. Re-scoped 23e to the cert.
- **The new cert = A3-transposed `fromBlocks A 0 C D` (zero UPPER-right), via a row op zeroing `B`** (recon
  verdict, 2026-06-26, design §(4.49)). NOT the Schur-complement route: §(4.42)'s option 1 zeros `C`
  (lower-left) and mutates the bottom into `D − C·A⁻¹·B` (full-rank-ness genuinely-new). The recon found the
  better orientation — zero `B` (upper-right, the corner's off-`v` content) by subtracting the `e_b` bottom row
  (same `ab`-fill) from the `±r` corner row: this mutates the CORNER (`A → A' = A − L₀C`), leaving the bottom
  `[C D]` = the LANDED full-rank `mixedBottom` block UNTOUCHED. `rank (fromBlocks A 0 C D) ≥ #m₁ + #m₂` is the
  trivial transpose of A3 (`det_fromBlocks_zero₁₂`, mathlib). Genuinely-new content localizes to the corner
  `hA'` (KT (6.66)/(6.67) union-dimension, green Lemma 2.1 + the landed `d=3` discriminator). Spike (item 2)
  gates the reshape.
- **Step-2 spike: scaffolding GO, genuinely-new content relocated to `hA'`** (2026-06-26, session #37, design
  §(4.50)). The A3-transposed shape mirror + the row-op machinery (`rowOp_isUnit_det`/`rowOp_zeroes_upperRight`)
  + the `mixedBottom` bottom all build sorry-free — but the `±r` corner row and the bottom `e_b` rows share the
  same `e_b` functionals (the `ab`-fills are LI), so the corner `hA'` does NOT reduce to the landed `d=3`
  discriminator; it relocated intact as the `Mᵢ`-invertibility. KT avoids the overlap with `R(G₁∖row)` (frozen
  base deficiency); the project's def-0 `R(Gab)` bottom does not. CONVERGENCE: three spikes confirm the
  genuinely-new content is irreducibly KT's union-dimension `Mᵢ`-invertibility (6.65–6.67); cert-shape
  exploration is closed. Next = the item-(2b) structural recon, then the `Mᵢ`-invertibility build.
- **Step-2b recon: GO — the union-dimension is ALREADY LANDED general-`d`; §(4.50)'s "hardest argument" was
  STALE** (2026-06-26, session #37, design §(4.51); KT (6.60)–(6.67) read directly). The discriminator
  `exists_complementIso_ne_zero_of_homogeneousIncidence_gen` + callees are `{k : ℕ}` (NOT `d=3`-pinned),
  `Claim612.lean` sorry-free, and the general-`d` `exists_shared_redundancy_and_matched_candidate` (Phase 23c)
  already fires it — producing `ρ₀`, the `λ`-witness `ρ₀ = Σⱼ λⱼ rab j`, and the matched candidate. KT's `λ`
  row op (6.63) gives the clean `Mᵢ = [r(Lᵢ); ±r]` (the §(4.50) collapse was a generic-`L₀` artifact). So `hA'`
  = the landed discriminator via LEAF-3's `λ`; the A3-transposed cert (bottom = `mixedBottom` RANK fact, not
  `hbotmem`) replaces the walled option-2 `_sep` and UNBLOCKS the dispatch. Remaining = ASSEMBLY, not new math.
  One prose-not-kernel hedge (§(4.46)): the LEAF-3-`λ` → `A' = Mᵢ` → discriminator wiring — confirm via the
  item-(2c) spike before the forked-cert assembly.
- **Step-2c wiring spike: GO — the §(4.46) hedge discharged, de-risking arc COMPLETE** (2026-06-26, session #37,
  design §(4.52)). Kernel-confirmed (sorry-free) that the LEAF-3-`λ` → `A' = Mᵢ` → discriminator `hA'`
  route-composition reduces to landed facts + LEAF-3 outputs with NO new hypothesis. The §(4.50) corner concede
  is DISSOLVED by the `Gv`-row PIN-ZERO fact (`rigidityMatrixEdge_mul_columnOp_apply_pin_zero`): LEAF-3's
  widening lands the `±r` `ab`-fill ENTIRELY in `Gv` rows (both endpoints ≠ v), pin-zero after the column op, so
  the off-`v` zeroing leaves the corner pin `= ρ₀` UNCHANGED (a combination of `e_b`'s OWN rows could not — it
  would kill the pin). Two sorry-free facts: `corner_hA'_of_gate` (`hA'` ⟸ {`e_a`-block LI} + {gate}) and
  `Gv_row_pin_zero`. All foundations landed; remaining 23e = ASSEMBLY (items 3a/3b/3c → LEAF-4/5/dispatch).

### Carried-forward interface decisions (for 23f, the dispatch)

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36). The interior
  arm needs the INTERIOR-split `hsplitGP` (`G.splitOff vᵢ …`), derivable only from `hIH` (via
  `splitOff_isMinimalKDof`), not in the frozen C.3 signature — so add `hIH` to the C.3 dispatch consume-shape: a
  one-field addition touching the C.0 producer/consumer/ENTRY lockstep trio, NOT a motive/IH-strength change
  (the landed `chainData_split_realization` already carries `hIH` separately). Lands with 23f. Context: design
  §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
- **Interior arm wrapper landed, parks in 23f** (`chainData_arm_realization_sep`, `CaseIII/Realization.lean`,
  2026-06-26). The `ChainData`-indexed sibling of `chainData_split_realization` for the interior route; sound
  (carries the disjoint-block obligations as hypotheses) but consumes the walled `hbotmem`, so it waits for the
  sound cert before wiring into the dispatch.
