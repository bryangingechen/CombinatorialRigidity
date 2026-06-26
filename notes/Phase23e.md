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

**Next step = the step-2 construct-or-concede de-risk spike (the GATE).** The cert-shape recon (item (1),
design §(4.49)) is DONE — VERDICT GO: a THIRD, un-examined cert shape `fromBlocks A 0 C D` (zero UPPER-right,
A3-TRANSPOSED) dodges all four walls AND §(4.42)'s Schur concern. The earlier `R(Gab)`-reproduction NO-GO
(§(4.48)) was about the block-triangular SHAPE with `e_b ∈ m₁`; the recon found that the LANDED `mixedBottom`
family already solves the bottom (`e_b ∈ m₂`, full rank `#m₂`, NO membership), and the only blocker is the
block orientation.

**The cert shape (design §(4.49)).** `rank (fromBlocks A 0 C D) ≥ #m₁ + #m₂` is the exact TRANSPOSE of A3
(trivial mirror, `det_fromBlocks_zero₁₂` confirmed mathlib). The zero upper-right comes from a row op zeroing
the corner's off-`v` `B` (subtract the `e_b` bottom row — same `ab`-fill — from the `±r` corner row); this
mutates the CORNER (`A → A' = A − L₀C`), NOT the bottom (which stays the `mixedBottom` full-rank block), so
§(4.42)'s "row op mutates the bottom into the Schur complement" concern does NOT apply (that was zeroing `C`;
this zeros `B`). The genuinely-new content localizes to ONE piece: the corner `hA' : LinearIndependent A'.row`
= KT (6.66)/(6.67) union-dimension `Mᵢ`-invertibility, on the GREEN Lemma 2.1 + the landed `d=3` discriminator
`exists_complementIso_ne_zero_of_homogeneousIncidence_gen` (`Claim612.lean:1462`), generalized to general `d`.

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
- [ ] **(2) Construct-or-concede de-risk spike** (the GATE — NEXT; no reshape until green) — make-or-break:
  (i) the row op composes as a unit-det left-multiply yielding `fromBlocks A' 0 C D` from the operated candidate
  matrix (`B` nonzero only in the `±r` row via the landed operated-entry facts; `mixedBottom` for the bottom);
  (ii) the corner `hA'` REDUCES to the union-dimension discriminator (the landed `d=3` one as the general-`d`
  target), NOT a bare assumption. Both compose → item (3); corner mutation breaks invertibility unfixably →
  concede with that named kernel obstruction. (§(4.22)/(4.46): a spike answers composition, not
  dischargeability — do NOT carry the crux as a hypothesis and call it feasible.)
- [ ] **(3) Build the rank infrastructure** — (a) A3-transposed `rank_fromBlocks_zero₁₂_ge_of_linearIndependent_rows`
  (trivial mirror, `Mathlib/LinearAlgebra/Matrix/Rank.lean`, upstream-eligible); (b) the row op as a unit-det
  left-multiply + A4-transposed bridge; (c) the corner `hA'` (generalize the `d=3` union-dimension discriminator);
  wire the landed `mixedBottom` `hD` (def-0 IH `hrank` via `hsplitGP`).
- [ ] **(4) Reshape cert + arm** — fork the cert: a new general-`d` `case_III_rank_certification_zero₁₂`
  consuming (3); `d=3` keeps the current `_matrix`/M₃ path (zero-regression). Then 23f wires the dispatch.

## Blockers / open questions

- **Open design question (item (1), not a blocker):** Schur-complement-full-row-rank vs a non-block-triangular
  cert. Leading hypothesis = Schur (KT's row op (6.52) lands `R(G₁∖row)` directly; the `mixedBottom` family is
  most of its bottom side). The recon decides; the item-(2) spike confirms before any build.
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive) —
  independent of the cert; tracked separately, lands with 23f/the spine.
- **Downstream (23f+):** the general-`k` dispatch + CHAIN-5, ENTRY's `exists_chain_data_of_noRigid` reshape +
  floor lift + OD-1, ASSEMBLY. The frozen contract (C.5/C.6) is invariant; none touches 23e's cert.

## Hand-off / next phase

**Next concrete commit = the cert-shape design recon verdict (docs):** pin the rank-lemma statement (Schur vs
non-block-triangular), the buildable-leaf list, and the `d=3` strategy, ending in the go/no-go for the item-(2)
de-risk spike. Then the spike (the gate). **What is solid regardless:** the literal-`Matrix` spine (A1–A6, the
cert `case_III_rank_certification_matrix`, the arm `case_III_arm_realization_matrix`) + the option-2 leaves +
the `mixedBottom` family are landed, axiom-clean, and reusable parallel facts for whichever cert shape the
recon picks. After a sound cert lands: 23f (dispatch + CHAIN-5) → 23g (ENTRY) → 23h (ASSEMBLY).

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
