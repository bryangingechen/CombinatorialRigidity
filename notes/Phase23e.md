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

**Next step = the cert-shape design recon (item (1)) — read-only + compiler-checked spot-checks, NOT a
build.** The literal-`Matrix` `R(Gab)`-reproduction bottom is a kernel-grounded NO-GO (design §(4.48), spike
`Spike48.lean`, reverted): the operated `e_b` row is dual-natured (nonzero pin entry AND nonzero off-`v`
`ab`-fill), so it fits NEITHER block of ANY block-triangular `fromBlocks` — the deficiency wall is intrinsic
to the block-triangular cert SHAPE, not to any bottom choice. **This is a formalization
representation-mismatch, NOT open math** — KT 2011 is a complete proof; the project's cert is block-triangular
while KT's argument is non-block-triangular (block-triangular only after the (6.62) relabel correspondence
identifying the operated bottom with the full-rank base `R(G₁∖row)`).

The genuinely-new certificate to build (two equivalent views): a **non-block-triangular rank lower bound**
tolerating a nonzero lower-left `C` with invertible corner `A = Mᵢ`; equivalently **the Schur-complement
full-row-rank fact** `rank (D − C·A⁻¹·B) = D(|V|−2)` (§(4.42)'s option 1, declined-not-refuted), where the
Schur complement IS KT's row-op-(6.52) bottom `R(G₁∖row)`. **Efficiency lever:** the stranded, sound,
zero-caller `mixedBottom` family (`Concrete.lean:1460/1518/1610`) already places `e_b ∈ m₂` and reduces its
row-LI to a def-0-IH-dischargeable span-count — most of the bottom-side work, stranded only by the cert's
`toBlocks₂₁ = 0` demand. The new cert RELAXES that demand.

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

- [ ] **(1) Cert-shape design recon** (~1 docs commit) — validate the Schur-complement-with-invertible-corner
  route against KT (6.52)–(6.67) read directly, the landed `mixedBottom` family
  (`Concrete.lean:1460/1518/1610`), §(4.42)'s Schur analysis, and L-hD. Output: the chosen rank-lemma
  statement, a buildable-leaf list, the `d=3` zero-regression strategy (fork vs unify), and the **go/no-go for
  the item-(2) spike**. Decision gate: Schur-complement vs a genuinely non-block-triangular cert.
- [ ] **(2) Construct-or-concede de-risk spike** (the GATE — no reshape until green) — build the chosen rank
  lemma sorry-free on a concrete instance, consuming `mixedBottom`. Green → item (3); walls → back to (1) with
  a kernel-grounded obstruction. (The §(4.22)/(4.46) discipline: a spike answers composition, not
  dischargeability; do NOT carry the full-rank bottom as a hypothesis and call it feasible.)
- [ ] **(3) Build the rank infrastructure** — the new LA rank lemma (likely upstream-eligible under
  `CombinatorialRigidity/Mathlib/LinearAlgebra/Matrix/Rank.lean`, the A3/A4 neighbours) + wire the `mixedBottom`
  bottom + the Schur-complement = `R(G₁∖row)` full-rank identity (def-0 IH via `hsplitGP`).
- [ ] **(4) Reshape cert + arm** — `case_III_rank_certification` / `case_III_arm_realization` (and their
  `_matrix`/`_sep` siblings) to consume the new lemma, `d=3` zero-regression held.

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
- **The new cert = Schur-complement-with-invertible-corner (leading hypothesis)** (2026-06-26). With `A = Mᵢ`
  invertible (`hA`, landed), `rank (fromBlocks A B C D) = #m₁ + rank(Schur)` is standard LA, so the
  genuinely-new content is `rank (D − C·A⁻¹·B) = D(|V|−2)`, the Schur complement = KT's row-op-(6.52) bottom
  `R(G₁∖row)`. This is §(4.42)'s option 1 (DECLINED-not-refuted). The stranded `mixedBottom` family
  (`Concrete.lean:1460/1518/1610`, sound, zero callers) is most of its bottom side, blocked only by the cert's
  `toBlocks₂₁ = 0` demand — which the new cert relaxes. Recon (item 1) validates; spike (item 2) gates.

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
