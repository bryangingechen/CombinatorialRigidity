# Phase 23e — Case III general `d`: the general-`k` dispatch + CHAIN-5 (work log)

**Status:** in progress (opened 2026-06-26 at the 23d rank-cert-scope close).
**Phase 23 stays in progress**; 23e is the *fourth* CHAIN-layer sub-phase (CHAIN spans
23b + 23c + 23d + 23e, design §3). ENTRY + ASSEMBLY are later sub-phases (codes-until-open).
The authoritative dep-graph / scope for 23e is **`notes/Phase23-design.md` §(4.43)** ("END-TO-END
SCOPE OF THE REMAINING 23d PATH") + **§C.0–C.6** (the CHAIN↔ENTRY contract); this note does **not**
duplicate that recon — it carries the current state, the leaf checklist, blockers, and hand-off, and
points there. Program map: `notes/MolecularConjecture.md`. 23d's landed route-A inventory (the rank
cert this dispatch consumes): `notes/Phase23d.md` *Current state* leaf table.

## Current state

**Next concrete commit = the `chainData_dispatch` leaf** (item (3) of §(4.43); the general-`k`
`Fin cd.d` router). 23d closed the general-`d` rank certification (route A, the option-2 separate-`R(Gab)`
cert chain LEAF-DBL → LEAF-SEPCERT → LEAF-SEPARM, all green/axiom-clean, no `ScrewSpace` unfold). What
remains to complete the CHAIN layer is **wiring**: build the router that dispatches the chain index
`i : Fin cd.d` (base/`d=3` → the landed `chainData_split_realization`; interior `2 ≤ i` → the landed
`case_III_arm_realization_matrix_sep` / LEAF-SEPARM), then reshape the spine's `hdispatch`/`hcand` to the
frozen `cd : G.ChainData n` record (C.0 lockstep) with a `d=3` zero-regression adapter.

§(4.43) scoped the whole remaining path **CLEAR — no new-math wall**: the rank cert is done, the
general-`k` unpack typechecks (the `k=2` in `case_III_candidate_dispatch` is *consumer hardcoding*, not an
unpack wall), and LEAF-SEPARM is the interior arm the dispatch feeds. The dispatch's hardest single
obligation (the corner `hLI` producer, leaf 3) is **already LANDED**
(`exists_corner_blockBasisOn_linearIndependent`, 23d); dispatch leaves 1 + 2 (the corner-entry brick +
the `hA` leaf, relaxed to `.2 ≠ v`) are LANDED too. So 23e is the leaves the dispatch spike (design
§(4.35)) named as still-open: the `chainData_dispatch` wiring + the bottom obligations it supplies to
LEAF-SEPARM + CHAIN-5.

Nothing is mid-stream as of this docs-only phase-open commit (no Lean touched; the first build leaf is
the next commit). `d=3` stays fully green throughout (zero-regression is a hard constraint).

## Architectural choices made up front

- **Frozen interface.** The `G.ChainData n` record (C.1) and the CHAIN↔ENTRY contract (C.0–C.6) are
  frozen in `notes/Phase23-design.md`. 23e builds the *consumer* (the dispatch + CHAIN-5) against that
  frozen shape; ENTRY (the producer) is parallel-safe against it. The one sanctioned interface touch is
  the C.3 `hIH` addition (below, under *Decisions made*).
- **No motive/IH change.** Route A reshaped only the rank cert + arm realization; the dispatch's
  `hdispatch` consume-shape, the `ChainData` record, and the 0-dof motive/IH are unchanged save for the
  one-field C.3 `hIH` addition (§I.8.21 confirmed no motive/IH-level blocker).

## Lemma checklist

Transcribed from `notes/Phase23-design.md` §(4.43) buildable-leaf decomposition (the two LEAF-SEP* items
there closed in 23d). Exact decl names where fixed; the dispatch internals decompose per the §(4.35)
dispatch spike (5 leaves — leaves 1/2/3 already LANDED in 23d).

- [ ] **(3) `chainData_dispatch`** (~2 commits) — the general-`k` `Fin cd.d` router.
  - Signature **carries `hIH`** (the sanctioned C.3 addition; see *Decisions made*).
  - Routes `i ≤ 1` (base / `d=3`) → the landed `PanelHingeFramework.chainData_split_realization`
    (`CaseIII/Realization.lean:1046`).
  - Routes interior `2 ≤ i < d` → the landed `PanelHingeFramework.case_III_arm_realization_matrix_sep`
    / LEAF-SEPARM (`CaseIII/Relabel/ForkedArm.lean:234`).
  - Interior `hsplitGP` (the per-`i` IH-generic base realization on `G.splitOff vᵢ …`) derived via
    `splitOff_isMinimalKDof` (`Induction/ForestSurgery/Reduction.lean:161`) **from `hIH`**.
  - Supplies LEAF-SEPARM's disjoint-block obligations: `corner` from the landed §(4.35) corner leaves
    (1, 2, 3 — all LANDED in 23d, incl. `exists_corner_blockBasisOn_linearIndependent`);
    `bottom`/`hbotindep`/`hbotmem`/`hbotblind` from `hsplitGP`'s IH `R(Gab)` full rank + the cross-label
    bridge + L-span; `hcornerpin`(=`hA`)/`hcornermem` from A5a.
  - Reads `hρe₀` off the landed interior chain `interior_hρe₀_of_baseWidening`
    (`CaseIII/Relabel/ForkedArm.lean`); discharges geometric hyps via the `d=3` `hne_F₀` pattern.
  - GAP-2 resolved: the `ends`-orientation pins use the `Function.update` override `ends₁` (= the landed
    `d=3` router `chainData_split_realization` pattern, `Realization.lean:1159`).
- [ ] **(4) CHAIN-5** (~1–2 commits) — wire the dispatch into the spine.
  - The C.0 lockstep reshape of `hdispatch`/`hcand` (currently the `(v,a,b,c,…)` 8-tuple bundle, fed by
    `Graph.exists_chain_data_of_noRigid`) to the frozen `cd : G.ChainData n` shape — three decls in
    lockstep (C.0): the producer `case_III_hsplit_producer_all_k` (`CaseIII/Arms.lean`), the consumer
    `case_III_realization_all_k.hdispatch` (`CaseIII/Realization.lean`), and
    `theorem_55_minimalKDof_k_all_k.hdispatch` (`AlgebraicInduction/Theorem55.lean`).
  - The `d=3` zero-regression adapter: `case_III_candidate_dispatch`
    (`CaseIII/Realization.lean:268`) stays byte-reachable via the C.4 record-to-tuple map
    `vtx = ![b, v, a, c]` (the only fiddly part; no `d=3` proof changes, just a 4-tuple→`ChainData`
    projection adapter).

(ENTRY + ASSEMBLY are later sub-phases — out of 23e's scope. ENTRY reshapes
`Graph.exists_chain_data_of_noRigid` to the `ChainData` producer + lifts the `6 ≤ bodyBarDim n` floor +
resolves OD-1; ASSEMBLY composes the honest general-`d` Theorem 5.5, re-greens
`prop:rigidity-matrix-prop11` + `hub`, derives Thm 5.6, states Conjecture 1.2.)

## Blockers / open questions

- **None blocking the next commit.** §(4.43) scoped the path CLEAR (no new-math wall). The C.3 `hIH`
  interface obligation is **adjudicated & approved** (see *Decisions made*), so it no longer gates.
- **Build-time latitude (not a blocker):** the exact `Fin` arithmetic of indexing `cd.vtx`/`cd.edge` in
  the router, and a possible `maxHeartbeats` bump on the `Sum.elim`-over-`ScrewSpace`-carrier whnf in the
  cert composition (LEAF-SEPCERT landed at default heartbeats in 23d, so this likely doesn't recur).
- **OD-4 / OD-1 are downstream** (CHAIN-4 internal alg-independence route; ENTRY's dichotomy shape) — the
  frozen contract (C.5/C.6) is invariant under both; neither touches 23e.

## Hand-off / next phase

**Next concrete commit:** the `chainData_dispatch` leaf (item (3), §(4.43)) — the general-`k` `Fin cd.d`
router, signature carrying `hIH`, base→`chainData_split_realization`, interior→LEAF-SEPARM. The dispatch
spike (design §(4.35)) confirmed it composes end-to-end modulo this wiring; leaves 1/2/3 are LANDED in
23d, so the open work is leaf 4's bottom obligations (supplied to LEAF-SEPARM from `hsplitGP`'s IH + the
cross-label bridge + L-span) + leaf 5's wiring (the `obtain`-`j₀`-before-`corner` order).

Then CHAIN-5 (the C.0 lockstep + `d=3` adapter) closes the CHAIN layer. After 23e, ENTRY + ASSEMBLY
remain (parallel-safe against the frozen contract). Full decomposition + commit estimate (~3–4 commits
for 23e): design §(4.43).

## Decisions made during this phase

### Phase-local choices and proof techniques

- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; the lone
  sanctioned interface touch). The frozen contract C.3 hands the dispatch the BASE-split `hsplitGP` (at
  `v₁`), but the interior arm needs the INTERIOR-split one (`G.splitOff vᵢ …`), derivable only from `hIH`
  (via `splitOff_isMinimalKDof`), which is not in the C.3 signature. Verdict: add `hIH` to the C.3
  dispatch consume-shape — a **one-field addition** to the consume-shape, touching the C.0
  producer/consumer/ENTRY lockstep trio, **NOT** a motive/IH-strength change (the landed floor router
  `chainData_split_realization` already carries `hIH` separately, confirming the shape). Do not reopen.
  Full context: design §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
