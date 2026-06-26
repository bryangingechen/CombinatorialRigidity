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

**⚠️ BLOCKED on a STRATEGIC user decision — the KT re-read (§(4.46)) reframed the wall as a
representation ARTIFACT with a FEASIBLE KT-faithful fix (heavy Lean engineering, NOT new math).**
Three recon steps (rows 503/504/505) settled the bottom-wall question: (503) the LEAF-4 spike refuted
the option-2 bottom `hbotmem` (`bottom = R(Gab)`'s `e₀=(a,b)` rows escape `span F₀`); (504) the
comparative recon found R1/R2/R3 all wall *within the dual-span representation* on the one §(4.18)–(4.29)
override-gate obstruction; (505) **the KT §6.4.2 source re-read found this wall is an ARTIFACT of the
formalization's dual-span rigidity-matrix representation** (`rigidityRows : Set (Module.Dual …)`,
span-based rank) — **KT has no override-gate and no span-membership obligation**: KT certifies the
interior bottom by an explicit invertible **column operation** landing `R(G₁,q₁)` as a **literal
block-triangular submatrix** (6.61)→(6.64), rank by block-additivity (6.65), the `k'`-deficiency
*inherited* from the base (IH 6.1), never re-filled. **The KT-faithful fix is the §(4.30) literal-`Matrix`
route-A spine** (23d's A1–A5c chain + the literal cert `case_III_rank_certification_matrix` are reusable;
the §(4.41) `e_b`-pin issue resolves via KT's column op, not the abandoned span options). **Heavy
(~9–14 leaves, A3/A4 genuinely-new ENGINEERING), but NOT blocked on new mathematics.** The next step is
the user's strategic call (see *Hand-off*) — NOT a build, NOT a further recon. 23d's "rank-cert CLOSED"
was premature; the option-2 span leaves (LEAF-DBL/SEPCERT/SEPARM + the wrapper) are sound but OFF the
KT-faithful route.

~~Next concrete commit = the `chainData_dispatch` router proper~~ (SUPERSEDED by the wall above). The
interior-arm geometry wrapper is **LANDED** (sound, but consumes the walled `hbotmem`):
`PanelHingeFramework.chainData_arm_realization_sep` (`CaseIII/Realization.lean`, after
`chainData_split_realization`, 2026-06-26; build/lint/warning/axiom-clean). It is the `ChainData`-indexed
sibling of `chainData_split_realization` for the **option-2 (separate `R(Gab)` bottom)** route: it reads
the interior split tuple `(v,a,b,e_a,e_b) = (vtx i.castSucc, vtx i.succ, vtx (i−1).castSucc, edge i,
edge (i−1))` off the `cd` accessors, builds the `Gv = G − vᵢ` framework geometry (the verbatim
`chainData_split_realization` setup), and ends in `case_III_arm_realization_matrix_sep` / LEAF-SEPARM. The
disjoint-block obligations (`corner`/`bottom`, `hcornerpin`/`hbotblind`/`hbotindep`/`hcornermem`/`hbotmem`,
`hm₁`/`hm₂`) + the geometric gates (`hLn`/`hgab`) + the framework general position `hgp` + the `ends`
override are **carried as hypotheses** — LEAF-4's outputs the router (LEAF-5) threads in. So the remaining
LEAF-5 work is: fire LEAF-3 (`exists_shared_redundancy_and_matched_candidate`), case-split `(i : ℕ)`
(base/`d=3` → `chainData_split_realization`; interior `2 ≤ i` → `chainData_arm_realization_sep`), and build
the disjoint-block bundle (LEAF-4: corner from leaves 1/2/3, bottom from `hsplitGP`'s IH + cross-label
bridge + L-span; `hρe₀` via `interior_hρe₀_of_baseWidening`).

23d closed the general-`d` rank certification (route A, the option-2 cert chain LEAF-DBL → LEAF-SEPCERT →
LEAF-SEPARM, all green/axiom-clean, no `ScrewSpace` unfold). §(4.43) scoped the whole remaining path
**CLEAR — no new-math wall**: the general-`k` unpack typechecks (the `k=2` in `case_III_candidate_dispatch`
is *consumer hardcoding*, not an unpack wall). The dispatch's hardest single obligation (the corner `hLI`
producer, leaf 3) is LANDED (`exists_corner_blockBasisOn_linearIndependent`, 23d); leaves 1 + 2 are LANDED.

Nothing is mid-stream. `d=3` stays fully green throughout (zero-regression is a hard constraint).

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

- [ ] **(3) `chainData_dispatch`** (~1–2 commits remaining) — the general-`k` `Fin cd.d` router.
  - Signature **carries `hIH`** (the sanctioned C.3 addition; see *Decisions made*).
  - Routes `i ≤ 1` (base / `d=3`) → the landed `PanelHingeFramework.chainData_split_realization`
    (`CaseIII/Realization.lean`).
  - [x] Routes interior `2 ≤ i < d` → the interior-arm geometry wrapper
    `PanelHingeFramework.chainData_arm_realization_sep` (**LANDED** 2026-06-26, `CaseIII/Realization.lean`,
    after `chainData_split_realization`) — the `ChainData`-indexed sibling for the LEAF-SEPARM route: reads
    the interior split tuple off `cd`, builds the `Gv = G − vᵢ` geometry, ends in
    `case_III_arm_realization_matrix_sep` (`CaseIII/Relabel/ForkedArm.lean:234`). Carries the disjoint-block
    obligations + `hLn`/`hgab`/`hgp`/`ends`-override as hypotheses (LEAF-4's outputs the router threads in).
    What remains in (3): fire LEAF-3, case-split `(i:ℕ)`, build the LEAF-4 disjoint-block bundle.
  - Interior `hsplitGP` (the per-`i` IH-generic base realization on `G.splitOff vᵢ …`) derived via
    `splitOff_isMinimalKDof` (`Induction/ForestSurgery/Reduction.lean:161`) **from `hIH`**.
  - Supplies LEAF-SEPARM's disjoint-block obligations: `corner` from the landed §(4.35) corner leaves
    (1, 2, 3 — all LANDED in 23d, incl. `exists_corner_blockBasisOn_linearIndependent`);
    `hcornerpin`(=`hA`)/`hcornermem` from A5a. **⚠️ `bottom`/`hbotmem` WALLED (design §(4.44)):** the
    intended `bottom = R(Gab)` does NOT land in `span F₀` (the `e₀` rows escape); `hbotindep` goes via the
    basis route (NOT L-hD, wrong shape); resolution = the (R1) relabel/`_chain` re-route, user-adjudicated.
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

- **🚧 BLOCKING — STRATEGIC user decision owed (the KT re-read reframe, design §(4.46)).** The wall is an
  **ARTIFACT of the dual-span rigidity-matrix representation**, not a KT obstruction (the §(4.45) "R1/R2/R3
  all wall" is correct only *within* that representation). KT certifies the interior bottom by an explicit
  invertible **column op** landing `R(G₁,q₁)` as a **literal block-triangular submatrix** (6.61)→(6.64),
  rank by block-additivity (6.65); no span membership, no override-gate, deficiency inherited from the base
  (IH 6.1). **§(4.42)'s "option-1" was a row-op-Schur, NOT KT's column op** — both §(4.42) options stayed in
  the span world that manufactures the wall. **The KT-faithful fix = the §(4.30) literal-`Matrix` route-A
  spine** (23d's A1–A5c + the literal cert `case_III_rank_certification_matrix` reusable; the §(4.41) `e_b`-pin
  issue resolves via the column op): **heavy (~9–14 leaves; A3 matrix block-additivity + A4 the entrywise
  (6.61) column op are genuinely-new ENGINEERING), but NOT new mathematics.** Strategic call (design §(4.46)):
  commit to the route-A literal-`Matrix` completion (reusing 23d's A1–A5c), vs. reconsider scope given the
  cost. Re-opens the §(4.42) option-2 choice.
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive)
  — independent of the override-gate wall; tracked separately, not gating the route-A cert work.
- **L-hD is the wrong shape for the bottom** (matrix-`toBlocks₂₂.row` LI, not functional `LinearIndependent ℝ
  bottom`) — the stale L-hD-as-bottom-brick ref below + in §(4.43) is corrected by §(4.44); `hbotindep`
  goes via the basis route `bW.linearIndependent_coe_subtype` (the `.map'` route hits the carrier `whnf` wall).
- **OD-4 / OD-1 are downstream** (CHAIN-4 internal alg-independence route; ENTRY's dichotomy shape) — the
  frozen contract (C.5/C.6) is invariant under both; neither touches 23e.

## Hand-off / next phase

**Next step is a STRATEGIC user decision — NOT a build, NOT a further recon (design §(4.46)).** The KT
re-read found the wall is a representation artifact and the KT-faithful fix is FEASIBLE (the §(4.30)
literal-`Matrix` route-A spine; heavy Lean engineering, not new math). The user must decide: **commit to
the route-A literal-`Matrix` completion** (the column-op block-triangular cert — resume 23d's literal cert
`case_III_rank_certification_matrix` + A1–A5c, resolve the §(4.41) `e_b`-pin via KT's column op; the
genuinely-new pieces are A3 matrix block-additivity + A4 the entrywise (6.61) column op; ~9–14 leaves),
**vs. reconsider scope** given the cost. If "commit", the **first concrete commit** is most likely a
compiler-checked spike of A4 (the entrywise column op (6.61) as an invertible right-multiplication →
`Matrix.rank_mul_eq_right_of_isUnit_det`) — the highest-risk genuinely-new piece — before the surrounding
leaves; settle the A3/A4 sub-decomposition first.

**What is solid regardless:** 23d's literal-`Matrix` A1–A5c chain + the literal cert are reusable; the
option-2 span leaves (LEAF-DBL/SEPCERT/SEPARM + the wrapper) are sound but OFF the KT-faithful route (do
not build the cert on them). The CHAIN-5 lockstep reshape (item (4)) is independent of the cert and could
proceed in parallel, but is not productive until the cert is sound. GAP 6 (all-`k` IH) is a separate
carried hypothesis. After the literal-`Matrix` cert lands, the LEAF-5 router + CHAIN-5 close the CHAIN
layer; ENTRY + ASSEMBLY remain.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **The bottom wall is a REPRESENTATION ARTIFACT; KT-faithful fix is the literal-`Matrix` route A — heavy,
  not new math** (2026-06-26, rows 503/504/505, design §(4.44)/§(4.45)/§(4.46)). Three recons: (503) LEAF-4
  spike refuted the option-2 `hbotmem` (`R(Gab)`'s `e₀` rows escape `span F₀`); (504) R1/R2/R3 all wall *in
  the dual-span representation* on the §(4.18)–(4.29) override-gate; (505) the KT §6.4.2 re-read found the
  wall is an **artifact of the dual-span `rigidityRows` representation** — KT uses an explicit invertible
  **column op** landing `R(G₁,q₁)` as a **literal block-triangular submatrix** (no span membership, no
  override-gate; deficiency inherited via IH 6.1). §(4.42)'s "option-1" was a row-op-Schur, NOT KT's column
  op. The KT-faithful fix = the §(4.30) literal-`Matrix` route-A spine (23d's A1–A5c + the literal cert
  reusable; A3 block-additivity + A4 the entrywise (6.61) column op are genuinely-new ENGINEERING; ~9–14
  leaves) — heavy but NOT blocked on new mathematics. 23d's "rank-cert CLOSED" was premature; the option-2
  span leaves are sound but OFF this route. STOP — strategic user decision owed (commit to route A vs.
  reconsider scope, §(4.46)). The KT-re-read-before-investing avoided committing to a heavy span-route
  rebuild that would have re-walled.
- **Interior arm landed as a geometry wrapper, block obligations carried** (`chainData_arm_realization_sep`,
  2026-06-26). Split the interior dispatch route into a thin `cd`-accessor + `Gv`-geometry layer (mirroring
  `chainData_split_realization`'s setup verbatim, ending in `case_III_arm_realization_matrix_sep`) that
  takes the disjoint-block data (`corner`/`bottom` + LI/membership/blind facts) + `hLn`/`hgab`/`hgp`/the
  `ends`-override as **hypotheses**. Keeps the geometry-plumbing leaf fully complete + reusable while the
  LEAF-4 block production stays a separate commit; the `ends` slot is the caller-supplied override `ends₁`
  (so disjoint-block rows are stated against it). Needs `hV3`/`hSimple` (the `Gv` vertex-count + `Loopless`
  the sibling carries). Axiom-clean.
- **C.3 `hIH`-on-consume-shape addition — APPROVED** (user-adjudicated 2026-06-26, session #36; the lone
  sanctioned interface touch). The frozen contract C.3 hands the dispatch the BASE-split `hsplitGP` (at
  `v₁`), but the interior arm needs the INTERIOR-split one (`G.splitOff vᵢ …`), derivable only from `hIH`
  (via `splitOff_isMinimalKDof`), which is not in the C.3 signature. Verdict: add `hIH` to the C.3
  dispatch consume-shape — a **one-field addition** to the consume-shape, touching the C.0
  producer/consumer/ENTRY lockstep trio, **NOT** a motive/IH-strength change (the landed floor router
  `chainData_split_realization` already carries `hIH` separately, confirming the shape). Do not reopen.
  Full context: design §(4.43) *THE ONE INTERFACE OBLIGATION* + §C.3.
