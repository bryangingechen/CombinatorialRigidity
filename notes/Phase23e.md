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

**⚠️ BLOCKED on a STRATEGIC user decision — the A4 de-risk spike (§(4.47)) CORRECTED §(4.46): the
literal-`Matrix` route does NOT escape the bottom-deficiency wall; the genuinely-new core is an
`R(Gab)`-reproduction bottom.** Four recon steps (rows 503–506) settled the bottom-wall question and
landed on a sobering, compiler-grounded picture:
- (503) LEAF-4 spike: option-2 `hbotmem` unsatisfiable (`R(Gab)`'s `e₀` rows escape `span F₀`).
- (504) comparative recon: R1/R2/R3 all wall *in the dual-span representation* on the §(4.18)–(4.29) gate.
- (505) KT §6.4.2 source recon: KT uses a column op → literal `R(Gab)` bottom; claimed the literal-`Matrix`
  route escapes, "heavy but not new math" — **but this was a PROSE recon, over-optimistic on project-side
  feasibility.**
- (506) **A4 de-risk spike (compiler-grounded, CORRECTS 505):** A3/A4/the literal cert + arm are ALL LANDED
  (~80% of the spine), but the project's `columnOp` gives `fromBlocks A B 0 D` (0 **lower**-left, not KT's
  upper-right); the operated `e_b` `ab`-fill strands in the discarded upper-right `B`, so the cert's bottom
  is the **deficient pure-`Gv` `R(Gv)`** (`hD` unsatisfiable = §(4.36)). KT's full-rank `R(Gab)` bottom is
  **NOT a submatrix of `R(G,p)`** (G lacks the `a—b` edge); the matrix-equality form is BLOCKED (§(4.40)).
  **ALL FOUR landed bottom mechanisms wall on the one intrinsic deficiency obstruction.**

The genuinely-new core (design §(4.47)) is the **`R(Gab)`-reproduction bottom**: show the operated candidate
matrix's bottom block attains the rank of the full `R(Gab)`, via a rank-preserving construction that does
NOT need `R(Gab)` to be a literal submatrix of `R(G,p)`. High-risk, no landed precedent. The next step is the
user's strategic call (see *Hand-off*) — NOT a build. The literal spine (A1–A6, cert, arm) is reusable for
whichever bottom construction lands; the option-2 span leaves are sound but off-route.

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

- **🚧 BLOCKING — STRATEGIC user decision owed (the A4 de-risk spike, design §(4.47), CORRECTS §(4.46)).**
  A3/A4 + the literal cert + arm are ALL LANDED (the literal-`Matrix` spine is ~80% built; §(4.46)'s "~9–14
  new leaves" was stale). BUT the literal-`Matrix` route does NOT escape the bottom-deficiency wall: the
  project's `columnOp` gives `fromBlocks A B 0 D` (0 lower-left, NOT KT's upper-right), so the operated `e_b`
  `ab`-fill strands in the discarded upper-right `B` and the cert's bottom is the **deficient pure-`Gv`
  `R(Gv)`** (the literal arm's `hD` is unsatisfiable = §(4.36)). KT's full-rank `R(Gab)` bottom is NOT a
  submatrix of `R(G,p)` (G lacks the `a—b` edge); the matrix-equality `submatrix_columnOp_toBlocks₂₂_eq_Gab`
  is BLOCKED (§(4.40)). **All four landed bottom mechanisms wall on the one intrinsic deficiency obstruction.**
  The genuinely-new core is the **`R(Gab)`-reproduction bottom** (operated bottom block attains `R(Gab)`'s full
  rank via a rank-preserving construction, NOT a literal submatrix) — high-risk, no landed precedent. Strategic
  directions (design §(4.47)): **(a)** invest in the `R(Gab)`-reproduction bottom; **(b)** reconsider fallback
  (C) declined at 23d-open (route A's bottom now confirmed genuinely-hard across all four representations);
  **(c)** re-scope. The literal spine (A1–A6, cert, arm) is reusable for whichever bottom lands.
- **Orthogonal carried hypothesis: GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive)
  — independent of the override-gate wall; tracked separately, not gating the route-A cert work.
- **L-hD is the wrong shape for the bottom** (matrix-`toBlocks₂₂.row` LI, not functional `LinearIndependent ℝ
  bottom`) — the stale L-hD-as-bottom-brick ref below + in §(4.43) is corrected by §(4.44); `hbotindep`
  goes via the basis route `bW.linearIndependent_coe_subtype` (the `.map'` route hits the carrier `whnf` wall).
- **OD-4 / OD-1 are downstream** (CHAIN-4 internal alg-independence route; ENTRY's dichotomy shape) — the
  frozen contract (C.5/C.6) is invariant under both; neither touches 23e.

## Hand-off / next phase

**Next step is a STRATEGIC user decision — NOT a build, NOT a further recon (design §(4.47)).** The A4
de-risk spike confirmed A3/A4/cert/arm are landed but the literal-`Matrix` route does NOT escape the
bottom-deficiency wall (the project's `columnOp` strands the `ab`-fill in the discarded upper-right block;
the bottom is the deficient pure-`Gv` `R(Gv)`). All four landed bottom mechanisms wall on the one intrinsic
obstruction. The user must decide among (design §(4.47)): **(a)** invest in the genuinely-new
`R(Gab)`-reproduction bottom (the operated bottom block attains `R(Gab)`'s full rank via a rank-preserving
construction, NOT a literal submatrix — high-risk, no landed precedent; the matrix-equality form is BLOCKED,
so it needs a fresh rank/LI-level idea); **(b)** reconsider the fallback (C) declined at 23d-open (route A's
bottom is now confirmed genuinely-hard across all four representations); **(c)** re-scope.

**What is solid regardless:** the literal-`Matrix` spine (A1–A6, the cert `case_III_rank_certification_matrix`,
the arm `case_III_arm_realization_matrix`) is landed + axiom-clean and reusable for whichever bottom
construction lands; the option-2 span leaves (LEAF-DBL/SEPCERT/SEPARM + the wrapper) are sound but off-route.
CHAIN-5 (item (4)) is independent but not productive until a sound cert exists. GAP 6 (all-`k` IH) is a
separate carried hypothesis. After a sound bottom lands, the LEAF-5 router + CHAIN-5 close the CHAIN layer;
ENTRY + ASSEMBLY remain.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **The bottom-deficiency wall is INTRINSIC across all four representations; the genuinely-new core is an
  `R(Gab)`-reproduction bottom** (2026-06-26, rows 503–506, design §(4.44)–§(4.47)). Four recons converged:
  (503) LEAF-4 spike — option-2 `hbotmem` unsatisfiable (`R(Gab)`'s `e₀` rows escape `span F₀`); (504)
  comparative recon — R1/R2/R3 all wall in the dual-span rep; (505) KT §6.4.2 PROSE recon — claimed the
  wall is a dual-span artifact + the literal-`Matrix` route escapes (right about KT's math, OVER-OPTIMISTIC
  on project-side feasibility); (506) **A4 de-risk spike (compiler-grounded, CORRECTS 505)** — A3/A4/cert/arm
  are ALL LANDED (~80% of the spine), but the project's `columnOp` gives `fromBlocks A B 0 D` (0 lower-left,
  not KT's upper-right), so the operated `e_b` `ab`-fill strands in the discarded upper-right `B` and the
  cert's bottom is the deficient pure-`Gv` `R(Gv)` (`hD` unsatisfiable = §(4.36)); KT's full-rank `R(Gab)` is
  NOT a submatrix of `R(G,p)` (no `a—b` edge), the matrix-equality is BLOCKED. The genuinely-new core: the
  `R(Gab)`-reproduction bottom (rank-preserving, not a literal submatrix). STOP — strategic decision owed
  (a invest / b fallback C / c re-scope, §(4.47)). **Meta-lesson:** the de-risk-spike-before-build (the
  user's choice) caught the §(4.46) prose recon's over-optimism pre-build — a route-composition feasibility
  claim needs a compiler-checked spike, not prose (DESIGN.md *Compiler-checked spike, not prose recon*).
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
