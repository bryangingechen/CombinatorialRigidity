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

**⚠️ BLOCKED on a design decision — user adjudication owed (design §(4.44)).** A read-only
compiler-checked LEAF-4 satisfiability spike (2026-06-26, row 503) found that the option-2 cert's
bottom obligation `hbotmem` is **UNSATISFIABLE with the intended `bottom = R(Gab)`**: the fresh
`e₀=(a,b)` split-off rows do NOT land in `span F₀` (the plain-`q` forked candidate) — G has no a—b
link, so only the single redundancy direction `ρ` lands, not a full `e₀`-block basis. This is the
§(4.36)/(4.37) **bottom-deficiency wall**, NOT dissolved: §(4.38)'s "R(Gab) edge rows dissolve it"
make-or-break (the KT (6.61)→(6.62) span-membership) was flagged "then UNSPIKED" and is now refuted.
The landed leaves (LEAF-DBL/SEPCERT/SEPARM + the 23e wrapper) are SOUND conditional lemmas but rest
on this unsatisfiable hypothesis, so **23d's "rank-cert scope CLOSED" was premature**. The next step
is a **design decision / recon (NOT a build)** — see *Blockers* + *Hand-off*. The non-bottom pieces
(count, `hbotindep` via the basis route, `hbotblind`, corner) all compose; only `hbotmem` walls.

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

- **🚧 BLOCKING (user adjudication owed) — the option-2 bottom `hbotmem` wall (design §(4.44)).** The
  option-2 cert (`case_III_rank_certification_matrix_sep`) requires `bottom` (card `D·(|Vᵥ|−1)`, LI,
  v-blind) ⊆ `span F₀` (plain-`q` candidate). The intended `bottom = R(Gab)` fails: its `e₀=(a,b)` rows
  escape `span F₀`. Three structurally-different bottoms have now hit this same obstruction (pure-`Gv`
  §4.36 / augmented §4.37 / R(Gab)-literal §4.38→§4.44), so it is **intrinsic to `F₀`'s span** (no
  full-rank v-blind bottom when `Gᵥ` is deficient). Resolution directions (design §(4.44) VERDICT):
  **(R1)** re-route the bottom onto the landed relabel/`_chain` Architecture B (KT-6.66 abstract fill
  rows in the RELABELLED candidate, `bottomRelabel_rigidityRows_mem_span_caseIIICandidate` ForkedArm.lean:729)
  — the designed KT route; restates the wrapper + the cert's consumed convention. **(R2)** plain-`q`
  bottom = v-blind part of `span F₀` (`R(Gᵥ)` + fork redundancies) — likely FALSE for deficiency `k'≥2`.
  **(R3)** revisit §(4.42) option-1/Schur or a fresh cert shape. **Recommend a focused compiler-checked
  design recon to pin Architecture B before any rebuild.** Touches the user's #33/#35 option-2 adjudication.
- **L-hD is the wrong shape for the bottom** (matrix-`toBlocks₂₂.row` LI, not functional `LinearIndependent ℝ
  bottom`) — the stale L-hD-as-bottom-brick ref below + in §(4.43) is corrected by §(4.44); `hbotindep`
  goes via the basis route `bW.linearIndependent_coe_subtype` (the `.map'` route hits the carrier `whnf` wall).
- **OD-4 / OD-1 are downstream** (CHAIN-4 internal alg-independence route; ENTRY's dichotomy shape) — the
  frozen contract (C.5/C.6) is invariant under both; neither touches 23e.

## Hand-off / next phase

**Next step is NOT a build — a design decision is owed (design §(4.44), user adjudication).** The LEAF-4
spike refuted the option-2 bottom `hbotmem` (the intended `bottom = R(Gab)` escapes `span F₀` on the
`e₀=(a,b)` rows). Until the bottom architecture is resolved, LEAF-4/LEAF-5 cannot be built. The likely
next concrete commit (pending the user's call) is a **focused compiler-checked design recon** scoping
resolution direction **(R1)** — re-route the interior-arm bottom onto the landed relabel/`_chain`
Architecture B (`bottomRelabel_rigidityRows_mem_span_caseIIICandidate`, KT-6.66 abstract fill rows in the
RELABELLED candidate): determine exactly what restates (the just-landed wrapper's plain-`q`
interior-`splitOff` geometry → the relabelled-base convention; the cert's `hbotmem`/`hcornermem`
candidate; whether LEAF-SEPCERT/SEPARM survive or restate). Alternatives (R2)/(R3) in §(4.44).

**What is solid regardless of the resolution:** the count/`hbotindep`(basis route)/`hbotblind`/corner
pieces compose; the corner side is plain-`q`-consistent; the landed conditional leaves are sound (just
fed a walled hypothesis). The CHAIN-5 lockstep reshape (item (4)) is independent of the bottom-architecture
call and could proceed in parallel if desired, but the cert it ultimately wires must first be satisfiable.

Then (after the bottom is re-routed) the LEAF-5 router + CHAIN-5 close the CHAIN layer; ENTRY + ASSEMBLY
remain. Commit estimate is no longer the §(4.43) ~3–4 (that assumed the bottom CLEAR); re-estimate after
the §(4.44) adjudication.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **The option-2 bottom `hbotmem` is WALLED — LEAF-4 spike refuted §(4.38)** (2026-06-26, row 503, design
  §(4.44)). A read-only compiler-checked spike showed the intended `bottom = R(Gab)` does NOT satisfy the
  cert's `hbotmem` (the fresh `e₀=(a,b)` split-off rows escape `span F₀`; G has no a—b link, only the single
  redundancy `ρ` lands). This is the §(4.36)/(4.37) bottom-deficiency wall — §(4.38)'s "R(Gab) edge rows
  dissolve it" make-or-break (the KT (6.61)→(6.62) span-membership) was "then UNSPIKED" and is now refuted.
  Landed leaves are sound (conditional) but rest on a walled hypothesis ⟹ 23d's rank-cert close was
  premature. Resolution owed (user adjudication): (R1) relabel/`_chain` re-route (recommended), (R2)/(R3)
  in §(4.44). The spike-before-build caught this where a build would have BLOCKED after a wasted cycle.
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
