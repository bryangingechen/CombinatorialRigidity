# Phase 23f — Case III general `d`: the geometry arm + the chain dispatch (work log)

**Status: ✓ COMPLETE** (closed 2026-06-29). The fifth and final CHAIN-layer sub-phase
(CHAIN = 23b + 23c + 23d + 23e + 23f). 23f built the geometry-arm infrastructure that
*constructs* the 23e cert's block data from the IH-fed widening, then completed the
**chain dispatch** — the geometry arm's last build piece — and retired the diverged
`_aug`/(D-substitution) interior fork (four deletion commits). The chain dispatch is the
general-`d` lift of the `d=3` `case_III_candidate_dispatch`; it lands **unused** (no live
consumer until 23g wires the C.0-trio CHAIN-5 field + the ENTRY general-`d` `ChainData`
extractor) — the design-pinned state, not an omission. `d=3` stays fully green throughout
via the untouched honest `k=2`-spine engine. Authoritative scoping:
`notes/Phase23-design.md` §(4.84)–(4.106) (closed; cited verdicts) + §C.0–C.6 (the frozen
contract). Program map: `notes/MolecularConjecture.md`.

## Hand-off / next phase (23g — ENTRY: chain extraction + CHAIN-5)

**23g gives the router a live consumer.** The router lands unused today: the C.0-trio
`hcand`/`hdispatch` field is still the `d=3` 8-tuple and no `ChainData` value constructor
exists at general `d`. Wiring needs two pieces (design §C.2/§C.5):

1. **CHAIN-5** — reshape the 8-tuple `hcand`/`hdispatch` field → `cd : G.ChainData n`.
2. **ENTRY** `exists_chain_data_of_noRigid` reshape
   (`Induction/ForestSurgery/Reduction.lean:383`, returns only the `d=3` 4-tuple today →
   general-`d` `ChainData` extractor, KT Lemma 4.6 chain-or-cycle / Lemma 4.8 split-off, +
   the Lemma 5.4 cycle branch) + the `hD` floor.

The frozen CHAIN↔ENTRY contract (C.5/C.6) is invariant; none touches 23e's cert; no
motive/IH change. The C.3 `hIH` consume-shape add (approved, landed with the router) is
the general `(k':ℤ)` IH already in scope at the spine — not a motive/IH-strength change.
Carry forward **GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive —
orthogonal to the cert; tracked separately). `ASSEMBLY` = **23h**.

**Two OUT-OF-SCOPE `d=3`-era orphans for a later sweep / 23g** (NOT `_aug`-fork, self-only):
`interior_hsplitGP` (`Realization.lean`) and `case_III_realization_of_line` (`Arms.lean`).

⚠️ **`caseIIICandidate` + its API are LIVE — DO NOT delete** (the honest engine consumes
it via `case_III_realization_of_rank` ← `case_III_arm_realization`). The non-aug edge-path
helpers `rigidityMatrixEdge_mul_columnOp_*` (WITHOUT `Aug`) in `Concrete.lean` are also LIVE.

## Architectural choices made up front (inherited from 23e / the frozen contract)

- **Cert is consumed, not re-derived.** The 23e cert chain is axiom-clean + SATISFIABLE;
  23f only *produces* its block data. Build against the literal `Lrow * M * U` product,
  NOT the component leaves in isolation (the §(4.46)/(4.54) lesson).
- **`d=3` zero-regression via the cert FORK.** `d=3` keeps the `_matrix`/M₃ path; only the
  general-`d` arm routes through the general-`d` cert. Do NOT unify the two. The corner
  seam is a `d ≥ 4`-only phenomenon (§(4.83)/(4.90)).
- **Below the CHAIN↔ENTRY contract TYPES + the motive/IH.** The geometry arm + dispatch are
  below the C.0–C.6 signatures and the 0-dof motive (no new motive conjunct, no
  IH-strength change, no `ChainData` field). The C.3 `hIH` field is an approved
  consume-shape add, not a motive change.

## Lemma inventory (all LANDED, axiom-clean, gates green, `d=3` untouched)

The full design detail for each item lives in the named §(4.9x)/§(4.10x) of
`notes/Phase23-design.md` (closed; cited verdicts). Compressed to one-line verdicts:

- **THE CHAIN DISPATCH — COMPLETE.** The router `chainData_dispatch` (`CaseIII/Realization.lean`)
  + both branches `chainData_dispatch_{interior,floor}_of_discriminator` + the firing producer
  `chainData_fire_discriminator`. Pure routing over the firing producer's base-split bundle:
  `by_cases 2 ≤ (i:ℕ)` → interior (the honest interior arm via the cert) / base-floor
  (M₁/M₂ arms). Design §(4.103)–(4.105).
- **The reshape live route.** The honest interior arm `chainData_interior_realization_hρGv`
  (`Realization.lean`) re-indexes `case_III_arm_realization` at the interior split tuple,
  candidate functional `−ρ₀`, seed `qρ = q ∘ shiftPerm i.castSucc`; the crux `hρGv` slot
  lands at the HONEST base selector `ends₀` (the leaf `chainData_relabel_arm_hρGv`,
  `ChainColumn.lean`) bridged to the override `endsσρ₁` via `rigidityRows_ofNormals_congr_ends`,
  the bottom `hwmem` slot at `candidateEnds i ends₀` bridged via the swap-tolerant
  `rigidityRows_ofNormals_congr_ends_swap`. Supporting leaves: the `ends₀`-perp producer
  `chainData_freshEdge_slot_perp_ends₀` (§(4.101)); the LEAF-1 selector-recording supplier
  `candidateEnds_records_splitOff_isLink` (`Relabel/Chain.lean`); the full-`G`-link recording
  supplier `fullLink_recording_of_splitOff_recording`; the `hends_i` disjunction-relaxation +
  `splitOff_swap_ab`; the interior-arm seed reads `seedShift_succ_/pred_castSucc`;
  `interior_hρe₀_of_baseWidening` (the `hρe₀` slot). Design §(4.94)/(4.95)/(4.100)–(4.104).
- **The discriminator re-exposure (B′).** `exists_shared_redundancy_and_matched_candidate`
  RETURNS `_hρ₀Gv` (base redundancy span at the honest `ends`) + `hrec'` (full `Gab`-link
  recording incl. `e₀`); `chainData_split_w6b_gates` RETURNS `hrec'`. Exposing-not-proving.
  Design §(4.100)/(4.101).

## Decisions made during this phase

### The route arc (settled; full blow-by-blow in `notes/Phase23-design.md` §(4.84)–(4.106) + git)
- **The honest-engine reshape is the route** — the honest cert `case_III_rank_certification`
  (`Candidate.lean`, already general-`k`) sources `±r` via the eq.-(6.27) ROW-OP of a BOTTOM
  `G−v`-row (`hingeRow v a ρ = hingeRow v b ρ − hingeRow a b ρ`), decoupling the gate from the
  membership. The interior matched candidate routes through that same engine. Design §(4.94).
- **The (D-substitution) detour was refuted** — a full session built a genuine-`ofNormals`
  candidate (no override) which a final dispatch found OFF-BY-ONE at the corner (the gate
  `ρ₀(C(e_a)) ≠ 0` is the exact negation of the `hr` perp `ρ₀(C(e_a)) = 0`, same `ρ₀`/panel:
  the genuine candidate collapsed the free panel + the redundant `±r` onto ONE chain edge).
  §(4.90)/(4.91) settled it; the GO-cascade lesson (a deferred gate carried through multiple
  GO spikes must be traced to its SOURCE) is promoted below. Design §(4.84)–(4.92).
- **The `_aug`-fork DISCARDS — all four deletion commits done.** G1 `Realization.lean`
  (728 lines, 7 wrappers), G2 `Relabel/ForkedArm.lean` (1024 lines, 12 arms/leaves), G3
  `Candidate.lean` (581 lines, the dead cert tail), G4 `Concrete.lean` (917 lines, the
  `rigidityMatrixEdgeAug` matrix backbone + 18 `*aug*` siblings + the orphaned A5d
  corner-index split, via a per-decl closure trace — every code reference to an `aug` name
  lived inside another `aug` decl; the LIVE non-aug edge-path helpers
  `rigidityMatrixEdge_mul_columnOp_*` KEPT). The (D-substitution) S1–S5/spine + the dead
  `_matrix`/`_rowOp`/chain arms all retired with the island. Design §(4.106).

### Promoted to DESIGN / FRICTION / TACTICS-QUIRKS
- **The GO-cascade deferred-hypothesis-unsatisfiable trap** (a deferred gate/side-condition
  carried through MULTIPLE GO spikes, each abstracting it, must be traced to its
  SOURCE/producer) → DESIGN.md *Constructibility recon* + the coordinate-phase command.
- **route-composition satisfiability must be COMPILER-CHECKED, not prose-argued** → FRICTION;
  DESIGN.md *Constructibility recon*.
- **`set`-folding a carried hypothesis's heavy type breaks `exact`/whnf** → TACTICS-QUIRKS §43.
  **`ℤ→ℕ` cast-subtraction** → TACTICS-QUIRKS §47. **`Fin.val ⟨…⟩` omega atomization** →
  TACTICS-QUIRKS §63.
