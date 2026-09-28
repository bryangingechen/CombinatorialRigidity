# Phase 40k — PENCIL-X0 / CONTRACT-A: contraction at an additive core (work log)

**Status:** in progress (opened design-first 2026-09-28). STEPS' seventh and last group
(`notes/Phase40-design.md` §3 STEPS, the CONTRACT-A entry). It lands the contraction step at a rigid
core whose planar deficiency adds: at an induced core `H = G[W]`, `W ⊊ V(G)`, `|W| ≥ 2`,
`def₃(H) = 0`, with no outside body adjacent to two core bodies, in a 2EC `G` satisfying (H), if
`def₂(H) + def₂(G/H) ≤ def₂(G)` and `X₀` attains at `H` and at `G/H = G.rigidContract (G.induce W) r`,
then `X₀(G)` attains ((MC-71)). It also splits `Contract.lean`. No new mathematics. Five nodes, all
red, and a remark; three builds B1–B3, possibly two. **Next: B1, the `Contract.lean` split** — see
*Hand-off*.

## Current state

**Opened.** Five nodes in `main-component.tex`'s new §`sec:main-component-contract-additive`
(between `sec:main-component-splitoff` and `sec:main-component-statements`; the chapter preamble
names it), with statements from the spike's exact statements (the 40h–40j precedent) and workbook
labels from `ledger.py --brief`:
- `lem:pencil-rank-collineation` — (MC-3)'s collineation mechanism (`lem:pencil-rank-scale-shift`'s)
  for any `g ∈ GL(K⁴)`;
- `lem:pencil-contract-kernel-bound` — (1) the core rows of (MC-69)(a)'s proof, at every `t`; (2)
  (MC-69)(a)'s bound as an inequality, `dim ker M(0) + 3 ≤ dim ρ(ker M(0)) + dim L_{G/H}(q)`;
- `lem:pencil-contract-magnified-rank` — the core at the magnified picture `δ = q|_W` of (MC-37),
  by a collineation;
- `lem:pencil-contract-standing-rigid` — (MC-39)'s side claim at `H`, at any `n ≥ 1`;
- `thm:pencil-x0-contract-additive` — (MC-71), with (MC-69)(b) (the chain and its by-product
  `S ⊆ T`), (MC-35), (MC-36) and (MC-37) steps 2–3; the unpinned remark after it records the
  proof-level departure (call 1), CONTRACT-R as the `def₂(H) = 0` case, (MC-67)(b) and (MC-87).

One statement edit (call 9, blueprint only): `lem:pencil-contract-limit` (2) is lifted out of the
flat setting, to match `Graph.exists_mem_ker_contractLiftingMatrix_zero` (`Contract.lean:727`),
which has no flat hypothesis. No Lean has landed. The red nodes carry no `\lean{…}` yet (40h's open
convention): each build adds its pins with `\leanok` (*Lemma checklist*). No other node changes.

**The spikes** (gitignored `scratch/40k/`, local to this checkout; builder pointers, not evidence),
re-run at this open with **`lake lean`** at `77f80d09`, identical to the coordinator's re-run:
- `S40kContractA.lean` (1 067 lines, the whole build and two variants not built): exit 0, no
  errors, no `sorry`; one warning, a long line inside a `#print axioms` command. Its ten
  `#print axioms` lines are each `[propext, Classical.choice, Quot.sound]`.
- `S40kInst.lean` (the instance): exit 0, no `sorry`, 34 style-linter warnings; one axioms line
  (`theta134_structural`), standard.
- `measure.py` (exact brute-force deficiencies over all set partitions, the formula of
  `Graph.partitionDef`/`Graph.deficiency`, `Molecular/Deficiency.lean:262–274`): output as the
  recon's.
- **Satisfiability** (not landed). θ(1,3,4) on `Fin 7`: the core `C₄` on `0–1–2–3`
  (`W = {0,1,2,3}`, `r = 0`) and the path `0–4–5–6–1`, so `G/H = C₄`. Kernel-checked in the instance
  spike: (H), 2EC (by a Hamiltonian cycle), `r ∈ W`, `W ⊊ V(G)`, `2 ≤ |W|`, `hatt`,
  `def₃(G[W]) = 0` (via `isKDof_zero_of_cycle`) and `1 ≤ def₂(G[W])`, so CONTRACT-R does not cover
  it. Measured (`measure.py`): `def₂ = 2 / 1 / 1` for `G / H / G/H`, so `hadd` reads `1 + 1 ≤ 2`;
  `def₃ = 0 / 0 / 0`. Also measured: θ(1,3,3) meets the measured hypotheses (`1 + 0 ≤ 1`), and the
  negative control, `C₄` with an outside triangle attached at three core bodies, fails `hadd`
  (`1 + 0 > 0`), so the hypothesis is not vacuous. `hH` and `hc` at θ(1,3,4) (both `C₄`) would come from the landed
  `of_cycle`; **not checked**.
- **Faithfulness** (against (MC-71)): `of_additiveContract` is (MC-71) with its count in the `≤`
  form (call 2); the reverse inequality, (MC-67)(b), is neither landed nor needed. `hdef3` is
  (MC-71)'s "proper rigid set" (call 3), and `hatt` its "`G/H` simple" in CONTRACT-R's form (call 4).
  (H) and 2EC are asked at `G`, attainment at `H` and `G/H` only; (H) at `H` is
  `lem:pencil-contract-standing-rigid` at `n = 3`, and at `G/H` the landed CONTRACT-R lemmas.

## Architectural choices made up front

- **The route** (the recon's verdict; the design doc's §3 STEPS, CONTRACT-A entry). One picture `q`
  generic for `X₀` and Jackson–Jordán at `H` and `G/H`, and main for `G`. A lower bound
  `dim ker M(0) ≥ 3 + def₂(G)` from the Cramer section's semicontinuity conjunct at the zero vector,
  which CONTRACT-R discards; the upper bound (MC-69)(a) through the core heights. With
  Jackson–Jordán at `H`, `G/H` and `hadd` they force `ρ(ker M(0)) = L_H(q)` ((MC-69)(b)'s `S ⊆ T`).
  Two open conditions in `ker M(0)` — `X₀(H)`'s height polynomial on `ρ`, and the degenerate-rank
  polynomial at `t = 0`, witnessed by the flat-core extension K4 — meet by
  `exists_mem_eval_ne_zero₂`; Cramer's section through the common point does not jump. The core's
  rank is `H`'s at the fixed picture `q`, by the collineation. Then the degenerate rank, the block
  coupling and `x0Attains_of_exists`, as in CONTRACT-R.
- **Carried over from CONTRACT-R unchanged:** the curve, `M(t)`, K1, K2, K4, the degenerate rank,
  the coupling, the curve polynomials and the `G/H` standing facts; the Cramer section is used
  twice. Not used: the flat K3, the core plane, the flat core rank, and Jackson–Jordán at `H` along
  the curve (only at `q`).
- **The proof-level departure from (MC-71)'s proof text** (call 1; in the theorem's blueprint proof
  and the remark, not a workbook claim): in place of (MC-68)(d)'s core-freeness and (MC-38)'s
  dominance, `S ⊆ T` from the two bounds, two open conditions in `ker M(0)` (the design doc's
  `HoldsGenerally` note) and a collineation (the mechanism of `lem:pencil-rank-scale-shift`).
- **The coordinator's calls** (2026-09-28). The PI's session-start configuration was **"follow
  precedent"** (the 40i/40j configuration): where a 40e–40j precedent answers a recon question, the
  coordinator applies it and records it as its call. These are not PI decisions, so they are not in
  `notes/pencil/adjudications.md`. The numbers are the recon's.
  1. **No new mathematics: 40k opens directly**, with no workbook commit and no second reading (the
     40f/40g/40i/40j precedent); the departure is recorded in the blueprint (the 40j precedent).
  2. **`hadd` in the `≤` form**, as spiked. (MC-89)'s step 5 takes additivity at a core from
     (MC-87), whose proof of (i) bounds every partition value of `G/H` by the singleton value
     `s′(V) − s′(W) = def₂(G) − def₂(H)`: exactly the `≤` form (coordinator-verified).
  3. **`hdef3` kept** (faithful to (MC-71)). The compiled `of_additiveContract_weak` (no core
     rigidity: `def₃`-additivity in its place, no `hW2`) is recorded, not adopted.
  4. **`hatt` kept**, for parity with CONTRACT-R. The PI-decision-2 readability todo stays open and
     unchanged; the recon's observation that COVERAGE's producer at the (MC-80) cores is itself
     `hatt`-shaped is added to it, for the PI (design doc §3 STEPS).
  5. **Option A, the design doc's line.** The general pieces move to a new
     `MainComponent/ContractCurve.lean` (importing `Cut.lean`); the flat-core pieces and CONTRACT-R's
     assembly stay in `Contract.lean`, CONTRACT-R untouched; the step goes in a new
     `ContractAdditive.lean`. Alternatives the PI may prefer: option B, the compiled
     `of_rigidContract_viaAdditive` (CONTRACT-R re-proved in about 20 lines through CONTRACT-A and
     FLAT, about 140 lines of duplicated setup removed, but three pinned flat nodes left without a
     consumer); and the cheaper-diff sub-option of A (the general part stays in `Contract.lean`, the
     flat part moves out).
  6. **G1, the collineation lemma, in `Configuration.lean`**, beside
     `pointJoinFramework_comp_eq_mapSupport`: a reading of PI decision 5's convention (the 40j
     placement precedent) that the PI may reverse; the alternative is `ContractCurve.lean`.
  7. **Pins:** CONTRACT-A consumes none of the D5 debt (the recon's grep of the spike: no
     `jointMotions`, `weldedRank`, `relScrews`, `pairDelta`, `weldPair`, `deficiencySep` or
     `deficiencyMerged`); it passes to COVERAGE.
  8. **(MC-67), (MC-68) and (MC-70) re-homed to the design doc's §2 *Not needed*.** (MC-89)'s step 5
     takes additivity from (MC-87), whose proof uses (MC-76) and (S) and cites no (MC-67)
     (coordinator-verified). Caveat: the second reader's independent cross-check (MC-119)/(MC-120)
     (Step MC16 §7) uses (MC-67)(a)–(c), so (MC-67) returns if COVERAGE takes that route. COVERAGE's
     MC15 row is corrected, keeping (MC-62)/(MC-63), which have other consumers; a COVERAGE tracked
     item is added for the `hadd` supplier.
  9. **`lem:pencil-contract-limit` (2)'s statement edited out of the flat setting** (blueprint only).
  10. **The subsection before `sec:main-component-statements`** (the 40g–40j precedent), named in
      the chapter preamble.
  11. **The name `Graph.X0Attains.of_additiveContract`**, as spiked.
  12. **The recon's four optional dedupes** are tracked cleanup-round items in the design doc's
      CONTRACT-A entry, not build scope.
- **Blueprint placement.** The general lemmas before the step; the collineation lemma first, as the
  only one not about the contraction.

## Lemma checklist

Planned names from the spike; pins in **bold**, the other names helpers, unpinned. The slicing is
the recon's: B1 and B2 may merge.

- [ ] **B1, the split** (call 5): a pure move plus an in-place generalization; no blueprint change,
  since every moved name is kept.
  - New `Molecule/Pencil/MainComponent/ContractCurve.lean`, importing `Cut.lean`: the sections *The
    rescaled lifting system* through *The bodies and closed neighbourhoods of the contraction*
    (`Contract.lean` lines 97–430), `Graph.closedNbhd_induce_subset`, `contractLimitMap` and
    `contractLimitMap_apply`, the two helpers below, `Graph.exists_mem_ker_contractLiftingMatrix_zero`
    (K4), *The surviving rows near the collapsed placement*, the five `G/H` standing lemmas
    (`rigidContract_induce_simple`, `three_le_ncard_closedNbhd_rigidContract`,
    `connected_rigidContract_induce`, `twoEdgeConnected_rigidContract_induce`,
    `isX0Graph_rigidContract_induce`) and *The curve as polynomials in `t`*.
  - `Graph.contractLimitMap_mem_liftingSpace` and `Graph.eq_zero_of_contractLimitMap_eq_zero`,
    generalized in place to the spike's `…_of_plane` statements: the plane hypothesis
    `hg : ∃ g, (∀ w ∈ W, x (Sum.inl w) = g ⬝ᵥ pencilPicturePoint q w) ∧ ∀ c ∈ W, (fun i => x
    (Sum.inr (c, i))) = g` in place of `hqH`/`hLH`. Both are unpinned, and the flat K3 is their only
    call site; it now takes `hg` from `Graph.exists_core_plane`.
  - `Contract.lean`, importing `ContractCurve.lean`, keeps `Graph.exists_core_plane`,
    `Graph.finrank_ker_contractLiftingMatrix_zero_le`,
    `Graph.finrank_span_rigidityRows_induce_contractHeight`,
    `Graph.isX0Graph_induce_of_deficiency_two_eq_zero` and `Graph.X0Attains.of_rigidContract`.
- [ ] **B2, the general pieces and the four lemma nodes:**
  - `Configuration.lean` (call 6):
    **`CombinatorialRigidity.Molecular.PanelHingeFramework.finrank_span_rigidityRows_ofNormals_linearEquiv`**
    → `lem:pencil-rank-collineation` (pinned fully qualified, the 40j B1 precedent);
  - `ContractCurve.lean`: **`Graph.liftingRestrict_mem_liftingSpace_induce_of_contract`** and
    **`Graph.finrank_ker_contractLiftingMatrix_zero_add_three_le`**, with `contractCoreRestrict` and
    `contractCoreRestrict_apply` → `lem:pencil-contract-kernel-bound`;
    **`Graph.finrank_span_rigidityRows_induce_contractHeight_eq`** →
    `lem:pencil-contract-magnified-rank`; **`Graph.isX0Graph_induce_of_deficiency_eq_zero`** →
    `lem:pencil-contract-standing-rigid`.
- [ ] **B3, the step**, new `MainComponent/ContractAdditive.lean`, importing `ContractCurve.lean`
  only, added to the root import, with a module docstring listing its statements (the `Cut.lean`
  pattern): **`Graph.X0Attains.of_additiveContract`** → `thm:pencil-x0-contract-additive`.
- [ ] **The close** (docs and blueprint only): the end-to-end re-read of the new subsection, with two
  candidates found at this open — `lem:pencil-contract-standing`'s `G/H` clauses do not need
  `def₂(H) = 0` (the theorem's proof says so), and the remark after `thm:pencil-x0-contract-rigid`
  may point at the new step; the exposition ledger (candidate: the two bounds on `ker M(0)` that
  force its core heights onto `L_H(q)`, and the core's rank by a collineation at the fixed picture);
  the headline axioms; the design doc's §3 STEPS (STEPS done), ROADMAP and `MolecularConjecture.md`;
  the public surfaces unchanged (the PI's standing call, recorded at 40f's close: they update when
  Phase 40 closes).

## Blockers / open questions

- None blocking B1.
- **Builder notes.**
  - B1: split the module docstring, each file listing its own statements (the `Cut.lean` pattern);
    add `ContractCurve.lean` to the root import. One live pointer names a moved declaration's file:
    `TACTICS-QUIRKS.md` §38's worked case (`exists_rankPolynomial_rigidContract_induce_proj`);
    repoint it. FRICTION's `[resolved]` entries record where their friction bit, and stay.
  - B2: the collineation lemma in `Configuration.lean` rebuilds its downstream files (cost unmeasured). The spike's
    docstrings are minimal; write real ones.
  - B3: the spike imports all of `Contract.lean`, but its step uses none of the flat pieces (this
    open's grep), so `ContractAdditive.lean` imports `ContractCurve.lean` only. The variants
    `…_viaAdditive` and `…_weak` are not the build (calls 3 and 5).
  - Every new top-level name and module greps to no prior definition (this open's check,
    TACTICS-QUIRKS §65).

## Hand-off / next phase

**Next: B1, the `Contract.lean` split (fresh builder).** Source: `Contract.lean` itself, with the
spike's `…_of_plane` statements (`scratch/40k/S40kContractA.lean`, section G3; gitignored, local to
this checkout; a builder pointer, not evidence). Target: the move and the in-place generalization of
the checklist's B1 item, green, with no blueprint change. Chores:
- **Placement** as the checklist (call 5). About 1 040 lines move to `ContractCurve.lean`;
  `Contract.lean` drops from 1 496 to about 430. No fragile-zone file is touched.
- **No repins.** Every name is kept, so `checkdecls` stays green and no node changes.
- Gates: `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`,
  `notes/check-phase-note.py`.

**Then B2** (the general pieces and the four lemma nodes; `ContractCurve.lean` grows to about
1 270, `Configuration.lean` 691 → about 715), **then B3** (`ContractAdditive.lean`, about 360 lines,
and the theorem), **then the close**.

**Cleanup-round items** (call 12; the design doc's CONTRACT-A entry), in the recon's names (G1 the
collineation lemma, G4 the kernel bound, G5 the rigid-core standing lemma): the flat K3
(`finrank_ker_contractLiftingMatrix_zero_le`) as a corollary of G4; the `def₂` standing lemma as a
corollary of G5; `exists_core_plane`'s middle step via the new core-heights lemma;
`Graph.finrank_span_rigidityRows_ofNormals_smul_add_affineLifts` via G1.

## Decisions made during this phase

- **2026-09-28 — opened design-first** from CONTRACT-A's design recon (opus, read-only,
  compiler-checked). This commit re-ran the two spikes and `measure.py` at `77f80d09` and got the
  coordinator's counts. The coordinator's calls are under *Architectural choices*.
