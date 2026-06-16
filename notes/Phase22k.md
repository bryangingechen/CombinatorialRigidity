# Phase 22k — completing the honest all-`k` Theorem 5.5 (Case III, spine) + Thm 5.6 `d=3` (work log)

**Status:** in progress (opened 2026-06-15 at the 22j close).

22k completes the honest all-`k` Theorem 5.5 the 22i→22j→22k arc set up: the three remaining
22h carries (`h622`, `h65`, `hsplit`) + Theorem 5.6 at `d = 3`. 22i delivered the all-`k`
genuine-hinge motive + the reduction-case producers (L0–L6, `hbase`/`hcontract` discharged);
22j landed the shared span-transport "pinned placement" rank brick
(`le_finrank_span_rigidityRows_of_pinned_placement` = **Brick A**, design §1.68) that **22k's
Case III consumes**. The design basis is the **L7–L10 layer plan + the §1.56 carries table**,
archived in `notes/Phase22i.md` *Hand-off / next phase* + its *Layer plan* / *carries table*
sections; this note transcribes them, with the carries-table "Lean consumption site" column
**re-located into the post-22j-perf 5-file chain** (`GenericityDevice ← Coupling ← CaseI ←
CaseII ← CaseIII ← Theorem55`, under `Molecular/AlgebraicInduction/`).

Structural-edit mode: no new blueprint chapter; the existing `algebraic-induction/*` chapters
restate per slice (the statement-grep gate, `CLAUDE.md` *Structural-edit phases*). The motive
design is canonical in `notes/Phase22-realization-design.md` §1.56 — point at it, don't duplicate.

## Current state

**L7–L9 complete; §1.56(e) cleanup landed; L10 DESIGN-SETTLED (§1.71); L10a is the next build.**
L9 landed: `theorem_55_all_k` + `theorem_55_d3` (zero-carry spine, no new build);
`deficiency_eq_zero_of_simple_rigid_no_simpleContraction` (new lemma, Contraction.lean) discharges
the all-`k` `h65` arm vacuously (k>0 contradicted by carrier construction); blueprint nodes
`thm:theorem-55` + `thm:theorem-55-d3-instance` flipped green.
§1.56(e) cleanup landed: deleted orphaned `theorem_55` + `theorem_55_generic` from PanelHinge.lean;
re-pinned `thm:theorem-55` to `theorem_55_all_k` only; updated all prose references in
GenericityDevice/Coupling/CaseI/CaseII/CaseIII/ForestSurgery. Build + lint + verify.sh green.
**L10 design pass landed (§1.71):** V9 **RESOLVED FREE** — the homogeneous projective move's
enabling brick `exists_extensor_in_two_panels` is ALREADY landed (`PanelLayer.lean:631`, no
transversality needed), and the rank lower bound is the already-green `lem:motions-mono-of-graph-le`
(`finrank_infinitesimalMotions_le_of_graph_le`). Two flags surfaced for the build (NOT design
blockers): (i) the no-deletable-edge ⟺ `IsMinimalKDof` matroid step in the strip brick (P≈3.5,
not a one-liner); (ii) **the load-bearing one** — `theorem_55_all_k` is exposed at `IsMinimalKDof n 0`
(0-dof), but the `def>0` feed needs Thm 5.5 at a `k>0`-dof minimal graph; L10b must first confirm the
all-`k` spine re-exposes at general `k` (likely a near-free wrapper since the producers are named
all-`k`, but a build-time check, not a design-pass certainty). Sub-layer plan: L10a (strip brick) →
L10b (all-`k` re-expose, settle flag (ii) FIRST) → L10c (`def>0` prop11 producer) → L10d (blueprint).
**Next commit: L10a** — the deficiency-preserving spanning-strip brick (see *Hand-off*).

## Layer plan (L7–L10; each layer opens with its own §1.69+ signature pin)

Transcribed from `notes/Phase22i.md` *Layer plan* (the L7–L10 entries) + the §1.56 carries table
+ §1.67. The 22i layers L0–L6 are closed (archived in `notes/Phase22i.md`); 22k is L7–L10.

- [x] **L7** ✓ — the Case-III rewire: `case_III_realization` restated, `h622` *derived* from the
  all-`k` IH (V8) — `h622` carry discharged. **L7a ✓** `exists_rankPolynomial_of_IH_linking` +
  `finrank_span_rigidityRows_ofNormals_eq`. **L7b ✓** `case_III_realization` restate + `h622lb`
  discharge + thin wrapper `case_III_realization_0dof` (Flag F1); discharge then **extracted** as
  the standalone `case_III_nested_rank_lower` so the node pins to a real decl. Blueprint nodes:
  `lem:case-III-nested-rank-lower` (green-and-pinned), `lem:case-III` / `thm:theorem-55-d3-instance` (restated).
- [x] **L8** ✓ — the Lemma-6.5 arm: KT Claim 6.6 graph side + the Π°-placement producer; `h65`
  carry discharged at the 0-dof spine. **L8a ✓** all Claim 6.6 graph-side pieces (Leaf-1 assembly
  `exists_degree_two_removeVertex_of_no_simple_contraction`, `Contraction.lean`). **L8b ✓**
  de-privatize `linearIndependent_normals_of_algebraicIndependent`. **L8c-1 ✓** the `hnewpin` brick
  `exists_independent_pinned_two_edge_span_full` (`Pinning.lean`). **L8c-2 ✓** the producer
  `PanelHingeFramework.case_I_realization_h65` (Theorem55.lean) — geometric blocks extracted as the
  `case_I_h65_*` helpers + the general `normalsJoin_pair_linearIndependent_of_triLI` /
  `triLI_subpairs` (PanelLayer.lean); witness via the combined `Sum.elim` block →
  `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` → the genericity-transfer keystone
  `hasGenericFullRankRealization_of_rigidOn_ofNormals` (no separate rank-poly transfer needed, both
  0-dof). Wiring: dropped `theorem_55_d3`'s 0-dof `h65` carry. Node `lem:case-I-dispatch` flipped
  green (re-pinned to `case_I_realization_h65`). `set_option maxHeartbeats 800000` (4×).
- [x] **L9** ✓ — the zero-carry spine + instance: `theorem_55_all_k`, `theorem_55_d3` restated
  with **zero carries**; new lemma `deficiency_eq_zero_of_simple_rigid_no_simpleContraction`
  (Contraction.lean) discharges the all-`k` `h65` arm; `hsplit` discharged by G0 + M4 wiring.
  Blueprint nodes `thm:theorem-55` + `thm:theorem-55-d3-instance` green.
- [ ] **L10** — Theorem 5.6 at `d = 3`: the deficiency-preserving spanning-strip brick +
  re-add edges (rank only grows) + the `def > 0` `prop:rigidity-matrix-prop11` feed.
  **DESIGN-SETTLED (§1.71): V9 free; sliced L10a–L10d.** The `def = 0` feed already landed in 22h
  (`rankHypothesis_deficiency_of_theorem_55_d3`). Sub-layers (each its own build):
  - [ ] **L10a** — `Graph.exists_isMinimalKDof_spanning_subgraph` (NEW, Deficiency.lean; greedy
    edge-deletion under matroid-rank descent; P≈3.5 — the no-deletable-edge ⟺ `IsMinimalKDof`
    matroid step is the cost). `\uses`-only brick, mints no node.
  - [ ] **L10b** — re-expose the all-`k` spine at general `k` (`theorem_55_all_k` is at
    `IsMinimalKDof n 0`; the `def>0` feed needs a `k>0`-dof minimal graph). **Settle flag (ii)
    FIRST** against `minimal_kdof_reduction_all_k` + the producers' `k`-quantification.
  - [ ] **L10c** — `PanelHingeFramework.rankHypothesis_of_theorem_55_d3` (the `def>0` prop11
    producer; Theorem55.lean tail; P≈3 — strip ∘ L10b ∘ `withGraph` ∘ monotonicity ∘ prop11 +
    one `reaim`-variant micro-brick for the in-two-panels off-edge selector, P≈2).
  - [ ] **L10d** — blueprint: flip `prop:rigidity-matrix-prop11` red→green + mint NEW
    `thm:theorem-55-6-d3` node. PLAN per §1.71(d), not flipped at the design pass.

**Beyond the carries**, the all-`k` restructure adds the structural deliverables of §1.56(c)/(e)
— but those (the new reduction cases, the motive restate of every producer) landed in 22i; 22k's
new structural work is only the Thm-5.6 `d=3` push (L10).

## The carries table (relocated to the post-22j-perf 5-file chain)

The §1.55(b) structural fix for orphaned deferrals. **Lean consumption sites re-located** from
the stale `CaseI.lean:6750/:6817/…` refs of `notes/Phase22i.md` into the new
`Molecular/AlgebraicInduction/` chain (the 22j-perf round split the 10,346-line `CaseI.lean`
monolith into `GenericityDevice ← Coupling ← CaseI ← CaseII ← CaseIII ← Theorem55`; rename-free,
so the decl names are unchanged — only the file:line moved).

| Carry | Blueprint red node | Lean consumption site (post-22j-perf chain) | Discharge sub-plan (§1.56) |
|---|---|---|---|
| `h622` (KT eq. (6.22), the nested-IH rank lower bound at the `k'`-dof `G_v`) | `lem:case-III-nested-rank-lower` (case-iii.tex) | **DISCHARGED (22k L7)**: `case_III_realization` carries the all-`k` IH; the `h622lb` slot is filled by the standalone `case_III_nested_rank_lower`; `theorem_55_d3` calls thin wrapper `case_III_realization_0dof` (Flag F1). `lem:case-III-nested-rank-lower` green-and-pinned. | **L7 complete** (22k): all-`k` IH at `G_v` → `exists_rankPolynomial_of_IH_linking` → footnote-6 non-root → arithmetic; discharge extracted as `case_III_nested_rank_lower`. |
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex; now green, re-pinned to `case_I_realization_h65`) | **DISCHARGED**: 0-dof form **L8c-2**; all-`k` form **L9** via `deficiency_eq_zero_of_simple_rigid_no_simpleContraction` (Contraction.lean) — k>0 + all contractions non-simple → carrier construction forces `def(G)=0`, contradicts k>0; so the arm is vacuous and the k>0 hcontract branch calls `case_I_realization_all_k` or `case_I_realization_nonsimple` only. | **L8 + L9 COMPLETE**: L8 built the Claim-6.6 graph side + Π°-producer; L9's new lemma closes the all-`k` spine vacuously. |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` + `def:rank-hypothesis`; `lem:theorem-55-base-producer` green at the strong pair | **DISCHARGED (22i L3)**: `theorem_55_base_producer` (`Theorem55.lean:436`) supplies `.2`; `hbase` dropped from the `theorem_55_d3` signature (`Theorem55.lean:498` comment) | **L3 complete** (22i): the producer concludes the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` (via `lem:case-III`) | **DISCHARGED (22k L9)**: `theorem_55_all_k`'s `hsplitZero` slot: G0 → `G.Simple`; forgetful M4 ∘ `case_III_realization`; `hsplitPos` slot analogously. Zero new build. | **L9 complete** (22k): wiring via `simple_of_isMinimalKDof_of_noRigid` + `hasPanelRealization_of_generic` |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | **DISCHARGED (22i L5)**: signature hyp of `theorem_55_d3` (`Theorem55.lean:494`) now wired through the `by_cases G.Simple` dispatch `case_I_dispatch` (`Theorem55.lean:1863`) → non-simple `case_I_realization_nonsimple` / simple `case_I_realization_all_k`; the negative-contraction sub-arm stays `h65` → L8 | **L5 complete** (22i) — split by motive; the 6.5 sub-arm stays `h65` → L8 |

## Blockers / open questions

- **L9 COMPLETE; L10 DESIGN-SETTLED (§1.71); L10a is the next build.** V9 RESOLVED FREE
  (the projective-move brick `exists_extensor_in_two_panels` is already landed). Two **build-time**
  flags (NOT design blockers, both flagged honestly per clause (ii)):
  - **Flag (i)** — the strip brick's no-deletable-edge ⟺ `IsMinimalKDof` matroid step (P≈3.5);
    confident in the shape (contrapositive of `subgraph_minimality`'s engine), uncertain whether it
    falls out of the landed `matroidMG`/`isBase` API in one pass or needs its own micro-pin.
  - **Flag (ii), load-bearing** — `theorem_55_all_k` is exposed at `IsMinimalKDof n 0` (0-dof), but
    the `def>0` Thm-5.6 feed needs Thm 5.5 at a `k>0`-dof minimal graph. The all-`k` *induction* is
    inside the proof; whether the *exposed theorem* re-exposes at general `k` as a near-free wrapper
    (likely — producers are named all-`k`) or hides a `k=0` assumption in a producer is an **L10b
    build-time check**, not a design certainty. If a producer assumes `k=0`, the L10 estimate
    changes — the phase-close-estimate risk. **L10b settles this before the L10c build.**

## Hand-off / next phase

**L10 DESIGN PASS LANDED (2026-06-16, §1.71):** V9 RESOLVED FREE; L10 sliced L10a–L10d with exact
signatures; two build-time flags surfaced (strip matroid step P≈3.5; the load-bearing all-`k`
re-expose flag (ii)). No `.lean`/`.tex` edits this commit. Build/lint/verify.sh unaffected
(docs-only).

**Next commit: L10a** — the deficiency-preserving spanning-strip brick (§1.71(b)):

```lean
theorem Graph.exists_isMinimalKDof_spanning_subgraph [DecidableEq β] [Finite α] [Finite β]
    (G : Graph α β) (n : ℕ) (hD : 1 ≤ Graph.bodyBarDim n) (hne : V(G).Nonempty) :
    ∃ G' : Graph α β, G' ≤ G ∧ V(G') = V(G) ∧
      G'.IsMinimalKDof n (G.deficiency n)
```

in `Deficiency.lean` (beside `subgraph_minimality`). Greedy edge-deletion under matroid-rank descent:
`def = D(|V|−1) − rank M(G̃)` (`rank_add_deficiency_eq`) at fixed `V` (`deleteEdges` preserves `V`),
so delete any edge keeping `rank M(G̃)` and recurse on `|E|` (WF, `[Finite β]`); stop when no edge is
deletable keeping rank — which is `IsMinimalKDof` (the **flag (i)** matroid step: convert
no-deletable-edge to base/fiber-meeting via `matroidMG`/`isBase`, P≈3.5). `\uses`-only brick (mints no
node). Self-contained unless the flag (i) step needs adjudication.

After L10a: L10b (settle flag (ii) — the all-`k` re-expose) → L10c (`def>0` prop11 producer
`rankHypothesis_of_theorem_55_d3`) → L10d (blueprint flip). Then 22k closes; then Phase 23
(general `d`, KT Lemma 6.13).

## Decisions made during this phase

(One-line verdicts; full proof-technique detail in §1.56–§1.71 design sections, docstrings, git.)

- **L10 design pass landed (2026-06-16, opus, docs-only; §1.71):** Thm 5.6 at `d=3` sliced
  L10a–L10d with exact signatures. **V9 RESOLVED FREE** — the homogeneous projective move's brick
  `exists_extensor_in_two_panels` (PanelLayer.lean:631, no transversality) is already landed, and the
  rank lower bound is the already-green `lem:motions-mono-of-graph-le`; the `def=0` prose's bundling
  of the projective move into the lower bound was over-careful (`withGraph` monotonicity is
  unconditional). Two build-time flags (clause (ii), flagged not forced): (i) the strip brick's
  no-deletable-edge ⟺ `IsMinimalKDof` matroid step (P≈3.5); (ii) **load-bearing** — `theorem_55_all_k`
  is exposed at `IsMinimalKDof n 0` but the `def>0` feed needs a `k>0`-dof minimal graph, so L10b must
  confirm the all-`k` re-expose before L10c. Verified against landed source per clause (i). Next: L10a.
- **§1.56(e) cleanup landed (2026-06-16, sonnet, clean):** deleted orphaned legacy spines
  `theorem_55` + `theorem_55_generic` (PanelHinge.lean); re-pinned `thm:theorem-55` to
  `theorem_55_all_k` only; updated prose in 6 files. No callers confirmed before deletion.
- **L9 zero-carry spine landed (2026-06-16, sonnet, clean):** `theorem_55_all_k` +
  `theorem_55_d3` placed at END of Theorem55.lean (after all producers). New lemma
  `deficiency_eq_zero_of_simple_rigid_no_simpleContraction` (Contraction.lean) handles the k>0
  all-contractions-non-simple arm via carrier construction steps 1–4a (which don't use k=0) +
  `deficiency_le_deficiency_of_le_vertexSet_eq` — forcing k=0 by contradiction, so the arm is
  vacuous. Blueprint `\cref{def:simple-of-isMinimalKDof-noRigid}` typo fixed to
  `\cref{lem:simple-minimal-noRigid}`. All gates green (build + lint + verify.sh).
- **L8c-2 producer + wiring + node flip landed (2026-06-16, opus, clean):**
  `PanelHingeFramework.case_I_realization_h65` (`Theorem55.lean`). Architecture is the recovered-WIP
  route but with the witness assembled via the **genericity-transfer keystone** (combined `Sum.elim`
  NEW+OLD block → `isInfinitesimallyRigidOn_vertexSet_of_span_le_rigidityRows` →
  `hasGenericFullRankRealization_of_rigidOn_ofNormals`) instead of B2+antisymmetry+manual `⟨Q,…⟩` — this
  is what cleared the `whnf` blowup that the monolithic B2/manual-assembly form hit even at 6M
  heartbeats. **The §38 fix that mattered: decomposition (per the escalation) PLUS routing the final
  assembly through the keystone** — extracting helpers alone was not enough; the manual `∃`-witness
  assembly was the dominant `whnf` cost. Geometric blocks extracted as `case_I_h65_{extensor_pair_LI,
  old_vanish,old_span,ofNormals_supportExtensor}` (private, Theorem55) + general
  `normalsJoin_pair_linearIndependent_of_triLI` / `triLI_subpairs` (PanelLayer). Producer fits at
  `maxHeartbeats 800000` (4×). Wiring dropped `theorem_55_d3`'s 0-dof `h65`; node `lem:case-I-dispatch`
  re-pinned to `case_I_realization_h65` + green. Build + lint + axiom-clean (propext/choice/Quot.sound).
- **L8c-1 `hnewpin` brick landed (2026-06-15, opus, clean):**
  `exists_independent_pinned_two_edge_span_full` in **`Pinning.lean`** (the §1.70(i.1) finrank chain:
  per-edge pinned subfamilies span `r(p(eₐ))`/`r(p(e_b))`, `finrank_sup_add_finrank_inf_eq` +
  `dualAnnihilator_sup_eq` give `finrank(sup) = D`, `exists_fun_fin_finrank_span_eq` extracts the
  `Fin D` LI subfamily, un-pinned rows are rigidity rows by `panelRow_mem_rigidityRows_of_link`).
  **Two §1.70(i.1) pin corrections (both forced by landed source, no math change):** (1) file is
  `Pinning.lean` not `RigidityMatrix.lean` — the brick's `panelRow`/per-edge deps are downstream of
  RigidityMatrix, so RigidityMatrix placement is a circular import; (2) signature gains
  `hlink_a`/`hlink_b` link hyps the pin omitted (the producer supplies them). `hnew_span` `whnf`
  timeout over coerced subtype index → destructure + `_of_link` (FRICTION §38-family *Recurred 22k*).
  Build + lint + axiom-clean.
- **L8a Leaf-1 assembly landed (2026-06-15, sonnet, clean):** `exists_degree_two_removeVertex_of_no_simple_contraction`
  (`Contraction.lean`). Full KT Claim 6.6 graph-side assembly: maximal induced-saturated proper rigid `G'`,
  two distinct `v`-edges via the extraction, carrier `G'' = addEdge-twice`, `G''.removeVertex v = G'`
  (by `le_antisymm`), `def(G'') = 0` (via `removeVertex_deficiency_ge`), maximality forces `V(G'') = V(G)`
  (`ssubset_of_ne_of_subset` + `Set.ncard_lt_ncard`), `G = G''` by the new brick. Then `G.removeVertex v =
  G'` is minimal 0-dof (`subgraph_minimality`) + simple (`hSimple.mono`). Build + lint clean.
  Key fix: `⊊` (U+228A) is not a Lean notation; use `⊂` (U+2282 = `HasSSubset.SSubset`).
- **L8a step-4 new brick landed (2026-06-15, sonnet, clean):** `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof`
  (`Deficiency.lean`, after `isBase_ncard_add_deficiency_eq`). Pattern: by contradiction pick
  `g ∈ E(G) ∖ E(G'')`, get a base `B''` of `M(G̃'')`, show `B''` is `M(G̃)`-independent via
  `matroidMG_restrict_mulTilde`, show `|B''| = rank M(G̃)` (both 0-dof + equal vertex sets), so `B''`
  is a `M(G̃)`-base; minimality forces `B'' ∩ ẽ_g ≠ ∅`, contradicting `B'' ⊆ E(G̃'')`.
  Axiom-clean (propext + Classical.choice + Quot.sound), warning-clean, no long lines.
- **L8a steps 3–5 DESIGN-SETTLE (§1.70(c″), 2026-06-15, opus, docs-only):** the carrier and the
  minimality→equality brick the (c) prose glossed are pinned, verified against landed source. **Carrier:**
  `G'' := (G'.addEdge eₐ v a).addEdge e_b v b` (package `Graph.addEdge`, no bespoke def); the four (c) facts
  hold — `V(G'')=V(G')∪{v}`, `v` degree-exactly-2 (`addEdge_isLink_iff_of_notMem`, `eₐ,e_b ∉ E(G')` since
  `v∉V(G')`), `G''.removeVertex v = G'` (the second place the opener's saturation is load-bearing, via
  `IsInducedSubgraph.vertexSet_induce_eq`), `G'' ≤ G` (`addEdge_le`-twice). **New brick:**
  `eq_of_isMinimalKDof_of_le_of_vertexSet_eq_of_isKDof` — a **near-clone of the landed
  `edgeSet_ncard_le_two_of_isMinimalKDof_of_ncard_two`** (`Deficiency.lean:2253`, same
  rank-equality⟹base⟹fiber-meet contradiction); only generalization is "avoid any `g∈E(G)∖E(G'')`". All
  API present (`isBase_ncard_add_deficiency_eq`, `matroidMG_restrict_mulTilde`, `rank_add_deficiency_eq`,
  `Indep.isBase_of_ncard`, `ext_of_le_le`). Buildable, NOT research-shaped; no motive/definitional change,
  no user decision (clause (ii) clean). Land the brick first (standalone leaf), then the Leaf-1 assembly.
- **L8a opener — the induced-saturated maximal proper rigid subgraph (2026-06-15, opus, clean):**
  `exists_maximal_induced_isProperRigidSubgraph` (`Deficiency.lean:798`, beside
  `exists_maximal_isProperRigidSubgraph` + `deficiency_le_deficiency_of_le_vertexSet_eq`). The §1.70(c′)
  1a+1b move packaged as one brick: from `hrig` (+`hD : 1 ≤ bodyBarDim n`, `[Finite α] [Finite β]`),
  returns a proper rigid `G'` that is vertex-cardinality-maximal **and** induced-saturated (the `hHsat`
  the extraction needs). `G' := G.induce V(G₀)` over the plain-maximal `G₀`; rigidity lifted by
  `deficiency_le_deficiency_of_le_vertexSet_eq` (`G₀ ≤ G'` at equal vertex sets) + `deficiency_nonneg`;
  saturation is `edgeSet_induce`. Zero friction; axiom-clean, build + lint clean. No `DecidableEq β`
  (`IsProperRigidSubgraph` is matroid-free). Scope call: shrank from the full Leaf-1 assembly — steps 3–5
  needed the carrier + minimality-brick design (now settled, §1.70(c″) entry above) before the build.
- **L8a step-2 — the shared-`v` extraction (2026-06-15, opus, clean):**
  `exists_isLink_pair_of_rigidContract_not_simple` + aux `collapseTo_eq_imp_mem_of_ne`
  (`Contraction.lean`, beside `rigidContract_not_simple`). The P≈3 piece of Claim 6.6 step 2: given
  `G.Simple` + `hHsat` (every `G`-edge inside `V(H)` lies in `E(H)` — the (c′) induced-saturation, fed by
  `edgeSet_induce`) + `¬(G/E(H)).Simple` at `r ∈ V(H)`, yields `v ∉ V(H)` with two distinct edges `eₐ, e_b`
  into `V(H)` (ends `a ≠ b`). Loop disjunct vacuous via `hHsat`; parallel disjunct's shared `v` from the
  aux brick (`r ∈ V(H)` ⟹ `collapseTo r V(H)` merges two *distinct* vertices only inside `V(H)`). The
  parallel extraction normalizes each surviving edge to `(outside v, inside a)` after ruling out both-out
  (matched pair + `G`-simplicity → same edge) and both-in (`hHsat`). Axiom-clean, warning-clean. **Lesson
  reuse:** the `rcases eq_and_eq_or_eq_and_eq with ⟨h,_⟩ + rw [← h]` (not `⟨rfl,_⟩`) avoidance of the
  subst-direction trap — already in FRICTION/TACTICS-QUIRKS § 4. FRICTION `map`-simplicity entry updated.
- **L8a-0 — def-antitone brick (2026-06-15, sonnet, clean):** `deficiency_le_deficiency_of_le_vertexSet_eq`
  (`Deficiency.lean:751`): `[Finite α] [Finite β]`, `(hD : 1 ≤ bodyBarDim n)`, `H ≤ H'`, `V(H) = V(H')` →
  `def(H̃') ≤ def(H̃)`. Proof: `numParts` equal (same image `f '' V(H) = f '' V(H')`); `crossingEdges H f ⊆
  crossingEdges H' f` (subgraph monotone via `IsLink.mono`); `ncard_le_ncard` (needs `[Finite β]` for
  `(H'.crossingEdges f).Finite`); `partitionDef` antitone by `D−1 ≥ 0` (needs `hD`). Both `[Finite β]`
  and `hD` absent from hand-off spec — both genuinely needed; compatible with all callers (full Leaf-1
  has `[DecidableEq β] [Finite α] [Finite β]` + `hD : 2 ≤ bodyBarDim n`).
- **L8a loop-case DESIGN-SETTLE (§1.70(c′), 2026-06-15, opus, docs-only):** the loop disjunct the
  `rigidContract_not_simple` build surfaced is resolved — take the maximal `G'` **induced**
  (`G' := G.induce V(G₀)`), making the loop mode (a `G`-edge inside `V(G')` off `E(G')`) vacuous by
  `edgeSet_induce`, so step 2 takes only the parallel mode. Verified against landed source (`collapseTo`,
  `IsProperRigidSubgraph` plain-not-induced, `induce`) + KT pdf p. 30 (KT takes `G'` vertex-maximal and
  silently assumes edge-saturation — induced is that, made explicit; KT-as-written has the same benign
  hole). One new brick `deficiency_le_deficiency_of_le_vertexSet_eq` (def antitone under edge addition at
  fixed vertex set, P≈2, absent from tree). `exists_maximal_isProperRigidSubgraph` reused as-is. NO
  definitional change to `IsRigidSubgraph` (clause (ii) not triggered). Full route §1.70(c′).
- **L8a step-2 bottom leaf — the contraction-non-simplicity unpacking (2026-06-15, opus, clean):**
  `map_not_simple` + `rigidContract_not_simple` (`Contraction.lean`, beside `map_simple`/
  `rigidContract_simple`): the contrapositive of the landed positive criterion — `¬(G/E(H)).Simple`
  ⟹ a loop disjunct (`∃ e x y, surviving-IsLink ∧ collapse x = collapse y`) or a parallel disjunct
  (two distinct surviving edges, collapsed-equal end-pairs). Mechanical `by_contra` + `map_simple`.
  **Scope call:** the full L8a steps 2–5 named in the hand-off did NOT fit cleanly — step 2's
  conclusion turns on a loop-vs-parallel case split, and the loop case is genuinely reachable
  (`IsProperRigidSubgraph` is not induced), so the §1.70(c) "parallel-only" framing is incomplete.
  Shrank to the certain, reusable bottom leaf (the brick that surfaces the case split honestly)
  rather than inventing the loop-case resolution under a degraded-certainty push (now settled in the
  §1.70(c′) design-settle above: induced `G'`). One general lesson promoted to FRICTION (the existing
  `map`-simplicity entry): a `map`-level statement must not bake in a source-graph looplessness
  hypothesis it doesn't take — the loop disjunct can't carry `x ≠ y`; the simple caller recovers it.
- **L8a step 1 — the maximal-subgraph existence (2026-06-15, opus, clean):**
  `exists_maximal_isProperRigidSubgraph` (`Deficiency.lean`, beside `subgraph_minimality`): from any
  proper rigid subgraph, a vertex-cardinality-maximal one exists. Finite-maximum via
  `Nat.findGreatest` over the achieved cardinalities (`α` finite ⟹ bounded by `|V(G)|`). The
  genuinely-new graph content of L8a's first leaf-step; lives in `Deficiency.lean` (introduces
  `IsProperRigidSubgraph`, per the convention) since it has no `rigidContract`/rigidity dependency,
  unlike the full L8a lemma (steps 2–5, downstream). Zero friction; build + lint clean, no blueprint
  pointer touched (`lem:case-I-dispatch` flips at L8c, not here).
- **L8 signature pin (2026-06-15, design §1.70, opus):** `h65` discharges via KT Claim 6.6 (graph
  side, NEW combinatorics) + the Π°-placement producer (geometric side, the L6 Case-II template:
  Brick A + B2, NEW block = the two `v`-edges spanning the full `D`). **Both `h65` shapes reconcile
  to one producer**: Claim 6.6 FORCES `k = 0` (its hypotheses make `G` 0-dof, verified against KT
  pp. 676–677), so `theorem_55_d3:516`'s 0-dof `h65` discharges with its own `k=0` IH (the nested
  `G−v` is also 0-dof — UNLIKE L7's `k'`-dof Case III, so L8 does **not** force the all-`k` spine);
  `case_I_dispatch:1867`'s all-`k` `h65` is L9's to drop. Landed `removeVertex_deficiency_ge`
  (SplitOffDeficiency:405) IS KT Lemma 4.4 at the exact direction Claim 6.6 needs (the §1.54(a3)-era
  "none surfaced" is superseded). One privacy fix: de-privatize CaseIII's `linearIndependent_normals_of_algebraicIndependent`.
  V11 RESOLVED — buildable, no motive/IH change, no user adjudication. Two P≈3 build-time leaves
  flagged (Leaf-1 contraction-non-simplicity unpacking; Leaf-2 Lemma-5.3-at-distinct-endpoints
  `hnewpin`). Slice: L8a graph side → L8b privacy → L8c producer + wiring + node flip.
- **L7b — `case_III_realization` restate + `h622` discharge (2026-06-15, sonnet; warning-bearing →
  coordinator-repaired):** dropped `h622` carry; added `hn : bodyBarDim n = screwDim 2`; upgraded
  `hIH` to all-`k` form. `h622lb` discharged via `splitOff_removeVertex_minimalKDof` + all-`k` IH +
  `exists_rankPolynomial_of_IH_linking` + footnote-6 non-root + arithmetic. Thin wrapper
  `case_III_realization_0dof` keeps `theorem_55_d3` building (Flag F1) until L9. Came in
  warning-bearing (5 `longLine`, false "all clean" attestation); coordinator follow-up `5b6cf9a` reflowed them.
- **L7 extraction + hanging-pin gate (2026-06-15, coordinator):** L7b folded the `h622lb` discharge
  inline, leaving `lem:case-III-nested-rank-lower` `\leanok` with **no `\lean{}` pin** (uncheckable
  green). Extracted the discharge as the standalone `PanelHingeFramework.case_III_nested_rank_lower`
  (`5492158`, `|V(Gab)| ≥ 2` form — drops the 4th-vertex `c`); node now pinned + checkdecls-verified.
  Added a **hanging-pin gate to `blueprint/lint.sh`** (`52c3175`, check 4: statement `\leanok` w/o
  `\lean{}`); audit confirmed it was the only such node (358/358 others clean). Promoted to:
  blueprint/CLAUDE.md *Static checks before commit*.
- **L7a — the V8-a non-relabel rank-poly brick (2026-06-15, opus, clean):** `exists_rankPolynomial_of_IH_linking`
  + `finrank_span_rigidityRows_ofNormals_eq` (`CaseI.lean`). §1.69(c) resolved favorably (relabel
  core specialized cleanly to `f = id`). Zero friction; gates clean, axiom-clean.
- **L7 signature pin (2026-06-15, design §1.69, opus):** `case_III_realization` restates to carry
  the all-`k` IH (drop `h622`); `h622lb` is *derived* — IH at `G_v` (`k' ≤ D−2`) gives rank
  `D(m−1)−k'`, transferred to the given `(ends, q)` by the **landed deficiency-aware rank-polynomial
  idiom** (§1.62, `exists_rankPolynomial_of_le_finrank_linking` + footnote-6 non-root), NOT the
  `def=0`-only seed-rank bridge. V8 RESOLVED to buildable; the one new brick is **V8-a** (L7a,
  `exists_rankPolynomial_of_IH_linking`, the non-relabel/`f=id` mirror of the landed relabel
  rank-poly, P≈3). L7 forces the `hsplitZero` spine slot to be all-`k`-conditioned (`theorem_55_all_k`,
  L9) — `theorem_55_d3`'s `k=0` IH cannot supply the `k'>0` nested instance. No motive change; no user
  adjudication. **Finding:** the blueprint prose of `lem:case-III-nested-rank-lower` cites the seed
  bridge for the rank transfer — wrong for `def>0`; fix to the rank-polynomial extractor at the L7b flip.
- **L8b — de-privatize the triple-LI bridge (2026-06-15, haiku, clean):** promote
  `linearIndependent_normals_of_algebraicIndependent` from `private` in `CaseIII.lean` to public so
  the L8c producer can call it. The lemma is the mathematical bridge for the Π°-placement construction
  (the geometric side of KT Claim 6.6 / Lemma 5.3): given algebraically-independent coefficients and
  three distinct indices, the three rows of the Plücker matrix are linearly independent over ℝ.
  No-op restructuring; gates clean, warning-clean. **Ordering constraint:** L8c needs this lemma
  public before it can build the producer; L8a's graph-side pieces are independent of this change.
- **Phase-open (2026-06-15):** opened 22k from the 22i L7–L10 design basis; transcribed the
  carries table with consumption sites re-located into the post-22j-perf 5-file chain
  (`AlgebraicInduction/{GenericityDevice,Coupling,CaseI,CaseII,CaseIII,Theorem55}.lean`).
  Red-node consistency gate run on the L7–L10 targets (`lem:case-III-nested-rank-lower`,
  `lem:case-III-seed-rank-bridge`, `lem:case-I-dispatch`, `def:genuine-hinge-realization`,
  `thm:theorem-55`, `thm:theorem-55-d3-instance`, `lem:case-III`, `prop:rigidity-matrix-prop11`):
  each statement+proof routes through the same argument the carries table claims; no live-route
  `\uses`/proof-step at a superseded node (`blueprint/lint.sh` green). One finding: blueprint
  prose mis-attributes the `h65`/all-`k` discharge to 22i (now 22k) at three sites — recorded in
  *Blockers*, deferred to an L7/L8 restate commit (not fixed in the phase-open).
