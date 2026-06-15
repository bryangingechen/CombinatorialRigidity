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

**L7 complete; L8a-0 ✓; L8a step-2 extraction ✓; L8a Leaf-1 assembly + L8b–L8c + L9–L10 open.**
Landed L8a sub-steps (all in `Contraction.lean`/`Deficiency.lean`): step 1
`exists_maximal_isProperRigidSubgraph` (`Deficiency.lean:718`), the step-2 *bottom* leaf
`rigidContract_not_simple` (`Contraction.lean:189`), L8a-0 `deficiency_le_deficiency_of_le_vertexSet_eq`
(`Deficiency.lean:751`), and the new **step-2 shared-`v` extraction
`exists_isLink_pair_of_rigidContract_not_simple` (`Contraction.lean`, ✓ axiom-clean + warning-clean,
landed this session)** + its auxiliary `collapseTo_eq_imp_mem_of_ne`. The extraction is the P≈3 sub-step
the design flagged: from `G.Simple` + `hHsat` (every `G`-edge inside `V(H)` lies in `E(H)` — the (c′)
induced-saturation abstraction) + `¬(G/E(H)).Simple` at `r ∈ V(H)`, it produces `v ∉ V(H)` with two
distinct edges `eₐ, e_b` into `V(H)` (ends `a ≠ b`). Loop disjunct vacuous by `hHsat`; parallel disjunct's
shared `v` read off `collapseTo_eq_imp_mem_of_ne`. **Next commit: the Leaf-1 assembly itself** —
`exists_degree_two_removeVertex_of_no_simple_contraction`, now consuming this extraction (step 2 done) +
the induced-saturation opener (1a/1b) + the `G''=G'+v+{e,f}` build (steps 3–5).

## Layer plan (L7–L10; each layer opens with its own §1.69+ signature pin)

Transcribed from `notes/Phase22i.md` *Layer plan* (the L7–L10 entries) + the §1.56 carries table
+ §1.67. The 22i layers L0–L6 are closed (archived in `notes/Phase22i.md`); 22k is L7–L10.

- [x] **L7** ✓ — the Case-III rewire: `case_III_realization` restated, `h622` *derived* from the
  all-`k` IH (V8) — `h622` carry discharged. **L7a ✓** `exists_rankPolynomial_of_IH_linking` +
  `finrank_span_rigidityRows_ofNormals_eq`. **L7b ✓** `case_III_realization` restate + `h622lb`
  discharge + thin wrapper `case_III_realization_0dof` (Flag F1); discharge then **extracted** as
  the standalone `case_III_nested_rank_lower` so the node pins to a real decl. Blueprint nodes:
  `lem:case-III-nested-rank-lower` (green-and-pinned), `lem:case-III` / `thm:theorem-55-d3-instance` (restated).
- [ ] **L8** — the Lemma-6.5 arm: KT Claim 6.6 graph side + the Π°-placement producer — `h65`
  carry discharged. **Signature-pinned in §1.70.** Slice cut: **L8a** the Claim 6.6 graph-side
  lemma `exists_degree_two_removeVertex_of_no_simple_contraction` (NEW combinatorics: maximal
  proper rigid subgraph + Lemma-4.4 +`v` step via the landed `removeVertex_deficiency_ge`).
  **L8a step 1 ✓** — `exists_maximal_isProperRigidSubgraph` (`Deficiency.lean`). **L8a step-2
  bottom leaf ✓** — `rigidContract_not_simple` (`Contraction.lean`): unpacks `¬(G/E(H)).Simple`
  into a loop or parallel disjunct. **L8a-0 ✓** — `deficiency_le_deficiency_of_le_vertexSet_eq`
  (`Deficiency.lean:751`): `H ≤ H'` + `V(H) = V(H')` → `def(H̃') ≤ def(H̃)`. Lifts `G₀`'s rigidity to
  `G.induce V(G₀)`. **L8a step-2 extraction ✓** — `exists_isLink_pair_of_rigidContract_not_simple`
  (`Contraction.lean`) + aux `collapseTo_eq_imp_mem_of_ne`: from `G.Simple` + `hHsat` (induced-saturation)
  + `¬(G/E(H)).Simple`, yields `v ∉ V(H)` + two distinct edges into `V(H)`. **Leaf-1 assembly (next
  commit)**: `exists_degree_two_removeVertex_of_no_simple_contraction`. Then **L8b** de-privatize
  CaseIII's triple-LI bridge → **L8c** the producer `case_I_realization_h65` (the L6 Case-II
  template via Brick A, NEW block = two `v`-edges spanning `D`) + wiring (drop `theorem_55_d3:516`'s
  `h65` carry) + the node flip. Claim 6.6 concludes inside `k = 0`, **no all-`k` generality needed**
  (verified against KT pp. 676–677, §1.70(a)). Target node: `lem:case-I-dispatch` (flip red→green;
  flip `\leanok`; reword the stale "22i" prose to 22k).
- [ ] **L9** — the zero-carry spine + instance: `theorem_55_all_k`, `theorem_55_d3` restated with
  **zero carries** (`hsplit` discharged here by wiring — G0 `simple_of_isMinimalKDof_of_noRigid`
  gives `G.Simple`, then forgetful M4 ∘ the GP Case-III producer; no new build), `theorem_55`
  deleted/re-pinned, blueprint spine restates. Target nodes: `thm:theorem-55` (flip red→green),
  `thm:theorem-55-d3-instance` (drop the carried family).
- [ ] **L10** — Theorem 5.6 at `d = 3`: the deficiency-preserving spanning-strip brick +
  re-add edges (rank only grows) + the `def > 0` `prop:rigidity-matrix-prop11` feed (V9: the
  homogeneous projective move). The `def = 0` feed already landed in 22h (the
  `thm:theorem-55-d3-instance` spanning-stratum corollary, `rankHypothesis_deficiency_of_theorem_55_d3`).
  Target node: `prop:rigidity-matrix-prop11` (currently red — drop the `\uses{thm:theorem-55}`
  dependency on red, flip to green once the spanning-strip + `def>0` feed lands) + a new Thm-5.6
  `d=3` node.

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
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex) | **0-dof** form: signature hyp of `theorem_55_d3` (`Theorem55.lean:516`), negative branch of the inlined dispatch (`:555`); **all-`k`** form: signature hyp of `case_I_dispatch` (`:1867`, consumed `:1893`; NO live caller yet — it is L9's spine dispatch) | **L8 (signature-pinned §1.70)**: KT Claim 6.6 graph side (L8a, NEW combinatorics — **step 1 ✓** `exists_maximal_isProperRigidSubgraph`; **step-2 bottom leaf ✓** `rigidContract_not_simple`; **L8a-0 ✓** `deficiency_le_deficiency_of_le_vertexSet_eq`; **step-2 extraction ✓** `exists_isLink_pair_of_rigidContract_not_simple`; loop-case settled via induced `G'` §1.70(c′); next: Leaf-1 assembly) + the Π°-placement producer `case_I_realization_h65` (L8c, L6 template via Brick A). **Both `h65` shapes → ONE producer**: Claim 6.6 forces `k = 0`, so `theorem_55_d3:516`'s 0-dof `h65` discharges with its own `k=0` IH (L8 drops it); `case_I_dispatch:1867`'s all-`k` `h65` is L9's to drop. L8 does **not** force the all-`k` spine (unlike L7 — the nested `G−v` is 0-dof here) |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` + `def:rank-hypothesis`; `lem:theorem-55-base-producer` green at the strong pair | **DISCHARGED (22i L3)**: `theorem_55_base_producer` (`Theorem55.lean:436`) supplies `.2`; `hbase` dropped from the `theorem_55_d3` signature (`Theorem55.lean:498` comment) | **L3 complete** (22i): the producer concludes the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` (via `lem:case-III`) | signature hyp of `theorem_55_d3` (`Theorem55.lean:489`); the `hsplitGP` wiring threads `case_III_realization` at `Theorem55.lean:541` | **L9 wiring, no new build**: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`; forgetful (M4) ∘ the GP Case-III producer |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | **DISCHARGED (22i L5)**: signature hyp of `theorem_55_d3` (`Theorem55.lean:494`) now wired through the `by_cases G.Simple` dispatch `case_I_dispatch` (`Theorem55.lean:1863`) → non-simple `case_I_realization_nonsimple` / simple `case_I_realization_all_k`; the negative-contraction sub-arm stays `h65` → L8 | **L5 complete** (22i) — split by motive; the 6.5 sub-arm stays `h65` → L8 |

## Blockers / open questions

- **L8a step-2 extraction ✓; L8a Leaf-1 assembly + L8b–L8c + L9–L10 open.** V9 (L10, the `def>0`
  homogeneous projective move for Thm 5.6 `d=3`) still gates to its layer's design pass. No open
  decisions on L8 shape: `h65` shapes reconcile to one producer; privacy resolves to de-privatization
  (§1.70(a)/(e)); loop case resolved to induced `G'` (§1.70(c′), no definitional change). The Leaf-1
  P≈3 step-2 (parallel-disjunct ⟹ shared-`v`) is now landed as a standalone brick — the Leaf-1
  assembly that remains is the induced-saturation opener + the `G''=G'+v+{e,f}` rigidity/maximality
  bookkeeping (all landed bricks, no new P≈3).
- **One L8c build-time leaf flagged (P≈3, buildable, not research-shaped):** Leaf 2 step 4 — the
  Lemma-5.3-at-distinct-endpoints `hnewpin` brick (`eq_of_hingeConstraint_two_parallel:2672` is the
  SAME-pair form, NOT the `va`/`vb` distinct-endpoint shape). Resolve at the L8c build. §1.70(h).
- **`lem:case-I-dispatch` prose staleness** (NOT a gate failure): case-i.tex still says "the
  obligation of sub-phase 22i" — reword to 22k at the L8c node flip (the natural same-commit moment).

## Hand-off / next phase

**Next commit: L8a Leaf-1 assembly** — `exists_degree_two_removeVertex_of_no_simple_contraction`,
consuming the landed L8a sub-steps: step 1 `exists_maximal_isProperRigidSubgraph`, step-2 bottom leaf
`rigidContract_not_simple`, L8a-0 `deficiency_le_deficiency_of_le_vertexSet_eq`, and the **step-2 shared-`v`
extraction `exists_isLink_pair_of_rigidContract_not_simple`** (the P≈3 piece — now landed) + `edgeSet_induce`.
Opener (§1.70(c′)): get the vertex-cardinality-maximal `G₀` from `exists_maximal_isProperRigidSubgraph`,
saturate to `G' := G.induce V(G₀)` (rigid by L8a-0 + `deficiency_nonneg`, proper since `V(G') = V(G₀)`).
Step 2 is now a single call: from `hnoSimpleContr` at `G'` and any `r ∈ V(G')`, feed
`exists_isLink_pair_of_rigidContract_not_simple` (its `hHsat` discharged by `edgeSet_induce`: every
`G`-edge inside `V(G')` lies in `E(G')`) to get `v ∉ V(G')` + two distinct edges `eₐ, e_b` into `V(G')`.
Steps 3–5: `G''=G'+v+{e,f}` rigid by `removeVertex_deficiency_ge` (KT Lemma 4.4, exact
direction) → maximality forces `G = G''`, `G−v = G'` minimal 0-dof simple. Target signature (§1.70(c),
lives in `ReducibleVertex.lean` or `Contraction.lean` — needs `rigidContract` + `removeVertex_deficiency_ge`,
both downstream of `Deficiency.lean`):
```lean
theorem Graph.exists_degree_two_removeVertex_of_no_simple_contraction
    [DecidableEq β] [Finite α] [Finite β] {G : Graph α β} {n : ℕ}
    (hD : 2 ≤ Graph.bodyBarDim n) (hV3 : 3 ≤ V(G).ncard)
    (hG : G.IsMinimalKDof n 0) (hSimple : G.Simple)
    (hrig : ∃ H : Graph α β, H.IsProperRigidSubgraph G n)
    (hnoSimpleContr : ∀ H : Graph α β, H.IsProperRigidSubgraph G n → ∀ r ∈ V(H),
      ¬ (G.rigidContract H r).Simple) :
    ∃ (v a b : α) (eₐ e_b : β), a ≠ v ∧ b ≠ v ∧ a ≠ b ∧ eₐ ≠ e_b ∧
      G.IsLink eₐ v a ∧ G.IsLink e_b v b ∧ (∀ e x, G.IsLink e v x → e = eₐ ∨ e = e_b) ∧
      (G.removeVertex v).IsMinimalKDof n 0 ∧ (G.removeVertex v).Simple
```
After L8a: **L8b** de-privatize CaseIII's triple-LI bridge → **L8c** the producer
`case_I_realization_h65` + wiring (drop `theorem_55_d3:516`'s `h65`) + flip `lem:case-I-dispatch`
green. After L8 close: **L9** (zero-carry spine `theorem_55_all_k`, wire `case_III_realization` +
drop `case_I_dispatch`'s all-`k` `h65`), **L10** (Thm 5.6 `d=3`). After L7–L10 close, 22k delivers
the KT-strength Thm 5.5 → 5.6 at `d = 3`; then Phase 23 (general `d`).

The step-2 extraction is a clean stopping point on its own (a reusable `Contraction.lean` brick;
`theorem_55_d3` still carries `h65`); the Leaf-1 assembly, then L8c, are separate sittings.

## Decisions made during this phase

(One-line verdicts; full proof-technique detail in §1.56–§1.70 design sections, docstrings, git.)

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
