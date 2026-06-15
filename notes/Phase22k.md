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

**L7 complete; L8 design-pinned (§1.70). Next: L8a — the Claim 6.6 graph side.** The `h622`
carry is discharged (L7): `case_III_realization` carries the all-`k` IH and fills the `h622lb`
slot via the standalone `case_III_nested_rank_lower`; `theorem_55_d3` calls the thin wrapper
`case_III_realization_0dof` (Flag F1) until L9 swaps the spine. The **L8 signature pin is done**
(§1.70, this commit): `h65` discharges via KT Claim 6.6 (graph side, NEW combinatorics) + the
Π°-placement producer (geometric side, the L6 Case-II template widened). **Both `h65` shapes
reconcile to one producer** — Claim 6.6 forces `k = 0`, so `theorem_55_d3:516`'s 0-dof `h65` is
dischargeable with its own `k=0` IH (no all-`k` spine forced, unlike L7); `case_I_dispatch:1867`'s
all-`k` `h65` is L9's to drop. `lake build` + `lake lint` + `blueprint/verify.sh` clean as of
L7 close (no Lean/TeX edits this commit). **L8–L10 open.**

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
  proper rigid subgraph + Lemma-4.4 +`v` step via the landed `removeVertex_deficiency_ge`) →
  **L8b** de-privatize CaseIII's triple-LI bridge → **L8c** the producer `case_I_realization_h65`
  (the L6 Case-II template via Brick A, NEW block = two `v`-edges spanning `D`) + wiring (drop
  `theorem_55_d3:516`'s `h65` carry) + the node flip. Claim 6.6 concludes inside `k = 0`, **no
  all-`k` generality needed** (verified against KT pp. 676–677, §1.70(a)). Target node:
  `lem:case-I-dispatch` (flip red→green; flip `\leanok`; reword the stale "22i" prose to 22k).
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
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex) | **0-dof** form: signature hyp of `theorem_55_d3` (`Theorem55.lean:516`), negative branch of the inlined dispatch (`:555`); **all-`k`** form: signature hyp of `case_I_dispatch` (`:1867`, consumed `:1893`; NO live caller yet — it is L9's spine dispatch) | **L8 (signature-pinned §1.70)**: KT Claim 6.6 graph side (L8a, NEW combinatorics) + the Π°-placement producer `case_I_realization_h65` (L8c, L6 template via Brick A). **Both `h65` shapes → ONE producer**: Claim 6.6 forces `k = 0`, so `theorem_55_d3:516`'s 0-dof `h65` discharges with its own `k=0` IH (L8 drops it); `case_I_dispatch:1867`'s all-`k` `h65` is L9's to drop. L8 does **not** force the all-`k` spine (unlike L7 — the nested `G−v` is 0-dof here) |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` + `def:rank-hypothesis`; `lem:theorem-55-base-producer` green at the strong pair | **DISCHARGED (22i L3)**: `theorem_55_base_producer` (`Theorem55.lean:436`) supplies `.2`; `hbase` dropped from the `theorem_55_d3` signature (`Theorem55.lean:498` comment) | **L3 complete** (22i): the producer concludes the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` (via `lem:case-III`) | signature hyp of `theorem_55_d3` (`Theorem55.lean:489`); the `hsplitGP` wiring threads `case_III_realization` at `Theorem55.lean:541` | **L9 wiring, no new build**: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`; forgetful (M4) ∘ the GP Case-III producer |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | **DISCHARGED (22i L5)**: signature hyp of `theorem_55_d3` (`Theorem55.lean:494`) now wired through the `by_cases G.Simple` dispatch `case_I_dispatch` (`Theorem55.lean:1863`) → non-simple `case_I_realization_nonsimple` / simple `case_I_realization_all_k`; the negative-contraction sub-arm stays `h65` → L8 | **L5 complete** (22i) — split by motive; the 6.5 sub-arm stays `h65` → L8 |

## Blockers / open questions

- **L7 done; L8 pinned (§1.70); L9–L10 open.** V9 (L10, the `def>0` homogeneous projective move
  for Thm 5.6 `d=3`) still gates to its layer's design pass (carried over from `notes/Phase22i.md`
  *Blockers*). No open decision on L8 — both `h65` shapes reconcile to one producer; the privacy
  issue resolves to a clean de-privatization (§1.70(a)/(e)).
- **Two L8 build-time leaves flagged (P≈3 each, buildable, not research-shaped):** (i) Leaf 1
  step 2 — `rigidContract`-non-simplicity ⟹ shared-`v` extraction; (ii) Leaf 2 step 4 — the
  Lemma-5.3-at-distinct-endpoints `hnewpin` brick (`eq_of_hingeConstraint_two_parallel:2672` is the
  SAME-pair form, NOT the `va`/`vb` distinct-endpoint shape). Resolve at the L8a/L8c builds. §1.70(h).
- **`lem:case-I-dispatch` prose staleness** (NOT a gate failure): case-i.tex still says "the
  obligation of sub-phase 22i" — reword to 22k at the L8c node flip (the natural same-commit moment).

## Hand-off / next phase

**Next commit: L8a — the Claim 6.6 graph-side lemma** (NEW combinatorics, the first L8 leaf, pure
graph theory, no dependency on the geometric side). Signature (§1.70(c), lives in
`ReducibleVertex.lean` or `Contraction.lean`):
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
Proof = KT Claim 6.6 (pdf p. 30): maximal proper rigid subgraph `G'` (NEW existence, `α` finite) →
non-simple contraction ⟹ `v ∉ V'` with two edges into `V'` → `G''=G'+v+{e,f}` rigid by Lemma 4.4
(the landed `removeVertex_deficiency_ge`, exact direction) → maximality forces `G = G''`, `G−v = G'`
minimal 0-dof simple. After L8a: **L8b** de-privatize CaseIII's triple-LI bridge → **L8c** the
producer `case_I_realization_h65` + wiring (drop `theorem_55_d3:516`'s `h65`) + flip
`lem:case-I-dispatch` green. After L8 close: **L9** (zero-carry spine `theorem_55_all_k`, wire
`case_III_realization` + drop `case_I_dispatch`'s all-`k` `h65`), **L10** (Thm 5.6 `d=3`). After
L7–L10 close, 22k delivers the KT-strength Thm 5.5 → 5.6 at `d = 3`; then Phase 23 (general `d`).

If L8a won't fit a sitting cleanly, the maximal-subgraph existence (step 1) is itself a clean
standalone first commit. L8a is a clean stopping point on its own (`theorem_55_d3` still carries
`h65`); L8c is then a separate sitting.

## Decisions made during this phase

(One-line verdicts; full proof-technique detail in §1.56–§1.70 design sections, docstrings, git.)

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
