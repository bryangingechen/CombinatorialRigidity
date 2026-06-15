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

**Next concrete commit: L7b — restate `PanelHingeFramework.case_III_realization` (drop the `h622`
carry, carry the all-`k` IH; §1.69(a)) and discharge `h622lb` via the now-landed L7a brick
(§1.69(b)), flipping `lem:case-III-nested-rank-lower` green.** The new `h622lb` lambda is L7a's
`N`-bound → footnote-6 non-root (alg-indep `q` from `HasGenericFullRankRealization`'s conjunct) →
`≥ D(m−1) − (D−2)` via the `k' ≤ D−2` arithmetic from `splitOff_removeVertex_minimalKDof`; everything
downstream (`case_III_candidate_dispatch`, the Claim-6.11/6.12 machinery) is the **unchanged landed
body** that already consumes `h622lb`. P≈2 (assembly only). Residual leaf b1 (`Gv = G − v` simple
from `hSimple` via subgraph — *simpler* than L6's `splitOff` simplicity). Per §1.69(a) Flag F1, if
the L7b commit must keep `theorem_55_d3` building, thread the old `h622`-carrying shape via a thin
wrapper until L9 swaps the spine. **Statement-grep gate** before commit: the `\lean{…case_III_realization}`
pin survives the carry-drop, so grep `blueprint/src` — `lem:case-III` / `thm:theorem-55-d3-instance`
state the `h622` carry, restate in the same commit; correct `lem:case-III-nested-rank-lower`'s proof
prose seed-transfer citation (seed bridge → rank-polynomial extractor) at the flip.

**Done (L7a, this commit):** the V8-a brick landed — `PanelHingeFramework.exists_rankPolynomial_of_IH_linking`
(`CaseI.lean`, beside the relabel sibling `exists_rankPolynomial_of_IH_relabel_linking`) + its
non-relabel shared core `finrank_span_rigidityRows_ofNormals_eq`. As §1.69(c) predicted (P≈3, the
favorable-resolution flag), the relabel core specialized **cleanly** to `f = id`: the dedicated
non-relabel core (selector-swap transport `Q.ends ↔ ends` via `recordsLinks_agree_swap` +
`infinitesimalMotions_ofNormals_eq_of_ends_swap` → `span_rigidityRows_eq_of_infinitesimalMotions_eq`,
exactly the relabel pattern minus the collapse map) compiled first try; no fresh selector-agreement
argument needed, no `map_id` reduction needed. The V8-a residual risk is **discharged**.
**(L7 signature pin / phase-open, prior commits):** design §1.69 pins; the four open-a-phase items +
red-node consistency gate. **L8–L10 open.**

## Layer plan (L7–L10; each layer opens with its own §1.69+ signature pin)

Transcribed from `notes/Phase22i.md` *Layer plan* (the L7–L10 entries) + the §1.56 carries table
+ §1.67. The 22i layers L0–L6 are closed (archived in `notes/Phase22i.md`); 22k is L7–L10.

- [ ] **L7** — the Case-III rewire: `case_III_realization` restated, `h622` *derived* from the
  all-`k` IH (V8) — `h622` carry discharged. **Signature pin DONE (design §1.69).** Two build
  slices: **L7a ✓** `exists_rankPolynomial_of_IH_linking` (the non-relabel rank-poly brick + its
  shared core `finrank_span_rigidityRows_ofNormals_eq`, V8-a, landed clean, no node) → **L7b**
  `case_III_realization` restate + `h622lb` discharge (P≈2, the unchanged candidate-dispatch body —
  the next commit). Target nodes: `lem:case-III-nested-rank-lower` (flip red→green at L7b; correct
  its seed-transfer citation to the rank-polynomial extractor), `lem:case-III` /
  `thm:theorem-55-d3-instance` (drop the carried `h622`).
- [ ] **L8** — the Lemma-6.5 arm: KT Claim 6.6 graph side (~2–3 commits) + the Π°-placement
  producer (own signature pin first) — `h65` carry discharged. §1.54(a3) steps 1–2; the dispatch
  itself landed in 22h/L5b-iii. Claim 6.6 concludes inside the `k = 0` stratum, **no all-`k`
  generality needed**. Target node: `lem:case-I-dispatch` (flip red→green; flip `\leanok`).
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
| `h622` (KT eq. (6.22), the nested-IH rank lower bound at the `k'`-dof `G_v`) | `lem:case-III-nested-rank-lower` (case-iii.tex) | signature hyp of `theorem_55_d3` (`Theorem55.lean:502`), threaded into `PanelHingeFramework.case_III_realization` (`CaseIII.lean:3831`, its own `h622` hyp at `:3835`) at `Theorem55.lean:541`; surfaces inside Case III as the `h622lb` lower-bound hyp of `PanelHingeFramework.case_III_candidate_dispatch` (`CaseIII.lean:3489`, hyp at `:3504`) and the `h622` (`finrank … = D(m−1) − k'`) hyps of the Claim-6.11 row helpers `BodyHingeFramework.exists_redundant_panelRow_ab*` (`CaseIII.lean:133/198/247/530`) | **L7** (pinned §1.69): replace the hypothesis by a derivation from the all-`k` IH at `G_v` — IH gives the generic realization at rank `D(m−1) − k'` (`k' ≤ D−2`); transfer to the given `(ends, q)` by the landed **deficiency-aware rank-polynomial idiom** (§1.62: `exists_rankPolynomial_of_le_finrank_linking` + footnote-6 non-root), NOT the `def=0`-only seed-rank bridge. New brick: **L7a ✓** `exists_rankPolynomial_of_IH_linking` (non-relabel/`f=id` mirror, V8-a, landed clean) + its core `finrank_span_rigidityRows_ofNormals_eq`. **L7b** (next) restates the producer + discharges `h622lb` |
| `h65` (the KT Lemma-6.5 vertex-removal arm of the Case-I dispatch) | `lem:case-I-dispatch` (case-i.tex) | signature hyp of `theorem_55_d3` (`Theorem55.lean:516`), the negative branch of the L5c′ `by_cases` (`Theorem55.lean:553`); the dispatch `case_I_dispatch` itself at `Theorem55.lean:1863` (its own `h65` hyp at `:1865`, consumed `:1891`) | **L8**: §1.54(a3) steps 1–2 — Claim 6.6 graph side (~2–3 commits) + the Π°-placement producer (own signature pin first); the dispatch itself landed in 22h/L5b-iii. Claim 6.6 concludes inside the `k = 0` stratum, no all-`k` generality needed |
| `hbase` (the bare two-vertex base) | `def:genuine-hinge-realization` + `def:rank-hypothesis`; `lem:theorem-55-base-producer` green at the strong pair | **DISCHARGED (22i L3)**: `theorem_55_base_producer` (`Theorem55.lean:436`) supplies `.2`; `hbase` dropped from the `theorem_55_d3` signature (`Theorem55.lean:498` comment) | **L3 complete** (22i): the producer concludes the §1.60(a) strong pair `(G.Simple → HasGenericFullRankRealization) ∧ HasPanelRealization` |
| `hsplit` (the bare no-rigid-subgraph branch) | `def:genuine-hinge-realization` (via `lem:case-III`) | signature hyp of `theorem_55_d3` (`Theorem55.lean:489`); the `hsplitGP` wiring threads `case_III_realization` at `Theorem55.lean:541` | **L9 wiring, no new build**: G0 (`simple_of_isMinimalKDof_of_noRigid`) gives `G.Simple`; forgetful (M4) ∘ the GP Case-III producer |
| `hcontract` (the bare Case-I branch) | `def:genuine-hinge-realization` | **DISCHARGED (22i L5)**: signature hyp of `theorem_55_d3` (`Theorem55.lean:494`) now wired through the `by_cases G.Simple` dispatch `case_I_dispatch` (`Theorem55.lean:1863`) → non-simple `case_I_realization_nonsimple` / simple `case_I_realization_all_k`; the negative-contraction sub-arm stays `h65` → L8 | **L5 complete** (22i) — split by motive; the 6.5 sub-arm stays `h65` → L8 |

## Blockers / open questions

- **L7a landed; L7b + L8–L10 open.** V8-a (the non-relabel rank-poly brick) is **discharged at the
  build level** — the relabel core specialized cleanly to `f = id` (the favorable §1.69(c)
  resolution); no residual proof-shape uncertainty remains in L7. V8's assembly half (the `h622lb`
  derivation) is L7b, P≈2 (the unchanged candidate dispatch already consumes `h622lb`). V9 (L10, the
  `def>0` homogeneous projective move for Thm 5.6 `d=3`) still gates to its layer's design pass
  (carried over from `notes/Phase22i.md` *Blockers*).
- **Blueprint prose staleness (NOT a gate failure; defer the fix to an L7/L8 design-settle
  commit, per the phase-open prologue — do NOT fix proof prose in the phase-open commit).** The
  red-node consistency gate found three live prose pointers that mis-attribute the `h65` /
  all-`k` discharge to **"sub-phase 22i"**, which is stale — that work is **Phase 22k** (22i
  delivered L0–L6 and explicitly deferred `h65` to L8/22k):
  - `lem:case-I-dispatch` (case-i.tex:706 *Status*: "the obligation of sub-phase 22i"; case-i.tex:713 proof: "vertex-removal arm (22i)");
  - `lem:case-III-nested-rank-lower` (case-iii.tex:182: "the all-`k` motive restructure of the successor sub-phase (22i)").
  These are documentation-attribution staleness in prose, not supersession-gate violations: no
  live-route `\uses`/proof-step points at a superseded node, and `blueprint/lint.sh` is green.
  Reword to 22k when the L7/L8 nodes are restated (the natural same-commit moment).

## Hand-off / next phase

**Next commit: L7b — restate `case_III_realization` + discharge `h622lb` via the landed L7a brick,
flipping `lem:case-III-nested-rank-lower` green** (§1.69(a)/(b); P≈2, assembly only — the candidate
dispatch already consumes `h622lb`). Drop the `h622` carry, carry the all-`k` IH; thread the old
shape via a thin wrapper if `theorem_55_d3` must keep building before L9 (Flag F1). Statement-grep
gate + restate `lem:case-III` / `thm:theorem-55-d3-instance` + correct the seed-transfer citation in
the same commit. Then **L8** (the Lemma-6.5 arm, `h65`), **L9** (the zero-carry spine `theorem_55_all_k`),
**L10** (Thm 5.6 `d=3`). After L7–L10 close, 22k delivers the KT-strength Thm 5.5 → 5.6 at `d = 3`
(Cor 5.7 lands in Phase 26), unblocking Phases 24–26; then **Phase 23** (general `d`, KT Lemma 6.13)
opens with its own recon, adding the general-`d` row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

(One-line verdicts; full proof-technique detail in §1.56–§1.69 design sections, docstrings, git.)

- **L7a — the V8-a non-relabel rank-poly brick (2026-06-15, opus, clean):** landed
  `PanelHingeFramework.exists_rankPolynomial_of_IH_linking` + its non-relabel shared core
  `finrank_span_rigidityRows_ofNormals_eq` (`CaseI.lean`, beside the relabel sibling). The §1.69(c)
  P≈3 residual risk **resolved favorably**: the relabel core specialized cleanly to `f = id` — a
  dedicated non-relabel core (selector-swap `Q.ends ↔ ends` via `recordsLinks_agree_swap` +
  `infinitesimalMotions_ofNormals_eq_of_ends_swap` → `span_rigidityRows_eq_of_infinitesimalMotions_eq`,
  the relabel pattern minus the collapse map) compiled first try; no `map_id` reduction, no fresh
  selector-agreement argument. Zero friction (a near-mechanical mirror); gates clean, axiom-clean.
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
