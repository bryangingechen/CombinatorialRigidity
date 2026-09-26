# Phase 40c — PENCIL-X0 / FLAT: the flat rank (work log)

**Status:** in progress (opened design-first 2026-09-26). FLAT proves Step MC4/MC5 of
§(K-main): the flat rank `6|V| − 3 − dim L(q)`, the bound `dim L(q) ≥ 3 + def₂`, `def₃ ≤ def₂`,
and "`X₀` attains at the flat witness". The accepted design is a compiler-checked recon whose
spike is sorry-free, so the build is transcription. **Next: the build commit** — see *Hand-off*.

## Current state

**Opened.** The FLAT subsection `sec:main-component-flat` of `main-component.tex` carries eight
red nodes, and `deficiency.tex` one (`lem:deficiency-antitone`), all transcribed from
`python3 notes/ledger.py --brief '(MC-4)' '(MC-5)'`. No Lean has landed yet. The build lands the
recon's spike in `Molecule/Pencil/MainComponent/Flat.lean` (new) and `Molecular/Deficiency.lean`,
and pays the 40a pin debt (`lem:relative-deficiency-rank-bound`, born green) in the same commit.

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the FLAT design recon:

- **The flat (primal) side.** The rank is computed on the point-join framework at `z = 0` and
  carried to `Graph.X0Attains`'s `ofNormals` framework by C4's two rewrites
  (`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`,
  `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`). The cone side is not used.
- **The split `Λ²K⁴ = W′ ⊕ W_Π`** is a linear equivalence `flatScrewEquiv : ScrewSpace K 2 ≃ₗ
  K³ × K³`, lifted from two alternating forms (`σ(v, w) = v_z ŵ − w_z v̂`, `π(v, w) = v̂ ×₃ ŵ`;
  the ScrewVelocity pattern, field-general), bijective by a rebuild map and `6 = 6`.
- **`F(q)` is `Graph.liftingPlanes`**: families `h : α → K³` whose differences across every link
  vanish at both ends' picture points, free off `V(G)`. `dim F(q) = 3|V(G)ᶜ| + dim L(q)`.
- **(MC-4)(a) is an exact identity**, via `Z(q, 0) ≃ linkConstants × F(q)` (linear
  equivalences, not inequalities). **(MC-4)(b)** is the landed grade-1 relative bound at the
  normals `(x_v, y_v, 1)`, whose motion space is exactly `F(q)`; this folds BRIDGE's first bullet
  into FLAT.
- **(MC-5)(i) in general form:** on a connected graph `def` is antitone in `n`, by
  `|P| − 1 ≤ d(P)` (cycle matroid). It goes in `Deficiency.lean`, reusing (generalized) its
  walk-constancy helper.
- **Consumer shapes:** `Graph.x0Attains_of_finrank_liftingSpace_le` (an admissible picture with
  `dim L(q) ≤ 3 + def₃` gives `X0Attains`; (MC-89) step 3 and CONTRACT's "`X₀(H)` attains by
  FLAT") and `Graph.x0Attains_of_finrank_liftingSpace_eq_three` (THETA, (MC-139)).

## Lemma checklist

Planned names; the spike compiles them all (`lake env lean`, exit 0, standard axioms).

- [ ] **`Deficiency.lean`**: `Graph.ConnBetween.eq_of_forall_isLink` (generalizes the private
  walk helper), `Graph.Preconnected.eq_of_forall_isLink`,
  `Graph.encard_image_le_numberOfComponents_restrict` (shared with
  `rk_cycleMatroid_within_parts_le`), `Graph.Connected.numParts_le_ncard_crossingEdges_add_one`,
  `Graph.Connected.deficiency_le_deficiency_of_le`,
  `Graph.Connected.deficiency_three_le_deficiency_two` → `lem:deficiency-antitone`.
- [ ] **`Flat.lean`, lifting planes**: `Graph.liftingPlanes`, `Graph.finrank_liftingPlanes` →
  `def:pencil-lifting-planes`, `lem:pencil-lifting-planes-dim`.
- [ ] **grade 1 (carrier)**: `screwOneEquiv`,
  `Graph.finrank_infinitesimalMotions_ofNormals_pencilPicturePoint`,
  `Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint` →
  `lem:pencil-lifting-planes-motions`; `Graph.three_add_deficiency_le_finrank_liftingSpace` →
  `lem:pencil-lifting-space-deficiency`.
- [ ] **grade 2 (carrier)**: `flatScrewEquiv`, `Graph.linkConstants`,
  `Graph.finrank_infinitesimalMotions_pointJoinFramework_flat` → `lem:pencil-flat-split`;
  `Graph.finrank_span_rigidityRows_ofNormals_flat` (and `_flat_le`, `_flat_eq_iff`) →
  `thm:pencil-flat-rank`.
- [ ] **consequences**: `Graph.finrank_liftingSpace_eq_three_add_deficiency_three_iff`,
  `Graph.x0Attains_of_finrank_liftingSpace_le` → `cor:pencil-flat-attains`;
  `Graph.x0Attains_of_finrank_liftingSpace_eq_three` and the rank clause →
  `cor:pencil-flat-x0`.
- [ ] **Pin debt (40a)**: `lem:relative-deficiency-rank-bound` in `rigidity-matrix.tex`, born
  green, pinning `BodyHingeFramework.screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
  and `BodyHingeFramework.finrank_span_rigidityRows_add_deficiency_le`; repoint the proof `\uses`
  and prose of `thm:theorem-55-6-rows` and `lem:pencil-x0-one-witness`. The wider audit is a
  cleanup-round item (`notes/Phase40-design.md` §3 FLAT).

## Blockers / open questions

- None. What BRIDGE keeps (moving generic normals into the chart; the edge-restricted selector)
  is in `notes/Phase40-design.md` §3 BRIDGE.

## Hand-off / next phase

**Next: the build commit.** Land the checklist in `Deficiency.lean` and a new
`Molecule/Pencil/MainComponent/Flat.lean` (root import), flip the FLAT nodes and
`lem:deficiency-antitone` green, and pay the pin debt, in one commit (or two, split at the
grade-2 section). Gates: `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`.
After the build, the next step is FLAT's close.

## Decisions made during this phase

- **2026-09-26 — opened design-first; the opus/fable A/B.** The coordinator re-ran both recons'
  witnesses (exit 0, no `sorry`, standard axioms) and adopted the opus route: flat side,
  exact (MC-4)(a), `F(q)` with the exact grade-1 motion equality, (MC-5)(i) in antitone form.
  The fable spike was cone-side and inequality-only, with two maps and (i) unproved (626k
  tokens, 87 min, against 411k, 45 min). Merged from fable: the pin-debt scope (both
  declarations; two stand-in sites) and the `Φ` citations — Crapo–Whiteley 1982 Example 4.4
  (pp. 72–73) and Whiteley 1996 §8.3, not Whiteley 1984; no identity is attributed.
- **2026-09-26 — the design doc's §3 FLAT table** mislabelled (MC-5)(ii) and omitted (MC-5)(i);
  re-transcribed from `ledger.py --brief` at the open. The codim bound `dim L(q) ≥ 3|V| − 2|E|`
  stays dropped (no consumer; a corollary of (MC-4)(b) if one appears).
