# Phase 40c — PENCIL-X0 / FLAT: the flat rank (work log)

**Status:** in progress (opened design-first 2026-09-26); **the build has landed**. FLAT proves
Step MC4/MC5 of §(K-main): the flat rank `6|V| − 3 − dim L(q)`, the bound `dim L(q) ≥ 3 + def₂`,
`def₃ ≤ def₂`, and "`X₀` attains at the flat witness", all green, with 40a's pin debt paid.
**Next: FLAT's close** (docs only) — see *Hand-off*.

## Current state

**Built.** The FLAT subsection `sec:main-component-flat` of `main-component.tex` (eight nodes)
and `lem:deficiency-antitone` in `deficiency.tex` are green, transcribed at the open from
`python3 notes/ledger.py --brief '(MC-4)' '(MC-5)'`. The Lean is in the new
`Molecule/Pencil/MainComponent/Flat.lean` (its module docstring lists the statements) and
`Molecular/Deficiency.lean` (the connectivity helpers and (MC-5)(i)), with
`linearIndependent_pencilPicturePoint_pair` in `Carrier.lean`. The pin-debt node
`lem:relative-deficiency-rank-bound` (`rigidity-matrix.tex`) is green, and
`thm:theorem-55-6-rows` and `lem:pencil-x0-one-witness` now `\uses` it. The seventeen new pinned
declarations, and the refactored `rk_cycleMatroid_within_parts_le`, each depend on exactly
`[propext, Classical.choice, Quot.sound]` (*measured, script not
retained*: one `#print axioms` per declaration under `import CombinatorialRigidity`).

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

- [x] **The build** (one commit): `Deficiency.lean` (connectivity helpers, (MC-5)(i)), `Flat.lean`
  (lifting planes, grade 1, grade 2, consequences), and the 40a pin debt. Nodes and names: the
  FLAT subsection's `\lean{}` pins and `Flat.lean`'s module docstring.
- [ ] **FLAT's close** (docs only) — see *Hand-off*.
- [ ] **Cleanup-round item, not FLAT's:** the wider `lem:trivial-motions-rank-bound` stand-in audit
  (`notes/Phase40-design.md` §3 FLAT).

## Blockers / open questions

- None. What BRIDGE keeps (moving generic normals into the chart; the edge-restricted selector)
  is in `notes/Phase40-design.md` §3 BRIDGE.

## Hand-off / next phase

**Next: FLAT's close** (docs only, `PHASE-BOUNDARIES.md` *When this commit closes a phase*):
flip the ROADMAP row and compress §40c, compress `notes/Phase40-design.md` §3 FLAT to a verdict,
re-read the FLAT subsection end to end, add the `notes/BlueprintExposition.md` section, put the
public-surface question to the PI, and re-verify the headline axioms. After it, BRIDGE opens
design-first (`notes/Phase40-design.md` §3 BRIDGE).

## Decisions made during this phase

- **2026-09-26 — the build**, one commit, transcribed from the recon's spike. The private walk
  helper of `Deficiency.lean` became the public `Graph.ConnBetween.eq_of_forall_isLink`, and its
  components count `Graph.encard_image_le_numberOfComponents_restrict`, now shared with
  `rk_cycleMatroid_within_parts_le`. Three FRICTION idioms filed (an `ℕ∞`/`WithTop ℕ` cancel, a
  `private` name clash, an omega atom).
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
