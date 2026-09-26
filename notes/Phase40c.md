# Phase 40c — PENCIL-X0 / FLAT: the flat rank (work log)

**Status:** ✓ complete (opened design-first and closed 2026-09-26). FLAT proved Step MC4/MC5 of
§(K-main): the flat rank `6|V| − 3 − dim L(q)`, the bound `dim L(q) ≥ 3 + def₂`, `def₃ ≤ def₂`, and
"`X₀` attains at the flat witness", all green, with 40a's pin debt paid. **Next: BRIDGE**, Phase
40's next layer (`notes/Phase40-design.md` §3), **not yet opened** — see *Hand-off*.

## Current state

**Closed.** The build (`598f20ce`) and the close landed. `main-component.tex`
§`sec:main-component-flat` (eight nodes), `lem:deficiency-antitone` (`deficiency.tex`) and the
pin-debt node `lem:relative-deficiency-rank-bound` (`rigidity-matrix.tex`) are green. The Lean is in
`Molecule/Pencil/MainComponent/Flat.lean` (its module docstring lists the statements) and
`Molecular/Deficiency.lean`, with `linearIndependent_pencilPicturePoint_pair` in `Carrier.lean`.
Headline axioms were re-verified at the close on 38 declarations: the eighteen `formalization.yaml`
main results and the twenty pins of those ten nodes. Each is exactly
`[propext, Classical.choice, Quot.sound]` (*measured, script not retained*: one `#print axioms` line
per declaration under `import CombinatorialRigidity`, run with `lake env lean` on the built tree).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the FLAT design recon (verdict also in
`notes/Phase40-design.md` §3 FLAT):

- **The flat (primal) side**, carried to `Graph.X0Attains`'s `ofNormals` framework by C4's two
  rewrites (`ofNormals_toBodyHinge_eq_mapSupport_pointJoinFramework`,
  `BodyHingeFramework.finrank_span_rigidityRows_mapSupport`); the cone side is not used.
- **The split `Λ²K⁴ = W′ ⊕ W_Π`** is the linear equivalence `flatScrewEquiv`, lifted from two
  alternating forms (the ScrewVelocity pattern, field-general).
- **`F(q)` is `Graph.liftingPlanes`**, free off `V(G)`: `dim F(q) = 3|V(G)ᶜ| + dim L(q)`.
- **(MC-4)(a) is exact**, by linear equivalences. **(MC-4)(b)** is the grade-1 relative bound at the
  normals `(x_v, y_v, 1)`, whose motion space is exactly `F(q)` (BRIDGE's first bullet, folded in).
  **(MC-5)(i)** is antitone in `n` on a connected graph, in `Deficiency.lean`.
- **Consumer shapes:** `Graph.x0Attains_of_finrank_liftingSpace_le` (an admissible picture with
  `dim L(q) ≤ 3 + def₃` gives `X0Attains`; (MC-89) step 3 and CONTRACT's "`X₀(H)` attains by
  FLAT") and `Graph.x0Attains_of_finrank_liftingSpace_eq_three` (THETA, (MC-139)).

## Lemma checklist

- [x] **The build** (`598f20ce`, one commit): `Deficiency.lean`, `Flat.lean` and the 40a pin debt.
  Nodes and names: the FLAT subsection's `\lean{}` pins and `Flat.lean`'s module docstring.
- [x] **The close** (docs only): ROADMAP, the design doc's §3 FLAT, the end-to-end re-read, the
  exposition ledger, the headline axioms; the public surfaces left unchanged (PI).
- [ ] **Cleanup-round item, not FLAT's:** the wider `lem:trivial-motions-rank-bound` stand-in audit
  (`notes/Phase40-design.md` §3 FLAT).

## Blockers / open questions

- None for FLAT. What BRIDGE keeps (moving generic normals into the chart; the edge-restricted
  selector) is in `notes/Phase40-design.md` §3 BRIDGE.

## Hand-off / next phase

**40c is closed. The next concrete commit opens BRIDGE design-first** (`notes/Phase40-design.md`
§3 BRIDGE: moving generic normals into the chart by per-body rescaling and open admissibility, and
the non-spanning forms at `H`, `G/H` and `G′ + ab`, with the edge-restricted-selector open point).
That commit mints its letter and its work log. FLAT's consumer shapes are in *Architectural
choices* above.

## Decisions made during this phase

- **2026-09-26 — the PI's close adjudication, verbatim.** Public surfaces (README, `home_page`,
  `intro.tex`, `formalization.yaml`): "Leave them (Recommended)". The arc-level wording stays; they
  update when Phase 40 as a whole closes.
- **2026-09-26 — the close.** The end-to-end re-read moved "`q` is a main picture" from the
  statement of `cor:pencil-flat-attains` to its proof (no pin exports it; it is an inline step of
  `Graph.x0Attains_of_finrank_liftingSpace_le`), and tightened two proof sentences and the chapter
  preamble. No new exposition-ledger entries. Project-organization review: no new item; the
  auto-loaded CLAUDE.md suite is unchanged since 40a's review (1 695 lines).
- **2026-09-26 — the build**, one commit from the recon's spike. `Deficiency.lean`'s private walk
  helper became the public `Graph.ConnBetween.eq_of_forall_isLink`, and its components count
  `Graph.encard_image_le_numberOfComponents_restrict` is shared with
  `rk_cycleMatroid_within_parts_le`. Three FRICTION idioms filed.
- **2026-09-26 — opened design-first; the opus/fable A/B.** The coordinator re-ran both recons'
  witnesses and adopted the opus route (flat side, exact (MC-4)(a), exact grade-1 motion equality,
  (MC-5)(i) proved); the fable spike was cone-side and inequality-only. Merged from fable: the
  pin-debt scope and the `Φ` citations (Crapo–Whiteley 1982 Example 4.4, Whiteley 1996 §8.3; not
  Whiteley 1984; no identity attributed).
- **2026-09-26 — the design doc's §3 FLAT table** was re-transcribed from `ledger.py --brief` at the
  open; the codim bound `dim L(q) ≥ 3|V| − 2|E|` stays dropped.
