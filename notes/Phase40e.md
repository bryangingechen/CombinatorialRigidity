# Phase 40e — PENCIL-X0 / CUT/BRIDGE: cut vertices and bridges (work log)

**Status:** ✓ complete (opened design-first, built and closed 2026-09-26). CUT/BRIDGE, STEPS' first
group (`notes/Phase40-design.md` §3 STEPS), proved the cut and bridge steps of the `X₀` induction,
the "if" halves of (MC-52) and (MC-53): if `G` satisfies the standing hypotheses (H) and has a cut
vertex or a chain of bridges of any length, `X₀` attaining at both pieces gives it at `G`.
**Next: the read-only ORBIT recon** (PI decision 1), then STEPS' next group (provisionally
CONTRACT-R), **not yet opened** — see *Hand-off*.

## Current state

**Closed.** Build 1 (`993ccc41`), build 2 (`c74ea8a1`, then `3d05ecc9` after the recon `c28767b4`)
and the close landed. The nine nodes are green: seven in `main-component.tex`
§`sec:main-component-cut`, `lem:deficiency-cut-vertex` in `deficiency.tex` and
`lem:block-rank-cut-vertex` in `rigidity-matrix.tex`. Build 2 also pinned the pendant rank law on
`lem:block-rank-cut` and Phase 39's pendant deficiency law on `lem:cut-edge-decomposition`. The Lean
is `Molecule/Pencil/MainComponent/Cut.lean` (its module docstring lists the statements), with the
cut-vertex laws in `Molecular/Deficiency.lean` and `RigidityMatrix/Bricks.lean`.

**Headline axioms, re-verified at the close** on 48 declarations: the eighteen `formalization.yaml`
main results, the twenty-eight pins of the nine nodes and the two new pins (among them
`Graph.X0Attains.of_cutVertex`, `Graph.X0Attains.of_bridgePath`, the cut-vertex deficiency and rank
laws, and the pendant rank law). Forty-four are exactly `[propext, Classical.choice, Quot.sound]`.
The other four use a strict subset: `pathVertex` and `pathVertex_zero` (`[propext]`),
`pathVertex_eq_or_exists` and `pathVertex_cases` (`[propext, Quot.sound]`). *Measured, script not
retained*: one `#print axioms` line per declaration under `import CombinatorialRigidity`, run with
`lake env lean` on the fully built tree (~27 s).

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the STEPS pre-build recon (one opus pass; verdicts in
`notes/Phase40-design.md` §3 STEPS):

- **The step contract.** A step concludes `G.X0Attains K` from `Gᵢ.X0Attains K` at smaller graphs in
  the same `Graph α β`: one picture generic for the pieces and main for `G`, heights in one fibre
  (`MvPolynomial.exists_mem_eval_ne_zero₂`), ending at `Graph.x0Attains_of_exists`.
- **(H) is `Graph.IsX0Graph`** (simple, connected, degree `≥ 2`); `h3` follows.
- **BRIDGE for `k ≥ 1`: explicit path hypotheses**, not a chain structure. The chain type is
  designed at CHAIN's open, with its consumers (the ears, COVERAGE's chain detection).
- **The PI's four decisions** (2026-09-26) are verbatim in `notes/pencil/adjudications.md`: ORBIT's
  recon after 40e's build (the hand-off below), the provisional grouping, the placement in
  `Deficiency.lean` / `Bricks.lean`, and the "if" halves formalized with the "only if" halves a
  tracked todo.

## Lemma checklist

All landed with the standard axioms or a subset (*Current state*).

- [x] **(H)**: `Graph.IsX0Graph` (+ `three_le_ncard_closedNbhd`) → `def:pencil-x0-standing`.
- [x] **Rank congruence** → `lem:pencil-rank-congr`; **restriction** → `lem:pencil-lifting-restrict`.
- [x] **Cut vertex** (build 1): deficiency (`Deficiency.lean`, pinning Phase 39's
  `partitionDef_split_of_vertexTwoCut`), rank (`Bricks.lean`), fibre, and CUT
  `Graph.X0Attains.of_cutVertex` → `lem:deficiency-cut-vertex`, `lem:block-rank-cut-vertex`,
  `lem:pencil-cut-fibre`, `thm:pencil-x0-cut`.
- [x] **Single bridge** (build 1, retired in build 2): `exists_dotProduct_eq_of_linearIndependent`,
  `Graph.exists_liftingRestrict_eq_of_bridge` and `Graph.X0Attains.of_bridge` were deleted once
  BRIDGE landed for every `k` — unpinned and unused; this line is their retirement record.
- [x] **The fibre lemma** (build 2): `pathVertex`, `Graph.exists_liftingRestrict_eq_of_bridgePath`
  → `lem:pencil-bridge-fibre`.
- [x] **BRIDGE** (build 2): `Graph.X0Attains.of_bridgePath`, with the `pathVertex` API,
  `Graph.cutEdges_union_image_of_bridgePath` and the two path telescopes → `thm:pencil-x0-bridge`;
  the pendant rank law `BodyHingeFramework.add_le_finrank_span_rigidityRows_induce_union_singleton`
  (`Bricks.lean`) → `lem:block-rank-cut`.
- [x] **The close** (docs and blueprint only): ROADMAP, the design doc's §3 STEPS and its new
  appendix, the end-to-end re-read, the exposition ledger, the headline axioms; the public surfaces
  left unchanged (the PI's standing call).
- **Not 40e's, tracked elsewhere:** the "only if" halves of (MC-52)(iv) and (MC-53)(iv) are an
  unchecked todo in `notes/Phase40-design.md` §3 STEPS, carried past this close (PI decision 4).

## Blockers / open questions

- None for 40e. Its one carried item, the "only if" halves, is tracked in the design doc (above).

## Hand-off / next phase

**40e is closed. The next step is the read-only ORBIT recon** (opus; PI decision 1), before any
later group opens. It decides how (MC-46)'s dimension counting, with (MC-138)'s orbit table, gets
formalized: a new polynomial-level proof of `(P₂)` outside the three families, routing the cell
`k = 2`, `a ≁ b`, `δ₂ ≥ 2` another way in COVERAGE, or building dimension theory
(`notes/Phase40-design.md` §4, *ORBIT's dimension counting*).

**Then** STEPS' next group opens design-first, provisionally CONTRACT-R (§3 STEPS, *The provisional
grouping*); its opening commit mints its letter and work log. The spike pieces CONTRACT-R and
SPLITOFF reuse (`Graph.rigidContract_induce_simple`; the curve-limit lemma) are verbatim in the
design doc's appendix *the STEPS recon's tracked spike*, so `scratch/` is no longer needed; the
coordinator removes it after checking the copy.

## Decisions made during this phase

- **2026-09-26 — the close.** The end-to-end re-read of `sec:main-component-cut` defined `tgt` in
  the preamble (the bridge proof used it undefined), fixed the body-term count in
  `thm:pencil-x0-bridge`'s proof (`6(k + 1)`, not `6k`), spelled out the closed-neighbourhood cases
  of `lem:pencil-bridge-fibre`'s proof, wrote the dimension remark's `c_k` as `k − 2`, and named the
  subsection in the chapter preamble. One exposition-ledger entry, done in place. Public surfaces
  unchanged, per the PI's standing call from 40c's close (they update when Phase 40 closes).
  Project-organization review: no new item; details in the next entry.
- **2026-09-26 — the close, housekeeping.** `S40eTracked.lean` is preserved verbatim in
  `notes/Phase40-design.md`'s appendix (re-checked at `d57672c0`); the auto-loaded CLAUDE.md suite
  is unchanged (1 695 lines); `notes/pencil/CLAUDE.md` still names only `notes/Phase40a.md` beside
  the design doc, left unedited (a CLAUDE.md, making no status claim).
- **2026-09-26 — build 2's second half:** BRIDGE by one cut at the last bridge and a telescope over
  the prefixes; a recon ruled out an `X0Attains` induction (a peeled body has no admissible picture).
- **2026-09-26 — build 2's first half:** the fibre lemma re-derived, not transcribed — one affine
  extension by `a`'s own witness, for every `k`, with no admissibility.
- **2026-09-26 — build 1:** the spike transcribed; the rank identity shortened via two private
  helpers in `Bricks.lean`.
- **2026-09-26 — opened design-first from one opus recon**, whose three spike files the coordinator
  re-ran (exit 0, no warnings, no `sorry`); the six tracked items settled in the design doc.
