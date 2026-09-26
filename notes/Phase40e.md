# Phase 40e — PENCIL-X0 / CUT/BRIDGE: cut vertices and bridges (work log)

**Status:** in progress (opened design-first 2026-09-26). STEPS' first group (`notes/Phase40-design.md`
§3 STEPS). It lands the standing hypotheses (H) in Lean and the CUT and BRIDGE steps, (MC-52) and
(MC-53): a cut vertex or a chain of bridges is a fibre product, so `X₀` attaining at both pieces
gives it at `G`. Build 1 landed (H), CUT and the single bridge: seven of nine nodes are green.
**Next: build 2**, BRIDGE for every `k` — see *Hand-off*.

## Current state

**Build 1 landed.** Nine nodes, with statements from `ledger.py --brief '(MC-52)' '(MC-53)'` and
the (H) header of `K-main.md`: seven in `main-component.tex` §`sec:main-component-cut`,
`lem:deficiency-cut-vertex` in `deficiency.tex`, `lem:block-rank-cut-vertex` in
`rigidity-matrix.tex`. Seven are green. Two are red: `lem:pencil-bridge-fibre` and
`thm:pencil-x0-bridge`. **The next concrete commit is build 2**, BRIDGE for every `k`, which turns
them green.

## Architectural choices made up front

The coordinator's adjudication (2026-09-26) of the STEPS pre-build recon (one opus pass; the verdicts
are in `notes/Phase40-design.md` §3 STEPS):

- **The step contract.** A step concludes `G.X0Attains K` from `Gᵢ.X0Attains K` at smaller graphs in
  the same `Graph α β`. It picks one picture generic for the pieces and main for `G`, chooses heights
  in one fibre (`MvPolynomial.exists_mem_eval_ne_zero₂`), and ends at `Graph.x0Attains_of_exists`.
  CUT and BRIDGE need nothing of the pieces beyond `X0Attains`; (H) at `G` gives its main-picture
  polynomial.
- **(H) is `Graph.IsX0Graph`** (simple, connected, degree `≥ 2`), the working name kept; `h3` follows.
- **BRIDGE for `k ≥ 1`: explicit path hypotheses**, not a chain structure. The chain type is
  designed at CHAIN's open, with its consumers (the ears, COVERAGE's chain detection).
- **The PI's decisions, verbatim** (2026-09-26; also `notes/pencil/adjudications.md`):

  ```adjudication
  PI decisions, 2026-09-26, on this recon's verdict (verbatim answers to the coordinator's questions):
  1. ORBIT risk: "After 40e opens+builds" — land 40e's open and its CUT/BRIDGE build first, then the read-only ORBIT recon (opus) before the next sub-phase opens.
  2. Grouping: "Accept" — 40e = CUT/BRIDGE; the six later groups go into the design doc as a provisional order, with letters minted only as each opens.
  3. Placement: "Deficiency/Bricks" — the cut-vertex deficiency laws in `Molecular/Deficiency.lean` and the rank identity in `Bricks.lean`, per the ROADMAP convention (a lemma lives with its definition), as FLAT did in 40c.
  4. CUT/BRIDGE faithfulness: "Let's formalize the if and leave only if as an explicit todo item."
  ```

## Lemma checklist

Every item but the last two landed in build 1 (standard axioms).

- [x] **(H)**: `Graph.IsX0Graph`, `Graph.three_le_ncard_closedNbhd`,
  `Graph.IsX0Graph.three_le_ncard_closedNbhd` → `def:pencil-x0-standing`.
- [x] **Rank congruence**: `PanelHingeFramework.finrank_span_rigidityRows_ofNormals_congr` →
  `lem:pencil-rank-congr`.
- [x] **Restriction**: `Graph.liftingRestrict` (+ `_apply`), `Graph.liftingRestrict_mem_liftingSpace`,
  `pencilConfigPoint_liftingRestrict`, `restrictPoly`, `eval_restrictPoly` →
  `lem:pencil-lifting-restrict`.
- [x] **Cut-vertex deficiency** (`Deficiency.lean`): `Graph.deficiency_add_le_of_cutVertex`,
  `Graph.deficiency_eq_add_of_cutVertex`, also pinning `Graph.partitionDef_split_of_vertexTwoCut`
  (Phase 39's D5 debt, consumed here) → `lem:deficiency-cut-vertex`.
- [x] **Cut-vertex rank** (`Bricks.lean`): `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq`
  → `lem:block-rank-cut-vertex`.
- [x] **Cut-vertex fibre**: `Graph.exists_liftingRestrict_eq_of_cutVertex` → `lem:pencil-cut-fibre`.
- [x] **CUT**: `Graph.X0Attains.of_cutVertex` → `thm:pencil-x0-cut`.
- [x] **Single bridge**: `exists_dotProduct_eq_of_linearIndependent`,
  `Graph.exists_liftingRestrict_eq_of_bridge`, `Graph.X0Attains.of_bridge`, in `Cut.lean` and
  pinned nowhere yet. Build 2 keeps them as its `k = 0` case or replaces them.
- [ ] **BRIDGE for every `k`** (not spiked) → `lem:pencil-bridge-fibre`, `thm:pencil-x0-bridge`.
  - Deficiency: KT Lemma 3.6 at the last bridge, then A1 `deficiency_removeVertex_of_degree_eq_one`
    along the pendant path (pin A1 if used: D5 debt).
  - Rank: `le_finrank_span_rigidityRows_of_cut`, iterated.
  - Onto: `z₁` on `V₁`, and an affine function on `V₂`. It is prescribed at `q_a, q_b` when
    `k = 0`, at `q_x` when `k = 1`, and zero when `k ≥ 2`. The path heights come from the planes at
    `a` and `b`.
- [ ] **Tracked, not a close gate:** the "only if" halves of (MC-52)(iv) and (MC-53)(iv)
  (`notes/Phase40-design.md` §3 STEPS).

## Blockers / open questions

- None. BRIDGE for `k ≥ 1` is engineering: path hypotheses, iterated landed laws, an explicit
  extension.

## Hand-off / next phase

**Next: build 2, BRIDGE for every `k`** → `lem:pencil-bridge-fibre`, `thm:pencil-x0-bridge`, in
`Cut.lean`. Not spiked. The plan is the checklist item's three sub-bullets, stated with explicit
path hypotheses (a path `a − x₁ − ⋯ − x_k − b` of degree-2 bodies), not a chain structure. Build 1's
single-bridge declarations are the `k = 0` case, to keep or replace. Pin
`deficiency_removeVertex_of_degree_eq_one` (A1, D5 debt) if it is used.
- **If it is too large for one commit**, land the fibre lemma first: the restriction is onto at a
  chain of bridges, at every admissible picture. Then land the theorem.
- Gates: `lake build`, `lake lint`, `blueprint/verify.sh`, `blueprint/lint.sh`.

**Then 40e's close.** The read-only ORBIT recon runs before the next group opens (PI). `scratch/`
still holds `S40eTracked.lean`'s `rigidContract_induce_simple` (CONTRACT-R) and the curve-limit
lemma (SPLITOFF), for those groups. The coordinator removes `scratch/` once 40e no longer needs it.

## Decisions made during this phase

- **2026-09-26 — opened design-first from one opus recon.** The coordinator re-ran its three spike
  files: exit 0, no warnings, no `sorry`. `Graph.X0Attains.of_cutVertex` and
  `Graph.X0Attains.of_bridge` use `[propext, Classical.choice, Quot.sound]`. The six tracked items
  are settled in `notes/Phase40-design.md` §3 STEPS, and the later groups are recorded there by
  code.
- **2026-09-26 — build 1: the spike transcribed.** The cut-vertex deficiency laws went in a new
  section at the end of `Deficiency.lean`, after the vertex-2-cut split they specialize. The rank
  identity went in `Bricks.lean`'s 2-cut section. There its proof is shorter than the spike's: the
  private helpers `mem_sup_infinitesimalMotions_induce` (at `u = v`) and
  `rigidityRows_eq_union_induce` do the work. **Headline axioms:** `Graph.X0Attains.of_cutVertex`,
  `Graph.X0Attains.of_bridge`, `Graph.deficiency_eq_add_of_cutVertex` and
  `BodyHingeFramework.finrank_span_rigidityRows_cutVertex_eq` all use
  `[propext, Classical.choice, Quot.sound]`.
