# Phase 42c — PD-STABLE: the pencil from a lower dimension (work log)

**Status:** in progress, opened 2026-10-30 by the PI (design doc §3's scope as written), a
sub-phase of Phase 42 beside 42a. Forward mode, the Lean under `/coordinate-phase`: the dep-graph
is `blueprint/src/chapter/pencil-d.tex` §`sec:pencil-d-stable`, 9 nodes, all green. The open
corrected the deficiency lemma (it needs `G` connected) and found its proof gives a sharper range;
the PI widened the theorem to `def_2 ≤ 3` (*Architectural choices*). Next concrete task: close 42c.

## Current state

**Next:** close 42c, the phase-close checklist (`PHASE-BOUNDARIES.md` *When this commit closes a
phase*). No red node is left and no Lean is planned.

**Landed (latest):** `lem:pencil-d-embed-realization` (green, one commit), in
`Pencil/Grade/Embedding.lean`, which now imports `Grade/Realization.lean`:
`HasPencilPlaneRealization.map_gradeEmbed`, `hasGradedPencilRealization_of_le` and
`hasGradedDistinctPencilRealization_of_le`, at a fixed deficiency parameter (*Decisions*), over the
grade-general `exists_eq_panelSupportExtensor_of_ne_zero`, `extensorInPanel_panelSupportExtensor_iff`
and `extensorThroughSubspace_panelSupportExtensor_iff` (`Grade/Realization.lean`).

**Landed before (each green, one commit):** `thm:pencil-d-deficiency-two-le-three`
(`Pencil/Grade/Stable.lean`); `lem:pencil-d-x0-attains-of-le` and `lem:pencil-d-embed-config-rank`
(`Pencil/Grade/ZeroHeights.lean`, which imports `Grade/Witness.lean`); `lem:screw-embedding-rank`,
`def:pencil-d-embedding` and `lem:pencil-d-embedding-join` (`Pencil/Grade/Embedding.lean`);
`lem:pencil-d-x0-attains-distinct` (`Pencil/Grade/Configuration.lean`); `lem:deficiency-stable`
(`Deficiency.lean`). The open laid down the section with its nodes red (no Lean).

## Architectural choices made up front

- **PI, 2026-10-30:** "Open as 42c, §3 scope (Recommended)". The scope: items 1–3 of design doc
  §3 (the embedding at every `d′ ≤ d` in its rank, statement and configuration forms; the
  deficiency lemma; `Pᵈ` at `def[3] ≤ 1`, Tier 0), with FRICTION's open `normalsJoin`
  `exteriorPower.map 2` lemma landing with item 1.
- **PI, 2026-10-30 (the sharp range):** "Widen to def_2 ≤ 3 (Recommended)". The question as put:
  "The open found that the deficiency lemma's own proof gives a sharper range. On a connected G, def at
  dimension d′ equals def at every d ≥ d′ once def_2(G) + 3 ≤ C(d′+1, 2), rather than at
  d′ ≥ def_2 + 2. The range is tight on cycles: C₇ has def_2 = 4, def_3 = 1 and def_4 = 0. With
  d′ = 3 (C(4,2) = 6), Phase 40 plus the embedding then proves the pencil in every dimension at
  def_2(G) ≤ 3, not just ≤ 1. I checked this by hand. Should Tier 0's theorem,
  thm:pencil-d-deficiency-two-le-one, widen?" The option: "Same proof; only the hypothesis and the
  node's name and wording change. No extra commits. The Tier 0 sentence on ROADMAP and the status
  surfaces says ≤ 3." The node is now `thm:pencil-d-deficiency-two-le-three`.
- **Notation:** design doc `def[3]` = blueprint `def_2` = Lean `G.deficiency 2` (`Strata.md`'s
  `def_3`); `def[6]` = `def_3` = `G.deficiency 3`. Grade `k = d − 1` and `m = d − 2` heights as
  42b (`notes/Phase42b.md` *Architectural choices*).
- **The embedding `ι`** inserts zeros before the last coordinate, so at
  `pencilConfigPointGrade q z'` it appends zero heights; `φ = * ∘ Λ²ι ∘ *⁻¹`
  (`complementIso`). The rank form is for any injective linear map of screw spaces.
- **Item 1 at a fixed deficiency parameter `n`:** `HasGradedPencilRealization K k' n G` gives
  `… K k n G` for `k' ≤ k`; the rewrite `def_{d′} = def_d` is the consumer's (item 3, PD-HEAD).
- **Homes (a builder may refine):** item 2 in `Deficiency.lean`; `exteriorPower_map_normalsJoin`
  in `PanelLayer.lean` (FRICTION's proposal; upstream of the tree) or the new file; the rest in a
  new `Pencil/Grade/Embedding.lean`, over `Grade/Witness.lean`, `Grade/Configuration.lean` and
  `MainComponent/CoverageTheoremS.lean`.

## Lemma checklist

All nine nodes are green, each pinned in `sec:pencil-d-stable` with its Lean names and hypotheses;
the chapter is the index (forward mode), so the per-node list is retired.

## Blockers / open questions

- **(b) resolved (2026-10-30):** the surfaces resting on Result 16's old form are restated (Strata Results 15–17 and 22, design doc §1/§2.5/§3/§4, ROADMAP §42): content range `def_3 ≥ C(d,2) − 2`, Tier 1 reach `def_3 ≤ 7`. SHORT-CORE's review 2 (workbook S50, branch `attack-short-core`, commit `38f41bf9`, not on master): its scope is unchanged at `d = 4` and `def_3 ≥ 2d − 3` at every danger cell. `strata.py`'s filters keep the old, wider range.

## Hand-off / next phase

The next commit closes 42c (*Current state*): every node of `sec:pencil-d-stable` is green, and the
coordinator held the close checklist for its own dispatch, so it did not fire on the last node's
commit.

## Decisions made during this phase

- **The open (2026-10-30), checked against the bodies** of every definition the nodes use
  (`deficiency`, `HasPencilPlaneRealization` and its parts, the graded realizations, `X0AttainsGrade`,
  `pencilConfigPointGrade`, `panelSupportExtensor`, `complementIso`): each statement and proof held.
- **Statement corrections at the open** (transcriptions, for the pre-build guard): (1) item 2
  needs `G` connected: two bodies and no edge have `def_n = bodyBarDim n`, so `def[3] = 3`,
  `d′ = 5`, yet `def[15] = 15 ≠ 21 = def[21]` (the coordinator's, by hand; `lake lean` witness);
  (2) item 2 states the sharp range, §3's form its "in particular" (Strata Result 16); (3) the
  configuration form at `2 ≤ d′`, not `3 ≤ d′` (no step uses a height); (4) the statement form
  carries the adjacent-distinct case; (5) item 3 split, `lem:pencil-d-x0-attains-distinct` (the
  every-`d` form of `lem:pencil-x0-attains-distinct`) its own node, on `thm:pencil-x0-coverage`.
- **All nine nodes in `pencil-d.tex`**, item 2 included: the red frontier stays in one section,
  and `deficiency.tex`, all green, stays so for `intro.tex`'s status sentence.
- **`def:pencil-d-embedding`:** `ι` extends by zero along `gradeEmbedIndex`; `φ` is the `∘ₗ`
  composite through `complementIso (j := 2)`, rewritten by `screwEmbed_apply` (`rfl`), never
  `comp_apply` (FRICTION). The Lean holds at every `k' ≤ k`.
- **`lem:screw-embedding-rank`:** `Z(φF) = φ ∘ Z(F) ⊔ Z₀` with `⊓ = φ ∘ Z₀′` (the zero-hinge
  frameworks' motions), not the blueprint's complement `T`; the bodies off `V(G)` cancel in the rank,
  and the blueprint proof counts them. `map` and the zero-hinge helpers' upstream home: FRICTION.
- **`lem:pencil-d-embed-config-rank`:** home `Pencil/Grade/ZeroHeights.lean`; the configuration's
  framework *equals* the mapped one, so no transfer at links (FRICTION's `gradeEmbed` index idiom).
- **`lem:pencil-d-embed-realization` at a fixed deficiency parameter** (the coordinator's hypothesis,
  checked): `D′(|V|−1) − def_n + (D − D′)(|V|−1) = D(|V|−1) − def_n`, so the Lean needs no deficiency
  equation. The node was restated to this form (every `d''`, `G` connected only for the rank); the
  `def_{d′} = def_d` reading is a sentence after it, the consumer's rewrite. Route: a nonzero hinge is
  `C(w₁, w₂)` (the blueprint's basis of `A^⊥`, the scale absorbed into `w₁`), and two `_iff` lemmas
  read its panels and orthogonals off `span {w₁, w₂}` at both grades. Home `Embedding.lean`, which
  now imports `Grade/Realization.lean` (no cycle: `ZeroHeights.lean` already reached both).
