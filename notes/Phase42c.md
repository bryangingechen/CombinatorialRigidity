# Phase 42c — PD-STABLE: the pencil from a lower dimension (work log)

**Status:** ✓ closed 2026-10-30 (opened the same day by the PI, design doc §3's scope as written),
a sub-phase of Phase 42, which stays in progress with 42a. Forward mode, the Lean under
`/coordinate-phase`: `blueprint/src/chapter/pencil-d.tex` §`sec:pencil-d-stable` has all 9 nodes
green, the Lean in `Deficiency.lean` and `Pencil/Grade/` (three new files), in 15 commits with the
open and the close. The open corrected the deficiency lemma (it needs `G` connected) and found its
proof gives a sharper range; the PI widened the theorem to `def_2 ≤ 3` (*Architectural choices*).
Next (*Hand-off*): which sub-phase opens goes to the PI.

## Current state

**Closed.** Tier 0 is proved: over an infinite field, every graph satisfying the standing
hypotheses with `def_2(G) ≤ 3` has the general configuration attaining in every dimension
`d ≥ 3`, and so an adjacent-distinct pencil realization at the deficiency rank there
(`Graph.x0AttainsGrade_of_deficiency_two_le_three`,
`Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three`; `#print axioms` at the close:
`[propext, Classical.choice, Quot.sound]`). The close re-read the section end to end (one clause of
narration cut; the chapter's and section's openings restated from "the theorem in every dimension"
to the attaining they prove), wrote `notes/BlueprintExposition.md`'s 42c section (no new entry),
groomed the dispatch log's two 42c rows (F56 kept open for `/harness-review`) and compressed design
doc §3's PD-STABLE to its verdict. File map, one line each:
- `Deficiency.lean`: `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le` and its
  "in particular", `…_of_two_add_deficiency_two_le` (`lem:deficiency-stable`).
- `Grade/Embedding.lean`: `gradeEmbed` and `screwEmbed` (`def:pencil-d-embedding`);
  `exteriorPower_map_normalsJoin` and `screwEmbed_panelSupportExtensor`
  (`lem:pencil-d-embedding-join`); `BodyHingeFramework.map` and its rank and motions
  (`lem:screw-embedding-rank`); `HasPencilPlaneRealization.map_gradeEmbed` and
  `hasGraded(Distinct)PencilRealization_of_le` (`lem:pencil-d-embed-realization`).
- `Grade/ZeroHeights.lean`: `padHeights` and the configuration's rank
  (`lem:pencil-d-embed-config-rank`); `Graph.X0AttainsGrade.of_le` (`lem:pencil-d-x0-attains-of-le`).
- `Grade/Configuration.lean`: `Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`
  (`lem:pencil-d-x0-attains-distinct`).
- `Grade/Realization.lean`: the grade-general `exists_eq_panelSupportExtensor_of_ne_zero` and two
  `_iff`s reading a hinge's panels and orthogonal off `span {w₁, w₂}`.
- `Grade/Stable.lean`: Tier 0 (`thm:pencil-d-deficiency-two-le-three`).

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
  `pencilConfigPointGrade q z'` it appends zero heights; `φ = * ∘ Λ²ι ∘ *⁻¹` (`complementIso`).

## Lemma checklist

All nine nodes are green, each pinned in `sec:pencil-d-stable` with its Lean names and hypotheses;
the chapter is the index (forward mode), and the file map is under *Current state*.

## Blockers / open questions

- None. The next sub-phase opens at the PI's word (*Hand-off*).

## Hand-off / next phase

Phase 42 continued with 42a, closed 2026-10-30 with SHORT-CORE's attack track (`notes/Phase42a.md`).
Which sub-phase opens next goes to the PI: PD-CARRIER / PD-STEPS / PD-COVERAGE (Phase 40's induction in
`Pᵈ` on R2's steps), PD-REDUCTION or PD-HEAD (design doc §3). What 42c leaves them: PD-COVERAGE
consumes `Graph.X0AttainsGrade.of_le` at `d′ = 3` with `lem:deficiency-stable`
(`def[6](G) = def[D](G)`); PD-HEAD rewrites `def_{d′} = def_d` into
`hasGradedPencilRealization_of_le`; a `P⁴` theorem (Tier 1) reaches every `d` at `def_2 ≤ 7` by
the same two lemmas at `d′ = 4`.

**Deferred from 42c, where they land** (design doc §3): FRICTION's moves of
`exteriorPower_map_normalsJoin` to `PanelLayer.lean` and of `BodyHingeFramework.map` with the
zero-hinge motion lemmas to `RigidityMatrix/Basic.lean` and `GenericityDevice.lean`, and FRICTION's
open `contragredientEquiv` in `Meet.lean`, each with the next commit that edits its file, under
PD-CARRIER / PD-STEPS / PD-COVERAGE; Tier 0's `formalization.yaml` row and its non-vacuity witness
at Phase 42's close, under PD-HEAD.

## Decisions made during this phase

- **The open** checked every statement against the definition bodies the nodes use; its
  corrections: item 2 needs `G` connected (two bodies, no edge: `def[15] = 15 ≠ 21 = def[21]`) and
  states the sharp range; the configuration form from `d′ = 2`; the statement form carries the
  adjacent-distinct case; item 3's realization step its own node.
- **All nine nodes in `pencil-d.tex`**, item 2 included, so `deficiency.tex` stays all green.
- **`def:pencil-d-embedding`:** `ι` extends by zero along `gradeEmbedIndex`; `φ` is the `∘ₗ`
  composite, rewritten by `screwEmbed_apply` (`rfl`), never `comp_apply` (FRICTION).
- **`lem:screw-embedding-rank`:** `Z(φF) = φ ∘ Z(F) ⊔ Z₀` with `⊓ = φ ∘ Z₀′`, not a complement;
  the bodies off `V(G)` cancel in the rank. Homes: FRICTION (open, *Hand-off*).
- **`lem:pencil-d-embed-config-rank`:** the configuration's framework *equals* the mapped one.
- **`lem:pencil-d-embed-realization` at a fixed deficiency parameter:** the Lean needs no deficiency
  equation; `def_{d′} = def_d` is the consumer's rewrite. A nonzero hinge is `C(w₁, w₂)`;
  `Embedding.lean` imports `Grade/Realization.lean` (no cycle).
- **No `main_results` row at this close:** an intermediate sub-phase close adds none (Phase 40's
  sub-phases added none), and a row needs a non-vacuity witness, a Lean change; tracked under
  PD-HEAD (design doc §3).
