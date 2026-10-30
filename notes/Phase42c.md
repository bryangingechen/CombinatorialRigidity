# Phase 42c — PD-STABLE: the pencil from a lower dimension (work log)

**Status:** in progress, opened 2026-10-30 by the PI (design doc §3's scope as written), a
sub-phase of Phase 42 beside 42a. Forward mode, the Lean under `/coordinate-phase`: the dep-graph
is `blueprint/src/chapter/pencil-d.tex` §`sec:pencil-d-stable`, 9 nodes, 8 green (`thm:pencil-d-deficiency-two-le-three`, `lem:deficiency-stable`, `def:pencil-d-embedding`,
`lem:pencil-d-embedding-join`, `lem:pencil-d-x0-attains-distinct`, `lem:screw-embedding-rank`,
`lem:pencil-d-embed-config-rank`, `lem:pencil-d-x0-attains-of-le`), 1 red (`lem:pencil-d-embed-realization`).
The open corrected the deficiency lemma (it needs `G` connected) and found its proof gives a
sharper range; the PI widened the theorem to `def_2 ≤ 3` (*Architectural choices*). Next concrete task: `lem:pencil-d-embed-realization`, the last red node.

## Current state

**Next:** `lem:pencil-d-embed-realization`, the last red node; its close fires the phase-close checklist.

**Landed (latest):** `thm:pencil-d-deficiency-two-le-three` (green, one commit): new file
`Pencil/Grade/Stable.lean` with `Graph.x0AttainsGrade_of_deficiency_two_le_three` (dimension three by
`Graph.IsX0Graph.x0Attains`, `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le` at
`n' = 3`, then `Graph.X0AttainsGrade.of_le`) and the realization form. Before it: `lem:pencil-d-x0-attains-of-le` (green, one commit): `Graph.X0AttainsGrade.of_le`
in `Pencil/Grade/ZeroHeights.lean`, which now imports `Grade/Witness.lean`; `hloop` is `⟨fun e v hl =>
hadm.1 e v v hl rfl⟩`, the arithmetic closes by `rw` then `ring`. Before it: `lem:pencil-d-embed-config-rank` (green, one commit), new file
`Pencil/Grade/ZeroHeights.lean` (over `Grade/Carrier.lean` and `Grade/Embedding.lean`): `padHeights`
(zero heights appended; no `m' ≤ m` argument, which the linter would flag unused),
`pencilConfigPointGrade_padHeights` (`ι` of the point, by `Fin.cases` on the index), the rank in `ℤ`
(the framework is `(q, z')`'s `.map (screwEmbed _)`, by `simp only` on the two fields), and
`Graph.padHeights_mem_liftingSpaceGrade`.

**Landed:** `lem:screw-embedding-rank` (green, one commit), in `Pencil/Grade/Embedding.lean`,
which now also imports `GenericityDevice.lean`: `BodyHingeFramework.map` (any linear `φ`,
grade-changing), the motion count `finrank_infinitesimalMotions_map_injective` (in `ℕ`) and the rank
form above (in `ℤ`, as `HasGradedPencilRealization` states its rank), with two zero-hinge helpers
(*Decisions*).

**Landed:** `lem:pencil-d-x0-attains-distinct`, `Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`
(`Pencil/Grade/Configuration.lean`), the grade form of `Graph.X0Attains.hasDistinctPencilRealization`.

**Landed:** `def:pencil-d-embedding` and `lem:pencil-d-embedding-join` (green), new file
`Pencil/Grade/Embedding.lean`: `gradeEmbed` (`ι`), `screwEmbed` (`φ`), their injectivity, `ι`'s
coordinates, `screwEmbed_apply` (*Decisions*), `exteriorPower_map_normalsJoin` (any linear `f`; its
natural home is `PanelLayer.lean`, the move deferred, FRICTION) and `screwEmbed_panelSupportExtensor`.

**Landed:** `lem:deficiency-stable` (green): `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`
(the sharp range, the scratch proof transcribed unchanged but for restoring `deficiency_nonneg n`,
needed by the cyclic arm) and `Graph.Connected.deficiency_eq_of_two_add_deficiency_two_le`
(§3's form, via `bodyBarDim n' ≥ n' + 1`, as `Nat.le_div_iff_mul_le` plus `nlinarith`).

**Landed (the open):** the section `sec:pencil-d-stable`, its nodes red with planned names
(*Lemma checklist*); the statement checks against the definition bodies (*Decisions*); the
counterexample to §3's "every multigraph", witnessed in `lake lean` (scratch, not retained). No
Lean.

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

Planned `\lean{...}` names (namespace `CombinatorialRigidity.Molecular` unless `Graph.`); a builder
may refine a name, and the pin lands with the Lean.

- [x] `lem:deficiency-stable` — `Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`,
  `Graph.Connected.deficiency_eq_of_two_add_deficiency_two_le`
- [x] `def:pencil-d-embedding` — `gradeEmbed` (`ι`, for `k' ≤ k`), `screwEmbed` (`φ`),
  `gradeEmbed_injective`, `screwEmbed_injective` (`exteriorPower.map_injective_field`)
- [x] `lem:pencil-d-embedding-join` — `exteriorPower_map_normalsJoin` (FRICTION; in `Embedding.lean`),
  `screwEmbed_panelSupportExtensor`
- [x] `lem:screw-embedding-rank` — `BodyHingeFramework.map` (hinges `φ C_e`, grade-changing),
  `BodyHingeFramework.finrank_span_rigidityRows_map_injective` (`G` connected, `[Finite α]`),
  `BodyHingeFramework.finrank_infinitesimalMotions_map_injective`
- [ ] `lem:pencil-d-embed-realization` — `HasPencilPlaneRealization.map_gradeEmbed`,
  `hasGradedPencilRealization_of_le`, `hasGradedDistinctPencilRealization_of_le`
- [x] `lem:pencil-d-embed-config-rank` — `padHeights`, `pencilConfigPointGrade_padHeights` (`ι` of
  the point), `Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights`
  (`G` connected, `[Finite α]`), `Graph.padHeights_mem_liftingSpaceGrade`
- [x] `lem:pencil-d-x0-attains-of-le` — `Graph.X0AttainsGrade.of_le` (`[Infinite K]`, `G` connected,
  `G.deficiency (m' + 2) = G.deficiency (m + 2)`)
- [x] `lem:pencil-d-x0-attains-distinct` — `Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`
- [x] `thm:pencil-d-deficiency-two-le-three` — `Graph.x0AttainsGrade_of_deficiency_two_le_three`,
  `Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three` (`G.IsX0Graph`, `1 ≤ m`)

## Blockers / open questions

- **(b) resolved (2026-10-30):** the surfaces resting on Result 16's old form are restated (Strata Results 15–17 and 22, design doc §1/§2.5/§3/§4, ROADMAP §42): content range `def_3 ≥ C(d,2) − 2`, Tier 1 reach `def_3 ≤ 7`. SHORT-CORE's review 2 (workbook S50, branch `attack-short-core`, commit `38f41bf9`, not on master): its scope is unchanged at `d = 4` and `def_3 ≥ 2d − 3` at every danger cell. `strata.py`'s filters keep the old, wider range.

## Hand-off / next phase

The next commit is `lem:pencil-d-embed-realization` (*Current state*), the last red node; it closes
the phase, so the phase-close checklist fires on it.

## Decisions made during this phase

- **The open (2026-10-30), checked against the bodies:** `partitionDef`/`deficiency`,
  `HasPencilPlaneRealization` (with `HasCoplanarPanelRealization`, `ExtensorInPanel`,
  `ExtensorThroughSubspace`), `HasGraded(Distinct)PencilRealization`, `X0AttainsGrade`,
  `pencilConfigPointGrade`, `IsAdmissiblePicture`, `infinitesimalMotions`, `panelSupportExtensor`,
  `complementIso`. Each node's statement and proof hold against them (the rank form counts the
  bodies outside `V(G)` too); `exteriorPower.map_injective_field` gives `Λ²ι` injective.
- **Statement corrections at the open** (transcriptions, for the pre-build guard): (1) item 2
  needs `G` connected: two bodies and no edge have `def_n = bodyBarDim n`, so `def[3] = 3`,
  `d′ = 5`, yet `def[15] = 15 ≠ 21 = def[21]` (the coordinator's, by hand; `lake lean` witness);
  (2) item 2 states the sharp range, §3's form its "in particular" (Strata Result 16); (3) the
  configuration form at `2 ≤ d′`, not `3 ≤ d′` (no step uses a height); (4) the statement form
  carries the adjacent-distinct case; (5) item 3 split, `lem:pencil-d-x0-attains-distinct` (the
  every-`d` form of `lem:pencil-x0-attains-distinct`) its own node, on `thm:pencil-x0-coverage`.
- **All nine nodes in `pencil-d.tex`**, item 2 included: the red frontier stays in one section,
  and `deficiency.tex`, all green, stays so for `intro.tex`'s status sentence.
- **`def:pencil-d-embedding`:** `ι` extends by zero (`Function.ExtendByZero.linearMap`) along
  `gradeEmbedIndex` (last to last, `Fin.castLE` elsewhere), the coordinator's hypothesis, checked.
  Its coordinates `gradeEmbed_apply_castLE`, `_eq_zero` (value bounds, for `omega`) and `_last` are
  what `pencilConfigPointGrade_padHeights` will case on. `φ` is the `∘ₗ` composite through
  `complementIso (j := 2)` at both grades, cast as `panelSupportExtensor` is; rewrite it by
  `screwEmbed_apply` (`rfl`), never `comp_apply` (FRICTION). The Lean holds at every `k' ≤ k`: the
  node's `2 ≤ d'` is the section's range, not a hypothesis.
- **`lem:screw-embedding-rank`:** the route is `Z(φF) = φ ∘ Z(F) ⊔ Z₀`, `⊓ = φ ∘ Z₀′`, with `Z₀`,
  `Z₀′` the motions of the zero-hinge frameworks (`finrank_sup_add_finrank_inf_eq`), not the
  blueprint's complement `T`: the constant-on-`V(G)` count is then the existing
  `finrank_infinitesimalMotions_of_isInfinitesimallyRigidOn_vertexSet`. The carrier's bodies off
  `V(G)` add `(D − D′)` each to the motion count and cancel in the rank; the blueprint proof now
  counts them (`B ⊇ V(G)`). `map` and the zero-hinge helpers sit in `Embedding.lean`; their natural
  home is upstream (FRICTION).
- **`lem:pencil-d-embed-config-rank`:** home `Pencil/Grade/ZeroHeights.lean`, a sibling, as
  `Embedding.lean`'s imports do not reach `Grade/Carrier.lean`; `padHeights` takes no `m' ≤ m` (the
  lemmas do). The configuration's framework *equals* the mapped one (both fields agree everywhere),
  so no transfer at links was needed. Friction: FRICTION's `gradeEmbed` index-form idiom.
