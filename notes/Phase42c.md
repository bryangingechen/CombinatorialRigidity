# Phase 42c — PD-STABLE: the pencil from a lower dimension (work log)

**Status:** in progress, opened 2026-10-30 by the PI (design doc §3's scope as written), a
sub-phase of Phase 42 beside 42a. Forward mode, the Lean under `/coordinate-phase`: the dep-graph
is `blueprint/src/chapter/pencil-d.tex` §`sec:pencil-d-stable`, 9 nodes, 1 green (`lem:deficiency-stable`), 8 red.
The open corrected the deficiency lemma (it needs `G` connected) and found its proof gives a
sharper range; the PI widened the theorem to `def_2 ≤ 3` (*Architectural choices*). `lem:deficiency-stable` landed (the sharp form and §3's form, `Deficiency.lean`). Next concrete task: `def:pencil-d-embedding`.

## Current state

**Next:** `def:pencil-d-embedding` (`gradeEmbed`, `screwEmbed` and their injectivity), a leaf; then
`lem:screw-embedding-rank` and `lem:pencil-d-x0-attains-distinct` (*Lemma checklist*).

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
  "The open found the deficiency lemma's own proof gives a sharper range. On a connected G, def at
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
- [ ] `def:pencil-d-embedding` (**next**) — `gradeEmbed` (`ι`, for `k' ≤ k`), `screwEmbed` (`φ`),
  `gradeEmbed_injective`, `screwEmbed_injective` (`exteriorPower.map_injective_field`)
- [ ] `lem:pencil-d-embedding-join` — `exteriorPower_map_normalsJoin` (FRICTION),
  `screwEmbed_panelSupportExtensor`
- [ ] `lem:screw-embedding-rank` — `BodyHingeFramework.map` (hinges `φ C_e`, grade-changing),
  `BodyHingeFramework.finrank_span_rigidityRows_map_injective` (`G` connected, `[Finite α]`)
- [ ] `lem:pencil-d-embed-realization` — `HasPencilPlaneRealization.map_gradeEmbed`,
  `hasGradedPencilRealization_of_le`, `hasGradedDistinctPencilRealization_of_le`
- [ ] `lem:pencil-d-embed-config-rank` — `pencilConfigPointGrade_padHeights` (`ι` of the point),
  `Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights`,
  `Graph.padHeights_mem_liftingSpaceGrade`
- [ ] `lem:pencil-d-x0-attains-of-le` — `Graph.X0AttainsGrade.of_le` (`[Infinite K]`, `G` connected,
  `G.deficiency (m' + 2) = G.deficiency (m + 2)`)
- [ ] `lem:pencil-d-x0-attains-distinct` — `Graph.X0AttainsGrade.hasGradedDistinctPencilRealization`
- [ ] `thm:pencil-d-deficiency-two-le-three` — `Graph.x0AttainsGrade_of_deficiency_two_le_three`,
  `Graph.hasGradedDistinctPencilRealization_of_deficiency_two_le_three` (`G.IsX0Graph`, `1 ≤ m`)

## Blockers / open questions

- **(b), for the PI, relayed to the SHORT-CORE attack track (not blocking):** the sharp deficiency
  range `def[3] + 3 ≤ D′` (tight on cycles: `C₇` has `def[3] = 4`, `def[6] = 1`, `def[10] = 0`)
  also moves design doc §2.5's content range and §1's tiers, which rest on Result 16's form: `G`
  attains at `d` from `P^{d−1}` once `def[3] + 3 ≤ D_{d−1}`, so the content at `d = 4` starts at
  `def[3] ≥ 4` (not `≥ 2`), and a `P⁴` theorem gives every `d` at `def[3] ≤ 7` (not `≤ 2`). These
  are 42a's notes, which that attack track's worktree keeps its own copies of; untouched here.

## Hand-off / next phase

The next commit is `def:pencil-d-embedding` (*Current state*). The other leaves are
`lem:screw-embedding-rank` and `lem:pencil-d-x0-attains-distinct`; then `lem:pencil-d-embedding-join` (with FRICTION's
`normalsJoin` map lemma), the statement and configuration forms, `lem:pencil-d-x0-attains-of-le`,
and the theorem last, at `def_2 ≤ 3` (the PI's widening from `≤ 1`, *Architectural choices*).

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
  (2) item 2 states the sharp range, §3's form its "in particular" (*Blockers*); (3) the
  configuration form at `2 ≤ d′`, not `3 ≤ d′` (no step uses a height); (4) the statement form
  carries the adjacent-distinct case; (5) item 3 split, `lem:pencil-d-x0-attains-distinct` (the
  every-`d` form of `lem:pencil-x0-attains-distinct`) its own node, on `thm:pencil-x0-coverage`.
- **All nine nodes in `pencil-d.tex`**, item 2 included: the red frontier stays in one section,
  and `deficiency.tex`, all green, stays so for `intro.tex`'s status sentence.
