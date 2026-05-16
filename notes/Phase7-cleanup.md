# Phase 7 cleanup round — work log

**Status:** in progress. Bucket A closed (A1 + A9 fixes; A2–A8/A10/A11
no-fix audits). Bucket B partial: B1 + B2 + B3 + B4 + B5 + B6 closed;
B3 landed via five commits (a/b/c/d/e). The audit found 6 of 8
`set_option linter.unused{Fintype,Decidable}InType false`
suppressions silenced advice already adopted as our resolved B2
style; the Zulip thread *Unused Decidable Instances linter*
confirmed the linter intent matches our DESIGN.md. B3a relaxed 3
TrivialMotions theorems; B3b/c dropped `[DecidableEq V]` from 3
Sparsity lemmas (IComponents + Augmentation); B3d cascaded the
`[Fintype V]` → `[Finite V]` relaxation across 16 rigidity-API
sites (Framework / HennebergRigidity / LamanTheorem); B3e
renamespaced 7 block decls from `IsSparse` to `SimpleGraph` so they
no longer require an unused sparsity hypothesis to enable dot
notation. Typeclass-shape design decision **resolved (follow
mathlib style: `[Finite V]` + inline bridge as idiom)**. Two
earlier resolution iterations ("uniform `[Fintype V]`", then per-
declaration "state at typeclass body uses") were considered and
reversed once the mathlib alignment became clear — the
`unusedFintypeInType` linter enforces the opposite direction of both
alternatives, and mathlib's own corpus follows the inline-bridge
pattern. B2 closes as no-change (audit confirms the existing project
pattern matches mathlib idiom). B5 closes similarly (the existing
`Set.ncard over Finset.card` convention is mathlib-aligned). B1
per-site vestigial check **closed**: 20 of 49 standalone `classical`
calls were vestigial and deleted (17 of 42 in project source + 3 of
7 in `Mathlib/` mirror); the remaining 29 are load-bearing (provide
`DecidableEq` for `Finset` ops / `Compl` / `rcases` on `Decidable`
data, or `DecidableRel G.Adj`). B4 `noncomputable def` audit
**closed**: 7 of 11 sites were vestigial and the keyword dropped (5
in `TrivialMotions.lean`, `countMatroid` in `CountMatroid.lean`, and
`SimpleGraph.rigidityMatroid` in `MatroidIdentification.lean`); the
4 forced sites reach `Real.instRCLike` via `innerSL` (3 in the
rigidity-row pipeline) or `Set.Finite.toFinset` (`maxBlock`). B6
`change` / `show` survey **closed**: 16 of 26 sites were vestigial
and refactored away (12 `change ⟪…⟫_ℝ = 0 at h…` lines in
HennebergRigidity collapsed into the preceding `simp only` via
`hp_ext_def, Option.elim_none, Option.elim_some`; 4 vestigial
`change Module.finrank … ≤ …` lines deleted; 2 `change … ; exact …`
pairs in Framework.lean collapsed to `simpa using key`; 1
`change … ; rw […]; exact …` 3-line block in Framework.lean
collapsed to a 1-liner via `kerEquiv.finrank_eq.le.trans`). The
remaining 10 sites are all load-bearing (term-mode `show … from
…` inside `simp` / `rw` arg lists; defeq unfolds in
RigidityMatroid.lean / MatroidIdentification.lean / Henneberg.lean;
one `change` in Framework.lean that bridges `IsInfinitesimallyRigid`
to its underlying `≤` for a downstream `omega`). Subsequent work
order: **B7 → C / D**.

This is the inter-phase cleanup round between Phase 7 and Phase 8.
See `../CLEANUP.md` for the round-level operating manual: when to
run a round, the three audit categories, and the per-round workflow.
The task list below is the round's "lemma checklist" equivalent —
populated up front so a session that runs out of time can hand off
cleanly.

## Current state

Bucket A closed. B1 + B2 + B3 + B4 + B5 + B6 closed. The B1 per-site audit
confirmed the design hypothesis: 29 of 49 `classical` sites
(~59%) are load-bearing in the expected mathlib-idiom way
(providing `DecidableEq` for `Finset` ops / `Compl` / `rcases`
on `Decidable` data, or `DecidableRel G.Adj`); the remaining 20
(~41%) were vestigial decorative calls whose bodies only touch
`Module`/`LinearMap`/`Set`/affine-span/polynomial APIs that
don't need decidability. All 20 vestigial sites deleted (17 in
project source + 3 in `Mathlib/` mirror); `lake build` and
`lake lint` pass clean. B3 closed (commits B3a–B3e):
the Zulip thread *Unused Decidable Instances linter* (channel
`mathlib4`, 2025-11-19 to 2026-03-18) confirmed the linter's intent
matches our resolved B2 mathlib-style design, and 6 of the 8
`set_option linter.* false` suppressions silenced advice we had
already adopted as our style. B3a relaxed 3 TrivialMotions theorems
to `[Finite V]` + body bridge. B3b/c dropped `[DecidableEq V]` from
3 Sparsity lemmas. B3e went past the original "keep with dot-
notation ergonomics" disposition for `IsSparse.HasBlock` /
`IsSparse.maxBlockSet`: per the user's observation that "it's
entirely possible to want to prove things about non-sparse edge sets
which contain blocks", moved 7 non-`hI`-using decls to bare
`SimpleGraph` and generalized the 2 retained `IsSparse` lemmas from
`(fromEdgeSet I)` to abstract `G`. B3d cascaded the
`[Fintype V]` → `[Finite V]` relaxation across 16 rigidity-API
sites (Framework / HennebergRigidity / LamanTheorem); the 4 sites
that legitimately use `Fintype.card V` in their conclusion stay at
`[Fintype V]`. B4 closed: 7 of 11 `noncomputable def` sites were
vestigial (5 in `TrivialMotions.lean` covering translations,
rotations, the span submodule, the elementary skew map, and the
joint family; plus `countMatroid` and `SimpleGraph.rigidityMatroid`);
the 4 forced sites all reach `Real.instRCLike` via `innerSL` (the
rigidity-row pipeline) or `Set.Finite.toFinset` (`maxBlock`). B6
closed: 16 of 26 `change` / `show` sites were vestigial; the 12
`change ⟪q - p ?, x.1 none - x.1 (some ?)⟫_ℝ = 0 at h…` lines that
unfolded `p_ext` through the `set p_ext := fun w => w.elim q p`
binding all collapsed into the preceding `simp only` by adding
`hp_ext_def, Option.elim_none, Option.elim_some` to the lemma list
(the standard TACTICS-QUIRKS § 6 `set name := fun … + simp [name]`
move); 4 `change Module.finrank ℝ (LinearMap.ker …) ≤ d * (d + 1) / 2`
goal-side unfolds of `IsInfinitesimallyRigid` were vestigial because
the followup `exact` typechecks against the `def` directly; two
Framework.lean `change … ; exact key` pairs collapsed to `simpa
using key`; one `change … ; rw […]; exact h` 3-line block became
`exact kerEquiv.finrank_eq.le.trans h`. Next concrete step: B7
(multi-step `rw [...]` chains) and/or C1 (top-10 long-proof
ranking).

Typeclass-shape design decision **resolved (follow mathlib style)**:
keep all `[Finite V]` signatures as-is; bridge inline in proof bodies
via `haveI : Fintype V := Fintype.ofFinite V` + `classical` when
`Fintype V`-strength data is needed. This is the canonical mathlib
idiom (enforced by the `unusedFintypeInType` env linter and visible
throughout mathlib's own corpus). The principle is *strongest
mathematical claim, maximum generality*: weaker hypothesis ⇒ more
general theorem.

Resolution arc: opened as an open *Choices to revisit* entry after
the B1+B2 sweeps surfaced 42+12 sites. First iteration proposed
uniform `[Fintype V]` (rejected after re-weighting the pebble-game
forward-compatibility argument). Second iteration proposed per-
declaration "state at typeclass body uses" with targeted lift of
10 (a)-style bridge sites (rejected after re-examining mathlib
style — the lift would *weaken* the 10 theorems' claims and
contradict the `unusedFintypeInType` linter). Settled on option 3:
follow mathlib idiom. The cleanup-round audit's value is
**verification that the project already matches mathlib style**;
no signature changes needed. Full discussion in `DESIGN.md`
*Typeclass shape for finiteness on `V`*; brief in `ROADMAP.md`
*Engineering conventions → Vertex types*.

B1 per-site vestigial-check **closed**. Of the 49 standalone
`classical` calls (42 in project source + 7 in `Mathlib/`
mirror), 20 (~41%) were vestigial and deleted, 29 (~59%)
confirmed load-bearing per the mathlib-idiom pattern. The 41%
vestigial fraction was higher than the pre-audit expectation
("most/all load-bearing"); see *Decisions made → B1* below for
the heuristic that emerged. Subsequent work order: B6 / B7 / C / D.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Bias: fix Lean first** for any blueprint/Lean divergence. Per
  `../blueprint/CLAUDE.md` *Proof verbosity*. The cleanup round
  records what was attempted on the Lean side before falling back
  to a prose aside.
- **Each fix as its own commit.** A cleanup commit obeys the same
  per-commit friction review and build/lint gates as a forward-work
  commit. The round's value is the trail of small principled
  commits, not a single mega-commit.
- **Sweep before fix, within each bucket.** Run the grep / walk for
  a category; record the task list; *then* start fixing. New tasks
  surfaced mid-fix are fine to append (with a one-liner about what
  exposed them), but the initial scope should be comprehensive.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit

One sub-task per chapter; each runs the audit of `\lean{...}`
statement-form match + prose-aside flag-finding + Lean-simplification
attempt for any flagged divergence.

- [x] A1: `chapter/intro.tex` (overview narrative; minimal `\lean{...}`
  surface — mostly sanity check that the phase plan still reads
  correctly post-Phase-7). Two stale claims fixed: "Phase 7 is in
  progress" → "All seven phases are complete", and "Phase 7 dep-graph
  still has red leaves" → narrowed to "main Laman line and through
  the Phase 7 matroid identification are all green" (honest about
  the single orphan `cor:isLaman-exists-rowIndependent`, since
  removed in A9).
- [x] A2: `chapter/sparsity.tex` ↔ `Sparsity.lean` + `EdgesIn.lean`.
  All 27 pinned declarations resolve. The Phase 7 additions
  `IsTightOn.union_with_bonus` and `IsTightOn.insert_vertex_with_edges`
  are described faithfully (chapter lines 432-440, 464-468); statement
  forms match the Lean hypotheses (`F ⊆ edgesIn (s ∪ t)`, disjointness,
  finite, the close-the-gap inequality). The `typeII_reverse_blocker`
  prose at lines 504-523 correctly flags the project-internal helper
  `image_edgesIn_comap` and its Sym2.map injectivity lift — the
  canonical *"named project-internal helper standing in for what the
  prose treats as a one-step correspondence"* aside from blueprint/
  CLAUDE.md *Proof verbosity*. Watch items in the original A2 task
  description (`IsTightOn.union_inter_of_pair`, the I-component prose,
  the `maxBlock` body-via-`Set.Finite.toFinset` discussion) were
  *misfiled*: all three pin in `count-matroid.tex` (A10), not
  `sparsity.tex`. The Set-vs-Finset maxBlock body is `DecidablePred`
  / type-class-elaboration friction (invisible to the math per
  blueprint/CLAUDE.md *Proof verbosity*: "Omit ... type-class
  elaboration") and is correctly elided in count-matroid.tex's prose.
  No fix required.
- [x] A3: `chapter/laman.tex` ↔ `Laman.lean`. Small chapter. Six
  pinned declarations all present in Laman.lean; statement forms
  (`IsLaman = IsTight 2 3` unfolds to "sparse + global tightness"),
  iso transport (specialisation of `IsTight.iso`), `K_2` base case,
  and the two degree lemmas all match the prose. No fix required.
- [x] A4: `chapter/henneberg.tex` ↔ `Henneberg.lean`. Phase 3 + Phase
  7 reflow (flat-form decomposition, public iso constructors). Watch
  for: blueprint statement-form aside that DESIGN.md *Statement-form
  conventions* now codifies; check the chapter wording still matches
  DESIGN.md's wording. All 12 pinned declarations resolve; statement
  forms (`typeI_edgeSet` via `Sym2.map some ''`, both preservation
  thms, `typeI_isLaman_iff`, the flat-form reverse decomposition with
  iso constructors `typeI_iso_of_two_neighbors` /
  `typeII_iso_of_three_neighbors`) match prose. Chapter's "flat /
  operation" wording (lines 14–21, 278–286) is consistent with
  DESIGN.md *Statement-form conventions*. Cross-refs to
  `sec:rigidity-matroid-lifts` and `sec:laman-theorem` resolve. No
  fix required.
- [x] A5: `chapter/frameworks.tex` ↔ `Framework.lean`. All 19 pinned
  declarations resolve (`Framework`, `Framework.finrank`,
  `RigidityMap`, `rigidityMap_apply`, the three `Is{Infinitesimally,
  Generically}Rigid{,Inj}` defs, the three mono / three iso / one
  eventually / range-le / ker-mono lemmas, `card_mul_le`, and the
  two `top_fin_two_*` worked examples). The `eventually` proof
  prose (basis of range → `Classical.choose` preimages → continuity
  → `LinearIndependent.eventually` → rank-nullity at both points)
  faithfully maps the Lean shape. `IsGenericallyRigidInj.toIs
  GenericallyRigid` (`Framework.lean`:294) is a trivial
  `And.proj`-via-`Exists.imp` accessor, justifiably skipped per
  blueprint *What to include vs. skip*. The original A5 watch item
  was misfiled: `exists_affinelySpanning_of_eventually` lives in
  `RigidityMatroid.lean` (Phase 7 generalisation) and is pinned by
  `lem:exists-affinelySpanning-of-eventually` in `laman-theorem.tex`
  (A8) and `rigidity-matroid.tex` (A9), not in `frameworks.tex`;
  the rename does match the blueprint label there. No fix required.
- [x] A6: `chapter/trivial-motions.tex` ↔ `TrivialMotions.lean`.
  Phase 6 milestone; check `elemSkewMap_ofLp_inr_apply` aside if any
  (the Commit 10 collapse from 6 lines to 1 is exactly the kind of
  "Lean now matches math" simplification we want — does the chapter
  reflect the simpler proof?). All 13 pinned declarations resolve.
  Chapter does not name `elemSkewMap_ofLp_inr_apply` (that helper is
  a Lean-internal coordinate accessor); the linear-independence proof
  prose is abstract enough that the Commit 10 collapse left no prose
  to update. No fix required.
- [x] A7: `chapter/henneberg-rigidity.tex` ↔ `HennebergRigidity.lean`.
  Five pinned declarations all resolve; rank-nullity / kernel-via-`some`
  proof prose matches the Lean shape; cross-refs to
  `lem:isInfinitesimallyRigid-eventually` (frameworks.tex) and
  `thm:top-fin-two-isGenericallyRigidInj` (frameworks.tex) resolve.
  No fix required.
- [x] A8: `chapter/laman-theorem.tex` ↔ `LamanTheorem.lean` +
  `RigidityMatroid.lean`. All 13 pinned declarations resolve (the
  four LamanTheorem.lean theorems + nine RigidityMatroid.lean
  declarations — `EdgeSetRowIndependent`, `rigidityRow`, the row
  span / iff-LI / rank-bound / basis-pick / affinely-spanning
  perturbation / row-independence-sparsity lemmas). The Phase 7
  inlined shape in `IsGenericallyRigid.exists_isLaman_le`
  (`LamanTheorem.lean`:151–185) is faithfully described by the
  chapter prose at lines 447–465: IR-witness extraction → `exists
  _affinelySpanning_of_eventually hp₀.eventually` → inline
  rank-nullity at the chosen `p` (the closed lemma `rigidityMap
  _finrank_range_ge_of_isGenericallyRigid` is cited with a
  "derived from IR at p via rank-nullity" parenthetical that
  honestly flags the unfold) → "placement-fixed companion of
  `lem:exists-rowIndependent-edge-basis`" (i.e. `exists_edgeSet
  RowIndependent_of_finrank_range_ge_dim_two` at
  `RigidityMatroid.lean`:252; the closed-form `_basis_dim_two`
  packages IR-extraction + companion, but the inlined caller wants
  IR + affine spanning at the *same* `p` and so calls the
  companion directly). No fix required.
- [x] A9: `chapter/rigidity-matroid.tex` ↔ `RigidityMatroid.lean` +
  `MatroidIdentification.lean`. All 12 pinned declarations resolve;
  statement forms (`IsSparse.exists_typeI_or_typeII_reverse` flat-form
  three-branch reverse; the typeI/pendant/typeII conditional cores
  and unconditional lifts; `EdgeSetRowIndependent.{eventually,iso}`;
  the hard direction `IsSparse.exists_rowIndependent_placement`; the
  full iff `edgeSet_rowIndependent_iff_isSparse_dim_two`; the matroid
  definition + Lovász–Yemini matroid-form iff) match the chapter
  prose; the typeII-lift parenthetical aside ("$p|_V$ agrees with
  $p'$ when non-collinear; otherwise perpendicular perturbation")
  honestly describes the internal proof choice without overselling
  the conclusion (Lean is just `∃ p, …`). One fix: materialised the
  previously orphan `cor:isLaman-exists-rowIndependent` as a Lean
  shim under `@[deprecated IsSparse.exists_rowIndependent_placement
  (since := "narrative-bridge")]` in `MatroidIdentification.lean`
  (a one-line composition `IsLaman.isSparse
  ∘ IsSparse.exists_rowIndependent_placement`). Investigation
  surfaced two design forks worth recording: (i) `private` would
  have broken `checkdecls` (kernel name becomes
  `_private.<file>.0.<name>`, not the natural name), so the
  `@[deprecated]` route is the only one that keeps the blueprint
  anchor resolvable while discouraging callsite use; (ii) the
  attribute-time warning emitted by Lean core when `since` is
  missing is unconditional (no `set_option` silences it — verified
  against `Lean/Linter/Deprecated.lean` line 44-45 in elan) and the
  mathlib `deprecatedNoSince` env-linter is a hard `lake lint`
  error, so `since` *must* be present. We picked the non-date
  sentinel `"narrative-bridge"` over a date because Lean's warning
  text says "date *or library version*" (version-shape is
  sanctioned) and mathlib's date-range cleanup tooling
  (`#clear_deprecations`) lex-compares `since` against `YYYY-MM-DD`
  bounds — `"narrative-bridge"` lex-compares above any realistic
  date bound, making the shim structurally invisible to accidental
  cleanup. The full pattern is documented in `blueprint/CLAUDE.md`
  *What to include vs. skip → Narrative-bridge corollaries* and
  cross-referenced from `CombinatorialRigidity/CLAUDE.md`
  *Engineering conventions*. Phase 7 dep-graph node for the
  corollary is now green; `lake build` and `lake lint` both pass
  silently.
- [x] A10: `chapter/count-matroid.tex` ↔ `CountMatroid.lean`. Newest;
  ~95 LoC of Lean, ~315 lines of TeX — check abstraction-level match.
  Eight pinned declarations resolve (most in `Sparsity.lean`,
  `countMatroid` + `countMatroid_indep_iff` in `CountMatroid.lean`).
  TeX verbosity-vs-LoC ratio is justified by the substantial
  exposition (Lee–Streinu/Whiteley/Jordán terminology cross-refs,
  upper-range aside, pebble-game pointer); the prose stays at the
  math abstraction level. Chapter's "definitional in Lean via
  `IndepMatroid.ofFinite_indep`" claim for `countMatroid_indep_iff`
  matches the Lean `Iff.rfl` body. No fix required.
- [x] A11: Ran `lake exe checkdecls blueprint/lean_decls` (after
  `inv web`) at end; confirmed every `\lean{...}` resolves. No fix required.

### Bucket B — Code-smell sweep

Each is a separate commit, root-cause fix preferred.

- [x] B1: `classical` audit (49 standalone-tactic sites; 42 in
  project source + 7 in `Mathlib/` mirror; grep:
  `^[[:space:]]*classical[[:space:]]*$`). **Result: 20 vestigial
  (deleted), 29 load-bearing (kept).** Per-site test was
  comment-out + `lake build`. Vestigial sites in project source:
  - `LamanTheorem.lean`:154 (`exists_isLaman_le`).
  - `Framework.lean`:131 (`rigidityMap_finrank_range_le`),
    242 (`IsInfinitesimallyRigid.eventually`).
  - `HennebergRigidity.lean`:131 (`typeI_isInfinitesimallyRigid_extend`),
    312 (`typeII_isInfinitesimallyRigid_extend`).
  - `Henneberg.lean`:211 (`typeI_edgesIn_ncard_decomp`),
    232 (`typeI_isLaman`),
    348 (`typeII_edgesIn_ncard_decomp`),
    374 (`typeII_isLaman`).
  - `RigidityMatroid.lean`:107 (`EdgeSetRowIndependent.iso`),
    160 (`EdgeSetRowIndependent.eventually`),
    258 (`exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`).
  - `MatroidIdentification.lean`:71 (`typeI_edgeSetRowIndependent_extend`),
    231 (`typeI_pendant_edgeSetRowIndependent_extend`),
    1035 (`edgeSet_rowIndependent_iff_isSparse_dim_two`),
    1116 (`IsLaman.exists_rowIndependent_placement` shim).
  - `Sparsity.lean`:1476 (`exists_aug_of_lt_two_mul`).

  Vestigial sites in `Mathlib/` mirror:
  - `Mathlib/Data/Set/Card.lean`:60 (`exists_injective_fin_of_le_ncard`).
  - `Mathlib/Data/Finset/Option.lean`:38 (`card_eraseNone_add_one_of_mem`).
  - `Mathlib/LinearAlgebra/Vandermonde.lean`:51 (`det_powerDifferences`).

  Load-bearing sites (29) provide `DecidableEq` (for `Finset` ops
  / `Compl` / `rcases` on `Decidable` data) or `DecidableRel G.Adj`.
  See *Decisions made → B1* below for the heuristic.
- [x] B2: `[Finite V] → Fintype` bridge audit (12 sites; grep:
  `letI|haveI` paired with `Fintype.ofFinite|Set.Finite.fintype`,
  plus 4 `have` variants the original sweep missed at
  `Sparsity.lean`:159/272, `Henneberg.lean`:233/375 — 10 V-level
  total). **Closed as no-change**: the resolved `DESIGN.md`
  *Typeclass shape for finiteness on `V`* convention is to follow
  mathlib style (state at weakest typeclass; bridge inline in
  proof body when stronger data is needed). The 10 V-level inline
  bridges + 6 G.edgeSet/I/b subtype-level bridges are all
  idiomatic mathlib and stay. The pebble-game-forward-compat
  argument was reweighted out; the per-decl "state at typeclass
  body uses" was rejected as anti-mathlib-style. Three
  sub-patterns surfaced in the sweep (recorded for reference):
  - **(a) Type-level `Fintype V` from `[Finite V]` (6 sites)** —
    candidate for "lift signature to `[Fintype V]`":
    - `Sparsity.lean`:1343 (`IsSparse.maxBlock_isTightOn`).
    - `Sparsity.lean`:1480 (`IsSparse.exists_aug_of_lt_two_mul`).
    - `MatroidIdentification.lean`:1036
      (`edgeSet_rowIndependent_iff_isSparse_dim_two`).
    - `MatroidIdentification.lean`:1117
      (`IsLaman.exists_rowIndependent_placement` — the A9
      narrative-bridge shim).
    - `RigidityMatroid.lean`:161 (`EdgeSetRowIndependent.eventually`).
    - `RigidityMatroid.lean`:370
      (`exists_affinelySpanning_of_eventually`).
  - **(b) Subtype `Fintype G.edgeSet` via `Set.Finite.fintype` (4
    sites)** — would *not* be eliminated by lifting `[Finite V] →
    [Fintype V]` since the bridge is for a specific subtype. Likely
    stay as-is; check whether a mathlib instance covers it:
    - `Framework.lean`:132 (`rigidityMap_finrank_range_le`).
    - `Framework.lean`:243 (`IsInfinitesimallyRigid.eventually`).
    - `RigidityMatroid.lean`:162 (`EdgeSetRowIndependent.eventually`).
    - `RigidityMatroid.lean`:259
      (`exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`).
  - **(c) Witness-level `Fintype` for a proof-local set (2 sites)**
    — same shape as (b) but the subtype is a proof-local witness
    (`I`, `b` for a basis-pick). Likely stay as-is:
    - `RigidityMatroid.lean`:163 (`EdgeSetRowIndependent.eventually`,
      `Fintype I` for the placement witness).
    - `RigidityMatroid.lean`:264
      (`exists_edgeSetRowIndependent_of_finrank_range_ge_dim_two`,
      `Fintype ↥b` for the basis).

  The fix pass starts with (a): for each declaration listed there,
  attempt to lift its `[Finite V]` hypothesis to `[Fintype V]` (plus
  `[DecidableEq V]` if the body uses `Finset V` operations) and
  delete the inline `haveI`. The expected secondary effect is that
  the declaration's `classical` (B1) becomes vestigial — verify and
  drop it in the same commit. Defer (b) / (c) until after (a) lands
  (and consider whether `Set.Finite.fintype` should be a project
  helper rather than an inline `haveI`).
- [x] B3: `@[nolint unusedArguments]` / `set_option linter.* false`
  audit. **Closed 2026-05-16.**
  Empirical test (temp-disable each override + `lake build` + `lake
  lint`) confirmed all 8 silenced rules still fire and all have
  multi-line "why" comments. But the Zulip discussion of the
  `unusedDecidableInType` / `unusedFintypeInType` linters (channel
  `mathlib4`, topic *Unused Decidable Instances linter*, 2025-11-19
  to 2026-03-18; ported from mathlib3's `decidable_classical` by
  Thomas Murrills) makes clear the linter's intent **exactly matches
  our resolved B2 mathlib-style design** — state at the weakest
  typeclass; bridge inline via `classical` / `Fintype.ofFinite` in
  the proof body. The 6 `set_option linter.* false` sites silence
  advice we have already adopted as our style, so they should be
  refactored rather than suppressed.

  The Mar-2026 Aaron Liu / Eric Wieser / Thomas Murrills exchange
  identifies one edge case where the linter's *suggested* fix
  breaks: when the consumed typeclass is needed *inside a proof-
  valued instance synthesised inside the type* (e.g., a
  `ContinuousSMul` shortcut instance missing for `[Finite ι]`-only
  inputs). The linter's diagnostic in that case reads "used in type,
  but only in a proof"; the fix is to add the missing shortcut
  instance, not to suppress. **Our 6 sites all carry the simpler
  message ("does not use the following hypothesis in its type")**,
  so they're not in this edge case — the standard refactor (loosen
  signature + body bridge) is appropriate. A `lake build` after each
  commit will catch the Aaron-Liu failure mode if it surfaces.

  Sites and dispositions:
  - **Refactor (6 sites, planned commits B3a/B3b/B3c):**
    - **B3a done.** `TrivialMotions.lean`:250, 321, 347
      (`set_option linter.unusedFintypeInType false`) — relaxed
      `[Fintype V]` → `[Finite V]` + body `haveI : Fintype V :=
      Fintype.ofFinite V`; deleted the three `set_option`s. Build
      + lint clean.
    - **B3b done.** `Sparsity.lean`:1275 (section `set_option
      linter.unusedDecidableInType false`) — affected
      `maxBlock_isTightOn` and `maxBlock_eq_of_subset_maxBlock`.
      Dropped `[DecidableEq V]` from both signatures;
      `maxBlock_isTightOn`'s body already had `classical` from the
      Phase 7 instance-friction resolution; added `classical` to
      `maxBlock_eq_of_subset_maxBlock`'s body. Deleted the section
      `set_option` and its justification comment. Build + lint clean.
    - **B3c done.** `Sparsity.lean`:1442 (section `set_option
      linter.unusedDecidableInType false`) — affected
      `exists_aug_of_lt_two_mul`. Dropped `[DecidableEq V]` from the
      Augmentation `section variable` (kept `[Finite V]`); added
      `classical` to `exists_aug_of_lt_two_mul`'s body alongside the
      existing `letI : Fintype V := Fintype.ofFinite V`. Deleted the
      section `set_option`. The two private auxiliaries
      (`ne_of_mem_top_edgeSet`, `edgeSet_fromEdgeSet_of_off_diag`)
      didn't depend on `DecidableEq V` (their types annotate
      `{V : Type*}` directly), so dropping the section variable left
      them unchanged. Build + lint clean.
  - **Renamespace (2 + 5 sites, B3e done).** Reconsidered the
    "keep with dot-notation ergonomics" disposition: per the user's
    observation *"it's entirely possible to want to prove things
    about non-sparse edge sets which contain blocks"*, the two `def`s
    `IsSparse.HasBlock` / `IsSparse.maxBlockSet` should be available
    without an `IsSparse` proof. Moved them — plus the 5 downstream
    lemmas (`maxBlockSet_finite`, `maxBlock`, `mem_maxBlock`,
    `subset_maxBlock`, `subset_maxBlock_of_hasBlock`) whose bodies
    don't use `hI` either — from `IsSparse` to `SimpleGraph`
    namespace, with `(G : SimpleGraph V) (k ℓ : ℕ)` made explicit.
    The two remaining IsSparse-namespaced lemmas
    (`maxBlock_isTightOn`, `maxBlock_eq_of_subset_maxBlock`) genuinely
    use `hI` and stayed under `IsSparse`, but were generalized from
    `(fromEdgeSet I)` to abstract `G : SimpleGraph V`. Deletes the
    two `@[nolint unusedArguments]` annotations. Updates
    `Sparsity.lean` module docstring, the IComponents/Augmentation
    section docstrings, the blueprint `\lean{}` pin in
    `count-matroid.tex`, and historical pointers in `FRICTION.md` /
    `TACTICS-QUIRKS.md`.
  - **B3d done.** `Framework.lean`:149 (`@[nolint unusedArguments]`
    on `IsInfinitesimallyRigid`) — env-linter override on the
    `[Fintype V]` contract guard. The Zulip discussion's "extend
    `unusedFintypeInType` to `noncomputable def`" improvement is
    planned-but-deferred (Thomas Murrills, Dec 2025), so for now
    this site is silenced via the env-linter, not via `set_option
    linter.unusedFintypeInType false`. Relaxed `[Fintype V]` →
    `[Finite V]` (still a meaningful contract guard); the
    `@[nolint unusedArguments]` stays as the explicit guard
    documentation, and the comment is updated to record the Zulip-
    informed rationale and migration path. Scope expanded to also
    relax all downstream theorems that picked up the resulting
    `unusedFintypeInType` cascade — 16 sites total relaxed from
    `[Fintype V]` (or `[Fintype V] [Fintype W]`) to `[Finite V]`
    (resp. both `[Finite V] [Finite W]`):
    - `Framework.lean` × 9: the two defs `IsInfinitesimallyRigid` /
      `IsGenericallyRigid`, the def `IsGenericallyRigidInj`, and
      the six theorems `{IsInfinitesimallyRigid,
      IsGenericallyRigid, IsGenericallyRigidInj}.mono`,
      `{IsInfinitesimallyRigid, IsGenericallyRigid,
      IsGenericallyRigidInj}.iso`, plus
      `IsInfinitesimallyRigid.eventually`, plus
      `IsGenericallyRigidInj.toIsGenericallyRigid`.
    - `HennebergRigidity.lean` × 6:
      `typeI_isInfinitesimallyRigid_extend`,
      `typeII_isInfinitesimallyRigid_extend`,
      `typeI_isGenericallyRigidInj_two`,
      `typeII_isGenericallyRigidInj_two_of_nonCollinear`,
      `exists_nonCollinear_rigid_placement_dim_two`,
      `typeII_isGenericallyRigidInj_two`.
    - `LamanTheorem.lean` × 1: `IsLaman.isGenericallyRigid_two`
      (also needed a body bridge `haveI : Fintype V :=
      Fintype.ofFinite V` + tactic-mode conversion to bridge to the
      `[Fintype V]`-typed `isGenericallyRigidInj_two_of_card`
      private induction helper that uses `Fintype.card V` in its
      type).
    The four theorems that legitimately use `Fintype.card V` in
    their conclusion type — `Framework.finrank`,
    `IsGenericallyRigid.card_mul_le`,
    `IsGenericallyRigid.card_mul_le_two`,
    `IsGenericallyRigid.exists_isLaman_le` /
    `isGenericallyRigid_two_iff_exists_isLaman_le` — keep their
    `[Fintype V]` signatures. `IsInfinitesimallyRigid.eventually`
    also picked up an in-body `haveI : Fintype V :=
    Fintype.ofFinite V` for its `Fintype G.edgeSet` bridge.
- [x] B4: `noncomputable def` audit. **7 of 11 sites were vestigial
  (deleted), 4 forced (kept).** Per-site test was drop the keyword +
  `lake build`. Vestigial sites:
  - `TrivialMotions.lean`:58 (`translationMotion` — `fun _ => t`).
  - `TrivialMotions.lean`:80 (`infinitesimalRotation` — `fun v => A
    (p v)`).
  - `TrivialMotions.lean`:110 (`trivialMotions` — `Submodule.span ℝ`
    over a `Set.range ∪ {…}`; `Submodule.span` is itself
    computable).
  - `TrivialMotions.lean`:149 (`elemSkewMap` — `LinearMap` from
    `PiLp.single`/smul/sub).
  - `TrivialMotions.lean`:227 (`trivialMotionFamily` — pattern match
    composing the two vestigial defs above).
  - `CountMatroid.lean`:61 (`countMatroid` — `IndepMatroid.ofFinite
    …).matroid`).
  - `MatroidIdentification.lean`:1083 (`SimpleGraph.rigidityMatroid`
    — transitively via `countMatroid`).

  Forced sites (kept `noncomputable`):
  - `Framework.lean`:70 (`edgeRow` — depends on `Real.instRCLike` via
    `innerSL ℝ`).
  - `Framework.lean`:92 (`RigidityMap` — transitively via `edgeRow`).
  - `RigidityMatroid.lean`:75 (`rigidityRow` — transitively via
    `RigidityMap`).
  - `Sparsity.lean`:1290 (`maxBlock` — depends on `Set.Finite.toFinset`).

  Heuristic that emerged: `noncomputable` is vestigial unless the
  body either (a) reaches `Real.instRCLike` (any inner-product /
  `innerSL ℝ` / `RCLike` arithmetic), or (b) reaches
  `Set.Finite.toFinset` (or another classical `Finset` extraction
  from a `Set`-side existence). `Submodule.span ℝ`,
  `IndepMatroid.ofFinite … .matroid`, `LinearMap` constructions
  over ℝ (without `innerSL`), and bare `fun`-formers all carry the
  keyword decoratively. The 64% vestigial fraction (7/11) mirrors
  the B1 surprise (41% vestigial `classical` calls) — both linters
  fire on a "this works without me" basis, so the resulting
  decoration accumulates silently.
- [x] B5: `Set` vs `Finset` consistency. **Closed as no-change**
  under the mathlib-style convention: the project's existing
  `Set.ncard over Finset.card` convention (cf. DESIGN.md) is
  already mathlib-aligned. `maxBlockSet : Set V` is the primary
  form; `maxBlock : Finset V` is the proof-internal companion
  needed for `Finset.sup_mem`. The `Set`-vs-`Finset` boundary at
  `EdgesIn.lean` / `Framework.lean` is at definition level (Set)
  vs. proof-internal level (Finset), which matches the principle
  of keeping definitions at the weakest typeclass and bridging
  inline in proofs. No round-tripping observed at audit-time.
- [x] B6: `change` / `show` survey. **16 of 26 sites vestigial
  (refactored), 10 load-bearing (kept).** The pre-audit expectation
  ("most load-bearing; looking for the 1-2 that aren't") was
  inverted — 62% were vestigial. Two distinct patterns drove the
  bulk:
  - **`set p_ext := fun w => w.elim q p` + chained `change` (12
    sites).** In `HennebergRigidity.lean` three blocks
    (`typeI_isInfinitesimallyRigid_extend` and the two halves of
    `typeII_isInfinitesimallyRigid_extend`), the `change ⟪q - p ?,
    x.1 none - x.1 (some ?)⟫_ℝ = 0 at hxa hxb hya hyb`-style
    four-up rewrite was just unfolding `p_ext` through its `set`
    binding. Adding `hp_ext_def, Option.elim_none, Option.elim_some`
    to the preceding `simp only` does the same job in one line. This
    is the textbook TACTICS-QUIRKS § 6 *`set name := fun … + simp
    [name]`* move; the friction was that the original Phase 5 code
    didn't follow it.
  - **Goal-side `change` of `IsInfinitesimallyRigid` (4 sites).**
    Since `IsInfinitesimallyRigid` is a `def`, the subsequent
    `exact` typechecks directly against the unfolded body — no
    explicit `change Module.finrank ℝ (LinearMap.ker …) ≤ d * (d +
    1) / 2` needed. 3 sites in `Framework.lean` (`IsInfinitesimallyRigid.iso`
    + `top_fin_two_isGenericallyRigid` `d = 0` branch) and 2 in
    `HennebergRigidity.lean` (the two `_extend` capstones); one
    Framework.lean `change … ; rw [kerEquiv.finrank_eq]; exact h`
    3-liner also folded to `exact kerEquiv.finrank_eq.le.trans h`.
  - **Two `change … ; exact key`-style pairs in Framework.lean's
    `IsInfinitesimallyRigid.iso`** collapsed to `simpa using key`
    once the prior `simp only [rigidityMap_apply, Pi.zero_apply]`
    was dropped (made redundant by `simpa`).

  Load-bearing sites (10) that stayed:
  - **Term-mode `show ... from ...` inside `simp` / `rw` arg lists
    (4 sites)**: HennebergRigidity.lean:357 (coerce
    `(typeII G a b c).Adj` to edge-set membership),
    HennebergRigidity.lean:545 and MatroidIdentification.lean:815
    (`show ... from by abel` glue),
    MatroidIdentification.lean:664 (`show ... from by abel` simp
    arg).
  - **Defeq unfolds in `RigidityMatroid.lean` (3 sites)**: line 89
    (`change LinearIndepOn ℝ (... LinearMap.ltoFun ...)` to set up
    `linearIndepOn_iff_of_injOn`), line 126 (`change G.RigidityMap
    …` to set up the next `rw [rigidityMap_apply ...]`), line 169
    (`change Continuous fun p => …` to unfold the `set M` for
    `fun_prop`).
  - **Defeq unfolds in `MatroidIdentification.lean` (1 site)**: line
    894 (`change Function.update p₀ a …` to unfold a `set p_t`
    let-binding).
  - **Defeq unfold in `Henneberg.lean` (1 site)**: line 597 (`change
    G'.Adj x y` to unfold `mem_edgeSet`; could equivalently be `rw
    [SimpleGraph.mem_edgeSet]` but the `change` form is shorter).
  - **One `change … ≤ …` bridge to `omega` in `Framework.lean` (1
    site)**: line 334 in `top_fin_two_isGenericallyRigidInj` — the
    omega step at line 356 needs the underlying `≤` form since
    `omega` cannot unfold `IsInfinitesimallyRigid`.

  Heuristic that emerged (worth a brief TACTICS-GOLF note): a
  goal-side `change` that unfolds a `def`-predicate (like
  `IsInfinitesimallyRigid`) is vestigial when the next tactic is
  `exact` — `exact` already unifies through the `def`. It is
  load-bearing when the next tactic is `omega` / `nlinarith` /
  `linarith`, which require ground-level `Nat`/`Int` shapes.
  Hypothesis-side `change at h` after a `set x := …` block can
  usually be folded into the preceding `simp only` via `[hx_def,
  ...]`.
- [ ] B7: Multi-step `rw [..., ..., ...]` chains. Same friction-review
  signal; look for fused-lemma candidates that warrant a
  `CombinatorialRigidity/Mathlib/<path>` mirror.

### Bucket C — Long-proof audit

- [ ] C1: Rank top ~10 proofs by body line count across all source
  files; record the ranked list in this log so subsequent sub-tasks
  can be filed concretely.
- [ ] C2: For each of the top 10: ask the four CLEANUP.md questions
  (API extraction / mathlib miss / tactic substitution / cross-proof
  unification). File any concrete improvement task as a follow-up
  sub-bullet here.
- [ ] C3: **Specific candidate — typeII conditional core unification**
  (Phase 7 *Blockers / open questions*, option 1). Extract the row
  identity
  `(s-1)·row newA - s·row newB = s(s-1) · restrictMap.dualMap (G'.rigidityRow ⟨s(a,b), h_ab⟩)`
  as a shared lemma in `Henneberg.lean`; both
  `typeII_isInfinitesimallyRigid_extend` (`HennebergRigidity.lean`)
  and `typeII_edgeSetRowIndependent_extend`
  (`MatroidIdentification.lean`) shrink by ~15 LoC. Apply same pattern
  to the typeI cores (simpler — no deleted row).
- [ ] C4: **Specific candidate — `IsSparse.exists_aug_of_lt_two_mul`**
  (Phase 7 Commit 17c). ~210 LoC. Walk the proof for API extraction
  candidates: the off-diag helpers `ne_of_mem_top_edgeSet` /
  `edgeSet_fromEdgeSet_of_off_diag` are already extracted; are there
  more sub-blocks that would be cleaner as named lemmas?

### Bucket D — Phase 7 notes compression

- [ ] D1: Lift cross-cutting lessons from `notes/Phase7.md`
  *Decisions made* to TACTICS-GOLF / TACTICS-QUIRKS / DESIGN.
  Candidates flagged by Phase 7's own "Promoted to …" subsection
  are already partially done; re-skim for residual entries that
  haven't been lifted yet.
- [ ] D2: Compress the *Multi-session plan* from a per-commit log
  to a brief summary + pointer to the blueprint dep-graph. The
  plan stopped being plan-relevant when Phase 7 closed.
- [ ] D3: Target: `notes/Phase7.md` ≤ 250 lines (currently 653).
  After D1/D2 plus removing redundant prose, check the line count;
  if still over budget, run a second compression pass.

## Decisions made during this round

*(Populated as the round runs; one entry per commit that closes a
checkbox.)*

### Phase-local choices and proof techniques

- **A1 — intro.tex re-statement after phase close.** Updated the
  *Phase plan* and *Reading this blueprint* prose to reflect Phase 7
  closed. Sweep also surfaced `cor:isLaman-exists-rowIndependent`
  as an orphan red node (no `\lean{...}`, no other `\uses{}` cite);
  filed under A9 rather than fixed here to keep A1 narrowly scoped.
- **A9 — rigidity-matroid.tex audit + narrative-bridge materialisation.**
  All 12 pinned declarations in `rigidity-matroid.tex` resolve to
  `RigidityMatroid.lean` / `MatroidIdentification.lean`, statement
  forms match the chapter, and the typeII-lift parenthetical aside
  honestly describes the internal proof's perturbation-via-openness
  choice. Materialised the previously orphan corollary
  `cor:isLaman-exists-rowIndependent` as a `@[deprecated]` Lean
  shim pointing at the general
  `IsSparse.exists_rowIndependent_placement` — preserves the
  narrative claim, mechanically verifies the prose against the
  general theorem, and discourages callsite proliferation via the
  deprecation warning. New pattern documented in
  `blueprint/CLAUDE.md` *What to include vs. skip → Narrative-bridge
  corollaries* with cross-reference from
  `CombinatorialRigidity/CLAUDE.md`. (Investigation history: removal
  was the first instinct; user pushed back on "narrative value vs
  maintenance"; `private` was floated and ruled out via empirical
  kernel-name probe — `private` decls become
  `_private.<file>.0.<name>`, breaking `checkdecls`'s `env.contains`
  resolution.)
- **A3 / A4 / A6 — no-divergence sweep.** Three small/medium chapters
  audited and recorded as [x] with no fix. Each chapter's
  `\lean{...}` pins all resolve, statement forms match the Lean,
  and proof prose stays at the math abstraction level (no leakage of
  internal helper names like `elemSkewMap_ofLp_inr_apply`).
  henneberg.tex's flat-form / iso-constructor wording is consistent
  with DESIGN.md *Statement-form conventions*.
- **A7 / A10 — second no-divergence sweep.** Two more medium
  chapters audited [x] with no fix. henneberg-rigidity.tex's
  rank-nullity prose matches the Lean's `ρ : ker … → ker …` shape;
  count-matroid.tex's higher TeX-to-Lean ratio is justified by the
  terminology / cross-reference exposition rather than overselling
  the formal content (the Lean's `Iff.rfl` definitional claim is
  honestly described).
- **A5 — frameworks.tex no-divergence sweep.** All 19 pinned
  declarations resolve in `Framework.lean`. `eventually` proof
  prose faithfully maps the Lean (`Classical.choose` preimages +
  `LinearIndependent.eventually`). Original A5 watch item misfiled
  (the `exists_affinelySpanning_of_eventually` rename is pinned by
  laman-theorem.tex / rigidity-matroid.tex, not frameworks.tex —
  defer to A8 / A9). `IsGenericallyRigidInj.toIsGenericallyRigid`
  is a trivial And-projection accessor, justifiably skipped.
- **A8 — laman-theorem.tex no-divergence sweep.** All 13 pinned
  declarations resolve (across `LamanTheorem.lean` +
  `RigidityMatroid.lean`). The Phase 7 inlining of the IR witness
  in `IsGenericallyRigid.exists_isLaman_le` matches the chapter
  prose: IR-extraction → affinely-spanning perturbation → inline
  rank-nullity → "placement-fixed companion" of the closed
  basis-pick lemma. The chapter's "placement-fixed companion"
  hint is the canonical "named project-internal helper standing
  in for what the prose treats as a one-step correspondence"
  aside from blueprint/CLAUDE.md *Proof verbosity*.
- **B6 — `change` / `show` survey + 16-site cleanup.** Audit found
  16 of 26 sites vestigial (62%); fix landed in one commit across
  `Framework.lean` (4 sites) and `HennebergRigidity.lean` (12
  sites). Two textbook patterns drove the bulk: (i) `change ⟪…⟫ = 0
  at h…` chains unfolding a `set p_ext := fun w => w.elim q p`
  binding folded back into the preceding `simp only` via
  `[hp_ext_def, Option.elim_none, Option.elim_some]` (the
  TACTICS-QUIRKS § 6 *`set name := fun … + simp [name]`* move
  applied four-up); (ii) goal-side `change Module.finrank ℝ … ≤ d *
  (d + 1) / 2` lines unfolding `IsInfinitesimallyRigid` were
  vestigial when followed by `exact` (`exact` unifies through
  `def`-unfolding) but load-bearing when followed by `omega` (which
  needs a ground-level `Nat` shape). Two `change … ; exact key`
  pairs in `IsInfinitesimallyRigid.iso` also folded to `simpa using
  key`, with the pre-existing `simp only [rigidityMap_apply,
  Pi.zero_apply] at key` dropped as redundant. Heuristic: a
  goal-side `change` of a `def`-predicate is vestigial iff the next
  tactic is `exact`. The 10 remaining sites are load-bearing
  (term-mode `show ... from ...` glue, definitional unfolds of `set
  M`-style let-bindings before `fun_prop` / `rw`, one `change G'.Adj
  x y` stylistic equivalent of `rw [SimpleGraph.mem_edgeSet]`).

- **B4 — `noncomputable def` audit + 7-site cleanup.** 7 of 11
  `noncomputable def` sites in the project were vestigial: 5 in
  `TrivialMotions.lean` (`translationMotion`, `infinitesimalRotation`,
  `trivialMotions`, `elemSkewMap`, `trivialMotionFamily`), plus
  `countMatroid` in `CountMatroid.lean` and `SimpleGraph.rigidityMatroid`
  in `MatroidIdentification.lean`. The 4 forced sites partition into
  two causes: `Real.instRCLike` reached through `innerSL ℝ` (the
  `edgeRow` → `RigidityMap` → `rigidityRow` chain) and
  `Set.Finite.toFinset` (`maxBlock`). Heuristic recorded in the B4
  checkbox: `noncomputable` is vestigial unless the body reaches
  `Real.instRCLike` (via `innerSL ℝ` / inner-product arithmetic over
  ℝ) or a `Set.Finite.toFinset`-style classical `Finset` extraction;
  `Submodule.span ℝ`, `IndepMatroid.ofFinite … .matroid`, and
  `LinearMap` constructions over ℝ that don't pass through `innerSL`
  are all computable. Left in cleanup-notes rather than promoted to
  TACTICS-GOLF — applies only at definition-writing time, which is
  uncommon; revisit if a future phase adds enough new `def`s that
  the rule starts being re-derived. Both forced-site elimination
  paths (`maxBlock` → pebble game; rigidity-row pipeline →
  field generalization) are deferred and recorded under
  *Blockers / open questions*.

- **B3 — `@[nolint]` / `set_option linter.* false` audit + refactor
  plan.** Empirical test (temp-disable each + `lake build` / `lake
  lint`) confirms all 8 silenced rules still fire. But the
  contemporary Zulip discussion of `unusedDecidableInType` /
  `unusedFintypeInType` (channel `mathlib4`, topic *Unused
  Decidable Instances linter*, ported by Thomas Murrills from
  mathlib3's `decidable_classical`) shows the linter is the
  enforcement arm of *exactly* our resolved B2 mathlib-style design.
  The Mar-2026 Aaron Liu / Eric Wieser / Thomas Murrills exchange
  identifies one edge case ("used in type, but only in a proof" —
  proof-valued typeclass synthesised inside the type) where the
  linter's suggested replacement breaks; none of our 6 sites carry
  that diagnostic ("does not use the following hypothesis in its
  type"), so the standard refactor is appropriate. Disposition: 6
  `set_option linter.* false` sites refactor to signature-loosen +
  body-bridge (commits B3a–B3c); 2 `@[nolint unusedArguments]`
  sites in `Sparsity.lean` stay (dot-notation ergonomics); 1
  borderline `@[nolint unusedArguments]` in `Framework.lean`
  (`IsInfinitesimallyRigid`) relaxes `[Fintype V]` → `[Finite V]`
  while keeping the env-linter override as the contract-guard
  rationale, pending the upstream syntax linter's planned extension
  to `def`s (B3d).

- **A2 — sparsity.tex no-divergence sweep.** All 27 pinned
  declarations resolve to `Sparsity.lean` / `EdgesIn.lean`. Phase 7
  additions (`IsTightOn.union_with_bonus`,
  `IsTightOn.insert_vertex_with_edges`) match the chapter's
  `F`-anchored phrasings. `typeII_reverse_blocker`'s prose at
  lines 504-523 correctly flags the `image_edgesIn_comap`
  project-internal helper + its Sym2.map injectivity lift — the
  same *"named project-internal helper standing in for ..."* aside
  pattern as A8. The original A2 watch list (`union_inter_of_pair`,
  I-component prose, `maxBlock` body-via-`Set.Finite.toFinset`) was
  misfiled — all three pin in `count-matroid.tex` (A10), not here;
  the `Set.Finite.toFinset` body is `DecidablePred` /
  type-class-elaboration friction (per blueprint/CLAUDE.md *Proof
  verbosity*: omit type-class elaboration) and correctly elided in
  the chapter prose.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *B1 / B2 / B5 share one root cause: the project's heterogeneous
  typeclass shape for finiteness on `V`. Resolved (follow mathlib
  style: `[Finite V]` + inline bridge as idiom).* → `DESIGN.md`
  *Typeclass shape for finiteness on `V`* + `ROADMAP.md`
  *Engineering conventions → Vertex types*. Two earlier iterations
  ("uniform `[Fintype V]`", then per-declaration "state at
  typeclass body uses") were considered and reversed; the third
  iteration matches mathlib style (enforced by the
  `unusedFintypeInType` env linter). B2 + B5 closed as no-change;
  B1 closed with 17 vestigial deletions + 25 load-bearing kept.

- **B1 audit heuristic (decorative-`classical` indicator).** A
  standalone `classical` in a proof body is vestigial iff the body
  touches only `Module` / `LinearMap` / `Set` / affine-span /
  topology / polynomial APIs (no `Finset` ops, no `Compl`, no
  `rcases` / `by_cases` on `Decidable` data, no `DecidableRel G.Adj`
  -needing graph-degree work). Where the body uses
  `Set.Finite.fintype` to bridge to a subtype-level `Fintype
  G.edgeSet`, the bridge is classical-internal and an outer
  `classical` is redundant. This matches mathlib's idiom:
  `classical` is reserved for proofs that actually need
  `Decidable` data, not as decorative scaffolding. 20 of 49
  audited sites (~41%) fit the vestigial pattern — a higher
  fraction than expected pre-audit. Worth a brief note in
  `TACTICS-GOLF.md` for future Lean writing.

### Cleanup pass summaries

## Blockers / open questions

- **B4 forced-`noncomputable` follow-ups (deferred).** The 4 forced
  sites partition into two elimination paths, neither pursued this
  round:
  - **`maxBlock` (`Sparsity.lean`:1290)** — forced via
    `Set.Finite.toFinset` (`Classical.choice` on the `Set.Finite`
    witness). A computable refactor to `(Finset.univ.powerset.filter
    (fun S => G.IsTightOn k ℓ S ∧ X ⊆ S)).biUnion id` form requires
    strengthening the hypothesis from `[Finite V]` to `[Fintype V]
    [DecidableEq V]`, which cascades to 5 lemmas that mention
    `maxBlock` in their statement (`mem_maxBlock`, `subset_maxBlock`,
    `subset_maxBlock_of_hasBlock`, `IsSparse.maxBlock_isTightOn`,
    `IsSparse.maxBlock_eq_of_subset_maxBlock`) — partial revert of
    B3b/B3c. Deferred in favour of the **pebble game** (Jacobs–
    Hendrickson 1997 / Lee–Streinu 2008): the directed pebble graph's
    reverse-reachability set from `X` is exactly `maxBlock X`, gives
    a polynomial-time algorithm rather than the powerset-filter
    brute force, and gives `Decidable (IsSparse G k ℓ)` /
    `Decidable (G.HasBlock k ℓ X)` as side benefits. Pebble-game
    formalization is on the forward-work radar (cf. `count-matroid.tex`
    Lee–Streinu pointer).
  - **`edgeRow` / `RigidityMap` / `rigidityRow`** — forced via
    `Real.instRCLike` reached through `innerSL ℝ`. Path: generalize
    the rigidity construction from "ℝ with inner product" to
    "arbitrary field with non-degenerate symmetric bilinear form"
    (Lovász–Yemini's matroid identification holds over any infinite
    field). The abstract definition would be computable; concrete
    ℝ-specialization sites would still carry the keyword. Cost: a
    substantial `Framework` / `TrivialMotions` / `RigidityMatroid`
    refactor (plus replacing the analytic genericity argument in
    `IsInfinitesimallyRigid.eventually` with Zariski genericity).
    Worth doing if/when the project aims at the matroid-identification
    result over arbitrary infinite fields; not worth doing solely to
    drop 3 `noncomputable` keywords on definitions that are never
    executed. Deferred to a later session.

## Hand-off / next phase

*(Populated when the round closes; expected handoff is "Phase 8 can
start; carry-over items if any are noted here.")*
