# Phase 7 cleanup round — work log

**Status:** in progress. Bucket A closed (A1 + A9 fixes; A2–A8/A10/A11
no-fix audits). Bucket B **closed** (B1–B7); B7 landed via four
commits (a/b/c/d). The audit found 6 of 8
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
to its underlying `≤` for a downstream `omega`). B7 `rw`-chain audit
**closed**: 4 of 64 chains were vestigial (1 mirror lemma, 1 simp
collapse, 1 project-internal helper, 1 duplicate b-branch simp
collapse); the remaining 60 do per-step substitution + arithmetic
that doesn't fit either heuristic (verbatim cross-site repeat ⇒
mirror; arithmetic tail in default simp set ⇒ simp). C1 closed
2026-05-16: top 10 by body LoC range 322 → 87 LoC, headed by the
typeI / typeII row-LI / IR extends quartet that C3 already targets.
C3 closed 2026-05-16: extracted `typeII_collinear_inner_combo` row
identity in `HennebergRigidity.lean`; the IR-side
`typeII_isInfinitesimallyRigid_extend` shrank 92 → 77 body LoC, the
row-LI-side `typeII_edgeSetRowIndependent_extend` shrank 322 → 313.
C2 closed 2026-05-16: four-question walk over the C1 top-10 sites
recorded (notes-only, no Lean changes). Highest-leverage finding is
the **lift+restrict+factor+oldSet-LI pattern** shared verbatim across
#1 / #4 / #7 / #10 (~80-100 LoC compound savings); seven follow-up
extraction candidates filed as Phase 8 warm-ups. Subsequent work
order: **C4 (focused `exists_aug_of_lt_two_mul` walk) → D**.

This is the inter-phase cleanup round between Phase 7 and Phase 8.
See `../CLEANUP.md` for the round-level operating manual: when to
run a round, the three audit categories, and the per-round workflow.
The task list below is the round's "lemma checklist" equivalent —
populated up front so a session that runs out of time can hand off
cleanly.

## Current state

Bucket A closed. Bucket B closed (B1–B7). The B1 per-site audit
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
`exact kerEquiv.finrank_eq.le.trans h`. B7 (multi-step `rw [...]`
chains) closed via 4 commits (a/b/c/d); C1 (top-10 long-proof
ranking) recorded 2026-05-16; C3 (typeII conditional core
unification) landed 2026-05-16 as the shared lemma
`typeII_collinear_inner_combo` in `HennebergRigidity.lean`, with
the IR-side and row-LI-side proofs both consuming it (15 + 9
body-LoC saved, plus the architectural win of factoring the
shared algebraic backbone). C2 closed 2026-05-16: notes-only
four-question walk over the C1 top-10 sites; highest-leverage
finding is the **lift+restrict+factor+oldSet-LI pattern** shared
verbatim across the typeI/typeII extends and the row-LI⇒sparsity
iso side (#1, #4, #7, #10; ~80-100 LoC compound savings under a
single `linearIndepOn_image_rigidityRow_of_injective` extraction).
Seven follow-up extraction candidates filed (Phase 8 warm-ups);
full per-site walk under the C2 task entry. Next concrete step:
**C4** (`exists_aug_of_lt_two_mul` focused walk) — the C2 sweep
already flagged three project-helper candidates that feed in.

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
- [x] B7: Multi-step `rw [..., ..., ...]` chains. **4 of 64 sites
  refactored across 4 commits; the remaining 60 are load-bearing.**
  Initial sweep: 64 `rw` blocks with 3+ args in project source
  (excluding `Mathlib/` mirror). Most are doing real per-step
  substitution + arithmetic and stay. Four cleanups landed:
  - **B7a — `Finset.mul_card_union_add_mul_card_inter` mirror.** The
    same 3-rewrite chain
    `rw [← Nat.mul_add, ← Nat.mul_add, Finset.card_union_add_card_inter]`
    appeared at two `IsTightOn`-accounting sites (`Sparsity.lean`:432
    in `IsTightOn.union_inter`, `Sparsity.lean`:478 in
    `IsTightOn.union_with_bonus`) — both proving
    `k * |s| + k * |t| = k * |s ∪ t| + k * |s ∩ t|`. Mirrored into
    `Mathlib/Data/Finset/Card.lean` alongside the existing
    `Finset.card_union_add_card_inter`; both sites collapse to a
    one-line `have h_card_mul :=
    Finset.mul_card_union_add_mul_card_inter s t k`. FRICTION entry
    under *Mirrored*.
  - **B7b — collapse 9-arg chain at `MatroidIdentification.lean`:692.**
    The `s * c_a = 0` branch of `typeII_edgeSetRowIndependent_extend`
    substituted three already-zero coefficients (`h_ca_zero, h_cb_zero,
    h_cc`) into a `Submodule.span` decomposition and then cleaned up
    via three `zero_smul` and two `zero_add` bookkeeping rewrites.
    `simp [hf_decomp, h_ca_zero, h_cb_zero, h_cc]` discharges the lot.
    9-arg chain → 4-arg `simp` call.
  - **B7c — `SimpleGraph.ncard_edgesIn_comap` project helper.** Two
    sites computed
    `((G.comap f).edgesIn ↑s').ncard = (G.edgesIn ↑(s'.image f)).ncard`
    under an injective `f` via the same 4-rewrite chain
    `rw [hS_def, Finset.coe_image, ← image_edgesIn_comap,
    Set.ncard_image_of_injective _ (Sym2.map.injective hf)]` — once
    in `IsSparse.comap` (`Sparsity.lean`:393) and once in
    `IsSparse.typeII_reverse_blocker` (`Sparsity.lean`:1035). Extracted
    as a project-internal companion to `image_edgesIn_comap` in the
    same file; both sites collapse to a one-line term-mode `have`.
  - **B7d — collapse duplicate 5-arg perturbation chain.** The
    same 5-arg chain
    `rw [h_p_t_a t, h_p_t_b t, zero_smul, one_smul, zero_add]`
    appeared at two perturbation-branch sites discharging
    `p_t t b - p_t t a = (0 : ℝ) • w + (1 : ℝ) • (p₀ b - p₀ a)` after
    substituting the perturbed-placement equalities —
    `HennebergRigidity.lean`:542 (`typeI_isGenericallyRigidInj_two`)
    and `MatroidIdentification.lean`:811
    (`typeI_pendant_edgeSetRowIndependent_lift`). The
    `zero_smul, one_smul, zero_add` tail is default simp content.
    Collapsed to `simp [h_p_t_a t, h_p_t_b t]` at both sites (5 args →
    2 args, same readability).

  Heuristic that emerged: a 3+-arg `rw` chain is a fused-lemma /
  helper candidate iff the chain (i) appears verbatim or near-verbatim
  at 2+ sites, or (ii) has an arithmetic tail (`zero_smul`,
  `one_smul`, `zero_add`, `sub_zero`, …) that lives in the default
  simp set. The `sub_smul, one_smul` tail at `HennebergRigidity.lean`:
  311 / `MatroidIdentification.lean`:360 / 407 *failed* the heuristic
  (`simp [h1, hcoll]` leaves a residual `α • d - d = (α - 1) • d`
  that needs `sub_smul` explicitly); the chain stays. Similarly for
  the `Fintype.card_sum / card_fin / card_sigma` chain in
  `TrivialMotions.lean`:306 (each step unrolls a distinct cardinality
  identity rather than normalizing).

### Bucket C — Long-proof audit

- [x] C1: Ranked top-25 by body line count via the CLEANUP.md awk
  recipe (`/^(private )?(theorem|lemma) /` → next blank or `end` /
  `namespace`, filter to bodies > 50 lines, with file paths). Top 10
  for C2 follow-up:

  | # | Body LoC | Site | Notes |
  |---|---|---|---|
  | 1 | 322 | `MatroidIdentification.lean:395 typeII_edgeSetRowIndependent_extend` | C3 candidate (typeII core) |
  | 2 | 184 | `Sparsity.lean:1454 IsSparse.exists_aug_of_lt_two_mul` | C4 candidate |
  | 3 | 134 | `RigidityMatroid.lean:360 exists_affinelySpanning_of_eventually` | |
  | 4 | 123 | `MatroidIdentification.lean:66 typeI_edgeSetRowIndependent_extend` | C3 candidate (typeI core) |
  | 5 | 118 | `Sparsity.lean:806 IsSparse.contradiction_three_pair` | |
  | 6 | 117 | `Sparsity.lean:1144 IsSparse.exists_typeI_or_typeII_reverse` | |
  | 7 | 107 | `RigidityMatroid.lean:514 isSparse_of_edgeSetRowIndependent_dim_two` | |
  | 8 | 92 | `HennebergRigidity.lean:301 typeII_isInfinitesimallyRigid_extend` | C3 candidate (typeII IR partner) |
  | 9 | 88 | `MatroidIdentification.lean:739 exists_nonCollinear_rowIndependent_placement_dim_two` | private |
  | 10 | 87 | `MatroidIdentification.lean:226 typeI_pendant_edgeSetRowIndependent_extend` | |

  The next 15 (LoC 86 down to 53) are recorded inline for context but
  not in C2 scope unless a sweep below upgrades one of them: `Sparsity.lean
  :1019 typeII_reverse_blocker` (86), `HennebergRigidity.lean:475
  exists_nonCollinear_rigid_placement_dim_two` (83, private),
  `Henneberg.lean:368 typeII_isLaman` (75), `MatroidIdentification.lean
  :941 IsSparse.exists_rowIndependent_placement` (64),
  `HennebergRigidity.lean:196 exists_off_line_off_finite_dim_two` (59),
  `Sparsity.lean:741 IsSparse.contradiction_two_pair` (57),
  `Sparsity.lean:632 IsSparse.no_isTightOn_excluding_three_neighbors`
  (57), `Henneberg.lean:546 IsLaman.exists_typeI_or_typeII_reverse`
  (57), `MatroidIdentification.lean:1028
  edgeSet_rowIndependent_iff_isSparse_dim_two` (56),
  `LamanTheorem.lean:68 IsLaman.isGenericallyRigidInj_two_of_card` (56,
  private), `Sparsity.lean:935 IsSparse.False_of_pairwise_blocker_or_edge`
  (54), `Sparsity.lean:569 IsSparse.exists_isTightOn_of_insert_not_sparse`
  (54), `HennebergRigidity.lean:126 typeI_isInfinitesimallyRigid_extend`
  (54), `Sparsity.lean:1327 IsSparse.maxBlock_isTightOn` (53),
  `Framework.lean:237 IsInfinitesimallyRigid.eventually` (53).

  Cross-cutting structure visible in the ranking: 4 of the top 10
  (#1, #4, #8, #10) and the leading runner-up
  (`Sparsity.lean:1019 typeII_reverse_blocker`, 86 LoC, just below
  the cutoff) are the typeI/typeII parallel pair across the IR side
  (`HennebergRigidity.lean`) and the row-LI / `IsSparse` side
  (`MatroidIdentification.lean` + `Sparsity.lean`). C3's typeII
  conditional-core unification proposal addresses #1 and #8
  directly; the typeI cores (#4, #10) carry the same algebraic
  backbone with a deleted row dropped, so the C3 extraction may
  cascade once landed. The Sparsity-side reverse / contradiction
  band (#5 `contradiction_three_pair`, #6
  `exists_typeI_or_typeII_reverse`, #7
  `isSparse_of_edgeSetRowIndependent_dim_two`, plus the runner-up
  `typeII_reverse_blocker`) is a separate cluster — note for C2 to
  check whether they share a common counting helper rather than each
  re-deriving the inequality.
- [x] C2: For each of the top 10: ask the four CLEANUP.md questions
  (API extraction / mathlib miss / tactic substitution / cross-proof
  unification). **Closed 2026-05-16.** Per-site walk recorded below;
  cross-cutting opportunity is the **lift+restrict+factor+oldSet-LI
  pattern** shared verbatim across the typeI/typeII extends and
  partially the row-LI⇒sparsity iso side (#1, #4, #7, #10).

  **Cross-cutting candidate (highest leverage).** The four-block sequence
  `hlift_mem` / `lift_some` / `hlift_some_inj` (build the lift
  `G'.edgeSet → H.edgeSet` via `Sym2.map φ`); `restrictMap :=
  LinearMap.funLeft ℝ _ φ` + `funLeft_surjective_of_injective`;
  `h_factor : H.rigidityRow p_ext (lift_some e') =
  restrictMap.dualMap (G'.rigidityRow p' e')`; and the oldSet-LI
  branch (`linearIndepOn_range_iff hlift_some_inj` → `funext h_factor`
  → `dualMap_of_surjective`) appears in:
  - `typeI_edgeSetRowIndependent_extend` (#4, lines 80-103 + 134-143
    = ~33 lines).
  - `typeII_edgeSetRowIndependent_extend` (#1, lines 426-453 + 507-520
    = ~42 lines, with the subtype refinement `{e' // e' ≠ s(a,b)}`).
  - `typeI_pendant_edgeSetRowIndependent_extend` (#10, lines 233-252
    + 268-277 = ~30 lines, with `a = b` for the pendant flat-form
    typeI).
  - `isSparse_of_edgeSetRowIndependent_dim_two` (#7, lines 562-610
    = ~49 lines, with `Subtype.val : ↥S → V` instead of `some`).
  Generic shape: `H.rigidityRow p_ext ∘ Sym2.map_lift =
  (LinearMap.funLeft ℝ _ φ).dualMap ∘ G'.rigidityRow p'` whenever
  `φ : V → W` injective and `p_ext (φ v) = p' v`. Concrete extraction
  target: `theorem linearIndepOn_image_rigidityRow_of_injective`
  in `RigidityMatroid.lean` taking `(G' : SimpleGraph V) (H : SimpleGraph W)
  (φ : V → W) (hφ : Function.Injective φ) (p_ext : Framework W d)
  (hcompat : ∀ v, p_ext (φ v) = p' v) (hlift : ∀ e' : G'.edgeSet,
  Sym2.map φ e'.val ∈ H.edgeSet) (h : G'.EdgeSetRowIndependent p'
  Set.univ)` and concluding `LinearIndepOn ℝ (H.rigidityRow p_ext)
  (Set.range fun e' => ⟨Sym2.map φ e'.val, hlift e'⟩)`. Expected
  aggregate savings ~80-100 LoC across the four sites; the pendant
  / typeI / typeII variants then differ only in the new-edge LI
  branch and the disjoint-spans branch. Worth filing as a Phase 8
  warm-up.

  **Per-site notes (four questions per site).**
  - **#1 `typeII_edgeSetRowIndependent_extend`** (313 LoC, post-C3,
    `MatroidIdentification.lean`:395).
    - *API extraction.* The three `hAB_ne / hAC_ne / hBC_ne` proofs
      at lines 462-485 follow identical 6-line `s(none, some u) =
      s(none, some v) → u = v` derivations. Candidate helper
      `Sym2.optionSome_pair_eq_iff : s(none, some u) = s(none, some v)
      ↔ u = v` (Sym2 mirror) collapses each to a one-line `apply h*_ne;
      exact Sym2.optionSome_pair_eq_iff.mp …`. ~15 LoC.
    - *Cross-proof unification.* Shared lift+restrict+factor pattern
      (cross-cutting candidate above).
  - **#2 `IsSparse.exists_aug_of_lt_two_mul`** (184 LoC,
    `Sparsity.lean`:1454; also C4 candidate).
    - *API extraction.* `h_edgesIn_eq` (lines 1537-1541, "edgesIn of
      `fromEdgeSet X` for off-diag `X` equals `X ∩ S.sym2`") is used
      4 times locally and looks like a generally useful project
      helper — extract to `EdgesIn.lean` as
      `edgesIn_fromEdgeSet_of_off_diag`.
    - *API extraction.* `h_toFinset_card_two` (lines 1483-1487) and
      the inline duplicate at 1524-1526 ("`e ∈ ⊤.edgeSet ⇒
      e.toFinset.card = 2`") could be a one-line helper
      `Sym2.card_toFinset_of_mem_top_edgeSet`. Likely already covered
      by `Sym2.card_toFinset_of_not_isDiag` + `edgeSet_top`; just
      missing the convenience wrapper.
    - *API extraction.* `h_toFinset_sub_iff` (lines 1545-1554,
      "`e ∈ (↑C).sym2 ↔ e.toFinset ⊆ C` for off-diag `e`") is also
      a candidate for a Sym2 / Set helper.
    - *Tactic substitution.* The `omega`-chains in step 7/9
      (lines 1567-1576, 1634-1636) are tight as written.
    - **Followed up under C4.** This is the dedicated focused-walk
      target; the API-extraction candidates above feed directly into
      it.
  - **#3 `exists_affinelySpanning_of_eventually`** (134 LoC,
    `RigidityMatroid.lean`:360).
    - *API extraction.* `h_per_tuple` (lines 400-448, ~49 lines) is
      a self-contained "for each injective tuple `q : Fin (d+1) → V`,
      the set of bad `t` is finite via polynomial roots" lemma. Could
      become a named private helper
      `private lemma finite_setOf_affineDependent_perturbation`. The
      proof would not shrink (it's the polynomial-trick machinery)
      but the top-level proof reads as a 4-step composition.
    - *Mathlib miss.* The polynomial-detector setup at lines 419-432
      uses `Polynomial.coeff_det_X_add_C_card` (project mirror in
      `Mathlib/LinearAlgebra/Vandermonde.lean`). Loogle on
      `Matrix.det_polynomial_X_add_C` style might surface a direct
      "leading coefficient = det of leading matrix" lemma; if so,
      the `hP_ne` block (lines 423-428) shrinks.
    - *Tactic substitution.* `h_rows` (lines 433-439) is a small
      7-line `ext`/`simp`/`ring` step; tight as written.
  - **#4 `typeI_edgeSetRowIndependent_extend`** (123 LoC,
    `MatroidIdentification.lean`:66).
    - *Cross-proof unification.* The lift+restrict+factor+oldSet-LI
      block (lines 80-103 + 134-143) is the cleanest instance of the
      shared pattern — refactor target for the cross-cutting lemma.
      After extraction the proof drops from 123 to ~60 LoC.
  - **#5 `IsSparse.contradiction_three_pair`** (118 LoC,
    `Sparsity.lean`:806).
    - *API extraction.* Lines 818-838 are three near-identical
      6-line `by_cases h_*_*: 2 ≤ (S_p ∩ S_q).card` blocks that each
      union the two tight sets via `union_inter` and discharge via
      `no_isTightOn_excluding_three_neighbors`. Extract a private
      auxiliary
      `private lemma IsSparse.contradiction_pair_aux
      (hS₁ : G.IsTightOn 2 3 S₁) (hS₂ : G.IsTightOn 2 3 S₂)
      (h : G.IsSparse 2 3) (h_inter : 2 ≤ (S₁ ∩ S₂).card) … : False`.
      Collapses three 6-line blocks to three 1-line `aux` calls.
      ~12 LoC.
    - *API extraction.* The three `card = 1` and three
      `eq_singleton_of_mem_of_card_le_one` derivations
      (lines 840-860) are tight as written; not worth fusing.
  - **#6 `IsSparse.exists_typeI_or_typeII_reverse`** (117 LoC,
    `Sparsity.lean`:1144).
    - *API extraction.* Lines 1216-1251 are three nearly-identical
      12-line per-pair dispatch blocks (`h_ab` / `h_ac` / `h_bc`)
      doing `by_cases adj` → `by_cases sparse` → either witness or
      blocker via `typeII_reverse_blocker`. Extract
      `private lemma IsSparse.typeII_pair_dispatch_aux` taking the
      pair `(x, y : {w // w ≠ v})` plus the third vertex `c` and
      neighbour-equivalence, returning
      `WitnessType ∨ G.Adj x.val y.val ∨ ∃ S, …`. Collapses the
      three blocks to three 1-line calls; ~30 LoC.
  - **#7 `isSparse_of_edgeSetRowIndependent_dim_two`** (107 LoC,
    `RigidityMatroid.lean`:514).
    - *API extraction.* `hH_edgeSet` derivation (lines 524-529,
      "fromEdgeSet of image of edgeSet under `Subtype.val` is the
      image") could mirror upstream as
      `SimpleGraph.edgeSet_fromEdgeSet_image_subtype_val` or
      similar; verify via loogle whether mathlib already has it.
    - *Cross-proof unification.* The `liftEdge` / `restrict` /
      `h_factor` block (lines 564-595) reuses the lift+restrict
      pattern with `φ := Subtype.val : ↥S → V` instead of
      `some : V → Option V`. Feeds into the cross-cutting lemma.
  - **#8 `typeII_isInfinitesimallyRigid_extend`** (77 LoC,
    post-C3, `HennebergRigidity.lean`:344). C3 has already
    consumed the typeII-specific savings via
    `typeII_collinear_inner_combo`. The remaining 77 lines split as
    `h_into` (~37 lines, the orbital-edge case split using
    `typeII_collinear_inner_combo` + Sym2 induction), `h_inj` (~21
    lines, the kernel-injectivity via `inner_sub_perp_of_eq` and
    `eq_zero_of_orthogonal_dim_two`), and rank-nullity (1 line).
    No further actionable items.
  - **#9 `exists_nonCollinear_rowIndependent_placement_dim_two`**
    (88 LoC, private, `MatroidIdentification.lean`:730).
    - *API extraction.* Lines 738-746 ("row-LI at `p₀` + adjacent
      edge `s(a, b)` ⟹ `p₀ a ≠ p₀ b`") could become an
      `EdgeSetRowIndependent.ne_of_adj` helper. Already done
      inline; check whether `typeII_isGenericallyRigidInj_two` or
      similar reuses this pattern.
    - *Mathlib miss.* Lines 750-762 explicitly factor a collinear
      pair `(v, w)` as `w = δ • v` from `¬ LinearIndependent ![v, w]`
      plus `v ≠ 0`. Loogle returned no direct hit on the goal-shape
      `¬ LinearIndependent ![v, w] → v ≠ 0 → ∃ δ, w = δ • v`. The
      standard mathlib path is `Submodule.mem_span_singleton` after
      `LinearIndependent.not_iff_eq_smul` (~6 lines, not 13). Worth
      a closer search; a 7-line saving.
    - *Cross-proof unification.* The "perturbation around `t = 0`
      via `Function.update` + continuity + `filter_upwards`" pattern
      is shared with `exists_nonCollinear_rigid_placement_dim_two`
      in `HennebergRigidity.lean` (83 LoC, runner-up at #11) — both
      do exactly the same `p_t := Function.update p₀ c (· + t • w)`
      perturbation, both pull back `eventually`-row-LI / IR through
      continuity, both choose `t ∈ nhdsWithin (≠ 0)`. Candidate
      shared lemma
      `exists_perturbation_with_property : ∀ᶠ p, P p → ∃ p_t, P p_t ∧
      (perturbation property at p_t)` — feasible but the two sites
      have slightly different "perturbation property" conclusions
      (LI of `![p b - p a, p c - p a]` for #9 vs. injectivity + LI
      for #11), so the helper needs care.
  - **#10 `typeI_pendant_edgeSetRowIndependent_extend`** (87 LoC,
    `MatroidIdentification.lean`:226).
    - *Cross-proof unification.* Same lift+restrict+factor+oldSet-LI
      pattern as #1, #4. Single new edge (pendant), so the LI-on-newSet
      branch is simpler (one `linearIndepOn_singleton_iff` + nonzero
      row check). After the cross-cutting lemma lands, the proof
      drops from 87 to ~35 LoC.

  Sub-bullet follow-up tasks filed (Phase 8 warm-up candidates, in
  rough priority order):
  - (a) Extract `linearIndepOn_image_rigidityRow_of_injective` and
    refactor #1/#4/#7/#10 — highest leverage (~80-100 LoC).
  - (b) Extract `IsSparse.contradiction_pair_aux` for #5 (~12 LoC).
  - (c) Extract `IsSparse.typeII_pair_dispatch_aux` for #6 (~30 LoC).
  - (d) C4 = focused #2 walk (`exists_aug_of_lt_two_mul`); the
    `h_edgesIn_eq` / `h_toFinset_card_two` / `h_toFinset_sub_iff`
    candidates above feed in.
  - (e) Closer mathlib search for the collinear-pair factoring
    helper in #9 (~7 LoC if it lands).
  - (f) `Sym2.optionSome_pair_eq_iff` mirror for #1 (~15 LoC).
  - (g) Shared `exists_perturbation_with_property` helper for #9
    + #11 — design-shape work, larger ROI but more delicate.
- [x] C3: **typeII conditional core unification (option 1 of Phase 7
  blocker).** Extracted the row identity in inner-product form as
  `SimpleGraph.Henneberg.typeII_collinear_inner_combo` in
  `HennebergRigidity.lean` (just before the typeII section's first
  theorem, with a 22-line doc-comment explaining the IR/row-LI
  duality). The lemma states, for `q - p' a = s • (p' b - p' a)` and
  any motion `x : Framework (Option V) d`:
  `(s − 1) · ⟪q − p' a, x none − x (some a)⟫ − s · ⟪q − p' b, x none − x (some b)⟫ = s (s − 1) · ⟪p' a − p' b, x (some a) − x (some b)⟫`.
  Both typeII extends consumed it:
  - **IR side** (`typeII_isInfinitesimallyRigid_extend`,
    `HennebergRigidity.lean`:344): the `h_into` block's manual
    derivation of the deleted-edge constraint (`hxa' → hxb' →
    h_deleted` via inner-product manipulations, ~24 lines) collapsed
    to a 5-line `h_combo + mul_eq_zero`-resolve step; the duplicate
    `hcoll_b` computation at line 351 was also dropped (it was only
    used by the now-deleted `hxb'`). Body LoC: 92 → 77 (saved 15).
  - **Row-LI side** (`typeII_edgeSetRowIndependent_extend`,
    `MatroidIdentification.lean`:395): the `h_f_eq` block's three
    per-row inner-product unfolds (`h_rowA, h_rowB, h_rowAB`) plus
    the `h_sub` inner-bilinearity step and the final
    `linear_combination ... * h_cb_rel` (~30 lines) collapsed to a
    single `h_combo` derivation + one `linear_combination` over
    `h_combo + h_cb_rel`. The `linear_combination`'s coefficients
    `c_a / (s − 1)` and `B / (s − 1)` use rational-function
    arithmetic, so the post-normalizer was overridden to
    `(norm := (field_simp; ring))` to clear the `(s − 1)`
    denominators. Body LoC: 322 → 313 (saved 9). Heuristic worth a
    TACTICS-GOLF note: `linear_combination (norm := (field_simp;
    ring))` extends the tactic to rational coefficients when there's
    a non-zero polynomial denominator in scope.

  The typeI cores (`typeI_edgeSetRowIndependent_extend` at
  `MatroidIdentification.lean`:66, and `typeI_isInfinitesimallyRigid_extend`
  at `HennebergRigidity.lean`:126) do **not** have a deleted edge, so
  there's no row identity to extract — they don't benefit from the
  same pattern. The "apply same pattern to the typeI cores" in the
  original C3 sketch was an over-extrapolation; reverse the claim
  in this commit's notes.

  Option 3 of the Phase 7 blocker (the principled
  `rank R_typeII = rank R_{G'} + 2` API) remains deferred; option 1's
  ~24-line incremental savings on each typeII core has now landed.
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

- **B7 — multi-step `rw` chain audit + 4-site cleanup across 4
  commits.** Audit found 4 of 64 chains (~6%) vestigial; the remaining
  60 do per-step substitution + arithmetic that doesn't fit the
  heuristic. Fix split into four commits (a/b/c/d): one Mathlib mirror
  (`Finset.mul_card_union_add_mul_card_inter` for two `IsTightOn`-
  accounting sites), one `simp` collapse (9-arg chain at
  `MatroidIdentification.lean`:692, six of the args lived in the
  default simp set), one project-internal helper
  (`SimpleGraph.ncard_edgesIn_comap` for two `IsSparse.comap`-style
  sites), and one duplicate `rw → simp` collapse (5-arg perturbation
  b-branch at `HennebergRigidity.lean`:542 and
  `MatroidIdentification.lean`:811). Two-pattern audit heuristic
  emerged: a 3+-arg `rw` chain is a candidate iff (i) it appears
  verbatim or near-verbatim at 2+ sites (⇒ fused lemma / project
  helper), or (ii) its tail lemmas live in the default simp set (⇒
  `simp`-collapse). Counter-examples that *failed* the heuristic stay
  as-is: `sub_smul, one_smul` tails leave a residual that needs the
  explicit `sub_smul` rewrite (HennebergRigidity:311 / Matroid:360,
  407); `Fintype.card_sum / card_fin / card_sigma` chains unroll
  distinct cardinality identities, not normalize a single shape
  (TrivialMotions:306).

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

- **C2 — four-question walk over C1 top-10 (notes only).** Walked
  the top-10 long-proof sites against the four CLEANUP.md questions
  (API extraction / mathlib miss / tactic substitution / cross-proof
  unification). No Lean changes this commit — the deliverable is the
  per-site improvement-candidate list filed under the C2 task entry.
  Highest-leverage finding: the
  **lift+restrict+factor+oldSet-LI pattern** —
  `Sym2.map φ` lift on `G'.edgeSet → H.edgeSet`,
  `LinearMap.funLeft ℝ _ φ` restriction whose `dualMap` factors the
  rigidity rows, and the `linearIndepOn_range_iff` →
  `dualMap_of_surjective` LI pullback — appears verbatim in #1 / #4 /
  #10 (with `φ = some : V → Option V`) and in #7 (with
  `φ = Subtype.val : ↥S → V`). A single extracted lemma
  `linearIndepOn_image_rigidityRow_of_injective` would compound-save
  ~80-100 LoC across the four sites. Six smaller per-site candidates
  filed: project helper `edgesIn_fromEdgeSet_of_off_diag` for #2,
  pair-aux for #5 and pair-dispatch-aux for #6 (each repeats a
  3-branch by-cases), `Sym2.optionSome_pair_eq_iff` for #1's three
  `≠` proofs, the collinear-pair factoring mathlib search for #9,
  and the shared `Function.update`-perturbation helper for
  #9 + #11. The C2 walk itself is a one-shot notes pass; the
  follow-up extractions are scheduled as Phase 8 warm-ups in
  rough priority order. The four-question framework worked as
  designed — every site surfaced either an API-extraction or a
  cross-proof-unification finding; none surfaced a pure
  tactic-substitution win at this depth (the C3 `linear_combination
  (norm := …)` move was the last of those).

- **C3 — typeII conditional core unification.** Extracted
  `typeII_collinear_inner_combo` in `HennebergRigidity.lean` (just
  before the typeII section's first theorem). The lemma states the
  inner-product identity
  `(s−1)·⟪q−p'a, x_none − x_(some a)⟫ − s·⟪q−p'b, x_none − x_(some b)⟫ = s(s−1)·⟪p'a−p'b, x_(some a) − x_(some b)⟫`
  for `q − p' a = s·(p' b − p' a)`, with a doc-comment explaining
  the IR/row-LI duality. Both typeII extends consumed it: the IR
  proof's `h_into` block dropped its manual deleted-edge derivation
  (24 lines → 5 lines via `h_combo + mul_eq_zero`-resolve; net 92 →
  77 body LoC); the row-LI proof's `h_f_eq` block dropped its three
  per-row inner-product unfolds and bilinearity manipulation (30
  lines → 14 lines via a single `linear_combination (norm := ...)`
  with rational-function coefficients; net 322 → 313 body LoC).
  The "apply same pattern to typeI cores" sub-goal from the
  original C3 sketch turned out to be over-extrapolation: typeI has
  no deleted edge, so no row identity to share. Heuristic that
  emerged: `linear_combination (norm := (field_simp; ring))`
  extends the tactic to rational coefficients with a non-zero
  polynomial denominator — useful when the linear-combination
  scaling factor itself has a `(s − 1)` in the denominator (e.g.
  the row-LI proof needs `c_a / (s − 1)` because the c_a-c_b
  constraint `(s − 1) c_b = −(s c_a)` doesn't admit a polynomial
  rearrangement at the coefficient level). Worth a brief
  TACTICS-GOLF entry. Phase 7 *Blockers / open questions* entry
  for option 1 closes; option 3 (`rank R_typeII = rank R_{G'} + 2`)
  remains deferred for the post-Phase-8 `Matroid` infrastructure.

- **C1 — top-10 long-proof ranking recorded.** Ran the CLEANUP.md
  awk recipe across all source files; top 10 by body line count
  range from 322 LoC (`typeII_edgeSetRowIndependent_extend`) down
  to 87 LoC (`typeI_pendant_edgeSetRowIndependent_extend`). The
  ranking confirms C3's typeI / typeII unification candidate is
  pointed at the right targets (#1 and #8 are the worked example
  pair of typeII cores; #4 and #10 are the typeI partners) and
  surfaces a second band of reverse-blocker / contradiction proofs
  (#5–#7 plus the `typeII_reverse_blocker` runner-up) that may
  share an extracted lemma once C3 lands. Full ranked list lives
  in the C1 checkbox above. Next concrete step: C2 walks each
  top-10 site against the four CLEANUP.md questions and files per-
  site improvement sub-bullets.

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
