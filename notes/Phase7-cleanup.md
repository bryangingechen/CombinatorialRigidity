# Phase 7 cleanup round — work log

**Status:** in progress. A1 + A9 (fixes) + A2/A3/A4/A5/A6/A7/A8/A10
(no-fix audits) done; A11, B*, C*, D* outstanding.

This is the inter-phase cleanup round between Phase 7 and Phase 8.
See `../CLEANUP.md` for the round-level operating manual: when to
run a round, the three audit categories, and the per-round workflow.
The task list below is the round's "lemma checklist" equivalent —
populated up front so a session that runs out of time can hand off
cleanly.

## Current state

Working through bucket A. A1 + A9 fixed; A2 / A3 / A4 / A5 / A6 /
A7 / A8 / A10 audited clean (no divergence). Remaining A-task:
A11. Then B/C/D.

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
- [ ] A11: Run `lake exe checkdecls blueprint/lean_decls` (after
  `inv web`) at end; confirm every `\lean{...}` resolves. This is
  fast and should pass; if it fails, capture which rename slipped
  through.

### Bucket B — Code-smell sweep

Each is a separate commit, root-cause fix preferred.

- [ ] B1: `classical` audit (39 sites; concentrated in `Sparsity.lean`:14,
  `MatroidIdentification.lean`:7, `Henneberg.lean`:6,
  `RigidityMatroid.lean`:6). For each: does adding `[DecidableEq V]`
  or `[DecidableRel G.Adj]` at the caller boundary remove the need?
  Or is the `classical` in a noncomputable section where there's no
  point? Goal: eliminate decorative `classical` calls, document
  load-bearing ones.
- [ ] B2: `letI : Fintype V := Fintype.ofFinite V` audit (~10 sites;
  most in `Sparsity.lean` and `RigidityMatroid.lean`). Same question
  pattern: should the caller take `[Fintype V]`? If the
  `[Finite V] → [Fintype V]` bridge happens at five sites in one
  file, consider lifting it to a single section-opening
  `variable [Fintype V] [DecidableEq V]` plus `[Finite V]` only
  where the weaker hypothesis is genuinely wanted.
- [ ] B3: `@[nolint unusedArguments]` / `set_option linter.* false`
  audit. Sites:
  - `Framework.lean`:150 (`@[nolint unusedArguments]` on
    `IsInfinitesimallyRigid` — confirm justification stands).
  - `TrivialMotions.lean`:250, 321, 347
    (`set_option linter.unusedFintypeInType false`) — three sites
    in one file; confirm the pattern.
  - `Sparsity.lean`:1275, 1442 (`set_option
    linter.unusedDecidableInType false`); 1283, 1295
    (`@[nolint unusedArguments]`) — Phase 7 additions; verify the
    rationale is recorded in a one-line comment.
  Each site: does the silenced rule still apply? If yes, does it
  have a one-line "why" comment? If no, remove the override.
- [ ] B4: `noncomputable def` audit. List each one, classify as
  "forced" (`Classical.choose`, `Module.Dual`, unbundled `Sym2.lift`,
  …) or "vestigial". Each vestigial site: drop the keyword and see
  if `lake build` still passes.
- [ ] B5: `Set` vs `Finset` consistency. Walk the major
  `IsSparse.maxBlock*` infrastructure (Phase 7 Commit 17b): the
  bridging between `maxBlockSet : Set V` and `maxBlock : Finset V`
  is necessary for `Finset.sup_mem`. Does any caller-side proof
  unnecessarily round-trip? Look also at `EdgesIn.lean` and
  `Framework.lean` for `Set`/`Finset` boundary friction.
- [ ] B6: `change` / `show` survey (concrete signal from
  `CombinatorialRigidity/CLAUDE.md` *Friction review*). For each
  `change` / `show` in source: is it covering for an un-fused
  predicate lemma? Could a project-internal `simp` lemma replace
  it? (Most `change` instances will be load-bearing; we're looking
  for the 1-2 that aren't.)
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

### Cleanup pass summaries

## Blockers / open questions

- None yet. Open items get filed here as the round runs.

## Hand-off / next phase

*(Populated when the round closes; expected handoff is "Phase 8 can
start; carry-over items if any are noted here.")*
