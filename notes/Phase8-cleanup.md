# Phase 8 cleanup round — work log

**Status:** in progress (round just opened).

This is the inter-phase cleanup round after Phase 8 closed. See
`../CLEANUP.md` for the round-level operating manual: when to run a
round, the three audit categories (A blueprint-divergence, B
code-smell, C long-proof, D project-organization), and the
per-round workflow. The task list below is the round's "lemma
checklist" equivalent — populated up front per CLEANUP.md's *Sweep
first, fix later* + *Task list discipline* so a session that runs
out of time can hand off cleanly.

This round is **scoped light**: Phase 8 itself shipped only ~400 LoC
of new Lean (one new file `LinearRigidityMatroid.lean` at 252 LoC
plus two new mirror lemmas in `Mathlib/LinearAlgebra/Matrix/Rank.lean`
at 148 LoC total). The Phase 7-cleanup round just closed and most
project-wide drift was discharged there. Bucket A–D scope is
therefore *Phase 8 surface only* (the new file + new mirror + Phase 8
touches in pre-existing files), not a project-wide re-sweep.

The round additionally carries a non-standard **Bucket E:
import / file-structure audit** — the user-requested consideration
of whether to split large Lean files to manage imports better. This
bucket is *audit-only* per the round-open scoping decision: survey
file sizes + import graph, recommend candidate splits with expected
import-graph benefit, but do **not** execute any split in this round.
Splits stay as recommendations in PERFORMANCE.md / DESIGN.md
*Choices to revisit*, to be picked up by a dedicated perf or
structural-refactor round.

## Current state

Bucket A (blueprint audit, 4 sub-tasks) closed clean: every Phase 8
`\lean{...}` pin resolves, statement forms match faithfully, the
`Subtype.val ''` image-packaging and `rigidityRow_add_smul` bridge
are both honestly flagged in blueprint prose. Bucket B in progress
— B1 found one vestigial `classical` (deleted this commit). The
full task list across A–E sits under *Task checklist* below.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Light scope for A–D.** Phase 8's own *Hand-off* section noted
  "no urgent friction items surfaced during Phase 8 implementation"
  and Phase 7-cleanup discharged the project-wide backlog of
  classical / Fintype / `change` / `noncomputable` / `rw`-chain
  smells. Re-running those project-wide would be ~80% re-audit of
  closed resolutions; the marginal find rate doesn't justify it.
  Buckets A–D therefore restrict to the Phase 8 surface (new file +
  new mirror + Phase 8 touches in `RigidityMatroid.lean`).
- **Audit-only for E.** PERFORMANCE.md *Module system* and
  *Recommendations for future perf work* both flag structural
  levers (file split + module-system conversion) as "unmeasured
  against the build-time noise band" and recommend they be picked
  up as a dedicated perf pass. Executing a split during a cleanup
  round would conflate hygiene with structural refactor, and
  PERFORMANCE.md's 4-run A/B protocol is the right gate for that
  decision — not the cleanup round.
- **Each fix as its own commit.** A cleanup commit obeys the same
  per-commit friction review and build/lint gates as a forward-work
  commit. Cleanup-round value is the trail of small principled
  commits, not a single mega-commit. The E bucket lands as one or
  two notes commits (updates to PERFORMANCE.md plus any DESIGN.md
  *Choices to revisit* entry); no Lean files touched.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit (Phase 8 surface)

- [ ] **A1:** `chapter/rigidity-matroid.tex` *Linear-matroid framing*
  subsection (lines 536+) ↔ `LinearRigidityMatroid.lean`. Five
  dep-graph nodes per Phase 8 notes: `def:linearRigidityRow`,
  `def:linearRigidityMatroid`, `lem:linearRigidityMatroid-indep-iff`,
  `lem:exists-uniform-rowIndependent-placement`,
  `thm:linearRigidityMatroid-eq-rigidityMatroid`. For each:
  - confirm the `\lean{...}` pin resolves;
  - compare blueprint statement form against Lean signature
    (hypotheses, conclusion form, implicit/explicit binders);
  - re-read the prose proof and flag any "formalization aside" or
    "the Lean does X via Y where Y is harder than X" pattern per
    `../CLEANUP.md` §A.
  Watch for: the uniform-genericity proof's `(2, 3)`-sparse-family
  bound being faithfully described; the `Function.extend`-by-zero
  off the edge set being honestly flagged as a Lean-side
  bookkeeping device that the math doesn't see.
- [ ] **A2:** `RigidityMatroid.lean` Phase 8 additions
  (`rigidityRow_add_smul` and any other Phase-8-touched lemmas)
  cross-check against `chapter/rigidity-matroid.tex` prose
  references. Phase 8 notes mention this helper as "the bridge from
  `Framework`-level affine paths to `Module.Dual`-level affine
  paths" — verify the blueprint reflects this (or honestly elides
  it as a Lean-side bookkeeping helper).
- [ ] **A3:** Two new mirror lemmas in
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`
  (`Matrix.linearIndependent_rows_iff_det_mul_transpose_ne_zero`
  and `LinearIndependent.finite_setOf_not_along_affine_path`) — do
  they need blueprint mention? Phase 8 chapter's
  *Linear-matroid framing* subsection points at them; verify the
  pointer is correct + statement-form-faithful.
- [ ] **A4:** Run `lake exe checkdecls blueprint/lean_decls` (after
  `inv web`) to confirm every Phase 8 `\lean{...}` resolves. Phase 8
  notes claim "the dep-graph at `blueprint/web/dep_graph_document.html`
  is fully green" — verify post-hoc.

### Bucket B — Code-smell sweep (Phase 8 surface)

Phase 8 surface = `LinearRigidityMatroid.lean` + new lemmas in
`Mathlib/LinearAlgebra/Matrix/Rank.lean` + Phase 8 additions in
`RigidityMatroid.lean`. Initial grep results pre-sweep:

| Smell | LinearRigidityMatroid.lean | Mathlib/.../Rank.lean | RigidityMatroid (P8 lines) |
|---|---|---|---|
| `classical` | 1 (L115) | 2 (L74, L124) | 3 (L295, L466, L620 — may be P6/P7, verify P8 attribution) |
| `haveI Fintype` | 1 (L116) | 3 (L75, L76, L125) | — |
| `change`/`show` | 0 | 0 | — |
| `@[nolint]` / `set_option linter` | 0 | 0 | — |
| `noncomputable def` | 2 (L39, L62) | 0 | — |

- [x] **B1:** `classical` audit closed. Comment-out + `lake build`
  on each of the 3 Phase 8 sites: the two Rank.lean ones (L74, L124)
  are load-bearing (failed-typeclass-synthesis errors on `Matrix.det`
  via `linearIndependent_rows_iff_det_mul_transpose_ne_zero`,
  multiple sites each); the one in `exists_uniform_rowIndependent_
  placement_dim_two` (LinearRigidityMatroid L115) is **vestigial** —
  build + lint stay green without it (likely leftover from an
  earlier draft that used a Finset op pre-replaced with a
  `Set.Finite`-bridged form). Deleted this commit.
- [x] **B2:** `Fintype.ofFinite` bridge audit closed. All 4 Phase 8
  sites stay: each statement's type-mention is `Matrix m n ℝ` /
  `Framework V 2` / `LinearIndependent ℝ (…)` / `Set (⊤).edgeSet`,
  none of which require `Fintype.card …`-shaped data in the
  signature. Bodies use `Matrix.det` / `Finset.induction_on` which
  do need `[Fintype …]`; inline `haveI` bridges are the canonical
  mathlib idiom per `DESIGN.md` *Typeclass shape for finiteness on
  `V`*. For the mirror lemmas, the `[Finite m]` / `[Finite n]`
  signature is also the upstream-PR-friendly shape.
- [x] **B3:** `noncomputable def` audit closed. Both forced.
  `linearRigidityRow` fails compilation as `def` with *"depends on
  `Function.extend`, which is `noncomputable`"*; `linearRigidityMatroid`
  fails as `def` with *"depends on `Real.instDivisionRing`, which is
  `noncomputable`"* (via `Matroid.ofFun ℝ …`). Phase 7-cleanup B4's
  observation extends: the new defs compose with the
  `Real.instRCLike`-driven `(⊤).rigidityRow p` pipeline AND introduce
  a second `noncomputable` driver (`Function.extend` for the
  off-edge-set zero extension).
- [ ] **B4:** Multi-step `rw [..., ..., ...]` chain survey on the
  new file + new mirror. Grep: `rw \[[^]]*,[^]]*,[^]]*,[^]]*\]`.
  For each 4+-arg chain, ask the standard *missing-fused-lemma* /
  *mirror-eligible* question per `../CLEANUP.md` §B.
- [ ] **B5:** Mirror-eligibility check on the two new
  `Mathlib/LinearAlgebra/Matrix/Rank.lean` lemmas. Phase 8
  *Hand-off* flags both as upstream PR candidates ("direct
  corollaries of `Matrix.rank_self_mul_transpose` and standard
  `Polynomial` machinery"). Decide: file as upstream PRs now, or
  defer until a "dropping the apnelson1/Matroid dep" mass-upstream
  occasion? Update `notes/FRICTION.md` *Mirrored* entries
  accordingly.

### Bucket C — Long-proof audit (Phase 8 surface)

- [ ] **C1:** Rank top proofs in `LinearRigidityMatroid.lean` (252
  LoC total — small) + the two new lemmas in
  `Mathlib/LinearAlgebra/Matrix/Rank.lean`. Walk each
  flagged-as-long proof for: API extraction, missing mathlib hits
  (re-run `lean_loogle` / `lean_leanfinder` on 5–10-line subblocks),
  tactic substitution (`grind only` / `linear_combination`), and
  definitional refactor. Phase 8 *Decisions made* already identifies
  the cross-cutting **lift+restrict+factor** pattern (extracted in
  Phase 7-cleanup C5–C7) and the **uniform-genericity** lemma
  shape; check whether the new file uses the resolved patterns
  consistently or whether any local proof re-derives a piece that
  the resolved API now covers.

### Bucket D — Project-organization compression

- [ ] **D1:** `notes/Phase8.md` length check. Current 253 lines —
  3 lines over the 250 soft budget. Compress: candidate targets
  are the resolved *Blockers* section (two long resolved entries)
  and *Decisions made → Phase-local choices and proof techniques*
  (4 entries averaging ~13 lines each). Apply *Lift on promotion*
  per `notes/CLAUDE.md` to any decision referenced in 2+ files.
- [ ] **D2:** FRICTION.md *Open* re-skim — three current open
  project-internal entries surfaced during Phase 8:
  *Chaining `LinearIndepOn.insert`...*, *`Polynomial.X` in a
  `set := ...` binding...*, *`h ▸ ...` substitutes through ambient
  terms...*. For each: did a second site surface during Phase 8
  finishing (triggering the promote-to-TACTICS-QUIRKS rule)? If
  no — leave open. If yes — promote.
- [ ] **D3:** `DESIGN.md` *Choices to revisit* drift check. Phase 8
  closed `Ground-set shape of Matroid.ofFun` and `apnelson1/Matroid
  pin drift` (both marked resolved at dep-bump commit). The new
  `apnelson1/Matroid dependency` entry's "watch on every mathlib
  bump" reminder remains active; the `Promoting edgesIn upstream`
  entry remains active. Quick sanity: no other entry needs P8
  update.
- [ ] **D4:** No-residual-lifts audit. Phase 7-cleanup D1 was the
  canonical example: scan every `notes/PhaseN.md`'s
  *Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN*
  section to confirm the targeted destination still exists and
  carries the lifted content. Phase 8's section is single-entry
  (`Extension by zero off a subtype` → FRICTION resolved); verify
  the entry actually lives at the cited location in
  `FRICTION-archive.md` (or the FRICTION *Resolved* section).

### Bucket E — Import / file-structure audit (audit-only)

The user-requested addition: "consider whether we should split up
our Lean files to manage imports better." Audit-only per the
round-open scoping decision; recommendations land in
PERFORMANCE.md (concrete split proposals) and DESIGN.md *Choices
to revisit* (if any becomes a project-policy question). No Lean
files are touched by this bucket.

File-size inventory (project source, descending; commit `2f3f036`):
- `Sparsity.lean` 1620 LoC ⚠️ very large
- `MatroidIdentification.lean` 975 LoC ⚠️ large
- `RigidityMatroid.lean` 709 LoC
- `Henneberg.lean` 647 LoC
- `HennebergRigidity.lean` 638 LoC
- `Framework.lean` 376 LoC
- `TrivialMotions.lean` 353 LoC
- `LinearRigidityMatroid.lean` 252 LoC
- `EdgesIn.lean` 225 LoC
- `LamanTheorem.lean` 199 LoC
- `Laman.lean` 143 LoC
- `CountMatroid.lean` 93 LoC

- [ ] **E1:** Build an explicit import-graph + downstream-impact
  map. Each file's direct importers (already gathered) plus the
  transitive importer set. Headline target: identify which files,
  if split, reduce the transitive-import surface of how many
  downstream files. Per PERFORMANCE.md, the dominant cost is
  import loading (~25–27 s for analysis-heavy files); reducing
  transitive imports is the lever.
- [ ] **E2:** For each file > ~600 LoC, identify the natural cut
  line. Concrete starting candidates per a first-pass file
  outline:
  - **`Sparsity.lean` (1620 LoC):** plausibly splits into a base
    (`IsSparse` / `IsTight` definitions + monotonicity) and an
    `IComponents` half (the `IsSparse.maxBlock` + I-component
    matroidal-regime scaffolding added during Phase 7). The
    base is what `Laman.lean` / `EdgesIn.lean`'s downstream needs
    most; `IComponents` is Phase 7's matroid-side need and only
    `MatroidIdentification.lean` / `CountMatroid.lean` use it.
  - **`MatroidIdentification.lean` (975 LoC):** the typeI/typeII
    *extends* lemmas (Phase 7) and the rigidity-matroid
    instantiation could plausibly split. Check the natural cut
    against the Phase 7-cleanup C5/C10 extracted helpers' homes.
  - **`Henneberg.lean` (647 LoC):** the typeI/typeII move
    *definitions* + edge-set decomps vs the iso constructors +
    flat-form reverse decomposition. Possibly natural; possibly
    not (the reverse decomposition consumes a lot of the API).
  - **`HennebergRigidity.lean` (638 LoC):** per-move IR
    preservation theorems are the body; possibly one file per
    move (typeI / typeII) given how independent they are.
  - **`RigidityMatroid.lean` (709 LoC):** the row-LI / span /
    rank API vs the affinely-spanning perturbation + basis-pick
    half. Check the natural cut.
- [ ] **E3:** For each candidate split: estimate the build-graph
  benefit. Concrete metric — how many downstream files'
  transitive-import set shrinks, and by what (LoC of moved
  declarations). The biggest single win is plausibly the
  `Framework.lean → Sparsity.lean` edge, since `Framework`
  imports all 1620 LoC of `Sparsity.lean` for what is mostly
  `edgesIn` / `IsTight 2 3`-level usage in the rigidity bound;
  if `Framework` only needs the *base* half, splitting
  `Sparsity.lean` shrinks the analysis-side import floor.
- [ ] **E4:** Module-system conversion option. PERFORMANCE.md
  *Module system* notes the conversion is "plausibly a win
  post-Phase-6, but still unmeasured" and is multi-file
  (must convert every transitively-imported file first). Audit:
  is mathlib's module-system conversion mature enough on
  `v4.X` that this is now a one-session refactor, or is it still
  multi-session? (Spot-check mathlib's `Mathlib/Analysis` /
  `Mathlib/Combinatorics/SimpleGraph` for `module` markers.) Don't
  execute; recommend.
- [ ] **E5:** Write recommendations to PERFORMANCE.md as concrete
  split proposals (with the E1–E4 findings). If any
  recommendation rises to a project-policy question (e.g.
  "should we split files at the 800-LoC threshold as a
  convention?"), add a DESIGN.md *Choices to revisit* entry.
  Update ROADMAP.md *Directory layout* only if a split actually
  ships — for an audit-only round, ROADMAP stays unchanged.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(Empty — populate as fixes land.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

### Cleanup pass summaries

**B1 — vestigial `classical` deletion.** One site:
`LinearRigidityMatroid.exists_uniform_rowIndependent_placement_dim_two`
(L115). The two `classical`s in `Mathlib/.../Rank.lean` (L74, L124)
are load-bearing (Matrix.det needs `DecidableEq m` / `DecidableEq ι`,
not provided by the `[Finite m]` / `[Finite n]` / `[Finite ι]`
signatures). No FRICTION-worthy lesson — Phase 7-cleanup B1 already
established "vestigial classicals accumulate from draft refactors";
the audit protocol caught a single Phase-8 instance.

**B2 — `Fintype.ofFinite` bridge audit.** No-edit. All 4 sites
(LinearRigidityMatroid L115; Rank.lean L75, L76, L125) stay. Each
is the canonical `[Finite …]`-signature + inline-`haveI` bridge per
`DESIGN.md` *Typeclass shape for finiteness on `V`*.

**B3 — `noncomputable def` audit.** No-edit. Both new defs forced.
`linearRigidityRow` by `Function.extend`; `linearRigidityMatroid`
by `Real.instDivisionRing` via `Matroid.ofFun ℝ …`. Verified by
keyword-strip + `lake build` failure trace.

## Blockers / open questions

*(None at round open.)*

## Hand-off / next phase

Round just opened; hand-off section to be populated at round close.
Default expectation: no follow-up phase queued — Phase 8 closed the
planned ROADMAP and this round is hygiene. Possible carry-overs:

- Any E5 recommendation that the project decides to actually
  execute spawns its own dedicated structural-refactor pass with
  the PERFORMANCE.md 4-run A/B protocol.
- Any B5 upstream-PR-eligible lemma filed against mathlib.
- Any D2 promote-to-TACTICS-QUIRKS triggered by a second site.
