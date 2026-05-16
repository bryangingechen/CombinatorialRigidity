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

Buckets A (blueprint audit, 4 sub-tasks), B (5 sub-tasks), C
(1 sub-task), and D (4 sub-tasks) all closed. Remaining: bucket E
(import / file-structure audit, audit-only). Findings landed:
B1 deleted one vestigial `classical`; B4 dropped two
`show … from rfl` workarounds via `RingHom.mapMatrix_apply` and
added a new `CLEANUP.md` smell row for the pattern; C1 saved
~20 lines on the uniform-genericity proof via parallel-case
unification + `Set.Finite.exists_notMem`; D1 compressed
`Phase8.md` 253 → 236 LoC; D2 promoted the `Polynomial.X`
ascription quirk to TACTICS-QUIRKS § 15. Bucket E is audit-only
per the round-open scoping decision.

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
- [x] **B4:** Multi-step `rw` chain survey closed. Project surface
  (LinearRigidityMatroid + Rank.lean): no chain with a missing
  fused-lemma gap. Real finding: one 6-arg chain at Rank.lean L95
  (inside `Matrix.finite_setOf_not_linearIndependent_rows_along_
  affine_path`) used **two `show ... from rfl`** workarounds — one
  to unfold the `let`-bound `Q`, one to bridge `(evalRingHom t)
  .mapMatrix (P * Pᵀ)` to `(P * Pᵀ).map ⇑(evalRingHom t)`. Both
  eliminated this commit: the `let`-unfold is unnecessary (the rw
  chain works without exposing Q's body), and the `mapMatrix → map`
  bridge has a named lemma `RingHom.mapMatrix_apply` in mathlib that
  the original proof didn't reach for. Net: 6 lines → 4 lines, no
  `show … from rfl` smell, upstream-PR-friendly.
- [x] **B5:** Mirror-eligibility decision: **defer upstreaming.**
  Both lemmas are already entered in FRICTION *Mirrored* (commit
  `53c3a25`) and the surrounding entry honestly flags them as
  upstream-PR-friendly. Filing-now-vs-later: no natural batching
  window with the `apnelson1/Matroid` upstreaming (the two Rank.lean
  lemmas are standalone LA packaging — they don't pair with anything
  in the matroid dep). The project's default for `[mirrored]`
  entries is "sit until a specific reason to PR surfaces"; the same
  default applies here. If/when mathlib refactors
  `Matrix.rank_self_mul_transpose` or `Polynomial.finite_setOf_isRoot`,
  re-check whether the iff packaging is still missing or has been
  superseded.

### Bucket C — Long-proof audit (Phase 8 surface)

- [x] **C1:** Long-proof audit closed. The only big proof on the
  Phase 8 surface is `exists_uniform_rowIndependent_placement_dim_two`
  (113 lines). Two refactors landed:
  1. **Parallel-case unification** — the `h_bad_finite` block had two
     `rcases`-cases (`I = I₀` at `t = 1` vs `I ∈ F'` at `t = 0`),
     each ~13 lines of identical shape modulo the witness placement
     (`q` vs `p₀`). Factored through a common `∃ t_w, EdgeSetRow-
     Independent (p₀ + t_w • r) I` unpacking. Saves ~18 lines.
  2. **`(badᶜ).Nonempty` via `Set.Finite.exists_notMem`** — the
     existing 3-line `obtain ⟨t, ht_good⟩ : (badᶜ).Nonempty := by
     rw [Set.nonempty_compl]; exact fun h_eq_univ => …` collapses
     to a one-liner via the named mathlib lemma. Saves 2 lines.
  Net: file 252 → 232 LoC; the main proof 113 → 95 lines.
  The other Phase 8 lemmas (Rank.lean mirrors 30-38 LoC each;
  `linearRigidityMatroid_eq_rigidityMatroid` 17 lines) are tight as
  written. No API extraction worth doing — the `h_eqOn` + `h_iff`
  block is a candidate `EdgeSetRowIndependent_add_smul_iff` helper
  but currently single-use, so premature.

### Bucket D — Project-organization compression

- [x] **D1:** Phase8.md compressed 253 → 236 LoC. Three entries
  tightened: *Uniform-genericity as a separate auxiliary lemma*
  (16 → 10 lines, drops the now-historical "original sketch failed"
  narrative); *Subtype factoring at Matroid.ext_indep* (13 → 8
  lines, drops the wide-stance "may recur, idiom is worth noting"
  prose for a tight watch-only entry); the resolved-blocker *Ground-
  set shape of Matroid.ofFun* (12 → 7 lines, drops the full
  signature recap that lives in the Lean code). Also tightened the
  Hand-off *Possible cleanup round* to point at the now-active
  `Phase8-cleanup.md`.
- [x] **D2:** FRICTION re-skim — one promote-to-QUIRKS triggered:
  the **`Polynomial.X` ascription quirk** hit a second site in
  Phase 8 (`finite_setOf_not_linearIndependent_rows_along_affine_path`
  in Rank.lean L78-79 uses the same `(Polynomial.X : Polynomial ℝ)`
  workaround). Lifted to `TACTICS-QUIRKS.md` § 15; FRICTION entry
  flipped to `[resolved]` with cross-reference; project CLAUDE.md
  Quirks-index symptom table updated. The other two open Phase-8-era
  entries (`LinearIndepOn.insert` chain, `h ▸` oversubstitution)
  stay open — no second site surfaced in Phase 8.
- [x] **D3:** DESIGN.md *Choices to revisit* drift check clean.
  Two active (`apnelson1/Matroid dependency` watch + `Promoting
  edgesIn upstream`); no other entry needs Phase-8 update. The
  resolved-marker on `apnelson1/Matroid dependency` correctly
  carries the "watch on every mathlib bump" reminder per the
  Phase 8 opener (`3e7e2e5`).
- [x] **D4:** No-residual-lifts audit clean. Phase 8's *Promoted*
  section has one entry: *Extension by zero off a subtype* →
  FRICTION [resolved] *Extending a function on a subtype to the
  parent type — `dite` vs `Function.extend`*. Verified at
  `notes/FRICTION.md:619`.

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

**B4 — Rank.lean L92-98 `hQ_eval` chain simplification.** Two
`show … from rfl` workarounds dropped:
1. `show Q = (P * Pᵀ).det from rfl` — unfolds the `let`-bound `Q`;
   eliminated by reordering the rewrite chain so the `(evalRingHom
   t).map_det` step lands on `Q` directly (a `let`-binding is `rfl`-
   reducible at the elaboration boundary).
2. `show (Polynomial.evalRingHom t).mapMatrix (P * Pᵀ) = (P * Pᵀ).map
   ⇑(Polynomial.evalRingHom t) from rfl` — bridges the bundled
   `RingHom.mapMatrix` to the unbundled `Matrix.map`; eliminated by
   the named mathlib lemma `RingHom.mapMatrix_apply`.

Lifted to `CLEANUP.md` bucket B as a new smell row: `show X = Y from
rfl` as a `rw`/`simp only` argument. Project-wide grep surfaces 4
additional sites (RigidityMatroid L647, MatroidIdentification L119,
TrivialMotions L312, Mathlib/Data/Finset/Card L45), out of scope for
this Phase-8-surface round but picked up by the next inter-phase
cleanup via the same grep pattern.

**B5 — Upstream-PR decision: defer.** Both new Rank.lean lemmas are
already entered in FRICTION *Mirrored* (commit `53c3a25`). No
natural batching window with the `apnelson1/Matroid` upstreaming
(disjoint LA packaging). Following the project's default for
`[mirrored]` entries — sit until a specific reason to PR surfaces.

**C1 — long-proof audit.** Two refactors on
`exists_uniform_rowIndependent_placement_dim_two`:
1. **Parallel-case unification** in `h_bad_finite`: two `rcases`
   cases (`I = I₀` at `t = 1`, `I ∈ F'` at `t = 0`) of identical
   shape modulo the witness placement, factored through a common
   `∃ t_w, EdgeSetRowIndependent (p₀ + t_w • r) I` unpacking.
2. **`Set.Finite.exists_notMem`** collapses the 3-line "`badᶜ` is
   nonempty because `bad` is finite in infinite ℝ" block to a one-
   liner.
Net: file 252 → 232 LoC; main proof 113 → 95 lines. Lint clean.

**D1 — Phase8.md compressed 253 → 236 LoC.** Three entries tightened:
*Uniform-genericity* (drops historical "original sketch failed"
narrative); *Subtype factoring* (single-site, tightened to
watch-only); resolved-blocker *Ground-set shape* (full signature
recap moved to Lean code only).

**D2 — Promote `Polynomial.X` ascription quirk to TACTICS-QUIRKS.**
Second site surfaced in Phase 8 (Rank.lean L78-79's
`(Polynomial.X : Polynomial ℝ) • B.map Polynomial.C + …` repeats the
exact workaround from `exists_affinelySpanning_rigid_placement` in
RigidityMatroid.lean, Phase 6). Lifted to TACTICS-QUIRKS § 15;
FRICTION entry flipped to `[resolved]` with cross-reference;
Quirks-index symptom table in CombinatorialRigidity/CLAUDE.md gets
the matching symptom line.

**D3 — DESIGN.md drift clean.** Two active entries
(`apnelson1/Matroid dependency` watch, `Promoting edgesIn upstream`);
no other needs Phase-8 touch.

**D4 — No-residual-lifts audit clean.** The single Phase 8 lift
entry resolves to `notes/FRICTION.md:619`.

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
