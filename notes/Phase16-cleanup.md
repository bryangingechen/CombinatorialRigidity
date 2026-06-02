# Phase 16 cleanup round (work log)

**Status:** ✓ Complete — A landed (A2 chapter-intro destale + A1
signature-compare no-op + A2 Lean-side `BodyHinge.lean` docstring
destale). B closed (B1–B7 no-op confirm batch — all seven greps
re-run zero-hit on `BodyHinge.lean`). C closed (C1–C3 long-proof
audit-gate no-op confirm batch — top three proofs forced structural
shape, no extraction). D closed this commit (D1 `notes/Phase16.md`
spot-check no-op; D2 migrated the one Phase-16 `[resolved]` FRICTION
entry to `FRICTION-archive.md`, kept the four Phase-13/14 `[matroid]`
entries active). Round closed; ROADMAP row flipped to ✓.

Between-phases cleanup round, run after Phase 16 (body-hinge /
panel-hinge Tay–Whiteley theorem, existence form) closed in `968e137`
and before any Phase 17 (molecular conjecture) opens. Round manual:
`CLEANUP.md`. The per-commit friction review
(`CombinatorialRigidity/CLAUDE.md`) still fires on every commit in this
round.

## Current state

Bucket **A closed**: A2 chapter-intro destale (`body-hinge.tex`
L13–16); A1 signature compare (no-op — all 10 pins resolve via
`checkdecls`, statement forms match node-for-node); and A2's Lean-side
leg — a second genuine doc finding, the `BodyHinge.lean` module
docstring's *Contents* list called itself the "lower" nodes and listed
only the two definition nodes, now reworded to all four. Build green on
`CombinatorialRigidity.BodyBar.BodyHinge` (2673 jobs); `checkdecls`
exit 0. Bucket **B closed**: the seven code-smell greps re-run
zero-hit on `BodyHinge.lean` (confirm-and-close, doc-only — no Lean
touched, so no build/lint/`checkdecls` gate fires). Bucket **C closed**
this commit: the LoC ranking re-run at close confirms none of
`BodyHinge.lean`'s proofs reach the §C 50-line threshold (top three:
`edgeMultiply_isSparse_iff` ~26L, `spanningVerts_edgeMultiply` ~20L,
`exists_toBodyBar_iff` ~13L), and the four-question audit gate on each
confirms forced structural shape — no extraction, no cross-proof
unification candidate (disjoint per-step shapes per `CLEANUP.md`
*Calibration*). Doc-only no-op confirm batch, no Lean touched.
Remaining: D1/D2.

The Phase-16 surface is small and uniform: a single new Lean file
(`BodyBar/BodyHinge.lean`, 279 lines) and four `body-hinge.tex` nodes,
all green at phase close. The code-smell greps (B) all came back
**zero-hit** on `BodyHinge.lean` — no `classical`, no
`Fintype.ofFinite`/`Finite`-bridge `letI`/`haveI`, no `nolint` /
`set_option linter`, no `noncomputable def`, no `change`/`show`, no
3+-arg `rw` chains, no `show … from rfl`. So B is expected to close as
a single no-op confirm batch. The two substantive findings to date are
both doc-only: **A2** (a stale forward-mode chapter-intro snapshot in
`body-hinge.tex` L13–16, exactly the shape Phase-15-cleanup A2 found)
and **D2** (one Phase-16 `[resolved]` FRICTION entry already lifted to
TACTICS-QUIRKS § 25, a migrate-to-archive candidate). The smallest
concrete next commit is **A2** (reword the stale intro prose); see
*Hand-off / next phase*.

## Scope

Phase 16 surface — one new Lean file + the four Phase-16 blueprint
nodes. No new `CombinatorialRigidity/Mathlib/` adders shipped in Phase
16 (the phase reused Phase-13/15 API — `tay_witness`,
`tutte_nash_williams`, `Graph.IsSparse`/`IsTight` — and added only the
edge-multiplication device and framework wrapper, no upstream-eligible
facts), so the mirror-directory leg of the usual sweep is empty.

- **(A) Blueprint ↔ Lean divergence** — `body-hinge.tex`
  §`sec:body-hinge` (4 nodes: `def:edge-multiply`,
  `def:body-hinge-framework`, `lem:edge-multiply-sparse`,
  `thm:body-hinge-tay`). All green at phase close; expect mostly no-op
  on the per-node signature compare (A1). One genuine stale-prose
  finding already surfaced for the prose re-read leg (A2): the chapter
  intro (L13–16) still carries the forward-mode "nodes below are mostly
  *red* (no `\leanok`) on first build: this dep-graph is the to-do
  list" snapshot, now false (Phase 16 closed, every node green) — same
  finding shape as Phase-15-cleanup A2's chapter-intro destale.
- **(B) Code-smell sweep** — `BodyBar/BodyHinge.lean`. All seven greps
  run at round open returned **zero hits** (findings recorded per-row
  in the task list); expect a single no-op confirm batch.
- **(C) Long-proof audit** — top LoC ranking on `BodyHinge.lean`. No
  proof reaches the §C 50-line screening threshold (longest is
  `edgeMultiply_isSparse_iff` at ~26 lines); the top 2–3 are the audit
  gate per `CLEANUP.md` *Calibration*, expect no-op confirm of forced
  structural shape (the iff-pair + transport-bijection wiring).
- **(D) Project-organization compression** — `notes/Phase16.md` is 172
  lines, under the 250 soft budget, so no compression forced; spot-check
  only. Re-skim `FRICTION.md` status sections for the one Phase-16
  `[resolved]` entry (`refine h.trans ?_` over a defeq-but-not-syntactic
  iff side, L79–95) already fully indexed by TACTICS-QUIRKS § 25 — a
  migrate-to-`FRICTION-archive.md` candidate, modulo the keep-active
  logic for the four Phase-13/14 `[matroid]` entries the body-bar chain
  reuses (Phase-15-cleanup D2 kept them; re-assess whether Phase 17, if
  opened, still forward-references them).

## Task list

### A. Blueprint ↔ Lean divergence audit

- [x] A1 — per-node `\lean{}` signature compare for all 4 Phase-16 nodes
  (`def:edge-multiply` → `Graph.edgeMultiply` + the three transport
  facts `vertexSet_edgeMultiply` / `edgeMultiply_edgeSet_ncard` /
  `spanningVerts_edgeMultiply`; `def:body-hinge-framework` →
  `Graph.BodyHingeFramework` + `.toBodyBar` + `.IsIndependent` +
  `.IsInfinitesimallyRigid`; `lem:edge-multiply-sparse` →
  `edgeMultiply_isSparse_iff`; `thm:body-hinge-tay` → `body_hinge_tay`).
  **No-op on the signature compare:** all 10 pins resolve (`checkdecls`
  exit 0, incl. the `@[simps! vertexSet]`-generated
  `vertexSet_edgeMultiply : V(G.edgeMultiply m) = V(G)`), and each
  blueprint statement form matches the Lean signature — the two iff-pair
  nodes' `[Finite α] [Finite β]` binders and the `(resp. isostatic/tight)`
  conjunction shape line up node-for-node. **Lean-side leg of A2 was the
  genuine fix this commit:** see A2 below.
- [x] A2 — re-read each Phase-16 node's prose proof for "the Lean does X
  via Y" smoothness glosses and "formalization aside" remarks (first
  response to any aside is a Lean-simplification attempt, `CLEANUP.md`
  §A). **Landed:** the chapter intro (`body-hinge.tex` L13–16) carried
  the stale forward-mode "The nodes below are mostly *red* (no `\leanok`)
  on first build: this dep-graph is the to-do list … As each Lean
  declaration lands, its node gains a `\lean` pointer and `\leanok` in
  the same commit" snapshot — false now that Phase 16 is closed and
  every node green. Reworded to a closed-phase statement ("Phase 16 is
  complete: every node below is formalized (green), with its `\lean{}`
  pointer resolving …"), matching Phase-15-cleanup A2's `body-bar.tex`
  destale. The four node proof bodies carried no stale asides (L110
  "deferred out of Phase 15" / L147 molecular-conjecture pointer are
  legitimate documented deferrals, ROADMAP §16 — kept). Doc-only; no
  `\lean{}` pin touched (so `checkdecls` not required); `inv web` builds
  clean. **Lean-side leg landed (A1 commit):** the `BodyHinge.lean`
  module docstring's *Contents* list (L21–27) read "This file lands the
  **lower** `body-hinge.tex` dep-graph nodes:" and enumerated only the
  two definition nodes (`def:edge-multiply`, `def:body-hinge-framework`)
  — stale incremental-build prose, since the single Phase-16 Lean file
  in fact lands all four nodes including the two upper ones
  (`lem:edge-multiply-sparse`, `thm:body-hinge-tay`, the chapter target).
  Reworded to "lands all four … nodes of Phase 16" + two added bullets,
  same finding shape as Phase-15-cleanup A2's `TayTheorem.lean`
  *Current state → Contents* destale (`0237b19`). Doc-comment-only;
  build + lint green and warning-clean, `checkdecls` exit 0 (re-run
  since the file changed; no pin touched).

### B. Code-smell sweep (greps run at round open — all zero-hit; re-confirmed at close)

- [x] B1 — `classical` invocations: **zero hits** on `BodyHinge.lean`.
  No-op confirm (no strip-build sweep needed; the file's decidability
  needs are met by the inherited Phase-13/15 API, which carries its own
  bridges).
- [x] B2 — `letI`/`haveI : Fintype … := Fintype.ofFinite _` bridges:
  **zero hits**. No-op confirm. `edgeMultiply_isSparse_iff` /
  `body_hinge_tay` take `[Finite α] [Finite β]` in the signature and
  delegate to `tay_witness` (which carries its own inline bridges), so
  no `[Finite] → Fintype` bridge is written at this surface.
- [x] B3 — `@[nolint …]` / `set_option linter.* false`: **zero hits**.
  No-op confirm. (The `IsInfinitesimallyRigid` `[Finite α]`-contract
  `@[nolint unusedArguments]` lives upstream in `Framework.lean`, audited
  in Phase-15-cleanup B3; the Phase-16 `IsInfinitesimallyRigid` wrapper
  takes `[Finite α]` but uses it via the delegate, no nolint needed.)
- [x] B4 — `noncomputable def`: **zero hits**. No-op confirm.
  `edgeMultiply` and `bodyHingeMult` are plain `def`s (computable —
  `edgeMultiply` is a `Graph` structure literal, `bodyHingeMult` is
  `bodyBarDim n - 1`); `BodyHingeFramework` / `toBodyBar` are a
  `structure` + a `def` with no noncomputable ingredient. Confirm none
  silently *should* be `noncomputable` (none are — no `Classical.choose`
  / `Module.Dual` / norm in any body).
- [x] B5 — `change`/`show` to coax `simp`/`rw`: **zero hits**. No-op
  confirm.
- [x] B6 — 3+-arg single-step `rw` chains: **zero hits**. No-op confirm.
  (`edgeMultiply_edgeSet_ncard` has a 5-lemma `rw` but it is a genuine
  multi-step `ncard_prod` expansion, not a single mathematical step — it
  is on a 2-arg-or-fewer pattern at each step; the grep for the
  4+-comma single chain returned empty.)
- [x] B7 — `show … from rfl`: **zero hits**. No-op confirm.

  *All seven B greps zero-hit → landed B1–B7 as one no-op confirm
  batch commit (re-run at close, exit 1 each; cf. Phase-15-cleanup
  B2/B3/B5/B7 batch).*

### C. Long-proof audit (LoC ranking re-run at close — none reach the §C 50-line threshold; all three no-op)

Top LoC ranking on `BodyHinge.lean` re-run at close (awk attributes the
`exists_toBodyBar_iff` body span to the trailing `toBodyBar_placement`
line by its blank-line heuristic — the real proof spans are
`edgeMultiply_isSparse_iff` ~26L, `spanningVerts_edgeMultiply` ~20L,
`exists_toBodyBar_iff` ~13L). None reach the §C 50-line screening
threshold; the top three are the audit gate per `CLEANUP.md`
*Calibration* — all confirm forced structural shape (no-op):

- [x] C1 — `edgeMultiply_isSparse_iff` (~26 lines, L232). Audit gate
  walked, no-op:
  the proof is `obtain ⟨hsparse, htight⟩ := tay_witness …` then two
  symmetric `rw [← h…]; constructor; rintro …` legs bridging the
  body-hinge ⇔ body-bar existentials via `exists_toBodyBar_iff` (the
  `.trans`-blocked transport, FRICTION → TACTICS-QUIRKS § 25). The two
  legs are the forced sparse/tight symmetric shape, no cover-fusing
  lemma, the bijection is already a named helper; no mathlib lemma
  collapses the existential transport, `grind` cannot fire across the
  `def`-predicate `IsIndependent` / `IsInfinitesimallyRigid` unfold.
- [x] C2 — `exists_toBodyBar_iff` (~13 lines, L207). Audit gate walked,
  no-op: the reverse direction's `cases Fb … cases hgraph; rfl`
  placement-transport wiring is forced — the `hgraph ▸` placement
  coercion is the content of the bijection, no self-contained sub-lemma
  another proof would call (its sole consumer is C1).
- [x] C3 — `spanningVerts_edgeMultiply` (~20 lines, L106). Audit gate
  walked, no-op: the `ext x; simp only …; constructor`
  membership-transport with the `[NeZero m]`-driven copy pick
  `(e, ⟨0, …⟩)` on the reverse is forced — the `NeZero`-witness is the
  content. No cross-proof unification candidate (C1 is the Tay
  transport, C2 the framework bookkeeping, C3 the spanning-verts
  bookkeeping — disjoint per-step shapes, matching `CLEANUP.md`
  *Calibration*).

  *All three C audit gates confirm forced structural shape → landed
  C1–C3 as one no-op confirm batch commit (doc-only — no Lean touched,
  so no build/lint/`checkdecls` gate fires; cf. the B1–B7 batch above).*

### D. Project-organization compression

- [x] D1 — `notes/Phase16.md` is **172 lines, under the 250 soft
  budget**, so no compression forced. Spot-checked, **no-op**: *Current
  state* + *Hand-off* pass the hand-off contract (name the molecular-
  conjecture Phase 17 concretely as the next phase), and the *Decisions
  made* entries all respect the ≤8-line rule. Sits naturally near 170
  lines for a short phase (4 forward-work commits) per `notes/CLAUDE.md`
  *Soft length budget*.
- [x] D2 — re-skimmed `FRICTION.md` status sections. **Migrated** the one
  Phase-16 `[resolved]` entry — `refine h.trans ?_` over a defeq-but-not-
  syntactic iff side (was L79–95), consumer `edgeMultiply_isSparse_iff`,
  fully indexed by TACTICS-QUIRKS § 25 — to `FRICTION-archive.md` with a
  *Migrated from FRICTION.md … (D2)* note; it has no forward reference
  (Phase 17 unopened). **Kept active** the four Phase-13/14 `[matroid]`
  entries (`Matroid.Union` `[DecidableEq β]`-binder, `signedIncMatrix`
  decidability-`letI`, `Matroid.Union`-ground-is-`univ`,
  `Graph.Components`-`Finite`): none is `Lifted to:` a TACTICS section —
  each is the sole living record of an `apnelson1/Matroid`-rebase idiom
  the body-bar/body-hinge chain reuses, so each remains a live forward
  reference for a Phase-17 open (which would build on the same matroid-
  union chain). Same keep-active disposition as Phase-15-cleanup D2. No
  TACTICS lift (the migrated entry is already lifted).

### Non-A–D items noted during the sweep

- **`BodyBar/BodyHinge.lean` is non-`module`** (no `module` marker, plain
  `import`, no `@[expose] public section`). **Forced, not a regression**:
  it imports the `BodyBar/{TreePacking,Framework,TayTheorem}.lean` chain,
  which (whole Phase 13–16 subtree) depends on the `apnelson1/Matroid`
  package, only ~4 % `module`-converted — a `module` file cannot import a
  non-`module` file. Same constraint + disposition as Phase-15-cleanup's
  same note and `CombinatorialRigidity/CLAUDE.md` *Module-system
  conversion* → *Some external dependencies block conversion*. No action;
  recorded so the next round doesn't re-investigate.

## Decisions made during this round

- **D2 keep-active criterion for the four `[matroid]` entries.** Migrated
  only the Phase-16 `[resolved]` entry (TACTICS-QUIRKS § 25-indexed, no
  Phase-17 forward ref). The four Phase-13/14 `[matroid]` `apnelson1/Matroid`-
  rebase idioms stayed active: none is lifted to a TACTICS section, so each
  is the sole living record of its gotcha, and a Phase-17 (molecular) open
  would build on the same matroid-union chain — same disposition as
  Phase-15-cleanup D2.

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**Round complete — all four buckets closed.** Build green (2673 jobs on
`BodyBar.BodyHinge`), `checkdecls` exit 0, `lake lint` clean (no Lean
touched in D, so no gate re-fired this commit). ROADMAP Status row
flipped to ✓.

Summary of the round:
- **A** — two genuine doc findings, both A2 (the `body-hinge.tex`
  chapter-intro forward-mode destale and the `BodyHinge.lean`
  *Contents*-list destale); A1's per-node signature compare was a no-op
  (all 10 pins resolve, statement forms match node-for-node).
- **B** — single no-op confirm batch; all seven code-smell greps
  zero-hit on `BodyHinge.lean`.
- **C** — single no-op confirm batch; top three proofs
  (`edgeMultiply_isSparse_iff` ~26L, `spanningVerts_edgeMultiply` ~20L,
  `exists_toBodyBar_iff` ~13L) all forced structural shape, no
  extraction, disjoint per-step shapes (`CLEANUP.md` *Calibration*).
- **D** (this commit) — D1 spot-check of `notes/Phase16.md` no-op (172
  lines, under budget, contract + ≤8-line rule both pass); D2 migrated
  the one Phase-16 `[resolved]` FRICTION entry to `FRICTION-archive.md`
  and kept the four Phase-13/14 `[matroid]` entries active (sole living
  record of `apnelson1/Matroid`-rebase idioms; live forward reference
  for a Phase-17 open).

**Next:** no follow-on cleanup. The next phase is the molecular
conjecture (Tay–Whiteley / Katoh–Tanigawa 2011) — a longer-horizon
**Phase 17**, not opened; opening it starts (forward mode) by drafting a
new `molecular.tex` chapter dep-graph and `notes/Phase17.md` (see
`notes/Phase16.md` *Hand-off*). A fresh session can resume from this log
plus ROADMAP §16 alone.
