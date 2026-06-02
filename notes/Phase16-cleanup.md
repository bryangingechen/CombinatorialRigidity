# Phase 16 cleanup round (work log)

**Status:** open — log skeleton + full A–D task list laid down (this
commit); no fixes landed yet. Smallest concrete next commit named in
*Hand-off / next phase*.

Between-phases cleanup round, run after Phase 16 (body-hinge /
panel-hinge Tay–Whiteley theorem, existence form) closed in `968e137`
and before any Phase 17 (molecular conjecture) opens. Round manual:
`CLEANUP.md`. The per-commit friction review
(`CombinatorialRigidity/CLAUDE.md`) still fires on every commit in this
round.

## Current state

Round just opened: scope decided, all four buckets' greps / file walks
run, task list below populated *before* any fix (per `CLEANUP.md`
*Workflow* rule 1 + *Task list discipline*). Build green on
`CombinatorialRigidity.BodyBar.BodyHinge` (2673 jobs) at round open.

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

- [ ] A1 — per-node `\lean{}` signature compare for all 4 Phase-16 nodes
  (`def:edge-multiply` → `Graph.edgeMultiply` + the three transport
  facts `vertexSet_edgeMultiply` / `edgeMultiply_edgeSet_ncard` /
  `spanningVerts_edgeMultiply`; `def:body-hinge-framework` →
  `Graph.BodyHingeFramework` + `.toBodyBar` + `.IsIndependent` +
  `.IsInfinitesimallyRigid`; `lem:edge-multiply-sparse` →
  `edgeMultiply_isSparse_iff`; `thm:body-hinge-tay` → `body_hinge_tay`).
  Confirm each resolves and the blueprint statement form matches the
  Lean signature (hypotheses, conclusion, binders). Expect no-op.
- [ ] A2 — re-read each Phase-16 node's prose proof for "the Lean does X
  via Y" smoothness glosses and "formalization aside" remarks (first
  response to any aside is a Lean-simplification attempt, `CLEANUP.md`
  §A). **Known finding to land:** the chapter intro (`body-hinge.tex`
  L13–16) carries the stale forward-mode "The nodes below are mostly
  *red* (no `\leanok`) on first build: this dep-graph is the to-do
  list … As each Lean declaration lands, its node gains a `\lean`
  pointer and `\leanok` in the same commit" snapshot — false now that
  Phase 16 is closed and every node green. Reword to a closed-phase
  statement (cf. Phase-15-cleanup A2's "All three phases are complete:
  every node below is formalized (green)" rewording of `body-bar.tex`).
  Doc-only; no `\lean{}` pin touched, so `checkdecls` not required;
  confirm `inv web` builds clean. Also spot-check the four node proof
  bodies for stale "next sub-step"/"in progress" asides from the
  incremental build (L110 "deferred out of Phase 15" / L147 molecular-
  conjecture pointer are legitimate documented deferrals, ROADMAP §16 —
  keep). Lean-side leg: spot-check the `BodyHinge.lean` module docstring
  / doc-comments for the same staleness (Phase-15-cleanup A2 found a
  stale "in progress" block in `TayTheorem.lean`).

### B. Code-smell sweep (greps run at round open — all zero-hit)

- [ ] B1 — `classical` invocations: **zero hits** on `BodyHinge.lean`.
  No-op confirm (no strip-build sweep needed; the file's decidability
  needs are met by the inherited Phase-13/15 API, which carries its own
  bridges).
- [ ] B2 — `letI`/`haveI : Fintype … := Fintype.ofFinite _` bridges:
  **zero hits**. No-op confirm. `edgeMultiply_isSparse_iff` /
  `body_hinge_tay` take `[Finite α] [Finite β]` in the signature and
  delegate to `tay_witness` (which carries its own inline bridges), so
  no `[Finite] → Fintype` bridge is written at this surface.
- [ ] B3 — `@[nolint …]` / `set_option linter.* false`: **zero hits**.
  No-op confirm. (The `IsInfinitesimallyRigid` `[Finite α]`-contract
  `@[nolint unusedArguments]` lives upstream in `Framework.lean`, audited
  in Phase-15-cleanup B3; the Phase-16 `IsInfinitesimallyRigid` wrapper
  takes `[Finite α]` but uses it via the delegate, no nolint needed.)
- [ ] B4 — `noncomputable def`: **zero hits**. No-op confirm.
  `edgeMultiply` and `bodyHingeMult` are plain `def`s (computable —
  `edgeMultiply` is a `Graph` structure literal, `bodyHingeMult` is
  `bodyBarDim n - 1`); `BodyHingeFramework` / `toBodyBar` are a
  `structure` + a `def` with no noncomputable ingredient. Confirm none
  silently *should* be `noncomputable` (none are — no `Classical.choose`
  / `Module.Dual` / norm in any body).
- [ ] B5 — `change`/`show` to coax `simp`/`rw`: **zero hits**. No-op
  confirm.
- [ ] B6 — 3+-arg single-step `rw` chains: **zero hits**. No-op confirm.
  (`edgeMultiply_edgeSet_ncard` has a 5-lemma `rw` but it is a genuine
  multi-step `ncard_prod` expansion, not a single mathematical step — it
  is on a 2-arg-or-fewer pattern at each step; the grep for the
  4+-comma single chain returned empty.)
- [ ] B7 — `show … from rfl`: **zero hits**. No-op confirm.

  *All seven B greps zero-hit → expect to land B1–B7 as one no-op
  confirm batch commit (cf. Phase-15-cleanup B2/B3/B5/B7 batch).*

### C. Long-proof audit

Top LoC ranking on `BodyHinge.lean` (none reach the §C 50-line
screening threshold; the top three are the audit gate per `CLEANUP.md`
*Calibration* — expect no-op confirming forced structural shape):

- [ ] C1 — `edgeMultiply_isSparse_iff` (~26 lines, L227). Audit gate:
  the proof is `obtain ⟨hsparse, htight⟩ := tay_witness …` then two
  symmetric `rw [← h…]; constructor; rintro …` legs bridging the
  body-hinge ⇔ body-bar existentials via `exists_toBodyBar_iff` (the
  `.trans`-blocked transport, FRICTION → TACTICS-QUIRKS § 25). Expect
  no-op: the two legs are the forced sparse/tight symmetric shape, no
  cover-fusing lemma, the bijection is already a named helper.
- [ ] C2 — `exists_toBodyBar_iff` (~21 lines, L202) /
  `toBodyBar_placement` (~19 lines, L177). Audit gate: the
  `exists_toBodyBar_iff` reverse direction's `cases Fb … cases hgraph;
  rfl` placement-transport wiring — expect forced (the `hgraph ▸`
  placement coercion is the content of the bijection, no extraction).
- [ ] C3 — `spanningVerts_edgeMultiply` (~20 lines, L101). Audit gate:
  the `ext x; simp only …; constructor` membership-transport with the
  `[NeZero m]`-driven copy pick `(e, ⟨0, …⟩)` on the reverse — expect
  forced (the `NeZero`-witness is the content). No cross-proof
  unification candidate (C1 is the Tay transport, C2/C3 the
  framework/spanning bookkeeping — disjoint shapes).

### D. Project-organization compression

- [ ] D1 — `notes/Phase16.md` is **172 lines, under the 250 soft
  budget**, so no compression forced. Spot-check only: confirm the
  *Current state* + *Hand-off* still pass the hand-off contract and the
  *Decisions made* entries respect the ≤8-line rule (they do at phase
  close). Likely no-op (a short phase, 4 forward-work commits, sits
  naturally near 170 lines per `notes/CLAUDE.md` *Soft length budget*).
- [ ] D2 — re-skim `FRICTION.md` status sections. **Migrate candidate:**
  the one Phase-16 `[resolved]` entry — `refine h.trans ?_` over a
  defeq-but-not-syntactic iff side (L79–95), consumer
  `edgeMultiply_isSparse_iff`, already fully indexed by TACTICS-QUIRKS
  § 25 — to `FRICTION-archive.md` (it has no forward reference if Phase
  17 stays unopened). Re-assess the four Phase-13/14 `[matroid]` entries
  Phase-15-cleanup D2 kept active: they are `apnelson1/Matroid`-API
  idioms the body-bar chain reuses; keep active only if a Phase-17
  open would still forward-reference them — otherwise this is the round
  to migrate them too. No TACTICS lift (the migrate candidate is already
  lifted).

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

<none yet — fixes land in subsequent commits>

## Blockers / open questions

<none at round open>

## Hand-off / next phase

**Round just opened — log skeleton + full A–D task list laid down this
commit; no fixes yet.** Build green at open (2673 jobs on
`BodyBar.BodyHinge`). The Phase-16 surface is small (one Lean file +
four blueprint nodes) and the B greps are all zero-hit, so the round is
expected to be light: one genuine doc fix (A2), one no-op confirm batch
(B), no-op long-proof confirms (C), and one FRICTION migrate (D2).

**Smallest concrete next commit:** land **A2** — reword the stale
forward-mode chapter-intro snapshot in `body-hinge.tex` (L13–16, "The
nodes below are mostly *red* … this dep-graph is the to-do list …") to
a closed-phase statement, matching Phase-15-cleanup A2's `body-bar.tex`
destale. Doc-only blueprint edit; no `\lean{}` pin touched (so no
`checkdecls`), confirm `inv web` builds clean. Then A1 (signature
compare, no-op), the B1–B7 no-op confirm batch, C1–C3 no-op confirms,
and D1/D2. A fresh session can resume from this log alone.
