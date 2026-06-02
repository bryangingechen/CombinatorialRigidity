# Phase 18 cleanup round (work log)

**Status:** in progress (open). Task list below is comprehensive
(swept 2026-06-02 before any fix lands); resumable from this log alone.

Between-phases cleanup round, run after Phase 18 (panel-hinge rigidity
matrix `R(G,p)`, KT §2.2–2.4 + Lemmas 5.1–5.3) closed in `22a0584` and
before Phase 19 (`M(G̃)`, deficiency, `k`-dof) opens. Round manual:
`CLEANUP.md`. The per-commit friction review
(`CombinatorialRigidity/CLAUDE.md`) still fires on every commit in this
round.

This round was scoped by a **user-requested readability + attribution
review** of the recent blueprint chapters (the molecular chapter,
written fast across Phases 17–18 by separate per-commit subagents) on
top of the usual `CLEANUP.md` A–D sweeps. The review's four findings map
onto the buckets below: readability → A, citation accuracy → A/D,
instruction alignment → D (process), file split → A (judgment call).

## Current state

The Phase-18 surface is the single new Lean file
`Molecular/RigidityMatrix.lean` (545 lines, 38 decls) and the nine
`molecular.tex` `sec:molecular-rigidity-matrix` nodes (eight green +
`prop:rigidity-matrix-prop11` red/deferred-to-Phase-19 at phase close).
The **B/C sweeps came back near-no-op** (one standard `Fintype.ofFinite`
bridge, one already-justified `nolint`, no proof over 30 lines, no
`classical` / `show … from rfl`) — as `CLEANUP.md` predicts for a phase
that introduced no new long-proof shape. The substance of this round is
**Bucket A** (the molecular.tex §2.2–2.4 readability pass — formalization
narration crept back in) and **Bucket D** (`MolecularConjecture.md`
destale + `Phase18.md` compression + two instruction tweaks), plus a
**citation fix** (`jacksonJordan2009`) and a **judgment-call file split**.

## Lemma checklist (task list across A–D)

### Bucket A — Blueprint ↔ Lean divergence (the main bucket)

- [ ] **A1** — per-node `\lean{}` signature compare for the 9
  `sec:molecular-rigidity-matrix` nodes vs the Lean decls. Expected
  no-op confirm (cf. Phase17-cleanup A1).
- [x] **A2 (readability pass — highest value)** — done. Collapsed the
  formalization-implementation narration in all four spots
  (`def:hinge-row-block`, `def:rigidity-matrix`,
  `lem:trivial-motions-rank-bound` proof, `def:dof-generic`) to a
  one-clause "formalized basis-free via …" aside each. Dropped the
  in-prose `\texttt{}` decl-name lists (still pinned in each node's
  `\lean{}` block, so `checkdecls` keeps them honest). Also folded in
  the §2.2–2.4 share of A3: rewrote the collapsed prose in `d`-terms
  (`⋀^{d-1}ℝ^{d+1}`, screw space `ℝ^D` with `D=binom(d+1,2)`), removing
  every `⋀^k ℝ^{k+2}` from §2.2–2.4 (the remaining `\bigwedge^{k}` at
  L85/L157 are the legitimate Phase-17 extensor degree `k`). `verify.sh`
  green. **A3 is now nearly subsumed** — only the section-head `k=d−1`
  statement remains if any `k` survives; re-confirm when picking up A3.
- [ ] **A3** — tie the index `k` to `d`. The §2.2–2.4 prose switches to
  `⋀^k ℝ^{k+2}` (L315, 329, 389, 397, …) where `k = d−1`, but that
  relation is never stated; the reader must reverse-engineer it. State
  it once at the section head, or rewrite §2.2–2.4 prose in `d`-terms.
- [ ] **A4** — forward-mode chapter-intro destale. `molecular.tex`
  L28–39 still describes the Phase-18 nodes as "the current forward-mode
  to-do list … red until their Lean lands"; eight of nine are now green.
  Update to a closed-phase statement (recurring Phase15/16/17-cleanup A2
  shape). Re-read the §2.2–2.4 *Status* block (L237–249) — already notes
  the deferral, likely fine.
- [x] **A5 (citation accuracy)** — done. Verified against `.refs/`
  jackson-jordan-2009-generic-rank-of-body-bar.pdf: the paper has **no
  Proposition 2.3** (and no Propositions at all — §2 holds only Lemmas
  2.1–2.5, the screw-center lemmas; the rank↔deficiency bridge is
  **Theorem 6.1** `r(G,q)=D(|V|−1)−def_D(G_H)` + **Corollary 6.2** rigid
  iff `G_H` has `D` edge-disjoint spanning trees, with `def_k` defined in
  §4 after Theorem 4.1). The invented "(i)⇔(ii)/(ii)⇔(iii)" multi-part
  labels don't exist either. Fixed `prop:rigidity-matrix-prop11` proof in
  `molecular.tex` and all six `MolecularConjecture.md` mentions (the
  references list, the survey line, the Phase-19 table row + detail +
  inherited bullet, and risk-register #4) to cite Thm 6.1 / Cor 6.2.
  *Note:* "KT Prop 1.1 / Tay–Whiteley's Prop 1.1" was verified correct in
  a prior pass against KT arXiv 0902.0236 — left as is. *Not touched:* the
  bib `jacksonJordan2009` `year={2009}` reflects online-availability;
  print volume 31 is 2010 — out of A5 scope (key churn), leave for a
  later bib-accuracy pass if wanted.

### Bucket B — Code-smell sweep (near no-op)

- [ ] **B1** — `haveI : Fintype α := Fintype.ofFinite α`
  (`RigidityMatrix.lean:489`). Confirm the `[Finite α]`-bridge is the
  right boundary per `DESIGN.md` *Typeclass shape*. Expected keep.
- [ ] **B2** — `@[nolint unusedArguments]` (`RigidityMatrix.lean:281`,
  on the trivial-motions submodule whose membership ignores the graph).
  Already carries a one-line justification (L280); confirm it holds.
- [ ] **B3** — multi-arg `rw` spot-checks (`RigidityMatrix.lean:225,
  495`). Confirm each is a genuine multi-step line, not a missing fused
  mirror lemma. Expected no-op.

### Bucket C — Long-proof audit (no-op expected)

- [ ] **C1** — top proof `screwSpace_finrank` (23 lines, the
  `⋀^k ℝ^{k+2}` finrank count); under the 50-line §C screening
  threshold. Run the four-question gate as a no-extract confirm.

### Bucket D — Project-organization compression

- [ ] **D1 (destale `MolecularConjecture.md`)** — the file header still
  says "PLANNING. No phase opened yet … Nothing here is built" (L4–6)
  and "When Phase 17 is actually opened …" (L10–13), and closes with an
  "Opening Phase 17 (when greenlit)" section (L422–439) — all stale now
  that 17–18 are complete. Fixes: (a) header status → 17–18 done, 19
  next; (b) mark 17/18 ✓ in the phase table (L181–192); (c) resolve
  risk-register #3 (L406–408, Lemma 5.2 perturbation — Phase 18 chose
  the basis-free span-refinement monotonicity form, no analytic
  perturbation); (d) compress the Phase 17 + Phase 18 detail sections
  (L203–248) to brief done-summaries + pointers to `notes/Phase{17,18}.md`
  per `CLEANUP.md` §D, **preserving the carry-forward notes** (the
  Phase-19 "Inherited from Phase 18" bullet at L264–277 already records
  the `prop:rigidity-matrix-prop11` + coordinatization carry-forward —
  keep it); (e) drop/convert the "Opening Phase 17" section to a one-line
  historical pointer.
- [ ] **D2 (compress `notes/Phase18.md`)** — 499 lines, over even the
  long-phase ceiling (`notes/CLAUDE.md` *Soft length budget*). Apply the
  ≤8-line-per-entry rule, lift cross-cutting lessons (*Promoted to …*),
  and compress the now-closed plan to a commit-log pointer + summary.
- [ ] **D3** — re-skim `notes/FRICTION.md` for open Phase-18 entries;
  lift/migrate per `CLAUDE.md` *Lift on promotion*.

### Process / instruction alignment (lands in D commits)

- [ ] **P1** — `blueprint/CLAUDE.md`: name the new anti-pattern in
  *Proof verbosity* / *What to include vs skip* — "basis-free /
  coordinatization-deferral narration is changelog, not math; one clause
  max." The existing guidance is framed around structural-edit reshape
  history and a forward-mode-new-chapter subagent didn't map Phase 18's
  failure mode onto it.
- [ ] **P2** — root `CLAUDE.md` *When this commit closes a phase*: add a
  step — "re-read each new/edited blueprint chapter end-to-end as a
  domain mathematician and collapse accumulated per-commit formalization
  asides." This is the step that would have caught the A2 narration at
  phase close rather than a round later.

### Judgment call (decide in-round or defer with rationale)

- [ ] **J1 (split `molecular.tex`)** — the file (526 lines) now holds
  two full `\section`s (Phase 17 §2.1 extensor algebra + Phase 18
  §2.2–2.4 rigidity matrix), with 8 molecular phases still queued.
  Candidate: split into `extensor.tex` + `rigidity-matrix.tex` (mirroring
  the Lean `Extensor.lean`/`RigidityMatrix.lean` split and phase
  boundaries), adopt "one `.tex` per molecular phase" going forward.
  **Counter-precedent:** `body-bar.tex` deliberately holds three phases
  (13–15) in one 642-line file. Not forced; lean split given program
  length. Decide here or file to Phase 19's open. *Companion (Lean):* no
  split needed now (`RigidityMatrix.lean` is coherent at 545 lines), but
  Phase 19's `M(G̃)`/deficiency machinery should go in a **new file**
  (`Molecular/Deficiency.lean`), not bloat `RigidityMatrix.lean`.

## Blockers / open questions

- A5 / D1(part) depend on the `.refs/` Jackson–Jordán 2009 PDF being
  text-extractable (the program plan says it is, L97). If "Prop 2.3"
  can't be confirmed, soften rather than guess (CLAUDE.md bar).
- J1 is a genuine judgment call; if deferred, record the decision in
  Phase 19's open so it isn't silently dropped.

## Hand-off / next phase

A2 + A5 landed (A5: "Proposition 2.3 of Jackson–Jordán" was a
phantom — the [15] paper has no Propositions; corrected to the verified
Theorem 6.1 / Corollary 6.2 in `molecular.tex` and all six
`MolecularConjecture.md` mentions). Next concrete commit: **D1**
(`MolecularConjecture.md` destale — header status, 17/18 ✓ in the phase
table, resolve risk-register #3, compress the Phase 17/18 detail
sections to pointers, drop the stale "Opening Phase 17" section). Then the A3
section-head `k`/`d` finish + A1/A4 confirms, the B/C confirms, D2/D3,
P1/P2, and J1 last. Each fix is its own commit per `CLEANUP.md`
*Workflow* rule 3. Close the round by flipping the ROADMAP row to ✓ and
writing the *Hand-off* summary; Phase 19 opens after.
