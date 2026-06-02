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

**Update (P1 landed):** Buckets A/B/C closed; D1 + D2 + D3 done; P1
done. Remaining: **P2** (instruction tweak, next), **J1** (judgment
call). See *Hand-off*.

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

- [x] **A1** — done (no-op confirm). `verify.sh`'s `checkdecls` resolves
  every `\lean{}` name across the 9 `sec:molecular-rigidity-matrix` nodes;
  spot-check of the `RigidityMatrix.lean` outline (BodyHingeFramework,
  ScrewSpace, screwDim, screwSpace_finrank, the trivial-motion family,
  IsInfinitesimallyRigid) matches the pinned signatures.
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
- [x] **A3** — done (subsumed by A2). Re-confirmed: no standalone `k`
  index survives anywhere in §2.2–2.4 (line 216 onward); the prose is
  fully in `d`-terms (`⋀^{d-1}ℝ^{d+1}`, `D=binom(d+1,2)`). The three
  remaining `k` (L85/86/157) are all in §2.1, the legitimate general
  extensor degree. No section-head `k=d−1` statement is needed — the
  reader never meets a bare `k` in §2.2–2.4 to reverse-engineer.
- [x] **A4** — done. Rewrote `molecular.tex` chapter-intro L28–39: the
  Phase-18 nodes are no longer "the current forward-mode to-do list …
  red", but "likewise formalized save for the single reconciliation node
  `prop:rigidity-matrix-prop11`, deferred to Phase 19". The §2.2–2.4
  *Status* block (L237–249) already notes the deferral + green state —
  re-read, fine, left as is.
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

- [x] **B1** — done (no-op confirm, keep). `haveI : Fintype α :=
  Fintype.ofFinite α` (`RigidityMatrix.lean:489`) is the `[Finite α]`
  → `Fintype` bridge inside `finrank_pinnedMotions_add_screwDim`,
  whose signature takes `[Finite α]` (L485) and whose proof needs
  `Fintype` for `Submodule.finrank_sup_add_finrank_inf_eq`. This is
  the sanctioned `[Finite α]`-bridge boundary (`DESIGN.md` typeclass
  shape) — the public API stays `[Finite α]`, the bridge is local.
- [x] **B2** — done (no-op confirm, keep). `@[nolint unusedArguments]`
  (`RigidityMatrix.lean:281`) on `trivialMotions (_F : …)`. Doc L278–280
  already justifies it: `_F` exists only for the `F.trivialMotions`
  dot-notation parallel to `F.infinitesimalMotions`; the space depends
  only on `α`, `k` (constant assignments), not the graph/hinges.
  Genuine false positive, justification holds.
- [x] **B3** — done (no-op confirm). Both sites are genuine multi-step
  lines, no missing fused mirror. L225 `rw [hingeConstraint,
  hingeConstraint, ← neg_sub …, Submodule.neg_mem_iff]` unfolds the
  same predicate at two distinct positions then takes one algebraic
  step (`hingeConstraint_comm`). L495 `rw [hdisj, hsup, finrank_bot,
  add_zero, F.finrank_trivialMotions]` substitutes five distinct
  named `have`s/lemmas into the dimension-counting identity.

### Bucket C — Long-proof audit (no-op expected)

- [x] **C1** — done (no-op confirm). `screwSpace_finrank`
  (`RigidityMatrix.lean:93–96`) is in fact a **4-line** finrank count
  (`rw [exteriorPower.finrank_eq, Module.finrank_pi, Fintype.card_fin,
  screwDim, ← Nat.choose_symm …]; congr 1`), well under the 50-line §C
  threshold (the "23 lines" in the sweep was a stale over-count). Four-
  question gate: no self-contained sub-lemma to extract (single finrank
  computation); no missed mathlib lemma (already chains
  `exteriorPower.finrank_eq` / `Module.finrank_pi` / `Nat.choose_symm`);
  no tactic-substitution win; no definitional refactor. No-extract.

### Bucket D — Project-organization compression

- [x] **D1 (destale `MolecularConjecture.md`)** — done. (a) header
  status → IN PROGRESS, 17–18 done / 19 next; (b) marked 17/18 ✓ in the
  phase table; (c) resolved risk-register #3 (Lemma 5.2 — Phase 18 chose
  the basis-free span-refinement monotonicity form, no analytic
  perturbation); (d) compressed the Phase 17 + Phase 18 detail sections
  to brief done-summaries + pointers to `notes/Phase{17,18}.md`,
  preserving the Phase-19 "Inherited from Phase 18" carry-forward bullet;
  (e) converted the "Opening Phase 17" section to a generic "Opening the
  next phase" pointer.
- [x] **D2 (compress `notes/Phase18.md`)** — done. 499 → 275 lines (in
  line with Phase17.md's 223 for a comparable molecular-program phase,
  under the long-phase ceiling). Collapsed the *Current state* +
  per-node *Landed so far* narrative (it triplicated *Lemma checklist* +
  *Hand-off*) to one architectural paragraph; tightened every *Decisions*
  entry to ≤8 lines; replaced the two FRICTION-lifted entries (the
  `smul_sub` graded-piece stall, the `Module.finrank_pi_const` mirror)
  with one-line *Promoted to FRICTION* pointers per `notes/CLAUDE.md`
  "Don't duplicate FRICTION explanations". Also **folded in the A5
  citation fix's reach into this file** (out of A5's stated scope, which
  only touched `molecular.tex` + `MolecularConjecture.md`): the five
  stale phantom "Prop 2.3 [15]" references are now "JJ [15] Thm 6.1 /
  Cor 6.2", with one explanatory line in *Citations verified* noting the
  phantom + pointing at A5 — so compressing didn't silently re-propagate
  the bad citation.
- [x] **D3** — done. Re-skimmed `notes/FRICTION.md` for Phase-18 entries.
  Two surfaced: the `[mirrored]` `Module.finrank_pi_const` (correctly
  placed + indexed, left as is) and the `[resolved]` `simp [← smul_sub]`
  graded-piece-subtype entry that was living in the **Open** section. The
  latter carried a buried cross-cutting rescue lesson ("over a
  `RingQuot`-built algebra subtype, prefer explicit `rw` of the
  `AddCommGroup`/`Module` identity over `simp [← lemma]`") — exactly the
  "don't bury a general rule in a `[resolved]` entry" smell FRICTION's
  scope rule warns against. Lifted the lesson to **TACTICS-QUIRKS § 26**
  (new section + sections-list entry), migrated the worked
  `infinitesimalMotions.smul_mem'` case study to `FRICTION-archive.md`
  with a `**Lifted to:** § 26` index, struck the FRICTION.md Open entry to
  a one-line migration pointer, and re-pointed both Phase18.md references
  (the *Promoted to FRICTION* bullet + the *Carrier compatibility*
  mention) at § 26. The two open Phase-17 entries
  (`ιMulti_ne_zero_iff_linearIndependent`, …) stay open — single
  callsite, upstream-eligible, not Phase-18.

### Process / instruction alignment (lands in D commits)

- [x] **P1** — done. Added an **"Anti-pattern: basis-free /
  coordinatization-deferral narration"** paragraph to `blueprint/CLAUDE.md`
  *Proof verbosity* (after the existing failure-mode paragraph, before
  *Static checks*). Framed as the mirror failure of the *Note*-the-cost
  case: representation-choice narration ("formalized basis-free",
  "abstract graded piece rather than a basis") is changelog, not math —
  one clause max and only when the modelling choice is load-bearing for a
  later node, else cut. Names the accretion mechanism (per-commit subagent
  narrates its own modelling choice) and the four Phase-18 §2.2–2.4 sites
  A2 collapsed. Chose *Proof verbosity* over *What to include vs skip* — it
  is about prose content of a node that *is* included, not about
  inclusion. Doc-only; `verify.sh` not run (no `.tex`/`\lean{}` touched).
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

Buckets A, B, C are **closed**. Bucket A: A2 + A5 landed earlier; A1
(no-op confirm via `checkdecls` + outline spot-check), A3 (subsumed by
A2), A4 (chapter-intro destale) landed in `46b269f`. D1 landed earlier.
Buckets B/C: this commit batched the four expected no-op confirms
(B1 `Fintype.ofFinite` `[Finite α]`-bridge keep, B2 `nolint` justification
holds, B3 both multi-arg `rw` sites genuine multi-step, C1
`screwSpace_finrank` 4-line no-extract gate) — all confirm-only, no Lean
edit, build re-verified warning-clean.

D3 + P1 landed (P1: the basis-free / coordinatization-deferral-narration
anti-pattern is now named in `blueprint/CLAUDE.md` *Proof verbosity*, framed
as the mirror of the *Note*-the-cost case — representation-choice narration
is changelog, not math, one clause max). Next concrete commit: **P2** (root
`CLAUDE.md` *When this commit closes a phase*: add the "re-read each
new/edited blueprint chapter end-to-end as a domain mathematician and
collapse accumulated per-commit formalization asides" step — the step that
would have caught the A2 narration at phase close rather than a round
later). Then **J1** last (split `molecular.tex`, a judgment call — decide
or defer to Phase 19's open with rationale). Each fix is its own commit
per `CLEANUP.md` *Workflow* rule 3. Close the round by flipping the
ROADMAP row to ✓ and writing the *Hand-off* summary; Phase 19 opens
after.
