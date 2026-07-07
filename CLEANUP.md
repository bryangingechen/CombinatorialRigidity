# Cleanup rounds — operating manual

This file is the project's **cleanup-round reference**: how to run a
between-phases (or post-phase) audit pass that surveys what already
shipped, rather than the per-commit friction review that fires on
work-in-progress.

For per-commit / end-of-session discipline, see
`CombinatorialRigidity/CLAUDE.md` *Friction review*. That review keeps
new friction from accumulating silently; this file's review *discharges*
debt that the per-commit review didn't catch (because the lesson only
becomes visible across many proofs, or because a "standard idiom"
worth re-examining was waved through earlier).

For golfing idioms / rescue patterns, see `TACTICS-GOLF.md` /
`TACTICS-QUIRKS.md` — cross-cutting lessons surfaced by a cleanup round
land there, not here.

## When to run a cleanup round

- **Between phases**, before opening the next phase's work log. The
  default cadence. A finished phase is a natural moment to step back
  before the next dependency-introducing decisions.
- **When a `notes/PhaseN.md` has gone finished-heavy** (*Decisions made*
  outweighs the forward sections) **or trips the ~500-line tripwire**
  (cf. `notes/CLAUDE.md` *Forward-weighted note*) — which now signals the
  per-commit *Compress-in-commit* gate was skipped, since rebalancing is
  meant to happen continuously. Compress it and bundle related sweeps so
  the next agent sees the slimmer notes.
- **When the friction log accumulates four+ open entries** of the
  same shape (e.g. four "I had to write `letI : Fintype V := …`"
  entries → consider a typeclass-boundary sweep).
- **After a major API addition** that may have left earlier files
  using a now-superseded pattern (e.g. a new helper that subsumes
  three older multi-step proofs).
- **Ad-hoc**, when an agent or user spots a code-smell pattern worth
  surveying systematically.

## Three audit categories

A cleanup round picks some subset of these; the round's work log
records which were in scope and why.

### A. Blueprint ↔ Lean divergence audit

The bias is **fix Lean first**. `blueprint/CLAUDE.md` (*Proof
verbosity*) states the principle: "First make Lean as painless as the
math; only then add prose asides." A cleanup round operationalises
that across the existing corpus.

For each chapter under `blueprint/src/chapter/`:

1. For each `\lean{...}` entry, compare the blueprint statement form
   against the Lean declaration's signature. Flag any mismatch in
   hypotheses, conclusion form, or implicit/explicit binders. Two
   distinct failure modes hide here, and the second is easy to miss
   if you only hunt the first:
   - *Prose oversells the Lean* — the smoothness-gloss case the rest
     of this section is about (a prose proof claiming an argument the
     Lean can't sustain).
   - *Hypothesis laundering* — a **`\leanok` node carrying a
     load-bearing hypothesis** (the hard part assumed, not proved)
     that is neither discharged in the Lean body nor the conclusion
     of a node it `\uses{...}`. This is a dishonestly-green node and
     should be red. This audit is the **between-phases safety net**
     for the per-commit honesty gate in `blueprint/CLAUDE.md`
     (*Static checks before commit → every hypothesis of a `\leanok`
     node is discharged*) — that gate should have caught it at the
     commit that added `\leanok`; §A is where a missed one surfaces.
     Walk every `\leanok` node's hypotheses against its `\uses` edges,
     not just the ones with suspicious prose. Phase 21b's
     `lem:case-I-realization` (a producer lemma assuming the rigidity
     it was named to construct) is the calibration case.
2. Re-read each prose proof. If it suggests "the Lean does X via Y"
   where Y is harder than X, that's a candidate for Lean
   simplification — the blueprint shouldn't be carrying a smoothness
   gloss the Lean can't sustain.
3. Look for "formalization aside" remarks. Each one is a flag: the
   round's first response is to attempt a Lean simplification that
   eliminates the aside. Only if simplification fails does the aside
   stay (and become more concrete about what residual cost remains).

`checkdecls` is the always-on per-commit gate that verifies every
`\lean{...}` still resolves; it lives in `blueprint/CLAUDE.md`
*Static checks before commit* and runs on every commit that touches a
blueprint pointer (cf. `CombinatorialRigidity/CLAUDE.md` *Before each
commit — build and lint gates*). A cleanup round does not need a
separate "run checkdecls" task — failures of that gate are caught
in-commit, not in a post-hoc audit.

The friction direction matters: we **prefer to shorten the Lean**
rather than add a prose aside. If a Lean simplification attempt fails,
the cleanup-round log records *what was tried* so the next round
doesn't re-litigate, plus the aside that was added in its place.

### B. Code-smell sweep

Concrete grep targets in this repo. Each smell is its own commit
(or small cluster); the goal is principled root-cause fixes, not
local workarounds.

| Smell | Grep | Question to ask each site |
|---|---|---|
| `classical` invocations | `grep -n "^\s*classical$\|^\s*classical *--" CombinatorialRigidity/*.lean` | Is `[DecidableEq V]` / `[DecidableRel G.Adj]` a cleaner boundary, or is the decidability genuinely unavailable here? |
| `letI : Fintype V := Fintype.ofFinite V` (and `haveI`) | `grep -nE "letI\|haveI.*(Fintype.ofFinite\|Set.Finite.fintype)" CombinatorialRigidity/*.lean` | Should the caller take `[Fintype V]`, or is the `[Finite V]`-bridge the right boundary? Is the same `haveI` repeated across many sites suggesting a single helper? |
| `@[nolint …]` / `set_option linter.* false` | `grep -nE "@\[nolint\|set_option linter" CombinatorialRigidity/*.lean` | Why was the lint silenced? Is the underlying issue still present, or has mathlib evolved past it? Each site should have a one-line comment justifying it. |
| `noncomputable def` | `grep -n "noncomputable def" CombinatorialRigidity/*.lean` | Is the keyword forced (`Classical.choose`, `Module.Dual`, no `Decidable` instance for the body)? Or accidental? |
| `Set` vs `Finset` mixing | manual; look for `.toFinset` / `Set.ncard_coe_finset` chains | Does the definition belong in `Set` form (avoid `[Fintype V]` requirement) per `DESIGN.md` *`Set.ncard` over `Finset.card`*, or is the proof site obviously cleaner with a `Finset`-form companion? |
| `change` / `show` to coax `simp`/`rw` | `grep -nE "^\s*(change\|show)\b" CombinatorialRigidity/*.lean` | Per `CombinatorialRigidity/CLAUDE.md` *Concrete signals* — is the `change` covering for an un-fused predicate lemma? Could a project-internal simp lemma replace it? |
| Multi-step `rw [..., ..., ...]` chains (3+ args, one mathematical step) | `grep -nE "rw \[[^]]*,[^]]*,[^]]*,[^]]*\]" CombinatorialRigidity/*.lean` | Missing fused lemma — usually a one-line mirror under `CombinatorialRigidity/Mathlib/<path>`. |
| `show X = Y from rfl` as a `rw` / `simp only` argument | `grep -nE "show .* from rfl" CombinatorialRigidity/*.lean` | Falls into one of: (a) a `let`-binding the rewrite chain should be reducing on its own — reorder so the binder lives at the elaboration boundary, or if a `set X := … with hX_def` is in scope, use `hX_def`; (b) a bundled-vs-unbundled morphism gap with a named `_apply` lemma upstream (`RingHom.mapMatrix_apply`, `LinearMap.coe_mk`, `DFunLike.coe_fn_eq`, …); (c) a numeric / arithmetic literal — reach for the named lemma (`Nat.choose_self`, `Nat.add_sub_cancel`, `Nat.succ_sub_one`, …) instead of `rfl`; (d) a notation unfold (e.g. `{a, b, c}` to nested `insert`) — the whole `rw` chain often collapses to a one-line `simp [structural_lemma, side_hypotheses]`. Phase 8-cleanup B4 + the post-cleanup sweep cleared the project surface; re-grep at each round open. |
| Manual `Fintype.card` / coercion chains | manual | Often `Set.ncard_coe_finset` / `Set.ncard_eq_toFinset_card'` bridges that the autoparam pattern (`TACTICS-GOLF.md` § 2) would have absorbed. |

`DESIGN.md` *Engineering conventions* and *Choices to revisit* pin
the project's official answers — a cleanup-round sweep is "are we
actually following these". Drift gets fixed; if the drift looks
deliberate, the convention itself goes in *Choices to revisit*.

**Liveness is a property of the Lean call chain, not of `\uses`/grep
(Phase-26-cleanup calibration).** Before retiring a decl or a whole
blueprint section as "dead" or "orphaned", confirm it against the
**actual Lean call chain to the main theorem** — trace `lean_references`
transitively, or trial-delete + full-rebuild. Two signals that look
decisive but are not: a blueprint node with **zero incoming `\uses`**
(the graph may simply under-wire a real dependency — a missing edge, not
deadness), and a decl with **zero grep callers** (it may be reached via a
`_gen`/wrapper sibling, or the caller may live in a file the grep missed).
Phase-26's d=3 Claim-6.12 section tripped *both* signals yet was
load-bearing — its capstone `case_III_claim612_gen` is used by the general
proof, and the fix was to add the missing `\uses` edge, not to retire the
section. When both signals fire, the honest outcomes split three ways:
truly-dead-and-unpinned (delete, as `case_I_dispatch`), live-under-wired
(add the `\uses` edge), or dead-but-worth-keeping-as-exposition (ground it
as a worked-example node). Diagnose which before acting.

### C. Long-proof audit

Rank the top ~10 proofs by line count and walk each:

```sh
# crude line-count ranking by `theorem`/`lemma` body
awk '/^(private )?(theorem|lemma) /{name=$0; line=NR}
     /^(end|namespace) /{ if (line) {print NR-line, line, name; line=0} }
     /^\s*$/{ if (line && NR-line > 50) {print NR-line, line, name; line=0} }
' CombinatorialRigidity/*.lean | sort -rn | head -20
```

For each long proof, ask:

- **API extraction.** Is there a self-contained sub-lemma that other
  proofs would call separately? Extract → smaller pieces with a
  named API surface, and the main proof reads as composition.
- **Mathlib lemma we missed.** Re-run `lean_loogle` (type pattern)
  or `lean_leanfinder` (concept) against any 5-10+ line subblock.
  TACTICS-GOLF § 3 *Search mathlib before mirroring* lists worked
  examples — multi-line hand-rolled blocks regularly collapse to a
  one-line mathlib invocation.
- **Tactic substitution.** Could `grind only [...]` / `fun_prop` /
  `linear_combination` collapse a multi-step `rw` chain? Use
  `lean_multi_attempt` to A/B-test candidates without an edit-build
  cycle.
- **Definitional refactor.** Would making a predicate `abbrev` (or
  reshaping its body) save proofs that currently have to unfold it
  by hand? *Don't* convert `def`s to `abbrev`s casually — `DESIGN.md`
  pins them as `def` deliberately; this is a per-proof judgement
  call, not a policy reversal.
- **Cross-proof unification.** Two proofs that share an algebraic
  backbone (e.g. the typeII IR vs. row-LI extends in this project)
  are candidates for a shared lemma. Phase 7 *Blockers / open
  questions* records the typeII-cores unification as a worked
  example.

**Calibration: long-proof rankings surface structural shape, not
extraction debt.** The top-10 ranking is a *screening* tool, not a
to-do list. Phase 9-cleanup C2 and Phase 11-cleanup C2 both closed
with all top-10 sites as no-op, plus cross-proof unification
clusters dissolving on inspection: the long bodies are forced by
structural recursion / case-dispatch boilerplate that is shared at
the *boilerplate* level but not at the *step* level — sibling
lemmas look like unification candidates from the LoC ranking, but
each pair has a per-step semantic divergence that resists a
cross-proof combinator. Expect Bucket C to close mostly no-op
unless a phase introduces a genuinely new long-proof shape; treat
the four-question walk as the audit gate that confirms the
no-extract finding rather than as a discovery procedure for
refactor candidates. When C does surface a refactor, it tends to
come from outside the top-10 — a smaller proof whose shape
matches one already known to be unifiable.

**Calibration (Phase 22j, the L6b producer
`case_II_realization_all_k`).** The molecular layer's largest single
proof (~900 lines, formerly carrying a `maxHeartbeats 3200000`
budget) was walked in a dedicated design-pass (`notes/PERFORMANCE.md`
*Molecular `CaseI.lean` perf recon*). Only **one** small
self-contained sub-lemma was cleanly extractable — the duplicated
ℤ/ℕ rank-cast bridge (→ `toNat_le_of_add_pred_eq` /
`sub_toNat_eq_of_add_pred_eq` in `RigidityMatrix.lean`), which
removed the dominant `CoeT` typeclass load and let the whole-decl
budget drop 3.2M → 600000. The rest of the cost is *diffuse* across a
geometric middle whose ~15–20-local dependency surface makes
sub-lemma extraction a net-negative (the "S4b trap",
`notes/Phase22j.md`). This confirms the no-extract default above and
adds the lever the four-question walk doesn't name: **when a long
proof's cost is diffuse and its locals don't factor, the win is a
*file* split** (carry the whole proof to its own file), not sub-lemma
extraction. That file-split candidate (`CaseI.lean` at 10,346 lines)
is ranked in `notes/PERFORMANCE.md` for a follow-up perf round.

### D. Project-organization compression

Compression is **primarily a per-commit constraint** now (`CLAUDE.md`
*Before each commit → Compress in-commit*; `notes/CLAUDE.md`
*Forward-weighted note*) — a note should rarely be finished-heavy by the
time a cleanup round runs. §D is the **safety net**: it catches notes
that slipped past the per-commit gate (and is where a never-promoted
cross-cutting lesson referenced in 2+ files / 2+ phases finally lifts).
Concretely, when a `notes/PhaseN.md`'s *Decisions made* outweighs its
forward sections (or it trips the ~500-line tripwire), or such a lesson
has gone unlifted:

- **Lift** lessons from phase notes to `TACTICS-GOLF.md` (idioms),
  `TACTICS-QUIRKS.md` (rescue), or `DESIGN.md` (cross-cutting
  rationale) per `CLAUDE.md` *Lift on promotion*.
- **Compress** the multi-session plan to a commit-log pointer + a
  brief summary once the phase is closed (the plan stops being
  plan-relevant the moment the phase ships).
- **Sweep** `notes/FRICTION.md` — `[resolved]`-tagged entries are
  archive-ready by construction (the `[resolved]` vs `[idiom]` split
  records indexed-vs-inline at filing time), so migrating them to
  `FRICTION-archive.md` is a mechanical `grep '^### \[resolved\]'`;
  `[idiom]` entries stay put. See FRICTION.md's filing rule.

This category is essentially a structured re-run of `CLAUDE.md`
*When this commit closes a phase* → *Review project organization*,
applied to phases that have been closed for a while.

## Per-round work log

Every cleanup round gets its own work log under `notes/`, named to
sort near the relevant phase:

- `notes/PhaseN-cleanup.md` for a round between Phase N and Phase
  N+1 (alphabetical / glob order keeps it next to `PhaseN.md`).
- `notes/<topic>-cleanup.md` for ad-hoc rounds outside the
  between-phases cadence (e.g. `notes/perf-cleanup.md`).

The log follows the standard `notes/PhaseN.md` template — see
`notes/CLAUDE.md` *Template for `notes/PhaseN.md`*. Sub-organisation
of *Decisions made* is encouraged when many sweeps happen in one
round; the cleanup round's "Lemma checklist" is the task list
across (A)–(D).

**Task list discipline.** Populate the *full* task list in the log
*before starting any cleanup work*. The point of the log is clean
handoff: a session that runs out of time should be resumable from
the log alone, without the agent having had to scope the work
mid-session. New tasks discovered during the round are fine to
append (with a one-line note about what surfaced them), but the
initial sweep checklist should be comprehensive.

`ROADMAP.md`'s Status table gets a row for each cleanup round
between phases, so the existence and scope of the round is visible
without browsing `notes/`.

## What a cleanup round is *not*

- **Not a performance pass.** Build-time tuning has its own log
  (`notes/PERFORMANCE.md`) and protocol (4-run A/B, median
  comparison). A cleanup round can incidentally reduce per-file
  build time, but it doesn't measure it.
- **Not a phase.** The Status table row is for visibility; the
  cleanup round doesn't have a mathematical milestone, and it
  doesn't unlock new content. Phase N+1 doesn't depend on the
  round between Phase N and N+1 — the round is hygiene.

Refactor passes *are* in scope when surfaced by an A–D audit —
§C explicitly lists "API extraction", "Definitional refactor", and
"Cross-proof unification" as long-proof dispositions, and a B-sweep
that surfaces a missing fused lemma is itself a small refactor.
Land each surfaced refactor in-round as its own commit per *Workflow*
rule 3, not as a forward-work carry-over. The exclusion is on
*free-form* refactors started without an audit anchor — those still
belong in a phase plan or `DESIGN.md` *Choices to revisit*.

## Workflow

1. **Open the work log** with the round's planned scope (which of
   A–D, which files, which smells). One commit just for the log
   skeleton + task list is fine.
2. **Sweep first, fix later.** Within each category, run the greps
   / file walks and *record the task list* before starting fixes.
   You'll find more items than you expect; deferring some to a
   follow-up round is normal.
3. **Each fix as its own commit.** The per-commit friction review
   discipline (`CombinatorialRigidity/CLAUDE.md`) still applies. A
   cleanup commit looks the same as any other commit: build/lint
   gates, friction review, work-log update. Refactor candidates
   surfaced by an A–D audit (API extraction, cross-proof
   unification, a fused mirror lemma, …) count as fixes — land
   them in-round each as its own commit, not as a forward-work
   carry-over.
4. **Lift cross-cutting lessons in-commit.** If a sweep reveals
   "always prefer X over Y" — that goes to `TACTICS-GOLF.md` /
   `TACTICS-QUIRKS.md` in the same commit as the fix, per the
   existing lift-on-promotion rule.
5. **Close the round** with a *Hand-off / next phase* section in
   the work log that names what carried over (if anything) and
   updates the ROADMAP Status row.
