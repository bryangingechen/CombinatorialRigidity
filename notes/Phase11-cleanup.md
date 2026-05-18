# Phase 10 + 11 cleanup round — work log

**Status:** in progress (A1 closed as no-op; A2 closed with Phase-9-era
`some`/`none` → `.inr`/`.inl` cleanup in `chapter/pebble-game.tex` +
matching docstring fix in `Algorithm.lean`; A3 closed with two
targeted fixes in `chapter/executable.tex` — `def:runPebbleGameExec`
`\uses{}` completion + `lem:mem-edgeListSorted` retired forward-reference
to non-existent discharge nodes; A4 closed as no-op — Bucket A
complete; B1 closed as no-op — zero `classical` tactic invocations
and zero `Classical.*` term-mode references in actual code across the
Phase 10+11 surface; B2 closed as no-op — all 6 `noncomputable def`
sites on the Phase 10+11 surface are forced by the same `Finset.toList`
/ `Quot.out` enumeration driver Phase 9-cleanup documented, with the
delta vs Phase 9 being a net wash (`reachClosure` retired in Phase 11
Layer 1 in favour of computable `reachClosureComputable`;
`runPebbleGame.aux` added in Phase 11 Layer 4b alongside
`runPebbleGame`); pre-grep smell-count table revised — the previous
entry's 29-site claim conflated docstring/comment mentions of
"`noncomputable`" with actual `noncomputable def` sites; B3 closed as
no-op + smell-table revision — depth-aware comma count surfaces 6
genuine 4+ arg `rw` chains (the pre-grep regex's 9 was inflated by
inner-`⟨_, _⟩`-tuple commas at lines 421/435/448 in `Basic.lean`,
which are 2-arg chains), each verdict per-step structural rewrite
with no missing-fused-lemma candidate; B4 closed as no-op —
`grep -nE 'letI|haveI|Fintype.ofFinite|Set.Finite.fintype'` over the
Phase 10+11 surface returns zero `letI` / `haveI` / `Set.Finite.fintype`
hits and two `Fintype.ofFinite` hits, both in *Style island* docstrings
documenting the deliberate *absence* of the bridge idiom; B5 closed as
no-op — `grep -nE '@\[nolint|set_option linter'` and a wider
case-insensitive `grep -nEi 'nolint|linter'` across the Phase 10+11
surface return zero hits; Bucket B complete; **C1 closed with top-10
ranking + per-site question** — `Algorithm.lean` (Layer 3 reshape)
carries 6 of 10 entries split into two cross-proof unification
clusters (three fold-traversal lemmas on `runPebbleGameWith`; three
case-traversal lemmas on `tryAddEdgeWith`), `Correctness.lean` carries
2 bridge-form lemmas, `DFS.lean` carries the 2 completeness halves; the
docstring-filtered AWK ranking dropped a docstring false-positive that
the §C-template grep would have surfaced; C2/C3, D pending).

This is the inter-phase cleanup round covering **both Phase 10 and
Phase 11**. See `../CLEANUP.md` for the round-level operating manual:
when to run a round, the three audit categories (A blueprint-
divergence, B code-smell, C long-proof, D project-organization), and
the per-round workflow. The task list below is the round's "lemma
checklist" equivalent — populated up front per CLEANUP.md's *Sweep
first, fix later* + *Task list discipline* so a session that runs out
of time can hand off cleanly.

**Combined scope rationale.** No cleanup round ran between Phase 10
and Phase 11 — Phase 11 (witness extraction, a structural-edit phase)
opened immediately after Phase 10 closed and reshaped much of the
Phase 10 surface in place (Layer 3 absorbed the
`tryAddEdgeWith` / `runPebbleGameWith` `Option`-returning shape into
`Sum`; Layer 4b collapsed Phase 10's certificate-form
`runPebbleGameExec_correct` iff into the verdict's return type).
A separate Phase-10-cleanup round would have been an audit of code
that Phase 11 then rewrote; a single combined round is the right
unit, audits everything once at the current shape, and matches the
A/B-equivalent decision made for Phase 8-cleanup / Phase 9-cleanup
(scope to the phase's surface, not project-wide).

The accompanying **perf pass** opens in a parallel work log
(`Phase11-perf.md`) per `../CLEANUP.md` *What a cleanup round is
not*; structural levers (per-decl `@[expose]` audit on the Phase 11
file additions, fresh 4-run A/B baseline) route through that pass.

## Current state

Round open. A1 closed as a no-op (the Layer 1 `chapter/dfs.tex`
additions match `Search/DFS.lean` cleanly; no retired-predecessor
zombie references; the reuse-pattern + proof asides are still
accurate under the Phase 11 reshape). A2 closed with a small targeted
edit (NOT a no-op): the `lem:runPebbleGameWith-underline-subset` and
`lem:runPebbleGame-underline-eq` statements + proofs still mentioned
the Phase-9-era `\mathrm{some}\,D'` / `\mathrm{none}` return shape and
the "four runtime checks" claim (the per-vertex out-degree check is no
longer runtime after Layer 3's `hD` absorption). Updated to the
Layer 3 `\mathrm{.inr}\,D'` / `\mathrm{.inl}\,w` shape with explicit
"three runtime checks" + parenthetical note about the absorbed bound;
matching staleness in `Algorithm.lean`'s top-of-section `tryAddEdgeWith`
docstring ("If both DFS attempts fail, return `none`" → "...return
`.inl w` carrying a workhorse-level failure witness"). A3 closed with
two targeted fixes in `chapter/executable.tex` (NOT a no-op): (1)
`def:runPebbleGameExec`'s `\uses{}` was missing three statement-level
deps that the construction prose forward-references —
`def:pebbleGameResult` (the verdict shape returned), `thm:runPebbleGameWith-correct`
(supplies the underline/reachability proof fields on `.accept`), and
`lem:workhorseWitness-certifies` (supplies the size/lt proof fields on
`.reject` after the bridge-facts discharge for `G.edgeListSorted`); now
listed alongside `def:runPebbleGame, def:outListSorted, def:edgeListSorted`.
(2) `lem:mem-edgeListSorted`'s prose carried a Phase-10-era forward-
reference claim that the three discharge lemmas (`edgeListSorted_no_loops`,
`edgeListSorted_pairwise`, `edgeListSorted_map_sym2_toFinset`) "are packaged
as separate blueprint nodes with `thm:runPebbleGameWith-correct`" — they
are correctly NOT in the blueprint per `blueprint/CLAUDE.md`'s *Skip*
rule for small bridge/glue lemmas, but the prose hadn't been updated to
match; rewritten to describe them as Lean-side glue (named, with the
"not formalised as blueprint nodes" disposition explicit). The walk
also confirmed: all Phase-10/Phase-11 nodes in `executable.tex` resolve
at their current shape (verified by name + signature spot-check + the
bundled `checkdecls` gate via `blueprint/verify.sh`); retired-node
hygiene clean (no live `\lean{...}` for `runPebbleGameExec_correct` /
`runPebbleGameExec_result` — these collapsed into `def:runPebbleGameExec`
per the Layer 4b maximal reshape, and the explanatory prose in
`def:isSparse-decidable` correctly records the Layer 3 / Layer 4 / Layer
4b history); `examples/` directory exists with the four sample files
described at the CLI binary node; `Main.lean`'s entry point shape matches
the *CLI binary* subsection's flow. A4 closed as a **no-op**:
formalisation-aside scan across all three Phase 10/11 chapters
(`chapter/dfs.tex`, `chapter/pebble-game.tex`, `chapter/executable.tex`)
inspected every `\emph{}` / `\begin{remark}` site. Two outcomes:
(i) the bulk of `\emph{}` hits are italicised defined terms or local
emphasis ("computable", "same", "type", "verdict", etc.) — not
formalisation asides at all; (ii) every *substantive* aside (the
*Reuse pattern* note on `def:tryReachPebble`; the *Practical
consequence: zero `noncomputable` in the instance body* paragraph at
`sec:executable-backends`; the *Layer 0 audit #1 (revised outcome)*
note on `def:edgeListSorted`; the polynomial-vs-exponential
`\begin{remark}` on `def:isSparse-decidable`; the *Out of scope* /
*Multigraphs* paragraphs at the head of `sec:pebble-game`; the *Lean
placement note (Phase 11 Layer 4 / Layer 4b maximal reshape)* on
`def:pebbleGameResult`; the two *Special case: planar rigidity*
paragraphs at the chapter foots) is *sticky design rationale* whose
underlying friction is structural — the `Sym2.PartialOrder` slot
conflict, the math-layer/exec-layer noncomputable boundary, the
phase-history record on the verdict placement, or a cross-chapter
pointer — and none has been dissolved by a later Layer. Per
`../CLEANUP.md` §A *"first attempt is to shorten the Lean to retire
the aside"*: no Lean-side shortening is available because the
friction is structural (`SetLike.instPartialOrder` occupies the slot,
the math-layer `runPebbleGame` is `noncomputable` by Finset.toList /
Quot.out and that's the reason the exec wrapper exists, the
verdict's Lean placement is determined by where the type is
declared). Bucket A complete. B1 closed as a **no-op**: two grep
passes over the surface confirmed zero standalone `classical` tactic
invocations and zero `Classical.*` term-mode references at code
level; all nine `Classical` matches are inside docstrings or module
headers documenting why upstream callees are `noncomputable`. The
style island `[Fintype V] [DecidableEq V]` provides every typeclass
the bodies need without `classical`. Bucket B (B2-B5) closed in
subsequent commits as documented in the *Cleanup pass summaries*
below; **C1** (long-proof top-10 ranking) closed with the table in
§C below. Remaining: C2 four-question walk, C3 in-round refactor
candidates, D project-organization compression.
Pre-sweep smell counts (Phase 10+11
surface only —
`CombinatorialRigidity/PebbleGame/*.lean`,
`CombinatorialRigidity/Search/DFS.lean`, `Main.lean`):

| Smell | DFS | Basic | Algorithm | Correctness | Exec | Examples | Main |
|---|---|---|---|---|---|---|---|
| `classical` (standalone) | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `noncomputable def` | 0 | 2 | 2 | 2 | 0 | 0 | 0 |
| `change` / `show` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| `@[nolint …]` / `set_option linter` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| Multi-step `rw [..., ..., ...]` (4+ args, depth-aware) | 3 | 2 | 0 | 0 | 1 | 0 | 0 |
| `show … from rfl` | 0 | 0 | 0 | 0 | 0 | 0 | 0 |

*Revised at B2 close:* the previous `noncomputable def` row's 29-site
total was off — `grep -nE "(^|\s)noncomputable (def|abbrev|instance)"`
returns 6 actual sites (Basic: `outList` L138, `reach` L1055;
Algorithm: `tryReachPebble` L122, `tryAddEdge` L448;
Correctness: `runPebbleGame.aux` L748, `runPebbleGame` L802; Exec: 0).
The original count conflated docstring/comment mentions of
"`noncomputable`" (e.g. `Basic.lean:130` "noncomputable in mathlib
because `Multiset.toList` …") with actual declaration sites.

*Revised at B3 close:* the previous multi-step `rw` row claimed 9
sites (3 DFS + 5 Basic + 1 Exec) under a 3+ comma regex `rw
\[[^]]*,[^]]*,[^]]*,[^]]*\]`. That regex doesn't track inner-bracket
depth, so it captured three `Basic.lean` sites (lines 421, 435, 448)
that are actually 2-arg `rw [if_pos ⟨a, b⟩, if_neg (fun ⟨_, h⟩ => h
rfl)]` chains whose inner anonymous-constructor commas inflated the
top-level comma count. A depth-aware AWK pass over the same surface
returns 6 genuine 4+ arg sites: 3 in DFS (L207/L213/L300), 2 in Basic
(L268/L940), 1 in Exec (L177). The table row above is revised to "4+
args, depth-aware" with the corrected per-file counts. The original
3-arg-and-up grep still has audit value as a Phase 9-cleanup-style
multi-step screen — call it out separately if and when those sites
need a re-audit.

Phase 9-cleanup B4 audited the `noncomputable def` sites in `DFS.lean`
and the pre-Phase-11 `PebbleGame/*.lean`; Phase 11 reshape may have
added or removed sites — re-audit only the delta (Phase 10 additions
in `Exec.lean` / `Examples.lean` and Phase 11 reshape in `Basic.lean`
/ `Algorithm.lean` / `Correctness.lean`). Multi-step `rw` chains
likely break down to per-step structural rewrites with no missing
fused lemma (Phase 9-cleanup B7 saw the same pattern), but the
audit is the discharge.

## Architectural choices made up front

These extend `../DESIGN.md` *Choices to revisit*; if any turns out
wrong, revisit there.

- **Combined Phase 10+11 round, scoped to Phase 10+11 surface.**
  See *Combined scope rationale* above. Same A-D restrict-to-surface
  pattern as Phase 8-cleanup / Phase 9-cleanup; project-wide drift
  was discharged by Phase 7-cleanup and reconfirmed by Phase 8 /
  Phase 9 cleanup rounds.
- **Perf split-out.** Per `../CLEANUP.md` *What a cleanup round is
  not*, performance-tuning work (per-decl `@[expose]` audit, 4-run
  A/B baseline) routes through `Phase11-perf.md`, not this round.
  Refactors *surfaced by an A-D audit* (API extraction, fused-lemma
  mirror, cross-proof unification) are in-round per `../CLEANUP.md`
  *Workflow* rule 3 and *What a cleanup round is not*'s refactor
  carve-out.
- **Each fix as its own commit.** The per-commit friction review and
  build/lint gates apply normally (`../CombinatorialRigidity/CLAUDE.md`
  *Friction review*); cleanup commits look the same as forward-work
  commits.
- **No new phase queued at round close** by default. Phase 11's
  *Hand-off / next phase* listed three candidates (component pebble
  game; Henneberg-sequence extraction; benchmarks harness); the
  user picks at round close if any is ready to open.

## Task checklist

### Bucket A — Blueprint ↔ Lean divergence audit (Phase 10+11 surface)

Three chapters touched by Phase 10/11: `chapter/dfs.tex` (Phase 11
Layer 1 additions), `chapter/pebble-game.tex` (Phase 11 Layer 2-4b
reshape), `chapter/executable.tex` (Phase 10 + Phase 11 Layer 4b/5
reshape). `checkdecls` is on the per-commit gate path so we don't
need a separate "run checkdecls" task here.

- [x] **A1:** `chapter/dfs.tex` ↔ `Search/DFS.lean` walk. Closed as
  a **no-op**. Layer 1 additions verified: `def:reachClosureComputable`
  (line 134) pins `CombinatorialRigidity.Search.reachClosureComputable`
  and its prose "tests each candidate $w : V$ via
  $\mathrm{reachableFinding}\,\mathrm{succ}\,(\cdot = w)\,v$"
  matches the Lean body `Finset.univ.filter fun w =>
  (reachableFinding succ (fun x => decide (x = w)) v).isSome`. The
  companion `lem:mem-reachClosureComputable` (line 151) groups
  three pins (`mem_reachClosureComputable`,
  `reachClosureComputable_sound`,
  `reachClosureComputable_complete`); all three resolve, and the
  iff statement matches. `\uses{}` edges (`def:reachable-finding`
  on the def, `def:reachClosureComputable + thm:reachable-finding-correct`
  on the lemma) are correct. No zombie references to the retired
  `def:reachClosure` / `lem:mem-reachClosure` predecessors anywhere
  in the blueprint or Lean (re-verified Phase 9-cleanup A1 finding
  about "planned `reachClosure` helper" mentions). The two `\emph`
  asides in `chapter/dfs.tex` (reuse-pattern at line 109, the
  inner-induction visited-set claim in the completeness proof at
  line 96) are still accurate under the Phase 11 verdict-bearing
  reshape — neither documents a Phase-9-era `Option` return type.
- [x] **A2:** `chapter/pebble-game.tex` ↔ `PebbleGame/{Basic,
  Algorithm, Correctness}.lean` walk. Closed with a targeted fix
  (not a no-op): all `\lean{...}` pins resolve and align with the
  Lean shape (verified by name + signature spot-check, plus the
  bundled `checkdecls` gate); retired-node hygiene clean (no live
  `\lean{...}` for `tryAddEdgeWith_isSome` /
  `tryAddEdge_iff_independent` / `pebble-game-failure-witness` /
  `tryAddEdgeWith_eq_none_imp_exists_witness` /
  `runPebbleGameWith_eq_none_imp_exists_witness` /
  `runPebbleGame_correct` /
  `runPebbleGame_sound` — only LaTeX-comment retirement notes,
  which are accurate as historical record). Phase~11 Layer~2-4b
  insertions (`def:workhorseWitness`,
  `lem:workhorseWitness-certifies`, `def:pebbleGameResult`,
  `thm:pebbleGameResult-isAccept-iff`) all present with correct
  shapes; `def:tryAddEdge`, `def:runPebbleGame`,
  `thm:pebble-game-correct`, `cor:pebble-game-countMatroid-indep`
  restated against the `Sum`-return / `hD` signature / verdict
  form. The fix: `lem:runPebbleGameWith-underline-subset` and
  `lem:runPebbleGame-underline-eq` (statements + proofs) still
  carried Phase-9-era `= \mathrm{some}\,D'` / `\mathrm{some} \ne
  \mathrm{none}` prose plus the proof of the second one referenced
  "the four runtime checks" (the per-vertex out-degree check is no
  longer runtime after Layer~3 absorbed `(∀ x, D.out x ≤ k)` into
  `hD : Reachable k ℓ D`) — updated to `= \mathrm{.inr}\,D'` /
  `\mathrm{.inr} \ne \mathrm{.inl}` shape, "three runtime checks"
  with a parenthetical note about the absorbed bound, and the
  particular form `\mathtt{hD}` argument added to the workhorse
  signature presentation. Matching Lean-side docstring fix:
  `Algorithm.lean`'s top-of-section `tryAddEdgeWith` docstring
  still claimed "If both DFS attempts fail, return `none`" while
  the very next paragraph correctly described `.inl ⟨…⟩`; updated
  to the `.inl w` shape for self-consistency.
- [x] **A3:** `chapter/executable.tex` ↔ `PebbleGame/Exec.lean` +
  `Main.lean` walk. Closed with two targeted fixes (NOT a no-op): the
  `\uses{}` of `def:runPebbleGameExec` was missing three statement-
  level dependencies forward-referenced by its construction prose
  (`def:pebbleGameResult`, `thm:runPebbleGameWith-correct`,
  `lem:workhorseWitness-certifies`); now listed alongside the
  original `def:runPebbleGame, def:outListSorted, def:edgeListSorted`.
  `lem:mem-edgeListSorted`'s prose forward-referenced three discharge
  lemmas as "packaged as separate blueprint nodes with
  `thm:runPebbleGameWith-correct`" — the discharges are correctly
  *Skip*ped per `blueprint/CLAUDE.md` (small bridge/glue lemmas), so
  the prose was rewritten to describe them as Lean-side glue with the
  explicit *not formalised as blueprint nodes* disposition. All other
  Phase-10/Phase-11 nodes (`def:outListSorted`, `lem:mem-outListSorted`,
  `def:edgeListSorted`, `def:runPebbleGameExec`, `thm:runPebbleGameWith-correct`,
  `def:isSparse-decidable`, `def:isTight-decidable`,
  `def:isLaman-decidable`, *Worked examples* / *CLI binary*
  subsections) verified against the current Lean shape (verdict-direct
  routing in `runPebbleGameExec`'s aux helper at `Exec.lean:271-303`;
  Phase 11 Layer 4b reduction-body history in
  `def:isSparse-decidable`'s explanatory prose is accurate;
  `Main.lean`'s `classify` flow matches the CLI binary's enumerated
  steps). Retired-node hygiene clean — `thm:runPebbleGameExec-correct`
  and `def:runPebbleGameExec-result` collapsed into
  `def:runPebbleGameExec` per Layer 4b maximal reshape, with no
  surviving `\lean{...}` pin or `\label{...}` for either retired
  node. `examples/` directory exists with the four sample files
  (`k4-minus-e.txt`, `k4.txt`, `moser-spindle.txt`, `path5.txt`)
  carrying the Phase 11 Layer 5 expected-output schema as a header
  comment block, matching the CLI binary node's description.
- [x] **A4:** Formalization-aside scan across all three chapters.
  Closed as a **no-op**. Walked every `\emph{}` and
  `\begin{remark}` site in `chapter/dfs.tex`, `chapter/pebble-game.tex`,
  `chapter/executable.tex`. Two outcomes: the majority of `\emph{}`
  hits are italicised defined terms or local emphasis (not asides);
  every substantive aside is sticky design rationale or a
  cross-chapter pointer with no Lean-side shortening available
  (structural friction: `Sym2.PartialOrder` slot conflict; the
  math-layer/exec-layer noncomputable boundary; the Layer 4/4b
  history record on the verdict's Lean placement; etc.). No orphan
  asides documenting the Phase-9-era `Option` return type remain
  anywhere on the surface — all `Option`-shape claims were updated
  to `Sum` / verdict shape during Phase 11's per-Layer blueprint
  restate-in-place and the A1-A3 walks. See *Cleanup pass summaries*
  below for the per-aside disposition table.

### Bucket B — Code-smell sweep (Phase 10+11 surface)

Pre-grep summary in *Current state* above. Phase 9-cleanup audited
`DFS.lean` and the pre-Phase-11 `PebbleGame/*.lean`; this sweep
re-audits the delta only (Phase 10 additions + Phase 11 reshape).

- [x] **B1:** `classical` audit. Closed as a **no-op**. Two grep
  passes over the Phase 10+11 surface
  (`CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,
  Exec,Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`,
  `Main.lean`): standalone tactic `classical` — zero hits;
  case-sensitive `Classical` — nine hits, all inside docstrings or
  module-header explanatory prose (e.g. `Exec.lean:21` documents why
  `Finset.toList` lifts through a `Classical`-flavored `Quotient.lift`,
  `Exec.lean:56` documents the style-island promise of "no `Classical`
  machinery in the body", `DFS.lean:765` contrasts `reachClosureComputable`
  with a `Classical.decPred`-filtered formulation). No code-level
  `classical` or `Classical.*` reference exists; the style island
  `[Fintype V] [DecidableEq V]` provides every typeclass the bodies
  use. No comment-out test is needed because there is nothing to
  comment out. Confirms the pre-grep summary in *Current state*
  above.
- [x] **B2:** `noncomputable def` audit (delta vs Phase 9-cleanup
  B4). Closed as a **no-op**. Re-grep
  (`grep -nE "(^|\s)noncomputable (def|abbrev|instance)"`) over
  the Phase 10+11 surface returns **6 sites total** (not the 29
  the pre-grep table claimed — see *Cleanup pass summaries* B2
  for the conflation diagnosis):
  - `Basic.lean:138` `outList` — root driver. `(D.outNbhd v).toList`
    threads `Finset V → Multiset V → List V` via `Finset.toList`,
    whose Quotient lift uses `Classical`-flavored `Quotient.lift`
    machinery; docstring documents.
  - `Basic.lean:1055` `reach` — inherits via
    `reachClosureComputable D.outList v`; the wrapper is computable
    but `D.outList` is the noncomputable input; docstring documents.
  - `Algorithm.lean:122` `tryReachPebble` — inherits via
    `tryReachPebbleWith … D.outList …`; one-liner math-layer
    specialisation of the computable `tryReachPebbleWith`
    workhorse; docstring documents.
  - `Algorithm.lean:448` `tryAddEdge` — inherits via
    `tryAddEdgeWith … (fun D' => D'.outList) …`; one-liner
    math-layer specialisation of the computable `tryAddEdgeWith`
    workhorse; docstring documents.
  - `Correctness.lean:748` `runPebbleGame.aux` — inherits via
    `D'.outList` + `G.edgeFinset.toList.map Quot.out`; both
    `Finset.toList` and `Quot.out` carry the noncomputable burden;
    docstring documents.
  - `Correctness.lean:802` `runPebbleGame` — inherits via
    one-line call to `runPebbleGame.aux`; docstring documents.

  Delta vs Phase 9-cleanup B4 (6 sites: `outList`,
  `tryReachPebble`, `tryAddEdge`, `runPebbleGame`, `reach`, plus
  `DFS.reachClosure`):
  - **Removed (−1):** `DFS.reachClosure` retired in Phase 11
    Layer 1 in favour of the **computable**
    `reachClosureComputable` (no `noncomputable` keyword;
    `DFS.lean` now has 0 sites).
  - **Added (+1):** `runPebbleGame.aux` in `Correctness.lean`,
    introduced in Phase 11 Layer 4b to dodge the
    `match h : <expr> with` substitution quirk (TACTICS-QUIRKS
    § 17) by taking the `Sum`-shaped workhorse output as an
    explicit argument.
  - **Reshape neutral:** the two `Algorithm.lean` sites and the
    two `Basic.lean` sites are present in both rounds (Phase 11
    Layer 3 reshape changed `tryAddEdge`'s return type from
    `Option` to `Sum` but did not change its `noncomputable`
    posture).
  Net total: 6 sites, all forced by the same `Finset.toList` /
  `Quot.out` enumeration driver (the math-layer / exec-layer
  split documented in `../DESIGN.md` *Pebble-game style island*).
  No vestigial sites; no in-round refactor surfaced. Sanity build
  via `lake build CombinatorialRigidity.PebbleGame.Correctness`
  succeeded as expected. Pre-grep smell counts table revised in
  *Current state*.
- [x] **B3:** Multi-step `rw [..., ..., ..., ...]` chain audit.
  Closed as a **no-op** + smell-table revision. The pre-grep claimed
  9 sites under a comma-only regex; a depth-aware AWK re-count
  surfaces 6 genuine 4+ arg sites (the other 3 were 2-arg chains
  with inner `⟨_, _⟩` tuple commas — see *Cleanup pass summaries* B3
  for the diagnosis). Each of the 6 sites is a per-step structural
  rewrite with no missing-fused-lemma candidate: DFS L207/L213 unfold
  the WF-recursive helper definitionally (`mapRel`, `length`,
  `length`, `ih`); DFS L300 chains three structural unfolds with the
  IH backward (`arcsFinset_cons`, `Finset.image_insert`, `← ih`,
  `reversedArcsFinset_cons`); Basic L268 substitutes summand →
  folds → smul/mul → factor-order swap (`Finset.sum_congr rfl h`,
  `Finset.sum_const`, `smul_eq_mul`, `mul_comm`); Basic L940 unfolds
  `pebOn`/`outOn` at `empty` + drops `+ 0` + aligns multiplication
  order; Exec L177 chains both Sym2 mk-equations with the
  inf/sup-of-le reductions. `lean_multi_attempt`-tested
  `simp [name list]` collapses on every site — they all close, but
  with no measurable simplification benefit (and `simp [mul_comm]`
  is a non-terminator risk). No project-mirror surfaced.
- [x] **B4:** `letI`/`haveI Fintype.ofFinite` audit. Closed as a
  **no-op**. Four greps over the Phase 10+11 surface
  (`CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,Exec,
  Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`, `Main.lean`):
  `grep -nE 'haveI'` — zero hits; `grep -nE 'letI'` — zero hits;
  `grep -nE 'Fintype\.ofFinite'` — **two** hits, both in *Style
  island* docstrings (`Basic.lean:49`, `DFS.lean:73`) that document
  the deliberate *absence* of the bridge — they are pointers to the
  project-default `[Finite V]` + inline-bridge idiom that the
  algorithm files explicitly *do not* use; `grep -nE 'Set\.Finite\.fintype'`
  — zero hits. The style island convention `[Fintype V] [DecidableEq V]`
  end-to-end (`../DESIGN.md` *Pebble-game style island*) is uniformly
  respected; no inline `Fintype.ofFinite` / `Set.Finite.fintype`
  bridge appears in any algorithm body. No comment-out test was
  needed (nothing to comment out). Confirms the cross-cutting
  expectation that algorithm-bearing files take their finiteness
  data via the typeclass slot, not via inline derivation.
- [x] **B5:** `@[nolint …]` / `set_option linter …` audit. Closed as
  a **no-op**. Two greps over the Phase 10+11 surface
  (`CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,Exec,
  Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`, `Main.lean`):
  (i) `grep -nE '@\[nolint|set_option linter'` — zero hits;
  (ii) wider case-insensitive `grep -nEi 'nolint|linter'` — zero hits
  (no docstring or comment mentions either). The Phase 10+11 surface
  carries no lint suppressions of any form, confirming the pre-grep
  summary in *Current state* and the round-open expected closure.
  Bucket B (code-smell sweep) complete: B1 no-op / B2 no-op +
  smell-table revision / B3 no-op + smell-table revision / B4 no-op /
  B5 no-op. No code-smell entries were converted into in-round
  refactors — every Bucket B audit found the existing shape is forced
  by structural drivers documented in `../DESIGN.md` (the style
  island, the `Finset.toList` / `Quot.out` enumeration drivers) or by
  the absence of a missing fused-lemma candidate.

### Bucket C — Long-proof audit (Phase 10+11 surface)

- [x] **C1:** Top-10 by body LoC across `PebbleGame/*.lean`,
  `Search/DFS.lean`, `Main.lean`. Ranking discharged via a
  docstring-filtered AWK pass over the seven surface files
  (`Algorithm`, `Basic`, `Correctness`, `Examples`, `Exec` under
  `PebbleGame/`, plus `Search/DFS.lean` and `Main.lean`). The top
  ten by body LoC, with one-line per-site question for C2's
  four-question walk:

  | # | Site | LoC | Per-site question |
  |---|---|---|---|
  | 1 | `tryAddEdgeWith` (Algorithm.lean L276) | 172 | **API extraction.** Phase 11 Layer 3 inlined the case-5 failure-witness construction (the `WorkhorseWitness` `.inl` arm) — is the case-5 body a self-contained sub-lemma other proofs would call? Or is it tied so tightly to the recursion's local state (`hD`, `path₁`, `hpath₁_no_pebble`, etc.) that lifting it would just reshuffle locals? |
  | 2 | `tryAddEdgeWith_reachable` (Algorithm.lean L470) | 86 | **Cross-proof unification.** This is the case-by-case Reachable-propagation lemma; cases 3 and 4 walk the `arc_insert` / `reverse_path` invariants in parallel. Could a shared "Reachable preserves under arc-insert ∘ path-reverse" lemma collapse the case-3/case-4 duplication? |
  | 3 | `span_succ_le_edgesIn_ncard_of_subset` (Correctness.lean L242) | 63 | **Mathlib lemma we missed.** This is the algebraic-core ncard inequality bridging `D.span (V'.insert u ∪ {v})` to `(G.edgesIn _).ncard + 1`. Re-run `lean_loogle` / `lean_leanfinder` against the 5-10 line subblocks — is there a `Set.ncard_insert_of_notMem` / `Finset.card_union_add_card_inter` form that collapses the manual add-cancel chain? |
  | 4 | `runPebbleGameWith_witness_bridges` (Correctness.lean L391) | 62 | **API extraction.** This lemma routes the `WorkhorseWitness.certifies_against` payload through the bridge to `IsSparse k ℓ`'s contrapositive. The 62 LoC are essentially three sequential reconciliations (size, vertex inclusion, span bound) — is there a packaging into a single "witness certifies sparsity-failure on `G`" applied lemma that the success branch could share? |
  | 5 | `runPebbleGameWith_mem_underline` (Algorithm.lean L903) | 61 | **Definitional refactor.** Per-edge underline-membership propagation along the fold; structure mirrors `runPebbleGameWith_underline_subset` (#8) and `runPebbleGameWith_reachable` (below top-10) — three sibling fold-traversal lemmas, each with the same case dispatch shape. Could a single "fold over Sum preserves these three invariants together" lemma replace all three? Cross-proof unification candidate spanning #5/#8/runPebbleGameWith_reachable. |
  | 6 | `tryAddEdgeWith_underline` (Algorithm.lean L556) | 61 | **Cross-proof unification.** Sibling to #2 (`_reachable`) — same case-by-case structure tracking underline membership through `arc_insert` / `reverse_path`. Bundle with #2 if a shared "tryAddEdgeWith preserves these invariants" lemma can carry both. |
  | 7 | `reachableFindingAux_complete` (DFS.lean L677) | 60 | **Definitional refactor.** The inner-induction over `n : ℕ` walks a `DirectedWalk` via `dropUntilBundle` truncation. Is the `visited` accumulator's lift-out at each `if h : v ∈ visited` step the right boundary, or could the proof factor through a `DirectedWalk.dropUntil` API lemma we don't have? |
  | 8 | `runPebbleGameWith_underline_subset` (Algorithm.lean L844) | 59 | **Cross-proof unification.** See #5; sibling fold-traversal lemma. Bundle candidate. |
  | 9 | `tryAddEdgeWith_witness_uv` (Algorithm.lean L617) | 57 | **API extraction.** Companion-projection lemma on the `WorkhorseWitness` returned by `tryAddEdgeWith` (extracts the `u ∈ V'.cell` / `v ∈ V'.cell` fields). The 57 LoC walk every recursion case to project that vertex inclusion — is there a "projection through the recursion" combinator? Or is it forced by the case-5 inline construction (#1)? |
  | 10 | `reachableFinding_complete` (DFS.lean L737) | 56 | **Tactic substitution.** Lifts a `Relation.ReflTransGen` witness to a `DirectedWalk` via `head_induction_on`, then forward-proves the conclusion. Could `lean_multi_attempt` shrink the per-step bookkeeping? Or is this the right shape for a verified-iterative DFS completeness proof? |

  Just outside the top-10 (still substantive — flagged for C2
  bundle consideration if a sibling pattern lands above): #11
  `pebOn_add_span_add_outOn` (Basic.lean L261, 41 LoC); #12
  `runPebbleGameWith_reachable` (Algorithm.lean L804, 40 LoC,
  sibling to #5/#8); #13 `tryAddEdgeWith_isSparse` (Correctness.lean
  L351, 40 LoC).

  Files at a glance: `Algorithm.lean` (Layer 3 reshape) carries 6
  of the top-10 (#1, #2, #5, #6, #8, #9 — three case-traversal
  lemmas + three fold-traversal lemmas, all rooted at
  `tryAddEdgeWith` / `runPebbleGameWith`); `Correctness.lean`
  carries 2 (#3, #4 — both bridge-form lemmas threading workhorse
  output to `IsSparse`); `DFS.lean` carries 2 (#7, #10 — the
  completeness halves of `reachableFindingAux` / `reachableFinding`).
  `Basic.lean` and the smaller files (`Examples`, `Exec`, `Main`)
  hold no top-10 entries — `Basic.lean`'s longest body
  (`pebOn_add_span_add_outOn` at 41 LoC) sits just outside; `Exec`
  / `Main` max at the verdict-pattern-match `classify` (25 LoC)
  and parsing helpers.

  Two cross-proof unification clusters surface as primary C2
  candidates: **(i) Algorithm.lean's three fold-traversal lemmas**
  (#5 `_mem_underline`, #8 `_underline_subset`, plus the
  #12-runner-up `runPebbleGameWith_reachable`) share a fold-over-`Sum`
  case dispatch and might collapse to one combinator; **(ii)
  Algorithm.lean's three case-traversal lemmas** (#2 `_reachable`,
  #6 `_underline`, plus the case-5-companion #9 `_witness_uv`) share
  the seven-case recursion on `tryAddEdgeWith` and might collapse
  to one preserved-invariant lemma. C2 dispatches each top-10
  candidate via the four-question walk and decides per cluster
  whether an in-round refactor (C3) is structurally small enough.
- [ ] **C2:** Four-question walk over the C1 top sites (per
  `../CLEANUP.md` §C — API extraction, mathlib lemma we missed,
  tactic substitution, definitional refactor, cross-proof
  unification). Record candidates for in-round refactor; defer to
  follow-up phases only when the refactor is structurally large.
- [ ] **C3:** In-round refactor candidates land each as its own
  commit, per `../CLEANUP.md` *Workflow* rule 3.

### Bucket D — Project-organization compression

- [ ] **D1:** `notes/Phase11.md` compression. Currently 856 LoC vs
  the adaptive 350-450 budget for a substantive phase
  (`../notes/CLAUDE.md` *Soft length budget*). Phase 11 was a
  five-layer structural-edit phase with 6 forward-work commits + 2
  opener docs commits — substantive but not at the "20+ commits"
  scale that justifies the upper end. Compression candidates:
  - *Current state* runs ~150 LoC of per-layer narrative that
    re-tells what each layer commit's message + the *Layer plan*
    section already say. Collapse to a per-layer-pointer summary.
  - *Architectural choices made up front* is ~80 LoC of design
    rationale; some entries (e.g., the verdict-shape inductive
    declaration in TeX-style) duplicate `chapter/pebble-game.tex`
    *User-facing verdict* prose and can collapse to a pointer.
  - *Decisions made during this phase* is well-organized but a
    few entries (e.g., *Layer 4b: collapsed to maximal reshape*)
    duplicate the *Current state* narrative.
  Target: ~400 LoC.
- [ ] **D2:** `notes/Phase10.md` compression. Currently 546 LoC.
  Phase 10 was a shorter five-layer forward-work phase; adaptive
  budget allows ~250-350. *Current state* and *Architectural
  choices* duplicate each other in spots (e.g., the
  `[LinearOrder V]` and `Fact (ℓ < 2 * k)` decisions appear in
  both); collapse the *Current state* narrative to a per-layer
  pointer. Target: ~300 LoC.
- [ ] **D3:** FRICTION re-skim. Phase 10's *Promoted* section
  lifted three entries (TACTICS-QUIRKS § 22, § 23, DESIGN.md
  *One Decidable instance per project predicate*); Phase 11's
  *Promoted* lifted one (TACTICS-QUIRKS § 17 third bullet, the
  `match h:` quirk fix via `*.aux` helper). Verify each was a
  one-line pointer in the phase notes after lifting, and that the
  FRICTION/QUIRKS entries themselves carry the cross-references
  back. The two open Phase-11 promotion candidates flagged in
  Phase11.md *Promoted* parenthesis (*Strengthen past results to
  reduce duplication* and *Blueprint reshape in-place per Layer*)
  may be ripe for promotion now — assess on second-site evidence
  (whether the principle would also have applied to Phase 7 / 8 /
  9 / 10 in retrospect).
- [ ] **D4:** DESIGN.md *Choices to revisit* drift check. The
  active entries (`apnelson1/Matroid dependency` watch, `Promoting
  edgesIn upstream`, *Pebble-game style island* if any drift)
  should reflect Phase 10/11's reality. Phase 11's
  *Architectural choices* shouldn't have left any
  *Choices to revisit* candidate unresolved; verify.
- [ ] **D5:** No-residual-lifts audit. For each Phase 10 / 11
  *Promoted to* entry, verify the destination still carries the
  cross-reference back; verify the phase entry is a one-line
  pointer per CLAUDE.md *Lift on promotion*.

## Decisions made during this phase

### Phase-local choices and proof techniques

*(Empty — populate as fixes land.)*

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

*(Empty — populate as cross-cutting lessons surface.)*

### Cleanup pass summaries

- **A1: `chapter/dfs.tex` ↔ `Search/DFS.lean` walk** — no-op closure.
  Layer 1's *Reachability closure (computable)* subsection
  (`def:reachClosureComputable` + `lem:mem-reachClosureComputable`,
  the latter grouping the iff with its sound / complete halves under
  one `\lean{...}`) matches the Lean signatures and proof-pattern
  prose verbatim; no retired-predecessor `\lean{...}` pin survives
  anywhere in `blueprint/` or `CombinatorialRigidity/`. The
  `chapter/dfs.tex` asides (reuse-pattern and the inner-induction
  visited-set claim) are still accurate under Phase 11's verdict
  reshape. Pre-checklist task A1 marked closed; no edits to either
  side.
- **A2: `chapter/pebble-game.tex` ↔ `PebbleGame/{Basic, Algorithm,
  Correctness}.lean` walk** — targeted-fix closure. All `\lean{...}`
  pins resolve (verified by name + signature spot-check + the bundled
  `checkdecls` gate); retired-node hygiene clean (Phase~11 Layer~3-4b
  retirees appear only as LaTeX-comment retirement notes — accurate
  historical record, no live `\lean{...}` pin). Inserted nodes
  `def:workhorseWitness`, `lem:workhorseWitness-certifies`,
  `def:pebbleGameResult`, `thm:pebbleGameResult-isAccept-iff` all
  present at correct shape; existing `def:tryAddEdge` /
  `def:runPebbleGame` / `thm:pebble-game-correct` /
  `cor:pebble-game-countMatroid-indep` restated against the
  `Sum`-return / `hD` signature / verdict form. Fix scope: two
  *proof*-level Phase-9-era residuals
  (`lem:runPebbleGameWith-underline-subset` and
  `lem:runPebbleGame-underline-eq`) carrying `= \mathrm{some}\,D'` /
  `\mathrm{some} \ne \mathrm{none}` shape claims plus the "four
  runtime checks" phrasing (now three after Layer~3 absorbed
  `(∀ x, D.out x ≤ k)` into `hD : Reachable k ℓ D`); rewritten to the
  Layer~3 `.inr`/`.inl` shape with the workhorse `hD` argument shown
  in the call form, plus a one-clause parenthetical on the absorbed
  bound where Invariant~(1) was previously cited as a runtime check.
  Matching Lean-side fix: `Algorithm.lean`'s top-of-section
  `tryAddEdgeWith` docstring (line 229 area) still said "If both DFS
  attempts fail, return `none`" while the very next paragraph
  correctly described `.inl ⟨…⟩`; updated to the `.inl w` shape with
  a forward pointer to the next paragraph's witness-construction
  description.
- **A3: `chapter/executable.tex` ↔ `PebbleGame/Exec.lean` +
  `Main.lean` walk** — targeted-fix closure (NOT a no-op). Two
  divergences fixed in `chapter/executable.tex`:
  (1) `def:runPebbleGameExec`'s `\uses{}` was missing three deps that
  its construction prose forward-references — `def:pebbleGameResult`
  (the verdict shape returned), `thm:runPebbleGameWith-correct`
  (supplies the underline/reachability proof fields on `.accept`),
  and `lem:workhorseWitness-certifies` (supplies the size/lt proof
  fields on `.reject` after the bridge-facts discharge for
  `G.edgeListSorted`); now listed alongside the original
  `def:runPebbleGame, def:outListSorted, def:edgeListSorted`. The
  dep-graph edges these missing entries should have drawn were
  silently absent from the rendered graph.
  (2) `lem:mem-edgeListSorted`'s prose forward-referenced three
  discharge lemmas (`edgeListSorted_no_loops`, `edgeListSorted_pairwise`,
  `edgeListSorted_map_sym2_toFinset`) as "packaged as separate
  blueprint nodes with `thm:runPebbleGameWith-correct`". The
  discharges are correctly *Skip*ped per `blueprint/CLAUDE.md` —
  they are small bridge/glue lemmas whose facts are legible from the
  type signature; the forward-reference was a Phase-10-era plan
  residual that didn't track the final selection decision. Rewritten
  to describe them as Lean-side glue with the *not formalised as
  blueprint nodes* disposition explicit, so the next reader doesn't
  go looking for nodes that aren't there. All other Phase-10/11
  nodes in the chapter checked out at their current Lean shape;
  retired-node hygiene clean (the Layer 4b maximal-reshape retirees
  `runPebbleGameExec_correct` / `runPebbleGameExec_result` carry no
  surviving `\lean{...}` or `\label{...}` and the explanatory prose
  in `def:isSparse-decidable` correctly records their history);
  `examples/` directory and `Main.lean` flow verified against the
  *Worked examples* and *CLI binary* subsections.
- **A4: Formalisation-aside scan across all three chapters** —
  no-op closure. Walked every `\emph{}` and `\begin{remark}` site
  in `chapter/dfs.tex`, `chapter/pebble-game.tex`, and
  `chapter/executable.tex` (full enumeration via
  `grep -nE '\\emph\{|\\begin\{remark\}'`). Per-aside disposition:
  | Aside | Site | Disposition |
  |---|---|---|
  | *Reuse pattern* (DFS specialisation to `tryReachPebble`) | `dfs.tex` L109 | Keep — still accurate; verified in A1 |
  | *Practical consequence: zero `noncomputable` in instance body* | `executable.tex` L81 | Keep — still true under Phase 11 (Layer 1 `reachClosureComputable` keeps the body `Classical`-free); operational reason `runPebbleGameExec` exists |
  | *Layer 0 audit #1 (revised outcome)* (`Sym2.PartialOrder` slot conflict) | `executable.tex` L160 | Keep — sticky design rationale; verified in A3 |
  | `\begin{remark}[Polynomial vs.\ exponential reduction]` | `executable.tex` L335 | Keep — still accurate; the "exactly one Decidable instance per predicate" rule is enforced in source |
  | *Special case: planar rigidity (continued)* | `executable.tex` L478 | Keep — cross-chapter pointer; references resolve |
  | *Out of scope* (component pebble game / Henneberg-sequence) | `pebble-game.tex` L28 | Keep — scope statement, still accurate; both items remain candidates for follow-up phases |
  | *Multigraphs* (matroidal-regime simplification audit) | `pebble-game.tex` L39 | Keep — already updated to reference Layer 3 `Sum`-return shape and `lem:pebble-game-tryAddEdgeWith-isSparse` / `lem:workhorseWitness-certifies` |
  | `tryReachPebble` math-layer noncomputable + *Style island* pointer | `pebble-game.tex` L341 | Keep — `tryReachPebble` is still `noncomputable` per the revised cleanup-round smell table (Algorithm.lean `noncomputable def` count = 2: `tryReachPebble` + `tryAddEdge`); the file-header *Style island* reference resolves to `PebbleGame/Basic.lean:43` (still present) |
  | `tryAddEdgeWith` reshape detail incorporating Layer 3 `hD` absorption | `pebble-game.tex` L388 | Keep — already verified accurate in A2 (the L398-401 paragraph documents the absorption explicitly) |
  | *Lean placement note (Phase 11 Layer 4 / Layer 4b maximal reshape)* | `pebble-game.tex` L1039 | Keep — phase-history record; sticky |
  | *Special case: planar rigidity* | `pebble-game.tex` L1121 | Keep — cross-chapter pointer; references resolve |
  All other `\emph{}` matches are italicised defined terms or local
  emphasis — *not* formalisation asides. Per `../CLEANUP.md` §A's
  "first attempt is to shorten the Lean to retire the aside": no
  Lean-side shortening applies because every kept aside records
  *structural* friction (`SetLike.instPartialOrder` occupying the
  `Sym2.PartialOrder` slot; the math-layer/exec-layer
  `noncomputable` boundary forced by `Finset.toList` /
  `Quot.out`; the verdict's Lean placement determined by where the
  type is declared) or is a cross-chapter pointer that has no
  Lean residual. Bucket A complete; the round's blueprint-divergence
  audit is fully discharged. Three formalisation-aside *Note*-style
  paragraphs inside the three `def:is{Sparse,Tight,Laman}-decidable`
  bodies ("packaged in the formalisation as `Fact (ℓ < 2 * k)`",
  "the formalisation bridges Set.ncard / Nat.card …", "the
  formalisation registers Fact (3 < 2 * 2) as a top-level instance")
  were also verified — each remains accurate against the current Lean
  shape per the in-source Fact-instance registration at
  `PebbleGame/Exec.lean:415` and the explanatory prose at line 412.
- **B1: `classical` audit (Phase 10+11 surface)** — no-op closure.
  Two grep passes over
  `CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,Exec,
  Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`, and
  `Main.lean`:
  (i) `grep -nE '\bclassical\b'` (standalone tactic) — zero hits.
  (ii) `grep -n 'Classical'` (case-sensitive, includes term-mode) —
  nine hits, all inside docstrings or module-header explanatory prose
  documenting why upstream callees are `noncomputable` (e.g.
  `Exec.lean:21` documents `Finset.toList`'s `Classical`-flavored
  `Quotient.lift`, `Exec.lean:23` documents `Quot.out`'s
  `Classical.choice` use, `Basic.lean:131` and `DFS.lean:27` repeat
  the same `Classical`-flavored `Quotient.lift` explanation,
  `DFS.lean:765` contrasts `reachClosureComputable` with a
  `Classical.decPred`-filtered formulation, three `Exec.lean` sites at
  L56/L110/L145/L254 are the style island's positive
  "no `Classical`" promises). No code-level `classical` or
  `Classical.*` reference exists; the style island
  `[Fintype V] [DecidableEq V]`
  (`../DESIGN.md` *Pebble-game style island*) provides every typeclass
  the bodies use. No comment-out test was needed because there is
  nothing to comment out; sanity build via
  `lake build CombinatorialRigidity.PebbleGame.Exec` succeeded as
  expected. Confirms the pre-grep summary in *Current state*.
- **B2: `noncomputable def` audit (Phase 10+11 surface)** — no-op
  closure with **smell-table revision**. Re-grep via
  `grep -nE "(^|\s)noncomputable (def|abbrev|instance)"` over the
  Phase 10+11 surface returns **6 sites** — `outList` and `reach` in
  `Basic.lean` (L138 / L1055), `tryReachPebble` and `tryAddEdge` in
  `Algorithm.lean` (L122 / L448), and `runPebbleGame.aux` /
  `runPebbleGame` in `Correctness.lean` (L748 / L802). Each is
  forced by `Finset.toList` (math-layer `outList`'s `Multiset.toList`
  → `Classical`-flavored `Quotient.lift`), and the two `Correctness`
  sites additionally consume `G.edgeFinset.toList.map Quot.out` for
  edge enumeration (`Quot.out` uses `Classical.choice`). Every site's
  in-source docstring already names the driver, with the math-layer
  / exec-layer split documented at `../DESIGN.md` *Pebble-game style
  island*. No vestigial sites; no in-round refactor candidate
  surfaced. Sanity build via
  `lake build CombinatorialRigidity.PebbleGame.Correctness` clean.

  **Delta vs Phase 9-cleanup B4** (Phase 9's `noncomputable def`
  audit covered the same surface modulo the Phase 11 reshape, with 6
  sites at the time: 5 PebbleGame + 1 DFS):
  - **Removed (−1):** `Search.DFS.reachClosure` retired in Phase 11
    Layer 1 in favour of computable `reachClosureComputable` (no
    `noncomputable` keyword; `DFS.lean` now has 0 sites — a strict
    improvement, since the predecessor had been forced
    `noncomputable` by an undecidable `Relation.ReflTransGen`
    membership and could not feed `#eval` / `decide`).
  - **Added (+1):** `Correctness.runPebbleGame.aux` in Phase 11
    Layer 4b — introduced to dodge the `match h : <expr> with`
    substitution quirk (TACTICS-QUIRKS § 17) by taking the workhorse
    `Sum`-shaped output as an explicit argument. The keyword on aux
    is forced by the same drivers as the parent `runPebbleGame`.
  - **Net total stays 6**; the structural-edit phase did not
    introduce vestigial `noncomputable` sites.

  **Smell-table revision (in-commit).** The pre-grep `noncomputable
  def` row in *Current state* claimed DFS:2, Basic:8, Algorithm:10,
  Correctness:6, Exec:3 = 29 sites; the actual count under
  `^noncomputable def` (or the inclusive
  `(^|\s)noncomputable (def|abbrev|instance)`) is **6**. The
  29-site total was inflated by counting docstring / comment
  mentions of the word "`noncomputable`" (e.g. `Basic.lean:130-136`
  is a four-line docstring paragraph using the word three times
  while declaring exactly one `noncomputable def`). Revised in
  *Current state* alongside an explanatory note; no other row in
  the pre-grep table is affected by the same conflation.
- **B3: Multi-step `rw [..., ..., ..., ...]` chain audit** — no-op
  closure with **smell-table revision**. The pre-grep at round open
  used `grep -nE "rw \[[^]]*,[^]]*,[^]]*,[^]]*\]"` (four `[^]]`
  segments separated by three commas) and reported 9 sites. That
  regex doesn't track inner-bracket depth, so three `Basic.lean`
  hits (lines 421/435/448) were 2-arg `rw` chains whose top-level
  comma count was inflated by inner `⟨_, _⟩` anonymous-constructor
  tuples — e.g. `rw [if_pos ⟨hmem, hw⟩, if_pos ⟨hmem, hu⟩]` has 3
  top-level commas under a depth-blind count but only 1 at depth 0.
  A depth-aware AWK re-count on the same surface (tracking nesting
  in `[`/`]`, `(`/`)`, `⟨`/`⟩`) returns **6 genuine 4+ arg sites**:
  3 in DFS (L207/L213 each `[mapRel, length, length, ih]`-shaped;
  L300 `[arcsFinset_cons, Finset.image_insert, ← ih,
  reversedArcsFinset_cons]`), 2 in Basic (L268 sum-rewrite chain
  `[Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul,
  mul_comm]`; L940 `[pebOn_empty, outOn_empty, Nat.add_zero,
  mul_comm V'.card k]`), 1 in Exec (L177 Sym2 inf/sup chain). Each
  is a per-step structural rewrite — every step does one distinct
  semantic normalisation (definitional unfold, fold of a constant
  sum, smul→mul coercion, factor-order alignment) with no candidate
  *fused* mirror lemma the combination would collapse to. The
  Phase 9-cleanup B7 finding ("multi-step `rw` chains likely break
  down to per-step structural rewrites") generalises through the
  Phase 11 reshape; no new project-mirror surfaced.

  `lean_multi_attempt`-tested `simp only [name list]` collapses at
  each site close successfully, but with no measurable simplification
  benefit (most chains land at the same goal state via the same
  rewrites), and `simp [..., mul_comm, ...]` carries non-terminator
  risk where `rw [mul_comm V'.card k]` is the deterministic single-
  step. Kept as-is.

  Two **observations surfaced** that aren't B3's concern but should
  be flagged: (i) `Basic.lean` L435/L448 (inner-tuple-comma sites)
  currently do `rw [if_pos …, if_neg …] at h` then `omega`, and
  `simp [h_mem, h_ne] at h` produces a *cleaner* `h` (no residual
  `+ 0`) that an `exact h` could close directly — but the existing
  shape is correct and the audit's discharge isn't a free-form
  refactor (cf. `../CLEANUP.md` *What a cleanup round is not*); not
  in-scope at B3. (ii) The 9-site count drove the per-file
  expectation in this round's open prose ("3 in DFS, 5 in Basic, 1
  in Exec") — the revised counts (3 DFS / 2 Basic / 1 Exec = 6) are
  the canonical numbers going forward; *Current state* smell-table
  row revised accordingly.

  Sanity build via `lake build` clean (2467 jobs). All six sites
  remain at their current shape post-audit.
- **B4: `letI`/`haveI Fintype.ofFinite` audit (Phase 10+11 surface)**
  — no-op closure. Four greps over
  `CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,Exec,
  Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`, and
  `Main.lean`:
  (i) `grep -nE 'haveI'` — **zero** hits.
  (ii) `grep -nE 'letI'` — **zero** hits.
  (iii) `grep -nE 'Fintype\.ofFinite'` — **two** hits at `Basic.lean:49`
  and `DFS.lean:73`. Both are inside the *Style island* docstring
  paragraphs ("This file ... departing from the project's default
  `[Finite V]` + inline `Fintype.ofFinite V` bridge idiom") — pointers
  *to* the project-default idiom that the algorithm files deliberately
  do *not* use; neither is a code-level invocation.
  (iv) `grep -nE 'Set\.Finite\.fintype'` — **zero** hits.
  The style island convention `[Fintype V] [DecidableEq V]` end-to-end
  (`../DESIGN.md` *Pebble-game style island*) is uniformly respected
  across the Phase 10+11 surface; the algorithm bodies pull finiteness
  data from the typeclass slot rather than deriving it inline. No
  comment-out test was needed because there is nothing to comment out.
  Confirms the expected closure noted at round open. Bucket B is now
  80 % done (B1 no-op / B2 no-op + smell-table revision / B3 no-op +
  smell-table revision / B4 no-op); B5 pending.
- **B5: `@[nolint …]` / `set_option linter` audit (Phase 10+11 surface)**
  — no-op closure. Two greps over
  `CombinatorialRigidity/PebbleGame/{Basic,Algorithm,Correctness,Exec,
  Examples}.lean`, `CombinatorialRigidity/Search/DFS.lean`, and
  `Main.lean`:
  (i) `grep -nE '@\[nolint|set_option linter'` (the CLEANUP.md §B
  pattern) — **zero** hits.
  (ii) Wider case-insensitive `grep -nEi 'nolint|linter'` — **zero**
  hits, including no docstring or comment mentions. The Phase 10+11
  surface carries no lint suppressions of any form — neither
  declaration-attached `@[nolint …]` nor file-scoped or `in`-scoped
  `set_option linter.X false`. No comment-out test was needed because
  there is nothing to comment out; the audit confirms the round-open
  expected closure noted in *Current state*. The only project-wide
  `@[nolint unusedArguments]` site (`IsInfinitesimallyRigid` in
  `Framework.lean`, per `../CombinatorialRigidity/CLAUDE.md` *Before
  each commit — build and lint gates*) sits outside the cleanup
  round's Phase 10+11 scope, and no new suppression has been
  introduced anywhere on the surface — neither Phase 11's
  verdict-bearing return-type collapse (Layer 4 / Layer 4b) nor
  Phase 10's `Exec` / `Examples` / `Main` forward additions needed
  one. This is the expected outcome given the style island
  `[Fintype V] [DecidableEq V]` already supplies the typeclass
  density the algorithm bodies need without a `nolint` /
  `set_option linter` workaround.

  **Bucket B (code-smell sweep) complete.** B1 no-op / B2 no-op +
  smell-table revision / B3 no-op + smell-table revision / B4 no-op /
  B5 no-op. Every B entry closed as a no-op; the Phase 10+11 surface
  is clean against the round's code-smell grep targets. Two smell-
  table revisions surfaced during the sweep (B2's `noncomputable def`
  conflation between actual sites and docstring mentions; B3's
  depth-blind comma count over-counting `⟨_, _⟩`-tuple chains as 4+
  arg `rw` chains) — both are revisions to the pre-grep summary's
  *expectations*, not to source code; they pass through to the next
  cleanup round as accurate audit baselines.
- **C1: Long-proof top-10 ranking (Phase 10+11 surface)** —
  ranking landed; full table with per-site one-line question is
  in §C above (the *Bucket C — Long-proof audit* checklist entry).
  Ranking discharged via a docstring-filtered AWK pass over the
  seven Phase 10+11 surface files
  (`CombinatorialRigidity/PebbleGame/{Algorithm,Basic,Correctness,
  Examples,Exec}.lean`, `CombinatorialRigidity/Search/DFS.lean`,
  `Main.lean`); the docstring filter was needed because the
  `../CLEANUP.md` §C template's naked AWK pattern picked up an
  Exec docstring reference to "theorem `runPebbleGameWith_correct`"
  as a 70-LoC declaration body. Total bodies ≥ 50 LoC: 10 across
  three files (`Algorithm.lean` 6 / `Correctness.lean` 2 /
  `DFS.lean` 2); `Basic.lean`'s longest body
  (`pebOn_add_span_add_outOn` at 41 LoC) sits just outside; `Exec`
  / `Examples` / `Main` carry no entries ≥ 35 LoC.

  **Per-site one-line question** (full text in §C; summary by
  question category):
  - *API extraction* candidates: #1 `tryAddEdgeWith` (case-5 inline
    body), #4 `runPebbleGameWith_witness_bridges` (three sequential
    reconciliations), #9 `tryAddEdgeWith_witness_uv` (projection
    through the recursion).
  - *Cross-proof unification* candidates: #2 `tryAddEdgeWith_reachable`,
    #5 `runPebbleGameWith_mem_underline`, #6 `tryAddEdgeWith_underline`,
    #8 `runPebbleGameWith_underline_subset` — split into two clusters
    (Algorithm.lean's three fold-traversal lemmas on `runPebbleGameWith`
    vs. three case-traversal lemmas on `tryAddEdgeWith`).
  - *Mathlib lemma we missed* candidate: #3
    `span_succ_le_edgesIn_ncard_of_subset` (ncard add-cancel chain).
  - *Definitional refactor* candidate: #7 `reachableFindingAux_complete`
    (inner-induction's `visited` accumulator boundary).
  - *Tactic substitution* candidate: #10 `reachableFinding_complete`
    (per-step bookkeeping after `head_induction_on`).

  Two cross-proof unification clusters are the primary C2 anchors:
  (i) Algorithm.lean's three fold-traversal lemmas (#5 / #8 / the
  #12-runner-up `runPebbleGameWith_reachable`) share a fold-over-`Sum`
  case dispatch; (ii) Algorithm.lean's three case-traversal lemmas
  (#2 / #6 / #9, all rooted at `tryAddEdgeWith`'s seven-case
  recursion). C2 dispatches each top-10 entry via the four-question
  walk and decides per cluster whether an in-round refactor (C3) is
  structurally small enough to land alongside the cleanup round.

## Blockers / open questions

*(None at round open.)*

## Hand-off / next phase

Round still in progress; Bucket A complete (A1 no-op / A2 targeted
fix / A3 targeted fix / A4 no-op); Bucket B complete (B1 no-op /
B2 no-op + smell-table revision / B3 no-op + smell-table revision /
B4 no-op / B5 no-op); **C1 closed** with the top-10 ranking table +
per-site question in §C and a summary in *Cleanup pass summaries*.

Next concrete commit: **C2** — four-question walk over the C1
top-10 sites. Dispatch each of the ten entries via the per-site
question (already recorded in §C's table) and record the verdict:
*no-op* (the long-proof body is forced by the recursion / case
structure with no extracted sub-lemma to win), *in-round refactor*
(the audit anchor surfaces a structurally small refactor — a fused
mirror lemma, an extracted helper, a `lean_multi_attempt` tactic
substitution — that should land this round per `../CLEANUP.md`
*Refactor passes are in scope when surfaced by an A-D audit*), or
*deferred* (the refactor is large enough that it carries into a
follow-up phase, e.g. the typeII-cores unification from Phase 5's
appendix). C2's primary anchors are the two cross-proof unification
clusters identified in C1 — Algorithm.lean's three fold-traversal
lemmas (#5 / #8 / runPebbleGameWith_reachable) and three
case-traversal lemmas (#2 / #6 / #9). After C2, **C3** (any
in-round refactor candidates land each as its own commit). Then
**D** (project-organization compression of `notes/Phase10.md` and
`notes/Phase11.md`, FRICTION re-skim, DESIGN.md drift check,
no-residual-lifts audit).

The round's close hand-off, when reached, defaults to whichever
follow-up direction the user picks from Phase 11's three candidates
(component pebble game / Henneberg-sequence extraction / benchmarks
harness); cleanup-round work is hygiene, not a phase dependency.
