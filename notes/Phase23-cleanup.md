# Phase 23-cleanup — blueprint readability rewrite + statement-surface audit (work log)

**Status:** in progress — **R1e landed (2026-07-03); parks at owner
re-review (checkpoint #3)**: the calibration-v3 revision of the R1 page
(`algebraic-induction.tex` preamble + `panel-layer.tex`) against
`blueprint/AUTHORING.md` rules 14–16 + the checkpoint-#2 defect list. R2
stays blocked until R1e passes owner re-review.
Landed so far (details in *Decisions made*): R0 (style spec); the `hfresh`
vacuity repair arc F1–F3 (2026-07-02 — the supply binder was
kernel-checked unsatisfiable, repaired to the minimality-conditioned form
+ satisfiability lemmas + the `Nonvacuity.lean` witness); S2 (the `d = 3`
producer-spine collapse); R1 through R1e (the calibration chapter at the
owner's v1 → v2 → v3 rules); and the owner-directed E1–E3 consumer-surface
ergonomics arc (2026-07-03 — headline decls take `3 ≤ n` + an explicit
label-headroom bound, `k := n − 1`, `theorem_55_all_k` merged away;
`notes/FreshEdgeSupply-design.md` §E). All gates green throughout. Round
manual: `CLEANUP.md`.
Owner-directed round between Phases 23 and 24 (owner call, 2026-07-02): **not**
a full A–D cleanup — §A runs only in the narrow *statement-surface* form
below; §B/§C are out of scope (no friction signal; historically no-op); §D
rides as an optional tail. The round is expected to run as a
`/coordinate-phase` loop; each task below is a dispatch-sized unit unless
marked otherwise.

## Goal

Rewrite the molecular-program blueprint chapters so they are readable by
**a mathematician working in rigidity theory who knows Katoh–Tanigawa 2011
but has not carefully studied its proof**. A 2026-07-02 survey (record at
the bottom of this file) found ~60–90 passages of project-internal process
vocabulary, ~70% in six files, including inside the *statements* of the
headline theorems. The failure is deeper than word choice: statements carry
formalization bookkeeping inside the claim, and proofs read as dep-graph
traversals ("the base-adjacent arms fire the M₁/M₂ template") rather than
mathematical arguments. The fix is a prose-layer rewrite against the target
style below, with a small Lean statement-surface audit running just ahead
of it (`CLEANUP.md` §A bias: make the Lean as painless as the math *before*
writing a prose aside).

## Target style

Codified (task R0, landed) in `blueprint/AUTHORING.md` *Audience &
vocabulary* — the numbered *Target style* rules, the audience test, and
the terminology dictionary all live there now; read it before starting
any R-task below. The `intro.tex` one-paragraph dep-graph-convention
note (rule 4) landed in the same commit
(`chapter/intro.tex` *Reading this blueprint*).

### Calibration sample (owner-approved; the R1 target level)

For `thm:theorem-55-d3-instance` (`panel-layer.tex`), currently a single
node pinning five decls whose statement includes "all three adjudicated
carries (`h622`, `hsplit`, `hcontract`) are now discharged (Phase 22k
L7–L9)". Target:

> **Theorem** (Theorem 5.5 at d = 3; KT Theorem 5.5). *Let G be a minimal
> 0-dof-graph with |V| ≥ 2. Then G admits a panel-hinge realization (G,p)
> in ℝ³ whose rigidity matrix attains the maximal rank D(|V|−1), where
> D = 6. Moreover, if G is simple, the realization may be chosen generic:
> hinges in general position, with algebraically independent coordinates.*
>
> **Proof.** Induction on |V|, driven by the reduction theorem (Theorem
> 4.9, \cref{thm:minimal-kdof-reduction}): every minimal 0-dof-graph on at
> least three vertices has a cut edge, a proper rigid subgraph, or a
> degree-2 vertex whose splitting-off is again minimal. The two-vertex
> base — the double edge — is realized directly (\cref{...}). Each
> reduction move is then realized at full rank: contraction of a proper
> rigid subgraph by Case I (\cref{...}), the cut edge and the k > 0
> splitting-off by Case II (\cref{...}), and the k = 0 splitting-off — the
> heart of the proof — by Case III (\cref{lem:case-III}). Throughout, the
> induction hypothesis is quantified over *all* deficiencies k′, not only
> k′ = 0 (KT hypothesis (6.1)); Case III consumes this stronger hypothesis
> through its nested rank bound (\cref{lem:case-III-nested-rank-lower}). ∎
>
> *Formalization note.* The general-position conjunct is conditioned on
> simplicity because it fails at the non-simple base (two parallel copies
> of an edge admit no "nonparallel" realization); the Lean statement is
> the conjunction of the two claims above. [+ role-labeled pin map.]

A matching sample exists for `lem:case-III` (same conversation): statement
reduced to graph hypotheses + all-deficiency IH + conclusion; proof = the
triangle floor / chain-vs-cycle dichotomy / one split + eq. (6.12)
placement / Claim 6.11 redundant row + candidate completion / eq. (6.67)
discriminator / genericity upgrade, each step anchored per rule 7.

### Terminology dictionary (D2 — settled at defaults, landed in R0)

Table now lives in `blueprint/AUTHORING.md` *Audience & vocabulary*
(task R0). This dictionary settles `notes/FRICTION.md` open entry
*[process] "Brick" is a project mnemonic…* (task P2, still open — P2
flips the FRICTION entry to resolved, pointing at the AUTHORING.md
table).

## Task list

Order: R0 first (the style spec must exist before any chapter dispatch);
R1 is the calibration chapter and **stops for owner review of the rendered
draft** before R2+ proceed; P1 (the lint gate) runs last, after the
chapters are clean.

### R0 — codify the style (1 commit) — done
- [x] Lift *Target style* + the terminology dictionary into
  `blueprint/AUTHORING.md` as a new **Audience & vocabulary** section
  (audience test: "would a rigidity theorist who has read KT know this
  term?"); compress this file's copy to a pointer. Add the `intro.tex`
  one-paragraph dep-graph-convention note in the same commit.

### R1–R11 — per-chapter rewrites
Each chapter task = (a) **statement-surface audit** of the decls its nodes
pin (for every would-be Formalization note, first attempt the Lean
simplification that removes it; Lean changes land as their own commits
*before* the prose commit), then (b) **prose rewrite** to Target style,
then (c) `blueprint/verify.sh` + `blueprint/lint.sh` green. Line counts
are current-tree.

- [ ] **R1 — `algebraic-induction/panel-layer.tex`. CALIBRATION.**
  Landed in four passes — headline-node family, infrastructure sweep,
  R1d calibration-v2 chapter revision + the `algebraic-induction.tex`
  overview preamble, then **R1e — the calibration-v3 revision** (2026-07-03,
  details: *Decisions made*) fixing owner checkpoint #2 (register/tone, pin
  budgets, statement brevity, per-section points; v3 rules 14–16 in
  `blueprint/AUTHORING.md`). R1 completes when the R1e page passes owner
  re-review (checkpoint #3).
- [ ] **R2 — `algebraic-induction/case-iii.tex` (1514).** Largest; may be
  2–3 dispatches (suggested split: Claim 6.11 chain / Claim 6.12 + d=3
  assembly / general-d dispatch + `lem:case-III`). Narrative blocks become
  proof backbones; seeded item S3 (S1 resolved by the `hfresh` repair arc).
- [ ] **R3 — `algebraic-induction/genericity-and-count.tex` (670).**
  N7b-*/M* titles; the superseded-block collapse (D1); `notes/` file refs.
- [ ] **R4 — `rigidity-matrix.tex` (616).** "L5a-i splice brick"-family
  titles (incl. one "superseded, route-2 leaf" title), `hub`-as-term,
  status-paragraph preamble.
- [ ] **R5 — `molecular-induction.tex` (1587).** "L4a/L4b-2 producer"
  titles, "leaf-most red node / live to-do list" preamble,
  `notes/Phase20.md` ref; prose is otherwise more dilute — likely 1–2
  dispatches.
- [ ] **R6 — `algebraic-induction/case-i.tex` (737).** `hcSimple`/
  `hcontract`/`h65` in statements; `hg`/`hcoord`/`hindep` prose.
- [ ] **R7 — `algebraic-induction/case-ii.tex` (195).** motive/producer/
  spine. (The `algebraic-induction.tex` overview was pulled forward into
  R1d at the 2026-07-03 owner review — same rendered page as the
  calibration chapter.)
- [ ] **R8 — `meet.tex` (342).** "N3b assembly" titles; motive.
- [ ] **R9 — `deficiency.tex` (489) + `extensor.tex` (219).** Preamble
  rewrites (incl. deleting `extensor.tex`'s reader-facing forward-mode
  mechanics note); light prose touches.
- [ ] **R10 — `body-bar.tex` (642) + `body-hinge.tex` (148).**
  Preamble/dep-graph framing only.
- [ ] **R11 — pre-molecular spot pass.** `rigidity-matroid.tex` two
  `DESIGN.md` refs; `pebble-game.tex` `hD` mentions; nothing structural.

### S — seeded statement-surface audit items
- [x] **S1 — the fresh-edge supply binder.** **RESOLVED** (2026-07-02) by
  the `hfresh` repair arc (`notes/FreshEdgeSupply-design.md`): the original
  universal binder was kernel-unsatisfiable for nonempty `α` (the
  all-loops-at-one-vertex graph has `edgeSet = univ`), so the S1 remedy
  ("derive from `[Infinite β]`") was impossible and the affected statements
  were vacuous. Repaired to a minimality-conditioned two-tier supply (F1),
  satisfiability lemmas + a non-vacuity witness (F2), docs close-out (F3) —
  all three leaves landed 2026-07-02.
- [x] **S2 — the `d = 3` producer duplication.** **RESOLVED (collapse)**
  (2026-07-02): `theorem_55_minimalKDof_k` re-based onto
  `theorem_55_minimalKDof_gen (k := 2)`; the three now-orphaned d=3-only
  producer wrappers deleted; their blueprint pins re-pointed at the `_gen`
  forms. See *Decisions made* below for the full verdict.
- [ ] **S3 — promote the dispatch/discriminator pair.**
  `chainData_dispatch` / `chainData_fire_discriminator`
  (`Molecular/AlgebraicInduction/CaseIII/Realization.lean`) are the firing
  mechanism of KT eq. (6.67) and are pinned nowhere. Promote to small
  nodes (they are genuine steps of KT's argument, consumed by R2's
  rewritten `lem:case-III` proof); restate their signatures first if
  prose-embarrassing.

### D — decisions with defaults (owner sign-off)
- [x] **D1 — superseded blocks.** **Owner-confirmed 2026-07-02: collapse
  (the default).** `genericity-and-count.tex:476–660` (four dead lemmas
  N7b-4/M1/M2/M3 + route-history prose) and the `rigidity-matrix.tex:495`
  superseded title each collapse to a one-sentence remark (git is the
  audit trail), **revising `blueprint/CLAUDE.md`'s retain-with-marker
  supersession rule in the same commit** so the discipline and the corpus
  stay consistent. Lands with R3/R4.
- [x] **D2 — terminology dictionary** (table above). **Owner-confirmed
  2026-07-02: as listed.** Lands with R0.

### P — prevention (after R-tasks)
- [ ] **P1 — `lint.sh` vocabulary gate.** Greppable banned-term check over
  `blueprint/src/chapter/` (candidate list: `brick`, `motive`, `producer`,
  `stratum`, `green-modulo`, `Phase 1[7-9]`, `Phase 2[0-9]`, sub-phase
  codes `\b2[23][a-l]\b`, `\mathtt{h[a-z0-9]+}` in statement blocks). Tune
  to zero false positives against the cleaned corpus; runs with the other
  per-commit static gates.
- [ ] **P2 — friction-log resolution.** Flip `notes/FRICTION.md`
  *[process] "Brick" is a project mnemonic…* to resolved, pointing at the
  D2 verdict + the new AUTHORING.md section.

### Optional tail (CLEANUP.md §D riders; skip if the round runs long)
- [ ] `notes/FRICTION.md` `[resolved]`-entry archive sweep (mechanical;
  the file is ~3.9k lines).

## Out of scope / deferred (decided at round open)
- **ScrewSpace "part 2"** (general-`d` opaque carrier,
  `notes/ScrewSpaceCarrier-design.md`) — was deferred "to the Phase-23
  boundary", but its motivating symptom is gone (`maxHeartbeats` overrides
  at 0 project-wide) and Phases 24–25 don't stress the general-`d` tree.
  **Re-assess at Phase 26 open.**
- **Retroactive BlueprintExposition scan** (`notes/BlueprintExposition.md`,
  scheduled 2026-06-21) — exposition *addition*, not readability; stays
  scheduled, unchanged.
- **CLEANUP §B code-smell / §C long-proof sweeps** — no signal.
- **Lean proof-body golfing; Lean file/section renames** — invisible to
  blueprint readers.

## Blockers / open questions
- **The `hfresh` repair (F1–F3) is complete (2026-07-02)** — no longer a
  blocker. R1 (and R2–R11) resume against the repaired, satisfiable
  statements; see `notes/FreshEdgeSupply-design.md` for the compressed
  verdict.
- D1 + D2: owner-confirmed at defaults, 2026-07-02 (no longer open).

## Hand-off / next phase
**R1e landed (2026-07-03); parks at owner re-review (checkpoint #3).** The
calibration-v3 revision of the rendered `sec-molecular-algebraic-induction`
page (the R1 files: `algebraic-induction.tex` preamble + `panel-layer.tex`)
is in, against `blueprint/AUTHORING.md` rules 14–16 + the checkpoint-#2
defect list (register/tone, pin budgets, statement brevity, and the
per-section points — the full list is in the checkpoint-#2 commit + the
AUTHORING.md rules it drove). Docs-only; `blueprint/verify.sh` +
`blueprint/lint.sh` green. The next action is **owner re-review of the
rendered page**; **do NOT start R2** until R1 passes.

If checkpoint #3 passes: R2 (`case-iii.tex`, seeded item S3) per the task
list; then R3–R11, then P1/P2 close the round.

**Follow-up surfaced by R1e (for R6/R7, not now):** the pin-budget split
added finer `panel-layer.tex` nodes (`def:hinge-coplanar`,
`def:panel-general-position`, `lem:general-position-support-nonzero`,
`lem:moment-curve-general-position`, `lem:generic-yields-genuine-hinge`,
`def:framework-with-normal`, `lem:with-normal-preserves`).
`case-i.tex`/`case-ii.tex` still `\uses` the coarse
`def:panel-hinge-framework` / `def:framework-with-graph` (valid, no gate
issue); when R6/R7 revise those chapters, their `\uses` edges can be refined
to the new nodes.

After P1/P2 close the round: update this file's Status, flip the ROADMAP row,
and Phase 24 opens per the standard protocol
(`notes/MolecularConjecture.md` *Opening the next phase*).

## Decisions made during this round
- **R1e — calibration-v3 revision of the R1 page (2026-07-03, docs-only):**
  register flattened against KT 2011's running prose (`.refs/`; removed
  significance-pointing, mechanism metaphors, and most em-dash asides, rule
  14); the five over-pinned nodes split to ≤3 pins (rule 15) —
  `def:panel-hinge-framework` 8→2, `def:framework-with-graph` 7→3,
  `def:rank-hypothesis` 4→2, `def:genuine-hinge-realization` 3→2,
  `def:panel-support-extensor` 3→1, via seven new sibling nodes
  (see *Hand-off*); Formalization notes moved outside definition
  environments (rule 16); the "bar-joint 1-extension" credited to
  Whiteley 1996 Thm 2.2.2 (`\cite{whiteley1996}` = KT ref [33], verified
  against KT p. 4 + AMS metadata). All checkpoint-#2 per-section defects
  fixed; no Lean touched; `verify.sh` + `lint.sh` green.
- **E3 — the `theorem_55_all_k` docstring sweep landed (2026-07-03):** 24
  mentions across 10 files re-pointed by role: `theorem_55_minimalKDof_k_all_k`
  for spine-shape/branch references (`hsplitZero`/`hcontract` carries, the
  motive) — the majority; `theorem_55_d3` for the 3 public-instance mentions
  in `Theorem55.lean`. Two exceptions: a `PanelHinge.lean` black-box citation
  of "Theorem 5.5" at general `k` (no branch in view) went to
  `theorem_55_minimalKDof_gen` instead, and a `Theorem55.lean` mention naming
  two now-merged decls was reworded descriptively rather than repeat
  `theorem_55_d3` confusingly. The five E2-reshaped public decls' cross-file
  docstrings were checked and already consistent. Done-gate 0 hits; `lake
  build` (full, warning-clean) / `lake lint` green; no blueprint touched.
- **E2 — the consumer-surface reshape build landed (2026-07-03):** the five
  in-place reshapes (`molecular_conjecture`, `theorem_55_gen`,
  `rankHypothesis_of_theorem_55_gen`, `rankHypothesis_of_theorem_55_d3`,
  `theorem_55_d3`) all took the exact signatures pinned in
  `notes/FreshEdgeSupply-design.md` §E.3, with `theorem_55_all_k` deleted and
  merged into `theorem_55_d3`; `Nonvacuity.lean`'s `freshEdgeSupply_witness`
  deleted and `molecular_conjecture_witness` restated per §E.4; the seven
  `panel-layer.tex` touch-points landed per §E.5. One deviation from the
  pinned homes: `Graph.bodyBarDim_eq_screwDim_sub_one` could not land in
  `RigidityMatrix/Basic.lean` as pinned — that file is a `module` file and
  `Graph.bodyBarDim` lives in the non-`module` `BodyBar/Framework.lean`, and
  a `module` file cannot import a non-`module` file at all (`LEAN-OPS.md`).
  Landed instead in `PanelLayer.lean`, next to its already-landed sibling
  `Graph.eq_add_one_of_bodyBarDim_eq_screwDim` — same name/signature/proof,
  different file (`Graph.six_le_bodyBarDim` landed in `BodyBar/Framework.lean`
  as pinned, no issue there). Full account: `notes/FRICTION.md` *[process] A
  design doc's pinned lemma "home" can be unbuildable …*. `lake build`
  (full, warning-clean) / `lake lint` / `blueprint/verify.sh` /
  `blueprint/lint.sh` all green.
- **E1 — consumer-surface packaging settled (2026-07-03, design pass):**
  full pin in `notes/FreshEdgeSupply-design.md` §E. Public surface = the six
  `panel-layer.tex`-pinned forms; five reshape in place (single `3 ≤ n` +
  explicit `hcard` headroom bound; framework types at `k := n − 1`,
  ℕ-subtraction — defeq to the literal at `n := 3`, spiked), the spanning
  corollary is already ergonomic and unchanged; `theorem_55_all_k` (byte-
  identical to `theorem_55_d3`) is deleted; the `hfresh`-threading engine
  forms are untouched. Two new arithmetic helpers; witness restated;
  blueprint impact = 7 `panel-layer.tex` touch-points, statements untouched.
- **`hfresh` repair route settled (2026-07-02, design pass):**
  minimality-conditioned supply, two tiers — leaf producers take the
  per-graph `∃ e₀ ∉ E(G)`, recursion drivers/spine take
  `∀ c G', IsMinimalKDof n c → ∃ e₀ ∉ E(G')`; `[Finite β]` stays (it is
  load-bearing through the vendored matroid-union layer, so the
  `[Infinite β]` route is a framework rebuild — dead). Satisfiability
  compile-checked (edge bound from minimality + headroom derivation).
  Full verdict, signatures, and leaves F1–F3:
  `notes/FreshEdgeSupply-design.md`.
- **D1 + D2 adjudicated (owner, 2026-07-02, session-start check-in):** both
  at defaults — D1 collapse (dead-route blocks → one-sentence remarks +
  CLAUDE.md supersession-rule revision, with R3/R4), D2 dictionary as
  tabled (lands in AUTHORING.md with R0). Details in the task-list entries.
- **R0 landed (2026-07-02):** *Target style* (8 rules) + the D2
  terminology dictionary moved to `blueprint/AUTHORING.md` *Audience &
  vocabulary*; this file's copies compressed to pointers. The `intro.tex`
  *Reading this blueprint* paragraph gained the one-place explanation of
  the dep-graph color convention + the forward-mode "leaf-most red node /
  live to-do list" vocabulary, so per-chapter preambles (R2–R11) can drop
  their own copies without losing the explanation anywhere.
- **F1 landed (2026-07-02):** the Tier-1/Tier-2 `hfresh` signatures per the
  design doc's *Verdict* are in across all six carrier files (16 decls);
  the three application sites, the spine's two split-arm instantiations,
  and every call-site reorder from the Tier-1 binder move are rewritten;
  the docstrings narrating the old unconditioned form (Reduction.lean,
  `molecular_conjecture`) and the blueprint's supply-describing passages
  (`panel-layer.tex`, `case-ii.tex`, `case-iii.tex`, `molecular-induction.tex`)
  are resynced. `lake build`/`lake lint`/`blueprint/verify.sh`/
  `blueprint/lint.sh` all green. F2 is next.
- **F2 landed (2026-07-02):** the two satisfiability lemmas
  (`Graph.edgeSet_ncard_add_deficiency_le_of_isMinimalKDof`,
  `Graph.freshEdgeSupply_of_card_lt`) land in `Deficiency.lean` verbatim per
  the design doc's spikes; the two-decl `Nonvacuity.lean` witness
  (instance `n=3, k=2, α=Fin 2, β=Fin 7`, graph `Graph.singleEdge 0 1 0`)
  fully applies `molecular_conjecture`, certifying non-vacuity with no
  `sorry`; the `rem:molecular-conjecture-nonvacuous` blueprint remark
  records the witness on `panel-layer.tex`; the README/home_page/ROADMAP
  honesty clauses (¶ + the home_page status-table row) are all dropped in
  this commit (not deferred to F3). `lake build`/`lake lint`/
  `blueprint/verify.sh`/`blueprint/lint.sh` all green. F3 is next.
- **F3 landed (2026-07-02, docs-only):** `notes/FreshEdgeSupply-design.md`
  compressed to a verdict + pointer (per `notes/CLAUDE.md` *Live design
  recon*; the full recon lives in git history); S1 above flipped to
  resolved; the `notes/Phase22a.md`:440 parenthetical reworded to cite the
  conditioned form. The `hfresh` repair arc (F1–F3) is closed; this commit's
  hand-off re-points at R1.
- **S2 landed + follow-up (2026-07-02, Lean-only, ahead of the R1 prose
  commit):** the "duplication" A2/orphan-decl sweep was no longer proof
  *content* — `theorem_55_base_producer` / `case_cut_edge_realization{,_gp}`
  were already thin `k := 2` wrappers of grade-general `_gen` forms; only
  `theorem_55_minimalKDof_k` independently re-ran the induction combinator
  instead of delegating to `theorem_55_minimalKDof_gen (k := 2)`. Collapsed
  to a one-line corollary; deleted the 3 orphaned wrappers + a 4th
  (`exists_extensor_in_two_panels`) found in the follow-up sweep; re-pointed
  4 blueprint `\lean{}` pins and 3 stale docstring references (`PanelLayer.lean`,
  `GenericityDevice.lean:1486`, `Theorem55.lean`) at the `_gen` forms —
  mechanical name swaps, no prose rewrite. Incidental, left untouched
  (unpinned, flagged for a future dead-code sweep): `case_I_dispatch` is an
  analogous zero-caller d=3 `k := 2` wrapper. `lake build`/`lake lint`/
  `blueprint/verify.sh`/`blueprint/lint.sh` all green.
- **R1 headline-node prose rewrite (2026-07-03, docs-only):** the five
  headline nodes to (v1) Target style; `thm:theorem-55-d3-instance`'s 5
  pins split into the main node + `cor:theorem-55-d3-spanning`; a dup pin
  and a stale extra pin dropped (pin-hygiene, no Lean change). Gates
  green. Details in git history.
- **R1 infrastructure sweep (2026-07-03, docs-only):** the ten
  `\uses`-adjacent infrastructure nodes audited against their actual Lean
  signatures; 6 needed terminology edits (incl. the four base-region
  retitles), plus adjacent stray spots so the rendered page was clean end
  to end. No Lean changes. Gates green. Owner review #1 then found the
  page "not yet comprehensible to a typical mathematician" → R1d.
- **R1d — calibration-v2 chapter revision (2026-07-03, docs-only):** all
  six owner defect points fixed (statement purity via two new remarks; KT
  prefixes chapter-wide; English-only Formalization notes; connective
  prose; multi-paragraph proofs; the single fresh-edge-label remark), and
  the `algebraic-induction.tex` overview preamble rewritten jargon-free
  (pulled forward from R7). No Lean touched; gates green. Owner review #2
  then returned the v3 defect list (register/pins/statement brevity —
  see *Hand-off*) → R1e.

## Survey record (2026-07-02, condensed; line numbers = current tree)

Pre-molecular chapters are clean (3 short formalization parentheticals
across six files; no process vocabulary). Molecular chapters, worst first:

1. `algebraic-induction/panel-layer.tex` — jargon inside the Theorem
   5.5/5.6 statements: "zero-carry instance" (278), "simplicity-conditioned
   motive" (260, 291), "adjudicated carries (h622, hsplit, hcontract) …
   (Phase 22k L7–L9)" (297–301), "M4 for the bare conjunct" (322), "the 6.5
   arm is vacuous" (323), "spanning stratum corollary" (325).
2. `algebraic-induction/genericity-and-count.tex` — node-code titles
   N7b-0/1/2/3 (304,351,389,439), superseded block N7b-4/M1/M2/M3 with
   route-history prose (476–660), `notes/Phase21b.md`+design-doc refs
   (480–481), "Rank-input rank polynomial; Phase 22i L4b-1" title (219).
3. `algebraic-induction/case-iii.tex` — highest density: "stratum-1 brick"
   (312,336,486,498), "the brick green here" (126), "gap3" (59), "(R1)
   reconciliation" title (874), `hsplitGP` in a statement (1441), "all
   inputs green" (9); the (good) chain-dispatch narrative (1344–1423) sits
   beside a dep-graph-traversal proof (1449–1514).
4. `rigidity-matrix.tex` — "L5a-i splice brick"-family titles
   (321,461,495,538,583), "superseded, route-2 leaf" title (495), "the
   `hub` bound" as pseudo-term (199,217), status-paragraph preamble
   (23–42), `notes/MolecularConjecture.md` ref (310).
5. `molecular-induction.tex` — "L4a/L4b-2 … producer" titles (1292,1326),
   "live to-do list / leaf-most red node" preamble (18–21),
   `notes/Phase20.md` ref (861), GP-in-title (1326).
6. `case-i.tex` — `hcSimple` in statement (601), "discharging the Case I
   premise (`hcontract`)" (612), `h65` (722), `hg`/`hcoord`/`hindep`
   prose (361–415), "(Phase 22k L8c-2)" (719).

Category counts corpus-wide: node codes in ~17 titles (HIGH); codename
nouns — producer ×77, motive ×43 (undefined; collides with the
algebraic-geometry term), brick ×35, stratum ×15; Lean hypothesis names in
prose ~25 spots (~6 inside statements); dep-graph status slang ~40 spots;
"This chapter is the Phase N dep-graph" preambles ×8 + inline sub-phase
codes ~25; `notes/`/`DESIGN.md` refs ×7. Total ~60–90 passages, ~70% in
files 1–6 above. Pin coverage context: `Molecular/` has ~1,215 decls vs
~143 pinned names in the eight molecular chapters (~12% — healthy
selectivity, but rules 6–7 above are what make the prose navigable
side-by-side with the Lean).
