# Phase 23-cleanup — blueprint readability rewrite + statement-surface audit (work log)

**Status:** in progress — **R1 is complete** (2026-07-03): the
headline-theorem prose rewrite (Prop 1.1, Theorem 5.5, Theorem 5.6, both
general-$d$ and $d=3$) plus the surrounding definition/lemma infrastructure
sweep (rank-hypothesis, genuine-hinge-realization, the base-producer family,
triangle/cycle normals, framework-with-graph) are both landed for
`panel-layer.tex`. R1 now **stops for owner review** of the rendered
chapter before R2 opens. The
`hfresh` vacuity finding (2026-07-02) had
paused R1: the fresh-edge-supply binder on the Theorem-5.5 spine +
`molecular_conjecture` was kernel-checked unsatisfiable, so the headline
statements were vacuous as stated. The repair arc (F1 reshape, F2
satisfiability + witness, F3 docs close-out) is **complete** (2026-07-02) —
see `notes/FreshEdgeSupply-design.md` for the compressed verdict; the
statements are satisfiable and checked non-vacuous. The seeded S2 item (the
`d = 3` producer duplication) is **also resolved** (2026-07-02, collapse) —
see the S2 entry below. `lake build` + `lake lint` + `blueprint/verify.sh` +
`blueprint/lint.sh` were green throughout. R0 (the style spec) is landed and
unaffected. Round manual: `CLEANUP.md`.
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

- [x] **R1 — `algebraic-induction/panel-layer.tex` (824). CALIBRATION.**
  **Complete (2026-07-03).** Headline theorems 5.5/5.6 + Prop 1.1 +
  Conjecture 1.2 nodes. Includes: split `thm:theorem-55-d3-instance` (5
  pins, 4 roles: spine / base helper / d=3 instance / spanning corollary)
  into 2–3 nodes (S1 and S2 both resolved — see the S entries below — so
  the prose rewrite pins against the final, collapsed decl set).
  **Headline-node family landed** (2026-07-03): `prop:rigidity-matrix-prop11`,
  `thm:theorem-55`, the `thm:theorem-55-d3-instance` split (main node +
  new `cor:theorem-55-d3-spanning`), `thm:theorem-55-6`, `thm:theorem-55-6-d3`
  are all at Target style; `thm:molecular-conjecture` +
  `rem:molecular-conjecture-nonvacuous` were already compliant (no edit
  needed). **Infrastructure sweep landed** (2026-07-03): the surrounding
  definition/lemma infrastructure the headline theorems `\uses` —
  `def:panel-support-extensor`, `def:panel-hinge-framework`,
  `def:rank-hypothesis`, `def:genuine-hinge-realization`,
  `lem:theorem-55-base(-producer{,-empty,-single,-parallel})`,
  `lem:theorem-55-triangle`, `lem:triangle-normals`, `lem:cycle-normals`,
  `def:framework-with-graph`, `lem:motions-mono-of-graph-le` — audited;
  of these only `def:rank-hypothesis`, `lem:theorem-55-base`, and the four
  `lem:theorem-55-base-producer*` nodes actually carried `motive`/
  `producer`/`arm`/`spine` language (plus one adjacent, non-listed node,
  `lem:extensor-pair-in-panel`, which had "brick"/"producer", and three
  stray preamble/proof spots outside any listed node — a stale
  "Phase-18"/"Phase~16" project-history mention and a "wires"/"routed
  through"/"op" word choice); the rest
  (`def:panel-support-extensor`, `def:panel-hinge-framework`,
  `lem:theorem-55-triangle`, `lem:triangle-normals`, `lem:cycle-normals`,
  `def:framework-with-graph`, `lem:motions-mono-of-graph-le`) were already
  Target-style and needed no edit. All four base-producer titles dropped
  "producer"/"arm" for "base region ... : \<case\>" naming; one stale
  reference (`\mathtt{theorem\_55\_generic}`, a decl that no longer exists)
  was corrected to plain prose. No Lean touched; `blueprint/verify.sh`/
  `blueprint/lint.sh` green. **R1 is now fully complete and stops for
  owner review of the rendered chapter before R2 opens** — see *Hand-off*.
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
Next concrete commit: **R1d — revise `panel-layer.tex` to the owner's
calibration-v2 verdict** (owner review of the rendered R1 draft,
2026-07-03; the new rules are codified as `blueprint/AUTHORING.md`
*Audience & vocabulary* rules 9–13 + the strict statement-purity
sharpening of rule 1 — read them all before editing). The review found
the draft "better, but not yet comprehensible to a typical
mathematician". Concrete defects to fix, chapter-wide (the whole of
`panel-layer.tex`, not just the headline family — and note the earlier
"thm:molecular-conjecture already at Target style" audit verdict was
WRONG, the owner review contradicts it):

1. **Statement purity** (rule 1 v2): `thm:molecular-conjecture`'s
   statement carries a "'Realized as…' means:" expansion + the ≥2-body
   essentiality discussion — move both out (the existing
   `rem:molecular-conjecture-nonvacuous` is a natural home for the
   essentiality half); `def:rank-hypothesis` carries the
   "V(G)-relative" methodological essay — move to a remark or section
   prose.
2. **KT prefix** (rule 9): "Theorem 4.9", "Proposition 1.1", "(6.1)"
   etc. → "KT Theorem 4.9", "KT Proposition 1.1", "KT eq. (6.1)"
   throughout.
3. **Formalization notes in prose, not Lean syntax** (rule 10):
   `def:rank-hypothesis`'s note carries `∃ Q, Q.graph = G ∧ …` and
   "B1"; `def:genuine-hinge-realization` uses `\mathtt{}` names as
   nouns mid-definition.
4. **Connective prose** (rule 11): subsection-opening orientation
   paragraphs + lead-ins for the load-bearing definitions.
5. **Multi-paragraph proofs** (rule 12): break the long single-
   paragraph proofs by argument movement.
6. **The fresh-edge-supply remark** (rule 13): one reader-facing
   remark where the supply first appears (near `thm:theorem-55`),
   explaining the ambient-label-type bookkeeping (no KT analogue;
   satisfied by any large-enough label type — `\cref` the F2
   satisfiability/witness nodes if pinned, else name the decls in the
   Formalization note); the per-node supply mentions then point at it.

Scope addition (owner-directed): the **chapter-overview preamble of
`algebraic-induction.tex`** renders on the same page and is "in rather
poor shape" — pull its rewrite forward from R7 into R1d (R7 keeps
`case-ii.tex` only). Gates: `blueprint/verify.sh` + `blueprint/lint.sh`
green. **R1d again ends at the owner checkpoint** — rendered-chapter
review before R2 opens; do NOT start R2. Once the review passes: R2's
seeded item is S3 (belongs to `case-iii.tex`). After P1/P2 close the
round: update this file's Status, flip the ROADMAP row, and Phase 24
opens per the standard protocol (`notes/MolecularConjecture.md`
*Opening the next phase*).

## Decisions made during this round
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
- **S2 landed (2026-07-02, Lean-only, ahead of the R1 prose commit):** the
  "duplication" A2/the orphan-decl sweep deferred was no longer proof
  *content* — `theorem_55_base_producer` / `case_cut_edge_realization{,_gp}`
  were already thin `k := 2` wrappers of grade-general `_gen` forms — only
  `theorem_55_minimalKDof_k` independently re-running the induction
  combinator a second time instead of delegating to
  `theorem_55_minimalKDof_gen (k := 2)`. Collapsed to a one-line corollary;
  deleted the 3 orphaned wrappers; re-pointed their 3 blueprint pins (4
  `\lean{}` sites across `panel-layer.tex` + `molecular-induction.tex`) at
  the `_gen` forms — a mechanical name swap, no prose rewrite needed
  (neither chapter's prose committed to `d = 3` for these nodes). Also
  fixed several already-stale `Theorem55.lean` doc-comments describing a
  pre-OD-7 "still d=3-pinned" picture, independent of this collapse.
  Incidental, left untouched (unpinned, so outside S2's scope; flagged for
  a future dead-code sweep): `case_I_dispatch` and
  `exists_extensor_in_two_panels` are analogous zero-caller d=3 `k := 2`
  wrappers. `lake build`/`lake lint`/`blueprint/verify.sh`/`blueprint/lint.sh`
  all green.
- **S2 follow-up (2026-07-02, Lean + docstring sweep):** S2 left three stale
  docstring references + one orphaned wrapper (`exists_extensor_in_two_panels`)
  that survived the collapse. Swept here: docstring references in
  `PanelLayer.lean`'s `exists_extensor_in_two_panels_grade` and
  `GenericityDevice.lean:1486` re-pointed from deleted `case_cut_edge_realization` /
  `case_cut_edge_realization_gp` forms to the live `_gen` forms; the orphaned
  `k = 2` wrapper deleted entirely (zero consumers, no blueprint pin). `lake
  build` warning-clean; `lake lint` green.
- **R1 headline-node prose rewrite (2026-07-03, docs-only):** rewrote
  `prop:rigidity-matrix-prop11`, `thm:theorem-55`, `thm:theorem-55-6`, and
  `thm:theorem-55-6-d3` to Target style (dropped `hgen`/phase-number/
  "stratum"/"spine" mentions, added a *Formalization note* paragraph per
  rule 1). Split `thm:theorem-55-d3-instance`'s 5 pins into the calibration
  sample's 2 nodes: the main node (kept the label; `theorem_55_all_k` +
  `theorem_55_d3`, the spine + d3-instance roles) and a new corollary
  `cor:theorem-55-d3-spanning` (`rankHypothesis_deficiency_of_theorem_55_d3`,
  the spanning-corollary role). The base-helper role
  (`theorem_55_base_producer_gen` + `Graph.not_simple_of_isMinimalKDof_of_ncard_two`)
  needed no new node — the former was already redundantly re-pinned here on
  top of its own `lem:theorem-55-base-producer` node (dropped the dup); the
  latter is a helper `lem:theorem-55-base-producer`'s own proof calls, so it
  moved there instead (with an inline findability mention). Also found and
  fixed a stale extra pin: `rankHypothesis_deficiency_of_theorem_55_d3` was
  *also* pinned on `thm:theorem-55-6-d3`, whose proof never calls it — pure
  pin-hygiene, not a Lean change. `thm:molecular-conjecture` +
  `rem:molecular-conjecture-nonvacuous` were audited and are already
  compliant. The surrounding definition/lemma infrastructure
  (`def:rank-hypothesis`, `def:genuine-hinge-realization`, the
  `lem:theorem-55-base*` family, etc.) still needs a pass — see *Hand-off*.
  `blueprint/verify.sh`/`blueprint/lint.sh` green (no Lean touched).
- **R1 infrastructure sweep, R1 complete (2026-07-03, docs-only):** audited
  all ten nodes the *Hand-off* above named; only `def:rank-hypothesis`
  (6 `motive` hits, plus a stale `\mathtt{theorem\_55\_generic}` reference
  to a decl that no longer exists — corrected to plain prose), the base
  case `lem:theorem-55-base` (3 `motive` hits, plus a "prior Lean
  required…" changelog aside dropped per `blueprint/CLAUDE.md` *Keep
  reshape/phase history out of the prose*), and the four
  `lem:theorem-55-base-producer*` nodes (title `producer`/`arm` language
  throughout, renamed to "base region (\|V(G)\| ≤ 2): \<case\>"; `motive`
  in each proof) needed edits; `def:panel-support-extensor`,
  `def:panel-hinge-framework`, `lem:theorem-55-triangle`,
  `lem:triangle-normals`, `lem:cycle-normals`, `def:framework-with-graph`,
  and `lem:motions-mono-of-graph-le` were already Target-style (verified
  against their actual Lean signatures; no edit). Also swept, since they
  sat directly adjacent and shared the same banned-term list: one
  non-listed node `lem:extensor-pair-in-panel` ("brick" + "producer"), and
  three stray non-node spots — a "Phase-18"/"Phase~16" project-history
  mention in two subsection preambles, and one each of "wires", "routed
  through", "op"/"this phase" (subsection titles/prose) — so the *rendered
  chapter* the owner reviews is clean end to end, not just the ten named
  nodes. No Lean changes were needed (every pinned decl's statement already
  matched the prose once the terminology was fixed — verified against the
  actual `PanelHinge.lean`/`Pinning.lean`/`Theorem55.lean`/
  `ReducibleVertex.lean` signatures per rule 8). `blueprint/verify.sh`/
  `blueprint/lint.sh` green. **This closes R1**; see *Hand-off* for the
  owner-review gate before R2.

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
