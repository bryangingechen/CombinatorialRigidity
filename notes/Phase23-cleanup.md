# Phase 23-cleanup — blueprint readability rewrite + statement-surface audit (work log)

**Status:** in progress — **R1h (the checkpoint-#6 fidelity commit)
LANDED 2026-07-04; R1 closed again.** The owner-adjudicated work list
(V1–V8 + J1–J22 + KEEP; rows 694–695, coordinator-arbitrated) landed in one
commit over `panel-layer.tex`. **B8 — the one item held for owner from
checkpoint #6 — resolved 2026-07-04**: `thm:theorem-55` restated at its
actual all-deficiency strength, `theorem_55_gen` (zero callers) deleted;
this closes the checkpoint-#6 arc in full. **The Conjecture-1.2 multigraph
question resolved 2026-07-04 (disclosure landed; analysis verified). R2 is
now fully LANDED (2026-07-05): slices 1, 2a, 2b, 2c, and 3 (the Claim 6.11
chain + the candidate-completion + the $D$-candidate disjunction + the
triangle floor + the general-$d$ chain dispatch/`lem:case-III`) close out
`case-iii.tex`'s readability rewrite. R3 (`genericity-and-count.tex`) is now
fully LANDED (2026-07-05), including the `genericity-and-count.tex` half of
D1 and its `blueprint/CLAUDE.md` supersession-rule revision. **R4
(`rigidity-matrix.tex`) is now fully LANDED (2026-07-05)**, including the
`rigidity-matrix.tex` half of D1 (the isolated superseded node retained
with a plain marker, per the revised rule) and the `sec:case-I` broken
`\ref` fix. **R5 (`molecular-induction.tex`) is now fully LANDED
(2026-07-05)**, including the `def:graph-operations` endpoint-selector
rename and the `forest_surgery_count`/`forest_surgery_split`
statement-fidelity fix. **R6 (`algebraic-induction/case-i.tex`) is now fully
LANDED (2026-07-05)**, including the repin of three producer nodes off
zero-caller `d=3` wrappers onto their live general-grade `_gen` forms (a
statement-surface audit finding) and the R1e `\uses`-refinement follow-up.
**R7 (`algebraic-induction/case-ii.tex`) is now fully LANDED (2026-07-05)**,
including a statement-fidelity fix (`lem:case-II-realization`'s "$k \ge 0$"
claim corrected to the Lean's actual `k > 0` hypothesis), a graph-identity
fix (`lem:case-II`'s framework sits on $G - v$, not $G_v^{ab}$, which is
*not* a subgraph of $G$ per `lem:splitoff-edge-substitution` itself), the
R1e `\uses`-refinement follow-up (`def:framework-with-graph` →
`def:framework-with-normal`/`lem:with-normal-preserves`, the actual
dependency for the panel-normal choice), and a newly-flagged liveness
finding (see *Hand-off*). **R8 (`meet.tex`) is now fully LANDED
(2026-07-05)**, including the standing duplicate-`\label` fix
(`lem:case-III-claim612-line-in-panel-union`: deleted the `case-iii.tex`
copy, kept the fuller `meet.tex` node) carried since R2 slice 2b, and a
new Formalization note disclosing that the node's bare-to-generic-upgrade
pin is general-purpose (also cited by `lem:cycle-realization`), not
Case-III-specific. **R9 (`deficiency.tex` + `extensor.tex`) is now fully
LANDED (2026-07-05)**, including a statement-fidelity fix
(`thm:def-eq-corank` was missing the `V(G) \ne \emptyset` hypothesis its
pins carry, matching its sibling `lem:rank-matroidMG-le`) and deleting
`extensor.tex`'s reader-facing forward-mode mechanics note. **R10
(`body-bar.tex` + `body-hinge.tex`) is now fully LANDED (2026-07-05,
docs-only, preamble/dep-graph framing only per its narrower scope)** —
dropped both chapters' "forward-mode authoritative dep-graph and lemma
index for Phase(s) N" openings and "Phase~N is complete ... (green)"
status paragraphs, and every other bare `Phase~N`/`ROADMAP.md` pointer in
the two files (7 total), with no Lean or node-statement change. **Next:
R11** (`rigidity-matroid.tex` + `pebble-game.tex`, the pre-molecular spot
pass) — see *Hand-off*. Checkpoints #5 (2026-07-04) and #6 passed.
The rendered R1g page passed owner review modulo one defect — "endpoint
selector" used in `cor:theorem-55-d3-spanning`'s proof and Formalization
note before the chapter introduced it — fixed the same day:
`def:panel-hinge-framework`'s statement now shows all three pinned
fields, its Formalization note explains the selector's totality
convention, and both `cor:theorem-55-d3-spanning` uses are anchored back
to the definition. The 11 checkpoint-#4 owner notes were grounded by a
read-only recon (log row 688) and all dispositions settled with the owner
(verdicts in *Hand-off* below). Landed: (i) calibration-v5
**consolidation** of AUTHORING.md (17 rules + residue → six principles
A–F) — **landed 2026-07-03**; (ii) the 9(a) Lean collapse of
`rankHypothesis_of_theorem_55_d3` — **landed 2026-07-04**; (iii) the
R1g revision pass over `panel-layer.tex` + the Formalization-note
environment — **landed 2026-07-04**; (iv) the checkpoint-#5 follow-up
(five owner-adjudicated edits) — **landed 2026-07-04**; (v) R1h (the
checkpoint-#6 fidelity commit) — **landed 2026-07-04**; (vi) the
Conjecture-1.2 multigraph disclosure — **landed 2026-07-04**; (vii) R2 slice 1
(the Claim 6.11 chain of `case-iii.tex`) — **landed 2026-07-04**; (viii) R2 slice 2a
(the candidate-completion of `case-iii.tex`) — **landed 2026-07-04**; (ix) R2 slice 2b
(the $D$-candidate disjunction of `case-iii.tex`) — **landed 2026-07-04**; (x) R2 slice 2c
(the triangle floor of `case-iii.tex`) — **landed 2026-07-04**; (xi) R2 slice 3
(the general-$d$ chain dispatch + `lem:case-III` of `case-iii.tex`, plus the S3
`chainData_dispatch`/`chainData_fire_discriminator` node promotion) —
**landed 2026-07-05, closing R2**. **Next: R3
(`algebraic-induction/genericity-and-count.tex`).**
Landed so far (details in *Decisions made*): R0 (style spec); the `hfresh`
vacuity repair arc F1–F3 (2026-07-02 — the supply binder was
kernel-checked unsatisfiable, repaired to the minimality-conditioned form
+ satisfiability lemmas + the `Nonvacuity.lean` witness); S2 (the `d = 3`
producer-spine collapse); R1 through R1f (the calibration chapter at the
owner's v1 → v2 → v3 → v4 rules); the calibration-v5 A–F consolidation of
AUTHORING.md (2026-07-03); the owner-directed E1–E3 consumer-surface
ergonomics arc (2026-07-03 — headline decls take `3 ≤ n` + an explicit
label-headroom bound, `k := n − 1`, `theorem_55_all_k` merged away;
`notes/FreshEdgeSupply-design.md` §E); and 9(a) (2026-07-04 — the
`rankHypothesis_of_theorem_55_d3` collapse to a corollary of
`rankHypothesis_of_theorem_55_gen (n := 3)`). All gates green throughout.
Round manual: `CLEANUP.md`.
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

Codified in `blueprint/AUTHORING.md` *Audience & vocabulary* — the six
A–F principles (calibration v5; task R0 first lifted the numbered *Target
style* rules, since consolidated), the audience test, and the terminology
dictionary all live there now; read it before starting any R-task below.
The `intro.tex` one-paragraph dep-graph-convention note (principle F)
landed in the same commit (`chapter/intro.tex` *Reading this blueprint*).

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

- [x] **R1 — `algebraic-induction/panel-layer.tex`. CALIBRATION. COMPLETE.**
  Landed in eight passes — headline-node family, infrastructure sweep,
  R1d (calibration v2), R1e (calibration v3: register, pin budgets,
  Formalization-note placement), R1f (the rule-17 statement-surgery
  pass), R1g (the checkpoint-#4 11-item pass + the Formalization-note
  environment, landed 2026-07-04), and the checkpoint-#5 follow-up (the
  `def:panel-hinge-framework` endpoint-selector statement fix, landed
  2026-07-04), plus R1h (the checkpoint-#6 fidelity commit, V1–V8 + J1–J22 +
  KEEP, landed 2026-07-04). Checkpoints #5 and #6 both passed 2026-07-04.
- [x] **R2 — `algebraic-induction/case-iii.tex` (1444). COMPLETE.** Largest; slice split.
  **Slice 1 — the Claim 6.11 chain (subsection opening + 8 nodes through
  `lem:case-III-claim-6-11`) LANDED 2026-07-04** (audit: all 8 pins at strength, no
  Lean change; pure prose rewrite). Slice 2 (candidate-completion + Claim 6.12 + `d=3`
  assembly) proved too large for one sitting and was **sub-split**: **slice 2a — the
  candidate-completion subsubsection (opening + 9 nodes `lem:case-III-vanish-off-column`
  … `lem:case-III-candidate-row`, KT eqs. (6.24)–(6.29)) LANDED 2026-07-04** (audit: all
  9 pins at strength, no Lean change; pure prose rewrite). **Slice 2b — the $D$-candidate
  disjunction (KT eqs. (6.30)–(6.45)), the subsubsection "The $D$-candidate disjunction"
  through `lem:case-III-claim612` (21 nodes: the 14 `lem:case-III-claim612-*` nodes plus
  the 3 `lem:splitOff-*-relabel` transport nodes) LANDED 2026-07-04** (audit: all 21 pins
  at strength, no Lean change; pure prose rewrite; fixed the empty `\uses{}` at
  `lem:splitOff-isLink-relabel` → `def:graph-operations`). **Found in the audit (flagged,
  not fixed — cross-chapter, out of this slice's scope): `lem:case-III-claim612-line-in-panel-union`
  is a duplicate `\label` — defined once here (2 pins) and again in `meet.tex:239` (11
  pins, the fuller Phase-22f assembly) — a pre-existing plastex "multiply defined
  reference" warning (confirmed present identically on unmodified `master` via
  `git stash`, so not introduced by this commit); likely the case-iii.tex copy is a stale
  pre-22f leaf that should have been deleted/repointed when 22f discharged it into
  `meet.tex` and never was. Resolve when R8 (`meet.tex`) opens, or as a standalone fix:
  probably delete the case-iii.tex copy and re-point its one caller
  (`lem:case-III-claim612`) at the `meet.tex` node.** **Slice 2c — the triangle
  floor + the two triangle nodes (`lem:triangle-third-edge`/`lem:triangle-realization`),
  stopping before `lem:case-III`, LANDED 2026-07-04** (audit: both pins at strength;
  fixed the empty `\uses{}` at `lem:triangle-third-edge` → `def:k-dof` on the
  statement, plus a second gap found in the audit — the proof invoked the
  rank-formula-at-deficiency-0 fact with no `\uses` at all — closed with
  `\uses{thm:def-eq-corank}` on the proof). **Slice 3 — the general-`d` chain
  dispatch + `lem:case-III` LANDED 2026-07-05** (audit: `chainData_dispatch`'s
  signature already clean, pinned verbatim; `chainData_fire_discriminator`'s
  fat existential is internal-infra-shaped — see S3 below — no Lean change on
  either; pure prose + two new nodes). Delivered the seeded S3 promotion (two
  new nodes, `lem:case-III-chain-discriminator` /
  `lem:case-III-chain-dispatch`) and the BlueprintExposition general-`d`
  chain-dispatch seed (the KT §6.4.1→§6.4.2 two-stage lift framing). The old
  three-item narrative (one base / the `±r` carry / the discriminator) is now
  the backbone of the two new nodes' proofs; `lem:case-III`'s own proof
  shortened to cite the dispatch node for the $|V|\ge 4$ step instead of
  re-narrating the mechanism, dropping ~10 mechanism-level `\uses` targets
  down to the two chain nodes. **Found in the audit (flagged, not fixed —
  out of this slice's scope):** `PanelHingeFramework.case_III_candidate_dispatch`
  (the old $d=3$-only three-panel `fin_cases` dispatch, `Realization.lean:324`)
  has **zero callers** — `case_III_realization` now routes through the general
  `chainData_dispatch` for every grade including $d=3$ (a one-line
  specialization of `case_III_realization_all_k`) — so the chain
  `case_III_candidate_dispatch` → `exists_complementIso_ne_zero_of_homogeneousIncidence`
  → `case_III_claim612` is orphaned, and the five blueprint nodes pinned to it
  (`lem:case-III-claim612`, `-p2-placement`, `-p3-placement`, `-eq644`, and
  possibly `lem:case-III-candidate-row`) may be describing dead code as if
  live. Not resolved here (a correctness/liveness audit of that whole family
  is its own task, orthogonal to this slice's prose-register scope, and risks
  touching R2 slices 1/2a/2b's just-landed work); flagged for a future
  dead-code sweep alongside the precedent `case_I_dispatch` finding (S2
  above). **R2 is now fully complete** (slices 1, 2a, 2b, 2c, 3).
- [x] **R3 — `algebraic-induction/genericity-and-count.tex` (670 → 387
  lines). COMPLETE (2026-07-05).** Audit: all 13 pinned Lean signatures
  (`GenericityDevice.lean`, `Pinning.lean`, `CaseII.lean`,
  `RigidityMatrix/Basic.lean`) already at the strength the blueprint states —
  no Lean change. Dropped the N7b-\*/M\* node-code titles and all process
  vocabulary (`brick`, `motive`, `producer`, `honest`/`honesty`, Lean
  hypothesis names, raw Lean identifiers in math mode) from titles,
  statements, and proofs; the `notes/Phase21b.md` / `notes/Phase22-realization-design.md`
  refs sat inside the D1 dead block and were removed with it. Delivered D1's
  `genericity-and-count.tex` half: the four dead lemmas (row-side N7b-4,
  motion-side M1/M2/M3) plus their ~200-line route-history subsubsection
  collapsed to two short connective paragraphs (git is the audit trail) —
  **with the `blueprint/CLAUDE.md` retain-with-marker rule revised in the
  same commit**: retain-with-marker stays the default for an *isolated* dead
  node, but a whole dead *route* (several struck nodes plus route-history
  prose) now defaults to collapse. `verify.sh`/`lint.sh` green; the two
  pre-existing warnings (`sec:case-I` undefined in `rigidity-matrix.tex`, the
  `lem:case-III-claim612-line-in-panel-union` duplicate label, both flagged
  in R2) confirmed unchanged via `git stash`. D1's `rigidity-matrix.tex` half
  still lands with R4.
- [x] **R4 — `rigidity-matrix.tex` (616 → 618 lines). COMPLETE
  (2026-07-05).** Audit: all ~35 pinned Lean signatures across
  `RigidityMatrix/{Basic,Bricks}.lean` and
  `AlgebraicInduction/{CaseI,Coupling}.lean` already at the strength the
  blueprint states, no Lean change — except `def:dof-generic`, confirmed
  correctly red (no `\leanok`): its "generic realization" conjunct
  (max-rank over all realizations) has no Lean counterpart, only
  `IsInfinitesimallyRigid` is pinned, so the missing `\leanok` was already
  honest, not an oversight. Dropped the "L5a-i splice brick"-family node-code
  titles, the "superseded, route-2 leaf" title, and every `brick`/`producer`/
  `stratum`/`honest`/`route`/`carries`(-as-verb) occurrence; replaced "the
  `hub` bound" with the plain codimension-bound statement it names (per the
  terminology dictionary); deleted the "Status." preamble paragraph
  (principle F), folding its real content (the Prop-1.1 reconciliation
  needing the Phase-19 matroidal bridge + the algebraic induction) into a
  half-page chapter roadmap; dropped the `notes/MolecularConjecture.md` risk-
  register ref from `lem:rank-rotation-semicont`'s proof. Fixed the
  pre-existing broken `\S\ref{sec:case-I}` (no matching `\label` anywhere in
  the corpus) to `\cref{sec:molecular-algebraic-induction-caseI}`. Added a new
  unlabeled `\subsection{Block-rank-addition lemmas for the case analyses}`
  (principle F) and reordered `lem:block-rank-cut` (KT Lemma 6.1) to open it,
  ahead of Lemma 6.2/6.8/6.10 — restores KT's own numbering order; verified
  via a `\label`/`\lean`/`\leanok`/`\uses` line-diff against HEAD that this
  reorder is the *only* structural change (every other such line byte-
  identical, same order). Trimmed `def:rigidity-matrix`'s statement to the
  actual definition ($R(G,p)$, $Z(G,p)$) and moved the bundled row-
  independence build-up (13 pins on one node) into two unlabeled connective
  paragraphs after the environment — same pins, same label, principle-B
  deletion test only; a full node-split was not attempted (would touch
  `\uses` edges in not-yet-cleaned R5/R6 chapters) and is flagged below.
  D1's `rigidity-matrix.tex` half: the one superseded node
  (`lem:rank-polynomial-IH-relabel`) is the corpus's *only* struck node
  outside `matroid-union.tex` (confirmed by grep) — an isolated dead node,
  not a dead route, so it stays retained-with-marker per the revised rule,
  with the title's internal codes dropped and the route-history prose
  trimmed to two sentences. **Found in the audit (flagged, not fixed):**
  two new `\Cref{a,b,c}`/`\cref{a,b}` multi-label crefs I drafted rendered
  as literal "??" in the plastex output (a real, causally-confirmed,
  project-wide plastex/cleveref limitation — dozens of pre-existing "??"
  instances survive untouched in `molecular.tex`, `molecular-induction.tex`,
  and even the already-R2-cleaned `case-iii.tex`); rewrote mine to the
  corpus's established `\cref{a}, \cref{b}, and \cref{c}` idiom, but the
  pre-existing corpus-wide instances are unfixed — a candidate `lint.sh`
  addition (grep for `[cC]ref\{[^}]*,`) for a future session.
  `def:rigidity-matrix`'s 13-pin bundle is a standing over-pin candidate for
  a future node-split pass (R1e precedent), not attempted here for the same
  cross-chapter-`\uses` risk. `verify.sh`/`lint.sh` green; the `sec:case-I`
  fix confirmed by rendered-HTML diff (was the literal broken "see §??"
  before the fix, resolves to "Case I: a proper rigid subgraph" after); the
  one pre-existing warning flagged in R2 (the
  `lem:case-III-claim612-line-in-panel-union` duplicate label, out of this
  file) is unaffected, reconfirmed unchanged via `git stash` diff of the
  full plastex warning set.
- [x] **R5 — `molecular-induction.tex` (1587 → 1615). COMPLETE
  (2026-07-05).** Audit: all 58 pinned Lean signatures across
  `Molecular/Induction/{Operations,Contraction,ReducibleVertex,
  SplitOffDeficiency,ForestSurgery/*}.lean`, `Molecular/Deficiency.lean`,
  and `Molecular/AlgebraicInduction/Theorem55.lean` read against the
  blueprint statements; two Lean-faithful but oversold restatements found
  and fixed (docs-only, no Lean change): `lem:forest-surgery-count` and
  `lem:forest-surgery-split` both claimed their packing/rerouted set was
  "a base $I$ of $M(\tilde G)$", but neither pinned declaration
  (`Graph.forest_surgery_count`, `Graph.forest_surgery_split`) hypothesizes
  a base — restated at the pin's actual generality (an independent/
  arbitrary fiber set with the stated packing), moving the
  base-of-$M(\tilde G)$ framing into the proof of `lem:forest-surgery-split`
  where it is the genuine proof strategy. Rewrite: dropped the "Phase~20"
  self-description, the "leaf-most red node / live to-do list" forward-mode
  Status paragraph (replaced with a proper half-page KT~§3–§4 roadmap
  matching the `algebraic-induction.tex` template), "the fourth stratum",
  the `notes/Phase20.md` self-correction reference in `rem:kt-lemma-44`
  (kept the math: the naive rank-monotonicity argument only gives a
  weaker bound; the isolated case forces the full crossing-drop), all
  "green ... infrastructure" dep-graph-status language (4 instances),
  "route"/"critical path" throughout (replaced with "argument" /
  "does not enter the proof of Theorem 4.9"), "arm" → "branch" (the
  full-fiber/partial-fiber case split, ~10 instances, matching the
  corpus's established term), and the "L4a bare-conjunct producer"/"L4b-2
  GP-conjunct producer" titles (→ "Nondegenerate-hinge realization at a
  cut edge"/"Generic full-rank realization at a cut edge", both "; KT
  Lemma 6.1", dropping "producer" and the internal L4a/L4b-2/GP codes;
  "genuine-hinge panel realization" in their statements → the established
  "nondegenerate-hinge panel realization"). Renamed `def:graph-operations`'s
  graph-level "endpoint selector" → "canonical endpoint choice" (the
  checkpoint-#5 disambiguation: it is `Graph.endsOf`, a different object
  from the panel-hinge framework's `ends` field, which keeps "endpoint
  selector" everywhere else in the corpus). Marked `lem:chain-data-of-noRigid`
  ("Chain data; G4a-ii" → "A four-vertex chain from an adjacent degree-2
  pair ($d = 3$; superseded)") retained-with-marker per the D1 rule: it
  has zero `\uses`-consumers anywhere in the corpus (confirmed by grep)
  since the Phase-23h general-$d$ producer-site rewire, an isolated dead
  node rather than a dead route, so retained rather than collapsed; dropped
  its "Phase~23h"/"producer-site rewire"/raw-Lean-identifier disclosure in
  favor of the plain math fact. Moved ~15 role/positioning trailing
  sentences ("This is the engine of Case~I...", "This is the counting half
  of...") out of statement blocks into `\medskip\noindent` connective
  prose after the proof, per principle B; fixed one pre-existing-style
  multi-`\cref{a,b}` I drafted that rendered as literal "??" (the
  corpus-wide plastex/cleveref limitation flagged in R4) to the
  established `\cref{a} and \cref{b}` idiom — the two genuinely
  pre-existing "??" instances elsewhere in this file (confirmed unchanged
  by `git diff`) are untouched, matching R4's precedent.
  `verify.sh`/`lint.sh` green.
- [x] **R6 — `algebraic-induction/case-i.tex` (737 → 630 lines). COMPLETE
  (2026-07-05).** Audit first: read all ~30 pinned Lean signatures across
  `PanelHinge.lean`, `Pinning.lean`, `PanelLayer.lean`, `GenericityDevice.lean`,
  `Contraction.lean`, `CaseI.lean`, `RigidityMatrix/Basic.lean`, and
  `CaseIII/Arms.lean` — found a real liveness/fidelity gap, fixed docs-only
  (no Lean change; the general-grade `_gen` forms already existed and were
  fully proven): `lem:case-I-realization`, `lem:case-I-realization-nonsimple`,
  and `lem:case-I-dispatch` were pinned to `case_I_realization_all_k`,
  `case_I_realization_nonsimple`, and `case_I_realization_h65` respectively —
  all three `d=3`-only (`k := 2`) wrappers with **zero proof-term callers**
  (confirmed by grep; only doc-comment mentions), since `thm:theorem-55`
  (already `\leanok`, stated at every dimension `n ≥ 3`) actually routes its
  Case-I carry through `case_I_hcontract_gen`, which calls the general-grade
  `case_I_realization_all_k_gen`/`case_I_realization_nonsimple_gen`/
  `case_I_realization_h65_gen`/`case_I_dispatch_gen` chain (Phase 23b OD-7
  tail) — the blueprint was silently describing dead code as live, the same
  pattern as the `case_I_candidate_dispatch`/`case_III_candidate_dispatch`
  precedents (S2, R2 slice 3). Repinned all three to the live `_gen` forms
  (a pure re-pin — no Lean change, since the general forms were already
  proven; each restated at its pin's exact strength, fixing one further
  fidelity bug in the same pass: `lem:case-I-realization`'s conclusion had
  silently dropped the `-k` deficiency term, oversized to `D(|V(G)|-1)`
  instead of `D(|V(G)|-1)-k`, contradicting its own "(all-$k$)" title).
  Split the 5-pin `lem:pinned-motions-on-rank-bound` bundle (3 distinct
  claims in one statement, over the D pin-budget) into the kept label (now
  the single lower-bound claim actually consumed by `lem:case-I`) plus a new
  node `lem:pinned-motions-on-rigid-iff` for the rigid-block nullity iff and
  its converse (confirmed self-contained to this file, no cross-chapter
  `\uses`). Minted `lem:case-I-realization-h65` (KT Lemma~6.5/Claim~6.6, the
  vertex-removal arm) as its own node, pinned to `case_I_realization_h65_gen`
  — previously folded as prose-only inside `lem:case-I-dispatch`'s statement
  with no `\leanok` pin of its own covering that branch; `lem:case-I-dispatch`
  (repinned to `case_I_dispatch_gen`) is now the thin three-way combinator
  (KT Lemma 6.2 non-simple / 6.3 simple-contraction / 6.5 vertex-removal),
  restated to include the KT-6.2 non-simple-$G$ branch it had previously
  omitted entirely. The R1e follow-up: refined the coarse `def:panel-hinge-
  framework` `\uses` edge on `lem:case-I-splice-seed` to `def:framework-with-
  graph` (the statement is phrased at the `BodyHingeFramework`/`withGraph`
  level, not the panel level) and added the missing `def:rank-hypothesis`/
  `def:genuine-hinge-realization` edges on the three producer nodes (the
  "generic realization"/"nondegenerate-hinge realization" terms their
  conclusions actually use were previously un-anchored). Dropped
  `hcSimple`/`hcontract`/`h65`/`hg`/`hcoord`/`hindep` and all raw Lean
  identifiers from statements and prose (the task's named target), plus
  `brick`/`motive`/`producer`/`arm`/"GREEN-modulo"/Phase-number/internal-code
  vocabulary (`L5a-i`, `L8c-2`, `U1`–`U4`, `OD-7`, …) throughout; moved
  role/positioning trailers out of statement blocks into connective prose
  (KT Claim~6.4's three-bullet Lean-internal proof narrative rewritten as
  three prose paragraphs, keeping the full mathematical content per the
  crux carve-out). Added a subsection-opening orienting paragraph (principle
  F). `verify.sh`/`lint.sh` green; confirmed via `git stash` that the
  plastex warning set (the pre-existing `crefname`/`hrulefill`/mathtools
  warnings) is byte-identical before and after, and that no new `??` appear
  in the rendered Case~I section.
- [x] **R7 — `algebraic-induction/case-ii.tex` (195 → 173). COMPLETE
  (2026-07-05).** Audit first: read all 10 pinned Lean signatures across
  `AlgebraicInduction/{Pinning,PanelHinge,CaseII}.lean` — found two real
  fidelity gaps, fixed docs-only (no Lean change): (i)
  `lem:case-II-realization`'s title/statement claimed "all $k \ge 0$" but
  its pin `case_II_realization_all_k` has hypothesis `hc : 0 < c` — the
  Lean's `_all_k` suffix means "general ambient dimension", not "every
  deficiency" (KT Lemma 6.8 is the $k > 0$ half; $k = 0$ is Case III);
  restated to "$k > 0$", matching `lem:case-II`'s own hypothesis and
  `thm:theorem-55`'s proof text ("a positive-deficiency splitting-off is
  realized by Case~II"). (ii) `lem:case-II`'s statement described its
  framework `P` as living on the splitting-off graph $G_v^{ab}$, but the
  pinned `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`
  requires `P.graph ≤ G` — impossible for $G_v^{ab}$, which
  `lem:splitoff-edge-substitution` (in the *same file*) states is *not* a
  subgraph of $G$ (it carries the fresh short-circuit edge $e_0 \notin
  E(G)$); the framework actually sits on the common subgraph $G - v$,
  restated accordingly. Delivered the R1e `\uses`-refinement follow-up for
  this file: `lem:case-II-rank-lift`'s "choosing $v$'s panel normal ...
  does not disturb the null space" step was `\uses`d to the coarse
  `def:framework-with-graph` (the *graph*-swap operation) when the actual
  dependency, traced through `case_II_realization_all_k`'s Lean body, is
  the *normal*-swap invariance `def:framework-with-normal`/
  `lem:with-normal-preserves` — refined throughout. Slimmed
  `lem:case-II-rank-lift`'s 8-pin bundle (4 facts × body-hinge/panel-hinge
  levels, over the principle-D pin budget) to the 2 pins witnessing its
  now-singular statement claim, moving the $\le$/$=$/`hnew`-reduction
  facts' narrative to `lem:case-II` (their actual consumer) and leaving
  the two now-unpinned pairs as proof-internal helpers (principle D's
  "leave helpers unpinned"), a same-file, cross-file-`\uses`-free
  restructuring (confirmed via grep: neither `lem:case-II-rank-lift` nor
  `lem:splitoff-edge-substitution` is referenced outside this file). Dropped
  `brick`/`motive`/`producer`/`W-suite`/two `carries`-as-verb instances and
  fixed three raw-Lean-notation leaks (`\mathrm{graph}`, `.withGraph`,
  `\mathrm{isInfinitesimallyRigidOn\_insert\_iff}`). Added a
  subsection-opening orienting paragraph (principle F).
  **Found in the audit (flagged, not fixed):** `lem:case-II`'s two pinned
  decls (`isInfinitesimallyRigidOn_insert_iff`,
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`,
  `Pinning.lean`/`PanelHinge.lean`) have **zero proof-term callers**
  anywhere in the codebase (confirmed by grep) — the live producer
  `case_II_realization_all_k` builds the extended framework directly
  (row-family union + rank-polynomial genericity lift) rather than routing
  through this bridge, per its own doc-comment ("no shared brick fits
  here"). Both decls are real, proven, and correctly `\leanok` (no honesty
  violation), but the node they back is orphaned infrastructure — the same
  liveness pattern S2/R2-slice-3/R6 found, but a "superseded design
  attempt" rather than a "d=3-only wrapper with a live `_gen` sibling", so
  no straightforward re-pin target exists. Left as-is (re-pinning or
  deleting `lem:case-II`'s current pins is a larger, `lem:case-II`-wide
  change — the node is `\uses`'d from 9 other files); flagged for a future
  dead-code sweep alongside the `case_I_dispatch`/`case_I_candidate_dispatch`/
  `case_III_candidate_dispatch` precedents. `verify.sh`/`lint.sh` green; the
  known pre-existing warning set (11 `??` instances on this rendered page,
  `crefname`/`hrulefill`/mathtools) confirmed byte-identical via `git stash`.
- [x] **R8 — `meet.tex` (342 → 296 lines). COMPLETE (2026-07-05).** Audit
  first: read all 12 pinned Lean signatures in `Molecular/Meet.lean`
  (top-power/pairing-dual/complement isos, the wedge-pairing dictionary
  chain) plus the 9-decl bundle
  `lem:case-III-claim612-line-in-panel-union` pins across
  `Molecular/AlgebraicInduction/{PanelLayer,CaseI}.lean`,
  `Molecular/RigidityMatrix/Claim612.lean`, and
  `Molecular/AlgebraicInduction/CaseIII/{Candidate,Arms}.lean` — every
  signature already at the strength the blueprint states, no Lean change.
  Dropped the "Phase~21a" self-description, the "Status." preamble
  paragraph (folded into a half-page roadmap, principle F), the
  "N3b assembly"/"assembly N3b-1" node-code titles, "(step (i))"/"(step
  (ii))" title codes (kept as plain ordinal prose), and both `motive`
  occurrences (rewritten as the plain "generic realization" claim already
  used elsewhere in the corpus). Moved five statement-block role/trailer
  sentences ("this is the genuinely new core of the chapter", "reused by
  ... Phase~25", "on which the proportionality ... rests", etc.) out of
  statement blocks per principle B; the biggest was
  `lem:case-III-claim612-line-in-panel-union`'s statement, which had
  ~50 lines of $d=3$ Case-III producer/candidate/row-space-criterion proof
  narrative stuffed into the statement block (with `panelSupportExtensor`
  and other panel-layer.tex terms used before that chapter is reached) —
  trimmed the statement to the honest KT eq.~(6.45) core claim alone,
  moved the genuine proof content to the environment's own proof, and
  added one Formalization note disclosing the bundle's other 9 pins by
  role (**flagging, not splitting**, per the R2-slice-3 precedent for an
  over-large existential: 12 pins on one node is a standing over-pin
  candidate for a future split). The note also fixes a real fidelity gap
  the audit found: one of the 9 pins
  (`hasGenericFullRankRealization_of_rigidOn_ofNormals`, the general
  bare-to-generic upgrade, KT Lemma~5.2) is *not* specific to this node's
  point-join/panel-meet duality at all — it is independently cited by
  `lem:cycle-realization` (`case-i.tex`) for an unrelated upgrade, so a
  reader following that citation into this node would not find what they
  came for; the note discloses the shared citation inline instead of
  deferring the mismatch. Added a one-clause forward gloss the first time
  `meet.tex` uses "panel"/"$\Pi(u)$" concretely (pointing at
  `sec:molecular-algebraic-induction`, which formally defines it later),
  fixing a backward-anchoring gap (principle E) that predates this pass.
  **Delivered the standing duplicate-`\label` fix** flagged since R2
  slice 2b: `lem:case-III-claim612-line-in-panel-union` was defined twice
  (`case-iii.tex`, 2 pins; `meet.tex`, the fuller 11-pin — now 12-pin —
  Phase-22f assembly); verified the `case-iii.tex` copy's 2 pins are a
  strict subset of `meet.tex`'s before deleting it (nothing lost), and
  replaced the deleted environment with a one-paragraph connective
  pointer at the `meet.tex` node. The plastex "multiply defined
  reference" warning is confirmed gone (`inv web` output has zero
  `multiply`/`duplicate` hits, vs. present on unmodified `master`).
  `verify.sh`/`lint.sh` green throughout.
- [x] **R9 — `deficiency.tex` (489 → 486) + `extensor.tex` (219 → 207).
  COMPLETE (2026-07-05).** Audit: all ~30 pinned Lean signatures across
  `Molecular/Deficiency.lean` and `Molecular/Extensor.lean` already at
  the strength the blueprint states — no Lean change, and no
  zero-caller/dead-wrapper liveness pattern found (unlike R2/R6/R7's
  `d=3`-only-wrapper finds). One small fidelity fix landed docs-only:
  `thm:def-eq-corank`'s statement was missing the `V(G) \ne \emptyset`
  hypothesis its pinned `Graph.rank_add_deficiency_eq` family actually
  carries (its sibling `lem:rank-matroidMG-le` states it, this node
  didn't) — added the clause to match. Rewrote both preambles to Target
  style: dropped `deficiency.tex`'s "Phase~19"/"third stratum" framing
  and its standalone `Status.` paragraph (folded its KT-Lemma-number
  content into a proper half-page roadmap naming the three subsections
  in order, principle F), fixed a self-referencing `\cref` bug in
  `def:k-dof` (pointed at its own section instead of
  `sec:molecular-induction`/`thm:minimal-kdof-reduction`), replaced
  "the honest rank form" with "the rank form" (twice) and "Phase~16"/
  "Phase~21+" with `\cref{sec:body-hinge}`/
  `\cref{sec:molecular-algebraic-induction}`, and dropped a meta
  aside ("the first formalization step of Phase~19 confirms...") from
  `def:matroid-MG`'s proof. **Deleted `extensor.tex`'s reader-facing
  forward-mode mechanics note** (the "Forward-mode chapter" paragraph
  citing `\uses{}`/green nodes; that convention now lives solely in
  `intro.tex` per principle F) and its "Phases~17--26"/"five-strata
  architecture"/`notes/MolecularConjecture.md` opening, replacing both
  chapters' openings with roadmap paragraphs naming what is proved, in
  what order, with section `\cref`s (matching the `rigidity-matrix.tex`/
  `molecular-induction.tex` template). Dropped "the genuine panel-hinge
  rigidity matrix" → "the panel-hinge rigidity matrix" (not a
  hinge/realization use of "genuine", but matches `rigidity-matrix.tex`'s
  own register, which never claims that adjective for itself).
  `verify.sh`/`lint.sh` green; `checkdecls` confirms the one statement
  edit didn't touch any `\lean{...}` pin.
- [x] **R10 — `body-bar.tex` (642 → 631) + `body-hinge.tex` (148 → 143).
  COMPLETE (2026-07-05).** Scoped narrower than R2–R9 per the task list
  (preamble/dep-graph framing only, connective prose only — no node
  statement touched, so no statement-surface audit of the pinned Lean
  signatures was needed; no `\lean{}`/`\uses`/`\label` changed). Dropped
  both chapters' opening
  "This chapter is the forward-mode authoritative dep-graph and lemma
  index for Phase(s) N ..." paragraph and trailing "Phase~N is complete:
  every node below is formalized (green) ..." status paragraph (the
  pattern the hand-off flagged by grep), replacing each with a plain
  "this chapter proves ..." opening naming the target theorem directly
  (matching the pre-molecular backfill-mode chapters' style, since both
  phases are long since complete). `body-bar.tex`'s three-ingredient
  proof-route paragraph needed no phase language and is untouched.
  Dropped every remaining bare `Phase~N`/`ROADMAP.md` pointer in the two
  files: `body-bar.tex`'s "(Phase~12)" matroid-union pointer (twice, one
  of which also duplicated `matroid-union.tex`'s own Provenance
  paragraph — trimmed to the bare `\cref`), "fresh to Phase~13" (→ "fresh
  to this chapter"), and the twice-repeated "deferred out of Phase~15
  (re-assessed when the body-hinge phase opens; see `ROADMAP.md` §15)"
  aside on Whiteley's irreducible-variety lift (→ "is not pursued here",
  keeping the math content — the lift stays genuinely unaddressed, per
  `notes/Phase16.md`'s "deferred ... now to the molecular-conjecture
  phase if ever pursued" — without the internal phase/file pointer);
  `body-hinge.tex`'s matching "(Phase~15)" cross-reference and its own
  "deferred out of Phase~15 ... re-assessed here" aside got the same
  treatment. `verify.sh`/`lint.sh` green; confirmed via `git stash` that
  the plastex warning set (the pre-existing `hrulefill`/`providecommand`
  render-default warnings) is byte-identical before and after.
- [x] **R11 — pre-molecular spot pass. COMPLETE** (2026-07-05, two
  commits): the `pebble-game.tex` `hD`-in-display mentions reworded and
  one `rigidity-matroid.tex` `DESIGN.md` ref retargeted (`e7874d06`);
  the coordinator follow-up dropped both reader-facing "see `DESIGN.md`"
  pointers outright (the R4/R5 treatment of repo-internal doc refs),
  keeping the surrounding content.

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
- [x] **S3 — promote the dispatch/discriminator pair. RESOLVED (R2 slice 3,
  2026-07-05).** `chainData_dispatch` / `chainData_fire_discriminator`
  (`Molecular/AlgebraicInduction/CaseIII/Realization.lean`) are now pinned by
  `lem:case-III-chain-dispatch` / `lem:case-III-chain-discriminator`
  (`case-iii.tex`). `chainData_dispatch`'s signature was already clean (pinned
  verbatim, no Lean change); `chainData_fire_discriminator`'s conclusion is a
  fat existential mixing the genuine KT eq.-(6.57)–(6.67) content (the shared
  redundancy + the matched-candidate gate) with internal bookkeeping (a
  link-recording selector, the redundancy's hinge-functional decomposition, an
  independent bottom-row family) threaded only to its two sibling dispatch
  branches — a full-fidelity restate would have meant slimming that interface
  across several call sites, judged substantial and out of this slice's scope
  (flagged, not attempted). The node states the honest headline conclusion
  (weaker than, never stronger than, the Lean) and discloses the elided
  bookkeeping in one Formalization note, per the "don't over-note" +
  Formalization-note carve-out (`AUTHORING.md` principles B/D).

### D — decisions with defaults (owner sign-off)
- [x] **D1 — superseded blocks.** **Owner-confirmed 2026-07-02: collapse
  (the default).** `genericity-and-count.tex:476–660` (four dead lemmas
  N7b-4/M1/M2/M3 + route-history prose) and the `rigidity-matrix.tex:495`
  superseded title each collapse to a one-sentence remark (git is the
  audit trail), **revising `blueprint/CLAUDE.md`'s retain-with-marker
  supersession rule in the same commit** so the discipline and the corpus
  stay consistent. **`genericity-and-count.tex` half LANDED with R3
  (2026-07-05)**, `blueprint/CLAUDE.md` revised in the same commit
  (retain-with-marker stays the default for an isolated dead node; a whole
  dead route now defaults to collapse). `rigidity-matrix.tex` half still
  lands with R4.
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
**Next agent action: P1 — the `lint.sh` vocabulary gate** (see the *P —
prevention* task entry: a greppable banned-term check over
`blueprint/src/chapter/`, tuned to zero false positives against the
now-cleaned corpus, running with the other per-commit static gates).
After P1, only P2 (the FRICTION resolution flip) and the optional §D
tail are left before the round closes. R11 is complete (2026-07-05; the
haiku spot pass `e7874d06` + a coordinator follow-up that dropped both
reader-facing `DESIGN.md` pointers per the R4/R5 internal-doc-ref
treatment).

R10 (`body-bar.tex` (642 → 631) + `body-hinge.tex` (148 → 143)) is now
fully LANDED (2026-07-05, docs-only): per the task list's narrower scope
(preamble/dep-graph framing only, "a smaller dispatch than R2–R9"), no
statement-surface audit was needed — the pinned nodes themselves are
untouched, so no Lean signatures were re-read against the blueprint text.
Both chapters' opening "This chapter is the forward-mode authoritative
dep-graph and lemma index for Phase(s) N ..." paragraph and closing
"Phase~N is complete: every node below is formalized (green) ..." status
paragraph (confirmed by grep beforehand) are gone,
replaced by a one-paragraph "this chapter proves ..." opening naming the
target theorem directly — matching how the backfill-mode pre-molecular
chapters (`sparsity.tex`, `frameworks.tex`, `rigidity-matroid.tex`,
`pebble-game.tex`) open, since both phases have been complete for many
sessions. Every remaining bare `Phase~N` pointer in the two files was
also dropped (7 occurrences: `body-bar.tex`'s two "(Phase~12)"
matroid-union pointers — one of which duplicated `matroid-union.tex`'s
own Provenance paragraph, trimmed to the bare `\cref` — "fresh to
Phase~13", and the twice-repeated "deferred out of Phase~15 (re-assessed
when the body-hinge phase opens; see `ROADMAP.md` §15)" aside on
Whiteley's irreducible-variety lift; `body-hinge.tex`'s matching
"(Phase~15)" cross-reference and its own "deferred ... re-assessed here"
aside), rewritten to keep the honest math content (the lift is still
genuinely unaddressed — `notes/Phase16.md`: "deferred ... now to the
molecular-conjecture phase if ever pursued") without the internal
phase/file pointer. `verify.sh`/`lint.sh` green; confirmed via `git
stash` that the plastex warning set is byte-identical before and after.
Full account in the R10 task-list entry.

R9 (`deficiency.tex` + `extensor.tex`) is now fully complete
(2026-07-05, 489→486 + 219→207 lines): audit read all ~30 pinned Lean
signatures across `Molecular/{Deficiency,Extensor}.lean` — every
signature already at the strength the blueprint states, except one small
gap fixed docs-only (no Lean change): `thm:def-eq-corank` was missing the
`V(G) \ne \emptyset` hypothesis its pinned `rank_add_deficiency_eq`/
`isBase_ncard_add_deficiency_eq`/`le_rank_add_deficiency` family actually
carries (its sibling node `lem:rank-matroidMG-le`, two nodes up in the
same subsection, states the identical hypothesis explicitly; this one
silently dropped it) — added the clause. No zero-caller/dead-wrapper
liveness issue found (unlike R2/R6/R7's `d=3`-only-wrapper finds) and no
self-inconsistent superseded-route issue. Rewrote both preambles to
Target style: `deficiency.tex` dropped its "Phase~19"/"third stratum"
opening and standalone `Status.` paragraph, replacing both with a
roadmap paragraph naming its three subsections in proof order (principle
F, folding the `Status.` paragraph's KT-Lemma-number content in);
**fixed a genuine bug the audit found** — `def:k-dof`'s prose cited
`\cref{sec:molecular-deficiency}` (this chapter's own section label, a
no-op self-reference) where it meant to point at the reduction theorem
`\cref{thm:minimal-kdof-reduction}` in `\cref{sec:molecular-induction}`;
also replaced "the honest rank form" (×2) with "the rank form" and bare
"Phase~16"/"Phase~21+" mentions with `\cref{sec:body-hinge}`/
`\cref{sec:molecular-algebraic-induction}`. **Deleted `extensor.tex`'s
"Forward-mode chapter" mechanics paragraph outright** (per the task's
explicit instruction; that convention now lives solely in `intro.tex`)
along with its "Phases~17–26"/"five-strata architecture"/
`notes/MolecularConjecture.md` opening, replacing both with a roadmap
paragraph matching the `rigidity-matrix.tex`/`molecular-induction.tex`
template. `verify.sh`/`lint.sh` green throughout; `checkdecls` confirms
the one statement edit didn't disturb any `\lean{...}` pin. Full account
in the R9 task-list entry.

**Findings surfaced during R2/R7/R8, flagged, not fixed, carried forward:**
- **`lem:case-III-claim612-line-in-panel-union` is a 12-pin bundle across
  five files** (`Molecular/Meet.lean`,
  `Molecular/AlgebraicInduction/{PanelLayer,CaseI}.lean`,
  `Molecular/RigidityMatrix/Claim612.lean`,
  `Molecular/AlgebraicInduction/CaseIII/{Candidate,Arms}.lean`; R8's
  audit) — well over principle D's split threshold. One of the 9
  "extended pipeline" pins
  (`hasGenericFullRankRealization_of_rigidOn_ofNormals`, the general
  bare-to-generic upgrade) is not really about this node's point-join/
  panel-meet duality at all; it is independently cited by
  `lem:cycle-realization` (`case-i.tex`) for an unrelated purpose, and its
  own `\uses`-worthy dependencies (the genericity-device machinery of
  `genericity-and-count.tex`) postdate `meet.tex` in reading order, so it
  cannot honestly live in this chapter as its own node either. R8's fix
  was a disclosure (one Formalization note naming the role of each of the
  9 extra pins and flagging the shared citation), not a split — a full
  split would mint a new node in `case-i.tex` or `panel-layer.tex`'s
  territory (where the upgrade lemma's real dependencies live) and repoint
  `case-i.tex`'s existing citation, which is a larger, cross-chapter
  change than a register-only pass should attempt. Flagged for a future
  dead-code/over-pin sweep.
- **`PanelHingeFramework.case_III_candidate_dispatch` has zero callers**
  (`Realization.lean:324`, the old $d=3$-only three-panel `fin_cases`
  dispatch; slice 3's audit) — `case_III_realization` is now a one-line
  specialization of `case_III_realization_all_k`, which routes through the
  general `chainData_dispatch` for every grade including $d=3$. The chain
  `case_III_candidate_dispatch` → `exists_complementIso_ne_zero_of_homogeneousIncidence`
  → `case_III_claim612` is therefore orphaned, and the blueprint nodes
  pinned to it (`lem:case-III-claim612`, `-p2-placement`, `-p3-placement`,
  `-eq644`, possibly `lem:case-III-candidate-row`) may be describing dead
  code as if live. Not resolved here — a liveness/correctness audit of that
  family is its own task, orthogonal to a prose-register slice and risking
  R2 slices 1/2a/2b's just-landed work; flagged for a future dead-code
  sweep. (The precedent this pointed at, `case_I_dispatch` and its sibling
  `d=3` wrappers, is **resolved** — R6 found and repinned the exact same
  orphaning pattern in `case-i.tex`'s three producer nodes onto their live
  general-grade `_gen` forms, 2026-07-05. The `case_III_candidate_dispatch`
  family above is a distinct, still-open instance in `case-iii.tex`/
  `meet.tex`'s territory.)
- **`lem:case-II`'s two pinned bridge decls have zero proof-term callers**
  (`BodyHingeFramework.isInfinitesimallyRigidOn_insert_iff`,
  `PanelHingeFramework.rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions`,
  R7's audit) — the live producer `case_II_realization_all_k` builds the
  extended framework directly (a row-family union + the rank-polynomial
  genericity lift) rather than routing through this bridge, matching its
  own doc-comment ("no shared brick fits here"). Unlike the
  `case_I_dispatch`/`case_III_candidate_dispatch` precedents, there is no
  live `_gen` sibling to re-pin onto — this looks like a superseded design
  attempt at the Case-II accounting, not a `d=3`-only wrapper. Not resolved
  here: `lem:case-II` is `\uses`'d from 9 other files, so re-pinning or
  retiring it is a `lem:case-II`-wide change, out of scope for a
  register-only slice; flagged for a future dead-code sweep.

The Conjecture-1.2 multigraph question is resolved (2026-07-04, disclosure
landed — verdict in *Decisions made* below). R1 is closed (checkpoints
#5/#6 passed, R1h landed 2026-07-04); the B8 resolution, the R1h work list,
and the checkpoint-#4/#5 arc are recorded in full just below and in git
history.

**B8 resolved (owner, 2026-07-04):** the `thm:theorem-55` all-deficiency-form
question (review item B8), held for owner and excluded from R1h — the node
titled "KT Theorem 5.5" stated the k′=0 case while KT's 5.5 is the all-k
statement; the Lean proved BOTH (two pins; the fmlnote disclosed the all-k
form), so the blueprint undersold rather than oversold. Owner verdict:
restate at all-k strength, and drop the k=0 wrapper rather than keep it as a
second pin — `theorem_55_gen` had zero proof-term callers (only its own
decl, the parent spine's docstring pointer, two comparative docstring
mentions, and this one blueprint pin), so it was dead weight, not a
consumer surface worth preserving. `thm:theorem-55` is now pinned solely to
`theorem_55_minimalKDof_gen` and restated at its actual (all-deficiency)
strength, with the deficiency-zero case kept as an "in particular" closing
sentence; `theorem_55_gen` deleted from `Theorem55.lean`, and the two
comparative docstring mentions repointed to the spine / the other
consumer-facing wrapper. **Future work (Phase 24+):** if a consumer-facing
deficiency-zero wrapper of KT Theorem 5.5 is wanted again, mint a fresh
headroom-bound all-k wrapper deriving the fresh-edge supply via
`Graph.freshEdgeSupply_of_card_lt` on demand (the E-arc pattern), rather
than resurrecting `theorem_55_gen`.

### R1h work list — LANDED (`2f55efb8` + `d72f5210`)
The full adjudicated list (V1--V8 confirmed violations + J1--J22 adopted
judgment calls + one KEEP) lives in the `87be4c0f` version of this file
(git is the audit trail); all items delivered, plus the B8 resolution
(`theorem_55_gen` deleted, `thm:theorem-55` restated at all-deficiency
strength). Two durable artifacts: the new node `thm:theorem-55-6-genuine`
(pins the witness form `molecular_conjecture` actually uses) and the J3
finding that `rigidityMatrix_prop11` carries no spanning hypothesis.


**The checkpoint-#4/#5 revision arc is LANDED and R1 is closed** — the
calibration-v5 A–F consolidation of AUTHORING.md (`50736861`), the 9(a)
collapse of `rankHypothesis_of_theorem_55_d3` to a corollary of the
general form (`643188b7`), the R1g 11-item pass + the shared-counter
`fmlnote` environment (`98dae6af`), and the checkpoint-#5
endpoint-selector follow-up (`be47e869`). The full 11-item adjudicated
disposition list lives in the `9c73c79e` version of this file (git) and
the *Decisions made* entry below; the two math-fidelity finds (the
Case-II cut-edge mis-grouping; the duplicated d=3 proof) are fixed in
tree.

**R1 passed owner checkpoints #5 and #6 (2026-07-04) and is closed again after
R1h; the fresh-session next steps (Conjecture-1.2 question, then R2) are in
*Hand-off* above.**

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
- **R4 — `rigidity-matrix.tex`, COMPLETE (2026-07-05, docs-only):**
  statement-surface audit first: read all ~35 pinned signatures across
  `RigidityMatrix/{Basic,Bricks}.lean` and
  `AlgebraicInduction/{CaseI,Coupling}.lean` — every node already at its
  pin's strength, no Lean change, with one honest-red confirmation
  (`def:dof-generic` correctly lacks `\leanok`: its "generic realization"
  conjunct is unformalized, only `IsInfinitesimallyRigid` is pinned).
  Rewrite: dropped the "L5a-i splice brick"/"L5b-i"/"L4a" node-code titles,
  "brick"/"producer"/"stratum"/"honest" throughout, "the `hub` bound" (→ the
  plain codimension-bound statement), and the `notes/MolecularConjecture.md`
  risk-register aside; deleted the "Status." preamble paragraph (principle
  F), folding its real content into a half-page roadmap. Fixed the
  pre-existing broken `\S\ref{sec:case-I}` (rendered "see §??"; confirmed via
  rendered-HTML diff) to `\cref{sec:molecular-algebraic-induction-caseI}`.
  Two structural moves, both label/lean/uses-preserving (verified via a
  line-diff against HEAD): added an unlabeled
  `\subsection{Block-rank-addition lemmas for the case analyses}` and
  reordered `lem:block-rank-cut` (KT Lemma 6.1) to open it ahead of Lemma
  6.2/6.8/6.10, restoring KT's numbering; trimmed `def:rigidity-matrix`'s
  statement to the bare definition and moved its bundled row-independence
  build-up into unlabeled connective prose after the environment (same 13
  pins, same label). D1's `rigidity-matrix.tex` half: the one struck node
  (`lem:rank-polynomial-IH-relabel`) is the corpus's only superseded node
  outside `matroid-union.tex` — an isolated dead node, so it stays
  retained-with-marker (title/prose de-jargoned), not collapsed.
  Post-draft fidelity re-check (per the R2 caution against smuggling
  extra/dropped hypotheses into a restate): caught and fixed one own slip in
  the `def:rigidity-matrix` connective prose — the forest-independence gloss
  had compressed away half of `linearIndependent_hingeRow_forest`'s
  hypothesis (`hu` distinct private endpoints only, dropping the `hsep`
  no-other-endpoint-hits-a-private-endpoint half), which would have
  overclaimed the fact; restored both clauses before commit. **Found in
  the audit (flagged, not fixed):** two multi-label `\cref{a,b,c}` I first
  drafted rendered as literal "??" — a real, causally-confirmed
  plastex/cleveref limitation with dozens of unfixed pre-existing instances
  across `molecular.tex`, `molecular-induction.tex`, and the already-R2-cleaned
  `case-iii.tex`; reworked mine to the corpus's `\cref{a}, \cref{b}, and
  \cref{c}` idiom, but the pre-existing instances elsewhere are untouched (a
  candidate future `lint.sh` grep, `[cC]ref\{[^}]*,`). `def:rigidity-matrix`'s
  13-pin bundle is a standing over-pin candidate for a future node-split pass
  (R1e precedent), not attempted here (cross-chapter `\uses` risk in the
  not-yet-cleaned R5/R6 chapters). `verify.sh`/`lint.sh` green; the one
  pre-existing warning flagged in R2 (`lem:case-III-claim612-line-in-panel-union`
  duplicate label) reconfirmed unchanged via `git stash` diff of the full
  plastex warning set.
- **R3 — `genericity-and-count.tex`, COMPLETE (2026-07-05, docs-only + the
  `blueprint/CLAUDE.md` rule revision):** statement-surface audit first: read
  all 13 pinned Lean signatures across `GenericityDevice.lean`,
  `Pinning.lean`, `CaseII.lean`, and `RigidityMatrix/Basic.lean` — every node
  already at its pin's exact strength, no Lean change warranted. Prose
  rewrite to principles A–F: dropped the N7b-\*/M\* node-code titles;
  "brick", "motive", "producer", "honest"/"honesty"/"launders", and Lean
  hypothesis names (`hgen`, `hub`, `hglue`, `hspan`) from the subsection-
  opening paragraph and every statement/proof; replaced raw Lean-identifier
  math (`\mathrm{ofNormals}\,G\,\mathrm{ends}\,q`, `\mathrm{Screw}`,
  `\mathrm{pinnedMotionsOn}\,s`, `\mathrm{Function.update}`,
  `\mathrm{Sum.elim}`) with the established corpus notation ("free-normal
  panel framework", $\Lambda^k \R^{k+2}$ matching `case-i.tex`, $Z_s(G,p)$ /
  $\operatorname{pinned}(v)$ matching `case-i.tex`'s `def:pinned-motions-on`
  / `lem:rank-delete-vertex`). Moved role/positioning material (the
  "forward converse" framing, the Case-I/Case-II structural parallel) out of
  statements into unlabeled connective prose, matching this file's own
  established `\medskip\noindent\emph{...}` pattern. Delivered D1's
  `genericity-and-count.tex` half: the four dead lemmas (row-side N7b-4,
  motion-side M1/M2/M3) and their ~200-line route-history subsubsection
  (intro + "why the row-side framing fails" + the superseded motion-side
  rank-lift + the buildable sub-node decomposition) collapsed to two short
  connective paragraphs after the live `lem:case-II-realization-placement`
  proof and after `lem:case-II-placement-old-rows-extract`'s proof
  respectively — no lemma/proof environment, no `\label`ed audit-trail
  block, git the audit trail. Confirmed via grep that no other file in the
  corpus `\cref`'d the four deleted labels before deleting them. Revised
  `blueprint/CLAUDE.md`'s supersession-gate section in the same commit: the
  retain-with-marker convention stays the default for an isolated dead node,
  but a whole dead route (several struck nodes plus route-history prose)
  now defaults to collapse, since retain-with-marker inverts the reader's
  cost once the dead material outweighs the live node it decorates.
  `verify.sh`/`lint.sh` green; the two pre-existing warnings flagged in R2
  (`sec:case-I` undefined in `rigidity-matrix.tex`; the
  `lem:case-III-claim612-line-in-panel-union` duplicate label) reconfirmed
  unchanged via `git stash`.
- **R2 slice 3 — the general-`d` chain dispatch + `lem:case-III`, closing R2
  (2026-07-05, docs-only + the S3 node promotion):** prose rewrite of the
  connective narrative preceding `lem:case-III` (the "one base, $d$ views" /
  "the single redundancy and its $\pm$ carry" / "the discriminator" items) to
  principles A–F, explicitly narrating KT's §6.4.1 ($d=3$) → §6.4.2 (general
  $d$) two-stage structure per the BlueprintExposition seed: Claim 6.11 and
  Lemma 2.1's general-grade span argument lift verbatim from the $d=3$ case;
  the $\pm$-transport of the shared redundancy across the chain's $d$ panels
  is the genuinely new bridge. Delivered seeded item S3: promoted
  `chainData_fire_discriminator` / `chainData_dispatch`
  (`Molecular/AlgebraicInduction/CaseIII/Realization.lean`) to two new nodes,
  `lem:case-III-chain-discriminator` / `lem:case-III-chain-dispatch`.
  Statement-surface audit first: `chainData_dispatch`'s signature is clean
  (pinned verbatim, no Lean change); `chainData_fire_discriminator`'s
  conclusion is a fat existential bundling the genuine KT eq.-(6.57)–(6.67)
  content (the shared redundancy $\rho_0$ + the matched-candidate gate) with
  bookkeeping consumed only by its two sibling dispatch branches (a
  link-recording selector, $\rho_0$'s hinge-functional decomposition, an
  independent bottom-row family) — a full-fidelity restate would mean
  slimming that interface across several call sites, judged substantial and
  flagged rather than attempted; the new node states the honest (weaker,
  never stronger) headline conclusion and discloses the elided data in one
  Formalization note. `lem:case-III`'s own proof shortened to cite
  `lem:case-III-chain-dispatch` for the $|V| \ge 4$ step instead of
  re-narrating the mechanism inline, dropping its `\uses` from 20 targets to
  7 (14 mechanism-level labels — the eq.-(6.12) placement, Claim 6.11, the
  candidate-row completion, the nested-rank bound, the two relabel lemmas,
  the rank-attainment lemma, the genericity device, and the four
  $d=3$-only Claim-612 sub-nodes plus the Claim-612 span/orthseq pair — now
  sit on the two new nodes' own `\uses` instead). **Found in the audit
  (flagged, not fixed — a liveness question
  orthogonal to this slice's prose-register scope):**
  `PanelHingeFramework.case_III_candidate_dispatch` (`Realization.lean:324`,
  the old $d=3$-only three-panel dispatch) has zero callers —
  `case_III_realization` now routes through the general `chainData_dispatch`
  for every grade, so the chain `case_III_candidate_dispatch` →
  `exists_complementIso_ne_zero_of_homogeneousIncidence` →
  `case_III_claim612` is orphaned, and the blueprint nodes pinned to it
  (`lem:case-III-claim612`, `-p2-placement`, `-p3-placement`, `-eq644`,
  possibly `lem:case-III-candidate-row`) may describe dead code as live; see
  *Hand-off* for the full account and the precedent (`case_I_dispatch`, S2).
  `verify.sh`/`lint.sh` green; no pre-existing warning changed.
- **R2 slice 2c — the triangle floor of `case-iii.tex` (2026-07-04, docs-only):**
  prose rewrite of the connective paragraph ("The triangle floor.") + the two
  triangle nodes (`lem:triangle-third-edge`, `lem:triangle-realization`) to
  principles A–F, stopping before `lem:case-III` (slice 3). Statement-surface
  audit: both pins already at strength (no Lean change); found and fixed **two**
  dep-graph gaps, not one — the hand-off's flagged empty `\uses{}` on
  `lem:triangle-third-edge`'s statement (→ `def:k-dof`, the "minimal $0$-dof
  graph" hypothesis), plus a second one the audit turned up: the proof invokes
  `rank_matroidMG_of_isKDof_zero` (KT's def-eq-corank identity specialized at
  deficiency $0$) with no `\uses` macro on the proof block at all — added
  `\uses{thm:def-eq-corank}` there. Register fixes: the raw Lean field access
  `cy.m` → plain `$|V(G)|$`; the banned mechanism verb "consumes" → "is exactly
  the dichotomy's cycle disjunct"; the banned term "arm" (in "the chain arm
  runs under") → "disjunct", matching the paragraph's own established term;
  `lem:triangle-realization`'s proof dropped the un-introduced `T1`/`T2`/`T3`
  internal codes (copied verbatim from the Lean docstring's own shorthand — not
  a KT label) and its two inline Lean-name citations
  (`\texttt{unique\_edge}`, `\texttt{hasGenericFullRankRealization\_of\_rigidOn\_ofNormals}`)
  — the first described directly ("no two edges share both endpoints"), the
  second replaced by citing the genericity device (`\cref{lem:genericity-device}`,
  matching the exact phrase already used for this step later in the same file at
  line ~1199, "the genericity device re-realizes that rank …"), added to the
  proof's `\uses`. Dropped the banned term "motive" ("upgrade to generic
  motive" → "giving the generic full-rank realization", matching the
  statement's own wording). The empty `\uses{}` this closes out was confirmed
  the sole remaining one in the whole corpus (`grep -rn '\uses{}' blueprint/src/`
  now empty). `verify.sh`/`lint.sh` green; the pre-existing
  `lem:case-III-claim612-line-in-panel-union` duplicate-label warning (flagged
  in slice 2b, out of scope here) is unchanged.
- **R2 slice 2b — the $D$-candidate disjunction of `case-iii.tex` (2026-07-04,
  docs-only):** prose rewrite of the subsubsection "The $D$-candidate disjunction"
  (opening + 21 nodes: the 14 `lem:case-III-claim612-*` nodes through the capstone Claim
  6.12, plus the 3 `lem:splitOff-*-relabel` transport nodes, KT eqs. (6.30)–(6.45)) to
  principles A–F. Statement-surface audit first: read all ~25 pinned signatures across two
  Lean files (`Molecular/RigidityMatrix/Claim612.lean`,
  `Molecular/AlgebraicInduction/CaseIII/Relabel/Basic.lean`) — every node already at its
  pin's strength, no Lean change warranted. Fixed the empty `\uses{}` at
  `lem:splitOff-isLink-relabel` → `def:graph-operations` (the statement's only external
  dependency is `Graph.splitOff`/the link relation; the natural `lem:chain-data-of-noRigid`
  candidate is explicitly dead — its own node says its only remaining consumer is the
  orphaned `chainData_extract_d3` — so `\uses`-ing it would resurrect a dead edge).
  Rewrite: dropped "capstone", "producer" (×7+), "consumes"/"consumer" (mechanism
  metaphor, ×6+), "brick" (×2), "route"/"routing" (×4), the "(R1) reconciliation" internal
  code in a title, and all inline Lean helper-lemma citations
  (`\texttt{...}`/`\mathrm{Foo.bar}` naming a *proof step*, e.g.
  `MvPolynomial.exists_eval_ne_zero`, `RingHom.map_det`, `Fin.snoc`,
  `Fintype.card_subtype_fst_lt_snd`, `LinearMap.ext_on`) in favor of describing the fact
  directly or `\cref`-ing a node — matching slices 1/2a's established practice (verified:
  zero such inline citations in the already-landed lines 1–593). Extended the
  register-calibration note: `\mathrm{ScrewSpace}\,k` / `\mathrm{Module.Dual}` → the plain
  $\bigwedge^k \R^{k+2}$ and its dual; `\mathrm{Fin.snoc}(pp_i, 1)$ → the established
  homogenization bar-notation $\overline{pp_i} := (pp_i, 1)$ (from `extensor.tex`'s
  `def:homogeneous-coords`); `\mathrm{Equiv.swap}\,a\,v` → cycle notation $(a\,v)$, matching
  the nodes' own titles ("the $\rho = (a\,v)$ relabel"). Kept `\mathrm{col}_a
  \mathrel{+}= \mathrm{col}_v` and `\mathrm{complementIso}` — both name a *defined
  operation* anchored by a `\uses`'d def node, not a helper-lemma citation (the latter
  matches `meet.tex`'s own not-yet-cleaned usage, R8). Moved role/positioning material
  (why a witness is needed relative to real normals, why the transport is stated at the
  framework level not as a bare existential, why the general polynomial route "would also
  work" but is unnecessary) out of statements into connective prose or proof narrative,
  per principle B. **Found, flagged, not fixed (cross-chapter, out of this slice's
  scope):** `lem:case-III-claim612-line-in-panel-union` is a duplicate `\label` — this
  file's copy (2 `\lean` pins) and `meet.tex:239`'s (11 pins, the fuller Phase-22f
  assembly) share one label; confirmed pre-existing via `git stash` (identical plastex
  "multiply defined reference" warning on unmodified `master`) — see the R2 task-list
  entry and *Hand-off* for the recommended fix. No `\lean`/`\uses`/`\leanok` changed
  besides the one `\uses{}` fix; `verify.sh`/`lint.sh` green.
- **R2 slice 2a — the candidate-completion of `case-iii.tex` (2026-07-04,
  docs-only):** prose rewrite of the "candidate-completion" subsubsection (opening + 9
  nodes `lem:case-III-vanish-off-column` … `lem:case-III-candidate-row`, KT eqs.
  (6.24)–(6.29)) to principles A–F. Statement-surface audit first: all 9 pins at their
  strength, no Lean change. Dropped "stratum-1 brick" and Lean identifiers
  (`hingeRow`/`annihRow`/`single`/`proj`/`Sum.elim`/`ofNormals`/`ScrewSpace`); kept KT's
  row/column-op notation, wrote hinge rows as $\rho(S_v - S_a)$ and the screw space as
  $\bigwedge^k \R^{k+2}$; the column op $\Phi$ stays (a genuine mathematical operation).
  Slice 2 was too large for one sitting → sub-split (2a done / 2b $D$-candidate disjunction
  / 2c triangle floor); the two pre-existing empty `\uses{}` fall in 2b (`case-iii.tex:1022`)
  and 2c (`:1257`). No `\lean`/`\label`/`\uses`/`\leanok` changed; `verify.sh`/`lint.sh` green.
- **R2 slice 1 — the Claim 6.11 chain of `case-iii.tex` (2026-07-04,
  docs-only):** prose rewrite of the Case III subsection opening + the 8 nodes
  through `lem:case-III-claim-6-11` to principles A–F. Statement-surface audit
  first: read all 8 pinned signatures (`splitOff_exists_base_inter_fiber_lt`,
  `splitOff_removeVertex_minimalKDof`, the three CaseI seed-rank lemmas,
  `case_III_nested_rank_lower{,_all_k}`, the two Candidate.lean redundant-row
  lemmas) — every node already at its pin's strength, no Lean change warranted.
  Rewrite: dropped process vocabulary (`hub`/`brick`/`motive`/`stratum`,
  "green"/"leaf-most", `Gap-2`/`L7a` codes), moved Lean identifiers
  (`ofNormals`/`panelRow`/`hingeRow`/`RankHypothesis`/raw helper names) out of
  statements and prose, introduced "free-normal panel framework" once at the
  subsection opening (anchored to `def:panel-hinge-framework`, resolving the
  chapter-wide `ofNormals` anchoring gap), and added one `fmlnote` on
  `lem:case-III-nested-rank-lower` for its two-pin general-`k`/`d=3` grade
  structure. Title "Case III (the crux)" → "Case III" (significance-pointing,
  principle A). No `\lean`/`\label`/`\uses`/`\leanok` changed;
  `verify.sh`/`lint.sh` green.
- **Conjecture-1.2 multigraph disclosure (2026-07-04, docs-only):** the
  review's analysis verified against the Lean defs + KT pp. 648/669–670 and
  HOLDS: the meet model forces parallel edges to share their hinge line
  (coincident panels degenerate the meet; swap only negates), so KT
  Lemma 5.3's coincident-panel double-edge realization is inexpressible and
  the unrestricted iff is FALSE in the model (double edge: body side rigid
  nondegenerate, panel side flexible). Landed as disclosure, no Lean change:
  `fmlnote:molecular-conjecture-multigraph` (carries the full argument) +
  "simple-graph case" attribution; the 5.6 fmlnote repointed; the "every
  multigraph"/"a graph" overclaims fixed on intro.tex/README/home_page.
- **R1h — checkpoint-#6 fidelity commit (2026-07-04, docs-only):** the
  owner-adjudicated V1–V8 + J1–J22 + KEEP work list landed over
  `panel-layer.tex`. V4 minted `thm:theorem-55-6-genuine`
  (`rankHypothesis_genuine_of_theorem_55_gen`, the ≥2-body nondegenerate-hinge
  witness form the conjecture actually routes through) and rerouted
  `thm:molecular-conjecture`'s cref/`\uses`; V2/V3 restated to the pins' exact
  strength (bare conjunct → `HasPanelRealization`; `lem:generic-yields-genuine-hinge`
  → `HasGenericFullRankRealization`). J3 flag: `rigidityMatrix_prop11` has no
  spanning supposition — only the nondegenerate-hinge `hC` moved into the
  statement. Signatures read before restating; new node the only `\lean{}`
  change; `verify.sh`/`lint.sh` green.
- **Checkpoint-#4/#5 arc (2026-07-03/04) — R1 closed after 5 owner
  checkpoints:** the owner's 11 rough notes were grounded by a fable recon
  (row 688; 2 math-fidelity finds: the Case-II cut-edge mis-grouping traced
  to the v1 calibration sample; the un-rebased d=3 `rankHypothesis`
  duplicate), adjudicated (6: `fmlnote` on the shared counter, collapsible
  deferred; 9(a): Lean-first collapse; 10: nondegenerate-in-statement +
  encoding note at the framework def), and landed as v5 (A–F) + 9(a) + R1g
  + the endpoint-selector follow-up (extends principle E to definition
  data). Full lists: git `9c73c79e` / rows 688–692.
- **R1g — checkpoint-#4 11-item pass + Formalization-note env (2026-07-04,
  docs-only):** the `fmlnote` environment (shared theorem counter, remark
  style, `\crefname` after cleveref, dashed-border CSS) landed first, then the
  11 items at their adjudicated shapes; seven surviving notes converted, the
  rest deleted/trimmed. Two findings promoted below. Renders as "Formalization
  note 23.N" with working crefs; the numbering renumber is the accepted
  one-time cost. `verify.sh`/`lint.sh` green; no `\lean{}` pin changed; KT §2.3
  + "genuine ∉ KT" verified against the `.refs/` PDF. Details in the *Hand-off*
  (iii) block and git.
  - *`\crefname` for a shared-counter amsthm env must go after cleveref, which
    is loaded after `preamble/common.tex`* — so the env is defined in
    `common.tex` but its `\crefname`/`\Crefname` live in `web.tex`+`print.tex`.
    plastex + cleveref then number and name it correctly from the env (not the
    shared `theorem` counter), same as the existing lemma/definition envs.
  - *Dep-graph gap found + fixed:* `lem:case-cut-edge-realization{,-gp}`
    (molecular-induction.tex) were orphaned — no node `\uses`'d them (only a
    proof cross-`\cref`); the item-1 four-case narration of `thm:theorem-55`
    now consumes both. Pre-existing benign defect flagged for R2: empty
    `\uses{}` at `case-iii.tex:1070,1305` (two plastex `Label ''` warnings).
- **9(a) — `rankHypothesis_of_theorem_55_d3` Lean collapse (2026-07-04,
  Lean-only):** collapsed to a one-line corollary of
  `rankHypothesis_of_theorem_55_gen (n := 3)`, name/signature kept
  (`panel-layer.tex` pin unaffected); moved to sit textually after its new
  parent. Both discharges closed exactly as the E1 spike predicted:
  `norm_num` for `3 ≤ 3`, `simpa [Graph.bodyBarDim] using hcard`, and
  `PanelHingeFramework (3-1) α β` vs. the pinned `2` by plain `Nat.sub`
  kernel defeq — no cast. Repo-wide grep found no live residue beyond
  historical phase-note mentions. Seeded `notes/BlueprintExposition.md`'s
  general-`d` chain-dispatch entry with the R2 exposition note. `lake
  build`/`lake lint` green; no blueprint file touched.
- **Calibration-v5 A–F consolidation of `blueprint/AUTHORING.md`
  (2026-07-03, docs-only):** the *Audience & vocabulary* section's 17
  *Target style* rules + the 4 checkpoint-#4 candidates were rewritten
  into six principles (A vocabulary/register, B statements, C proofs, D
  formalization notes & pins, E fidelity & anchoring, F chapter flow),
  each with one mechanical test; rule 8 → a process footer. Clause-by-
  clause coverage of all 17 rules verified before commit; the header
  (audience statement + test) was kept; the dictionary was extended
  (honest/honesty, genuine→nondegenerate, Lean-verb coinages,
  threads/carries-in-notes, the "parallel" convention) and a "rule N →
  git" historical pointer added. Section 189→126 lines. Provenance
  narration dropped to git per the hand-off.
- **R1f — rule-17 statement-surgery pass over `panel-layer.tex` (2026-07-03,
  docs-only):** ~28 nodes + minor residuals reduced to Let/Suppose/Then +
  gloss (calibration v4); role/comparison/construction material and Lean
  identifiers moved to connective prose, proofs, Formalization notes (never
  dropped except proof-duplicating text). `lem:theorem-55-base` restated at
  the `theorem_55_base` conditional's exact strength (honesty pin);
  `prop:rigidity-matrix-prop11` JJ credit kept plain. No `\lean`/`\uses`/
  `\label` touched; deletion + standalone tests run; `verify.sh`/`lint.sh` green.
- **KT-style review pair → rule 17 (2026-07-03, recon):** after the owner's
  checkpoint-#3 signal ("declarations too prose-y"), an opus+fable
  diverse-lens pair independently audited all 33 panel-layer nodes against
  KT's own statements (both read the KT PDF). Converged diagnosis: the
  flagship theorems are at register, but ~2/3 of the supporting nodes carry
  role/positioning tails, comparisons, construction-in-statement, or Lean
  identifiers — classes rules 1–16 miss. Folded as rule 17 (calibration v4,
  `blueprint/AUTHORING.md`) + the R1f work list (*Hand-off*). Good pair data
  point: verdicts materially identical (fable sharper on statement shape,
  opus on category taxonomy + attribution carve-outs).
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
