# Phase 43 — PENCIL-NATURAL: design (cross-phase plan)

**Status:** ✓ closed 2026-11-08 (opened 2026-11-07 with the PI), sub-lettered 43a–43d: a simpler
pencil proof, with no main result's statement changed. **43a** READS (`notes/Phase43a.md`): the
three fresh reads held. **43b** LIFT3 (`notes/Phase43b.md`): the `d = 3` theorem is the case
`d = 3` of the theorem in every dimension, and the reduction's cases are proved once. **43c** NORMAL
and SPRIME (`notes/Phase43c.md`): the reduction on five structural cases, and Theorem S′ at `d = 3`,
with the two unnecessary steps gone. **43d** EXPO (`notes/Phase43d.md`): the road map of the proof
and the flatness remark, with the two main-component statements removed and a duplicate theorem
folded, at the PI's word. Summary: ROADMAP §43. No sub-phase is open, and the next step is
PENCIL-SCENES (queued 2026-11-09 ahead of ORIGAMI, `notes/PencilScenes.md`), with the PI.

This file is the phase's entry point: the target (§0), the PI's decisions (§1, verbatim), the
layers by stable code (§2) and the open questions (§3). The recon record stays in
`notes/PencilNatural.md`, cited by section: the proof as it stands (§2), the verdicts N1–N6 with
their sizes (§3), the recon's brief (§4) and the intuitions I1–I4 (§5).

## 0. Target

Make the proof of the pencil realization theorem simpler and its cases more natural, in every
dimension, and then explain it in the blueprint: a road map in the manner of KT §1.1. The main
results (`pencil_realization_theorem`, `pencilPair_of_nonempty`,
`Graph.graded_pencil_conditioned_pair`) keep their statements. What changes is the route:
- the `d = 3` generic conjunct comes from the every-dimension lift (N1c), so every dimension has one
  shape: A the reduction, B the main-component induction, C the lift;
- the reduction is restated on five structural cases (N2);
- the `d = 3` coverage loses two short-chain rows (N3, Theorem S′).
What the recon ruled out (N3's other rows, N4, N5, N6) is `notes/PencilNatural.md` §3.

## 1. The PI's decisions (verbatim)

**PI, 2026-11-07, on N2's call (a), whether the reduction may stop mirroring KT Theorem 4.9:** "I
think we should be free to diverge from KT Theorem 4.9, but if it plays a similar role in the proof
as KT Theorem 4.9 does in the KT proof, then it's worth a reference (perhaps just in a remark or in
surrounding glue text)."

**PI, 2026-11-07, on N2's call (b), `lem:pencil-min-degree-rigid`, after asking why it would
retire:** "Let's keep it off the route for now; perhaps we could move it into a separate appendix."
The blueprint's `\appendix` holds only `retrospective.tex` today.

**PI, 2026-11-07 (a second session), D1–D5**, deferred from the first, after a synthesis of the
verdicts. Each was chosen from the options offered; the chosen label is quoted, then what it was
offered as:
- **D1:** "N1c (Recommended)": the reduction proved once, for every `d` (about −4.6k Lean lines,
  17 files, 15 nodes); `pencil.tex` stops proving `d = 3` on its own terms.
- **D1, the old route:** "Collapse to a remark (Recommended)": the explicit `d = 3` generic
  constructions leave, Lean and nodes, for one short remark naming the route and why C replaces it.
- **D2:** "Yes, before N3's build (Recommended)": the fresh read of Theorem S′.
- **D3:** "Both now": the premise check and the flatness reading, in parallel, before any N1 work.
- **D4:** "Bank them, geng allowed (Recommended)": the probes committed with README rows, nauty's
  `geng` the second exception to stdlib-only Python.
- **D5:** "Open as Phase 43 (Recommended)": in this session, sub-lettered, each sub-phase opened
  at the PI's word.

**PI, 2026-11-08, at LIFT3's open,** answering design doc §3's first open question ("Whether
LIFT3 lands as one sub-phase or two (N1a first)"). Question put: "Phase 43 design doc §3 leaves
LIFT3's shape to you at its open: N1a first as its own sub-phase, or N1c whole as one sub-phase
(43b)?" Chosen: "N1c whole as 43b (Recommended)" — offered as: "One sub-phase: N1a first slice,
then N1b and N1c. About −4.6k Lean lines, 17 files, 15 nodes; the d=3 route collapses to a remark
(D1)." Not chosen: "N1a alone as 43b".

**PI, 2026-11-08, after 43b's close,** asked whether anything needed discussing before 43c, was
offered four points, each with a recommendation, and answered them by number. The points as put,
in short, then the PI's words:
1. NORMAL had shrunk under LIFT3 (one caller, which already sends cases (iii)–(v) to one
   argument; the reduction would lose `n` and `hD`, and its simple two-edge-connected case its
   induction hypothesis), so: "make 43c NORMAL plus SPRIME, with NORMAL as slice 1", or NORMAL
   alone. **"Agreed, let's fold it into 43c then."**
2. `lem:pencil-min-degree-rigid` loses its last user under NORMAL: (a) a new short appendix
   chapter of results off the route, the Lean and the green node kept (recommended); (b) an aside
   in `pencil.tex`; (c) delete. **"Yes, that sounds like what I had in mind."**
3. KT Theorem 4.9 (contraction of rigid subgraphs and splitting off at degree two) has its
   counterpart in the main-component induction, not in the restated reduction: drop "cf. KT
   Theorem 4.9" from the reduction's title, put the 4.9 remark where its content is (the coverage
   or EXPO's road map), and keep one glue sentence that the reduction plays only the role of 4.9's
   outer induction. **"Sounds good."**
4. The open FRICTION entry on `check-phase-note.py --selftest` (red between sub-phases): approve
   its proposed fix and land it with 43c's open. **"Yes, let's fix it with the open."**

Then: "Let's do the opening commit of 43c with any fixes / clarifications recorded, and then hand
off to a fresh coordinate-phase session."

**PI, 2026-11-08, the same session,** answering §3's open question, which folding SPRIME into
43c brought forward. Question put: "Folding SPRIME into 43c means its open question gets answered
now (design doc §3). Theorem S′ (a core when no chain is usable) is stated today in every
dimension (thm:pencil-d-theorem-s, with def:pencil-d-usable-chain), but only d = 3 uses it; the
d ≥ 4 coverage uses 'long chain or core' instead. Keep S′ general in d, or fold it into a d = 3
statement?" Chosen: "Fold into d = 3 (Recommended)" — offered as: "One statement and one proof of
S′ in main-component.tex. thm:pencil-d-theorem-s, def:pencil-d-usable-chain, the d = 3 bridge
lemma and the formalization note go (about 80 TeX lines beyond SPRIME's −450). pencil-d.tex's
chains section loses its 'this core exists in every dimension' contrast sentence. A little more
Lean churn (specializing working code)." Not chosen: "Keep general in d".

**PI, 2026-11-08, a third session (the 43c coordinator's), reviewing SPRIME's pin,** whose one
choice taken in the PI's absence kept S′'s TeX proof on its own `d = 3` argument through
`lem:deficiency-core-bound`, rather than citing `lem:pencil-d-maximal-rigid-core` throughout as
the Lean does (which leaves `lem:deficiency-core-bound` with no user). The PI asked: "was there an
opportunity for extra simplification using the maximal-rigid-core lemma? If so, I'd go with
that." Told yes, and that the `d = 3` node and its two Lean pins (no Lean user) would then go, the
PI asked: "Would those results be independently interesting? If so we could put them in an
appendix like we have been for some others, but if not then we can lose them." Answered: no, they
are exactly the case `d = 3` of `lem:deficiency-core-bound-d`, which stays (the maximal-rigid-core
lemma uses it), so deleting them loses no result. So S′'s proof cites the maximal-rigid-core lemma,
and `lem:deficiency-core-bound` and its two declarations are deleted (`notes/Phase43c.md` item 4).

**PI, 2026-11-08, at EXPO's open** (a coordinator session after 43c's close; verbatim, the
coordinator's questions and the options as offered). First check-in. Question put:
"notes/Phase43d.md doesn't exist, and design doc §1 D5 says each Phase 43 sub-phase opens at your
word. Is this run that word to open EXPO (the road map of the pencil proof, in the manner of KT
§1.1) as 43d? The opening commit would be an Opus design pass: the note, the slice plan, and EXPO's
open items from design doc §2 (where the KT 4.9 remark goes, which chapter holds
thm:pencil-reduction, the flatness remark, the role of thm:pencil-x0-generic-attains). It would
bring any of those that need your call back to you before slice 1." Chosen: "Discuss EXPO first" —
offered as: "We go through EXPO's scope and open items here before anything is dispatched." Not
chosen: "Open EXPO as 43d (Recommended)".

Then, after the coordinator's summary of EXPO (A the reduction on five structural cases; B the
main-component induction and its steps; C the lift; why each split is forced; the stale intro.tex
sentence; one sub-phase, about 3–4 prose slices plus the close, which also closes Phase 43; Opus
throughout):
- **Q1.** Question put: "Where should EXPO's road map of the pencil proof (parts A reduction / B
  main-component induction / C lift, in every dimension) live in the blueprint?" Chosen: "Opening of
  pencil.tex (Recommended)" — offered as: "A new subsection 'Road map of the proof' right after
  pencil.tex's introduction, where the reader enters and the theorem is stated. It covers all three
  chapters; their introductions keep their section-by-section guides and point at it." Not chosen:
  "Own section first" (a short standalone section placed before pencil.tex, covering pencil.tex,
  main-component.tex and pencil-d.tex); "In intro.tex" (expand the reader's introduction's pencil
  paragraphs into the road map; the chapters stay as they are).
- **Q2.** Question put: "How much intuition should the pencil road map carry, beyond the A/B/C
  structure and the KT case correspondence?" Chosen: "Structure + intuitions (Recommended)" —
  offered as: "Also why each split is forced (K4 ⊃ C4, parallel edges, K_{2,3}, no induction on d)
  and the recon's corrected intuitions: the gap def₂ − def_d that the heights recover, degree-two
  bodies, a planar-rigid set acting like one body, slack at larger D." Not chosen: "Structure only"
  (a short map in KT §1.1's register: the three parts, their cases, and how they correspond to KT's
  Cases I–III; no intuitions).
- **Q3.** Question put: "The flatness reading: at a main picture every planar-rigid set's points lie
  in one plane, so two members of one closed hub-neighbourhood in it make the configuration
  degenerate. That explains why the generic conjunct leaves the main component. No proof uses it.
  Its argument composes five formalized lemmas plus one step done by hand. How should EXPO treat
  it?" Chosen: "Unpinned remark (Recommended)" — offered as: "A remark with no Lean, after the
  K_{2,3} paragraph of the main-component statements (or in the road map), with its argument
  written out. Includes the doubled-triangle example that the two-hubs lemma misses." Not chosen:
  "Formalize as further result" (state and prove it in Lean, as a green node in the further-results
  appendix; adds Lean work to EXPO; the coordinator had not estimated the size); "Leave it out"
  (the road map mentions K_{2,3} only; no flatness remark).
- **Q4.** Question put: "After these answers, should I open EXPO as 43d now? That means an Opus
  design pass that writes notes/Phase43d.md and the slice plan, and settles the small items with
  recommendations: which chapter holds thm:pencil-reduction, the d = 3 sentences in
  sec:pencil-d-reduction, the role of thm:pencil-x0-generic-attains, and the stale intro.tex
  sentence. It brings anything contentious back to you before slice 1." Chosen: "Open 43d now
  (Recommended)". Not chosen: "More discussion first".

**PI, 2026-11-08, this coordinator session (verbatim),** after the open's return flagged decision
D-c as the PI's optional call. The coordinator first gave verified facts: X0Dist, X0Gen, x0Dist and
x0Gen have no Lean consumer since 43b (only three docstrings outside their home files mention
them); X0.lean (49 lines) holds just the two definitions; they are not main results in
formalization.yaml (two of its notes mention them); the phrase "main-component statement" appears
19 times across pencil.tex, main-component.tex, pencil-d.tex and intro.tex; each statement is a
special case of a conjunct of the theorem itself; the attaining claim (x0Attains) that
thm:pencil-x0-generic-attains also carries stays on the route (the d ≥ 4 embedding uses it).
Question put: "The two main-component statements (X0Dist / X0Gen, proved as x0Dist / x0Gen, with
the node def:pencil-main-component-statements) are off every proof route since 43b: no Lean
consumer, and each is a special case of a conjunct of the pencil realization theorem. Keep them, or
remove them? Removing means: delete the two defs and two theorems (X0.lean whole), delete the def
node, restate thm:pencil-x0-generic-attains to its attaining claim only (which stays on route), and
reword the 19 prose mentions. No main result's statement changes."
Chosen: "Remove in 43d, before slice 3" — offered as: "One added Opus slice (Lean deletion plus
blueprint rewording), so the road map and the pointer slices never describe a detour. My estimate:
one slice; the rewording size is my guess, not measured. By your earlier test ('independently
interesting?'), they are special cases of the theorem's conjuncts."
Not chosen: "Keep them (the open's D-c)" (thm:pencil-x0-generic-attains stays main-component.tex's
summary at d = 3, its role prose saying it is off the realization theorem's route); "Remove later,
after Phase 43" (queue the removal as a cleanup round after 43d closes; EXPO's prose describes them
as they stand now).

**PI, 2026-11-08, this coordinator session (verbatim),** on the Blockers item slice 2 left.
Question put: "After the removal, main-component.tex has two nodes with the same claim and the same
Lean pin (Graph.IsX0Graph.x0Attains). One is thm:pencil-x0-coverage: every graph satisfying the
standing hypotheses reduces, and so the general configuration attains. The other is
thm:pencil-x0-generic-attains, 'The general point of the main component attains', which ends the
chapter. In the every-dimension chapter, one node, thm:pencil-d-coverage, carries the attaining
claim. What should happen to the duplicate?"
Chosen: "Fold into the coverage (Recommended)" — offered as: "Delete thm:pencil-x0-generic-attains
and repoint its citations (in intro.tex, pencil.tex, main-component.tex, pencil-d.tex) to
thm:pencil-x0-coverage, matching the every-dimension chapter. Prose only, no Lean; done in slice 5
(the main-component pointer slice)."
Not chosen: "Split the claims" (thm:pencil-x0-coverage keeps only 'every graph reduces' (pinned to
x0Reduces); thm:pencil-x0-generic-attains keeps 'the general configuration attains' (x0Attains) as
the chapter's headline. Each node then has one claim, but every citation of the coverage for
attaining has to be checked and some repointed); "Keep both" (leave the duplicate: the coverage as
the induction's endpoint, generic-attains as the chapter's titled summary).

*The coordinator's correction to that entry (not the PI's words):* the option text's "slice 5" was
the coordinator's error. After slice 2's renumbering, the main-component pointer slice is slice 4,
and the fold belongs there (`notes/Phase43d.md` item 4).

## 2. The layers, by stable code

In order. A letter is minted when a layer opens.

- **READS** (43a, closed 2026-11-07; all three held). Three read-only fresh reads, in parallel: Theorem S′ (N3, D2); the premise
  check, that `sec:pencil-d-generic` uses no `d = 3` generic node as a premise (N1, D3); and N6's
  flatness reading, every planar-rigid set flat on the main component (D3). With them, the probes
  of `notes/PencilNatural.md` §4 banked (D4). Gates LIFT3 (the premise check: no cycle, 43a) and
  SPRIME (S′).
- **LIFT3** (43b, opened and closed 2026-11-08; N1c; `notes/Phase43b.md`). **Verdict: done as
  planned**, in four slices and the close. `HasGenericPencilRealization K 3 G` is
  `liftAttains_of_simple 0` (`x0Gen`, removed in 43d's slice 2); `pencilPair_of_nonempty` is the
  `m = 1` case of `Graph.graded_pencil_conditioned_pair`; the reduction's cases are proved once, in
  `sec:pencil-d-reduction`; the explicit `d = 3` route is one remark after `thm:pencil-d-generic`'s
  proof (D1). 91 declarations and 15 nodes went, none came, and no main result's statement
  changed. The premise check (43a) found no cycle (`notes/pencil-natural/premise_closure.py`,
  `PremiseClosure.lean`). The build's inputs (the edges, the kept premises, the counts) are in
  `git show dc26fbfd:notes/Phase43-design.md`, §2.
- **NORMAL** (N2; 43c's slice 1, `2b010699`; `notes/Phase43c.md`). **Verdict: done as planned.**
  `thm:pencil-reduction` (`Graph.pencil_reduction`, moved to `Grade/Reduction.lean` beside its one
  caller, `Graph.graded_pencil_realization_theorem`) is on five structural cases: a loop; at most
  two bodies; not 2-edge-connected; not simple; simple and 2-edge-connected, the last with no
  induction hypothesis, and its statement has no `n`, `hD` or finiteness.
  `lem:pencil-min-degree-rigid` is in the new appendix `sec:further-results`, its Lean kept (§1 (b),
  and 2026-11-08 item 2); "cf. KT Theorem 4.9" left the title for one glue paragraph, the remark
  itself EXPO's (§1 (a), and 2026-11-08 item 3). The plan, with the spike
  `notes/pencil-natural/NormalSpike.lean`, is `git show b9e9e2b2:notes/Phase43-design.md`, §2.
- **SPRIME** (N3; 43c's slices after NORMAL, `27fd2c06` to `b9e9e2b2`; `notes/Phase43c.md`).
  **Verdict: done as planned, with one simplification at the PI's review.** Theorem S′ holds as Lean
  at `d = 3` (`Graph.IsX0Graph.exists_additiveCore`, its hypothesis `¬ ChainUsable` two disjuncts
  weaker), so open-ear-two and the split-off left the `d = 3` coverage (`X0Reduces` two constructors
  fewer). This revises the 42f record (`notes/Phase42-design.md` §1, "in `P³` both are
  load-bearing") to name the sense: used by Phase 40's route, not needed. S′ is stated at `d = 3`
  only (§1), so `thm:pencil-d-theorem-s`, `def:pencil-d-usable-chain` and their Lean went. Its proof
  cites `lem:pencil-d-maximal-rigid-core` as the Lean does (§1, the 43c coordinator's session), and
  `lem:deficiency-core-bound`, the case `d = 3` of the kept `-d` node, went with its two pins. NEW-1
  and NEW-2 (slice A) are the rigid-set forms of the two chain lemmas. With NORMAL, 23 declarations,
  13 nodes and three Lean files went, two declarations came, and no main result's statement changed.
  The pin's spike and walk stay banked (`notes/pencil-natural/SprimeSpike.lean`, `sprime_walk.py`)
  as its record, naming what slices B and C deleted. The read's inputs for the build (the move,
  NEW-1 and NEW-2, the sizes) are `git show b9e9e2b2:notes/Phase43-design.md`, §2.
- **EXPO** (43d, opened and closed 2026-11-08 at the PI's word, §1; `notes/Phase43d.md`).
  **Verdict: done, with two items the PI added.** The road map (`sec:pencil-roadmap`, opening
  `pencil.tex`; §1 Q1, Q2) gives the three parts in every dimension, KT's Cases (I)–(III) and
  Lemmas 4.5–4.6 against them (KT pp. 649–650, 663–667), why each split is forced (`K₄ ⊃ C₄`,
  parallel edges, `K_{2,3}`; no induction on `d` is a choice, not forced), how the parts depend on
  one another, and I1–I4 (`notes/PencilNatural.md` §5) as restated against the chapters. The
  flatness reading (F) is the unpinned `rem:pencil-x0-flatness` (§1 Q3), after the `K_{2,3}`
  paragraphs of `main-component.tex`: over a main picture every height agrees on a planar-rigid set
  with one affine function, so its points lie in one plane, the panel clause coming from the lifting
  system's coefficient vectors. The degeneracy is written in one direction only (two pencil hubs of
  one planar-rigid set, adjacent or with a common neighbour, make every configuration over a main
  picture degenerate); the converse stays probe evidence (`flatprobe.py`), and the doubled triangle
  is the remark's example that `lem:pencil-x0-two-hubs-obstruction` misses. At the PI's word (§1)
  slice 2 removed the two main-component statements (`X0Dist`, `X0Gen`, `x0Dist`, `x0Gen`, three
  lemmas only they used, `Pencil/X0.lean`, three nodes), and slice 4 folded
  `thm:pencil-x0-generic-attains` into `thm:pencil-x0-coverage`. The small items are
  `notes/Phase43d.md` D-a to D-i. The read's inputs as pinned at the open (the draft remark, and what
  LIFT3, NORMAL and SPRIME left EXPO) are `git show 0f7dad8a:notes/Phase43-design.md`, §2.

## 3. Open questions

- *Closed 2026-11-08:* whether LIFT3 lands as one sub-phase or two (N1a first). One, 43b, with
  N1a its first slice: the PI's entry of that date, §1.
- *Closed 2026-11-08:* whether SPRIME keeps Theorem S′ general in `n`, as
  `thm:pencil-d-theorem-s` is, or folds it and `def:pencil-d-usable-chain` into a `d = 3` S′.
  Folded: the PI's entry of that date, §1.
