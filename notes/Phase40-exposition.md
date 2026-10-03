# Phase 40 cleanup round 3/5 — `40-exposition`, the pencil proof explained (work log)

**Status:** in progress (opened 2026-09-30). Round 3 of the five post-Phase-40 cleanup rounds. Their
order, stops and the PI's decisions are in `notes/Cleanup40.md`, and `.claude/autopilot/queue.toml`
is the authority for which rounds are done. The round rewrites the prose of `pencil.tex` and
`main-component.tex`, and `intro.tex`'s reader path into them, so that they "explain the
mathematics clearly" and "the proof and its key ideas in context" (the PI, `notes/Cleanup40.md`
§1). Pins, `\uses` edges and statement strength stay as they are. The round also writes a
build-or-leave recommendation for eight items, which the PI decides at round 4's stop. 27
one-commit tasks, 11 landed (tasks 1–11; tasks 3 and 4 with a corrective each). **Stop 1 is
closed** (the PI, 2026-10-03), and the round runs unattended to its close. **Next concrete task:**
task 12, `sec:main-component-jj`, against the pinned exemplar
(`notes/Phase40-exposition-exemplar.md`) and defaults (a)–(f), returning per *Hand-off*'s standing
bullet. Round manual: `CLEANUP.md`.

## Autopilot: for the PI

### 2026-09-30 — `NEEDS_PI`: Stop 1, the sample section (planned stop, `notes/Cleanup40.md` §2)

**What happened.** Task 1 landed the sample (`806db52e`; the full Stop-1 entry is at
`82d806c5`): its register, defaults (a)–(d), the granularity, and "an endpoint selector" (item 4).

**PI, 2026-10-03:** (transcribed verbatim from the attended session that reviewed the sample)
- On the sample: "I think the text is a bit wordy and there are redundancies. For example, "Each
  step deduces that the general configuration of $G$ attains from the same conclusion at smaller
  graphs on the same bodies and edge labels." is already implicit when it says the proof proceeds
  by strong induction. Furthermore the text still feels a bit overwrought; I think the term is
  "mannered prose"? Could you check the style of papers in .refs/ again and try and edit the text
  to be easier to follow?"
- On allowing "we", as KT do: "Yes, and at some point we should also look into doing a rewrite
  round of the rest of the blueprint too."
- On item 4: "Right, we should be skeptical of any nonstandard terminology; certainly any such
  uses need a definition / explanation in a hard-to-miss place."
- On writing the register guidance down for tasks 3–26: "Good idea. Yes, please add guidance per
  what you found above."
- On `blueprint/AUTHORING.md` principles A and C, whose bans and citation test push toward
  stilted prose: "Hmm, I wonder if we can find some balance here?"
- On leaving the chapter introduction to task 25: "Fine, as long as it doesn't get missed."
- On `lem:pencil-splitoff-curve`, which bundles three unrelated facts: "Good catch; yes, we also
  struggled with nodes containing too much in earlier blueprint phases, I wouldn't be surprised
  if there are still some left around."
- On the first revision: "In fact the whole paragraph still seems dense and tough to follow.
  Perhaps we could lessen the detail since this is supposed to just be an overview? There are
  also sentences which have too many clauses [...] It's not even clear to me what "This" refers
  to. Can you try again?"
- On the second revision and the balance for `AUTHORING.md`: "OK, this looks much better and your
  suggested balance also sounds good."
- On the granularity: "I think the task granularity is probably reasonable if it's backed by a
  judgment that this would be most efficient and effective." Then, given that judgment (one
  commit per subsection; *Decisions*): "The granularity judgment also looks fine."
- On the defaults: "(a) agreed. In cases where the informal argument might give more insight but
  we decided not to formalize it due to technical reasons, it could be worth mentioning as well.
  (b)-(d) These look fine." Then: "Let's commit."

**What follows.** Stop 1 is closed: the exemplar is pinned (task 2), defaults (a)–(f) and the
granularity are under *Decisions*, the introduction's flags are in task 25, and **PROSE** is queued.

## Current state

**Round 3 is open** (opened at `5f9cbe04`, docs only; its Lean tree is `0b260626`'s). **Tasks 1–11
have landed**, tasks 3 and 4 with a corrective each, and nothing is mid-stream. Task 2, attended by
the PI, pinned the exemplar and settled defaults (a)–(f). Every commit so far leaves the gates at
the baseline below (graph fingerprint, pin hash, warning counts). `pencil.tex` is done but for its
introduction (task 24), and `main-component.tex`'s first two subsections are done; next is
task 12, Jackson and Jordán's equality.

**Verified at the open:**
- Whole-project `lake build` green (3003 jobs, 0 `warning:` lines). `#print axioms` on all 19
  `formalization.yaml` main results gives the standard three, through round 2's harness copied to
  `scratch/40-exposition/Axioms.lean` (gitignored; its names and imports diffed against
  `formalization.yaml`, identical). Re-run it the same way at the close.
- **The blueprint baseline** every slice compares against: `lint.sh` and `verify.sh` green
  (`checkdecls` silent, 9 `WARNING:` lines, all plasTeX notices); 0 `LaTeX Warning` lines and 187
  overfull boxes in `blueprint/print/print.log`; 1 062 pins, hash `36133299d3fcc3c8`; 668 nodes
  and 1 308 edges, fingerprint `6c5064b7034feb95`, stable across runs (commands: *Scope*, gate 3).
- **The surface.** `pencil.tex` 1 411 lines, 10 subsections, 41 nodes; `main-component.tex` 4 858
  lines, 14 subsections, 123 nodes; `intro.tex` 471 lines. Line numbers below are the open's; the
  labels are the stable reference.

**What the inventory found** (seen at the open; each task re-derives its own findings):
- **An unintroduced "informal argument."** 23 lines of prose compare with the project's workbook
  (`notes/pencil/workbook/K-main*.md`), which the blueprint never introduces; default (a) rules.
- **Proofs that rest on lemmas stated later**, and a statement citing a later definition: tasks 10
  and 14 name each one and cure it (task 5 cured its one).
- **Nodes outside the headline's closure.** On the dependency graph, 21 of `pencil.tex`'s 41 nodes
  (placed by tasks 3–8) and 2 of `main-component.tex`'s 123 (`thm:pencil-x0-main-component`,
  `thm:pencil-x0-closed-ear`) lie outside the closure of `thm:pencil-conjecture`. Liveness is a
  property of the Lean call chain (`CLEANUP.md` §B), so a task confirms it there before its prose
  calls anything "off the proof".
- **Mathematics in the wrong place.** Lean names sit inside statement blocks: `def:pencil-ear-data`,
  `lem:pencil-ear-data` and `lem:pencil-ear-data-open` (task 16).

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2, restated only as far as a builder needs them:

- **Surface.** `pencil.tex`, `main-component.tex`, and `intro.tex`'s reader path into them (lines
  44–47, 362–392 and 406–407), all in `blueprint/src/chapter/`. No Lean edits, and no other
  chapter's TeX: a finding elsewhere goes to *Moved to a later round* or *Candidates*.
- **Prose only** (Phase 28's rule).
  - What does not change: every node's `\label`, `\lean{…}` pins, `\leanok` and `\uses` edges,
    and the strength of its statement. A statement block may be edited for register or
    anchoring only.
  - A finding that would change a headline or blueprint statement's strength goes to
    *Candidates for `40-simplify`*. It is not acted on and it is not a stop.
  - A dependency edge the graph lacks is not added either: record it under *Moved to a later
    round*, with target `40-simplify`.
  - A node may move within its chapter to cure a forward reference, per *Decisions* (d).
- **Evidence.**
  - Citations follow `CLAUDE.md` *Referencing prior work*. The primary sources are in `.refs/`,
    read as `REFS.md` says: KT 2011 (the journal version), Crapo–Whiteley 1982 and Whiteley 1996.
    For Jackson–Jordán 2008 only the technical report is there (EGRES TR-2006-06, 31 August
    2006): check against it, and cite `\cite{jacksonJordan2008pin}` with no claim or section
    number unless the published text has been checked. Name the TR passage in the commit
    message.
  - No new bib entry unless it has been verified as `blueprint/AUTHORING.md` *Citations* asks.
  - A claim about the Lean is read from the declaration's statement and body, never from its
    docstring or from blueprint prose (`CLAUDE.md` *Docstrings are not evidence*).
  - The workbook is a source for the argument, never a citation.
- **Conventions.** `blueprint/CLAUDE.md` (it auto-loads on the TeX) and `blueprint/AUTHORING.md`:
  principles A–F with the R-task order, and the terminology dictionary. The audience is a
  rigidity theorist who knows KT and JJ and has not seen the project's notes.
- **Gates for every section slice** (blueprint commits; this round edits no Lean). Run each in the
  foreground with an explicit `timeout`.
  1. `blueprint/lint.sh` green: references, citations, supersession, hanging pins, vocabulary.
  2. `blueprint/verify.sh` green: `inv bp`, `inv web`, and `lake exe checkdecls` silent.
  3. **The invariance check**, run from the repository root after `verify.sh`. Both values must
     equal the open's (*Current state*):
     ```sh
     python3 -c "import re,hashlib;g=open('blueprint/web/dep_graph_document.html').read();g=g[g.find('digraph'):];g=g[g.find('{')+1:g.find('}')];s=sorted(filter(None,(re.sub(r'\s+',' ',x).strip() for x in g.split(';'))));print(sum(' -> ' in x for x in s),'edges',hashlib.sha256('\n'.join(s).encode()).hexdigest()[:16])"
     sort blueprint/lean_decls | shasum -a 256 | cut -c1-16
     ```
  4. No new warnings: 0 `LaTeX Warning` lines in `blueprint/print/print.log`, and 9 `WARNING:`
     lines in the output of `verify.sh`.
  5. On a commit that edits a phase note, `python3 notes/check-phase-note.py` exits 0. Its pattern
     does not match this log's name, so this log is kept forward-weighted by hand: under ~500
     lines, *Decisions* shorter than the forward sections, each entry at most 8 lines.

  Every commit also gets `blueprint/CLAUDE.md`'s friction review and updates this log: its
  checklist line, *Current state* and *Hand-off*. Where a task names a build-or-leave item, it
  also fills that item's recommendation.

## Lemma checklist (the round's task list)

One commit per task, in the order given. Each task's diagnosis says what the unit needs in order
to explain the mathematics and the proof's key ideas in context. The line ranges are the open's.

- [x] **1. S — the sample, `sec:main-component-splitoff`** (`806db52e`; pinned by task 2). Its JJ
  paragraph is checked against the TR (Theorem 6.1, Claim 6.5, Case 1, pp. 15–16).
- [x] **2. E — pin the exemplar** (attended, with the PI, 2026-10-03; *Autopilot*, *Decisions*).
- [x] **3. P1 — `pencil.tex`'s opening subsections** (`99a3e639`, then a corrective). The pencil
  picture and the molecular reading lead in; `lem:pencil-self-dual` is put off the proof. *(f):* for
  task 25, "the pencil condition" ("the point condition" is left to task 23). Four forward `\cref`s.
- [x] **4. P2 — base, cycle and extension** (`6bc95de3`, then a corrective). The base case leads;
  `lem:cycle-coplanar-realization` follows its `\uses` target; `sec:pencil-cycle`'s two lemmas serve
  no case (edge: *Moved*). *(f):* new, *cross-incidence(s)*. Nine forward `\cref`s.
- [x] **5. P3 — `sec:pencil-reduction`** (`96eda8e2`). A roadmap; the cut-edge reason; loop and base
  cases live (edges: *Moved*); KT Theorem 5.6's route, its `K_4` failure, KT Lemmas 4.5–4.6. *(f):*
  in a node, *deficiency rank*. Forward `\cref`s into `sec:main-component`.
- [x] **6. P4 — `sec:pencil-nondegenerate`** (`58fc3a52`). Conditioning in prose (KT p. 668,
  Theorem 5.5); the pair theorem's two results in the lead-in (edges, splitting: *Moved*,
  *Candidates*). *(f):* in a node, *pencil hub*, *nondegenerate*, *adjacent-distinct*, *conditioned
  pair*, kernels (K), (K-bare) and three more; four removed. Five forward `\cref`s.
- [x] **7. P5 — `sec:pencil-main-component-route`** (`1010c804`), retitled *Reduction to the main
  component*: its one idea; `lem:pencil-nonsimple-case` kept (KT Lemma 6.2, p. 673); the JJ paragraph
  left to task 12. *(f):* for task 25, *main component*. Nine forward `\cref`s.
- [x] **8. P6 — `sec:pencil-girth-chain`** (`694d892e`). Outside the closure, confirmed in the Lean;
  kept as results under their hypotheses; the two-cut composition cut (item 2 written);
  `def:girth`'s false clause cut. Three forward `\cref`s.
- [x] **9. M1a — the carrier, first half** (`a23508c0`). The lifting idea leads (Whiteley 1996
  §8.3, checked); `lem:pencil-condition-linear` follows `lem:pencil-config-distinct-realization`.
  *(f):* for task 25, *standing hypotheses*; *selector* removed. Eight forward `\cref`s.
- [x] **10. M1b — the carrier, second half** (`a5f782a5`; full entry there). Every step's pin uses
  `Graph.x0Attains_of_exists`; the fibre lemma is outside 5 of the 15 step pins' closures (measured,
  script not retained), so the opening says *most* steps need it. The one-witness proof states the
  polynomial section in general; nodes moved to cure forward `\uses`; `rem:pencil-hinge-affine` cut
  (default (a)). *(f):* for task 25, *main component*, *pencil configuration space*; removed,
  *endpoint selector*, *point-join rank*, *Cramer section*. Nine forward `\cref`s.
- [x] **11. M2 — `sec:main-component-flat`.** Every diagnosis bullet done, one corrected:
  - *Roadmap: done.* The opening says what is proved and why, the idea, Crapo–Whiteley's picture,
    then the order. `lem:pencil-flat-split` (retitled) moves after `lem:pencil-lifting-planes-dim`,
    curing its note's forward `\cref` (default (d)).
  - *Citations: checked.* Crapo–Whiteley Example 4.4 (pp. 72–73): a flat tetrahedron's panel
    motions give the tetrahedra over it, "true in great generality". Whiteley 1996 §8.3 is cut
    here; the opening points back to the carrier's liftings.
  - *The split's idea: done*, in the opening: the hinges lie in `z = 0` and glue the complementary
    screws; the screws of the plane's lines are affine functions (over the reals, normal velocities).
  - *Why it matters: corrected.* Equal deficiencies is clause (1) of `def:pencil-x0-reduces`, but
    the coverage's third case (its proof; `Graph.IsX0Graph.x0Reduces`). So the opening says it
    settles "one case of the induction with no appeal to smaller graphs" (`cor:pencil-jj-flat`).
  - *Item 8: written* (below). Also: `cor:pencil-flat-attains` says "has rank" (*attains* is the
    general configuration's), and `cor:pencil-flat-x0` drops "the main component is flat".
  - *(f):* in a node, *lifting planes*, *flat rank*, *flat lower bound*, `P_q`, *deficiency rank*;
    for task 25, *flat configuration*, `def₂`, `def₃`; removed, *flat split*, *flat main component*.
    Forward `\cref`s: `cor:pencil-jj-flat`, `thm:pencil-jj-equality`, `sec:main-component-coverage`,
    `sec:main-component-contract`; from the opening to its own `lem:pencil-flat-split`,
    `def:pencil-lifting-planes`, `lem:pencil-lifting-planes-dim`,
    `lem:pencil-lifting-planes-motions`, `cor:pencil-flat-attains`.
- [ ] **12. M3 — `sec:main-component-jj`, 943–1101.**
  - Say what JJ's theorem is in their own terms (pin-collinear body-and-pin frameworks), and why
    it is the equality used here, checked against the TR.
  - Say why it is derived afresh: their frameworks are real, and here the field is any infinite
    field.
  - Keep the relabelling terse; it is Lean-side.
  - **Writes items 4 and 7's recommendations.**
- [ ] **13. M4 — `sec:main-component-cut`, 1102–1328.** The subsection opens with "The steps of the
  induction share one shape": one picture generic for the smaller graphs and main for `G`, the
  heights in one fibre, two open conditions meeting, and one witness sufficing. Seven subsections
  rest on that template. Display it here once, for later subsections to cite rather than
  re-derive. The four "Informally …" remarks fall under default (a), and are item 3's text. Not
  every step meets two open conditions (task 10 checked the Lean; its entry names the five).
  **Writes item 3's recommendation.**
- [ ] **14. M5 — `sec:main-component-contract`, 1329–1631.** The preamble packs the argument into
  a paragraph.
  - Give an overview of four things. The curve: the core shrinks to `r`'s point, the placement of
    KT eq. (6.7). The rescaling: the core heights are magnified by `1/t`, so the core's rows do not
    depend on `t`. Why the kernel not jumping at `t = 0` is the crux: it gives a polynomial section
    through the limit. What planar deficiency zero buys: the core has one plane.
  - Check the KT pinpoints: §6.2, Lemma 6.3, Claim 6.4, eqs. (6.3), (6.5), (6.7) and (6.9), and
    pp. 674–675.
  - Move `lem:pencil-contract-kernel-bound` and `lem:pencil-contract-standing-rigid` here,
    before their first use. The closing remark falls under default (a).
  - From task 10: the one-witness proof now states the polynomial section in general. Cite that
    statement rather than re-derive it.
- [ ] **15. M6 — `sec:main-component-chain`, 1632–1966.**
  - The ear rank formula, `lem:block-rank-ear`, organizes all three ear subsections but is stated
    inline. Display it, with `ρ` and `Λ` explained.
  - Put the key idea before the proof rather than in a remark: one certifying point suffices, and
    it may lie over a degenerate picture, provided its heights are heights of `G`.
  - Keep in view that the coverage never uses `thm:pencil-x0-closed-ear`. The remark after the
    open-ear theorem falls under default (a).
  - **Writes item 1's recommendation.** `lem:block-rank-two-cut` lies behind the ear formula.
- [ ] **16. M7a — `sec:main-component-short`'s toolkit, 1967–2261.** `def:pencil-line-pairing`
  through `lem:pencil-ear-data-open`; 11 nodes.
  - The pairing, `⟨p∧q, r∧s⟩ = det(p, q, r, s)`, stars and plane lines are classical line
    geometry: the Plücker bilinear form, under which two lines meet exactly when they pair to
    zero. Name it and cite it after checking, or call it classical.
  - The preamble's case analysis for `k = 3` runs ahead of its definitions.
  - Move the Lean names out of the ear-data statement blocks.
- [ ] **17. M7b — SHORT's three steps, 2262–2583.** `thm:pencil-x0-open-ear-two`, `-four`,
  `-three`, and four remarks.
  - State the idea before the proofs. Count against `G″`, then put `x₂` back on a line through a
    neighbour: this gains a dimension unless `W` holds every line through `x₁` and `x₃`, and then
    `W` is everything (the tetrahedron, or the split on `ρ`).
  - The remark after the four-body step compares with the informal argument: default (a).
  - **Writes item 5's recommendation.**
- [ ] **18. M8 — `sec:main-component-orbit`, 2584–2951.**
  - The key ideas sit in the closing remark; lead with them. The one-body ear picks `x₁`'s
    picture together with the heights, as a point of their incidence. The two-body step counts
    against `G₁`, and gains a dimension because `p_a, y, u₀, p_b` form a tetrahedron.
  - The preamble packs what the planar merged hypothesis gives (each end's point off the other
    end's plane, `lem:pencil-flag-genericity`) into one chain of clauses: unpack it.
  - Check `fmlnote:pencil-flag-genericity` against principle D.
- [ ] **19. M10 — `sec:main-component-contract-additive`, 3274–3568.**
  - Lead the proof with the key idea: under additivity the two bounds on `ker M(0)` meet, so the
    core heights of its solutions are all of `L_H(q)`. This replaces the dominance of restriction
    to the core.
  - The remarks fall under default (a). The claim of a reverse inequality "for every `W`" is not
    proved here.
  - Re-read the subsection after tasks 10 and 14 move its lemmas out.
- [ ] **20. M11 — `sec:main-component-sparse`, 3569–3894.** Singleton-value combinatorics.
  - Three proofs compare with "the partition into maximal rigid sets". Check whether that is
    Jackson–Jordán's brick partition (the TR) before naming it; those remarks fall under default
    (a). From task 1 (TR §3, pp. 7–8): their bricks are the maximal subgraphs with `def₂ = 0` in
    this chapter's terms, not `def₃ = 0`, and "brick" is lint-banned in chapter prose.
  - Say in words what "sparse" and "tight" mean here.
- [ ] **21. M12 — `sec:main-component-coverage`, 3895–4329.** The proof's combinatorial skeleton.
  - A displayed table would let the reader check that the cases are exhaustive: each case, the
    step that settles it, and the smaller graphs it consumes.
  - `thm:pencil-x0-theorem-s` needs an overview: every chain is short, a short chain gives a rigid
    set, and a maximal one is the additive core.
  - Two "informal" remarks fall under default (a).
  - **Writes item 6's recommendation.**
- [ ] **22. M13a — `sec:main-component-statements`, first half, 4330–4559.** The two-hubs
  obstruction is why the generic statement leaves the main component. Work it at `K_{2,3}`, and
  anchor the unlabelled paragraph after it (4439–4445). The base case's idea needs an overview
  before `lem:pencil-x0-planes-separate`'s partition count: without a planar-rigid set, JJ's
  equality at `G` and at `G_{uw}` separates two bodies' planes. The preamble's comparison with the
  informal argument falls under default (a).
- [ ] **23. M13b — the statements' second half, 4560–4858.**
  - Motivate `lem:pencil-generic-steer` first: nondegenerate realizations are chart points, so
    the smaller graph's generic realization can meet the new bodies' finitely many open
    conditions.
  - `thm:pencil-x0-generic-attains`'s proof repeats the subsection preamble: keep one account.
  - The good-ear lemma's closing remark falls under default (a).
  - Name the direct construction on three bodies that `thm:pencil-generic-step` borrows.
- [ ] **24. F1 — `pencil.tex`'s introduction, 1–37.** One dense paragraph now; principle F asks for
  a half-page roadmap.
  - What is proved and in what order.
  - What the reader needs from earlier chapters: `sec:molecular-coplanar-multigraph`, the
    deficiency, the polarity.
  - Which parts are off the proof: the kernel forms and the girth-chain subsection.
- [ ] **25. F2 — `main-component.tex`'s introduction, 1–122.** It is Phase 40's close-time outline,
  the account `notes/BlueprintExposition.md` records as written.
  - Re-read it against the rewritten subsections.
  - Add a notation paragraph: `def₂`, `def₃`, `tgt`, attaining, the standing hypotheses, `ρ`, `Λ`
    and `(⋆)`.
  - Name the two tools every step uses.
  - Default (a), as ruled, leaves nothing that names "the informal argument". Confirm with
    `grep -in informal` over the round's surface, and that each kept mention reads on its own.
  - From task 1: the split-off sentence (78–84) says the body "starts on the line through the
    points of its neighbours" *as in* JJ's proof. The TR does not: JJ move the new pin, then
    reinsert the vertex by extensions. Match `sec:main-component-splitoff`'s account.
  - **The PI's flags (2026-10-03; "as long as it doesn't get missed").** The introduction is
    wordy and repeats itself. Their example, "Each step deduces …", restated the strong induction
    and is already cut. *The induction* paragraph packs the whole case analysis into one
    paragraph: split it. Apply defaults (e) and (f) throughout. The notation paragraph is where
    the chapter's coinages are defined (default (f)).
  - From task 9: the carrier's opening now sketches the lifting idea and the one witness, so *The
    main component* paragraph (15–41) can shrink to pointers.
  - From task 11: *The flat rank* paragraph's "the flat configuration attains" misuses the term;
    the general configuration attains (`cor:pencil-jj-flat`), a configuration *has* a rank.
- [ ] **26. F3 — `intro.tex`'s reader path.** The fifth-continuation paragraph (362–392) runs the
  whole arc in one paragraph. Check each sentence against tasks 24 and 25, and split it where it
  joins two results. Lines 44–47 and 406–407 get the same check. Phase numbers are allowed here.
- [ ] **27. X — close the round** (`CLEANUP.md` *Workflow* rule 5; docs only).
  - **Gates.** `lake build` and `lake lint` green. The harness is re-diffed and re-run: 19 of 19
    at the standard axioms.
  - **The blueprint.** `verify.sh` and `lint.sh` green; the invariance fingerprints equal the
    open's; the warning counts are unchanged.
  - **Stop 2's inputs.** The build-or-leave table has no *pending* slot. Mirror it, one line per
    item, and the *Candidates*, into `notes/Cleanup40.md` §2 *Round 4*.
  - **The ledger.** Check the pointers of `notes/BlueprintExposition.md`'s `pencil.tex` and
    `main-component.tex` entries against the new text, and add a one-paragraph round note.
  - **Status surfaces.** The ROADMAP row reads ✓ Complete. The queued bullet and
    `notes/Cleanup40.md`'s **Status** name opening round 4.
  - **The queue.** `40-exposition`'s row in `.claude/autopilot/queue.toml` gets `done = true`,
    and nothing else there changes.

## The build-or-leave items (recommendations for round 4's Stop 2)

From `notes/Cleanup40.md` §2 *Round 3*. Each gets one recommendation: build it, add its blueprint
node, refactor around it, or leave it with a recorded reason. The task named writes it, once the
exposition has made the item's role clear. The PI decides at round 4's stop.

1. **The D5 blueprint debt.** Of the 40 names in `notes/Phase40-design.md` §7's list, nine are
   pinned; 31 have no node. *Task 8 read all 40 in the Lean* (the closure of both headlines' types
   and values; measured, script not retained). 11 are live: seven pinned names (not the two pins of
   `cor:block-rank-vertex-two-cut`) and four unpinned helpers (`bddAbove_range_partitionDef_merged`,
   `span_jointRows_eq_map_dualAnnihilator`, `finrank_span_jointRows`, `map_screwDiff_comm`). The
   other 29, `TwoCut.lean`'s nine included, feed neither headline; item 2's reason may carry over.
   Role: task 8 (the two-cut composition) and task 15 (the ear formula). *Recommendation: pending*
   (task 15).
2. **A6, the welded pendant law, and item 6's other deferred laws.** These are S7(i), S7(ii),
   S7(iii), S7(v) and S9, all unbuilt. Role: task 8. *Recommendation (task 8): leave them unbuilt,
   with no node.* They belong to the two-cut composition, an unfinished attempt at kernel (K-bare):
   split `G` at case (3)'s `{w, w'}` and combine the sides' deficiencies
   (`Graph.deficiency_eq_of_vertexTwoCut`) and ranks (`cor:block-rank-vertex-two-cut`), as
   `pencilLoss_vertexTwoCut` does. In the Lean that composite has no caller, and the kernels are
   hypotheses only of three declarations off the proof: a build gains no caller. Nor are these laws
   its gap. A6 reduces at a side end of degree one, but both ends keep degree two or more
   (`lem:pencil-chain-side-connected`); the S7/S9 laws are not consumed; it lacks ear-profile facts
   and a variety layer (`notes/Phase39-design.md` *Item-6 carrier recon*). From the cut remark:
   it covers case (3) only, and case (2) falls to the induction's cut-vertex case.
3. **The "only if" halves of (MC-52)/(MC-53).** Unbuilt; stated informally in the remarks after
   `thm:pencil-x0-cut` and `thm:pencil-x0-bridge`. Role: task 13. *Recommendation: pending*
   (task 13).
4. **The edge-restricted, non-spanning generic-normals row rank** (design §3 BRIDGE). Three
   declarations, compiled by a recon and not landed; the chart route of `lem:pencil-jj-chart`
   never uses them. Role: task 12. *Recommendation: pending* (task 12).
5. **SHORT's shared assembly**, `Graph.X0Attains.of_openEar_splitOff` and
   `Graph.exists_earBase_splitOff` (`Short.lean`). Called only by the three- and four-body steps.
   Role: task 17. *Recommendation: pending* (task 17).
6. **The CHAINS pair**, `Graph.IsOpenEar.exists_maximal` (`CoverageChain.lean`) and
   `Graph.Connected.induce_of_gate` (`CoverageCut.lean`). Role: task 21. *Recommendation: pending*
   (task 21).
7. **`Graph.exists_isMinimalKDof_spanning_subgraph`** (`Molecular/Deficiency.lean`). It has four
   call sites in `AlgebraicInduction/Theorem55.lean`, behind `thm:theorem-55-6-genuine` and
   `thm:theorem-55-6-rows` (`panel-layer.tex`), which `lem:pencil-jj-chart` consumes. Role:
   task 12. *Recommendation: pending* (task 12).
8. **`Graph.exists_normalized_labeling`** (`Molecular/Deficiency.lean`). It is the relabelling
   inside `lem:relative-deficiency-rank-bound` (`rigidity-matrix.tex`), which
   `lem:pencil-lifting-space-deficiency` uses. Role: task 11. *Recommendation (task 11): leave it
   unpinned, with no node.* Read in the Lean, it has two callers: the hub pinned at
   `lem:relative-deficiency-rank-bound`, on the proof (the flat lower bound's pin calls it, and the
   split-off step calls that), and the merged hub of `TwoCut.lean`, which only the library root
   imports. It serves the encoding: a partition is a self-map of the body type, the bound counts
   the map's range, and the relabelling makes each body off `V(G)` its own part (with no body off
   `V(G)`, the hub needs none). That proof says so in a clause. A node would hold only the
   encoding; at most a later round names it there, as `40-cleanup` task 43 named item 7's strip.

A node these items might gain would sit in `deficiency.tex`, `rigidity-matrix.tex` or
`panel-layer.tex`, outside this round's surface. The round only recommends.

## The pinned exemplar

In its own file, `notes/Phase40-exposition-exemplar.md` (task 2, 2026-10-03). Every builder of
tasks 3–26 reads it. It is altered only to correct a verified factual error.

## Candidates for `40-simplify`

Structural findings, and any finding that would change a headline or blueprint statement. They are
recorded here and never acted on in this round (`notes/Cleanup40.md` §2). The close (task 27)
mirrors them, one line each, into `notes/Cleanup40.md` §2 *Round 4*.

- **`lem:pencil-splitoff-curve` bundles three unrelated facts** (seen at Stop 1; the PI agreed,
  2026-10-03). They are a linear-algebra lemma, the extension of a height across `x`, and the
  locality of the lifting system, under three pins. Splitting the node changes the dependency
  graph, so this round leaves it. The PI expects more such nodes in earlier chapters; that audit is
  queued with **PROSE** (ROADMAP).
- **`thm:pencil-reduction` is stronger than its pin** (task 5). It gives cases (iii)–(v) the
  property at every lexicographically smaller graph; `Graph.pencil_reduction`'s `hcut`, `hcontract`
  and `hsplit` get it only at graphs with fewer vertices. Matching them changes the statement.
- **`thm:pencil-conditional-realization-pair` is two results** (task 6). Its first pin,
  `pencil_conjecture_of_arms_pair`, is the live reduction with the contraction and split cases as
  hypotheses; its statement and other two pins are the kernel form, off the proof. Splitting it
  changes the graph.
- **…and its statement is stronger than its pins** (task 6). Kernel (K) is assumed only at a
  nondegeneracy-feasible `G`, while `hK` has no such antecedent. "Strictly smaller", read in
  `thm:pencil-reduction`'s order, also gives more than the pins' fewer vertices (likewise in
  `thm:pencil-conditional-realization`).
- **`lem:pencil-selector-independent-scalar` assumes an admissible picture** (task 9); its pin
  does not. Dropping the hypothesis would raise the statement to the pin's strength.
- **`lem:pencil-condition-linear` restates another lemma** (task 9's return, checked by task 10).
  Its clause "`p` gives a pencil realization whose adjacent points are distinct" is
  `lem:pencil-config-distinct-realization`'s content. Neither pin proves it:
  `mem_liftingSpace_of_coplanar` is the converse direction alone, `exists_smul_eq_interpolant` the
  plane's normal. The forward direction is `lem:pencil-selector-plane-contains-nbhd`'s pin.
- **`lem:pencil-x0-main-picture-open` claims more than its pins** (task 10). "In particular `U` is
  … Zariski-open" does not follow from its polynomial, and `Graph.exists_mvPolynomial_isMainPicture`
  gives only a nonempty open subset of `U`. `U` is open (admissibility and `dim ker M(q) ≤ ℓ₀` are),
  but nothing here proves it.

## Moved to a later round

Each line gives the task, its target round, and a one-line reason. The same line goes into the
target round's plan section in `notes/Cleanup40.md` in the same commit.

- **Task 4, target `40-simplify`.** `def:pencil-nondegenerate`'s hub threshold rests on
  `lem:coplanar-hinges-concurrent` (cited before task 6 in a note, now in the lead-in through
  `sec:pencil-realization`), with no `\uses` edge to it.
- **Task 5, target `40-simplify`.** Only the off-route `thm:pencil-conditional-realization` has
  `\uses` edges to `lem:pencil-loop-case` and `lem:pencil-base-case`. The live route uses them
  through the pins of `thm:pencil-conditional-realization-pair` and
  `thm:pencil-conditioned-pair-nonempty`.
- **Task 5, target `40-simplify`.** `lem:pencil-simple-of-noRigid` has no in-edge, though
  `thm:pencil-generic-step`'s pin calls it through the unpinned three-body construction.
- **Task 6, target `40-simplify`.** `thm:pencil-conditional-realization-main-component` has no
  `\uses` edge to `thm:pencil-conditional-realization-pair`, though its proof applies the
  reduction as in it and its pin calls `pencil_conjecture_of_arms_pair`.
- **Task 6, target `40-simplify`.** `thm:pencil-conditional-realization-pair`'s two notes sit
  between its statement and proof, so plasTeX attaches the proof to a note and the graph draws the
  node unfilled. Moving them after the proof fills it (the graph's one changed line); the only case.

## Blockers / open questions

- None. Stop 1 is closed (2026-10-03). The round's next planned stop is round 4's Stop 2.

## Hand-off / next phase

**Next: task 12** (checklist above has its scope); then tasks 13–26 in order,
and task 27 closes the round. Each section task reads the pinned exemplar (`notes/Phase40-exposition-exemplar.md`),
defaults (a)–(f) under *Decisions*, and `blueprint/AUTHORING.md`'s clauses of 2026-10-03.

- **Standing, for every section task (4–26)** (from task 3's corrective). Its return and its
  checklist entry (i) answer every diagnosis bullet of the task: done, not done with the reason, or
  moved per *Moved to a later round*; (ii) carry the section's (f) coinage list, each coinage
  marked standard, defined in a node, or left for task 25's notation paragraph; (iii) name every
  forward `\cref` it adds.

## Decisions made during this round

- **2026-09-30, the open: the sample is `sec:main-component-splitoff`** (a typical step, with a JJ
  citation).
- **The task list** (the PI approved it, 2026-10-03). One commit per subsection, split or grouped
  at natural seams into slices of 150–430 lines, near the sample's 322. The introductions and
  `intro.tex` come last (principle F): each summarizes what precedes it.
- **Round-wide default (a), as the PI ruled and amended (2026-10-03; verbatim under *Autopilot*).**
  Cut every comparison with the workbook's informal argument. A reason the proof is shaped as it
  is stays, stated on its own. So does an argument that gives more insight but was not formalized
  for technical reasons (the PI): a short remark or formalization note, with that reason. A
  stronger fact not proved here is cut unless a reader would expect it; then one sentence says the
  proof needs only the weaker form. A remark that carries a build-or-leave item is cut only after
  that item's recommendation records the fact.
- **Defaults (b)–(d)** (the PI approved them as drafted). (b) A formalization note keeps only what
  the Lean does differently. (c) A Lean name never appears in a statement block. (d) A node may
  move within its chapter to cure a forward reference.
- **(e) The register, and (f) terminology** (the PI, 2026-10-03, Stop 1). Every task follows
  `blueprint/AUTHORING.md`'s clauses of that date. They are A *Voice and sentences* ("we" as KT
  write it, one idea per sentence, no unasked questions), C's indexing test limited to proofs, F
  *Once* (one sketch per subsection, no lead-in that restates a node), and E *Terminology*. Under
  (f) each task lists its section's project coinages. Each one is replaced by the standard term,
  or defined in a definition node or in task 25's notation paragraph.
- **The invariance check** (gate 3). `checkdecls` and `lint.sh` cannot see a changed `\uses` edge
  or `\leanok`; the sorted hash of `inv web`'s graph can, and ignores node order, so a move passes.
- **Formalization notes** (task 6's reading of *Scope*, which protects nodes' labels). A note left
  with no Lean divergence is deleted, label and all, as a note is not a graph node. A note stays on
  its side of a proof: plasTeX attaches a proof to the environment just before it.
- **Rungs.** Tasks 3 and 4 ran Sonnet, and each needed an Opus corrective for a gate-invisible
  claim about other sections. From task 5 every section task runs Opus, fresh per task
  (coordinator, 2026-10-03; `notes/dispatch-log.md`).
