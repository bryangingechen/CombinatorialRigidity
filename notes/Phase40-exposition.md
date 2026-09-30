# Phase 40 cleanup round 3/5 — `40-exposition`, the pencil proof explained (work log)

**Status:** in progress (opened 2026-09-30). Round 3 of the five post-Phase-40 cleanup rounds. Their
order, stops and the PI's decisions are in `notes/Cleanup40.md`, and `.claude/autopilot/queue.toml`
is the authority for which rounds are done. The round rewrites the prose of `pencil.tex` and
`main-component.tex`, and `intro.tex`'s reader path into them, so that they "explain the
mathematics clearly" and "the proof and its key ideas in context" (the PI, `notes/Cleanup40.md`
§1). Pins, `\uses` edges and statement strength stay as they are. The round also writes a
build-or-leave recommendation for eight items, which the PI decides at round 4's stop. 27
one-commit tasks, 1 landed: task 1, the sample section `sec:main-component-splitoff`. **Next
concrete task:** Stop 1, the PI's review of the sample, which the coordinator writes; no other
section is written before the PI's entry. Then task 2 pins the exemplar. Round manual:
`CLEANUP.md`.

## Current state

**Round 3 is open** (opened at `5f9cbe04`, docs only; its Lean tree is `0b260626`'s). **Task 1,
the sample, has landed** (this commit): `sec:main-component-splitoff` is rewritten, its record is
under *Lemma checklist*, and nothing is mid-stream. Its gates: `lint.sh` and `verify.sh` green,
`checkdecls` silent; the graph fingerprint (1 308 edges, `6c5064b7034feb95`) and the pin hash
(`36133299d3fcc3c8`, 1 062 names) equal the open's; 0 `LaTeX Warning` lines, 187 overfull boxes
and 9 `WARNING:` lines, as at the open. Next is Stop 1, then task 2.

**Verified at the open:**
- Whole-project `lake build` green, 3003 jobs, 0 `warning:` lines, 0 `failed to cache artifact`
  (the full output, grepped).
- `#print axioms` on all **19** `formalization.yaml` main results gives `[propext,
  Classical.choice, Quot.sound]`. The harness is round 2's `scratch/40-factor/Axioms.lean`, copied
  to `scratch/40-exposition/Axioms.lean` (gitignored) after its 19 names (in order) and 14 imports
  (as a set) were diffed against `formalization.yaml`'s `declaration:` and `file:` fields
  (identical), and run with `lake lean`. The output equals round 2's close, up to the scratch
  path; the one warning is the harness's own over-long line. Re-run it the same way at the close.
- **The blueprint baseline**, which every section slice compares against:
  - `blueprint/lint.sh` green. `blueprint/verify.sh` green: `checkdecls` silent, and 9 `WARNING:`
    lines in its output, all plasTeX package and renderer notices.
  - `blueprint/print/print.log`: 0 `LaTeX Warning` lines; 187 overfull boxes, recorded for
    information.
  - `blueprint/lean_decls`: 1 062 names, pin hash `36133299d3fcc3c8`.
  - The dependency graph: 668 nodes and 1 308 edges, fingerprint `6c5064b7034feb95`. It was
    identical on a second `verify.sh` run. The commands are under *Scope*, gate 3.
- **The surface.** `pencil.tex` has 1 411 lines, 10 subsections and 41 graph nodes;
  `main-component.tex` has 4 858 lines, 14 subsections and 123 nodes; `intro.tex` has 471 lines.
  Line numbers below are as of the open. The labels are the stable reference.

**What the inventory found** (seen at the open; each task re-derives its own findings):
- **An unintroduced "informal argument."** 23 lines of reader-facing prose (19 in
  `main-component.tex`, 4 in `pencil.tex`) compare with "the informal argument" or "statement".
  That is the project's workbook `notes/pencil/workbook/K-main*.md`, which the blueprint never
  introduces or cites (principle E). The round-wide default is under *Decisions*.
- **Proofs that rest on lemmas stated later.** `lem:pencil-rank-scale-shift` rests on
  `lem:pencil-rank-collineation`, `lem:pencil-contract-standing` on
  `lem:pencil-contract-standing-rigid`, and `lem:pencil-contract-core-plane` and
  `lem:pencil-contract-limit` on `lem:pencil-contract-kernel-bound`; all three are stated in
  `sec:main-component-contract-additive`. In `pencil.tex`, `lem:pencil-cut-case`'s statement cites
  the next subsection's `def:pencil-distinct-motive`. Tasks 10, 14 and 5 cure these.
- **Nodes outside the headline's closure.** On the dependency graph, 21 of `pencil.tex`'s 41 nodes
  and 2 of `main-component.tex`'s 123 lie outside the closure of `thm:pencil-conjecture`.
  - Some look off the proof in Lean too. `lem:pencil-self-dual`'s pin is named only in
    docstrings. The girth-chain subsection and `thm:pencil-x0-closed-ear` are also outside.
  - Others are on the Lean call chain but have no edge to the headline:
    - `pencil_conjecture` calls `pencil_conjecture_of_X0`, which calls
      `pencil_conjecture_of_arms_pair`. That is one of the three pins of
      `thm:pencil-conditional-realization-pair`, whose statement is the kernel form.
    - `pencilPair_of_nonempty` (`Statements.lean`) calls `pencilPair_of_isLoopAt` and
      `pencilPair_of_ncard_le_two`, which call the pins of `lem:pencil-loop-case` and
      `lem:pencil-base-case`.

  Liveness is a property of the Lean call chain (`CLEANUP.md` §B), so a task confirms it there
  before its prose calls anything "off the proof".
- **Mathematics in the wrong place.** Formalization notes carry mathematics: the five in
  `sec:pencil-nondegenerate`, and `fmlnote:pencil-main-component-statements`. Lean names sit
  inside statement blocks: `def:pencil-ear-data`, `lem:pencil-ear-data` and
  `lem:pencil-ear-data-open`.

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

- [x] **1. S — the sample section: `sec:main-component-splitoff`** (Opus; this commit; the spec is
  at the open, `5f9cbe04`). Now `main-component.tex` lines 2952–3329: 322 → 378 lines (+56).
  Clauses (a)–(e) are all delivered. No `\label`, `\lean`, `\leanok` or `\uses` line, statement
  block or node order changed, and the diff stays inside the subsection. Two proof edits, argument
  unchanged: the flexes proof's first sentence became its (c) lead-in, and part (1) of
  `lem:pencil-splitoff-curve`'s proof now derives its line from the rational solution in words.
  - *Record: what the PI should check.* **The remarks:** both are cut. The first folds into (b), a
    paragraph just before the theorem (a lead-in, not text between statement and proof). The
    second's coverage facts moved into (a); its every-`δ` bound is unproved and is cut, and (a) says
    instead that `δ ≥ 5` enters only the count (the Lean agrees: `hδ` is used only for `hdef3a`).
    **The JJ passage:** the TR's proof of Theorem 6.1, Claim 6.5, Case 1 (printed pp. 15–16), with
    its Lemmas 2.2(b), 2.3 and 2.4 (p. 4) and the planar count of §3 (p. 7). The prose names no
    claim or section number. "Brick" is lint-banned, so their case reads "adding the edge lowers
    the deficiency", which Case 1 states. **The depth:** four opening paragraphs, not three; (d) is
    the fourth.
  - *Corrections to the spec.* `a ≁ b` is not in `Graph.ChainUsable`'s `k = 1` clause. It is a
    hypothesis of `Graph.X0Attains.of_splitOff` and of the `X0Reduces.splitOff` constructor,
    supplied from sparsity inside `Graph.IsChain.x0Reduces_of_chainUsable` (by
    `Graph.IsOpenEar.not_adj_and_two_le_pairDelta_two`, `lem:deficiency-one-body-chain`(1)); the
    prose says so. The new prose writes `def(G̃[V₁])`, not `def₃`, to match the frozen statement
    blocks. Left for the PI: "an endpoint selector" in `lem:pencil-curve-limit`'s statement, a Lean
    artifact that the frozen statement blocks kept.
- [ ] **2. E — pin the exemplar.** Docs only; in the commit after the PI's Stop-1 entry.
  - Transcribe the PI's answer verbatim into *Decisions*.
  - If the PI approved the sample, copy the subsection verbatim into *The pinned exemplar*.
  - If the PI asked for revisions, this task revises the sample and pins it. It stops again only
    if the PI asked to see it again.
  - Settle the four defaults of *Decisions* as the PI ruled.
- [ ] **3. P1 — `pencil.tex`'s three opening subsections, 38–188**: `sec:pencil-through-point`,
  `sec:pencil-realization` and `sec:pencil-duality`. The definitions arrive without their picture,
  a pencil of lines through a point of a plane, or its molecular reading; only the chapter opening
  gives it. Nothing says what self-duality is for. It looks off the proof, since its pin is named
  only in docstrings (confirm on the call chain). What it does is constrain how the induction
  statement is shaped (`fmlnote:pencil-distinct-motive`). The field-generality paragraph (92–104)
  points ahead to a formalization note three subsections on.
- [ ] **4. P2 — base, cycle and extension, 189–463**: `sec:pencil-base`, `sec:pencil-cycle`,
  `sec:pencil-extension`.
  - Three local constructions, none placed: say which case of the reduction each serves.
  - The two cross-incidences of `lem:two-pencil-extension-iff` are the chapter's first new
    obstruction. Say where they matter later: the failure of minimality, the repositioning in the
    cut-edge case, and `K₄`.
  - `lem:cycle-coplanar-realization` is stated as a corollary before the lemma it follows from
    (319–347): reorder.
  - Keep `notes/BlueprintExposition.md`'s pointer to "the `sec:pencil-extension` preamble +
    proofs" true.
- [ ] **5. P3 — `sec:pencil-reduction`, 464–754.** 11 nodes.
  - The nodes do not follow the five cases of `thm:pencil-reduction`. It needs a roadmap from
    cases (i)–(v) to the lemma that settles each, naming the two cases left for later
    subsections.
  - The cut-edge proof repositions a side without saying why: the crossing edge's two
    cross-incidences.
  - Cure `lem:pencil-cut-case`'s forward citation of `def:pencil-distinct-motive`.
  - Confirm the loop and base cases' live use (*Current state*), say in prose where the live route
    proves them, and record the missing edges under *Moved to a later round*.
  - Check "KT Lemma 6.2" in `lem:pencil-simple-of-noRigid` against KT.
- [ ] **6. P4 — `sec:pencil-nondegenerate`, 755–1040.** Four definitions,
  `thm:pencil-conditional-realization-pair`, and five formalization notes.
  - Why the induction statement is conditioned as it is sits in formalization notes, which
    principle D reserves for Lean divergence. That is: `K₄` against conditioning on simplicity
    alone, a parallel class against conditioning on feasibility alone, distinctness as a separate
    statement, and the kernels' induction hypothesis. Move it into the prose.
  - The theorem is two things at once: a live reduction and an open conditional. Its pin
    `pencil_conjecture_of_arms_pair` is on the headline's call chain through
    `pencil_conjecture_of_X0` (*Current state*). It is the reduction with the conditioned-pair
    loop, base and cut-edge cases, and it takes the contraction and split cases as hypotheses. Its
    kernel forms are off the proof. Say this where the theorem is stated, and name the parts the
    live route reuses: those three cases, and the direct construction on three and four bodies,
    which `thm:pencil-generic-step` cites. Record the missing edge from
    `thm:pencil-conditional-realization-main-component` under *Moved to a later round*. If the
    node wants splitting, that goes under *Candidates*.
  - The theorem's 43-line proof needs an overview.
  - The field note's "known routes" for the kernels cite nothing, and are the project's own: say
    so, or cut them.
- [ ] **7. P5 — `sec:pencil-main-component-route`, 1041–1195.** The route's one idea: over a fixed
  planar picture the pencil condition is linear in the heights. The preamble says it, but its
  sketch sits in `fmlnote:pencil-main-component-statements`, as mathematics: move it to prose, and
  keep in the note only what the Lean does differently. `lem:pencil-nonsimple-case`'s proof is
  the model to keep; check its KT Lemma 6.2 citation.
- [ ] **8. P6 — `sec:pencil-girth-chain`, 1196–1411.** 8 nodes, all outside the headline's closure
  (confirm).
  - The preamble should say at once that the subsection serves the bypassed kernels of
    `thm:pencil-conditional-realization-pair`, and why it is kept.
  - Relate its chains to the coverage's `def:pencil-x0-chain`, which is proved separately.
  - Its last sentence names "the two-cut composition" of kernel (K-bare) without introducing it.
    That composition is where build-or-leave items 1 and 2 have their purpose. **Writes item 2's
    recommendation**, and a note toward item 1's.
  - Round 1's candidate on `lem:pencil-chain-side-connected` stands: no prose should paper over
    it.
- [ ] **9. M1a — `sec:main-component-carrier`, first half, 123–338.** Pictures, the lifting space,
  configurations, and the linearity of the pencil condition; 8 nodes. It needs the idea that
  should lead: a configuration is a lifting of a planar drawing, the scene-analysis picture
  `sec:main-component-flat` cites (Whiteley 1996 §8.3), and coplanarity of each closed
  neighbourhood is linear in the heights. "Throughout, G is … of minimum degree at least two"
  comes before `def:pencil-x0-standing`: anchor it.
- [ ] **10. M1b — the carrier, second half, 339–715.** Main pictures, attaining, the point-join
  rank, the one-witness lemma, openness, the fibre intersection, and the main component; 11
  nodes.
  - Say that the one-witness lemma and the fibre intersection are the two tools every step uses.
  - Give an overview before the one-witness proof's Cramer section, which the two contraction
    subsections reuse with a parameter.
  - Let `rem:pencil-x0-main-component`, which explains the name, lead in rather than trail.
  - Move `lem:pencil-rank-collineation` here, ahead of `lem:pencil-rank-scale-shift`.
  - Say what `thm:pencil-x0-main-component`, a bundle of three tools, is for.
- [ ] **11. M2 — `sec:main-component-flat`, 716–942.** A good roadmap. Check both citations,
  Crapo–Whiteley Example 4.4 and Whiteley 1996 §8.3, against `.refs/`.
  - Before the flat split's coordinates, state its idea: at zero heights every hinge lies in
    `z = 0`, and the planar motions are families of affine functions.
  - Say why the flat case matters: through `cor:pencil-jj-flat` it settles the coverage's first
    case, equal deficiencies.
  - **Writes item 8's recommendation.**
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
  re-derive. The four "Informally …" remarks fall under default (a), and are item 3's text.
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
  - If default (a) leaves any comparison with the informal argument, introduce that argument here,
    once.
  - From task 1: the split-off sentence (78–84) says the body "starts on the line through the
    points of its neighbours" *as in* JJ's proof. The TR does not: JJ move the new pin, then
    reinsert the vertex by extensions. Match `sec:main-component-splitoff`'s account.
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
   pinned; 31 have no node. Seen at the open: Layer C's file, `Molecule/Pencil/TwoCut.lean`, is
   imported only by the root `CombinatorialRigidity.lean`, so its names feed neither headline.
   Layers A and B were not checked. Role: task 8 (the two-cut composition) and task 15 (the ear
   formula). *Recommendation: pending* (task 15).
2. **A6, the welded pendant law, and item 6's other deferred laws.** These are S7(i), S7(ii),
   S7(iii), S7(v) and S9, all unbuilt; they belong to the same composition's block-profile family.
   Role: task 8. *Recommendation: pending* (task 8).
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
   `lem:pencil-lifting-space-deficiency` uses. Role: task 11. *Recommendation: pending*
   (task 11).

A node these items might gain would sit in `deficiency.tex`, `rigidity-matrix.tex` or
`panel-layer.tex`, outside this round's surface. The round only recommends.

## The pinned exemplar

Empty until Stop 1. Task 2 copies the PI-approved sample here verbatim, between `---BEGIN
EXEMPLAR---` and `---END EXEMPLAR---` markers, as `notes/FormalizationRetrospective.md` did for
Phase 29. Afterwards the block is altered only to correct a verified factual error. It fixes the
register, depth and evidence bar for tasks 3–26.

## Candidates for `40-simplify`

Structural findings, and any finding that would change a headline or blueprint statement. They are
recorded here and never acted on in this round (`notes/Cleanup40.md` §2). The close (task 27)
mirrors them, one line each, into `notes/Cleanup40.md` §2 *Round 4*.

- None yet.

## Moved to a later round

Each line gives the task, its target round, and a one-line reason. The same line goes into the
target round's plan section in `notes/Cleanup40.md` in the same commit.

- None yet.

## Blockers / open questions

- None blocking. The coordinator writes Stop 1 (`NEEDS_PI`) in a `## Autopilot: for the PI`
  section of this log (`.claude/autopilot/system-prompt.md`). The sample is meant to answer three
  questions there:
  1. Are the sample's register, depth and evidence bar the round's?
  2. Do the four defaults of *Decisions* hold?
  3. Is the task list's granularity right? That is 24 section tasks, with three subsections split
     and two groups formed.

## Hand-off / next phase

**Next: Stop 1 (`NEEDS_PI`), the PI's review of the sample.** Task 1 has landed, and the choices
the PI should check are in its record under *Lemma checklist*. The coordinator writes the stop
after verifying task 1's commit. No other section is written before the PI's entry. Then task 2
transcribes the answer and pins the exemplar, tasks 3–26 follow in order, and task 27 closes the
round.

## Decisions made during this round

- **2026-09-30, the open: the sample is `sec:main-component-splitoff`.** It is typical of the round:
  the seven step subsections of `main-component.tex` (about 2 500 of its 4 858 lines) each prove
  one step by a construction and a count against the one-witness lemma. It has five nodes, a key
  idea stated but not explained, a published argument whose citation needs checking (JJ), and
  three "informal argument" passages. It has no forward reference, so it is one clean commit.
  Rejected: `sec:main-component-cut` (too easy), `sec:main-component-short` (617 lines), and
  `sec:main-component-contract` (its lemmas are entangled with the additive subsection).
- **The task list.** One commit per subsection. The carrier, SHORT and the statements split at
  their natural seams; `pencil.tex`'s short opening and local-construction subsections are
  grouped. Pinning the exemplar is its own task, so it is copied exactly as approved.
- **The two chapter introductions and `intro.tex` come last.** Principle F revises preambles and
  connective prose once the content around them is stable. `pencil.tex`'s introduction also
  summarizes the route into `main-component.tex`, so both introductions follow every subsection;
  `intro.tex`'s paragraph summarizes both, so it follows them.
- **Round-wide defaults, pending the PI at Stop 1.**
  - (a) A comparison with the workbook's informal argument stays only if it is mathematics the
    reader can follow without the notes and it says why the proof is shaped as it is. A stronger
    fact not proved here is marked unused, with its reason, or cut.
  - (b) A formalization note keeps only what the Lean does differently.
  - (c) A Lean name never appears in a statement block.
  - (d) A node may move within its chapter to cure a forward reference.
- **The invariance check** (gate 3). `checkdecls` resolves names and `lint.sh` checks that targets
  exist; neither sees a changed `\uses` edge or `\leanok`. The graph `inv web` writes records node
  status and edge kind, and its sorted hash does not depend on the order of the nodes, so a move
  passes and any other change fails.
- **Rungs.** The sample is Opus, since it sets the exemplar. After Stop 1 the coordinator picks
  each task's rung against the exemplar, as Phase 29's post-exemplar slices ran at Sonnet (the
  playbook). The tasks that check JJ or KT pinpoints (12, 14, 20) may still merit Opus.
