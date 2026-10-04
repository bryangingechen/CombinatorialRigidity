# The post-Phase-40 cleanup rounds (planning note)

**Status:** queued by the PI on 2026-09-29, ahead of ORIGAMI. Round 1, `40-cleanup`, opened
2026-09-29 and closed 2026-09-30 (`notes/Phase40-cleanup.md`). Round 2, `40-factor`, opened and
closed 2026-09-30 (`notes/Phase40-factor.md`). Round 3, `40-exposition`, opened 2026-09-30
(`notes/Phase40-exposition.md`); rounds 4–5 have not opened. Five cleanup rounds (`CLEANUP.md`)
over what Phases 39–40 built, run under autopilot in this order: `40-cleanup`, `40-factor`,
`40-exposition`, `40-simplify`, `40-docs`. `.claude/autopilot/queue.toml` is the authority for the
order and for which rounds are done. Round 3's Stop 1 closed on 2026-10-03: the PI approved the
revised sample section, pinned as the exemplar (`notes/Phase40-exposition.md` *Autopilot: for the
PI*). Tasks 1–20 have landed. **The next concrete task** is round 3's task 21, run unattended.

## 1. The PI's decisions (2026-09-29, verbatim)

From the session that set up the autopilot, answering the coordinator's proposals:

- "Rather than open ORIGAMI, I'd like to direct the autopilot work towards some cleanup phases
  first."
- On three mechanical rounds and a deeper recon: "Let's go with 3 rounds, but I wonder if we
  should have a more indepth cleanup recon first to search for bigger simplifications? I suppose
  we could also do that after the more mechanical cleanups; there's an argument that there's less
  to sift through at that point."
- On the build-or-leave items: "I want to revisit those when we do a cleanup round on the
  exposition, making sure that the mathematics is explained clearly and that we explain the proof
  and its key ideas in context. At that point it may be more clear whether we should build /
  refactor around those results?"
- On the five-round order below and round 5's scope: "1+2, I think the suggested order makes
  sense, including round 5."
- On the autopilot check-in: "Yes, let's go with the standard runcap lifting+mechanical fixups.
  Since this will be autopilot, we'll want as few interruptions as possible. Sonnet+Opus also
  makes sense."

What follows from them:

- The deep recon (round 4) runs after the mechanical rounds and after the exposition round,
  whose account of the proof's ideas is its best input. So round 1's long-proof audit screens and
  records candidates; it does not restructure proofs.
- Round 5 runs last: compressing Phase 40's notes and design doc earlier would remove what
  rounds 3 and 4 read.
- The autopilot stops for the PI twice: after round 3's sample section, and after round 4's
  verdicts. Round 3 prepares the build-or-leave recommendations and the PI decides them at
  round 4's stop, so they cost no stop of their own. Rounds 1, 2 and 5 open and close unattended.
  (The coordinator's reading of "as few interruptions as possible".)

## 2. The rounds

**All five rounds** (`CLEANUP.md`; the Phase 26 round is the precedent):

- They are hygiene. New mathematics lands only where the PI sanctions it at round 4's stop.
- Headline statements and blueprint statement strength stay as they are. A finding that would
  change one is recorded as a round-4 candidate. It is neither acted on nor a stop.
- Every commit builds green and warning-clean, with `lake lint` green.
- At each round's open and close, `#print axioms` on `formalization.yaml`'s main results gives
  `[propext, Classical.choice, Quot.sound]`.

### Round 1 — `40-cleanup`: the mechanical round (`notes/Phase40-cleanup.md`)

The surface:

- the Lean: `Molecular/Molecule/Pencil/**` (Phases 39–40), plus Phase 40's edits outside it.
  `git diff --stat c9d26ef9^ 91fcd24a` lists them; the largest are `Induction/SparseDeficiency.lean`,
  `RigidityMatrix/Bricks.lean`, `Deficiency.lean`, `Induction/SplitOffDeficiency.lean`,
  `AlgebraicInduction/Theorem55.lean` and the new `Mathlib/` mirrors;
- the blueprint: `pencil.tex` and `main-component.tex`, plus Phase 40's additions to
  `deficiency.tex` and `rigidity-matrix.tex`.

The work:

- `CLEANUP.md` A (blueprint against Lean) and B (code smells).
- C (long proofs) as screening only. Rank the proofs and walk the top ten with §C's four
  questions. Land only local changes: a tactic substitution, a missed mathlib lemma, or a small
  extraction. Record each structural candidate for round 4.
- Four mechanical items carried by `notes/Phase40-design.md` §7:
  - the wider stand-in audit of `lem:trivial-motions-rank-bound` (§3 FLAT);
  - the 40h file-size and readability items, `span_supportExtensor_ofNormals_eq` in `Cut.lean`,
    and call 12's corollary rebases (§3 STEPS);
  - the `pathVertex` helpers, moved to their definition's file (§3 COVERAGE);
  - the `mapExtensor`/`mapSupport` duplication (§4).
- A stale status. ROADMAP's toolchain-bump row and `notes/ToolchainBumps.md` still say the stack
  is unpushed and CI has never validated it. On 2026-09-29, `origin/master` was at `91fcd24a` and
  CI's *Build & deploy site* run passed there.

Not in this round: the hub normalization (round 2), the build-or-leave items (round 3), and
`CLEANUP.md` D (round 5).

### Round 2 — `40-factor`: the shared hub normalization (`notes/Phase40-factor.md`)

The factoring item of `notes/Phase40-design.md` §7, as specified there. The `ι₀` normalization is
duplicated between `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions`
(`Molecule/Pencil/TwoCut.lean`) and `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
(`AlgebraicInduction/PanelLayer.lean`). Extract it once and rebuild both sites on it.

- §7 calls the extraction "one private lemma", but the two sites are in different files; settle
  its visibility first. Settled at the open: a public `Graph.exists_normalized_labeling` in
  `Molecular/Deficiency.lean`, the file that defines `numParts` and `crossingEdges`
  (`notes/Phase40-factor.md` *Decisions*).
- `PanelLayer.lean` is in the fragility zone, so the builds are Opus (the playbook floor).
  Phase 38 is the precedent.

### Round 3 — `40-exposition`: the proof explained (`notes/Phase40-exposition.md`)

`pencil.tex` and `main-component.tex`, and `intro.tex`'s reader path into them. Explain the
mathematics clearly, and explain the proof and its key ideas in context (§1). It is prose: each
node's pinned Lean strength and dependency edges stay as they are (Phase 28's rule).

- **Stop 1 (`NEEDS_PI`).** Comes after the open and one sample section, before any other section
  is written. The approved sample is copied verbatim as the pinned exemplar (in the end, into its
  own file, `notes/Phase40-exposition-exemplar.md`, to keep the work log short). It fixes
  the register, depth and evidence bar for the remaining sections, as in Phase 29.
- **The build-or-leave items.** The round writes a recommendation for each into its hand-off, as
  the exposition makes each result's role clear: build it, add its blueprint node, refactor around
  it, or leave it with a recorded reason. The PI decides at round 4's stop. The items are in
  `notes/Phase40-design.md` §7 and §3:
  - the D5 blueprint debt: §7's list of landed names that have no blueprint node;
  - A6, the welded pendant law, and item 6's other deferred laws;
  - the "only if" halves of (MC-52)/(MC-53) (§3 STEPS);
  - the edge-restricted, non-spanning generic-normals row rank (§3 BRIDGE). A recon has compiled it
    as three declarations; it is off every consumer path. The coordinator added this one, because
    it is the same kind of item.
  - `Graph.X0Attains.of_openEar_splitOff` and `Graph.exists_earBase_splitOff`
    (`Molecule/Pencil/MainComponent/Short.lean`), the shared assembly SHORT's task 18
    (`b8b24c9a`) factored the three- and four-body open-ear steps' base data and two-round
    argument into. Neither cites a nonexistent blueprint label, so `40-cleanup` task 38 (A-MC6)
    minted no node for either and instead pointed `thm:pencil-x0-open-ear-four`/`-three`'s proofs
    at them by name (`notes/Phase40-cleanup.md` task 38).
  - `Graph.IsOpenEar.exists_maximal` (`Molecule/Pencil/MainComponent/CoverageChain.lean`) and
    `Graph.Connected.induce_of_gate` (`Molecule/Pencil/MainComponent/CoverageCut.lean`), the
    shared maximal-ear-extension and one-gate-connectivity lemmas Phase 40m's CHAINS sub-phase
    built. Neither cites a nonexistent blueprint label, so `40-cleanup` task 41 (A-MC9) minted no
    node for either; both callers' proofs already narrate the shared construction honestly, so no
    prose fix was needed either (`notes/Phase40-cleanup.md` task 41).
  - `Graph.exists_isMinimalKDof_spanning_subgraph` (`Molecular/Deficiency.lean`), the
    converse-direction strip both `thm:theorem-55-6-genuine` and `thm:theorem-55-6-rows`'s
    constructions call to produce a deficiency-preserving minimal spanning subgraph. Its own
    docstring says it mints no blueprint node (it is the converse of `lem:subgraph-minimality`,
    KT 3.3), so `40-cleanup` task 43 (A-D) minted no node for it; `thm:theorem-55-6-rows`'s proof
    had wrongly cited `lem:subgraph-minimality` for it, fixed this round to name the strip
    directly by `\texttt{}` (`notes/Phase40-cleanup.md` task 43).
  - `Graph.exists_normalized_labeling` (`Molecular/Deficiency.lean`), the relabelling both
    relative hubs share, which `40-factor` task 1 extracted from them. It cites no nonexistent
    blueprint label, so that round minted no node for it; `lem:relative-deficiency-rank-bound`'s
    proof already narrates the relabelling mathematically (`notes/Phase40-factor.md` task 1).

### Round 4 — `40-simplify`: the deep recon (`notes/Phase40-simplify.md`)

A read-only Opus recon over the pencil surface, looking for bigger simplifications. Where a route
question comes up, it uses compiler-checked spikes (rescue §6). Its inputs are rounds 1 and 2's
recorded candidates and round 3's account.

Round 1's recorded candidates, one line each. The detail, and why each is structural, is in
`notes/Phase40-cleanup.md` *Candidates for `40-simplify`*, under the task named:

- `lem:pencil-chain-side-connected` states a two-ended degree fact that its pin
  `Graph.degree_deleteVerts_interior_add_one` proves only for `P.first`; either fix changes a
  statement's strength (task 32).
- Six type-unused `[DecidableEq β]` binders, each with a silencer, on `pencil_conjecture` and five
  pinned pencil theorems; dropping them changes a headline signature (task 2).
- A finsum-native rewrite of `CoverageTheoremS.lean`'s degree-sum pair, which needs finsum
  comparison and constant-sum mirror lemmas first (task 8).
- `pencilPair_of_habitat_ncard_eq_four` feeds neither headline: keep it, with `_three`'s task-24
  substitutions carried over, or retire it (task 24).
- A shared sub-lemma for `Pair2.lean`'s pendant producers #4 and #6, whose ~190-line tails are
  byte-identical (task 26).
- The `|C| = 0`/`|C| = 1` case-split duplication in
  `hasPencilRealization_of_not_twoEdgeConnected_core` (`Arms.lean`), over `ScrewSpace` carrier
  terms (task 27).
- `Graph.X0Attains.of_closedEar` has no callers: keep, retarget or retire it (task 37).

Round 2's recorded candidates, one line each. The detail is in the log each names, under
*Candidates for `40-simplify`*:

- Both relative hubs state `V(G).compl.ncard` where `V(G)ᶜ.ncard` is idiomatic, so they and their
  three consumers carry five `rfl` bridges; restating changes two statements, one pinned
  (`lem:relative-deficiency-rank-bound`) (`notes/Phase40-factor.md`, seen at the open).
- The merged hub's `hne : V(F.graph).Nonempty` is redundant (it follows from `hu`, and the proof
  uses it only for a `Nonempty α` it does not need), but dropping it changes the statement; the
  hub has no blueprint node (`notes/Phase40-factor.md`, task 2).

Round 3's recorded candidates, one line each. The detail is in `notes/Phase40-exposition.md`
*Moved to a later round*:

- `def:pencil-nondegenerate`'s hub threshold rests on `lem:coplanar-hinges-concurrent` (since
  task 6 through its lead-in, before in a deleted note), with no `\uses` edge to it (task 4).
- Only the off-route `thm:pencil-conditional-realization` has `\uses` edges to
  `lem:pencil-loop-case` and `lem:pencil-base-case`, which the live route uses (task 5).
- `lem:pencil-simple-of-noRigid` has no in-edge, though `thm:pencil-generic-step`'s pin calls it
  through the unpinned three-body construction (task 5).
- `thm:pencil-conditional-realization-main-component` has no `\uses` edge to
  `thm:pencil-conditional-realization-pair`, though its proof applies the reduction as in it and
  its pin calls `pencil_conjecture_of_arms_pair` (task 6).
- `thm:pencil-conditional-realization-pair`'s two notes sit between its statement and proof, so
  plasTeX attaches the proof to a note and the graph draws the node unfilled; moving them after the
  proof fills it, the graph's one changed line (task 6).

The coordinator's starting questions, guessed from file names and sizes (nobody has read the proofs
for them):

- The open-ear steps are split by the number of interior bodies: two, three and four in SHORT, one
  or two at non-adjacent ends in ORBIT. Is that one argument or several?
- Where does `Pencil/` re-prove something `AlgebraicInduction/` already has? Round 2's duplication
  is one instance.
- What Lean feeds neither headline (`pencil_conjecture`, `pencilPair_of_nonempty`)? For example,
  the conditional theorems kept when design §6 was retired. This one is a mechanical dependency
  check.

**Stop 2 (`NEEDS_PI`).** One write-up for the PI:
- each verdict, GO or NO-GO, with a commit estimate;
- round 3's build-or-leave recommendations.

Then the items the PI sanctions land, green at every commit (the structural-edit discipline), and
the round closes.

### Round 5 — `40-docs`: project organization (`notes/Phase40-docs.md`)

`CLEANUP.md` D, project-wide:

- Move `notes/FRICTION.md`'s seven `[resolved]` entries to `FRICTION-archive.md`.
- Compress Phase 40's notes (`Phase40a`–`Phase40p`) and `notes/Phase40-design.md`, preserving
  anchors. On 2026-09-29 the design doc had 11 Lean doc-comment anchors, so `notes/CLAUDE.md`'s
  anchor-count test (*One canonical home*) says compress rather than freeze. The precedent is
  `Phase22-realization-design.md`, with 8 anchors.
- Lift the lessons of Phase 40 and rounds 1–4 into `TACTICS-GOLF.md`, `TACTICS-QUIRKS.md` or
  `DESIGN.md`.

Left out, per §1: trimming the auto-loaded `CLAUDE.md` files, and reorganizing `notes/` into
directories (`CLEANUP.md` D's standing candidate).

## 3. Baseline (2026-09-29, at `91fcd24a`)

- **The pencil tree.** `Molecular/Molecule/Pencil/` has 40 files, 34 363 lines. Phase 40
  (`c9d26ef9^..91fcd24a`) touched 71 files in `CombinatorialRigidity/` and `blueprint/`,
  +27 816 / −670 lines; `main-component.tex` alone gained 4 809.
- **The longest proofs**, by `CLEANUP.md` §C's script. It ends a proof at its first blank line
  past 50 lines, so these are low. From Phase 39:
  - `pencilPair_of_habitat_ncard_eq_four` (`Base.lean`, 852);
  - a `Witness.lean` proof (483);
  - `pencilPair_of_habitat_ncard_eq_three` (`Base.lean`, 474);
  - three `hasGenericPencilRealization_of_isNondegPencilRealiza…` proofs in `Pair.lean` and
    `Pair2.lean` (448, 447, 409).

  From Phase 40: `GenericTriangle.lean` (401), `Orbit.lean` (368), `Short.lean` (353, 351).
- **`notes/FRICTION.md`.** 5 440 lines. Its entry headings are 196 `[idiom]`, 67 `[mirrored]`,
  18 `[open]`, 12 `[process]`, 7 `[resolved]`, 7 `[wontfix]` and 2 `[blueprint]`.
- **Phase 40's notes.** 1 734 lines in `Phase40a`–`Phase40p`, and 1 434 in `Phase40-design.md`.
  The auto-loaded CLAUDE.md files total 1 704 lines.
