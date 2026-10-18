# RECONCILE: acting on the PROSE findings (planning note)

**Status:** rounds 1 and 2 closed, round 3 open (all 2026-10-15). The PI queued RECONCILE next,
ahead of ORIGAMI, as three autopilot rounds and one attended phase (`.claude/autopilot/queue.toml`).
Its input is PROSE's findings report `notes/Prose-report.md` (items S1–S42, L1–L12, M1–M5, G1–G6
and §2.6), with each finding's home the ledger `notes/Prose-findings.md`. Round 1, `reconcile-texts`
(`notes/Reconcile-texts-cleanup.md`), is done in nine tasks: S1's and S2's scopes, M1's text, M2's
and M5's credits (Pollaczek-Geiringer 1927 states the characterization and is credited beside
Laman), §2.6's example and the non-vacuity rule; the Lean is unchanged. Round 2,
`reconcile-statements` (`notes/Reconcile-statements-cleanup.md`), is done in 21 one-commit tasks: the
false statements (S6–S10) made true, S4 and S5 restated, S7 and Case III's three counts (S20)
repinned, G1's three pin changes made, S14, S15, S21, S26–S29, S35, S36 and S38–S42 fixed, G2's two true duplicates
merged, the genericity device's citations made to say which argument they borrow, and the nodes of
Cases I, II and III, `meet.tex` and the forest surgery that the formal proof leaves each framed by a
remark; the Lean is unchanged, and the declarations the round unpinned are in round 3's list
(§3, L9). Round 3, `reconcile-lean` (`notes/Reconcile-lean-cleanup.md`), opened with 39 one-commit
tasks; task 2 committed the docstring-label check (`scripts/check-docstring-labels.py`), task 3
deleted L9's Theorem 5.5 and Case I wrappers and the cycle forms, task 4 Case III's line route,
the candidate rows, `case_III_realization` and `blockPiSpan`, task 5
`exists_good_realization_const` and `exists_finite_spanning_rigidityRows` with their dead callers,
task 6 L9's shim `splitOff_deficiency_le_of_forest_surgery`, with
`cor:forest-surgery-deficiency` repinned on `forest_surgery_split`, task 7 renamed `F-061`'s two
`_forest` pins `_starForest`, the shape their hypothesis forces, task 8 dropped the planar
layer's unused or derivable hypotheses, task 9 the pebble game's `hloops`, which `himg` implies,
task 10 the unused hypotheses of the deficiency and the induction, task 11 the chain
extraction's, its triangle lemma now the case $m = 3$ of the cycle lemma, which left one missing
forward edge (`F-270`), task 11.1 moved the cycle lemma to `deficiency.tex` so that the edge
points back, task 12 dropped the algebraic induction's unused or derivable hypotheses (the
cut-edge lemmas' among them), task 13 made the forest-packing lemma give a disjoint cover,
which Tutte–Nash-Williams and its two other callers use as it is, task 14 had the balanced
packing's descent call the packing move, whose statement now says what the move does, task 15
shortened Katoh–Tanigawa Lemma 4.8(ii)'s minimality to their Lemma 4.3's argument, which needs
no Lemma 4.7, task 15.1 dropped three vertex hypotheses of that lemma which its edge
hypotheses imply (`F-274`), task 16, a recon, settled the fix of the pebble game's search
(one marked set threaded through the sibling calls, completeness from the set it returns) and
found a kernel-reducible `decide` not cheap, so the texts name `native_decide`; task 17
landed that search, re-proved, with `dfs.tex` restated, task 18 committed
`scripts/DFSTiming.lean`, which times it beside the old search and holds the `decide` facts,
task 19 had `parsePair` split on any whitespace, so a tab-separated input reads, task 20
rewrote the texts on the search, its running time (measured, no bound claimed), `decide` and the
input, and tasks 21–24 landed the non-vacuity witnesses of the sixteen main results outside S1's
and S2's rows in `CombinatorialRigidity/Nonvacuity.lean`, the molecule and Jacobs rows last,
and tasks 25–29 swept the docstrings of the thirteen planar files, of `Search/`, of
`Mathlib/`, of `PebbleGame/`, of `Matroid/`, of `BodyBar/`, of the square-graph and
generic-rigidity files (every top-level file but `Nonvacuity.lean`) and of the first half of
`Molecular/Deficiency.lean`.
**Next concrete task:** round 3's task 29.1, the docstrings of the rest of
`Molecular/Deficiency.lean`.
The two PDFs of §2 are in `.refs/` (the PI, 2026-10-15).

## 1. The PI's decisions

**2026-10-15**, the planning session, after reading the report's summary. The PI's message,
verbatim:

> OK let's queue RECONCILE next.
>
> For S1, let's do the refactor - we shouldn't keep any vacuous statements around. For S2 can you
> explain why linking will take a whole phase even though we have the strong form?
> Let's fix any incorrect statements in the blueprint as well. For KT's route, let's jeep [keep]
> it but make sure it's explained well.
> G6 is it significant enough to mention?
> M2 let's make sure this is correct.
> M5 yes, probably.
> L1-L2 we should fix the algorithm and the proofs.
> 2.6 yes, drop stale content
> Anything else?

The agent answered S2 (strengthening the statements from
`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` takes about 2–4 commits; a structure field
takes a phase, since `PanelHingeFramework` is built at about 70 sites in 21 files, and `reaimSub`
and `withGraph` break link-recording by design) and G6 (the panel theorem is JJ 2010 Theorem 7.2
as an iff, the generic form of KT Theorem 5.6's panel side). The PI's choices:

- **Push now**: the 126 PROSE commits (the PI pushes; the session had no key).
- **S2: "Structure field"**, over strengthening the statements: the link condition becomes part of
  `PanelHingeFramework`, so a mis-linked framework is unrepresentable.
- **G6: "Own row"**: the generic panel theorem gets its own `formalization.yaml` row, after S1's
  refactor.
- **M1: "Text now, multigraphs in phase"**: "for simple graphs" in round 1, and the multigraph
  form (JJ 2010 Theorem 6.1) formalized in the phase, beside S1's refactor.

The agent's proposals in the same session, which the PI did not object to:

- **A non-vacuity witness for every main result**: a closed declaration instantiating each
  `formalization.yaml` row's hypotheses at a minimal input of its intended class, where S1 fails;
  the phase-close checklist requires one for every new main result.
- **Kind E is formalized, not restated** (`DESIGN.md` *Formalize everything the argument uses*):
  S22–S25 and S31, and the report's optional S3, S16 and S19, since the PI keeps KT's route and
  its nodes should have Lean behind them.
- **Kept as the report suggests**: S11 (`body_hinge_tay` is Tay's body-bar theorem on
  $(D-1)G$, which its row says; S1's refactor gives the form with hinges), S12 (the formal
  infinitesimal rigidity is weaker than Jordán's at $2 \le |V| \le d - 1$, $d \ge 3$; no main
  result is affected), and the Lean round's docstring sweep and deletions (L3–L12).

What follows, per item:

| Item | Decision | Where |
|---|---|---|
| S1 | refactor: families indexed by $E(G)$, no `hends`; then the notes, rows and README | phase (a); scope stated in round 1 |
| S2 | the link condition as a field of `PanelHingeFramework` | phase (a); scope stated in round 1 |
| S3–S10, S14–S16, S18, S20–S29, S35–S36, S38–S42 | every false or mis-scoped statement fixed | round 2, or the phase where Lean comes first |
| S11–S13, S30, S32–S34, S37 | keep or confirm (S13 within S1's refactor) | no commit |
| M1 | "for simple graphs"; then the multigraph form | round 1; phase (b) |
| M2 | verify against the sources, then fix every credit | round 1 (docs), round 3 (docstrings) |
| M3, G3, G4 | **keep KT's route**, explained (§3, round 2): no retirement | round 2 |
| M4 | the docstrings | round 3 |
| M5 | read Pollaczek-Geiringer 1927; credit if it states the characterization | round 1 |
| G1, G2 | the pin changes; merge only true duplicates | round 2 |
| G5 | Lean+ | phase (c) |
| G6 | its own row | phase (a) |
| L1–L2 | fix the search and re-prove it; then the texts | round 3 |
| L3–L12 | as suggested | round 3, the phase's footprint in the phase |
| §2.6 | drop the stale example | round 1 |

## 2. Standing rules (every round, and the phase where they apply)

- **The ledger stays the home.** A task names the ledger IDs it acts on and replaces each entry's
  `reported` or `left` disposition with `done (<sha>)`. New findings take IDs from `F-251` on,
  under the ledger's format and categories; a round's log holds one line per finding.
- **Hygiene, lifted exactly for §1's items.** A statement change outside §1's table is recorded as
  an `S` entry under the round log's *Candidates for the PI*, and not acted on. Headline statements
  change only in the phase, and only as §1 says.
- **Evidence.** As PROSE's (`notes/Prose.md` §2): claims about the Lean come from statements and
  bodies, never docstrings; a surprise gets a `lake lean` witness before it is written; citations
  meet `CLAUDE.md` *Referencing prior work* against `.refs/`.
- **The two PDFs** (M2, M5): Lovász–Yemini 1982 (doi:10.1137/0603009) as
  `.refs/lovasz-yemini-1982-on-generic-rigidity-in-the-plane.pdf`, and Pollaczek-Geiringer 1927
  (doi:10.1002/zamm.19270070107) as
  `.refs/pollaczek-geiringer-1927-uber-die-gliederung-ebener-fachwerke.pdf`. A task whose PDF is
  missing moves to the next round with a one-line reason; after round 3 it moves to the phase,
  which is attended. A credit is never changed on a reading of a secondary source alone.
- **Main results' axioms** (`PHASE-BOUNDARIES.md`, the close checklist): run at each round's open
  and close with PROSE's harness, built from `formalization.yaml`. Rounds 1–2 must reproduce round
  5's output byte for byte; round 3 and the phase must give `[propext, Classical.choice,
  Quot.sound]` for every row.
- **Gates.** Round 1: PROSE rounds 1–4's invariance check (no node, edge or pin changes) and no
  Lean edit. Round 2: PROSE round 5's expected-diff gate and honesty gate
  (`notes/Prose-graph-cleanup.md` *Scope*), and no Lean edit. Round 3: whole-project `lake build`
  with 0 warnings, `lake lint`, `CLEANUP.md` §B's trial deletion before any deletion, and the
  blueprint gates. Every round: `lint.sh`, `verify.sh` with `checkdecls` silent, `print.log` with 0
  `LaTeX Warning` lines, and `python3 notes/check-phase-note.py` on its log.
- **Rungs and logs** as PROSE's (`notes/Prose.md` §2): Opus for opens, statement, Lean and recon
  tasks; Sonnet may take docs bookkeeping and closes. Each round's log follows `CLEANUP.md`
  *Per-round work log*, with `## Autopilot: for the PI`.

## 3. The rounds and the phase

| # | Queue id | Work log | Scope | Commits |
|---|---|---|---|---|
| 1 | `reconcile-texts` | `notes/Reconcile-texts-cleanup.md` | docs and blueprint prose | ~8 |
| 2 | `reconcile-statements` | `notes/Reconcile-statements-cleanup.md` | blueprint statements, pins, KT's route | ~20–30 |
| 3 | `reconcile-lean` | `notes/Reconcile-lean-cleanup.md` | the Lean outside the phase's footprint | ~30–40 |
| P | `RECONCILE-FORMAL` | its phase note, at the open | the carriers and new formalization | the open's recon |

Each round opens on Opus with its log, baselines and task list, lands one commit per task, and
closes under `CLEANUP.md` *Workflow* 5: the queue row's `done = true`, ROADMAP's Status row (added
at the open), this note's **Status**, and the ledger's dispositions.

### Round 1 — `reconcile-texts`: the texts

No node, edge or pin changes; no Lean. The open sliced it into nine tasks, with each task's surfaces
(`notes/Reconcile-texts-cleanup.md`).
- **S1 and S2's scope, until the phase**: the `formalization.yaml` rows of the generic body-hinge
  theorem, KT Theorem 5.6 and `molecular_conjecture`, and README, say what the statements cover
  today (S1: no minimal graph; S2: the selector is free) beside the forms that are proved
  (`rankHypothesis_genuine_recordsLinks_of_theorem_55_gen`).
- **M1**: `body-hinge.tex`'s two passages say "for simple graphs".
- **M2, verified first**: read Lovász–Yemini 1982 and Jordán 2016 (pp. 45, 49, 51), and the
  statements of Phases 6–7's declarations; settle what each credit names, and whether the proofs
  follow LY's argument (a "presentation we follow" credit). Then fix `formalization.yaml`'s
  reference entry and its four lines, and ROADMAP's Phase 6–7 texts, Status row title and
  directory-layout line. The Lean docstrings go to round 3.
- **M5**: read Pollaczek-Geiringer 1927 (in German). Its scan's text layer is garbled OCR, so read
  the page images (the Read tool's `pages`), not `REFS.md`'s text extraction; the PDF's 15 pages
  are pp. 58–72, and the first also carries the end of the preceding article. If it states the
  characterization, credit it beside Laman
  wherever the blueprint, README, home page and `formalization.yaml` name the originator, and add
  the reference; if not, record what it does state as an `M` entry.
- **§2.6**: drop the stale `lem:case-I` example from `blueprint/CLAUDE.md`'s honesty gate (replace
  it only with a case the open verifies from current pins).
- **The non-vacuity rule**: `PHASE-BOUNDARIES.md`'s close checklist and `CLEANUP.md` §A gain the
  witness requirement of §1.

### Round 2 — `reconcile-statements`: every false statement, and KT's route explained

Under the expected-diff and honesty gates; one task per item or chapter batch. The open sliced it
into 21 tasks, with each task's surfaces and expected diff (`notes/Reconcile-statements-cleanup.md`);
S3, S16, S18, S19, S22–S25 and S31 wait for the phase, which lists each.
- **False first** (kind B): S6–S9 in one commit; S10 restated in its pin's form and filled.
- **Vacuous or trivially met** (kind A): S4 drops its vacuous assertion; S5 states its pin's
  conclusion. S3 waits for its Lean (phase (c)).
- **The rest of §1.4's restatements and repins**: S7 (nondegenerate hinges, repinned on
  `exists_rankPolynomial_of_le_finrank_linking`), S14, S15, S20, S21, S26–S29, S35, S36 and S38–S42,
  as the report suggests. S16, S18 and the kind-E items wait for the phase, so each statement
  changes once.
- **G1**'s three pin changes; **G2**'s true duplicates merged (`lem:case-III-claim-6-11-base` into
  `lem:splitoff-kdof-criterion`, the two affine nodes into one); the pencil doubles and
  `lem:reduction-step`'s stay; `case_III_realization` unpinned.
- **KT's route, kept and explained** (M3, G3, G4; the PI): no node is retired or merged away. Each
  off-route group (Case I's, Case II's, Case III's, `meet.tex`'s two step lemmas, and the forest
  surgery) gets one framing remark: KT's step, why the formal proof leaves it, and what replaces it
  (`\cref`s to the live nodes). Each node in it states what is true (above), and a node restating a
  general form says so. The eleven `\cref`s of `lem:genericity-device` say which argument they
  borrow. The crux carve-out holds (`notes/BlueprintExposition.md`).

### Round 3 — `reconcile-lean`: the Lean outside the phase's footprint

`CLEANUP.md` §A–§C; no main result's statement changes. **The footprint** (the open lists it): the
files that construct `PanelHingeFramework` (21 at planning; 33 read from the Lean at the open) and
`GenericLift/`. There the docstrings that describe the panel-hinge carrier or S1/S2's theorems wait
for the phase, which writes them once; everything else proceeds. The open sliced the round into 39
tasks, with each task's surfaces and expected diff (`notes/Reconcile-lean-cleanup.md`), and moved
the footprint's docstrings to the phase's list.
- **The docstring-label check** (report §2.1): a committed script that checks each blueprint label
  a Lean docstring names exists and pins that declaration; run on every later commit that moves a
  pin.
- **Non-vacuity witnesses** for every main result outside S1, S2 and G6's rows. A witness that
  fails is a new `S` entry for the phase, not a stop.
- **L1–L2, the algorithm**: a recon first (the completeness proof then inducted along the walk with
  `dropUntilBundle`, which task 17 deleted), then one visited set threaded through sibling calls,
  with `reachableFinding_sound` and `_complete` re-proved, and the diamond-chain timing re-measured
  by a committed script. Then `parsePair` on any whitespace, and one rewrite of the texts: the
  docstrings, `Main.lean`, `Examples.lean`, the `lakefile.toml` comment, `DESIGN.md`'s section and
  `dfs.tex`. The recon also settles `decide`: a kernel-reducible form if one is cheap, else the
  texts name `native_decide` as measured.
- **L9**'s deletions after §B's check (with `F-090`'s shim, whose deletion repins
  `cor:forest-surgery-deficiency` on `forest_surgery_split` in the same commit: round 2 keeps the
  node and its pin), and the eight declarations that round 2 unpinned, which its close lists for
  L9's §B check (dead: no main result's proof reaches it):
  `rankHypothesis_withNormal_withGraph_iff_finrank_pinnedMotions` (no caller; `ab3a0d45`),
  `exists_good_realization` and `exists_good_realization_const` (dead, `F-152`; `1b46edc6`; the
  open's screen keeps the first, which pinned declarations call, and the second goes with its five
  dead callers, `F-265`),
  `linearIndependent_sum_augment_candidateRow`, `linearIndependent_sum_p2_candidateRow` and
  `linearIndependent_sum_p3_candidateRow` (dead; `9e98aaba`),
  `add_le_finrank_span_rigidityRows_induce_union_range_of_bridgePath` (live: the bridge theorem's
  and the path lemma's pins call it, so it is not a deletion; `94196444`) and
  `case_III_realization` (dead, no caller; `58307442`); **L6–L8**'s
  signatures and repeated derivations, with S17 and the statements they touch; `F-061`'s rename.
- **The docstring sweep** by directory: L3–L5, L10–L12, M2's and M4's docstrings. M2's include
  `BodyBar/TayTheorem.lean`'s "Lovász–Yemini-style" necessity argument (548), which the report does
  not list, and `MatroidIdentification.lean`'s "`|E|`-induction" (23, 190, 263, 708, 749), where
  the proof inducts on $|V|$ (round 1, task 5); M5's, `Laman.lean`'s header (21), which credits
  the theorem to Laman alone (round 1, task 6); and `F-253`'s, the two pins of
  `lem:rank-rotation-semicont`, whose docstrings call them KT Lemma 5.2 and reverse their inclusion
  (round 2, task 2); and `F-254`'s, which still give `lem:case-II` the pin that round 2 task 4
  dropped; and `F-256`'s, three declarations whose docstrings still give them as
  `lem:genericity-device`'s, which round 2 task 5 repinned; and `F-258`'s, the three that round 2
  task 7 unpinned from Case III's counts, whose docstrings still name those nodes; and `F-263`'s,
  `mem_hingeRowBlock_iff`'s docstring and its file's header, which still place it in
  `case-iii.tex`, though round 2 task 12 moved it to `def:hinge-row-block`; and `F-264`'s,
  `case_III_realization`'s docstring and its file's header, which still give it as
  `lem:case-III`'s, though round 2 task 14 unpinned it. The ledger's
  two Lean baselines feed §B and §C.

### The phase — `RECONCILE-FORMAL` (attended; a number minted on open)

New formalization, so it opens with the PI. A design recon comes first, on S2 and S1 together:
both concern how a carrier relates edge labels to $E(G)$. It sizes the ~70 constructions (round
3's open: 257 declarations in 33 files name a constructor, `notes/Reconcile-lean-cleanup.md`
*Current state*), settles `reaimSub` and `withGraph`, and proposes a sub-phase split, likely:
- **(a) the carriers**: S2's structure field, then S1's refactor, restating the S1 and S2 main
  results, their nodes and notes, the rows and README (removing round 1's scope sentences);
  `cor:theorem-55-d3-spanning` fixed; S13 and S18 within; G6's row; the non-vacuity witnesses of
  these rows; the footprint's docstrings: `F-123`, `F-130` and `F-220`, and the parts of `F-126`,
  `F-133`, `F-210`, `F-215`, `F-225`, `F-237` and `F-243` that round 3's open moved here
  (`notes/Reconcile-lean-cleanup.md` *Moved to a later round*).
- **(b) M1**: the multigraph generic body-hinge theorem (JJ 2010 Theorem 6.1).
- **(c) the claims no declaration states**: S22–S25, S31, S3, S16 and S19, G5 (`def:blockingWitness`,
  `def:dof-generic`, the Plücker expansion; the packing move was round 3's task 14, L8's `F-088`),
  and `F-061`'s forest lemma; each
  node restated or repinned when its declaration lands. Round 2's open moved these here, with S18
  to (a) (`notes/Reconcile-statements-cleanup.md` *Moved to a later round*).

The program closes with the phase: ROADMAP's RECONCILE bullet compressed, and the ledger's last
`reported` entries given dispositions.

## 4. Order and stops

The queue runs `reconcile-texts`, `reconcile-statements` and `reconcile-lean` unattended, with no
planned stop, then stops before `RECONCILE-FORMAL` (attended), which comes before ORIGAMI (also
attended). Moving a task to a later round, with a one-line reason in both logs, is not a stop.
