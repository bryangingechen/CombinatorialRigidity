# Phase 40 cleanup round 5/5 — `40-docs`, project organization (work log)

**Status:** in progress (opened 2026-10-04). Round 5, the last of the five post-Phase-40 cleanup
rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` D over Phase 40 and rounds 1–4: lift their cross-cutting lessons, compress Phase 40's
notes and design doc with every anchor kept, archive FRICTION's `[resolved]` entries, align the
user-facing surfaces with `intro.tex`, and run the standing project-organization sweep. No
planned stop. The full task list below was populated at the open; tasks 1–10 landed 2026-10-04.
**Next concrete task:** task 11 (C4), `notes/Phase40e.md`–`Phase40h.md` (Sonnet). Round
manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: the round opens and closes unattended (`notes/Cleanup40.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first.

## Current state

**Next commit: task 11 (C4)**, `notes/Phase40e.md`–`Phase40h.md`. Of the 17 tasks, task 1 (U) is done
(2026-10-04: README, home page and `formalization.yaml` on `intro.tex`'s reader path). Task 2
(L1) is done (2026-10-04: new `TACTICS-QUIRKS.md` §115 (`unusedDecidableInType`) and §116
(a `<;>`-chained flexible `simp`'s per-goal "Try this"), both with symptom-index lines; worked
cases added to §55 (a spike's `#print axioms` lines passing the warning-only gate) and §58 (the
40c `Fin (1 + 2)` ℕ/ℤ atom-split); `TACTICS-GOLF.md` §26 widened from `push_neg` to the
`if_pos`/`if_neg`/`dif_pos`/`LinearEquiv.ofLinear` renames; five FRICTION entries pointed at their
lift, three flipped to `[resolved]`, and the two `if_pos` entries merged into one — (a) stays
`[idiom]` as the task said). Task 3 (L2) is done (2026-10-04: two new `DESIGN.md` sections,
*Genericity without dimension theory* after *Genericity device* and *New mathematics found by
formalization is second-read before it is built on* before *Choices to revisit*; design §4 and §5
point at them). Task 4 (L3) is done (2026-10-04: `CLEANUP.md` §C's long-proof ranking now measures
declaration span, header line to the next column-0 line, with a one-liner tested against a
`Pencil/MainComponent/*.lean` file and the manual's own glob; §A gained round 3's invariance check
verbatim, re-run at HEAD (1 292 edges / `7c7ef987ce81e090`, 1 029 pins / `8225e0a2bc15ccdb`,
identical to round 4's close — no blueprint drift); a new *Per-round work log* subsection names
what all five rounds' logs share (the hygiene rule, *Candidates for …* / *Moved to a later round*,
*Autopilot: for the PI*); `PHASE-BOUNDARIES.md`'s `formalization.yaml` bullet spells out the
headline-axioms harness as this round's open ran it). Task 5 (L4) is done (2026-10-04:
`blueprint/AUTHORING.md`'s *Proof verbosity* gained default (a), with the PI's 2026-10-03 amendment
quoted verbatim, right before *The carve-out*; principle E gained default (d), *Node order*, right
after the backward test's failure tells. Defaults (b)–(c) were already principles D and B, and the
note-placement rule already `blueprint/SETUP-AND-PITFALLS.md`, confirmed and left as is. ROADMAP's
**PROSE** bullet, its queued-rounds bullet, `notes/BlueprintExposition.md`'s pointer and
`notes/Cleanup40.md`'s **Status** all now point at `blueprint/AUTHORING.md` instead of this log's
*Decisions*, whose own (a) and (b)–(d) entries are now one-line *Promoted to* pointers — (e)–(f)
already were). Task 6 (F) is done (2026-10-04: FRICTION's 17 `[resolved]` entries, re-derived at
HEAD, moved verbatim to `FRICTION-archive.md` — 281 lines, `git diff` multisets equal; the one
real stale cross-reference, `Phase40-design.md` §3 STEPS' "the open FRICTION entry", left for
task 8; `[mirror-candidate]` defined in FRICTION's *Entry format* and *Filing rule*). Task 7 (S)
is done (2026-10-04: re-derived at HEAD, the open's line numbers having moved under tasks 1–6;
ROADMAP §39's three *What landed* items and §38's `cutEdge_finrank_assemble` get a short
parenthetical naming the surviving rename or the `40-simplify` task/sha that deleted it (10g
`f8c6b0d4`, 10i `1e7d78a9`, 10b `c48d323e`, 10o `919486d3`; corrected by the coordinator next); the nine GOLF/QUIRKS worked cases get
the same, by name, none renumbered; `blueprint/SETUP-AND-PITFALLS.md` 81–83 gets one line noting
10h moved the notes it describes as left. A grep for all 124 deleted/renamed names and the six
deleted files over the surfaces found no site the open's inventory missed). Task 8 (C1) is done
(2026-10-04: design §3 from 928 lines to 553, every heading verbatim, each tracked item a cited
verdict, the Lean it names brought to HEAD; its anchor inventory re-derived before the cut and
walked after it, nothing repointed). Task 9 (C2) is done (2026-10-04: the rest of the design doc,
1 096 lines to 864 — §6 to one verdict paragraph, §7's five items and §3's eight tracked
cleanup-round items to one line each, the STEPS appendix's 140-line verbatim spike dropped to git;
§1–§2 and §4–§5 untouched but for the stale §5 "Do not" bullet, fixed; the anchor inventory
re-derived before the cut (9 Lean, unchanged) and walked after it, nothing repointed). Task 10 (C3)
is done (2026-10-04: `Phase40a.md`–`Phase40d.md`, 371 lines to 204 (45, 67, 47, 45), each now a
**Status** line, one *Current state* paragraph, *Decisions made* as one-line verdicts and a
*Hand-off* naming the actual next sub-phase in place of the stale "**Next: …** … **not yet
opened**" every header carried; *Architectural choices* kept only in 40b, where the design doc's
§3 CARRIER pointer needs it. Preserved: 40b's *Decisions made* entry "2026-09-26 C1a"
(`Carrier.lean` 90, `Configuration.lean` 75), its slice names C1a, C1b, C2, C3, C4, C5′
(`Carrier.lean` 16, `Configuration.lean` 15) and DUAL-K (`ProjectiveInvariance.lean` 34). Dropped,
no anchor needing it and one entry stale: 40a's "What keeps `6 ≤ D`" declaration list, one of
whose four named siblings, `edgeBound_of_noRigid_of_degree_two`, round 4 task 10i (`1e7d78a9`) had
already deleted; 40c's and 40d's "Cleanup-round item" checkboxes, both already tracked done in
`notes/Phase40-design.md` §3 FLAT/BRIDGE; the four files' "project-organization review: no new
item" sentences, one of which cited `notes/pencil/CLAUDE.md` status-line text that has since moved
on. Anchor inventory re-derived at HEAD before the cut (0 Lean for 40a and 40d, 5 for 40b, 1 for
40c — the table's 2026-09-29-era *Other* counts were stale and not used) and walked after it:
every Lean and non-Lean anchor resolves, none repointed). Task 15 (G)
is the coordinator's own commit, and task 16 (P) has no commit of its own. Nothing is mid-stream.

**Verified at the open** (`4360ab0e`, docs only; the Lean tree is `654bae8a`'s, the blueprint
`993b9e74`'s):
- Whole-project `lake build` green, 2996 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`. Round 4's harness was diffed against the yaml's `declaration:` and `file:` fields
  (19 names in order, 14 imports: identical), copied to `scratch/40-docs/Axioms.lean`
  (gitignored) and run with `lake lean`. Its output is round 4's close's byte for byte, apart from
  the harness's own path. Re-run it the same way at the close.
- This log, by `notes/check-phase-note.py`'s `parse` and `offenders` run on it directly (its name
  pattern skips `Phase40-*.md`): 398 lines, header 110 words, forward 292 / finished 20, no
  offenders.

**How the open's figures were measured**, so that each task can re-derive its own inventory at
build time, as dispatch-log F1 asks of a compression:
- Lean anchors: `grep -rc '<name>.md' --include='*.lean' .` (`notes/CLAUDE.md` *One canonical
  home*). Other anchors: `git grep -c -F '<name>.md'` over the tracked tree, less the file itself,
  Lean and `scratch/`; then each hit read for the section or sub-item it names. The design doc is
  also cited without its filename ("design §N", "the design doc's §N").
- Deletions: `git diff --name-status --diff-filter=DR 06d175b8 HEAD`, and the names of the
  declaration lines that diff removes which nothing declares now (124, deleted or renamed), each
  grepped in the live manuals and surfaces.
- FRICTION: `grep -c '^### \[resolved\]' notes/FRICTION.md`; an entry runs to the next heading.

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2, restated only as far as a builder needs them:

- **Docs only.** No Lean and no blueprint TeX. `blueprint/AUTHORING.md` and
  `blueprint/SETUP-AND-PITFALLS.md` are manuals, in scope (tasks 5 and 7).
- **Hygiene.** Headline statements and blueprint statements' strength stay as they are. A finding
  that would change one goes to *Candidates for the PI*: recorded, not acted on, not a stop.
  (Rounds 1–3 sent such findings to `40-simplify`, which is closed.)
- **Out of scope:** trimming the auto-loaded `CLAUDE.md` files and reorganizing `notes/` into
  directories (`notes/Cleanup40.md` §2); **PROSE**'s work and opening ORIGAMI (ROADMAP's queue);
  editing `.claude/autopilot/system-prompt.md` (task 16).
- **Anchors** (`notes/CLAUDE.md` *One canonical home*). A compression first re-derives the anchor
  inventory with the commands above; the table and the tasks below are the plan, not the
  contract. It keeps every anchored heading and sub-item, verbatim where an anchor quotes it, and
  after the cut confirms that each anchor resolves to the text it claims. Cutting text an anchor
  points at means repointing the anchor in the same commit, never leaving a dangling claim.
- **One canonical home.** A lifted lesson leaves a one-line *Promoted to …* or **Lifted to:**
  pointer behind. The PI's words stay verbatim at their canonical home, which for Phase 40's calls
  is `notes/pencil/adjudications.md`; a compressed note points there.
- **Gates, every commit:** `python3 notes/check-phase-note.py`, and this log checked by hand as
  above and kept under ~500 lines; `git diff --check`; the staged diff and the message scanned for
  local paths (`CLAUDE.md`). A commit that touches a Lean doc comment (none is planned) runs the
  Lean gates (`CombinatorialRigidity/CLAUDE.md`).

## The open's inventory: compress or freeze

`notes/CLAUDE.md`'s test: few Lean anchors, compress; many, freeze and say so in the header.
"Other" counts the filename's occurrences in tracked files outside Lean and outside the file; the
sub-items each anchor names are in the owning task. The plan's 2026-09-29 figures, re-counted:
the 16 sub-notes have 1 735 lines (1 734 then); the design doc 1 472 (1 434) and 9 Lean anchors
(11); FRICTION 14 `[resolved]` entries (seven).

| File | Lines | Lean | Other | Disposition |
|---|---:|---:|---:|---|
| `Phase40-design.md` | 1 472 | 9 | 105 | compress (tasks 8–9): `Phase22-realization-design.md`, the precedent, had 8 |
| `Phase40a.md`–`40d.md` | 115, 99, 80, 77 | 0, 5, 1, 0 | 5, 4, 2, 3 | compress (task 10) |
| `Phase40e.md`–`40h.md` | 109, 98, 110, 137 | 2, 3, 1, 3 | 5, 7, 10, 8 | compress (task 11) |
| `Phase40i.md`–`40l.md` | 125, 119, 122, 107 | 1, 1, 6, 2 | 6, 6, 9, 8 | compress (task 12) |
| `Phase40m.md`–`40p.md` | 121, 129, 108, 79 | 0, 2, 4, 2 | 9, 7, 5, 17 | compress (task 13) |
| `Phase40-cleanup.md` | 491 | 0 | 14 | compress (task 14): at the tripwire |
| `Phase40-factor.md` | 227 | 0 | 11 | leave: short, and design §7 cites its tasks 1–2 |
| `Phase40-exposition.md` | 372 | 0 | 14 | leave, but for task 5: `Cleanup40.md` §2 and the verdicts' IDs cite its long sections |
| `Phase40-exposition-exemplar.md` | 341 | 0 | 4 | freeze: pinned verbatim at Stop 1; **PROSE** reads it |
| `Phase40-simplify.md` | 249 | 2 | 14 | leave: compressed at its own close (`Contract.lean` cites task 10q) |
| `Phase40-simplify-verdicts.md` | 399 | 0 | 4 | freeze: the record the PI sanctioned at Stop 2 |
| `Cleanup40.md` | 307 | 0 | 61 | leave: §2 *Round 4*'s lists define the verdicts' IDs by position; the close updates **Status** |

The design doc's anchors by target. With the filename: §3 and its layer codes 71 (STEPS 33,
§3 alone 11, COVERAGE 9, MOTIVES 8, BRIDGE 5, FLAT 4, SHORT 1), §7 11, §6 4, §4 4, §1 3, the
appendix 2, §2 1, §5 1, the bare filename 18. Without it, about 40 more (§6 14, §7 7, §3's codes
16, §2 3). Lean: §1 (`X0.lean` 14), §3 (`Theorem55.lean` 2737, `Carrier.lean` 90,
`Configuration.lean` 75), §3 STEPS (`ContractAdditive.lean` 37, `ContractCurve.lean` 83 and 89),
the appendix (`ContractCurve.lean` 1056) and the bare file (`X0.lean` 36).

## Lemma checklist (the round's task list)

One commit per task, in this order (*Decisions*). Line numbers are as of the open; names and
section titles are the stable reference.

### The user-facing surfaces

- [x] **1. U — the user-facing surfaces, aligned with `intro.tex`** (Opus; `3dc6f67b`; round 3's
  task 26). README's and the home page's paragraph, still identical, is now **The pencil
  conjecture (phases 39–40, complete)**, re-summarized on `intro.tex`'s reader path: the pencil
  realization and its molecular reading, the two *main-component statements*, the pictures lifted
  into space and the lifting space. The home page's rows 39–40 and `formalization.yaml`'s five
  sites are renamed, its `status.scope` and `fidelity` re-summarized the same way; no
  `declaration:`, `file:` or `lean:` field changed. Done-check: the `git grep` for the four old
  phrases over the three files is empty, and `ruby -ryaml` parses the yaml. ROADMAP's Phase-39
  title and `RESEARCH-ARC.md` left alone.

### Lifts (before the archive sweep and the compressions that read the same notes)

- [x] **2. L1 — Lean idioms into `TACTICS-QUIRKS.md` and `TACTICS-GOLF.md`** (Sonnet;
  `f02c2a9c`; §115's precedent and calibration brought to HEAD by the coordinator's next commit).
  Each recurred across two or more sub-phases or rounds. Each gets a section or a worked case, a
  symptom-index line where the file has an index, and a **Lifted to:** pointer in its FRICTION
  entry. An entry whose *Status* carries no open work flips to `[resolved]`, so task 6 archives it.
  - (a) QUIRKS, a new section: `linter.unusedDecidableInType` on a type-unused `[DecidableEq β]`.
    Drop the binder and open the proof with `classical`; suppress only for a stated reason; on a
    pinned or headline signature in a hygiene round, suppress and record a candidate. FRICTION
    *`unusedDecidableInType` flags a `[DecidableEq β]`…* (Phase 39 W3-L6a; 40-cleanup task 2;
    40-simplify 10r). Its *Status* lists the suppressions outside the pencil tree, so it stays
    `[idiom]`.
  - (b) QUIRKS, a new section: flexible-`simp` warnings across a `<;>` chain. Each warning's "Try
    this" is a per-goal delta, not a drop-in; `simp?` at the chain's own position
    (`lean_multi_attempt`) gives the full set. FRICTION *The four certificate eliminations…*,
    three instances (40g build 2, 40h B1, 40n B1).
  - (c) QUIRKS §55, in its paragraph on a spike checked under `lake env lean`: a transcribed
    spike's `#print axioms` lines pass the warning-only gate, because their output is `info:`;
    strip them (`notes/Phase40o.md` *Decisions*, fixup `7f782d79`, and the dispatch log's 40o
    row).
  - (d) QUIRKS §58: FRICTION *`omega` misses a `finrank` atom … `Fin (1 + 2)`* (40c), which calls
    itself an instance of the omega-atom family, as a worked case.
  - (e) GOLF §26, widened from `push_neg` to this mathlib's deprecated names: `if_pos`, `if_neg`
    and `dif_pos` give way to `ite_eq_left`, `ite_eq_right` and `dite_eq_left`, and
    `LinearEquiv.ofLinear` to `LinearEquiv.ofLinearMap`. FRICTION has two entries on it (*`if_pos`
    / `dif_pos` are now deprecated*, 40b C1b and C4; *`if_pos` / `if_neg` are deprecated in this
    mathlib*, the 40-factor open): merge them into one.
- [x] **3. L2 — `DESIGN.md`: two cross-phase rationales** (Opus: new rationale sections; landed
  2026-10-04).
  - (a) **New mathematics found by formalization is second-read before it is built on.** Record it
    in the owning workbook step, under the next free labels, marked "found by formalization"; then
    a fresh, read-only, adversarial reading; then the build. Instances: SHORT (40h, PI decision 1,
    "the ORBIT precedent"), ORBIT (40i), route B (40n) and EARS (40o, read after the builds). The
    rule is design §5 *Landing a mathematical repair*; the reusable brief is the design doc's
    *Appendix — the reusable second-reader brief*, which task 9 keeps and the section points at.
  - (b) **Genericity without dimension theory**, beside *Genericity device (Claim 6.4/6.9)*. Each
    delicate generic step becomes an explicit nonzero-polynomial or rational-parametrization
    statement (design §4 *Genericity*). ORBIT's dimension count was rerouted because mathlib has
    `ringKrullDim`, `Algebra.trdeg`, Noether normalization, Chevalley and `UpperSemicontinuous`, but
    no fibre-dimension theorem, algebraic group actions, orbit–stabilizer dimensions or
    trdeg–Krull bridge (design §4, *ORBIT's dimension counting*; checked 2026-09-26, and the date
    goes with the list, since mathlib moves). Also cited by `notes/pencil/workbook/K-main-MC13.md`
    and `notes/pencil/adjudications.md` (PI D1/D2). ORIGAMI's subvariety-generic engine is the
    next consumer.

  Design §4's and §5's entries get *Promoted to `DESIGN.md`* pointers, which task 9 keeps.
  Landed: (b) right after *Genericity device*, with `Graph.X0Attains`, the contraction curve and
  ORBIT as its worked cases; (a) right before *Choices to revisit*, with the four instances by
  commit and its boundary (a compiler-checked new proof of a second-read claim, adding no label,
  is not new mathematics: COVERAGE's D1–D3, 40p's N1–N4). §4's (C) mathlib list moved there,
  dated as checked (the mathlib pin has not moved since the 2026-08-24 bump), and §4's (C) bullet
  is now its pointer.
- [x] **4. L3 — cleanup-round procedure into `CLEANUP.md` and `PHASE-BOUNDARIES.md`** (Sonnet).
  These files, not the plan's three manuals, are now the canonical home.
  - (a) `CLEANUP.md` §C now ranks by **declaration span** (header line to the next column-0 line,
    the round 1 / round 4 task 7 (`40b36fda`) method) with a corrected one-liner written in:
    `/^[^[:space:]]/` (any column-0 line) closes the span instead of the old blank-line-past-50
    test, which closed early and under-counted whenever a proof's true end was further on
    (`notes/Cleanup40.md` §3 flags its own figures as low for exactly this). Tested against
    `Pencil/MainComponent/ContractCurve.lean` (the new one-liner surfaces several mid-sized proofs
    — e.g. a 39- and a 34-line one — the old awk dropped entirely, since it only ever printed a
    declaration closed by `end`/`namespace` or one running past 50 lines to a blank line) and
    against the manual's own `CombinatorialRigidity/*.lean` glob (runs clean, same ranking as
    before up to the old method's off-by-one).
  - (b) `CLEANUP.md` §A gained round 3's invariance check, copied verbatim from
    `notes/Phase40-exposition.md` *Scope and standing rules*. Re-run at HEAD: 1 292 edges, hash
    `7c7ef987ce81e090`; 1 029 pins, hash `8225e0a2bc15ccdb` — both commands still run, and both
    figures are identical to round 4's close (`notes/Phase40-simplify.md` *Current state*),
    confirming no blueprint drift since.
  - (c) `CLEANUP.md` *Per-round work log* gained a new subsection naming what all five rounds'
    logs share beyond the template: the hygiene rule (a finding that would change a headline
    statement or a blueprint statement's strength is recorded, not acted on, not itself a stop);
    the two standing sections *Candidates for …* and *Moved to a later round*, each line mirrored
    into its target's own plan in the same commit; and, for a round that is an autopilot-queue
    row, *Autopilot: for the PI* (present even with no planned stop).
  - (d) `PHASE-BOUNDARIES.md`'s `formalization.yaml` bullet now spells out the headline-axioms
    harness, described as round 5's own open ran it (*Current state*, *Verified at the open*,
    above): a scratch file under `scratch/<phase-or-round>/` (gitignored) imports every
    `main_results` entry's `file:` module and prints `#print axioms` for each `declaration:`; its
    name list and imports are diffed against the yaml's fields first; it runs with `lake lean`,
    never `lake env lean` (which skips `[leanOptions]` and under-reports); its output is compared
    byte for byte against the last such run's, net of the harness's own path.
- [x] **5. L4 — round 3's defaults (a) and (d) into `blueprint/AUTHORING.md`** (Sonnet). (a) is now
  *Proof verbosity*'s **Cut comparisons with the project's own informal argument**, right before
  *The carve-out*: cut every comparison with the project's own informal argument; keep a reason the
  proof is shaped as it is, and the PI's 2026-10-03 amendment verbatim — "In cases where the
  informal argument might give more insight but we decided not to formalize it due to technical
  reasons, it could be worth mentioning as well" — as a short remark or formalization note; cut a
  stronger fact not proved here unless a reader would expect it. (d) is now principle E's *Node
  order*, right after the backward test's failure tells: a node may move within its chapter to cure
  a forward reference the test catches. Checked, not copied: defaults (b) and (c) are already
  principles D and B, and the note-placement rule is already `blueprint/SETUP-AND-PITFALLS.md`
  (lines 77–83). Repointed: ROADMAP's **PROSE** bullet and its queued-rounds bullet, and
  `notes/BlueprintExposition.md`'s pointer to default (a), all now name `blueprint/AUTHORING.md`
  instead of this log's *Decisions*; `notes/Cleanup40.md`'s **Status** likewise. This log's
  *Decisions* entries for (a) and (b)–(d) are now one-line *Promoted to* pointers (the PI's ruling
  and amendment stay verbatim in *Autopilot: for the PI*'s Stop-1 entry, untouched).

### FRICTION and the standing sweep

- [x] **6. F — FRICTION's `[resolved]` entries to `FRICTION-archive.md`** (Sonnet). Re-derived at
  build time, since the open's line numbers went stale under tasks 1–5's edits: 17 entries (the
  open's 14, itself already a revision of the plan's 2026-09-29 count of seven, plus the three
  `f02c2a9c` flipped), 281 lines (264 content + 17 blank separators). Moved verbatim to the end of
  the archive's *Resolved (project-internal)*, as `88436c0b` did; the two files' `git diff` `-`/`+`
  line multisets match exactly, confirming a pure relocation. Cross-reference sweep (each entry's
  title, and "the open FRICTION entry", across `.md`/`.lean`/`.tex`/`.py`): the one real stale
  pointer, `notes/Phase40-design.md` §3 STEPS' "the open FRICTION entry *The three-body step
  repeats…*", is left for task 8 as planned. The other hits (`TACTICS-GOLF.md` §26,
  `TACTICS-QUIRKS.md` §116 and §58's bare `FRICTION [resolved] *title*` pointers) are the
  project's established "name the friction-log system by title" convention — both files already
  tell a reader to grep *both* `FRICTION.md` and `FRICTION-archive.md` — so left unedited, as
  `88436c0b` did for the same pattern. No Lean doc comment names any of the 17: every
  `notes/FRICTION.md` mention under `CombinatorialRigidity/` is a generic "see `notes/FRICTION.md`"
  pointer or names a still-open `[mirror-candidate]`/`[idiom]` entry. `[mirror-candidate]`, the tag
  of 7 entries since Phase 39 (`d4f21ee3`), is now defined in *Entry format* (added to the STATUS
  list) and *Filing rule* (a new bullet): an `open` sub-flavor for a general-purpose lemma mathlib
  (or a project-owned API's own file) doesn't package, proved/worked around locally under a named
  helper, with a proposed signature and target file stated but deliberately not yet mirrored
  (import-cone cost, a one-off call site, or awaiting a second consumer) — revisit at a cleanup
  round or the next file-toucher. Done: `grep -c '^### \[resolved\]' notes/FRICTION.md` is 0.
- [x] **7. S — pointers to what rounds 1–4 deleted or changed** (Sonnet; `PHASE-BOUNDARIES.md`
  *Review project organization*). Re-derived at HEAD by grepping each deleted file and declaration
  name over the live manuals and surfaces (the open's line numbers had moved under tasks 1–6's
  edits); found no site the open's inventory missed. Every named item in ROADMAP, GOLF, QUIRKS
  and the blueprint manual got a short parenthetical, never a deleted lesson:
  - ROADMAP §39, *What landed*: `pencil_conjecture_of_arms_pair` "carrying two kernels" (it
    still takes the two, `hcontract` and `hsplit`; `40-simplify` task 10g, `f8c6b0d4`, restated it
    over every nonempty multigraph — the open's "retired by 10h" was wrong, the coordinator's fix), "the girth / degree-two-chain normal form" and item 6's laws in
    `TwoCut.lean` (both deleted, tasks 10i `1e7d78a9` and 10b `c48d323e`). ROADMAP §38:
    `cutEdge_finrank_assemble`, renamed `finrank_span_rigidityRows_cutEdge_eq` by task 10o,
    `919486d3`.
  - The eleven GOLF/QUIRKS worked-case sites (`ForestSurgery/MaximalChain.lean` ×2, `Girth.lean`,
    `Habitat.lean`/`c4_isProperRigidSubgraph`, `cutEdge_finrank_assemble`,
    `WitnessGeneral.lean`'s two declarations, `Pencil/Base.lean` ×2, `Motive.lean`'s
    `ncard_closedNbhd_inter_le_two_of_girthGE`, `weldedRank_eq`) each get the deleting task and sha
    (all 10i `1e7d78a9` except `cutEdge_finrank_assemble`'s rename, 10o, `weldedRank_eq`'s
    deletion with `TwoCut.lean`, 10b `c48d323e`, and `Pencil/Base.lean` itself, deleted whole by
    10j `8f297c7d` after 10i removed its two helpers) inline; none renumbered.
  - `blueprint/SETUP-AND-PITFALLS.md`'s "that round left them" note on
    `thm:pencil-conditional-realization-pair` gained one line: task 10h (`528381ef`, verdict `m5`)
    moved the notes, the node now draws filled.
  - Left as the open said: ROADMAP's round-2 Status row's `TwoCut.lean` mention (history); the
    stale sites inside Phase 40's notes and design doc (tasks 8–13).

### The compressions (after the lifts)

- [x] **8. C1 — `notes/Phase40-design.md` §3, the layer plan and proof map** (Opus; landed
  2026-10-04). §3 went from 928 lines to 553 (10 852 words to 6 285), the doc from 1 470 to 1 096.
  Every heading stays verbatim, and so do the done paragraphs (*CUT/BRIDGE* to *CONTRACT-A done*,
  the routes the sub-notes and `BlueprintExposition.md` point at), the proof-map tables, the step
  contract, *The provisional grouping* with the PI's dated calls, COVERAGE's numbered sub-phases,
  D1–D4 and *Lean reuse*, and every source citation. Each tracked item is now its verdict: paid by
  round 1 (task, sha), or left by round 3's call sanctioned at round 4's Stop 2. Brought to HEAD,
  each name grepped and each deletion's commit found by `git log -S`: CONTRACT-R as CONTRACT-A's
  corollary and the merged contraction section (10p `993b9e74`, 10q `91755996`); `TwoCut.lean`,
  `deficiency_eq_of_vertexTwoCut`, `jointMotions`, `weldedRank` (10b `c48d323e`);
  `MaximalChain.lean` and two Phase 39 lemmas (10i `1e7d78a9`);
  `noRigid_of_simple_of_ncard_eq_three` (10j `8f297c7d`); `rem:pencil-hinge-affine` (round 3,
  `a5f782a5`). Fixed: the FRICTION pointer, now `notes/FRICTION-archive.md`; the header's size
  sentence (9 Lean anchors). Dropped labels: (MC-49), (MC-88), (MC-120), which no verdict needs.
  Anchors: the 6 Lean ones into §3 and every non-Lean one resolve; none repointed.
- [x] **9. C2 — `notes/Phase40-design.md`, the rest** (Sonnet; landed 2026-10-04). The doc 1 096
  lines to 864. §1–§2 and §4–§5 untouched but for one fix (below); every "§3 …" pointer in them
  still resolves to §3 as task 8 left it. §6 (the retired fallback) collapsed to one verdict
  paragraph; §7's five deferred items and §3's eight tracked cleanup-round items collapsed to one
  line each, detail left where it already lived (`notes/Phase40-exposition.md` *The build-or-leave
  items*, `notes/Cleanup40.md` §2, `notes/Phase40-factor.md`). *Appendix — the reusable
  second-reader brief* untouched (task 3). *Appendix — the STEPS recon's tracked spike* keeps its
  heading, provenance and where each of the three pieces landed (all three did); the 140-line
  verbatim spike dropped to git (full text through `cc376480`, the commit before this cut), no
  `lake env lean` recipe kept. Fixed: the header's anchor-count sentence now also names task 9;
  §5's "Do not: edit `hK`, `hbareSplit`, … which stay as conditional theorems" (round 4 deleted
  them, §6); §7's stale "§3's *There is no landed cut-vertex deficiency law* note" pointer (dropped
  with the paragraph it was in). Anchor inventory: 9 Lean (unchanged — `X0.lean` 14 into §1, 36 to
  the bare file, `ContractCurve.lean` 1056 into the appendix; all resolve, none repointed); the
  non-Lean citations of §1, §2, §4–§7 and the two appendices checked against their targets, all
  still resolve.
- [x] **10. C3 — `notes/Phase40a.md`–`Phase40d.md`** (Sonnet; landed 2026-10-04). 371 lines to 204
  (45, 67, 47, 45): each now a **Status** line, one *Current state* paragraph, *Decisions made* as
  one-line verdicts and a *Hand-off* naming the actual next sub-phase, in place of the stale
  "**Next: …** … **not yet opened**" every header carried (Phase 40 closed 2026-09-29, long after
  these were written). *Architectural choices* kept only in 40b, where the design doc's §3 CARRIER
  anchor needs it (line 155's "uncurried pictures, one `X0Attains` carrying a Zariski-open set of
  attaining heights"). Preserved: the *Decisions made* entry "2026-09-26 C1a" (`Carrier.lean` 90,
  `Configuration.lean` 75), the slice names C1a, C1b, C2, C3, C4, C5′ (`Carrier.lean` 16,
  `Configuration.lean` 15) and DUAL-K (`ProjectiveInvariance.lean` 34). Dropped, since no anchor
  needed it and one entry was stale: 40a's "What keeps `6 ≤ D`" declaration list, one of whose four
  named siblings (`edgeBound_of_noRigid_of_degree_two`) round 4 task 10i (`1e7d78a9`) had already
  deleted; 40c's and 40d's "Cleanup-round item" checkboxes, both already tracked done in
  `notes/Phase40-design.md` §3 FLAT/BRIDGE; the four files' "project-organization review: no new
  item" sentences, one of which cited `notes/pencil/CLAUDE.md` status-line text that has since
  moved on. Anchor inventory re-derived at HEAD before the cut (0 Lean for 40a and 40d, 5 for 40b,
  1 for 40c — the table's 2026-09-29-era *Other* counts were stale and unused) and walked after it:
  every Lean and non-Lean anchor resolves, none repointed.
- [ ] **11. C4 — `Phase40e.md`–`Phase40h.md`** (Sonnet; 454 lines). As task 10. Preserve 40e's
  "Build 2, BRIDGE for every `k`" (`Cut.lean` 411). 40f's, 40g's and 40h's PI decisions (1–4, 1–4
  and 1–5) are cited by number: `Chain.lean` 30 ("the PI's decision 3", 40g),
  `Configuration.lean` 16 ("PI decision 5", 40h), design §3 STEPS (40f's decisions 2 and 4) and
  `notes/Phase40-cleanup.md` (40g's decision 2). Their three `adjudication` blocks (25 lines) are
  copies of `notes/pencil/adjudications.md`; check that, then make each a pointer plus one line per
  numbered decision. Fix 40h's *Hand-off* and *Blockers*: rounds 1 and 4 paid their cleanup-round
  items, and the FRICTION entry they call open is resolved.
- [ ] **12. C5 — `Phase40i.md`–`Phase40l.md`** (Sonnet; 473 lines). As task 10. Preserve 40k's
  coordinator calls 4, 5 and 8 and its checklist (`ContractCurve.lean` 16, "call 5"; design §3,
  three places), and 40l's *Architectural choices* with the departures D1–D3
  (`SparseDeficiency.lean` 20). Bare Lean anchors: 40i `Orbit.lean` 13; 40j `SplitOff.lean` 15;
  40k `Contract.lean` 36, `ContractAdditive.lean` 13 and 37, `ContractCurve.lean` 15 and 89; 40l
  `SparseDeficiency.lean` 58.
- [ ] **13. C6 — `Phase40m.md`–`Phase40p.md`** (Sonnet; 437 lines). As task 10. Preserve 40m's
  *Current state* (design §3) and *Decisions made* (`notes/pencil/adjudications.md`), and 40p's
  *Architectural choices* item 2 (`adjudications.md`) and *Hand-off* (ROADMAP, `notes/Phase39.md`,
  `notes/pencil/CLAUDE.md` and `notes/MolecularConjecture.md` point at 40p). Bare Lean anchors:
  40n `GenericBase.lean` 37 and `Statements.lean` 40; 40o `GenericEar.lean` 28,
  `GenericSteer.lean` 36, `GenericTriangle.lean` 40 and `Reseed.lean` 29; 40p `GoodEar.lean` 27
  and `Statements.lean` 40. Fix 40p's *Decisions*, "the landed Lean stays as conditional
  theorems": round 4 retired it.
- [ ] **14. C7 — `notes/Phase40-cleanup.md`** (Sonnet; 491 lines). One line per landed task,
  naming its commit (round 4's log is the model); the §A walk, the §C screen and the close's
  blocks collapse to verdicts. Preserve every task number (`notes/Cleanup40.md` §2 cites tasks 2,
  8, 24, 26, 27, 32, 37, 38, 41 and 43, FRICTION task 17); task 45's figures verbatim
  (`scripts/cleanup-smell-sweep.py`'s docstring cites them as round 1's run); *Candidates for
  `40-simplify`* whole (`Cleanup40.md` §2 points at its detail, the verdicts' `a1`–`a7` are its
  items, FRICTION cites it); and *Moved to a later round*.

### The coordinator's grooming, and the close

- [ ] **15. G — the dispatch log's Phase 40 grooming** (the coordinator's own commit; a builder
  does not edit the log). 45 rows dated 2026-09-25 to 2026-10-04 (one from Phase 39's close, 34
  from Phase 40, 10 from rounds 1–4) were never distilled: Phase 40's close left that to the
  coordinator (`notes/Phase40p.md` *Decisions*), and *Findings* ends at F43. Distill the recurring
  exceptions into new findings (the rows name gate-invisible defects caught in verification,
  coordinator-spec defects, recon calls settled under "follow precedent", and Sonnet prose tasks
  that needed Opus correctives), prune what is distilled, and settle F1: tasks 8–9 are the third
  `*-design.md` compression, its trigger, so this task follows them. A promotion into
  `.claude/commands/coordinate-phase.md` is the coordinator's; one beyond its remit goes to the
  close's *For the PI*.
- [ ] **16. P — `.claude/autopilot/system-prompt.md`'s round pointers** (no commit of its own:
  task 17's report discharges it). Line 60 sends a cleanup round's statement-changing finding to
  "a candidate for `40-simplify`", which is closed; line 46 names the rounds' planned stops. Not
  edited: the file is the PI's autopilot rules, written at the setup session (`06d175b8`), and
  after this round the queue's only row is ORIGAMI, attended (the coordinator's call at the open).
  Its disposition is one line in the close's *For the PI*.
- [ ] **17. X — close the round** (Opus). `.claude/autopilot/queue.toml`'s `40-docs` row to
  `done = true`; the ROADMAP row to ✓, re-thinned; the queued-rounds bullet to all five closed,
  ORIGAMI next and attended; `notes/Cleanup40.md`'s **Status**; the build, `lake lint` and the
  axioms harness as at the open; this log closed as round 4's was. *For the PI*: task 16's line;
  the auto-loaded `CLAUDE.md` suite, 1 704 lines at the open (root 381, `CombinatorialRigidity/`
  456, `notes/` 203, `blueprint/` 664), whose trimming §2 leaves out, and FRICTION's open
  `[process]` entry on it, which still says 1 695; task 15's outcome; any *Candidates for the PI*.

### Seen at the open, not a task

- Backticked paths older than Phase 40 that no longer resolve, among them
  `Molecular/RigidityMatrix.lean` (ROADMAP, GOLF, `home_page/index.md`,
  `notes/MolecularConjecture.md`); `ForestSurgery.lean`, `PebbleGame.lean` and `molecular.tex`
  (ROADMAP); `Molecule/Pencil.lean` (GOLF); `CaseIII/Relabel.lean` and `MeetHodge.lean` (QUIRKS);
  `Density.lean`, `GlobalRigidity.lean` and `LocalRigidity.lean` (`DESIGN.md`). They predate
  rounds 1–4, whose deletions are task 7's.
- Checked, no lift: the PI's placement convention ("Convention everywhere", 40f; "Convention,
  split Carrier", 40h; 40n, 40p, rounds 1–2) is `CombinatorialRigidity/CLAUDE.md` *Engineering
  conventions* (a lemma in its definition's file, the ~1500-line tripwire). Round 3's defaults
  (b), (c) and its note-placement rule are already in `blueprint/` (task 5).
- `notes/check-phase-note.py` skips `Phase40-*.md` by design (`NOTE_RE`), so every round's log
  was gated by hand. The `[DecidableEq β]` suppressions outside the pencil tree (task 2 (a)) are
  Lean edits, not this round's. Dispatch-log F40 (`check-roadmap-cells.py`) stays the
  coordinator's open tooling item. `notes/MolecularConjecture.md`'s "ORIGAMI … the next phase to
  open" stays true after this round.

## Candidates for the PI

A finding that would change a headline statement or a blueprint statement's strength: one line
each, with the task that found it. Recorded, not acted on, not a stop; the close lists them.

- None yet.

## Moved to a later round

Each line gives the task, its target (an entry in ROADMAP's queue, since no cleanup round follows)
and a one-line reason; the same line goes into the target in the same commit.

- None yet.

## Blockers / open questions

- None.

## Hand-off / next phase

**Next commit: task 11 (C4)**, `notes/Phase40e.md`–`Phase40h.md` (Sonnet; 454 lines), compressed
the same way task 10 compressed 40a–40d. Preserve 40e's "Build 2, BRIDGE for every `k`"
(`Cut.lean` 411); 40f's, 40g's and 40h's PI decisions (1–4, 1–4 and 1–5), cited by number at
`Chain.lean` 30, `Configuration.lean` 16, design §3 STEPS and `notes/Phase40-cleanup.md`; check
their three `adjudication` blocks against `notes/pencil/adjudications.md` before reducing each to
a pointer plus one line per decision. Fix 40h's *Hand-off* and *Blockers* (rounds 1 and 4 already
paid the cleanup-round items and resolved the FRICTION entry it calls open). Then tasks 12–14
(the remaining sub-note groups), the coordinator's grooming (15) and the close (17).

## Decisions made during this round

- **The granularity** (the open): 17 tasks, one commit each. Lifts go one commit per target
  manual, the design doc in two (§3, then the rest), and the sub-notes in four groups of 371–473
  lines.
- **The order** (the open): the surfaces first, as they are independent. Lifts before the archive
  sweep, since a lifted `[idiom]` can become archive-ready, and before the compressions, so that
  what is lifted is compressed after. The grooming after the design doc, whose re-derived anchor
  inventory settles F1.
- **Homes** (the open): a lesson goes to its content type's canonical home (`notes/CLAUDE.md`
  *One canonical home*), not only the plan's three manuals. Cleanup-round procedure is
  `CLEANUP.md`'s, the close's checks `PHASE-BOUNDARIES.md`'s, blueprint conventions
  `blueprint/AUTHORING.md`'s; round 3's promotion of its defaults (e) and (f) there is the
  precedent.
- **Dispositions** (the open, by the test): compress the design doc (9 Lean anchors), all 16
  sub-notes (6 or fewer each) and the round-1 log; freeze the exemplar and the verdicts; leave the
  rest, for the reasons in the inventory.
- **`.claude/autopilot/system-prompt.md` is not edited** (the coordinator's adjudication at the
  open): the PI's rules file, written only at the PI's setup session. Until the close, a
  statement-changing finding goes to *Candidates for the PI*.
