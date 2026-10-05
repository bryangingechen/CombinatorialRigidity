# Phase 40 cleanup round 5/5 — `40-docs`, project organization (work log)

**Status:** ✓ closed 2026-10-05 (opened 2026-10-04). Round 5, the last of the five post-Phase-40
cleanup rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. Docs only (`CLEANUP.md`
D over Phase 40 and rounds 1–4): lessons lifted, Phase 40's sub-notes compressed 1 735 → 935 lines
and its design doc 1 472 → 864 with every anchor kept, FRICTION's `[resolved]` entries archived,
the user-facing surfaces aligned with `intro.tex`. No stop; all 19 main results' axioms
unchanged. **Next concrete task:** none in this round; what comes next is in
`notes/Cleanup40.md`'s **Status**. Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop, and none arose: the round opened and closed unattended (`notes/Cleanup40.md`
§1), with no `NEEDS_PI` entry. The close's report for the PI is under *Hand-off*; it is a report,
not a stop.

## Current state

**Round 5 is closed** (task 17, docs only). All 17 tasks are done: 1–15 landed 2026-10-04/05,
task 16 (P) was discharged by the close's report, and each is one or two lines in the checklist
below, not duplicated here. Nothing is mid-stream, and nothing carried over: *Candidates for the
PI* and *Moved to a later round* stayed empty. The report for the PI is under *Hand-off*.

**Verified at the close** (task 17, 2026-10-05; the Lean tree is still `654bae8a`'s and the
blueprint TeX `993b9e74`'s, since the round touched neither):
- Whole-project `lake build` green, 2996 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`. The open's harness, `scratch/40-docs/Axioms.lean`, was re-diffed against the
  yaml's `declaration:` and `file:` fields (19 names in order, 14 imports: identical) and run with
  `lake lean` after the build; its output is the open's byte for byte.
- The anchors into the 16 sub-notes: every tracked file's `*…*` section name after a sub-note's
  filename, checked against that note's text. One dangled: `Cut.lean` 411–412 cite
  `notes/Phase40e.md` *Architectural choices*, a section task 11 folded into *Decisions made*. The
  close restored the heading in 40e as a three-line pointer (docs only; the Lean is unchanged).
- This log, by `parse` and `offenders` as below: 300 lines, header 104 words, no offenders.

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
| `Phase40-cleanup.md` | 491 | 0 | 14 | compressed (task 14): 491 → 448 |
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

- [x] **1. U — the user-facing surfaces, aligned with `intro.tex`** (Opus; `3dc6f67b`). README, the
  home page and `formalization.yaml` re-summarized on `intro.tex`'s reader path; no `declaration:`,
  `file:` or `lean:` field changed.

### Lifts (before the archive sweep and the compressions that read the same notes)

- [x] **2. L1 — Lean idioms into `TACTICS-QUIRKS.md` and `TACTICS-GOLF.md`** (Sonnet; `f02c2a9c`;
  §115's precedent and calibration brought to HEAD by the coordinator's next commit). Five
  cross-cutting idioms lifted (two new QUIRKS sections, two worked cases, one GOLF section
  widened); five FRICTION entries pointed at their lift, three flipped to `[resolved]`.
- [x] **3. L2 — `DESIGN.md`: two cross-phase rationales** (Opus; `91258678`). New sections
  *Genericity without dimension theory* and *New mathematics found by formalization is second-read
  before it is built on*; design §4 and §5 point at them.
- [x] **4. L3 — cleanup-round procedure into `CLEANUP.md` and `PHASE-BOUNDARIES.md`** (Sonnet;
  `6127b56e`). §C's long-proof ranking now measures declaration span; §A gained round 3's
  invariance check (re-run at HEAD, unchanged); a new *Per-round work log* subsection; the
  `formalization.yaml` bullet spells out the headline-axioms harness.
- [x] **5. L4 — round 3's defaults (a) and (d) into `blueprint/AUTHORING.md`** (Sonnet; `7f3e7fab`,
  coordinator `f64eb0b9`). *Proof verbosity* gained default (a) with the PI's amendment verbatim;
  principle E gained default (d) *Node order*; ROADMAP, `BlueprintExposition.md` and `Cleanup40.md`
  repointed.

### FRICTION and the standing sweep

- [x] **6. F — FRICTION's `[resolved]` entries to `FRICTION-archive.md`** (Sonnet; `fb61351f`). 17
  entries (281 lines) moved verbatim; `[mirror-candidate]` defined in FRICTION's *Entry format* and
  *Filing rule*.
- [x] **7. S — pointers to what rounds 1–4 deleted or changed** (Sonnet; `86ce7faf`, coordinator
  `30171a9b`). Every named item in ROADMAP, GOLF, QUIRKS and the blueprint manual got a short
  parenthetical naming the deleting task and sha; two wrong attributions (one from the open's own
  task text) were the coordinator's fix.

### The compressions (after the lifts)

- [x] **8. C1 — `notes/Phase40-design.md` §3, the layer plan and proof map** (Opus; `cc376480`). §3
  928 lines to 553, every heading and done paragraph verbatim, each tracked item now a cited
  verdict; anchor inventory re-derived and walked, none repointed.
- [x] **9. C2 — `notes/Phase40-design.md`, the rest** (Sonnet; `84827160`). The doc 1 096
  lines to 864; §6's and §7's items and §3's tracked cleanup-round items collapsed to verdicts; one
  stale §5 bullet fixed; 9 Lean anchors unchanged, all resolve.
- [x] **10. C3 — `notes/Phase40a.md`–`Phase40d.md`** (Sonnet; `cbb729db`). 371 lines to 204,
  each to the archive shape; preserved 40b's "2026-09-26 C1a" entry, its slice names and DUAL-K;
  dropped one stale declaration list (a named sibling already deleted by round 4) and two
  already-resolved cleanup-item checkboxes.
- [x] **11. C4 — `Phase40e.md`–`Phase40h.md`** (Sonnet; `b254ad9b`). 454 lines to 213;
  preserved "BRIDGE for every `k`" and the three `adjudication` blocks' PI decisions, each findable
  by number; fixed 40h's *Hand-off*/*Blockers* (rounds 1 and 4 already paid them) and 40f's stale
  open `hatt` TODO (closed at 40l's open) and superseded curve-based proof (round 4's
  restatement).
- [x] **12. C5 — `Phase40i.md`–`Phase40l.md`** (Sonnet; `96a939e2`). 473 lines to 224;
  preserved 40k's coordinator calls 4, 5, 8 and 12 (the G1/G4/G5 Lean-name mapping) and 40l's
  departures D1–D3, each findable by number. Fixed two stale cleanup items presented as still open
  (40j's call 9 and 40k's call 12, both paid by round 1) and 40i's pointer to a friction entry that
  task 6 had already archived (`notes/FRICTION.md` → `notes/FRICTION-archive.md`).
- [x] **13. C6 — `Phase40m.md`–`Phase40p.md`** (Sonnet; `3ed587bf`). 437 lines to 294, each
  to the archive shape; preserved 40m's recon-flags bullet (*Decisions made*, the one
  `notes/pencil/adjudications.md` names) and 40p's *Architectural choices* item 2 (N1–N4, cited by
  design §3 and `adjudications.md`) and *Hand-off* (pointed at by ROADMAP, `notes/Phase39.md`,
  `notes/pencil/CLAUDE.md`, `notes/MolecularConjecture.md`). Fixed 40p's stale *Decisions* line
  "the landed Lean stays as conditional theorems": round 4 retired it (`1e7d78a9`, `f8c6b0d4`,
  `654bae8a`), noted in place.
- [x] **14. C7 — `notes/Phase40-cleanup.md`** (Sonnet; `c9419d5e`, coordinator correction next; 491
  → 448 lines). The §A walk, §C screen and close's blocks collapsed to one-line verdicts; every task
  number, task 45's table and *Candidates*/*Moved to a later round* kept whole, none repointed. The
  seven round-1 candidates each got round 4's disposition appended (grep/`git log`-confirmed),
  nothing rewritten.

### The coordinator's grooming, and the close

- [x] **15. G — the dispatch log's Phase 40 grooming** (the coordinator; the commit after `e5b8eaee`).
  48 rows (2026-09-25 to 10-04, this round's three included) distilled into F44–F48 and pruned to
  git history, with a profile; F1 settled, promoted to `notes/CLAUDE.md`. Promoted: F44–F46 into
  the playbook (*Verification tiers*, the docs-only P calibration, the `hygiene` block, step 3
  *Resume and land*), F45 also into `CLEANUP.md` §D. For the close's *For the PI*: F47 (the
  "follow precedent" settlements, a possible change to when the PI is asked) and F48 (two
  missing gates: proof-level `\leanok` in `blueprint/lint.sh`, cleanup-round logs in
  `notes/check-phase-note.py`).
- [x] **16. P — `.claude/autopilot/system-prompt.md`'s round pointers** (no commit of its own:
  task 17's report discharges it; done, the first line of *For the PI* under *Hand-off*). Line 60
  sends a cleanup round's statement-changing finding to "a candidate for `40-simplify`", which is
  closed; line 46 names the rounds' planned stops. Not
  edited: the file is the PI's autopilot rules, written at the setup session (`06d175b8`), and
  after this round the queue's only row is ORIGAMI, attended (the coordinator's call at the open).
  Its disposition is one line in the close's *For the PI*.
- [x] **17. X — close the round** (Opus; this commit: what it verified is under *Current state*,
  its report under *Hand-off*). `.claude/autopilot/queue.toml`'s `40-docs` row to
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

- None: no task recorded one.

## Moved to a later round

Each line gives the task, its target (an entry in ROADMAP's queue, since no cleanup round follows)
and a one-line reason; the same line goes into the target in the same commit.

- None.

## Blockers / open questions

- None.

## Hand-off / next phase

**Round 5 is closed; there is no next step in it.** All five post-Phase-40 cleanup rounds are
closed and no round follows (`notes/Cleanup40.md`'s **Status**). The autopilot queue's next row is
ORIGAMI, which is attended: it opens with the PI, and takes its phase number then (ROADMAP *Queued
post-program phases*). Nothing carried over, and no task of this round is left open.

**For the PI** (a report, not a stop):
- **Task 16: `.claude/autopilot/system-prompt.md`'s cleanup-round lines.** Line 60 still sends a
  cleanup round's statement-changing finding to "a candidate for `40-simplify`", which is closed;
  line 46 names the cleanup rounds' planned stops (`40-exposition`'s sample section,
  `40-simplify`'s verdicts). Not edited: the file is the PI's autopilot rules, and the queue's only
  remaining row is ORIGAMI, attended. The PI may update or retire those two lines.
- **The auto-loaded `CLAUDE.md` suite is 1 711 lines** (root 381, `CombinatorialRigidity/` 456,
  `notes/` 210, `blueprint/` 664): 1 704 at the open, the 7 more being task 15's promotion of F1
  into `notes/CLAUDE.md`. Trimming it was outside the rounds (`notes/Cleanup40.md` §2). FRICTION's
  open `[process]` entry on the largest file, `blueprint/CLAUDE.md` (extract two long-form blocks
  to read-on-demand references), said 1 695: the Phase-40a close's figure, stated as current. A
  stale number, so this close updated it to 1 711, dated, keeping the 1 695. Whether and when to
  trim is the PI's (a later cleanup round, or a harness review, as the entry says).
- **Task 15's grooming** promoted F44–F46 and F1 (the playbook, `CLEANUP.md` §D and
  `notes/CLAUDE.md`) and left two findings open (`notes/dispatch-log.md` *Findings*):
  - **F47**: under a "follow precedent" answer the coordinator settled fifteen recon-flagged calls
    in 40i–40k, each checked against its source and recorded as the coordinator's, and none was
    reversed. Making that a rule would change when the PI is asked, so the PI would decide whether
    such calls may stay the coordinator's.
  - **F48**: two checks have no gate: a green node's proof-level `\leanok` (`blueprint/lint.sh`
    checks only the statement's), and the cleanup-round logs, which `notes/check-phase-note.py`'s
    name pattern skips, so a round's log is gated only by hand (every task of this round did it).
    The PI would decide whether to commission the two guards (tooling items, like F40).
- ***Candidates for the PI*:** none were recorded.

## Decisions made during this round

- **Granularity and order** (the open): 17 one-commit tasks; the surfaces first, the lifts before
  the archive sweep and the compressions that read the same notes, the grooming after the design
  doc.
- **Homes** (the open): each lesson to its content type's canonical home (`notes/CLAUDE.md` *One
  canonical home*): cleanup-round procedure to `CLEANUP.md`, the close's checks to
  `PHASE-BOUNDARIES.md`, blueprint conventions to `blueprint/AUTHORING.md`.
- **Dispositions** (the open, by the anchor test): compress the design doc, the 16 sub-notes and
  the round-1 log; freeze the exemplar and the verdicts; leave the rest (the inventory).
- **`.claude/autopilot/system-prompt.md` is not edited** (the coordinator's call at the open): it
  is the PI's rules file; a statement-changing finding goes to *Candidates for the PI*.
- **The close's report is under *Hand-off*, not *Autopilot: for the PI*** (the coordinator's call
  at task 17's dispatch, as round 4's close did): an open question there with no PI answer would
  stall the next autopilot session.
