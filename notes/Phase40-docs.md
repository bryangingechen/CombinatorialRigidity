# Phase 40 cleanup round 5/5 — `40-docs`, project organization (work log)

**Status:** in progress (opened 2026-10-04). Round 5, the last of the five post-Phase-40 cleanup
rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` D over Phase 40 and rounds 1–4: lift their cross-cutting lessons, compress Phase 40's
notes and design doc with every anchor kept, archive FRICTION's `[resolved]` entries, align the
user-facing surfaces with `intro.tex`, and run the standing project-organization sweep. No
planned stop. The full task list below was populated at the open; tasks 1–14 landed 2026-10-04.
**Next concrete task:** task 15 (G), the dispatch-log grooming — the coordinator's own commit.
Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: the round opens and closes unattended (`notes/Cleanup40.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first.

## Current state

**Next: task 15 (G)**, the dispatch-log grooming — the coordinator's own commit. Of the 17 tasks,
1–14 are done (2026-10-04); each is one or two lines in the checklist below, not duplicated here.
Task 16 (P) has no commit of its own. Nothing is mid-stream.

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

**Next: task 15 (G)**, the dispatch-log grooming — the coordinator's own commit (a builder does
not edit `notes/dispatch-log.md`); then task 16 (P, no commit of its own) and the close (17).

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
