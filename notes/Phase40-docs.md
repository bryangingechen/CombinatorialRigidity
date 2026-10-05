# Phase 40 cleanup round 5/5 — `40-docs`, project organization (work log)

**Status:** in progress (opened 2026-10-04). Round 5, the last of the five post-Phase-40 cleanup
rounds. Their order, stops and the PI's decisions are in `notes/Cleanup40.md`, and
`.claude/autopilot/queue.toml` is the authority for which rounds are done. The work is
`CLEANUP.md` D over Phase 40 and rounds 1–4: lift their cross-cutting lessons, compress Phase 40's
notes and design doc with every anchor kept, archive FRICTION's `[resolved]` entries, align the
user-facing surfaces with `intro.tex`, and run the standing project-organization sweep. No
planned stop. The full task list below was populated at the open; tasks 1 and 2 landed
2026-10-04. **Next concrete task:** task 3 (L2), `DESIGN.md`'s two cross-phase rationales (Opus,
docs only). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop: the round opens and closes unattended (`notes/Cleanup40.md` §1). An unplanned
`NEEDS_PI` entry goes here, newest first.

## Current state

**Next commit: task 3 (L2)** (*Lemma checklist*). Of the 17 tasks, task 1 (U) is done
(2026-10-04: README, home page and `formalization.yaml` on `intro.tex`'s reader path). Task 2
(L1) is done (2026-10-04: new `TACTICS-QUIRKS.md` §115 (`unusedDecidableInType`) and §116
(a `<;>`-chained flexible `simp`'s per-goal "Try this"), both with symptom-index lines; worked
cases added to §55 (a spike's `#print axioms` lines passing the warning-only gate) and §58 (the
40c `Fin (1 + 2)` ℕ/ℤ atom-split); `TACTICS-GOLF.md` §26 widened from `push_neg` to the
`if_pos`/`if_neg`/`dif_pos`/`LinearEquiv.ofLinear` renames; five FRICTION entries pointed at their
lift, three flipped to `[resolved]`, and the two `if_pos` entries merged into one — (a) stays
`[idiom]` as the task said). Task 15 (G) is the coordinator's own commit, and task 16 (P) has no
commit of its own. Nothing is mid-stream.

**Verified at the open** (this commit, docs only; the Lean tree is `654bae8a`'s, the blueprint
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

- [x] **1. U — the user-facing surfaces, aligned with `intro.tex`** (Opus; this commit; round 3's
  task 26). README's and the home page's paragraph, still identical, is now **The pencil
  conjecture (phases 39–40, complete)**, re-summarized on `intro.tex`'s reader path: the pencil
  realization and its molecular reading, the two *main-component statements*, the pictures lifted
  into space and the lifting space. The home page's rows 39–40 and `formalization.yaml`'s five
  sites are renamed, its `status.scope` and `fidelity` re-summarized the same way; no
  `declaration:`, `file:` or `lean:` field changed. Done-check: the `git grep` for the four old
  phrases over the three files is empty, and `ruby -ryaml` parses the yaml. ROADMAP's Phase-39
  title and `RESEARCH-ARC.md` left alone.

### Lifts (before the archive sweep and the compressions that read the same notes)

- [x] **2. L1 — Lean idioms into `TACTICS-QUIRKS.md` and `TACTICS-GOLF.md`** (Sonnet; this commit).
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
- [ ] **3. L2 — `DESIGN.md`: two cross-phase rationales** (Opus: new rationale sections).
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
- [ ] **4. L3 — cleanup-round procedure into `CLEANUP.md` and `PHASE-BOUNDARIES.md`** (Sonnet).
  These files, not the plan's three manuals, are the canonical home (*Decisions*).
  - (a) `CLEANUP.md` §C: rank proofs by declaration span, from the header line to the next
    column-0 line, as rounds 1 (`notes/Phase40-cleanup.md` *Current state*) and 4 (task 7) did. The
    awk stops at a proof's first blank line past 50 lines and under-counts (`notes/Cleanup40.md`
    §3). Write the span one-liner in.
  - (b) `CLEANUP.md` §A: round 3's invariance check, verbatim from `notes/Phase40-exposition.md`
    *Scope* (the dependency graph's fingerprint and the pins' hash). It sees a changed `\uses` edge
    or `\leanok`, which `checkdecls` and `lint.sh` cannot; rounds 3 and 4 gated on it.
  - (c) `CLEANUP.md` *Per-round work log*: what all five rounds' logs share. The hygiene rule (a
    finding that would change a headline statement or a blueprint statement's strength is recorded
    for a later round or the PI, not acted on, not a stop); the standing sections *Candidates for
    …* and *Moved to a later round*, each line mirrored into its target's plan in the same commit;
    and, for an autopilot round, *Autopilot: for the PI*.
  - (d) `PHASE-BOUNDARIES.md` *When this commit closes a phase*, the `formalization.yaml` bullet:
    the headline-axioms check as Phase 40's closes and every round's open and close ran it. A
    scratch file imports each main result's `file:` and prints `#print axioms` for each
    `declaration:`; its names (in order) and imports are diffed against the yaml; it runs with
    `lake lean`, never `lake env lean`; its output is compared byte for byte with the last run's.
- [ ] **5. L4 — round 3's defaults (a) and (d) into `blueprint/AUTHORING.md`** (Sonnet).
  **PROSE** will apply them, and ROADMAP's **PROSE** bullet points at `notes/Phase40-exposition.md`
  *Decisions* for them. (a): cut every comparison with the informal argument; keep a reason the
  proof is shaped as it is, and an argument that gives more insight but was not formalized for a
  technical reason (the PI's amendment, 2026-10-03, verbatim in that log's *Autopilot: for the
  PI*); cut a stronger fact not proved here unless a reader would expect it. (d): a node may move
  within its chapter to cure a forward reference (principle E's backward test). Defaults (b) and
  (c) are already principles D and B, and the note-placement rule is already
  `blueprint/SETUP-AND-PITFALLS.md`: check them, do not copy. Then repoint the **PROSE** bullet
  and `notes/BlueprintExposition.md`'s pointer to default (a) at `AUTHORING.md`, and make round 3's
  *Decisions* entries one-line *Promoted to* pointers (the ruling's words stay in its Stop-1 entry).

### FRICTION and the standing sweep

- [ ] **6. F — FRICTION's `[resolved]` entries to `FRICTION-archive.md`** (Sonnet). 14 at the open
  (the plan's "seven" was the 2026-09-29 count), 232 lines, at lines 101, 117, 145, 190, 208, 292,
  321, 342, 421, 576, 2480, 2978, 2988 and 3041, plus any entry task 2 flipped. Move each
  verbatim to the end of the archive's *Resolved (project-internal)*, as `88436c0b` did. Each
  entry's fix still resolves (checked at the open). One inbound reference was found:
  `notes/Phase40-design.md` §3 STEPS calls *The three-body step repeats the four-body step* "the
  open FRICTION entry", which task 8 rewrites; repoint any other a build-time grep finds. Also, the
  header's *Entry format* and *Filing rule* do not define `[mirror-candidate]`, the tag of 7
  entries since Phase 39 (`d4f21ee3`): add it, with the meaning those entries give it. Done:
  `grep -c '^### \[resolved\]' notes/FRICTION.md` is 0.
- [ ] **7. S — pointers to what rounds 1–4 deleted or changed** (Sonnet; `PHASE-BOUNDARIES.md`
  *Review project organization*). Rounds 1–4 deleted six files (`Pencil/Base.lean`,
  `Escape.lean`, `Habitat.lean`, `TwoCut.lean`, `Induction/Girth.lean`,
  `Induction/ForestSurgery/MaximalChain.lean`) and deleted or renamed 124 declarations. Sites
  outside Phase 40's notes:
  - ROADMAP §39, *What landed*: `pencil_conjecture_of_arms_pair` "carrying two kernels", "the
    girth / degree-two-chain normal form", and item 6's laws in "`TwoCut.lean`". Round 4 retired
    all three (10h, 10i, 10b); §40 says so only of the design doc's §6. ROADMAP §38:
    `cutEdge_finrank_assemble`, which 10o published as `finrank_span_rigidityRows_cutEdge_eq`.
  - Worked cases whose file or declaration is gone. GOLF 528 (`ForestSurgery/MaximalChain.lean`)
    and 1186–1187 (`girthGE_of_noRigid_of_three_le_degree`, `Girth.lean`). QUIRKS 2101
    (`Habitat.lean`, `c4_isProperRigidSubgraph`), 2140 (`cutEdge_finrank_assemble`), 2595
    (`MaximalChain.lean`), 2682 (`hasGenericPencilRealization_of_independent_pencilRow_target`),
    3401–3404 (`exists_coord_linearIndepOn_pencilChartPoint_perBody`), 3919 and 3944
    (`Pencil/Base.lean`), 4174 (`Graph.ncard_closedNbhd_inter_le_two_of_girthGE`) and 4238
    (`weldedRank_eq`). Per site, name the surviving equivalent, or add "(deleted by `40-simplify`,
    `<sha>`)"; never delete the lesson.
  - `blueprint/SETUP-AND-PITFALLS.md` 81–83: "moving its notes changes the graph, so that round
    left them". Round 4 moved them (10h, `m5`).
  - Left: ROADMAP's round-2 Status row names `TwoCut.lean` as that round's surface, which is
    history. The stale sites inside Phase 40's notes and design doc belong to tasks 8–13.

### The compressions (after the lifts)

- [ ] **8. C1 — `notes/Phase40-design.md` §3, the layer plan and proof map** (Opus: what is
  settled is a judgment, and most anchors land here). Lines 114–1041; STEPS alone is 483 lines.
  Collapse each closed layer's recon arcs, plan tables and tracked-item lists to cited verdicts,
  leaving the blow-by-blow to git. Preserve:
  - the headings and codes the anchors name: §3, SPINE2, CARRIER, FLAT, BRIDGE, STEPS (with SHORT
    in it), COVERAGE, MOTIVES and *The blueprint chapter*;
  - the sub-items cited by name: STEPS' *CHAIN done*, *SHORT done*, *SPLITOFF done* and
    *CONTRACT-A done* (`notes/BlueprintExposition.md`, `notes/pencil/adjudications.md`); STEPS'
    *Tracked todo, carried past 40f's close (PI decision 2…)* (`ContractCurve.lean` 83);
    COVERAGE's departures D1–D3 (`BlueprintExposition.md`) and its *Lean reuse*; the PI's dated
    sub-phase calls;
  - the Lean anchors (the table above), every source citation, and each (MC-…) label a verdict
    needs.

  Fix: STEPS' "the open FRICTION entry *The three-body step repeats…*", resolved in round 1 and
  archived by task 6.
- [ ] **9. C2 — `notes/Phase40-design.md`, the rest** (Sonnet). The header, §1–§2, §4–§7 and the
  appendices: lines 1–113 and 1042–1472. Preserve §1 (`X0.lean` 14), §2, §4 (task 3's entries as
  pointers) and §5. §6, the retired fallback, cited about 18 times (`notes/pencil/adjudications.md`,
  the verdicts, ROADMAP, the two attack `state.md`s, `notes/Phase40p.md`, `W4-reopen.md`), becomes
  one verdict paragraph. §7, the carried index (about 18), which round 4 marked paid item by item,
  keeps one line per item. *Appendix — the reusable second-reader brief* stays verbatim (task 3).
  *Appendix — the STEPS recon's tracked spike* (`ContractCurve.lean` 1056, `notes/Phase40e.md`)
  keeps its heading, provenance and where each of the three pieces landed (all three did); the
  140-line verbatim spike goes to git. Fix: the header's "11 live Lean anchors" (9 at the open;
  re-count) and its size; §5's "Do not: edit `hK`, `hbareSplit`, … which stay as conditional
  theorems" (round 4 retired them); the appendix's `lake env lean` re-run recipe, if it stays.
- [ ] **10. C3 — `notes/Phase40a.md`–`Phase40d.md`** (Sonnet; 371 lines). Make each the archive
  `notes/CLAUDE.md` *Forward-weighted note* describes: a **Status** line, one *Current state*
  paragraph (what landed, where), a *Hand-off* naming the next sub-phase, and *Decisions made* as
  one-line verdicts; *Architectural choices* only where an anchor needs it. A verdict that quotes
  the PI keeps the words or points at `notes/pencil/adjudications.md`. Preserve 40b's *Decisions
  made* entry "2026-09-26 C1a" (`Carrier.lean` 90, `Configuration.lean` 75), its slice names C1a,
  C1b and C2–C5′ (`Carrier.lean` 16, `Configuration.lean` 15) and DUAL-K
  (`ProjectiveInvariance.lean` 34). Fix: all four headers' "**Next: …** … **not yet opened**".
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

**Next commit: task 3 (L2)**, `DESIGN.md`'s two cross-phase rationales (Opus, docs only): (a) new
mathematics found by formalization is second-read before it is built on (the design doc's
*Appendix — the reusable second-reader brief* and §5 stay the home; this is a *Promoted to*
pointer), and (b) genericity without dimension theory beside *Genericity device (Claim 6.4/6.9)*
(design §4). Both get *Promoted to `DESIGN.md`* pointers, which task 9 keeps. Then task 4 (L3,
cleanup-round procedure into `CLEANUP.md`/`PHASE-BOUNDARIES.md`) and task 5 (L4, round 3's
defaults into `blueprint/AUTHORING.md`), the FRICTION archive and the standing sweep (6–7), the
compressions (8–14), the coordinator's grooming (15) and the close (17).

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
