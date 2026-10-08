# PROSE: the blueprint prose rounds (planning note)

**Status:** planned with the PI on 2026-10-07 and queued ahead of ORIGAMI as five autopilot rows
(`.claude/autopilot/queue.toml`). Round 1, `prose-laman`, opened 2026-10-07 and closed 2026-10-08
(`notes/Prose-laman-cleanup.md`, with the ledger `notes/Prose-findings.md`). Round 2,
`prose-molecular`, opened 2026-10-08 (`notes/Prose-molecular-cleanup.md`); rounds 3–5 have not
opened. These are five `CLEANUP.md` rounds over every blueprint chapter that round 3 of the
post-Phase-40 cleanup (`40-exposition`) did not rewrite. Four prose rounds go arc by arc, and a
fifth repairs the dependency graph and writes the findings report. There is one planned stop, after
round 1's sample section. The PI answered it on 2026-10-07 (§6; round 1's log, *Autopilot: for the
PI*), approving the sample, which is now the exemplar `notes/Prose-exemplar.md`. Round 1 wrote the
dependency-audit script `scripts/blueprint-deps.py` (§5), rewrote its twelve chapters in sixteen
slices, and recorded `F-001`–`F-047` in the ledger; round 2's open recorded `F-048`–`F-050`, and
its first twelve slices `F-051`–`F-088`. **Next concrete task:** round 2's task 2.13, the
third slice of `molecular-induction.tex`, the thirteenth of its eighteen (the round's log, *Lemma
checklist*).

## 1. The PI's decisions

**2026-10-03**, at `40-exposition`'s Stop 1 (verbatim in `notes/Phase40-exposition.md` *Autopilot:
for the PI*):

- "at some point we should also look into doing a rewrite round of the rest of the blueprint too."
- On a node bundling three facts: "Good catch; yes, we also struggled with nodes containing too much
  in earlier blueprint phases, I wouldn't be surprised if there are still some left around."
- "Right, we should be skeptical of any nonstandard terminology; certainly any such uses need a
  definition / explanation in a hard-to-miss place."

**2026-10-07**, the planning session:

- The request (verbatim): "I'd like to plan an autopilot phase that goes over earlier phases and
  cleans up the exposition there (as well as marks down any other inconsistencies / inefficiencies
  in the math or Lean, etc. that it happens to notice for later cleanup)."
- The PI's answers, as the chosen options:
  - On depth: **"Full rewrite, like round 3"**. Every subsection is rewritten to `40-exposition`'s
    register, in slices of 150–430 lines.
  - On stops: **"One sample stop"**. After round 1 opens, a sample subsection from a non-KT chapter
    is written, and the run stops for review.
  - On graph defects: **"Add a graph-repair round"**. A final round adds the missing `\uses` edges
    and splits bundled nodes under an expected-diff gate. Statement-strength changes are still only
    recorded.
  - On a dependency-audit script: **"Yes, at the open"**.

What follows from these decisions:

- Rounds 1–4 change prose only, as `40-exposition` did. Every graph and pin change waits for round
  5, so the invariance check gates every commit of rounds 1–4 against one baseline.
- No round edits the Lean library. Lean findings are recorded only (the PI's "marks down … for later
  cleanup"). The program's one piece of Lean-side tooling is the audit script under `scripts/` (§5).
- Every finding is recorded in one place, the ledger `notes/Prose-findings.md` (§4). Round 5 acts on
  its graph, terminology and status-surface entries, and reports the rest to the PI.
- Stop 1 is the only planned stop, and rounds 2–5 open and close unattended. ORIGAMI is attended and
  follows round 5, so the driver stops there. The PI reads round 5's findings report at that point.
- The rounds follow the blueprint's reading order. A chapter's backward anchor sweep (principle E)
  then checks against earlier chapters that are already in their final register. Introductions come
  last (principle F).

**2026-10-07**, at round 1's Stop 1 (verbatim in `notes/Prose-laman-cleanup.md` *Autopilot: for the
PI*): the sample approved as the exemplar for rounds 1–4, with the principle-B amendment and the
slice lists, and "These facts are classical." dropped from it. On the carve-out: "more than
following rules strictly though, the overriding goal is to make sure the result is
understandable."

## 2. Standing rules (all five rounds)

- **Hygiene** (`CLEANUP.md`). No round changes a headline statement or the strength of a blueprint
  statement. A finding that would need such a change goes to the ledger as an `S` entry. It is not
  acted on, and it is not a stop.
- **No Lean edits.** `CombinatorialRigidity/` and the toolchain files stay untouched for the whole
  program. Each close checks that `git diff --stat <open>.. -- CombinatorialRigidity/ lakefile.toml
  lake-manifest.json lean-toolchain` is empty. Each open confirms that the whole-project build is
  green, since `checkdecls` needs it. The `#print axioms` check on `formalization.yaml`'s main
  results runs at round 1's open and round 5's close, using the same harness as the post-Phase-40
  rounds (`PHASE-BOUNDARIES.md`, the close checklist). It must give `[propext, Classical.choice,
  Quot.sound]`, byte-identical to the last run.
- **Rounds 1–4 change prose only.** This is Phase 28's rule, as `40-exposition` applied it
  (`notes/Phase40-exposition.md` *Scope and standing rules*). Every node keeps its `\label`, its
  `\lean{…}` pins, its `\leanok` and its `\uses` edges. A statement block is edited only for
  register and anchoring. A node may move within its chapter to fix a forward reference
  (`blueprint/AUTHORING.md` principle E, *Node order*). Graph and node-shape findings go to the
  ledger for round 5.
- **The register** comes from three sources:
  - `blueprint/AUTHORING.md` principles A–F, with their 2026-10-03 clauses, which hold
    `40-exposition`'s defaults (a)–(f);
  - `40-exposition`'s exemplar, `notes/Phase40-exposition-exemplar.md`;
  - from Stop 1 on, round 1's pinned sample, `notes/Prose-exemplar.md`.

  Principle A's algorithmic carve-out applies in `dfs.tex`, `pebble-game.tex` and `executable.tex`.
  `retrospective.tex` keeps its own register and is out of scope (`AUTHORING.md` *The retrospective
  appendix*).
- **Crux nodes keep their depth.** A node with a *done* entry in `notes/BlueprintExposition.md`
  keeps its full proof (the crux carve-out, `AUTHORING.md` *Proof verbosity*). The rewrite changes
  its register, not its depth. If a node newly meets the ledger's criterion, it gets a capture line
  there and an `M` finding.
- **Evidence.**
  - Citations meet `CLAUDE.md` *Referencing prior work*. Each is checked against `.refs/`, and the
    commit that relies on a passage names it. Jordán 2016, Lee–Streinu 2008, Tay 1984, Tay–Whiteley
    1985, Whiteley 1988 and 1996, Nash-Williams 1961, Tutte 1961, Edmonds 1965, Crapo–Whiteley 1982,
    White 1994, KT 2011 and Jackson–Jordán are all there.
  - A source not in `.refs/` is checked against its DOI landing page. If that fails, the claim is
    weakened to "classical" or "see X" (`REFS.md`).
  - Claims about the Lean come from declarations' statements and bodies, never from docstrings, and
    from the audit script's report for what a pin reaches (§5).
- **Gates for every slice**, each run in the foreground with an explicit timeout:
  - `blueprint/lint.sh` and `blueprint/verify.sh` are green, and `checkdecls` is silent;
  - the invariance check (`CLEANUP.md` §A) equals the round's open values (rounds 1–4), or the
    task's expected diff (round 5, §3);
  - `blueprint/print/print.log` has 0 `LaTeX Warning` lines, and `verify.sh` has as many `WARNING:`
    lines as at the open;
  - `python3 notes/check-phase-note.py` is green on the round's log.

  Overfull boxes are counted at each open and close but not gated.
- **Rungs.** Every open, section, sample and graph-repair task runs on Opus, with a fresh agent per
  task. In `40-exposition`, two Sonnet slices needed Opus correctives, and then 22 Opus slices ran
  clean (`notes/dispatch-log.md` F44). Docs-only bookkeeping and the closes may run on Sonnet. Under
  autopilot, `.claude/autopilot/system-prompt.md` binds.
- **Each round's log** follows `CLEANUP.md` *Per-round work log*: the full task list at the open,
  one commit per task, the two standing sections, and `## Autopilot: for the PI`. Its *Candidates*
  and *Moved* sections hold one line per finding, naming the finding's ledger ID. The ledger holds
  the finding itself (one canonical home, `notes/CLAUDE.md`).

## 3. The rounds

The commit counts are estimates at `40-exposition`'s rate (a slice averaged about 270 lines). Each
open re-slices its chapters after reading them, and records that judgment as `40-exposition`'s open
did.

| # | Queue id | Work log | Chapters | Lines | Nodes | Commits |
|---|---|---|---|---|---|---|
| 1 | `prose-laman` | `notes/Prose-laman-cleanup.md` | `sparsity` → `executable` (12) | 5 011 | 153 | ~23 |
| 2 | `prose-molecular` | `notes/Prose-molecular-cleanup.md` | `matroid-union` → `meet` (8) | 4 792 | 151 | ~20 |
| 3 | `prose-algebraic` | `notes/Prose-algebraic-cleanup.md` | `algebraic-induction` + 5 sections | 4 221 | 106 | ~18 |
| 4 | `prose-applications` | `notes/Prose-applications-cleanup.md` | `bar-joint-3d` → `generic-lift` (5), `intro` | 3 640 | 95 | ~16 |
| 5 | `prose-graph` | `notes/Prose-graph-cleanup.md` | every chapter's graph | — | — | ~15 |

That comes to about 90 commits. Every round has the same shape:

- an Opus open: the log, baselines, a per-chapter diagnosis, and the task list;
- one commit per slice, in `chapter/main.tex` order. A chapter's opening section goes in its last
  slice;
- a close (`CLEANUP.md` *Workflow* 5). The close sets the round's queue row to `done = true`,
  updates ROADMAP's Status row (added at the open) and this note's **Status**, and adds a round note
  to `notes/BlueprintExposition.md`.

### Round 1 — `prose-laman`: Laman's theorem and the rigidity matroid

The round covers the chapters of the first two arcs (phases 1–11): `sparsity`, `laman`, `henneberg`,
`frameworks`, `henneberg-rigidity`, `trivial-motions`, `laman-theorem`, `rigidity-matroid`,
`count-matroid`, `dfs`, `pebble-game` and `executable`. Its sources are Jordán 2016, Laman 1970,
Henneberg 1911, Lovász–Yemini 1982, Asimow–Roth 1978, Lee–Streinu 2008 and Whiteley 1996.

Three things set these chapters apart:

- Phases 1–5 wrote them in backfill mode, and Lean devices sit in their statements, for example
  `\mathrm{typeI}\,G\,a\,b` and the fresh vertex $\mathrm{none}$.
- `sparsity.tex` is the chapter model that `blueprint/CLAUDE.md` names, so its rewrite updates that
  model.
- The pebble-game chapters fall under the algorithmic carve-out.

Tasks, in order:

1. **The open.** This includes choosing the sample. The default is `henneberg.tex`'s
   *Preservation of the Laman property*: 115 lines, typical of phases 1–6, with Lean devices in its
   statements.
2. **The audit script** (§5). The task also writes the script's first report into the ledger's
   `E` and `N` sections, together with the Lean baselines of §4.
3. **The sample**, followed by **Stop 1** (`NEEDS_PI`, §6).
4. **Pinning the exemplar.** The task transcribes the PI's answer verbatim into *Decisions*, copies
   the approved sample to `notes/Prose-exemplar.md` (frozen, like `40-exposition`'s), and lands any
   `AUTHORING.md` amendment the PI makes.
5. **The slices**, chapter by chapter.
6. **The close.**

### Round 2 — `prose-molecular`: body-bar, body-hinge and the molecular foundations

The round covers `matroid-union`, `body-bar` and `body-hinge` (phases 12–16, after Edmonds,
Nash-Williams, Tutte, Tay, Tay–Whiteley and Whiteley 1988). It then covers `extensor`,
`rigidity-matrix`, `deficiency`, `molecular-induction` and `meet` (phases 17–21a, KT §2–§4, and
White 1994 for the meet).

The post-Phase-23 cleanup rewrote the molecular chapters for the rigidity-theorist audience. This
round brings them to the 2026-10-03 clauses, which came later.

The round's most bundled nodes go to the ledger for round 5:

- `def:rigidity-matrix` (14 pins) and `lem:trivial-motions-rank-bound` (9);
- `lem:case-III-claim612-line-in-panel-union` in `meet.tex` (12);
- three in `deficiency.tex`.

Provisional slices (Stop 1, 2026-10-07; the open re-slices after reading), 19, each chapter's
opening in its last slice: `matroid-union`, `body-hinge`, `extensor` and `meet` one each;
`body-bar` two (42–374, 375–626); `rigidity-matrix` three (52–337, then 338–902 split at a node);
`deficiency` three (27–118, 119–523, 524–713); `molecular-induction` seven (43–260, 261–802 in two,
803–1308 in two, 1309–1551, 1552–1678). The long subsections have no subsubsections, so they split
at node boundaries. The open re-sliced these to 18: `body-hinge` rides with `body-bar`'s second
slice, and `deficiency`'s three run 27–271, 272–523 and 524–712 (`notes/Prose-molecular-cleanup.md`
*Decisions*).

### Round 3 — `prose-algebraic`: the algebraic induction

The round covers `panel-layer`, `case-i`, `case-ii`, `genericity-and-count` and `case-iii`, and then
the chapter preamble `algebraic-induction.tex` (KT §5–§6).

- Most of the ledger's *done* expositions are here (Phase 27, in `case-i` and `case-iii`), so the
  crux carve-out binds.
- Its prose has the most principle-A flags of any round (§7).
- Expect the smallest slices of the program.

Provisional slices (Stop 1), 16: `panel-layer` five (1–228, 229–1057 in three, 1058–1353);
`case-i` three; `case-ii` and `genericity-and-count` one each; `case-iii` five (1–237, 238–501,
502–1387 in three); then the preamble `algebraic-induction.tex`. Smaller slices are likely here.

### Round 4 — `prose-applications`: applications, continuations and the introduction

The round covers `bar-joint-3d`, `molecule-modelling` and `molecule-application` (phases 24–26),
then `jacobs` (phase 32) and `generic-lift` (phase 34).

The round ends with `intro.tex`, outside the reader path that `40-exposition` rewrote. That means
its four-arc *Organization* list, the continuation paragraph and *Reading this blueprint*:

- the list's phase numbers stay (`lint.sh` check 5b exempts `intro.tex`);
- its *genuine* (in the panel-hinge item) goes, per `AUTHORING.md`'s terminology dictionary.

Provisional slices (Stop 1), 13: `bar-joint-3d` and `molecule-application` one each;
`molecule-modelling` two (41–343, 344–477); `jacobs` four (58–275, 276–583, 584–881, 882–1053);
`generic-lift` three (55–438, 439–734, 735–1148); `intro` two (51–434, then 435–513 with the
opening).

### Round 5 — `prose-graph`: graph repairs and the findings report

The surface is every chapter's `\uses` edges, `\lean{…}` pins and node environments. That includes
`pencil.tex` and `main-component.tex`, because `40-simplify` moved its `c8a` here. The open re-runs
the script and triages the ledger's `E`, `N`, `T` and `U` entries into tasks. Each task names its
expected diff.

- **E, edges.** Add the missing `\uses` edges, one commit per chapter group. Remove an edge only
  when neither the statement, the proof prose nor the pins use it, and record the reason.
- **N, node shape.** For each bundled node, choose one of three fixes (principle D):
  - split it along its pins' roles;
  - unpin its helpers;
  - leave it, with a recorded reason.

  A split keeps each claim at its strength. A new node carries `\leanok` only where the honesty gate
  passes. `\cref`s and in-edges are retargeted by the script's reach report. Where the ledger
  recommends it, a load-bearing unpinned lemma gets a node.
- **T, cross-chapter terminology and notation.** Prose only.
- **U, status surfaces.** Align `README.md`, `home_page/index.md` and `formalization.yaml`'s text
  with the rewritten chapters.
- **R, the findings report.** The `S`, `L` and `M` entries are grouped, deduplicated and ranked.
  Each gets its evidence, a suggested disposition and a commit estimate. The task proposes a
  follow-up program as an unqueued ROADMAP bullet, which the PI queues. The report is not a stop.
- **X, the close.** The axioms check, the no-Lean-edit check, the queue row, ROADMAP, and this
  note's **Status**.

**The expected-diff gate** replaces the invariance check in this round:

1. Run `verify.sh`.
2. Take the script's `--dump` of the built graph's sorted edges and the label→pins map.
3. Diff it against the previous commit's dump. The diff must be exactly the task's listed changes. A
   split that only moves pins leaves the `lean_decls` hash unchanged; unpinning a helper changes it.

## 4. The findings ledger, `notes/Prose-findings.md`

Round 1's open creates the ledger. It is append-only through round 4; round 5 sets each entry's
disposition (done with its sha, left with a reason, or reported). Each finding is one line:

```
- **F-NNN** · <cat> · `<label or decl>` (`<file>`): the finding, in one or two sentences.
  *Evidence:* measured (script at <sha>) | read (Lean body, or source passage) | suspected.
  *Found:* <round> task N.
```

| Cat | What | Acted on by |
|---|---|---|
| `E` | a `\uses` edge missing or unbacked; a node the graph draws unfilled | round 5 |
| `N` | a node bundling unrelated results (principle D), a pinned helper, a load-bearing lemma with no node | round 5 |
| `T` | a term or notation used inconsistently across chapters, or a coinage whose definition is hard to find | round 5 (prose) |
| `U` | `README.md`, `home_page/index.md` or `formalization.yaml` text that contradicts a rewritten chapter | round 5 |
| `S` | a statement stronger or weaker than its pins, or a headline signature oddity | the PI, after the report |
| `L` | Lean: dead or duplicated code, a long proof or missed mathlib lemma, a docstring or comment that contradicts its body, an unused binder, inconsistent naming | a later cleanup round |
| `M` | mathematics and sources: an unverifiable citation, a gap between a prose argument and the Lean, a misattribution too large for its slice | the PI, after the report |

A slice fixes, rather than records, what is prose and local to the slice: register, anchoring, a
citation it can verify, and a terminology choice within its chapter.

**The bar for "notice".** A builder records what it meets while reading its slice's pins and
sources, and no slice runs a separate Lean audit. Systematic coverage comes from two places:

- the script (§5), for edges, node shape and liveness;
- a Lean baseline that task 2 of round 1 writes into the ledger's opening section: the counts from
  `scripts/cleanup-smell-sweep.py` over the whole tree, and the top 20 proofs from `CLEANUP.md` §C's
  ranking. These are inputs for the later Lean round, not tasks of this program.

## 5. The dependency-audit script (round 1, task 2)

The script is `scripts/blueprint-deps.py`, with a Lean metaprogram that it runs through `lake lean`,
never `lake env lean` (`CombinatorialRigidity/CLAUDE.md` *Lean LSP MCP*). It is committed, under
`notes/CLAUDE.md`'s rule that every script the project runs is committed.

**Inputs.**
- From `blueprint/src/chapter/**.tex`: every `\label`, `\lean{…}`, `\leanok`, and statement- and
  proof-level `\uses`.
- From `formalization.yaml`: the main results.

**The Lean side.** For each pinned declaration, the script collects the constants in its type and in
its value. It follows them through unpinned project declarations: those in `CombinatorialRigidity`
modules, including the `Mathlib/` mirrors, private declarations and auxiliary `match_`/`proof_`
declarations. It stops at pinned declarations and at constants from outside the project.

**The reports.**
1. For each node: the nodes its pins reach, split into reach through the type (statement) and reach
   through the value (proof). These are compared with its `\uses` to give two lists:
   - missing edges;
   - unbacked edges, meaning `\uses` that no pin reaches. These are often legitimate, so they are
     listed for a check, not as defects.
2. Pins outside the closure of every main result: `CLEANUP.md` §B's liveness, read from the Lean
   call chain.
3. Pins per node, with four or more flagged (principle D).
4. `--dump`: the built graph's sorted edges, parsed as the invariance check parses them, and the
   label→pins map. This is round 5's gate.

**Acceptance tests**, run in the script's own commit:
- **(a) A seeded defect.** In a scratch copy of the TeX, remove `lem:deficiency-zero-connected` from
  the proof `\uses` of `thm:pencil-x0-theorem-s`. This is `40-exposition`'s `m6`, which
  `40-simplify` added. The script must report that edge missing.
- **(b) Liveness.** `Graph.x0Attains_of_finrank_liftingSpace_eq_three` is the pin of
  `cor:pencil-flat-x0` and has no Lean caller (`notes/Phase40-simplify.md`, *For the PI*). The
  script must place it outside every main result's closure.
- **(c) Run time.** The script's run time goes in the task's log line.

If the task is still BLOCKED after one escalation, its route findings are salvaged into the log, it
is recorded as not done, and rounds 1–4 continue by reading. This is the autopilot rules' resolution
for a blocked cleanup task. Round 5's open then retries it once before triaging.

## 6. Stop 1: the sample (round 1, after task 3)

The stop's entry goes in `notes/Prose-laman-cleanup.md` *Autopilot: for the PI*. It includes:

- the sample's commit and its rendered text;
- the choices it made where these chapters differ from `40-exposition`'s. These include how Lean
  devices in statements are restated, where Jordán's terminology replaces the project's, and how the
  algorithmic carve-out reads;
- any `AUTHORING.md` amendment it proposes;
- the slice list for rounds 1–4, with its granularity judgment.

The PI answers in that section. Task 4 pins the approved sample as `notes/Prose-exemplar.md`, beside
`40-exposition`'s exemplar.

## 7. Baseline (2026-10-07, at `64bb9754`)

Round 1's open re-measured these at `6f4f7afa` and added the built graph's node and edge counts and
the invariance hashes (`notes/Prose-laman-cleanup.md` *Current state*). That log also records the
register screen's regex, which this section's figures did not.

- **Surface.** Rounds 1–4 cover 32 TeX files, 17 663 lines and 505 nodes. Out of scope:
  - `pencil.tex` (1 186 lines) and `main-component.tex` (5 518), which `40-exposition` rewrote;
    round 5 still touches their graph;
  - `retrospective.tex` (789);
  - `main.tex`.

  The whole blueprint has 657 statement environments and 1 030 pins (`blueprint/lean_decls`).
- **Nodes with four or more pins.**
  - 19 in scope:
    - `rigidity-matrix`: `def:rigidity-matrix` (14), `lem:trivial-motions-rank-bound` (9);
    - `meet`: `lem:case-III-claim612-line-in-panel-union` (12);
    - `jacobs`: `lem:square-cross-classification` (9), `lem:normal-cross-count-partition` (4),
      `def:two-core` (4);
    - `molecule-modelling`: `lem:panel-hinge-dual-molecular` (8), `thm:projective-invariance` (7);
    - `deficiency`: `def:cut-edges-2ec` (7), `lem:cut-edge-decomposition` (7),
      `lem:two-vertex-trichotomy` (4);
    - `pebble-game`: `def:pebble-counts` (5), `lem:pebble-game-invariants` (5), `def:tryReachPebble`
      (4);
    - `case-iii`: `lem:case-III-claim612-eq644` (5);
    - `molecule-application`: `lem:molecule-graph-carrier` (5);
    - `case-i`: `lem:cycle-realization-rigid` (4);
    - `molecular-induction`: `def:graph-operations` (4);
    - `sparsity`: `lem:edgesIn-corners` (4), which principle D's grouping rule allows as corner
      cases.
  - 9 in `pencil.tex` and `main-component.tex`: `c8a`'s seven, plus
    `lem:pencil-x0-main-picture-open` and `lem:pencil-bridge-fibre`.
- **The register, screened.** A regex for principle A's banned metaphors and a few tells, with TeX
  comments stripped, gives counts per chapter. It is a screen, not a gate, since "route" and
  "carries" are sometimes literal. The highest counts are:
  - `panel-layer` 43;
  - `molecular-induction` 25;
  - `case-i` 20;
  - `case-iii` 17;
  - `generic-lift` 16;
  - `molecule-modelling` and `intro` 10 each.

  The phases 1–11 chapters score 0–7 but carry the Lean devices noted under round 1 (§3).
