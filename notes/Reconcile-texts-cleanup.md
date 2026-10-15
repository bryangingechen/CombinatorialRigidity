# RECONCILE round 1/3 — `reconcile-texts`, the texts (work log)

**Status:** in progress (opened 2026-10-15). Round 1 of **RECONCILE**'s three autopilot rounds;
the plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is
the authority for which rounds are done. Docs and blueprint prose only: the scopes of S1 and S2 on
the status surfaces, M1's "for simple graphs", M2's and M5's credits read against the two PDFs,
§2.6's stale example in an agent manual, and the non-vacuity rule. No node, edge or pin changes,
and no Lean edit. Nine one-commit tasks; tasks 1–8 (the open, S1's and S2's scopes, M1's text, M2's
and M5's credits, §2.6's example, the non-vacuity rule) are done. **Next concrete task:** task 9, the
close (Sonnet may take it). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Tasks 1–8 are done**; task 8, the non-vacuity rule, is this commit: `PHASE-BOUNDARIES.md`'s
close checklist (a row joins `main_results` with a closed non-vacuity witness, S1 the calibration)
and `CLEANUP.md` §A (a third failure mode, vacuous hypotheses). Round 3 writes the existing rows'
witnesses. Next: task 9, the close (*Hand-off*). Task 8's gates (docs only, no TeX edit; gate 4's log
is task 6's, not rebuilt): `lint.sh` green; `verify.sh` green, `checkdecls` silent, 9 `WARNING:`
lines; `1501 edges 11033da1dbaa0fae`, `8cdc1b9723e22064`; the dump `2e4cbc2acd13d193` (3 588
lines); `print.log` 0 `LaTeX Warning` lines; the no-Lean-edit diff empty; no gate 7.

**Verified at the open** (2026-10-15, at `f39e35e6`, whose Lean and blueprint are round 5's close
tree, `62175c74`):
- Whole-project `lake build` green: "Build completed successfully (2996 jobs)", 0 `warning:` and 0
  `error:` lines (re-run, all cached). **The no-Lean-edit base is `f39e35e6`**: the close checks
  that `git diff --stat f39e35e6.. -- CombinatorialRigidity/ lakefile.toml lake-manifest.json
  lean-toolchain` is empty.
- Round 5's close values, reproduced exactly: `lint.sh` green; `verify.sh` green, `checkdecls`
  silent, **9** `WARNING:` lines; the invariance check **`1501 edges 11033da1dbaa0fae`** and
  **`8cdc1b9723e22064`** (1 010 pins, 1 000 distinct; 692 nodes); `print.log` **0** `LaTeX
  Warning` lines and 31 overfull boxes (not gated; latexmk had nothing to do, no TeX having changed
  since `34f61fd9`); the dump (`python3 scripts/blueprint-deps.py --dump`, after `verify.sh`) 3 588
  lines, **`2e4cbc2acd13d193`**, byte-identical to round 5's close; `--summary` exits 0, both
  consistency checks OK, its output the same bytes as round 5's close.
- **The axioms check** (`notes/Reconcile.md` §2): the harness `scratch/reconcile-texts/Axioms.lean`
  (gitignored), generated from `formalization.yaml` by the command under *Scope*, has the 19
  `main_results` names in order and their 14 modules as sorted imports, byte-identical to round 5's
  close harness. Run with `lake lean`, every main result gives `[propext, Classical.choice,
  Quot.sound]`, and the output equals round 5's close and round 1's open byte for byte, net of the
  harness's path (its one warning is its own long line 31).
- **The two PDFs** are in `.refs/`: `lovasz-yemini-1982-on-generic-rigidity-in-the-plane.pdf` (8
  pages) and `pollaczek-geiringer-1927-uber-die-gliederung-ebener-fachwerke.pdf` (15 pages), both
  readable (`pdfinfo`); not read further (tasks 5 and 6 read them).
- **§2.6's replacement**, `lem:case-III`, verified from current pins; task 7 re-read it at HEAD.

## Scope and standing rules

From `notes/Reconcile.md` §1–§3, restated as far as a builder needs them.

- **Surface.** Each task's line names its files and lines (as at the open; re-`grep` before
  editing). In all: `formalization.yaml`'s text fields, `README.md`, `home_page/index.md`,
  `ROADMAP.md` and `DESIGN.md` (credits and scopes); the blueprint prose of `body-hinge.tex`,
  `intro.tex` and the chapters that name Laman as originator, with `bibliography.bib` (M5);
  `blueprint/CLAUDE.md` (§2.6); `PHASE-BOUNDARIES.md` and `CLEANUP.md` (the non-vacuity rule); the
  ledger; this log, ROADMAP's row and bullet, and `notes/Reconcile.md`'s **Status**.
- **No node, edge or pin changes** (§2 *Gates*): every node keeps its `\label`, its `\lean{…}`, its
  `\leanok` and its `\uses`; a statement block changes no claim. A node's title may change for a
  credit (M5). In `formalization.yaml`, no `main_results` entry's `declaration:` or `file:` changes:
  they are the axioms harness, which rounds 1–2 must reproduce byte for byte.
- **No Lean edits**: `CombinatorialRigidity/`, `lakefile.toml`, `lake-manifest.json` and
  `lean-toolchain` stay untouched. A Lean docstring a task finds wrong is round 3's (*Moved to a
  later round*).
- **The hygiene rule, lifted exactly for §1's items** (here: S1's and S2's scope sentences, M1, M2,
  M5, §2.6 and the non-vacuity rule). A change outside them to a headline statement, a blueprint
  statement's strength or a credit is recorded as a ledger `S` (or `M`) entry, with its line under
  *Candidates for the PI*, and not acted on; it is not a stop. A task or finding outside this
  round's scope goes under *Moved to a later round*, mirrored in the same commit into the target
  round's list (`notes/Reconcile.md` §3, until that round's log exists).
- **Evidence** (§2): claims about the Lean come from declarations' statements and bodies, never
  docstrings; a surprise gets a `lake lean` witness in `scratch/reconcile-texts/` before it is
  written; a citation meets `CLAUDE.md` *Referencing prior work* against `.refs/` (`REFS.md`), and a
  credit never changes on a secondary source alone. A task whose PDF is missing moves to round 2
  with a one-line reason.
- **The ledger** (`notes/Prose-findings.md`) stays each finding's home. A task names the IDs it acts
  on. An entry the round finishes becomes `done (<sha>)`; one it acts on in part (S1, S2, M1, M2,
  whose rest is round 3's or the phase's) keeps `reported` and gains `; round 1: <what> (<sha>)`.
  New entries take IDs from `F-251` on, under the ledger's format and categories; a new entry's
  disposition reads `open (<this log>, task N)` until a task sets it. One line here per new entry.
- **Gates for every commit**, each in the foreground with an explicit `timeout`:
  1. `blueprint/lint.sh` green.
  2. `blueprint/verify.sh` green: `checkdecls` silent, 9 `WARNING:` lines.
  3. The invariance check (`CLEANUP.md` §A) gives `1501 edges 11033da1dbaa0fae` and
     `8cdc1b9723e22064`, and the dump is byte-identical (`2e4cbc2acd13d193`, 3 588 lines).
  4. `blueprint/print/print.log` has 0 `LaTeX Warning` lines; a TeX task checks that latexmk
     rebuilt (the log's date).
  5. `python3 notes/check-phase-note.py` green.
  6. The no-Lean-edit `git diff --stat` above is empty.
  7. A task that edits `formalization.yaml` regenerates the harness, which parses the YAML, and
     `cmp`s it with the open's (identical):
     ```sh
     ruby -ryaml -e 'r=YAML.load_file("formalization.yaml")["status"]["main_results"]; i=r.map{|x| x["file"].sub(/\.lean$/,"").tr("/",".")}.uniq.sort; print i.map{|m| "import #{m}\n"}.join+"\n"+r.map{|x| "#print axioms #{x["declaration"]}\n"}.join' > scratch/reconcile-texts/Axioms-tN.lean
     ```
  Every commit also updates this log: its checklist line, *Current state* and *Hand-off*.
- **Rungs** (§2): Opus for tasks 2–7 (scope statements, credits read from the sources, a manual's
  claim about pins), a fresh agent per task; Sonnet may take task 8 (the rule's text) and the close.

## Lemma checklist (the round's task list)

One commit per task, in this order; each line gets its commit's sha. A task's line names the ledger
IDs and report items it acts on, its rung and its surfaces (lines as at the open).

- [x] **1. Open** (`0638fd12`; docs only): this log, the baselines, the task list, `F-251`.
- [x] **2. S1's scope** (`8ee0f8a8`; `F-207` in part, `F-252`): beside both theorems in
  `formalization.yaml`, README, the home page, `intro.tex` and ROADMAP §34; a `lake lean` witness.
- [x] **3. S2's scope** (`b0eb63eb`; `F-122`, `F-128` in part; `F-251`): KT Theorem 5.6's and the
  molecular conjecture's, read from the bodies, beside the link-recording form, on the status
  surfaces and `intro.tex`; no `declaration:` change.
- [x] **4. M1, "for simple graphs"** (`b72c0202`; `F-222` in part): `body-hinge.tex`'s two
  passages, the scope read from the corollary's pin.
- [x] **5. M2's credits** (`b408df1a`; `F-025`'s docs part): read against Lovász–Yemini 1982 and
  Jordán 2016, the verdict in `F-025`; `formalization.yaml`, ROADMAP and `DESIGN.md` fixed.
- [x] **6. M5, Pollaczek-Geiringer 1927** (`211e2737`; `F-228`): read from the page images, the
  verdict in `F-228`; credited beside Laman, with a `bibliography.bib` entry.
- [x] **7. §2.6, the honesty gate's example** (`3b68f7de`; report §2.6): `blueprint/CLAUDE.md`'s
  stale `lem:case-I` example replaced by `lem:case-III`'s `hSimple`, every fact the open verified
  re-read at HEAD, with the report's two cautions.
- [x] **8. The non-vacuity rule** (this commit; §1, the agent's proposal; report §1.1's checks; Sonnet may take
  it). `PHASE-BOUNDARIES.md`'s close checklist, *Sync the user-facing status surfaces* (172–200,
  where a headline theorem joins `status.main_results`), and `CLEANUP.md` §A (its audit list, 51–81)
  gain the requirement: a closed declaration instantiating each `main_results` row's hypotheses at a
  minimal input of its intended class, landing with the row; S1 is the calibration. Round 3 writes
  them for the existing rows outside S1, S2 and G6's.
- [ ] **9. Close** (`CLEANUP.md` *Workflow* 5; Sonnet may take it). The axioms check (byte-identical
  to the open's, net of the path); the no-Lean-edit check from `f39e35e6`; gates 1–4 at the open's
  values; every ledger entry the round touched has its disposition, task numbers as shas; the queue
  row `done = true`; ROADMAP's row ✓ and its RECONCILE bullet, and `notes/Reconcile.md`'s
  **Status**, pointing at round 2's open.

## Candidates for the PI

`S` and `M` findings this round makes, one line each naming the ledger ID.

- `F-252` (S, task 2): S1's gap is wider than its report says: `hfresh` fails at every graph with at
  most $2(|V| - 1)$ edges, $K_4$ at $d = 2$ among them (a tree of single and double edges uses every
  label); the transfer witnessed, the tree's minimality argued. The phase's (a) removes it with S1.

## Moved to a later round

Tasks and findings outside this round's scope, one line each, mirrored into the target round's
list in `notes/Reconcile.md` §3.

- `BodyBar/TayTheorem.lean` 548's "Lovász–Yemini-style rank-upper-bound argument" (task 5): a
  docstring crediting LY with the necessity half, which the report's M2 does not list; and
  `MatroidIdentification.lean`'s "`|E|`-induction" (its header, a section heading and three
  docstrings), where `IsSparse.exists_rowIndependent_placement` inducts on $|V|$. Round 3's
  docstring sweep, with M2's.
- `Laman.lean` 21's "Laman's 1970 theorem" (task 6): the module header credits Laman alone; with
  `F-228` it credits Pollaczek-Geiringer 1927 too. Round 3's docstring sweep.

## Blockers / open questions

None.

## Hand-off / next phase

**Next: task 9, the close** (Sonnet may take it): its checklist line above, in full. Then the
queue's next row, `reconcile-statements`.

## Decisions made during this round

- **The slicing** (the open): nine tasks against §3's ~8, S1 and S2 apart, as their rows and
  passages do not overlap. M2 comes before M5: both touch `formalization.yaml`'s planar lines.
- **Surfaces beyond the plan's lists** (the open): the home page and `intro.tex` for S1 and S2,
  which repeat README's claims (round 5 task 7's rule: a finding's phrase follows to the surfaces
  its entry does not name); `DESIGN.md`'s two credits for M2 (§1: "fix every credit"); ROADMAP's
  opening and *References* for M5. `DESIGN.md`'s pebble-game section, which the report's Part 3
  put in round 1, is round 3's with L1–L2 (§1's table).
- **`F-251`** (the open): `formalization.yaml`'s fidelity paragraph claims every blueprint
  statement is in the exact form proved; task 3 qualifies it beside S2's scope.
- **S1's and S2's surfaces** (tasks 2–3): ROADMAP §34 and §23 too; `F-252`'s sharper reading stays
  off the surfaces (argued, not witnessed); Theorem 5.6's row credits the rank formula to the
  nondegenerate form; the free selector does not reach the multigraph theorems.
- **M1's passages** (task 4): the scope is the pin's signature; for multigraphs the formalization
  "has" the bundle form, not `F-222`'s "only".
- **M2's credits** (task 5): Laman originates it; LY is `independently-proves` for Corollary 1, no
  "presentation we follow" credit, as the proofs follow Jordán's.
- **M5's credits** (task 6): Pollaczek-Geiringer is credited first and Laman "again" wherever the
  originator is named; "Laman's theorem" and "Laman graph" keep their names. The planar
  row-independence node's title gained her name (no "in the plane": it overfilled a print line).
- **§2.6's example** (task 7): the sentence calls `hSimple`, not the node, case (b): the pins' other
  hypotheses are outside the example.
- **The non-vacuity rule** (task 8): `notes/Reconcile.md` §1's text, transcribed; `CLEANUP.md` §A
  names the failure mode as a third beside its two. No new entry (tasks 3–8 made none beyond
  `F-251`, `F-252`).
