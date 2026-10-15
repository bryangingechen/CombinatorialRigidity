# RECONCILE round 1/3 — `reconcile-texts`, the texts (work log)

**Status:** in progress (opened 2026-10-15). Round 1 of **RECONCILE**'s three autopilot rounds;
the plan and the PI's decisions are `notes/Reconcile.md`, and `.claude/autopilot/queue.toml` is
the authority for which rounds are done. Docs and blueprint prose only: the scopes of S1 and S2 on
the status surfaces, M1's "for simple graphs", M2's and M5's credits read against the two PDFs,
§2.6's stale example in an agent manual, and the non-vacuity rule. No node, edge or pin changes,
and no Lean edit. Nine one-commit tasks; task 1, the open, is done. **Next concrete task:** task
2, S1's scope on the status surfaces (Opus, a fresh agent). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

No planned stop (`notes/Reconcile.md` §4): the queue runs the three rounds unattended and stops
before `RECONCILE-FORMAL`. An unplanned `NEEDS_PI` entry goes here, newest first, and the PI
answers in an entry that starts `**PI, <date>:**`. No entries yet.

## Current state

**Task 1, the open, is done** (this commit; docs only). Next: task 2 (*Hand-off*).

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
- **§2.6's replacement**, verified from current pins: task 7's line.

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

- [x] **1. Open** (this commit; docs only): this log, the baselines, the task list, `F-251`.
- [ ] **2. S1 — the generic body-hinge theorem's scope** (`F-207`, in part; report S1; Opus). Read
  the signatures of
  `BodyHingeFramework.isInfinitesimallyRigidOn_ofHinge_isGenericHingePoints_iff_spanningTrees`
  (`GenericLift/HingeGeneric.lean:1005`) and of the panel form its row names,
  `PanelHingeFramework.isInfinitesimallyRigidOn_ofNormals_isGenericNormals_iff`
  (`GenericLift/PanelGeneric.lean:484`), both taking `hfresh` and `hends`, and
  `rem:fresh-edge-supply` (`panel-layer.tex:1087`). Then say, beside each statement, what it covers
  today: its hypotheses hold at no graph that is itself a minimal $k$-dof-graph (a single edge, a
  tree, every minimal $0$-dof-graph), they hold when $|E(G)| > D(|V| - 1)$ (the report's reading of
  that remark, which the task checks), and the graphs between are unsettled; the refactor is the
  phase's (a). Surfaces: `formalization.yaml`'s `main_results` row (448) and its `alignment` entries
  for JJ 2010 Thm 6.1 / Cor 6.3 and Thm 7.2 (716, 722); README 145–151; the home page 131–134;
  `intro.tex`'s third continuation (234–245). The blueprint notes after `cor:panel-generic-rigid`
  and `cor:bodyhinge-generic-tree-packing` already say it, and stay.
- [ ] **3. S2 — KT Theorem 5.6's and the molecular conjecture's scope** (`F-122`, `F-128`, in part;
  `F-251`; report S2; Opus). Read `PanelHingeFramework` (its `ends`), `RankHypothesis`,
  `hingeConstraint`, `panelSupportExtensor_ne_zero_iff`, and the statements of
  `rankHypothesis_of_theorem_55_gen` (`Theorem55.lean:2880`), `molecular_conjecture` and
  `rankHypothesis_genuine_recordsLinks_of_theorem_55_gen` (2615). Then say what the two cover today,
  each claim checked against those bodies (the endpoint selector is free and hinges may be
  degenerate: at deficiency zero a framework with every normal zero meets Theorem 5.6's conclusion,
  and the panel side of the molecular conjecture states no condition on `Q.ends`), beside the proved
  form, the link-recording one with nondegenerate hinges, named in the text only: no `declaration:`
  change (that is the phase's). Surfaces: the `main_results` rows (357, 371); the `alignment`
  entries for KT Theorem 5.6, Conjecture 1.2 and JJ 2008 (674, 679, 685); README 93–108; the home
  page 82–98; `intro.tex` 40–49. And `F-251`: `fidelity.divergences`' "states each result in the
  exact form proved" (`formalization.yaml` 580–582) names its exceptions. Read
  `molecular_conjecture_multigraph` and `theorem_55_6_multigraph` too: if the free selector reaches
  them (README 151–160, the row 465), that is a new `S` entry under *Candidates for the PI*. `F-125`
  is the phase's.
- [ ] **4. M1 — "for simple graphs"** (`F-222`, in part; report M1; Opus). `body-hinge.tex`'s note
  after `def:body-hinge-framework` (70–79, "The rigidity statement for frameworks with hinges … is
  `cor:bodyhinge-generic-tree-packing`") and the paragraph after `thm:body-hinge-tay`'s proof
  (144–152, KT Proposition 1.1 for multigraphs "is" the corollary) say that the corollary is for
  simple graphs, with the rest of its scope read from its pin's signature (`hSimple`, $|V| \ge 2$,
  `hspan`, $K$ infinite), and that for multigraphs the formalization has the form for bundles of
  bars (S11). No `\cref` or `\uses` changes. The multigraph form is the phase's (b).
- [ ] **5. M2 — the planar characterization's credits, verified first** (`F-025`, its docs part;
  report M2; Opus). Read Lovász–Yemini 1982 (`.refs/`, 8 pages), Jordán 2016 pp. 45, 49 and 51
  (`.refs/jordan-2016-msj-memoirs.pdf`), and the statements of Phases 6–7's declarations
  (`linearRigidityMatroid_eq_rigidityMatroid`; the pins of
  `thm:edgeSet-rowIndependent-iff-isSparse`, `thm:rigidityMatroid-indep-iff-rowIndependent`,
  `thm:linearRigidityMatroid-eq-rigidityMatroid` and `lem:isSparse-of-rowIndependent-two`). Settle
  what each credit names, and whether the proofs follow LY's argument (then a "presentation we
  follow" credit beside Laman's); the verdict, with pages, goes into `F-025`. Then fix:
  `formalization.yaml`'s LY `sources` entry (37–43: `location`, `relationship`) and the lines
  crediting LY, `status.scope` (234), the description at 278 and `alignment`'s source (607);
  ROADMAP's directory-layout line (61), Status row title (96), §6's text (269), §7's heading and
  text (277, 279), and its *References* entry (1374) as the verdict says; `DESIGN.md` 42 and 213.
  The docstrings are round 3's (`notes/Reconcile.md` §3 lists them).
- [ ] **6. M5 — Pollaczek-Geiringer 1927, read** (`F-228`; report M5; Opus). Read the PDF's page
  images with the Read tool's `pages`, not its garbled text layer; its 15 pages are pp. 58–72, and
  the first also carries the end of the preceding article. If it states the characterization, credit
  it beside Laman where the originator is named (the open's `grep`; a list's "Laman's theorem" is
  the task's call): `intro.tex` 12 and 114, `laman.tex` 5, `laman-theorem.tex` 4, `henneberg.tex`
  10, `rigidity-matroid.tex` 5 and the title at 444, `bar-joint-3d.tex` 25 and 93; a
  `bibliography.bib` entry checked against Crossref (doi:10.1002/zamm.19270070107); README 10 and
  68; the home page 11–12; `formalization.yaml` (a `sources` entry, `status.scope` 232, the
  description at 270, `alignment`'s source at 602); ROADMAP's opening (4) and *References* (1372).
  If it does not, record what it states as a new `M` entry and change no credit. Either way `F-228`
  is `done (<sha>)`, with the verdict and pages.
- [ ] **7. §2.6 — the honesty gate's example** (report §2.6; Opus). `blueprint/CLAUDE.md` 196–198
  ("`lem:case-I` is honestly green because its hypothesis *is* `lem:genericity-device`") is stale.
  **The open verified the replacement, `lem:case-III`, from current pins**: its pin
  `case_III_realization_all_k` (`CaseIII/Realization.lean:2650`) takes `hSimple : G.Simple` beside
  `hG`, `hV3` and `hnoRigid`; `Graph.simple_of_isMinimalKDof_of_noRigid`
  (`Induction/ReducibleVertex.lean:698`) concludes `G.Simple` from those three and
  `2 ≤ bodyBarDim n`; `lem:case-III`'s statement `\uses` `lem:simple-minimal-noRigid` (`case-iii.tex:2460–2461`),
  which pins that lemma (`molecular-induction.tex:1928`); and `theorem_55_minimalKDof_k_all_k`
  (`Theorem55.lean:2345`), which `thm:theorem-55`'s pin `theorem_55_minimalKDof_gen` calls (2433),
  derives `hSimple` by it in its Case III branch (2397–2403). `--label lem:case-III` reads the edge
  as unbacked, transitively, as the report's second caution says. The task re-reads these at its
  HEAD and writes the example with the report's two cautions, or, if any has changed, drops the
  example with no replacement.
- [ ] **8. The non-vacuity rule** (§1, the agent's proposal; report §1.1's checks; Sonnet may take
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

- None yet.

## Moved to a later round

Tasks and findings outside this round's scope, one line each, mirrored into the target round's
list in `notes/Reconcile.md` §3.

- None yet.

## Blockers / open questions

None.

## Hand-off / next phase

**Next: task 2, S1's scope** (Opus, a fresh agent): read the two generic theorems' signatures and
`rem:fresh-edge-supply`, then state what they cover today on the surfaces its line names, under
gates 1–7. Then tasks 3–9 in order.

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
