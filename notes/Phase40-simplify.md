# Phase 40 cleanup round 4/5 — `40-simplify`, the deep simplification recon (work log)

**Status:** in progress (opened 2026-10-04); **stopped for the PI at Stop 2** (`NEEDS_PI`).
Round 4 of the five post-Phase-40 cleanup rounds. Their order, stops and the PI's decisions are in
`notes/Cleanup40.md`, and `.claude/autopilot/queue.toml` is the authority for which rounds are
done. The round is a read-only Opus recon over the pencil surface, looking for bigger
simplifications (`notes/Cleanup40.md` §2 *Round 4*). Tasks 1–7 committed their GO / NO-GO verdicts
to `notes/Phase40-simplify-verdicts.md`, and task 8 wrote Stop 2, the round's one planned stop,
from them (*Autopilot: for the PI*). Then the items the PI sanctions land, and task 11 closes.
**Next concrete task:** task 9 (S), once the PI has answered Stop 2: transcribe the answer and
slice the sanctioned items (Opus, docs only). Round manual: `CLEANUP.md`.

## Autopilot: for the PI

### 2026-10-04 — `NEEDS_PI`: Stop 2, the round's verdicts (planned stop, `notes/Cleanup40.md` §2)

**What happened.** Tasks 1–7, seven Opus recons, read the pencil surface (920 declarations;
`Pencil/`'s 33 691 lines and the two chapters) and wrote 63 verdicts, in
`notes/Phase40-simplify-verdicts.md` under their task; each task's commit message has the
measurements. The evidence is compiler-checked: a declaration graph of the whole project (task 1; 0
mismatches against round 3's closure), and about two dozen spikes run with `lake lean`, which the
coordinator re-ran (0 errors, no `sorry`). Tasks 6–7's spikes, kept in the gitignored
`scratch/40-simplify/`, are the builds for `a5`, `a6`, `a6a` and `7a`–`7d`. The findings:
- 144 declarations of the surface (5 963 lines) feed no main result, and nothing in `Pencil/`
  feeds any result but the two pencil headlines (task 1).
- Every conditional theorem's conclusion is now a theorem: `_of_card`'s exact statement compiles
  from `pencil_conjecture` (task 2). Design §6's Lean records a route, not a result (`1a`).
- Phase 39's pendant route at degree three re-proves Phase 40's steering lemma: `7a` frees 1 300
  lines, or 2 249 after `a5` (task 7). Four producer duplications fold into shared shapes (`a5`,
  `a6`, `a6a`, `7b`), and three re-proofs go (`q2a`–`q2c`, task 5).
- The open ears are four arguments, not one (task 4); the other long proofs are as long as their
  arguments (task 7). One headline signature can move (`a2`, strictly more general).
- **Recommended package:** 17 commits (7 Opus), about −7 640 Lean lines net. **Minimal package**
  (statement-neutral items only, `1a` kept): 13 commits (5 Opus), about −3 820.

**Rungs, corrected here.** Where a verdict says "Sonnet transcribing" for a ⚠Z proof rewrite, the
rung is **Opus**, by the dispatch playbook's fragility-zone floor, even where a complete spike
exists: `a4`, `a5`, `a6`+`a6a`, `7a`, `7b`, `7c`. Deletions (`r1`, `1a`), mechanical moves (`q2a`,
`b1`), TeX and non-⚠Z transcriptions stay Sonnet.

**The decisions.** The forks that change other verdicts come first.

**Default, to accept wholesale:** "Sanction every GO as recommended: `1a` retire, `r1` delete,
decision 4's statement moves, `a2` last, `7d` (i), `c3a` NO-GO, `a7` kept, and round 3's
`r2`–`r8` as written (`r7`'s node built)." Override any item by its ID ("`1a` keep", "`c5`
restate instead", "`7d` (ii)"), or answer "minimal package" for the statement-neutral items only.

1. **`1a`, design §6's Lean: retire (recommended) or keep.** The PI's words cancelled the kernels'
   work ("we'll stop / cancel future work on the currently open kernels on the other route to the
   pencil conjecture", 2026-09-29, `notes/pencil/adjudications.md`). "The landed Lean on that route
   stays, untouched, as conditional theorems" is the close's own **Decided** record, not the PI's
   words; retiring revisits it. Task 2 found each such theorem's conclusion proved outright.
   - *Retire:* after `c3`'s TeX, 1 deletion (Sonnet, ⚠Z files): `_of_card`'s cluster with `q3a`'s
     two roots (2 482 lines; `Escape.lean`, `Habitat.lean`, `WitnessGeneral.lean` whole), `1b`,
     `1c-ii` and the girth chain (990), −3 636 in all. It fixes ROADMAP §40, whose "their landed
     Lean stays as conditional theorems" is marked verbatim. Moots `a4`, `c4`(a) and `a1`; makes
     `7c` GO; `m3` then retires two nodes; `r1`'s two kept pins keep one citing chapter.
   - *Keep:* no deletion; `a4` (1, Opus), `c4`(a) (1, Sonnet, two pinned signatures) and `a1` (1,
     Sonnet) become GO, `7c` NO-GO; `q3a` and the girth chain stay.
   - Either way `c3` and `a2` change `pencil_conjecture_of_arms_pair`'s signature, one of the four
     theorems the record keeps "untouched" (under *keep*, `a2` two more in `Escape.lean`).
     Sanctioning them covers that.
2. **`r1`, the D5 debt: delete 27 of its 29 off-headline names (recommended).** Round 3 said leave
   all 31 unpinned. Task 1 found that these 27, with two helpers only they reach, serve only the
   two-cut composition built for smark's kernel attack, which design §6 retired, and that no
   blueprint text names them. 1 commit, Sonnet: `TwoCut.lean` whole and 20 declarations elsewhere,
   −986. The 2 pinned (51 lines) stay. Moots `b2`; `b1` then restates one hub, not two. *Leave:*
   `b2` becomes GO (1 commit, Sonnet).
3. **`a2`, a headline signature: GO (recommended), last.** `pencil_conjecture` and five pinned
   theorems drop a type-unused `[DecidableEq β]`, using `classical`: strictly more general (spike,
   0 warnings). 1 commit, Sonnet, two sites once `1a`, `1b` and `c3` have landed; the axioms
   harness re-runs. *Leave:* the six silencers stay.
4. **The statement moves: GO (recommended), each needing the PI's sanction** (`notes/Cleanup40.md`
   §2, *All five rounds*). Stronger: `c3` (`_of_arms_pair` over every nonempty graph; a new node
   for the pair's loop, base and cut leaves) and `c8`'s `-lifting-restrict` (the clause five
   proofs cite). Weaker, to the pin or to what the readers use: `c2`, `c4`(b), `c6`, `c8`'s
   `-contract-standing`, `c9`. Nodes retired: `c5`, `1b`, `1c-ii`, `m3`'s one or two, and the girth
   chain's eight (with `1a`). Form only: `b1` (a pinned hub's `V(G).compl` as `V(G)ᶜ`,
   definitionally equal). Under `1a` keep, also `c4`(a). The estimates are in the table.
5. **`7d`, CONTRACT-R's account in the chapter: (i) keep (recommended) or (ii) restate.** The Lean
   is GO either way: CONTRACT-R from CONTRACT-A at `def₂(H) = 0`, 238 → 22 lines, 1 commit, Sonnet,
   statement unchanged. (i) The chapter keeps its own proof by KT's Lemma 6.3; `-core-plane`,
   `-core-rank`, a `-limit` clause and a `cor:pencil-flat-x0` clause keep their pins (122 lines)
   with no Lean reader, like `a7` and the duality section; a sentence in the node's proof can name
   the Lean's route. (ii) R is stated as A's corollary: those pins and two nodes retire (−122), the
   section reorders; +1 commit, Opus (prose, as in round 3). (i) keeps KT's order, in the section
   round 3 just rewrote.
6. **`c3a`, `pencil_conjecture` as `pencilPair_of_nonempty` at a spanning graph: NO-GO
   (offered).** A one-line proof (spike), and 101 lines leave the closure, but they stay. The PI
   chose the present term on 2026-09-28 ("`pencil_conjecture_of_X0 x0Dist x0Gen`, the L0 shape"),
   `formalization.yaml` says so, and no line is saved. *GO:* 1 commit, Sonnet, with the yaml.
7. **`a7`, `Graph.X0Attains.of_closedEar`: keep (recommended); the PI's own keep** (Phase 40g
   decision 2, 2026-09-27: "Named theorem (Recommended)"). Task 1's 118 dead lines are no new
   argument. *Retire:* 1 commit, Sonnet, not ⚠Z, −118: the node goes, and the section's opening
   and `rem:pencil-x0-ear-class` drop the closed ear.
8. **Round 3's eight build-or-leave items** (below): as recommended, with `r1` per decision 2.

**The verdicts** (63; wording and evidence in the verdicts file). *Changes:* **H** a headline
signature; **S** a blueprint statement's strength or a pinned statement (the PI's sanction); **G**
the dependency graph or pins only; – nothing a reader sees. Lines are net Lean lines; "est." marks
an estimate, not a spike or a measurement. A bold **Opus** is this entry's correction.

| ID | What | Verdict | Commits, rung | Changes, lines | Depends on |
|---|---|---|---|---|---|
| `r1` | delete 27 of D5's 29 off-headline names | GO (27); the 2 pinned kept | 1, Sonnet (deletion, ⚠Z files) | –, −986 | decision 2 |
| `b2` | the merged hub's `hne` | NO-GO: moot under `r1` | if `r1` left: 1, Sonnet | S (unpinned) | `r1` |
| `q3a` | the kernel route's two roots | GO with `1a`, else keep | in `1a`'s deletion | –, −917 | `1a` |
| `q3b` | `pencilChartWF_standing_ofCoord_toCoord` | GO | in `r1`'s, Sonnet | –, −27 | – |
| `q3c` | the rest: API, a design witness | NO-GO, keep (255 lines) | – | – | – |
| `1a` | design §6's conditional theorems | PI call; retire recommended | 1, Sonnet (deletion, ⚠Z files) | S, G; −1 565 (−2 482 with `q3a`) | decision 1; `c3`'s TeX |
| `a4` | `pencilPair_of_habitat_ncard_eq_four` | with `1a`; kept: GO | kept: 1, **Opus** (⚠Z proof) | –, about −124 (est.) | `1a` |
| `c4` | `-pair`'s statement against its pins | GO by part | (a), if kept: 1, Sonnet; (b) in `c2` | S | `1a`, `c2` |
| `c2` | `thm:pencil-reduction`'s cases (iii)–(v) | GO, restate to the pin | in `c3`'s TeX, Sonnet | S (weaker) | – |
| `c3` | `-pair` split; one assembly | GO | 2, Opus | S (stronger), G; about −21 | `1a` (kernel form) |
| `c3a` | the headline's direct proof | NO-GO (offered) | GO: 1, Sonnet | H's proof term | decision 6 |
| `1b` | `pencil_conjecture_of_arms` | GO, retire | node in `c3`'s TeX; Lean in `1a`'s deletion | S, G; −78 | `c3` |
| `a2` | the six `[DecidableEq β]` binders | GO | 1, Sonnet; axioms harness | H (more general) | `1a`, `1b`, `c3` |
| `m1` | the hub threshold's edge | NO-GO | – | – | – |
| `m2` | edges to the loop and base cases | GO | in `c3`; alone 1, Sonnet, TeX | G | `c3` |
| `m3` | the no-rigid lemma's in-edge: remove the call | GO | 1, Sonnet; with `7c`, **Opus** | S, G; −35 (−97 with `1a`) | – |
| `m4` | `-main-component` to the pair theorem | GO | in `c3` | G | `c3` |
| `m5` | the pair node drawn unfilled | GO | in `c3`; alone 1, Sonnet, TeX | G | `c3` |
| `1c-i` | `lem:two-pencil-extension-iff`, re-pinned | GO | TeX batch, Sonnet | G | – |
| `1c-ii` | `lem:pencil-base-parallel-pair` | GO, retire | in `1a`'s deletion | S, G; −86 | – |
| duality, cycle | `sec:pencil-duality`, `sec:pencil-cycle` | NO-GO, keep (366) | – | – | – |
| girth | `sec:pencil-girth-chain` (8 nodes) | with `1a`: retire; kept: NO-GO | in `1a`'s deletion, Sonnet | S, G; −990 | `1a` |
| `a1` | `lem:pencil-chain-side-connected` | moot with girth; kept: GO | kept: 1, Sonnet | –, +12 | girth |
| task 1's (c) | dead pins in other chapters | NO-GO, keep (127) | – | – | – |
| task 1's (b) | six nodes' caller-less clauses | NO-GO, keep (100) | – | – | – |
| polynomial | `def:pencil-configuration`'s polynomial | GO, retire | in `r1`'s, Sonnet | G (pins), −32 | – |
| `c5` | `lem:pencil-selector-independent-scalar` | GO, retire (or restate) | in `r1`'s, Sonnet | S, G; −52 | – |
| two-hubs | `lem:pencil-x0-two-hubs-obstruction` | node NO-GO; GO, drop one edge | TeX batch | G | – |
| `c6` | `lem:pencil-condition-linear` | GO, restate; pin the iff | 1 with `c7`, Sonnet | S (weaker), +13 | `c5` |
| `c7` | `lem:pencil-x0-main-picture-open` | GO, strengthen the Lean | 1 with `c6`, Sonnet | –, +6 | – |
| `c1` | `lem:pencil-splitoff-curve` | GO, three one-pin nodes | TeX batch, Sonnet | G (+2 nodes) | – |
| `c8` restrict | `lem:pencil-lifting-restrict` | GO, add the cited clause | TeX batch | S (stronger) | – |
| `c8` bridge | `thm:pencil-x0-bridge` | GO, unpin five helpers | TeX batch | G | – |
| `c8` standing | `lem:pencil-contract-standing` | GO, two clauses dropped | TeX batch; its pin in `r1`'s | S (weaker), −27 | – |
| `c8` steer | `lem:pencil-generic-steer` | GO, unpin a helper | TeX batch | G | – |
| `c8a` | seven more nodes with four or more pins | NO-GO here (**PROSE**'s audit) | – | – | – |
| `m6` | `-x0-theorem-s` to `lem:deficiency-zero-connected` | GO | TeX batch | G | – |
| `m7` | `-generic-steer` to `-feasible-hub-conditions` | GO | TeX batch | G | – |
| `q1` | the open ears as one argument | NO-GO: four arguments | – | – | – |
| `q1a` | one certificate step for `k ≥ 5` and `k = 2` | GO | 1, Sonnet (not ⚠Z) | –, −43 (−76 via `certHeights`) | – |
| `q1b` | one second stage for the antecedent steps | NO-GO (nets about 8) | – | – | – |
| `a7` | `Graph.X0Attains.of_closedEar` | NO-GO, keep; the PI may revisit | retire: 1, Sonnet | retire: S, G; −118 | decision 7 |
| `c9` | two caller-less toolkit halves | GO, retire | TeX batch; Lean in `r1`'s | S (weaker), −35 | – |
| `q2` | where `Pencil/` re-proves | GO for `q2a`–`q2c` only | – | – | – |
| `q2a` | Theorem55's cut-edge bricks, one copy | GO | 1 with `b1`, Sonnet (⚠Z, mechanical) | –, −100 | after `a5`, `a6` (task 6) |
| `q2b` | the perp's dimension, one lemma | GO | 1 with `q2c`, `a3`, Sonnet | –, about −45 | – |
| `q2c` | the common non-root, by the mirror | GO | in `q2b`'s | –, −8 | – |
| `q2d` | a shared edge-classification lemma | NO-GO (task 6: nets −16) | – | – | – |
| `b1` | `.compl` as `ᶜ` in the hubs | GO | with `q2a`, Sonnet (⚠Z, mechanical) | S (form only), −5 | `r1` (size) |
| `a3` | the degree-sum pair | GO for one half | in `q2b`'s | –, −17 | – |
| `a5` | one tail for `Pair2.lean`'s #4 and #6 | GO | 1, **Opus** (⚠Z) | –, about −295 | – |
| `a6` | the core's two branches as one | GO | 1 with `a6a`, **Opus** (⚠Z) | –, −149 | – |
| `a6a` | Theorem55's cut case, the same | GO | with `a6` | –, −115 | – |
| `7a` | the pendant cut by the steering lemma | GO | 1, **Opus** (⚠Z) | –, −1 240; one route for every degree after `a5`: −1 470 beyond `a5`'s −295 | `a5` (that form) |
| `7b` | one glue for a cut's two sides | GO | 1, **Opus** (⚠Z) | –, −213 (about −280 with `a5`'s tail, est.) | `a6`, `a5` |
| `a6b` | `a6`'s shape at `Pair.lean`'s producers | NO-GO (their shared part is `7b`) | – | – | – |
| `7c` | `_three` by `linearIndependent_pointJoin_triangle` | GO with `1a`; else NO-GO | 1 with `m3`, **Opus** (⚠Z) | –, −74 | `1a` |
| `7d` | CONTRACT-R as CONTRACT-A's corollary | GO (Lean); the chapter a PI call | 1, Sonnet (not ⚠Z); (ii) +1, Opus | –, −216; (ii) S, G, −122 | decision 5 |
| `7e` | #7, `GenericTriangle.lean` | NO-GO | – | – | – |
| `7f` | `of_splitOff` | NO-GO | – | – | – |
| `7g` | `of_additiveContract` | NO-GO | – | – | – |
| `7h` | GenericEar's producer | NO-GO (a shared `V₁` half: about −60, est.) | – | – | – |
| `7i` | (MC-188), `GenericSteer.lean` | NO-GO | – | – | – |

**Round 3's build-or-leave recommendations** (`notes/Phase40-exposition.md` *The build-or-leave
items*), as written unless a task here changed a premise:
- `r1`, the D5 debt: leave all 31 unpinned. **Changed by task 1:** 27 of the 29 dead names go
  (decision 2); the 4 live helpers stay unpinned, and the 2 dead pins stay.
- `r2`, A6, the welded pendant law, S7(i)–(iii), S7(v) and S9: leave unbuilt, no node. Stands,
  more firmly: the two-cut composition they belong to goes with `r1`, its kernels with `1a`.
- `r3`, the "only if" halves of (MC-52)/(MC-53): leave unbuilt, no node. Stands; no task bore on it.
- `r4`, the edge-restricted, non-spanning generic-normals row rank: leave unbuilt, no node.
  Stands; no task bore on it.
- `r5`, SHORT's shared assembly: leave both unpinned. Stands (task 4): `q1a`'s new helper follows
  it, and `q1b` found no shared second stage.
- `r6`, the CHAINS pair: leave both unpinned. Stands; no task bore on it.
- `r7`, `Graph.exists_isMinimalKDof_spanning_subgraph`: give it a node in `deficiency.tex`, beside
  `lem:subgraph-minimality`. Stands: 1 commit, Sonnet, TeX (four proofs gain a `\cref`).
- `r8`, `Graph.exists_normalized_labeling`: leave unpinned, no node. Stands. After `r1` its one
  caller is the PanelLayer hub (TwoCut's merged hub goes), so it shares no code; folding it back
  into that hub was not assessed.

**Proposed landing order** (task 9 cuts it to what the PI sanctions). Every commit is green:
whole-project `lake build` warning-clean and `lake lint`; the blueprint gates on TeX; trial
deletion and a whole-project build for each deletion. The axioms harness (re-diffed against
`formalization.yaml`, run with `lake lean`) re-runs on the two headline commits, `c3`'s Lean and
`a2`, and costs little on any other Lean commit inside a main result's closure (`a6a`'s cut case
is in 10 of the 19, task 1's graph).

*Recommended package: 17 commits, 7 Opus, about −7 640 lines.*
1. TeX, Sonnet: task 3's batch (`m6`, `m7`, `1c-i`, `c1`, the two-hubs edge, `c8`'s four, `c9`'s
   clauses, `c5`'s node, the polynomial's pins). It unpins first, so no deletion strands a pin.
2. Deletion, Sonnet: `r1`, with `q3b` and the Lean step 1 unpinned (polynomial, `c5`, `c8`,
   `c9`): −1 159.
3. `c6` + `c7`, Sonnet: +19.
4. `q2b` + `q2c` + `a3`, Sonnet: −70.
5. `q1a`, Sonnet: −43.
6. `r7`'s node, Sonnet, TeX.
7. `c3`'s Lean, Opus: `pencilPair_of_nonempty` from the general assembly (axioms harness).
8. `c3`'s TeX, Opus: with `c2`, `c4`(b), `m2`, `m4`, `m5` and `1b`'s node; the kernel statement
   leaves (`1a`).
9. Deletion, Sonnet: `1a` with `q3a`, `1b`, `1c-ii`, the girth chain and its nodes; ROADMAP §40:
   −3 636.
10. `m3` + `7c`, Opus: `_three` from `G.Simple`, moved into `MainComponent/`; two nodes go: −171.
11. `a6` + `a6a`, Opus, moving the two crossing lemmas to `Deficiency.lean`: −264.
12. `a5`, Opus: −295.
13. `7a`, one route for every degree, Opus: −1 470.
14. `7b`, Opus, four sites: −213 (about −280).
15. `q2a` + `b1`, Sonnet (⚠Z, mechanical; four `Pencil/` calls left, not six): −105.
16. `7d`, Sonnet, and the chapter per decision 5: −216.
17. `a2`, Sonnet, last (axioms harness).

*Minimal package: 13 commits, 5 Opus, about −3 820 lines* (`1a` kept; no **H** or **S** item):
step 1's **G** half with `m2` and `m5` alone; step 2 without `c5`, `c8`, `c9` (−1 045); `c7` + `a1`
(+18); steps 4, 5, 6; `a4` (Opus, about −124, est.); steps 11–14; `q2a` alone (−100); step 16
with (i).

The PI answers below, in an entry of the PI's own. Task 9 starts only after it: it transcribes the
answer verbatim into *Decisions made* and slices the sanctioned items.

## Current state

**Round 4 is stopped for the PI at Stop 2** (task 8, 2026-10-04, docs only). The recon is
complete: tasks 1–7 wrote 63 verdicts, one subsection a task in
`notes/Phase40-simplify-verdicts.md`, and task 8 wrote them up for the PI under *Autopilot: for the
PI*: eight decisions with a recommendation each, a default to accept wholesale, the full table,
round 3's `r1`–`r8`, and a landing order (17 commits recommended, 13 minimal). Nothing is
mid-stream, and nothing runs until the PI answers. Then task 9 transcribes the answer and slices
the sanctioned items into task 10, and task 11 closes.

**Verified at the open** (the Lean tree is `0b260626`'s and the blueprint `30e79461`'s; neither has
changed since round 3's close):
- Whole-project `lake build` green, 3003 jobs: 0 `warning:`, 0 `error:` and 0 `failed to cache
  artifact` lines. `lake lint` green.
- `#print axioms` on all 19 `formalization.yaml` main results gives `[propext, Classical.choice,
  Quot.sound]`. Round 3's harness was diffed against the yaml's `declaration:` and `file:` fields
  (19 names in order, 14 imports: identical), copied to `scratch/40-simplify/Axioms.lean`
  (gitignored) and run with `lake lean`. Its output is round 3's close's, byte for byte apart from
  the harness's own path. Re-run it the same way at the close.

**The surface**, as round 1 set it (`notes/Cleanup40.md` §2 *Round 1*):
- the Lean: `Molecular/Molecule/Pencil/**`, now 42 files and 33 691 lines; Phase 40's edits in 26
  Lean files outside it (`git diff --stat c9d26ef9^ 91fcd24a -- CombinatorialRigidity/`), with
  rounds 1–2's moves and additions; and, for task 1, every declaration the two chapters pin
  (Phase 39 put some in `Induction/ForestSurgery/`, e.g. `Graph.pencil_reduction`);
- the blueprint: `pencil.tex` (1 589 lines) and `main-component.tex` (5 696), plus Phase 40's nodes
  in `deficiency.tex`, `rigidity-matrix.tex`, `molecular-induction.tex` and `panel-layer.tex`
  (`notes/Phase40-cleanup.md` *Scope*).

## Scope and standing rules

From `notes/Cleanup40.md` §1–§2, restated only as far as a task needs them.

- **Read-only recon.** Tasks 1–9 are docs commits. Each edits this log, its verdicts file
  (`notes/Phase40-simplify-verdicts.md`, which these rules bind), and the next-task pointer
  in ROADMAP's queued-rounds bullet and `notes/Cleanup40.md`'s header (`CLAUDE.md`, F17); tasks 8
  and 9 also the other status surfaces. No Lean, no blueprint TeX, no `formalization.yaml`,
  no `queue.toml`. A probe or spike goes in `scratch/40-simplify/<task>/` (gitignored) and runs
  with `lake lean <file>`, never `lake env lean`. `git status` is clean apart from the commit's
  own files.
- **Route questions get compiler-checked spikes** (`notes/coordinate-phase-rescue.md` §6). Build
  the candidate composition with `sorry` at each gap, and record the exact kernel-checked residual
  goals, not a prose verdict.
- **Evidence.** A claim about a declaration comes from its statement and body, never its docstring
  (`CLAUDE.md` *Docstrings are not evidence*). Liveness is the Lean call chain (`CLEANUP.md`
  *Liveness*): task 1's closure here, and trial deletion with a whole-project build at landing;
  never grep or `\uses` alone.
- **No statement moves in the recon.** A verdict may propose a headline signature change, or a
  change to a blueprint statement's strength. Only the PI's sanction at Stop 2 lets one land
  (`notes/Cleanup40.md` §2, *All five rounds*).
- **Prior evidence stands unless a task brings a new argument.** Round 1's task 17 (a
  `Fin.succAbove`-general split-off ear nets no shorter) and task 24 (no `_three`/`_four`
  unification); round 2's residual shared tail (about 13 lines a hub, left); round 3's eight
  recommendations, which task 8 presents as written unless a task here changes a premise.
- **A verdict** is one entry in its task's subsection of the verdicts file, at most five lines:
  `**<id>, <name>: GO**` (or NO-GO); one sentence of why; the commit estimate (commits, rung, ⚠Z
  for the fragility zone); what it changes (a headline signature, a blueprint statement's strength,
  the dependency graph, or nothing a reader sees); any verdict it depends on; its evidence (read,
  measured, or a spike's residual). The detail goes in the task's commit message.
- **Gates for tasks 1–9.** `git diff --stat` shows docs only. This log stays under ~500 lines,
  forward-weighted, with a **Status:** header under 300 words and *Decisions* entries of at most 8
  lines. `notes/check-phase-note.py`'s name pattern skips `Phase40-*.md`, so run its `parse` and
  `offenders` on this file directly, as the open did. No local machine paths in the diff or the
  message.
- **Rungs.** The recon tasks are Opus (`notes/Cleanup40.md` §2 *Round 4*). A landing's rung is
  its verdict's: Opus in the fragility zone (`.claude/commands/coordinate-phase.md` *Fragility
  zone*), otherwise rung-mapped.

## Input IDs

`notes/Cleanup40.md` §2 *Round 4* lists the round's inputs, one line each, and this log names them
by their position there. Each input has one owner task, which writes its verdict; other tasks may
read it. Round 3's `r1`–`r8` are recommendations already: task 8 presents them, and task 1 answers
the one question `r1` left open, whether to delete its 29 off-headline names.

- `a1`–`a7`, round 1's candidates: `a1` the one-ended chain-side degree pin; `a2` the six
  `[DecidableEq β]` binders; `a3` the finsum rewrite; `a4` `pencilPair_of_habitat_ncard_eq_four`;
  `a5` `Pair2.lean`'s #4/#6 tails; `a6` `Arms.lean`'s `|C| = 0`/`|C| = 1` split; `a7`
  `Graph.X0Attains.of_closedEar`.
- `b1`–`b2`, round 2's: `b1` `.compl` against `ᶜ` in the two hubs; `b2` the merged hub's `hne`.
- `m1`–`m7`, round 3's *Moved* lines: the six missing `\uses` edges and the unfilled pair node, in
  that list's order.
- `c1`–`c9`, round 3's structural candidates, in that list's order (`c4` is the "…and its
  statement" line, `c8` the four-pin nodes, `c9` the caller-less toolkit halves).
- `r1`–`r8`, round 3's build-or-leave recommendations, as numbered there.
- `q1`–`q3`, the coordinator's starting questions: `q1` the open ears, `q2` `Pencil/` against
  `AlgebraicInduction/`, `q3` the Lean that feeds neither headline.
- Added by the tasks: `1a`, `1b`, `1c-i` and `1c-ii` are task 1's hand-ons (a)–(c) to task 2. A
  new finding takes the ID of the input it bears on, with a letter (`q3a`, `c3a`). Task 7's findings
  on no listed input are `7a`–`7i`.

## Lemma checklist (the round's task list)

One commit per task, in this order. Each line names the inputs it owns; its commit names its
verdicts.

- [x] **1. L — the liveness map** (`q3`, `b2`, and `r1`'s deletion question; Opus, docs). The
  closure of the 19 main results, the off-closure clusters, the verdicts and the hand-ons are in
  the verdicts file, *Task 1*.
- [x] **2. R — `pencil.tex`'s reduction layer** (`a2`, `a4`, `m1`–`m5`, `c2`–`c4`, design §6,
  task 1's hand-ons; Opus, docs). The shape and the verdicts are in the verdicts file, *Task 2*.
- [x] **3. N — node shapes outside the reduction layer** (`a1`, `m6`, `m7`, `c1`, `c5`–`c8`, task
  1's hand-ons; Opus, docs). Which side moves where a node and its pins disagree, or a node bundles
  results: the verdicts are in the verdicts file, *Task 3*.
- [x] **4. E — the open ears** (`q1`, `a7`, `c9`, with task 1's sizes; Opus, docs; two spikes).
  One argument or several, and if one, what shared statement: the reading and the verdicts are in
  the verdicts file, *Task 4*.
- [x] **5. A — where `Pencil/` re-proves** (`q2`, `b1`, `a3`; Opus, docs; five spikes). What
  `Pencil/` re-proves of `Theorem55.lean`, `Meet.lean` and the project's mathlib mirrors, with the
  hubs' `ᶜ` and the degree-sum pair: the reading and the verdicts are in the verdicts file,
  *Task 5*.
- [x] **6. P — Phase 39's producers** (`a5`, `a6`, and task 5's `q2d`; Opus, docs; four spikes).
  Whether a recorded cross-proof duplication admits a shared lemma that nets shorter: the reading
  and the verdicts are in the verdicts file, *Task 6*.
- [x] **7. G — the remaining long proofs** (round 1's §C screen, now structural, and task 6's
  hand-on; Opus, docs; five spikes). Is any long proof longer than its argument: the re-rank and
  the verdicts are in the verdicts file, *Task 7*.
- [x] **8. W — Stop 2, the write-up** (`r1`–`r8`, and every verdict; Opus, docs; `NEEDS_PI`). The
  entry is under *Autopilot: for the PI*; the round waits on the PI.
- [ ] **9. S — slice the sanctioned items** (after the PI's answer; Opus, docs). Transcribe the
  answer verbatim into *Decisions made*. Replace task 10's placeholder with one line per sanctioned
  item (10a, 10b, …), in dependency order, each with its rung and gates. Record each NO-GO and
  each item not sanctioned as a one-line verdict under *Decisions made*. Move an item the PI sends
  elsewhere (round 5, or **PROSE** in ROADMAP's queue) to *Moved to a later round*.
- [ ] **10. B — the sanctioned items land** (a placeholder until task 9). One commit each, green at
  every commit: whole-project `lake build` warning-clean and `lake lint` green; the blueprint gates
  (`blueprint/CLAUDE.md` *Static checks before commit*) on any TeX edit; and
  `CombinatorialRigidity/CLAUDE.md` *Forward-mode slices* on a changed statement, an additive
  successor or a deletion. A deletion is confirmed by trial deletion and a whole-project build. A
  commit that touches a headline re-runs the axioms harness.
- [ ] **11. X — close the round** (`CLEANUP.md` *Workflow* rule 5; docs). Whole-project
  `lake build` and `lake lint` green. The axioms harness re-diffed against `formalization.yaml`
  and re-run with `lake lean`: 19 of 19 at the three standard axioms. The ROADMAP row reads ✓, and
  `40-simplify`'s row in `.claude/autopilot/queue.toml` gets `done = true` (nothing else there
  changes). The status surfaces name round 5, `40-docs`, as next. *Moved to a later round* is
  mirrored into `notes/Cleanup40.md` §2 *Round 5*, or ROADMAP's **PROSE** bullet.

## Verdicts (Stop 2's inputs)

In their own file, `notes/Phase40-simplify-verdicts.md` (moved at task 4; *Decisions*). Each recon
task adds a subsection there, `### Task N (X)`, with one entry per input it owns, in the format
under *Scope*.

## Moved to a later round

Each line gives the task, its target (round 5, `40-docs`, or **PROSE** in ROADMAP's queue) and a
one-line reason. The same line goes into the target's plan section in the same commit. None yet.

## Blockers / open questions

- **Stop 2 (`NEEDS_PI`), the round's one planned stop.** The round waits on the PI's answer to the
  entry under *Autopilot: for the PI*: decisions 1–8, or the default there. Task 9 does not start
  before a PI entry follows it.

## Hand-off / next phase

**Waiting on the PI at Stop 2** (`NEEDS_PI`; *Autopilot: for the PI*). Nothing runs until a PI
entry follows the Stop-2 entry. **Then task 9 (S)** (Opus, docs only): transcribe the PI's answer
verbatim into *Decisions made*; replace task 10's placeholder with one line per sanctioned item
(10a, 10b, …), taken from the entry's landing order, each with its rung (the entry's Opus
corrections hold) and gates; record each NO-GO and unsanctioned item as a one-line verdict; move
anything the PI sends elsewhere to *Moved to a later round*. The smallest next commit is that
transcription and slicing, one docs commit. If the PI sanctions `1a`'s retirement, the first
landing to touch ROADMAP §40 is `1a`'s deletion (its "stays as conditional theorems", marked
verbatim).

## Decisions made during this round

- **2026-10-04, the open: the granularity.** Seven recon tasks, each one coherent question over a
  bounded reading surface. The mechanical map comes first, since three tasks' verdicts rest on it.
  Then come the two blueprint regions whose inputs are statement-against-pin questions, and then
  the three deeper questions. The write-up is its own commit because it is the stop. A task per
  input would re-pay a dispatch's reading for each of 36 inputs; fewer tasks would put two of the
  spike-bearing tasks 4–6, or task 7's long reading, into one sitting. The landings are sliced
  after Stop 2, once the PI has chosen them.
- **Probes stay in scratch.** No recon task commits a script. Its figures are tagged *measured,
  script not retained* (`HARNESS.md` *Reproducibility*), as rounds 1 and 3 did for liveness. No
  deletion rests on such a figure: a sanctioned retirement is re-verified at landing by trial
  deletion and a whole-project build (`CLEANUP.md` *Liveness*).
- **The landing order is set at task 9, not now.** It depends on what the PI sanctions, and on
  task 1's map: a retired cluster can moot another verdict, as retiring `TwoCut.lean` would moot
  `b2` and half of `b1`.
- **2026-10-04, task 1: a pinned cluster goes to the task that reads its node.** The checklist
  named hand-ons to tasks 2 and 4 only; the map found pinned dead nodes in sections neither reads.
  Task 2 takes those the reduction layer `\uses`; task 3, which already owns `c5`, `c6`, `c8` and
  the girth chain's `a1`, takes the rest outside the ears, as one-line verdicts where prior
  evidence stands (round 3 kept the unused parts the chapter's opening names).
- **2026-10-04, task 4: the verdicts move to their own file** (the coordinator's decision). At 440
  lines, with tasks 4–8 still to write, the log would pass its ~500-line tripwire. *Verdicts*,
  tasks 1–3 verbatim, moved to `notes/Phase40-simplify-verdicts.md`, as round 3 moved its exemplar
  to `notes/Phase40-exposition-exemplar.md`; *Verdicts* here points there, *Scope* binds it, and
  each task from 4 on writes its subsection there.
