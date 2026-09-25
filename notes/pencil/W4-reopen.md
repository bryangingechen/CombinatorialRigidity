# W4 reopened — the live hand-off

**Read this first, then `notes/Phase39.md` *Status*.** This file is the forward part only: where the
W4 line stands, the next tasks, the PI calls pending, and the standing constraints. The earlier
hand-off text is frozen verbatim in **`W4-reopen-archive.md`**, not read on load: the 2026-09-23
strategy re-think and its P1–P5 ranking, each session's P1 paragraph, the unranked directions, tasks
T0–T4, *Why reopen*. Section references elsewhere of the form "`W4-reopen.md` P1" or "*START HERE*"
resolve there. The PI's calls, verbatim, are in `adjudications.md` (§§ 2026-09-23 onward). The
mathematics is `workbook/K-main.md` §(K-main), tag `MC-`. It is about 6 000 lines, so query it
with `python3 notes/ledger.py --label '(MC-89)'` or `--brief …` rather than reading it end to end.

## Where things stand (2026-09-25)

The W4 line has become **P1, the `X₀` programme**. Over a fixed planar picture `q` the pencil
condition is linear in the heights, so the configuration space has a main component `X₀`, a vector
bundle over generic pictures ((MC-1)–(MC-3)). The motive (MC-10)(a) reads: *`X₀(G)`'s generic point
attains `6(|V| − 1) − def₃(G)`*. It is proved by strong induction on graphs, using ear, split-off,
contraction and cut steps on `X₀`.

- **The coverage theorem (MC-89).** Every finite simple connected graph of minimum degree ≥ 2
  satisfies (MC-10)(a), **modulo Jackson–Jordán** (their pin-collinear rank theorem; field-general
  only `[INFORMAL]`, (MC-33)(i)). Step MC16's argument is second-read. Step MC20 claims to replace
  every exact-over-ℚ certificate it consumed by a hand proof over every infinite field.
- **The generic motive (MC-133).** Every *feasible* such graph has `HasGenericPencilRealization K 3 G`,
  mod Jackson–Jordán, in characteristic 0 (Step MC19).
- **A second proof** of (MC-89)'s in-𝒮 half, by the ear route alone (MC-148), Step MC21. The last ear
  cell narrows to "Case II-cyclic" (MC-154), which coverage does not need.

**Second-reading status by step.** The next session updates this table. The column "on (MC-89)'s
path" is the transitive closure of (MC-89)'s *explicit* citations, from `ledger.py --label`; a proof
can lean on more than it cites.

| Step | on (MC-89)'s path | status |
|---|---|---|
| MC1–MC6, foundations and the flat rank | (MC-4)–(MC-6) | coordinator-checked, with per-instance driver asserts; **never independently re-derived** |
| MC7–MC9, exact gain, nondegeneracy | (MC-9) | second-read |
| MC10, the ear step | (MC-16), (MC-18)–(MC-22), (MC-24)–(MC-26) | coordinator-checked; (MC-16), (MC-17), (MC-22), (MC-26) re-read but not re-derived; (MC-22) repaired by a reader. **Not independently re-derived** |
| MC11 and (MC-33), split-off and Jackson–Jordán beyond ℝ | (MC-33) | re-derived by a second agent |
| MC12, contraction | (MC-34), (MC-37)–(MC-39) | second-read |
| MC13, short ears with the antecedent | (MC-45), (MC-46) | itself a second reading, which re-derived them |
| MC14, the reach | (MC-54), (MC-59) | second-read |
| MC15, partition counts | (MC-67)–(MC-71) | (MC-68)–(MC-71) second-read; (MC-62)–(MC-67): **reader D in flight** |
| MC16, the coverage theorem | (MC-80), (MC-87), (MC-89) | second-read, by two readers |
| MC17–MC18, the ear cells | (MC-97), (MC-115) | not second-read |
| MC19, the generic motive | — | **reader A in flight** |
| MC20, the certificate leaves | (MC-134), (MC-139), (MC-141) | **reader B in flight** |
| MC21, EAR covers 𝒮 | — | **reader C in flight** (with Step MC17's (MC-105)) |

## Next, in order

1. **Land the four second readings in flight** (dispatched 2026-09-25, read-only, reports in the
   session's scratch): A on Step MC19 ((MC-123), (MC-129), (MC-130), (MC-133) first, plus a check of
   the Lean predicates' definitions); B on Step MC20 (and whether its certificate list is complete);
   C on Step MC21 with (MC-105); D on Step MC15's (MC-62)–(MC-67).
2. **Second wave, one dispatch each:** Steps MC17–MC18; and the path claims never independently
   re-derived, Step MC10's ear step with Steps MC1–MC6's (MC-4)–(MC-6).
3. **An architecture recon** (read-only, for the PI's call below), best run after reader A lands.
   Map (MC-89) and (MC-133) onto the Lean consumer, `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
   and `PencilPair`'s three conjuncts, working from the Lean rather than from prose. Which carried
   hypotheses would they discharge (`hK`, parts of `hcontract`, `hbareSplit`?) and which would stay?
   What Lean statement would the `X₀` route formalize, and what would it cost: Jackson–Jordán,
   the `X₀` steps, and reuse of the molecular programme (pencil ⊆ panel, so (MC-10)(a) implies the
   molecular theorem for these graphs)? In particular, can a stronger *landed* theorem replace
   each Jackson–Jordán use? That is a statement-shape choice, and Phase 25 made one to avoid two
   Jackson–Jordán papers (`DESIGN.md` *Formalize everything the argument uses*).

## PI calls pending

- **Architecture.** Should the W4/`hK` Lean plan move to the `X₀` induction? What would stop: the
  `kres` attack (held), the contraction kernels (K-c)/(K-bare-c) (never attacked), and smark's O7e
  programme, which is unnecessary in principle for the Lean target if `X₀` suffices (no edit to
  smark's files; the PI decides). Task 3 above is the input.
- **Jackson–Jordán: when and how to formalize it, not whether.** The project formalizes every
  result it uses (`DESIGN.md` *Formalize everything the argument uses*); citing it is not an option.
  The call is the scope: over `ℝ`, or field-general following (MC-33)'s second reading. Or it
  is the route: task 3 asks whether a landed theorem can stand in for it.
- **Characteristic.** The Lean target is over any infinite field. Since Step MC20 (if confirmed), the
  only characteristic-0 dependence is Jackson–Jordán's field-general proof, `[INFORMAL]` (MC-33)(i).
- **T1's scope question**, open since 2026-09-23 and moot if the architecture moves: a full
  L3′-successor wrapper, the residual-branch producer only, or a design doc only (archive, T1
  finding 6).
- *Deferred, not cancelled:* the adversarial census (`n = 9–14`, biased to 2-edge-cuts and large
  `def₂ − def₃`). With (MC-89) claimed proved, it would now be a falsification test of it.
- *Structural chore:* split `K-main.md` by step. It costs repointing the drivers' docstrings and
  `labels.md`, so do it in a deliberate commit.

## The Lean-side picture, if the split/contract architecture stays

`hcontract`'s L3′ skeleton has these branches; T1's findings are in the archive.
- **0** — `¬ TwoEdgeConnected`: the landed cut arm.
- **1** — `¬ Simple`: the bare motive only, via W4-A (W4-L1).
- **2** — simple and infeasible: distinct and bare, via `hbareContract` (K-bare-c). (α) lands here
  entirely.
- **3a** — co-1: W4-L4b and `hremove` (W4-L5).
- **3b** — a good contraction: `hKc` (K-c) and W4-B (W4-L2).
- **3c** — a residual: (SAFE-RES′), the L7a residual sibling, and (K-res).

There are three research kernels, with disjoint habitats: **(K-res)**, **(K-c)** and **(K-bare-c)**.
The last two were never attacked, and both are pinned in the pre-2026-09-16 shape: no induction
hypothesis, and a stale conclusion. T1 recommended restating them, but that kernel-shape decision is
the PI's. T1's draft `hKres` is `hK` token for token, with `hnoRigid` replaced by the residual
bundle plus `PencilNondegFeasible K G`. (S3) `a ≁ b` follows from (T). The full draft is in the
archive, T1. Closed on W4, do not redo: route 3 packaging (b); (T); (E-loc) refuted and
unnecessary; (E-pair) and (V); gates N8/N9/N10/N10b (`workbook/W4.md`, `notes/Phase39-design.md`
§§ *W4 decomposition recon*, *W4-L4 identification recon*).

## Standing constraints

- **Gate G0** (PI, 2026-09-23; `adjudications.md`): the Lean hold is lifted only for (i) a W4
  wrapper, a new declaration carrying (K-res) and any other unsettled piece as hypotheses, with no
  `sorry` and no edit to smark's consumer; and (ii) W4-L4b (`exists_degree_two_of_co1_rigid`).
  W4-L1/L2/L3′/L5 stay parked until the PI's next call.
- **Files.** Never touch `notes/attacks/smark/` or `notes/pencil/workbook/attack-smark.md`. A
  resumed smark runs in its own worktree. Keep edits to the shared files (`notes/Phase39.md`,
  `ROADMAP.md`, `notes/harness/incidents.md`) small and anchored. The shared-checkout commit rule
  was retired on 2026-09-24. Commit rules are in `CLAUDE.md` *Working*.
- **Landing a reader's report.** Repairs go in place, marked as the reader's. New claims get the
  next free `MC-` labels, with a `labels.md` row in the same commit. Port any new driver to
  `notes/scripts/w4/` with a `README.md` row (`HARNESS.md` *Reproducibility*). Run
  `python3 notes/ledger.py --lint` before committing.
- **Do not:**
  - edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` or the headline theorem;
  - write the (K-res) brief before T1's Lean declaration exists;
  - launch `kres` or a contraction attack before the architecture call;
  - treat `W4.md`'s (K-res) statement or cost estimates as current, since both predate 2026-09-16;
  - ask smark for anything.
