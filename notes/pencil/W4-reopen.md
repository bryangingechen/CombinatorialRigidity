# W4 reopened — the live hand-off

**Read this first, then `notes/Phase39.md` *Status*.** The forward plan, now that the architecture
is decided, is **`X0-formalization.md`**. This file is the W4 line's forward part only: where it
stands, the next tasks, the PI calls pending, and the standing constraints. The earlier
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
  only `[INFORMAL]`, (MC-33)(i)). Step MC16's argument is second-read. So is Step MC20, which
  replaces every exact-over-ℚ certificate it consumed by a hand proof over every infinite field. A
  reading-level audit (MC-166) finds no other characteristic dependence, so over any infinite field
  (MC-89) holds modulo (MC-33)(i).
- **The generic motive (MC-133).** Every *feasible* such graph has `HasGenericPencilRealization K 3 G`,
  mod Jackson–Jordán, in characteristic 0 (Step MC19, second-read 2026-09-25). And every such graph,
  feasible or not, has `HasDistinctPencilRealization K 3 G` (MC-157), with the same caveats.
- **Against the Lean** (the 2026-09-25 architecture recon, below): these theorems discharge `hK`,
  `hbareSplit`, and all of `hcontract` except W4-A. A simpler top-level route compiles with only W4-A
  left.
- **A second proof** of (MC-89)'s in-𝒮 half, by the ear route alone (MC-148), Step MC21. The last ear
  cell narrows to "Case II-cyclic" (MC-154), which coverage does not need.

**Second-reading status by step.** The next session updates this table. The column "on (MC-89)'s
path" is the transitive closure of (MC-89)'s *explicit* citations, from `ledger.py --label`; a proof
can lean on more than it cites.

| Step | on (MC-89)'s path | status |
|---|---|---|
| MC1–MC6, foundations and the flat rank | (MC-4)–(MC-6) | second-read 2026-09-25; the Plücker bookkeeping checked by hand |
| MC7–MC9, exact gain, nondegeneracy | (MC-9) | second-read |
| MC10, the ear step | (MC-16), (MC-18)–(MC-22), (MC-24)–(MC-26) | second-read 2026-09-25; (MC-25), (MC-26) scope-repaired; (MC-27)'s bad set repaired; (MC-169), (MC-170) added |
| MC11 and (MC-33), split-off and Jackson–Jordán beyond ℝ | (MC-33) | re-derived by a second agent |
| MC12, contraction | (MC-34), (MC-37)–(MC-39) | second-read |
| MC13, short ears with the antecedent | (MC-45), (MC-46) | itself a second reading, which re-derived them |
| MC14, the reach | (MC-54), (MC-59) | second-read |
| MC15, partition counts | (MC-67)–(MC-71) | second-read in full (2026-09-25 for (MC-62)–(MC-67): no gap; one missing merge step supplied) |
| MC16, the coverage theorem | (MC-80), (MC-87), (MC-89) | second-read, by two readers |
| MC17–MC18, the ear cells | (MC-97), (MC-115) | second-read 2026-09-25; nothing refuted; (MC-89) never used a false value; (MC-171) added |
| MC19, the generic motive | — | second-read 2026-09-25; (MC-130)'s cycle citation repaired; (MC-157), (MC-158) added |
| MC20, the certificate leaves | (MC-134), (MC-139), (MC-141) | second-read 2026-09-25; the argument leaves audited for characteristic (MC-166); the certificate list is complete |
| MC21, EAR covers 𝒮 | — | second-read 2026-09-25; accounting repaired (a second proof inside 𝒮 only); (MC-162)–(MC-165) added |

## Next, in order

1. **All second readings have landed** (readers A–F, 2026-09-25): every claim on (MC-89)'s path is
   independently re-derived at least once. Recon H (`n = 2` sizing) has landed too. Writer I
   (Jackson–Jordán over any field) was asked to wrap up early; land whatever it returns as a
   fallback (`X0-formalization.md` §6).
2. **Then open the formalization from `X0-formalization.md`**, the planning note. It holds the
   target, the index of everything already done, the proposed blueprint layers, the risk points,
   the open calls in gating order, and one-line briefs for re-dispatching anything still in flight.
   The architecture and the characteristic target are decided (below).

**The architecture recon (2026-09-25)** is recorded in full in `notes/Phase39-design.md`
§ *X₀ architecture recon (2026-09-25)*, with its Lean spike verbatim; the coordinator re-elaborated
the spike, with exactly two `sorry`s. In one line: (MC-89), (MC-133)(ii) and (MC-157) discharge
`hK`, `hbareSplit`, and all of `hcontract` except W4-A. A simpler `pencil_conjecture_of_arms_pair`
route compiles with only W4-A left, and no landed theorem replaces Jackson–Jordán.

## Decided (PI, 2026-09-25; verbatim in `adjudications.md`)

- **Architecture: the simpler route.** The Lean target is a headline shaped like the spike's
  `spike_pencil_conjecture_of_X0`.
- **Characteristic: every infinite field.** So Jackson–Jordán's equality is needed field-general.
  The `n = 2` recon shows the landed KT spine supplies it over every infinite field.

## PI calls pending

The gating order is in `X0-formalization.md` §5.
- **Phase structure** for the formalization: a new, sub-lettered phase, or new items inside Phase 39.
- **The W4-L1 (W4-A) hold lift.** W4-A is on the adopted route.
- **The Jackson–Jordán route's shape.** The `n = 2` sizing recon (2026-09-25, `notes/Phase39-design.md`)
  shows (a) the landed KT spine extends to `n = 2` over every infinite field, compiler-checked,
  about 3–6 commits. So (b) the TR is only a fallback. Weakening the landed statements in place is the
  default: a weaker hypothesis gives a stronger theorem, and siblings would only duplicate. The
  open part is where the commits land (`X0-formalization.md` §5).
- **The kernels and smark's O7e:** cancel or hold. The recon reads *hold* until the `X₀` motives
  land in Lean.
- *Deferred, not cancelled:* the adversarial census (`n = 9–14`, biased to 2-edge-cuts and large
  `def₂ − def₃`), now a falsification test of (MC-89).
- *Structural chore (deferred 2026-09-25):* split `K-main.md` by step before blueprint transcription.
  The design as scoped:
  - `K-main.md` keeps the header, a file index, and Steps MC1–MC9.
  - Each later step moves to `workbook/K-main-MCnn.md`, which the ledger's `workbook/*.md` glob
    picks up.
  - Each file opens with a `## §(K-main) — Step MCnn …` heading. The ledger keys sections on the
    `§(…)` token (`section_key`), and `DIRECTION` matches only "direction XXX", so every claim keeps
    seckey `§(K-main)` and `--delta` reports it RELOCATED.
  - Existing "`K-main.md` Step MCnn" pointers resolve through the index, so no driver docstring
    changes.
  - Open: this breaks the workbook's "one section per file". The precedent is `bare-ext/`, one
    section over many files, told apart by direction codes. Check `workbook/README.md`'s index,
    `check-gapmap-cells.py` and `gapdiff.py` before splitting.
  Deferred because of that open convention question, and because writer I was still reading the
  file.

## The Lean-side picture, if the split/contract architecture stays (the fallback)

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
  - launch `kres` or a contraction attack: held, and the adopted route does not need them;
  - treat `W4.md`'s (K-res) statement or cost estimates as current, since both predate 2026-09-16;
  - ask smark for anything.
