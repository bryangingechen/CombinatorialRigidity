# W4 reopened — HELD (2026-09-25)

**Status: HELD** (PI, 2026-09-25, verbatim in `adjudications.md`). The W4 line produced the `X₀`
programme. That programme's formalization is now **Phase 40**: the plan and the proof map are in
`notes/Phase40-design.md`, and the first sub-phase is in `notes/Phase40a.md`. The one piece of
W4 on the adopted route is **W4-A** (W4-L1), which is Phase 39's closing item L0b
(`notes/Phase39.md` item 0). Everything else on the W4 line is **held**, as the fallback, until
Phase 40's MOTIVES layer lands in Lean; then the PI re-decides it.

**Earlier text is frozen verbatim in `W4-reopen-archive.md`**, which is not read on load:
- the first freeze, at `73ea85a3`: the 2026-09-23 strategy re-think, P1–P5, T0–T4, *START HERE*;
- the second freeze, at `d90bae12`: the 2026-09-25 *Where things stand*, the second-reading table,
  *Next*, *Decided*, *PI calls pending*, the Lean-side picture and the standing constraints.

Section references elsewhere of the form "`W4-reopen.md` …" resolve there.

## What is held

- **The split/contract architecture** for `hcontract` (L3′ branches 0–3c). Its kernels are
  **(K-res)** / `kres`, **(K-c)** and **(K-bare-c)** with (α). The last two were never attacked,
  and both are pinned in the pre-2026-09-16 shape. Restating them is a kernel-shape decision, the
  PI's, if they are ever unheld.
- **T1**, the W4 wrapper carrying (K-res), with its scope question unanswered; **W4-L4b**
  (`exists_degree_two_of_co1_rigid`, pinned and spike-elaborated); **W4-L2/L3′/L5**; `hnoGood'`.
- **smark's O7e programme** on `hbareSplit` at `m ≤ 4`, paused. Its status surface is
  `notes/attacks/smark/state.md`.
- *Deferred, not cancelled:* the adversarial census (`n = 9–14`, biased to 2-edge-cuts and large
  `def₂ − def₃`). It is now a falsification test of (MC-89).

**Closed on W4, do not redo:**
- route 3 packaging (b);
- (T);
- (E-loc), refuted and unnecessary;
- (E-pair) and (V);
- gates N8/N9/N10/N10b.

Their records are `workbook/W4.md` and `notes/Phase39-design.md` §§ *W4 decomposition recon* and
*W4-L4 identification recon*.

## Standing constraints (bind while held)

- **Files.** Never touch `notes/attacks/smark/` or `workbook/attack-smark.md`. A resumed smark
  runs in its own worktree.
- **Do not:**
  - edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat` or the landed headline;
  - write the (K-res) brief;
  - launch `kres` or a contraction attack;
  - treat `W4.md`'s (K-res) statement or cost estimates as current, since both predate 2026-09-16;
  - ask smark for anything.
- **Landing a mathematical repair** in §(K-main) follows `notes/Phase40-design.md` §5.
