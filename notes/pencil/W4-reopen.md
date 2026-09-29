# W4 reopened — RETIRED (2026-09-29; held 2026-09-25 to 2026-09-29)

**Status: RETIRED** (PI, 2026-09-29, verbatim in `adjudications.md`, the Phase 40 close entry;
held from 2026-09-25 until then). The W4 line produced the `X₀` programme, whose formalization,
**Phase 40** (`notes/Phase40-design.md`), closed 2026-09-29 with the pencil conjecture proved
outright (`pencil_conjecture`). The one piece of W4 on the adopted route was **W4-A** (W4-L1),
Phase 39's closing item L0b (`notes/Phase39.md` item 0). Everything else on the W4 line was held
as the fallback until MOTIVES landed, and is now **retired**; its landed Lean stays as conditional
theorems.

**Earlier text is frozen verbatim in `W4-reopen-archive.md`**, which is not read on load:
- the first freeze, at `73ea85a3`: the 2026-09-23 strategy re-think, P1–P5, T0–T4, *START HERE*;
- the second freeze, at `d90bae12`: the 2026-09-25 *Where things stand*, the second-reading table,
  *Next*, *Decided*, *PI calls pending*, the Lean-side picture and the standing constraints.

Section references elsewhere of the form "`W4-reopen.md` …" resolve there.

## What was held, now retired

- **The split/contract architecture** for `hcontract` (L3′ branches 0–3c). Its kernels are
  **(K-res)** / `kres`, **(K-c)** and **(K-bare-c)** with (α). The last two were never attacked,
  and both are pinned in the pre-2026-09-16 shape.
- **T1**, the W4 wrapper carrying (K-res), with its scope question unanswered; **W4-L4b**
  (`exists_degree_two_of_co1_rigid`, pinned and spike-elaborated); **W4-L2/L3′/L5**; `hnoGood'`.
- **smark's O7e programme** on `hbareSplit` at `m ≤ 4`; smark is CLOSED
  (`notes/attacks/smark/state.md`, its header line).
- *Not covered by the retirement, which named design §6 only:* the adversarial census
  (`n = 9–14`, biased to 2-edge-cuts and large `def₂ − def₃`), deferred, not cancelled, as a
  falsification test of (MC-89), which Phase 40 has since proved in Lean.

**Closed on W4, do not redo:**
- route 3 packaging (b);
- (T);
- (E-loc), refuted and unnecessary;
- (E-pair) and (V);
- gates N8/N9/N10/N10b.

Their records are `workbook/W4.md` and `notes/Phase39-design.md` §§ *W4 decomposition recon* and
*W4-L4 identification recon*.

## What still binds after the retirement

- **The landed Lean stays.** Do not edit `hK`, `hbareSplit`, `pencilPair_of_splitOff_of_habitat`
  or the Phase 39 headlines; they are conditional theorems on record.
- **Do not treat `W4.md`'s (K-res) statement or cost estimates as current**, since both predate
  2026-09-16.
- Reopening any retired item is the PI's call.
