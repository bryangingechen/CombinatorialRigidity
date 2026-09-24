# `notes/w4-pending/` — agent write-ups awaiting landing

**Not part of the workbook, and nothing here is authoritative.** This directory holds read-only
agent outputs from the third 2026-09-24 W4-reopen session (`notes/pencil/W4-reopen.md`, P1). They
returned after the session had to stop for context, and are committed verbatim so that nothing is
lost. The next session lands each one into `notes/pencil/workbook/K-main.md` §(K-main), as the
earlier tracks were, and then deletes it from here:
- re-read the write-up;
- renumber its provisional labels into the `MC-` series (next free: `(MC-142)`);
- port its scripts into `notes/scripts/w4/`, with the canonical path bootstrap and renamed where a
  name is generic;
- re-run every cited figure;
- write the step's preamble, record second-reading status, and add the README rows.

## `trackJ/` — Track J, the last ear cell (MC-117) and a second structural proof

*Claimed by its author, not second-read; the coordinator has not checked it.*
- (J-6): every graph in the sparse class 𝒮 has a chain whose ear step closes: usable, or in cell
  (a′) (closed by (MC-105)), or closed by the rigid-set closure (J-2).
  - This would give a **second proof of (MC-89) inside 𝒮**, without Theorem S (MC-80) or additivity
    (MC-87). It still shares (MC-68)(d) and Jackson–Jordán with the first.
- (J-7)–(J-9): cell (c′) at `δ ∈ {3, 4}` closes except "Case II-cyclic" (J-10), which (MC-89) does
  not need.
- It measured every 𝒮 member on 9–13 vertices as closable (`earcover.py`). The commands are in the
  write-up's *Scripts* table, run from the repository root with `PYTHONHASHSEED=0`.

Scripts import `notes/scripts` and `notes/scripts/w4` through `os.getcwd()`, so run them from the
repository root. `foldcheck.py` imports `chordprobe`, which is landed in `notes/scripts/w4/`.
