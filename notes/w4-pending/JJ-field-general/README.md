# Staged, unlanded: Jackson–Jordán over any infinite field (writer I, 2026-09-25)

**Not authoritative, and not in the ledger's corpus.** `notes/w4-pending/` sits outside
`notes/pencil/workbook/`, so its placeholder labels `(NEW-I1)`–`(NEW-I27)` are invisible to
`notes/ledger.py`. This follows the precedent of Track J (`e2ec9927`, landed as Step MC21 in
`73ea85a3`).

**What it is.** `write-up.md` is a read-only writer's complete write-up of Jackson–Jordán's Thm 6.1
and Thm 7.1 over every infinite field (TR-2006-06). It turns §(K-main)'s (MC-33)(i) from a table of
verdicts into a written proof:
- bypass R2 is carried as an induction invariant;
- every ε-move becomes a Zariski move with a named parameter and excluded set;
- the brick and superbrick lemmas are re-proved, with no Tutte–Nash-Williams.

It is copied verbatim from the writer's message. Its driver is already ported:
`notes/scripts/w4/jjbuild.py`, with the canonical bootstrap and the local path removed.
`--run` reproduces the writer's output byte for byte (75/75), and `--selftest` passes.

**Why it is staged, not landed.** The 2026-09-25 `n = 2` sizing recon (`notes/Phase39-design.md`)
showed the landed KT spine extends to `n = 2` over every infinite field. That replaces every
Jackson–Jordán use on the `X₀` route. So this proof is a **fallback**, not on the route
(`notes/Phase40-design.md` §2, §3 BRIDGE). It is also a one-writer proof, not yet second-read.

**To land it, if ever wanted** (the procedure the 2026-09-25 readers' landings followed):
1. Dispatch a second reader on `write-up.md` (brief: `notes/Phase40-design.md`, Appendix).
2. Land the result as a sub-section of K-main's *Jackson–Jordán beyond ℝ*. Renumber
   `(NEW-I…)` to the next free `MC-` labels (`ledger.py --reserve`), with a `labels.md` row.
3. Move (MC-33)(i)'s tag from `[INFORMAL]` to `[PROVED]` only after the second reading.
4. Delete this directory in the same commit.
