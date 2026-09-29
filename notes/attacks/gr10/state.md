# Attack gr10 — state

**Part B RETIRED on the PI's word, 2026-09-29**: no longer a fallback; it is retired with the rest of `notes/Phase40-design.md` §6 at Phase 40's close, which proved the pencil conjecture by the main-component route (verbatim in `notes/pencil/adjudications.md`).

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 1 · last session: 2026-09-23 (session 1; S1–S4) · review 1: 2026-09-23 (verdict *stop — close Part A*; fixes landed as S5 and revisions of S1, S2, S4) · baseline HEAD: 84f60e2d (branch `attack-gr10`) · consumer unchanged since `084ee4ff` · **CLOSED on the PI's word (2026-09-23): Part A done, verdict "characteristic 2 limits the grid method only, at every shape tested"; Part B stays a fallback, reopened only by the PI**

## Statement <!-- budget 10 -->
Probe (P), brief §A2: `HasGenericPencilRealization K 3 G` over every infinite field `K` of characteristic 2 — `hK`'s *conclusion* (kernel of `pencilPair_of_splitOff_of_habitat`), not `hK` — at the shapes of two populations, both exactly tight (`5|E| = 6(|V|−1)`): the 907-shape census (`grid.census_shapes()`) and the (GR-26) cubic stratum (1 967 classes, 40 742 labelled; caps in workbook S3). Also at four named graphs in `hK`'s habitat outside both (S5).
Route: the bridge `hasGenericPencilRealization_of_independent_pencilRow_target` (`[Infinite K]`, no characteristic; axioms `propext`, `Classical.choice`, `Quot.sound`).
Unused: all of `hK`'s antecedents (IH, split-off antecedent, `degree v = 2`, `¬PencilHub a ∨ ¬PencilHub b`, `e₀ ∉ E`, `eₐ ≠ e_b`), because (P) concerns the conclusion only (brief §A4).

## Current route and proof sketch <!-- budget 30 -->
Per shape: the Lean `pencilRow` matrix at a `GF(2^20)` seed (`drivers/char2chart.py`), greedy elimination selects `s`, an independent dense re-rank verifies it.
- **S1 (transfer):** a nonzero minor at one `GF(2^k)` point ⟹ nonzero mod 2 ⟹ a non-root over any infinite char-2 `K` ⟹ the bridge. Remark (iv): the same at any deficiency `d`, with `|s| = 6(|V|−1) − d`.
- **S2:** census 907/907 hits. The odd-`p` controls rule out a rank-lowering transcription error. The full-rank half of O1 is the reading of the driver against the Lean (the hub-normal sharing pattern), re-done independently at review 1.
- **S3:** cubic stratum 1 967/1 967 classes.
- **S4:** the report and the verdict, with population caps: both populations exactly tight, no residual of W4's (K-res) in either.
- **S5:** the counting bound `rank ≤ 6(|V|−1) − partitionDef G 3 f` (any field) certifies `def₃` from a hit. `C₅`, `C₆`, θ(3,4,4) (def₃ = 0, two of them over-counted) and `C₈` (def₃ = 2) are `hK`-habitat graphs that hit (`--small`).
Open obligations: **none**. O1–O5 are discharged (O1 by S2's controls plus the reading, O2 in S4, O3 = S1, O4 = S2 + S3 + S5, O5 = S4).
Not commissioned (PI, 2026-09-23): N1, def > 0 as a population. The one characteristic-2 population bearing on a live decision is W4's residual pool (the field binder of `hKres`). It is an optional leg of W4's T2 recon, not a gr10 session.

## Where it breaks <!-- budget 10 -->
Nothing: the attack is closed. What stays undecided is outside the probe's reach: (P) is per shape, so the field range of `hK`'s conclusion on the infinite tight stratum, on the over-counted corner and at def > 0 has only finite evidence (S2, S3, S5), and no shape anywhere was found where characteristic 2 fails. A uniform statement comes only through a proof of `hK` (smark's R2, which by smark's own record uses no characteristic; not checked here).

## Tried on this route, and what each rules out <!-- budget 10 -->
- `--sweep` (907 census, seed 20260923): 907 hits. Rules out a char-2 obstruction at any census shape. Re-run identically at review 1.
- `--cubic` (seed 20260924): 1 967/1 967 classes, re-run identically.
- `--control --cap 907` (`GF(2^31−1)`, `GF(10007)`): 907/907. Rules out a rank-lowering transcription error.
- `--small` (seed 20260925): `P₃`, `C₅`, `C₆`, `C₈`, θ(3,4,4) all at `6(|V|−1) − def₃`.
- `blindaxes.py --imports --population`: fences 6 (Plücker indices) and 3 (selector slots), both structural.

## Next steps <!-- budget 5 -->
1. None for gr10. Merge branch `attack-gr10` into master at the PI's timing, when smark is between sessions (`notes/pencil/W4-reopen.md` *Where you are working*).
2. Reopening Part B, or a new gr10 question, is the PI's call; start from brief Part B and this file.

## Worries <!-- budget 5 -->
- Retired at review 1: the `def₃` identification (a hit certifies it through S5(a), so the count-matroid value is a cross-check) and the transcription (checked against the Lean definitions by the reviewer).
- The census and cubic populations are the corpus's own generators, and both are exactly tight (S4's caps).

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (closed at review 1)
- Open obligations: 0 (trend: 5 → 0 within session 1; closed)
