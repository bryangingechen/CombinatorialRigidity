# Attack gr10 — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 1 · last session: 2026-09-23 (session 1; S1–S4) · baseline HEAD: 84f60e2d (worktree branch `attack-gr10`) · consumer unchanged since `084ee4ff` (`git diff 084ee4ff HEAD -- CombinatorialRigidity` empty; `hK` token-identical to brief §A1) · **count 0: probe (P) PROVED on both populations; report S4 delivered — PI decision pending**

## Statement <!-- budget 10 -->
Probe (P), brief §A2: for every shape `G` of the 907-shape census (`grid.census_shapes()`), `HasGenericPencilRealization K 3 G` over every infinite field `K` of characteristic 2 — `hK`'s *conclusion* (kernel of `pencilPair_of_splitOff_of_habitat`) at def = 0, not `hK`.
Route: the bridge `hasGenericPencilRealization_of_independent_pencilRow_target` (`[Infinite K]`, no characteristic): `G.Simple`, `V(G).Nonempty`, `∀ v, |closedHubNbhd v| ≤ 3`, triangle-free, and `hEsc` (selector, seed, genuine-edge indices `s` with `|s| = 6(|V|−1) − def₃ G`, `pencilRow`s at `s` independent).
Unused: all of `hK`'s antecedents (IH, split-off antecedent, `degree v = 2`, `¬PencilHub a ∨ ¬PencilHub b`, `e₀ ∉ E`, `eₐ ≠ e_b`) — (P) concerns the conclusion only (brief §A4).

## Current route and proof sketch <!-- budget 30 -->
Per shape: the Lean `pencilRow` matrix at a `GF(2^20)` seed, transcribed from `PencilSeed.ofCoord`, `hubSlotNormal`, `pencilChartPoint` (`cross₃`), `extensor`/`screwBasis`, `annihRow`, `hingeRow` (`drivers/char2chart.py`); greedy elimination selects `s`, an independent dense re-rank verifies it.
- **S1 (transfer, proved):** a nonzero `s × c` minor at one `GF(2^k)` point ⟹ its ℤ-polynomial is nonzero mod 2 ⟹ a non-root over any infinite char-2 `K` ⟹ the bridge. Every bridge hypothesis discharged by name; `def₃ = 0` via the count-matroid form (Nash-Williams–Tutte).
- **S2 (proved):** 907/907 census shapes hit, first seed each. Controls: odd `p` 907/907 at `6(|V|−1)`; `P₃`, `C₈` short as expected.
- **S3 (proved):** (GR-26) cubic stratum, 1 967/1 967 isomorphism classes = 40 742 labelled shapes, hcard/simple/triangle-free/def = 0 asserted at each.
- **S4:** report to the PI — verdict "characteristic 2 limits the *method* only, at every shape tested".
Open obligations: **none** on the brief's route (O1–O5 all discharged: O1 by S2's controls, O2 in S4, O3 = S1, O4 = S2 + S3, O5 = S4).
Candidate next obligations, each the PI's call (none is consumed by the brief as written):
- **N1 — def > 0 in char 2.** *Would be consumed by* `hK`'s conclusion on its def > 0 domain (the bridge's card conjunct is `6(|V|−1) − def₃`, so S1 transfers verbatim); needs a named habitat population with def > 0.
- **N2 — a uniform statement.** *Would be consumed by* `hK`'s conclusion on *all* tight shapes; per-shape hits do not give it. Only via a route (R2 or Part B), not by this probe.

## Where it breaks <!-- budget 10 -->
Nothing on the brief's route breaks: every census shape and every class of the cubic population hits in characteristic 2. What remains open is outside the probe's reach: (P) is per-shape, so the field range of `hK`'s conclusion on the *infinite* tight stratum is still undecided — no shape anywhere was found where char 2 fails, and no uniform argument exists. The concrete next attackable step, if the PI wants one, is N1: run S1 unchanged on a def > 0 habitat population (e.g. `flanks.py`'s named shapes, or a seeded draw of 2-edge-connected, no-proper-rigid-subgraph graphs with `def₃ > 0`), with target `6(|V|−1) − def₃`.

## Tried on this route, and what each rules out <!-- budget 10 -->
- `char2chart.py --sweep` (907 census, `GF(2^20)`, seed 20260923): 907 hits, 0 misses — rules out a char-2 obstruction to `hK`'s conclusion at any census shape.
- `char2chart.py --cubic` (seed 20260924): 1 967/1 967 classes — the same on the (GR-26) population (`n_hub ≤ 6`, `|Λ| ≤ 1` at 6).
- `--control --cap 907` (`GF(2^31−1)`, `GF(10007)`): 907/907 — rules out a transcription error that lowers rank in every characteristic.
- `blindaxes.py --imports --population` on the driver: fences 6 (Plücker indices) and 3 (selector slots), both structural; population comes from `grid.census_shapes` / `gisland.stratum`, imported unmodified.

## Next steps <!-- budget 5 -->
1. PI read S4 (2026-09-23) and chose **`/review-attack gr10` on S1–S4 before closing Part A**; N1 not commissioned.
2. If N1: pick a named def > 0 habitat population, add `--defpos` to the driver with target `6(|V|−1) − def₃`, land as S5.
3. Merge branch `attack-gr10` at the PI's milestone (worktree per `notes/attacks/README.md`).

## Worries <!-- budget 5 -->
- `def₃ = 0` is taken from `nogood_subdiv.deficiency` (count-matroid rank) plus the Nash-Williams–Tutte equivalence, not from the Lean `deficiency` directly; standard, but not re-derived here.
- The transcription of `pencilRow` is checked by rank controls and one reading of the Lean, not by a Lean evaluation; a sign-convention slip would not change rank, but a wrong slot/role assignment would — read against `PencilSeed.ofCoord` and `hubSlotNormal` twice in session 1 (role 0 = hub normal, fill slot `j` = role `j+1`); a Lean `#eval` cross-check would close this.
- The census and cubic populations are the corpus's own; neither contains a def > 0 shape.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (session 1: from "nothing attempted" to "the brief's route closes; open only beyond it")
- Open obligations: 0 (trend: 5 → 0 within session 1)
