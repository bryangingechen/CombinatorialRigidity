# Attack short-core — state

Sessions so far: 4 · last session: 2026-10-30 · baseline HEAD: 3c55436e · review 1: 2026-10-30 (S25)

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3, restated at review 1 on the PI's word) for the `Pᵈ` analogue of
`Graph.X0Attains.of_openEar_three` / `-four`, concluding `Graph.X0AttainsGrade K (d − 2) G` (on master, S39).
Hypotheses: `hG`; the open ear on `V₁` (`hcover hinj hxV₁ ha hb hab hpath hsep`); `h₁`, `h₂` read in `Pᵈ`;
`ρ = relScrews a b` of `G[V₁]`. Conclusion: at general ear data, `W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`.
At a danger cell this is the step's conclusion itself: it fails exactly when `G` does not attain (S41).
- `k ≥ 4`: every `ρ`, every base datum, every `d` (S35).
- `k = 3`: base data general in S21's sense; at `d ≥ 5` also S31's and S33's factors. Every-`ρ` iff `κ < 7 − d` (S32).
Unused: `hG` (only S20's main-picture polynomial); the danger numbers outside S31's path-length step.

## Current route and proof sketch <!-- budget 30 -->
**`d = 4`: claimed proved by hand (S1–S21), read by three readers (S12, S24, S25).** Also S35 (`k = 4, 5`) and
S31–S33 (`k = 3`).

**Secondary target, every `d`** (brief §6):
- `k ≥ 4`: S35 (curves moving the free point `y₃`). `k = 3`, `d ≤ 6`: S28–S33. Read by S38.
- `k = 3`, `d ≥ 7`: every danger cell has `κ = 0` and is in Case 2 (S31, S33); every `ρ`-agnostic argument
  fails there (S26, S32). Session 4:
  - S40: Case 2's quotient `Q = F/P*` is simple with connected parts, `Pᵈ` motions are constant on parts, and
    every point of `N[X]` lies in `Π_X = graph(Λ_X)`. With `θ : V → Ē = V/H` (dimension `d − 5`), the image of
    `ρ` in `Λ²(V/H)` is `Ψ(M)`: `M = Λ²P(Z_d(F))` (dimension `3 + f`) and
    `Ψ(μ) = Σ_path Λ²Λ̄_X(μ_X − μ_{X'})`, `Λ̄ ∈ Z_{ab}(Q) ⊗ Ē` the pinned part of the heights.
  - S41: at a danger cell, failure ⟺ `G` does not attain; one configuration of `G` at a main picture
    at target certifies a cell (`lem:pencil-d-x0-one-witness`).
  - S42: a fresh reader CONFIRMED S36, S40, S41, with four repairs made in place.
  - S43 (`d7_short.py`): every measured `k = 3` danger cell is certified, so 41 graphs are proved cells: 26
    at `d = 7` (6 of them diamond necklaces) and 15 at `d = 8`. `ρ` maps onto `Λ²(V/H)` at all 41, while
    S36 (i)'s failure condition holds at 20 of the 26 at `d = 7`.

Open obligation (1), consumed by the `Pᵈ` step's `hins` at `k = 3` (PD-STEPS, brief §6):
- **G1** `k = 3`, `d ≥ 7`, `κ = 0`, Case 2: `Ψ(M) = Λ²Ē` (S34 with S40); at `d = 7`, `Ψ ≠ 0` on `M`.

## Where it breaks <!-- budget 10 -->
`k = 3`, `d ≥ 7`, `κ = 0`, Case 2. The open step (S40): a `P²` motion `μ` of `Q` that lifts to `Pᵈ`, i.e.
`Σ_C ±t_e(μ) b_u∧b_v = 0` in `E∧V` on every cycle `C` of `Q`, with `Ψ(μ) ≠ 0` (at `d = 7`; at `d ≥ 8`, enough
such `μ` to fill `Λ²Ē`). The cycle conditions split by order in `Λ̄` into the `P⁵` condition, a part
linear in `Λ̄` (`H⊗Ē`), and a quadratic part (`Λ²Ē`) whose path form is `Ψ`. In `Q/ab` that path closes
into a cycle, and `Ψ` is its quadratic condition. S36 (i)'s alternative is out (S43, `log.md`).
Equivalently (S41), `G` attains. Measured (S43) only on subdivided cores and diamond necklaces.

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `k = 3`, `κ ≥ 7 − d` (S2, S5, S26): `ρ = H∧V` refutes it. S32 shows that this is the
  only obstruction to the ear-data curves.
- S36 (i) as the closing route (S43): its necessary condition for failure holds at most certified cells.
- Special height subspaces (cone `x₂` off a hyperplane, `Λ̄` supported on the ear): `F` drops below target
  (`f_{d−1} > f_d`). So a certificate for S41 (b) cannot come from those.

## Next steps <!-- budget 5 -->
1. Base-data curves: a chain of free degree-2 bodies far from `a`, `b` can move with `H` fixed. Apply S6's
   tangent lemma to the flow form of `ω_H ∈ R` ("`ω_H` routed `a → b` by edge forms killing the hinges"), as
   S35 did with the free ear point `y₃`; aim `Ψ ≠ 0` at `d = 7` when an a–b route has a free stretch.
2. S43 with richer Case-2 parts (cores whose parts are larger rigid blocks): a cell below target, certified,
   would be a counterexample to `def:pencil-d-x0-attains` (S41 (a)).

## Worries <!-- budget 5 -->
- S41 (a) changes brief §6's reading: a counterexample refutes `def:pencil-d-x0-attains` at `G`, not only
  the coverage. That is the PI's to rule on.
- S43's population: Case-2 parts are single bodies or diamonds. S35 and S40–S41 each have one reader.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 1 (same cell as session 3; S40 restates the step as `Ψ(M) = Λ²Ē`)
- Open obligations: 1 (trend: 6 → 3 → 3 → 1 → 1 over sessions 1–4; flat this session, G1 unchanged)
