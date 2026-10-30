# Attack short-core — state

Sessions so far: 3 · last session: 2026-10-30 · baseline HEAD: e27569d0 · review 1: 2026-10-30 (S25)

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3, restated at review 1 on the PI's word) for the `Pᵈ` analogue of
`Graph.X0Attains.of_openEar_three` / `-four`, concluding `def:pencil-d-x0-attains` (S27: carrier unchanged).
Hypotheses: `hG`; the open ear on `V₁` (`hcover hinj hxV₁ ha hb hab hpath hsep`); `h₁`, `h₂` read in `Pᵈ`;
`ρ = relScrews a b` of `G[V₁]`. Conclusion: at general ear data, `W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`.
- `k ≥ 4`: every `ρ`, every base datum, every `d` (S35). No base-data condition.
- `k = 3`: base data general in S21's sense ((P), (B)); at `d ≥ 5` also `q'` off S28's polynomial (S31) and
  the heights off S33's minor of `la − lb`. The step's own choice meets all. Every-`ρ` iff `κ < 7 − d` (S32).
Unused: `hG` (only S20's main-picture polynomial); the danger numbers outside S31's path-length step.

## Current route and proof sketch <!-- budget 30 -->
**`d = 4`: claimed proved by hand (S1–S21), read by three readers (S12, S24, S25).** Session 3 adds a
second, shorter `d = 4` proof: S35 for `k = 4, 5`, and S31 with S32 for `k = 3`.

**Secondary target, every `d`** (brief §6), session 3:
- `k ≥ 4`: S35. Curves moving the free point `y₃`, first along `y₄`, then in every direction, leave `ζ̄`
  annihilated by all of `Q`, impossible in degree `d − 3`. Closes G2 and transcribes the every-`ρ` `hins`.
- `k = 3`, the actual `ρ`: S28 (the `P²` framework with `a, b` glued attains `3 + def(F/ab)`), S29 (Case 1:
  `a, b` joined inside a glued part; Case 2: `r = 3`, `Z(F)` constant on an optimal partition separating
  them), S30 (Case 1: `Λ²P` injective on `ρ`, `dim ρ ≤ r ≤ 3`). S31: a danger cell at `k ≤ 2d − 4` has
  `r = 3`, at `k ≤ 2d − 5` Case 2. Closes G3 and G1 at `r ≤ 2`, every `d`.
- `k = 3`, every `ρ`: S32 (Koszul form of S6/S22: curves `C_u`, `D_w` give `x̄∧ζ̄ = 0` on `H/⟨y₁,y₃⟩`, of
  dimension `4 − κ`). With S33's lemma (`κ = 3 − min(d − 2, r)`, via `G''`), `k = 3` closes at `d ≤ 6`.
- Controls: `rho_bound.py` for S28–S31 (S37, at `n ≤ 9`, where `ρ` is bridge hinges only); a fresh
  reader CONFIRMED S28–S35, with one gap in S33's base data, repaired (S38).

Open obligation (1), consumed by the `Pᵈ` step's `hins` at `k = 3` (PD-STEPS, brief §6):
- **G1** `k = 3`, `d ≥ 7`, `r = 3`, `κ = 0`, Case 2. By S34 and S36, failure needs: `ρ` not onto `Λ²(V/H)`;
  `ρ ∩ H∧V + Λ²H = H∧V`; `dim ρ ≥ 6(d − 5)`; `def₂(G[V₁]) ≥ 6(d − 5)`.

## Where it breaks <!-- budget 10 -->
`k = 3`, `d ≥ 7`, `κ = 0` (`H = Π_a ⊕ Π_b`, `U = V/H` of dimension `d − 5`), Case 2: every `P²` motion and
every `Pᵈ` motion is constant on `C_a ∋ a` and on `C_b ∋ b`, and every hinge at `C_a` lies in `Λ²Π_a`.
The open step: show that `ρ` maps onto `Λ²U` (S34), or that `ρ ∩ H∧V` does not map onto `H ⊗ U` (S36 (i)).
At `d = 7` this reads: `ρ ⊄ H∧V`, or `ρ ∩ H∧V + Λ²H ≠ H∧V`. Every `ρ`-agnostic argument fails here (S26).
Whether `d = 7`, `k = 3` danger cells exist is unmeasured (T3 stops at `d = 5`).

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `k = 3`, `κ ≥ 7 − d` (S2, S5, S26): `ρ = H∧V` refutes it, so `d ≥ 7` needs the
  actual `ρ`. S32 shows it is the only obstruction to the curve method.
- `Λ²P(ρ) ⊆ ρ⁽²⁾` alone (S26 (ii)) at `d = 5`, `r = 1`: the 12-dimensional `Λ²L + E∧H + e₀∧V` meets it and
  fails; S30's injectivity is what closed the cell (`log.md`).

## Next steps <!-- budget 5 -->
1. Existence at `d = 7`, `k = 3`: build a Case-2 graph with `def₂(G[V₁]) ≥ 12` and measure `ρ` against
   `H∧V` exactly, or exclude it (a theta or a necklace, S36's numbers).
2. Case 2's structure: the hinges at `C_a` lie in `Λ²Π_a`; ask whether `ρ` reaches `Λ²U` through the
   middle parts' hinges.

## Worries <!-- budget 5 -->
- S35 is the strongest claim of the session; one reader (S38) and its targeted search. S36 is unread.
- S37 does not stress S30's mechanism: at `n ≤ 9` every Case-1 `ρ` is spanned by bridge hinges.
- S28 needs no common neighbour of `a, b`; S31 gets it only at danger cells with `k ≤ 2d − 4`.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (moved from `d = 5`, `k = 3`, `r = 1` to `d ≥ 7`, `k = 3`, `κ = 0`)
- Open obligations: 1 (trend: 6 → 3 → 3 → 1 over sessions 1–3; G2 by S35, G3 and G1 at `r ≤ 2`, `d ≤ 6` by S31–S33)
