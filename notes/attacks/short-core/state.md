# Attack short-core — state

Sessions so far: 2 · last session: 2026-10-30 · baseline HEAD: 3b6dd7e9

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3), for the `P⁴` analogue of `Graph.X0Attains.of_openEar_three` / `-four` (`k = 5` has
no `P³` model). `d = 4`, `V = K⁵`, `3 ≤ k ≤ 5`. Hypotheses: `hG`; the open ear on `V₁` (`hcover hinj hxV₁
ha hb hab hpath hsep`, edge `ab` allowed); `h₁`, `h₂` read in `P⁴`; `ρ = relScrews a b` of `G[V₁]`.
Conclusion: at general ear data, `W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`. It differs from the brief
in two ways. (1) `ρ` is the actual relative-screw space, because the every-`ρ` form is false (S2).
(2) The base data are general (S21: (P) `p_a ∦ p_b`, and (B) `la ≠ lb` or `ρ ⊆ Λ²Π_a`), not every attaining
datum; the step's own choice of base data meets this. Unused hypotheses:
- `hG`: it enters only S20's main-picture polynomial.
- the danger numbers: S20 proves the implication at every base datum with (P) and (B).

## Current route and proof sketch <!-- budget 30 -->
**`d = 4`: claimed proved by hand (S1–S21).** S14–S16 were read independently and confirmed (S24); S19–S21
were not. Annihilator form first (S1), then per cell:
- `k = 4, 5`: tangent lemma, every `ρ`, every `κ` (S7, S8; read independently in S12).
- `k = 3`, `κ ≤ 2`: tangent lemma, every `ρ` (S6, existence corrected in S12).
- `k = 3`, `κ = 3`: at general base data `ρ ⊆ Λ²Π_a`, so `dim W ≤ 3` (S16).
  - `κ = 3` forces `a`, `b` to be relatively rigid in the `P²` framework (S9).
  - The project's 2D rank theorem (`finrank_span_rigidityRows_of_isGenericNormals`, `n = 2`; S15) holds
    at `G[V₁] + ab`. With it, a partition argument gives a connected rigid `X ∋ a, b` (S14).
  - `X`'s points lie in `Π`.
- The step (S20): `of_openEar_splitOff` at `D = 10`.
  - The ear rank formula and the deficiency bounds are stated at every grade (S19 (a), (b)).
  - The insertion is proved by hand in `Λ²K⁵` (S19 (c)).
  - `hins` is restricted to base data with (P) and (B), which the base data supply (S21).
- Controls: `p2_path.py` (S17); `t3_kappa.py` (S18: no T3 danger cell has `κ = 3`).
- Formal ports are PD-STATE's and PD-STEPS': the `P⁴` carrier, `earConfig`, the grade-3 polynomial
  lemmas, and S15 on a subtype.

**Secondary target: every `d`, `3 ≤ k ≤ C(d − 1, 2) + 2`.** S22: at `k = 3`, S6's curves force
`ker M ⊆ p̄_a∧p̄_b∧Λ^{d−5}Q`. S23: in SHORT's range at `d = 5`, T3's cells all have `κ = 0`.

Open obligations (3, all of the secondary target):
- **G1** `k = 3`, `κ ≤ 2`, `d ≥ 5`. At `d = 5` a third curve closes `κ = 0` (S22, a sketch); `κ = 1, 2`
  remain.
- **G2** `4 ≤ k ≤ C(d − 1, 2) + 2`, `d ≥ 5`: S7 and S8's curves through S22's divisibility.
- **G3** `κ = 3` at every `d`: S9 with `d − 2` heights (`κ = 3 − min(d − 2, dim ρ⁽²⁾)`), then S14–S16.

Each is consumed by the `Pᵈ` step's `hins` at `d ≥ 5` (PD-STEPS, brief §6's every-`d` tier).

## Where it breaks <!-- budget 10 -->
At `d = 4`, nowhere known: the break is now the review of S14–S21. The first open step of the
secondary target is `d = 5`, `k = 3`, `κ = 2`. S22 leaves `y₁∧y₃∧p_a∧p_b ∈ R` at a failing datum. The
third curve `(y₁ + tu, y₃)`, `u ∈ Π_a`, then needs `Π_a ∩ ⟨y₃, p_b⟩ = 0`. That fails at `κ = 2`, where
every 2-plane `⟨y₃, p_b⟩ ⊂ Π_b` meets the 2-plane `Π_a ∩ Π_b`. The candidates are a curve moving
`y₃` off `p_b`'s plane, or `ρ`'s provenance as in S16, which `κ = 2` at `d = 5` may also force
(`dim ρ⁽²⁾ = 1`). T3 holds no such cell in range (S23).

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `κ = 3`, `k = 3` (S2, S5). It rules out `ρ = Π∧V`, and any `ρ` with
  `ρ + Λ²Π = Π∧V`. This is why `hins` at `k = 3` takes (B) (S20).
- The tangent lemma alone at `κ = 3`, `k = 3`: retired to `log.md`. S16 closes the cell instead.

## Next steps <!-- budget 5 -->
1. `/review-attack` on S19–S21, with S14–S16 already read (S24). It is a milestone: `d = 4` is claimed
   proved. Then the PI rules on the statement change (general base data).
2. G1 at `d = 5`: write the third curve as a result, then attack `κ = 1, 2` at `k = 3`.
3. G2 at `d = 5`, `k = 4`: S7's curves read through S22. Check them on T3's `d = 5` cells.

## Worries <!-- budget 5 -->
- S9, S16 and S21 read the `P⁴` configuration (closed neighbourhoods span ≤ 3, `L = L₁²`) from the brief
  and Strata Result 13, not from a Lean carrier. If PD-STATE's carrier differs, they must be re-derived.
- S15's citation needs `V(G) = Set.univ`, but `G[V₁] + ab` lives on a subtype. The transport is believed
  routine (S24 lists this and two smaller formal costs).
- The brief's every-attaining-datum form is open and unused; a consumer fixing base data would need it.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (it moved from O3(3,3), closed by S16, to G1)
- Open obligations: 3 (`d = 4`'s six fell to 0 this session; the three are the secondary target's, new)
