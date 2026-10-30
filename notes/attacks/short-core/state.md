# Attack short-core — state

Sessions so far: 1 · last session: 2026-10-29 · baseline HEAD: a7bbb96c

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3), for the `P⁴` analogue of `Graph.X0Attains.of_openEar_three` / `-four`
(`k = 5` has no `P³` model). `d = 4`, `V = K⁵`. Hypotheses: `hG` (`IsX0Graph`); the open ear on `V₁`,
`3 ≤ k ≤ 5` (`hcover hinj hxV₁ ha hb hab hpath hsep`, edge `ab` allowed); base data where `G[V₁]`
(`h₁`) and `G'' = G.splitOff x₂ x₁ x₃` (`h₂`) attain; `ρ = relScrews a b` of `G[V₁]`; the danger
numbers `f > def(G) = def(G'')` and `7 ≤ dim W ≤ 9`. Conclusion: at general ear data,
`W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`.
Changed from the brief (corrected with the PI's authorization): `ρ` is the actual relative-screw space,
because the every-`ρ` form is false at `k = 3` (S2). Unused hypotheses:
- `hG`: it enters only through O1 (the main picture polynomial).
- `h₂` and the danger numbers: unused by S6–S8, which hold for every `ρ`. S11 uses only `dim ρ`.

## Current route and proof sketch <!-- budget 30 -->
Annihilator route. With `R = ρ°` and `T(y) = y₁∧y₃∧V`, failure at `y` is `0 ≠ R ∩ J(y)° ⊆ T(y)` (S1).
- **Tangent lemma (S6).** Move one ear point along a line that keeps the joins' annihilator. Off a
  nonzero polynomial in the ear data, SHORT-CORE then holds for every subspace `ρ` in three places:
  - `k = 3` with `κ = dim(Π_a ∩ Π_b) ≤ 2` (S6, existence corrected in S12);
  - `k = 4` at every `κ` (S7);
  - `k = 5` at every `κ` (S8).
  An independent reader checked these (S12), and the exact controls are `drivers/tangent_check.py`
  and `drivers/adversarial_rho.py`.
- **The one remaining cell, `κ = 3`, `k = 3`.**
  - S9: `κ = 3` iff `a` and `b` are relatively rigid in the `P²` point-join (pin-collinear) framework
    of `G[V₁]` at the picture.
  - S10: then `ρ ⊆ E∧V`, where `E` is the span of the height directions.
  - S11: failure is exactly `ρ = Π∧E` (dimension 6). If the `P²` rigid class `H` of `a` holds an
    a–b path, then `ρ = 0` and the cell is not a danger cell.
- S3: a danger cell has `dist_{G[V₁]}(a,b) ≥ 7 − k`, so `a ≁ b`. O2, the domain, is closed.

Open obligations (6):
- **O1** the reduction in `P⁴`. Consumed because the `P⁴` step concludes `G.X0Attains` through an
  amended `of_openEar_splitOff`.
  - O1a: the ear rank formula at `D = 10` (`finrank_span_rigidityRows_ear_eq`, stated at every `d`).
  - O1b: the deficiency bounds at `D = 10` (`splitOff_deficiency_le_of_eq_left`,
    `deficiency_induce_add_le_of_ear`).
  - O1c: the insertion in `Λ²K⁵` (`exists_insertion_gain`, whose argument is free of the dimension).
  - O1d: the polynomial family. Its `hins` may stay every-`ρ` at `k = 4, 5` (S7, S8) but must name the
    actual `ρ` at `k = 3` (S2).
- **O3(3,3)** the crux at `κ = 3`, `k = 3`. Consumed because `hins` at `k = 3` must hold at every base
  datum the step produces, including `Π_a = Π_b`.
- **O4** genericity, joint over base and ear data, including the choice of `Π_a` when `a` has a single
  neighbour in `V₁` (S9). Consumed by `hins`'s `∃ Q ≠ 0` and by `exists_earBase_splitOff`'s choices.

## Where it breaks <!-- budget 10 -->
O3(3,3), after S11. Let `a` and `b` be relatively rigid in the `P²` pin-collinear framework of `G[V₁]`
(the pin of `uv` is where the polars of `q_u` and `q_v` meet), and let
`H = {v : λ_v = λ_a for every P² motion λ}`, which holds `b`. The open step: show that `G[H]` holds an
a–b path, or otherwise that `ρ ≠ Π∧E` (6-dimensional, `R = Λ³Π ⊕ Π∧Λ²E`). For the generic
body-hinge count matroid with `D = 3`, rigid components are rigid induced subgraphs, which would give
the path. The missing input is that the `P²` pin-collinear framework at a general picture has that
matroid; the candidate source, unverified, is Jackson and Jordán (DCG 2008) on pin-collinear
frameworks. The project formalizes what it uses, so a citation alone does not close it.

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `κ = 3`, `k = 3` (S2, S5). Ruled out: `ρ = Π∧V`, or any `ρ` with
  `ρ + Λ²Π = Π∧V`, fails. So that cell needs the provenance of `ρ` (S9–S11).
- The tangent lemma at `κ = 3`, `k = 3` (S6 remark). It gives only `R ∩ T(y) ⊆ K·Λ³Π`, so it cannot
  close the cell by itself.

## Next steps <!-- budget 5 -->
1. O3(3,3): prove the path statement of "Where it breaks" directly for the `P²` framework, for
   instance from S9's lifting description, or find a citable theorem and its formalization cost.
2. A control for O3(3,3): which of T3's 72 cells at `d = 4` have `κ = 3`, if any.
3. O1d and O4: write the amended `hins` and its genericity as one statement, every-`ρ` at `k = 4, 5`.

## Worries <!-- budget 5 -->
- S9 reads the `P⁴` configuration (closed neighbourhoods span ≤ 3 dimensions) from the brief and
  Strata Result 13, not from a Lean carrier; PD-STATE has not laid one. If the carrier differs,
  S9–S11 must be re-derived.
- S3 reads "danger" at general ear data, as the brief does; not re-derived from Phase42-design §2.3.
- `adversarial_rho.py` does not guard its draws by S6–S8's independence conditions.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (first session)
- Open obligations: 6 (trend: first session, so no trend; 9 when the route was enumerated mid-session)
