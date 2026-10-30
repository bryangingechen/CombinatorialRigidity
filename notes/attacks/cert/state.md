# Attack cert — state

Sessions so far: 1 · last session: 2026-10-30 · baseline HEAD: 97a631ba · reviews: none yet

## Statement <!-- budget 10 -->
CERT (brief §3), unchanged: for `d ≥ 3`, `D = C(d+1,2)`, every infinite `K`: (C1) a closed `m`-gon of affine
points with independent joins, `3 ≤ m ≤ D`; (C2) `p_a, p₁..p_{D−1}, p_b` affine, height zero at `p_a, p₁, p_{D−1},
p_b`, the `D` joins independent; (C3) the same for `3 ≤ k ≤ D − 2`, `k + 1` joins. Consumers, read at `97a631ba`
with no mismatch against brief §1: `Graph.X0Attains.of_cycle_of_certificate` (`hli`, `hcard`) and
`Graph.X0Attains.of_openEar_of_cert` (`hcert`, `hzs` via `Graph.mem_liftingSpace_of_ear`, `hcount`), in `Pᵈ`
through `pencilConfigPointGrade`. Proved (S6) over every field with `|K| ≥ 4`, a superset of the infinite fields.
Unused: `hG`, `hcover`, `hpath`, `hsep`, `h₁` (the graph enters only through which links carry joins);
`hcount`'s deficiencies (they fix `n`, not the points); `[Infinite K]` beyond `|K| ≥ 4`.

## Current route and proof sketch <!-- budget 30 -->
R1 (brief §5), every step claimed proved by hand this session, each by its author only (no second reader yet):
- R1 (i) = S1: three consecutive vertices of a good polygon are independent. Any field.
- R1 (ii) = S2: (a) an affine good polygon, by an affine map (`λ ∘ g = λ`), gets any three consecutive vertices
  at `P₁, P₀, P₂` and stays affine, any field; (b) R1 (ii) as the brief states it (openness), infinite `K`.
  The route uses (a) only, because S5 keeps every polygon affine.
- R1 (iii) = S3: an affine good closed `(k+1)`-gon gives the open ear with `p_a = p_b = P₀`, `p₁ = P₂`,
  `p_k = P₁`. Consumer reading in S3: `a ≠ b` bodies at one point, as `of_openEar` does at `d = 3`.
- R1 (iv) = S4 + S5: some vertex `Y_i` and `u` in {vertices} ∪ {standard basis} have `Y_i∧u ∉ W` (S4); the
  insertion `Y_i, (Y_i + tu)/(1 + tλ(u)), Y_{i+1}` is good off at most three values of `t` (S5).
- S6 assembles (C1)–(C3) and the flat ear `k = 2` by induction from `P₀P₁P₂`, every field with `|K| ≥ 4`.
- S7: the collapsing placements (`m > D` cycles, `k ≥ D − 1` ears), Phase 40's at `d = 3`.
- S8: the exact driver, `d = 3..9`, every `m`, `k`, collapses at `m = D+1, D+3`, `k = D, D+2`; all pass.
- S9: G1's revival trigger ("CERT's open ears fail at some `d ≥ 7`") cannot fire.
Open obligations: none. O1–O6 of the session-1 opening are S1, S2 (a), S3, S4–S6, S7, S8.

## Where it breaks <!-- budget 10 -->
Nowhere found: every step of R1 went through, and S8 controls it over `ℚ` at `d ≤ 9`. If a reader finds a gap, the
places to look first are S5's "one row affine in `t`" (the minor's degree in `t`), S4's `S ≠ V` case (that `Y_i∧u`
is a new basis vector of `Λ²V`), and S3's consumer reading (heights zero on all of `V₁ ∪ {x₁, x_k}` with
`a, b` at one point). R2's integer certificates over every field are not attempted (secondary, PI's word only).

## Tried on this route, and what each rules out <!-- budget 10 -->
- R1 (ii) by openness (S2 (b)): holds over infinite `K`, but not needed; S2 (a) replaces it at every field.

## Next steps <!-- budget 5 -->
Stop for the PI (brief §6): S9's verdict on G1, and whether CERT closes now or after a `/review-attack` reading of
S1–S7. If the PI asks, R2 (integer certificates, unit Smith form at every `d`) is the secondary target; S8 reports
`cert_top` unimodular at `d = 7, 8, 9`.

## Worries <!-- budget 5 -->
- S1–S7 are one session's hand proofs with no second reader; R1 was the brief writer's sketch, read by no one else.
- S9's "what it leaves" is read from SHORT-CORE's S56 text, not re-derived.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (changed this session: from "not yet attempted" to "nowhere found")
- Open obligations: 0 (6 → 0 in session 1; no three-session trend yet)
