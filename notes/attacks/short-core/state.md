# Attack short-core — state

Sessions so far: 5 · last session: 2026-10-30 · baseline HEAD: ab64d1e0 · review 1: 2026-10-30 (S25)

## Statement <!-- budget 10 -->
SHORT-CORE (brief §3, restated at review 1 on the PI's word) for the `Pᵈ` analogue of
`Graph.X0Attains.of_openEar_three` / `-four`, concluding `Graph.X0AttainsGrade K (d − 2) G` (on master, S39, S44).
Hypotheses: `hG`; the open ear on `V₁` (`hcover hinj hxV₁ ha hb hab hpath hsep`); `h₁`, `h₂` read in `Pᵈ`;
`ρ = relScrews a b` of `G[V₁]`. Conclusion: at general ear data, `W ⊇ star(y₁) + star(y₃)` implies `W = Λ²V`.
At a danger cell this is the step's conclusion itself: it fails exactly when `G` does not attain (S41).
- `k ≥ 4`: every `ρ`, every base datum, every `d` (S35).
- `k = 3`: base data general in S21's sense; at `d ≥ 5` also S31's and S33's factors. Every-`ρ` iff `κ < 7 − d` (S32).
Unused: `hG` (only S20's main-picture polynomial); the danger numbers outside S31's path-length step and S45.

## Current route and proof sketch <!-- budget 30 -->
**`d = 4`: claimed proved by hand (S1–S21), read by three readers (S12, S24, S25).** Also S35 (`k = 4, 5`) and
S31–S33 (`k = 3`).

**Secondary target, every `d`** (brief §6):
- `k ≥ 4`: S35. `k = 3`, `d ≤ 6`: S28–S33. Read by S38.
- `k = 3`, `d ≥ 7`: `κ = 0`, Case 2 (S31, S33); S40 reads `ρ` mod `H∧V`, S41 makes failure "`G` does not attain",
  S43 certifies 41 measured graphs. Session 5, at `d = 7` (failure there is `ω_H ∈ ρ°`, S34):
  - S45: a `Pᵈ`-optimal partition `P` of `F = G[V₁]` has motions constant on parts, `F/P` independent, every cycle of
    `F/P` at least `D` long, `a`, `b` in different parts; `ρ` is additive over cut vertices; bridge hinges lie in `ρ`.
  - S46: an `a`–`b` bridge with full `P²` freedom on both sides closes the cell; seven bridges in series suffice;
    so every cell whose `F/P` route is a tree path is closed (`G[V₁]` a path included).
  - S47 (run lemma): moving a free base point (degree-2 body, neighbours of degree 2, off `N[a] ∪ N[b]`) with the
    tangent lemma, the stress resolving `ω_H` has `t_i b_{v_{i−1}} − t_{i+1} b_{v_{i+1}}` in its radical for every
    motion; on a run whose points span `V` and with no coloop (`t_e ≡ 0`), the stress is 0 there. A cut of such runs
    closes the cell.
  - S48: `G[V₁]` a cycle (T3's first family) is closed at every length, the no-coloop step by `path_span.py`.

Open obligations (2 by piece), each consumed by the `Pᵈ` step's `hins` at `k = 3` (PD-STEPS, brief §6):
- **G1a** `d = 7`: the cells with no `a`–`b` cut of S46 bridges or S47 runs. Known members: the thetas (`th4`, `k4`,
  `same`, `hub`: runs exist, no-coloop unchecked); necklaces and Case-2 parts without free bodies.
- **G1b** `d ≥ 8`: `ρ` onto `Λ²Ē` (S34, S40). S46 needs `C(d − 5, 2)` independent bridge wedges; S47's identity
  gains a term `⟨ω_H∧η̇, S_b − S_a⟩` (the load `ω_H∧η` moves with the curve) unless `S_b − S_a ∈ H∧V`.

## Where it breaks <!-- budget 10 -->
`d = 7`, the no-coloop hypothesis of S47 (ii) on a run that lies on a cycle of `F/P`. For a run edge `e = uv`, S45's
rank count gives `r_e = dim ρ(F/P − e; u, v) ∈ {D − 1, D}`, and `e` is a coloop exactly when `r_e = D − 1`, i.e. when
`F − e` leaves `u`, `v` a hyperplane of relative screws missing `b_u∧b_v`. S48 settled it when the cycle minus `e` is
a path of at least 28 edges on general points; on a theta it is `span(P₁ − e) + (U₂ ∩ U₃) = Λ²V`, with `U_j` the
span of path `j`'s hinges and points near the hubs constrained to `Π_a`, `Π_b`. Separately, a 2-edge-connected route
whose parts have no free body (necklaces with short paths, larger rigid parts) has no run at all: there the moving
data must be heights inside a part (`δΛ ∈ Z_{ab}⊗E`), for which S47's identity is not yet derived.

## Tried on this route, and what each rules out <!-- budget 10 -->
- The every-`ρ` form at `k = 3`, `κ ≥ 7 − d` (S2, S5, S26): `ρ = H∧V` refutes it. S32 shows that this is the
  only obstruction to the ear-data curves; S47 therefore moves base data instead.
- S36 (i) as the closing route (S43): its necessary condition for failure holds at most certified cells.
- Special height subspaces (cone `x₂` off a hyperplane, `Λ̄` supported on the ear): `F` drops below target
  (`f_{d−1} > f_d`). So a certificate for S41 (b) cannot come from those.
- Requiring `Y_v` two-dimensional in S47 (i) (both stars at `v`'s neighbours inside `ρ(F − v)`): unnecessary;
  one motion with every `t_i ≠ 0` suffices (S47 (ii)).

## Next steps <!-- budget 5 -->
1. No-coloop on theta runs: show `r_e = D` for an edge in the middle of a path of length at least 10 on a theta
   with `Σℓ ≥ 66`, by a uniform certificate (S45's rank count reduces it to one rank at one configuration per shape).
2. Necklaces: S47 on the connecting paths when they carry six or more free bodies; else derive S47 (i) for height
   moves `ḃ_v = δλ_X(q̂_v)·m` inside a part.
3. G1b: the run lemma restricted to motions with `S_b − S_a ∈ H∧V`.

## Worries <!-- budget 5 -->
- S45–S48 have one reader (S49, all confirmed); S35, S40, S41 one each. A review is due (sessions 3–5).
- S41 (a) changes brief §6's reading: a counterexample refutes `def:pencil-d-x0-attains` at `G`, not only the
  coverage. That is the PI's to rule on.
- S47's "free" excludes `N[a] ∪ N[b]`; at a single-neighbour `a` the plane `Π_a` is base data (S9), not a point span.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (from "`Ψ ≠ 0` on `M` at Case 2" to S47's no-coloop step)
- Open obligations: 2 by piece (G1a, G1b; G1 counted them as one at sessions 3–4): flat over sessions 3–5
