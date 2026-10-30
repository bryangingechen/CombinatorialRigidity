# Attack nondeg — state

Sessions so far: 2 · last session: 2026-10-30 · baseline HEAD: 5c9948e2

## Statement <!-- budget 10 -->
C2-same is the definition (the PI's word after session 1, brief header): N1, N3 on `b`, and
`dim ⋂_{w∈S} Π_w ≤ 4 − |S|` for `S ⊆ H[v]`, `|S| ≥ 2`. Target: the `Pᵈ` form of `PencilPair`'s first
conjunct, `G.Simple → PencilNondegFeasible K G → Generic_d(G)` (S9 makes the antecedent Phase 39's),
via the motive `RL_d(G)` (S18 (iv)), which implies it; producer at `d = 3`: `hasGenericPencilRealization_of_IH`.
Consumer diff re-run at `5c9948e2` (workbook, session-2 preamble): no mismatch. Unused: `X0Gen`'s
`hV`, `htec` only select the reduction's case (S26); `[Infinite K]` enters through general choices.

## Current route and proof sketch <!-- budget 30 -->
The carrier is the lift family over `𝒩(G)`, the C2-same realizations in dimension 3, irreducible by
the steer (S18 (i)); a lift `R(r⁰, λ)`, `λ ∈ L¹(r⁰)^{d−3}`, is always C2-same (S18 (ii)).
`RL_d(G)`: a general lift of a general `r⁰` has rank `t_d(G)`. `RL_3` holds everywhere (S18 (iv));
one witness at a point of least `dim L̃` suffices (S18 (v)). Transfer to a subgraph: S19.
The reduction (S26), strong induction on `|V|`, `pencilPair_of_IH`'s case split:
- ≤ 2 bodies, triangle, disconnected: S20. Cut edge: S21. Pendant body: S22. Pendant triangle: S23.
- Good ear `x` (ends `a, b`): lifts of `G` = `ker μ` in `H = G − x`'s (S24 (3)); free when
  `μ = 0`, then `RL_d(H) ⟹ RL_d(G)` (S24 (4)); every E2 ear is free (S24 (5)).
- At the lemma's own ear (`x, a, b` in a minimal planar-rigid `W₀`, `X = W₀ − x`), `μ` reads only
  `X`, and vanishes under (W): `X`'s restriction lifts only trivially (S29). Outside bodies meet
  `W₀` in ≤ 2 hubs (S31).
- No planar-rigid set: from (A), the coverage in dimension `d` (S25).
- Outer step: `RL_{d′} ⟹ RL_d` where `def_{d′} = def_d` (S27), so a costly ear matters only at
  `def_{d−1} > def_d` ((B′)).
Certified (S30): (W) at every `W₀`-ear of every case-(ii) graph on ≤ 9 bodies (478 ears, 188 graphs,
exact draws); so `Generic_d` holds on ≤ 9 bodies at every `d ≥ 4`, given (A) there.
Open obligations (O6b closed: S20–S23, S26; O6a narrowed to O7):
- **O7 — (W) in general.** At a general `r⁰ ∈ 𝒩(G)`, `dim L¹_{G[X]}(r⁰|_X) = 4` for the
  good-ear lemma's `W₀`-ear. Consumer: case (ii) of `hasGenericPencilRealization_of_IH`, the
  one-ear branch (`Graph.IsOpenEar.hasGenericPencilRealization_of_one`), in `Pᵈ`.
Dependency, not this track's: (A), the coverage at graphs with no planar-rigid set (42d's bare and
distinct main component), consumed by case (i) of the same producer.

## Where it breaks <!-- budget 10 -->
(W), O7: why the restriction of a general nondegenerate `P³` realization of `G` to `X = W₀ − x`
should be general for `G[X]` (only trivial lifts; picture form `dim L_{G[X]}(q₀|_X) = 4 =
3 + def_2(G[X])`). `G[X]` is planar-tight with one non-trivial lift `z*` at a general picture, and
the one constraint `W₀` itself imposes (`q_x` on the line where `Π_a`, `Π_b` meet) is free of `X`.
The step to prove: a realization of `G[W₀]` general for `G[X]`, `x` on that line, extends to a
nondegenerate realization of `G`. S31 shows the outside meets `W₀` only at ≤ 2 hub planes per body,
so each single nondegeneracy condition is local; the gap is that outside planar-rigid sets sharing
hubs with `W₀` need special pictures (S10) that could drag `X`'s along. Attack: reduce to "each
nondegeneracy condition of `G` holds somewhere on the relative steer family over the general
`G[W₀]` realization" (irreducible, so they then hold together), condition by condition.

## Tried on this route, and what each rules out <!-- budget 10 -->
- The bare `Generic_d` motive: too weak for the arms (`log.md`, S15); `RL_d` replaces it.
- An arbitrary good ear: 40 costly at their draws, none a `W₀`-ear (`log.md`, S30).
- C2-gp, the direct transcription, C1 as the definition: retired in session 1 (`log.md`).

## Next steps <!-- budget 5 -->
1. The PI's answer to the report's question (who proves (W)). 2. If NONDEG: the condition-by-condition
extension of "Where it breaks"; first the C2 conditions at hubs shared by `W₀` and an outside
planar-rigid set. 3. A counterexample hunt beyond nine bodies, aimed at two minimal planar-rigid
sets sharing hubs (`oneear.py` with a structured or seeded population). Review 1 is due after session 3.

## Worries <!-- budget 5 -->
- One reader for S9, S13–S14 (session 1) and S18–S31 (this session); S18 (i)'s steer reading at
  non-hubs with `|N[v]| ≤ 2` and S21's reuse of the `P³` cut arm for every pair are readings.
- S30's certificates are exact, but S26's consequence leans on the arms and on (A) at every size.
- Intermediate `f_d` were not examined (session 1); moot under the PI's choice.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0
- Open obligations: 1 (O7; 2 at the session's start, 6 at session 1's; falling)
