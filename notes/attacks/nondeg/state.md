# Attack nondeg — state

Sessions so far: 3 · last session: 2026-10-30 · baseline HEAD: 92315252

## Statement <!-- budget 10 -->
C2-same is the definition (the PI's word after session 1, brief header): N1, N3 on `b`, and
`dim ⋂_{w∈S} Π_w ≤ 4 − |S|` for `S ⊆ H[v]`, `|S| ≥ 2`. Target: the `Pᵈ` form of `PencilPair`'s first
conjunct, `G.Simple → PencilNondegFeasible K G → Generic_d(G)` (S9 makes the antecedent Phase 39's),
via the motive `RL_d(G)` (S18 (iv)), which implies it; producer at `d = 3`: `hasGenericPencilRealization_of_IH`.
Consumer diff re-run at `92315252` (workbook, session-3 preamble): no mismatch. Unused: `X0Gen`'s
`hV`, `htec` only select the reduction's case (S26); `[Infinite K]` enters through general choices.

## Current route and proof sketch <!-- budget 30 -->
The carrier is the lift family over `𝒩(G)`, the C2-same realizations in dimension 3, irreducible by
the steer (S18 (i)); a lift `R(r⁰, λ)`, `λ ∈ L¹(r⁰)^{d−3}`, is always C2-same (S18 (ii)).
`RL_d(G)`: a general lift of a general `r⁰` has rank `t_d(G)`. `RL_3` holds everywhere (S18 (iv));
one witness at a point of least `dim L̃` suffices (S18 (v)). Transfer to a subgraph: S19.
The reduction (S26), strong induction on `|V|`, `pencilPair_of_IH`'s case split:
- ≤ 2 bodies, triangle, disconnected: S20. Cut edge: S21, with S32's `(T1)` (review 1's F2 repaired:
  the glue matches each side's far-end point, `E` = the C2 condition at `{u, v, w₁}`).
- Pendant body: S22. Pendant triangle: S23.
- No planar-rigid set: from (A), the coverage in dimension `d` (S25).
- Otherwise the good-ear lemma returning `W₀` (S33, O8) gives a pendant triangle or a `W₀`-ear
  `(W₀, x)`; its lifts are `ker μ` (S24), `μ` reads only `X = W₀ ∖ {x}` (S29), and (W) holds
  (S36, claimed): so the ear is free and `RL_d(G − x) ⟹ RL_d(G)` (S24 (4)). S26's (B) is never used.
(W)'s proof: push the steer family of `G` forward to the points of `X`. Its image closure `T` lies in
`P`, the closure of the points of `G[X]`'s own steer family (S35 (a)); a general point of the family
`S_L` that labels `X`'s hubs of `G` as hubs extends to a steer point of `G`, because an outside hub's
plane meets `X` in at most two points (S31, S35 (b)); `S_L` and `G[X]`'s family have one dimension,
as an extra label sits at a body of degree two in `G[X]`, and `S_L`'s planes are fixed by its points
(S34); so `T = P` (S35 (c)), and `P`'s general point is over a general picture
(`thm:pencil-x0-base-generic`'s proof with JJ's polynomial), where `dim L¹_X = 3 + def_2(G[X]) = 4` (S36).
Controls: (W) certified exactly at 6217 `W₀`-ears on 6–16 bodies, no collinear triple in `X` (S37).
Open obligations:
- **O8 — the good-ear lemma, returning `W₀`** (S33: statement; proof an assembly of S24 (1), S29 (1)
  and the lemma's proof). Consumed because the one-ear branch
  (`Graph.IsOpenEar.hasGenericPencilRealization_of_one` in `Pᵈ`) reads `X` and `W₀` from it, and
  `Graph.IsX0Graph.exists_oneEar_or_pendantTriangle` returns neither. A write-up deliverable
  (slice W10's red node), no new mathematics.
Closed this session (claimed, one reader): O7, (W), by S34–S36.
Dependency, not this track's: (A), the coverage at graphs with no planar-rigid set (42d's bare and
distinct main component), consumed by case (i) of the same producer.

## Where it breaks <!-- budget 10 -->
No step is known to fail; the route's last piece of new mathematics, (W), is claimed (S36). What a
reader should break first:
- S35 (b): an outside hub `u` with two points of `X`; that `n_u` can be chosen orthogonal to them while
  every `H_G[v]`, `v ∈ X`, keeps independent normals (cases `O_v = {u}` with `H_L[v] = {v, w}`, and
  `O_v = {u, u′}`; both reduce to a triangle with two hubs).
- S34's count `dim S_L = 3|X| − Σ_{w∈L}(deg w − 2)` and the finite fibre (Rado on `F_w, F_y, F_{y′}`).
- S36's reading of `thm:pencil-x0-base-generic`'s proof, with JJ's polynomial added (as S14's).
- S32: that the cross C2 conditions at `u` and `v` are the only ones reading both sides.

## Tried on this route, and what each rules out <!-- budget 10 -->
- The bare `Generic_d` motive: too weak for the arms (`log.md`, S15); `RL_d` replaces it.
- An arbitrary good ear: 40 costly at their draws, none a `W₀`-ear (`log.md`, S30).
- S21's `(T1)` with `E = 1` (`log.md`; S32 corrects it).
- Fixing a realization of `G[W₀]` and extending it (session 2's plan, review 1's caution): not
  needed; S35 pushes forward instead, so the relative family's irreducibility is never used.

## Next steps <!-- budget 5 -->
1. The PI's answer to the report's question: review 2 now on S32–S38, or session 4.
2. If the review confirms S32–S36: stop the track; S38's five pieces go to the write-up as red nodes,
   with O8 as slice W10's node.
3. If it does not: the failing step of "Where it breaks" is the next session's target.

## Worries <!-- budget 5 -->
- One reader for S32–S36. S35 (b)'s two independence cases and S34's count carry (W).
- S25 (case (i) from (A)) and S18 (i)'s steer reading at non-hubs with `|N[v]| ≤ 2` remain unverified
  by review 1; S27 is off the route now.
- S37's populations are structured and capped (`MAX_N = 16`; one geng slice at 10 bodies).

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0
- Open obligations: 1 (O8, write-up only; O7 closed by claim). 6 after s1, 1 after s2 (2 with review 1's O8), 1 now: falling
