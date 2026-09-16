# Attack smark — retired attempts (one line each; what each rules out)

Overflow from `state.md`'s *Tried* section as the route narrows. Newest first.

## Sessions 1–2 (route R1, retired at session 3 as the break moved to O4′)
- Incidence count over the 19 orbit strata (S2, session 1): rules out "the gauge group `S(ϕ)` is too small to attain the block cap" — only the four isotropy exceptions (X1)–(X4) escape the `dim ≤ 4 < 5` count.
- Two-stars pair (S4, exact, 20 × 30 group draws): rules out "the 16 block inequalities are sufficient" — Klein parity forces two α-planes to meet, an obstruction outside the block list.
- Side-profile batteries, 23 sides × 6 draws (S5/S8, seed 20260915; theorems by S7(vi)): rules out excess at a side-degree-≥2 terminal **for those 23 sides**; showed (X4)'s ruling-plane shape is realised by `ear1`, so (X4) stays a hypothesis of S2.
- `earone.py`, 23 sides × 6 × 3 `p_x` (S9, seed 20260915): rules out a hidden case in S9's `ear1`-criterion proof within the population; `T ∩ ⟨M,L⟩ ≠ 0` only at `dist(u,v) ≤ 3`.
- Path wrench mechanism (S8 reading): rules out extending the transparent `dist ≥ 4 ⟹ T ∩ ⟨M,L⟩ = 0` argument to general sides — `T = ρ̄^⊥` strictly exceeds the path-generated `Σ_P span(P)^⊥`; the mechanism is a theorem only for paths.
- Side-induction kill (session 2): peeling the whole degree-2 chain lands back on the block lattice at the hub cut (that is S10), not a genuine reduction of `H′`; what survives is the O4′ profile bounds at side-degree ≥ 2.
- Reading `Deficiency.lean` (`def₂ = 3(|P|−1) − 2d(P)`): rules out the flat all-coplanar witness (brief §3(a),(c)) as a substitute for the Lemma on the consumed class — `C_n` has `def₂ = n−3 > n−6 = def₃`.
- Review reading of `Escape.lean:467` (2026-09-15): the disjunct `¬ PencilHub a ∨ ¬ PencilHub b` — rules out the one-vertex ear between two hubs as the consumed shape (S9 is about a case the consumer does not take); the consumed shape is the `ear_m` trichotomy (S11).
