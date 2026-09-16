# Attack smark — retired attempts (one line each; what each rules out)

Overflow from `state.md`'s *Tried* section as the route narrows. Newest first.

## Session 4 (route R1, retired at session 5: (O4″) is not consumed — workbook S14)
- `pencilline.py` (6/6 draws, `sk4_d3`/`sk4_d4`/`prism`): rules out "the K4-minor / three-hub structure puts a screw into the pencil" — the line is the direct branch's `L_{wx}` and the branch co-moves with `v`; with `δ(side − branch) = 6` this is S8's ear profile via S13(ii).
- `census.py` (200 rows, 13 skeleton families, lengths 2–4, `δ ∈ {2,3,4}`, `|V| ≤ 32`; 0 flagged): rules out any excess at any block for side-degree-`≥ 2` single pieces at `δ ≤ 3` **within the population**; the only `c(Π_w) = 1` rows are bridges (S6) and `δ = dist = 4` (a path span).
- `specialcfg.py` (nine special loci × 3 draws on `K4−e (4,2,3,4,2)`): rules out `Π_w ⊆ ρ̄` on those loci even where the side stops attaining; family (i) (`a′ = 1`, `a′_w = 0`, `δ′ = 3`) is now the pointwise witness of S14(v)'s gap.
- Path-span bound `ρ̄ ⊆ span(P)` for `dist ≥ 6`: rules out nothing (`span = Λ²K⁴`); it is exactly what S13(v) exhausts at `dist ≤ 5`.
- Sub-side monotonicity toward `K4−e`: rules out that route — a `K4−e` sub-side of a `dist ≥ 8` piece has `≥ 17` edges and may have `δ = 6`.
- Re-gluing `m` (with `m(v) − m(w) = L_{wx₁}`) into `H/wv` by `m(w) := L_{wx₁}`: fails at every other hinge at `w` — rules out a one-line contradiction from the welded framework at side-degree `≥ 2`.
- (O4″) itself — `ρ̄ ∩ Π_w = 0` on single pieces with `dist ≥ 6`, `δ ≤ 3`: measured true at 52 census rows and 9 special families, unproved; retired because the consumer needs only `Π_w ⊄ ρ̄′`, which the split-off antecedent supplies (S14(iii)). Still a true-looking statement about sides; nobody consumes it.

## Sessions 1–2 (route R1, retired at session 3 as the break moved to O4′)
- Incidence count over the 19 orbit strata (S2, session 1): rules out "the gauge group `S(ϕ)` is too small to attain the block cap" — only the four isotropy exceptions (X1)–(X4) escape the `dim ≤ 4 < 5` count.
- Two-stars pair (S4, exact, 20 × 30 group draws): rules out "the 16 block inequalities are sufficient" — Klein parity forces two α-planes to meet, an obstruction outside the block list.
- Side-profile batteries, 23 sides × 6 draws (S5/S8, seed 20260915; theorems by S7(vi)): rules out excess at a side-degree-≥2 terminal **for those 23 sides**; showed (X4)'s ruling-plane shape is realised by `ear1`, so (X4) stays a hypothesis of S2.
- `earone.py`, 23 sides × 6 × 3 `p_x` (S9, seed 20260915): rules out a hidden case in S9's `ear1`-criterion proof within the population; `T ∩ ⟨M,L⟩ ≠ 0` only at `dist(u,v) ≤ 3`.
- Path wrench mechanism (S8 reading): rules out extending the transparent `dist ≥ 4 ⟹ T ∩ ⟨M,L⟩ = 0` argument to general sides — `T = ρ̄^⊥` strictly exceeds the path-generated `Σ_P span(P)^⊥`; the mechanism is a theorem only for paths.
- Side-induction kill (session 2): peeling the whole degree-2 chain lands back on the block lattice at the hub cut (that is S10), not a genuine reduction of `H′`; what survives is the O4′ profile bounds at side-degree ≥ 2.
- Reading `Deficiency.lean` (`def₂ = 3(|P|−1) − 2d(P)`): rules out the flat all-coplanar witness (brief §3(a),(c)) as a substitute for the Lemma on the consumed class — `C_n` has `def₂ = n−3 > n−6 = def₃`.
- Review reading of `Escape.lean:467` (2026-09-15): the disjunct `¬ PencilHub a ∨ ¬ PencilHub b` — rules out the one-vertex ear between two hubs as the consumed shape (S9 is about a case the consumer does not take); the consumed shape is the `ear_m` trichotomy (S11).

## Session 3 (route R1, retired at session 4 as the break moved to (O4″))
- Hand verification of S10 block-by-block against S3 + S8 (S12(i)): rules out an arithmetic slip in the reviewer's chain-length stratification — every `m`-case bound reproduced.
- `earcompose.py`, 14 hub sides × 3 ears × 6 draws = 252/252 (seed 20260916; theorems by S7(vi)): rules out "S10 predicts attainment wrongly" and "a battery side exceeds the S10 `c′` bound" — 2-cut law holds, S3 criterion ⟺ exact rank.
- `adversarial.py`, K4-minor + prism sides at `δ = 2,3,4` × 6 draws: rules out `c′(Π_w) ≥ 2` on those four sides; its "tight = 1" reading was an ear's `L_{wx}` (S13(i)), so it rules out nothing about hub structure.
- `earcompose --side sk4_d*` (K4-minor ∪ `ear_{2,3}`, 6 draws): rules out "the consumed shape fails on a K4-minor side" — attains at every draw; the side is an ear composed with a `δ = 6` remainder.
