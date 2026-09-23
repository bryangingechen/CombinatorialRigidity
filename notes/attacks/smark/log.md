# Attack smark — retired attempts (one line each; what each rules out)

Overflow from `state.md`'s *Tried* section as the route narrows. Newest first.

## Session 11 (route R2; O7e-b's three coincidence relations closed, workbook S24–S27)
- Treating twin-natural incidences (a class natural for the merged point through the *other* label) as unpaid half-damage: rules out that bookkeeping — their number is bounded by no habitat count (one per big member of every class seeing exactly one label); S25(iv) absorbs them per class instead (`Δ′_A ≤ g_A` with `disc_A = 0`, and `T_A ≥ 0.25 ⟹ T_A ≥ 0`).
- Reading the `s = 0` relations (adjacent coincidence, star, coplanar quadruple) as needing S22(vi)'s tightness step redone on points (first draft of S26): rules out nothing and was a misreading — the requirement at a degenerate stratum is `cost − J₃ ≥ −s`, one less than S22's generic `+1`, so S22's three nonnegative sums suffice whenever the damage is `≤ s`; withdrawn the same session (S26(i)).
- Counting two `β = 2` flats on one line as a per-line loss (first draft of S25(iii)): rules out nothing — with `δ_ℓ` counting flats rather than lines the balance `N_ℓ + δ_ℓ ≥ 0` holds verbatim; the only new loss is an extra serving more than two flats (S25(v)).

## Session 10 (route R2; O7e piece (a) closed, workbook S22)
- S16(ii)'s 2-degenerate hub tower for Case 2 (carried in *Tried* through session 9): rules out nothing S21(i)'s 3-degeneracy of `𝔅` does not; retired as superseded.
- `planefirst.py` (135 sides, session 7): no Case-2 side in its library, so it says nothing about O7e; retired from *Tried*.

## Session 9 (route R2; O7e reduced to pieces (a)–(c), workbook S21)
- Plane-first rank stratum `{rk_y = min(s_y, 3)}` as Case 2's main stratum (first draft of S21(ii)): rules out stating (★₂) on rank strata of `B` — that set contains tower strata such as `q_u = q_{u′}` for far-apart big `u, u′` (codimension 3, no jump), so its irreducibility is not automatic; (★₂) is stated on the tower `T`.

## Session 8 (route R2; O7d, O10, O11 closed, workbook S19–S20)
- `earspan.py` / `earspan_modp.py` (ℚ- and `F_p`-draws of the ear span at `m = 5, 6, 7`): superseded by certificate (A) of `unitcert.py`; they rule out nothing the certificate does not, and stay as the record of how O11 was found.
- Reading S18(iv) after S19: rules out any need for it — `hK`'s arm is Case 1 at every `m ≤ 5`; not consumed.
- Brief §3.5(d)'s "cut-vertex additivity, corpus-proved": re-derived for a one-vertex cut only (S20(ii)); rules out the two-vertex analogue (it is the 2-cut law's `min(δ₁ + δ₂, 6)`).

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

## Session 6 (route R2; the break moved from "the tower needs a hub order that need not exist" to O7c)
- Re-diff of the consumer at `c9dd58ca` against every definition body: rules out the brief's "`hK`'s domain is the feasible case" as a *given* (S16(i) D1 — feasibility of `G` must be derived from the antecedent; done in S16(v)) and its "(α) deletes O8" (D2 — `HasDistinctPencilRealization` still admits collinear hub stars and coincident hub planes; absorbed by S16(iv)).
- The habitat count on the hub graph (S16(ii)): rules out a hub **subgraph of minimum degree `≥ 3`** — every subgraph has `5|E| ≤ 6|V| − 6`, so the hub graph is 2-degenerate; the planned adjacent-hub control was not run. *(Reworded at review 4, S23(iii): as first written this line claimed to rule out the brief's O7 "first instance" — a hub with three hub neighbours each of hub-degree `≥ 3` — as a habitat member. It does not: that local shape is habitat-legal with long paths (S21(vii)(c), the spider T9) and is live as O7e-c. Only the global minimum-degree statement is what the count gives.)*
- `earspan.py` (seed 20260922, 20 draws per cell): rules out "`ρ̄(ear_m) = Λ²` fails at incident flags" for `m = 5, 6` — rank 6 at every draw, one being a certificate (S16(iii)(c)).
- The direct deficiency count `def₃(H′ ∪ ear_m) = f′ + m − 5` (S16(iii)(a)): rules out any need for the edge-bipartition 2-cut law at `m ≥ 5`, and the `m ≥ 5` step's use of S14(i).

## Session 7 (route R2; crashed uncommitted 2026-09-22/23, recovered 2026-09-23 from the local transcript — nothing here was verified in-session; the recovery aids were deleted after review 3, the durable record is workbook S17)
- Route A, ear decompositions of the hub graph with ears of interior length `≥ 4` (excess function over the Krull floor, 7 `PGL₄`-orbits of flag pairs, `C(3)` fails only at equal flags): rules out nothing — girth `≥ 7` admits length-1 chords and the `K₄`/`K_{3,3}` subdivided into length-3 branches; abandoned.
- Route B, hub-edge graph vs length-2 branches, forest case via Shafarevich, peeling induction `T2 → T7`: rules out the one-hub-at-a-time peel — the `(3,3,3,3,1,1)`-type core leaves every remaining hub with hub-edge-degree `≥ 3` after a pinned pair; abandoned at the output cap.
- Direct fibre recount over `{π_{z₁} = π_{z₂}}`: rules out S16(iv)'s "(a′) jump 2" — both sub-cases jump 1 (confirmed plane-first, S17(vi)).

## Session 7-recovery (2026-09-23; route R2 restated plane-first, S17)
- Peel induction on a marked vertex in the plane-first base: rules out a naive induction on `|Z|` — concurrent-line conditions on the earlier planes are invisible to `J′`; replaced by global charging (Lemmas P, L).
- Reading S14(iii) pointwise for `hK` at `m = 5` from the IH: rules out that shortcut — the hub-neighbourhood conjunct at a `G`-degree-3 chain end is not imposed on `H′`'s witness.

## Session 12 (2026-09-23; S28–S31)
- Planning a separate charge for the line `ℓ₀` of classes through `λ₀` (state, session 11): rules out its necessity — S28(i)'s rank values price those classes at their true cost `0`.
- S22(iii)'s "an extra serves at most two flats" as the working bound: superseded by S28(iii) (at most one, any `q`), which removes the extras overflow at the collinear and coplanar strata.
