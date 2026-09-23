# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 10 · last session: 2026-09-23 (session 10, two commits; small results landed one at a time per the 2026-09-23 trial rule) · review 3: 2026-09-23 (workbook S18); **review 4 due — three flat sessions at count 1** · baseline HEAD: d3d0bac0 · **Session 10 closed O7e piece (a) (S22):** at generic big points every rank pattern has `cost ≥ J₃ + 1` — a Case-2 pattern calculus with incidence sets, the flat-vertex geometry, Lemma D′ (a class pays for the `β = 2` flats it makes natural), the per-line flat balance, and a tightness argument · **count 1: O7e**, now pieces (b)–(c) · consumer unchanged at `d3d0bac0` (no Lean change since `084ee4ff`)

## Statement <!-- budget 10 -->
The two kernels of `pencilPair_of_splitOff_of_habitat` (`Escape.lean`, verbatim in brief §3.1; re-diffed session 10 at `d3d0bac0` — no Lean change since `084ee4ff`). For `G : Graph α β` and `v a b`, `eₐ e_b e₀` with `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid subgraph (`IsProperRigidSubgraph _ G 3`), `G.degree v = 2`, `eₐ ≠ e_b`, `G.IsLink eₐ v a`, `G.IsLink e_b v b`, `¬ PencilHub a ∨ ¬ PencilHub b`, `e₀ ∉ E(G)`, and the IH `∀ G', V(G').Nonempty → |V(G')| < |V(G)| → PencilPair K 3 G'`:
- **`hK`:** `HasGenericPencilRealization K 3 (G.splitOff v a b e₀) → HasGenericPencilRealization K 3 G`; no feasibility hypothesis (D1, S16(i)/(v)).
- **`hbareSplit`:** additionally `¬ PencilNondegFeasible K G`; `HasDistinctPencilRealization K 3 (G.splitOff v a b e₀) → HasDistinctPencilRealization K 3 G`.
Domain split (exhaustive, S19): (i) `G = C_n`, `n ≥ 5`; (ii) the chain closes at one hub `w`, `G = H″ ∪_w C_{m+1}`, `m + 1 ≥ 7`; (iii) two hubs, `G = H′ ∪ ear_m`, `m ≥ 2`, `G.splitOff = H′ ∪ ear_{m−1}`. Cases (i)–(ii) reach the kernels because the cut arm is `¬ TwoEdgeConnected` (S18(i)). Field `[Infinite K]`, no characteristic.
Unused: `eₐ ≠ e_b`, `e₀ ∉ E(G)` — well-formedness of `splitOff` only. In case (iii) at `m ≥ 6` the IH is unused by `hK` and the antecedent by `hbareSplit` (S17(v)); in cases (i)–(ii) `hbareSplit` is vacuous for cycles (feasible) and both kernels are pointwise (S20).

## Current route and proof sketch <!-- budget 30 -->
**Route R2 — the split-off antecedent and the IH as certificates for the generic point** (S14, S16, S17, S19–S22; adopted at review 2, plane-first form endorsed at review 3). Status by cell:
- **Case (iii), `hK`, all `m` — closed modulo O9 (written, S16(vi)).** `m ≥ 6` pointwise (S17(v)(b)); `m ≤ 5` Case 1 for `H′` (derived feasibility S16(v)), (★) by S19, `X̄(G₋)` by S18(iii), S14(iii) at the generic point, O9 for the `K`-point.
- **Case (iii), `hbareSplit`, `m ≥ 5` — closed (S17(v)(a)).**
- **Case (iii), `hbareSplit`, `m ≤ 4` — OPEN, O7e.** `H′` is Case 2 (S19(vii)(c)); S14(iii) at the generic point needs `X̄(H′)` irreducible, i.e. (★₂) on S21(ii)'s three-level tower `T` (big points, then planes, then other points): `codim_T Σ ≥ J₂ + J₃ + 1` off the generic stratum.
- **Cases (i)–(ii) — closed (S20(ii)–(iv))**; **characteristic — closed (S20(i))**, certificate (A).
- **What S22 gives (piece (a), strata over generic big points `q`, so `J₂ = 0`).** Pattern = classes, lines, and an incidence set `P_A ⊇ U_A` per class (extras `X_A`); consistency `P_B ∩ P_C = I(ℓ)`, `|I(ℓ)| ≤ 2`. Sequential cost with fixed planes first, U-classes, then flat singletons: a flat singleton after its line costs `2 − β_w` (`β_w` = its big neighbours, all on the line); a class after one line costs `c_A(ℓ) = 2 − |U_A ∩ I| − (|U_A ∖ I| − 1)⁺` (+ extras); relaxations (R1) reduce lines to flat-carrying ones, (R2) drop off-line extras. Then `cost − J₃ = Σ_A(σ_A − F_A) + Σ_ℓ N_ℓ + Σ_C cost_C` with the flat balance `N_ℓ ≥ −[w_{ab} ∈ ℓ]` (`w_{ab}` the unique common neighbour of two non-adjacent big vertices, cost `0`, jump `1`), paid by Lemma D′: `σ_A − F_A − Δ_A/2 ≥ 1` when `A` naturally supplies such an incidence (strict count on `Γ_A` plus the `w`'s). Tightness forces a nontrivial non-bad class in every case (S22(vi)). Theorem: `cost ≥ J₃ + 1` for every realisable pattern at generic `q` with `J₃ ≥ 1`.
Open obligations:
- **O7e** — (★₂) for Case-2 sides, remaining pieces (S21(vii), S22(vii)): **(b)** degenerate `q` (a rank drop among the big points) with nontrivial plane classes, lines or extras: pay the class discount `def_q(U_A) − Σ_{c ∈ A} def_q(U_c)` and S21(v)'s forced-`J₃` caveat out of `cost₁(q) − J₂` (S19 on `(Γ, Big)`, S21(v)) and S22(v)'s surplus; **(c)** sides with some `k_c ≥ 4` need another 3-degenerate order (S21(i)) and its own count. *Consumed because:* `hbareSplit` at `m ≤ 4` in case (iii) — its hypothesis `¬ PencilNondegFeasible K G` forces `H′` into Case 2 (S19(vii)(c)), and S14(iii) is applied at the generic point of `X̄(H′)` to the IH's Distinct witness (`hIH`'s second conjunct for `H′`) and to the antecedent (`HasDistinctPencilRealization K 3 (G.splitOff …)`).
Closed: O7d (S19); O10, O11 (S20); O7c (S17); O7e (a) (S22); O7 at `m ≥ 5`/`m ≥ 6` (S17(v)); O9 written (S16(vi)), load-bearing on `hK` at `m ≤ 5` and, through O7e, on `hbareSplit` at `m ≤ 4`.

## Where it breaks <!-- budget 10 -->
**O7e (b): the mixed patterns at degenerate big points.** A tower stratum where the big points satisfy a relation — `q_u = q_{u′}` (level-1 codimension `3`), three collinear (`2`), four coplanar (`1`) — *and* the planes carry classes, lines or extras. Pure point patterns are S19 on `(Γ, Big)` by duality (S21(v): `cost₁(q) ≥ J₂ + 1`), pure class patterns are S21(iv) (`cost − J₂ − J₃ = cost₁ − Σ_A def_q(U_A) + Σ_A σ_A`); S22 is the pure-plane side at generic `q`. What does not yet go through when both degenerate: (1) a class whose members see two now-dependent big points pays `def_q(U_A) − Σ_c def_q(U_c)` less than S22's merge cost — e.g. `q_u = q_{u′}` for far-apart `u ∈ U_c`, `u′ ∈ U_{c′}` gives `A = {c, c′}` a discount `1` against `cost₁ = 3`, `J₂ = 0`; (2) S22's incidence bookkeeping counts big *points*, so a coincident pair on a line is one point of `I(ℓ)` with two labels, and (ii)(a)–(b), Lemma D′ and the `|I(ℓ)| ≤ 2` cut all need restating for labelled points; (3) S21(v)'s caveat — two planes with `r_c = 3` and equal point spans are *forced* equal, a `J₃` contribution S22's classes never pay for. **Concrete first step:** state the pattern calculus of S22(i) over a *point pattern* `Q` (S19's strata on `(Γ, Big)`): `cost = cost₁(Q) + Σ_A merge_A(Q) + LC(Q)`, `J = J₂(Q) + J₃`, and prove `cost − J ≥ 1` first for the single relation `q_u = q_{u′}` with `u, u′` at Γ-distance `≥ 3` — the discount is then `1` on every class seeing both and `0` otherwise, and `cost₁ = 3` must cover the classes it touches.

## Tried on this route, and what each rules out <!-- budget 10 -->
- `case2geo.py` (session 10, helper-written; exact ℚ-realisations at fixed generic big points, Jacobian codimension bound): rules out a pattern with `M + ρ ≤ J₃` on twelve Case-2 hub graphs (`|Z| ≤ 9`, T10/T11 capped in pass 2, T9 skipped); the only tight shapes are the three S22(viii) predicts at value exactly `1`. Evidence over ℚ under its caps, not a proof.
- A lines-first (order-free) codimension count `Σ_A (1 − |U_A| + dim W_A) − Σ_ℓ (4 − 2|I(ℓ)|)` (session 10): rules out replacing S22's sequential cost by it — vacuous (`−1`) on three pencil planes sharing a line — unless the line's freedom is cut by the fixed axes and planes on it, a lemma with special-position cases; not pursued.
- Charging the whole `w_{ab}` deficit to one of `[a]`, `[b]` (session 10): rules out a `1` per charge from the augmented strict count alone (`0.75` per charge); the half-charge of Lemma D′ is what the count supports, and it suffices.
- `case2m2.py` (session 9; exact `ZZ/32003`, gauge-fixed standard charts, `minimalPrimes`): rules out a second component of the reduced variety on T1, T1c, T3, T2, T6, T7, T8, T9 (ten hand-built Case-2 hub graphs, `|Z| ≤ 10`, characteristic `32003`; cycle cases T10, T11 unfinished at `280` s); detects the extra components of the girth-3/4 negative controls.
- The three-level identity (S21(iii)): rules out any Case-2 penalty on pure class patterns at generic `q`.
- `unitcert.py` (session 8): rules out any characteristic restriction on S16(iii)(c)/S17(v)/S20 — certificate (A) has unit determinant.
- `starcomb.py` (session 8): rules out a violation of S19's four links and `cost ≥ J + 1` on `64 325` Case-1 patterns (seeds `1`, `2`: `73 969`, `55 831` more); `--case2 6` exhibits a legal Case-2 side.
- `starcheck.py` (session 7): the independent geometric control of (★) in Case 1 — PASS on nine graphs, `|Z| ≤ 7`, over ℚ.

## Next steps <!-- budget 5 -->
1. **O7e (b)**: the labelled-point pattern calculus of *Where it breaks*, single relation `q_u = q_{u′}` first, then collinear triples and coplanar quadruples; extend `case2geo.py` to draw the big points on the relation's stratum as the control for each step.
2. **O7e (c)**: a canonical 3-degenerate order when some `k_c ≥ 4` (planes of the `k_c ≥ 4` vertices first) and its jump count; T9 already shows one component.
3. **Review 4 (due):** the count has been `1` for sessions 8–10; S19–S22 are unreviewed — S22(ii)(e)'s realisability cuts and (iv)(c)'s path analysis are the two places a reviewer should re-derive.
4. **Lean round (PI-directed, not this attack):** S20(v)'s pointwise skeleton — unchanged.

## Worries <!-- budget 5 -->
- S22(ii)(e) (at most two fixed planes on a line; a pencil plane cannot join them) is the one geometric input of S22 beyond linear algebra; it was argued at generic `q`, and piece (b) will need its degenerate-`q` form.
- S22(iv)(c) and (vi)(4b) are hand case analyses (paths through a big point; the bad pair on a 2-point line); `case2geo.py`'s graphs are too small to exercise a bad pair on a 2-point line or a `u_ℓ = 1` path through a big point, so those two steps rest on the prose alone.
- S21(v) applies S19 to `(Γ, Big)`; S19 is unreviewed, and its relaxation step (S19(i)) is the one geometric sentence a reviewer should re-derive.
- `case2m2.py` counts primes over `F_{32003}`: evidence only (a single prime does not exclude a splitting over an extension, and says nothing in characteristic 0).
- The strict habitat count (S19(viii)) is load-bearing in S21(iii) and Lemma D′; it rests on "tight and sparse ⟹ six edge-disjoint spanning trees of `5K` ⟹ rigid", re-derived, not checked against a source.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (piece (a) of O7e is proved, S22(vi); the break moved to piece (b) — a proof landed, not a rename)
- Open obligations: 1 (trend over the last three sessions: 1 → 1 → 1 — flat; three flat sessions, review due)
