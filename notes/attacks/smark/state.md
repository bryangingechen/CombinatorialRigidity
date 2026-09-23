# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 9 · last session: 2026-09-23 (session 9, one commit; resumed once after an output-cap cut, checkpointed per the 2026-09-23 trial rule) · review 3: 2026-09-23 (workbook S18) · baseline HEAD: dc846bf2 · **Session 9 reduced O7e (S21):** the incidence structure is 3-degenerate; (★) restated for Case 2 in the three-level tower (big points → planes → other points); the class surplus equals the Case-1 surplus and Lemma P holds in every case under the strict count; pure point patterns are S19 by duality; `case2m2.py` finds one component on ten Case-2 hub graphs · **count 1: O7e**, now pieces (a)–(c) · consumer unchanged at `dc846bf2` (no Lean change since `084ee4ff`)

## Statement <!-- budget 10 -->
The two kernels of `pencilPair_of_splitOff_of_habitat` (`Escape.lean`, verbatim in brief §3.1; re-diffed session 9 at `dc846bf2`, S21 — no change). For `G : Graph α β` and `v a b`, `eₐ e_b e₀` with `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid subgraph (`IsProperRigidSubgraph _ G 3`), `G.degree v = 2`, `eₐ ≠ e_b`, `G.IsLink eₐ v a`, `G.IsLink e_b v b`, `¬ PencilHub a ∨ ¬ PencilHub b`, `e₀ ∉ E(G)`, and the IH `∀ G', V(G').Nonempty → |V(G')| < |V(G)| → PencilPair K 3 G'`:
- **`hK`:** `HasGenericPencilRealization K 3 (G.splitOff v a b e₀) → HasGenericPencilRealization K 3 G`; no feasibility hypothesis (D1, S16(i)/(v)).
- **`hbareSplit`:** additionally `¬ PencilNondegFeasible K G`; `HasDistinctPencilRealization K 3 (G.splitOff v a b e₀) → HasDistinctPencilRealization K 3 G`.
Domain split (exhaustive, S19): (i) `G = C_n`, `n ≥ 5`; (ii) the chain closes at one hub `w`, `G = H″ ∪_w C_{m+1}`, `m + 1 ≥ 7`; (iii) two hubs, `G = H′ ∪ ear_m`, `m ≥ 2`, `G.splitOff = H′ ∪ ear_{m−1}`. Cases (i)–(ii) reach the kernels because the cut arm is `¬ TwoEdgeConnected` (S18(i)). Field `[Infinite K]`, no characteristic.
Unused: `eₐ ≠ e_b`, `e₀ ∉ E(G)` — well-formedness of `splitOff` only. In case (iii) at `m ≥ 6` the IH is unused by `hK` and the antecedent by `hbareSplit` (S17(v)); in cases (i)–(ii) `hbareSplit` is vacuous for cycles (feasible) and both kernels are pointwise (S20).

## Current route and proof sketch <!-- budget 30 -->
**Route R2 — the split-off antecedent and the IH as certificates for the generic point** (S14, S16, S17, S19–S21; adopted at review 2, plane-first form endorsed at review 3). Status by cell:
- **Case (iii), `hK`, all `m` — closed modulo O9 (written, S16(vi)).** `m ≥ 6` pointwise (S17(v)(b)); `m ≤ 5` Case 1 for `H′` (derived feasibility S16(v)), (★) by S19, `X̄(G₋)` by S18(iii), S14(iii) at the generic point, O9 for the `K`-point.
- **Case (iii), `hbareSplit`, `m ≥ 5` — closed (S17(v)(a)).**
- **Case (iii), `hbareSplit`, `m ≤ 4` — OPEN, O7e.** `H′` is Case 2 (S19(vii)(c)); S14(iii) at the generic point needs `X̄(H′)` irreducible.
- **Cases (i)–(ii) — closed (S20(ii)–(iv))**, cut-vertex additivity; **characteristic — closed (S20(i))**, certificate (A).
- **What S21 gives O7e.** (i) `𝔅(H′)` (points `V`, planes `Z`, `y — c` iff `y ∈ N[c]`) is 3-degenerate — a min-degree-4 core forces a hub subgraph of min degree 3 against average `< 2.4` — so every 3-degenerate order has a tower of the expected dimension and S16(iv)'s "codim > jump" reduction. (ii) When `k_c := |Big ∩ N_Γ[c]| ≤ 3` for all `c`, the order *big points `q_u`, then planes `π_c ∋ U_c`, then the other points* is one; jumps `J₂ = Σ_c (k_c − r_c)`, `J₃ = Σ_{y ∉ Big}(s_y − rk_y)`, big hyperedges absent from `J₃`; **(★₂)** `codim_T ≥ J₂ + J₃ + 1` off the generic tower stratum ⟹ `X̄(H′)` irreducible. (iii) At generic `q` a plane class costs `σ_A + J₃_A` exactly (S19's `σ_A` on the full hypergraph), Lemma P holds in every case (`J_A ≤ 2.4a − 2.8`), and `σ_A − F_A ≥ 1` except S19's bad pair. (iv) At degenerate `q`: `cost − J = cost₁(q) − Σ_A def_q(U_A) + Σ σ_A` (no lines). (v) Pure point patterns = S19 on `(Γ, Big)` by `P³ ↔ P³*` duality. (vi) The `--case2 6` side is irreducible by hand.
Open obligations:
- **O7e** — (★₂) for Case-2 sides, in three pieces (S21(vii)): **(a)** lines at generic `q`: S19 Steps 2–4 with placement cost `min(2 − |I(λ)|, 3 − |Ū_C|)` on one determined line, `3 − |Ū_C|` on two, extras `1` each; **(b)** mixed patterns (degenerate `q` with nontrivial plane classes or lines): pay the discount `def_q(U_A) − Σ_{c ∈ A} def_q(U_c)` and S21(v)'s forced-`J₃` caveat from `cost₁ − J₂` and `σ_A`; **(c)** sides with some `k_c ≥ 4` need another 3-degenerate order. *Consumed because:* `hbareSplit` at `m ≤ 4` in case (iii) — its hypothesis `¬ PencilNondegFeasible K G` forces `H′` into Case 2 (S19(vii)(c)), and S14(iii) is applied at the generic point of `X̄(H′)` to the IH's Distinct witness (`hIH`'s second conjunct for `H′`) and to the antecedent (`HasDistinctPencilRealization K 3 (G.splitOff …)`).
Closed: O7d (S19); O10, O11 (S20); O7c (S17); O7 at `m ≥ 5`/`m ≥ 6` (S17(v)); O9 written (S16(vi)), load-bearing on `hK` at `m ≤ 5` and, through O7e, on `hbareSplit` at `m ≤ 4`.

## Where it breaks <!-- budget 10 -->
**O7e (a): the line charging with constrained planes** (the first of S21(vii)'s three pieces; (b), (c) wait on it). At generic big points, planes through a common big point `q_u` are cheap to put on a line through `q_u` (cost `1` per placement, `0` on the line `q_u q_{u′}`), so S19's per-line surplus `2(t − 2) − f` no longer holds as stated. The compensating fact to prove: a class on a line `λ` must contain every big point on `λ`; it does so *naturally* only if some member lies in `N_Γ[u]`, otherwise it pays one extra incidence per missing point; and a flat non-big `y` has at most two of its triple `{y, a, b}` in `N[u]` (exactly two iff `u ∈ {a, b}`), so each flat on such a line forces `≥ 1` extra or a merged class. Worked cases: flat `y` between big `a, b` on `q_a q_b` — cost `2` (two extras), jump `1`; `k` flat neighbours `y_j` of one big `u` on a line through `q_u` — `LC = 2k − 1`, `≥ k` extras, jump `k`. **Concrete first step:** state and prove the per-line surplus `LC_ℓ + X_ℓ − f_ℓ ≥ 0` with equality classified (as S19(iii) did for type (3)), `X_ℓ` the extras charged to `ℓ` (an extra on a class lying on two lines through `q_u` must be charged once — that class then costs its full budget), then redo S19's loss step.

## Tried on this route, and what each rules out <!-- budget 10 -->
- `case2m2.py` (session 9; exact `ZZ/32003`, gauge-fixed standard charts, `minimalPrimes`): rules out a second component of the reduced variety on T1 (`--case2 6`), T1c, T3 (`K_{1,4}`), T2 (adjacent big hubs), T6, T7 (big hubs at distance 2), T8 (three big hubs in a path, `k = 3`), T9 (spider, `k_c = 4`, `1098` s); detects the extra components of the girth-3/4 negative controls. Cycle cases T10, T11 did not finish in `280` s. Ten hand-built graphs, not a population.
- The three-level identity (S21(iii)): rules out any Case-2 penalty on pure class patterns at generic `q` — the class surplus is S19's `σ_A ≥ 1` computed on the full hypergraph.
- S16(ii)'s 2-degenerate hub tower for Case 2: not needed — (i)'s 3-degeneracy of `𝔅` supersedes it.
- `unitcert.py` (session 8): rules out any characteristic restriction on S16(iii)(c)/S17(v)/S20 — certificate (A) has unit determinant.
- `starcomb.py` (session 8): rules out a violation of S19's four links and `cost ≥ J + 1` on `64 325` Case-1 patterns (seeds `1`, `2`: `73 969`, `55 831` more); `--case2 6` exhibits a legal Case-2 side. Population uses the non-strict count (a superset of legal sides).
- `starcheck.py` (session 7): the independent geometric control of (★) in Case 1 — PASS on nine graphs, `|Z| ≤ 7`, over ℚ.
- `planefirst.py` (135 sides): no Case-2 side in its library; says nothing about O7e.

## Next steps <!-- budget 5 -->
1. **O7e (a)**: the per-line surplus with constrained costs and extras (Where it breaks), then S19's loss step; test it with a Case-2 extension of `starcomb.py` (points `q` generic, patterns = classes × lines × incidence sets `I(λ)`), strict-count population.
2. **O7e (b)** after (a): the discount of S21(iv) against `cost₁ − J₂` (S19 on `(Γ, Big)`) and `σ_A`; include S21(v)'s forced-`J₃` caveat.
3. **O7e (c)**: pick a canonical 3-degenerate order when some `k_c ≥ 4` (e.g. put the planes of the `k_c ≥ 4` vertices first); T9 (a `k_c = 4` side) already has one component; run T10/T11 in the background with a long timeout.
4. **Review:** S19–S21 are unreviewed; a `/review-attack` is recommended before the Lean round leans on S20 (not mechanically due: the route is unchanged).
5. **Lean round (PI-directed, not this attack):** S20(v)'s pointwise skeleton — unchanged by this session.

## Worries <!-- budget 5 -->
- S21(i)'s "generic position at each step" is checked only for the three-level order (the Hall check of S21(ii)); another order for (c) needs its own check.
- S21(v) applies S19 to `(Γ, Big)`; S19 is unreviewed, and its relaxation step (S19(i)) is the one geometric sentence a reviewer should re-derive.
- `case2m2.py` counts primes over `F_{32003}`: a single prime there does not exclude a splitting over an extension, and says nothing in characteristic 0 — evidence only.
- The strict habitat count (S19(viii)) is now load-bearing in S21(iii); it rests on "tight and sparse ⟹ six edge-disjoint spanning trees of `5K` ⟹ rigid", re-derived, not checked against a source.
- S20(i)(b)'s orbit-closure step and S16(ii)'s count remain as flagged in session 8.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 1 (still O7e since session 8; this session narrowed it from "the three-level base" to piece (a), the line charging — same obligation, not a moved break)
- Open obligations: 1 (trend over the last three sessions: 4 → 1 → 1 — flat this session; O7e split into pieces (a)–(c), none closed)
