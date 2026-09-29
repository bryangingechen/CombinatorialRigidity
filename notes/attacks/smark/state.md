# Attack smark — state

**CLOSED on the PI's word, 2026-09-29**: the O7e programme on `hK`/`hbareSplit` is retired with the rest of `notes/Phase40-design.md` §6 at Phase 40's close, which proved the pencil conjecture by the main-component route (verbatim in `notes/pencil/adjudications.md`); the rest of this file records where the attack stopped.

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 14 · last session: 2026-09-23 (session 14; S39–S41) · review 6: 2026-09-23 (S42) · baseline HEAD: b0d76407 · **count 4: O7e-b(a), O7e-b(b), O7e-b(c), O7e-c** · consumer unchanged (`git diff 084ee4ff HEAD -- CombinatorialRigidity` empty; kernels token-identical to brief §3.1) · **next: O7e-c's `M ⊋ M₀` strata on the one-centre shape (S41(iv)); new results from S43**

## Statement <!-- budget 10 -->
The two kernels of `pencilPair_of_splitOff_of_habitat` (`Escape.lean`, verbatim in brief §3.1; re-diffed at session 14, no Lean change since `084ee4ff`). For `G : Graph α β` and `v a b`, `eₐ e_b e₀` with `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid subgraph (`IsProperRigidSubgraph _ G 3` — a *proper vertex subset*), `G.degree v = 2`, `eₐ ≠ e_b`, `G.IsLink eₐ v a`, `G.IsLink e_b v b`, `¬ PencilHub a ∨ ¬ PencilHub b`, `e₀ ∉ E(G)`, and the IH `∀ G', V(G').Nonempty → |V(G')| < |V(G)| → PencilPair K 3 G'`:
- **`hK`:** `HasGenericPencilRealization K 3 (G.splitOff v a b e₀) → HasGenericPencilRealization K 3 G`; no feasibility hypothesis (D1, S16(i)/(v)).
- **`hbareSplit`:** additionally `¬ PencilNondegFeasible K G`; `HasDistinctPencilRealization K 3 (G.splitOff …) → HasDistinctPencilRealization K 3 G`.
Domain split (exhaustive, S19): (i) `G = C_n`, `n ≥ 5`; (ii) one hub `w`, `G = H″ ∪_w C_{m+1}`, `m + 1 ≥ 7`; (iii) two hubs, `G = H′ ∪ ear_m`, `m ≥ 2`, `G.splitOff = H′ ∪ ear_{m−1}`. Cases (i)–(ii) reach the kernels because the cut arm is `¬ TwoEdgeConnected` (S18(i)). The domain contains rigid `G` (`C₅`, `C₆`, `θ(5,3,4)`); the route needs no positivity (S14(iii)'s cell `g′ = 0`). Marked set `Z = hubs(G)`; Case 2 for `(H′, Z)` ⟺ `¬ PencilNondegFeasible K G` (S19(vii)(c)). Field `[Infinite K]`, no characteristic.
Unused: `eₐ ≠ e_b`, `e₀ ∉ E(G)` — well-formedness of `splitOff` only. In case (iii) at `m ≥ 6` the IH is unused by `hK` and the antecedent by `hbareSplit` (S17(v)); in cases (i)–(ii) `hbareSplit` is vacuous for cycles and both kernels are pointwise (S20).

## Current route and proof sketch <!-- budget 30 -->
**Route R2 — the split-off antecedent and the IH as certificates for the generic point** (S14, S16, S17, S19–S22, S25–S41). Status by cell:
- **Case (iii), `hK`, all `m` — closed modulo O9 (written, S16(vi)).** `m ≥ 6` pointwise (S17(v)(b)); `m ≤ 5` Case 1 for `H′`, (★) by S19.
- **Case (iii), `hbareSplit`, `m ≥ 5` — closed (S17(v)(a)).** **Cases (i)–(ii), characteristic — closed (S20).**
- **Case (iii), `hbareSplit`, `m ≤ 4` — OPEN.** `H′` is Case 2 (S19(vii)(c)); S14(iii) needs `X̄(H′)` irreducible.
- **O7e restructured (S40, session 14).** For a pair `(Γ, Z)` (girth `≥ 7`, strict count, unmarked degree `≤ 2`) with onion `S₀ = Z`, `S_{i+1} = {deg_{Γ[S_i]} ≥ 3}`, depth `D`: `X̄(Γ, Z)` is irreducible if `W := X̄(Γ[Z], Big)*` (depth `D − 1`) is, and **(★₂)** `c₁(M) − J₂(M) + cost(P) ≥ J₃(P) + 1` holds for every realisable `(M, P)` with `J₃ ≥ 1` (S40(iii); jump counts are tower-independent, S40(ii), so the three-level ledger is valid at every depth, `k_c ≥ 4` included). Depth `0` is S19. **So O7e ⟸ (★₂) at every depth `≥ 1`** (sufficient only: `cost(P)` is a lower bound, S42(i)). Depth is unbounded (S40(v): a depth-3 core is legal), and the onion order is this induction unrolled (S40(i)).
- **Depth 1:** generic `M` is S22 (O7e-a, closed); degenerate `M` is O7e-b: all single relations closed (S25–S30); several relations reduced to S34(iv), `Dmg ≤ Σ_{R touched} b_R − ½`.
- **Control S39 (the PI's first step, session 14):** E55 at `v=u;a=u+b` *is* S35(iii)'s test cluster (S37's "no damage shapes on E55" was wrong); `dmgmax.py` enumerates every pattern: max `Dmg = 2` vs `9/2`, all maximisers two class units of S36(i)'s equality type; four more multi-relation strata give max `≤ s − 1`. S34(iv) is not refuted; the programme continues.
- **Depth `≥ 2` (O7e-c):** at `M₀` (generic `W`-point, `Q_c := Big ∩ N[c]` coplanar for `c ∈ S₂`) `s = −1`, so (★₂) is S22's *strict* theorem there; at `M ≠ M₀`, `s(M) ≥ 0` by the induction and (★₂) is O7e-b's counting with forced circuits of `b_R = 0` (S40(iv)). **S41: on the one-centre shape (`S₂ = {c}`, `deg c = 3`, `U_{x_i} = {x_i, c}`) the `M₀` part holds** — at tightness `[c]` is a singleton and on no reduced line, and S22(vi) runs verbatim (audited S42(v): holds with two repairs, at the generic point of `{Q_c coplanar}`).
Open obligations (each is `hbareSplit` at `m ≤ 4` in case (iii): its hypothesis `¬ PencilNondegFeasible K G` forces `H′` into Case 2, and S14(iii) is applied at the generic point of `X̄(H′)` to the IH's Distinct witness for `H′` and to the antecedent `HasDistinctPencilRealization K 3 (G.splitOff …)`):
- **O7e-b — S34(iv)**, by piece (review 5). *Consumed because:* a degenerate `q` is a tower stratum; a component of `X̄(H′)` over it would break irreducibility.
  - **O7e-b(a) — the class lemma** (S36(iii)): no-charge, `J^{nb} = 0` case proved (S36(i)–(ii)); open `J^{nb}_A ≥ 1` (a) and `M`-natural charges (b). S39: on E55 neither carries damage.
  - **O7e-b(b) — prices add** across the relations of one cluster (S35(iii)).
  - **O7e-b(c) — per cluster**, max damage under `6|B₀| − 7` is `≤ b_R − ½` (type-sensitive, S35(ii)).
- **O7e-c — (★₂) at depth `≥ 2`** (S40(iii)–(iv)). *Consumed because:* habitat-legal cores have `k_c ≥ 4` (`k4core 6`, depth 2; `tree2 5`, depth 3 — S38(iv), S40(v)); a component over any of their strata breaks irreducibility. Open: `M ⊋ M₀` (O7e-b's statement with forced `b_R = 0` circuits; first stratum: `Q_c`'s collinear degeneration with `c` a star, S41(iv)); `M₀` beyond the one-centre shape (several centres; a centre with a non-big neighbour; depth `≥ 3`).
Closed: O7d (S19); O10, O11 (S20); O7c (S17); O7e-a (S22, with S42(v)'s (4a) repair); O7e-b's six single relations (S25, S26 with S27(i)'s O6 line, S28–S30); O7 at `m ≥ 5`/`m ≥ 6` (S17(v)); O9 written (S16(vi)).

## Where it breaks <!-- budget 10 -->
Two places, one per open piece. **(1) O7e-c, the strata over `M ⊋ M₀`** — first on the one-centre shape, the stratum where `q_c, q_{x₀}, q_{x₁}` are collinear inside `π_c` (S41(iv)): `c₁` rises by `1`, `J₂` is unchanged (`r_c = 3` through `q_{x₂}`), so `s = 0` and zero damage is required; `c` sees the whole triple (a star, S29), and whether girth again leaves no damage shape is unchecked. Then the coincidences inside `Q_c` (`q_c = q_{x_i}` is adjacent, S26(ii)'s type; `q_{x_i} = q_{x_j}` is at distance 2). Beyond the one-centre shape the `M₀` part breaks first where a centre has a non-big neighbour: a flat vertex then puts `π_c` (four labels) on a reduced line, which S41(iii)(3) used to exclude. **(2) O7e-b(a), the class term at an arbitrary `M`** (unchanged from session 13): no lemma yet gives `(disc_A + Δᴹ_A/2 − S_A)⁺ ≤ ⅛ · price(A)` (twin `½`) when `J^{nb}_A ≥ 1` or `Δᴹ_A ≥ 1`; S36's identity `damage_A = (3 − rk U_A) + J^{nb}_A + (Δ_A + Δᴹ_A)/2 − Σ ε_c` is the tool, and S36(iii)(b)'s corrected statement (price relative to `B₀ ∪ (A ∩ Big)`, `S_A` paying `½` per charge from a big member outside `B₀`) is the next step there.

## Tried on this route, and what each rules out <!-- budget 10 -->
- `dmgmax.py` (session 14, S39): exhaustive `Dmg` on D3, D3r, E13, E15 (reproduces S25(vi) exactly) and five multi-relation strata (E55 ×4, E15): max `≤ s − 1`; rules out a refutation of S34(iv) there — non-core graphs, one draw; tests the ledger bound, not (★₂).
- `onion.py` (session 14, S40(v)): `tree2 5` is a legal depth-3 core; rules out treating O7e-c shape by shape — hence the induction on depth.
- `case2deg.py --relations` (session 13, S37): no negative slack on two-relation strata, lower bounds under caps; E55 *does* carry the damage shapes (S39(i)).
- `case2deg.py --collinear` / `--pair` (sessions 11–12): no negative slack on thirteen single-relation runs, exact below caps.
- `case2m2.py` (sessions 9, 11): every PASS is a tree or a `C₇` core; rules out nothing about Case 2 (S27(vi)).
- `case2geo.py` (session 10): no pattern with `M + ρ ≤ J₃` at generic `q` on twelve graphs.
- Per-label budgets (session 13): rule out label-local budgets; components replace them (S32).
- One uniform ratio `⅛` (session 13): rules out a type-blind count on coplanar clusters; the hub's fixed price is needed (S35(ii)).
- Summing S28(vi)'s per-triple `k₁ ≤ 1` (session 13): rules out cluster-level `k₁ ≤ 1` (S35(iii); S39 confirms two coexist, `Dmg = 2`).
- Lines-first count and one-sided `w_{ab}` charging (session 10): rule out replacing the sequential cost.

## Next steps <!-- budget 5 -->
1. **O7e-c, one-centre shape, `M ⊋ M₀`:** the collinear degeneration of `Q_c` (star at `c`, `s = 0`; S29's ledger re-derived at `k_c = 4`, where `π_c` is fixed, S42(iii)), then the coincidences inside `Q_c`, then relations mixing `Q_c` with outside labels; each as one S-number.
2. **O7e-c, `M₀` in general:** a centre with a non-big neighbour (`π_c` on a reduced line), then two adjacent centres (`Q_c ∩ Q_{c′} = {c, c′}`; prove the `Q_c` are `M₀`'s only small circuits).
3. **O7e-b(a):** S36(iii)(b), then (iii)(a); then O7e-b(b)–(c). Propose to the PI that O7e-b be stated at every depth (forced circuits with `b_R = 0`), which folds O7e-c's `M ⊋ M₀` part into it.
4. **Audits:** S26, S29, S40(i)–(iii), S41 done at review 6 (S42(ii)–(v)); S30 still owed (it matters only on cores of `≥ 17` vertices, S42(vi)).
5. **Lean round (PI-directed):** S20(v)'s pointwise skeleton — unchanged.

## Worries <!-- budget 5 -->
- No control reaches a core of `≥ 17` vertices, where every open piece lives (S42(vi)): on the 12-vertex thetas `dmgmax` and Macaulay2 time out and `case2deg` caps at ~0.6 % of partitions (S42(vii)). The open statement has no evidence where it can fail.
- S34(iv) has zero slack at its single-relation base cases; S39's margins (`≥ 3/2`) are on non-core graphs only, and a genuine core carrying the test cluster (17 vertices) is out of exhaustive reach.
- S41's one-centre shape is the easy case (every neighbour of `c` big); `M₀` with several centres may have circuits beyond the `Q_c` (S40(iv), unproved).
- S33–S34 are readings of S22/S25/S28 at arbitrary `M` (audited S38(ii)); the strict habitat count's "tight and sparse ⟹ rigid" is re-derived, not checked against a source.
- The Macaulay2 record tests no Case-2 core (S27(vi)); no variety-level control exists for any O7e-c stratum.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (O7e-c's break is new and specific — the `Q_c` degenerations and the centre with a non-big neighbour, S41(iv); O7e-b(a)'s part is unchanged)
- Open obligations: 4 (trend: 2 → 4 → 4 — the rise at session 13 is the count by piece; flat since, with O7e-c restated from "needs its own order and count" to (★₂) at depth `≥ 2` and its `M₀` part closed on one shape)
