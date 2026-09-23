# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 13 · last session: 2026-09-23 (session 13; S32–S36) · review 4: 2026-09-23 (S23; *continue on R2*) · baseline HEAD: 907f521a · **count 2: O7e-b (now one counting statement, S34(iv)), O7e-c** · consumer unchanged (`git diff 084ee4ff HEAD -- CombinatorialRigidity` empty; kernels token-identical to brief §3.1) · **review 5 due** · **next: the class-pricing lemma S35(iv), cases S36(iii)(a)–(b)**

## Statement <!-- budget 10 -->
The two kernels of `pencilPair_of_splitOff_of_habitat` (`Escape.lean`, verbatim in brief §3.1; re-diffed at session 13, no Lean change since `084ee4ff`). For `G : Graph α β` and `v a b`, `eₐ e_b e₀` with `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid subgraph (`IsProperRigidSubgraph _ G 3` — a *proper vertex subset*), `G.degree v = 2`, `eₐ ≠ e_b`, `G.IsLink eₐ v a`, `G.IsLink e_b v b`, `¬ PencilHub a ∨ ¬ PencilHub b`, `e₀ ∉ E(G)`, and the IH `∀ G', V(G').Nonempty → |V(G')| < |V(G)| → PencilPair K 3 G'`:
- **`hK`:** `HasGenericPencilRealization K 3 (G.splitOff v a b e₀) → HasGenericPencilRealization K 3 G`; no feasibility hypothesis (D1, S16(i)/(v)).
- **`hbareSplit`:** additionally `¬ PencilNondegFeasible K G`; `HasDistinctPencilRealization K 3 (G.splitOff …) → HasDistinctPencilRealization K 3 G`.
Domain split (exhaustive, S19): (i) `G = C_n`, `n ≥ 5`; (ii) one hub `w`, `G = H″ ∪_w C_{m+1}`, `m + 1 ≥ 7`; (iii) two hubs, `G = H′ ∪ ear_m`, `m ≥ 2`, `G.splitOff = H′ ∪ ear_{m−1}`. Cases (i)–(ii) reach the kernels because the cut arm is `¬ TwoEdgeConnected` (S18(i)). The domain contains rigid `G` (`C₅`, `C₆`, `θ(5,3,4)`); the route needs no positivity (S14(iii)'s cell `g′ = 0`). Marked set `Z = hubs(G)`; Case 2 for `(H′, Z)` ⟺ `¬ PencilNondegFeasible K G` (S19(vii)(c)). Field `[Infinite K]`, no characteristic.
Unused: `eₐ ≠ e_b`, `e₀ ∉ E(G)` — well-formedness of `splitOff` only. In case (iii) at `m ≥ 6` the IH is unused by `hK` and the antecedent by `hbareSplit` (S17(v)); in cases (i)–(ii) `hbareSplit` is vacuous for cycles and both kernels are pointwise (S20).

## Current route and proof sketch <!-- budget 30 -->
**Route R2 — the split-off antecedent and the IH as certificates for the generic point** (S14, S16, S17, S19–S22, S25–S36). Status by cell:
- **Case (iii), `hK`, all `m` — closed modulo O9 (written, S16(vi)).** `m ≥ 6` pointwise (S17(v)(b)); `m ≤ 5` Case 1 for `H′`, (★) by S19, S14(iii) at the generic point, O9 for the `K`-point.
- **Case (iii), `hbareSplit`, `m ≥ 5` — closed (S17(v)(a)).**
- **Case (iii), `hbareSplit`, `m ≤ 4` — OPEN.** `H′` is Case 2 (S19(vii)(c)); S14(iii) needs `X̄(H′)` irreducible, i.e. (★₂) on S21(ii)'s tower: at a big-point stratum with matroid `M`, `cost − J₃ ≥ −s`, `s := c₁ − J₂ − 1`. Generic big points: S22. One relation: S25–S30.
- **Cases (i)–(ii) — closed (S20(ii)–(iv))**; **characteristic — closed (S20(i))**.
- **Several relations — reduced to one counting statement (session 13):**
  - *Components (S32).* Relations = circuits of `M` of size `≤ 4`; their connected components `R` have ranks adding exactly (S32(i)), so `c₁ ≥ Σ_R c₁(R)`, `J₂ = Σ_R J₂(R)`, and `b_R := c₁(R) − J₂(R) ≥ 1` (S21(v) per component). *Reduction:* damage `≤ Σ_{R touched} b_R − ½` gives (★₂) by integrality (S32(iii)). The closed single relations all have damage `≤ b − ½`, with equality at the far coincidence, the star-free triple and the quadruple.
  - *Damage list at any `M` (S33–S34).* `Dmg = Σ_A (disc_A + Δᴹ_A/2 − S_A)⁺ + k₃ + Σ_C (D_C − cost_C)⁺ + k₆/2`: class term, O3 paths between parallel labels (the only line loss, S33(i)), extras overflow (only through parallel servers or a plane with many served extras, S33(ii)–(iii)), free singleton `M`-natural incidences. Exact class identity: `−T_A = (3 − rk U_A) + J^{nb}_A + F_A + (Δ_A + Δᴹ_A)/2 − Σ_c (3 − r_c)` (S34(i)).
  - *Prices (S35).* The strict count in path-graph form, `Σ_p (6 − ℓ_p) ≤ 6|B| − 7`; every listed unit has a witness and a price, twin units at damage/price `≤ ½`, all others `≤ ⅛`; this reproduces S25(vi), S28(vi) (sharper), S30(ii). The test cluster (coincidence + collinear triple through `q*`, `b = 5`) closes at `Dmg ≤ 4` **modulo the class lemma** and cross-relation price additivity (S35(iii)).
- **Core reduction (S27(vi)).** O7e may assume Γ is its own 2-core with a vertex of core-degree `≥ 3`.
Open obligations (each is `hbareSplit` at `m ≤ 4` in case (iii): its hypothesis `¬ PencilNondegFeasible K G` forces `H′` into Case 2, and S14(iii) is applied at the generic point of `X̄(H′)` to the IH's Distinct witness for `H′` and to the antecedent `HasDistinctPencilRealization K 3 (G.splitOff …)`):
- **O7e-b — the counting statement S34(iv):** for every point matroid `M` with `k_c ≤ 3` and every realisable pattern, `Dmg ≤ Σ_{R touched} b_R − ½`. *Consumed because:* a degenerate `q` is a tower stratum like any other; a component of `X̄(H′)` over it would break irreducibility. Pieces: (a) the class lemma S35(iv) — its no-charge, `J^{nb}_A = 0` case proved (S36(i)–(ii): damage `≤ 1`, all-tight rank-2 classes only, priced at `⅛`/`½`); (b) prices add across relations of one cluster; (c) per cluster, max damage under the slack `6|B₀| − 7` is `≤ b_R − ½` (type-sensitive: coplanar units need their hub's fixed price, S35(ii)).
- **O7e-c — sides with some `k_c ≥ 4`** (S21(vii)(c)): the three-level order fails; another 3-degenerate order (S21(i)) needs its own count. *Consumed because:* a big hub with three big Γ-neighbours is habitat-legal with long paths (S23(iii)); on a 2-core it needs four adjacent vertices of core-degree `≥ 3`.
Closed: O7d (S19); O10, O11 (S20); O7c (S17); O7e-a (S22); O7e-b's six single relations (S25, S26, S28–S30); O7 at `m ≥ 5`/`m ≥ 6` (S17(v)); O9 written (S16(vi)).

## Where it breaks <!-- budget 10 -->
**The class term at an arbitrary `M` is not yet priced** (S35(iv)): no lemma yet shows `(disc_A + Δᴹ_A/2 − S_A)⁺ ≤ ⅛ · price(A)` (bad pairs over a twin pair at `½`), where `price(A)` is the slack of the paths attaching `A`'s members to the labels of `U_A`. The tool is S34(i)'s identity written as `damage_A = (3 − rk U_A) + J^{nb}_A + (Δ_A + Δᴹ_A)/2 − Σ_{c ∈ A} ε_c`, `ε_c := 3 − r_c − [c flat] ≥ 0`: only *tight* members (`ε_c = 0`: big with `r_c = 3`, or flat non-big with `r_c = 2`) fail to pay for themselves, and each attaches to two labels by edges (price `≥ 4` per length-2 label–member–label path). The two places it can go wrong: `J^{nb}_A` (members sharing non-big neighbours; bound it by Lemma P's strict count on `Γ_A`) and `Δᴹ_A` beyond `g_A` (several `y ∈ cl(U_A) ∖ U_A` per big member, e.g. `U_A ∩ R = {u, b}` on the test cluster gives `y ∈ {u′, d}`). The case `Δᴹ_A = 0 = J^{nb}_A` is proved (S36(i)–(ii)). **Concrete next step:** S36(iii)(b) — `M`-natural charges from big members, priced relative to `B₀ ∪ (A ∩ Big)` with `S_A` paying `½` per charge from a big member outside `B₀` (S25(iv)'s arithmetic, now with several `y` per member); then (iii)(a) by Lemma P on `Γ_A`; land as S37.

## Tried on this route, and what each rules out <!-- budget 10 -->
- Per-label budgets charged to the last label of each circuit (session 13): rules out label-local budgets (a centre label can have `κ − j = −1`); components replace them (S32).
- One uniform ratio `⅛` for non-twin units (session 13): rules out a type-blind count on coplanar clusters of `≤ 10` labels; the hub's fixed price `10` is needed (S35(ii)).
- Summing S28(vi)'s per-triple `k₁ ≤ 1` over a cluster (session 13): rules out cluster-level `k₁ ≤ 1` (two collinear bad pairs on an 8-cycle, S35(iii)).
- S28's rank reading (session 12): rules out a separate charging of the line through `λ₀`; now used at every `M` (S33).
- `case2deg.py --collinear` / `--pair` (sessions 11–12): no negative slack on thirteen single-relation runs, exact below caps (S27(ii), S31(ii)); damage shapes never occurred on those graphs.
- `case2m2.py` (sessions 9, 11): every PASS is a tree or a `C₇` core; no Case-2 core is within reach (S27(vi)); rules out nothing about Case 2.
- `case2geo.py` (session 10): no pattern with `M + ρ ≤ J₃` at generic `q` on twelve graphs.
- Lines-first count and one-sided `w_{ab}` charging (session 10): rule out replacing the sequential cost.

## Next steps <!-- budget 5 -->
1. **Session 14: S37, the class lemma with `M`-natural charges** (S36(iii)(b)), then `J^{nb}_A ≥ 1` (S36(iii)(a)), then the test cluster in full.
2. O7e-b piece (c): the per-cluster inequality by cluster type (twins at `½`, collinear at `⅛`, coplanar with hub price); piece (b) price additivity across relations.
3. **Review 5 is due** (sessions 11–13 since review 4): whether S34(iv) is the right single statement; whether S32's `b_R ≥ 1` via S21(v)/S19 needs S19 reviewed first; S29–S30 audit.
4. **O7e-c:** with Γ its own 2-core, bound by the strict count which cores have a vertex with three big neighbours; then the 3-degenerate order for those shapes.
5. **Lean round (PI-directed):** S20(v)'s pointwise skeleton — unchanged.

## Worries <!-- budget 5 -->
- S32's `b_R ≥ 1` and every degenerate-stratum count lean on S21(v), i.e. S19 by duality — S19 is still unreviewed, and S21(v) is quoted for the *true* codimension `c₁(R)`.
- S33–S34 are readings of S22/S25/S28 at arbitrary `M`, like S28(ii); S27(i)'s lesson says each needs a fresh-reader audit before it is relied on.
- The strict habitat count (S19(viii)) is load-bearing everywhere; "tight and sparse ⟹ rigid" is re-derived, not checked against a source.
- The Macaulay2 record tests no Case-2 core (S27(vi)); only the stratum drivers target Case 2, and they check counting, not the variety.
- Sessions 8–13 have landed ~1 150 workbook lines; S25–S35 are unreviewed by a `/review-attack` pass.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (moved from "no lemma bounds the damage for arbitrary `M`" to the class-pricing lemma, by S32–S36; the line, extras and free-incidence terms are priced, and the class term without charges or shared non-big neighbours)
- Open obligations: 2 (trend over the last three sessions: 2 → 2 → 2 — flat by count; O7e-b narrowed from a list of relation shapes to one counting statement with three named pieces)
