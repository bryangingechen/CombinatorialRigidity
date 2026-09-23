# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 12 · last session: 2026-09-23 (session 12; S28–S31, one result at a time) · review 4: 2026-09-23 (S23; *continue on R2*) · baseline HEAD: 9b93f770 · **count 2: O7e-b (now only several relations at once), O7e-c** — every single big-point relation closed (S25, S26, S28–S30) · consumer unchanged (`git diff 084ee4ff HEAD -- CombinatorialRigidity` empty; kernels token-identical to brief §3.1) · **next: the multi-relation damage lemma (*Where it breaks*)**

## Statement <!-- budget 10 -->
The two kernels of `pencilPair_of_splitOff_of_habitat` (`Escape.lean`, verbatim in brief §3.1; re-diffed at session 12, no Lean change since `084ee4ff`). For `G : Graph α β` and `v a b`, `eₐ e_b e₀` with `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid subgraph (`IsProperRigidSubgraph _ G 3` — a *proper vertex subset*), `G.degree v = 2`, `eₐ ≠ e_b`, `G.IsLink eₐ v a`, `G.IsLink e_b v b`, `¬ PencilHub a ∨ ¬ PencilHub b`, `e₀ ∉ E(G)`, and the IH `∀ G', V(G').Nonempty → |V(G')| < |V(G)| → PencilPair K 3 G'`:
- **`hK`:** `HasGenericPencilRealization K 3 (G.splitOff v a b e₀) → HasGenericPencilRealization K 3 G`; no feasibility hypothesis (D1, S16(i)/(v)).
- **`hbareSplit`:** additionally `¬ PencilNondegFeasible K G`; `HasDistinctPencilRealization K 3 (G.splitOff …) → HasDistinctPencilRealization K 3 G`.
Domain split (exhaustive, S19): (i) `G = C_n`, `n ≥ 5`; (ii) one hub `w`, `G = H″ ∪_w C_{m+1}`, `m + 1 ≥ 7`; (iii) two hubs, `G = H′ ∪ ear_m`, `m ≥ 2`, `G.splitOff = H′ ∪ ear_{m−1}`. Cases (i)–(ii) reach the kernels because the cut arm is `¬ TwoEdgeConnected` (S18(i)). The domain contains rigid `G` (`C₅`, `C₆`, `θ(5,3,4)`); the route needs no positivity (S14(iii)'s cell `g′ = 0`). Marked set `Z = hubs(G)`; Case 2 for `(H′, Z)` ⟺ `¬ PencilNondegFeasible K G` (S19(vii)(c)). Field `[Infinite K]`, no characteristic.
Unused: `eₐ ≠ e_b`, `e₀ ∉ E(G)` — well-formedness of `splitOff` only. In case (iii) at `m ≥ 6` the IH is unused by `hK` and the antecedent by `hbareSplit` (S17(v)); in cases (i)–(ii) `hbareSplit` is vacuous for cycles and both kernels are pointwise (S20).

## Current route and proof sketch <!-- budget 30 -->
**Route R2 — the split-off antecedent and the IH as certificates for the generic point** (S14, S16, S17, S19–S22, S25–S30). Status by cell:
- **Case (iii), `hK`, all `m` — closed modulo O9 (written, S16(vi)).** `m ≥ 6` pointwise (S17(v)(b)); `m ≤ 5` Case 1 for `H′`, (★) by S19, S14(iii) at the generic point, O9 for the `K`-point.
- **Case (iii), `hbareSplit`, `m ≥ 5` — closed (S17(v)(a)).**
- **Case (iii), `hbareSplit`, `m ≤ 4` — OPEN.** `H′` is Case 2 (S19(vii)(c)); S14(iii) needs `X̄(H′)` irreducible, i.e. (★₂) on S21(ii)'s tower: `codim_T Σ ≥ J₂ + J₃ + 1` off the generic stratum. Generic big points: S22. Degenerate big points, one relation: S25–S30.
- **Cases (i)–(ii) — closed (S20(ii)–(iv))**; **characteristic — closed (S20(i))**.
- **The degenerate-stratum method (S25–S30).** A stratum with point matroid `M` of level-1 codimension `c₁` and forced jumps `J₂` needs `cost − J₃ ≥ −s`, `s := c₁ − J₂ − 1`. Read S22's ledger in **ranks** (S28(i)): `cost − J₃ = Σ_A (σ_A − F_A − disc_A) + Σ_ℓ N_ℓ + Σ_C cost_C`, `disc_A = def(U_A) − Σ_{c ∈ A} def(U_c)`; incidences split into normal / `M`-natural / extra. Three robust facts: **an extra serves at most one flat** (S28(iii), any `q`: two would force `π_{[y]} = π_C`), so `Σ(cost_C − D_C) ≥ 0` whenever each served extra adds rank; **lines lose only at coincidences** (S25(iii)'s O3; S28(iv)); `M`-natural charges on nontrivial classes are absorbed when they force `disc_A = 0` and number `≤ g_A` (S25(iv), S28(v)). The damage is then `disc` on bad pairs (`k₁`), free `M`-natural incidences on singletons (`½` each, `k₆`), O3 lines, and extras overflow.
- **Single relations, all closed:** coincidence at distance `≥ 3` (S25, damage `≤ 2 = s`), `2` and adjacent (S26, `0`), collinear triple without star (S28: `k₁ ≤ 1`, `k₆ ≤ 1`, `≤ 3/2`, so `≥ −1` by integrality) and with star (S29, `0`), coplanar quadruple (S30, `k₆ ≤ 1`, `½ < 1`). S28 audited by a fresh reader, no miss (S31(i)); collinear control PASS (S31(ii)).
- **Core reduction (S27(vi)).** O7e may assume Γ is its own 2-core with a vertex of core-degree `≥ 3`.
Open obligations (each is `hbareSplit` at `m ≤ 4` in case (iii): its hypothesis `¬ PencilNondegFeasible K G` forces `H′` into Case 2, and S14(iii) is applied at the generic point of `X̄(H′)` to the IH's Distinct witness for `H′` and to the antecedent `HasDistinctPencilRealization K 3 (G.splitOff …)`):
- **O7e-b — (★₂) at big points satisfying several relations** (`k_c ≤ 3`). *Consumed because:* a degenerate `q` with two or more relations is a tower stratum like any other; a component of `X̄(H′)` over it would break irreducibility.
- **O7e-c — sides with some `k_c ≥ 4`** (S21(vii)(c)): the three-level order fails; another 3-degenerate order (S21(i)) needs its own count. *Consumed because:* a big hub with three big Γ-neighbours is habitat-legal with long paths (S23(iii)); on a 2-core it needs four adjacent vertices of core-degree `≥ 3`.
Closed: O7d (S19); O10, O11 (S20); O7c (S17); O7e-a (S22); O7e-b's six single relations (S25, S26, S28–S30); O7 at `m ≥ 5`/`m ≥ 6` (S17(v)); O9 written (S16(vi)).

## Where it breaks <!-- budget 10 -->
**O7e-b with several relations: no lemma yet bounds the damage by `s = c₁(M) − J₂(M) − 1` for an arbitrary point matroid `M`.** The per-relation proofs used local slack budgets `c₁ − J₂ − ½ ≥ damage` (coincidence far `3 ≥ 2.5`, collinear `2 ≥ 1.5`, coplanar `1 ≥ ½`, star/adjacent/distance-2 `≥ ½ ≥ 0`); if (a) `c₁` and `J₂` were additive over a decomposition of `M`'s relations into clusters and (b) every damage unit were local to one cluster, integrality would close O7e-b (`damage ≤ Σ(c₁ⁱ − J₂ⁱ) − k/2 < s + 1`). Both fail as stated: `c₁` is not additive over dependent relations (a collinear triple implies every coplanarity containing it), and one damage shape can use two relations (a class whose `U_A` has `disc_A ≥ 2`, e.g. seeing a coincident pair *and* a collinear triple; an `M`-natural charge on a class that also has `disc_A ≥ 1`, which S25(iv)/S28(v) never face). **Concrete first step:** state the damage per class as `(disc_A + Δᴹ_A/2 − (σ_A − F_A − Δ_A/2))⁺` and prove `disc_A ≤ c₁(M|_{U_A}) − J₂(M|_{U_A})`-type bounds with `M|_{U_A}` restricted to the class's labels, then assign each relation to at most one damaging class or singleton by a girth count (land as S32); the first test case is a coincidence `q_u = q_{u′}` plus a collinear triple through `q*`.

## Tried on this route, and what each rules out <!-- budget 10 -->
- S28's rank reading (session 12): rules out that the collinear triple needs a separate charging of the line `ℓ₀` through `λ₀` — the rank values price those classes at `0`, their true cost; and rules out damage from extras there (an extra serves at most one flat, S28(iii)).
- Fresh-reader audit of S28 (session 12, helper): 17 steps of S22/S25 examined, no miss, two slips repaired (S31(i)); S29–S30 not audited separately (they reuse S28's lemmas plus girth counts).
- `case2deg.py --collinear` (session 12, helper-written, adopted): rules out `cost − J₃ < J₂ − 1` on D3r, E15, E55 (star-free, min slack `1`) and T8 (star, min `0`), exact below caps (S31(ii)); every minimum at trivial or forced-line patterns — the damage shapes never occur on these graphs.
- `case2deg.py --pair` (session 11): coincidence strata of nine graphs, min slack `2` (distance `≥ 3`), `1` (distance 2), over ℚ under README caps (S27(ii)).
- Fresh-reader audit of S25(ii) (session 11): found (L6)/O6, repaired (S27(i)); the lesson that each new spot list gets an audit held for S28.
- `case2m2.py` (sessions 9, 11): every PASS is a tree or a `C₇` core; no Case-2 core is within reach (S27(vi)); rules out nothing about Case 2.
- `case2geo.py` (session 10): no pattern with `M + ρ ≤ J₃` at generic `q` on twelve graphs; tight shapes exactly S22(viii)'s three.
- Lines-first count and one-sided `w_{ab}` charging (session 10): rule out replacing the sequential cost, and a `1`-per-charge bound from the strict count (`0.75`).
- `unitcert.py`, `starcomb.py`, `starcheck.py` (sessions 7–8): certificate (A); S19's four links; (★) in Case 1.

## Next steps <!-- budget 5 -->
1. **Session 13: S32, the multi-relation damage lemma** (*Where it breaks*), test case coincidence + collinear through `q*`; control first: a `case2deg.py` mode taking a list of relations (pair and triple together), on D3r or E55.
2. If S32's cluster assignment stalls, the named alternative is a plane-first (★) in `P³*` with rank-3 flats of normals as pattern elements (S19's calculus plus "points"), which treats every `M` at once.
3. **O7e-c:** with Γ its own 2-core, bound by the strict count which cores have a vertex with three big neighbours; then the 3-degenerate order for those shapes.
4. **Review 5 is due** (three sessions since review 4 is session 13; the break moved twice). It should decide whether O7e-b is now one obligation (several relations) and whether S29–S30 need their own audit.
5. **Lean round (PI-directed):** S20(v)'s pointwise skeleton — unchanged.

## Worries <!-- budget 5 -->
- S28(ii)'s spot list is a reading of S22; its audit found no miss, but S29–S30 were not audited separately and each rests on a girth enumeration done once.
- S25(iv)/S28(v)'s fractional arithmetic (`T_A ∈ ½ℤ`) is re-checked by two readers now, but the multi-relation case will stress it (`disc_A ≥ 1` together with `M`-natural charges).
- The Macaulay2 record tests no Case-2 core (S27(vi)); only the stratum drivers target Case 2, and they check counting, not the variety.
- The strict habitat count (S19(viii)) is load-bearing everywhere; "tight and sparse ⟹ rigid" is re-derived, not checked against a source.
- Sessions 8–12 have landed ~950 workbook lines; S25–S30 are unreviewed by a `/review-attack` pass.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (moved from the collinear triple to several relations, by the proofs S28–S30; not a rename)
- Open obligations: 2 (trend over the last three sessions, by piece: 2 → 2 → 2 — flat by piece, falling by relation: O7e-b went from four open relation-pieces to one)
