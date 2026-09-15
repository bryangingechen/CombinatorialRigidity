# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 2 · last session: 2026-09-15 · baseline HEAD: eeb413eb

## Statement <!-- budget 10 -->
`G` 2-connected of girth `≥ 5`, `{u,v}` a 2-separation with `u ≁ v`, sides `H₁, H₂`; `ϕ` a *generic* flag pair (`p_u ≠ p_v`, `π_u ≠ π_v`, `p_v ∉ π_u`, `p_u ∉ π_v`). Assume for `i = 1,2` that `Y°(H_i; ϕ)` has an irreducible component `Y_i` at whose generic point `H_i` attains and `H_i/uv` attains (`a_i = 0`, `ρ_i = δ_i`). Then the generic point of `Y₁ ×_ϕ Y₂` has `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)`; so `G` attains ((BE-86)(i), re-derived).
Changes from the brief's Lemma, and why: (1) girth `≥ 5` (brief §6 idea 1; the Lean consumer `hbareSplit` in `Escape.lean` has girth `≥ 7`, confirmed at its statement, so nothing consumed is lost); at girth `≥ 5` the coplanarity closure never forces `π_u = π_v`, the only reason the brief weakened to `a_i > 0`. (2) `ϕ` is a fixed generic pair, not "some `ϕ`", and `a_i = 0` is restored; whether generic `ϕ` is *legal* for a side is an induction-frame obligation (Worries), not this lemma's. (3) The incident case `u ~ v` is deferred (O6). Unchanged in session 2. The **consumed instance** is `H₂ = ear1` (the degree-2 vertex `x` of `hbareSplit`, `H₁ = G − x`, `dist(u,v) ≥ 5`); S9 gives it in closed form.

## Current route and proof sketch <!-- budget 30 -->
**Route R1 — gauge-group transversality by orbit strata, then per-side profiles.** Proofs in `notes/pencil/workbook/attack-smark.md` (S1–S9; no labels minted, the brief assigns no prefix). Frame = BUNIF's ((BE-94)): blocks `⟨M⟩, Π_u, Π_v, ⟨L⟩` of `Λ²K⁴`, stabiliser `S(ϕ)` of dimension 5 acting on side 2 alone.
- **S1–S4 (session 1, done).** Semi-invariant quadrics `Q₁ = x_M x_L`, `Q₂ = det[x_u|x_v]`, Klein form `Q₁ − Q₂`; 19 orbit strata. **S2:** if the 16 block inequalities `c_A(U) + c_B(U) ≤ dim U` hold and the pair avoids four isotropy exceptions (X1)–(X4), then `A ∩ gB = 0` for generic `g ∈ S(ϕ)` (incidence count `≤ 4 < 5`). **S3:** dual/unified form: block inequalities with slack `max(0, ρ₁+ρ₂−6)` + no exception ⟹ `dim(A + gB) = min(6, ρ₁+ρ₂)` — the `⟸` of (BE-96)(iv), a theorem outside (X1)–(X4). **S4:** two stars satisfy every block inequality yet always meet (Klein parity): the block list is incomplete; (X1) same-family is a real obstruction.
- **S5 (reduction, done).** The Lemma holds at `(G; u, v)` as soon as the generic side profiles satisfy the 14 inequalities and the pair avoids (X1)–(X4); openness on the attaining locus turns one good pair into the generic point.
- **S6 (session 2, done) — side-degree 1 at `u`, neighbour `w`.** `ρ̄_{uv}(H) = ρ̄_{wv}(H−u) + K·L_{uw}`; `f = f'+1`, `g = max(g', f'−5)`, `δ = min(δ'+1, 6)`; `H` attains iff `H−u` does; **`H` welded-attains iff `H−u` welded-attains at `(w,v)` and `L_{uw} ∉ ρ̄_{wv}(H−u)`** (or `δ' = 6`). Profile transfer: `c(U) = c'(U)+1` for `U ⊇ Π_u`, else `c(U) = dim(ρ̄' ∩ (U ⊕ K L_{uw}))` — a block sum plus one pencil line, off the block lattice of `(p_w, π_w; p_v, π_v)`.
- **S7 (done) — excess is attainment loss.** `c(U) = dim M(H ∪ bars(U^⊥)) − dim M(H/uv)`: the `U`-joint is `6 − dim U` bars between bodies `u, v` along lines spanning `U^⊥` (every block sum is spanned by lines). **No excess at `U` ⟺ the bar-augmented side attains its Tay count.** Excess is Klein-self-dual (`(ρ̄, U) ↔ (T, U^⊥)`, `T = ρ̄^⊥` the transmissible wrenches). **Witness principle:** one exact configuration certifies attainment, welded attainment and upper bounds on all 16 `c(U)` for every component through it (upper semicontinuity).
- **S8 (done).** Sides without interior hubs have irreducible `Y°(H; ϕ)`; so the session-1 ear and theta rows are theorems for the whole fibre (ears: excess `Π_u, Π_v: 1` at `m ≤ 3`, plus the `m ≤ 2` blocks; thetas/dumbbell: no excess); `tail`, `cycletail` rows are theorems for their component.
- **S9 (done) — the `ear1` criterion, an equivalence.** With `A' := ρ̄₁ ∩ (Π_u ⊕ Π_v)`: for `δ ≤ 4`, `G = H ∪ ear1` attains at the generic point iff `dim A' ≤ 2` and `A'` is not a ruling plane `y ∧ W` (`y ∈ M`; `y = p_u` is `A' = Π_u`); for `δ = 5` iff `dim A' ≤ 3`; `δ = 6` always. And `dim A' = δ − 2 + dim(T₁ ∩ ⟨M, L⟩)`: the dimension clause is **"no nonzero wrench `αM + βL` is transmissible through `H`"** (`δ ≥ 4`; at `δ = 3`, not both `M, L`). `⟨M,L⟩ = (Π_u ⊕ Π_v)^⊥` is exactly the set of wrenches every terminal hinge passes.
Open obligations:
- **O4** Per-side bounds — now: attainment of `H ∪ bars(U^⊥)` for the block sums `U` where the pair has no slack (slack `= dim U + max(0,Σδ−6) − Σ_i max(0, δ_i + dim U − 6)`; tightest at `dim U = 5`, slack 1 at `Σδ = 6`). For the consumed shape: `T(G−x; u,v) ∩ ⟨M,L⟩ = 0` and `A' ≠ y ∧ W`, for `G − x` connected, girth `≥ 7`, `dist ≥ 5`.
- **O5** Pair conditions for two general sides (combine O4 with the slack table; (X1)–(X4) avoidance). Absorbed into O4 when one side is `ear1`.
- **O6** The incident case `u ~ v`: `S(ϕ)` of dimension 7; redo S1–S3.

## Where it breaks <!-- budget 10 -->
**O4, general sides.** S7 shows O4 is a rigidity statement of the *same type as the target*: attainment of a body–bar–hinge framework built from a pencil configuration (side + bars along the flag lines). For the consumed shape it is one clean claim, `T(H; u, v) ∩ ⟨M, L⟩ = 0` at generic `ϕ` for `dist(u,v) ≥ 4` — measured on 19/19 such sides (114 draws, `earone.py`), with a transparent mechanism **only for paths** (a wrench of `⟨M,L⟩` passes every terminal hinge; two interior hinges in general position cut the 2-plane to `0`); for a general side `T` strictly exceeds the path-generated `Σ_P span(P)^⊥` and nothing bounds it.
No induction on the side closes: (a) peeling a side-degree-1 terminal (S6(iv)) moves the question to `ρ̄' ∩ (U ⊕ K·L_{uw})`, off the block lattice of the new flag pair; (b) peeling a hub terminal, or cutting at an internal 2-cut `{x,y}`, needs the transmission space from several neighbours to `v` (multi-terminal), which `ρ̄`/`T` do not carry; (c) series composition composes (`T = T₁ ∩ T₂`, so `T ∩ ⟨M,L⟩ ⊆ T₁ ∩ ⟨M,L⟩`) but **parallel composition is `T = T₁ + T₂`, which is the Lemma itself**; (d) collapsing degree-2 paths to chain joints turns `H` into a body–bar framework on its hubs, and O4 into the generic-rank statement for that non-generic framework.
Concrete first target for a fresh reader: prove `T ∩ ⟨M,L⟩ = 0` at `dist ≥ 4` for **series–parallel** sides by finding the invariant of `(T; u, v; ϕ_u)` that survives the parallel rule — the one-flag statement "`T(H; u, z)` meets `⟨M', L'⟩` trivially for generic `M' ∋ p_u`, `L' ⊂ π_u`" composes under series and is where to start.

## Tried on this route, and what each rules out <!-- budget 10 -->
- Incidence count over orbit strata (S2, session 1): rules out "the gauge group is too small" — only the four isotropy exceptions escape the count.
- Two-stars pair (S4, exact, 20 × 30): rules out "the 16 block inequalities are sufficient" — Klein parity lies outside the block list.
- Side-profile battery, 11 sides × 6 draws (S5, seed 20260915; now theorems by S7(vi)/S8): rules out excess at a side-degree-2 terminal **for those sides**; shows (X4)'s shape is realised (`ear1`), so (X4) stays a hypothesis of S2.
- Widened battery, 12 sides × 6 draws (`sideprof.py --side all2`, seed 20260915; hub terminals of side-degree 3–4, mixed 3/1 and 3/2, two interior hubs, `dist` up to 6): no excess except the side-degree-1 hinge `Π_v: 1` on `hubpend`, `hubpend2`; rules out "excess at a hub terminal" and "excess from interior hubs" **within the 23 named sides** (caps `s = 20`, 6 draws) — not found, not a theorem.
- `earone.py`, 23 sides × 6 draws × 3 `p_x` (seed 20260915): S9's predicted verdict = exact rank of `H + x` at 138/138, both S7/S9 identities asserted at every draw; rules out a hidden case in S9's proof within the population; `T ∩ ⟨M,L⟩ ≠ 0` only at `dist ≤ 3`.
- Reading `Deficiency.lean` (`bodyBarDim n = n(n+1)/2`): `def₂` is the planar count `3(|P|−1) − 2d(P)`, so `C_n` has `def₂ = n−3 > n−6 = def₃`; rules out the flat witness (brief §3(a), (c)) as a substitute for the Lemma on the consumed class.

## Next steps <!-- budget 5 -->
1. Attack `T ∩ ⟨M,L⟩ = 0` at `dist ≥ 4` for series–parallel sides: state the one-flag invariant, prove it composes under series (`∩`) and find what extra datum makes it survive parallel (`+`); a proof for thetas-of-thetas is the milestone.
2. Adversarial controls on the `dist ≥ 4` law (cheap, before proving): a rigid `C₅` at `u` with `dist ≥ 4` (cycletail stretched), a side with a bridge near `v`, and random girth-`≥ 5` sides on `≤ 12` vertices via `sideprof`'s sampler; one `T ∩ ⟨M,L⟩ ≠ 0` at `dist ≥ 4` would refute S9's clean form for the consumed shape.
3. O6: the 7-dimensional `S(ϕ)` at `u ~ v` and its strata; the S2 count should go through with more special orbits.
4. Ask the reviewer (review due: route refinement proposed) whether R1's O4 should be narrowed to the consumed shape (S9) or restated with a multi-terminal invariant; the general 2-cut Lemma is still needed by the global induction for `G − x`, so narrowing alone does not close the consumer.

## Worries <!-- budget 5 -->
- Frame: generic `ϕ` legal for each side, and welded attainment supplied by the induction — S6(iii) shows welded attainment at a side-degree-1 terminal needs `L_{uw} ∉ ρ̄_{wv}(H − u)`, a real condition the induction must carry; 3-connected pieces attain at the *flat* configuration and `K₄` only there. Not this lemma's, but it is vacuous without it.
- R1 may have made the target one-sided without making it easier: O4 is target-type (S7). If session 3 finds no composable invariant, the route should be judged at review, not pushed.
- S2's exceptions (X2)–(X4) are proof artefacts; a real pair landing in one needs a direct argument there. (BE-96)(iv)'s criterion in BUNIF is incomplete (S4); PI decides whether to annotate.
- Characteristic 0, `K` algebraically closed for the generic-point arguments; descent to the Lean field unchecked (brief §3); the 5-rows-per-hinge matrix against `rigidityRows` unchecked.
- The 23-side population has at most two interior hubs and no 3-connected chunk; the `dist ≥ 4` law has not been tested where `T` is far from path-generated.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0
- Open obligations: 3 (trend over the last three sessions: flat — 7 at the start of session 1, 3 at its end, 3 now; O4 restated, not discharged)
