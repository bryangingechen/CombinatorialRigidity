# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 2 · last session: 2026-09-15 · baseline HEAD: eeb413eb · re-oriented at the first `/review-attack` (2026-09-15, PI-directed); session 3 verifies S10 before building on it

## Statement <!-- budget 10 -->
`G` 2-connected of girth `≥ 5`, `{u,v}` a 2-separation with `u ≁ v`, sides `H₁, H₂`; `ϕ` a *generic* flag pair (`p_u ≠ p_v`, `π_u ≠ π_v`, `p_v ∉ π_u`, `p_u ∉ π_v`). Assume for `i = 1,2` that `Y°(H_i; ϕ)` has an irreducible component `Y_i` at whose generic point `H_i` attains and `H_i/uv` attains (`a_i = 0`, `ρ_i = δ_i`). Then the generic point of `Y₁ ×_ϕ Y₂` has `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)`; so `G` attains ((BE-86)(i), re-derived at review, workbook S10(ii)).
Changes from the brief's Lemma, and why: (1) girth `≥ 5` (brief §6 idea 1); at girth `≥ 5` the coplanarity closure never forces `π_u = π_v`, the only reason the brief weakened to `a_i > 0`. (2) `ϕ` is a fixed generic pair, not "some `ϕ`", and `a_i = 0` is restored; whether generic `ϕ` is *legal* for a side is an induction-frame obligation (Worries), not this lemma's. (3) The incident case `u ~ v` is deferred (O6).
**Consumed instance (corrected at review):** `hbareSplit` (`Escape.lean:467`) also carries `¬ PencilHub a ∨ ¬ PencilHub b` — one neighbour of the degree-2 vertex has degree exactly `2` — so the consumed shape is `G = H′ ∪ ear_m` at a **hub** 2-cut `{w, v}`, `m ≥ 2` interior vertices, `w ≁ v`, `H′ = G − chain` connected with side-degree `≥ 2` at both ends, `dist_{H′}(w, v) ≥ 6 − m` (brief §3 *Consumed shape*). The one-vertex ear between two hubs (S9) is *not* consumed. Girth is `≥ 7` unless `G ∈ {C₅, C₆}` (base case (b)).

## Current route and proof sketch <!-- budget 30 -->
**Route R1 — gauge-group transversality by orbit strata, then per-side profiles at the hub cut.** Proofs in `notes/pencil/workbook/attack-smark.md` (S1–S9 the attack's; S10 the reviewer's, unverified; no labels minted, the brief assigns no prefix). Frame = BUNIF's ((BE-94)): blocks `⟨M⟩, Π_u, Π_v, ⟨L⟩` of `Λ²K⁴`, stabiliser `S(ϕ)` of dimension 5 acting on side 2 alone.
- **S1–S4 (session 1, done).** Semi-invariant quadrics `Q₁ = x_M x_L`, `Q₂ = det[x_u|x_v]`, Klein form `Q₁ − Q₂`; 19 orbit strata. **S2:** if the 16 block inequalities `c_A(U) + c_B(U) ≤ dim U` hold and the pair avoids four isotropy exceptions (X1)–(X4), then `A ∩ gB = 0` for generic `g ∈ S(ϕ)` (incidence count `≤ 4 < 5`; one sentence for base-locus subspaces added at review, S10(i)). **S3:** dual/unified form: block inequalities with slack `max(0, ρ₁+ρ₂−6)` + no exception ⟹ `dim(A + gB) = min(6, ρ₁+ρ₂)` — the `⟸` of (BE-96)(iv), a theorem outside (X1)–(X4). **S4:** two stars satisfy every block inequality yet always meet (Klein parity): the block list is incomplete; (X1) same-family is a real obstruction.
- **S5 (reduction, done).** The Lemma holds at `(G; u, v)` as soon as the generic side profiles satisfy the 14 inequalities and the pair avoids (X1)–(X4); openness on the attaining locus turns one good pair into the generic point.
- **S6 (session 2, done) — side-degree 1 at `u`, neighbour `w`.** `ρ̄_{uv}(H) = ρ̄_{wv}(H−u) + K·L_{uw}`; `f = f'+1`, `g = max(g', f'_sep−5)`, `δ = min(δ'+1, 6)`; `H` attains iff `H−u` does; **`H` welded-attains iff `H−u` welded-attains at `(w,v)` and `L_{uw} ∉ ρ̄_{wv}(H−u)`** (or `δ' = 6`). Profile transfer: `c(U) = c'(U)+1` for `U ⊇ Π_u`, else `c(U) = dim(ρ̄' ∩ (U ⊕ K L_{uw}))`.
- **S7 (done) — excess is attainment loss.** `c(U) = dim M(H ∪ bars(U^⊥)) − dim M(H/uv)`: the `U`-joint is `6 − dim U` bars between bodies `u, v` along lines spanning `U^⊥`. **No excess at `U` ⟺ the bar-augmented side attains its Tay count.** Excess is Klein-self-dual (`(ρ̄, U) ↔ (T, U^⊥)`, `T = ρ̄^⊥`). **Witness principle:** one exact configuration certifies attainment, welded attainment and upper bounds on all 16 `c(U)` for every component through it (upper semicontinuity).
- **S8 (done).** Sides without interior hubs have irreducible `Y°(H; ϕ)`; the session-1 ear and theta rows are theorems for the whole fibre (ears: excess `Π_u, Π_v: 1` at `m ≤ 3`, plus the `m ≤ 2` blocks; `m ≥ 4` generic throughout; thetas/dumbbell: no excess); `tail`, `cycletail` rows are theorems for their component.
- **S9 (done) — the `ear1` criterion, an equivalence.** With `A' := ρ̄₁ ∩ (Π_u ⊕ Π_v)`: for `δ ≤ 4`, `G = H ∪ ear1` attains at the generic point iff `dim A' ≤ 2` and `A'` is not a ruling plane `y ∧ W`; for `δ = 5` iff `dim A' ≤ 3`; `δ = 6` always; `dim A' = δ − 2 + dim(T₁ ∩ ⟨M, L⟩)`. A theorem about a shape the consumer does not take (Statement); its machinery (S7's wrench dual) carries over.
- **S10 (review 2026-09-15; the reviewer's arithmetic from S3 + S8 — verify before building on it).** At the hub cut with `B = ρ̄(ear_m)` (S8's profile) and `A = ρ̄′`, `ρ′ = δ′`: **`m ≥ 4`** — every block inequality reads `c′(U) ≤ max(1, δ′)` and no exception can fire against a 1-dimensional (dual) partner, so the Lemma holds given only that `H′` attains and welded-attains at `(w, v)`. **`m = 3`** — only `c′(Π_w), c′(Π_v) ≤ 1` at `δ′ = 2` survives, plus (X3) bookkeeping on `ear3`'s fixed profile ((X2), (X4) are avoided there). **`m = 2`** — `c′(Π_w), c′(Π_v) ≤ 1` and `c′(Π_w ⊕ Π_v) ≤ 2` (`δ′ ≤ 3`; `≤ 3` at `δ′ = 4`); `c′(⟨M⟩⊕Π), c′(Π⊕⟨L⟩) ≤ 2` at both pencils (`δ′ = 3`); plus (X1)–(X4).
Open obligations:
- **O4 (re-aimed at review)** — S10's `m = 2` conditions for girth-`≥ 7` sides with side-degree `≥ 2` at both terminals, at generic `ϕ` on the attaining + welded-attaining component; `m = 3`'s residue; the exception bookkeeping. By S7 each is attainment of `H′ ∪ bars(U^⊥)` (`U = Π_w`: four bars; `U = Π_w ⊕ Π_v`: the two bars `M, L`). The general-side form (every 2-cut, for the induction on `H′`) stays open but is the induction frame's to state (Worries).
- **O5** Pair conditions for two general sides — needed only by the global induction; parked behind the frame decision.
- **O6** The incident case `u ~ v` — not consumed directly (`w ≁ v` at girth `≥ 7`); parked with O5.

## Where it breaks <!-- budget 10 -->
**O4 at `m = 2`, hub terminals.** Need, for `H′` at generic `ϕ` on the right component: `ρ̄′ ⊉ Π_w`, `ρ̄′ ⊉ Π_v`, `dim(ρ̄′ ∩ (Π_w ⊕ Π_v)) ≤ 2`. Measured: no excess anywhere on the 23-side battery (`sideprof.py`, caps `s = 20`, 6 draws); a theorem for `theta33/34/44`, `dumbbell` (S8) and for the component through each draw elsewhere (S7(vi)); **no proof for any side with an interior hub**, and the population has at most two interior hubs and no 3-connected chunk.
The transparent mechanism (paths: a wrench of `⟨M,L⟩` passes every terminal hinge, two interior hinges in general position kill it) does not extend — `T = ρ̄′^⊥` strictly exceeds the path-generated `Σ_P span(P)^⊥` for a general side, and nothing bounds it. Session 2's kill of side-induction (a) was premature: peeling the *whole* degree-2 chain lands back on the block lattice at the hub cut (that is S10); what it leaves is the three inequalities above at side-degree `≥ 2`. Hub peeling (b) and parallel composition (c) still fail as stated.
Concrete first target: `c′(Π_w) ≤ 1` at side-degree `≥ 2` — by S7, the four-bar framework `H′ ∪ bars(Π_w^⊥)` attains — for **series–parallel** `H′` (thetas of thetas); one exact witness per shape is a proof for that shape (S7(vi)), the class needs a structural argument.

## Tried on this route, and what each rules out <!-- budget 10 -->
- Incidence count over orbit strata (S2, session 1): rules out "the gauge group is too small" — only the four isotropy exceptions escape the count.
- Two-stars pair (S4, exact, 20 × 30): rules out "the 16 block inequalities are sufficient" — Klein parity lies outside the block list.
- Side-profile battery, 11 sides × 6 draws (S5, seed 20260915; theorems by S7(vi)/S8): rules out excess at a side-degree-2 terminal **for those sides**; shows (X4)'s shape is realised (`ear1`), so (X4) stays a hypothesis of S2.
- Widened battery, 12 sides × 6 draws (`sideprof.py --side all2`, seed 20260915; hub terminals of side-degree 3–4, mixed 3/1 and 3/2, two interior hubs, `dist` up to 6): no excess except the side-degree-1 hinge `Π_v: 1` on `hubpend`, `hubpend2`; rules out "excess at a hub terminal" and "excess from interior hubs" **within the 23 named sides** (caps `s = 20`, 6 draws) — not found, not a theorem.
- `earone.py`, 23 sides × 6 draws × 3 `p_x` (seed 20260915): S9's predicted verdict = exact rank of `H + x` at 138/138, both S7/S9 identities asserted at every draw; rules out a hidden case in S9's proof within the population; `T ∩ ⟨M,L⟩ ≠ 0` only at `dist ≤ 3`.
- Reading `Deficiency.lean` (`bodyBarDim n = n(n+1)/2`): `def₂` is the planar count `3(|P|−1) − 2d(P)`, so `C_n` has `def₂ = n−3 > n−6 = def₃`; rules out the flat witness (brief §3(a), (c)) as a substitute for the Lemma on the consumed class.
- Review reading of `Escape.lean:467` (2026-09-15): the disjunct `¬ PencilHub a ∨ ¬ PencilHub b` — rules out the one-vertex ear between two hubs as the consumed shape; S9 is a theorem about a case the consumer does not take.

## Next steps <!-- budget 5 -->
1. Verify S10 line by line against S3 and S8 and record a verdict in the workbook; one exact control: compose `ear2`, `ear3`, `ear4` with the hub-terminal sides of the battery (`theta*`, `cross*`, `hubcyc`) and compare S10's predicted verdict with the exact rank of the composed graph (an `earone.py` variant; `def₃` by the 2-cut law).
2. Attack `c′(Π_w) ≤ 1` at side-degree `≥ 2` via S7 — the four-bar-augmented side attains — for series–parallel `H′`; thetas-of-thetas is the milestone.
3. Adversarial controls first, cheap: random girth-`≥ 7` hub-terminal sides on `≤ 12` vertices from `sideprof`'s sampler, one with a 3-connected chunk; one excess at `Π_w`, `Π_v` or `Π_w ⊕ Π_v` refutes the `m = 2` clean form.
4. PI decision pending, not the attack's: the induction frame (welded attainment supply; the core clause) — `notes/Phase39.md` *Blockers*. O5/O6 wait on it.

## Worries <!-- budget 5 -->
- Frame: generic `ϕ` legal for each side, and welded attainment supplied by the induction — S6(iii) shows welded attainment at a side-degree-1 terminal needs `L_{uw} ∉ ρ̄_{wv}(H − u)`; 3-connected pieces attain at the *flat* configuration and `K₄` only there. Not this lemma's, but every version of it is vacuous without it; **PI decision pending** on whether the frame gets its own brief.
- S10 is the reviewer's derivation, not the attack's; a slip there mis-aims session 3 — verify before building.
- O4 is target-type (S7) even in its `m = 2` form; if session 3 finds no structural argument for a side with an interior hub, judge the route at review, not push it.
- S2's exceptions (X2)–(X4) are proof artefacts; (BE-96)(iv)'s criterion in BUNIF is incomplete (S4); PI decides whether to annotate.
- Characteristic 0, `K` algebraically closed for the generic-point arguments; descent to the Lean field unchecked (brief §3); the 5-rows-per-hinge matrix against `rigidityRows` unchecked.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (moved at the 2026-09-15 review, not by a session)
- Open obligations: 3 (trend over the last three sessions: flat — 7 → 3 → 3; O4 narrowed to the consumed `m = 2`/`m = 3` conditions at review, O5/O6 parked behind the frame decision)
