# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 1 · last session: 2026-09-15 · baseline HEAD: 43648e65

## Statement <!-- budget 10 -->
`G` 2-connected of girth `≥ 5`, `{u,v}` a 2-separation with `u ≁ v`, sides `H₁, H₂`; `ϕ` a *generic* flag pair (`p_u ≠ p_v`, `π_u ≠ π_v`, `p_v ∉ π_u`, `p_u ∉ π_v`). Assume for `i = 1,2` that `Y°(H_i; ϕ)` has an irreducible component `Y_i` at whose generic point `H_i` attains and `H_i/uv` attains (`a_i = 0`, `ρ_i = δ_i`). Then the generic point of `Y₁ ×_ϕ Y₂` has `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)`; so `G` attains ((BE-86)(i), re-derived).
Changes from the brief's Lemma, and why: (1) girth `≥ 5` (brief §6 idea 1; the Lean consumer `hbareSplit` in `Escape.lean` has girth `≥ 7`, confirmed at its statement, so nothing consumed is lost); at girth `≥ 5` the coplanarity closure never forces `π_u = π_v`, the only reason the brief weakened to `a_i > 0`. (2) `ϕ` is a fixed generic pair, not "some `ϕ`", and `a_i = 0` is restored; whether generic `ϕ` is *legal* for a side is an induction-frame obligation (Worries), not this lemma's. (3) The incident case `u ~ v` is deferred (O6).

## Current route and proof sketch <!-- budget 30 -->
**Route R1 — gauge-group transversality by orbit strata.** Results with proofs are in `notes/pencil/workbook/attack-smark.md` (S1–S5; no labels minted, the brief assigns no prefix). Frame = BUNIF's ((BE-94)): blocks `⟨M⟩, Π_u, Π_v, ⟨L⟩` of `Λ²K⁴`, stabiliser `S(ϕ) = {(a,b,C)}/K*` of dimension 5 acting by `(ab·x_M; aCx_u; bCx_v; det C·x_L)`, acting on side 2 alone ((BE-94)(ii)).
- **S1 (done).** `Q₁ = x_M x_L`, `Q₂ = det[x_u|x_v]` are the semi-invariant quadrics (Klein form `Q₁ − Q₂`); the orbit strata of `P⁵` are a 1-parameter family of 4-dimensional orbits (open in the quadrics `Q₁ = I·Q₂`) plus 18 special strata whose closures are the 16 block sums and three `Q₂`-cones. Computer-checked (`drivers/orbits/`).
- **S2 (done) — the key step, new.** For `dim A + dim B ≤ 6`: if the 16 block inequalities `c_A(U) + c_B(U) ≤ dim U` hold and the pair avoids four isotropy exceptions (X1)–(X4), then `A ∩ gB = 0` for generic `g ∈ S(ϕ)`. Proof: `dim{(g, y) : gy ∈ P(A)} ≤ Σ_Σ [dim(P(A)∩Σ) + dim(P(B)∩Σ) + 5 − d_Σ] ≤ 4 < 5`. The brief §5 dismissal "orbit 5 vs Grassmannian 9" counted the wrong thing: the gauge group need only move `B` off `A`.
- **S3 (done).** Dual case by Klein complements; unified: `c_A(U) + c_B(U) ≤ dim U + max(0, ρ₁+ρ₂−6)` for all 16 `U` + no exception ⟹ `dim(A + gB) = min(6, ρ₁+ρ₂)`. This is the `⟸` of BUNIF's reduction (BE-96)(iv), there a 400/400 measurement, now a theorem outside (X1)–(X4). Specialised to an ear it recovers BEARCASE's `(P), (Z), (R)` mechanisms ((BE-35)(iv)).
- **S4 (done).** Two stars `star(p), star(p′)` satisfy all 16 block inequalities yet always meet (Klein parity, same family): the block list is **incomplete** as an abstract criterion; (X1) is a real obstruction. The corpus's `abst` sampler never draws isotropic pairs.
- **S5 (reduction, done).** The Lemma holds at `(G; u, v)` as soon as the generic side profiles satisfy the 14 inequalities and the pair avoids (X1)–(X4); openness on the attaining locus turns one good `(q₁, g·q₂)` into the generic point.
Open obligations:
- **O4** Per-side profile bounds at generic `ϕ`, girth `≥ 5`, on the attaining + welded-attaining component: bound `c(U)` for the 16 `U` by structure at `u, v`. Measured law (11 sides, `drivers/sideprof.py`): excess at `Π_u` iff `u` has side-degree 1 (then exactly the hinge `L_{uw}`), and excess only in blocks containing that pencil; no 3-dimensional Klein-isotropic `ρ̄` (so (X1) unseen); `ear1` realises the (X4) ruling shape.
- **O5** Pair conditions: combine O4 for the two sides; at girth `≥ 5` two side-degree-1 ends at the same terminal cannot both be 2-paths (4-cycle), which is what kills (X4) pairs and the `Π_u ⊕ Π_v` inequality at the worst profile.
- **O6** The incident case `u ~ v`: `S(ϕ)` of dimension 7; redo S1–S3 there.

## Where it breaks <!-- budget 10 -->
**O4.** I can state the profile law the data shows but cannot yet prove it. The first concrete gap: for a side with `u` of side-degree `≥ 2` at generic `ϕ`, show `c(Π_u) = 0` — i.e. no motion of `H` rotates `v` relative to `u` about a line through `p_u` in `π_u` — and more generally that the profile is generic ("no excess") at side-degree `≥ 2` on both ends (measured at `theta33/34/44`, `dumbbell`). Second gap: exclude a 3-dimensional Klein-isotropic `ρ̄` (a spherical joint or a planar slider between `u` and `v`) on the attaining + welded-attaining component — (X1) — by a structural argument, not by sampling. Third: the side-degree-1 case reduces by `ρ̄_{uv}(H) = K·L_{uw} + ρ̄_{wv}(H − u)` (one line, to be written up), but the profile of `ρ̄_{wv}(H − u)` at the pencil `Π_u ∋ L_{uw}` is then the question for a *shifted* pencil sharing one line with `Π_w`, which the block calculus does not see; this is where a proof by induction on the side would have to be set up.

## Tried on this route, and what each rules out <!-- budget 10 -->
- Incidence count over orbit strata (S2): rules out "the gauge group is too small" — `dim I ≤ ρ₁+ρ₂−2 ≤ 4` suffices; only the four isotropy exceptions escape the count.
- Two-stars pair (S4, exact, 20 pairs × 30 group elements): rules out "the 16 block inequalities are sufficient" — Klein parity is a mechanism outside the block list.
- Side-profile battery (S5, 11 girth-`≥ 5` sides × 6 draws, seed 20260915; `theta34` also 24 draws, seed 1): rules out excess at a terminal pencil at side-degree `≥ 2` **within the sampled sides** (a "not found under cap", not a theorem) and shows (X4)'s shape is realised by a real side (`ear1`), so (X4) cannot be dropped from S2's hypotheses.

## Next steps <!-- budget 5 -->
1. Write up the side-degree-1 reduction `ρ̄_{uv}(H) = K·L_{uw} + ρ̄_{wv}(H − u)` and derive the ear profiles from it (S6), so the measured ear rows become theorems.
2. Attack `c(Π_u) = 0` at side-degree `≥ 2` (the first gap above): try the wrench dual — a relative screw in `Π_u` is Klein-orthogonal to every hinge at `u`, so it is a load every hinge at `u` transmits; look for the contradiction with `ρ = δ` via the welded count.
3. Widen the control battery to sides with `u` a hub (side-degree 3) and to mixed patterns, hunting for excess at side-degree `≥ 2` — the cheapest way to refute the profile law before proving it.
4. O6: compute the 7-dimensional `S(ϕ)` at `u ~ v` and its strata; the same count should go through with more special orbits.

## Worries <!-- budget 5 -->
- Frame: generic `ϕ` legal for each side (fibre non-empty with an attaining, welded-attaining component) is an induction obligation the brief's S-mark″ does not state; 3-connected pieces attain at the *flat* configuration (coincident flags) and `K₄` has only flat configurations. Girth `≥ 5` does not fix this by itself. Not mine, but the lemma is vacuous without it.
- S2's exception list is a proof artefact: (X2)–(X4) may or may not obstruct in a given case; if a real pair lands in one, a direct argument is needed there.
- (BE-96)(iv)'s criterion in BUNIF is incomplete as stated (S4); the PI decides whether to annotate the owning section — I did not touch it.
- Characteristic 0, `K` algebraically closed for the generic-point arguments; descent to the Lean field unchecked (brief §3).

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0
- Open obligations: 3 (trend over the last three sessions: falling — 7 at the start of session 1, 3 at its end)
