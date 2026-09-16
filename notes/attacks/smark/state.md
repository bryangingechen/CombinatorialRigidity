# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 3 · last session: 2026-09-16 · baseline HEAD: 850f0bb6 · S10 verified (S12); K4-minor adversarial frontier opened; break sharpened to (O4′)

## Statement <!-- budget 10 -->
`G` 2-connected of girth `≥ 5`, `{u,v}` a 2-separation with `u ≁ v`, sides `H₁, H₂`; `ϕ` a *generic* flag pair (`p_u ≠ p_v`, `π_u ≠ π_v`, `p_v ∉ π_u`, `p_u ∉ π_v`). Assume for `i = 1,2` that `Y°(H_i; ϕ)` has an irreducible component `Y_i` at whose generic point `H_i` attains and `H_i/uv` attains (`a_i = 0`, `ρ_i = δ_i`). Then the generic point of `Y₁ ×_ϕ Y₂` has `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)`; so `G` attains ((BE-86)(i), re-derived at review, workbook S10(ii)).
Changes from the brief's Lemma, and why: (1) girth `≥ 5` (brief §6 idea 1); the coplanarity closure never forces `π_u = π_v`, so `a_i = 0` is restored. (2) `ϕ` a fixed generic pair, not "some `ϕ`"; whether generic `ϕ` is *legal* for a side is an induction-frame obligation (Worries). (3) The incident case `u ~ v` is deferred (O6).
**Consumed instance (a trichotomy; brief §3, S11).** `hbareSplit` (`Escape.lean:467`) carries `¬ PencilHub a ∨ ¬ PencilHub b`, so the degree-2 vertex lies on a maximal degree-2 chain of `m ≥ 2` interior vertices with hub ends, and either (i) `G` a cycle `≥ 5` (base case (b)), (ii) the chain closes at a **single** hub (cycle `≥ 7` through a cut vertex; outside this 2-connected Lemma, induction case (d)), or (iii) `G = H′ ∪ ear_m` at a **hub** 2-cut `{w, v}`, `H′` connected side-degree `≥ 2` at both ends, `dist_{H′}(w,v) ≥ 6−m`, so `w ≁ v` for `m ≤ 4`. Girth `≥ 7` once some vertex has degree `≥ 3` (`lem:pencil-girth-of-hub`). The consumed side inherits girth `≥ 7`.

## Current route and proof sketch <!-- budget 30 -->
**Route R1 — gauge-group transversality by orbit strata (S1–S4), then per-side profiles at the hub cut (S5–S12).** Proofs in `notes/pencil/workbook/attack-smark.md`; no labels minted (the brief assigns no prefix). Frame = BUNIF ((BE-94)): blocks `⟨M⟩, Π_w, Π_v, ⟨L⟩` of `Λ²K⁴`, `S(ϕ)` of dim 5.
- **S1–S5 (done).** 19 orbit strata; **S2** the 16 block inequalities + avoidance of four isotropy exceptions (X1)–(X4) ⟹ `A ∩ gB = 0` generically; **S3** dual/unified: `c₁(U)+c₂(U) ≤ dim U + max(0, ρ₁+ρ₂−6)` for all 16 blocks + no exception ⟹ `dim(A+gB) = min(6, ρ₁+ρ₂)` — the `⟸` of (BE-96)(iv); **S4** two stars meet always (Klein parity: block list incomplete, (X1) same-family real); **S5** the Lemma holds once the generic side profiles satisfy the 14 inequalities and the pair avoids (X1)–(X4).
- **S6 (done).** Side-degree-1 terminal reduces to `H − u`; welded needs `L_{uw} ∉ ρ̄_{wv}(H−u)`.
- **S7 (done) — excess is attainment loss.** `c(U) = dim M(H ∪ bars(U^⊥)) − dim M(H/uv)`; **no excess ⟺ the bar-augmented side attains**; Klein self-dual; **witness principle (vi):** one exact configuration certifies attainment, welded attainment, and upper bounds on all 16 `c(U)` for every component through it.
- **S8 (done).** Hub-free sides have irreducible fibres; ear and theta profiles are theorems (`c(Π)=0` at side-degree 2 for thetas).
- **S9 (done).** The `ear1` criterion in closed form (a shape the consumer does not take).
- **S10 (review) → S12 VERIFIED (session 3).** At the hub cut, side 2 = `ear_m`: **`m ≥ 4`** the Lemma holds given only `H′` attains + welded-attains (no profile condition); **`m = 3`** only `ρ̄′ ∉ {Π_w, Π_v}` at `δ′ = 2` (+ (X3)/dual bookkeeping on `ear3`); **`m = 2`** the core: `c′(Π_w), c′(Π_v) ≤ 1`, `c′(Π_w⊕Π_v) ≤ 2` (`δ′ ≤ 3`), the two 3-dim blocks `≤ 2` (`δ′ = 3`), (+ (X1)–(X4)). Verified: arithmetic by hand (S12(i)); end-to-end control `earcompose.py`, 252/252 (S12(ii)).
Open obligations:
- **O4′ (session-3 sharpened)** — the `m = 2` bounds for girth-`≥ 7` sides, side-degree `≥ 2` both terminals, at generic `ϕ` on the attaining+welded component. By S7, `c′(Π_w) = max(0, δ′−4) + exc(Π_w)`, `exc(Π_w) =` attainment loss of the four-bar framework `H′ ∪ bars(Π_w^⊥)` (bars `M, L`, two lines of `Π_w`). Need **`exc(Π_w) ≤ 1`** (symmetrically `v`), and `c′(Π_w⊕Π_v) ≤ 2` (the two-bar `M, L` framework). `m = 3`'s residue + exception bookkeeping ride along.
- **O5** Pair conditions for two general sides — needed by the global induction; parked behind the frame.
- **O6** The incident case `u ~ v` — parked with O5.

## Where it breaks <!-- budget 10 -->
**(O4′) `exc(Π_w) ≤ 1` for a girth-`≥ 7` hub-terminal side with a K4 minor.** New this session (S12(iii)): the series-parallel thetas gave `c′(Π_w) = 0` (S8), but the first **K4-minor** sides (`sk4_d3`, `prism`, `sk4_d4`, girth 9–10) and prism **saturate S10's bound at `c′(Π_w) = 1`** once `δ′ ≥ 3` — never exceeding it. So the bound `≤ 1` is *tight*, and `= 0` (S8's series-parallel value) is false in general; the non-series-parallel structure puts exactly one relative screw into the terminal pencil. What is missing is a proof that it puts **at most** one: `exc(Π_w) = ` attainment loss of `H′ + 4 bars` between `w, v`, measured `∈ {0, 1}` on every draw (0 series-parallel, 1 K4-minor at `δ′ ≥ 3`), with no structural argument bounding it for a side with a K4 minor / `≥ 3` interior hubs.
Concrete first target: `exc(Π_w) ≤ 1` for the K4-minor family — one exact witness per shape is a proof for that shape (S7(vi)); the class needs a structural argument (why the four flag bars kill all but one dof of the pencil). The transparent path mechanism (S8) does not reach it.

## Tried on this route, and what each rules out <!-- budget 10 -->
- Hand verification of S10 block-by-block against S3 + S8 (S12(i)): rules out an arithmetic slip in the reviewer's stratification — every `m`-case bound reproduced exactly.
- `earcompose.py`, 14 hub sides × 3 ears × 6 draws = 252/252 (seed 20260916; theorems by S7(vi)): rules out "S10 predicts attainment wrongly" and "some battery side exceeds the S10 `c′` bound" — 2-cut law holds, S3 criterion ⟺ exact rank, no bound exceeded.
- `adversarial.py`, K4-minor + prism sides at `δ = 2,3,4` × 6 draws (seed 20260916): rules out "K4-minor structure pushes `c′(Π_w) ≥ 2`" **within these four sides** — `c′(Π_w) ≤ 1` at every draw, tight at `δ′ ≥ 3`; not found above 1, not a theorem.
- `earcompose --side sk4_d*` (K4-minor ∪ `ear_{2,3}`, 6 draws): rules out "the consumed shape fails on a K4-minor side" — attains at every draw, S3 crit ⟺ actual.
- (Sessions 1–2 attempts retired to `log.md`: side-induction kill, path wrench mechanism, block-list sufficiency, the incidence count.)

## Next steps <!-- budget 5 -->
1. Attack `exc(Π_w) ≤ 1` (O4′) structurally: the four-bar framework `H′ ∪ bars(Π_w^⊥)` — why do the flag bars `M, L` + two `Π_w` lines leave ≤ 1 dof of the terminal pencil? Start with the K4-minor family where it is tight (a proof there is the milestone); series-parallel (`exc = 0`) may fall to the S8 fibre argument first.
2. Widen the adversarial net cheaply before proving: more K4-minor lengths, a K_{3,3}-minor side, a side with a 3-connected chunk of `≥ 3` interior hubs; one `c′(Π_w) ≥ 2` refutes the clean form.
3. Verify the `m = 3` / `m = 2` exception bookkeeping ((X1)–(X4) on the pair, dual at high `δ′`) — a finite check on `ear2`/`ear3`'s fixed `ρ̄, T` (S10 flagged it not done).
4. PI decision pending, not the attack's: the induction frame (welded-attainment supply; the core clause) — `notes/Phase39.md` *Blockers*. O5/O6 wait on it.

## Worries <!-- budget 5 -->
- O4′ is target-type (S7): if no structural argument for `exc(Π_w) ≤ 1` on K4-minor sides emerges, judge the route at review, not push it. The tightness (`= 1`, not `< 1`) means any proof must be exact, not slack-based.
- Frame: generic `ϕ` legal for each side, welded attainment supplied by the induction (S6(iii) shows it is a real condition at side-degree 1). **PI decision pending** on whether the frame gets its own brief; every version of the Lemma is vacuous without it.
- S10's exception bookkeeping is asserted avoidable (ear traces on `Π_w⊕Π_v` not ruling planes) but the pair-side and dual-side (X1)–(X4) at higher `δ′` are unchecked (next step 3).
- Field (S11(v)): no characteristic used; `K` algebraically closed for generic-point arguments is the genuine item, descent to `K`-points not automatic — to settle with the frame, in witness form over `K` (S7(vi)); `IsAlgClosed K` interim, `[Infinite K]` target. The 5-rows-per-hinge matrix vs `rigidityRows` unchecked.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (sharpened to (O4′) with K4-minor witnesses this session)
- Open obligations: 3 (trend over last three sessions: flat — 3 → 3 → 3; O4 sharpened to O4′ this session, O5/O6 parked behind the frame decision)
