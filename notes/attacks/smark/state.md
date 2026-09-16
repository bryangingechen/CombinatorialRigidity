# Attack smark — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: 4 · last session: 2026-09-16 · baseline HEAD: c0b0fdc5 · the K4-minor frontier was an ear in disguise; the obligation decomposes over pieces (S13); break moved to (O4″)

## Statement <!-- budget 10 -->
`G` 2-connected of girth `≥ 5`, `{u,v}` a 2-separation with `u ≁ v`, sides `H₁, H₂`; `ϕ` a *generic* flag pair (`p_u ≠ p_v`, `π_u ≠ π_v`, `p_v ∉ π_u`, `p_u ∉ π_v`). Assume for `i = 1,2` that `Y°(H_i; ϕ)` has an irreducible component `Y_i` at whose generic point `H_i` attains and `H_i/uv` attains (`a_i = 0`, `ρ_i = δ_i`). Then the generic point of `Y₁ ×_ϕ Y₂` has `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)`; so `G` attains ((BE-86)(i), re-derived at review, workbook S10(ii)).
Changes from the brief's Lemma, and why: (1) girth `≥ 5` (brief §6 idea 1); the coplanarity closure never forces `π_u = π_v`, so `a_i = 0` is restored. (2) `ϕ` a fixed generic pair, not "some `ϕ`"; whether generic `ϕ` is *legal* for a side is an induction-frame obligation (Worries). (3) The incident case `u ~ v` is deferred (O6).
**Consumed instance (a trichotomy; brief §3, S11).** `hbareSplit` (`Escape.lean:467`) carries `¬ PencilHub a ∨ ¬ PencilHub b`, so the degree-2 vertex lies on a maximal degree-2 chain of `m ≥ 2` interior vertices with hub ends, and either (i) `G` a cycle `≥ 5` (base case (b)), (ii) the chain closes at a **single** hub (cycle `≥ 7` through a cut vertex; outside this 2-connected Lemma, induction case (d)), or (iii) `G = H′ ∪ ear_m` at a **hub** 2-cut `{w, v}`, `H′` connected, side-degree `≥ 2` at both ends, `dist_{H′}(w,v) ≥ 6−m`, so `w ≁ v` for `m ≤ 4`. Girth `≥ 7` once some vertex has degree `≥ 3` (`lem:pencil-girth-of-hub`); the consumed side inherits girth `≥ 7`.

## Current route and proof sketch <!-- budget 30 -->
**Route R1 — gauge-group transversality by orbit strata (S1–S4), then per-side profiles at the hub cut (S5–S13).** Proofs in `notes/pencil/workbook/attack-smark.md`; no labels minted (no prefix assigned). Frame = BUNIF ((BE-94)): blocks `⟨M⟩, Π_w, Π_v, ⟨L⟩` of `Λ²K⁴`, gauge `S(ϕ)` of dim 5.
- **S1–S5 (done).** 19 orbit strata; **S2/S3**: 16 block inequalities `c₁(U)+c₂(U) ≤ dim U + max(0, ρ₁+ρ₂−6)` + avoidance of four isotropy exceptions (X1)–(X4) ⟹ `dim(A + gB) = min(6, ρ₁+ρ₂)` for generic `g ∈ S(ϕ)` — the `⟸` of (BE-96)(iv); **S4** the block list alone is insufficient (Klein parity); **S5** the Lemma follows from the generic side profiles.
- **S6–S9 (done).** Side-degree-1 reduction (`L_{uw} ∈ ρ̄`, welded needs `L_{uw} ∉ ρ̄_{wv}(H−u)`); **S7** excess at a block = attainment loss of the bar-augmented side, Klein self-dual, and the **witness principle**: one exact configuration certifies attainment, welded attainment and upper bounds on all sixteen `c(U)` for every component through it; **S8** hub-free sides have irreducible fibres, so ear and theta profiles are theorems; **S9** the `ear1` criterion (not the consumed shape).
- **S10 → S12 (verified).** Side 2 = `ear_m` at the hub cut: `m ≥ 4` needs only attainment + welded attainment of `H′`; `m = 3` only `ρ̄′ ∉ {Π_w, Π_v}` at `δ′ = 2` (+ exception bookkeeping); **`m = 2`** is the core: `c′(Π_w), c′(Π_v) ≤ 1`, `c′(Π_w⊕Π_v) ≤ 2`, the two 3-dim blocks at each pencil `≤ 2` (at `δ′ ≤ 3`; nothing binds at `δ′ ≥ 5`), + (X1)–(X4). End-to-end control `earcompose.py` 252/252.
- **S13 (session 4) — the obligation decomposes over the pieces of `H′` at the cut.** (ii) `ρ̄_{wv}(H) = ∩_j ρ̄_{wv}(H_j)` over the components `C_j` of `H − {w,v}` (`H_j = H[C_j ∪ {w,v}]`), with `δ(H₁∪H₂) = max(0, δ₁+δ₂−6)`; series at a cut vertex: `ρ̄ = ρ̄_a + ρ̄_b`; monotone under subgraphs. So `c′(U) ≤ min_j c_j(U)`: **one piece not containing `Π_w` discharges `c′(Π_w) ≤ 1`.** (iii) An ear piece of length 4 discharges the whole `m = 2` list (length 5: all but `Π_w⊕Π_v ≤ 2` at `δ′ = 3`). (iv) **Irreducible fibre when hubs are pairwise non-adjacent** (S8's tower extended): there the frame's component clause is vacuous and every exact witness is a theorem for the side. (v) **Short-path kill:** pairwise non-adjacent hubs and `dist(w,v) ∈ {4,5}` ⟹ `c(Π_w), c(Π_v) ≤ 1`, 3-dim blocks `≤ dist − 3`, `c(Π_w⊕Π_v) ≤ dist − 2` (the shortest path's chain moduli is a free factor of the fibre; `ρ̄ ⊆ span(P)`; S8 ear profiles). (i) The session-3 "K4-minor frontier" (`sk4_d3`, `sk4_d4`, `prism`) is an ear in parallel with a fully flexible remainder (`δ = 6` once the direct branch is removed): its tight `c′(Π_w) = 1` is S8's ear line `L_{wx}` — S12(iii)'s hub reading is withdrawn.
- **SPQR reading.** In the SPQR tree of `H′ + wv`: P-nodes intersect (with the gauge acting on each piece independently, so S2–S3 give the *dimension* of `ρ̄₁ ∩ gρ̄₂`), S-nodes add, and the content sits in the R-nodes (subdivided 3-connected skeletons with the virtual edge `wv`). The census (S13(vi), `census.py`, 200 rows, 0 flagged) measures R-nodes with side-degree `≥ 2`: **no excess at any block at `δ ≤ 3`**; `c(Π_w) = 1` only from a bridge at `w` or when `δ = dist ≤ 5` (then `ρ̄ = span(P)`).
Open obligations:
- **(O4″)** (replaces O4′): the R-node core — a single piece with `dist(w,v) ≥ 6`, `δ ≤ 3`, side-degree `≥ 2` both ends: `ρ̄ ∩ Π_w = 0` (Where it breaks). Side items riding on it: the series case; `c(Π_w⊕Π_v) ≤ 2` at `(dist, δ) = (5, 3)`; the P-node rule (block profile of `ρ̄₁ ∩ gρ̄₂`, not just its dimension) for an `H′` with several non-ear pieces; irreducibility for hub-adjacent-hub sides; (X1)–(X4) bookkeeping for `m = 2, 3`.
- **O5** Pair conditions for two general sides — needed by the global induction; parked behind the frame.
- **O6** The incident case `u ~ v` — parked with O5.

## Where it breaks <!-- budget 10 -->
**(O4″) A single piece `H` (`H − {w,v}` connected, no cut vertex between `w` and `v`), `w ≁ v`, girth `≥ 7`, side-degree `≥ 2` at both terminals, `dist(w,v) ≥ 6`, `δ ≤ 3`: prove `ρ̄ ∩ Π_w = 0`.** Measured `0` at all 52 such census rows (8 skeleton families, `dist` 6–7, each a theorem for its side by S13(iv)) and at nine special-incidence families on the minimal instance `K4−e (4,2,3,4,2)` (`|V| = 14`, `g = 0`, `specialcfg.py`) — so it looks pointwise true, not component-dependent.
Dually (S7(v)): among the `6 − δ ≥ 3` transmissible wrenches — self-stresses of the rigid welded `H/wv` modulo those of `H` — exhibit one with a nonzero moment about an axis of `Π_w` (`T ⊄ Π_w^⊥`); at side-degree 2 this says the wrench through hinge `wx₂` has a moment about `L_{wx₁}`.
Why nothing reaches it: every `w`–`v` path has `≥ 6` lines, so `span(P) = Λ²K⁴` and the path/transversal argument of S13(v) is empty; sub-sides of a stiff side are floppier (monotonicity goes the wrong way), so there is no reduction to `K4−e`; re-gluing the motion `m(v) − m(w) = L_{wx₁}` into the welded framework violates the other hinges at `w`; the stress is cycle-generated. A degenerate witness cannot help either: `ρ̄` only grows at special points.
Concrete first target: `K4−e (4,2,3,4,2)` by hand — `g = 0`, three self-stresses of `H/wv` as branch circulations `ω_X ∈ span(X)^⊥` (`X ∈ {A,B,C,D,R}`, lengths `4,2,3,4,2`) in equilibrium at `p, q`; show one has `Q(ω_B, L_{wx_A}) ≠ 0`.

## Tried on this route, and what each rules out <!-- budget 10 -->
- `pencilline.py` (6/6 draws, `sk4_d3`/`sk4_d4`/`prism`): rules out "the K4-minor / three-hub structure puts a screw into the pencil" — the line is the direct branch's `L_{wx}` and the branch co-moves with `v`; with `δ(side − branch) = 6` this is S8's ear profile via S13(ii).
- `census.py` (200 rows, 13 skeleton families, lengths 2–4, `δ ∈ {2,3,4}`, `|V| ≤ 32`; 0 flagged): rules out any excess at any block for side-degree-`≥ 2` single pieces at `δ ≤ 3` **within the population**; the only `c(Π_w) = 1` rows are bridges (S6) and `δ = dist = 4` (a path span).
- `specialcfg.py` (nine special loci × 3 draws on `K4−e (4,2,3,4,2)`): rules out `Π_w ⊆ ρ̄` on those loci even where the side stops attaining — the target is not visibly component-sensitive.
- Path-span bound `ρ̄ ⊆ span(P)` for `dist ≥ 6`: rules out nothing (`span = Λ²K⁴`); it is exactly what S13(v) exhausts at `dist ≤ 5`.
- Sub-side monotonicity toward `K4−e`: rules out that route — a `K4−e` sub-side of a `dist ≥ 8` piece has `≥ 17` edges and may have `δ = 6`.
- Re-gluing `m` (with `m(v) − m(w) = L_{wx₁}`) into `H/wv` by `m(w) := L_{wx₁}`: fails at every other hinge at `w` — rules out a one-line contradiction from the welded framework at side-degree `≥ 2`.
- (Sessions 1–3 attempts retired to `log.md`.)

## Next steps <!-- budget 5 -->
1. (O4″) on `K4−e (4,2,3,4,2)` by hand in the stress picture (branch circulations, `g = 0`); then look for the R-node argument (why a cycle-generated wrench must carry a pencil moment). A proof there is the milestone; a hub-terminal single piece with `c(Π_w) ≥ 1` at `dist ≥ 6`, `δ ≤ 3` refutes the clean form.
2. The P-node rule: block profile of `ρ̄₁ ∩ gρ̄₂` for generic `g ∈ S(ϕ)` (refine S2 to a block sum `U`); with S13(iii)/(v) this closes every `H′` whose R-nodes are covered.
3. The series case and the `(5,3)` `Π_w⊕Π_v` bound; extend S13(iv) to hub graphs with a 2-degenerate ordering.
4. (X1)–(X4) bookkeeping for `m = 2, 3` on `ear2`/`ear3`'s fixed `ρ̄, T` (carried from session 3).
5. PI decision pending, not the attack's: the induction frame (welded-attainment supply; the core clause) — O5/O6 wait on it.

## Worries <!-- budget 5 -->
- (O4″) is target-type (S7): a rigidity statement about the welded side's stresses. If no structural argument emerges by the review, judge the route there; the census says the clean form (`= 0`, no excess) is what to aim at, tighter than S10 needs.
- Frame: generic `ϕ` legal for each side, welded attainment supplied by the induction (S6(iii) shows it is a real condition at side-degree 1). **PI decision pending** on whether the frame gets its own brief; every version of the Lemma is vacuous without it.
- Hub-adjacent-hub sides (allowed at girth `≥ 7`) have no irreducibility statement (S13(iv) needs pairwise non-adjacent hubs), so there a witness is a theorem only for its component; S8′-style towers stop at a hub with three placed hub neighbours.
- S10's exception bookkeeping ((X1)–(X4) on the pair, dual at high `δ′`) is still unchecked (next step 4); S13(iii)/(v) inherit it.
- Field (S11(v)): no characteristic used; `K` algebraically closed for generic-point arguments is the genuine item, descent to `K`-points not automatic — to settle with the frame, in witness form over `K` (S7(vi)); `IsAlgClosed K` interim, `[Infinite K]` target. The 5-rows-per-hinge matrix vs `rigidityRows` unchecked.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: 0 (moved from (O4′) — `exc(Π_w) ≤ 1` on K4-minor sides — to (O4″) — `ρ̄ ∩ Π_w = 0` on single pieces with `dist ≥ 6`; the K4-minor instances were ears)
- Open obligations: 3 (trend over last three sessions: flat — 3 → 3 → 3; O4′ replaced by the narrower O4″ with side items; O5/O6 parked behind the frame decision)
