# The post-Phase-42 cleanup (planning note)

**Status:** queued, not open; its rounds are not yet planned. On 2026-10-30, during 42g, the PI
asked for a cleanup phase after Phase 42 to address the informal proofs of
`blueprint/src/chapter/pencil-d.tex` that were difficult to formalize as written (§1). Its
placement, right after Phase 42 and ahead of ORIGAMI, is the coordinator's proposal, which the PI
has not answered. `.claude/autopilot/queue.toml` carries it as `CLEANUP-42`, attended, between
PENCIL-D and ORIGAMI; ROADMAP *Queued post-program phases* lists it. Its input is the proof-route
ledger (§2), which every remaining Phase 42 recon or build extends until the cleanup opens (§3).

## 1. The PI's decision (2026-10-30, verbatim)

From 42g, after the recon's acceptance and the `Grade/Polygon.lean` build. The record, as the
coordinator gave it:

> PI, 2026-10-30 (42g, after the recon's acceptance and the Grade/Polygon.lean build). The
> coordinator had answered the PI's question "Which proofs are more natural, the formalized ones or
> the ones currently written?" with: the Lean routes read better for the star
> (lem:pencil-d-polygon-star: by contradiction through linearity in the first point when the
> vertices span, else a 2×2-minor functional vanishing on the span of the vertices; Y_0 ≠ 0 from
> J_0 ≠ 0) and for the insertion's one bad value (lem:pencil-d-polygon-insert: the first n members
> of F(t) are independent with span A, so F(t) is independent iff J_i + t·w ∉ A, and J_i ∉ A makes
> that line meet A at most once); the chapter reads better for part (2) of
> lem:pencil-d-polygon-normal (the explicit affine map) and for the base triangle of
> lem:pencil-d-polygons (P_0,…,P_d a basis); the cycle's placement (two cases vs one path with N =
> min(m, D)) a toss-up. It offered to bring the star and insertion proofs in line with the Lean at
> the close.
>
> The PI answered, verbatim: "Yes, we should definitely align the star and insertion proofs with
> the Lean. For the other informal proofs that were difficult to formalize in Lean, are those
> tracked somewhere? I think we'll need a cleanup phase after Phase 42 to address them."
>
> The coordinator then answered that they are tracked only in notes/Phase42g.md *Blockers* item 2,
> which the close compresses, and proposed: a tracking note notes/Cleanup42.md for a
> post-Phase-42 cleanup, queued right after Phase 42 and ahead of ORIGAMI "unless you want it
> elsewhere"; a standing rule that any recon or build whose Lean departs from the chapter's proof
> adds a row in the same commit; and that the cleanup's opening recon compare every green node of
> pencil-d.tex (42b–42f were never checked for this) with its Lean, not only the logged rows. The
> PI has not replied on the placement: record "ahead of ORIGAMI" as the coordinator's proposal,
> not the PI's decision.

What follows from it:

- The star and the insertion were aligned in 42g, in the commit that created this note (R-1, R-2).
- **The standing rule** (`notes/Phase42-design.md` §3): a recon or build of any remaining Phase 42
  layer whose Lean departs from the chapter's proof adds a row to §2 in the same commit, and a
  commit that aligns a row sets its status.
- The cleanup's opening recon compares **every green node of `pencil-d.tex`** with its Lean, not
  only the rows of §2. The nodes 42b–42f made green (PD-STATE, PD-STABLE, 42d's COUNT-A and COUNT-B,
  PD-CARRIER and 42f's six) were never checked for a departing route.

## 2. The proof-route ledger

One row per node of `pencil-d.tex` whose Lean proof departs from the chapter's, in the chapter's
notation. *Status* is `open`, or `aligned` with the commit that made the chapter and the Lean follow
one route (`this commit` in that commit; a later edit may replace it with the sha), or `no
departure` for a row raised and then judged a carrier encoding of the chapter's own object, kept as
a short row so that the cleanup's recon does not raise it again. *Remedies* are the options: the
prose to the Lean, a Lean helper so that the Lean can follow the chapter, or keep both routes, each
valid. The cleanup chooses one per `open` row, with the PI.

- **R-1** · `lem:pencil-d-polygon-star` (`exists_normalsJoin_notMem_span_polygon`,
  `Pencil/Grade/Polygon.lean`) · **aligned, this commit** (42g).
  *Chapter (until then):* CERT S4's two basis arguments. If the vertices span, `d + 1` of them form
  a basis whose pairwise joins form a basis of `⋀²`, not all in `W(Y)`; otherwise extend `Y_i`,
  then `u ∉ S`, to a basis, and `Y_i ∨ u` is a basis vector outside `⋀²S ⊇ W(Y)`, with `Y_i ≠ 0`
  from part (1) of `lem:pencil-d-polygon-normal`.
  *Lean:* by contradiction through linearity of the join in its first point when the vertices span;
  otherwise a 2 × 2-minor functional, `ψ₂` vanishing on the span of the vertices, kills `W(Y)` but
  not `Y_0 ∨ u`; `Y_0 ≠ 0` from `J_0 ≠ 0`.
  *Remedies:* the prose to the Lean, taken; the proof's `\uses` is now `def:extensor` (the remark
  after it, for linearity), not `-normal`.
- **R-2** · `lem:pencil-d-polygon-insert` (`exists_insertNth_linearIndependent_join`, with
  `eq_of_add_smul_mem_of_add_smul_mem`) · **aligned, this commit** (42g).
  *Chapter (until then):* CERT S5's minor: `F(t)` as an `(m + 1) × D` coordinate matrix with one
  row affine in `t`, and an `(m + 1)`-minor `δ(t) = δ(0) + t δ₁` with `δ(0) ≠ 0` has one root at
  most.
  *Lean:* the first `m` members of `F(t)` are independent with span `A`, so `F(t)` is independent
  iff `J_i + t w ∉ A` (`w = u ∨ Y_{i+1}`); `J_i ∉ A`, so that line meets `A` once at most.
  *Remedies:* the prose to the Lean, taken.
- **R-3** · `lem:pencil-d-polygon-normal`, part (2) (`exists_linearEquiv_polygon_normal`) ·
  **open**.
  *Chapter:* the explicit affine map `g(x̄, ω) = (M(x̄ − ω ȳ_i), ω)`, `M` sending a basis that
  extends `ȳ_{i−1} − ȳ_i`, `ȳ_{i+1} − ȳ_i` to the standard basis of `K^d`.
  *Lean:* extend the basis map `Y_{i−1}, Y_i, Y_{i+1} ↦ P_1, P_0, P_2` of part (1) to an
  equivalence `g₁` (`Submodule.exists_linearEquiv_restrict_eq`), then correct its last coordinate
  by the transvection `v ↦ v + φ(v) P_0`, `φ = f ∘ g₁⁻¹ − f`, `f` the last coordinate.
  *Remedies:* keep both (the coordinator judged the chapter's the better read); a Lean helper, a
  split of `K^{d+1}` as `K^d × K` on which `g` is the chapter's block map; or the prose to the Lean.
- **R-4** · `lem:pencil-d-polygons`, the base triangle (`linearIndependent_join_triangle`) ·
  **open**.
  *Chapter:* `P_0, …, P_d` is a basis of `K^{d+1}`, so the `P_α ∨ P_β` (`α < β`) form a basis of
  `⋀²`, of which the triangle's three joins are three, up to sign.
  *Lean:* three 2 × 2-minor functionals, on the coordinate pairs first–second, first–last and
  second–last, separate the three joins; no basis of `⋀²`.
  *Remedies:* keep both (the coordinator judged the chapter's the better read); a Lean helper, the
  basis of `⋀²` induced by a basis of `K^{d+1}` (mathlib's, or a mirror), so that the Lean follows
  the chapter; or the prose to the minors, which the star's proof now uses (R-1).
- **R-5** · `thm:pencil-d-cycle`, the placement (`Graph.X0AttainsGrade.of_cycle`,
  `Pencil/Grade/Chain.lean`) · **open**.
  *Chapter:* two cases, CERT S6 (C1) and S7 (a): for `m ≤ D` the bodies at the vertices of a closed
  `m`-gon (`lem:pencil-d-polygons`); for `m > D` on a closed `D`-gon by part (1) of
  `lem:pencil-d-polygon-collapse`.
  *Lean (the landed proof, rechecked at the Chain build; it is the spike's):* one path, a closed
  `N`-gon with `N = min(m, D)` and every `c_j` at `Y_{π(j)}`, `π = polygonCollapse N m`, the
  identity when `N = m`.
  *Remedies:* a toss-up (the coordinator): the prose to the one path, or keep both.
- **R-6** · `thm:pencil-d-cycle`, the heights (`Graph.X0AttainsGrade.of_cycle_of_certificate`) ·
  **no departure** (42g's close): the Lean restricts `z` to `V(G)`, where the chapter's `z` lives.
- **R-7** · `lem:pencil-d-two-stars`, parts (2) and (3) (`dualAnnihilator_starGrade_sup_starGrade`,
  `finrank_add_two_le_of_forall_ιMulti_eq_zero`, `Pencil/Grade/Stars.lean`) · **aligned, this
  commit** (42h).
  *Chapter (until then):* the annihilator in `⋀^{d−1}` is `y ∧ y' ∧ ⋀^{d−3}`; (3) for every
  `p ≥ 0`, through bases `e_I` of `⋀^p Q`.
  *Lean:* the annihilator is the forms on `⋀²` (the chapter's pairing), (2) the forms through
  `⋀²(K^{d+1}/⟨y, y'⟩)`, (3) at `p = d − 3` only: a nonzero form whose radical holds `A` has
  `dim A + 2 ≤ dim V`. No exterior power past `⋀²`.
  *Remedies:* the prose to the Lean, taken at the PI's word (`notes/Phase42-design.md` §1,
  2026-10-31): parts (2) and (3) and the section's annihilator on forms, the `⋀^{d−1}` reading
  kept in one sentence; the `⋀^{d−1}` bridge declined. `lem:pencil-d-stars-three`'s proof cites
  the restated parts through the pairing.
- **R-8** · `lem:pencil-d-stars-four` (`exists_mvPolynomial_starsFour`,
  `eq_zero_of_starsFour_firstOrder`) · **aligned, this commit** (42h).
  *Chapter (until then):* `M(y)` on `⋀^{d−3}`, `ζ ↦ y₁ ∧ y₃ ∧ ζ` modulo `ρ°` and paired with
  `J₂`; the first-order `δ_w`, then two-stars (3) in `Q` to reach `d − 1 ≤ d − 3`.
  *Lean:* the kernel curve on the family `ρ`'s basis, the path joins, `y₁ ∨ e_l`, `y₃ ∨ e_l`, whose
  annihilator is `W° ∩ Σ°`; a nonzero `φ₀` in it extends to `φ₁` along `y₃ + t w`; `φ₁` kills `W`
  (at `w = y₄`, then every `w`), so `φ₀ (w ∨ ·) = 0` for every `w`, and `φ₀ = 0`. The independence
  of `y₁`, `y₃` is not used.
  *Remedies:* the prose to the Lean, taken at the PI's word (`notes/Phase42-design.md` §1,
  2026-10-31); its `\uses` are now two-stars, the kernel curve and
  `lem:pencil-x0-fibre-intersection`, what the Lean calls.
- **R-9** · `lem:pencil-d-kernel-curve` (`exists_mvPolynomial_kernel_curve`,
  `exists_mulVec_add_mulVec_eq_zero`, 42h recon) · **open**.
  *Chapter:* Cramer's rule over `K(t)`: `ξ(t) = (−A(t)⁻¹B(t)ξ₀|_{C'}, ξ₀|_{C'})`, a power series,
  whose coefficient of `t` is `ξ₁`.
  *Lean:* if no `ξ₁` exists, `M_wξ₀ ∉ range A`; `r` columns spanning `range A` with `M_wξ₀` are
  independent at `t = 0`, hence at some `t ≠ 0`, and with `M(y₀ + tw)ξ₀ = t(M_wξ₀ + tM₂(t)ξ₀)`
  give `M(y₀ + tw)` rank `r + 1`, against the generic rank. The generic minor is the same.
  *Remedies:* the prose to the Lean (no power series), or keep both.
- **R-10** · `lem:pencil-d-ear-data`, part (3) (`exists_mvPolynomial_earDataGrade_of_smul`, 42h
  recon) · **open**.
  *Chapter:* a nonzero multihomogeneous component `f_α`; `g(s) = f_α(y(s))`, and at `g(s) ≠ 0` the
  polynomial `λ ↦ f((λ_x y_x)_x)` has coefficient `f_α(y) ≠ 0` at `λ^α`.
  *Lean:* `h(λ, s) = f((λ_x y_x(s))_x)` is nonzero (a point of the planes with nonzero last
  coordinates, rescaled to an ear datum by part (2)); `g` is a nonzero coefficient of `h` as a
  polynomial in `λ` (`MvPolynomial.sumAlgEquiv`). Same coefficient argument, no `f_α`.
  *Remedies:* the prose to the Lean, or keep both (a toss-up).
- **R-11** · `lem:pencil-d-two-stars`, part (1) (`starGrade_sup_starGrade_eq_ker`,
  `finrank_starGrade_sup_starGrade`, 42h build) · **open**.
  *Chapter:* `e₁ = y`, `e₂ = y'` extended to a basis; the sum of the stars is spanned by the
  `e_i ∧ e_j` with `i ≤ 2`, and the `e_i ∧ e_j` with `3 ≤ i < j` go to a basis of `⋀²Q`.
  *Lean:* a linear section `s` of the quotient map, `P = s ∘ mkQ`:
  `a ∨ b − P a ∨ P b = (a − P a) ∨ b − (b − P b) ∨ P a` lies in the sum of the stars, so every
  `ω` is `⋀²P ω` modulo it, and `⋀²P` vanishes on the kernel; the dimension by rank–nullity.
  *Remedies:* keep both (the basis also carries the `⋀^{d−1}` reading of part (2) in the chapter);
  a Lean helper, mathlib's `Basis.exteriorPower`, so that the Lean follows the chapter; or the
  prose to the Lean.
- **R-12** · `thm:pencil-d-open-ear-four` (`Graph.X0AttainsGrade.of_openEar_four`, 42h build) ·
  **open**.
  *Chapter:* the ear datum is chosen twice (for `G″`, then for `G` after `x₂` is put back), the
  stars-four condition is shown at a general point by the third condition on the ear data, and the
  insertion is applied to the joins of the ear.
  *Lean:* `Graph.X0AttainsGrade.of_openEar_splitOff` takes the put-back as a hypothesis `hins`;
  `hins` is discharged by stars-four (as the condition `C`, with `pa`, `pb` the base points), then
  `exists_mvPolynomial_earDataGrade_of_smul` (its `hC` is `starsCond_of_smul`, the condition's
  scale invariance), then `exists_insertion_of_starGrade_sup` at `R = ρ ⊔` the joins of `G″` but the
  one at `1` (`span_joins_succAbove_two`). The order is the factored one, not the chapter's.
  *Remedies:* the prose to the Lean (state the factoring), or keep both.
- **R-13** · `lem:pencil-d-stars-three` (`exists_mvPolynomial_starsThree`, `Grade/StarsThree.lean`,
  42i) · **aligned, this commit** (42i, the theorem's build).
  *Chapter (until then):* annihilators read in `⋀^{d−1}`, `M(y₁, y₃)` on `⋀^{d−3}` and `ζ` in its
  kernel. A first step found four independent points `p_a, y₁, y₃, p_b`, which used `κ ≤ 1` and
  `p_a`, `p_b` independent, and its minor entered the polynomial; the statement also took `d ≥ 4`.
  *Lean:* forms on `⋀²` as stars-four's (R-8). The dual kernel curve runs for `starsFamily` at two
  interior points. Moving `y₁` along `p_a`, then any `u ∈ Π_a`, and `y₃` along `p_b`, then any
  `w ∈ Π_b`, puts `Π_a + Π_b` in the radical of `φ₀`. `y₁`, `y₃` are independent off a coordinate
  of `y₁ ∨ y₃`. It takes only `dim Π_a = dim Π_b = 3`, `d + κ ≤ 6`, `p_a ∈ Π_a` and `p_b ∈ Π_b`.
  *Remedies:* the prose and the statement to the Lean, taken at the PI's word on 2026-10-31
  ("Restate to the Lean", `notes/Phase42-design.md` §1, *42i, stars-three*). The theorem's first
  stage no longer takes its picture off the first coordinate of `q_a − q_b`.
- **R-14** · `thm:pencil-d-open-ear-three` (`Graph.X0AttainsGrade.of_openEar_three`,
  `Grade/ShortThree.lean`, on `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`, 42i) · **open**.
  *Chapter:* the proof of `thm:pencil-d-open-ear-four` with the first stage and the third condition
  changed. A span with both stars, not everything, gives `dim ρ ≥ 2d − 4`. Then `a`, `b` lie in one
  component (else `ρ` is everything), and a path joins them (`lem:relative-screws-path`) with at
  least four edges. So they are not adjacent and have no common neighbour, and glued-ends gives
  `r = 3`.
  *Lean (landed):* R-12's factored order, through the variant whose insertion hypothesis is taken
  at the first stage's base data (`Pq = g`, glued-ends' polynomial or `1`; `Rz` planes-meet's) for
  `ρ = joinRelScrews` of `G[V₁]`. When `r ≤ 2`, `dim ρ ≤ 2` directly: by glued-ends when the closed
  neighbourhoods of `a` and `b` are disjoint, and otherwise a common member `t` gives
  `ρ ⊆ span(b_a ∨ b_t, b_t ∨ b_b)` from the motions (`joinRelScrews_le_span_of_mem_closedNbhd`). So
  there is no component step and no path lemma, and a span with both stars is impossible at
  independent points (`not_starGrade_sup_le_of_finrank_le_two`), with no `W ≠ ⋀²`. The third
  condition (`exists_mvPolynomial_earDataGrade_starsCond_three`) and the insertion
  (`exists_insertion_earDataGrade_three`) are lemmas of their own.
  *Remedies:* the prose to the Lean (state the variant and the common member), or keep both.
- **R-15** · `lem:pencil-d-planes-meet` (`Graph.exists_mvPolynomial_planesMeet`, 42i, landed) ·
  **open**.
  *Chapter:* the functionals `λ^i_v`, the inverse of the lifting-planes isomorphism, linear in
  `z`. `Π_a ∩ Π_b` is `σ_a` of the common kernel of the rows of `L(z)`. `R` is a nonzero minor of
  `L(z)`, whose entries are linear in `z`.
  *Lean:* no `λ` map. The statement takes `la`, `lb` by their agreement with `z` on the closed
  neighbourhoods, as the base data give them, and `Π_a ∩ Π_b` as
  `range (gradeSigma la) ⊓ range (gradeSigma lb)`. A fixed inverse three-point matrix
  (`exists_inv_of_isAdmissiblePicture`) makes the rows `lb i − la i` linear in `z`, and `R` comes by
  rank openness (`exists_mvPolynomial_le_finrank_span_of_repr`) at a height whose rows are
  independent. The proof extends a family of lifting planes of `G[V₁]` along the ear
  (`exists_mem_liftingPlanes_extend_ear`), as the chapter does by `ℓ₁, ℓ₂, ℓ₃`; the Lean keeps
  `E = E(G[V₁])` as `Graph.liftingPlanesDiff` of the induced graph (so only `⊆` goes through
  `G`'s planes). `[Infinite K]` and `[Finite α]` are not taken.
  *Remedies:* keep both, or the prose names `R` by rank openness.
- **R-16** · `lem:pencil-d-glued-ends` (`Graph.exists_mvPolynomial_gluedEnds`,
  `Grade/GluedEnds.lean`, 42i, landed) · **open**.
  *Chapter:* `m = def₂(G; a, b)`, the merged deficiency, equal to `def₂(G')` by the partitions of
  `G'`; `g` a nonzero minor of `Z⁰(q)`'s matrix at the glued picture times the first coordinates
  of `q_u − q_v` over the edges, so that `dim Z⁰(q) = 3 + m`; a part `X` of value `m` refined into
  the `c ≥ 2` components of `G[X]`, the lifting planes constant on the refined parts counted
  directly, `r ≥ 3(c − 1)`.
  *Lean:* no merged deficiency: a partition of `G'` of the largest value pulls back
  (`partitionDef_map`) to one of `G` with `a`, `b` in one part and value `def₂(G')`, and only
  `dim Z⁰(q) ≤ 3|V(G)ᶜ| + 3 + def₂(G')` is used, from the kernel-dimension polynomial of `Z⁰`'s
  matrix (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`) and the inclusion of `Z⁰_G(q₀)` in
  `G'`'s lifting planes with `h_a = h_b`. `g` is that polynomial times Jackson–Jordán's polynomial
  for `G`, whose admissible pictures replace the edge coordinates. The planes constant on the
  parts are the plane framework's partition motions read through `screwOneEquiv`. The refinement
  splits `X` in two (the bodies `G[X]` joins to `a`, and the rest, `partitionDef_merge` read
  backwards), counted by `dim F(q) ≥ 3|V(G)ᶜ| + 3 + def₂(G)` (`lem:pencil-lifting-space-deficiency`
  with `lem:pencil-lifting-planes-dim`). The Lean takes every number of heights, not only `d ≥ 3`.
  *Remedies:* keep both, or the prose to the Lean (the proof's `\uses` then drops
  `def:deficiency-merged`).

## 3. The cleanup (not yet planned)

- **Until it opens:** the standing rule (§1) keeps §2 current through PD-STEPS's rest,
  PD-COVERAGE, PD-REDUCTION and PD-HEAD (`notes/Phase42-design.md` §3).
- **At its open**, with the PI: the placement (§1), then the opening recon, which compares every
  green node of `pencil-d.tex` with its Lean and adds a row for each departure; then the rounds,
  and a remedy per `open` row, are planned with the PI.
