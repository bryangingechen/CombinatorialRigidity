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
- **R-17** · `lem:pencil-d-chain-count` (`Graph.IsChain.partitionDef_induce_le`,
  `Grade/Chains.lean`, 42j, landed) · **open**.
  *Chapter:* the segments (the chains and the edges joining two branch bodies) partition `E(G)`,
  each body of degree two interior to exactly one, so `|E(G)| = Σ L_j` and
  `|V(G)| = |B| + Σ (L_j − 1)`; the branch bodies' degrees sum to `2e`, so `3|B| ≤ 2e`; then
  `s_D(V₁) = Σ_{j≠i} L_j − D(e − |B|) ≤ −(ℓ + 1)`.
  *Lean (landed, the recon's spike):* no edge segments. The interior bodies of the
  chains are the classes: two chains sharing an interior body have the same interior bodies
  (`Graph.IsChain.range_subset_of_mem`, walking along bodies of degree two), and every body of
  degree two lies on one (`lem:pencil-x0-chain-exists`). The edges at the interior bodies of a chain
  number one more than those bodies, and are disjoint between chains. With `T` the bodies of degree
  two and `c` the classes: `T + c ≤ |E(G)|` and `T + ℓ ≤ k + ℓc`; the handshake bound
  `3|V(G)| − T ≤ 2|E(G)|` (`Graph.IsX0Graph.three_mul_sub_le_two_mul_ncard`, from the proof of
  `lem:pencil-x0-sparse-count`) replaces the branch degrees; `|E(G[V₁])| ≥ |E(G)| − (k + 1)` is
  used as an inequality. The same final count (`e − |B|` is `|E(G)| − |V(G)|`).
  *Remedies:* the prose to the Lean (classes of bodies, the handshake bound; the proof's `\uses`
  then adds `lem:pencil-x0-sparse-count`), or keep both.
- **R-18** · `lem:pencil-d-base-case` (`hasGradedPencilRealization_of_ncard_le_two`,
  `finrank_span_rigidityRows_of_single_edge`, `Grade/Arms.lean`, 42k build 2, landed) · **open**.
  *Chapter:* the ranks are read off the motions, `D|U| − dim Z`: with one edge the motions are the
  `S` with `S(u) − S(v) ∈ K C₁`, so the rank is `D − 1`; with `m ≥ 2` edges the partition into
  singletons has value `D − (D − 1)m < 0`, so `def_d = 0`.
  *Lean (landed, the recon's spike):* the `d = 3` Lean's counts
  (`hasPencilRealization_of_ncard_le_two`), at `D`. One edge: at least the `D − 1` independent rows
  of a nonzero hinge (`lem:edge-rows-independent`), at most the target
  (`lem:relative-deficiency-rank-bound`), with `def_d = 1`. At `m ≥ 2`: `def_d = 0` as the
  subgraph of two of the edges has it (`Graph.isKDof_zero_of_parallel_pair`) and adding edges on
  the same bodies does not raise it; the rank `D` is the chapter's (`lem:theorem-55-base`).
  *Remedies:* the prose to the Lean, a Lean helper (the motions of one edge, of codimension
  `D − 1`) so that the Lean follows the chapter, or keep both.
- **R-19** · `lem:pencil-d-nonsimple-case` (`hasGradedPencilRealization_of_not_simple`,
  `Grade/Reduction.lean`, 42k build 3, landed) · **open**.
  *Chapter:* every edge joining `u` and `w` other than `e` gets `C_{B₂}`; the motions of `G` are
  those of `G/H` with `S(w) = S(u)`, of codimension `D` in them, so the rank is that of `G/H` plus
  `D`. Its closing remark cites the block-triangular count (KT eqs. (6.3)–(6.5),
  `lem:rigidityRows-splice-rank-add`) only at `d = 3`.
  *Lean (landed, the recon's spike):* the `d = 3` Lean's route
  (`hasPencilRealization_of_not_simple`), at `D`. `e ↦ C_{B₁}`, `f ↦ C_{B₂}`, and the other edges
  joining `u` and `w`, loops at `u` in `G/H`, keep their hinges there. The rank is at least `D` (the rows of `e` and `f`,
  `lem:theorem-55-base`) plus that of `G/H`, by the splice
  (`BodyHingeFramework.le_finrank_span_rigidityRows_of_splice`, at every grade), and at most the
  target (`lem:relative-deficiency-rank-bound`).
  *Remedies:* the prose to the Lean (the splice at every `D`, which also widens the remark), a
  Lean helper (the motions of `G` as those of `G/H` with `S(w) = S(u)`), or keep both.
- **R-20** · `lem:pencil-d-nondegenerate-feasible` (`gradedPencilNondegFeasible_iff`, `exists_rowsMap_two`, `exists_rowsMap_three`,
  `exists_injOn_finrank_iInf_map_le`; `Grade/Feasible.lean`, 42l build 2) · **open** (the Lean landed
  as below; the chapter's proof stays as the prose).
  *Chapter:* for (b) at one body `v` and one set `S`, pass to `W = K^(d+1)/K b_v` and
  `A_w = Π_w/K b_v`, and find `π̄ : W → K³` by induction on `dim Σ A_w`, a quotient by `c` at each
  step, `c` off finitely many proper subspaces and at most one quadric (the case
  `A₃ ⊆ A₁ ⊕ A₂`); `π` sends `b_v` to `e₄`.
  *Lean (the recon's spike):* no quotient, induction or quadric. `π`'s rows are a form `f` with
  `f(b_v) ≠ 0` and, for each `w ∈ S`, a form `μ_w` vanishing on `Π_w`, so `πΠ_w` lies in a
  coordinate hyperplane and the images meet in `K e₀` (`|S| = 3`) or a plane (`|S| = 2`, with a
  fourth form `g` vanishing at `b_v`). `π` is injective on `Π_w` when the forms vanishing on `Π_w`
  and the other two rows span those vanishing at `b_v` (`injOn_rowsMap`); each `μ_w` (and `g`) is
  chosen off at most two proper subspaces (`exists_forms_three`, `exists_mem_notMem_two`), over any
  field. The combination over all bodies and sets is the chapter's (minors in the entries of `π`,
  the `ν_w` as `cross₃`).
  *Remedies:* the prose to the Lean (shorter, no quadric), or keep both.
- **R-21** · `lem:pencil-d-lift-one-witness` (`liftAttains_of_least`,
  `liftAttains_of_holdsGenerally`; `Grade/LiftWitness.lean`, 42l build 4) · **open** (the Lean landed as below; the chapter stays as the prose).
  *Chapter:* (1) a basis `k_j(b⁰)` of `L̃(b⁰)` by Cramer's rule on a nonzero minor `M` of size
  `c − N`, the lifts by `Σ γ^i_j k_j`, `P(b⁰, γ)` a minor of size `t`, `Q₀ = M · P_α` for a
  coefficient `P_α` of `P` in `γ`. (2) the least `dim L̃` holds where `A(b⁰(s))` has the largest
  rank.
  *Lean (the recon's spike):* (1) one polynomial section `Z_i(b⁰) ∈ L̃(b⁰)` through the given lift's
  `i`-th parameter (`Matrix.exists_mvPolynomial_section_mulVec_eq_zero`, as
  `lem:pencil-d-x0-one-witness`), valid where its `D_i ≠ 0` and `dim L̃` is least;
  `Q₀ = ∏ D_i · P(lift by Z(b⁰))`, `P` the rank polynomial at the given lift; no `γ`. The bodies off
  `V(G)` are fixed at `b*` before homogenizing, so `Q` has its variables in `V(G)`. (2) `dim L̃ ≤`
  its value at a least point off the zero set of that section's `D` at `z₀ = 0`. The
  homogenization is the chapter's.
  *Remedies:* the prose to the Lean (the section, as `lem:pencil-d-x0-one-witness` already reads),
  or keep both.
- **R-22** · `lem:pencil-d-steer` (`PencilSeed.ofGamma`, `steerPoint`, `steerNormal`, `steerSet`;
  `Grade/Lift.lean`, 42l build 3) · **aligned, this commit** (42l's close).
  *Chapter (until then):* `Γ(G)` had at each body `m_v` and five auxiliary vectors, the closed
  (hub-)neighbourhood in a fixed order followed by as many of the first three, or of the last two,
  as are needed.
  *Lean (the recon's spike):* the `d = 3` chart's parameters (`PencilSeed`), `m_v` and six auxiliary
  vectors, three per selector, the one at slot `i` read when the slot is empty; the fixed order is a
  pair of selectors (`IsFin3SelectorOf`), parameters of the lemma. A neighbour selector of a body
  that is not a hub always fills a slot, so one of its three vectors is never read. Every other
  part, and the converse through `exists_pencilSeed_of_nondeg_of_selectors`, is the chapter's.
  *Remedies:* the prose to the Lean, taken at the PI's word (2026-11-04, at 42l's close,
  verbatim): "Yes, let's make it say six at the close. I guess we should make the wording clear
  that there's some flexibility in the proof here and we decided to go with six in the
  formalization even though five actually suffice." The statement takes six auxiliary vectors at
  every body, with fixed assignments of places 1 to 3 to the closed hub-neighbourhood and, off the
  hubs, the closed neighbourhood; `y_i` is the `i`-th of the first (last) three at an empty place.
  The converse chooses those at the empty places; a formalization note after the proof says that
  five suffice (a body that is not a hub fills its own place) and that the formalization takes six.
  `lem:pencil-d-ear-extend`'s proof (red) reads "the first three ..., those at the places left
  empty" to match.
- **R-23** · `lem:pencil-d-lift-transfer` (`lift_transfer`, `Grade/LiftWitness.lean`, 42l build 4)
  · **open** (the Lean landed as below; the chapter stays as the prose).
  *Chapter:* the maps `ζ ∈ L(b⁰|_(V′))^m` whose lift has rank `tgt_d(H)` form a nonempty
  Zariski-open set; by (T2) the restriction `𝓛(r⁰)^m → L(b⁰|_(V′))^m` is onto, and the preimage of a
  nonempty Zariski-open set under an onto linear map is nonempty and Zariski-open.
  *Lean (the recon's spike):* nonempty as the chapter (a lift of `r⁰|_H` of rank `tgt_d(H)`, through
  (T2)); open directly, at each `λ` of the set, by the rank polynomial of the framework on `H` at
  its normals, read in the coordinates of the maps `ζ^i`, with the bound
  (`lem:relative-deficiency-rank-bound`); (T2) is not used for openness.
  *Remedies:* the prose to the Lean, or keep both.
- **R-24** · the cases' (T1), `lem:pencil-d-lift-pendant` and `lem:pencil-d-lift-ear` (and the
  pendant triangle on their template) (`exists_minorPoly`, `liftAttains_of_pendant`,
  `liftAttains_of_ear`; 42m's recon spike, `scratch/42m/Spike.lean`) · **open** (spiked; the
  chapter stays as the prose).
  *Chapter:* `E` is a product of minors, one for each condition of nondegeneracy of `G` that reads
  only bodies of `H` and is not a condition of `H`, nonzero at `r|_H`.
  *Lean (the recon's spike):* `E` is the product of one minor per closed hub-neighbourhood in `G`
  of every body (each lies in `V(H)`, as a removed body is no hub), so the conditions already of
  `H` are included, harmlessly; at the ear, times one of `b_a · n_b`, `b_b · n_a`. One lemma
  (`exists_minorPoly`) gives each minor with its homogeneity and variables.
  *Remedies:* the prose to the Lean (shorter: no case analysis of which conditions are new), or
  keep both.
- **R-25** · `lem:pencil-d-lift-pendant`, (T1) (`pendant_T1`; 42m's recon spike) · **open** (spiked;
  the chapter stays as the prose).
  *Chapter:* two cases, `u` with at least two neighbours in `H` (a hub of `G`: `b⁰_v` in `Π⁰_u` off
  `K b⁰_u`) or with one neighbour `w` (replace `Π⁰_u` by the span of `b⁰_u, b⁰_v, b⁰_w`); the
  statement asks that `u` have another neighbour.
  *Lean (the recon's spike):* the split is on whether `u` is a hub of `G`; in the second case `b'_v`
  is off the span `W` of the normals of the closed neighbourhood of `u` in `H` (of dimension at
  most two) and `n'_u = n'_v` is orthogonal to `W` and `b'_v`, which also covers `u` with no other
  neighbour. So the hypothesis that `u` has another neighbour is unused, and the pin drops it.
  *Remedies:* the prose to the Lean, and the statement without the hypothesis, or keep both.
- **R-26** · `lem:pencil-d-lift-pendant` and `lem:pencil-d-lift-ear`, (T2) (`pendant_T2`, `ear_T2`;
  42m's recon spike) · **open** (spiked; the chapter stays as the prose).
  *Chapter:* (T2) extends a lift `(ζ, φ)` of `r⁰|_H`: `ζ_v = φ_u(b⁰_v)` with `φ_v` on `Π⁰_v` by
  its values at a basis; at the ear, `ζ_x = φ_a(b⁰_x) = φ_b(b⁰_x)` and `φ_x` by its values at
  `b⁰_a, b⁰_x, b⁰_b`.
  *Lean (the recon's spike):* `lift_transfer`'s (T2) reads the maps `L(b⁰)`, a form `ψ_y` on `K⁴`
  per body (`mem_liftMaps_iff`): the pendant puts `ζ_v = ψ_u(b⁰_v)` and reuses `ψ_u` at `u` and
  `v`; the ear puts `ζ_x = φ_a(b⁰_x)` from a lift of `r⁰|_H`, extends `φ_a` and `φ_b` to `K⁴` at `a`
  and `b` (the ear's condition at `b`), and at `x` takes a form with three prescribed values at the
  independent `b⁰_a, b⁰_x, b⁰_b` (`exists_dual_three`).
  *Remedies:* the prose to the Lean (one form per body), or keep both.
- **R-27** · `lem:pencil-d-lift-small` (1), the triangle (`linearIndependent_normalsJoin_triangle`,
  `finrank_triangle`, `liftAttains_of_triangle`; 42m's recon spike) · **open** (spiked; the chapter
  stays as the prose).
  *Chapter:* the three joins of independent normals are independent; the triangle has rank `2D`;
  its deficiency is zero, the singletons having value `2D − 3(D − 1) < 0` and two parts
  `D − 2(D − 1) < 0`.
  *Lean (the recon's spike):* the joins by three `2 × 2` minors at a dual triple
  (`exists_linearMap_normalsJoin_eq`, as `linearIndependent_join_triangle` does at fixed vectors),
  each hinge `±` the join's image as the link selector orients it; the deficiency is never
  computed: the rank `D(|V| − 1)` (rigidity) is at most the target, and the deficiency is
  nonnegative, so they agree. The ear's two joins are the same argument (`ear_rank`).
  *Remedies:* the prose to the Lean (no partition values), or keep both.

- **R-28** · `lem:pencil-d-lift-small` (2) (`liftAttains_of_cutEdges_eq_empty`, `Grade/LiftSmall.lean`,
  42m build 1) · **open** (the Lean landed as below; the chapter stays as the prose).
  *Chapter:* a realization of `G` restricts to the sides and two glue; "the lift space of `G` is the
  product of those of the sides"; the ranks add by `lem:block-rank-cut-vertex` and the targets by
  `lem:cut-edge-decomposition`; the product of the sides' polynomials serves; `G` is simple.
  *Lean:* the same steps, but the lift space is never named as a product: the lifts of the two
  sides at the restrictions are glued body by body (a form at a body of `V₁` or `V₂` reads only its
  own closed neighbourhood, which stays on its side), and the conditions of nondegeneracy are
  checked at the bodies of each side (`PencilNondegConditions.of_induce`). The glue of the
  realizations needs no rank (`exists_hasPencilPlaneRealization`, not the glue lemma of
  `Grade/Arms.lean`, whose lower bounds a bare nondegenerate realization does not have). `G.Simple`
  is not needed, and the pin drops it.
  *Remedies:* the prose to the Lean (no product of lift spaces; no simplicity), or keep both.

- **R-29** · `lem:pencil-d-lift-pendant-triangle`, and the pins of `-lift-pendant` and `-lift-ear`
  (`liftAttains_of_pendantTriangle`, `pendantTri_*`, `Grade/LiftCases.lean`, 42m build 2) ·
  **open** (the Lean landed as below; the chapter stays as the prose).
  *Chapter:* (T1) `b⁰_{x₁}, b⁰_{x₂}` in `Π⁰_c`, `Π⁰_{x_i} = Π⁰_c`; (T2) `ζ_{x_i} = φ_c(b⁰_{x_i})`,
  using `Π⁰_{x_i} = Π⁰_c` at every nondegenerate realization; the rank `2D` of the triangle, the
  ranks and the deficiencies add at `c`, the triangle's deficiency being zero; the pendant asks
  that `u` have another neighbour, the ear that `a` and `b` not be adjacent.
  *Lean:* the same, on the pendant's template. (T1) is in the polarity form: two points of
  `n_c^⊥` completing `b_c` to an independent triple, `n'_{x_i} = n_c`. (T2) puts one form `ψ_c` on
  `K⁴` at `x₁`, `x₂` and `c`, so `Π⁰_{x_i} = Π⁰_c` is never used. The triangle's deficiency is not
  computed: its rank `2D` (`finrank_triangle`) is at most the target (`finrank_liftNormal_le`) and
  the deficiency is nonnegative. The pendant's and the ear's pins drop the hypotheses above (R-25;
  the ear's rank needs no non-adjacency, `ear_rank`), each pin stronger than its node.
  *Remedies:* the prose to the Lean (no `Π⁰_{x_i} = Π⁰_c`, no partition values), or keep both.

- **R-30** · `lem:pencil-d-lift-cut-edge` (`liftAttains_of_cutEdge`, `exists_cutEdge_glue`,
  `cutEdge_T1`, `cutEdge_T2`, `cutEdge_rank`, `Grade/LiftCutEdge.lean`, 42m build 3) · **open** (the
  Lean landed as below; the chapter stays as the prose).
  *Chapter:* (T1) glues `r₁` with the image of `r₂` under a general `g ∈ 𝒢` (`g b′_u = b_u`,
  `g b′_v = b_v`); the cross conditions at `u` and `v` hold on a nonempty Zariski-open subset of `𝒢`
  exactly when `P = {b_u, b_v}^⊥ ⊄ N`, which a case analysis on `|S|` reduces to
  `E₁ = b_v · n_{w₁}` (`u`, `v` hubs, `{u, v, w₁}` the closed hub-neighbourhood of `u`), and `E₂`
  likewise; `E₂ ≠ 0` at some realization of `G₂` by replacing the normal of `u`; `|V₁|, |V₂| ≥ 2`.
  *Lean:* one `g`, a frame map with `g c_u = b_u`, `g c_v = b_v`, `gᵀ t = m_v`, `gᵀ n_u = t′`
  (`exists_frame_linearEquiv`), `t ∈ P` off the line of `n_u` and, when `v` is a hub, off the span
  `N` of the rest of the closed hub-neighbourhood of `u` (`exists_dotProduct_eq_zero_avoid`: no
  space is the union of two proper subspaces), `t′` likewise at `v`. `E₁` is one minor, `n`
  independent on the closed hub-neighbourhood of `u` in `G` (`exists_minorPoly`): its non-roots put
  `r₁`'s own `n_v ∈ P` off `N`, so `P ⊄ N`, with no case analysis on `|S|`. `E₁ ≠ 0` and the fixed
  `r₂` are the restrictions of one realization of `G`
  (`IsNondegPencilRealization.induce_union_singleton`), so no normal is replaced. (T2) and the rank
  follow the chapter; `rank G_i ≤ rank G[V_i] + D − 1` is
  `BodyHingeFramework.finrank_span_rigidityRows_le_add_of_links_subset`, and the two sides' lifts
  meet at one `λ` by `MvPolynomial.exists_mem_eval_ne_zero₂` on the image of `𝓛(r⁰)^m` in the
  maps' coordinates. `|V₁|, |V₂| ≥ 2` is unused, and the pin drops it (stronger than the node).
  *Remedies:* the prose to the Lean (one frame map, one minor, no replaced normal, no size
  hypothesis), or keep both.
- **R-31** · `lem:pencil-d-good-ear` (`Graph.IsPencilGoodEar`, `exists_goodEar_or_pendantTriangle`,
  `exists_minimalRigid_ear_or_pendantTriangle`, `Grade/GoodEar.lean`, 42m build 4) · **open** (the
  Lean landed as below; the chapter stays as the prose).
  *Chapter:* the proof of `lem:pencil-rigid-good-ear` returns the pendant triangle or `x`; (iii)
  runs the triangle argument at `x` and `a`, then `s(X) = s(W₀) + 1` and the singleton bound for
  `def₂(G[X]) = 1`, and a disconnected `G[X]` has `s(X) ≥ 3`; (iv) at every `d ≥ 3` from
  `def_d(G[X]) = 0`, the merged deficiency and the ear's bound, and a partition of `V(G)` is at
  most its restriction; (v) from (i) and `hF1`.
  *Lean:* `exists_oneEar_or_pendantTriangle`'s proof is split at its core
  (`exists_minimalRigid_ear_or_pendantTriangle`, returning `W₀`, the ear's data and the hubs; the
  old theorem is now its corollary, statement unchanged), and `closedEar_two_of_triangle` states
  the pendant triangle with its end explicit (the end's degree at least four). (iii)'s
  `def₂(G[X]) = 1` is the partition case split at `n = 2` (`deficiency_two_induce_le_one_of_tight`,
  beside `deficiency_three_induce_eq_zero_of_tight`'s at `n = 3`), connectivity is
  `preconnected_of_deficiency_two_lt` (a component with no edge across adds `D = 3` by
  `deficiency_eq_of_cutEdges_ncard_le_one`, not through `s`), and the two-neighbour step for
  an end is the triangle lemma's hypothesis at `(x, a)`. (iv)'s lower bound is
  `partitionDef_induce_insert` at `x` with two edges to the other labels. The index of
  `deficiency n` is the chapter's `d` (`bodyBarDim 2 = 3`, `(i)`'s `s` is `partitionDef 2 id`).
  The pin adds the first outcome as `∃ x₁ x₂ c` (the chapter's two adjacent bodies of degree two
  with a common neighbour of degree at least four).
  *Remedies:* the prose to the Lean (no `s(X)` for connectivity), or keep both.
- **R-32** · `lem:pencil-d-lift-no-rigid` (`liftAttains_of_forall_deficiency_two_ne_zero`,
  `exists_planeDiff_ne_zero_poly`, `finrank_liftSpaceTilde_pencilConfigPoint`,
  `exists_pencilConfigPoint_of_dotProduct`, `Grade/LiftNoRigid.lean`, 42m build 5) · **open** (the
  Lean landed as below; the chapter stays as the prose).
  *Chapter:* `q` off Jackson and Jordán's polynomial, `dim L(q) = ℓ₀ = 3 + def₂(G)`; at `r*`,
  `dim L̃ = dim L(b⁰) + |V(G)|` by the spanning of the closed neighbourhoods; at a general spanning
  realization a map `g` of `K⁴` (`g b⁰_v` of nonzero last coordinate, `e₃ ∉ gΠ⁰_v`) and a rescaling
  give a configuration over an admissible `q'`, so `dim L̃ ≥ ℓ₀ + |V(G)|`.
  *Lean:* `q` off the main-picture polynomial (`Graph.exists_mvPolynomial_isMainPicture`; only
  `dim L(q) ≤ dim L(q')` is used, never `ℓ₀`). One point of the space of the `r + 1` heights and
  the first one's planes makes the attaining and planes polynomials nonzero
  (`exists_mem_eval_ne_zero₂`). At every configuration with `z ∈ L(q)`, spanning or not,
  `dim L̃ = dim L(q) +` the free coordinates (`liftFreeCoords`: maps and forms off `V(G)`, the third
  coordinate of each form), by two injective maps through the lifting system's kernel. No `g`: the
  two nonzero coordinates and three independent points per closed neighbourhood (`q`'s admissible
  triples; the chapter's spanning) hold generally, witnessed at `r*`; the rescaled points of such a
  realization are the configuration (`exists_pencilConfigPoint_of_dotProduct`).
  *Remedies:* the prose to the Lean (no `g`, no `ℓ₀`, `dim L̃` through the lifting system), or keep
  both.

- **R-33** · `lem:pencil-d-ear-extend` (`exists_earExtend_poly`, `exists_earExtend_cond_poly`,
  `exists_linearIndepOn_of_finrank`, `Grade/EarFree.lean`, 42m build 6) · **open** (the Lean landed
  as below; the chapter stays as the prose).
  *Chapter:* a witness `t′` of (a) and (b) together, the `m_h` at distinct points of the moment
  curve (every four independent) and the auxiliary vectors completing bases; the `n_u ∈ A_u` by
  the case analysis on `O_v` (`{u}`, or `{u, u′}` with `n_{u′}` chosen before `n_u`).
  *Lean:* one witness per condition, the slots of `b_v` (and `m_u`) the standard basis at
  distinct places of `Γ(G)`, and `E_L` the product (no moment curve). (b) is asked at every `u`
  off the selector of `v`, not only at the hubs. The `n_u` are chosen one closed
  hub-neighbourhood at a time, greedily in any order: each `A_u` has dimension at least three
  (`u`'s only neighbour in `X` is `v`), or at least two and misses `m_v` (by (b) at a second
  neighbour), so it is never inside the span of at most two chosen vectors containing `m_v`. The
  pin drops `G` simple and the neighbour selector (unused), stronger than the node.
  *Remedies:* the prose to the Lean (one witness per condition, the greedy choice), or keep both.

- **R-34** · `lem:pencil-d-ear-free` (`holdsGenerally_earFree`, `earFree_of_finrank_liftSpaceTilde_le`,
  `exists_earFree_config`, `exists_earFree_gammaL`, `Grade/EarFree.lean`, 42m build 6b) · **open**
  (the Lean landed as below; the chapter stays as the prose).
  *Chapter:* (c) is `dim L̃_Y(b) ≤ |X| + 4`; under (a) `dim L̃_Y = dim L_Y(b) + |X|`, so `L_Y(b)` is
  the trivial maps; (a) is read with "rank at most three wherever it is read", argued on `Γ_L`, at
  `Γ(G)` and at the configuration; (b) at the configuration by "a vanishing form makes `z` globally
  affine (all planes agree) or puts the picture points on a line"; each condition open as "some
  minor of a fixed size is nonzero"; `t₁` a non-root of the product with `E_L`.
  *Lean:* `L̃` lives on all of `α`, so (c) is `≤ 4 +` the free coordinates (`liftFreeCoords`: `|X|`
  plus five per body off `X`). The trivial lifts and the free coordinates, the third coordinate of
  each form moved along a normal `n_v` of its closed neighbourhood, embed in `L̃`
  (`liftTildeOfTrivial`), so by (c) they are all of it; `L_Y(b)` and the count `dim L̃ = dim L + |X|`
  are not used. Rank at most three is used only at a realization in `U(G)` (the points of a closed
  neighbourhood in a three-dimensional subspace), never on `Γ_L`; only rank at least three is
  carried, as the independence of `q`'s admissible triples. (b) at the configuration: a vanishing
  form is a multiple of the plane normals of two distinct bodies, which are independent
  (`span_pencilConfigPoint_eq_top`); it is carried as the independence of the points on a fixed set
  of four bodies (`exists_linearIndepOn_extension`). (c) is open at every point by the section of
  `liftMatrixPoly` (`isZariskiOpen_finrank_liftSpaceTilde_le`). The planes' solution comes from
  `exists_planeDiff_ne_zero_poly` itself (no fibre intersection here). `t₁` is a common non-root
  (`IsZariskiOpen.exists_mem_inter`). `H_L[v]` has three members only with `v` among them, as a
  body that is not a hub has at most three members in its closed neighbourhood.
  *Remedies:* the prose to the Lean (the embedding by dimension, rank at most three only in `U(G)`,
  (b) by two plane normals), or keep both.

## 3. The cleanup (not yet planned)

- **Until it opens:** the standing rule (§1) keeps §2 current through PD-STEPS's rest,
  PD-COVERAGE, PD-REDUCTION and PD-HEAD (`notes/Phase42-design.md` §3).
- **Also left to it** (not a route row): Theorem S's fold, `Graph.IsX0Graph.exists_additiveCore`
  (`MainComponent/CoverageTheoremS.lean`) as the `n = 3` case of
  `Graph.IsX0Graph.exists_additiveCoreAt` (`Grade/TheoremS.lean`, which imports that file), with a
  bridge `Graph.ChainUsable ↔ Graph.ChainUsableAt 3`. It reverses the import, so COUNT-B's
  lemmas move upstream of the `d = 3` coverage; no node of PD-COVERAGE uses Theorem S at `D` (42j's
  recon, `notes/Phase42j.md`).
- **Also left to it** (not a route row): the `d = 3` cases of the reduction (`Pencil/Arms.lean`,
  `hasPencilRealization_of_not_simple` in `Pencil/X0.lean`) as the `m = 1` case of 42k's graded
  ones (`Grade/Arms.lean`, `Grade/Reduction.lean`) through `hasGradedPencilRealization_two_iff`. It
  reverses the imports, as Theorem S's fold does (FRICTION *42k's cases repeat the `d = 3` cases'
  proofs*).
- **Also left to it** (not a route row): two instances no `main_results` witness exhibits. (1) The
  generic conjunct's hypothesis at a small graph. Phase 42's one `main_results` row, the headline
  `Graph.graded_pencil_conditioned_pair`, has a witness of its distinct conjunct only (the PI's
  (A) without (C), `notes/Phase42-design.md` §1, 2026-11-05), as the two `d = 3` pencil rows do,
  so no row's witness meets the generic conjunct's feasibility hypothesis, whose satisfiability
  `#print axioms` cannot see (F-207, F-252). The likely witness: `K₂`, by
  `PencilNondegFeasible.mono` from `exists_isNondegPencilRealization_parallel_pair` through
  `gradedPencilNondegFeasible_iff` (not spiked). (2) Beside it, an instance of the two predicates
  42m introduced, `Graph.IsPencilGoodEar` and `EarLiftCondition`; the candidate is `K_{2,3}`
  (`W₀` all five bodies, `x` a body of degree two; `s(W₀) = 3·4 − 2·6 = 0`, `X` a four-cycle with
  `s = 1`; `notes/Phase42m.md` *Blockers*). It would witness an inner arm of the induction, not a
  hypothesis of the headline.
- **At its open**, with the PI: the placement (§1), then the opening recon, which compares every
  green node of `pencil-d.tex` with its Lean and adds a row for each departure; then the rounds,
  and a remedy per `open` row, are planned with the PI.
