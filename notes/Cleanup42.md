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

## 3. The cleanup (not yet planned)

- **Until it opens:** the standing rule (§1) keeps §2 current through PD-STEPS's rest,
  PD-COVERAGE, PD-REDUCTION and PD-HEAD (`notes/Phase42-design.md` §3).
- **At its open**, with the PI: the placement (§1), then the opening recon, which compares every
  green node of `pencil-d.tex` with its Lean and adds a row for each departure; then the rounds,
  and a remedy per `open` row, are planned with the PI.
