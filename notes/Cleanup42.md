# The post-Phase-42 cleanup (planning note)

**Status:** open (2026-11-05, at the PI's word, §1), ahead of ORIGAMI; round 1, the route audit,
closed 2026-11-05 at its planned stop (`notes/Phase42-cleanup.md`). On 2026-10-30, during 42g, the
PI asked for a cleanup phase after Phase 42 to address the informal proofs of
`blueprint/src/chapter/pencil-d.tex` that were difficult to formalize as written (§1). On 2026-11-05
the PI opened it ahead of ORIGAMI and shaped its first round: an audit of every green node of the
chapter (99) against its Lean, adding a row to §2 for each departure, with no prose or Lean edit,
then a stop at which the PI picks a remedy per `open` row and plans rounds 2+ (§3).
`.claude/autopilot/queue.toml` carries it as `CLEANUP-42`, attended, between PENCIL-D (done) and
ORIGAMI; ROADMAP *Queued post-program phases* lists it. Its input is the proof-route ledger (§2): 34
rows at Phase 42's close (2026-11-05), 27 `open`, 6 `aligned`, 1 `no departure`, to which round 1
added; at its close, 54 rows, 34 `open`, 6 `aligned` and 14 `no departure` (R-35, R-46, R-48 to R-51
and R-53 `open`, R-36 to R-45, R-47, R-52 and R-54 `no departure`; R-1 to R-34 re-checked, R-7, R-9,
R-12, R-15 to R-17, R-24 to R-27, R-31, R-32 and round 1's R-50 corrected in place). The open rows
by family: §3 *Round 1's stop*. The PI answered the stop on 2026-11-05 (§1): family A to the Lean
(R-46 kept), families B and C judged per row first, no close call reopened, rounds 2+ as proposed.
**Next concrete task:** the B/C judgment recon, one Opus recon proposing L, K or H for each of the
22 B/C rows of §3 *Round 1's stop*, then a short second stop for the PI's approval; round 2 opens
after it (§3).

## 1. The PI's decisions (verbatim)

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

### 2026-11-05: the open, ahead of ORIGAMI, and round 1

From the coordinator's open check-in after Phase 42's close: each question, then the option the PI
chose with its description.

**PI, 2026-11-05:** (verbatim)
- Q: "CLEANUP-42 is queued but not open. It covers the pencil-d.tex proofs whose Lean departs from
  the chapter's route: 34 ledger rows, 27 still open, in notes/Cleanup42.md. Running it before
  ORIGAMI was only the coordinator's proposal, and you never answered it. Open CLEANUP-42 now, ahead
  of ORIGAMI?" — A: "Yes, open now (Recommended)" — "Open CLEANUP-42 now and record your answer as
  the placement decision (ahead of ORIGAMI) in notes/Cleanup42.md §1."
- Q: "How should the opening be shaped? The plan says the first step compares every green node of
  pencil-d.tex (99 of them) with its Lean and adds a ledger row for each departure. The rounds, and
  a fix for each open row, are then planned with you." — A: "Audit round, then stop (Recommended)"
  — "Round 1 (notes/Phase42-cleanup.md) is the full-chapter audit: opus recons sliced by layer,
  starting with 42b–42f, which were never checked, and adding ledger rows only, with no prose or
  Lean edits. Then stop so you pick a fix per open row and plan the later rounds."

What follows from it:

- **The placement is the PI's decision:** CLEANUP-42 runs now, after Phase 42 and ahead of ORIGAMI.
  It opened on 2026-11-05.
- **Round 1 is the route audit** (`notes/Phase42-cleanup.md`): Opus recons, one slice of the
  chapter's nodes per dispatch, by layer, 42b–42f first; each adds rows to §2 and re-checks the
  rows on its nodes, and edits no prose, statement, pin or Lean.
- **Then the planned stop:** the PI picks a remedy per `open` row and plans rounds 2+ (§3).

### 2026-11-05: round 1's stop, the remedies and rounds 2+

From the coordinator's relay of round 1's `NEEDS_PI` entry (`notes/Phase42-cleanup.md` *Autopilot:
for the PI*): each question, then the option the PI chose with its description.

**PI, 2026-11-05:** (verbatim)
- Q: "CLEANUP-42's audit left 34 open rows where the Lean departs from pencil-d.tex. Family A (12
  rows): the pin drops a hypothesis the node states, such as G simple, K infinite or a nonzero
  normal. Families B and C (22 rows): the Lean proves a step by another argument, or skips, adds or
  reorders steps. The remedies are L (restate the chapter to the Lean), H (a Lean helper so the
  Lean follows the chapter; offered for R-3, R-4, R-11, R-18 and R-19) and K (keep both). Which
  remedies should round 2 apply?" — A: "A: L; B/C judged per row" — "Restate the 12 family-A
  statements to their pins; R-46 is kept, as its recon recommends. Before round 2, one Opus recon
  judges each of the 22 B/C rows (which route reads better) and proposes L, K or H per row, for you
  to approve at a short second stop."
- Q: "Four 'no departure' rows are close calls where the Lean drops a hypothesis judged vacuous,
  recovered from the others, or part of the setting. R-36: no `r ∈ W`. R-38: no separate case
  `Z = V(G)`. R-44: no `ℓ ≥ 1`, vacuous at `ℓ = 0`. R-54: the generic theorem reads less where its
  case pins drop hypotheses. Reopen any of them as open rows?" — A: "Reopen none (Recommended)" —
  "Leave all four as recorded. They are encodings or vacuous drops, with nothing to align."
- Q: "How should the rounds after the audit run? The proposal: round 2 brings the chapter to the
  Lean (blueprint and notes only, about 11 tasks, including the two prose slips and the 60 missing
  \uses edges). Round 3 is Lean helpers, only if a row goes H (1–6 tasks). Round 4 is the 'also
  left' items, Lean, about 5–7 tasks: the Theorem S fold, the d = 3 reduction fold, and non-vacuity
  witnesses at K₂ and K_{2,3}." — A: "The proposal as written (Recommended)" — "Prose round first,
  then helpers if any, then the folds and witnesses last, since they reverse imports and move d = 3
  pins."

What follows from it:

- **Family A** (§3 *Round 1's stop*): each statement restated to its pin (L), except R-46, kept
  (K) as its recon leans.
- **Families B and C** (22 rows): one Opus recon proposes L, K or H per row, with which route reads
  better; a short second stop, at which the PI approves or amends, precedes round 2.
- **No close call reopened:** R-36, R-38, R-44 and R-54 stay `no departure`.
- **Rounds 2+ as proposed** (§3): round 2 the chapter to the Lean (no Lean), round 3 Lean helpers if
  any row goes H, round 4 the *Also left to it* items.

## 2. The proof-route ledger

One row per node of `pencil-d.tex` whose Lean proof departs from the chapter's, in the chapter's
notation. *Status* is `open`, or `aligned` with the commit that made the chapter and the Lean follow
one route (`this commit` in that commit; a later edit may replace it with the sha), or `no
departure` for a row raised and then judged a carrier encoding of the chapter's own object, kept as
a short row so that the cleanup's recon does not raise it again. *Remedies* are the options: the
prose to the Lean, a Lean helper so that the Lean can follow the chapter, or keep both routes, each
valid. The cleanup chooses one per `open` row, with the PI. Round 1's rows (from R-35) name their
task in `notes/Phase42-cleanup.md`, and its re-checks of R-1 to R-34 are recorded there.

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
  the restated parts, on forms since 42i (R-13).
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
  *Lean:* if no `ξ₁` exists, `M_wξ₀ ∉ range M(y₀)`. With `M(y₀)u_j` a basis of that range, of
  dimension `r`, the family `M(y₀ + tw)u_j`, `M_wξ₀ + tM₂(t)ξ₀` is independent at `t = 0`, hence
  at some `t ≠ 0`, and lies in the range of `M(y₀ + tw)`, which sends `t⁻¹ξ₀` to its last member;
  so `M(y₀ + tw)` has rank `r + 1`, against the generic rank. The generic minor is the same.
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
  *Lean:* `Graph.X0AttainsGrade.of_openEar_splitOff` (since 42i the corollary, at `Pq = Rz = 1`,
  of `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`, which carries the two stages) takes the
  put-back as a hypothesis `hins`;
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
  rank openness (`exists_mvPolynomial_le_finrank_span_of_repr`) at a height whose first `min(m, r)`
  rows are independent and the others zero. The proof extends a family of lifting planes of
  `G[V₁]` along the ear (`exists_mem_liftingPlanes_extend_ear`), as the chapter does by
  `ℓ₁, ℓ₂, ℓ₃`; the Lean keeps
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
  backwards), whose value is at most `def₂(G)`, counted by `dim F(q) = 3|V(G)ᶜ| + 3 + def₂(G)` at
  the pictures of Jackson–Jordán's polynomial for `G` (`thm:pencil-jj-equality` with
  `lem:pencil-lifting-planes-dim`; only its `≥` half, the bound of
  `lem:pencil-lifting-space-deficiency`, is used, and that lemma is not called). The Lean takes
  every number of heights, not only `d ≥ 3`.
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
  number at least one more than those bodies (the chain's own `k + 1` edges,
  `Graph.IsOpenEar.range_subset_inc`), and are disjoint between chains. With `T` the bodies of
  degree two and `c` the classes: `T + c ≤ |E(G)|` and `T + ℓ ≤ k + ℓc`; the handshake bound
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
  `lem:pencil-d-ear-extend`'s proof (green) reads "the first three ..., those at the places left
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
  `liftAttains_of_ear`, `liftAttains_of_pendantTriangle`; 42m's recon spike, landed in
  `Grade/LiftCases.lean` at 42m build 2) · **open** (spiked; the chapter stays as the prose).
  *Chapter:* `E` is a product of minors, one for each condition of nondegeneracy of `G` that reads
  only bodies of `H` and is not a condition of `H`, nonzero at `r|_H`.
  *Lean (the recon's spike):* `E` is the product of one minor per closed hub-neighbourhood in `G`
  of every body (each lies in `V(H)`, as a removed body is no hub), so the conditions already of
  `H` are included, harmlessly; at the ear, times one of `b_a · n_b`, `b_b · n_a`. One lemma
  (`exists_minorPoly`) gives each minor with its homogeneity and variables.
  *Remedies:* the prose to the Lean (shorter: no case analysis of which conditions are new), or
  keep both.
- **R-25** · `lem:pencil-d-lift-pendant`, (T1) (`pendant_T1`; 42m's recon spike, landed in
  `Grade/LiftCases.lean` at 42m build 2) · **open** (spiked; the chapter stays as the prose).
  *Chapter:* two cases, `u` with at least two neighbours in `H` (a hub of `G`: `b⁰_v` in `Π⁰_u` off
  `K b⁰_u`) or with one neighbour `w` (replace `Π⁰_u` by the span of `b⁰_u, b⁰_v, b⁰_w`); the
  statement asks that `u` have another neighbour.
  *Lean (the recon's spike):* the split is on whether `u` is a hub of `G`; in the second case `b'_v`
  is off the span `W` of the normals of the closed neighbourhood of `u` in `H` (of dimension at
  most two) and `n'_u = n'_v` is orthogonal to `W` and `b'_v`, which also covers `u` with no other
  neighbour. So the hypothesis that `u` has another neighbour is unused, and the pin drops it.
  *Remedies:* the prose to the Lean, and the statement without the hypothesis, or keep both.
- **R-26** · `lem:pencil-d-lift-pendant` and `lem:pencil-d-lift-ear`, (T2) (`pendant_T2`, `ear_T2`;
  42m's recon spike, landed in `Grade/LiftCases.lean` at 42m build 2) · **open** (spiked; the
  chapter stays as the prose).
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
  `finrank_triangle`, `liftAttains_of_triangle`; 42m's recon spike, landed in `Grade/LiftSmall.lean`
  at 42m build 1) · **open** (spiked; the chapter stays as the prose).
  *Chapter:* the three joins of independent normals are independent; the triangle has rank `2D`;
  its deficiency is zero, the singletons having value `2D − 3(D − 1) < 0` and two parts
  `D − 2(D − 1) < 0`.
  *Lean (the recon's spike):* the joins by three `2 × 2` minors at a dual triple
  (`exists_linearMap_normalsJoin_eq`, as `linearIndependent_join_triangle` does at fixed vectors),
  each hinge `±` the join's image as the link selector orients it; the deficiency is never
  computed: the rank `D(|V| − 1)` (rigidity) is at most the target, and the deficiency is
  nonnegative, so they agree. The ear's two joins are the same argument
  (`linearIndependent_normalsJoin_pair`, in `ear_rank`).
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
  (`exists_minimalRigid_ear_or_pendantTriangle`, returning `W₀`, the ear's data, the hubs,
  `|X| ≥ 3` (R-53) and `s(X) ≤ 1`, the latter by adding `x` with its two edges as (iii) does; the
  old theorem is now its corollary, statement unchanged), and `closedEar_two_of_triangle` states
  the pendant triangle with its end explicit (the end's degree at least four). (iii)'s
  `def₂(G[X]) = 1` is the partition case split at `n = 2` (`deficiency_two_induce_le_one_of_tight`,
  beside `deficiency_three_induce_eq_zero_of_tight`'s at `n = 3`), connectivity is
  `preconnected_of_deficiency_two_lt` (a component with no edge across adds `D = 3` by
  `deficiency_eq_of_cutEdges_ncard_le_one`, not through `s`), and the two-neighbour step for
  an end is the triangle lemma's hypothesis at `(x, a)`. (iv)'s lower bound is
  `partitionDef_induce_insert` at `x` with two edges to the other labels. The index of
  `deficiency n` is the chapter's `d` (`bodyBarDim 2 = 3`, `(i)`'s `s` is `partitionDef 2 id`).
  The pin's first outcome is the node's, `∃ x₁ x₂ c` (two adjacent bodies of degree two with a
  common neighbour of degree at least four), as the core returns it; the `d = 3` pin's is a closed
  ear (`exists_closedEar_two_of_triangle`).
  *Remedies:* the prose to the Lean (no `s(X)` for connectivity), or keep both.
- **R-32** · `lem:pencil-d-lift-no-rigid` (`liftAttains_of_forall_deficiency_two_ne_zero`,
  `exists_planeDiff_ne_zero_poly`, `finrank_liftSpaceTilde_pencilConfigPoint` and its `_ker`,
  `exists_pencilConfigPoint_of_dotProduct`, `Grade/LiftNoRigid.lean`, 42m build 5) · **open** (the
  Lean landed as below; the chapter stays as the prose).
  *Chapter:* `q` off Jackson and Jordán's polynomial, `dim L(q) = ℓ₀ = 3 + def₂(G)`; at `r*`,
  `dim L̃ = dim L(b⁰) + |V(G)|` by the spanning of the closed neighbourhoods; at a general spanning
  realization a map `g` of `K⁴` (`g b⁰_v` of nonzero last coordinate, `e₃ ∉ gΠ⁰_v`) and a rescaling
  give a configuration over an admissible `q'`, so `dim L̃ ≥ ℓ₀ + |V(G)|`.
  *Lean:* `q` off the main-picture polynomial (`Graph.exists_mvPolynomial_isMainPicture`; only
  `dim L(q) ≤ dim L(q')` is used, never `ℓ₀`). One point of the space of the `r + 1` heights and
  the first one's planes makes the attaining and planes polynomials nonzero
  (`exists_mem_eval_ne_zero₂`). At every configuration with `z ∈ L(q)`, spanning or not, `dim L̃`
  is the dimension of the lifting system's kernel at `q` plus the free coordinates
  (`liftFreeCoords`: maps and forms off `V(G)`, the third coordinate of each form), by two
  injective maps (`finrank_liftSpaceTilde_pencilConfigPoint_ker`); over an admissible picture, as
  `q` and `q'` are, the kernel has dimension `dim L(q)` (`Graph.finrank_ker_liftingMatrix`), so
  `dim L̃ = dim L(q) +` the free coordinates (`finrank_liftSpaceTilde_pencilConfigPoint`). No `g`:
  the two nonzero coordinates and three independent points per closed neighbourhood (`q`'s
  admissible triples; the chapter's spanning) hold generally, witnessed at `r*`; the rescaled
  points of such a realization are the configuration (`exists_pencilConfigPoint_of_dotProduct`).
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

- **R-35** · `lem:pencil-d-agrees-three`, its first sentence (`hasPencilPlaneRealization_two_iff`,
  `Grade/Realization.lean`, round 1 task 2) · **open**.
  *Chapter:* the points `q_v` are nonzero, with `Π_v = q_v^⊥`. As the dot product is nondegenerate,
  `Π_v^⊥` is the span of `q_v`, so passing through `Π_v^⊥` is passing through `q_v`
  (`lem:extensor-through-flat-point`), and `b_v ∈ Π_v` is `q_v · b_v = 0`. That `Π_v` is
  three-dimensional and `q_v` nonzero is left to the hypothesis.
  *Lean:* no `q_v ≠ 0`: the hypothesis is `Π_v = q_v^⊥` on `V(G)` alone, and the two definitions
  are matched condition by condition (the hinge-coplanar realization, a condition of both, is not
  assumed either). Two are the chapter's steps (`dotPerp_dotPerp`,
  `extensorThroughSubspace_span_singleton_iff`, `mem_dotPerp_span_singleton`); the third is added:
  `q^⊥` is three-dimensional exactly when `q ≠ 0` (`finrank_dotPerp`), which matches the dimension
  of `def:pencil-d-realization` with the nonzero point of `def:pencil-panel-realization`. So the pin
  is stronger than its node, and a caller reads `n_v ≠ 0` off it
  (`isNondegPencilPlaneRealization_two_iff`, `Grade/Nondegenerate.lean`, on task 13's
  `lem:pencil-d-nondegenerate-three`). The second sentence
  (`exists_hasPencilPlaneRealization_two_iff`) is the chapter's.
  *Remedies:* the prose to the Lean (the statement without "nonzero", the proof with the sentence
  on the dimension; its `\uses` unchanged), or keep both (the points of a pencil realization are
  nonzero). The recon leans to the prose: one word and one sentence.

- **R-36** · `lem:pencil-d-contract-magnified-rank`, its `r ∈ W`
  (`Graph.finrank_span_rigidityRows_induce_contractHeightGrade_eq`, `Grade/Contract.lean`, round 1
  task 3) · **no departure**: the pin takes any `r`, with no `r ∈ W`, as the curve
  `contractPicture` is total in `r`. The chapter's `r ∈ W` is the setting of
  `def:pencil-contract-lifting-system` (the curve "defined for every `W` and every `r ∈ W`"), and
  its proof never reads it; the `d = 3` pin
  (`Graph.finrank_span_rigidityRows_induce_contractHeight_eq`) takes any `r` too. The rest is the
  chapter's proof: its map of `K^(d+1)`, with its inverse, at the bodies of `W`, then the
  collineation.

- **R-37** · `lem:deficiency-stable`, its equality
  (`Graph.Connected.deficiency_eq_of_deficiency_two_add_three_le`, `Molecular/Deficiency.lean`,
  round 1 task 4) · **no departure**: the chapter shows that at every `D ≥ D′` the deficiency is the
  largest `|P| − 1` over the partitions with `c(P) = 0`; the pin never forms that maximum. It proves
  the equality by antisymmetry: `def_d ≤ def_{d′}` is `lem:deficiency-antitone`
  (`Graph.Connected.deficiency_le_deficiency_of_le`), which the proof `\uses`, and for
  `def_{d′} ≤ def_d` it bounds the value of each partition at `D′` by the chapter's case split, its
  value at `D` when `c(P) = 0`, at most `t − (D′ − 3) ≤ 0 ≤ def_d` when `c(P) ≥ 1`
  (`deficiency_nonneg`, the partition `{V(G)}`). The antitone lemma is the chapter's formula
  `|P| − 1 − (D − 1) c(P)` read with `c(P) ≥ 0`, so the steps are the chapter's. The "in particular"
  (`Graph.Connected.deficiency_eq_of_two_add_deficiency_two_le`) bounds `D′ ≥ d′ + 1 ≥ t + 3`
  (`d′ ≥ 2`), where the chapter goes through `binom(t + 3, 2)`: arithmetic.

- **R-38** · `lem:deficiency-tight-part`, its case `Z = V(G)`
  (`Graph.IsTightPartition.deficiency_induce_eq_zero`, `Molecular/Induction/SparseDeficiency.lean`,
  round 1 task 5) · **no departure**: the chapter sets `Z = V(G)` apart (then `P = {V(G)}` has value
  `0`, so `def_d(G) = 0`), as `lem:separated-partition-value` asks `∅ ≠ V′ ≠ V(G)`; the pin has no
  case split. The pin of that lemma (`partitionDef_split_of_sides`) asks neither side nonempty: at
  `V′ = V(G)` the side `G[∅]` has no part and no edge, so its value is `D(0 − 1) = −D` under every
  labeling, which the split's `+ D` cancels (a `lake lean` probe at HEAD). So the chapter's other
  case, the refinement `R` of `Z` glued to `P` outside it (`exists_glue`) and split, covers every
  `Z`, and `{Z}` attains the bound (`deficiency_nonneg`). The pin is at every `n`, for the part of
  each body `u`.

- **R-39** · `thm:pencil-d-flat-rank`, its proof's second paragraph
  (`Graph.finrank_span_rigidityRows_ofNormals_flat_grade`, `Grade/Flat.lean`, round 1 task 6) ·
  **no departure**: the proof gives the exact rank twice. Its first paragraph is the Lean's: with no
  height the points are the homogeneous picture points
  (`pencilConfigPointGrade_eq_pencilPicturePoint`), so the rank is the plane framework's
  `3|V(G)| − dim L(q)` (`Graph.finrank_span_rigidityRows_ofNormals_pencilPicturePoint`), and the
  `d − 2` zero heights add `(D − 3)(|V(G)| − 1)` (`lem:pencil-d-embed-config-rank` at `d′ = 2`:
  `Graph.finrank_span_rigidityRows_ofNormals_pencilConfigPointGrade_padHeights` at `m′ = 0`, the
  padding of no height being the zero heights). Its second paragraph carries the `d = 3` proof's
  count of motions to every dimension (the component in a complement of `⋀²Ĥ` constant, that in
  `⋀²Ĥ` a family of lifting planes, so `D − 3 + dim L(q)` motions, then rank–nullity). It is
  sound, and no Lean follows it; the first paragraph is complete without it, so it stands as the
  comparison with `d = 3` that the chapter's nodes close with, here written out as a second proof.

- **R-40** · `lem:pencil-d-polygon-collapse`, its pins at index level (`polygonCollapse`,
  `polygonCollapseEdge` and five lemmas, `Grade/Polygon.lean`, round 1 task 8) · **no departure**:
  no pin names the closed `D`-gon `Y` or a join. `polygonCollapse N M` is `π_M` read as vertex
  indices (`j ↦ N − 1` at the last body, else `min(j, N − 2)`), and `polygonCollapseEdge N M` lists
  the proof's `D` edges (`l ↦ l` for `l ≤ N − 3`, then `M − 2` and `M − 1`, the last from `c_{M−1}`
  to the cyclic `c_0`). `polygonCollapse_polygonCollapseEdge` gives `π(e_l) = l` and
  `π(e_l + 1) = l + 1` at every `2 ≤ N ≤ M`, so with `c_j` at `Y_{π(j)}` the join at `e_l` is
  `Y_l ∨ Y_{l+1} = J_l`: the proof's computation, its last rewrite left to the two theorems. Part (2)
  is part (1) at `M = k + 1` with `b` at the vertex of `c_0`, as the proof derives it
  (`polygonCollapse_zero`, `_one`, `_neg_one` for `a`, `x_1`, `x_k`; `b` at `Y_0` is the ear
  theorem's placement). The distinctness pin, `polygonCollapseEdge_injective`, is dead: `D`
  independent joins at a family of edges bound the span of its hinges whether or not an edge repeats
  (`card_le_finrank_of_linearIndependent_normalsJoin`, `Grade/Chain.lean`), and the ear's proof says
  "distinct" without its count using it.

- **R-41** · `lem:pencil-d-ear-data`, part (1), the picture of the base data
  (`Graph.earHeightGrade_mem_liftingSpaceGrade`, `Grade/EarData.lean`, round 1 task 9) · **no
  departure**: the pin takes the base heights in `L_{G[V₁]}(q)^{d−2}` and the planes `la`, `lb` at
  the admissible picture `q` it is applied at, where the definition fixes them at `q₁`. The move
  from `q₁` to `q(s)`, equal on `V₁`, for which the proof cites `lem:pencil-picture-local`, is made
  where the base data are built, for every ear datum (`Graph.liftingSpace_congr` in
  `Graph.exists_earBase_splitOff_grade`, `Grade/Short.lean`, which `thm:pencil-d-open-ear-four`'s
  pin reaches): the pin's hypotheses there are that lemma's conclusion, which is why
  `scripts/blueprint-deps.py` calls the edge to it *unbacked*. The `d = 3` pin
  (`Graph.earHeight_mem_liftingSpace`) has the same shape. The rest is the proof's: the `d = 3`
  lemma height by height, the plane of height `i` the coefficients `la i` of `σ_a`.

- **R-42** · `thm:pencil-d-open-ear-four`, the planes of its base data
  (`Graph.exists_earBase_splitOff_grade`, `Grade/Short.lean`, round 1 task 9) · **no departure**:
  the chapter takes `σ_a`, `σ_b` "whose images `Π_a` and `Π_b` are spanned by the points of
  `(q*, z*)` at the closed neighbourhoods of `a` and `b` in `G″`", citing
  `lem:pencil-d-condition-linear`. The Lean takes for `σ_a` that lemma's `σ_v` (`gradeSigma la`) at
  the coefficients `la` of the affine functions `z*` agrees with on that neighbourhood, read off
  `z* ∈ L_{G″}(q*)^{d−2}` (`def:pencil-lifting-space`), and never forms the span
  (`Graph.IsAdmissiblePicture.span_pencilConfigPointGrade_closedNbhd_eq_range` is not called). What
  the next sentence uses, that the points there are `σ_a(q*(w), 1)`, so that `(q*, z*)` is the
  configuration of one ear datum, is those affine functions read through `σ_v`; the span is the
  chapter's description of the plane (as before `def:pencil-d-ear-data`), true by the lemma's
  second sentence. The pin reaches the lemma for `σ_v` and its injectivity alone (`Π_a ≠ 0`, for
  stars-four's polynomial).

- **R-43** · `lem:pencil-d-planes-meet`, its planes, and those of `thm:pencil-d-open-ear-three`'s
  first stage (`Graph.exists_mvPolynomial_planesMeet`, `Grade/PlanesMeet.lean`;
  `Graph.X0AttainsGrade.of_openEar_three`, `Grade/ShortThree.lean`; round 1 task 10) · **no
  departure**: the lemma states `Π_a`, `Π_b` as the spans of the points of `(q, z)` at the closed
  neighbourhoods, and its proof cites `lem:pencil-d-condition-linear` for `Π_a` the image of the
  injective `σ_a`. The pin takes them as the ranges of `gradeSigma la` and `gradeSigma lb` at any
  `la`, `lb` with which `z` agrees there (some exist, as `z ∈ L_G(q)^{d−2}`), the phase's pinned
  encoding, and never forms the span
  (`Graph.IsAdmissiblePicture.span_pencilConfigPointGrade_closedNbhd_eq_range`, the lemma's second
  sentence, is not called). It reaches the lemma for `σ_v` and its injectivity
  (`gradeSigma_injective`, in `finrank_inf_range_gradeSigma`: the proof's `σ_a` of a common kernel).
  The theorem's planes are R-42's base data at three interior bodies (through
  `Graph.X0AttainsGrade.of_openEar_splitOff_of_base`), its proof citing the lemma only through
  `thm:pencil-d-open-ear-four`'s; it reads `p_a ∈ Π_a` and `p_b ∈ Π_b` by
  `pencilConfigPointGrade_eq_gradeSigma_iff`, and stars-three's three dimensions by
  `finrank_range_gradeSigma`.

- **R-44** · `lem:pencil-d-chain-count` and `thm:pencil-d-chain-or-core`, their `ℓ ≥ 1`
  (`Graph.IsChain.partitionDef_induce_le`, `Graph.IsX0Graph.exists_chain_or_core`,
  `Grade/Chains.lean`, round 1 task 11) · **no departure**: both nodes take `ℓ ≥ 1` beside
  `3(ℓ + 1) ≤ D`, and neither proof reads it; neither pin takes `1 ≤ ℓ`, only
  `3 * (ℓ + 1) ≤ Graph.bodyBarDim n`. At `ℓ = 0` the count's hypotheses contradict each other, as a
  chain has an interior body (`hshort` at `hC`, against `hC.one_le`). The theorem's outcomes at
  `ℓ = 1`, admissible at every `d ≥ 3` (`D ≥ 6`; the pin takes `3 ≤ n`), give those at `ℓ = 0`: a
  chain with more than one interior body has more than none, and the other two outcomes do not
  read `ℓ`. The chapter's `ℓ ≥ 1` is the setting, read only by the count's closing remark (at
  `d = 3` only `ℓ = 1` is allowed).

- **R-45** · `thm:pencil-d-coverage`, `G″` in the chain case and the "proof of" citations
  (`Graph.IsX0Graph.x0AttainsGrade`, `Grade/Coverage.lean`;
  `Graph.IsOpenEar.isX0Graph_splitOff_succ`, `MainComponent/CoverageCut.lean`; round 1 task 11) ·
  **no departure**: the chapter shows that `G″` (`x₂` suppressed) satisfies the standing
  hypotheses at every chain with `k ≥ 3`, before it splits on `k`, reading the edges at `x₂` and
  at `x₁` off the degree two of a chain's interior bodies (`def:pencil-x0-chain`). The pin settles
  `screwDim (m + 1) - 1 ≤ k` first by the long ear, which needs only `G[V₁]`, and forms `G″` in
  the other two branches only, by the `d = 3` helper `isX0Graph_splitOff_succ`. That helper reads
  the same edges off the open ear (`Graph.IsOpenEar.isLink_interior`: every edge off the path lies
  inside `V₁`), then calls part (2) of `lem:pencil-x0-chain-standing` (`Graph.IsX0Graph.splitOff`)
  with the chapter's facts: the two edges at `x₂`, and `x₃` neither `a` nor `x₂`, so `x₁ ≠ x₃` and
  the two are not adjacent. An order, and another definition cited for one clause. The three edges
  `scripts/blueprint-deps.py` calls *unbacked* (`lem:pencil-x0-cut-reduces`, `-cycle-reduces`,
  `-planar-rigid-reduces`) are the proof's "the proof of" citations: the pin calls the data lemmas
  factored from those `d = 3` proofs (`Graph.IsX0Graph.exists_bridgePath_of_not_twoEdgeConnected`,
  `Graph.IsX0Graph.exists_cutVertex_of_not_connected`,
  `Graph.IsX0Graph.exists_cycle_of_forall_degree_eq_two`,
  `Graph.exists_rigidCore_of_deficiency_two_pos`), not their `X0Reduces` pins. The rest is the
  chapter's proof, case by case and in its order.

- **R-46** · `lem:pencil-d-two-pencil-extension`, the setting of parts (1) and (2)
  (`perpExtensor_two_pencils`, `exists_eq_smul_perpExtensor`,
  `exists_extensor_two_pencils_iff_grade`, `Grade/TwoPencil.lean`, round 1 task 12) · **open**.
  *Chapter:* the statement takes `b_u`, `b_v` nonzero and `Π_u ∋ b_u`, `Π_v ∋ b_v`
  three-dimensional for all three parts. The proof reads none of it, except `b_u ≠ 0` in the
  converse of (2)'s last claim (`B` the span of `b_u` and a vector independent of it); (3) has
  `C_B ≠ 0` from the proof's first paragraph.
  *Lean:* (1) and (2)'s first claim take no nonzero normal, no dimension of `Π_u`, `Π_v` and no
  `b ∈ Π` (in (1) it follows from `b ∈ B ⊆ Π`); (2)'s last claim takes `b_u ≠ 0` alone. Each proof
  is the chapter's, so the pins are stronger than their node. The drop is not vacuous (a zero
  normal, or a `Π` of another dimension, meets the pins' hypotheses) and is not recovered from the
  node's statement: (3)'s pin (`linearIndependent_perpExtensor_pair`, the argument of (2) applied
  to `C_{B'} = a C_B`) calls (1) at `b_u = b_v = 0` and `Π_u = Π_v = B` for `C_B ≠ 0`, and at
  `Π_u = Π_v = B` for the panel of each `w ∈ B`. The four cases call (1) and (3) only in the node's
  setting; (2)'s two pins have no caller. `C_B` is `perpExtensor B`, the extensor of one fixed basis
  of `B^⊥` (`0` off dimension two), an encoding of the chapter's notation; its "up to a nonzero
  scalar" is `exists_smul_extensor_eq_of_mem_span_range_grade`, which (2)'s first pin uses and no
  pin names.
  *Remedies:* the prose to the Lean (parts (1) and (2) for any vectors and subspaces, `b_u ≠ 0` only
  in (2)'s last claim; the proof and its `\uses` unchanged), or keep both (the statement in the
  pencils' setting, the one every case uses). The recon leans to keeping both: the two routes agree
  step by step, and the only call outside the setting is (3)'s, for a fact the chapter has from its
  first paragraph.

- **R-47** · `lem:pencil-d-loop-case`, its rank (`hasGradedPencilRealization_of_isLoopAt`,
  `Grade/Arms.lean`, round 1 task 12) · **no departure**: the chapter reads the loop's hinge
  constraint on the motions (`S(v) − S(v) = 0` lies in the span of any hinge, so the loop leaves the
  motions and the rank unchanged); the pin reads it on the rows (`BodyHingeFramework.hingeRow_self`:
  a row of the loop is `r(S(v) − S(v))`, zero), so the rows of `G` and of `G − e` span one space.
  The rank is the dimension of that span and the motions are the rows' common kernel
  (`def:rigidity-matrix`), so the step is one fact read from its other side, with no count on either
  side: not the motions counted against bounds on the rows of R-18 and R-19. The rest is the
  chapter's: `C_B` for `B` the span of `b_v` and a `c ∈ Π_v` independent of it
  (`exists_mem_linearIndependent_pair`, `perpExtensor_two_pencils`), and the deficiency through a
  loop crossing no partition (`Graph.deficiency_deleteEdges_singleton_eq_of_isLoopAt`).

- **R-48** · `lem:pencil-d-nondegenerate-maps`, the setting of parts (1) and (2)
  (`PencilNondegConditions.of_map`, `PencilNondegConditions.map`, `Grade/Nondegenerate.lean`,
  round 1 task 13) · **open**.
  *Chapter:* the statement takes, for both parts, a nonzero `b_v ∈ K^(d+1)` and a
  three-dimensional `Π_v ∋ b_v` at every body. The proof reads none of it: (1) a relation among
  vectors gives one among their images, and `⋂_{w ∈ S} Π_w` lies in each `Π_w`, where `p` is
  injective, and maps into `⋂ pΠ_w`; (2) an injective `p` keeps independence and maps `⋂ Π_w`
  onto `⋂ pΠ_w`.
  *Lean:* both pins take any vectors and subspaces (of any `K^N` and `K^(N′)`, the standing
  generality), with `p` injective on each `Π_v`, `v ∈ V(G)`, in (1); each proof is the chapter's,
  so the pins are stronger than their node. The nonzero normals are trivially recovered: the
  conditions force `b_v ≠ 0` on `V(G)` (the closed neighbourhood of a body that is not a hub, a
  link at a hub; checked with `lake lean`), in (1) through `p b_v ≠ 0`. The dimension and
  `b_v ∈ Π_v` are not recovered, and their drop is not vacuous: with no hub the third condition
  reads no subspace, so any `Π` meets the pins' hypotheses. Both callers are in the node's setting:
  `IsNondegPencilPlaneRealization.lift` (`π`, part (1)) and
  `IsNondegPencilPlaneRealization.map_gradeEmbed` (the "in particular", which takes a
  nondegenerate realization).
  *Remedies:* the prose to the Lean (parts (1) and (2) for any vectors `b_v` and subspaces `Π_v`;
  the proof, the "in particular" and the `\uses` unchanged), or keep both (the pencils' setting,
  the one both callers use). The recon leans to the prose: one clause, and the conditions read only
  vectors and subspaces.

- **R-49** · `lem:pencil-d-steer`, `lem:pencil-d-lift-one-witness` and `-lift-transfer`, their
  simple `G` (`isZariskiOpen_steerSet`, `exists_mem_steerSet_of_isNondeg`, `steerSet_nonempty_iff`,
  `Grade/Lift.lean`; `liftAttains_of_least`, `liftAttains_of_holdsGenerally`, `lift_transfer`,
  `Grade/LiftWitness.lean`; round 1 task 13) · **open**.
  *Chapter:* each statement takes `G` simple ("a finite simple multigraph whose closed
  hub-neighbourhoods have at most three members"; "simple and nondegeneracy-feasible"). No proof
  reads it: the parametrization reads the assignments of places, the other two the
  parametrization and the lifts.
  *Lean:* no pin takes `G.Simple` (their signatures, checked with `lake lean`); each proof is
  otherwise the chapter's up to R-21 and R-23 (R-22 aligned), so the pins are stronger than their
  nodes. Not vacuous: the parallel pair, two bodies and two edges between them, is
  nondegeneracy-feasible (`exists_isNondegPencilRealization_parallel_pair`, `Pencil/Pair.lean`)
  and not simple. Not recovered: no hypothesis of the pins implies it. The nodes' other hypotheses
  are taken or recovered: the closed hub-neighbourhoods of at most three members as the selectors
  (`IsFin3SelectorOf`, the statement's assignments of places); nondegeneracy-feasibility from a
  realization the pins take (`hnd`, the nonempty `U(G)` under `HoldsGenerally`, (T1)'s realization
  of `G`). The induction's pin, `liftAttains_of_simple` (`thm:pencil-d-generic`), takes it.
  *Remedies:* the prose to the Lean (the three statements without "simple"; the proofs and their
  `\uses` unchanged), or keep both (simple graphs, the setting of `thm:pencil-d-generic`'s
  induction). The recon leans to the prose: one word in each statement, read by no proof.

- **R-50** · `lem:pencil-d-lift-realization`, the setting of parts (2) and (3)
  (`mem_liftMaps_iff`, `liftSmul_mem_liftSpace_iff`, `liftTransport_mem_liftSpace_iff`,
  `finrank_span_rigidityRows_ofNormals_smul`, `finrank_liftNormal_transport`, `Grade/Lift.lean`,
  round 1 task 13) · **open**.
  *Chapter:* the statement takes, for all three parts, a nondegenerate realization `(b⁰, Π⁰)` in
  dimension three and `λ ∈ 𝓛(b⁰, Π⁰)^m`. The proofs of (2) and (3) read only that `Π⁰_v` contains
  the points of the closed neighbourhood of `v` ((2): a form on `Π⁰_v` extends to `K⁴`, and one on
  `K⁴` restricts) or nothing ((3): `ζ_w = φ_v(b⁰_w)` exactly when `c_w ζ_w = φ_v(c_w b⁰_w)` and
  when `ζ_w = (φ_v ∘ g⁻¹)(g b⁰_w)`; the hinges scale by `c_u c_v`; a collineation keeps the rank).
  *Lean:* (2)'s pin takes only `b⁰_w ∈ Π⁰_v` on the closed neighbourhoods; (3)'s two membership
  pins take any `b⁰` and `Π⁰` (and `c_v ≠ 0` on `V(G)`), and its two rank pins any normals, at any
  maps `ζ` (the scaling at any grade). Each proof is the chapter's, so the pins are stronger than
  their node. Not vacuous (`b⁰ = 0` meets (2)'s hypothesis; (3)'s pins have none beyond the
  scalars) and not recovered. (1)'s pin, `IsNondegPencilPlaneRealization.lift`, takes the node's
  setting. (2) has five callers, each supplying only the incidences. The (T2) steps of the cut
  edge (`cutEdge_T2`, `Grade/LiftCutEdge.lean`), the pendant and the pendant triangle
  (`pendant_T2`, `pendantTri_T2`, `Grade/LiftCases.lean`) call it at `G`, at a point of `U(G)` (a
  nondegenerate realization, the node's setting), and at an induced subgraph with `G`'s chart
  points and subspaces; `ear_T2` calls it at `G` alone, at a point of `U(G)`; and
  `mem_liftMaps_pencilConfigPoint_iff` (`Grade/LiftNoRigid.lean`, a pin of
  `lem:pencil-d-lift-no-rigid`) at any configuration `(q, z)` with `z ∈ L(q)` and any subspaces
  containing its closed neighbourhoods (its one caller at the nondegenerate `r*`). So four of the
  five use (2) in `def:pencil-d-lift`'s setting, not the node's. (3)'s scaling is called in the
  setting (`liftAttains_of_least`, at `c b⁰`); its transport has no caller
  (`scripts/blueprint-deps.py` calls its two pins dead).
  *Remedies:* the prose to the Lean ((2) and (3) for any `(b⁰, Π⁰)` as in `def:pencil-d-lift`,
  (1) alone at a nondegenerate realization and `λ ∈ 𝓛^m`; the proofs and `\uses` unchanged), or
  keep both (one setting for the three parts). The recon leans to the prose, as four of (2)'s five
  callers are outside the node's setting.

- **R-51** · `lem:pencil-d-lift-small`, its infinite `K` (`liftAttains_of_ncard_le_two`,
  `liftAttains_of_triangle`, `liftAttains_of_cutEdges_eq_empty`, `Grade/LiftSmall.lean`, round 1
  task 14) · **open**.
  *Chapter:* the statement takes `K` infinite for both parts, as the section's other cases do.
  Neither proof reads it: (1) shows the target rank at every lift, so `Q = 1` serves; (2) takes
  the product of the sides' polynomials, nonzero at the glued realization.
  *Lean:* none of the three pins takes `[Infinite K]` (their signatures, checked with `lake lean`;
  the pins of `-lift-cut-edge`, `-lift-pendant`, `-lift-pendant-triangle` and `-lift-ear` take it),
  and each proof is the chapter's up to R-27, R-28 and R-52, so the pins are stronger than their
  node. Not vacuous: all three apply over `ZMod 2` (the same `lake lean` probe), where simple
  nondegeneracy-feasible graphs exist (`exists_isNondegPencilRealization_parallel_pair`,
  `Pencil/Pair.lean`, holds over every field, and its one-edge subgraph `K₂` is feasible by
  `PencilNondegFeasible.mono`, the pair having no hub). Not recovered: no hypothesis of the pins
  implies it. R-28 names only the simple `G` of (2); `notes/Phase42m.md` *Statement faithfulness*
  records this drop for (2) alone. The induction's pin, `liftAttains_of_simple`
  (`thm:pencil-d-generic`), takes it.
  *Remedies:* the prose to the Lean (the statement without "K infinite"; the proofs and their
  `\uses` unchanged), or keep both (the section's setting, which the other cases and the theorem
  take). The recon leans to the prose: one clause, read by neither proof.

- **R-52** · `lem:pencil-d-lift-small`, part (1), its lifts and its cases on at most two bodies
  (`liftAttains_of_forall`, `liftAttains_of_ncard_le_two`, `Grade/LiftSmall.lean`, round 1 task 14)
  · **no departure**: the chapter shows that every lift of every nondegenerate realization has rank
  `tgt_d(G)`, so that `Q = 1` serves; the pins show it of one lift, by the zero maps
  (`liftAttains_of_forall`, `λ = 0`), which is what `def:pencil-d-lift-attains` asks. The argument
  is the chapter's at any maps: the normals of a lift are independent where those of `b⁰` are, by
  the projection `π` that deletes the inserted coordinates (`linearIndependent_liftNormal`, the step
  of part (1) of `lem:pencil-d-lift-realization` the proof cites, unpinned, so
  `scripts/blueprint-deps.py` calls that edge *unbacked*). One body and two bodies with no edge are
  one case (no edge: rank `0`, and `def_d = D(|V(G)| − 1)` at the singletons,
  `Graph.deficiency_of_edgeSet_empty`); two bodies with an edge are the base case's step
  (`finrank_span_rigidityRows_of_single_edge`, `Grade/Arms.lean`, `def_d = 1` by the chapter's two
  partitions, `Graph.deficiency_of_single_edge`), as the proof's "as in `lem:pencil-d-base-case`"
  says; its rank is R-18's route. The two-body pin's `[Nonempty α]` is the carrier's: over an empty
  `α` with edge labels, `LiftAttains` asks for a selector `β → α × α`, which does not exist
  (reported to the PI at 42m as an encoding, `notes/Phase42m.md` *Statement faithfulness*).

- **R-53** · `lem:pencil-d-good-ear`, (iii)'s `|X| ≥ 3`
  (`Graph.IsX0Graph.exists_minimalRigid_ear_or_pendantTriangle`, `MainComponent/GoodEar.lean`;
  `exists_goodEar_or_pendantTriangle`, `Grade/GoodEar.lean`; round 1 task 15) · **open**.
  *Chapter:* (iii) shows that `a` and `b` keep two neighbours in `X` and the other bodies of `X`
  all of theirs, so `G[X]` has minimum degree at least two, "and `|X| ≥ 3` as `G` is simple".
  *Lean:* `|X| ≥ 3` is the core's output, by the argument of the last paragraph of
  `lem:pencil-rigid-good-ear`'s proof: were `X = {a, b}`, `s(X) ≤ 1` would need the edge `ab`
  (`Graph.partitionDef_two_induce_insert_id` at `a` and `{b}`), and `{x, a, b}` would be a
  triangle with two hubs (`hF2`). The minimum degree two is shown after it and does not feed it.
  The rest of (iii) is R-31's. Close, and not a departure: a planar-rigid `Z ⊆ X` is excluded by
  (i), `s(Z) ≤ def₂(G[Z]) = 0` against `s(Z) ≥ 1`, not by the minimality of `W₀` that (i) records.
  *Remedies:* the prose to the Lean ((iii) reads `|X| ≥ 3` off the proof of
  `lem:pencil-rigid-good-ear`, as the first paragraph reads (i) and (ii) off it; the statement and
  the `\uses` unchanged), or keep both (one line each). The recon leans to the prose: one clause,
  and that proof states it.

- **R-54** · `thm:pencil-d-generic`, its case split (`liftAttains_of_simple`,
  `hasGradedGenericPencilRealization_of_simple`, `Grade/Generic.lean`, round 1 task 15) · **no
  departure**: the induction is the chapter's, arm by arm and in its order (at most two bodies; a
  cut no edge crosses; a cut edge with two bodies on each side, or a pendant body; the triangle;
  no planar-rigid set, with the coverage `Graph.IsX0Graph.x0AttainsGrade`; the good ear's two
  outcomes, the ear's condition from `holdsGenerally_earFree`), each smaller graph feasible by its
  case lemma, and the outer pin is the chapter's first and last steps
  (`gradedPencilNondegFeasible_iff`, `LiftAttains.hasGradedGenericPencilRealization`). It reads
  less than the chapter only where a case's pin drops a hypothesis of its node: it never derives
  that the pendant's neighbour `u` has another neighbour (R-25), and passes `a ≠ b` to the ear,
  not `a ≁ b` (R-29). Those are the rows': R-25's prose-to-Lean remedy also strikes the proof's
  "and its neighbour `u` has another neighbour, as `G` is connected with at least three bodies".
  `|V₁|, |V₂| ≥ 2`, which the cut edge's pin drops (R-30), still bound the sides' sizes, as in the
  chapter; R-28's and R-51's drops do not reach it, as the theorem takes `G` simple and `K`
  infinite. The rest are carrier readings: "say `V₂`" as two cases, the triangle from the degrees
  (`adj_of_twoEdgeConnected_ncard_eq_three`), connectivity from two-edge-connectivity, and the
  ear's condition at the selectors of `lem:pencil-d-steer` (`exists_steer_selectors`).

## 3. The cleanup's rounds

- **Round 1, the route audit** (opened and closed 2026-11-05, `notes/Phase42-cleanup.md`): every
  green node of `pencil-d.tex` against its Lean, in 14 one-dispatch Opus recon slices by layer, the
  47 nodes of 42b–42f first; each added rows to §2 and re-checked the rows on its nodes at HEAD,
  with no prose, statement, pin or Lean edit. It added R-35 to R-54 (7 `open`, 13 `no departure`)
  and corrected 13 rows in place. It closed at its planned stop, which grouped the 34 `open` rows
  by family (below, *Round 1's stop*) and asks the PI for a remedy per row and the plan of rounds
  2+ (`notes/Phase42-cleanup.md` *Autopilot: for the PI*).
- **Between rounds 1 and 2: the B/C judgment** (the PI, 2026-11-05, §1). One Opus recon reads
  each of the 22 rows of families B and C (*Round 1's stop*, below) against the chapter and the
  Lean and proposes L, K or H with a one-line reason (which route reads better), in one docs commit
  (a per-row table in this section, after *Round 1's stop*; read-only otherwise, no row's status
  changed); a short second stop, at which the coordinator relays the proposals and the PI approves
  or amends, then round 2 opens with its own work log.
- **Rounds 2+** (planned with the PI at round 1's stop, §1: the proposal as written): round 2, the
  chapter to the Lean (blueprint and notes, no Lean; family A's L rows, the B/C rows the PI sends
  L, a remark for each K row, the *Moved* lines below and the `\uses` sweep; about 11 tasks);
  round 3, Lean helpers, only if a row goes H; round 4, the three items *Also left to it* below.
  Round 1's *Candidates for the PI* and *Moved to a later round* lines are mirrored here as they
  land:
  - *Moved to a later round* (round 1 task 2): `lem:pencil-d-point-configuration`'s statement reads
    the closed neighbourhood (`Graph.closedNbhd`, pinned by `def:pencil-nondegenerate` in
    `pencil.tex`) with no `\uses` edge to it, which `scripts/blueprint-deps.py` reports *missing*.
    The script reports 60 missing edges over the chapter (`--chapter pencil-d`), so a later round
    may take them in one sweep.
  - *Moved to a later round* (round 1 task 10): a prose slip. `thm:pencil-d-open-ear-four`'s proof
    calls an ear datum `y` ("Take an ear datum $y$ off all three zero sets", then "Keep the other
    points of $y$"), where `def:pencil-d-ear-data` and the same proof's first stage (`s^*`) write
    `s` for ear data, and the section writes `y` for points (`y_1`, `y_3`, …).
  - *Moved to a later round* (round 1 task 13): a prose slip. `lem:pencil-d-nondegenerate-maps`
    fixes `p : K^(d+1) → K^(d′+1)`, so (2)'s injective `p` has `d ≤ d′`, but its "in particular"
    embeds a realization in dimension `d′ ≤ d` into dimension `d` (the letters of
    `lem:pencil-d-embed-realization`), a map `K^(d′+1) → K^(d+1)`: `d` and `d′` swap roles within
    one statement.
  - *Moved to a later round* (round 1 task 15): a stale docstring. `Grade/LiftNoRigid.lean`'s
    module docstring names `mem_liftMaps_pencilConfigPoint_iff` among the steps stated "for
    `lem:pencil-d-ear-free`" (`L(b⁰) = L(q)` in the maps), but its one caller is
    `liftAttains_of_forall_deficiency_two_ne_zero`: the Lean of `-ear-free` never reads `L(b⁰)`
    (R-34) and calls only the other two it names.
- **The ledger at Phase 42's close:** the standing rule (§1) kept §2 current through PD-STEPS's
  rest, PD-COVERAGE, PD-REDUCTION and PD-HEAD (`notes/Phase42-design.md` §3), the last rows 42m's,
  R-24 to R-34; Phase 42 closed on 2026-11-05 with no row added after them. Round 1 adds from R-35.
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

### Round 1's stop: the open rows by family (2026-11-05)

The 34 `open` rows at round 1's close, by the kind of departure the audit's criterion names
(`notes/Phase42-cleanup.md` *The audit's criterion*); each row's full text is in §2. A row with a
statement part goes under A, its argument or step part marked (B) or (C) and named again under that
family. The remedies, as the rows give them: **L**, the prose (under A, the statement) to the Lean;
**H**, a Lean helper so that the Lean follows the chapter; **K**, keep both. *Lean:* the recon's or
the coordinator's recorded lean, if any. The PI's questions are the `NEEDS_PI` entry of
`notes/Phase42-cleanup.md` *Autopilot: for the PI*.

**A. The pin is stronger than its node** (12): a hypothesis of the node the Lean does not take.
- R-15 `lem:pencil-d-planes-meet`: no `K` infinite (the row's *Lean*; its remedies omit it); `R` by
  rank openness, no `λ` (B). K, L (the argument). No lean.
- R-25 `lem:pencil-d-lift-pendant` (T1): no "`u` has another neighbour"; the split on `u` a hub of
  `G` (B). L (it also strikes `thm:pencil-d-generic`'s derived clause, R-54), K. No lean.
- R-28 `lem:pencil-d-lift-small` (2): no `G` simple; the lift space never a product (C). L, K. No
  lean.
- R-29 `lem:pencil-d-lift-pendant-triangle`, with the pins of `-lift-pendant` and `-lift-ear`: the
  ear's pin takes no `a ≁ b` (the pendant's drop is R-25); (T1) by polarity, (T2) one form `ψ_c`,
  no deficiency of the triangle (B). L, K. No lean.
- R-30 `lem:pencil-d-lift-cut-edge`: no `|V₁|, |V₂| ≥ 2`; one frame map, one minor, no case
  analysis on `|S|`, no replaced normal (B). L, K. No lean.
- R-33 `lem:pencil-d-ear-extend`: no `G` simple, no neighbour selector; one witness per condition,
  the `n_u` chosen greedily (B). L, K. No lean.
- R-35 `lem:pencil-d-agrees-three`, its first sentence: no `q_v ≠ 0`; a sentence added, `q^⊥`
  three-dimensional exactly when `q ≠ 0` (C). L, K. Lean: the recon, L.
- R-46 `lem:pencil-d-two-pencil-extension` (1), (2): no nonzero normals, dimension or `b ∈ Π`,
  `b_u ≠ 0` in (2)'s last claim only; (3)'s pin calls (1) outside the setting. L, K. Lean: the
  recon, K.
- R-48 `lem:pencil-d-nondegenerate-maps` (1), (2): any vectors and subspaces (the nonzero normals
  recovered, the dimension and `b_v ∈ Π_v` not). L, K. Lean: the recon, L.
- R-49 `lem:pencil-d-steer`, `-lift-one-witness`, `-lift-transfer`: no `G` simple (the parallel
  pair, feasible and not simple, meets the pins). L, K. Lean: the recon, L.
- R-50 `lem:pencil-d-lift-realization` (2), (3): (2) takes only the incidences, (3) any
  `(b⁰, Π⁰)`; four of (2)'s five callers are outside the node's setting. L, K. Lean: the recon, L.
- R-51 `lem:pencil-d-lift-small`: no `K` infinite (the three pins apply over `ZMod 2`). L, K. Lean:
  the recon, L.

**B. A different argument for a step** (16). Also the argument parts of R-15, R-25, R-29, R-30 and
R-33 (under A) and of R-14, R-17 and R-32 (under C).
- R-3 `lem:pencil-d-polygon-normal` (2): a basis map extended, then a transvection, not the
  explicit affine map. K, H (`K^{d+1}` as `K^d × K`, `g` a block map), L. Lean: the coordinator, K
  (the chapter reads better).
- R-4 `lem:pencil-d-polygons`, the base triangle: three 2 × 2 minors, no basis of `⋀²`. K, H (the
  basis of `⋀²` a basis of `K^{d+1}` induces), L. Lean: the coordinator, K.
- R-9 `lem:pencil-d-kernel-curve`: a rank count at some `t ≠ 0`, not Cramer's rule over `K(t)` (no
  power series). L, K. No lean.
- R-10 `lem:pencil-d-ear-data` (3): a coefficient of `h(λ, s)` in `λ`, no component `f_α`. L, K.
  Lean: a toss-up.
- R-11 `lem:pencil-d-two-stars` (1): a linear section of the quotient and rank–nullity, not a
  basis. K, H (`Basis.exteriorPower`), L. No lean.
- R-16 `lem:pencil-d-glued-ends`: no merged deficiency (a partition of `G′` pulled back),
  Jackson–Jordán's polynomial for the edge coordinates, `X` split in two, not into its components
  (C). K, L (the `\uses` drops `def:deficiency-merged`). No lean.
- R-18 `lem:pencil-d-base-case`: the rank bounded below by a hinge's rows and above by the target,
  not read off the motions. L, H (the motions of one edge), K. No lean.
- R-19 `lem:pencil-d-nonsimple-case`: the rank by the splice at every `D`, not by the motions of
  `G/H` with `S(w) = S(u)`. L (it also widens the closing remark), H (those motions), K. No lean.
- R-20 `lem:pencil-d-nondegenerate-feasible`: forms chosen off at most two proper subspaces; no
  quotient, induction or quadric. L, K. No lean.
- R-21 `lem:pencil-d-lift-one-witness`: one polynomial section, no Cramer basis and no `γ`. L, K.
  No lean.
- R-23 `lem:pencil-d-lift-transfer`: openness by the rank polynomial at each `λ`, not through
  (T2). L, K. No lean.
- R-26 `lem:pencil-d-lift-pendant`, `-lift-ear` (T2): one form on `K⁴` per body, not `φ` on
  `Π⁰`. L, K. No lean.
- R-27 `lem:pencil-d-lift-small` (1), the triangle: the joins by minors at a dual triple; no
  partition values, the rank at most the target and the deficiency nonnegative (C). L, K. No lean.
- R-31 `lem:pencil-d-good-ear`: the proof split at a core; `def₂(G[X]) = 1` by a partition case
  split, connectivity not through `s(X)`. L, K. No lean.
- R-34 `lem:pencil-d-ear-free`: the trivial lifts embedded by dimension, rank at most three only in
  `U(G)`, (b) by two plane normals. L, K. No lean.
- R-53 `lem:pencil-d-good-ear` (iii): `|X| ≥ 3` from the core (`s(X) ≤ 1` needs the edge `ab`,
  then `hF2`), not "as `G` is simple". L, K. Lean: the recon, L.

**C. A step skipped, added or ordered otherwise** (6). Also the step parts of R-28 and R-35 (under
A) and of R-16 and R-27 (under B).
- R-5 `thm:pencil-d-cycle`, the placement: one path, a closed `N`-gon with `N = min(m, D)`, not two
  cases. L, K. Lean: the coordinator, a toss-up.
- R-12 `thm:pencil-d-open-ear-four`: the factored order (the put-back a hypothesis, discharged
  after). L (state the factoring), K. No lean.
- R-14 `thm:pencil-d-open-ear-three`: no component step and no path lemma; `r ≤ 2` gives
  `dim ρ ≤ 2` by glued-ends or a common member (B). L, K. No lean.
- R-17 `lem:pencil-d-chain-count`: classes of interior bodies and the handshake bound, no edge
  segments (B). L (the `\uses` adds `lem:pencil-x0-sparse-count`), K. No lean.
- R-24 the cases' (T1) (`-lift-pendant`, `-lift-ear`, the pendant triangle): one minor per closed
  hub-neighbourhood, no case analysis of which conditions are new. L, K. No lean.
- R-32 `lem:pencil-d-lift-no-rigid`: no map `g` and no `ℓ₀`; `dim L̃` through the lifting
  system's kernel (B). L, K. No lean.

**Close calls**, `no departure` rows on criterion (3) (a dropped hypothesis judged vacuous,
recovered or the setting), so that the PI may reopen any:
- R-36 `lem:pencil-d-contract-magnified-rank`: the pin takes any `r`, no `r ∈ W`, the setting of
  `def:pencil-contract-lifting-system`, read by no proof.
- R-38 `lem:deficiency-tight-part`: no case `Z = V(G)`, as the pin of the cited
  `lem:separated-partition-value` (`deficiency.tex`, outside the audit) takes neither side nonempty.
- R-44 `lem:pencil-d-chain-count`, `thm:pencil-d-chain-or-core`: no `ℓ ≥ 1`, vacuous for the count
  (its hypotheses contradict at `ℓ = 0`), recovered for the theorem, the setting.
- R-54 `thm:pencil-d-generic`: its proof reads less where a case's pin drops a hypothesis (R-25's
  other neighbour; R-29's `a ≁ b`, passed as `a ≠ b`).
