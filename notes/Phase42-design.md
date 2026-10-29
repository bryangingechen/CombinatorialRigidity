# Phase 42 — PENCIL-D: design (cross-phase plan and recon)

**Status:** opened 2026-10-29 with the PI, sub-lettered, research first. **42a** (PD-RECON,
`notes/Phase42a.md`) is open: no Lean, no blueprint. The step table has landed (§2.1). Of its 22
rows, 10 generalize as they stand and 6 given routine or formal work (CERT, CARRIER); the coverage
waits on the ear rows, nondegeneracy's lift is open, and 4 rows fail as written: the short ears,
the one-body and orbit ears (rows 14–15), and route B. Next concrete task: T1 and T2 (§2.4),
one driver mode; the PI's calls are §4. Evidence: `notes/Strata.md`, Results 12–19.

This file is the phase's entry point: the target (§0), the PI's decisions (§1), the recon (§2),
the layers by stable code (§3) and the open questions (§4). Letters are minted when a sub-phase
opens (`PHASE-BOUNDARIES.md`); until then the stable codes of §3 name the layers.

## 0. Target

**The `Pᵈ` pencil conjecture.** Let `G` satisfy `def:pencil-x0-standing` (finite, simple,
connected, minimum degree at least two), and let `d ≥ 2`. Take a general picture `q` and general
heights `z¹, …, z^{d−2} ∈ L(q)`. Then the hinges `b_u ∧ b_v`, with
`b_v = (q_v, z¹_v, …, z^{d−2}_v, 1)` (`Strata.md` Result 13), have rank `D(n−1) − def_D(G)`,
`D = C(d+1, 2)`. The headline is the multigraph form, Phase 39's `PencilPair` in dimension `d`,
through Phase 39's reduction.

Status: `d = 2, 3` are proved and formalized (Phases 40a, 40). Every `d` with `def_3 ≤ 1` is
`Strata.md` Result 17. `d = 4, 5, 6` are measured (Results 11, 19), not found below target under
the `--d4` population's cap (`n ≤ 12`, 36 simple graphs) and 8 graphs past it.

**What it implies.** By Result 12, every per-body flag stratum of `Pᵈ` attains, KT's panel
theorem among them. That is a strengthening, not a new proof: Phase 40 itself uses KT Theorem 5.6
at `d = 2` and KT Lemma 6.3.

**What exists.** KT's chain is formalized in every `d` (Phases 21–23, 33, 41). The pencil layer is
`P³` only. `IsNondegPencilRealization` takes a `BodyHingeFramework K 2` and points `Fin 4 → K`
(`Pencil/Motive.lean`), and `main-component.tex` computes in `Λ²K⁴`'s flat coordinates. The
planar carrier is the reusable part: pictures, `L(q)`, the one-witness lemma, the
fibre-intersection lemma and Jackson–Jordán's equality.

## 1. The PI's decisions

- **PI, 2026-10-29 (queue):** PENCIL-D queued ahead of ORIGAMI: prove the pencil realization
  theorem in every `Pᵈ` and formalize it over the next few phases.
- **PI, 2026-10-29 (open), where PD-RECON runs:** "In-phase, as 42a (Recommended)".
  The options put were: in-phase as 42a, attended, recon-first as Phase 39 was, with any single
  step that needs a new argument split off as an attack track then; an attack track under
  `/attack`, the phase opening on PD-STATE's Lean; or in-phase with PD-STATE and PD-STABLE queued
  beside it.
- **PI, 2026-10-29 (open), the plan's home:** "Sub-lettered, Phase42-design.md (Recommended)".
  The program section moved here from `notes/Strata.md`, which keeps its Results and evidence.

## 2. PD-RECON (42a)

**Routes**, as queued:
- **(R1) Induction on `d`.** The step `d−1 → d` starts from Result 13's base, the `P^{d−1}` pencil
  in a hyperplane, and adds one height in `L(q)`. Phase 40 is the step `2 → 3` from the flat base.
- **(R2) Direct.** Phase 40's induction, run once with `d − 2` heights.

Either way, Result 15 limits the work for each graph to `d ≤ 2 + def_3(G)`.

### 2.1 The step table (2026-10-29)

Four read-only recon passes (Claude Opus 5.5), one per slice of `main-component.tex` (A: lines
158–1370; B: 1371–3215; C: 3216–4864; D: 4865–5623 with `pencil.tex`), on one brief: for each
step, its uses of `d = 3` beyond `D = 6` and the flat base, and a verdict per route. Line numbers
are at `2168de79`. Notation: `def[D]` is `def:D-deficiency` at screw dimension `D` (the chapter's
`def₂ = def[3]`, `def₃ = def[6]`), `D_d = C(d+1, 2)`, `Π_v = span b_{N[v]}` (dimension 3).
**GEN** generalizes; **GEN|X** given obligation X (§2.3); **FAILS** fails as written in `Pᵈ`.

| # | Step (`main-component.tex` unless marked) | Its `d = 3` beyond `D` and the base | Verdict |
|---|---|---|---|
| 1 | Pictures, `L(q)`, main pictures (212–760) | none: planar data; the fibre is `L(q)^{d−2}`, same main pictures | GEN |
| 2 | `def:pencil-configuration`, `lem:pencil-condition-linear` (307, 468) | plane normal as a `4×4` determinant; "solving for `z_w`" (495–499) | GEN: `S → K³` is an isomorphism, so `S` is the graph of a map `K³ → K^{d−2}`; the configurations are `L(q)^{d−2}` (Result 13) |
| 3 | Rank carrier: `lem:pencil-config-point-join-rank`, `-rank-collineation`, `-rank-scale-shift` (387–563) | the polarity as a self-map of `Λ²K⁴`; Lean at `Fin 4`, `k := 2`; scalar `t` | GEN\|CARRIER (formal); scale-shift becomes `GL_{d−2}` and `Aff(q)^{d−2}` |
| 4 | `lem:pencil-x0-one-witness`, `-fibre-intersection` (670, 823) | none; the hinge is affine in each height, with a `Λ²Z` part quadratic in the heights at `d ≥ 4` | GEN: `L(q)^{d−2}` is linear, one polynomial section serves every height, the fibre lemma's Lean takes any submodule |
| 5 | Flat rank (886–1167) | the split `Λ²K⁴ = K³ × K³` | GEN: R2's flat rank `D_d(n−1) + 3 − dim L(q)`; R1's base `D_d(n−1) − def[D_{d−1}]` where `P^{d−1}` attains (both by hand, untested, T1) |
| 6 | Jackson–Jordán's equality (1169–1369) | none: planar, KT Theorem 5.6 at `d = 2` | GEN unchanged |
| 7 | Cut vertex, the shared scheme (1384–1564) | count only (`lem:deficiency-cut-vertex`, every `D`) | GEN: the height is used only as a vector |
| 8 | Chain of bridges (1566–1645) | count only | GEN |
| 9 | Contraction at an additive core, its corollary (1647–2139) | none beyond row 3; KT Claim 6.4's Lean pin takes `Fin (k+2)` normals | GEN\|CARRIER: "rigid" is `def[D_d](H) = 0`; additivity stays planar, `def[3]`, under both routes |
| 10 | Cycle `thm:pencil-x0-cycle` (2387) | the `K⁴` certificate `Y₀…Y₅` (2342) | GEN\|CERT: needs `λ ≥ min(m, D_d)` |
| 11 | Long ear `thm:pencil-x0-open-ear` (2439) | "five interior bodies give six hinges" (2191); the hexagon placement | GEN\|CERT, for `k ≥ D_d − 1` only (9 at `d = 4`) |
| 12 | (⋆) and the two-body ear `thm:pencil-x0-open-ear-two` (2534, 2896) | none: (⋆)'s `k + 1` holds at every `D` (`lem:block-rank-ear`) | GEN; covers every `k ≤ D_d − 1` with `def[D](G[V₁]) ≤ def[D](G)`, given `k + 1` independent joins (CERT) |
| 13 | Short ears `k = 3, 4` (2960, 3081) and their line geometry (2601–2804) | the Klein pairing into `Λ⁴K⁴ = K`; four points' six joins span `Λ²K⁴`; two stars of codimension 1 | **FAILS** for `d ≥ 4`; the step itself unclear; its range grows to `3 ≤ k ≤ D_d − 2` (SHORT) |
| 14 | One-body ear (3341–3491) | one affine function `D(z)` and its zero line (3346–3348) | **FAILS** for `d ≥ 5`, and at `d = 4` when `a, b` share a neighbour in `V₁` (ONE-EAR) |
| 15 | Two-body ear at non-adjacent ends (3498–3627) | two hyperplanes of `K⁴` meet in a line; a tetrahedron | inherits 14; insertion plausible at `d = 4`, unclear at `d ≥ 5` (ONE-EAR) |
| 16 | Split-off (3629–3957) | `δ ≥ 5`, a count; collinearity only | GEN: `δ_D ≥ D − 1` |
| 17 | Sparse estimates (3959–4313) | `v₃ = 2v₂ − d_G` uses `6 = 2·3`; Lean pins fix `n = 3` | GEN, restated at `D`: the consumers need only "`v₂ ≤ 0` gives `v_D ≤ 0`", one line at every `D ≥ 3` |
| 18 | Coverage, Theorem S (4314–4864) | `s₆ → s_D`, every `D ≥ 6` | GEN\|rows 11–15: "no chain with three or more interior bodies" needs every `k ≥ 3`; the `k = 1, 2` orbit cells are load-bearing |
| 19 | `pencil.tex`'s reduction, bare and distinct conjuncts | counts in `K⁴` only (P440); the self-duality is unused (P115–215) | GEN\|CARRIER; two-pencil extension gains a third clause `dim(Π_u ∩ Π_v) ≥ 2`, met at every consumer |
| 20 | Phase 39's definitions (`pencil.tex` P64, P89) | a per-body *point*: the pencil only at `d = 3`, at `d ≥ 4` Result 12's type `(0, B)` | restate (CARRIER) |
| 21 | Nondegeneracy (P818, M4933) | two "at most three" bounds from 3-spaces of `K⁴`; not self-dual | unclear: no canonical `Pᵈ` lift (the PI) |
| 22 | Route B, the generic conjunct (M5216, M5333) | `K⁴` triple cross product (M5248); `p_x` on `n_a^⊥ ∩ n_b^⊥` (M5371) | **FAILS**: steer for `d ≥ 4`, one-ear for `d ≥ 5` (GENERIC); separable, as bare and distinct never consume it |

Checked by the coordinator against the text or by hand: the passages of rows 13, 14 and 22; the
codimension `C(d−1, 2)` of two stars in `Λ²K^{d+1}` (1 only at `d = 3`); two general 3-spaces of
`K^{d+1}` meet in dimension `5 − d`; row 5's flat rank at `d = 3`; and that `def[3] = def[D′]` for
one `D′ > 3` forces a tree-quotient optimum, so `def[3] = def[D]` at every `D ≥ 3` (row 5: the flat
class does not change with `d`). `lem:deficiency-antitone` (every `d ≤ d′`, connected `G`) is
formalized. The rest is the agents' reading, cited by row.

### 2.2 Verdict on the routes

**Neither route closes as written; the step structure is R2's.** Every step reads Phase 40's
induction on `|V|` at a fixed `d` with all `d − 2` heights general. R1 as "fix `z¹…z^{d−3}` from a
`P^{d−1}` witness and add one height" breaks contraction, whose heights must move along its curve
(B), and does not help the one-body ear: every configuration of `G` restricted to `V₁` lies on the
incidence locus, whatever the base (C). What R1 contributes is a **base row**: where `P^{d−1}`
attains at `G`, its base has rank `D_d(n−1) − def[D_{d−1}](G)` (row 5), so `G` attains in `Pᵈ`
whenever `def[D_{d−1}](G) = def[D_d](G)`. That is Result 15 at `d′ = d − 1`; the class grows with
`d` and contains R2's flat class `def[3] = def[D_d]`. The recon's proposal, for the PI: R2's
induction with R1's base row, inside an outer induction on `d`.

**The pattern behind the failures.** In `P³` the planes of two bodies always share a line; in `Pᵈ`
two 3-spaces of `K^{d+1}` meet in dimension `5 − d`. A step that deletes a body `x` and keeps its
two neighbours' planes relaxes a closed condition at `d ≥ 5` (`b_x ∈ Π_a ∩ Π_b`), so "the smaller
graph attains generally" no longer reaches `G` (rows 14, 15, 22). The short ears fail for a related
reason: the joins through two points have codimension `C(d−1, 2)`, not 1 (row 13).

**Where `d = 4` stands.** Row 14 fails only when the ends share a neighbour in `V₁`, row 15's
insertion is plausible (`Λ²K⁵` is the whole screw space), row 22's one-ear works given steer; row
13 is blocked as written. By Results 15–16 a `P⁴` theorem gives every `d` at `def[3](G) ≤ 2`,
Result 17's `def[3] ≤ 1` one step further.

### 2.3 Obligations (stable codes)

- **CERT** (rows 10–12): at each `d`, a closed `m`-gon of affine points with independent
  consecutive joins for `m ≤ D_d`, and the long ear at `k = D_d − 1` with its ends at height zero.
  Looks routine (B suggests an Euler circuit of `K_{d+1}` for even `d`, unchecked); T2 tests it.
- **SHORT** (row 13): ears with `3 ≤ k ≤ D_d − 2` and `def[D](G[V₁]) > def[D](G)`. Re-inserting
  `x₂` adds only joins in `star(y₁) + star(y₃)`; X3 would be "at general ear data, `W` containing
  both stars is `Λ²K^{d+1}`", or the step moves `x₁` and `x₃` too. New mathematics.
- **ONE-EAR** (rows 14–15): either a motive that asks `G[V₁]` to attain on the locus where `Π_a`
  and `Π_b` meet above a general `q_x`, or another step for `k = 1, 2` at non-adjacent ends, plus
  a `Pᵈ` insertion lemma (at `d ≥ 5` every reachable hinge lies in `Λ²(A+B)`, of dimension ≤ 10).
- **CARRIER** (rows 3, 9, 19–21): PD-STATE's. The point-based `HasPencilPanelRealization` is the
  wrong object at `d ≥ 4`. Primal (a `(d−3)`-flat `A_v` in a hyperplane) or dual (a point in a
  3-space); an all-`d` polarity `Λ²K^{d+1} ≅ Λ^{d−1}K^{d+1}` (`screwComplementIso` is grade 2
  only); the collineation lemma; nondegeneracy's lift.
- **GENERIC** (row 22): route B in `Pᵈ`, an irreducible parametrization of the nondegenerate
  realizations, and the one-ear step at `d ≥ 5`. D's candidate witness against the good-ear lemma
  supplying a common neighbour: `C₆` with the chord `14` and `y` joined to `2, 5` (by hand,
  feasibility unchecked).

### 2.4 Proposed tests (named, not run)

- **T1** (row 5): at `d = 4` on the `--d4` population, the flat rank `10(n−1) + 3 − dim L(q)` and
  R1's base `10(n−1) − def[6]`.
- **T2** (CERT): the certificates at `d = 4, 5, 6`, by exact rank.
- **T3** (SHORT): at `d = 4`, ears with `3 ≤ k ≤ 8` and `def[10](G[V₁]) > def[10](G)`: does a
  general datum give `W ⊇ star(y₁) + star(y₃)` with `W ≠ Λ²`, and does (⋆) hold?
- **T4** (ONE-EAR): at `d = 4, 5`, the rank of `G[V₁]` on `G`'s configurations, one-body chains
  whose ends share a neighbour; at `d = 5, 6`, `dim(ρ + Λ²(A+B))` against `3 + f − def[D](G)`.
- **T5** (coverage): the graphs whose only row at `D = 10, 15` is a `k = 1, 2` orbit cell. C's hand
  count: `K₄` with every edge subdivided twice takes the orbit cell at `D = 6` and row 12 at `D = 10`.

## 3. Layers (stable codes)

- **PD-RECON** (42a, open): settle R1 or R2 on paper, or refute with a certificate (§2).
- **PD-STATE**: the `Pᵈ` statement layer on the general-`d` panel carrier, agreeing with Phase 39's
  `P³` definitions. The candidate encoding (Result 13) is a panel realization whose normals on each
  closed neighbourhood span at most three dimensions. Check it against the carrier's definition
  bodies at open; docstrings are not evidence.
- **PD-STABLE**: Results 15–17, formally: the embedding, the deficiency lemma, and `Pᵈ` for
  `def_3 ≤ 1`. It needs PD-STATE and Phase 40, but not the recon.
- **PD-CARRIER**, **PD-STEPS**, **PD-COVERAGE**: Phase 40b–40m in `Pᵈ`, shaped by PD-RECON's route.
- **PD-REDUCTION**, **PD-HEAD**: Phase 39's reduction in `Pᵈ`; the headline `PencilPair`, and the
  flag strata as corollaries.

PD-STATE and PD-STABLE do not depend on the route, so they can run beside PD-RECON; the PI kept
them out of the open (§1).

## 4. Open questions

For the PI:
- The route: §2.2's proposal, R2's induction with R1's base row inside an induction on `d`.
- Whether SHORT and ONE-EAR (§2.3) become attack tracks, and whether `d = 4` is targeted first
  (§2.2: it gives every `d` at `def[3] ≤ 2`).
- Whether the `Pᵈ` headline ships the bare and distinct conjuncts first, GENERIC after (row 22).
- Nondegeneracy's `Pᵈ` lift, and primal or dual carrier (CARRIER; PD-STATE's open).
- When PD-STATE and PD-STABLE open: beside the recon or after it.

Settled by the table: Phase 39's reduction is `d`-general for the bare and distinct conjuncts,
given CARRIER (row 19).
