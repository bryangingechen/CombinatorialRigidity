# Phase 42 — PENCIL-D: design (cross-phase plan and recon)

**Status:** opened 2026-10-29 with the PI, sub-lettered, research first. **42a** (PD-RECON,
`notes/Phase42a.md`) is open: the step table (§2.1), the thresholds `d = 4, 5` and the content
`def[3] ≥ d − 2` (§2.5), T1–T5 (§2.4) and ONE-CLASS's lemma (§2.3, Result 27) have landed, so
**the coverage at `d ≥ 4` needs SHORT-CORE and no ONE-EAR**; ONE-EAR waits for GENERIC. The route
is the PI's (§1): R2's steps, Result 15's embedding as the base row, any induction on `d` left to
Tier 2. SHORT-CORE's attack brief awaits the PI's reading. **42b** (PD-STATE,
`notes/Phase42b.md`) opened beside it, the statement layer in `Pᵈ`: its chapter
`blueprint/src/chapter/pencil-d.tex`, all red. The carrier check (§2.3 CARRIER) found the dual form
right once each body's plane is data; that reading is for the PI's confirmation, and the first leaf
does not depend on it. PD-STABLE is laid out in §3. Next concrete task: 42b's first leaf, the
collineation lemma in every `d`. Evidence: `notes/Strata.md`, Results 12–27.

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
the `--d4` population's cap (`n ≤ 12`, 36 simple graphs) and 8 graphs past it. Where the
conjecture has content, that is 47 cells on 18 graphs, six of them cycles (§2.5).

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
- **PI, 2026-10-29 (planning), the defaults for the next sessions:** "Let's record your
  suggestions and let those be the default for the next session." The suggestions, as put
  (with §2.5's recommendations):
  1. Measure the statement where the proof breaks, before any attack track: §2.5's content-range
     graphs, in T1 and T2's driver mode.
  2. Tiered targets, each a closable headline. Tier 0: every `d` at `def[3] ≤ 1` (PD-STABLE,
     formal only). Tier 1: a `P⁴` theorem, so every `d` at `def[3] ≤ 2` (SHORT, ONE-EAR's `d = 4`
     case, CERT). Tier 2: every `d`.
  3. The bare and distinct conjuncts first, GENERIC after, deferring nondegeneracy's lift with it.
  4. PD-STATE and PD-STABLE open beside the research once T1 and T2 land, the Lean under
     `/coordinate-phase`; the carrier in dual form (a point per body, each closed neighbourhood in
     a plane).
  5. A second read of rows 9 (contraction) and 12 ((⋆), the two-body ear) before anything builds
     on them.

  The order put: T1, T2 and the content-range graphs; then T3 and T4 at `d = 4, 5` on the content
  range, sizing SHORT and ONE-EAR; then attack tracks, with PD-STATE and PD-STABLE in parallel.
- **PI, 2026-10-29 (after T5), the research call of §4:** "ONE-CLASS first (Recommended)". The
  options put: ONE-CLASS's lemma first, on deficiencies alone and checkable exactly against T5's
  population, its size unknown; ONE-EAR's attack at `d = 5` (the motive, a `Pᵈ` insertion lemma,
  X2), the default recorded at open; or SHORT-CORE first, needed either way. On the session's
  work, where the options were this call, PD-STATE's open, or the second read of rows 9 and 12:
  "Let's do 1 but dispatch subagents for the second reads if that can be done safely in
  parallel."
- **PI, 2026-10-29 (after the second reads), the route:** "OK, let's go with this
  recommendation." The recommendation, as put: no separate route discussion before PD-STATE, since
  R1 as a step is out (rows 9 and 14) and every test measured R2's steps. Record R2's step
  structure with Result 15's embedding as the base row, and leave an outer induction on `d` to
  Tier 2, where it may enter only through CERT's open ears at `d ≥ 7`. PD-STABLE states the
  embedding at every `d′ ≤ d`, not only at `d′ = 3`, so that Tier 1 reaches every `d` by it.

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
| 5 | Flat rank (886–1167) | the split `Λ²K⁴ = K³ × K³` | GEN: R2's flat rank `D_d(n−1) + 3 − dim L(q)`; R1's base `D_d(n−1) − def[D_{d−1}]` where `P^{d−1}` attains (both by hand; measured, T1, `Strata.md` Result 20) |
| 6 | Jackson–Jordán's equality (1169–1369) | none: planar, KT Theorem 5.6 at `d = 2` | GEN unchanged |
| 7 | Cut vertex, the shared scheme (1384–1564) | count only (`lem:deficiency-cut-vertex`, every `D`) | GEN: the height is used only as a vector |
| 8 | Chain of bridges (1566–1645) | count only | GEN |
| 9 | Contraction at an additive core, its corollary (1647–2139) | the collineation (row 3), one-witness (row 4), flat attainment (row 5) and `def:pencil-x0-attains`; the KT-layer pins are `k`- or `n`-general | GEN\|CARRIER: "rigid" is `def[D_d](H) = 0`; additivity stays planar, `def[3]`; second read below |
| 10 | Cycle `thm:pencil-x0-cycle` (2387) | the `K⁴` certificate `Y₀…Y₅` (2342) | GEN\|CERT: needs `λ ≥ min(m, D_d)` |
| 11 | Long ear `thm:pencil-x0-open-ear` (2439) | "five interior bodies give six hinges" (2191); the hexagon placement | GEN\|CERT, for `k ≥ D_d − 1` only (9 at `d = 4`) |
| 12 | (⋆) and the two-body ear `thm:pencil-x0-open-ear-two` (2534, 2896) | mathematically none: (⋆)'s `k + 1` holds at every `D` (`lem:block-rank-ear`); every Lean pin is `P³` (`Fin 4`, one height, the hexagon) | GEN\|CARRIER at `k = 2` (a flat certificate in every `d`); `3 ≤ k ≤ D_d − 2` given CERT's open ears; second read below |
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

**Second read of rows 9 and 12** (2026-10-29, the PI's default 5; two read-only recons, Claude
Opus 5.5, briefed to refute). Neither found a gap.
- *Row 9* holds under R2 at every `d ≥ 4`, alike at `d = 4` and `d ≥ 5`. The step consumes `H`
  and `G/H` attaining, each at its own general configuration, and no special locus. Every closed
  condition in it (the lifting systems `M(t)`, `M(0)`, `L(q)`) is planar and acts on each height
  separately; only the two rank conditions couple the heights, and both are open. Row 14 differs:
  its incidence `b_x ∈ Π_a ∩ Π_b` is closed and couples the heights. `def[D]` enters only through
  `H`'s standing hypotheses, `rigidContract_deficiency_eq` and `H`'s target, all `n`-general in
  Lean, and the count closes. The limit at `t = 0` is not a pencil configuration of `G/H` at `r`,
  but the step never needs one. Checked by the reader exactly over `GF(2⁶¹ − 1)` on 6 graphs at
  `d = 4, 5`, cores `D`-rigid but not 6-rigid included, with a non-additive control (measured,
  script not retained).
- *Row 12* holds at every `d ≥ 2` for `k = 2`. With `k ≥ 2`, the ear only fixes `x₁`'s and `x_k`'s
  heights given their picture points, so `G`'s configurations restrict onto `G[V₁]`'s. At height
  zero the points lie in a 3-space whose `Λ²` embeds, so the `k = 2` certificate needs no hexagon.
  For `3 ≤ k ≤ D − 2` the step is the long ear's height-finding with CERT's open ears, proved only
  at `d ≤ 6` (§2.3 CERT). Also, by hand, checked here: `m` parts inside an ear force `m + 1`
  crossings, so `def[D](G) ≤ def[D](G[V₁]) + max(0, k + 1 − D)`. For `k ≤ D − 1` the step's
  hypothesis is therefore an equality, and for `2 ≤ k ≤ D − 2` it is the coverage's merged test.

### 2.2 Verdict on the routes

**Neither route closes as written; the step structure is R2's.** Every step reads Phase 40's
induction on `|V|` at a fixed `d` with all `d − 2` heights general. R1 as "fix `z¹…z^{d−3}` from a
`P^{d−1}` witness and add one height" breaks contraction, whose heights must move along its curve
(B; the curve moves the picture, so this holds at `d = 3` too, and R2 runs it per height, §2.1's
second read), and does not help the one-body ear: every configuration of `G` restricted to `V₁`
lies on the incidence locus, whatever the base (C). What R1 contributes is a **base row**: where `P^{d−1}`
attains at `G`, its base has rank `D_d(n−1) − def[D_{d−1}](G)` (row 5), so `G` attains in `Pᵈ`
whenever `def[D_{d−1}](G) = def[D_d](G)`. That is Result 15 at `d′ = d − 1`; the class grows with
`d` and contains R2's flat class `def[3] = def[D_d]`. The recon's proposal, for the PI: R2's
induction with R1's base row, inside an outer induction on `d`. The PI took R2's induction with
R1's base row, the outer induction left to Tier 2 (§1).

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
  consecutive joins for `m ≤ D_d`, the long ear at `k = D_d − 1` with its ends at height zero,
  and row 12's open ears: `k + 1` independent joins, heights zero at `a, x₁, x_k, b`. **Holds at
  `d ≤ 6`, over every field** (T2, `Strata.md` Result 21). The `D`-gon is a construction in every
  `d`: B's Euler circuit at even `d`, a matching and detours at odd `d`, checked at `d = 3, 5`. Left
  for PD-STEPS: a uniform construction for `m < D` and the open ears (or, at the cycle, KT, since a
  cycle's pencil condition is empty). Row 12's second read (§2.1) sizes the open ears at `d ≥ 7`.
  A certificate at `d′` stays one at every `d ≥ d′` (embed the heights; `Λ²` of an injective map
  is injective), so only `D_{d−1} ≤ k + 1 ≤ D_d − 1` is new at `d`. Trails in the complete graph
  on an affine basis with first and last edges at height zero give every `k + 1 ∈ [4, D − 1]` at
  `d = 3, 4, 6`. At odd `d` parity caps them at `D − (d−1)/2` edges, so the top values need
  detours, as the `D`-gon's do (the reader's search, measured, script not retained).
- **SHORT** (row 13): ears with `3 ≤ k ≤ D_d − 2` and `def[D](G[V₁]) > def[D](G)`. Re-inserting
  `x₂` adds only joins in `star(y₁) + star(y₃)`, so the step needs X3: at general ear data, `W`
  containing both stars is `Λ²K^{d+1}`. It is needed only where `def[D](G'') = def[D](G)` and
  `2d − 1 ≤ dim W ≤ D − 1` (the danger cells); elsewhere the `d`-general insertion lemma settles
  the step. **X3 holds for `k ≥ C(d−1, 2) + 3`** (6 at `d = 4`, 9 at `d = 5`) at every graph.
  The stars have codimension `C(d−1, 2)`, and the joins `y₄ y₅, …, y_k p_b` of `G''`'s ear lie in
  `W`; they span the quotient at one ear datum, hence at a general one. There `y₄, …, y_{k−1}` are
  free and `y_k` any point of `Π_b`, so a linear map onto `K^{d+1}/⟨y₁, y₃⟩` places CERT's closed
  `C(d−1, 2)`-gon of `P^{d−2}` (Result 21: the triangle at `d = 4`, the hexagon at `d = 5`) with
  its last two points over `y_k` and `p_b`. At `d = 3` this is the chapter's tetrahedron. **Left,
  SHORT-CORE:** `3 ≤ k ≤ C(d−1, 2) + 2` (3–5 at `d = 4`, 3–8 at `d = 5`), where `ρ`'s image in
  that quotient must supply the rest; the chapter's `k = 3` case split on `ρ` is the `d = 3` model.
  T3 (§2.4) found no obstruction on 198 danger cells. New mathematics, now bounded. Attack brief:
  `notes/attacks/short-core/brief.md` (DRAFT, awaiting the PI).
- **ONE-EAR** (rows 14–15): either a motive that asks `G[V₁]` to attain on the locus where `Π_a`
  and `Π_b` meet above a general `q_x`, or another step for `k = 1, 2` at non-adjacent ends, plus
  a `Pᵈ` insertion lemma (at `d ≥ 5` every reachable hinge lies in `Λ²(A+B)`, of dimension ≤ 10).
  **T4 sized it** (§2.4; `Strata.md` Results 23, 25): the first option stands wherever the `d = 3`
  steps' merged hypothesis **M**, `def[3](G[V₁]; a, b) + 2 ≤ def[3](G[V₁])`, holds, at every cell
  measured, `d = 3..6`, and fails only where M fails, as at `d = 3`. T5 (§2.4) confined its role
  in the coverage at `D ≥ 10` to row 14 on ONE-CLASS, and ONE-CLASS is Phase 40's (below), so
  **the coverage never needs ONE-EAR**. It remains GENERIC's (row 22's one-ear step). Its open
  parts, for an attack at `d = 5` when GENERIC opens:
  - **The motive:** `G[V₁]` attains at a general configuration of `G[V₁]` plus the ear
    `a − x − b`, restricted to `V₁`. At `d = 3` this is `lem:pencil-one-ear-base`; at `d = 4`
    without a shared neighbour the incidence is free, as two planes of `P⁴` meet in one point.
    New at `d ≥ 5`, and at `d = 4` with a shared neighbour. At `k = 2` every configuration of
    `G₁` lies on the locus, so `G₁` attaining and the motive are two open conditions on one
    irreducible space, and meet.
  - **The insertion:** `dim(ρ + Λ) ≥ min(s + 1, dim(ρ + Λ²(A+B)))`, the `Pᵈ` form of
    `lem:pencil-insertion-two`, and **X2**: where M holds, `W ⊉ Λ²(A+B)` unless `W = Λ²`. X2 is
    free where `Π_a + Π_b = K^{d+1}`, so `Λ²(A+B)` is everything: at `d = 3`, where M gives
    `Π_a ≠ Π_b`, and at `d = 4` when `Π_a ∩ Π_b = ⟨y⟩`. Both are measured only beyond that.
  - **`(⋆)` at `k = 1` with `def[D](G[V₁]) > def[D](G)`: not needed.** Theorem S holds at every
    `D ≥ 6` (T5, §2.4), so the coverage uses a one-body chain only where row 14's
    `def[D](G[V₁]) ≤ def[D](G)` holds, or splits it off. Measured anyway at 46 cells (T4), with
    `dim(ρ + Λ) = min(dim ρ + 2, D)`.
- **ONE-CLASS** (T5, §2.4): the graphs past rows 1–5 with `def[D](G) = 0`, only one-body chains
  and no core at `D`, the only ones where the coverage at `D ≥ 10` could need ONE-EAR. **Settled
  `[PROVED]`** (this session, Claude Opus 5.5, at the PI's call, §1; `Strata.md` Result 27):
  each has `def[6](G) = 0`, so Phase 40's `P³` witness embeds (Result 15). The lemma: let `G` be
  sparse, of minimum degree two, with no two bodies of degree two adjacent, and `D ≥ 6`. If
  `def[6](G) > 0`, a set `W` of least `s_3` among those of two or more bodies with `def[D]` zero
  is a core at `D`.
  - *A set below `V`.* Let `P` attain `def[6](G) > 0`. Refining a part by a partition changes
    `P`'s value by that partition's value in the part (`lem:separated-partition-value`), so each
    part has `def[6]` zero, so `def[D]` zero (`lem:deficiency-antitone`). The singletons have
    value `6(n − 1) − 5|E| < 0`, since no two bodies of degree two are adjacent gives `5|E| ≥ 6n`
    (the count in `lem:pencil-x0-sparse-count` (2)). So some part `Z` has `|Z| ≥ 2`, and `Z ≠ V`.
    As `v_6(P) = 2v_3(P) − e(P) > 0`, `v_3(P) ≥ 1`, and `lem:deficiency-singleton-bound` gives
    `s_3(Z) ≤ s_3(V) − v_3(P) < s_3(V)`.
  - *The core.* `s_3(W) ≤ s_3(Z) < s_3(V)`, so `W ≠ V`. If some `X ⊇ W` had `s_3(X) < s_3(W)`,
    one of least size would have `s_3(Q) ≥ s_3(W)` whenever `W ⊆ Q ⊊ X`, so `def[D](G[X]) = 0`
    (`lem:deficiency-core-bound` (1), read at `D` as in T5), against the choice of `W`. So
    `s_3(W) ≤ s_3(X)` for every `X ⊇ W`: no body outside `W` has two neighbours in it
    (`lem:deficiency-add-body`), and `lem:deficiency-additive-core` (2) gives the additivity.

  The second half also shows that `G` has a core at `D` exactly when a set of least `s_3` among
  those of `def[D]` zero can be taken proper. The lemma first posed here (ONE-CLASS empty at
  `D ≥ 15`, an unshared chain at `D = 10`) is not needed, and is not what holds: cells with no
  core occur at every `D` measured, all with `def[3] ≤ 2`, so outside the content range at
  `d ≥ 5`. Checked by `oneclass.py` (§2.4).
- **CARRIER** (rows 3, 9, 12, 19–21): PD-STATE's. The point-based `HasPencilPanelRealization` is
  the wrong object at `d ≥ 4`. Primal (a `(d−3)`-flat `A_v` in a hyperplane) or dual (a point in a
  3-space); the collineation lemma; nondegeneracy's lift. The all-`d` polarity exists:
  `complementIso` (`j := 2`, every `k`; `Molecular/Meet.lean`) underlies `panelSupportExtensor`,
  and `finrank_span_rigidityRows_mapExtensor` is `k`-general. So rows 9 and 12 need only
  conjugation through it (second read, §2.1); `screwComplementIso` and `pointJoinFramework` are
  the `P³` route's. Their `P³` pins to restate: `def:pencil-x0-attains`, the one-witness lemma,
  the magnified rank, the scale-shift and the join-independence lemmas (`Fin 4`, one height).
  Also name `bodyBarDim (k+1) = screwDim k`, now inline in `PanelLayer.lean`. Rows 19–21 were
  not re-read. The PI's default is the dual form (§1, item 4). **Checked against the definition
  bodies at 42b's open** (2026-10-30, this session, Claude Opus 5.5; the two surprises by a
  `lake lean` witness, scratch, not retained):
  - *`HasPencilPanelRealization` at grade `k`* (`Statement.lean`) is point-based, as read: at
    `k ≥ 3` the hinges at a body pass through one point of the panel and need share no line
    (`rem:pencil-d-point-type`'s three planes of `P⁴`). `HasPencilRealization`,
    `HasDistinctPencilRealization`, `IsNondegPencilRealization` and `PencilPair` fix grade 2 and
    `Fin 4`; `X0Attains` reads the rank at `ofNormals (k := 2)` of the configuration points.
  - *Read literally, the dual form fails both ways.* (W1) On the containment carrier
    `HasCoplanarPanelRealization` the one-line encoding of §3 ("normals on each closed
    neighbourhood span ≤ 3") is strictly weaker than Phase 39's at `d = 3`: at dependent adjacent
    normals `ExtensorInPanel` admits any line of the shared plane. Witness: two bodies, three
    parallel edges, normal `e₀` at both, hinges `e₁e₂`, `e₁e₃`, `e₂e₃`; the encoding holds, and
    no nonzero point lies on all three, so no `HasPencilPanelRealization` exists (`K₁,₃` with one
    panel is the simple-graph form). (W2) On the meet carrier (`ofNormals`, hinges
    `complementIso` of the joins, Result 13's form) parallel edges get one hinge, so the double
    edge cannot reach rank `D` (the target, `def = 0`), while Phase 39's bare conjunct holds there.
    The meet form does agree with the distinct conjunct (`lem:pencil-d-point-configuration`).
  - *What agrees:* the dual form with each body's 3-space `Π_v ∋ b_v` as data and every hinge at
    `v` through `Π_v^⊥` (dually, a line through `b_v` in `Π_v`), i.e. §2.3's own "dual (a point
    in a 3-space)". At `k = 2`, `Π_v = q_v^⊥` makes it Phase 39's definition on the nose; the
    distinct conjunct agrees through `lem:pencil-self-dual`. Stated as `def:pencil-d-realization`
    (red), pending the PI.
  - *Options, for the PI's confirmation* (not blocking: 42b's first leaf is the same under each).
    (a) The reading above, **recommended**, and what the chapter's red nodes state (restated if
    the PI picks otherwise): the predicate, its `d = 3` agreement and the distinct bridge, about
    three commits. (b) Primal data `(b_v, A_v = Π_v^⊥)`: the same mathematics and
    cost, the data named the other way; the PI's default is dual. (c) The meet form alone: the
    cheapest (no predicate beyond a span condition), but the `Pᵈ` headline loses the bare
    multigraph conjunct, against §0. (d) The normals-only encoding: fails W1, not viable.
- **GENERIC** (row 22): route B in `Pᵈ`, an irreducible parametrization of the nondegenerate
  realizations, and the one-ear step at `d ≥ 5`. D's candidate witness against the good-ear lemma
  supplying a common neighbour: `C₆` with the chord `14` and `y` joined to `2, 5` (by hand,
  feasibility unchecked). It has `def[3] = 0` (Result 22), so its rank is Result 17's; the
  question it raises is GENERIC's alone.

### 2.4 Proposed tests (T1–T5 run)

- **T1** (row 5): at `d = 4` on the `--d4` population, the flat rank `10(n−1) + 3 − dim L(q)` and
  R1's base `10(n−1) − def[6]`. **Run** at `d = 4, 5, 6` (`Strata.md` Result 20): both formulas
  hold; R1's base is at the `Pᵈ` target on 30 of 36 simple graphs at `d = 4`, missing only cycles
  and `C11ear`.
- **T2** (CERT): the certificates at `d = 4, 5, 6`, by exact rank. **Run** at `d = 3..6`, over
  every field (Result 21; §2.3).
- **T3** (SHORT): at `d = 4`, ears with `3 ≤ k ≤ 8` and `def[10](G[V₁]) > def[10](G)`: does a
  general datum give `W ⊇ star(y₁) + star(y₃)` with `W ≠ Λ²`, and does (⋆) hold? **Run** at
  `d = 3, 4, 5` (`Strata.md` Result 24; `--short`, seeds 1–3, the cells seed-independent), on
  danger cells only (§2.3), two per family, `d` and `k`, `n ≤ 40`. `G[V₁]` is a cycle, or a theta
  with `a, b` its hubs, inside two paths, inside one, or a hub and a path body, or a necklace of
  diamonds, where a pencil condition binds at every diamond body. Every deficiency is certified by
  a partition and a generic rank (the cells at `d = 4, 5` have `n ≥ 17`, past the DP cap). At all
  72 cells at `d = 4` and 126 at `d = 5`,
  `G[V₁]` and `G''` attain, `W` contains neither star, each star meets the rest of `W` in the
  general-position dimension, and `x₂` at a general point gains the dimension (⋆) needs; (⋆) also
  holds at a general ear datum of `G`. Modulo the stars, `ρ`'s image has dimension
  `min(dim ρ, C(d−1, 2))`, the joins' `min(k − 3, C(d−1, 2))`, and `W`'s is everything. The 24
  cells at `d = 3` assert the chapter's theorem. So X3 stands, and the step that moves `x₁` and
  `x₃` is not needed on this population; §2.3 bounds what is left.
- **T4** (ONE-EAR): at `d = 4, 5`, the rank of `G[V₁]` on `G`'s configurations, one-body chains
  whose ends share a neighbour; at `d = 5, 6`, `dim(ρ + Λ²(A+B))` against `3 + f − def[D](G)`.
  **First half run** (`Strata.md` Result 23; `--oneear`, seeds 1–3, the cells seed-independent).
  The ear is `a − x − b` on theta graphs, `G₁ = G − x`, and a configuration of `G` restricted to
  `V₁` is a general point of the incidence locus. On `θ(2, 2, k)` (`k = 4..10`, the ends share
  one neighbour) and the control `θ(2, 3, k)` (`k = 4..9`, none), where the step's merged
  hypothesis holds, `G₁` attains there at all 26 cells. The locus is proper: `dim(Π_a ∩ Π_b)` is 2
  on it against 1 at `G₁`'s own configuration on `θ(2, 2, k)`, and on `θ(2, 3, k)` 1 against 0 at
  `d = 5` (1 and 1 at `d = 4`, where the incidence costs nothing). The step's other hypothesis
  read at `D`, `def[D](G₁) ≤ def[D](G)`, fails at `d = 4` on `θ(2, 2, 9)` and `θ(2, 3, 8)`
  (`G₁ = C₁₁`): there `(⋆)` at `k = 1` asks `dim(ρ + Λ) ≥ 3`, not 2, the second half's question.
  On `θ(2, 2, 2, k)` (`k = 5..10`, two shared neighbours `y, w`; the merged hypothesis fails under
  the cap) `G₁` attains at 11 of 12 cells and misses at `k = 10`, `d = 4`: 119 against 120, a
  target `G₁`'s own configuration certifies. **The miss is forced.** Where `b_x, b_y, b_w` are
  independent, `Π_a` and `Π_b` (each 3-dimensional, both containing them) coincide, so the cycle
  `a y b w` has its four hinges in the 3-dimensional `Λ²Π_a`. A dependency among them, with
  `k`-path coefficients solving the long cycle's equation, is a nonzero motion assignment of `G₁`
  (`Strata.md` Result 1) wherever the path's hinges span `Λ²K^{d+1}` (so `k ≥ D`), and `G₁` ranks at most
  `D(n₁ − 1) − 1`. Both conditions are open on `G`'s irreducible configuration space and hold at
  the seeded point (the driver checks both, exactly, and lists the cell), so the bound holds on a dense subset of the locus.
  **Second half run** (`Strata.md` Result 25; `--orbit`, seeds 1–3, the rows seed-independent).
  The orbit cells: open ears with `k = 1, 2` interior bodies at non-adjacent ends and
  `def[D](G[V₁]) > def[D](G)`, where row 12 does not apply, on the content range at `d = 3..6`.
  The population is T3's six families, `n ≤ 40`, every deficiency certified, M certified per cell.
  - `k = 1`: 46 cells, Result 23's two `d = 4` cells among them, all with M. `G[V₁]` attains on
    the locus at every one, `d = 6` included, and `(⋆)` holds: `dim(ρ + Λ) = min(dim ρ + 2, D)`,
    so `ρ` supplies the `need − 2 = f − def[D](G)` that the `d = 3` hypothesis
    `def(G̃[V₁]) ≤ def(G̃)` makes at most zero.
  - `k = 2`: 69 cells with `def[D](G₁) = def[D](G)`, so `(⋆)` needs `s + 1`, `s = dim W` at
    `G₁`'s configuration. 16 are danger cells at `d = 5, 6` with M: `10 ≤ s ≤ D − 1`, so
    `W` could hold `Λ²(A+B)`. At every cell `G₁` and `G[V₁]` attain on the locus and a general
    insertion reaches `min(s + 1, c)`, `c = dim(ρ + Λ²(A+B))`. At all 62 with M, `W ⊉ Λ²(A+B)`
    and the insertion gains `(⋆)`'s one dimension, so the route goes through.
  - The 7 cells without M, at every `d` from 3 to 6, are necklaces whose ends lie in two diamonds
    joined by one edge. Each diamond's points lie in one 3-space, the edge's ends lie in both, and
    `y` makes three, so the locus forces `Π_a = Π_b` (`dim Λ²(A+B) = 3`). There `c = 3 < 4 =
    need` and the route fails, at `d = 3` as at `d = 6`; `G` attains at its own configuration.
- **T5** (coverage): which rows of the coverage carry the graphs at `D = 10, 15`. C's hand count:
  `K₄` with every edge subdivided twice takes the orbit cell at `D = 6` and row 12 at `D = 10`.
  **Run** (`Strata.md` Result 26; `--coverage`, exact combinatorics, seed-independent), with two
  arguments by hand (this session, Claude Opus 5.5; `HARNESS.md`: claimed proved, read the proof
  before building on it).
  - **Theorem S at `D` `[PROVED]`.** The proof of `thm:pencil-x0-theorem-s` holds at every
    `D ≥ 6` with "rigid" read as `def[D] = 0` and "usable" read at `D`: `k ≥ 3`; `k = 2` with
    `m = f`, or ends apart and M; `k = 1` with `m = f` or `m + D − 1 ≤ f`. Here
    `f = def[D](G[V₁])` and `m = def[D](G[V₁]; a, b)`. The constants move as follows.
    `lem:deficiency-one-body-chain` (2) gives `m + D − 1 ≤ f` unless `x` lies in a `D`-rigid set:
    its `10 − 6 = 4` becomes `2(D − 1) − D = D − 2`, and an edge from `x` to another part costs
    `D − 1 > D − 2`. `lem:deficiency-two-body-chain` holds at `D ≥ 6`, since a tight set is rigid
    at 6 and hence at `D` (`lem:deficiency-antitone`). The 4-cycle is `D`-rigid at `D ≥ 4`.
    `lem:pencil-x0-sparse-count` (2) gives `s_D(V − x) = Dn − (D − 1)|E| − 2 < 0` from
    `5|E| ≥ 6n`. `lem:deficiency-core-bound` needs only that a value of at most zero at `d = 2`
    is at most zero at `D ≥ 3`. `-merge-rigid`, `-add-body` and `-ear-merge` hold at every `D`,
    and the additivity is planar. So a graph past rows 1–5 has a chain usable at `D` or a core at
    `D`. It uses a one-body chain only through `m = f`, which gives `f ≤ def[D](G)`, or through
    the split-off. **ONE-EAR's third part is never needed.**
  - **Where ONE-EAR can be load-bearing, `D ≥ 10` `[PROVED]`.** Call a row GEN when its `Pᵈ` step
    needs only formal work (§2.1's GEN rows, CERT, CARRIER, SHORT's X3 range, row 14 at `d = 4`
    without a shared neighbour). For a set `W` of core bodies and whole paths,
    `s_D(W) = ΣL − D·c`, with `ΣL` the paths' lengths and `c` the cycle rank. Let a graph past
    rows 1–5 have no GEN row. If `def[D](G) > 0`, it has no `D`-rigid set, since Theorem S's
    maximal one would be a core. Then every one-body chain splits off by (2). And `s_D(V) ≥ 1`
    with `c ≥ e/3 + 1` (core bodies of degree 3 or more, `e` core edges) forces a path longer
    than `D/3`, so a chain with `k ≥ 3`. If `def[D](G) = 0` and every chain has `k ≤ 2`, then a
    two-body chain has `s_D(V₁) ≤ e(3 − D/3) − 3 < 0`. So a `D`-rigid set avoids `x₁`, and
    Theorem S's argument with `X₀ = {x₁}` gives a core. **So a graph with no GEN row has a chain
    with `k ≥ 3`, or `def[D](G) = 0` and only one-body chains.** Given SHORT, row 15 is never
    needed at `D ≥ 10`, and row 14 only on that class, call it **ONE-CLASS**: `def[D](G) = 0`,
    every chain one-body, and no core.
  - **Measured.** The population is subdivisions of ten cores of minimum degree 3 (`θ₃`, `θ₄`,
    two small multigraphs, `K₄`, `W₄`, the prism, `K₃,₃`, the cube, Petersen), each core edge a
    path of 1–4 edges, simple, sparse and in the content range. That is every length vector up to
    isomorphism on the five smallest cores and 60 drawn on the others: 1077, 1059, 1021 and 957
    cells at `d = 3..6`. At `d = 4, 5, 6` every cell has a GEN row, so no cell needs SHORT-CORE or
    ONE-EAR. A core is present at every one, and is the only GEN row at 20, 9 and 6. So the cover
    rests on row 9, and the second read of rows 9 and 12 (§1; landed, §2.1) weighs more. A one-body box (paths
    of 1–2 edges) gives 231, 180 and 131 cells at `d = 4, 5, 6`, all with `def[D](G) = 0` and
    every chain one-body, and each has a GEN row. At `d = 5, 6` each has a core, its only GEN row
    (row 14 the alternative), so ONE-CLASS is not met there. At `d = 4`, 228 have a core. The other
    three are in ONE-CLASS: `K₃,₃` and two Petersen subdivisions, `def[3] = 2`. Row 14 carries
    each at ends that share no neighbour, and so does R1's base row. At `d = 3`, 8 cells have only
    `k = 1, 2` ear rows (7 only row 15's), C's `K₄` among them; it takes row 12 and a core from
    `d = 4`. Past the box, Petersen with every edge a 4-path at `d = 4`, or a 6-path at `d = 5`,
    has only SHORT-CORE's rows (`k = 3`, `k = 5`): `def[D](G) = 0` and no core (by hand, every
    proper subgraph has `ΣL > D·c`, so no proper set is `D`-rigid). So the coverage needs
    SHORT-CORE, and on this population ONE-EAR nowhere.
- **ONE-CLASS** (the PI's call after T5, §1; `Strata.md` Result 27; `oneclass.py`, exact, no
  draw). Proved by hand (§2.3) and checked at `D = 6, 10, 15, 21`. On T5's ten cores and every
  core of nauty's on 4–8 bodies with at most 12 edges, paths of 1–2 edges (279 and 13 738 cells),
  `def[6] > 0` never occurs: it needs a quotient with under `6/5` edges per part past the first,
  a ring of rigid blobs. The 523 cells with no core all have `def[3] ≤ 2`. On three necklaces of
  diamonds and `K₄ − e` (432 cells, 151 with `def[6] > 0`) the proof's set is a core at every
  cell and `D`. **So with T5, a graph past rows
  1–5 at `D ≥ 10` has a GEN row (the embedding of Phase 40 at `def[6] = def[D]` counted, Result
  15) or a chain with `k ≥ 3`, and the coverage's only new mathematics is SHORT-CORE.**

### 2.5 Where the dimension bites: two frames (2026-10-29)

This session (Claude Opus 5.5) read §2.1–§2.2 against `Strata.md` Results 15–19 with the PI. The
question: is `d = 4` to PENCIL-D what `d = 3` was to KT? Not in KT's sense. KT's proof is uniform
in `d`: its geometry, two panels meeting in a `(d−2)`-flat, is the same in every `d`, and `d = 3`
is the worked case (Lemma 6.10; §6.4.2, p. 692: *"The proof strategy is exactly the same as
`d = 3`"*). The pencil's `Π_v` stays 3-dimensional while `K^{d+1}` grows, so incidences that are
free in `P³` become conditions. That gives two kinds of threshold:

- **The steps' thresholds, 4 and 5.** At `d = 4` the short ears and route B's steer fail (rows 13
  and 22: two stars have codimension `C(d−1, 2)`). At `d = 5` the one-body ear and route B's
  one-ear fail outright (rows 14 and 22: `Π_a ∩ Π_b` has dimension `5 − d`). So `d = 4` is where the
  `P³` argument first breaks, not where it breaks in its general form: a `d = 4` ONE-EAR may use the
  point `Π_a ∩ Π_b`, which is gone at `d ≥ 5`. T4 (`d = 5, 6`) asks whether 5 is the last
  threshold. Rows 13, 15 and 22 are where Phase 40 found new mathematics at `d = 3` (SHORT, ORBIT
  and route B; ROADMAP §40).
- **The graph's threshold, `2 + def[3](G)`.** Inside the outer induction on `d` (§2.2), `G` attains
  at `d` from `P^{d−1}` whenever `def[3](G) ≤ d − 3`. Then `D_{d−1} = C(d, 2) ≥ C(3 + def[3], 2)`, and
  Result 16 makes `def[D_{d−1}] = def[D_d] = def_∞`. So the work at `d` is the graphs with
  `def[3](G) ≥ d − 2`. That class is nonempty at every `d`, so no fixed `d` suffices; a `P⁴` theorem
  gives every `d` at `def[3] ≤ 2`. Such a `G` has a partition with
  `e(P) ≤ (3|P| − 3 − def[3])/2`, a quotient of average degree below 3 and rich in ears, which is
  where rows 13–15 sit.

**The evidence where the conjecture has content**, read off `strata.py --pd --seed 1`. Of the 36
simple capped graphs, 24 have `def[3] ≤ 1` and are settled at every `d` by Result 17. The cells at
`d ≥ 4` with `def[3] ≥ d − 2` are 47, on 18 graphs (12 capped, 6 past the cap). Result 19's 41
leaves out each graph's top cell, `d = 2 + def[3]`, which also carries content.
- **Six are cycles.** Every body has degree 2, so the pencil condition is empty (three points span
  a plane), and these cells are KT's case.
- **The other twelve** are thetas, cycles with triangle ears, subdivided `K₄`, `K₃,₃` and Petersen,
  and `ring5`. In all but `ring5` the condition binds at 2 to 10 bodies, and `ring5`'s only content
  cell is `d = 4`.
- **What none of them has, in that range:** row 14's configuration (a one-body ear whose
  non-adjacent ends share a neighbour), route B's two hubs with three common neighbours, or a
  condition at every body at `d ≥ 5`.
- **Measured since** (`strata.py --content`, seeds 1–3; `Strata.md` Result 22): 38 more content
  cells, on 15 graphs that carry all three between them, every one at its target. Up to `d = 6`
  these are `θ(2, 2, k)` (`k = 4..10`, `def[3] = k − 2` under the cap), `θ(2, 2, 2, k)`
  (`k = 5..10`, `def[3] = k − 3`) and the diamond rings at `m = 6, 7`. That makes 85 content cells,
  none below target. So far the failing rows fail as proof steps only: every graph built to carry
  their configurations attains.

**Recommendations**, for the PI (§4):
- **Measure the statement where the proof breaks**, before any attack track (**done**: every
  cell matched, above):
  - `θ(2, 2, k)` (paths of 2, 2 and `k` edges between two hubs): row 14's configuration,
    `def[3] ≥ k − 2` by the singleton partition, `n = k + 3`.
  - `θ(2, 2, 2, k)`: route B's, `def[3] ≥ k − 3`.
  - Diamond rings at `m = 6, 7`: a condition at every body, `def[3] ≥ m − 3`, certified by reaching
    `D(n−1)` as `ring5` is.
  - D's candidate witness (§2.3, GENERIC).

  A shortfall redirects the phase. A match is the first evidence where the failing rows bite.
- **Run T3–T5 at each `d` only on graphs with `def[3] ≥ d − 2`**, and run T3 at `d = 5` as well.
- **Attack each obligation at its own threshold:** SHORT at `d = 4`, ONE-EAR at `d = 5`, each
  checked one dimension up. `d = 4` stays the first milestone (every `d` at `def[3] ≤ 2`), but its
  ONE-EAR case must not lean on `Π_a ∩ Π_b ≠ 0`. (Since Result 27 the coverage needs no ONE-EAR,
  §2.3; it stays GENERIC's.)

## 3. Layers (stable codes)

- **PD-RECON** (42a, open): settle R1 or R2 on paper, or refute with a certificate (§2).
- **PD-STATE** (42b, open, `notes/Phase42b.md`): the `Pᵈ` statement layer on the general-`d`
  panel carrier, agreeing with Phase 39's `P³` definitions. Its dep-graph is
  `blueprint/src/chapter/pencil-d.tex`: the carrier definitions (an extensor through a subspace,
  pencil realizations in dimension `d` with each body's 3-space as data, their rank and
  adjacent-distinct forms), the `d = 3` agreement, the dual form's bridge (independent adjacent
  normals give the meet form, and configurations over admissible pictures are pencil
  realizations), and CARRIER's restatements (configurations, attaining, the collineation, the
  scale-shift, one witness, the magnified rank, join independence). The encoding's check and the
  options put to the PI: §2.3 CARRIER. Nondegeneracy's lift is GENERIC's (§4), not PD-STATE's.
- **PD-STABLE** (stable code; it states over PD-STATE's definitions, so it opens once they land):
  Results 15–17, formally. It needs PD-STATE and Phase 40, not the recon. `G` satisfies
  `def:pencil-x0-standing`; `def[D_d]` is Lean's `G.deficiency d` (`bodyBarDim d = D_d`), so
  `def[3]` is `G.deficiency 2` and `def[6]` is `G.deficiency 3`. Planned names are tentative.
  1. *The embedding, at every `d′ ≤ d`* (Result 15; the route, §1). Let `ι : K^{d′+1} → K^{d+1}`
     insert zeros before the last coordinate, and `φ` the injective map of screw spaces it induces
     on the polar lines (`complementIso` of `Λ²ι`). **Rank:** for a framework on a connected `G`,
     `rank(φF) = rank F + (D_d − D_{d′})(|V| − 1)`; split the screw space as `im φ ⊕ T`, so a
     motion of `φF` is a motion of `F` plus one constant in `T` (planned
     `BodyHingeFramework.finrank_span_rigidityRows_map_injective`). **Statement
     form** (PD-HEAD): a pencil realization in dimension `d′` of rank
     `D_{d′}(|V| − 1) − def[D_{d′}]` gives one in dimension `d` of rank `D_d(|V| − 1) − def[D_{d′}]`
     (`b ↦ ιb`, `Π ↦ ιΠ`), at the deficiency rank where `def[D_{d′}] = def[D_d]` (planned
     `hasGradedPencilRealization_of_le`). **Configuration form** (PD-COVERAGE; `3 ≤ d′ ≤ d`): the
     configuration `(q, (z′, 0, …, 0))` has the rank of `(q, z′)` plus `(D_d − D_{d′})(|V| − 1)`, so
     if the general configuration attains in dimension `d′` and `def[D_{d′}](G) = def[D_d](G)`, it
     attains in dimension `d` (one main picture and `lem:pencil-d-x0-one-witness`; planned
     `Graph.X0AttainsGrade.of_le`). Its `d′ = 3` case is the form PD-COVERAGE consumes,
     `def[6](G) = def[D](G)`, and settles ONE-CLASS (Result 27); its `d′ = 4` case takes Tier 1
     to every `d`.
  2. *The deficiency lemma* (Result 16): if `2 + def[3](G) ≤ d′ ≤ d`, then
     `def[D_{d′}](G) = def[D_d](G)`. Proof: a partition with cycle rank `c ≥ 1` positive at
     `D′ = D_{d′}` has `|P| − 1 > (D′ − 1)c`, so `def[3] ≥ |P| − 1 − 2c > (D′ − 3)c ≥ D′ − 3`,
     against `D′ ≥ C(def[3] + 3, 2)`; so above `D′` only tree quotients count, at a value free of
     `D`. Holds for every multigraph. Planned `Graph.deficiency_eq_of_two_add_deficiency_two_le`,
     beside `lem:deficiency-antitone`.
  3. *`Pᵈ` at `def[3] ≤ 1`* (Result 17; Tier 0): if `def[3](G) ≤ 1` and `d ≥ 3`, the general
     configuration of `G` attains in dimension `d`, so `G` has an adjacent-distinct pencil
     realization at the deficiency rank in dimension `d` (`lem:pencil-d-config-realization`).
     Proof: Phase 40 (`thm:pencil-x0-generic-attains`) at `d′ = 3`, item 2 (`def[3] ≤ 1 = d′ − 2`)
     and item 1. Result 17 embeds the planar witness at `def[3] = 0`; `d′ = 3` covers that case
     too, as there `def[6] = def[D] = 0`. Planned `Graph.x0AttainsGrade_of_deficiency_two_le_one`.
- **PD-CARRIER**, **PD-STEPS**, **PD-COVERAGE**: Phase 40b–40m in `Pᵈ`, on R2's steps (§1).
- **PD-REDUCTION**, **PD-HEAD**: Phase 39's reduction in `Pᵈ`; the headline `PencilPair`, and the
  flag strata as corollaries.

PD-STATE and PD-STABLE do not depend on the route, so they run beside PD-RECON (§1's defaults).
PD-STATE opened as 42b on 2026-10-30; PD-STABLE opens once PD-STATE's definitions have landed.

## 4. Open questions

The PI's planning defaults (§1) answer most of the calls put at the open. A session follows them
unless a finding argues otherwise:
- `d = 4` first, as Tier 1 of three. SHORT is attacked at `d = 4` and ONE-EAR at `d = 5`, as
  attack tracks once T3 and T4 size them (§2.5). Both have: SHORT's attack is SHORT-CORE, `k = 3,
  4, 5` at `d = 4`. ONE-EAR (the motive, the insertion and X2 at `d = 5`) has left the coverage
  (Result 27, §2.3), so it waits for GENERIC.
- The headline ships the bare and distinct conjuncts first, GENERIC after (row 22). Nondegeneracy
  enters `PencilPair` only in the generic conjunct (`Pencil/Motive.lean`), so with row 22's reading
  its `Pᵈ` lift is deferred with it.
- The carrier in dual form (CARRIER). Checked at 42b's open: it agrees with Phase 39's
  definitions once each body's 3-space is data (§2.3), the reading put to the PI for confirmation.
- PD-STATE and PD-STABLE open beside the research once T1 and T2 land: PD-STATE has, as 42b.

Settled by the PI (§1): the route. R2's steps with Result 15's embedding as the base row; an outer
induction on `d` is Tier 2's question, entering if at all through CERT's open ears at `d ≥ 7`.
Open for the PI: the reading of SHORT-CORE's DRAFT brief, and confirming the carrier's reading
(§2.3 CARRIER, options (a)–(d)); neither blocks 42b's first leaf.

Settled by the table: Phase 39's reduction is `d`-general for the bare and distinct conjuncts,
given CARRIER (row 19). Settled by the PI's call (§1) and Result 27: ONE-CLASS, not ONE-EAR. Its
lemma is proved, so the coverage at `d ≥ 4` needs SHORT-CORE and no ONE-EAR (§2.3–2.4).
