# PENCIL — informal mathematics workbook (kernel-(K) arc)

**Scope.** This workbook carries the **live kernel-(K) arc**: the escape
uniformity kernel `hK` and its descendants, plus the (K-bare) stub. The
**W4 (`hcontract`) residual arc** — `hnoGood'` vacuity, (SAFE-RES)/(SAFE-RES′),
and the routes-1/3 kernel widening ((K-res), (E)/(E-loc)/(T)/(V)) — was split
out to **`notes/Pencil-W4-informal.md`** on 2026-08-05: all three of its
sections are closed as arguments and W4 itself is parked by the route-3(b)
adjudication, but they stay at full detail there as the eventual W4 build's
input. The *Shared dictionary* and *State of (K)* map below serve both files.

**Purpose.** Informal proofs under development for the kernels and branch
arms Phase 39 (PENCIL) carries as hypotheses. This is the **staging ground
before blueprint transcription**: nothing here is formalization-committed, no
`\lean{...}` pin points at it, and a section may be rewritten wholesale when
the argument changes. Once a section reaches *proven-informally* and the
coordinator commissions its build, its content moves to
`blueprint/src/chapter/pencil.tex` (with a `notes/BlueprintExposition.md`
entry when it earns a detailed exposition) and the section here shrinks to a
pointer.

**Discipline.**

- Each section reads as the **current state of the argument**, revised in
  place. Git is the changelog; do not keep superseded reasoning inline (the
  `notes/CLAUDE.md` rule for phase notes applies here too).
- Each section carries an explicit **confidence verdict**, one of:
  *proven-informally* / *true-modulo-named-gap* / *open* / *refuted*, plus a
  **"what would change this"** line naming the observation that would move
  the verdict.
- Landed Lean facts are cited by declaration name; claims that are *not*
  landed are flagged as such at the point of use. `PencilNondegFeasible` has
  no combinatorial characterization — whenever an argument needs a
  feasibility fact, say whether it is landed-**sufficient**
  (`hcard ∧ triangle-free`, L6b; the spanning-`C₃` witness, L7c-3),
  landed-**necessary** (`hcard`; no-2-hub-triangle), or **middle zone**
  (undecided by landed lemmas).

- **Labels are registered, not invented.** Before minting any label, read
  `notes/Pencil-labels.md` and follow its four-clause rule: grep the registry
  for the token, never write a bare parenthesized token for a *Step*, qualify
  every cross-section citation with its owner (`§(K-slide-comb) (C6)`), and do
  not rename existing labels. Add your row in the same commit that mints the
  label. That file also carries the reserved namespaces for in-flight parallel
  dispatches.

**Recon verdict history lives elsewhere.** The dated recon record — what was
asked, what method was used, what was refuted — is
`notes/Phase39-design.md`; the one-line decisions are `notes/Phase39.md`
*Decisions made*. This file carries only the mathematics, in its current
state.

## Section index — navigation

**Navigation only.** The *State of (K)* map below is and remains the single
mathematical entry point; this table exists so that a dispatch can load the two
or three sections it needs rather than the whole file. Line ranges are **as of
this commit** — if one looks wrong, grep the `## §(…)` heading, which is the
durable anchor. The *tag* column is the section's prefix for **new** labels
(`notes/Pencil-labels.md` clause L1); statuses are one-word pointers to the
section's own verdict block and the gap-map row, which stay authoritative.

| § | lines | status (owner: the section's verdict block) | tag |
|---|---|---|---|
| *Shared dictionary* + test shapes `W19`/`S29` | 88–166 | serves **both** workbooks | `SD-` |
| ***State of (K)* — the gap map** | 167–309 | **the entry point; a pass updates it in place** | — |
| §(K-tight) | 310–569 | criterion proven-informally; **(K-tight) open — the phase's hardest item** | `KT-` |
| §(K-pitch) | 570–1003 | (T1)–(T5) proven-informally; closed at `ℓ = 3`; uniform form open | `PT-` |
| §(K-slide) | 1004–1295 | (S1) proven-informally; settled per member | `SL-` |
| §(K-slide-cl) | 1296–1587 | reduction proven; **refuted as stated**; the `∃Σ` form open | `SC-` |
| §(K-slide-comb) | 1588–1939 | **refuted as a class statement**; (C6)/(C7) proven-informally | `SB-` |
| §(K-flank) | 1940–2492 | per shape, not a uniform gap; half 2 proven-informally | `FL-` |
| §(K-pure) | 2493–3048 | direction C **refuted**; (PC-Z)/(PC-OBS) proven-informally; **(K-chord)** the successor | `PC-` |
| §(K-Λ) | 3049–3970 | **refuted as an independent gap**; (Λ1) an identity; **(OUT)** lives here | `Λ` |
| §(K-dom) | 3971–4364 | dominance holds at every probed habitat; **C1 not a route** | `DM-` |
| §(K-σ) | 4365–5040 | **route σ a CANDIDATE, `ℝ`-only** — the one live candidate | `σ` |
| §(K-ind) | 5041–5386 | **refuted as a route** | `IN-` |
| §(K-Δ) | 5387–5653 | **NO HIT — the lead is discharged** | `DL-` |
| §(K-bare-ext) | 5654–5692 | open, nothing being developed | `BE-` |

**Live vs settled**, using the division of the 2026-08-05 reorganization pass.
Live: §(K-tight), §(K-Λ), §(K-σ), §(K-pure), and **(K-wit)** (owned jointly by
§(K-pitch) *Step 3* and §(K-Λ) *Steps 3–6*). Settled or refuted, so **do not
re-derive**: §(K-slide-comb), §(K-Δ), §(K-ind), §(K-slide-cl) as stated, and
§(K-dom)'s C1 verdict. The gap map's *Settled, so not to be re-derived* blocks
are authoritative for the per-item detail.

## Shared dictionary (used by every section of both workbooks)

Body-hinge at `d = 3`: `D = bodyBarDim 3 = 6`, hinge multiplicity `5`.
For a graph `H`,

```
def(H) = max over partitions P of V(H) of [ 6(|P| − 1) − 5·d(P) ]
```

(`Molecular/Deficiency.lean`), `d(P)` = number of edges crossing `P`; `H` is
**rigid** (`H.IsKDof 3 0`) iff `def(H) = 0` iff `5H` packs 6 edge-disjoint
spanning trees (Tay; `thm:body-hinge-tay`). Writing `f(W) = 5|E(W)| −
6(|W| − 1)` for a vertex set `W`, one has `def(H) = 6(|V|−1) − 5|E| +
max { Σ_parts f(part) }`, so `def(H) = 0` forces `f(V(H)) ≥ 0`.

Consequences used throughout (all elementary, all numerically re-checked in
`notes/scripts/w4/nogood_subdiv.py --validate`):

- **(R1) min degree.** A rigid `H` with `2 ≤ |V(H)|` has `deg_H(v) ≥ 2`
  everywhere and is connected (`{v}`-vs-rest gives `6 − 5·deg ≥ 1 > 0`;
  components give `6(p−1) > 0`). Landed as
  `two_le_degree_of_isKDof_zero` (`Deficiency.lean:1306`).
- **(R2) size bound.** A rigid `H` with cycle rank `c = |E| − |V| + 1`
  satisfies `|V(H)| ≤ 5c + 1`, and has at most `2c − 2` vertices of
  `H`-degree `≥ 3`.
- **(R3) short cycles.** `def(C_k) = max(0, k − 6)`: `C_k` is rigid iff
  `k ≤ 6` (the classical 6R-loop count). `C₃` and `C₄` are landed
  (`isKDof_zero_of_triangle`, `c4_isProperRigidSubgraph`).
- **(R4) `hcard` restated.** `PencilNondegFeasible K G` gives `∀ v ∈ V(G),
  (G.closedHubNbhd v).ncard ≤ 3` (`ncard_closedHubNbhd_le_three_of_
  isNondegPencilRealization`). At a **non**-hub the bound is automatic
  (`closedHubNbhd v ⊆ N(v)`, of size `≤ 2`), so `hcard` says exactly:
  **every hub has at most two hub neighbours** — the subgraph induced on
  `{v : deg v ≥ 3}` has maximum degree `≤ 2`. Hence a `2`-edge-connected
  feasible `G` is a **subdivision** of a multigraph `G°` on its hubs (or a
  bare cycle), and hub-hub adjacency is confined to paths/cycles.
- **(R5) feasible triangles are pendant.** `not_pencilNondegFeasible_of_
  triangle_two_hubs` says a triangle of a feasible `G` has `≤ 1` hub, so
  two of its vertices have degree exactly `2`: every triangle is either the
  spanning `C₃` or a two-vertex ear hanging at one vertex.

### Test shapes `W19` and `S29` (canonical definitions)

Two explicit graphs recur as **test shapes** across both workbooks. They were
built as the W4 residual arc's counterexamples — their certification, their
role there, and their robustness/minimality records are
`notes/Pencil-W4-informal.md` §`hnoGood'` vacuity *Step 3* and §(SAFE-RES)
*Step 2* — and the (K) sections below reuse them as residual-habitat probes
(they are the (K-res) habitat's two named members). **This is their canonical
definition; neither workbook redefines them.**

**`W19`** — `|V| = 19`, `|E| = 22`, `f(V) = 2`, `def = 0`;
`notes/scripts/w4/nogood_subdiv.py --witness` builds it.

```
core       C₄ :  c0 – c1 – c2 – c3 – c0
poles      z0, z1 attached to c0 ;  z2 attached to c2
paths      z0 –w0_0 w0_1 w0_2 w0_3– z1
           z1 –w1_0 w1_1 w1_2 w1_3– z2
           z2 –w2_0 w2_1 w2_2 w2_3– z0
```

Degrees `c0 ↦ 4`, `c2 ↦ 3`, `z0,z1,z2 ↦ 3`, all others `2`. Hubs:
`{c0, c2, z0, z1, z2}`. Its only proper rigid subgraph is the core `C₄`.

**`S29`** — `|V| = 29`, `|E| = 34`, `f(V) = 2`, `def = 0`;
`notes/scripts/w4/saferes.py --witness` builds it.

```
core    C₄ :  A – m1 – B – m2 – A            (A deg 4, B deg 3)
poles   hub edges  A–z0,  A–z1,  B–z2
ring    z0 – y0 – z1 – y1 – z2 – y2 – z0,  every leg 2-subdivided
spokes  y0–p, y1–p, y2–p,                  every spoke 2-subdivided
```

Hubs (9): `A, B, z0, z1, z2, y0, y1, y2, p`; every one of the 14 branches
carries `0`, `1` or `2` interior vertices. Its only proper rigid subgraph is
the core `C₄`.

## State of (K) — the gap map

**What this is.** The current state of the kernel-(K) arc, one row per named
gap, each row derived from that section's own *Verdict* / *Confidence verdict*
block. Nothing here is stated more strongly than its section states it, and a
conditional verdict names what it is conditional on. **This map is the artifact
a new pass updates** — edit these rows (together with the section's own verdict)
rather than writing a fresh summary of the arc beside it.

The arc in one paragraph. `hK` is the escape `≢ 0` uniformity kernel of the
split arm; the corank stratification (recon of 2026-07-30, `notes/Phase39.md`
*Hand-off*) discharges the `index(G) ≥ 1` habitats and leaves **(K-tight)** —
tight, both chain ends hubs, 2-connected, hard stratum `dim R_a = 1` — which
since the W4 route-3(b) adjudication also carries the whole **(K-res)**
residual habitat (statement: `notes/Pencil-W4-informal.md` §"widened kernels
(routes 1/3)" *Step 4*; same difficulty class, same stratum, so one uniform
gap serves both). The escape *criterion* on that stratum is settled; what is
open is making some good seed exist **uniformly over the class**, and every
route below is an attack on that one thing.

Sections cited by name + step number (`(K-tight) 0–3` = §(K-tight) Steps 0–3),
all in this file.

| gap | § + steps | status | what would close it |
|---|---|---|---|
| escape criterion | (K-tight) 0–3 | **proven-informally** (attainment ⟺ two `U`-functionals independent; combined failure ⟺ `★r ∥ C(M)`); 80/80 per-placement | — settled; not a gap |
| **(K-tight)** | (K-tight) 5; (K-σ) | **open**, true with strong evidence; no genuine escape failure anywhere in the corrected numerics **on the hard stratum `dim R_a = 1`** (and above it) — the claim is **false without that qualifier**: §(K-flank) F5(d) exhibits 5 legal nondegenerate target-rank `G′` seeds at `P21` with `s₀ = 1`, `dim R_a = 0`, `dim U = 1`, which the Step-2.3 calculus *proves* fail at every placement (8/8 observed each); `hK`'s ∃-form is untouched (30/35 escape). **A CANDIDATE closure now exists and this row does NOT move on it**: §(K-σ)'s **route σ** (route A run at the dual seed `σu`) would close the hard stratum *length-free* via the 6-dimensional span `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶` (or its `c`-mirror — the side condition is **free** by (σ7)), but it rests on four named obligations, the first of which — σ-nondegeneracy of the transported seed — is **NOT implied**: 53 constructed hard-stratum, primally-nondegenerate seeds violate the dual conjuncts (`sigma.py --hunt`, 2026-08-05), so the earlier "observed 63/63" was genericity. Two of the four conjuncts are free **at `ℝ`** (1 by the landed `hasPencilPanelRealization_mapExtensor_screwComplementIso`, 3 by the primal conjuncts when no two hubs are adjacent) and the steering repair is exhibited exactly on a chart line. **FIELD-SCOPE CAVEAT (2026-08-05, recorded not settled):** route σ is an `ℝ`-only construction — `screwComplementIso` is `ScrewSpace ℝ 2 ≃ₗ[ℝ] ScrewSpace ℝ 2` — aimed at an `hK` quantified at general `[Infinite K]`, so this candidate closes the row only at `ℝ` unless the polarity generalizes (§(K-σ) *Field scope*) | (K-move), (K-pitch), **or** discharging §(K-σ) *Step σ5* obligation 1 — the named repair is `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`), whose remaining design decisions are **which maximal minor** to fix per LI conjunct (they are unions of basic opens, not single hypersurface complements) **and at which field** (`ℝ`, instantiating the headline first, or general `K`, which needs a general-`K` polarity). **`exists_pencilSeed_of_nondeg` is NOT the bridge** — it takes obligation 1 as a hypothesis |
| **(K-move)** | (K-tight) 5 | **open — the sharpest gap** on the stress side; N8 refutes block-determined `[r]` at both probed families | `[r]`-as-chart-rational-function infrastructure (option B, **not** commissioned) |
| **(K-pitch)** | (K-pitch); (K-pure) P3; (K-Λ) | (T1)–(T5) **proven-informally**; **closed** at length-3-companion splits (bracket monomial, θ(3,3,6)); uniform form **open**. Step 2's (F-A)/(F-B) dichotomy is **upgraded to the algebraic form (PC-Z)** (§(K-pure), proven-informally): `Q(z) = 0 ⟺ V_bc` meets `α(a)` or `Λ²π̂`, the only two maximal totally isotropic 3-spaces containing `T` — the exact target of any future non-vanishing argument (its *reason* is Witt's theorem — §(K-Λ) *Step 1*). The `ℓ = 3` verdict is unchanged but now has a **two-line proof that *explains* its five brackets**: they are the coordinate form of `S ∩ α_a = S ∩ β_{π_a} = 0` (§(K-Λ) *Step 1*(i)). The bracket **closed form extends from `ℓ = 3` to `ℓ = 4`**, as a **product of two bracket-linear forms in the far covector** ((Λ1), since 2026-08-05 a **symbolic identity over the function field** — `M2 --script notes/scripts/m2/lambda1.m2`) — a positive standalone result, but **not** a non-vanishing theorem: its zero locus is nonempty exactly at the two structurally meaningful configurations | one seed with `Q(z) ≠ 0` per (graph, split), uniformly — by (PC-Z), one seed where `V_bc` misses **both** isotropic 3-spaces |
| **(K-wit)** | (K-pitch) 3; (K-Λ) 3–6 | **open**; the weakest exact form — per habitat+split *equivalent* to the escape at a good seed — and now the **single live form of the pitch route at companion splits**: it inherits (K-Λ)'s status and gains a *necessary-and-sufficient* companion form (§(K-Λ) *Theorem (Λ-completeness at length-4 companions)*: the escape holds at some target-rank seed **iff** the pitch certificate is nonzero at some target-rank seed). The **two-point failure locus is this row's content** — `{V_bc ⊥_B C(M)}` (the failure itself) and `{V_bc ⊥_B C(bc)}` (route A escapes, `★r ∝ C(bc)`); since 2026-08-05 those two points are known to be **exactly a σ-orbit** (§(K-σ) (σ5)), so the recorded asymmetry between their consequences is a *one-frame artifact*, not a broken symmetry — and if §(K-σ)'s candidate route σ stands, this row's trichotomy loses its failure branch and (K-wit) leaves the escape's critical path. Two load-bearing side conditions are newly **named**, neither present in the prior formulation: **(Λ0d)** panel non-incidence in **both** directions (`pt(c) ∉ Π(b)` *and* `pt(b) ∉ Π(c)`; witness θ(3,4,5) seed 345, where `span_t ω⁻` collapses `3 → 1`) and **(Λ0f)**, now **PROVEN at the generic point and WIDER than first stated** (2026-08-05, `m2/lambda0.m2`): the exact criterion is **(Λ0f′)** `span_t ω⁺ = 3 ⟺ p⁺₂p⁺₃·g₁₃g₁₄g₂₄ ≠ 0` (and `q₂q₃·g₁₃g₁₄g₂₄ ≠ 0` for `ω⁻`), where `g₁₃g₂₄ ≠ 0` is `rank Q|_S = 4` and **`g₁₄ = [b,x₁,x₃,c] ≠ 0` was asserted nowhere** — the two outer companion lines must not meet. Since 2026-08-05 (§(K-Λ) *Step 3a*, `outer.py`) that clause is **located, not merely named**: geometrically it says the two marked points `C₁ ∩ M`, `C₄ ∩ M` of the meet line coincide **(Λ0g)**; wherever a companion end is free it is **implied by (Λ0d)** **(Λ0i)** (3628/4280 swept pairs); **no class habitat in scope forces it** (`g₁₄ ≠ 0` at 4280/4280 exact pairs over 1357 class shapes, `d g₁₄ ≠ 0` at 684/684 chart points), so **Λ-completeness stands as written**; but it *is* reachable at a target-rank `dim R_a = 1` seed of all four habitats by an explicit chart move, both spans dropping `3 → 2`, so the clause is load-bearing. Residual: class shapes with **two or more hubs on the companion interior**, which no swept family realizes. **New 2026-08-05, a sufficient condition rather than a status change:** since `p⁺` and `q` both have their *outer* entries vanishing structurally, the whole (Λ2) bad set lies on the single line `{λ₁ = λ₄ = 0}` of `P(S*)`, so **(OUT)** (§(K-Λ) *Step 5a*) — *either outer companion line not a relative twist* — already forces the escape by pitch at `k = 4`; it is conditional on (Λ0) in full and its hypothesis is **unmeasured** | one `H`-motion pairing non-trivially with `C(M)`, uniformly — **or, at length-4 companions only, the strictly cheaper (OUT)**: `C₁ = C(b x₁) ∉ V_bc` or `C₄ = C(x₃ c) ∉ V_bc`, a far-side, panel-free, `a`-free condition (§(K-Λ) *Step 5a*; conditional on (Λ0d) + the widened (Λ0f′), sufficient and never necessary, and a rank *lower* bound so §2.3's asymmetry is relocated, not evaded) |
| **(K-pitch-∞)** | (K-pitch) 4 | **open**; sufficient for (K-pitch) at a split; all five quartic coefficients nonzero at 4/4 habitats | `Q(z_∞) ≢ 0` on the `a`-free chart |
| **(K-Λ)** | (K-Λ) 1–6; (K-pitch) 5b | **REFUTED as an independent gap** (§(K-Λ), fan-out direction B): at a length-4-companion split it is *equivalent* to **(K-wit)** (Steps 3–5), so **closing (K-Λ) *is* closing (K-wit)** and no local argument can close it. `Φ_loc`'s non-degeneracy is **PROVEN, class-uniformly** — `Φ_loc` is always a **rank-2** form, the product of two distinct rational linear forms ((Λ1), an **identity over the function field** since 2026-08-05: `m2/lambda1.m2`, the harness's first Macaulay2 driver; it needs none of (Λ0) and none of the panel data) — so the previously-flagged "`Φ_loc ≡ 0`" degeneration is **impossible** and the "local quadric" is a pair of rational hyperplanes. Using (T4)'s `a`-line freedom, the far covectors bad for the whole line shrink to **two points**, with failure locus `{V_bc ⊥_B C(M)}` (= the genuine (T3) failure) and `{V_bc ⊥_B C(bc)}` (= route A escapes outright, `★r ∝ C(bc)`). Its exemplar θ(3,4,5) is separately closed by a reduced-support slide witness (§(K-pure) P7) | — refuted as an independent gap; the live form is **(K-wit)** (row above) |
| **(K-slide)/(S1)** | (K-slide) 1–4 | **(S1) proven-informally**; per-member (K-slide) **witness-decidable and discharged at every probed member** (23/23, 7 members, 11 split-classes) — `K4`/`W4` control habitats closed at **every** split. Status unchanged by the sixth pass, but (S1) **remark (iii)'s support freedom is promoted from a proof convenience to *the* load-bearing parameter**: `E_chord(Σ)` shrinks with `Σ`, so the support choice alone decides whether the limit is pitched (§(K-pure) P1/P7) | — settled per member; the class form is (K-slide-cl) |
| **(K-slide-cl)** | (K-slide-cl), (K-slide-comb), (K-pure) | **REFUTED as stated** (§(K-pure), at the full support): the chord obstruction **(PC-OBS)** kills (W4) — or (W3) — at *every* decoration of three `K5` class shapes and of θ(3,4,5). This is a **statement**-level refutation by `R_3`-dependence, a **different mechanism** from (K-slide-comb)'s antecedent-level colouring refutation below — do not conflate them. The **repaired** statement quantifies `∃Σ` over slide supports and in that form is **open**. The **covered sub-class grows**: the collapse-solvable shapes (all 7 battery members) *plus* the three `K5` 5-chromatic shapes, `K222` and θ(3,4,5), which now carry **reduced-support** (S1) witnesses | for the `∃Σ` form: **(K-chord)** below, plus a mechanism for the residual (W2)/(W4) failures. The "generic pure condition of the limit system instead of the collapse" route is itself **REFUTED** (§(K-pure) P0/P5: that condition sees only (W1) ∧ (W2)) |
| **(K-slide-comb)** | (K-slide-comb) | **REFUTED as a class statement** (two structural flanks at explicit class members satisfying `hcard`/`htf`); per shape still a finite certificate-bearing problem, and "(K-slide-comb) at a shape ⟹ (K-slide-cl) there" stays **proven** | — refuted; the needed invariant is **acyclic** 4-colourability, which 3-degeneracy does *not* give |
| **(C6)** | (K-slide-comb) D1 | **proven-informally at every class shape** — the unrestricted 6-fold base packing exists because Edmonds' matroid-partition min-max hypothesis for it *is* 5/6-sparsity; so the packing content is never the obstruction (and is Phase-12/13/14-reachable). **Status unchanged, role downgraded** (§(K-pure) P2/P6): it certifies the *ambient* hypothesis of a theorem that does **not** transfer to the decoration variety, and it is about the 6-fold **graphic union** — the wrong matroid for the pitch, which `R_3`-dependence governs | — settled; only a non-tight shape could break it |
| **(C7)** | (K-slide-comb) D4 | **proven-informally combinatorially** (the length-4 menu is *all* five 2-subsets containing `L_ij`; 12/12 exact; `K4` coverage 439 → 702/877, octahedron flank rescued); two honest gaps — no full (W1)–(W4) witness at a repaired member, and `ℓ ∈ {1,2,5}` open (at `ℓ = 5` the mandatory-`L_ij` claim is itself suspect) | a geometric witness at a repaired member + the `ℓ ∈ {1,2,5}` analogues; cannot touch either structural flank |
| **(K-chord)** *(new, 2026-08-05)* | (K-pure) P1–P4, P9 | **open**, and the *replacement* combinatorial residue: `∃Σ` with `e₀ ∉ cl_{R_3}(E_chord(Σ))` at generic hub points — **necessary** for the slide device by (PC-OBS). Per shape it is checkable by **exact rank** — done exhaustively over the 23 candidate hub graphs with `|V°| ≤ 6` (`R_3`-dependence ⟺ Maxwell-overbraced; 5 dependent, 18 independent; smallest `K5`) — but unlike (K-slide-comb) it lives in a matroid with **no combinatorial characterisation** (generic 3-dimensional rigidity), so a class argument has nothing to reduce to | a support menu wide enough to satisfy it *together with* (W1)–(W4) at every class shape (P9 item 5: widen the 5-support menu, sweep the `|V°| ≤ 6` strata, 6v11e first) — or a class shape satisfying it at **no** support, which would refute the device class-wide |
| `P21` / parallel `G°` edges | (K-slide) 5, (K-flank) F5, (K-pure) P4/P7 | **mechanism corrected and scope sharpened** (§(K-pure)): at a *class* parallel shape the full-support obstruction is the **chord stress at (W4)**, not (S5) at (W1), and it needs only a `bc`-parallel edge of length `≤ 4`. (S5)'s `(3,3)` row-dependence mechanism is **proven impossible inside tight + `hnoRigid`** (`C_k` rigid for `k ≤ 6` forces `ℓ₁ + ℓ₂ ≥ 7`), so **`P21` is a (K-res) residual, not a tight class member**. `P21`'s own obstruction is unchanged and is **not confined to the `ε = 0` limit** — §(K-flank) F5(d)/(e) exhibits the same theta-circuit stress (`{12, 13, 23a, 23b}`, 12 edges, line rank 6) on a **nonempty locus of the pencil chart itself** (5 of 35 rational seeds), where it forces `dim R_a = 0`. **θ(3,4,5) is CLOSED** by a reduced support, without (K-Λ) | for `bc`-parallel class shapes: a reduced support (done at θ(3,4,5)) or the companion forms — the monomial at `ℓ = 3`, and at `ℓ = 4` **(K-wit)**, since §(K-Λ) shows the companion form there is *equivalent* to it rather than an independent gap. At `ℓ = 5,6` **the (T5) frame is REFUTED as the route** (§(K-Λ) *Step 7*: at `k ≥ 5` the (F-A) bad locus gains a second, equal-dimensional component — a smooth conic, so nonempty over `K̄` — and at `k = 6` `C(M) ∈ S` removes even the local guard), so those shapes need **something else, none identified** (this refutes the *argument shape*, not the conjecture and not their closability; whether a *rational* point of that component is realized by a real habitat is open). For `P21`-type (K-res) shapes: a new `G°`-local mechanism — none identified |
| **(K-flank)** | (K-flank) F0–F7 | **per shape, not a uniform gap: half 2 proven-informally** by exact `∃`-witnesses at the Tay target (8 named + 843 stratum shapes, 0 failures); half 1 carries **no `hK` counterexample and no re-pin** (16/16 `e₀`-end splits, 26/26 eligible splits of the 5-chromatic flank, both KT routes); **(K-pitch) closed at all 16 flank splits** by `ε = 1` certificates; the full-support slide limit is **degenerate at all four structural flanks**; **class uniformity untouched** | — n/a: a per-shape result, not a gap. *Settled per shape; the uniform statement is unchanged* (the disproof risk is removed, no uniform gap moves) |
| **(K-dom)** *(new, 2026-08-05)* | (K-dom) D0–D7 | **open as the uniform statement, and provably FALSE off the class**, so the strategy doc's §4-C1 route is **not recommended**. Writing `k` for the *companion length* (the shortest `b`–`c` path of `H`; `k ≥ 3`): **(D1)** `rank d(H ↦ V_bc) ≤ min(9, 6k − 14)` in the bad-locus-frozen scoping, **proven** from path-sum containment — so `≤ 4` at `k = 3`, where `V_bc` is moreover always in the discriminant hypersurface of `Gr(3,6)`; **(D2)** the far block is `≤ 3(k−3)` (a corollary of (T5)), **attained** at `0,3,6,9` for `k = 3,4,5,6`; **(D3)** `hnoRigid` forces `k ≥ 4` (= §(K-slide) *Step 5*'s `ℓ₁+ℓ₂ ≥ 7`), so the cap bites exactly on **(K-res)**. Measured: rank **9 — dominance — at all 5 probed class habitats** (θ(3,4,5), NT21, NT16k5, `K4`/`K5−M` dbl-subdiv; `k ∈ {4,5,6}`) and exactly **4** at both `k = 3` habitats. **(D4)**: rank 9 at one rational seed ⟹ the escape on a *dense open* subset of that shape's chart — a strictly stronger per-shape statement than an `∃`-witness, and no more useful. §4-C1's two claimed values are **REFUTED** (D6): the image does **not** grow with the far graph (it is capped by the local `k`), and the 2026-07-30 locality gate was run at `k = 6`, the *maximal* far-dependence grade, so it is not evidence for dominance. **Class uniformity untouched** — "rank 9 at every class shape" is one determinantal condition per (shape, split), the same per-shape object §(K-pure) *P5* names as the wall | a class habitat with `rank dV < 9` at every seed (a sharp new obstruction; none found), **or** a mechanism making `rank dV = 9` combinatorially certifiable class-wide — the only thing that would turn C1 into a uniform route |
| **(K-σ)** *(new, 2026-08-05)* | (K-σ) *Field scope*, σ0–σ6, σ4b | **four settled verdicts + one CANDIDATE, offered for adjudication — all under a FIELD-SCOPE caveat.** `σ = screwComplementIso` exists in tree **only over `ℝ`** (`Duality.lean:69`), and so does the self-duality theorem the conjunct-1 freeness cites (`Statement.lean:257`), while **`hK` is quantified at the general `[Infinite K]`** of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Escape.lean:555`). Whether the polarity generalizes is **OPEN and not attempted** — encouraging, since `complementIso` and `ScrewSpace.equivExteriorPower` are already general-`K` in tree, but unproven. **(σ7) needs no polarity and is field-neutral outright**; (σ1)–(σ6) and route σ are field-neutral *modulo the polarity existing*; the two refutations below use `ℝ`-**definiteness** and do **not** port. Settled: the σ-intertwining question is **REFUTED in its literal form** (`pt(a) ∈ π_a` forces `pt(a)·pt(a) = 0`, impossible over ℝ with the project's *definite* polarity — `Molecular/Meet.lean:88` records it is the Hodge star of the standard dot product) and **CONFIRMED covariantly** (`σ(α_p) = β_{p^⊥}`, `σ(β_π) = α_{pole(π)}`), which makes §(K-Λ)'s two-point failure locus **exactly a σ-orbit**; and **σ-equivariant seed recipes are DEAD** — no σ-fixed pencil configuration exists over ℝ, and a null polarity puts every hinge line in a linear line complex, giving a self-stress per cycle (**deficit exactly 1 at 6/6** on tight `C₆`). Fourth settled verdict, **new 2026-08-05** (`sigma.py --hunt`, three pools of its own, disjoint from the 63): **(σ7)** *Step σ3*'s side condition `pt(b) ∉ Π(c)` is **FREE** — primal conjunct 4 at the split's middle body `a` forbids both halves of (Λ0d) from failing at once (39/39 witnesses that forcing both leaves `a` with no panel), settling *What would change this* (iv); **and, in the other direction, the dual conjuncts at `σu` are NOT implied** — 53 constructed hard-stratum, primally-nondegenerate seeds violate dual conjuncts 2 and 4 (coplanar-chain degeneration), so *Step σ4*'s 63/63 was genericity. Candidate: **route σ**, whose uniform-failure criterion `★r ∥ C(bc)` is the σ-image of routes A/B's `★r ∥ C(M)` and cannot hold simultaneously with it. Scope of the validation: `s₀ = 0`, `dim R_a = 1`, both ends hubs, tight control only (the hunt pools widen the *configurations*, not the shape) — `dim R_a = 0` **untouched**, (K-res) `s₀ = 2` **unsampled**; the criterion at `σu` is **imported, not re-derived**, and its failure direction is **unwitnessed** (`predAfalse = 0/63`); and the branch route σ closes has **never been observed nonempty**, so the gain is **evidence → argument**, never *bug fixed*. **No gap-map status moves on account of route σ** | obligation 1 of §(K-σ) *Step σ5* — now **sized, not just named** (all of it **at `ℝ`** — see the caveat opposite): conjunct 1 free by a landed theorem, conjunct 3 free by the primal conjuncts on no-adjacent-hub shapes, conjunct 2 at the two `a`-edges = two-sided (Λ0d), leaving two genuinely new conditions with a steering repair exhibited exactly (`bracket(τ) = τ·bracket(1)`). Route σ faces exactly **one** crux: the workbook's two kills of M₁ (§(K-tight) *Step 1* and *Step 2.6*) have the **same** stated reason, the `hinge(vb) := q(ab)` pinning |
| **(K-ind)** *(new, 2026-08-05)* | (K-ind) I0–I6 | **REFUTED as a route**, and not merely "no invariant found": the transport structure the question presupposes does not exist on the `hK` habitat. **(I1)** tight ⟺ `(|V|,|E|) = (5c+1, 6c)`, so two tight graphs of equal cycle rank have equal size and **no arm of `pencil_reduction` can relate them**; **(I2)** `splitOff` at a degree-2 vertex takes `index 0 → 1` preserving `c` and fixing the hub multigraph `G°`; **(I4)** inside one `G°` the class is a **finite antichain**, and the class's infinitude is entirely in the `G°` direction, which no move reaches. **(I0)**: the failure locus is a **divisor**, so its only numerical invariant is the single bit `codim F = 1`, which *is* `hK` — the question as posed is circular, and the image-side reading is (K-dom), already struck. One genuine positive by-product: **(I3)**, subdivision-monotonicity of `Image(V_bc)` — real, new, *and pointing the wrong way*, since the induction descends and every descent bottoms out at `k ≤ 3` where (D1) caps the rank at 4 | — refuted as a route. Any future "strengthen the inductive invariant" proposal must first exhibit a move relating two class members; `pencil_reduction`'s five arms supply none |
| **(K-Δ)** *(new, 2026-08-05)* | (K-Δ) | **NO HIT — the literature lead is discharged**, not open. Two independently fatal hypothesis failures: **(M1)** the subject's objects are *totally isotropic* subspaces and `V_bc` never is (Klein Gram rank 3, or 2 on serial chains — an `O(6)`-invariant, not a frame choice), so it has no Wick vector and carries no Δ-matroid; **(M3)** the ground set is `[3]`, fixed by `dim Λ²K⁴ = 6`, and never grows with the graph — `Pencil-strategy.md` §2.2's ingredient-2 failure in the target literature's own terms. Recorded as a *pass*: the **form** matches exactly (transversality to two coordinate isotropics = two Wick coordinates nonzero). Buys two readings, not a route: **(N1)** the `ℓ = 3` criterion as five feasible pairs in the Dress–Havel metroid of the five lines, and **(N2)** the **pentagon** reading — `Q(z) ≠ 0` ⟺ no two non-consecutive edges of the closed chain `b–x–y–c–a–b` meet | — discharged. `Pencil-strategy.md` §7's "one unverified lead" is now a checked negative with the reason |
| **(K-bare)/(K-bare-ext)** | (K-bare-ext) | **open**, nothing being developed; `hbareSplit` carried as pinned, off W4 routes 1/3's path; the (K-tight) re-pin fixes the criterion's shape and corrects "the failure set is exactly the line" to `line(a,b) ∪ P′` | (i) `dim R_a ≥ 1` at an adversarial IH seed and (ii) a rank-2 point in the confinement space — with no chart supplying genericity for either |

**Shapes no *class-uniform* mechanism covers** (the class program's uncovered
flanks, all from §(K-slide-comb) *Step D5* + §(K-slide) *Step 5*): `χ(G°) ≥ 5` —
exactly `K5` or `Δ(G°) ≥ 5` by Brooks, since four hub positions cap the
collapse; hub graphs with no **acyclic** 4-colouring; shapes where the (pure)
menu is unsolvable even though the colouring premise holds (438 of the 877
exhaustive `K4` shapes, of which (C7) rescues enough to reach 702/877);
non-`bc`-parallel `G°`-edges with no length-`≤ 4` `bc`-companion (`P21`); and
the (K-res) length-6 flank, unprobed.

Every one of them is now **individually discharged** (§(K-flank)): half 2 by an
exact nondegenerate witness at the Tay target — 8 named shapes plus 843 in whole
strata, including the exhaustive 438 menu-blocked `K4` shapes — and (K-pitch) by
an `ε = 1` certificate at every probed split (16/16). What they lack is a
class-uniform *mechanism*, not a certificate; three of them (the two wheels and
one menu-blocked `K4` shape) even reach the `G°`-level carrier and join the
§(K-slide) *Step 4* battery. The (K-res) length-6 flank remains the one
**unprobed** entry (§(K-flank) F7 item 3).

**And every *probed* one now has its split closed** (§(K-pure), direction C):
the three obstructed `K5` all-`{3,4}` shapes by a **reduced** slide support, the
two `K5` shapes carrying an `ℓ = 5` edge at the **full** support, `K222` and
θ(3,4,5) by a reduced support, and **6v11e by its chart certificate only** (the
slide *device* fails there at every probed nonempty support). So what remains
uncovered is no longer a *shape* list: it is the **class-uniform** statement,
plus **two unexplained mechanisms** — 6v11e's `dim V_bc = 2` drop and the
`V_bc ∩ Λ²π̂ ≠ 0` incidence at `K222` / `K4 (1,1,3,5,4,4)` (§(K-pure) P8).

**Settled, so not to be re-derived:** the carrier escape criterion and the
`dim U = dim R_a + 1` structure ((K-tight) 0–3); routes 1 and 2 of the original
(K) pin, **REFUTED** by the locality gate — and now *graded*: (K-dom) (D2) shows
far-dependence of `V_bc` is `3(k−3)`, zero at `k = 3` and maximal at the `k = 6`
shapes the gate was run on; the naive collinear collapse,
**REFUTED** as a chart move ((K-pitch) 6a); the (T1)–(T5) motion-side transfer;
(S1) and its (S2) carrier; (C6); the **companion length** `k` as the arc's
organizing local invariant — `k ≥ 4` on the class, `k = 3` exactly on the
(K-res) `C₆` residuals ((K-dom) (D3)); **(Λ0)** and the `a`-line spans, proven at
the **generic point** of the local frame and **class-uniform** ((K-Λ) *Standing
notation* + 3, `m2/lambda0.m2`) — do not re-sample them, but note the criterion
is the widened **(Λ0f′)**, not the recorded (Λ0f); the **`g₁₄` clause** of
(Λ0f′), settled as *not forced by any class habitat in scope* and *implied by
(Λ0d) at a free companion end* ((K-Λ) *Step 3a*, `outer.py`) — do not re-sweep
it; the open residual is the two-hub-interior companion pattern, item (vii);
and **(Λ1)**, now a **symbolic
identity over the function field** ((K-Λ) 2, `m2/lambda1.m2`) rather than 23 frames —
`Φ_loc` factors into two bracket-linear forms at *every* length-4-companion
frame, with no (Λ0) and no panel hypothesis, so nothing about `Φ_loc`'s shape
or rank needs re-deriving or re-sampling. Every recorded escape *failure* in the
phase's numerics was a placement-sampler artifact ((K-tight) 3).

**Settled 2026-08-05, second batch — also not to be re-derived.**

- **The polarity's action** ((K-σ) σ0–σ1): `σ` = the Hodge star, `σ² = id`, a
  `B`-isometry, `σ(α_p) = β_{p^⊥}`; on a realization it **replaces every body's
  point by its own panel normal**. The **literal** intertwining question is
  refuted, the **covariant** one confirmed, and the two-point failure locus is a
  σ-orbit. **σ-equivariant seed recipes are dead** with a proof — do not
  re-attempt a symmetric-configuration construction.
- **The field scope of §(K-σ) is RECORDED, not settled** ((K-σ) *Field scope*,
  2026-08-05): `σ` and the four polarity theorems are `ℝ`-only in tree while
  `hK` is consumed at general `[Infinite K]`; (σ7) is field-neutral, (σ1)–(σ6)
  and route σ port *if* the polarity does, and *Step σ1(a)*/*Step σ6*'s two
  refutations use `ℝ`-definiteness and do **not** port. Do not re-derive the
  signature census; **do** treat "does the polarity generalize?" as open.
- **The obligation-1 hunt is DONE, in both directions** ((K-σ) σ3/σ4b,
  `sigma.py --hunt`; three pools of its own): the dual conjuncts at `σu` are
  **not implied** by the primal ones (53 constructed hard-stratum,
  primally-nondegenerate counterexamples — the coplanar-chain degeneration), so
  no future pass should read a `n/n` dual-conjunct census as an implication;
  **random** search cannot find them (0 in 107 fresh draws), so a re-hunt must
  be constructive; conjuncts **1 and 3** are free (a landed theorem, and the
  primal conjuncts when no two hubs are adjacent); conjunct **2 at the split's
  two `a`-edges IS two-sided (Λ0d)**; and **(σ7)** both halves of (Λ0d) cannot
  fail at once at a primally nondegenerate seed — do not re-derive any of
  these, and do not re-open *What would change this* (iv).
- **The transport structure of the induction** ((K-ind) I0–I2, I4): tight ⟺
  `(5c+1, 6c)`; `splitOff` raises `index` by exactly 1, preserves `c`, fixes
  `G°`; the class is a finite antichain inside each `G°`. **No move of
  `pencil_reduction` relates two class members** — do not re-open "carry a
  numerical invariant along the moves" without first exhibiting such a move.
- **Which induction the pencil side runs** ((K-ind) *Verification*): it is
  `Graph.pencil_reduction`, **not** KT Thm 4.9 / `minimal_kdof_reduction`, and
  `hK` enters **only** through the split arm
  (`pencilPair_of_splitOff_of_habitat`). Fix any prose that implies otherwise.
- **The `Gr(3,6)` picture, with its four objects kept apart** ((K-ind) I0): the
  point `V_bc(p)`, the map `φ_G` and its image, the **graph-independent** bad
  locus `B` (two Schubert divisors = a degree-2 form factoring into two
  hyperplanes), and `F = φ_G^{-1}(B)`. That global factorization is the same
  geometry as (Λ1)'s local one, at a different scale. `deg Gr(3,6) = 42` is
  orientation only; **the class of the discriminant `{det Gram_B = 0}` is
  UNVERIFIED — do not assert `2σ₁`.**
- **A third reading of the `ℓ = 3` five brackets** ((K-Δ) (N2)): they are the
  five **diagonals of the pentagon** `b–x–y–c–a–b`, whose sides are the
  structurally-vanishing Gram entries — so `Q(z) ≠ 0` ⟺ no two non-consecutive
  edges of that closed chain meet.
- **The Δ-matroid / orthogonal-matroid literature is checked and MISSes**
  ((K-Δ)) — `Pencil-strategy.md` §7's lead is discharged; do not re-run it.

## §(K-tight) — the carrier escape criterion (KT pp. 684–691 re-pin) and the uniform mechanism

The hard residue of kernel **(K)** after the corank stratification: tight
habitats (`5|E| = 6(|V| − 1)`), both chain ends hubs, 2-connected — plus,
since the W4 route-3(b) adjudication, the whole (K-res) residual habitat,
which sits in the same `dim R_a = 1` shape (`notes/Pencil-W4-informal.md`
§"widened kernels" *Step 2*).

**Verdict (two-part).** The **escape criterion** below is
**proven-informally** — exact linear algebra from KT's pp. 684–691 machinery
re-derived against the carrier, machine-validated per-placement and per-seed
at every probed habitat (`notes/scripts/w4/repin.py`). The **kernel** stays
**open**, narrowed to one uniform gap ((K-move)/(K-pitch), Step 5). A key
factual correction rides along: **no escape failure has ever actually been
observed in the phase's numerics** — the recorded failure figures (11/12 at
the tight control including seed 442; 94/96 pool-wide) were artifacts of a
degenerate placement sampler, not of the mathematics (Step 3).

**What would change this.** *For the criterion:* an error in the
model-to-Lean dictionary (the scripts' 5-rows-per-hinge Euclidean-perp
rigidity model vs `BodyHingeFramework.rigidityRows`) — the derivation is
pairing-agnostic, but the numerics live in the script convention. *For the
kernel:* a target-rank seed with genuine uniform failure (`r̃ ∥ C(M)` below)
would inhabit the bad locus and force the uniform mechanism to engage it; a
White–Whiteley-style evaluation of the pitch polynomial (Step 5(b)) would
close it.

### Step 0 — what KT pp. 684–691 actually prove (transcription)

KT Lemma 6.10, `k = 0` case (all pointers verified against the `.refs` copy
this pass): `v` of degree 2 with neighbours `a, b`; `a` of degree 2 with
neighbours `v, c`; `G′ = G^{ab}_v`, with a generic nonparallel realization
`(G′, q)` at rank `6(|V|−2)` (6.18). **Claim 6.11** (p. 684): some copy
`(ab)_{i*}` of the 5-fold `ab` fiber is redundant — sourced from Lemma
4.3(ii)'s base `B′` with `|B′ ∩ ãb| < 5` (this is where KT consumes
minimality) — giving a row dependency `λ` with `λ_{(ab)i*} = 1`
(6.24)–(6.25). Three candidate realizations of `G`:

- `p₁` (6.12): `hinge(vb) := q(ab)` **pinned**, `hinge(va) := L` swept over
  **all** lines in the panel `Π(a)`;
- `p₂` (6.19): symmetric — `hinge(va) := q(ab)` pinned, `hinge(vb) := L′`
  swept over `Π(b)`;
- `p₃` (6.31)–(6.33): via the isomorphism `ρ : G^{vc}_a ≅ G^{ab}_v` (`v, a`
  an adjacent degree-2 pair), `hinge(va) := q(ac)`, `hinge(vb) := q(ab)`
  pinned, `hinge(ac) := L″` swept over `Π(c)`.

Row/column operations (6.26)–(6.30), (6.35)–(6.41) reduce attainment to a
top-left `6×6` block `M₁/M₂/M₃` (6.42), whose second row is always
`r := Σ_j λ_{(ab)j} r_j(q(ab))` — for `M₃` via the identity **(6.44)**
`r = −Σ_j λ_{(ac)j} r_j(q(ac))`, the stress balance at the degree-2 body `a`
(KT glosses `r` as the force applied to `a`'s panel through the hinge,
p. 681). **Claim 6.12** (pp. 690–691): if all three fail for every choice of
`L, L′, L″`, then `r ⊥` the span (6.45) `= Λ²Π̂(a) + Λ²Π̂(b) + Λ²Π̂(c)`,
which is **6-dimensional** at a generic nonparallel seed (the four-point
Lemma-2.1 argument), forcing `r = 0` — contradiction.

### Step 1 — which KT freedoms survive the carrier pin

Carrier facts, from definition bodies: `HasPencilPanelRealization`
(`Molecule/Pencil/Statement.lean:88`) requires every link's extensor through
**both** endpoint points; `IsNondegPencilRealization` conjunct 2 makes
adjacent points projectively distinct, so **every hinge is pinned**:
`C(uv) ∝ pt(u) ∧ pt(v)`. Conjunct 4 forbids `pt(v) ∈ line(pt a, pt b)` at
the degree-2 body `v`. At a hub `h`, every neighbour's point lies in `Π̂(h)`
(the hinge is in `h`'s panel and through the neighbour's point).

| KT freedom | carrier fate |
|---|---|
| `p₁`/M₁: `hinge(va)` sweeps `Π(a)`, `hinge(vb) := q(ab)` | **DEAD**: `hinge(vb) = pt(v) ∧ pt(b) = q(ab)` forces `pt(v) ∈ line(a,b)` — the nondegeneracy-forbidden locus |
| `p₂`/M₂: `hinge(vb)` sweeps `Π(b)` | survives as **route A**: `pt(v)` sweeps `Π̂(b)` (`b` hub; all of `K⁴` if not) — with **both** new hinges moving, neither pinned |
| `p₃`/M₃: `hinge(ac)` sweeps `Π(c)` | survives as **route B**: `ρ` is carrier-valid (degrees preserved), `pt(v) := old pt(a)`, new `pt(a)` sweeps `Π̂(c)` |
| — | **NEW, not in KT**: the joint sweep `(pt v, pt a) ∈ Π̂(b) × Π̂(c)`, strictly larger than A ∪ B — un-analyzed; can only enlarge the escape |

So the carrier deletes M₁ outright and re-shapes M₂/M₃ from
one-hinge-swept-one-pinned constructions into point sweeps moving both new
hinges at once. Neither the §2 form `S = Λ²Π̂(a) + pencil(b) + pencil(c)`
nor the pencil-restricted M₂ is the right criterion; Step 2 derives what is.

### Step 2 — the boundary-load calculus on the carrier

Scope: `def(G) = def(G′) = 0` (the `k = 0` / Case-III world; `k > 0` routes
to KT Case II per the design doc), `deg_G v = 2`, a target-rank `G′`-seed.
Write `⟨·,·⟩` for the fixed pairing in which each hinge's 5 rows span
`C(e)^⊥` (Euclidean on Plücker coordinates in the scripts; the derivation
never uses more), `s₀` = corank of the **shared** rows (edges of `G − v`),
and

> `U := {u ∈ K⁶ : (u @ a, −u @ b) ∈ rowspan(shared rows)}`
> ` = {u : ⟨u, m(a) − m(b)⟩ = 0 for every motion m of the shared framework}`.

All of the following is exact (no genericity), machine-validated at every
probed seed (Step 3):

1. **Corank identity.** At placement `pt(v) = x` (with `x ∉ {[â],[b̂]}`),
   `corank R(G) = s₀ + dim(U ∩ C(va)^⊥ ∩ C(vb)^⊥)`; attainment of
   `target(G)` ⟺ the two functionals `u ↦ ⟨u, C(va)⟩`, `u ↦ ⟨u, C(vb)⟩`
   are **linearly independent on `U`**. (A `G`-row dependency's `v`-block
   forces antisymmetric fiber loads `±u`; its remaining blocks say exactly
   `(u@a, −u@b) ∈ rowspan(shared)`.)
2. **`U ∩ C(ab)^⊥ = R_a`** — the boundary loads reciprocal to the deleted
   hinge are exactly the stress loads (`u = Σ ν_j r_j(C_ab)` plus the shared
   relation *is* a `G′`-stress with `ab`-part `ν`).
3. **`dim U = dim R_a + 1`, forced**: `≤` because `U` meets the hyperplane
   `C(ab)^⊥` in the `dim R_a`-dim `R_a`; `≥` because the shared framework
   has exactly `4 + s₀ − index(G)` relative motions while
   `dim R_a = index(G) + 1 − s₀` at a target-rank seed. Consequences:
   `dim R_a = 0` (the `s₀`-jump seeds, and most deficient residuals) means
   **failure at every placement**; `dim R_a ≥ 1` is the live case; the old
   (K-shared) seed-quality worry is absorbed here — "some `G′`-stress
   engages the `ab` fiber" is all the quality a seed needs.
4. **The hard stratum `dim R_a = 1`** ((K-tight) and every probed (K-res)
   residual): `U = ⟨r⟩ ⊕ ⟨w⟩` with `⟨w, C_ab⟩ ≠ 0` forced. The route-A
   failure locus in the confinement space is the **degenerate conic**
   `det = ℓ_{line(ab)} · ℓ_{P′}`: the deleted hinge's line **union a second
   line `P′`** — so "the failure set is exactly the line" is refuted (the
   `∃`-form side conditions survive; any `∀`-form "off-line ⟹ attains"
   would be false). Uniform route-A failure ⟺
   `r ⊥ (pencil(pt a; Π(b)) + pencil(pt b; Π(b))) = Λ²Π̂(b)` when `b` is a
   hub (the two pencils span **all** lines in the panel because
   `pt(a) ∈ Π(b)` in the `G′`-seed), resp. ⟺ `r ∥ ★C_ab` when `b` is free.
   Route B is the mirror with load `−r` (KT 6.44): uniform failure ⟺
   `r ⊥ Λ²Π̂(c)`.
5. **(K-tight) combined criterion.** Both chain ends hubs: uniform failure
   of A and B ⟺ `r ⊥ (Λ²Π̂(b) + Λ²Π̂(c))` (5-dim) ⟺
   **`r̃ := ★r ∥ C(M)`**, `M = Π(b) ∩ Π(c)` the panels' **meet line** (which
   passes through `pt(a)`: the `G′`-seed pins `pt(a)` onto `M`). Gloss: the
   wrench the stress transmits through the deleted hinge is a **pure force
   along the meet line**. In particular a **non-null transmitted wrench**
   (`⟨r̃, r̃⟩_Klein ≠ 0`, "the wrench has pitch") certifies escape.
6. **Where KT's six dimensions went.** The carrier keeps 5 of KT's 6 escape
   dimensions — M₁'s panel `Λ²Π̂(a)` is exactly the lost one — so failure
   is one dimension away from KT's impossible. That single dimension is why
   PENCIL is research where KT Claim 6.12 was a page.

### Step 3 — machine validation, and the corrected numerical record

`notes/scripts/w4/repin.py` (tracked; exact-ℚ). Reproduce:
`python3 notes/scripts/w4/repin.py --control | --theta | --witness |
--stratum | --pointwise`.

- **The seed-442 "mispredict" was a sampler artifact.** `localtest.py`'s
  `plane_basis` returns two *parallel* in-plane directions whenever the
  normal's third coordinate is `0`, so `in_plane_point` then samples a
  **line through `pt(b)`**, freezing `hinge(vb)` across all placements. At
  seed 442, `nrm[b] = (1, −5/2, 0)`. With a robust sampler
  (`repin.py::rob_in_plane`) **seed 442 escapes on both routes**; so do the
  pool's two recorded failures (one pair, seeds 5000/5001, both with
  `nrm[b][2] = 0`). Corrected record: **on the hard stratum `dim R_a = 1`, and
  above it, every target-rank seed ever probed escapes** — 34/34 tight control,
  12/12 `W19`, 4/4 `S29`, 24/24 the `(def 0, dim R_a 1)` pool stratum, and 6/6
  θ(4,4,3) at `dim R_a = 2`. (Positive records — on-line failures, rank
  attainments — are unaffected; the artifact only ever *suppressed* escapes.)
  **The stratum qualifier is load-bearing** (added 2026-08-05, §(K-flank)
  F5(d)): without it the sentence is *false*. At `P21` five legal nondegenerate
  target-rank `G′` seeds have `s₀ = 1`, `dim R_a = 0`, `dim U = 1`, and fail at
  **every** placement — exactly as Step 2.3 predicts. The figures above are
  unaffected (every seed behind them sits at `dim R_a ≥ 1`); what was stated
  more strongly than measured is the *record*, not the mathematics.
- **Per-placement biconditional 80/80** (`--pointwise`): attainment ⟺ the
  two `U`-functionals independent, checked placement-by-placement at the
  tight control (`s₀ = 0`) and `W19` (`s₀ = 2`).
- **Structure checks at every seed**: `dim U = dim R_a + 1`,
  `U ∩ C(ab)^⊥ = R_a`, `R_a ⊆ U` — all asserted, no exceptions.
- **`P′` exhibited**: at control seed 440 the calculus *predicts* an
  off-line failure point from `(r, w)`; the placement fails by exactly 1.
- **The pencil-restricted M₂ form is refuted as criterion**: seeds 442 and
  473 have `r ⊥ pencil(pt b; Π(b))` yet escape (the `pencil(pt a; Π(b))`
  half of `Λ²Π̂(b)` is what saves them) — 32/34 for M₂-pencil vs 34/34 for
  the corrected `Λ²Π̂(b)` test. The workbook's earlier "M2 12/12 vs S 11/12"
  observation is superseded: both figures scored predictors against
  artifact-contaminated observations.
- **`★C(M)` identified**: the 1-dim perp of `Λ²Π̂(b) + Λ²Π̂(c)` equals the
  meet line's starred extensor (seed-442 post-mortem; `r` is *not* parallel
  to it there, and `⟨r̃, r̃⟩ ≠ 0`).

### Step 4 — reconciliation with the §2 derivation

What the design doc's §2 boundary-load derivation got **right**: the
antisymmetric-load setup; `R_a` as the stress-load space with
`dim R_a = corank − s₀`; failure as a perp condition of the right
codimension (its `dim S = 5` matches Step 2's 5-dim span — hence 11/12-style
agreement); the qualitative stratification (`dim R_a ≥ 2` generically
escapes — now: `dim U = dim R_a + 1 ≥ 3` makes the rank-≤1 locus of the
`2 × dim U` form matrix codim `≥ 2` in the sweep). Three **panel leaks**:

1. **M₁'s span is carrier-unrealizable** — `Λ²Π̂(a)` (or even `pencil(a)`)
   must not appear: its construction pins `hinge(vb) := q(ab)`, forbidden.
2. **M₂/M₃ under-counted**: restricting to `pencil(b)`/`pencil(c)` treats
   one hinge as swept and one as pinned; on the carrier both new hinges move
   with the point, and the effective span is the **full**
   `Λ²Π̂(b)`/`Λ²Π̂(c)`.
3. **`u` was confined to `R_a`** — correct only under a pinned
   `hinge = q(ab)` (which lands `u` in `C(ab)^⊥`); the carrier's obstruction
   space is `U = R_a ⊕ ⟨w⟩`, whose extra direction produces the second
   failure line `P′`.

Also corrected: the (K) recon item 4's "non-hub chain ends give `dim S = 6`,
`r ≠ 0` suffices" — a free end still leaves a 1-dim bad set (`r ∥ ★C_ab`);
it is the *pair* of routes that generically kills it.

### Step 5 — the uniform mechanism ((K-move)/(K-pitch)): assessment

What the kernel still needs, per habitat graph `G` and split: **some**
target-rank `G′`-chart-seed with `r̃ ∦ C(M)` (the both-ends-hubs form; at a
free end the failure direction is the deleted hinge's own line — `r̃ ∦ C_ab`
suffices, strictly easier). Per-graph this is polynomial non-vanishing on
the chart variety — one exact-ℚ witness decides it (and every probed
habitat has many). The **uniform** statement over the class is the open
mathematics. Named routes, with status:

- **(K-move) — fiber variability** (the route-1 gate's lever, sharpened).
  `C(M)` is *local-block data* (determined by `Π(b), Π(c)`); uniform failure
  at a graph would force `[r]` to be the local-block-determined value
  `[★C(M)]` on **every** local-block fiber. The gate's N8 already witnesses
  `[r]` taking 5 distinct directions on one fiber (and moving under a single
  distance-4 far move), refuting this at both probed habitat families. A
  uniform proof still needs `[r]`-as-rational-function infrastructure.
  **Status: open — the sharpest gap**, unchanged in substance from the (K)
  recon, but the target is now the *proven* failure direction `★C(M)`
  rather than a criterion carried on trust.
- **(K-pitch) — the null-wrench test** (new this pass). Failure requires
  `r̃` to be a *line* extensor (Klein-null, `⟨r̃, r̃⟩ = 0`); so
  `⟨r̃, r̃⟩ ≢ 0` on the seed variety suffices — a **single scalar
  polynomial** per (graph, split). By Cramer cofactors, the corank-1 stress
  coefficients are signed maximal minors of the deleted-row matrices, so
  `⟨r̃, r̃⟩` is an explicit quadratic in such minors — exactly the shape the
  White–Whiteley pure-condition calculus structures (the 1983/1987 papers,
  the literature hunt's verified nearest exemplars). A leading-term /
  degeneration evaluation of this one polynomial is the most attackable
  formal route identified so far. **Status: open, newly named; strictly
  easier as a target than (K-move)** (scalar vs projective direction),
  though not implied by it in either direction.
- **Degeneration / limit arguments**: unchanged **NO-GO** — still blocked on
  stress control at degenerate seeds (route-1 gate).
- **The joint sweep** (Step 1's new freedom): un-analyzed; even a genuinely
  `r̃ ∥ C(M)` seed might escape through it. Only widens the target.

**Adversarial hunt (the mandate).** A counterexample to `hK`/(K-res) at this
stratum must have `r̃ ∥ C(M)` at **every** target-rank chart seed — the
transmitted wrench a pure force along the panel-meet line, identically on
the variety — and additionally kill the joint sweep. Structural constraints
do not forbid it: `r̃` is reciprocal to both hinges at `a` (lines through
`pt(a)`), and `C(M)` passes through `pt(a)`, so the bad direction sits
*inside* the structurally-allowed cone — there is no cheap refutation. But
nothing found points toward it: no genuine failure seed exists anywhere in
the phase's corrected numerics; N8's fiber variability contradicts
block-determined `[r]` at both probed families; and a candidate structural
mechanism (a stress confined to the two panels) is excluded by the route-1
gate's full-support finding. **No counterexample candidate; hunt negative.**

**Verdict for (K-tight) (and (K-res), same stratum): open — true with
strong evidence, narrowed to (K-move)/(K-pitch).** The enabling technology
is unchanged (stress-as-chart-rational-function / pure-condition
infrastructure, option B), with (K-pitch) as the new sharpest entry point:
one scalar polynomial whose non-vanishing per habitat closes the kernel's
hard stratum. **(K-pitch) is developed in §(K-pitch) below (2026-08-04)**:
the pitch transfers off the stress side onto the motion side of
`G − v − a`, and closes in bracket-monomial form at companion-chain
habitats.

## §(K-pitch) — the null-wrench route: motion-side transfer, the placement quartic, a bracket-monomial closed form

The attack on §(K-tight) Step 5's sharpest entry point: escape failure
requires the transmitted wrench `r̃ = ★r` to be a *line* extensor
(`⟨r̃, r̃⟩_Klein = 0`), so `⟨r̃, r̃⟩ ≢ 0` on the seed variety suffices — one
scalar polynomial per (graph, split). Standing notation, on top of
§(K-tight)'s: split chain `b–v–a–c` at a target-rank `G′`-seed in the
`def(G) = def(G′) = 0` world, hard stratum `dim R_a = 1`;
`H := G − v − a = G′ − a` (terminal bodies `b, c`);
`T := ⟨C_ab, C_ac⟩` (the pencil of lines through `pt(a)` in
`plane(a,b,c)`); `B(x,y) := ⟨x, ★y⟩` the Klein form (`B(C(L), C(L′)) = 0`
⟺ the lines meet), `Q(x) := B(x,x)` the pitch quadric (`Q(x) = 0` ⟺ `x`
is a line extensor).

**Verdict (three-part; parts (ii)/(iii) extended 2026-08-04, second
pass).** (i) The reductions (T1)–(T5) below — transferring the pitch off
the stress side onto the **motion side of `H`** — are
**proven-informally**: exact linear algebra plus classical quadratic-form
theory, machine-validated per seed at every probed habitat
(`notes/scripts/w4/pitch.py`). (ii) At habitats whose split chain has a
**parallel length-3 companion chain** — θ(3,3,6) the exemplar, a member of
the **(K-res)** hard stratum (it contains a rigid `C₆`) — the pitch
polynomial collapses to a **bracket monomial** and (K-pitch) **closes**
(Step 5): the first hard-stratum splits discharged by argument (exact
seeds certify only the open side conditions' nonemptiness) rather than by
observation alone. For **longer companions** the far data compresses to a
single annihilator covector and `Q(z)` is an explicit local quadratic in
it (Step 5b, (T5)). (iii) The uniform kernel over the full class stays
**open**, but the naive collinear-collapse route is **refuted** and
replaced by the chart-legal **slide-in degeneration** (Step 6), which
evaluates the pitch at a `G°`-local limit system — developed in the
sibling **§(K-slide)** (2026-08-04 third pass) into a proof device: the
slide-transfer theorem (S1) makes one exact limit witness close a
habitat's split, the `K4`/`W4` control habitats are closed at every
split, and the named gaps are now **(K-Λ)** — since **refuted as an
*independent* gap**, being equivalent to **(K-wit)** at length-4-companion
splits (§(K-Λ), sixth pass) — and **(K-slide-cl)** —
itself reduced (fourth pass, §(K-slide-cl)) to the combinatorial
**(K-slide-comb)**, which the fifth pass (§(K-slide-comb)) **refutes**
class-wide, so (K-slide-cl) stays open with a named covered sub-class —
plus the `P21`-type parallel-edge shapes (with
(K-wit) still the weakest exact form). Adversarial record intact — pitch was **nonzero at every
probed seed** (29/29 first pass: 16 tight-control + 5 residual + 8
pool-stratum; +5/5 second pass at the (T5) driver, θ(3,4,5) and the new
non-theta tight habitat NT21; +23/23 limit witnesses + 12/12 transfer
certificates, third pass, §(K-slide) Step 4).

**What would change this.** *For the reductions:* an error in the two-port
derivation (T1) — each claim is asserted per seed against an independently
computed stress. *For the route:* a habitat with `Q(z) ≡ 0` at every seed
(that kills the pitch route there, while escape may still hold through a
moving line wrench); none found. *For the closed form:* a companion-chain
habitat where one of the five brackets vanishes identically on the pencil
chart — the stated hypotheses exclude the one identified degeneration
(an `x`/`y`–opposite-hub adjacency, which drops `dim V_bc ≤ 2` and leaves
the companion-chain hypothesis unsatisfiable). *For the slide-in route:* a
simple-`G°` habitat whose slide-in limit twist is null or rank-degenerate
(that would puncture (K-slide-cl); none found — §(K-slide) *What would
change this* carries the sharper conditions). *(Retired:* "a companion habitat
whose local quadratic `Φ_loc` is the zero form" was listed here as the (K-Λ)
risk; §(K-Λ) (Λ1) proves it **impossible** — `Φ_loc` is always a nonzero rank-2
form — so that observation cannot occur.*)*

### Step 0 — the pitch polynomial, and which specializations are legitimate

By Cramer, the corank-1 stress's coefficients at a target-rank seed are
signed maximal minors of the deleted-row matrices of `R(G′)`, so
`r = Σ_j λ_{(ab)j} r_j(C_ab)` and `P := ⟨r̃, r̃⟩` are honest **polynomials
in the chart coordinates** (not just rational functions on the target-rank
locus). Two consequences frame everything below.

- **One witness seed decides a split.** `P ≢ 0` plus density of the
  target-rank locus (supplied by the kernel's own antecedent,
  `HasGenericPencilRealization` of the split graph) gives a seed that is
  simultaneously target-rank and `P ≠ 0`; §(K-tight) Steps 2/5 then give
  the escape, and `hK`/(K-res)'s conclusion follows (the hub-selector /
  `pencilRow` packaging is combinatorial, from `hcard` —
  `notes/Pencil-W4-informal.md` §"widened kernels" Step 5).
- **Polynomial specialization ≠ the refuted degeneration route.** The
  route-1 NO-GO (design doc §"(K) route-1 gate") refuted *analytic stress
  control at degenerate seeds*; evaluating the polynomial `P` at a special
  chart point needs no control — the obstruction was only ever that no
  specialization made the global minors *computable*. (T1) supplies
  exactly that computability, by eliminating the stress from `P`
  altogether.

### Step 1 — (T1): the two-port transfer — `r` from motions of `H`, no stress

`H = G′ − a` and `a` carries exactly the two hinges `C_ab, C_ac` in `G′`,
both through `pt(a)` (KT's (6.44) equilibrium body). Let

> `V_bc := { m(b) − m(c) : m a motion of H }` ⊆ `K⁶`

be the **relative twist system** of the terminals — a motion-side object
(motions of a body–hinge framework are screw-center assignments with
`m(x) − m(y) ∈ ⟨C_xy⟩` per hinge; Whiteley 1996 §12.2). Then, exactly:

> **(T1)** `r` is Euclidean-orthogonal to `V_bc` and to `T`; at a seed
> with `dim V_bc = 3` (the generic value; observed at every probed seed)
> `W := V_bc ⊕ T` is 5-dimensional and **`r` spans `W^⊥`**. Moreover
> `V_bc ∩ T = 0` is *forced* at a target-rank seed.

*Proof.* Restrict the stress `λ` to the `H`-rows: equilibrium at every
body off `{a, b, c}` is untouched, at `b` the deleted `ab`-fiber
contributed `−r`, at `c` the `ac`-fiber contributed `−r_ac = +r` (6.44).
So `λ|_H` is an `H`-row combination with net load `(+r @ b, −r @ c, 0)`.
Pairing a row combination's loads against any motion gives `0`, so
`⟨r, m(b) − m(c)⟩ = 0` for every motion `m` — `r ⊥ V_bc`; `r ⊥ T` is the
reciprocity of `r` to both `a`-hinges (§(K-tight)). Conversely a nonzero
`t = ω₁C_ab + ω₂C_ac ∈ V_bc ∩ T` extends the `H`-motion to
`m(a) := m(b) − ω₁C_ab = m(c) + ω₂C_ac`, a nontrivial flex of `G′` —
impossible at a target-rank seed with `def(G′) = 0`. So
`dim W = dim V_bc + 2 = 5` and the 1-dimensional `W^⊥` is `⟨r⟩`. ∎

Two structural facts ride along. **(a) Path-sum containment:** telescoping
`m(x) − m(y) = ω_{xy}C_{xy}` along any `b`–`c` path `P` of `H` gives
`V_bc ⊆ span{C_e : e ∈ P}` — for **every** path, simultaneously. This is
the lever Step 5 uses. **(b)** `V_bc` needs only a kernel computation
(cycle conditions on hinge rotations) — the stress, its cofactors, and
the corank bookkeeping have disappeared from the right-hand side; this is
the computable simplification the refuted routes lacked.

### Step 2 — (T2): the sign law — pitch of `r` = − pitch of the reciprocal twist

`T` is **totally isotropic** for `B` (its two generators meet at `pt(a)`),
and both `★r` and the solution set of `B(·, C_ab) = B(·, C_ac) = 0` live
in `T^⊥` (Klein-perp, 4-dimensional). Let

> `z` span `V_bc ∩ T^{⊥_B}` — the **reciprocal twist**: the unique (up to
> scale, generically) relative twist of `b` vs `c` through `H` that does
> no reciprocal work on either hinge at `a`.

In the quotient `T^{⊥_B}/T` — a **hyperbolic plane** (Witt index drops by
`dim T`) — the classes of `★r` and `z` are `B`-orthogonal (that is (T1):
`B(★r, z) = ⟨r, z⟩ = 0`). In a hyperbolic plane two nonzero orthogonal
vectors are either both isotropic (and parallel) or both anisotropic with
`Q`-values of product `= −(nonzero square)`:

> **(T2)** at a seed where `z ∉ T` and `★r ∉ T`:
> `Q(r) = 0 ⟺ Q(z) = 0`, and when nonzero `Q(r)·Q(z) < 0`.

So the pitch of the transmitted wrench equals (up to a negative square)
the pitch of a **motion** of the smaller framework `H`. Failure geometry:
`Q(z) = 0` means the reciprocal twist is an actual **line** `L`; `z ∈ T^⊥`
then forces `L` through `pt(a)` or `L ⊆ plane(a,b,c)` (a line meets both
`a`-hinges ⟺ one of the two). On the irreducible chart, identical
vanishing of `Q(z)` therefore splits into two sharp identical-membership
statements — *(F-A)* `z` is always a rotation about a line through
`pt(a)`, or *(F-B)* always about a line in `plane(a,b,c)` — each refutable
by one exact seed.

### Step 3 — (T3): the motion form of the full criterion, and (K-wit)

The β-plane `Λ²Π̂(b)` is maximal isotropic, hence its own Klein-perp; so
§(K-tight)'s route-A uniform-failure criterion `r ⊥ Λ²Π̂(b)` reads:
**`★r` is a line lying in the panel `Π(b)`** — and route B dually. Both
routes failing ⟺ `★r ∈ Λ²Π̂(b) ∩ Λ²Π̂(c) = ⟨C(M)⟩`, recovering
§(K-tight) Step 2.5. Transferred by (T1) (and using
`B(C(M), C_ab) = B(C(M), C_ac) = 0`, since `M` passes through `pt(a)`):

> **(T3)** at a `dim W = 5` target-rank seed, both hubs: **escape ⟺ some
> motion `m` of `H` has `B(C(M), m(b) − m(c)) ≠ 0`** — the relative twist
> system is not contained in the linear line complex of the meet line.

Two consequences. **(a)** `Q(r) ≠ 0` certifies **both routes at once**
(any failure mode requires `★r` decomposable) — and this is
**end-stratum-uniform**: at a free chain end the failure directions are
again line extensors (`★C_ab`-type, §(K-tight) Step 4), so pitch ≠ 0
certifies escape in every end configuration with the *same* polynomial.
**(b)** The kernel's remaining content, in its weakest exact form, is now
stress-free and existential:

> **(K-wit)** *(per habitat + split; equivalent to the escape at a good
> seed)* — some pencil-chart target-rank seed of `G′` admits a motion of
> `H` whose relative `b`–`c` twist pairs non-trivially with `C(M)` (both
> hubs; at a free end, with the corresponding 1-dim failure direction).

One linear functional on one kernel — much closer to the phase's
somewhere-witness engine food than stress cofactors, though still open
uniformly (the kernel is seed-dependent).

### Step 4 — (T4): the placement quartic, and an `a`-free leading term

`pt(a)` is a chart coordinate confined to the meet line `M`; `V_bc` does
not involve `a` at all. Fix everything but `pt(a) = p₀ + t·d` (`d` = the
direction of `M`): the two conditions cutting `z` out of `V_bc` are linear
in `t`, so `z(t)` is quadratic and

> **(T4)** `q(t) := Q(z(t))` is a polynomial of degree ≤ 4 whose `t⁴`
> coefficient is `Q(z_∞)`, where `z_∞` is the same construction with the
> two `a`-hinges replaced by the lines joining `M`'s **direction point**
> `(d, 0)` to `pt(b)`, `pt(c)` — an expression in which `a` does not
> appear.

Validated by exact interpolation at four habitats (one seed each,
`--sweep`), with the sign law re-checked against a fully recomputed stress
at moved placements. All five coefficients were nonzero at all four, the
leading one included. This gives a sufficient reduction one level down:

> **(K-pitch-∞)** *(sufficient for (K-pitch) at the split)* — `Q(z_∞) ≢ 0`
> on the `a`-free part of the chart.

### Step 5 — the companion-chain closed form: pitch as a bracket monomial

Suppose the split chain `b–v–a–c` has a **parallel length-3 companion**:
a second path `b–x–y–c` in `H` (so `G` has two length-3 hub paths between
the same hubs). Write `C₁ = C(bx), C₂ = C(xy), C₃ = C(yc)` and
`[p,q,r,s]` for the `4×4` determinant of the four homogenized points.

> **Proposition (companion-chain closed form).** At a target-rank seed
> with `dim V_bc = 3`: path-sum containment (Step 1a) pins
> `V_bc = ⟨C₁, C₂, C₃⟩`, and the reciprocal twist is
> `z = −[y,c,a,b][x,y,a,c]·C₁ + [y,c,a,b][b,x,a,c]·C₂
>      − [x,y,a,b][b,x,a,c]·C₃`, with
>
> `Q(z) = 2·[x,y,a,b]·[b,x,a,c]·[y,c,a,b]·[x,y,a,c]·[b,x,y,c]`.
>
> In particular (T2/T3): if the five brackets are nonzero at one such
> seed, the split escapes.

*Proof.* The Gram of `B` on `(C₁, C₂, C₃)` has only one nonzero entry,
`B(C₁, C₃) = [b,x,y,c]` (consecutive lines meet at `pt(x)`, `pt(y)`) —
the serial-chain signature (`rank Q|_{V_bc} = 2`, observed identically at
θ(3,3,6)). The two cutting conditions have coefficient rows
`(0, [x,y,a,b], [y,c,a,b])` and `([b,x,a,c], [x,y,a,c], 0)` — the zeros
because `C₁` and `C_ab` meet at `pt(b)`, `C₃` and `C_ac` at `pt(c)`. The
cross product gives `z`; expanding `Q` through the Gram leaves the single
`2·z₁z₃·[b,x,y,c]` term. ∎

**What the five brackets *are*, in two lines** (§(K-Λ) *Step 1*(i)). At a
length-3 companion `S := ⟨C₁,C₂,C₃⟩ = V_bc` is 3-dimensional, so
`dim(S ∩ α_a) = dim(S ∩ β_{π_a}) = 3 + 3 − 6 = 0` generically, where
`α_a`/`β_{π_a}` are the two maximal isotropic 3-spaces containing `T`
(§(K-pure) (PC-Z)); and `z ≠ 0` lies in `S ∩ T^{⊥B}`, so `Q(z) = 0` would force
`z ∈ α_a ∪ β_{π_a}` (§(K-Λ) (Λ0′)). **The monomial above is therefore the
coordinate form of the two transversality conditions
`S ∩ α_a = S ∩ β_{π_a} = 0`** — which also says why the closure is a length-3
phenomenon (§(K-Λ) *Step 1*(ii): those intersections have dimension `k − 3`).

**Instantiation: θ(3,3,6)** (two length-3 paths + one length-6 path
between two hubs; tight, `def = 0` (machine-checked), 2EC,
landed-**sufficient** feasible — triangle-free with `hcard` from the R4
shape, the L6b criterion — and it contains the rigid `C₆` spanned by the
two short paths, so it is a **(K-res)**-habitat member, not reachable by
the pinned `hK`). On its chart: `x, a ∈ Π(b)`, `y, a ∈ Π(c)`, all else
generic. Each bracket has an obvious witness — `[x,y,a,b]` needs
`y ∉ Π(b)` etc.; `[b,x,y,c]` needs the two short paths non-coplanar — so
each is `≢ 0` on the irreducible chart, hence so is their product; the
remaining open conditions (target rank, `dim V_bc = 3`, the (T2) side
conditions) are nonempty by the validated seeds, so a common good seed
exists and **(K-pitch) holds at θ(3,3,6)'s hard-stratum split:
proven-informally** (machine-confirmed exactly, `--theta336`:
`V_bc = ⟨C₁,C₂,C₃⟩`, the monomial identity, and the sign law against the
independently computed stress, 4/4 seeds).

**Scope.** The proposition applies verbatim to any hard-stratum split
with a parallel length-3 companion (interior `x, y` may even be hubs —
only the five bracket-nonvanishing checks are chart-dependent). The one
identified degeneration: `y` adjacent to `b` (or `x` to `c`) forces the
bracket's four points coplanar *and* creates a shorter `b`–`c` path,
collapsing `dim V_bc ≤ 2` — outside the proposition's hypotheses. This is
the White–Whiteley mechanism in miniature: at special structure the pure
condition **factors into brackets** (cf. the 1987 paper's factorization
of bar-and-body pure conditions along the block lattice), and the pencil
chart is then attacked bracket-by-bracket.

### Step 5b — (T5): longer companions — the Λ-compression

Suppose the companion `b`–`c` path has length `k` with `4 ≤ k ≤ 6` and
independent lines `C₁,…,C_k`. Path-sum containment still pins
`V_bc ⊆ ⟨C₁,…,C_k⟩`, now of codimension `k − 3`; **all far-graph
dependence enters through the annihilator** `Λ` of `V_bc` in the span's
dual (a `(k−3)`-frame of covectors; for `k = 4` a single covector `λ`, up
to scale). For `k = 4`:

> **(T5)** with `m := (⟨C_i, ★C_ab⟩)_i = (0, m₂, m₃, m₄)` and
> `n := (⟨C_i, ★C_ac⟩)_i = (n₁, n₂, n₃, 0)` (the zeros structural, as in
> Step 5), the reciprocal twist's coefficient vector is the Laplace
> cofactor vector `ω` of the `3×4` matrix `[λ; m; n]`, and — since the
> path Gram is banded (consecutive lines meet) —
>
> `Q(z) = 2·(ω₁ω₃·[b,x₁,x₂,x₃] + ω₂ω₄·[x₁,x₂,x₃,c] + ω₁ω₄·[b,x₁,x₃,c])`
>
> — an explicit **quadratic form `Φ_loc(λ)`** whose coefficients are
> 4-point brackets in the local points `{b, x₁, x₂, x₃, c, a}` only.

`k = 3` recovers Step 5 (no far data at all — `Φ_loc` is a constant, the
bracket monomial); at `k ≥ 7` the span is everything and the compression
is vacuous. The gap this was originally reduced to on such habitats (**as first
stated; superseded — see the paragraph below it**):

> **(K-Λ)** *(sufficient for (K-pitch) at a length-4-companion split)* —
> some target-rank chart seed's far covector `λ` avoids the local quadric
> `{Φ_loc = 0}`.

**That framing is SUPERSEDED — see §(K-Λ).** "One projective point against one
locally-computable quadric" reads as if the far graph's only job were to miss a
small set, and the risk it flagged was `Φ_loc ≡ 0`. Both readings are wrong.
`Φ_loc` is *always* a **rank-2** form — the product of two distinct rational
linear forms in `λ` (§(K-Λ) (Λ1)) — so the quadric is a pair of hyperplanes and
there is nothing to prove on the non-degeneracy side; and once (T4)'s `a`-line
freedom is used, the far covectors bad for the *whole* line shrink to **two
points**, which are exactly the genuine (T3) escape failure and a configuration
where route A escapes outright. Hence **(K-Λ) is *equivalent* to (K-wit)** at a
length-4-companion split and is **not an independent gap**; §(K-Λ) also
**refutes** the `ℓ ∈ {5,6}` continuation of this frame. What stands unchanged is
the (T5) machine validation (`--companion4`): at θ(3,4,5) (where `λ` is
independently recomputable as the far arc's span normal — cross-checked) and at
**NT21**, a new non-theta tight habitat (hub multigraph on 4 hubs with `b`–`c`
paths of lengths 3 and 4 plus five more; `Σℓ = 24 = 6·4`; certified `def = 0` and
no proper rigid branch-union over all `2⁷` branch subsets): `λ` unique, `z`
reproduced from `(λ, m, n)` alone, the `Φ_loc` identity exact, and `Q ≠ 0` with
the (T2) sign law against the independently computed stress, 5/5 seeds.

### Step 6 — uniformity: the naive collapse refuted, and the slide-in degeneration

**(a) The naive collinear collapse is REFUTED as a chart move.** "Each
hub path degenerates toward its own line" cannot happen on the pencil
chart: an interior `x` adjacent to hub `u` lives in `Π(u)`, and the chord
`line(pt u, pt w)` meets `Π(u)` only at `pt(u)` (else the panels are
incident) — so the path can only reach its chord *at the hub point
itself*. And repairing this by making chords panel-resident
(`pt(w) ∈ Π(u)` along every `G°`-edge) forces each closed hub star
coplanar (`n_u ⊥` every neighbour chord — impossible outright when the
chords at `u` span 3-space), which on the probed complete-type `G°`
(e.g. `K4`) is exactly the **all-coplanar locus** — and that locus is
target-rank-**deficient** on tight habitats (R2's criterion
`2|E| < 3|V| − 3` holds identically under `5|E| = 6(|V|−1)`). The
tightness budget `Σ_P ℓ_P = 6·c°(G°)` (elementary:
`index(G) = 6(|E°| − |V°| + 1) − Σℓ_P`) survives as bookkeeping, but the
order-0 "body–hinge on `G°` with one line per path" picture does not.

**(b) The corrected, chart-legal degeneration: the slide-in.** Move each
panel-constrained interior *into its hub point along its own ray*:
`x(ε) = pt(u) + ε·(x₀ − pt(u))` — the segment stays in `Π(u)`, so every
`ε > 0` is an honest chart point. The hinge lines have a clean limit,
per edge: a **hub-incident** hinge `u–x` is *constant* along the slide
(`û ∧ (û + εd) = ε·û∧x̂₀` — same line, dying magnitude); an
**interior–interior** hinge becomes the **chord** `û∧ŵ`; an
interior–fixed hinge becomes the hub-to-point line. So for an
all-length-3 (double-subdivision) habitat the limit system is **body–
hinge on `G°` where each edge carries the serial triple
(pencil line at `u`, chord `u∧w`, pencil line at `w`)** — consecutive
members meeting at the hub points, i.e. per `G°`-edge exactly the banded
serial-chain Gram of Step 5, one level up. The far data compresses to
`G°`-local decorations (hub points, normals, one pencil parameter per
edge-end).

**(c) Why the limit is legitimate: the slide-transfer theorem.** The
analytic route this pass first recorded (constant-rank family ⟹
continuous kernel, with `O(ε)` Plücker convergence as evidence) is
**superseded by §(K-slide) (S1)**: the normalized row family is
polynomial in (chart data, `ε`) including `ε = 0`, the slide is a chart
automorphism for `ε ≠ 0`, and one exact limit witness proves `Q(z) ≢ 0`
on the chart by Zariski closure alone — no convergence, and rank
persistence (the observed `9 → 9`) is an a-posteriori corollary, not a
hypothesis.

**(d) The slide-in evaluation WORKS on simple `G°` — now a proof
device.** At dbl-subdivided `K4` (the (K-tight) control), the limit
system keeps `dim V_bc = 3` and its reciprocal twist is **pitched**
(3/3 exact, `--slide`). The gap this named, (K-slide) — "`Q ≠ 0` at
the limit system for generic decorations" — is **witness-decidable per
member by (S1)** and *discharged at every probed member*; the surviving
uniform statement is **(K-slide-cl)** (§(K-slide) Step 5). The
`G°`-level system — decorated multigraphs, finitely many parameters per
edge, no subdivision interiors — is squarely White–Whiteley-1987
territory and now carries the class program.

**(e) The parallel-edge obstruction — and the division of labor.** On a
theta, all chords coincide with `line(b,c)`, and the (partial) slide-in
limit twist comes out **null** (`Q = 0`, 2/2 exact at θ(3,4,5)): the
order-0 evaluation fails on `G°` with parallel edges — and §(K-slide)
(S5) shows this is structural (a repeated line in a hinge cycle under
the full support; a hub-concentrated circuit under reduced supports).
Parallel `b`–`c` edges are exactly **short companion paths** — Steps
5/5b's monomial / `Φ_loc` territory. The two flanks this pass left
untested — mixed path lengths on simple `G°`, and hub–hub edges — are
now **witnessed inside the slide framework** (§(K-slide) Steps 2/4);
what remains outside both mechanisms is the non-`bc`-parallel shape
(`P21`, §(K-slide) S5).

- **The joint sweep** (§(K-tight) Step 5) still only widens the escape;
  un-analyzed.

**Adversarial hunt (this pass).** A pitch-route counterexample must have
the reciprocal twist `z` decomposable at every seed — by the Step-2
dichotomy, a line through `pt(a)` always, or a line in `plane(a,b,c)`
always — while `V_bc` varies with the far seed (route-1 gate, N8). No
structural mechanism produces that: the only found `Q|_{V_bc}`-degeneracy
(the serial-chain Gram) still yields nonzero pitch as a bracket monomial.
Pitch was nonzero at **29/29** probed seeds: 16 tight-control (dbl-subdiv
`K4` 6, θ(3,4,5) 5, θ(3,3,6) 5), 5 residual (`W19` 3 — free-end shape,
`S29` 2 — both-hubs), 8 pool-stratum (4 splits × 2); the second pass adds
**5/5** at the (T5) driver (θ(3,4,5) 3, NT21 2). The slide-in limit's
*null* twist on thetas is not a counterexample — those splits escape
through Steps 5/5b, and the theta `ε`-family itself stays `Q ≠ 0` at every
sampled `ε` down to `1/64`. **No counterexample candidate; hunt
negative.**

### Verification

`notes/scripts/w4/pitch.py` (tracked; exact-ℚ, on top of `repin.py`, with
its robust in-plane sampler; every sampled object carries rank/dimension
asserts). Reproduce:
`python3 notes/scripts/w4/pitch.py --control | --witness | --stratum |
--sweep | --theta336 | --companion4 | --slide`. Per seed it asserts:
(T1) `r ⊥ V_bc`, `V_bc ∩ T = 0`, `W^⊥ = ⟨r⟩`; (T2) side conditions and
the sign law `Q(r)·Q(z) < 0` (or both zero); (T3) the motion-form
combined criterion against `repin.py`'s validated `critA/critB`, and the
`★r`-in-panel route-A form; (T4) exact interpolation, degree ≤ 4,
`q₄ = Q(z_∞)`, and the sign law against a recomputed stress at two moved
placements; (`--theta336`) the pairing–bracket dictionary
`B(C(uv), C(pq)) = [u,v,p,q]`, `V_bc = ⟨C₁,C₂,C₃⟩`, the closed-form `z`,
and the bracket-monomial identity; (`--companion4`, T5) the containment
`V_bc ⊆ ⟨C₁..C₄⟩`, uniqueness of `λ`, `z` from `(λ, m, n)` alone, the
`Φ_loc` identity, the θ far-arc `ν` cross-check, and NT21's habitat
certificates (`def = 0`, no proper rigid branch-union, `2⁷` subsets);
(`--slide`) the per-edge limit-line rule, motion-rank persistence
(9 → 9), `O(ε)` Plücker convergence of `V_bc(ε)` to the limit plane, and
the limit twist's pitch class (pitched at dbl-K4, null at θ).

**Confidence verdict: (T1)–(T5), the companion-chain closed form, and
the slide-in limit calculus proven-informally; (K-pitch) at
θ(3,3,6)-type splits proven-informally; the naive collinear collapse
refuted; the uniform (K-pitch)/(K-tight)/(K-res) kernel open — narrowed
at companion habitats to **(K-wit)**, onto which (K-Λ) collapses
(§(K-Λ): equivalent there, so not an independent gap), and to (K-slide-cl),
whose combinatorial
residue (K-slide-comb) is itself **refuted** class-wide by
§(K-slide-comb)'s fifth pass (covered sub-class named, every probed
member still discharged), plus the `P21`-type shapes, with
(K-wit)/(K-pitch-∞) as the weakest exact forms.**

## §(K-slide) — the slide-in transfer theorem: the `G°`-level limit is a proof carrier

Sibling of §(K-pitch), attacking the gap its Step 6 named; standing
notation inherited (split chain `b–v–a–c`, both ends hubs, `G′ = G − v +
ab`, `H = G′ − a`, `V_bc`, `T = ⟨C_ab, C_ac⟩`, the reciprocal twist `z`,
the pitch quadric `Q`). `G°` = the hub multigraph (vertices = hubs, one
edge per hub path, the split path's edge written `e₀ = bc`); a
**decoration** of the limit system = hub points, normals, one pencil
direction per slid path end, one meet-line point per length-2 path, and
free middle points for paths of length ≥ 4 — exactly the chart data the
slide does not destroy.

**Verdict (2026-08-04, third pass).** (i) The **slide-transfer theorem
(S1) is proven-informally**: the slide is an automorphism of the pencil
chart for every `ε ≠ 0`, the (normalized) `H`-row family is polynomial in
(chart data, `ε`) *including* `ε = 0`, and hence **one exact `ε = 0`
witness** — (W1) limit rows independent, (W2) `dim V_bc(limit) = 3`, (W3)
`z(limit)` defined, (W4) `Q(z_limit) ≠ 0` — proves `Q(z) ≢ 0` on the
habitat's chart. Step 6(d)'s rank-persistence proviso is **dissolved**:
nothing analytic is consumed (the `O(ε)` convergence record survives only
as numerics history, and rank constancy along the slide is now an
a-posteriori corollary, not a hypothesis). (ii) The limit carrier
extends to **arbitrary path lengths and arbitrary slide supports** (S2);
Step 6(e)'s two untested flanks — mixed path lengths on simple `G°`, and
hub–hub edges — are *inside* the framework and **witnessed**; the
hub-level serial-chain system equals the subdivision-level limit
(interior elimination, machine-asserted). (iii) **Witnessed members**
(S4): dbl-subdiv `K4` (all splits, by `Aut(K4)`), the wheel `W4` (**all**
splits: rim orbit + both spoke ends), `K5 − {01, 23}` at split `02` (both
ends), prism+diagonal at split `01` (both ends), the mixed-length `K4`
(both ends), the hub–hub-edge `K4` (both ends) — **23/23 hard witnesses
pitched** — so (K-pitch) closes at every one of these splits, and in
particular **the double-subdivision (K-tight) control habitats over `K4`
and `W4` close at every split**, with no side condition left. (iv)
**Parallel `G°`-edges obstruct the device at order 0** (S5): under the
full slide support the coincident chords force a stress on the
parallel-pair cycle (proven — a repeated line in a 6-hinge cycle), and
the probed reduced support does not rescue it (a circuit closes on a
theta sub-multigraph; exhibited). The sharpest uncovered *shape* is
**P21** — a parallel non-`bc` edge with no length-≤4 `bc`-companion —
reachable by neither the slide device nor the companion forms. The
class-uniform residue is **(K-slide-cl)** (Step 5) — attacked in
**§(K-slide-cl)** (fourth pass, 2026-08-04): the geometry is discharged
by the tetrahedral collapse and the residue reduces to the purely
combinatorial **(K-slide-comb)** — which **§(K-slide-comb)** (fifth pass,
2026-08-05) then **refutes** class-wide (5-chromatic and
acyclicity-obstructed `G°` both occur in the class), leaving
(K-slide-cl) **open** with a named covered sub-class (all probed splits
included) and the flanks located; its packing half is uniform and proven
there ((C6)).

**What would change this.** *For (S1):* an error in the
automorphism/polynomiality argument — refutable by a habitat whose chart
pitch vanishes identically while a (W1)–(W4) witness exists (the theorem
says none can). *For the member closures:* nothing short of that — each
rests on exact certificates plus (S1). *For the residue:* (K-slide-comb)
is now settled (refuted, §(K-slide-comb)), so what would move
(K-slide-cl) is a decoration scheme reaching that section's Step-D5
flanks, or a class argument on the generic pure condition of the limit
system; and, separately, any local mechanism for `P21`-type shapes.

### Step 1 — (S1): the slide-transfer theorem

Fix the habitat, the split, and a **slide support** `Σ`: any set of
single-panel interiors of `H` (each `x ∈ Σ` is adjacent to exactly one
hub `h_x`, its only chart constraint `pt(x) ∈ Π(h_x)`). For `ε ∈ K` let
`slide_ε` fix every chart coordinate except `pt(x) ↦ pt(h_x) + ε·(x₀ −
pt(h_x))` for `x ∈ Σ`.

> **Theorem (S1).** Suppose one exact chart point `data₀` satisfies, at
> its `ε = 0` limit line system: **(W1)** the `H`-rows are independent
> (`dim ker = 6|V_H| − 5|E_H|`; `= 9` at every tight member), **(W2)**
> `dim V_bc = 3`, **(W3)** the two `T`-conditions are independent on
> `V_bc`, **(W4)** `Q(z) ≠ 0`. Then `Q(z) ≠ 0` on a dense open subset
> of the pencil chart of `G′`.

*Proof.* (a) For `ε ≠ 0`, `slide_ε` is an **automorphism of the chart**:
it maps each panel `Π(h_x)` to itself bijectively (an affine scaling
about `pt(h_x)` inside the plane) and touches no other coordinate's
constraint. (b) Choose per-edge line representatives polynomial in
`(data, ε)`: for a hub-incident hinge `(h, x)` with `x ∈ Σ`, `x̂(ε) = ĥ +
ε·(x₀ − pt(h), 0)` gives `ĥ ∧ x̂(ε) = ε·(ĥ ∧ x̂₀)` — the hinge line
**never moves along the slide**; take the constant representative `ĥ ∧
x̂₀` (at `ε = 0` it reads as the pencil line at `pt(h)` toward `x₀`).
For every other hinge take `p̂(ε) ∧ q̂(ε)`; at `ε = 0` a slid–slid hinge
becomes the hub **chord**, a slid–fixed hinge the hub-to-point line, all
others their original lines. Off a proper closed set every
representative is nonzero at every `ε`, `0` included. (c) Encode `m(u) −
m(w) ∈ ⟨C_e⟩` by the 15 minor rows `(m(u) − m(w))_i (C_e)_j − (m(u) −
m(w))_j (C_e)_i` (same kernel as the 5-row perp form): the stacked
matrix `R(data, ε)` is **polynomial**, and its kernel depends only on
the projective lines — so for `ε ≠ 0` it is the `H`-motion space at the
chart point `slide_ε(data)`, while `T` is constant (`a, b, c` are never
slid). (d) Let `U ⊆ chart × 𝔸¹` be the locus where `rank R` and
`rank [R; P]` (`P : m ↦ m(b) − m(c)`) attain their absolute bounds
(`5|E_H|` resp. `6|V_H| − 6`; the latter because trivial twists always
lie in `ker [R; P]`, so (W2)'s `dim V_bc = 3` under (W1) says exactly
`ker [R; P]` = the trivial twists) and the `2 × 3` matrix of the
`T`-conditions on `V_bc` has rank 2. These are maximal-rank conditions on polynomial
matrices, so `U` is **open**, and (W1)–(W3) say precisely `(data₀, 0) ∈
U`. On `U`, `dim V_bc ≡ 3`, fixed cofactor formulas give a basis
rational in `(data, ε)`, and `z`, `Q(z)` are rational with `{Q(z) = 0}`
closed. (e) Suppose the chart function `data ↦ Q(z)` vanished
identically wherever defined. The chart is irreducible (a tower of
affine-linear fibers: free hub points, normals in hub-dependent linear
subspaces, interiors in panels / meet lines / free space), so `U` is
irreducible; by (a)+(c), `Q(z) = 0` on `U ∩ {ε ≠ 0}` — dense open in `U`
since `U` is open nonempty, hence not inside `{ε = 0}` — so `Q(z) ≡ 0`
on `U`, contradicting (W4) at `(data₀, 0)`. ∎

Three remarks. **(i) Nothing analytic survives**: no `ε → 0` limits, no
constant-rank family, no convergence — and no target rank, realization
count, or stress at the witness: (W1)–(W4) are linear-algebra
certificates on the limit lines alone. **(ii) Rank persistence is now a
corollary**: (W1) certifies the absolute row-count bound at `ε = 0`, and
rank is subgeneric only on a closed set, so it is constant along the
slide off finitely many `ε` — Step 6(c)'s observed `9 → 9` is proven
a-posteriori and consumed nowhere. **(iii) The support is a free
parameter**: the proof runs verbatim for any `Σ`; smaller supports leave
more surviving chart coordinates in the limit data (less locality, same
validity) — the freedom Step 5 exploits and (S5) tests.

### Step 2 — (S2): the general limit carrier on `G°`

Per hub path `[u, x₁, …, x_{ℓ−1}, w]` (with the ≥3-length ends in `Σ`),
the limit lines are:

    ℓ = 1 : (u∧w)                      — hub-hub hinge (mutual-panel data)
    ℓ = 2 : (u∧x₁, x₁∧w)               — x₁ on the meet line; not slid
    ℓ = 3 : (P_u, u∧w, P_w)            — the serial triple of Step 6(b)
    ℓ = 4 : (P_u, u∧x₂, x₂∧w, P_w)     — x₂ free; not slid
    ℓ = 5 : (P_u, u∧x₂, x₂∧x₃, x₃∧w, P_w)

with `P_u` the (constant) pencil line at `u` toward the slid end. All of
it is `G°`-local decoration data, and the decoration space is an
irreducible linear-fiber tower, so per member "one witness ⟹ generic
decorations" holds for the limit system itself too. **Interior
elimination is exact**: every interior has degree 2, so relative twists
telescope, and the hub-level system — bodies at hubs only, one
constraint `m(u) − m(w) ∈ span(chain lines)` per `G°`-edge — has the
same `V_bc` as the subdivision-level limit (machine-asserted at the `K4`
and mixed members). Step 6(e)'s flanks are therefore *inside* the
framework: mixed lengths contribute longer serial chains with surviving
free points, hub–hub edges contribute their own hinge as a 1-member
chain.

### Step 3 — (S3): what a witness closes

Per split, the battery pairs each `ε = 0` witness with an `ε = 1`
**transfer certificate**: one exact target-rank `dim R_a = 1` seed
passing (T1)–(T3) with the (T2) side conditions and `Q(r) ≠ 0`. The
certificate alone already exhibits an escaping seed (§(K-tight)'s
per-seed criterion, via (T3)) — by Step 0's one-witness logic every
probed split is *individually* closed that way, `P21`'s included. What
(S1) adds is **where the argument lives**: the witness computation runs
on the `G°`-level limit system — pencil lines, chords, banded serial
Grams, the bracket-friendly objects — so a *class-uniform* proof can now
be attempted on the structured limit carrier and transferred to every
chart at once. That is the program (K-slide-cl) names.

### Step 4 — (S4): the battery (all exact, `kslide.py`)

Every member is tight (`def = 0`, asserted), both split-chain ends hubs.
"hnoRigid" = no proper rigid branch-union (NT21-standard `2^paths`
sweep). Witness = hard (W1)–(W4); certificate = (T1)–(T3) + `Q(r) ≠ 0`.

| member (`G°`, lengths) | \|V\| | hnoRigid | splits covered | witnesses |
|---|---|---|---|---|
| dbl-subdiv `K4` (all 3) | 16 | yes | all (Aut-transitive on directed edges) | 3 + (S2) check |
| `W4` wheel, rim (all 3) | 21 | yes | rim orbit, both ends (`0↔1, 3↔2`) | 2 |
| `W4` wheel, spoke (all 3) | 21 | yes | both spoke ends (2 runs) | 2 + 2 |
| `K5 − {01, 23}`, split `02` (all 3) | 21 | yes | both ends (`0↔2, 1↔3` autom.) | 2 |
| prism + diagonal `04`, split `01` (all 3) | 26 | yes | both ends (2 runs) | 2 + 2 |
| `K4` mixed `(3,4,2,3,3,3)` | 16 | yes | both ends (2 runs) | 2 + 2, (S2) check |
| `K4` + hub-hub edge `23`, `(3,1,4,4,3,3)` | 16 | yes | both ends (2 runs) | 2 + 2 |
| `W5` wheel (all 3) † | 26 | yes | the `e₀` split of §(K-flank) *F1* | 1 (full support) |
| `W7` wheel (all 3) † | 36 | yes | ibid. | 1 (full support) |
| `K4`, lengths `(1,1,3,5,3,5)` † | 16 | yes | ibid. | 1 (full support) |

23/23 witnesses pitched; 12/12 certificates passed ((T1)–(T3) re-validated
at every new habitat) — those two figures are the original seven members'
record. Consequences: **(K-pitch) holds at every listed
split, proven-informally** ((S1) + (S3)); the `K4` and `W4` rows close
their habitats at *every* split (orbit-complete), so the
double-subdivision (K-tight) control class over `K4`/`W4` is **closed
with no residual side condition**.

† **Three members added 2026-08-05 by §(K-flank) *Step F6*** (`flanks.py
--limit`; 3/3 further witnesses). Each carries a full **full-support**
(W1)–(W4) limit witness at *generic, non-aligned* decorations, seed 101 —
(W1) `dim mot = 9`, (W2) `dim V_bc = 3`, (W3) `z` defined, (W4)
`Q(z_lim) ≠ 0` — so by (S1) + (S3) each of those splits is closed
**through the `G°`-level carrier**, not merely by an `ε = 1` certificate.
The wheels are §(K-flank)'s high-concurrency probes (`Δ(G°) = 5, 7`:
five resp. seven concurrent coplanar hinges at one body). **The third
row is the significant one:** `K4` `(1,1,3,5,3,5)` is one of the **438
menu-blocked** shapes of §(K-slide-comb) *Step D5* item 3, so at that
shape the menu obstruction is strictly *stronger than the slide device
requires* — evidence that the 438-shape flank is (at least partly) a
defect of the **dictionary**, not of the device, consistent with (C7)'s
partial rescue.

### Step 5 — (S5): the parallel-edge obstruction, and the residue

**Full support (proven).** For a `k`-hinge body cycle, telescoping gives
`#stresses = 6 − rank{lines}`. Two parallel length-3 chains slide to
serial triples `(P_u, C, P_w)`, `(P_u′, C, P_w′)` **sharing the chord**
`C`: their union is a 6-hinge cycle with ≤ 5 distinct lines — one stress,
always. (Machine: the exhibited stress sits exactly on the parallel
pair, 6 edges, line rank 5.) So (W1) is unattainable at parallel
`G°`-edges under the full support, for *every* decoration.

**Reduced supports (probed, obstructed).** Hub-incident lines never move
along any slide ((S1)(b)), so both parallel chains keep pencil-line ends
at the shared hubs regardless of support, and the limit concentrates
chords through hub points. At **P21** — `G°` = **`K4` with `23` doubled**
(7 hub paths, `Σℓ = 24`), lengths `(3; 3,3; 4,5,3,3)`, `|V| = 21`,
residual-shaped (the parallel pair is a rigid `C₆`) — leaving one parallel
chain fully
unslid still yields exactly one limit stress, now supported on the theta
sub-multigraph `{12, 13, 23a, 23b}` (12 edges, line rank 6; exhibited).
Half-measures are worse: a half-slid chain's middle line passes through
the hub point and rebuilds the short circuit. (**`G°` corrected
2026-08-05**, §(K-flank) *F1*: this shape read "`K4 − 02` plus doubled
`23`" here, which supplies only six hub paths and so cannot carry the
seven-entry length list above; `kslide.flanks()` builds all six `K4`
edges plus a second `23`, and every figure in this paragraph is that
shape's. §(K-flank) *F5(d)/(e)* then exhibits the **same** theta-circuit
stress at `ε = 1`, on a nonempty locus of the pencil chart itself — so
this obstruction is not confined to the limit.)

**Division of labor, updated from Step 6(e)** — *and revised 2026-08-05
by §(K-Λ); the gap map's `P21` row is the canonical form.* `bc`-parallel
shapes go to the companion forms (Steps 5/5b: the monomial at `ℓ = 3`;
at `ℓ = 4` **(K-wit)**, since §(K-Λ) shows the companion form there is
*equivalent* to it rather than an independent gap). At `ℓ = 5, 6` **the
(T5) frame is REFUTED as the route** (§(K-Λ) *Step 7*), so those shapes
need something else, none identified — a refutation of the *argument
shape*, not of the conjecture or of their closability.
Non-`bc`-parallel shapes with no
length-≤4 `bc`-companion — exemplar `P21` — are covered by **neither**
mechanism: closable per-split by Step-0 seed logic (P21's certificate
seed escapes), but with no `G°`-local argument. The named residue:

> **(K-slide-cl)** *(class-uniform; supersedes the per-member (K-slide),
> which is now witness-decidable and discharged at every probed
> member)* — for every tight/(K-res) habitat shape `(G°, ℓ, e₀)` without
> parallel `G°`-edges, generic decorations of the slide-in limit system
> satisfy (W1)–(W4).

**As stated (i.e. at the full support) this is REFUTED** — §(K-pure)
(PC-OBS), 2026-08-05: the chord obstruction kills (W4)/(W3) at every
decoration of three `K5` class shapes and of θ(3,4,5). The repaired form
quantifies **`∃Σ`** over slide supports (remark (iii)'s freedom, now the
load-bearing parameter) and is open.

Every attempted member closed at the first sampled decorations; a class
proof should factor the limit system's pure condition along `G°`'s
structure (the White–Whiteley 1987 mechanism, now aimed at a decorated
bar-and-body-like object with only pencil lines and chords). **That
factoring is carried out in §(K-slide-cl)** (the tetrahedral collapse),
which reduces (K-slide-cl) to the purely combinatorial
**(K-slide-comb)** — solved by search at every probed member, but
**refuted class-wide** in §(K-slide-comb) (fifth pass). So the collapse
is a *sub-class* device, and (K-slide-cl) is open; §(K-slide-comb)
carries the uniform positive residue ((C6): the packing half always
works) and locates the two flanks a second-generation decoration would
have to reach.

### Verification

`notes/scripts/w4/kslide.py` (tracked; exact-ℚ, on top of `repin.py` /
`pitch.py`; every sampled object carries rank/dimension asserts).
Reproduce: `python3 notes/scripts/w4/kslide.py --k4 | --battery [0-3] |
--mixed | --flanks`. Per member it asserts: `def = 0`; the transfer
certificate ((T1)–(T3) via `pitch.transfer_probe`, internal asserts);
per witness (W1) `dim mot = 6|V_H| − 5|E_H|`, (W2) `dim V_bc(limit) =
3`, (W3) `z` defined, (W4) `Q(z_limit) ≠ 0` (hard everywhere except the
flank probes, which report); at `K4`/mixed the (S2) hub-level equality
of `V_bc` spans; at the parallel member the (W1) failure in both
supports with the stress's chain support and line rank printed.

**Confidence verdict: (S1) and the (S2) carrier proven-informally;
(K-pitch) at all 11 probed split-classes (7 members) proven-informally —
the `K4`/`W4` double-subdivision control habitats closed at every
split; the parallel-edge order-0 obstruction proven (full support) /
exhibited (reduced support); the uniform kernel still open — residue
(K-slide-cl), reduced by §(K-slide-cl) to (K-slide-comb) and then
**refuted** at that residue by §(K-slide-comb) (so (K-slide-cl) is open,
not conditional), + (K-Λ) + the `P21`-type shapes, with
(K-wit)/(K-pitch-∞) the weakest exact forms.**

## §(K-slide-cl) — the tetrahedral collapse: the class statement reduced to a combinatorial assignment problem (**reduction proven; the statement itself REFUTED as stated at the full support** — §(K-pure) (PC-OBS) — and its combinatorial antecedent separately refuted, see §(K-slide-comb); the `∃Σ`-repaired form is **OPEN**)

Sibling of §(K-slide), attacking the class-uniform residue its Step 5
named; standing notation inherited (`G°`, decorations, the split edge
`e₀ = bc` of length 3, witnesses (W1)–(W4), the limit-line dictionary of
(S2)). The route is the one §(K-slide) suggested — factor the limit
system along `G°`'s structure — made concrete by the **specialization
technique of White–Whiteley 1987** (the Theorem-2.18 proof: evaluate the
pure condition at an assignment of *one shared coordinate frame per
spanning tree*, so a single Laplace term survives), now run **inside the
decoration variety**, whose pencil/chord structure does not admit free
`k`-frame rows.

**Verdict (2026-08-04, fourth pass).** (i) The **collapse mechanism
(C1)–(C3) is proven-informally**: at a *tetrahedral collapse* decoration
— hubs placed on the four vertices of a coordinate tetrahedron by a
proper 4-coloring, panels/pencil directions/interior points chosen per
the transversal dictionary (C2) — every limit row becomes a scalar
difference equation in one of six basis-line coordinates, and
(W1)–(W2) become **pure combinatorics**: the six edge classes must be
forests, exactly three spanning trees and three two-component forests
each separating `b` from `c`; then `V_bc` = the span of the three
separating lines' opposite duals, and (W3)/(W4) close by an explicit
bracket monomial in `pt(a)` (C3). (ii) The **length dictionary is
complete** on the class (C0): tightness alone caps every path at length
6 (`def ≥ ℓ − 6`, interiors-as-singletons partition), and under
`hnoRigid` a length-6 path is impossible too (its complement branch
union is tight, hence a proper rigid subgraph; 5848/5848 machine sweep)
— so `ℓ ∈ {1,…,5}`, exactly the range (C2) covers. (iii) The pure
tetrahedral scheme has one genuine obstruction, located exactly: a
**length-2 path forces a tetra point into both end panels**, and at the
mixed-length member this pincers against the neighbouring pencil planes
(every pt-mode assignment dies — proven by the finite case check, C4);
the **meet-plane extension** (C4) repairs it (interior at
`M ∩ π(i,j,m)`, panels freed, one non-basis row absorbed by the exact
witness). (iv) With the extension, **the assignment problem is solved
and the collapse witness verified at all 7 probed members** — the full
§(K-slide) battery (`kslidecl.py`, exact-ℚ; 6 pure, 1 extended) — so
(K-slide-cl) holds at every one of those splits, and the implication
"**(K-slide-comb) at a shape ⟹ (K-slide-cl) at that shape**" is proven.
(v) **But (K-slide-comb) is now REFUTED as a class statement**
(§(K-slide-comb), 2026-08-05): two structural flanks — a 5-chromatic
`G°` (`K5` with all-`{3,4}` lengths) and shapes with no acyclic
4-colouring — sit in the class, and the pure dictionary is menu-blocked
at 438 of the 877 exhaustive `K4` shapes even where the colouring
premise holds. So **(K-slide-cl) is open**, covered exactly on the
solvable sub-class (all 7 battery members included); the packing half of
the residue is uniform and proven ((C6) there), and the dictionary's
length-4 entry — called "forced" in (C2) below — is **corrected** there.
(vi) **And (K-slide-cl) is now REFUTED as stated** (§(K-pure), 2026-08-05,
sixth pass): at the **full support** the slide-in limit fails (W4) — or
(W3) — at *every* decoration of three `K5` class shapes and of θ(3,4,5),
by the **chord obstruction (PC-OBS)**, an `R_3`-dependence mechanism
**independent** of (v)'s colouring refutation of the *antecedent*; the
two refutations are at different levels and must not be conflated. The
repaired statement quantifies **`∃Σ`** over slide supports, and in that
form it is open — with 5 of the 6 probed flank shapes now carrying
reduced-support witnesses (§(K-pure) *Step P7*).

**What would change this.** *For the mechanism (C1)/(C3)/(C4):* an error
in the transversal calculus — machine-asserted per edge per member
(`klein(L, C) = 0` for every assigned basis line against every chain
line), with the V_bc-structure and Gram identities asserted globally.
*For (C2):* its length-4 row "forced" is already known **wrong**
(§(K-slide-comb) Step D4, 12/12 exact witnesses); the `ℓ ∈ {1,2,5}`
rows have not been re-examined the same way and are the next suspects.
*For the class verdict:* only a decoration scheme with more than four
hub positions, or one admitting non-basis rows on long paths, can reach
the refuted flanks — see §(K-slide-comb) Step D5.

### Step C0 — the hub-level target, and dictionary completeness

By (S2), interior elimination is exact and the limit system is the
hub-level serial-chain system: bodies at the hubs of `G° − e₀`, one
constraint `m(u) − m(w) ∈ S_P := span(chain lines)` per edge `P`, i.e.
`6 − ℓ_P` scalar rows (for independent chain lines). Tightness
(`Σ_P ℓ_P = 6·c°(G°)`) makes the total row count `6|V°| − 9`, so
(W1) says the rows are independent (`dim mot = 9`), (W2) that the
kernel is trivial twists ⊕ a 3-dimensional `V_bc`.

Two elementary lemmas close the length bookkeeping:

- **(ℓ ≥ 7 is not tight.)** Putting a length-`ℓ` path's interiors in
  singleton parts and everything else in one part scores
  `6ℓ − 6 − 5ℓ = ℓ − 6`, so `def(G) ≥ ℓ − 6`: a tight graph has every
  path of length ≤ 6. (Machine: K4 lengths `(3;7,2,2,2,2)` has the
  tight count but `def = 1`.)
- **(ℓ = 6 forces a rigid complement.)** If `G` is tight with a
  length-6 non-split path, the branch union of all *other* paths has
  the tight count (`Σℓ` drops by `6 = 6·Δc°`), and any bad partition of
  it would lift to `G` at zero cost through the six interiors — so the
  complement is a proper **rigid** branch union and `hnoRigid` fails.
  (Machine: 5848/5848 tight W4-wheel shapes with a length-6 path fail
  `hnoRigid`.)

So on the tight-`hnoRigid` subclass `ℓ ∈ {1,…,5}` — the dictionary
below is complete. ((K-res) residual shapes waive `hnoRigid`, so they
may carry length-6 paths; those contribute **no** hub-level rows and
the mechanism is unchanged, but no parallel-free (K-res) member was at
hand to probe.)

### Step C1 — the six scalar systems

Let `E₁…E₄` be the vertices of a coordinate tetrahedron and
`L_ij := C(E_i ∨ E_j)` its six edge lines: a **basis** of `Λ²K⁴` with
`B(L_ij, L_kl) ≠ 0` iff `{i,j}, {k,l}` are **opposite** (disjoint). So
`x_L(v) := B(m(v), L)` are linear coordinates on twists, and a
constraint `m(u) − m(w) ∈ S_P` whose reciprocal space
`R_P := {ω : B(ω, C) = 0 ∀C ∈ S_P}` is *spanned by basis lines*
`A_P ⊆ {L_ij}` reads as the `|A_P|` scalar equations

> `x_L(u) = x_L(w)`, one per `L ∈ A_P`.

If every edge is basis-aligned this way, the whole hub-level system
splits into **six scalar graph systems**: for each basis line `L`, the
class `E_L := {P : L ∈ A_P}` constrains `x_L` to be constant on the
components of `(V°, E_L)`. Hence, exactly:

> **(C1)** rows independent ⟺ every class is a **forest**; then
> `dim ker = Σ_L c_L` (`c_L` = component count), and since
> `Σ_L (c_L − 1) = 3`: **(W1) ∧ (W2)** ⟺ three classes are spanning
> trees and three are two-component forests **each separating `b` from
> `c`**; in that case `V_bc = ⟨ opp-dual(L) : L separating ⟩` (the
> B-dual basis vector of `L_ij` is proportional to its opposite line).

This is the White–Whiteley tree-specialization structure: the surviving
"Laplace term" is the product of the six forest determinants, evaluated
inside the pencil-decoration variety rather than at free `k`-frame
rows.

### Step C2 — the transversal dictionary (which alignments the chart allows)

Color the hubs `φ: V° → {1,…,4}` **properly** (adjacent hubs distinct,
`φ(b) ≠ φ(c)` — `b, c` are non-adjacent in `G° − e₀` by
parallel-freeness, but (C3) needs their points distinct) and place
`pt(u) = E_{φu}`. Per edge `P = uw` of length `ℓ`, colors
`(i, j) = (φu, φw)`, the chain lines can be decorated so that `R_P` is
*exactly* a basis-line span (each claim = one transversal computation;
all machine-asserted per edge):

    ℓ = 1 : chord L_ij; panels of u, w both contain it (mutual-panel
            data).                     A_P = all five basis lines ≠ opp(ij)
    ℓ = 2 : interior at E_k (k ∉ {i,j}), forced into BOTH panels; chain
            (L_ik, L_kj).              A_P = {ij, ik, jk, opp(ij)}
    ℓ = 3 : P_u = Π(u) ∩ π(i,j,s), chord L_ij, P_w = Π(w) ∩ π(i,j,t).
                                       A_P = {ij, it, js}
    ℓ = 4 : middle at E_k, P_u ⊂ π(i,k,l), P_w ⊂ π(j,k,l) ({k,l} =
            complement).               A_P = {ij, opp(ij)}
    ℓ = 5 : middles at E_k and a generic point of π(i,j,k); pencil ends
            generic in their panels.   A_P = {ij}

**"Forced" was wrong at ℓ = 4** (§(K-slide-comb) Step D4, 12/12 exact
witnesses): a generic middle in a face plane `π(i,j,k)` with one end's
pencil line confined to that plane gives `A_P = {ij, xk}` for either
`x ∈ {i,j}`, so the length-4 menu is *every* 2-subset containing `ij`.
The ℓ = 5 row's uniqueness has not been re-examined the same way (and
with fully generic middles `R_P` need not be a basis line at all).

The ℓ = 3 computation is the exemplar: a line through `E_i` meets
`L_js` iff it lies in `π(i,j,s)`, so the class prescription *forces*
`P_u = Π(u) ∩ π(i,j,s)` — the transversal set of the serial triple is
`pencil(E_i, π(i,j,t)) ∪ pencil(E_j, π(i,j,s))`, spanning exactly
`⟨L_ij, L_it, L_js⟩`. (Same-color chords of different edges coincide as
lines; that is harmless — dependencies live inside classes, and classes
are forests.)

### Step C3 — (W3)/(W4) at the collapse: the bracket monomial, and finiteness of the local type

With separators `{L¹, L², L³}` and duals `D_s ∝ opp(L^s)`,
`Q|_{V_bc}`'s Gram is nonzero exactly on opposite dual pairs — so the
separator triple must contain **exactly one opposite pair** (no pair ⟹
`Q|_{V_bc} ≡ 0` ⟹ that witness fails (W4); two pairs don't fit in a
triple). Then `Q|_{V_bc}` has the serial-chain signature (rank 2), and
with `pt(a)` on the meet line `M = Π(b) ∩ Π(c)`, `z` is the cross
product of the rows `(B(D_s, C_ab))_s, (B(D_s, C_ac))_s` — 4-point
brackets. Exemplar (the type found at `K4`, separators
`{L₁₂, L₁₃, L₂₄}`, `φb = 1, φc = 2`; structural zeros from
`E₁ ∈ D₃ = L₁₃`, `E₂ ∈ D₂ = L₂₄`):

> `Q(z) = 2·[3,4,a,1]·[2,4,a,1]·[3,4,a,2]·[1,3,a,2]·[2,4,1,3]`

— a bracket **monomial** again (the Step-5 pattern one level up),
nonzero iff `pt(a)` avoids the four tetrahedron faces: generic on `M`.
Crucially, (W3)/(W4) depend only on the **local type** (separator
triple, `φb`, `φc`, the `b`/`c` panels and `pt(a)`) — *not* on the
shape — so their nonvanishing is a **finite** check over types, not
part of the per-shape combinatorics. (Machine corroboration: members
with the same type produce byte-identical `Q(z_lim)` under the same
panel draws.)

### Step C4 — the length-2 pincer, and the meet-plane extension

The ℓ = 2 alignment is the one dictionary entry that **constrains the
panels**: `E_k` must lie in both end panels. At the mixed-length member
(`K4`, lengths `(3;4,2,3,3,3)`) this is fatal: in either admissible
coloring, the forced panel point's color collides with the color of a
neighbouring ℓ = 3 edge's far end, degenerating that edge's pencil line
onto its chord (`E_j ∈ Π(u)` forces `P_u = Π(u) ∩ π(i,j,s) = L_ij` for
*every* `s`) — both colorings die, all pt-mode assignments fail (a
finite check, confirmed by exhaustive search). The repair keeps the
class structure and frees the panels:

> **(meet-plane mode)** place the ℓ = 2 interior at
> `x₁ = M_uw ∩ π(i,j,m)` (`m ∉ {i,j}`). Both chain lines then lie in
> `π(i,j,m)`, so `A_P ⊇ {ij, im, jm}` — three aligned rows — and the
> fourth row is non-basis ("extra"). The aligned kernel grows to
> `9 + z` (`z` = number of meet-plane edges, budget
> `Σ(c_L − 1) = 3 + z`), and the `z` extra rows must cut it back to 9
> with `dim V_bc = 3` — checked by the **exact witness itself** (which
> is all (S1) consumes; `V_bc ⊆ ⟨opp duals of separating classes⟩`
> remains a theorem and is asserted).

Local compatibility (part of the assignment problem): forced panel
points must avoid the far-end colors of ℓ = 3 edges at the same hub,
and each ℓ = 4 edge needs an admissible middle point
(`{k,l} ⊄ req(u) ∪ req(w)`).

### Step C5 — (K-slide-comb), what is proven, and the battery

> **(K-slide-comb)** *(the class-uniform residue; per shape a finite
> problem)* — for the shape `(G°, ℓ, e₀)`: there exist a proper
> 4-coloring `φ` of the simple graph underlying `G°` **+ e₀** (so
> `φb ≠ φc`) and per-edge choices (C2/C4: `k` or meet-plane `m` at
> ℓ = 2; `s, t` at ℓ = 3) satisfying the local compatibility rules,
> such that the six classes are forests with excess `3 + z`, at least
> three classes separate `b` from `c` (exactly three spanning trees +
> three separating 2-component forests when `z = 0`), the separating
> lines contain an opposite pair, and (for `z > 0`) the extra rows cut
> the aligned kernel exactly.

**Status: REFUTED as a class statement** — see **§(K-slide-comb)**, which
supersedes the "proven pieces" reading this step originally carried. Two
corrections belong here:

- The sparsity argument does give `|E(K)| ≤ 2|W| − 2` for every subgraph
  of an all-length-3 `G° + e₀`, hence 3-degeneracy and a greedy proper
  4-colouring — **but proper is the wrong invariant.** Every menu above
  contains `L_{ij}`, so `E_{L_ij}` swallows *all* `{i,j}`-coloured edges
  and `φ` must be **acyclic** (bicoloured subgraphs all forests); nothing
  in 3-degeneracy delivers that.
- At general lengths the colouring premise genuinely fails in the class:
  `χ(G°) = 5` occurs (`K5`, all-`{3,4}` lengths), and 4-colourable shapes
  with no acyclic 4-colouring occur.

The battery below is unaffected — each row is an exact witness and closes
its split by (S1). (`kslidecl.py`, all exact-ℚ; same members as
§(K-slide) Step 4):

| member | mode | separating classes | witness |
|---|---|---|---|
| dbl-subdiv `K4` | pure | {12},{13},{24} | (W1)–(W4) ✓ |
| `W4` rim split | pure | {12},{14},{23} | ✓ |
| `W4` spoke split | pure | {12},{14},{23} | ✓ |
| `K5 − {01,23}`, split 02 | pure | {12},{13},{24} | ✓ |
| prism + diagonal, split 01 | pure | {12},{14},{23} | ✓ |
| `K4` mixed `(3;4,2,3,3,3)` | meet-plane (z = 1) | {12},{13},{24} | ✓ |
| `K4` + hub-hub edge | pure | {12},{14},{23} | ✓ |

Each collapse witness realizes as an honest chart point (interiors
along the chosen pencil rays, `pt(a) ∈ M` — the chart's own
constraints are exactly the dictionary's), so (S1) applies verbatim:
each row of the table *re-closes* that split by a structural witness.
What the class program stands or falls with is (K-slide-comb) — now
**refuted** as a class statement, with the surviving positive content
((C6), (C7)) and the located flanks in §(K-slide-comb).

### Verification

`notes/scripts/w4/kslidecl.py` (tracked; exact-ℚ, on top of
`repin.py`/`pitch.py`/`kslide.py`; every sampled object carries
rank/dimension asserts). Reproduce:
`python3 notes/scripts/w4/kslidecl.py --k4 | --battery [0-3] | --mixed |
--hubhub | --scope`. Per member it asserts: `def = 0`; per edge the
chain-span dimension, independence of the assigned basis lines, and the
transversal identities `klein(L, C) = 0`; globally (W1) (subdivision-
level row independence), (W2) with the `V_bc` structure identity
(equality to the separators' opposite-dual span in pure mode,
containment in extended mode) and the Gram-structure identity (pure
mode), (W3), and (W4) `Q(z_lim) ≠ 0`. `--scope` validates both
dictionary-completeness lemmas (the `def = ℓ − 6` exemplar; the
exhaustive length-6 sweep).

**Confidence verdict: the collapse mechanism (C1)/(C3)/(C4) and the
dictionary-completeness lemmas proven-informally; (C2)'s per-entry
transversal identities proven-informally but its length-4
*exhaustiveness* REFUTED (§(K-slide-comb) Step D4); the seven battery
splits closed by exact witness + (S1); and (K-slide-cl) itself
OPEN — its combinatorial antecedent (K-slide-comb) is refuted
class-wide (§(K-slide-comb)), so the collapse covers exactly the
solvable sub-class (all 7 members, hence the `K4`/`W4` control
habitats). The (K-res) length-6 flank remains unprobed.**

## §(K-slide-comb) — the combinatorial residue: **refuted as stated**, and the packing half made uniform

Sibling of §(K-slide-cl), settling the residue its Step C5 named. Standing
notation inherited (`G°`, lengths `ℓ`, split edge `e₀ = bc` of length 3, the
six basis lines `L_ij` of the coordinate tetrahedron, the classes `E_L`, the
menus `A_P`, witnesses (W1)–(W4)). Throughout `n = |V°|` and
`E° = E(G°) ∖ {e₀}`; **class shape** means exactly what the §(K-slide)
battery certifies — `G°` simple with min degree ≥ 3, the subdivision `G`
tight (`def = 0`, hence 5/6-sparse on every subgraph) and `hnoRigid`, both
`e₀`-ends hubs.

> **Label scoping.** The `(C…)` labels below continue §(K-slide-cl)'s
> `(C0)`–`(C5)` run, so this section's **(C6)** (the unrestricted packing) and
> **(C7)** (the length-4 menu repair) belong to the *collapse* family. They are
> unrelated to the identically-numbered **(C7)/(C8)** of
> `notes/Pencil-W4-informal.md` §(SAFE-RES) / §`hnoGood'`
> vacuity, which are the *W4 residual structure theorem*'s claims — the ones the
> route-3(b) adjudication is pinned on. Cite either by section, never by bare
> number.

**Verdict (2026-08-05, fifth pass).**

(i) **(K-slide-comb) is REFUTED as a class statement**, at two *structural*
flanks — both exhibited at explicit class members with **all lengths in
`{3,4}`**, so `G` is triangle-free with singleton closed hub-neighbourhoods
and the `hcard`/`htf` side conditions the (K) consumer carries
(`hasGenericPencilRealization_of_independent_pencilRow_target`,
`Escape.lean:186`) hold outright — read off `Graph.closedHubNbhd`'s body
(`Motive.lean:82`: the *pencil hubs* among `v` and its neighbours): with every
`ℓ ≥ 3`, a hub's neighbours are all degree-2 interiors, so
`closedHubNbhd u = {u}`, an interior's is at most its two hub neighbours, and
the girth is `≥ 6`:

- **the 5-chromatic flank (robust).** `G° = K5` with lengths
  `(3,3,3,3,4,4,4,4,4,4)` is tight + `hnoRigid` (`|V| = 31`; 84 of the
  all-`{3,4}` assignments qualify **under this section's convention** — the
  count is convention-dependent, reconciled 2026-08-05 in §(K-flank) *F1*:
  **210** = `C(10,4)` all-`{3,4}` assignments with `Σℓ = 36` are class shapes,
  every one of them, `hnoRigid` never failing here; **84** = `C(9,3)` of those
  have the *designated* split edge `(0,1)` at length 3, which is what
  `kslidecomb.py` counts, while `flanks.py --strata` takes `e₀` := the first
  length-3 edge — as `--k4full` does — and so reports all 210. Both figures are
  right under their own convention), and `χ(K5) = 5`. A **proper** colouring
  is forced for *any* tetrahedral decoration, not merely for the (C2)
  dictionary: if `pt(u) = pt(w)` on a hub path of length `ℓ`, its (S2) limit
  chain spans `< ℓ` (machine-checked at every `ℓ ∈ {1,…,5}`; at `ℓ ∈ {1,3}`
  the chord is `0`), so by the serial-chain count of §(K-slide) Step 5 the
  path carries a stress and (W1) fails. Hubs live at four points, so
  `χ(G°) ≤ 4` is *necessary* — and it fails in the class. (By **Brooks'
  theorem**, `χ(G°) ≥ 5` forces `G° = K5` or `Δ(G°) ≥ 5`, so this flank is
  exactly characterised.)
- **the acyclicity flank.** Every menu of (C2)/(C4) contains
  `L_{φu, φw}`, so `E_{L_ij}` contains **all** of `E°`'s `{i,j}`-coloured
  edges; since every class must be a forest, `φ` must be an **acyclic**
  colouring — every bicoloured subgraph a forest — not merely proper.
  Among the 23 hub graphs with `|V°| ≤ 6` (simple, connected, min degree
  ≥ 3), four are 4-colourable but have **no** acyclic 4-colouring; the
  6-vertex 11-edge one carries all-`{3,4}` tight + `hnoRigid` lengths
  (`|V| = 31`) and admits no admissible `φ` **even after `e₀` is deleted**
  (deleting `e₀` does rescue one of the four — the octahedron, whose separate
  and deeper failure is Step D3 — but not this one). So
  Step C5's "proven piece" (5/6-sparsity ⟹ 3-degeneracy ⟹ greedy
  4-colouring) does **not** discharge the colouring premise: *proper* is the
  wrong invariant, and acyclic 4-colourability is not implied by
  3-degeneracy. (Acyclic colouring in **Grünbaum**'s sense — *Acyclic
  colorings of planar graphs*, Israel J. Math. **14** (1973) 390–408,
  DOI 10.1007/BF02764716.)

(ii) **The packing half is uniform and proven — (C6).** Strip the menus and
ask only for the packing: assign each `P ∈ E°` a set of `6 − ℓ_P` of the six
labels so that three classes are spanning trees of `G° − e₀` and three are
2-component forests separating `b` from `c`. Equivalently: **three bases of
`M(G°)/e₀` plus three bases of `M(G°) ∖ e₀`, with `P` used `6 − ℓ_P` times.**
This is a matroid-union / base-packing question, and **Edmonds' matroid-
partition min-max hypothesis for it is exactly 5/6-sparsity of `G`** — so it
holds at **every** class shape (Step D1; proof below, and the min-max
inequality plus an explicit packing re-verified at every shape any driver
touches — 877 exhaustive `K4` + 48 sweep + 7 battery + the flanks). The
forest/separator structure is therefore *never* the obstruction;
the menu is. This also settles the second sub-question Step C5 posed: yes,
matroid-flavoured — but the constrained problem is matroid **intersection**,
not union (Step D2).

(iii) **(C2)'s length-4 entry is not "forced" — a correction.** With the free
middle placed generically in a face plane `π(i,j,k)` and one end's pencil line
confined to that plane, `R_P = ⟨L_ij, L_xk⟩` for either `x ∈ {i,j}` — 12/12
exact witnesses. So the length-4 menu is **all five** 2-subsets containing
`L_ij`, not just `{L_ij, L_opp(ij)}`. That repair alone lifts the exhaustive
`G° = K4` coverage from **439/877 to 702/877** and **rescues** the third
(non-structural) flank below. It is the natural continuation, named **(C7)**.

(iv) **Coverage, measured.** Menu-solvability of the pure dictionary is far
from class-wide even where the colouring premise holds: on the exhaustive
`G° = K4` stratum, **439 of 877** class shapes solve — and all **438**
failures have a satisfiable colouring premise, so at `K4` the obstruction is
purely the menu. On the `|V°| ≤ 5` sweep, 18/48. The seven §(K-slide) battery
members all solve (control, 7/7), and the *only* all-lengths-`≥ 3` `K4` shape
is `(3,3,3,3,3,3)` — tightness forces it — which solves. So the tetrahedral
collapse covers a neighbourhood of the all-length-3 stratum
(`|E°| + 1 = 2n − 2`) and thins out as `G°` densifies, because tightness
(`Σℓ = 6(m − n + 1)`) then forces long paths, whose menus are smallest.

**Consequence for (K-slide-cl).** The implication "(K-slide-comb) ⟹
(K-slide-cl) at that shape" is untouched and still proven; what changes is
that its antecedent is now **known false** at explicit class members. So
(K-slide-cl) reverts to **open**, with the covered sub-class named
(every shape where the assignment problem — pure or (C7)-repaired — is
solvable, including all 7 battery members and hence the `K4`/`W4` control
habitats) and the uncovered flanks located (`χ(G°) ≥ 5`; no acyclic
4-colouring; plus the residual menu failures).

**What would change this.** *For the refutation:* an error in class
membership of the exhibited shapes — they are certified by the same
`def = 0` + `hnoRigid` + hub-ends + parallel-free criterion as the battery,
and additionally satisfy `hcard`/`htf`; a genuine further habitat condition
excluding `K5`-shaped or `Δ ≥ 5` hub graphs would blunt the 5-chromatic
flank (none is known — the L7b consumer's conditions are exactly
`hcard`/`htf`, both satisfied). *For (C6):* a class shape whose min-max
inequality fails — impossible by the Step-D1 proof unless 5/6-sparsity
fails, i.e. unless the shape is not tight. *For the route:* a repaired
dictionary (C7) that keeps `L_ij` mandatory can never beat the acyclicity
flank, and no tetrahedral decoration can beat the 5-chromatic flank — so a
class proof needs either a **basis configuration with more than four hub
positions**, or a decoration admitting **non-basis ("extra") rows on long
paths** — the (C4) meet-plane trade, generalized — or it must abandon the
collapse and work with the generic pure condition.

### Step D0 — the residue as pure combinatorics

By Step C0 the hub-level limit system has `6|V°| − 9` rows and edge `P`
contributes `6 − ℓ_P` of them; by (C1) an aligned decoration splits it into
six scalar systems indexed by the basis lines, with `E_L = {P : L ∈ A_P}`.
So the residue is exactly a **multiplicity-weighted 6-fold forest packing of
`G° − e₀` with a per-edge legal menu**:

- **count.** `Σ_{P∈E°}(6 − ℓ_P) = 6(m−1) − (Σ_{E(G°)}ℓ − 3) = 6n − 9`
  using tightness `Σℓ = 6(m − n + 1)`, matching Step C0's row count exactly.
- **(W1)** ⟺ every `E_L` is a forest; then `Σ_L (c_L − 1) = 3`.
- **(W2)** ⟺ exactly three classes separate `b` from `c` — which, given the
  excess-3 budget, forces three spanning trees plus three 2-component
  separating forests, and `V_bc = ⟨opp-dual(L) : L separating⟩`.
- **(W4)** ⟺ the separator triple contains an opposite pair (C3); **(W3)/(W4)
  otherwise depend only on the local type**, so they are a finite check, not
  part of the combinatorics (C3).

Two reformulations do the work below. First, a **separating class `E_L` with
`c_L = 2` and `b|c` separated is the same thing as `E_L ∪ {e₀}` being a
spanning tree of `G°`** — i.e. `E_L` is a *base of `M(G°)/e₀`*; a spanning
tree class is a *base of `M(G°) ∖ e₀`*. Sizes check:
`3(n−2) + 3(n−1) = 6n − 9`. Second, the **menu** is what makes the problem
hard, and it is worth naming what it forbids: for `P` coloured `{i,j}`,
`L_ij ∈ A_P` always, and every other member of `A_P` shares a colour with
`{i,j}` **except** `opp(ij)`, which is reachable only at `ℓ ∈ {2 (pt-mode),
4}`. So class `E_{pq}` can only receive edges that *touch* `p` or `q`, plus
`opp(pq)`-coloured edges of length 2 or 4 — the **starvation bound**
computed in Step D3.

### Step D1 — (C6): the packing half is never the obstruction

> **(C6)** *(proven-informally)* — for **every** class shape there exist
> `A_P ⊆ {L_ij}` with `|A_P| = 6 − ℓ_P` such that three classes are bases of
> `M(G°) ∖ e₀` and three are bases of `M(G°)/e₀` (hence 2-component forests
> separating `b|c`), and the three separating labels may be chosen to contain
> an opposite pair.

*Proof.* Take the ground set `Ω` with `6 − ℓ_P` parallel copies of each
`P ∈ E°` (`|Ω| = 6n − 9`) and the six matroids `M₁ = M₂ = M₃ = M(G°)/e₀`,
`M₄ = M₅ = M₆ = M(G°) ∖ e₀` (ranks `n−2`, `n−1`; `G°` is 2-edge-connected on
the stratum, so `G° − e₀` is connected — and the driver's *explicit* packing
re-certifies that shape by shape, since a spanning tree of a disconnected
`G° − e₀` would not exist). By **Edmonds' matroid-partition theorem** the
union has rank
`min_{T ⊆ Ω}(|Ω ∖ T| + Σ_i r_i(T))`, and since each `r_i` depends only on
the support of `T`, the minimum is attained at a union of parallel classes,
i.e. at some `F ⊆ E°`. So `Ω` is partitionable iff

> `Σ_{P∈F}(6 − ℓ_P) ≤ 3·r_{M/e₀}(F) + 3·r_{M∖e₀}(F)` for every `F ⊆ E°`.

Write `W = V(F)`, `k` = number of components of `(W, F)`. Then
`r_{M∖e₀}(F) = |W| − k`, and `r_{M/e₀}(F) = |W| − k` unless `b, c` lie in the
**same** component of `F`, in which case it is `|W| − k − 1`. Now
5/6-sparsity of `G` says, for any branch union `F′` spanning `W′` and
connected, `5·Σ_{F′}ℓ ≤ 6(|W′| + Σ_{F′}(ℓ−1) − 1)`, i.e.

> `Σ_{P∈F′}(6 − ℓ_P) ≤ 6(|W′| − 1)`.

*Case `b ≁ c` in `F`:* sum that over the `k` components — the requirement is
exactly `Σ_F (6−ℓ_P) ≤ 6(|W| − k)`. ✓
*Case `b ∼ c` in `F`,* say in component `F₀` on `W₀`: the requirement carries
an extra `−3`, i.e. `Σ_{F₀}(6−ℓ_P) ≤ 6(|W₀| − 1) − 3`. Apply the sparsity
inequality to `F₀ ∪ {e₀}` — still connected, still spanning `W₀`, and `e₀`
contributes `6 − ℓ_{e₀} = 3`: `Σ_{F₀}(6−ℓ_P) + 3 ≤ 6(|W₀| − 1)`. ✓ (The
`−3` is supplied *exactly* by `ℓ_{e₀} = 3`, the same 3 that is `dim V_bc`.)
Finally, partitioning `Ω` gives six independent sets of total size
`6n − 9 = 3(n−2) + 3(n−1)`, and each part is capped by its matroid's rank —
so every part is a **base**, which is the claim. Two parallel copies of `P`
can never share a part (they are parallel in a graphic matroid), so each `P`
lands in `6 − ℓ_P` *distinct* classes. The label names are ours, so the
separator triple can be any triple containing an opposite pair. ∎

Remarks. **(a)** Only 5/6-sparsity is consumed — not `hnoRigid`, not
parallel-freeness, not the colouring. **(b)** This is the same machinery the
project has landed: Phase 12's vendored matroid union
(`Matroid/Constructions/{Submodular,Union}.lean`), Phase 13's
Tutte–Nash-Williams packing (`BodyBar/TreePacking.lean`), Phase 14's k-fold
cycle-matroid union (`BodyBar/KFrame.lean`). The sparsity ⟺ arboricity
coincidence above is literally the Nash-Williams condition for the weighted
multigraph `Ĝ` (`P` with multiplicity `6 − ℓ_P`). **(c)** So a route that
needed only (C6) would be *in reach of landed machinery*. The route that is
actually needed is not.

### Step D2 — the menu: matroid intersection, and where even that stops

Fix a colouring and a separator triple. At lengths `ℓ ∈ {1, 3, 5}` — and at
`ℓ = 4` with the (C7) repair of Step D4 — the menu is the **base family of a
partition matroid** on the pairs `(P, L)`:

| `ℓ` | menu | partition parts |
|---|---|---|
| 1 | all five `L ≠ opp(ij)` (forced) | five singletons |
| 3 | `{ij, it, js}`, `s,t ∈ comp` | `{ij}`; `{ik, il}`; `{jk, jl}` |
| 4 (C7) | `{ij, X}`, `X` any other basis line | `{ij}`; the other five |
| 5 | `{ij}` (forced) | one singleton |

Total capacity `Σ_P (6 − ℓ_P) = 6n − 9`, so a maximum common independent set
of that size saturates every part. Hence **(W1) ∧ (W2) at a fixed colouring
and separator triple is exactly a common-base problem for a partition matroid
and the direct sum `⊕_{L∈S} M(G°)/e₀ ⊕ ⊕_{L∉S} M(G°)∖e₀`** — matroid
intersection, decidable in polynomial time with an Edmonds min-max
obstruction certificate. `Matroid.Intersection` (`exists_common_ind`,
`matroid_intersection_minmax`) is live and sorry-free in the
`apnelson1/Matroid` dependency, so this is *expressible* in the project's
setting — but it decides a per-(shape, colouring, triple) question, and the
outer quantifier over colourings is not matroidal.

Where it stops: **length-2 edges.** The (C2)/(C4) options at `ℓ = 2` are
`{ij, ik, jk, kl}` (pt-mode, 4 aligned rows) and `{ij, im, jm}` (meet-plane,
3 aligned + 1 extra) — different sizes, so not a matroid base family at all;
and even restricted to pt-mode the two options differ by a **2-element**
exchange (`{ik, jk}` vs `{il, jl}`), violating the base-exchange axiom. So
the ℓ = 2 dictionary entries genuinely break the matroid structure, and the
`z > 0` extended mode adds a non-linear-algebraic side condition on top
(the extra rows must cut the aligned kernel exactly, checked only by the
exact witness).

### Step D3 — the starvation bound, and the third flank

At a fixed colouring define, for each label `L_pq`, the **menu capacity**
`cap_pq` = the number of `P ∈ E°` that could carry `L_pq` at all:
`{p,q} = colours(P)` (mandatory), or `|{p,q} ∩ colours(P)| = 1` with
`ℓ_P ∈ {1,2,3}`, or `{p,q} = opp(colours(P))` with `ℓ_P ∈ {2,4}`. Since every
class needs `≥ n − 2` members, `cap_pq < n − 2` for any `pq` is an outright
obstruction. Long paths are what starve it: a length-4 edge can carry only
`L_ij` and `L_opp(ij)` (under the pure dictionary), a length-5 edge only
`L_ij`.

**The octahedron flank.** `G° = K_{2,2,2}` with lengths (six 3's, six 4's;
`Σℓ = 42 = 6(12 − 6 + 1)`) is a class shape (`|V| = 36`, `def = 0`,
`hnoRigid`), `χ = 3`, and an admissible colouring **does** exist
(`φ = [0,0,1,1,2,3]`, proper on `G°` and acyclic off `e₀`). Yet over all 8
colourings the pure-dictionary search produces **zero** all-forest
leaves — the failure is (W1) itself, not the separator count, the opposite
pair, or the panel rules. The capacity profile at the witness colouring is
`[2, 5, 7, 7, 7, 7]` against a requirement of `≥ 4`: one class is starved by
2. This is the flank the (C7) repair of Step D4 **rescues** — so it is a
defect of the dictionary, not of the class.

### Step D4 — (C7): the repaired length-4 entry, and what it buys

> **(C7)** *(the named continuation; the length-4 half proven-informally,
> the rest open)* — the (C2) dictionary is **not** exhaustive. At `ℓ = 4`,
> put the free middle `x₂` at a generic point of the face plane `π(i,j,k)`
> and confine *one* end's pencil line to that plane
> (`P_w = Π(w) ∩ π(i,j,k)`), leaving the other generic. All four limit lines
> still span a 4-space (only three lie in the plane), and
> `R_P = ⟨L_ij, L_{x k}⟩` where `x ∈ {i,j}` is the *other* end. Both
> `L_ij` and `L_{xk}` meet every chain line — the two lines through `E_x`
> meet the two chain lines through `E_x` automatically, and both lie in
> `π(i,j,k)` with the remaining two. So the `ℓ = 4` menu is **every**
> 2-subset containing `L_ij` (five options), exactly as free as `ℓ = 3`'s.

12/12 exact witnesses (all colour pairs × both ends). Consequences,
measured: the exhaustive `K4` stratum goes **439 → 702 of 877**; the
octahedron flank of Step D3 becomes solvable; the two structural flanks of
the verdict are **untouched** (they are about the colouring, which the repair
does not move — every repaired option still contains `L_ij`).

Two honest gaps in (C7). **(a)** The rescue is *combinatorial only*: no
full (W1)–(W4) exact witness has been built at a repaired-dictionary member
(the `kslidecl.py` `chain_lines` builder would need the new label wired in,
plus the per-hub compatibility bookkeeping the plane-confined pencil line
implies). **(b)** The analogous question at `ℓ ∈ {1, 2, 5}` is open — and at
`ℓ = 5` the mandatory-`L_ij` claim itself is suspect: with fully generic
middles `L_ij` need not meet `x₂ ∨ x₃`, so `R_P` can be a **non-basis** line,
i.e. an "extra" row in the (C4) sense. That is the one direction that could
also loosen the acyclicity necessity (which assumes every row aligned), at
the price of a larger `z` and a correspondingly weaker structural statement.
It cannot touch the 5-chromatic flank.

### Step D5 — what a class proof now needs

1. **`χ(G°) ≥ 5` shapes** (`K5`, or `Δ(G°) ≥ 5` by Brooks) need a decoration
   with **more than four hub positions** — the tetrahedron's four points are
   the hard cap, and `dim Λ²K⁴ = 6` caps the number of classes at six
   regardless. Whether a 5-or-more-point configuration can still make each
   `R_P` a coordinate subspace is untouched here.
2. **Acyclicity-obstructed shapes** need either a non-aligned (`z > 0`)
   decoration on the offending bicoloured cycles or, again, a bigger
   configuration.
3. **Everything else** is a menu/matroid-intersection question per
   (shape, colouring) — (C6) says the packing side is free, so this half is
   genuinely finite and certificate-bearing, and (C7) is the cheap way to
   enlarge it.
4. **Or drop the collapse.** (C6) is the honest positive residue of this
   pass: the *combinatorial* content of the limit system is uniform and
   landed-machinery-reachable; it is the *alignment* device that fails to be
   class-uniform. A class proof of (K-slide-cl) may be better sought on the
   generic pure condition of the limit system (§(K-slide) Step 3's carrier)
   than on any degenerate specialization of it.

### Verification

`notes/scripts/w4/kslidecomb.py` (tracked; exact ℚ/ℤ arithmetic and asserts
inherited from `repin.py`/`pitch.py`/`kslide.py`/`kslidecl.py`; every sampled
object carries a rank/dimension assert, and every shape is re-certified by
`shape_ok` = tight count + `def = 0` + `hnoRigid`). Reproduce:

| driver | what it asserts |
|---|---|
| `--battery` | control: the 7 §(K-slide) members are class shapes, (C6) holds, and all 7 are menu-solvable (7/7) |
| `--pack` | (C6): min-max slack `≥ 0` over every `F ⊆ E°` **and** an explicit packing with class sizes `{n−2}³ ∪ {n−1}³`, at 7 battery + 2 `K5` shapes |
| `--k5` | properness forced at every `ℓ` (chain-span drop); `χ(K5) = 5`; 5 exhibited `K5` class shapes with 0 collapse assignments but (C6) packings |
| `--acyclic` | `L_ij ∈ A_P` at every length/colour pair; `χ` and acyclic-4-colourability of all 23 hub graphs with `|V°| ≤ 6`; the 4 with `χ ≤ 4` and no acyclic 4-colouring |
| `--flanks` | the three flanks side by side, with the stage-by-stage diagnosis and the starvation profile |
| `--k4full` | exhaustive `K4` stratum: 877 shapes, 877 (C6), 439 menu-solvable, 438 failures **all** with a satisfiable colouring premise |
| `--sweep` | seeded `|V°| ≤ 5` sweep (seed 20260805): 48 shapes, 48 (C6), 18 menu-solvable, 12 colouring-blocked, 18 menu-blocked |
| `--dict4` | (C7): 12/12 exact length-4 witnesses with `R_P = ⟨L_ij, L_xk⟩`, chain span 4 |
| `--relaxed` | the repaired menu: octahedron flank rescued, `K4` stratum 702/877, both structural flanks unchanged |

**Confidence verdict: (K-slide-comb) REFUTED as a class statement** (two
structural flanks at explicit class members; the 5-chromatic one robust
against any tetrahedral decoration, the acyclicity one against any
fully-aligned one); **(C6) — the unrestricted 6-fold base packing — proven-
informally for every class shape** from 5/6-sparsity via Edmonds'
matroid-partition min-max, so the packing content is never the obstruction;
**(C7)'s length-4 repair proven-informally** (12/12 exact witnesses,
`K4` coverage 439 → 702/877, octahedron flank rescued) with its geometric
witness and its `ℓ ∈ {1,2,5}` analogues **open**; and **(K-slide-cl) back to
open**, covered exactly on the shapes where the assignment problem is
solvable (all 7 battery members, hence the `K4`/`W4` control habitats,
unchanged).

## §(K-flank) — the adversarial rank test at the uncovered flanks: **half 2 proven-informally per shape; no disproof**

Sibling of §(K-slide-comb), computing the geometry at the flank taxonomy its
*Step D5* left. Standing notation inherited from the *Shared dictionary*,
§(K-tight) (the escape criterion, `U`, `R_a`, `r`, `r̃ = ★r`, `C(M)`, `s₀`),
§(K-pitch) ((T1)–(T3), `Q`), §(K-slide) (`G°`, decorations, (W1)–(W4), (S1),
(S5), `P21`) and §(K-slide-comb) (the flank taxonomy of *Step D5*).

§(K-slide-comb) *Step D5* and §(K-slide) *Step 5* left a list of **shapes no
class-uniform mechanism covers**, all of them built **combinatorially only** —
`def`, `hnoRigid`, the chromatic / acyclicity obstruction, the packing. No
geometry had ever been computed at any of them, and the opening recon's R2
("the conjecture survives all exact-rational rank tests") **predates** them,
so it is not evidence about them. This section computes the geometry, keeping
two questions apart:

1. does the pinned kernel `hK` hold at these shapes (a failure forces a
   re-pin), and
2. does the **pencil conjecture itself** hold there — at a nondegenerate
   pencil realization of a flank shape, does the body-hinge rank reach the Tay
   target (a failure disproves the phase's target theorem)?

**Verdict (2026-08-05, sixth pass).**

(i) **HALF 2 HOLDS at every flank shape — proven-informally, per shape, by an
exact witness; there is no disproof.** At each shape an exact rational
configuration is exhibited that satisfies **all four conjuncts** of
`IsNondegPencilRealization` (`Molecule/Pencil/Motive.lean:110`) and whose
exact-ℚ body-hinge rank **equals** the Tay target `6(|V| − 1) − def`. Because
`HasGenericPencilRealization` (`Motive.lean:140`) is itself an **∃** over
(framework, normal, point), one such witness *is* the statement at that shape
— no genericity or sampling argument is consumed. Tested: the eight named
shapes below and **843** flank class shapes in whole strata (Step F3),
including the **exhaustive** 438 menu-blocked `K4` shapes and all 210 all-`{3,4}`
`K5` class shapes. Zero failures.

(ii) **HALF 1: no `hK` counterexample, and no re-pin needed.** At all 16
probed `e₀`-end splits (8 shapes × both ends) and at **every** eligible split
of the 5-chromatic flank, `hK`'s realization antecedent is witnessed by a
*nondegenerate* target-rank `G′` seed and the escape is **observed on both KT
routes**, with the §(K-tight) criterion matching the observation seed by seed
and the escaping configuration re-certified as a legal nondegenerate
realization of `G` at target rank. The hard stratum is what these shapes sit
in (`s₀ = 0`, `dim R_a = 1`, `dim U = 2` at every clean seed): the flanks are
not an easy case in disguise.

(iii) **(K-pitch) closes at every flank split** (16/16): the transmitted
wrench is **non-null** (`Q(r) ≠ 0`) at the first valid seed of each, with
(T1)–(T3) and the (T2) sign law re-validated, `dim V_bc = 3` and the Klein Gram
on `V_bc` of rank 3. By §(K-slide) *Step 3*'s one-witness logic each such
certificate closes (K-pitch) at that split individually. So the flank shapes
join the §(K-slide) *Step 4* battery as **individually closed members** —
what they are *not* is covered by a **class-uniform** device.

(iv) **What resists at the flanks is the degeneration, not the geometry — and
it resists one level *earlier* than the collapse.** At the very shapes where
the collapse's assignment problem is unsolvable, the undegenerate rank problem
is **maximally healthy**: the full pencil-row family of `G` is independent
(rank `= 5|E| =` target), and at `ε = 1` the transmitted wrench is non-null.
But the **full-support slide-in limit is itself degenerate at every structural
flank** (Step F6, `--limit`; 40 sampled decorations each, no (W1)–(W4)
witness), in a shape-dependent way — so §(K-slide)'s `G°`-level carrier, the
object *Step 3* designates as where a class-uniform argument should live, does
not reach these shapes under the full support either. This **corrects** the
reading this pass started from ("the flanks obstruct only the tetrahedral
alignment"): they obstruct the alignment **and** the full-support limit. The
slide support is a free parameter ((S1) remark (iii)), so what is bounded is
the device *as run*, not the carrier in principle — the concrete next probe is
named in Step F7.

(v) **A ∀-realization escape statement is FALSE — exhibited.** At `P21`,
5 of 35 valid target-rank `G′` seeds have an `s₀`-jump (`s₀ = 1`, hence
`dim R_a = 0`, `dim U = 1`) and therefore fail at **every** placement of `v`
— the first such seed ever exhibited in the phase's numerics, confirming a
§(K-tight) *Step 2.3* prediction that had never been tested. `hK`'s ∃-form is
untouched (30 of 35 seeds escape). Each jump seed's `G − v` stress is
supported on the **theta sub-multigraph `{12, 13, 23a, 23b}`** (12 edges, line
rank 6) — *exactly* the support §(K-slide) *Step 5* exhibits for `P21`'s
reduced-support **limit** stress: the parallel-edge obstruction is **not
confined to the `ε = 0` limit**; it inhabits a nonempty locus of the pencil
chart itself.

**What would change this.** *For half 2:* an error in the model dictionary
(the harness' 5-rows-per-hinge Euclidean-perp rigidity model vs
`BodyHingeFramework.rigidityRows`) — the standing §(K-tight) caveat, shared by
every numeric result in this workbook; or a flank shape outside the tested
strata (the `(K-res)` **length-6** flank is still unprobed, Step F7). *For
half 1:* a split at a flank shape where **no** seed escapes — none found, and
the only non-escaping seeds found are the ones the calculus proves must fail.
*For (iv):* a flank shape whose generic pencil rows are dependent (the strata
of Step F3 say there is none up to `|V| = 41`), or — in the other direction —
a **reduced slide support** under which a structural flank *does* carry a
(W1)–(W4) witness, which would move the flank inside the (K-slide) carrier
(Step F7 item 2).

### Step F0 — the two questions are not independent, and the quantifiers matter

Both halves must be stated against the landed objects, or the test measures the
wrong thing.

**Half 2 is an ∃.** `HasGenericPencilRealization K 3 G` unfolds
(`Motive.lean:140`) to: **∃** a body-hinge framework `F` and maps
`normal, point : α → Fin 4 → K` with `IsNondegPencilRealization G F normal
point` and `finrank (span F.rigidityRows) = 6(|V| − 1) − def`. The word
"generic" names the *stratum* (the nondegeneracy conjuncts), **not** a
Zariski-generic quantifier. So a single exact configuration settles half 2 at a
shape outright. Its four conjuncts, in the harness model (where the support
extensor **is** `pt(u) ∧ pt(v)`, so `ExtensorThroughPoint` at both endpoints
is built in):

1. `HasPencilPanelRealization` — per body a nonzero `normal v` with
   `point v ⬝ᵥ normal v = 0` and every incident hinge inside `normal v ^⊥`;
   equivalently, the hats of `{v} ∪ N(v)` admit a nonzero common annihilator
   (`kbare_common.verify_pencil_witness`, which also rejects coincident
   adjacent points);
2. every link's endpoint points **projectively distinct**;
3. `LinearIndepOn normal (closedHubNbhd v)` at every body;
4. `LinearIndepOn point (closedNbhd v)` at every **non-hub** body — i.e. at a
   degree-2 body, `pt(v), pt(p), pt(q)` not collinear.

At an all-lengths-`≥ 3` shape conjunct 3 is a nonzero-normal condition
(`closedHubNbhd` is a singleton at every body — hubs have no hub neighbours),
and conjunct 4 is the non-collinearity of every interior's little star. Both
are asserted per witness here, not assumed; so is `rank ≤ target`.

**Since each flank shape is tight, half 2 = full row rank.** `def = 0` and
`5|E| = 6(|V| − 1)` give `#rows = target = 6|V| − 6`. Two bounds then pin the
rank from above at *every* configuration, and neither needs the deficiency
theory: the six trivial twists always lie in the kernel (`rank ≤ 6|V| − 6`),
and the row count is what it is (`rank ≤ 5|E|`). So attainment is exactly
**independence of the whole pencil-row family**, and a `rank_modp` equal to the
target *certifies* the rational rank outright (`rank_p ≤ rank_ℚ ≤ #rows =
target`, the first inequality because a nonvanishing `k × k` minor mod `p` is a
nonvanishing integer minor). That is how the strata of Step F3 are certified
cheaply and exactly — `p = 2⁶¹ − 1` — with an exact-ℚ recheck at each
stratum's first shape and at every named witness of Step F2.

**Half 1 is an ∃ on both sides.** `hK` as pinned (`notes/Phase39-design.md`
§"W5-L7 research recon") reads: `G` simple, `5 ≤ |V|`, 2-edge-connected,
**`hnoRigid`**, `deg v = 2`, the two links, `(¬ hub a ∨ ¬ hub b)`, `e₀ ∉ E(G)`,
**and `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)`** ⟹ ∃ `hubSel`,
a seed `q` and a target-size set `s` of genuine edges with the `pencilRow`
subfamily independent at `q`. Three consequences for a refutation attempt:

- The conclusion is "**some** chart seed of `G` reaches the target", not "the
  given `G′`-seed extends". So a target-rank `G′`-seed that fails to extend is
  **not** a counterexample — only a shape where *no* `G`-seed reaches the
  target is, and by L7b (`hasGenericPencilRealization_of_independent_pencilRow_
  target`, `Escape.lean:186`, **landed**) that would refute half 2 as well.
  Hence: **half 2 holding at a shape closes the only route by which that shape
  could refute `hK`'s content.** The converse bridge — from a *witness
  configuration* to a *chart seed* — is the deferred re-seeding lemma
  `exists_pencilSeed_of_nondeg` (`Engine.lean`; the point-reproduction side is
  landed, the normal side and the final assembly are not). That step is
  **shape-independent**, so the flanks introduce no new gap; but the strict
  statement of what this section proves for half 1 is *the mathematics of
  `hK` at these shapes*, with the chart restatement resting on that landed-in-
  part lemma.
- `hnoRigid` sits in the antecedent, and `P21` **fails** it (its parallel pair
  is a rigid `C₆`, `no_rigid_branch_union` = False). So `hK` is **vacuous** at
  `P21`; `P21` is a `(K-res)`-shaped habitat member, and the probes there test
  the escape *mechanism* only. All seven other shapes carry `hnoRigid`.
- The antecedent asks for a **nondegenerate** `G′` realization. Every `G′`
  seed used below is re-certified against all four conjuncts (`G′` has a
  length-2 path, so its conjuncts 3 and 4 genuinely bite: the meet-line
  interior's two hub normals must be independent and `pt(a), pt(b), pt(c)`
  non-collinear).

**The placement-sampler trap, and the guard.** `widened.place_pencil_general`
places a single-panel interior with `localtest.in_plane_point`, whose
`plane_basis` returns two **parallel** in-plane directions whenever the
normal's third coordinate is `0` (`notes/scripts/README.md` *Divergences*; the
defect behind the corrected `widened.py` escape figures — §(K-tight) *Step 3*).
A hub normal is drawn from `rquat`, so this is not rare: at these shapes
**11 of 40** seeds are affected, and each affected hub collapses its whole
closed star onto a line. Read naively such a seed *looks like a disproof*. The
guard used throughout is structural, not a coordinate test: at a generic
pencil configuration the hats of `{v} ∪ N(v)` have rank **3** at every body
(3 is the maximum — at a hub they all lie in the 3-dimensional panel; at a
degree-2 body there are only three of them, and rank 3 there **is** conjunct
4). Step F4 measures that this guard detects exactly the artifact.

### Step F1 — the shapes, and their habitat certification

All eight are re-certified by the driver, **asserted** and not assumed:
`def = 0`, tight (`5|E| = 6(|V| − 1)`), 2-edge-connected, **`hcard`** (every
hub has `≤ 2` hub neighbours) and **triangle-free** — the last two being
exactly the conditions the (K) consumer carries
(`hasGenericPencilRealization_of_independent_pencilRow_target`,
`Escape.lean:186`). `hnoRigid` (`kslide.no_rigid_branch_union`) is **reported**
per shape rather than asserted, precisely because `P21` fails it; in the
`--strata` sweeps it *is* asserted, via `kslidecomb.shape_ok`.

| shape | `G°` | `χ(G°)` | `Δ(G°)` | `\|V\|` | `\|E\|` | target | flank |
|---|---|---|---|---|---|---|---|
| `K5`, lengths `(3,3,3,3,4,4,4,4,4,4)` | `K5` | 5 | 4 | 31 | 36 | 180 | D5-1, 5-chromatic |
| `K5 + v` (6th hub on `0,1,2`), `(4⁹,3⁴)` | 13 edges | 5 | 5 | 41 | 48 | 240 | D5-1, the Brooks `Δ ≥ 5` branch |
| 6v/11e, `(3⁸,4³)` | 11 edges | 4 | 4 | 31 | 36 | 180 | D5-2, no acyclic 4-colouring |
| `K222` octahedron, `(3⁶,4⁶)` | 12 edges | 3 | 4 | 36 | 42 | 210 | D5-3 (starved menu; (C7) rescues it) |
| wheel `W5`, all-3 | 10 edges | 4 | 5 | 26 | 30 | 150 | high-concurrency probe |
| wheel `W7`, all-3 | 14 edges | 4 | 7 | 36 | 42 | 210 | high-concurrency probe |
| `K4`, lengths `(1,1,3,5,3,5)` | `K4` | 4 | 3 | 16 | 18 | 90 | D5-3, first menu-blocked shape |
| `P21`, `(3;3,3;4,5,3,3)` | `K4` + doubled `23` | 4 | 4 | 21 | 24 | 120 | §(K-slide) 5, parallel `G°`-edge |

Two additions to the workbook's list, both deliberate:

- **`K5 + v`** exhibits the *second* branch of the Brooks characterization
  (§(K-slide-comb) verdict (i): `χ(G°) ≥ 5` forces `G° = K5` **or**
  `Δ(G°) ≥ 5`). The workbook names that branch but never exhibits it; here it
  is, as a class shape with `χ = 5`, `Δ = 5`, `G° ≠ K5`.
- **the wheels** are the sharpest *geometric* adversary available: their centre
  is a single body carrying `Δ(G°)` concurrent coplanar hinges, which is where
  a rank cap would be most plausible (and where the collapse's four-position
  ceiling bites hardest). All-length-3 is exactly tight for a wheel
  (`3m = 6(m − n + 1)` iff `m = 2n − 2`), so no search is needed. `W7` puts
  **seven** hinges in one pencil and still attains. The one visible mechanism
  by which a high-degree hub could cap the rank is that *all* of a body's
  hinges live in the 3-dimensional `Λ²Π̂(h)`, however many there are; the
  measurement says that does not bite for `Δ(G°) ≤ 7`. It is **not** evidence
  about unbounded `Δ`, which the class does not bound.

Two corrections to workbook prose, both checked, both **now applied in place**
(this section is their record):

- §(K-slide) *Step 5* described `P21` as "`G°` = `K4 − 02` plus doubled `23`".
  The spec it cites (and `kslide.flanks()` builds) is **all six `K4` edges plus
  a second `23`**: 7 hub paths, `Σℓ = 24 = 6(7 − 4 + 1)`, `|V| = 21`. With
  `K4 − 02` there would be 6 paths and the quoted lengths could not be tight —
  the sentence's own length list `(3; 3,3; 4,5,3,3)` has seven entries. Read
  "`K4` with `23` doubled".
- §(K-slide-comb) verdict (i) said "84 of the all-`{3,4}` assignments qualify"
  at `K5`. Reconciled: **210** = `C(10,4)` all-`{3,4}` assignments with
  `Σℓ = 36` are class shapes (all of them are — `hnoRigid` never fails here),
  of which **84** = `C(9,3)` have the *designated* split edge `(0,1)` of
  length 3. Both figures are right under their own convention; the driver here
  uses "`e₀` := the first length-3 edge", as `--k4full` does, and reports 210.

### Step F2 — (F1): half 2 at the named shapes

> **(F1)** *(proven-informally, per shape)* — at each of the eight shapes of
> Step F1 there is an exact rational configuration satisfying all four
> conjuncts of `IsNondegPencilRealization` whose exact-ℚ body-hinge rank equals
> the Tay target. Hence `HasGenericPencilRealization ℚ 3 G` holds at each —
> and, the witness being rational, over every field of characteristic 0 (rank
> of a fixed rational matrix is unchanged by field extension), and over
> `GF(2⁶¹ − 1)` by the same witness's mod-`p` rank.

*Proof.* By Step F0 the predicate is an `∃`, the witnesses are exhibited
(`flanks.py --conj`, seeds printed), and every conjunct plus `rank ≤ target` is
asserted at each witness. The rank figures: `180 = 180`, `180`, `210`, `240`,
`150`, `210`, `90`, `120` — in each case `= #rows = target`. ∎

Two remarks. **(a)** Attainment is *full row rank*, so at these tight shapes
the conclusion is the strongest possible: the pencil rows of `G` are
**independent**, and the deficiency bound is met with no slack anywhere.
**(b)** By the chart's irreducibility (a tower of affine-linear fibers —
§(K-slide) *Step 1(e)*) the attaining set is dense open, so the witnesses are
generic in the usual sense too; nothing below needs that.

### Step F3 — the strata: attainment is not an artifact of one length assignment

A single exhibited assignment per hub graph would be a weak test of a
*class*-flavoured worry, so half 2 is run over whole strata
(`flanks.py --strata`; the `rank_modp = #rows = target` certification of
Step F0, with an exact-ℚ recheck at each stratum's first shape):

| stratum | shapes | half 2 |
|---|---|---|
| `K5`, all-`{3,4}` assignments (`Σℓ = 36`) | 210 of 210 candidates are class shapes | **210/210** |
| 6v/11e, all-`{3,4}` (`Σℓ = 36`) | 155 of 165 candidates | **155/155** |
| `K222`, all-`{3,4}` (`Σℓ = 42`), seeded sample (seed 20260805, 40 draws) | 40 | **40/40** |
| `G° = K4`, the **menu-blocked** shapes, exhaustive | 438 of the 877 | **438/438** |

**843 flank class shapes, 0 failures.** The `K4` row is the exhaustive
menu-blocked flank of *Step D5 item 3* — every shape the pure dictionary
misses is included — and by the `--k4full` record every one of them carries an
`ℓ ≤ 2` edge (the only all-`≥ 3` `K4` shape is `(3,3,3,3,3,3)`, which solves),
so hub–hub adjacency and meet-line interiors are inside the sweep, not
excluded from it. Every shape in every row was additionally re-certified
`hcard` + triangle-free.

### Step F4 — the sampler-artifact control (and why the deficits are not evidence)

`flanks.py --degen`, at the 5-chromatic flank, seeds 1..40: **27** generic
samples, **all** at rank 180 = target; **11** guard-rejected samples, each
short of the target by **exactly** the number of hubs whose closed star
collapsed to a line (deficits 1 and 2 observed); 2 unplaceable. So

- every rank deficit ever seen at these shapes is a sampler artifact, and the
  star-rank guard is *exact* on this shape — it detects precisely the affected
  samples and predicts the deficit;
- a **coordinate** test would not do: `--degen` exhibits samples with two
  zero-coordinate normals whose stars are nonetheless generic, and one with a
  single zero-coordinate normal that collapses. Only the structural rank
  condition classifies correctly. (This is the `plane_basis` precedent
  generalized: the right guard is a rank assert on the sampled *object*, not a
  test on the sampled *parameter*.)

Without the guard, 11 of 40 seeds at the headline flank shape would have read
as rank deficits at a shape "no mechanism covers" — the exact shape of a false
disproof.

### Step F5 — half 1: `hK`, the escape mechanism, and the pitch at the flanks

**(a) Both `e₀` ends, all eight shapes** (`flanks.py --split`; seeds 101..120,
3 placements per route). At every split: `hK`'s antecedent witnessed by a
nondegenerate target-rank `G′` seed; `s₀ = 0`, `dim R_a = 1`, `dim U = 2` —
the **hard stratum**; the §(K-tight) structure identities
(`dim U = dim R_a + 1`, `U ∩ C(ab)^⊥ = R_a`, `R_a ⊆ U`) asserted; `critA` and
`critB` both true and **both routes observed to escape**; and the escaping
`G`-configuration re-certified against all four nondegeneracy conjuncts at
target rank (so each escape is *also* a half-2 witness). 16/16 splits.

**(b) Every eligible split of the 5-chromatic flank** (`flanks.py
--allsplits`). `hK` quantifies over `(v, a, b)`, so one bad split would
refute it. Every `v` with `deg v = 2` and a degree-2 neighbour is probed:
**26 splits — 26/26 escape**, at the first valid seed each. Eight of them have
**both** chain ends hubs (the two interiors of each of the four length-3
paths) — the (K-tight) hard form with the 5-dimensional combined failure span;
the other 18 are the three eligible interiors of each length-4 path, where one
chain end is free and the failure locus is 1-dimensional (strictly easier,
§(K-tight) *Step 4*). The escapes here are rank-level (the nondegeneracy
re-certification runs at the 16 `e₀` splits of (a)); nothing rests on it, since
half 2 at the shape is certified independently in Step F2.

**(c) The pitch certificate** (`flanks.py --pitch`). At the first valid seed of
each of the 16 splits: (T1) `r ⊥_E V_bc` with `W = V_bc ⊕ T` of dim 5 and
`W^⊥ = ⟨r⟩`; (T2) the sign law with `Q(r)·Q(z) < 0`; (T3) the motion-form
criterion agreeing with the §(K-tight) span form, and the route-A
`★r`-in-panel form; `dim V_bc = 3` with the Klein Gram of rank 3; and
**`Q(r) ≠ 0`** — a **non-null transmitted wrench**, which certifies escape on
both routes. 16/16. By §(K-slide) *Step 3* each certificate closes (K-pitch)
at that split, so the eight shapes of Step F1 are individually closed exactly
as the seven §(K-slide) *Step 4* battery members are.

**(d) The `dim R_a = 0` stratum, exhibited at last** (`flanks.py --rzero`).
§(K-tight) *Step 2.3* proves that a target-rank `G′` seed with `dim R_a = 0`
has `dim U = 1`, so the two placement functionals can never be independent on
`U` and the seed **fails at every placement**. No such seed had ever been
exhibited: the record was "every target-rank seed ever probed escapes"
(§(K-tight) *Step 3*). At `P21`, split `v = 100`, seeds 101..140: **30** seeds
with `dim R_a = 1` (escaping), **5** with `s₀ = 1`, `dim R_a = 0`, `dim U = 1`
(8/8 placements fail at each, as predicted), 5 invalid. Consequences:

- the prediction is **confirmed** against an exhibited *legal nondegenerate*
  target-rank `G′` realization;
- any **∀-realization** form of the escape ("every target-rank `G′` seed
  extends") is **FALSE at `P21`** — independent confirmation, at a
  whole-seed rather than a placement-locus granularity, of the design doc's
  "Finding 1 makes any ∀-realization opaque-`r` escape hypothesis false".
  `hK`'s ∃-form is untouched;
- the count-theoretic prediction (`widened.split_report`) is
  `dim R_a = 5 + def(G′) − def(G − v) = 1`; the jump is **geometric**, i.e.
  the *pencil* stratum carries corank the count does not see, on a locus that
  is not thin in the sampler's rational range (5/35).

**Correction to the numerical record** (the reason this matters beyond `P21`).
§(K-tight) *Step 3* recorded "**every** target-rank seed ever probed escapes",
and the gap map's (K-tight) row read "no genuine escape failure anywhere in the
corrected numerics". Both were true when written and both needed one
qualifier: the statement holds on the **hard stratum `dim R_a = 1`** (and above
it), and it is **false without that qualifier**, by the five seeds above. The
mathematics is unchanged (Step 2.3 always said so); the *record* was stated
more strongly than the stratum it was measured on. **Both are amended in
place** (§(K-tight) *Step 3*; the gap map's (K-tight) row).

**(e) What carries the jump — a hypothesis this pass refuted and replaced.**
The natural guess was "the parallel pair's rigid `C₆` picks up a stress".
Measured: at every one of the 5 jump seeds the `G − v` self-stress is
supported on **12 edges, on the four chains among hubs `{1,2,3}`** — hub pairs
`(2,3), (2,3), (1,2), (1,3)`, i.e. the **theta sub-multigraph
`{12, 13, 23a, 23b}`** — with **line rank 6**. Not the parallel pair alone.
That is *exactly* the support, edge count and line rank §(K-slide) *Step 5*
exhibits for `P21`'s reduced-support **limit** stress. So (S5)'s parallel-edge
obstruction is not an artifact of the `ε = 0` degeneration: the same theta
circuit closes on a nonempty locus of the pencil chart itself, where it forces
`dim R_a = 0`.

### Step F6 — what this settles for the gap map

**The geometry of `G` is unobstructed; both degenerations are not.**
§(K-slide-comb) *Step D5* item 4 suspected that "it is the *alignment* device
that fails to be class-uniform". Half of that is now measured and half is
**corrected**.

*Measured, and confirming Step D5:* where the collapse's assignment problem has
no solution at all, the undegenerate pencil-row family of `G` is
**independent** — full row rank, no slack (Steps F2/F3) — and the `ε = 1`
transmitted wrench is non-null (Step F5c). So no flank shape's *geometry*
resists.

*Corrected:* the obstruction is not confined to the tetrahedral alignment.
`flanks.py --limit` runs `kslide.limit_witness` at **generic, non-aligned**
decorations of the **full-support** `ε = 0` limit system, 40 seeds per shape,
and finds **no (W1)–(W4) witness at any of the four structural flanks**, with a
different first-failing conjunct per shape (the tally is printed; the assert
order is (W1) → (W4), so a tally concentrated on a later conjunct certifies the
earlier ones held at every seed):

| shape | full-support limit at 40 generic decorations |
|---|---|
| `K5`, χ = 5 | (W1) fails at 5 seeds; at the other 27 valid ones (W1)+(W2) hold and **(W3)** fails — `z(limit)` degenerate, the two `T`-conditions dependent on `V_bc` |
| 6v/11e | (W1) holds at all 30 valid seeds; **(W2)** fails at all 30 — `dim V_bc(limit) = 2`, the limit system over-constrained at `b, c` |
| `K222` octahedron | (W1),(W2),(W3) hold at all 30 valid seeds; **(W4)** fails at all 30 — the limit twist is Klein-**null** at every sampled decoration |
| `K5 + v`, χ = 5, Δ = 5 | identical profile: **(W4)** fails at all 30 valid seeds |
| `P21` | **(W1)** fails at all 35 valid seeds — the proven parallel-edge order-0 obstruction, (S5) |
| wheels `W5`, `W7`; `K4` `(1,1,3,5,3,5)` | **witness found at seed 101** — (W1) `dim mot = 9`, (W2) `dim V_bc = 3`, (W3) `z` defined, (W4) `Q(z_lim) ≠ 0` |

So the `G°`-level limit carrier — §(K-slide) *Step 3*'s designated home for a
class-uniform argument — **does not reach the structural flanks under the full
slide support**, and the three shapes where it does reach are exactly the ones
that were never structurally obstructed (two wheels and a menu-blocked `K4`,
each witnessed at the very first seed). The failure profiles are **uniform per
shape**, not scattered: 30/30 at `K222` and `K5 + v` ((W4) null twist), 30/30 at
6v/11e ((W2) `dim V_bc = 2`), 27/27 of the (W1)-passing seeds at `K5` ((W3) `z`
degenerate), 35/35 at `P21` ((W1)). Uniformity over 30-odd rational decorations
is consistent with identical vanishing on the decoration variety — which is
what a *proof* of the full-support limit's degeneracy at these shapes would
assert — but sampling can only ever refute identical vanishing, never
establish it, so this is evidence for the shape of the obstruction, not a
proof of it.
Since the ε = 1 pitch is non-null at these same splits (Step F5c), the
vanishing is a property of the **degeneration**, not of the shape; and since
the support Σ is a free parameter ((S1) remark (iii)), the negative bounds the
device *as run*. It is nonetheless a second, independent obstruction at the
flanks, and it is new: no prior pass ran the limit witness at these shapes.

**Mechanism, since supplied — see §(K-pure), not restated here** (2026-08-05,
fan-out direction C). **(PC-OBS)** explains the `K5` row of the table above
structurally, and *proves* the vanishing instead of sampling it: a chord
self-stress of the hub-point framework forces `z` into the isotropic `Λ²π̂` at
**every** decoration, and at the all-`{3,4}` `K5` shape `V_bc = α(pt c)`, the
strong-containment branch that makes **(W3)** fail — exactly the profile
measured here. The two passes' drivers are independent (`flanks.py --limit`, 40
non-aligned decorations per shape; `pure.py --flanks`, 10–11 chart seeds plus the
chord predictor) and they agree at every shape they share, which is evidence
rather than redundancy. The `K222` and 6v/11e mechanisms are still open there
too, and §(K-pure) *Step P7* additionally **answers** item 2 of Step F7 below.

**One flank shape moves inside the (K-slide) carrier — and it is a
menu-blocked one.** The `K4` shape `(1,1,3,5,3,5)`, a member of *Step D5 item
3*'s 438 menu-blocked shapes, carries a full (W1)–(W4) limit witness at the
first seed. By (S1) that closes (K-pitch) there **through the `G°`-level
carrier**, not merely through an `ε = 1` certificate. So for that shape the
menu obstruction is strictly stronger than the device requires: the 438-shape
flank is (at least in part) a defect of the *dictionary*, exactly as (C7)'s
partial rescue suggested, and not of the slide device. The two wheels are new
(K-slide) members on the same footing — the §(K-slide) *Step 4* battery table
gains three rows (done, marked `†` there).

Two readings, kept separate:

- **Settled.** No flank shape is a counterexample to the conjecture; no flank
  shape is a counterexample to `hK`; each flank shape is individually closed
  for (K-pitch) by an exact `ε = 1` certificate, and three of them through the
  `G°`-level carrier as well. The *Shapes no mechanism covers* list of the gap
  map is accordingly re-titled: these are shapes no **class-uniform** mechanism
  covers — every one of them is now individually discharged.
- **Not settled.** Nothing here is class-uniform. 843 shapes with `|V| ≤ 41`
  are 843 shapes, and the uniform statement remains (K-tight)/(K-move)/
  (K-pitch) exactly as before. This pass **removes a disproof risk and adds
  mechanism data**; it moves no uniform gap.

One structural consequence worth recording for direction C's benefit: at a
tight class shape, half 2 *is* the statement "the pencil rows of `G` are
independent at some chart point", i.e. the non-vanishing of one maximal
minor of the pencil rigidity matrix — a **pure-condition-shaped** statement in
White–Whiteley's idiom, on `G` itself rather than on a degenerated limit. The
843 shapes say that minor is nonzero at every tested class shape; what is
missing is a *reason*, and the pure condition of `G` (not of the limit) is
where a uniform reason would live.

### Step F7 — what remains open (honestly)

1. **Class uniformity.** Untouched. This section is per-shape certificates.
2. **Reduced slide supports at the structural flanks — ANSWERED**, by fan-out
   direction C the same day: **§(K-pure) *Step P7*** (the mathematics is there,
   not restated here). This pass named it the single most valuable follow-up its
   data points at, and it delivered: **5 of the 6 probed flank shapes close by a
   reduced support** — all three obstructed `K5` 5-chromatic shapes, the `K222`
   octahedron and θ(3,4,5), each by "no slide at `c`" — so the 5-chromatic flank
   *is* inside the (K-slide) carrier after all. The **6v/11e** flank is the one
   exception: it fails (W2) at every probed nonempty support, and its split
   closes by the `ε = 1` chart certificate only.
3. **The `(K-res)` length-6 flank** (gap map, *Shapes no class-uniform
   mechanism covers*) is **still unprobed**. It is out of this dispatch's
   target list, and it cannot be reached from the tight class: §(K-slide-cl)
   *Step C0*'s "`ℓ = 6` forces a rigid complement" lemma means a length-6 path
   is impossible under `hnoRigid`, so a probe needs a genuine `(K-res)`
   residual member (`notes/Pencil-W4-informal.md` §"widened kernels" *Step 4*),
   and none parallel-free was at hand. The right next probe, and cheap: build
   one, and run `--conj`/`--split` on it.
4. **The model dictionary.** Every rank figure lives in the harness'
   5-rows-per-hinge Euclidean-perp model (row space `= {w : ⟨w, C(e)⟩ = 0}`,
   kernel `= ⟨C(e)⟩`, global kernel the 6 trivial twists — checked implicitly
   by every `rank = 6|V| − 6` figure here). The §(K-tight) caveat stands
   unchanged; it is shared by the whole workbook, not specific to this pass.
5. **The chart bridge.** Half 1's chart-level restatement rests on
   `exists_pencilSeed_of_nondeg`, landed only in part (Step F0). Shape-
   independent, but not free.
6. **`P21`'s `s₀`-jump locus** is uncharted: 5/35 rational samples is not a
   dimension count. Whether the theta-circuit locus is a hypersurface in the
   `P21` chart, and whether an analogous locus exists at *parallel-free*
   shapes (none seen: 0 jump seeds at the other seven shapes), is open. It is
   the one place in this pass where a *negative* structure was found, and the
   natural continuation if the parallel-edge family is ever needed.

### Verification

`notes/scripts/w4/flanks.py` (tracked, new this pass; exact ℚ throughout, no
floating point; imports the harness read-only; every sampled configuration
carries the four-conjunct nondegeneracy check *and* the star-rank genericity
guard; all seeds are literals and printed). Reproduce, from the repo root and
with `PYTHONHASHSEED=0`: `python3 notes/scripts/w4/flanks.py --conj | --degen |
--strata | --split | --allsplits | --pitch | --rzero | --limit`.

| driver | ~time | what it asserts |
|---|---|---|
| `--conj` | 10 s | HALF 2 at the 8 named shapes: class + habitat certification, then an exact nondegenerate configuration at the Tay target (8/8, exact-ℚ ranks 180/180/210/240/150/210/90/120) |
| `--degen` | 4 s | the sampler control at the 5-chromatic flank: 27/27 generic samples at the target; 11 guard-rejected, each short by exactly the number of collapsed stars |
| `--strata` | 85 s | HALF 2 over whole strata: `K5` 210/210, 6v/11e 155/155, `K222` 40/40 (seed 20260805), `K4` menu-blocked 438/438 — 843 shapes, 0 failures, exact-ℚ recheck per stratum |
| `--split` | 193 s | HALF 1 at both `e₀` ends of all 8 shapes: antecedent witnessed + nondegenerate, hard-stratum invariants, criterion = observation, both routes escape, escape re-certified as a half-2 witness |
| `--allsplits` | 176 s | HALF 1 at **every** eligible split of the 5-chromatic flank (the ∀ in `hK`) |
| `--pitch` | 65 s | (T1)–(T3) + `Q(r) ≠ 0` at all 16 flank splits (16/16): (K-pitch) closes at each |
| `--rzero` | 84 s | the `dim R_a = 0` stratum at `P21`: 30/5/5 seeds, `dim U = 1`, 8/8 placements fail, and the theta-sub-multigraph stress support (12 edges, line rank 6) |
| `--limit` | 762 s | the (K-slide) FULL-SUPPORT limit carrier at the flanks, 40 generic decorations per shape, first-failure tally per conjunct: witnesses at `W5`, `W7` and the menu-blocked `K4` (seed 101, `dim mot = 9`); **none** at `K5` (W3 27/27), 6v/11e (W2 30/30), `K222` and `K5+v` (W4 30/30), `P21` (W1 35/35) |

**Confidence verdict: HALF 2 — the pencil conjecture at the uncovered flanks
— is PROVEN-INFORMALLY per shape** (exact nondegenerate witnesses at the Tay
target; 8 named shapes + 843 stratum shapes, 0 failures), so **no
counterexample exists at the shapes most likely to carry one and the disproof
risk is removed** — the **class-uniform** target theorem is *not* thereby
established (nothing in this section is uniform: (i) and Step F7 item 1);
**HALF 1 — `hK` at the flanks — carries no counterexample and needs no
re-pin** (16/16 `e₀`-end splits and every eligible split of the 5-chromatic
flank escape on both routes, with the (K-tight) criterion matching seed by
seed), with the strict caveat that the chart-level restatement rests on the
partly-landed re-seeding lemma; **(K-pitch) closes at every flank split**
(16/16 non-null transmitted wrenches); **the geometry of `G` is unobstructed at
the flanks while BOTH degenerations are obstructed there** — the tetrahedral
alignment (§(K-slide-comb), already known) and now, newly, the **full-support
slide-in limit** at all four structural flanks (uniform per-shape failure
profiles over 30-odd generic decorations each; **reduced** supports were named
here as the follow-up and were probed the same day by direction C, which
recovers 5 of the 6 flank shapes — §(K-pure) *Step P7*), against which three
previously-uncovered shapes —
the two wheels and a **menu-blocked `K4` shape** — do carry full (W1)–(W4)
limit witnesses and so join the (K-slide) battery; and **a ∀-realization escape
statement is REFUTED at `P21`** by an exhibited `dim R_a = 0` seed whose forced
failure confirms a (K-tight) prediction never before tested. **Class uniformity
is untouched** — this pass removes a disproof risk and adds mechanism data; it
closes no uniform gap.

## §(K-pure) — the pure condition of the limit carrier, un-specialized: the wrong invariant, the chord obstruction, and the support lever (**direction C REFUTED as a strategy; (K-slide-cl) REFUTED as stated; 5 of 6 flank shapes closed by reduced supports**)

Sibling of §(K-slide-cl)/§(K-slide-comb), answering the fan-out's **direction C**
(`notes/Pencil-fanout.md` §"Direction C"). Standing notation inherited (`G°` the
hub multigraph on `n = |V°|` hubs, lengths `ℓ`, `E° = E(G°) ∖ {e₀}`, split edge
`e₀ = bc` of length 3, decorations, the slide support `Σ`, the per-edge limit
chain span `S_P` of dimension `ℓ_P`, witnesses (W1)–(W4),
`T = ⟨C_ab, C_ac⟩`, the reciprocal twist `z`, the pitch `Q`, the Klein form `B`).
Three new pieces of notation:

- `R_P := S_P^{⊥_B}` — the **available bars** of `G°`-edge `P`, of dimension
  `6 − ℓ_P`. The hub-level limit rows for `P` are `m ↦ B(m(u) − m(w), ρ)`,
  `ρ ∈ R_P`, so a **stress** of the limit carrier is an assignment `ρ_P ∈ R_P`
  with `Σ_{P ∋ u} ±ρ_P = 0` in `Λ²K⁴` at every hub, and a **loaded stress with
  load `ω`** is one whose vertex sums vanish except for `±ω` at `b`, `c`.
- `α(u) := {ω : ω ∧ û = 0} = û ∧ K⁴` — the 3-dimensional **totally isotropic**
  α-space of `pt(u)`: `ω ∧ û` is the velocity the twist `ω` gives the point
  `pt(u)`, so `α(u)` = the twists fixing `pt(u)`.
- `π := plane(pt a, pt b, pt c)`, with `Λ²π̂ = ⟨C_ab, C_ac, C_bc⟩` — 3-dimensional
  (three sides of a non-degenerate triangle) and **totally isotropic** (coplanar
  lines meet). `α(a)` and `Λ²π̂` are the **only two** maximal totally isotropic
  3-spaces containing `T`, and `T = α(a) ∩ Λ²π̂` — the classical fact that the
  maximal isotropics of the Klein quadric are the α-planes (lines through a
  point) and β-planes (lines in a plane), and that a pencil determines its vertex
  and its plane uniquely.

**Verdict (2026-08-05, sixth pass; fan-out direction C).**

(i) **Direction C is REFUTED as a strategy — not merely unproven.** WW87's pure
condition is a **rank** certificate: by their Cor. 2.7 it is nonzero at a
realization iff that realization is `k`-isostatic, which for the limit carrier
is exactly **(W1) ∧ (W2)** (Step P0). The escape needs (W1)–(W4), and (W4) is
not a rank condition: it asks whether a distinguished kernel vector is **off the
Klein quadric**. Measured at four class shapes — θ(3,4,5) 14/14 seeds, `K5`
`(3,3,3,4,3,4,4,4,4,4)` 12/12, `K5` `(3,3,3,4,4,4,4,4,4,3)` 12/12, `K222`
octahedron 11/11 — **(W1) ∧ (W2) hold at every valid seed** (so the pure
condition is already known *not* to vanish identically there) **and `Q(z) = 0`
at every one**. A non-vanishing theorem for `C(G°-limit)`, however
un-specialized, would leave the escape unsettled at exactly the shapes it was
commissioned to reach. `pure.py --pure`.

(ii) **The right object, exactly — (PC-Z).** Under (W1)–(W3),
> **`Q(z) ≠ 0` ⟺ `V_bc ∩ Λ²π̂ = 0` and `V_bc ∩ α(a) = 0`.**

So (W4) is the non-vanishing of **two `6×6` incidence determinants** of `V_bc`
against two *fixed totally isotropic 3-spaces* — not of a rank determinant. This
is the pure-condition-shaped object direction C was reaching for, and it is a
different polynomial from `C(G°-limit)`. Proven-informally (Step P3), asserted
against the computed `Q(z)` at **every seed of every mode**.

(iii) **(PC1)–(PC3)/(PC-OBS): the chord obstruction, proven-informally — the
arc's first identically-vanishing-pitch theorem.** Every limit line of a "short
and slid" `G°`-edge passes through `pt(u)` or `pt(w)`, hence **meets the chord**
`C_uw`; so `C_uw ∈ R_P` (PC1). Chord bars in equilibrium are **precisely** the
projective **bar-and-joint** self-stresses of the *hub-point* framework on those
edges (PC2). A chord self-stress using `e₀` forces `V_bc ⊆ C_bc^{⊥_B}`, whence
`V_bc ∩ Λ²π̂ ≠ 0` and, by (PC-Z), **`Q(z) = 0` at every decoration** (PC3). The
governing invariant is therefore **`R_3`-dependence** — the generic
**3-dimensional bar-and-joint** rigidity matroid of the hub graph — a completely
different matroid from the 6-fold graphic union that (C6) is about.
`pure.py --chord`.

(iv) **(K-slide-cl) is REFUTED as stated.** At the `K5` 5-chromatic flank shapes
`(3,3,3,3,4,4,4,4,4,4)`, `(3,3,3,4,3,4,4,4,4,4)`, `(3,3,3,4,4,4,4,4,4,3)` —
explicit **tight + `hnoRigid`** class members with `hcard`/`htf`, exactly the
ones §(K-slide-comb) exhibited — and at **θ(3,4,5)**, the **full-support**
slide-in limit system fails (W4) (or (W3)) at **every** decoration by (iii). So
"generic decorations of the slide-in limit system satisfy (W1)–(W4)" is *false*
at class shapes, not merely open.

> **Two refutations, two mechanisms — do not conflate them.** The arc now
> carries two distinct negative results, and they are independent.
> §(K-slide-comb) (2026-08-05, fifth pass) refuted the collapse's
> **combinatorial antecedent** (K-slide-comb) class-wide: its *colouring*
> premise fails inside the class (`χ(K5) = 5`; acyclic 4-colourability is not
> implied by 3-degeneracy). What (iii)/(iv) refute is the **statement**
> (K-slide-cl) *itself*, at the full support, by the **chord obstruction**
> (PC-OBS) — an `R_3`-dependence mechanism with **nothing to do with
> colouring**, and one that would fire even if every class shape were
> acyclically 4-colourable. The two conditions first bite at the same shape
> (`K5`) by an arithmetic coincidence, not by a common mechanism — Step P4
> separates them.

(v) **But the slide support is the lever, and it clears the whole probed flank
list.** (S1) remark (iii) makes `Σ` free, and `E_chord(Σ)` **shrinks with `Σ`**
(an `ℓ = 3` edge is chord-obstructed iff ≥ 1 end is slid, an `ℓ = 4` edge iff
both are, `ℓ = 5` never). Dropping the slide at the `c`-side interiors produces
full **(W1)–(W4) witnesses** — which is all (S1) consumes, *one* witness — at all
three obstructed `K5` 5-chromatic flank shapes (2/3, 3/3, 3/3 sampled seeds), at
the **`K222` octahedron flank** (3/3) and at **θ(3,4,5)** (3/3). So the slide
device **closes** those splits, and the gap map's `χ(G°) ≥ 5` row, its `K222`
entry and (for θ(3,4,5)) its parallel-`G°`-edge row stop being uncovered. The
**6v11e acyclicity flank** is the one shape the *device* does not reach: it fails
**(W2)** (`dim V_bc = 2`) at all four nonempty probed supports, and only the
degenerate `Σ = ∅` (which is the `ε = 1` chart, where (S1) is **vacuous**) is
pitched. Its split closes anyway, by the (K-pitch) Step-0 one-witness argument —
full chart transfer certificates ((T1)–(T3) + `Q(r) ≠ 0`, `dim R_a = 1`, the (T2)
side conditions) at **11/11** valid seeds. `pure.py --support`. **This answers
§(K-flank) *Step F7* item 2**, which named reduced slide supports at the
structural flanks as the single most valuable follow-up its data pointed at.

(vi) **WW87 Thm 2.18 cannot transfer to the decoration variety** — direction C's
other half is independently dead. The decoration variety is a **proper closed
subvariety** of `∏_{P ∈ E°} Gr(6 − ℓ_P, 6)`, and Thm 2.18's
"packing ⟹ pure condition ≢ 0" is about the *generic point of the ambient
space*. Exhibited: at `P21` the free-bar system with the same multiplicities has
rank `15/15` (**independent**) and the (C6) packing exists, yet the
decoration-variety rows are **dependent at every support** ((S5), reproduced by
`kslide.py --flanks`). `pure.py --pure`.

(vii) **The parallel-`G°`-edge row is corrected in mechanism and in scope.**
(S5) proves a **(W1)** failure for two parallel **length-3** chains; that
mechanism **cannot occur inside the tight + `hnoRigid` class at all**, because a
parallel pair of lengths `(ℓ₁, ℓ₂)` is a cycle `C_{ℓ₁+ℓ₂}` of `G`, `C_k` is
rigid for `k ≤ 6` (R3), and a proper rigid subgraph contradicts `hnoRigid` — so
`ℓ₁ + ℓ₂ ≥ 7` and `(3,3)` is out (`P21` is thereby a **(K-res)** residual, not a
tight class member). At θ(3,4,5) — a parallel-edge shape that *is* tight +
`hnoRigid` — (W1) and (W2) **hold** at every probed seed and the full-support
obstruction is (W4) **by the chord stress** (two parallel bars `{e₀, the ℓ = 4
edge}` between `pt(b)` and `pt(c)` self-stress at *every* placement). And a
reduced support closes it. `pure.py --parallel`.

(viii) **Residual, unidentified.** Two (W4)/(W2) failures are *not* chord-stress
failures: the `K222` flank and the `K4` shape `(1,1,3,5,4,4)` fail (W4) with no
chord stress — measured cause `V_bc ∩ Λ²π̂ ≠ 0`, but **why** that codimension-1
incidence is forced there is open — and the **6v11e** flank's `dim V_bc = 2` has
no mechanism at all. Note `(1,1,3,5,4,4)` has `G° = K4`, so the residual
mechanism is *not* a dense-hub-graph phenomenon.

**What would change this.** *For (i)/(vi):* a reading of WW87 §2 under which the
pure condition sees more than isostaticity — Cor. 2.7 is explicit that it does
not. *For (ii):* an error in the two-maximal-isotropic-completions claim; it is
asserted per seed against the independently computed `Q(z)`. *For (iii):* an
error in the transversal bookkeeping (`C_uw ∈ R_P` is measured per edge per
decoration and cross-checked against the length/support rule on 90 instances) or
in the `★`-convention of the equilibrium identification (the chord stress is
assembled as an explicit row combination of the **actual** limit rows and its
covector checked to be a nonzero multiple of the `C_bc` load). *For (iv):* a
full-support decoration at one of the three `K5` shapes with `Q(z) ≠ 0` —
impossible by (PC3) unless `K5` is `R_3`-independent, which the Maxwell count
`10 > 3·5 − 6` forbids at *every* placement. *For (v):* the support menu is 5 of
the `2^{#slid interiors}` supports, so "not rescued" is not a verdict; a shape
where **no** support gives a witness would be the real class-level refutation,
and none is exhibited. *For (viii):* a mechanism for `V_bc ∩ Λ²π̂ ≠ 0` at
`K222`/`(1,1,3,5,4,4)` and for the 6v11e (W2) drop.

### Step P0 — what "the pure condition of the limit carrier" is, exactly

By (S2) the limit carrier is the hub-level serial-chain system: bodies at the
hubs of `G° − e₀`, one constraint `m(u) − m(w) ∈ S_P` per `P ∈ E°`, i.e.
`6 − ℓ_P` rows, `6n − 9` in total by tightness (Step C0). Close it up by adding
three rows `B(m(b) − m(c), ρ) = 0` for `ρ` in a **generic** 3-space `R₀`: the
system becomes `6(n−1) × 6n`, the body-bar shape of the multiplicity-weighted
`Ĝ` (`P` with multiplicity `6 − ℓ_P`, `e₀` included) that (C6) packs into six
spanning trees. Two facts fix the object.

- **The pure condition is the isostaticity determinant, and it sees (W1) ∧ (W2)
  and nothing more.** WW87 Prop. 2.6 makes `C(G) = det M(G, T)` a bracket
  polynomial; Cor. 2.7 says `C ≠ 0` at a realization iff it is `k`-isostatic.
  Adding `R₀`'s rows cuts `ker` by `dim V_bc − dim(V_bc ∩ R₀^{⊥_B})`, which for
  generic `R₀` is `dim V_bc`; so the closed-up carrier is isostatic (`ker` = the
  6 trivial twists) **iff** the `E°`-rows are independent ((W1), `dim ker = 9`)
  **and** `dim V_bc = 3` ((W2)).
- **"`C ≢ 0` on the decoration variety" is not a new statement.** The decoration
  variety is irreducible (a tower of affine-linear fibres, (S1)(e)), so
  `C ≢ 0` ⟺ some decoration is isostatic ⟺ (W1) ∧ (W2) generically. That is a
  *restatement* of half of (K-slide-cl), not a lever. A lever must be a
  **technique** for proving non-vanishing, and WW87 offers two: Cor. 2.7
  (pointwise — the restatement) and Thm 2.18 (combinatorial — Step P6 kills its
  transfer). Thm 2.18's own proof is a **specialization** (one shared coordinate
  frame per spanning tree), i.e. the tetrahedral collapse. So "un-specialized"
  can only mean "find an induction, or a better specialization"; it cannot mean
  "work with `C` directly".

### Step P1 — (PC1): on a short slid edge the chord is always a legal bar

> **(PC1)** *(proven-informally)* Under a slide support `Σ`, all limit lines of
> `G°`-edge `P = uw` meet the chord `C_uw = p̂t(u) ∧ p̂t(w)`, hence
> `C_uw ∈ R_P = S_P^{⊥_B}`, **iff**
>
>     ell = 1 : always            (the chain IS the chord)
>     ell = 2 : always            (both lines are hub-incident)
>     ell = 3 : at least one end slid
>     ell = 4 : both ends slid
>     ell = 5 : never.
>
> Call such an edge **chord-obstructed** and write `E_chord(Σ) ⊆ E°` for the set
> of them. At the full support `E_chord = {P ∈ E° : ℓ_P ≤ 4}`; at `Σ = ∅`
> (the `ε = 1` chart) `E_chord = {P : ℓ_P ≤ 2}`.

*Proof.* Two lines of `P³` meet iff `B = 0`; `pt(u)` and `pt(w)` both lie on
`C_uw`; so it suffices that every limit line pass through one of them. Read off
the limit-line rule ((S1)(b), the (S2) dictionary): a hub-incident hinge gives
the constant pencil line at its hub; a hinge with exactly one slid end gives
`p̂t(h) ∧ (the other point)`, through the hub `h` its slid interior collapsed to;
a slid–slid hinge gives the chord; an unslid–unslid hinge keeps its original
line, through neither hub. On `[u, y₁, …, y_{ℓ−1}, w]` the support touches only
`y₁, y_{ℓ−1}`, so only a *middle* hinge can fail to be hub-incident: `ℓ = 3` has
the one middle hinge `y₁y₂`, hub-incident as soon as either end is slid; `ℓ = 4`
has `y₁y₂` and `y₂y₃`, needing `y₁` resp. `y₃`; `ℓ = 5` has `y₂y₃` with neither
end ever slid, so it keeps a generic line missing the chord; `ℓ ≤ 2` has no
middle hinge. ∎

`ℓ = 5` is the one length that escapes — the same asymmetry §(K-slide-comb) Step
D4(b) saw from the other side (at `ℓ = 5` the transversal `R_P` need not be a
basis line).

### Step P2 — (PC2): chord bars in equilibrium are bar-and-joint self-stresses

> **(PC2)** *(proven-informally)* Put `ρ_P = λ_P · C_uw` on each
> `P ∈ E_chord(Σ)` and `0` elsewhere (legal by (PC1)). The resulting loaded-stress
> condition — vertex sums `0` at every hub except `±λ_{e₀} C_bc` at `b`, `c` — is
> **exactly** the self-stress condition of the **bar-and-joint framework**
> `(E_chord(Σ) ∪ {e₀}, pt)` in 3-space, with `e₀ = bc` an extra bar of
> coefficient `λ_{e₀}`.

*Proof.* The signed sum at hub `h` is `★(ĥ ∧ Σ_{P ∋ h} λ_P ô_P)` (`ô_P` = the
other end's homogenised point; the `★` is the harness's Euclidean-vs-Klein
bookkeeping — `rows_from_lines` pairs Euclideanly, so the legal per-edge
coefficient space is `S_P^{⊥_E} = ★R_P` and the chord contributes `★C_uw`; `★`
is linear and invertible, so it does not change the condition). It vanishes iff
`Σ_{P ∋ h} λ_P ô_P ∈ ⟨ĥ⟩`, i.e. affinely iff `Σ_{P ∋ h} λ_P = μ_h` and
`Σ_{P ∋ h} λ_P o_P = μ_h h`, i.e. iff `Σ_{P ∋ h} λ_P (o_P − h) = 0` — the
bar-and-joint equilibrium (the classical projective invariance of self-stresses).
At `b`, `c` the same computation leaves the residual `±λ_{e₀} ★C_bc`. ∎

So the obstruction is governed by the generic **3-dimensional bar-and-joint**
rigidity matroid `R_3` of the hub graph. This is the pass's structural punch
line: the collapse's combinatorics was a 6-fold **graphic-union** question
((C6), (C1)'s six forest classes); the invariant that decides the *pitch* is an
`R_3`-dependence question about the hub points. Different matroids, and (C6) —
uniform and proven — says nothing about this one.

**Decoration-free sufficient conditions.** A `λ` with `λ_{e₀} ≠ 0` exists at
generic hub points iff `e₀ ∈ cl_{R_3}(E_chord(Σ))`. Two cases need no genericity
at all:

- **Maxwell count.** If `F ⊆ E_chord(Σ) ∪ {e₀}` has `|E(F)| > 3|V(F)| − 6` then
  `F` self-stresses at *every* placement; if `F − e₀` is `R_3`-independent (so
  `F` is a circuit) the stress uses `e₀`. `K5` is the first instance: `10 > 9`,
  and `K5 − e` is generically isostatic.
- **Two parallel bars.** If `e₀` is `bc`-parallel to some `P ∈ E_chord(Σ)`, the
  two bars share both endpoints and `λ = (1, −1)` self-stresses at every
  placement. That is θ(3,4,5).

### Step P3 — (PC3)/(PC-Z): the two isotropic completions, and why a chord stress kills the pitch

The clean fact behind everything:

> **(PC-Z)** *(proven-informally)* `T = ⟨C_ab, C_ac⟩` (the pencil at `pt(a)` in
> `π`) is contained in exactly two maximal isotropic 3-spaces of `(Λ²K⁴, B)`:
> `α(a)` and `Λ²π̂`; both lie inside `T^{⊥_B}`; and `z` spans `V_bc ∩ T^{⊥_B}`.
> Hence, under (W1)–(W3),
>
> `Q(z) = 0 ⟺ z ∈ α(a) ∪ Λ²π̂ ⟺ V_bc ∩ α(a) ≠ 0 or V_bc ∩ Λ²π̂ ≠ 0.`

*Proof.* `Q(z) = 0` says `z` is a line extensor; `z ∈ T^{⊥_B}` says that line
meets both `a`-hinges, hence passes through `pt(a)` or lies in `π` (§(K-pitch)
Step 2's dichotomy (F-A)/(F-B)) — i.e. `z ∈ α(a)` or `z ∈ Λ²π̂`. Conversely both
spaces are totally isotropic, so any `z` in them has `Q(z) = 0`. For the second
equivalence: a maximal isotropic space is its own `B`-perp and contains `T`, so
`α(a), Λ²π̂ ⊆ T^{⊥_B}`; therefore any nonzero `y ∈ V_bc ∩ Λ²π̂` lies in
`V_bc ∩ T^{⊥_B} = ⟨z⟩`, giving `z ∈ Λ²π̂`; same for `α(a)`. ∎

`Λ²π̂ = ⟨C_ab, C_ac, C_bc⟩` is 3-dimensional whenever `pt a, pt b, pt c` are not
collinear (generic: `pt(a)` runs on `M = Π(b) ∩ Π(c)`, and `line(b,c) ⊆ Π(b)`
only if the panels are incident).

**The *reason* for the two-completions step is Witt's theorem — §(K-Λ) *Step 1*,
where it is derived independently.** (PC-Z) above stays the canonical
`V_bc`-level statement of the structural theorem and is not restated there; the
Witt argument is not restated here.

> **(PC3)** *(proven-informally)* A loaded stress with load `ω` forces
> `V_bc ⊆ ω^{⊥_B}`. With the chord stress of (PC2), `ω = C_bc ∈ Λ²π̂`, so
> `V_bc` and `Λ²π̂` both sit inside the 5-dimensional `C_bc^{⊥_B}`
> (`Λ²π̂` is isotropic), and `3 + 3 > 5` forces `V_bc ∩ Λ²π̂ ≠ 0`. By (PC-Z),
> `Q(z) = 0`. (If the containment is strong enough that `V_bc ⊆ Λ²π̂` — e.g.
> `V_bc = α(pt c)` at the `K5` shape `(3,3,3,3,4,4,4,4,4,4)` — the two
> `T`-conditions become dependent on `V_bc` and **(W3)** fails instead.)

*Proof of the first sentence.* A loaded stress says the functional
`m ↦ B(m(b) − m(c), ω)` is in the limit system's row space, hence vanishes on
its kernel, hence on `V_bc`. ∎

> **(PC-OBS)** *(proven-informally; the theorem)* Fix `(G°, ℓ, e₀)` and a support
> `Σ`. If `e₀ ∈ cl_{R_3}(E_chord(Σ))` at generic hub points, the slide-in limit
> system at support `Σ` fails **(W4)** — or (W3) — at **every** decoration: the
> reciprocal twist is a line in `plane(a,b,c)`, i.e. §(K-pitch) Step 2's failure
> mode **(F-B)**, realized structurally.

Two remarks. **(a)** This is the arc's first *proven* identically-vanishing-pitch
statement; every earlier (W4) obstruction was per-decoration observation, and the
(S5) parallel case was a (W1) statement. In particular it **explains** the `K5`
column of §(K-flank) *Step F6*'s table, where the full-support limit's degeneracy
at the structural flanks was measured (40 generic decorations per shape, an
independent driver) but had no mechanism: at the all-`{3,4}` `K5` shape
`V_bc = α(pt c)`, which is the strong-containment branch of (PC3), and the
(W3)-failure profile F6 records is exactly what (PC3) predicts there. The two
drivers agree at every shape they share — evidence, not redundancy — and the
mathematics is not repeated in F6. **(b)** It cannot threaten `hK` or the
pencil conjecture: it is a property of the *limit*. At `ε = 1` no interior is
slid, `E_chord = {ℓ ≤ 2}`, and the `K5` flank's chart-level transfer certificate
((T1)–(T3) with `Q(r) ≠ 0`) passes at every probed seed.

### Step P4 — where the chord obstruction bites

At the full support the necessary condition for the `G°`-local device is

> **(K-chord)** `e₀ ∉ cl_{R_3}(G°_{≤4} ∖ {e₀})` at generic hub points.

Length bookkeeping puts this exactly where the collapse's flanks are. Tightness
is `Σ_{E(G°)} ℓ = 6(m − n + 1)` with `m = |E(G°)|`; all `ℓ ≥ 3` gives
`m ≥ 2n − 2` and all `ℓ ≤ 4` gives `m ≤ 3n − 3`. Maxwell dependence needs
`m ≥ 3n − 5`, so for **simple** `G°`:

| `n` | `3n − 5` | max simple `m` | chord-obstructible with all `ℓ ≤ 4`? |
|---|---|---|---|
| 4 | 7 | 6 | **no** — the whole `K4` stratum is safe |
| 5 | 10 | 10 | **only `G° = K5`** |
| 6 | 13 | 15 | yes for `m ≥ 13`; `K222` (12) and 6v11e (11) are **not** |

Exhaustively over the 23 candidate hub graphs with `|V°| ≤ 6` (simple,
connected, min degree `≥ 3`), `R_3`-dependence holds **exactly** for the
Maxwell-overbraced ones — **5 dependent, 18 independent**: `|V°| = 5, |E°| = 10`
(`K5`, stress dim 1) and four at `|V°| = 6` with `|E°| ∈ {13, 13, 14, 15}` (stress
dims 1, 1, 2, 3) (`pure.py --chord`, census block). So the collapse's
four-colour ceiling and the chord
obstruction's `R_3` ceiling are **different conditions that first bite at the
same shape** — which is why the collapse's flank *looked* like the class's
flank. It is not the same: `K222` and 6v11e are collapse flanks with **no** chord
obstruction, and the two `K5` shapes carrying an `ℓ = 5` edge
(`(3,2,2,2,3,4,5,5,5,5)`, `(3,1,1,2,5,5,4,5,5,5)`) are collapse flanks that the
**full-support** device witnesses, pitched, at every probed seed. This is the
precise sense in which the fifth pass's refutation of (K-slide-comb) (colouring)
and this pass's refutation of (K-slide-cl) (`R_3`-dependence) are *independent*
results that happen to share their smallest witness.

Full-support verdicts (`pure.py --flanks`, 10–11 valid seeds per shape):

| shape | chord stress? | full-support verdict |
|---|---|---|
| dbl-subdiv `K4`; `K4` mixed `(3,4,2,3,3,3)` (controls) | no | PITCHED |
| `K5` `(3,3,3,3,4,4,4,4,4,4)` | yes | (W3) fails ×8, (W1) fails ×2 — `V_bc = α(pt c)` |
| `K5` `(3,3,3,4,3,4,4,4,4,4)`; `(3,3,3,4,4,4,4,4,4,3)` | yes | (W4) fails ×10 each |
| `K5` `(3,2,2,2,3,4,5,5,5,5)`; `(3,1,1,2,5,5,4,5,5,5)` | no | **PITCHED** ×11 each |
| 6v11e acyclicity flank | no | (W2) fails ×10 — mechanism open |
| `K222` octahedron flank | no | (W4) fails ×10 — `V_bc ∩ Λ²π̂ ≠ 0`, cause open |
| `K4` `(1,1,3,5,3,5)`; `(1,1,3,5,5,3)` (menu-blocked) | no | PITCHED ×10 each |
| `K4` `(1,1,3,5,4,4)` (menu-blocked) | no | (W4) fails ×10 — cause open |
| θ(3,4,5) | yes | (W4) fails ×11 |

Every row that §(K-flank) *Step F6* also measured agrees with it, on a driver
written independently (`flanks.py --limit` samples 40 non-aligned decorations per
shape; `pure.py --flanks` samples 10–11 chart seeds and additionally records the
chord predictor): `K5` (W3), 6v11e (W2) `dim V_bc = 2`, `K222` (W4), the
menu-blocked `K4 (1,1,3,5,3,5)` pitched.

### Step P5 — the invariant mismatch: why direction C cannot close the escape

Direction C asked for `C(G°-limit) ≢ 0` on the decoration variety; by Step P0
that is (W1) ∧ (W2) generically. The table has four class shapes where
(W1) ∧ (W2) hold at **every** valid seed and `Q(z) = 0` at every one. Hence:

> **(PC5)** A theorem "`C(G°-limit) ≢ 0` on the decoration variety for every
> class shape" would **not** close (K-slide-cl), (K-pitch) or `hK`. The escape's
> obstruction at the flanks lives in (W4), which the pure condition does not see.

The reason is structural. `C` is a determinant asking whether a kernel is as
small as the count allows. `Q(z)` asks whether a *particular* kernel vector is
off a *quadric* — by (PC-Z), whether `V_bc` misses two fixed isotropic
3-spaces. The Klein quadric is invisible to the matroid; it is exactly the extra
structure that makes body-hinge geometry more than body-bar combinatorics, and
exactly what (C6)'s uniform packing cannot reach. Direction C's premise ("the
obstruction the collapse hit is a property of the specialization, not of the pure
condition") is right about the collapse's four-point cap and wrong about the
*device*: the device has a second, pitch-side obstruction, and the collapse's
failure at `K5` was partly a symptom of it.

### Step P6 — WW87 Thm 2.18 does not transfer to the decoration variety

> **(PC6)** *(proven-informally)* The decoration variety maps into
> `∏_{P ∈ E°} Gr(6 − ℓ_P, 6)` with image a **proper closed subvariety** — `R_P`
> is determined by the hub points, the panels and a handful of per-edge
> parameters, and the hub points are **shared** by every edge at those hubs (an
> `ℓ = 3` edge's `R_P` is a point of the 9-dimensional `Gr(3,6)` cut out by two
> hub points and two pencil parameters). So Thm 2.18's equivalence "pure
> `k`-condition ≢ 0 ⟺ `k` edge-disjoint spanning trees", a statement about the
> generic point of the ambient realization space, does not descend.

*Witness, not merely a worry.* `P21` (`G° = K4 − 02` with `23` doubled, lengths
`(3; 3,3; 4,5,3,3)`; a **(K-res)** residual since its parallel `(3,3)` pair is a
rigid `C₆`). The (C6) packing exists (min-max slack `≥ 0`, explicit packing) and
the **free-bar** system with the same multiplicities `6 − ℓ_P` is
**independent** (rank `15/15` at seeded random screws) — so Thm 2.18's conclusion
holds in the ambient space. Yet the decoration-variety rows are **dependent at
every support** ((S5): coincident chords put a repeated line in a 6-hinge cycle;
reproduced by `kslide.py --flanks`). Same graph, same multiplicities, packing
satisfied, pure condition of the constrained family identically zero.

This also explains why (C6) — genuinely uniform, genuinely Phase-12/13/14
reachable — buys nothing here: it certifies the **ambient** hypothesis of a
theorem whose conclusion is about the ambient generic point.

### Step P7 — the support lever, the locality/pitch trade, and the rescued flanks

`E_chord(Σ)` shrinks with `Σ` (PC1), so the obstruction is support-dependent and
the device is not dead — it is *traded off*:

> **The locality/pitch trade.** The slide buys `G°`-locality by pushing chain
> lines through hub points. Pushing lines through hub points is exactly what
> makes the chord a legal bar. Chord bars generate `R_3` self-stresses as soon as
> the chord-obstructed hub graph is 3-dimensionally dependent, and any such
> stress through `e₀` puts `z` in the isotropic `Λ²π̂`. **The degeneration that
> makes the problem combinatorial is the same degeneration that kills the
> pitch.** The two extremes: `Σ` maximal is the collapse's `G°`-local system
> (maximal chord obstruction); `Σ = ∅` is the `ε = 1` chart itself
> (`E_chord = {ℓ ≤ 2}`, no locality) — which is (K-pitch) again.

**Rescues (`pure.py --support`; menu: full; drop the slide at `c`; at `b`; at
both; nowhere).** The rescue criterion is `≥ 1` seed with (W1)–(W4), because that
is exactly what (S1) consumes — *one* exact limit witness, not a majority. This
is the probe §(K-flank) *Step F7* item 2 called for, and it is the direction's
one positive class-side result.

- `K5` `(3,3,3,3,4,4,4,4,4,4)`: "no slide at `c`" removes the three `ℓ = 4` edges
  at `c` from `E_chord`, leaving the three `ℓ = 3` edges at `b` — a star on
  `{b,2,3,4}` not even spanning `pt(c)`, so `e₀ ∉ cl_{R_3}`; the chord stress is
  gone and full witnesses appear (2/3 seeds; the third has an unrelated (W1)
  drop). **Slide device closes it.**
- `K5` `(3,3,3,4,3,4,4,4,4,4)`, `(3,3,3,4,4,4,4,4,4,3)`: likewise, 3/3.
  **Closed.** (Note "no slide at `b`" removes the chord stress too but stays
  `Q(z) = 0` — the residual mechanism of Step P8 taking over; only the `c`-side
  reduction clears both.)
- `K222` octahedron: "no slide at `c`", 3/3. **Closed** — even though its
  full-support failure was *not* a chord stress.
- θ(3,4,5): "no slide at `c`" and "no slide at `b`", 3/3 each. **Closed** — and
  this is the parallel-`G°`-edge shape the gap map lists as reachable only by the
  companion forms ((K-Λ) at `ℓ = 4`). A slide witness reaches it directly.
- 6v11e acyclicity flank: (W2) fails (`dim V_bc = 2`) at **all four** nonempty
  supports. Only `Σ = ∅` is pitched — but that is the `ε = 1` chart, where the
  slide is the identity and **(S1) is vacuous**: the "witness" is just a chart
  seed. The *split* is nevertheless closed, by (K-pitch) Step-0 one-witness
  logic: full chart transfer certificates ((T1)–(T3) + `Q(r) ≠ 0`, which also
  check `dim R_a = 1` and the (T2) side conditions that (W1)–(W4) do not) at
  **11/11** valid seeds. The **slide device** does not reach this shape and no
  mechanism for its (W2) drop is known.

Three riders. **(a)** The menu is 5 of `2^{#slid interiors}` supports; "not
rescued" is not a verdict. **(b)** A reduced support costs precisely what the
collapse was buying: unslid interiors survive as chart coordinates, so a
*class-uniform* argument on the reduced-support carrier has strictly more
parameters than the collapse's decorated multigraph. The rescue is a **per-shape
witness engine**, not a class program. **(c)** `Σ = ∅` must never be counted as a
slide-device rescue — it is the chart, and (S1) says nothing there; the driver
labels that row `CHART … ((S1) is VACUOUS here)` for exactly this reason.

### Step P8 — the residual mechanism, localized but open

The refuted guess, recorded so it is not re-made: `C_bc ∈ V_bc` (the chord as a
relative twist) would force `z ∝ C_bc` and `Q(z) = 0`, but it is **false** at
`K222`, at `K4 (1,1,3,5,4,4)` and at the `K5` shapes 2–3 — it holds only at `K5`
`(3,3,3,3,4,4,4,4,4,4)`, where `V_bc = α(pt c) ∋ C_bc` anyway. By (PC-Z) the
right question is sharper and single-valued:

> **Open.** At `K222` and at `K4 (1,1,3,5,4,4)`, why is `V_bc ∩ Λ²π̂ ≠ 0` — a
> codimension-1 incidence between a 3-space that moves with the whole decoration
> and the `Λ²` of the split triangle's plane — forced at every decoration, with
> **no** chord stress present? At the `K5` shapes it is forced by (PC3); here
> nothing explains it. And at 6v11e, why does `dim V_bc` drop to 2?

These are the two honest gaps of this pass, and they are now *well-posed*:
(PC-Z) reduces "why does the pitch vanish?" to "why does `V_bc` meet one of two
named isotropic 3-spaces?".

### Step P9 — what a class proof needs now

1. **The combinatorial residue is replaced, not removed.** As the *governing*
   combinatorics, (K-slide-comb)'s colouring/menu problem is superseded by
   **(K-chord)**: per shape, a support `Σ` with `e₀ ∉ cl_{R_3}(E_chord(Σ))`.
   (The supersession is of the *role*, not of a shared mechanism: the fifth
   pass refuted (K-slide-comb) by colouring, this pass refutes (K-slide-cl) by
   `R_3`-dependence — see the verdict's two-refutations note.) Unlike
   (K-slide-comb) this lives in a matroid with **no combinatorial
   characterisation** (generic 3-dimensional rigidity), so it is checkable per
   shape by exact rank but not obviously by a class argument.
2. **A class proof must handle both flanks of the trade.** Large `Σ` gives
   `G°`-locality and risks (PC-OBS); small `Σ` avoids it and loses locality. The
   natural repaired statement quantifies `∃Σ` — and even that is only
   *necessary*: 6v11e (and the `K222`/`K4` residual mechanism) show at least one
   further obstruction.
3. **(C6)'s role is downgraded** (not its status): it certifies the ambient
   hypothesis of a theorem that does not transfer (P6), and it concerns the wrong
   matroid for the pitch (P2).
4. **Option B is NOT required by this direction.** Everything above is linear
   algebra on the limit carrier's decoration variety plus (S1) for transfer; no
   stress-as-chart-rational-function object appears (the pitch sits on the motion
   side by (T1)/(T2), and the chord stress is a stress of the *limit* system in
   closed form). So direction C was pursuable under the standing adjudications —
   it is simply aimed at the wrong invariant. That is the verdict, not a
   permission problem.
5. **The honest next question**, if the arc continues on the slide device: is
   `∃Σ` with (K-chord) *and* (W1)–(W4) attainable at every class shape? That is a
   per-shape finite search the driver already performs on a 5-support menu;
   widening the menu and sweeping the `|V°| ≤ 6` strata is cheap, and would
   either produce a genuine class-level refutation or a much larger covered
   sub-class. 6v11e is where to start.

### Verification

`notes/scripts/w4/pure.py` (tracked, new this pass; exact-ℚ, on top of
`repin.py`/`pitch.py`/`kslide.py`/`kslidecomb.py`; every sampled object carries a
rank/dimension assert; every shape is re-certified tight-count + `def = 0` +
`hnoRigid`; every limit system is built by `kslide.path_limit_lines` from an
honest `repin.seed_probe` chart seed — a hand-rolled "generic decoration" need
not be chart-realizable and would not transfer under (S1); `PYTHONHASHSEED=0`;
the one randomness literal is `RNG_SEED = 20260805`). **(PC-Z) is asserted at
every seed of every mode** (the computed `Q(z) == 0` against
`V_bc ∩ Λ²π̂ ≠ 0 ∨ V_bc ∩ α(a) ≠ 0`). Reproduce, from the repo root and with
`PYTHONHASHSEED=0`: `python3 notes/scripts/w4/pure.py --chord | --flanks |
--support | --pure | --parallel`.

| driver | ~time | what it asserts |
|---|---|---|
| `--chord` | 45 s | (PC1) as a length/support rule against the *measured* `C_uw ∈ R_P`, 90 `G°`-edge instances over 6 shapes; (PC2)+(PC3) by assembling the chord stress as an explicit row combination of the actual limit rows and checking its covector is a nonzero multiple of the `C_bc` load, then `z ∈ Λ²π̂` and `Q(z) = 0`; the biconditional "chord stress present ⟺ `V_bc ⊆ C_bc^{⊥_B}`"; and the **census**: over the 23 candidate hub graphs with `|V°| ≤ 6`, `R_3`-dependence ⟺ Maxwell-overbraced, smallest `K5` |
| `--flanks` | 385 s | full-support (W1)–(W4) at 13 shapes (2 controls, 5 `K5`, 6v11e, `K222`, 3 menu-blocked `K4`, θ(3,4,5)) with the chord predictor asserted against each verdict, and the residual-mechanism shapes printed by name |
| `--support` | 384 s | the 5-support menu at 3 `K5` shapes, 6v11e, `K222`, θ(3,4,5); rescue = `≥ 1` full witness at a **nonempty** support; `Σ = ∅` is reported separately as the chart (where (S1) is vacuous) and then the chart transfer certificate ((T1)–(T3) + `Q(r) ≠ 0`) is run and reported |
| `--pure` | 187 s | the invariant mismatch: (W1) ∧ (W2) at every valid seed while `Q(z) = 0` at every one, at 4 class shapes (14/14, 12/12, 12/12, 11/11); plus the free-bar contrast (rank `= 6n − 9`, independent) against (C6) at θ(3,4,5), `P21`, `K5` |
| `--parallel` | 4 s | at θ(3,4,5): (W1), (W2) hold, chord stress through `e₀` present, `z ∈ Λ²π̂`, `Q(z) = 0`, and the surviving `(4,5)` parallel pair's chain spans summing to dimension 6 (so **no** (S5) cycle stress); plus `def(C_k) = 0 ⟺ k ≤ 6`, hence `hnoRigid ⟹ ℓ₁ + ℓ₂ ≥ 7` on parallel pairs |

**Confidence verdict: direction C REFUTED as a strategy** — the pure condition is
a rank certificate (WW87 Cor. 2.7) and the escape's obstruction at the uncovered
flanks is **(W4)**, measured at four class shapes where the rank half holds at
every sampled decoration; **and WW87 Thm 2.18 does not transfer** to the
decoration variety (proper subvariety; `P21` exhibits the failure with (C6)
satisfied). **(PC-Z) proven-informally** — the exact reformulation
`(W4) ⟺ V_bc ∩ (Λ²π̂ ∪ α(a)) = 0`, which is the pure-condition-shaped object
direction C was reaching for and is *not* `C(G°-limit)`.
**(PC1)–(PC3)/(PC-OBS) proven-informally** — the arc's first
identically-vanishing-pitch theorem, governed by `R_3`-dependence of the
hub-point framework on the chord-obstructed edges, with an exhaustive
`|V°| ≤ 6` census. **(K-slide-cl) REFUTED as stated** at three `K5` class shapes
and θ(3,4,5) under the full support — a **statement**-level refutation by a
mechanism independent of §(K-slide-comb)'s **antecedent**-level one (colouring);
the parallel-`G°`-edge row's mechanism
corrected and the (S5) `(3,3)` mechanism proven **impossible** inside tight +
`hnoRigid`. **Five flank shapes CLOSED by reduced-support (S1) witnesses** — all
three obstructed `K5` 5-chromatic shapes, `K222`, and θ(3,4,5) — and the sixth,
the **6v11e acyclicity flank**, closed by its chart transfer certificate (11/11)
though the slide *device* fails there at every nonempty probed support. So every
probed §(K-slide-comb) Step-D5 flank shape now has its split closed, per shape,
and §(K-flank) *Step F7* item 2 is answered. **Open:** 6v11e's (W2) drop; the
`K222` / `K4 (1,1,3,5,4,4)` `V_bc ∩ Λ²π̂ ≠ 0`
coincidence; and whether `∃Σ` with (K-chord) + (W1)–(W4) is class-uniform.
**Option B is not required** by this direction.

## §(K-Λ) — the Λ-compression's quadric: a two-hyperplane factorization, and why (K-Λ) collapses onto (K-wit) (**(K-Λ) REFUTED as an independent gap; `ℓ ∈ {5,6}` refuted through the (T5) frame**)

Answering the fan-out's **direction B** (`notes/Pencil-fanout.md` §"Direction B").
Read against §(K-pitch) *Steps 0–5b*, whose notation it inherits verbatim.

**Headline, stated up front because it is a correction.** (K-Λ) was recorded
(§(K-pitch) *Step 5b*) as *"some target-rank chart seed's far covector `λ` avoids
the local quadric `{Φ_loc = 0}`"*, with the flagged risk *"a companion habitat
whose `Φ_loc` is the zero form"*. Both halves of that framing are wrong:

- `Φ_loc` is **never** the zero form. It is never a full-rank quadric either: it
  is always a **rank-2** form, the product of two *distinct rational linear*
  forms in `λ`. The flagged degeneration is impossible; there is nothing to prove
  on the non-degeneracy side. **(Λ1)** below is the exact bracket identity.
- Consequently "avoid the quadric" is "avoid two hyperplanes". And once the one
  local freedom that leaves `V_bc` untouched — `pt(a)` sliding along the meet
  line `M`, (T4)'s freedom — is used, the set of far covectors that are bad for
  the **whole** `a`-line shrinks from two hyperplanes to exactly **two points**
  of `P³`, and those two points are:
  `λ ∝ p⁺` ⟺ `V_bc ⊆ C(M)^{⊥B}` — which by (T3) **is** the genuine escape
  failure; and `λ ∝ q` ⟺ `V_bc ⊆ C(bc)^{⊥B}` — whereupon (T1) forces
  `★r ∝ C(bc)` and **route A escapes outright**.

So: **(K-Λ) at a length-4-companion split is *equivalent* to (K-wit) there.** The
pitch certificate is blind only where the escape actually fails. (K-Λ) is
therefore **not an independent gap** and no local argument can close it —
closing it *is* closing (K-wit). What the analysis does buy is positive and
standalone: the length-3 bracket **monomial** of §(K-pitch) *Step 5* becomes, at
length 4, a **product of two bracket-linear forms in the far covector**, whose
two factors are exactly (T2)'s two failure modes; the length-3 case gets a
two-line proof that explains its five brackets; both bad far covectors turn out
to lie on **one line** of `P(S*)`, giving the far-side sufficient condition
**(OUT)** (*Step 5a*); and the `ℓ ∈ {5,6}` continuation is **refuted** through
this frame, with the obstruction located exactly.

### Standing notation (on top of §(K-pitch))

Split chain `b–v–a–c` at a hard-stratum target-rank `G′`-seed (`b, c` hubs,
`dim R_a = 1`); `H := G − v − a`; `V_bc` the relative twist system (`dim = 3`);
`T := ⟨C_ab, C_ac⟩`; `B(x,y) = ⟨x, ★y⟩`, `Q(x) = B(x,x)`;
`M := Π(b) ∩ Π(c)` the meet line, `pt(a) ∈ M`, and `π_a := plane(a,b,c)`.
`α_p := Λ²(lines through p)` and `β_π := Λ²(lines in π)` — the two families of
maximal isotropic 3-spaces (α- and β-planes) of the Klein quadric. (These are
§(K-pure)'s `α(u)` and `Λ²π̂`: `α_{pt(a)} = α(a)` and `β_{π_a} = Λ²π̂`.)

A **length-4 companion** is a path `b–x₁–x₂–x₃–c` of `H` with lines
`C_i := C(x_{i−1}x_i)` (`x₀ = b`, `x₄ = c`) and `S := ⟨C₁,…,C₄⟩`; path-sum
containment (§(K-pitch) *Step 1a*) gives `V_bc ⊆ S`, and `λ ∈ S*` is the
annihilator of `V_bc` in the `C`-basis. Five bracket rows, all 4-point brackets
via the pairing dictionary `B(C(uv), C(pq)) = [u,v,p,q]`:

```
m_i = [x_{i−1}, x_i, a, b]     (m₁ = 0: C₁ and C_ab meet at pt(b))
n_i = [x_{i−1}, x_i, a, c]     (n₄ = 0: C₄ and C_ac meet at pt(c))
q_i = [x_{i−1}, x_i, b, c]     (q₁ = q₄ = 0: C₁, C₄ meet line(bc))
s_i = [x_{i−1}, x_i, a, w]     (w any point off π_a)
p⁺_i = [x_{i−1}, x_i, M₀, M₁]  (M₀, M₁ two points spanning M)
```

`cof(u)` := the Laplace cofactor vector of the `3×4` matrix `[u; m; n]` (the
existing `pitch.cross4`), so `z(λ) = Σ_i cof(λ)_i C_i` is the (T5)
Λ-compressed reciprocal twist and `Φ_loc(λ) := Q(z(λ))`.

**(Λ0) the named local genericity — all of it explicit brackets.**
(a) `rank{C₁..C₄} = 4`; (b) `S ∩ T = 0`; (c) `rank[m; n] = 2`
(⟺ `dim(S ∩ T^{⊥B}) = 2`); (d) **panels mutually non-incident**,
`pt(c) ∉ Π(b)` *and* `pt(b) ∉ Π(c)` (the §(K-pitch) *Step 6a* chart condition,
needed in **both** directions — see *Step 6*); (e) `C(M) ∉ S`;
(f) **`p⁺₂, p⁺₃ ≠ 0` and `q₂, q₃ ≠ 0`** — i.e. neither middle companion line
`C₂ = C(x₁x₂)`, `C₃ = C(x₂x₃)` meets `M`, and neither meets `line(bc)`. (The
outer entries vanish *structurally*: `C₁ ⊆ Π(b)` and `C₄ ⊆ Π(c)`, both panels
contain `M`, and two lines of one plane always meet — so `p⁺ = (0, p⁺₂, p⁺₃, 0)`
and `q = (0, q₂, q₃, 0)` always. (f) is exactly the span condition of *Step 3*;
the equivalence is asserted both ways per frame, and its necessity is
*constructed* in *Step 6*.)

Each clause is an open condition on the **local** chart of the frame
`{b, x₁, x₂, x₃, c, a, Π(b), Π(c)}`, which is the same irreducible variety for
every class habitat carrying a length-4 companion — the far graph enters the
frame only through (i) which of `x₁, x₂, x₃` are hubs and (ii) how many *far*
hub neighbours each frame hub has (`≤ 2` in total, by `hcard`), each of which
merely shrinks that hub's normal space to a generic subspace. So exact
witnesses across those finitely many strata certify (Λ0) generically for the
whole class; that is what the `--span` battery is: **38 strata** — the 2³ hub
patterns of `(x₁,x₂,x₃)` × far-hub counts `0/1/2` at `b, c`, plus, for each
pattern with a companion hub, two strata that additionally load the *companion*
hubs with `1` and with the maximal `2` far hub neighbours (the tightest
stratum: those normals are then pinned up to scale).

> **(Λ0) IS NOW PROVEN AT THE GENERIC POINT — and the 38 strata turn out to be
> irrelevant there** (2026-08-05, `M2 --script notes/scripts/m2/lambda0.m2`).
> The paragraph above is the *argument*; it is now executed rather than
> sampled. Gauge `ν_b = e₀*`, `ν_c = e₁*` (GL(4) is transitive on ordered pairs
> of independent covectors), so `Π(b) = {X₀=0}`, `Π(c) = {X₁=0}`,
> `M = ⟨e₂,e₃⟩`, `pt(a(t)) = e₂ + t·e₃`; the residual group then puts
> `P_b = e₁`, `P_c = e₀` **whenever (Λ0d) holds**, leaving 14 free coordinates
> (`x₁ ∈ Π(b)`, `x₃ ∈ Π(c)`, `x₂` free, `w` free). On that slice:
>
> - the bracket rows have **closed forms**
>   `p⁺ = (0, −u₁y₀, −y₁v₀, 0)` and `q = (0, u₃y₂−u₂y₃, y₃v₂−y₂v₃, 0)`,
>   so the structural zeros `p⁺₁ = p⁺₄ = q₁ = q₄ = 0` are visible rather than
>   argued, and (Λ0f)'s four brackets are explicit monomials/`2×2` brackets;
> - **every clause (a)–(f) is a nonzero polynomial**, hence holds on a dense
>   open subset — this is what replaces "certified generic by exact witnesses
>   in all 38 strata";
> - **the strata do not enter.** A stratum fixes which frame nodes are hubs and
>   how many far hub neighbours they carry; neither datum appears in any (Λ0)
>   quantity, and every stratum's frame data can be *completed* from a point of
>   the slice (a companion hub takes the panel `plane(x_{i−1},x_i,x_{i+1})`,
>   which satisfies the pencil condition there by construction; a far hub
>   neighbour is a free far-graph point, so it is placed inside that panel, and
>   `hcard` caps the count at 2 so the normal space never drops below dimension
>   1). So each stratum maps **onto a dense subset of one irreducible variety**
>   — driver block (P6), and the *class-uniformity bridge* of the verdict below.
>
> The gauge **consumes (Λ0d)**, so the driver's block (P7) re-runs the core with
> only `ν_b, ν_c` gauged (20 indeterminates): (Λ0d) reappears there as the
> non-vanishing of `ν_b·P_c` and `ν_c·P_b`, and the structural zeros,
> degree bounds and containments all survive — the `P_b`/`P_c` half of the
> gauge is not load-bearing.

### Step 1 — Witt: the isotropic locus of `T^{⊥B}` is `α_a ∪ β_{π_a}`

`T` is 2-dimensional and totally `B`-isotropic (both lines pass through
`pt(a)`), and the Klein form on `Λ²K⁴` is **split of Witt index 3**. Hence
`dim T^{⊥B} = 4`, `T ⊆ T^{⊥B}`, and `T^{⊥B}/T` is nondegenerate of dimension 2
and index `3 − 2 = 1`: a **hyperbolic plane**. `Q` descends to the quotient
(`Q(x + t) = Q(x)` for `x ∈ T^{⊥B}`, `t ∈ T`), a hyperbolic plane has exactly
two isotropic lines, both rational, and their preimages are two *maximal*
isotropic 3-spaces containing the pencil `T`. The only maximal isotropics
containing the pencil of lines through `pt(a)` in `π_a` are `α_{pt(a)}` and
`β_{π_a}`. Therefore

> **(Λ0′)** `{x ∈ T^{⊥B} : Q(x) = 0} = α_{pt(a)} ∪ β_{π_a}`.

This is (T2)'s failure dichotomy *(F-A)*/*(F-B)*, now with its reason: Witt's
theorem, not a case analysis.

**Relation to (PC-Z) — the same structural theorem, derived independently; not
restated here.** §(K-pure) *Step P3*'s **(PC-Z)** is the canonical, `V_bc`-level
statement of this fact (in its notation `α(a) = α_{pt(a)}` and
`Λ²π̂ = β_{π_a}`), derived there from the classical α/β-plane classification of
the Klein quadric; the Witt argument above is its **reason**. The two
derivations were produced independently — fan-out directions C and B, neither
consuming the other — and agree; that is **evidence, not a second result**. Read
(PC-Z) for the `V_bc`-level form; it is not restated here, and the Witt argument
is not restated there.

Two things fall out immediately.

**(i) Why `ℓ = 3` closes — a two-line replacement for §(K-pitch) *Step 5*'s
monomial.** `z` spans `V_bc ∩ T^{⊥B} ⊆ S ∩ T^{⊥B}`, so if
`S ∩ α_a = S ∩ β_{π_a} = 0` then `Q(z) ≠ 0` for the trivial reason that
`z ≠ 0`. At a length-3 companion `S = V_bc` is 3-dimensional and
`dim(S ∩ α_a) = 3 + 3 − 6 = 0` generically — likewise `β`. So **Step 5's
five-bracket monomial is the coordinate form of two transversality
conditions**, and the closure at θ(3,3,6)-type splits needs no monomial
computation at all. (Exact: `--habitat`, θ(3,3,6), both intersections `0` and
`Q(r) ≠ 0` at 3/3 seeds.)

**(ii) The obstruction, indexed by companion length.**
`dim(S ∩ α_a) = dim(S ∩ β_{π_a}) = k − 3` at a length-`k` companion
(`= 0, 1, 2, 3` for `k = 3, 4, 5, 6`; exact at 3 frames each,
`--l56`). `k = 4` is the **last** length at which these are 1-dimensional —
i.e. the last length at which "`V_bc` *meets* the intersection" is the same
condition as "`V_bc` *contains* it". That single fact is why the argument below
closes at `k = 4` and provably cannot at `k ≥ 5` (*Step 7*).

### Step 2 — (Λ1): `Φ_loc` factors into two bracket-linear forms

At `k = 4`, put

> `ω⁺ := cof(s)` — spans `S ∩ α_{pt(a)}`: **the unique line of the companion
> span through `pt(a)`**;
> `ω⁻ := cof(q)` — spans `S ∩ β_{π_a}`: **the unique line of the companion
> span lying in `plane(a,b,c)`**.

(Both are `cof(·)`-shaped because `α_a = ⟨C_ab, C_ac, C(a,w)⟩` and
`β_{π_a} = ⟨C_ab, C_ac, C(bc)⟩`, so membership is the vanishing of `m·ω`,
`n·ω` and one further bracket row.) Both lie in `N := S ∩ T^{⊥B}`, which
under (Λ0a–c) is 2-dimensional and — by Step 1 and `S ∩ T = 0`, so that
`N ≅ T^{⊥B}/T` as quadratic spaces — a **hyperbolic plane**. So `ω⁺`, `ω⁻` are
its two isotropic lines: distinct, rational, and `B(ω⁺, ω⁻) ≠ 0`.

> **(Λ1)** `(q·ω⁺)² · Φ_loc(λ) = −2 · B(ω⁺, ω⁻) · (λ·ω⁺) · (λ·ω⁻)`,
> an identity of quadratic forms in `λ`, with *every* entry a polynomial in the
> 4-point brackets of the six local points `{b, x₁, x₂, x₃, c, a}` (plus `w`,
> which cancels projectively). In particular `Φ_loc` is a **nonzero rank-2**
> form and `{Φ_loc = 0}` is the union of the two **distinct rational
> hyperplanes** `{λ·ω⁺ = 0}` and `{λ·ω⁻ = 0}`.

*Proof.* `λ ↦ cof(λ)` is linear with kernel `⟨m, n⟩` and image `N` (the two
conditions `m·ω = n·ω = 0` say exactly `z ∈ T^{⊥B}`). In the basis
`(ω⁺, ω⁻)` of `N` write `cof(λ) = α(λ)ω⁺ + β(λ)ω⁻`; `cof(λ) ⊥ λ` and
`m·ω± = n·ω± = 0` give `α(λ)(λ·ω⁺) + β(λ)(λ·ω⁻) = 0`, so
`cof(λ) = κ·[(λ·ω⁻)ω⁺ − (λ·ω⁺)ω⁻]` with `κ` independent of `λ` (two
proportional linear maps). Then
`Q(cof λ) = −2κ²(λ·ω⁺)(λ·ω⁻)B(ω⁺,ω⁻)`. Expanding `λ·cof(λ) = 0` at
`λ = σs + τq + (⟨m,n⟩-part)` gives `s·ω⁺ = q·ω⁻ = 0` and `s·ω⁻ = −q·ω⁺`, and
evaluating at `λ = s` (where `cof(s) = ω⁺`) pins `κ² = 1/(q·ω⁺)²`. ∎
(The driver verifies the identity with the scalar **exactly 1**, i.e. with the
`pitch.cross4` normalization of `cof` there is no residual constant. The
symbolic check below pins the *sign* as well: `κ = −1/(q·ω⁺)`.)

*Exact, per frame:* `--witt` computes `Φ_loc`'s `4×4` matrix from the linear map
`λ ↦ cof(λ)` and the banded Gram, and asserts `rank = 2`, `Φ_loc ≠ 0`,
`ω± ∈ S ∩ α/β` and that they *are* line extensors, and **(Λ1) with the scalar
exactly 1** (i.e. `(q·ω⁺)²·PhiM = −B(ω⁺,ω⁻)(ω⁺ω⁻ᵀ + ω⁻ω⁺ᵀ)`, all 16 entries)
— 23 frames: 5 hub-pattern strata × 3 local frames, plus 2 seeds at each of
four habitats.

**Symbolic, over the function field — (Λ1) is an IDENTITY, not 23 samples**
(2026-08-05, `M2 --script notes/scripts/m2/lambda1.m2`, the harness's first
Macaulay2 driver). Treating the frame's coordinates as indeterminates upgrades
(Λ1) from per-frame evidence to a statement about *every* frame at once. What
the driver establishes, in four blocks:

- **(M1) the universal cofactor identity**, with `m, n, q, s, λ` **free**
  covectors in `K⁴` (20 indeterminates, no geometry, no gauge):
  `(q·ω⁺)·cof(λ) = (λ·ω⁺)·ω⁻ − (λ·ω⁻)·ω⁺`. This is the *Proof* above's
  `cof(λ) = κ[(λ·ω⁻)ω⁺ − (λ·ω⁺)ω⁻]` together with its normalization, and it
  holds with no hypotheses whatsoever.
- **(M2) the universal quadratic expansion**, same 20 indeterminates plus a
  **free symmetric Gram** (30 in all): squaring (M1) gives
  `(q·ω⁺)²Φ_loc(λ) = (λ·ω⁺)²Q(ω⁻) − 2(λ·ω⁺)(λ·ω⁻)B(ω⁺,ω⁻) + (λ·ω⁻)²Q(ω⁺)`.
  So `Q(ω⁺) = Q(ω⁻) = 0` is the **only** geometric input (Λ1) has.
- **(M3) the α/β isotropy lemma**, gauge-free (four free points): each of
  `⟨C_ab, C_ac, C_aw⟩` and `⟨C_ab, C_ac, C_bc⟩` is totally isotropic and
  3-dimensional over the function field, hence maximal isotropic, hence
  self-`B`-perp — so anything `B`-orthogonal to one of them lies *inside* it.
  That is exactly `Q(ω⁺) = Q(ω⁻) = 0`, since `m·ω = n·ω = s·ω = 0` (resp.
  `q·ω = 0`) *is* `B`-orthogonality to those three lines. **(M1)+(M2)+(M3) is a
  gauge-free proof of (Λ1)** — the Step-1 Witt argument reappears here as the
  self-perpendicularity of a maximal isotropic, computed rather than quoted.
- **(M4) (Λ1) end-to-end**, both in its 16-entry matrix form and in the scalar
  form above, on the gauge slice `b, x₁, x₂, x₃ = e₀, e₁, e₂, e₃` with `a`, `c`,
  `w` and the far covector `λ` free. Both sides are bracket polynomials, hence
  GL(4) relative invariants of the same weight 13, and `g = [b|x₁|x₂|x₃]⁻¹` is
  the *unique* element of GL(4) carrying an independent quadruple to the
  standard basis — so the slice meets every orbit exactly once and vanishing on
  it is vanishing identically. The same run re-derives generically, rather than
  per frame, the structural zeros `m₁ = n₄ = q₁ = q₄ = 0`, the banded Gram,
  `ω±` nonzero line extensors with `ω⁺` through `pt(a)` and `ω⁻` inside
  `plane(a,b,c)`, `q·ω⁺ ≠ 0`, `B(ω⁺,ω⁻) ≠ 0`, the scalar exactly 1, and
  `rank Φ_loc = 2`.

**Two things this adds beyond confirming the 23 frames.**

1. **(Λ1) needs none of (Λ0), and none of the panel data.** In (M4) the points
   `a, c, w` and the covector `λ` are free — in particular `pt(a)` is *not*
   constrained to the meet line `M`, and no panel non-incidence is assumed. The
   identity is unconditional; (Λ0a–f) is what makes its ingredients **nonzero**
   (`ω± ≠ 0`, `q·ω⁺ ≠ 0`, `B(ω⁺,ω⁻) ≠ 0`, `rank[m;n] = 2`), and the driver shows
   each of those is nonzero *as a polynomial*, i.e. off a proper closed subset.
   So "(Λ1) under (Λ0)" is really "(Λ1) always, with (Λ0) securing the
   normalization" — a cleaner statement than the one the per-frame battery
   could support.
2. **`rank Φ_loc = 2` is now generic, not observed.** Previously 23 frames;
   now it follows from the identity plus `B(ω⁺,ω⁻) ≠ 0` and
   `rank[ω⁺; ω⁻] = 2`, both verified as polynomial non-vanishing.

*Feasibility, measured — the boundary a successor should budget for.* The
**ungauged** end-to-end expansion (all 28 point coordinates indeterminate) has
degree 52 and does **not** finish: killed at 600 s inside `cross4` on the
ungauged bracket rows. The local frame is symbolically viable; a whole-graph
placement is not (`notes/Pencil-strategy.md` §5.3). That probe is recorded as
*measured, script not retained* — it is (M4) with the gauge removed, a one-line
edit of the committed driver (`notes/scripts/m2/README.md`).

*Standing of this output.* Evidence for this workbook, at the same standing as
the exact-ℚ numerics — **never** a substitute for Lean. "Verified in Macaulay2"
is not a proof the project may cite in place of a formalization
(`DESIGN.md` *Formalize everything the argument uses*; `notes/scripts/m2/README.md`
convention 1). `lambda.py --witt` is **not** superseded: its 23 frames and its
recorded figures stand unchanged, and the two are cited together.

**This kills the flagged risk.** "`Φ_loc` the zero form" cannot happen under
(Λ0), and neither can `Φ_loc` be irreducible: the quadric is always a pair of
rational hyperplanes. Any attack aimed at "uniform non-degeneracy of `Φ_loc`"
is attacking something already free.

### Step 3 — the `a`-line spans: two hyperplanes shrink to two points

`V_bc`, `S` and `q` are **`a`-free** ((T4)'s observation: `a ∉ H`). Slide
`pt(a) = p₀ + t·d` along `M`. Then `m(t)`, `n(t)`, `s(t)` are linear in `t`, so
`ω⁺(t) = cof_t(s(t))` has degree `≤ 3` and `ω⁻(t) = cof_t(q)` degree `≤ 2`
(`q` constant). Geometrically:

- every `ω⁺(t)` is a line through the point `pt(a(t)) ∈ M`, hence **meets `M`**,
  hence `ω⁺(t) ∈ C(M)^{⊥B}`;
- every `ω⁻(t)` is a line in a plane containing `line(bc)`, hence **meets
  `line(bc)`**, hence `ω⁻(t) ∈ C(bc)^{⊥B}`.

Since `p⁺` and `q` are the coordinate forms of `B(·, C(M))` and `B(·, C(bc))`
on `S`, both containers are the 3-dimensional `S ∩ C(M)^{⊥B}` and
`S ∩ C(bc)^{⊥B}` (3-dimensional because `p⁺ ≠ 0 ≠ q`, i.e. some companion line
misses `M` resp. `line(bc)`). And the curves **fill their containers**:

> **(Λ0f), certified generic** — `span_t ω⁺(t) = S ∩ C(M)^{⊥B}` with
> annihilator `⟨p⁺⟩`, and `span_t ω⁻(t) = S ∩ C(bc)^{⊥B}` with annihilator
> `⟨q⟩`; both 3-dimensional, and `p⁺ ∦ q`. Equivalently, in brackets:
> `span_t ω⁺(t) = 3 ⟺ p⁺₂ ≠ 0 ≠ p⁺₃`, and `span_t ω⁻(t) = 3 ⟺ q₂ ≠ 0 ≠ q₃`.
> *Exact:* `--span`, **164 frames** — all 38 local-chart strata × 4 frames
> each, plus 3 seeds at each of the four habitats — every one with
> `(span ω⁺, span ω⁻, deg ω⁺, deg ω⁻) = (3, 3, 3, 2)`, both annihilators
> identified, and the bracket equivalence asserted in both directions.
> (The naive expectation `span ω⁺ = 4 = dim S`, which the degree count alone
> suggests and which would have closed (K-Λ) outright with no far-side
> condition at all, is **false** — this is the pass's decisive negative
> measurement, and the reason the verdict below is a refutation rather than a
> closure.)

**(Λ0f) PROVEN, and WIDER than stated** (2026-08-05, `m2/lambda0.m2`). The
containments and the degrees are now **identities** on the local frame's
generic point: `p⁺·ω⁺(t) ≡ 0` and `q·ω⁻(t) ≡ 0` in `t` *and* in the frame
coordinates, with `deg_t ω⁺ = 3` and `deg_t ω⁻ = 2` exactly. The *equality*
half — the curves filling their containers — comes out as a closed form.
Writing `g₁₃ = B(C₁,C₃)`, `g₁₄ = B(C₁,C₄)`, `g₂₄ = B(C₂,C₄)` for the three
surviving entries of the banded Gram of `S`, and taking the `cross4` of the
`t`-coefficient triples of each curve:

> **(Λ0f′) the exact span criterion.** For every coefficient triple `j`,
> `cross4(A_{j₀}, A_{j₁}, A_{j₂}) = (−1)^j w₃^{3−j} w₂^{j} · Π⁺ · p⁺` with
> `Π⁺ := p⁺₂ p⁺₃ g₁₃ g₁₄ g₂₄`, and `cross4(B₀,B₁,B₂) = Π⁻ · q` with
> `Π⁻ := q₂ q₃ g₁₃ g₁₄ g₂₄`. Hence, with `w` off `line(bc)` (which is implied
> by the standing `w ∉ π_a`, and is exactly what the four `w`-monomials
> `w₃³, w₃²w₂, w₃w₂², w₂³` express):
>
> `span_t ω⁺(t) = 3 ⟺ Π⁺ ≠ 0` and `span_t ω⁻(t) = 3 ⟺ Π⁻ ≠ 0`.

So the recorded bracket equivalence is **incomplete**: it carries `p⁺₂p⁺₃`
(resp. `q₂q₃`) but not the three Gram factors. Two of them are old news in
new clothing — `g₁₃g₂₄ ≠ 0` is exactly `rank Q|_S = 4` (the driver checks
`det Gram = (g₁₃g₂₄)²`), which `--witt` already asserts, though nothing linked
it to the span. **`g₁₄ = B(C₁,C₄) ≠ 0` is asserted nowhere in the harness**,
and it is a genuine clause, not a consequence: degenerating `C₄`'s direction
onto `C₁`'s (`v₂ = λu₂, v₃ = λu₃`) kills `g₁₄` while (Λ0a), (Λ0b), (Λ0c),
(Λ0e) and all four `p⁺`/`q` middle brackets **survive** — and both spans drop
(driver block (P5)). Geometrically `g₁₄ = [b, x₁, x₃, c]`, so the missing
clause reads: **the two outer companion lines `C₁ = C(bx₁)` and `C₄ = C(x₃c)`
must not meet.**

*No recorded figure moves.* All 164 sampled frames have `g₁₃g₁₄g₂₄ ≠ 0` — it
is generic — so the asserted equivalence never fired there and `--span`
reproduces unchanged. What was wrong was the *general statement*, which is
precisely the failure mode sampling cannot detect: a missing hypothesis that is
generically satisfied. `lambda.py` is left untouched (`notes/scripts/README.md`
§4 convention 5).

Combining with (Λ1) evaluated at each `t`: `Q(z(t)) = 0` ⟺
`λ·ω⁺(t) = 0` or `λ·ω⁻(t) = 0`. Both are polynomials in `t`
(degrees `≤ 3` and `≤ 2`) and `λ` is constant, so

> **(Λ2)** `Q(z(t)) ≡ 0` along the whole `a`-line ⟺ `λ ⊥ span_t ω⁺(t)` or
> `λ ⊥ span_t ω⁻(t)` ⟺ **`λ ∝ p⁺` or `λ ∝ q`** ⟺
> **`V_bc ⊆ C(M)^{⊥B}` or `V_bc ⊆ C(bc)^{⊥B}`**.

(Both equivalences are two lines of linear algebra: `V_bc = ker λ ∩ S` is a
hyperplane of `S`, so `V_bc ⊆ C(L)^{⊥B}` ⟺ the coordinate form of
`B(·, C(L))` annihilates `V_bc` ⟺ it is proportional to `λ`.)

So the bad far covectors are **two points of `P³`**, not a quadric's worth —
and each is structurally meaningful. (This rests on (Λ0f′) in full, whose one
previously-unasserted factor `g₁₄` is the subject of *Step 3a*: where `g₁₄`
vanishes, `span_t ω± = 2` and (Λ2) acquires a **third** branch — a whole
hyperplane of bad `λ` on each side, not a point. *Step 3a* settles that no
class habitat in the searched scope is confined to that locus.)

### Step 3a — the `g₁₄` clause, located (2026-08-05, `outer.py`)

*What would change this* item (vi) asked whether a **class habitat can force
`g₁₄ = 0` on its whole pencil chart**, which would put a third branch into
(Λ2) and force the completeness theorem to be restated. It cannot, in the
scope searched — and the reason is two elementary facts the arc had not
written down. Both are asserted per frame by `notes/scripts/w4/outer.py`.

> **(Λ0g) the geometric form.** `x₁ ∈ N_{G′}(b)` and `x₃ ∈ N_{G′}(c)`, so
> `C₁ = C(bx₁) ⊆ Π(b)` and `C₄ = C(x₃c) ⊆ Π(c)`. Both panels contain `M`,
> and two lines of a projective plane always meet, so **each outer companion
> line always meets `M`** — which is the structural vanishing
> `p⁺₁ = p⁺₄ = 0` read backwards. Two lines of `P³` meet iff they are
> coplanar, and a meet of `C₁ ⊆ Π(b)` with `C₄ ⊆ Π(c)` lies in
> `Π(b) ∩ Π(c) = M`. Hence, whenever `Π(b) ≠ Π(c)`,
>
> `g₁₄ = 0 ⟺ C₁ ∩ M = C₄ ∩ M` **as points of `M`**.

So the clause is not "two lines of space happen to meet" but "**two marked
points of the line `M` coincide**" — one equation, on the very line along
which `pt(a)` slides. (Asserted in both directions at every frame of `--geom`,
`--habitat` and `--sweep`; the meet is projective, so a line affinely parallel
to `M` meets it at `M`'s point at infinity, and two such lines coincide there.)

> **(Λ0i) the mobility criterion.** If `x₁` has degree 2 and its other
> neighbour `x₂` is not a hub, then `b` is `x₁`'s only hub neighbour and `x₁`
> carries no panel of its own, so `pt(x₁)`'s **only** chart constraint is
> `pt(x₁) ∈ Π(b)`: it sweeps a dense subset of that plane with the entire
> rest of the placement held fixed. `g₁₄` is affine in `pt(x₁)` with zero
> locus the plane `plane(b, x₃, c)`, so `g₁₄ ≡ 0` on the chart would force
> `Π(b) = plane(b, x₃, c)`, hence `pt(c) ∈ Π(b)` — a failure of **(Λ0d)**.
> Symmetrically with `x₃` free in `Π(c)` and the other half of (Λ0d).

**Consequence: wherever either companion end is free, the `g₁₄` clause is
*implied by* (Λ0d) and is not an independent hypothesis at all.** Measured
over the systematic sweep: **3628 of 4280** (split, companion) pairs are
covered by this criterion alone. The 652 that are not are all the single hub
pattern **`x₂` a hub** — the `2 + 2` via-hub companion `b–x₁–u–x₃–c`, where
`pt(x₁) ∈ Π(b) ∩ Π(u)` and `pt(x₃) ∈ Π(u) ∩ Π(c)` are each pinned to a *line*
rather than sweeping a plane. Those are discharged one level up, at the
chart's tangent space (`dominance.build_chart`, scoping FIXED, so `pt(a)`,
`pt(b)`, `pt(c)` and both panels stand still): `d g₁₄ ≠ 0` at **684/684**
probed chart points, **all 652** uncovered companions among them. A nonzero
differential makes `{g₁₄ = 0}` a proper hypersurface of the chart, which is
strictly more than "not identically zero".

**The degeneration is nevertheless REACHABLE — at a good seed.** `--geom`
constructs it: slide `pt(x₁)` inside `Π(b)` onto the line joining `pt(b)` to
`D := C₄ ∩ M` (legal, because both points lie in `Π(b)`, and in the free
pattern that is `x₁`'s only constraint). Then `C₁ ∩ M = D = C₄ ∩ M`, so
`g₁₄ = 0` exactly. At all four habitats — θ(3,4,5), NT21, NT24, NT30 — the
result is an exact pencil realization with

- `g₁₄ = 0` while `g₁₃, g₂₄ ≠ 0` and **all four middle brackets survive**, so
  (Λ0a), (Λ0b), (Λ0c), (Λ0d), (Λ0e) and the recorded (Λ0f) all hold;
- **both spans drop, `3 → 2`** — (Λ0f′) predicts exactly this, and the
  recorded (Λ0f) predicts the opposite: `lambda.omega_curves`' own coded
  equivalence **fires as an `AssertionError`** at these points (caught and
  reported by `outer.py`, never repaired — §4 convention 5);
- the placement is still **target-rank with `dim R_a = 1`**, i.e. a *good
  seed* on the hard stratum, with `dim V_bc = 3`.

So this is `m2/lambda0.m2` block (P5) reproduced on **real class habitats**
rather than on the abstract slice: the third (Λ2) branch is **not vacuous**
anywhere in the class — it is a genuine, reachable stratum of every probed
habitat's chart. What it is not is *forced*: it is a hypersurface, and at each
constructed point the habitat's **own** far covector `λ` annihilates neither
collapsed span, so `Q(z(t)) ≢ 0` (degree 4) and the pitch certificate still
fires — 0 of 4 constructed points is actually blind.

### Step 4 — branch 1: `λ ∝ p⁺` is the genuine escape failure

`λ ∝ p⁺` ⟺ `V_bc ⊆ C(M)^{⊥B}` ⟺ `V_bc ⊥_B C(M)`, which is **verbatim (T3)'s
uniform-failure criterion**: no motion of `H` pairs non-trivially with the meet
line, so both routes fail and the escape genuinely does not hold at any seed of
that far configuration. The pitch certificate is not *blind* here — it is
correctly reporting a failure. (`--habitat` asserts the equivalence
`escape(T3) ⟺ ¬(λ ∝ p⁺)` at every probed seed; `--adv` hunts for `λ ∝ p⁺` and
finds none, which is the expected outcome — a hit would be a **counterexample
to the pencil conjecture** at that habitat.)

### Step 5 — branch 2: `λ ∝ q` forces `★r ∝ C(bc)`, and route A escapes

Suppose `V_bc ⊆ C(bc)^{⊥B}`, i.e. `⟨x, ★C(bc)⟩ = 0` for all `x ∈ V_bc`. Also
`B(C(bc), C_ab) = [b,c,a,b] = 0` and `B(C(bc), C_ac) = [b,c,a,c] = 0`, so
`★C(bc)` is Euclid-orthogonal to `T` as well, hence to all of
`W := V_bc ⊕ T` (5-dimensional at a target-rank seed, (T1)). Since (T1) says
`⟨r⟩ = W^⊥`:

> **(Λ3)** `V_bc ⊆ C(bc)^{⊥B}` ⟹ `★r ∝ C(bc)`: the transmitted wrench is the
> **pure force along the line joining the two hub points**.

Route A fails only if `★r ∈ Λ²Π̂(b)`, i.e. only if `line(bc) ⊆ Π(b)`, i.e. only
if `pt(c) ∈ Π(b)` — excluded by (Λ0d). So in this branch **the split escapes at
every target-rank seed**, by route A rather than by the pitch certificate.
(`--dichot` asserts each step: `★C(bc) ⊥ W`, `W^⊥ = ⟨★C(bc)⟩` with
`dim W = 5`, and `C(bc) ∉ Λ²Π̂(b)`; 18 frames across 9 strata.)

The two branches are disjoint (`p⁺ ∦ q`, asserted per frame). Reading Steps 3–5
together:

> **Theorem (Λ-completeness at length-4 companions).** At a hard-stratum split
> with a length-4 companion, under (Λ0) and the standing (T1)/(T5) hypotheses:
> **the escape holds at some target-rank seed iff the pitch certificate `Q(z)`
> is nonzero at some target-rank seed.** Concretely, for each far
> configuration exactly one of: `Q(z) ≠ 0` somewhere on the `a`-line (escape,
> by pitch); `V_bc ⊆ C(bc)^{⊥B}` (escape, by route A, with `★r ∝ C(bc)`);
> `V_bc ⊆ C(M)^{⊥B}` (the escape genuinely fails there, (T3)).

### Step 5a — (OUT): the outer-line criterion, a far-side sufficient condition (2026-08-05, no driver)

Migrated here from `notes/Pencil-strategy.md` §4.6-U1, which derived it and
flagged it as having no workbook home; that file now carries only a pointer and
the strategic readings. **It is a corollary of Steps 3–5 and nothing else** —
no new geometry — but it is the one *positive* the broad class-uniformity recon
produced, and the arc under-produces those.

**The observation.** `p⁺` and `q` have their **outer** entries vanishing
*structurally*, not generically — `p⁺ = (0, p⁺₂, p⁺₃, 0)` and
`q = (0, q₂, q₃, 0)` always ((Λ0f)'s parenthetical; (Λ0g) restates the `p⁺`
half geometrically). So the *whole* (Λ2) bad set lies on **one projective line**
of `P(S*)`, namely `{λ₁ = λ₄ = 0}`. And by *Standing notation* `λ` is the
annihilator of `V_bc` in the `C`-basis, so `λ_i = λ(C_i)` and, since
`V_bc = ker λ ∩ S` is a hyperplane of `S` with `C_i ∈ S`,

>  `λ₁ = 0 ⟺ C₁ ∈ V_bc`   and   `λ₄ = 0 ⟺ C₄ ∈ V_bc`.

Hence:

> **(OUT) the outer-line criterion** *(proven-informally, **conditional** — see
> the hypothesis line below)*. At a hard-stratum, target-rank, length-4-companion
> split, if **either outer companion line fails to be a relative twist** —
> `C₁ = C(b x₁) ∉ V_bc` **or** `C₄ = C(x₃ c) ∉ V_bc` — then `λ` is proportional
> to neither `p⁺` nor `q`, so by (Λ2) `Q(z(t)) ≢ 0` along the `a`-line and the
> split **escapes by the pitch certificate** at some placement of `pt(a)` on `M`.

**Hypotheses, spelled out because a one-line quotation of (OUT) will drop them.**
(OUT) is *exactly as conditional as (Λ2)*: it needs the standing (T1)/(T5)
hypotheses, the hard-stratum target-rank seed with `dim V_bc = 3`, and **(Λ0) in
full** — in particular **(Λ0d)** (two-sided panel non-incidence) and the
**widened (Λ0f′)** including the `g₁₄` clause. Both are load-bearing here and not
decoratively so: if (Λ0d) fails, *Step 6* shows `span_t ω⁻` collapses `3 → 1` and
(Λ2)'s second branch becomes a whole **hyperplane** of bad `λ`; if the `g₁₄`
factor of (Λ0f′) vanishes, *Step 3*'s closing parenthetical gives (Λ2) a third
branch, again a hyperplane per side. A hyperplane is **not** contained in the
line `{λ₁ = λ₄ = 0}`, so the containment (OUT) rests on fails outright in either
degeneration. (OUT) inherits *Step 3a*'s scope for `g₁₄` verbatim, including the
open two-hub-interior residual, item (vii).

**What it costs.** (OUT) is **sufficient, never necessary**: it discards a
codimension-3 avoidance (`λ ∦ p⁺`, a point of `P³`) in exchange for a
codimension-2 one (`λ` off a line of `P³`), and it is silent on the whole line —
of whose points exactly one (`p⁺`) is a genuine (T3) failure and one (`q`) is a
route-A escape. It is not a strengthening of Λ-completeness; it is a *cheaper
test* that is decided by far-side data alone.

**Why the cheapness is the point.** (OUT)'s hypothesis mentions **no quadric, no
meet line `M`, no `pt(a)`, no panel and no ratio** — the two conditions
`C₁, C₄ ∈ V_bc` are statements about `H` alone. In hinge-rate coordinates
(`m(u) − m(w) = ω_e C_e` per hinge, as in §(K-ind) *Step I3*'s proof) the
companion lines are independent by (Λ0a), so a relative twist has *unique*
companion coordinates and

> `C₁ ∈ V_bc` ⟺ some motion of `H` has companion hinge-rates `(1,0,0,0)` —
> it **freezes the companion's last three hinges and bends the first** —
> ⟺ in `H/{e₂,e₃,e₄}` (weld `x₁,x₂,x₃,c` into one body `X`; any chord among
> them becomes a loop and drops out) the body `b` is **not rigidly attached to
> `X`**.

(The second equivalence in one line: `e₁` joins `b` to `X`, so any relative
motion of `b` and `X` lies in `⟨C₁⟩` and is `ω_{e₁}C₁`; it is nonzero iff
`ω_{e₁} ≠ 0`. Further `b`–`X` edges only make `b` more attached, and the
equivalence survives them.)

**Two consequences recorded, neither proven here.** *(1)* `C₁ ∉ V_bc` is a rank
**lower** bound (a rigidity statement), so `notes/Pencil-strategy.md` §2.3's
asymmetry is **relocated onto a smaller contracted graph, not evaded** — and
that is the honest reason (OUT) is a reformulation rather than a closure.
*(2)* The welded body `X` carries the hinges formerly at `x₁, x₂, x₃, c`, which
are not concurrent, so `X` is **not a pencil body**: the fact (OUT) reduces to
lives on the **mixed stratum** (§(K-ind) *Step I6* is why no transport repairs
this). That gives `Pencil-strategy.md` §4-C3 a consumer it did not have.

**Unmeasured, and this is the cheap probe.** `--adv` reports `λ ∝ p⁺` and
`λ ∝ q` at **0 of 1497** frames, but it reports **nothing about `λ₁` and `λ₄`
separately**, so (OUT)'s hypothesis has never been evaluated anywhere in the
arc. Recording `λ₁, λ₄ ≠ 0` (equivalently `C₁, C₄ ∉ V_bc`) at the recorded
length-4-companion frames would discharge the escape there by a far-side,
panel-free route; a frame with `λ₁ = λ₄ = 0` would put a habitat on the bad line
and is the sharpest single datum available at `k = 4`. That is a **new driver
mode**, not run by this pass.

### Step 6 — two side conditions that are load-bearing, with witnesses

(Λ0) is not decorative. Two of its clauses have exhibited witnesses:

- **(Λ0d), panel non-incidence, is needed in *both* directions.** At
  θ(3,4,5) **seed 345** the sampler happens to place `pt(b) ∈ Π(c)`; then
  `pt(b)` lies *on* `M`, `plane(a(t),b,c)` is **constant** along the `a`-line,
  and `span_t ω⁻(t)` collapses `3 → 1`, so (Λ2)'s second branch becomes a whole
  hyperplane of bad `λ`. (Route A still escapes there, since `pt(c) ∉ Π(b)`.)
  Reproduced and asserted by `--adv`. The earlier arc only ever used the
  one-sided form of this condition; the two-sided form is what (Λ2) needs.
  **Two additions, 2026-08-05 (§(K-σ) *Step σ3*/*Step σ4b*, `sigma.py
  --hunt`).** (1) The one-sided failure is not peculiar to θ(3,4,5)'s sampler:
  it is reachable by construction on the **tight control's** hard stratum, at
  35/35 primally-nondegenerate configurations. (2) The **two-sided** failure is
  *impossible* at a primally nondegenerate seed whose split middle body `a` is
  a degree-2 non-hub adjacent to both hubs — **(σ7)** — so (Λ0d) can fail in at
  most one direction. That does **not** relieve (Λ2), which needs both halves;
  it only bounds how badly (Λ0d) can fail.
- **(Λ0f) is a genuine hypothesis**, not a consequence of (Λ0a–e), and its
  failure is exactly one bracket. Forcing the single non-structural bracket
  `p⁺₃ = [x₂, x₃, M₀, M₁] = 0` — i.e. moving `pt(x₃)` inside `Π(c)` so that
  `C₃` meets `M`, an affine-linear solve — collapses `span_t ω⁺(t)` from 3 to
  2, deterministically (4/4 **constructed** frames, `--adv`
  `degeneracy_witnesses`); forcing `q₃ = [x₂, x₃, b, c] = 0` collapses
  `span_t ω⁻(t)` the same way. Discovered, not postulated: θ(3,4,5) **seed 695**
  has `p⁺ = (0, ∗, 0, 0)` and `span ω⁺ = 2`. In that situation
  `λ ⊥ span_t ω⁺(t)` no longer implies `V_bc ⊥_B C(M)`, so the Step-4
  identification breaks and the pitch route *could* be blind while the escape
  holds. It is a proper closed condition (0 hits in the 164 (Λ0a–e)-generic
  frames), so a good seed always exists — but it must be **named**, which the
  prior formulation did not do.

### Step 7 — `ℓ ∈ {5, 6}`: the frame does **not** reach them, and exactly why

The gap map listed the (T5) frame as the route for the `bc`-parallel
`ℓ ∈ {5,6}` shapes. It is not, and the obstruction is sharp.

By Step 1(ii), `dim(S ∩ α_a) = k − 3`, so at `k ≥ 5` "`V_bc` meets it" is
**strictly weaker** than "`V_bc` contains it", and the Step-3 span argument —
which works precisely because at `k = 4` the intersection is a *point* of
`P(S)` — has no analogue. Concretely at `k = 5` (`dim S = 5`,
`Y := S ∩ C(M)^{⊥B}` 4-dimensional, `P_α(t) := S ∩ α_{a(t)}` 2-dimensional and
`⊆ Y`): a bad `V_bc` with `V_bc ⊄ Y` meets every `P_α(t)` inside the 2-plane
`U := V_bc ∩ Y`. Two 2-planes of the 4-dimensional `Y` meet iff their Plücker
points pair to zero under `Λ⁴Y` (the Klein form again), so such `U` exist iff
`W^⊥` contains a nonzero **decomposable** point, where
`W := span_t Plücker(P_α(t)) ⊆ Λ²Y ≅ K⁶`. Measured exactly (`--l56`, 3 frames,
both the `α/C(M)` and the `β/C(bc)` side): `dim W = 3`, `dim W^⊥ = 3`, and
`Q|_{W^⊥}` is **nondegenerate of rank 3** — a *smooth conic*. So over `K̄` the
extra component is nonempty and 1-dimensional, giving a `1 + 2 = 3`-dimensional
family of bad `V_bc`, **the same dimension as the containment component**, and
it is neither the (T3) failure nor the route-A branch. At `k = 6`, `S = Λ²K⁴`
so `C(M) ∈ S` always (asserted), removing even the (Λ0e) guard.

> **`ℓ = 5, 6` verdict: REFUTED through this frame.** The `(F-B)`/route-A half
> (Step 5) is length-free and survives verbatim; the `(F-A)` half acquires a
> second bad component at every `k ≥ 5`, so no local argument of this shape
> settles `ℓ ∈ {5,6}`. What would be needed is a reason the *realized* `V_bc`
> of a class habitat misses that conic component — a far-side statement, and a
> harder one than at `k = 4` (where the analogous far-side statement turned out
> to be (T3) itself).

**Scope, stated because it is easy to overstate.** This refutes **the (T5)
frame / an argument of this shape** at `ℓ ∈ {5,6}`. It does **not** refute the
pencil conjecture there, and it does **not** show those shapes are unclosable:
the extra `k = 5` component is a smooth conic, so it is nonempty **over `K̄`**,
and whether a *rational* point of it is realized by a real habitat's `V_bc` is
**open** — item (iv) of *What would change this*.

### Step 8 — a length-free remark, flagged as *not* fully driver-tested

Steps 3–5 used the companion only through Step 1(ii)'s dimension count. The
`(F-B)` half is **length-free**: at *any* hard-stratum split with `b, c` hubs,
if the isotropic conic `𝒞 := P(V_bc) ∩ {Q = 0}` spans `P(V_bc)` (⟸
`rank Q|_{V_bc} = 3`, observed at **357/357** real habitat seeds) and every line
of `𝒞` meets `line(bc)` — which is what `(F-B)` at every `t` forces, because the
planes `plane(a(t),b,c)` sweep the pencil through `line(bc)` — then
`V_bc ⊆ C(bc)^{⊥B}`, and (Λ3) + route A escape. The `(F-A)` half is length-free
too, but its conclusion is weaker: `M` must lie on the ruled surface of `𝒞`,
which gives `C(M) ∈ V_bc` **or** `V_bc ⊆ C(M)^{⊥B}`. So in general the pitch
route's only blind spot beyond the genuine (T3) failure is `C(M) ∈ V_bc` —
excluded at `k ≤ 5` by `C(M) ∉ S`, unavailable at `k = 6`. This remark is
**geometric, over `K̄`, and only partially driver-tested** (the ingredients
`rank Q|_{V_bc} = 3` and `C(M) ∈ S ⟺ k = 6` are; the ruled-surface case
analysis is not). **It is recorded as a lead, not as a proven step.**

### Verification

`notes/scripts/w4/lambda.py` (tracked, new this pass; exact-ℚ, on top of
`pitch.py`; every sampled object rank/dimension asserted; all rng seeded,
`PYTHONHASHSEED=0` pinned). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --witt      # (Λ0′), (Λ1)
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --span      # (Λ0f), the spans
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --dichot    # (Λ2), (Λ3)
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --habitat   # end-to-end + ℓ=3
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --l56       # ℓ = 5, 6
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --adv       # the hunt
M2 --script notes/scripts/m2/lambda1.m2                         # (Λ1) symbolically
M2 --script notes/scripts/m2/lambda0.m2                         # (Λ0) + the spans
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --geom       # (Λ0g) + the construction
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --habitat    # named inventory
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --sweep      # the systematic sweep
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --tangent    # d g₁₄ ≠ 0 on the chart
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --patterns   # the coverage boundary
```

**(OUT) (*Step 5a*) carries no driver and adds no command line**: it is a
corollary of Steps 3–5, and the quantities its hypothesis names (`λ₁`, `λ₄`) are
computed but not reported by `--adv`. Do not read any figure below as evidence
for or against it.

The last five lines are `notes/scripts/w4/outer.py` (tracked, new 2026-08-05;
exact ℚ, a `w4/` leaf beside `flanks`/`pure`/`lambda`/`dominance`), the
*Step 3a* driver. It **reads** `lambda.py` through `importlib` for the four
certified habitats and the `ω±` curve machinery and never modifies it.

The last line is the harness's **Macaulay2 layer** (`notes/scripts/m2/`, opened
2026-08-05 with this driver; conventions in `notes/scripts/m2/README.md`, M2
version **1.26.06** pinned and printed, no randomness). It is *additive*: it
does not reimplement or replace `lambda.py --witt`, whose figures below stand
unchanged.

Habitats: θ(3,4,5) and NT21 (the two `pitch --companion4` shapes) plus **two
new length-4-companion shapes** — `NT24` (hubs `b,c,u,w`; `b`–`c` paths 3, 4
plus `b–u:3, u–c:4, b–w:4, w–c:3, u–w:3`; `|V| = 21`, `|E| = 24`) and `NT30`
(5 hubs; `b`–`c` paths 3, 4 plus `b–u:4, u–c:3, b–w:3, w–c:3, u–y:4, y–c:3,
w–y:3`; `|V| = 26`, `|E| = 30`) — and θ(3,3,6) for the `ℓ = 3` corollary. All
four length-4 shapes carry the class predicate at load time: `def = 0`
(`nogood_subdiv.deficiency`), `hnoRigid` at branch granularity
(`kslide.no_rigid_branch_union`), `hcard_ok`, triangle-free.

Per mode, what is asserted:

- `--witt`: `T` totally isotropic; `dim T^{⊥B} = 4`, `rank Q|_{T^{⊥B}} = 2` with
  radical exactly `T`; `α_a`, `β_{π_a}` totally isotropic, inside `T^{⊥B}`, and
  meeting in `T`; `dim N = 2`, `S ∩ T = 0`, `rank Q|_N = 2`, `B(ω⁺,ω⁻) ≠ 0`;
  `ω±` are line extensors and span `S ∩ α_a` / `S ∩ β_{π_a}`; `rank Q|_S = 4`;
  `Φ_loc ≠ 0`, `rank Φ_loc = 2`, and **(Λ1) with scalar exactly 1**.
- `--span`: per frame the degrees (`≤ 3`, `≤ 2`), the structural zeros
  `q₁ = q₄ = p⁺₁ = p⁺₄ = 0`, `p⁺ ≠ 0 ≠ q`, `p⁺ ∦ q`, `C(M) ∉ S`, both spans
  `= 3` **and the bracket equivalence (Λ0f) in both directions**, both spans
  identified as `S ∩ C(M)^{⊥B}` / `S ∩ C(bc)^{⊥B}`, both annihilators
  `⟨p⁺⟩` / `⟨q⟩`, `q·ω⁺(t) ≢ 0`. **164 frames** over **38 strata** + 4
  habitats, `(3,3,3,2)` uniformly.
- `--dichot`: for `λ = p⁺` and `λ = q`, `Q(z(t)) ≡ 0` (exact interpolation) and
  `ker λ ∩ S` = the corresponding `S ∩ C(L)^{⊥B}`; for a sampled generic `λ`,
  `Q(z(t)) ≢ 0`; the per-`t` factorization
  `Q(z) = 0 ⟺ λ·ω⁺ = 0 ∨ λ·ω⁻ = 0`; and (Λ3): `dim W = 5`, `★C(bc) ⊥ W`,
  `W^⊥ = ⟨★C(bc)⟩`, `C(bc) ∉ Λ²Π̂(b)`. **18 frames**, 9 strata.
- `--habitat`: the Λ-compressed `z` equals `pitch.z_from`'s `z`; the (T2) sign
  law `Q(r)·Q(z) < 0` against the **independently computed stress**; (T3)
  agreement `escape ⟺ ¬(λ ∝ p⁺)`; `Q(z) ≠ 0` at every seed; plus the `ℓ = 3`
  corollary at θ(3,3,6).
- `--l56`: `dim(S ∩ α_a) = dim(S ∩ β) = k − 3` and `rank Q|_N = 2` with radical
  `S ∩ T` for `k = 3,4,5,6`; `C(M) ∈ S ⟺ k = 6`; at `k = 5` the Plücker
  reduction `(dim W, dim W^⊥, rank Q|_{W^⊥}) = (3,3,3)` on both sides, and that
  every 3-space inside `Y` is bad (the containment component).
- `--adv`: three parts. (i) The **panel-incidence witness** — θ(3,4,5) seed
  345, `pt(b) ∈ Π(c)`, `pt(b)` on `M`, `span ω⁻ = 1`. (ii) The **(Λ0f)
  necessity witnesses** — constructed (not searched): moving `pt(x₃)` inside
  `Π(c)` to force `p⁺₃ = 0` gives `span ω⁺ = 2` at 4/4 frames, and forcing
  `q₃ = 0` gives `span ω⁻ = 2` at 4/4. (iii) The **hunt** over the habitat seed
  pools (seeds 200–499 × 4 habitats) and the local strata: hits for `λ ∝ p⁺`,
  `λ ∝ q`, `Q(z) = 0` — all **0** — plus the `(span ω⁺, span ω⁻)` and
  `rank Q|_{V_bc}` histograms and the `C(M) ∈ S` count, with the assertion that
  **every** off-pattern frame found carries a vanishing *middle* bracket, i.e.
  the only way (Λ0f) fails is the named one.

**Figures.**

| figure | value |
|---|---|
| `--witt` frames (5 strata × 3 + 4 habitats × 2) | **23**, all with `dim N = 2`, `S ∩ T = 0`, `rank Q\|_N = 2`, `rank Φ_loc = 2`, (Λ1) with scalar **1** |
| `--span` frames (38 strata × 4 + 4 habitats × 3) | **164**, `(span ω⁺, span ω⁻, deg ω⁺, deg ω⁻) = (3,3,3,2)` uniformly |
| `--dichot` frames (9 strata × 2) | **18**; both bad branches give `Q(z(t)) ≡ 0`, generic `λ` does not, (Λ3) + route A per frame |
| `--habitat` seeds | **4 each** at θ(3,4,5), NT21, NT24, NT30 (`λ` off both bad points, `Q(z) ≠ 0`, sign law, (T3) agreement) + **3** at θ(3,3,6) for the `ℓ = 3` corollary |
| `--l56`: `dim(S ∩ α_a)` at `k = 3,4,5,6` | **0, 1, 2, 3**; `rank Q\|_N = 1,2,2,2`; `dim(S ∩ T) = 0,0,1,2` = `dim radical`; `C(M) ∈ S` iff `k = 6` |
| `--l56`: the `k = 5` Plücker reduction, both sides | `(dim W, dim W^⊥, rank Q\|_{W^⊥}) = (3, 3, 3)` — a **smooth conic**, so the extra bad component is nonempty over `K̄` |
| `--adv` frames examined | **1497** (357 real habitat seeds + 1140 local frames) |
| `--adv`: `λ ∝ p⁺` / `λ ∝ q` / `Q(z) = 0` / `C(M) ∈ S` | **0 / 0 / 0 / 0** |
| `--adv`: `rank Q\|_{V_bc}` histogram (real seeds) | `{3: 357}` — always the smooth-conic case |
| `--adv`: `(span ω⁺, span ω⁻)` histogram | `{(3,3): 1491, (2,3): 6}`; **all 6** off-pattern frames have a vanishing *middle* `p⁺` entry — the named (Λ0f) failure, and nothing else |
| `--adv`: the two constructed necessity witnesses | `p⁺₃ = 0 ⟹ span ω⁺ = 2` (4/4), `q₃ = 0 ⟹ span ω⁻ = 2` (4/4) |
| `lambda1.m2` (M1)/(M2)/(M3): the gauge-free half of (Λ1) | identities in **20 / 30 / 16** indeterminates, residual **0** — no geometry in (M1)/(M2), no gauge anywhere |
| `lambda1.m2` (M4): (Λ1) end-to-end, matrix + scalar form | residual **0** in `ℚ[a,c,w,λ]` (16 indeterminates, `b,x₁,x₂,x₃` gauged) — all 16 matrix entries, scalar exactly **1** |
| `lambda1.m2`: the ungauged expansion | **infeasible** — degree 52 in 28 indeterminates, killed at 600 s |
| `lambda0.m2` (P1)–(P3): closed forms, genericity, containments | identities / non-vanishing in **14** indeterminates (20 ungauged, (P7)); `deg_t ω⁺ = 3`, `deg_t ω⁻ = 2` exactly |
| `lambda0.m2` (P4): the span criterion | `cross4` of all **4** coefficient triples `= ±w₃^{3−j}w₂^{j}·Π⁺·p⁺`; `Π⁺ = p⁺₂p⁺₃g₁₃g₁₄g₂₄`, `Π⁻ = q₂q₃g₁₃g₁₄g₂₄` |
| `lambda0.m2` (P5): the missing `g₁₄` clause | not vacuous — a degeneration killing **only** `g₁₄` keeps (Λ0a,b,c,e) + all four middle brackets and drops **both** spans |
| `lambda0.m2` run time | **0.1 s** (the `a`-line parameter `t` never becomes an indeterminate) |
| `outer.py --geom`: (Λ0g) | asserted in **both** directions at **12** (seed, companion) pairs (4 habitats × 3 hard-stratum seeds); `g₁₄ ≠ 0` at every one |
| `outer.py --geom`: the constructed `g₁₄ = 0` point | **4/4 habitats**; `g₁₃, g₂₄ ≠ 0` and all four middle brackets survive; both spans **3 → 2**; still **target-rank, `dim R_a = 1`, `dim V_bc = 3`**; `lambda.omega_curves`' coded (Λ0f) equivalence **raises** at each |
| `outer.py --geom`: does the third branch *bite*? | **0 of 4** — the habitat's own `λ` annihilates neither collapsed span, `Q(z(t)) ≢ 0` (deg 4) |
| `outer.py --habitat`: the named inventory | **7** named shapes carry a length-4 companion (θ(3,4,5), NT21, NT24, NT30, the `dominance` duplicates, and the `K4` menu-blocked flank `(1,1,3,5,3,5)`); **48** (split, seed, companion) triples, `g₁₄ ≠ 0` at every one |
| `outer.py --sweep`: the systematic sweep | **1357** class shapes with a length-4 companion, **4280** (split, companion) pairs, **4280** placed exactly — `g₁₄ = 0` at **0** |
| `outer.py --sweep`: (Λ0i) coverage | **3628 / 4280** covered by the free-end criterion alone; the 652 residual are all the single pattern `x₂` a hub |
| `outer.py --tangent`: `d g₁₄` on the chart | nonzero at **684/684** chart points, including **all 652** (Λ0i)-uncovered companions — so `{g₁₄ = 0}` is a proper hypersurface |
| `outer.py --patterns`: realizable hub patterns | **4 of 8** — `(0,0,0)`, `(0,0,1)`, `(1,0,0)`, `(0,1,0)`; **7002** companions. `(0,1,1)`, `(1,0,1)`, `(1,1,0)`, `(1,1,1)` unrealized **in scope** (a coverage boundary, not a theorem) |

**Confidence verdict.**

- **(Λ1) (the two-hyperplane bracket factorization): PROVEN — a symbolic
  identity over the function field**, upgraded 2026-08-05 from 23 sampled
  rational frames (`lambda.py --witt`) by `m2/lambda1.m2` (*Step 2*). Its
  gauge-free half (M1)+(M2)+(M3) is a complete proof; (M4) checks the assembled
  form end-to-end on a slice that meets every GL(4)-orbit once. It needs **none**
  of (Λ0) and none of the panel data — (Λ0) secures only the non-vanishing of
  the ingredients, itself now verified at the polynomial level. This is the arc's
  first class-uniform *positive* statement of any kind; it is about `Φ_loc`'s
  shape, and (as *Steps 3–5* show) it does **not** touch the escape's own
  uniformity.
- **(Λ0) and the `a`-line spans: PROVEN AT THE GENERIC POINT, and CLASS-UNIFORM**
  (2026-08-05, `m2/lambda0.m2`; *Standing notation* + *Step 3*). Every clause
  (a)–(f) is now a nonzero polynomial on the local frame's chart rather than a
  condition certified by witnesses in 38 strata; the containments and the
  `t`-degrees are identities; and the span criterion is the **closed form
  (Λ0f′)**, which is **wider than the recorded (Λ0f)** by the three Gram
  factors `g₁₃g₁₄g₂₄`, of which `g₁₄ = [b,x₁,x₃,c] ≠ 0` was asserted nowhere
  and is shown non-vacuous by an explicit degeneration.
  **The `g₁₄` clause itself is now located** (*Step 3a*, `outer.py`): it says
  the two marked points `C₁ ∩ M`, `C₄ ∩ M` of the meet line coincide
  **(Λ0g)**; wherever a companion end is free it is *implied by* (Λ0d)
  **(Λ0i)**, so it is a new hypothesis only in the `x₂`-a-hub pattern; and
  **no class habitat in the searched scope forces it** — `g₁₄ ≠ 0` at all
  4280 swept (split, companion) pairs and `d g₁₄ ≠ 0` on the chart tangent
  space at all 684 probed points. It is nevertheless **reachable at a good
  seed** of every probed habitat by an explicit chart move, so the clause is
  not decorative.
  **Why this is uniform and not 38 symbolic strata:** the proof mentions no
  habitat, no stratum and no sample — it runs on **one irreducible variety**
  (explicitly parameterized, hence irreducible), and the strata enter only in
  block (P6), where each is shown to map *onto a dense subset of that variety*.
  A dominant map pulls a dense open subset back to a dense open subset, so the
  conclusion is: **for every class habitat carrying a length-4 companion, (Λ0)
  holds on a dense open subset of its pencil chart.** That is the ∃-form (Λ0)
  is used in, uniformly over the class.
  **The one load-bearing conditional** is (P6)'s bridge, which is a geometric
  argument (hub panels are determined by local incidences or free; far hub
  neighbours are free far-graph points placed inside a panel; `hcard` caps the
  count at 2 so no normal space collapses), not a computation. Its constructive
  half is verified; its "every stratum arises this way" half is the reading of
  `sample_local_frame`'s model stated in *Standing notation*.
- **Step 1 (Witt structure `{Q = 0} ∩ T^{⊥B} = α_a ∪ β_{π_a}`), Step 1(i) (the
  `ℓ = 3` two-line closure), (Λ2) (the `a`-line dichotomy), (Λ3)
  (`★r ∝ C(bc)`), and the Λ-completeness theorem: proven-informally**, with
  (Λ0d) named as a hypothesis and (Λ0)/(Λ0f) now proven generic as above.
  (Step 1's maximal-isotropic input is separately re-derived symbolically as
  `lambda1.m2` (M3).)
- **(OUT) (the outer-line criterion, *Step 5a*): proven-informally,
  CONDITIONAL, and carrying NO DRIVER** (2026-08-05; migrated from
  `notes/Pencil-strategy.md` §4.6-U1, which now points here). It is a corollary
  of Steps 3–5 with no new geometry, and it is **exactly as conditional as
  (Λ2)** — (Λ0) in full, including two-sided (Λ0d) and the widened (Λ0f′) with
  its `g₁₄` clause; either degeneration replaces a bad *point* by a bad
  *hyperplane* and destroys the containment it rests on. It is **sufficient,
  never necessary** (a codimension-2 avoidance standing in for a codimension-3
  one), its hypothesis `C₁, C₄ ∈ V_bc` is a **rank lower bound**, so §2.3's
  asymmetry is relocated rather than evaded, and **its hypothesis has never been
  measured** — `--adv` reports the two proportionalities but not `λ₁`, `λ₄`
  separately. It closes nothing; it is a cheaper, far-side, panel-free test at
  `k = 4` and a bridge to the mixed stratum. **No gap-map *status* moves on it**
  (the (K-wit) row's *what would close it* cell gains it as a scoped sufficient
  condition).
- **Methodological verdict, and it cuts both ways.** This is the arc's first
  *demonstrated* per-stratum-to-class-uniform upgrade, and §5.3 was right that
  (Λ0) is where that logical form lives. But the reason it works is exactly the
  reason it does not generalize: **(Λ0) is a statement about the local frame
  alone**, in which the far graph does not appear — §(K-Λ)'s frame is designed
  to leave the far data in the free covector `λ`. The escape's uniformity,
  **(K-wit)**, quantifies over `λ`, so it is not a statement on this variety at
  all and no amount of generic-point computation on the frame reaches it. The
  upgrade therefore **confirms rather than circumvents** `notes/Pencil-strategy.md`
  §2.3's diagnosis: the symbolic route can make every far-graph-free
  *hypothesis package* of the arc uniform, and stops precisely where the far
  graph enters. **No gap-map status moves.**
- **(K-Λ) as an independent gap: REFUTED** — it is equivalent to (K-wit) at
  length-4-companion splits. Therefore **(K-pitch) at length-4-companion
  splits stays open, exactly as open as (K-wit)** — this pass does *not* close
  it, and no local argument can.
- **`ℓ = 5, 6` through the (T5) frame: refuted** (Step 7); the route-A half is
  length-free and survives. The refutation is of **that argument shape**, not
  of the conjecture and not of those shapes' closability (Step 7 *Scope*).
- The bracket-monomial *closed form* does extend from `ℓ = 3` to `ℓ = 4` — as a
  **product of two bracket-linear forms in the far covector** — but it is not a
  non-vanishing theorem, because its zero locus is nonempty exactly at the two
  structurally meaningful configurations.
- **Class uniformity is untouched.** This pass removes a named gap by showing it
  was never independent; it closes none.

**What would change this.** *(i)* A class habitat + seed with `λ ∝ p⁺`: that is
an escape **failure**, hence a counterexample to the pencil conjecture there —
hunt negative over the `--adv` pools. *(ii)* A habitat with `λ ∝ q`: harmless,
but it would exhibit the route-A branch in the wild and is worth recording.
*(iii)* A local frame satisfying (Λ0a–e) with `span_t ω⁺(t) ≠ 3` or
`span_t ω⁻(t) ≠ 3`: that would put a third component into (Λ2) and break the
completeness theorem — found only with a vanishing middle bracket (6 of 1497
frames, all accounted for), and the exhibited seed-345 collapse shows the
condition is not vacuous. *(iv)* At `ℓ = 5`, a *rational* point of the extra bad
component realized by a real habitat's `V_bc`: that would be a
length-5-companion split where the pitch route is blind while the escape holds —
the first genuine loss of the pitch route, and the sharpest reason to abandon it
at `ℓ ≥ 5`. *(v)* An error in (T1) or (T5) themselves — each is re-asserted per
seed here against an independently computed stress.

*(vi)* **ANSWERED, 2026-08-05 (*Step 3a*, `outer.py`): no class habitat in
the searched scope forces `g₁₄ = 0`.** The question was whether some class
habitat's whole pencil chart lies in `{g₁₄ = 0}` — the outer companion lines
`C(bx₁)`, `C(x₃c)` necessarily meeting — which by (Λ0f′) collapses the
`a`-line spans and gives (Λ2) a third branch, forcing the Λ-completeness
theorem to be restated. Three findings, in decreasing strength:

- **The clause is a coincidence of two points on `M`** (Λ0g), and wherever a
  companion end is free it is **implied by (Λ0d)** (Λ0i) — 3628 of 4280 swept
  pairs. It is a genuinely new hypothesis only in the `x₂`-a-hub pattern.
- **`g₁₄ ≠ 0`** at every one of **4280** exact (split, companion) pairs over
  **1357** class shapes, and **`d g₁₄ ≠ 0`** on the pencil chart's tangent
  space at **684/684** probed points — including all 652 (Λ0i)-uncovered
  companions. So `{g₁₄ = 0}` is a *proper hypersurface* of every chart in
  scope, not the whole chart.
- **But it is reachable at a good seed**: an explicit chart move produces, at
  each of θ(3,4,5)/NT21/NT24/NT30, a target-rank `dim R_a = 1` realization
  with `g₁₄ = 0`, every other (Λ0) clause intact, and both spans `3 → 2`.
  The third (Λ2) branch is therefore **real, and (Λ0)'s `g₁₄` clause is
  load-bearing** — it just never becomes the *only* option for a habitat.

**Λ-completeness stands as written**, provided (Λ0) is read with the widened
(Λ0f′) — which is what the theorem's "under (Λ0)" already means, since the
theorem is an `∃ good seed` statement and the bad set is a hypersurface.

*Scope of that answer, stated because it is easy to overstate.* Exhaustive
over the θ family, over `G° = K4` (lengths ≤ 5), and over `K4` + a parallel
`bc` edge (lengths ≤ 6); **capped** at 25 shapes per `|V°| = 5` hub graph
(3 graphs, `|E°| = 8, 9, 10`); the named inventory (`lambda`, `dominance`,
`flanks`) on top. Nothing beyond `|V°| = 5`, nothing at lengths above the
per-family bound, and — the sharpest boundary — **only 4 of the 8 companion
hub patterns are realized by any class shape in scope** (`--patterns`, at a
widened length bound of 8): the four with at most one hub among `x₁, x₂, x₃`.
A class shape realizing `(1,0,1)`, `(0,1,1)`, `(1,1,0)` or `(1,1,1)` — two or
more hubs on the companion interior — is **not** covered by anything above,
and whether one exists is open. That is the residual form of item (vi).

*(viii)* **A length-4-companion frame with `λ₁ = 0` and `λ₄ = 0`** — i.e. with
*both* outer companion lines relative twists (*Step 5a*). That puts the habitat
on the bad line `{λ₁ = λ₄ = 0}` of `P(S*)`, makes **(OUT)** inapplicable there,
and leaves only the full ratio test `p⁺₃λ₂ = p⁺₂λ₃` between it and an escape
failure. Never probed: the `--adv` pools record the two proportionalities but
not the two coordinates. Cheapest probe: a new driver mode reporting `λ₁, λ₄`
(equivalently `C₁, C₄ ∈ V_bc`) over the existing frames. A *uniform* reason some
class shape cannot have `C₁ ∈ V_bc` would upgrade (OUT) from a test into a
mechanism; §2.3 predicts that reason is a rank lower bound and therefore hard.

*(vii)* **A class shape whose length-4 companion carries two or more hubs**
(pattern `(1,0,1)`, `(0,1,1)`, `(1,1,0)`, `(1,1,1)`), i.e. two or more
hub-hub edges along the companion. None occurs in the swept families; the
`g₁₄` argument above says nothing about such a shape, and neither does
(Λ0i). Cheapest next probe: widen `outer.py --patterns` past `|V°| = 5`, or
prove the pattern impossible inside tight + `hnoRigid` + `hcard` (the same
shape of argument as §(K-slide) *Step 5*'s `ℓ₁ + ℓ₂ ≥ 7`).

## §(K-dom) — the dominance spike: the differential of `H ↦ V_bc`, and why C1 is not an inductive route (**dominance HOLDS at every class habitat probed; C1's two claimed values REFUTED; class uniformity untouched**)

Answering `notes/Pencil-strategy.md` §4-C1, the one candidate on that doc's
list nothing in the arc had run: *compute the Jacobian of the `V_bc` map with
respect to the far-realization parameters and measure its rank against
`dim Gr(3,6) = 9`.* Read against §(K-pitch) *Steps 1, 5b* (path-sum
containment and (T5)) and §(K-pure) *Step P3* ((PC-Z)), whose notation it
inherits verbatim. The strategy doc's §§2–4 are flagged there as
coordinator-authored synthesis carrying no driver; this section is the driver.

**Headline, stated up front.**

- **The rank is 9 — dominance holds — at every class habitat probed** (5 of
  them, companion lengths 4, 5, 6), so at each of those shapes the escape holds
  on a *dense open* subset of the chart. That is a genuine positive, and a new
  proof route.
- **But there is a structural cap, and it is sharp**: `rank dV ≤ min(9, 6k−14)`
  where `k` is the companion length (**(D1)**), so at `k = 3` the rank is at
  most **4**, measured to be exactly 4. `k = 3` habitats are exactly the ones
  whose split chain plus companion is a rigid `C₆`, i.e. **(K-res)** residuals —
  which `hK` carries as a byte-identical sibling.
- **Both of §4-C1's claimed values are refuted.** The far graph contributes at
  most `3(k−3)` to the rank (**(D2)**, a corollary of (T5), *attained* at every
  probed habitat and **0** at `k = 3`), so "as the far graph grows the image can
  only grow" is false: the image dimension is pinned by a purely **local**
  invariant. And the 2026-07-30 locality refutation was gated at `k = 6`, the
  *maximal* far-dependence grade, so it is not evidence for dominance in general
  — at `k = 3` the same quantity is `0` and, by (T1), the escape there is a
  **local** condition.
- **Class uniformity is untouched.** "Rank 9 at every class shape" is one
  determinantal condition per (shape, split) — the same per-shape object
  §(K-pure) *P5* identified as the wall. C1 relocates the wall; it does not
  cross it.

### Standing notation (on top of §(K-pitch))

Split chain `b–v–a–c` at a target-rank `G′`-seed with `b`, `c` hubs;
`H := G − v − a`; `V_bc` the relative twist system, `dim V_bc = 3`;
`T := ⟨C_ab, C_ac⟩`; `α(a)`, `Λ²π̂` the two maximal isotropic 3-spaces of
(PC-Z). The **companion length** `k` is the length of the *shortest* `b`–`c`
path of `H`; `k ≥ 3` always, since `dim V_bc = 3` needs `dim span{C_e : e ∈ P}
≥ 3`. Write `S_P := span{C_e : e ∈ P}`.

`Gr(3,6)` is `dim 9`, and at `V ∈ Gr(3,6)` its tangent space is
`Hom(V, K⁶/V)`, of dimension `3·3 = 9`. **The differential measured here is
the map (chart tangent) → `Hom(V_bc, K⁶/V_bc)`**, not the rank of a raw
coordinate Jacobian.

### Step D0 — the question, and what has to be held fixed

By (PC-Z) the escape fails exactly when `V_bc` meets `α(a)` or `Λ²π̂`; each is
the Schubert condition `σ₁` on `Gr(3,6)`, of **codimension 1**. So if the map
`H ↦ V_bc` were **dominant** — image dense in `Gr(3,6)` — a generic realization
would miss the bad locus and the escape would follow for generic reasons.

`α(a)` depends only on `pt(a)`; `Λ²π̂` only on `π̂ = plane(a,b,c)`, i.e. on
`pt(a), pt(b), pt(c)`. **Neither is far data.** So the well-posed dominance
question varies the chart with the bad locus *standing still*:

> **the FIXED scoping** — `pt(a)`, `pt(b)`, `pt(c)` and the two panels `Π(b)`,
> `Π(c)` frozen (`pt(a) ∈ M = Π(b) ∩ Π(c)` is then frozen consistently), every
> other chart coordinate free.

This resolves the `b`/`c` coupling the question carries (`b` and `c` are `a`'s
`G′`-neighbours, so `a`'s data constrains `H`'s realization at `b` and `c`): we
freeze *all* of it rather than trying to propagate it. Freezing more can only
lower the rank, so a rank of 9 in this scoping is a conservative positive.

Two further scopings are computed as **diagnostics only**: FREE (nothing
frozen — the bad locus co-moves, so a rank there bounds nothing about the
escape) and UNPINNED (the panel constraints dropped, `a,b,c` still frozen —
which isolates whether a rank deficiency is caused by the *pencil pin* or by
something pin-free).

Two scoping disciplines are load-bearing and were honoured: the differential is
taken along the **pencil-stratum chart** (the tangent space is the kernel of the
differentiated pencil condition `⟨n_u, pt(w) − pt(u)⟩ = 0` over every hub `u`
and `G′`-neighbour `w`), never along unconstrained point coordinates — the pin
removing freedom is the entire phenomenon under study; and no chart direction
is allowed to move `pt(a)`, `pt(b)` or `pt(c)` (asserted in the driver).

### Step D1 — (D1): the a-priori cap, `rank dV ≤ min(9, 6k − 14)`

This is settled **before** any numerics, because a structural cap and a
measured deficiency must agree.

> **(D1)** *(proven-informally)* In the FIXED scoping,
> `rank dV ≤ min(9, (3k − 5) + 3(k − 3)) = min(9, 6k − 14)`.
> In particular `rank dV ≤ 4` at every `k = 3` habitat, and `(D1)` is vacuous
> for `k ≥ 4`.

*Proof.* Fix a shortest `b`–`c` path `P = b x₁ … x_{k−1} c` of `H`. Path-sum
containment (§(K-pitch) *Step 1a*) gives `V_bc ⊆ S_P`, so `V_bc` is determined
by the pair (`S_P`, the annihilator of `V_bc` in `S_P*`). Two counts:

1. `S_P` is a function of `pt(x₁), …, pt(x_{k−1})` alone. In the FIXED scoping
   `x₁` is a neighbour of the hub `b`, so `pt(x₁) ∈ Π(b)`, a *frozen* plane —
   2 parameters; dually `pt(x_{k−1}) ∈ Π(c)` — 2; the `k − 3` middle interiors
   contribute `3` each. Total `3k − 5`. (If an `x_i` carries a further hub
   incidence it has *fewer* parameters, never more.)
2. `dim S_P = k` for `k ≤ 6` at a nondegenerate seed, and the annihilator of
   the hyperplane-or-deeper `V_bc ⊆ S_P` is a point of `Gr(k − 3, k)`, of
   dimension `3(k − 3)`.

The image of the chart therefore has dimension `≤ (3k − 5) + 3(k − 3)`, and the
rank of the differential is bounded by the image dimension. At `k = 3` the
containment is an **equality of 3-spaces** — `V_bc = S_P = ⟨C₁, C₂, C₃⟩`, the
§(K-pitch) *Step 5* configuration — the annihilator term is `0`, and the whole
map factors through `(pt x₁, pt x₂) ∈ Π(b) × Π(c)`: 4 parameters. ∎

**A basis-free corollary, independent of the freezing.** At `k = 3` the Gram of
`B` on `(C₁, C₂, C₃)` has a single nonzero entry `B(C₁,C₃) = [b,x₁,x₂,c]` (the
serial-chain signature, §(K-pitch) *Step 5*), so `rank B|_{V_bc} = 2` and

> `V_bc` always lies in the **discriminant hypersurface** `{det Gram_B = 0}` of
> `Gr(3,6)` — an 8-dimensional subvariety — so dominance is impossible at
> `k = 3` for a reason that no choice of frozen data can repair.

*Exact:* `--cap` asserts `rank Q|_{V_bc} = 2` at `k = 3` and `= 3` at `k ≥ 4`,
at 21 seeds over 7 habitats, together with `V_bc ⊆ S_P` at **every** `b`–`c`
path (not only the shortest).

### Step D2 — (D2): the far block is `3(k − 3)`, and it is attained

The strategy doc's inductive hope is about the *far* parameters specifically,
so they get their own bound. (T5) (§(K-pitch) *Step 5b*) already says the shape
of the answer: at a length-`k` companion **all far-graph dependence enters
through the annihilator `Λ` of `V_bc` in `S_P*`**. Counting that annihilator:

> **(D2)** *(proven-informally; a corollary of (T5) + (D1)'s count 2)*
> Restricted to chart directions that move only vertices **off** a shortest
> companion, `rank dV ≤ 3(k − 3)`. In particular the far block is
> `0` at `k = 3`, `3` at `k = 4`, `6` at `k = 5`, `9` at `k = 6`.

*Exact:* `--far` measures the far block at 14 seeds over the 7 habitats; the
per-habitat maximum is `0, 0, 3, 3, 6, 9, 9` in the table order of *Step D4* —
**the bound, attained at every habitat**. At the two `k = 3` habitats that means
all 13 resp. 41 far directions lie in `ker dV`.

Two consequences worth stating separately.

- **The far graph does not enlarge the image once `k` is fixed.** Beyond
  `3(k−3)` directions, every additional far parameter is in the kernel. At
  `k = 3` there is no budget at all: `V_bc` is *constant* along the entire far
  chart.
- **Locality is graded by `k`.** At `k = 3`, (T1) makes `⟨r⟩ = (V_bc ⊕ T)^⊥`
  with both summands functions of the six points `{b, x₁, x₂, c, a}` and
  `pt(a)`, so the escape criterion is a **local** condition there. The
  2026-07-30 route-1 locality gate (design doc §"(K) route-1 gate";
  `escape/localtest.py`) was run on the double subdivisions of `K4` and
  `K5 − M`, both `k = 6` — the *maximal* grade. Its refutation of locality is
  therefore consistent with (D2), and (D2) explains it: far-dependence rises
  from nothing to everything as `k` runs 3 → 6.

### Step D3 — `hnoRigid` forces `k ≥ 4`, so (D1) bites exactly on (K-res)

The split chain (3 edges) and a shortest companion (`k` edges) are internally
disjoint, so their union is a cycle `C_{3+k}` of `G`, and it is *proper*
(`b`, `c` are hubs, so `G` has more edges). By R3 (`def(C_j) = max(0, j − 6)`)
that cycle is **rigid iff `3 + k ≤ 6`, i.e. iff `k = 3`**. Hence:

> **(D3)** *(proven; it is §(K-slide) *Step 5*'s `ℓ₁ + ℓ₂ ≥ 7` in this
> notation)* A tight `hnoRigid` habitat has `k ≥ 4`. Equivalently, every
> `k = 3` habitat is a **(K-res)** residual, not a member of the pinned-`hK`
> class.

*Exact:* `--cap` asserts the `C_{3+k}` dichotomy at all 21 seeds and
cross-checks it against `kslide.no_rigid_branch_union` (the exhaustive
branch-union sweep) — the two certificates agree at every habitat.

So (D1) is **vacuous on the pinned `hK` class** and bites exactly on the
(K-res) half that `hK` also carries since the 2026-08-02 route-3(b)
adjudication. That is the honest scope of the negative: it does not touch the
class, and it does block C1 from covering everything `hK` must cover.

### Step D4 — the measurement

`--jac`, 7 habitats × 3 valid seeds × 3 scopings. Rank is lower semicontinuous,
so the **maximum over seeds** is a lower bound for the generic rank, and (D1) is
the upper bound; where the two meet the generic rank is *determined*.

| habitat | `k` | status | FIXED | FREE | UNPINNED | (D1) cap |
|---|---|---|---|---|---|---|
| θ(3,3,6) | 3 | (K-res) | **4** | 8 | 6 | 4 |
| NT21c3 | 3 | (K-res) | **4** | 8 | 6 | 4 |
| θ(3,4,5) | 4 | class | **9** | 9 | 9 | 9 |
| NT21 | 4 | class | **9** | 9 | 9 | 9 |
| NT16k5 | 5 | class | **9** | 9 | 9 | 9 |
| `K4` dbl-subdiv | 6 | class | **9** | 9 | 9 | 9 |
| `K5−M` dbl-subdiv | 6 | class | **9** | 9 | 9 | 9 |

Readings:

- **`k = 3`: rank exactly 4**, i.e. (D1) is *sharp*, at both habitats and every
  seed. Dropping the pencil pin (UNPINNED) raises it only to **6** = the
  `2 × 3` parameters of the two companion interiors freed of their panels, so
  **the deficiency is path-sum containment, not the pin**: C1 would fail at
  these shapes in KT's unpinned world too.
- **`k ≥ 4`: rank 9 at every habitat**, at 1–3 of the 3 seeds each (a seed
  giving 8 is a non-generic point of an irreducible chart, which
  semicontinuity handles). The map is **dominant** at θ(3,4,5) — the
  §(K-Λ)/(K-wit) exemplar — at two non-theta class shapes and at both control
  double subdivisions.
- The escape itself holds at **all 21** seeds (`V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0`,
  asserted), *including* the rank-capped `k = 3` ones. So dominance is
  **sufficient and very far from necessary** for the escape.

### Step D5 — what dominance buys at a shape, exactly

> **Proposition (D4).** Let a (shape, split) have a rational FIXED-scoping seed
> at which `rank dV = 9`. Then on a dense open subset of that shape's pencil
> chart the seed is target-rank, nondegenerate, and satisfies
> `V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0` — hence, by (PC-Z) and (T2)/(T3), `Q(r) ≠ 0`
> and the escape holds on **both** KT routes.

*Proof.* The chart with `pt(a), pt(b), pt(c), Π(b), Π(c)` frozen is an
irreducible tower of affine-linear fibres (§(K-slide) *Step 1(e)*, with the
first stages frozen). Rank is lower semicontinuous, so `rank dV = 9` at one
point makes the generic rank `9 = dim Gr(3,6)`; in characteristic `0` that is
dominance, so the preimage of the codimension-1 bad locus is a proper closed
subset. The remaining requirements (target rank, `dim V_bc = 3`, the (T2) side
conditions) are open and nonempty at the witness seed. A finite intersection of
dense opens in an irreducible variety is dense open. ∎

**Calibrate this honestly.** §4-C1's own caveat — "dominance *at one habitat* is
per-shape again" — is correct, and the driver's numbers do not weaken it. What
(D4) adds over §(K-flank)'s per-shape `∃`-witnesses is that it certifies a
*dense open* set of good seeds rather than one, and does so **uniformly in the
bad locus**: the same rank-9 statement kills *every* codimension-1 obstruction
at that shape, not just the two of (PC-Z). It is a strictly stronger per-shape
statement. It is not a more *useful* one for `hK` as pinned, because one
`Q(r) ≠ 0` witness plus chart irreducibility already gives the escape at a
generic seed — which §(K-flank) has at 16/16 probed splits.

### Step D6 — assessment of §4-C1's two claimed values

The strategy doc gives two reasons to prefer dominance over a pointwise
condition. Both fail, and (D2) is why.

**Claim (i) — "it is inductive in the right direction: as the far graph grows by
a generating move, parameters are *added*, so the image can only grow."
REFUTED.** By (D2) the far parameters' contribution is capped at `3(k−3)`, a
function of the *local* companion length only. Once that budget is saturated —
and `--far` shows it is saturated at every habitat probed — every further far
parameter lies in `ker dV`, so growing the far graph does not enlarge the image.
At `k = 3` the budget is `0`: the image is a fixed 4-fold no matter how large
the far graph is. What would actually have to be carried inductively is `k ≥ 4`,
and by (D3) that is *exactly* `hnoRigid` — already an antecedent of `hK`. The
inductive content C1 hoped to gain is therefore already in the hypothesis, and
C1 adds nothing to it.

**Claim (ii) — "it reframes route 1's refutation as an asset: the escape's zero
locus moves with the far graph, so the map is highly non-constant." REFUTED as
an inference.** The route-1 gate measured the *stress*-side zero locus at
`k = 6` habitats (`escape/localtest.py`, double subdivisions of `K4` and
`K5 − M`), which by (D2) is the maximal far-dependence grade. The same
measurement at `k = 3` would return the opposite verdict: far-dependence `0`,
and by (T1) a fully local escape criterion. So "the map is highly non-constant"
is not a property of the class — it is a property of high `k`, and the correct
statement is the **grading** (D2), not a global non-constancy.

**And the wall is not crossed.** Suppose one wanted the uniform statement
"`rank dV = 9` at every class (shape, split)". That is the non-vanishing of a
`9 × 9` minor of a matrix built from one shape's chart — **one determinantal
condition per (shape, split)**, with no subset-indexed family, no exchange, no
matroid: precisely the ingredient-2 failure §(K-pure) *P5* isolates. C1
*relocates* the crux from `Q(z) ≢ 0` to `rank dV = 9` — a strictly stronger and
equally per-shape condition. It is not a route to class uniformity.

### Step D7 — what this leaves, honestly

- **(K-dom)**, the uniform form — "`rank dV = 9` at every class (shape,
  split)" — is **open**, verified at 5 class habitats spanning `k ∈ {4,5,6}`,
  and provably **false** on the (K-res) `k = 3` family. Because a
  counterexample on the class would be a shape whose entire chart maps into a
  proper subvariety of `Gr(3,6)`, and none is known, the statement is plausible
  — but it is not a *weaker* target than `hK`, so closing it is not progress
  unless a mechanism appears.
- The `k = 3` family is not a loss: it is exactly where §(K-pitch) *Step 5*'s
  bracket monomial **closes** the pitch (θ(3,3,6)). So the two mechanisms are
  complementary — a **companion-length dichotomy** (`k = 3` by the monomial,
  `k ≥ 4` by dominance) covers every habitat probed. Whether that dichotomy can
  be made uniform is exactly the open (K-dom) plus the already-open `k ≥ 4`
  side; the dichotomy is an *organizing* observation, not a proof.
- Not probed: `k = 4, 5, 6` habitats with a **parallel `G°` edge** (`P21`-type),
  where §(K-pure) *P4* locates a separate obstruction; and whether any class
  shape has `rank dV < 9`.

### Verification

`notes/scripts/w4/dominance.py` (tracked, new this pass; exact-ℚ, stdlib-only,
no CAS; sits beside `flanks`/`pure`/`lambda` on `repin`/`pitch`/`kslide`; every
sampled object rank/dimension asserted, including `flanks.star_span_ranks` as
the `plane_basis` genericity guard; all rng seeded, `PYTHONHASHSEED=0` pinned;
all four modes verified byte-deterministic across repeated runs). Run from the
repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --cap       # (D1), (D3)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --jac       # the rank table
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --far       # (D2)
PYTHONHASHSEED=0 python3 notes/scripts/w4/dominance.py --validate  # the machinery
```

**The model, and why the differential is computable in exact ℚ.** `V_bc` is the
image under `m ↦ m(b) − m(c)` of the kernel of the **augmented** system in
unknowns `(m_x)_{x ∈ V(H)}`, `(ω_e)_{e ∈ E(H)}`

```
m_x − m_y − ω_e·C_e = 0      (6 rows per edge e = (x,y)),
```

whose entries are *polynomial* in the chart coordinates. So each directional
derivative is implicit differentiation of a kernel: `A u = 0` and
`A u′ = −(∂A) u`, a derived linear system solved at the base point, with
`dV(δ)` the class of `u′[m_b] − u′[m_c]` in `K⁶/V_bc`. Solvability of every such
system is itself asserted (it is exactly the local constancy of `rank A`). The
chart tangent is `ker` of the differentiated pencil condition, so the derivative
never leaves the stratum. This is §(K-pitch) *Step 1(b)*'s "`V_bc` needs only a
kernel computation" made differentiable.

Habitats (7): θ(3,3,6) and **NT21c3** (`k = 3`; NT21c3 is the NT21 hub
multigraph with the companion shortened to 3 — `b`–`c` paths 3 and 3, plus
`b–u:4, u–c:4, b–w:3, w–c:3, u–w:4`; `|V| = 21`, `|E| = 24` — so the `k = 3`
cap is not a θ artifact); θ(3,4,5) and NT21 (`k = 4`); **NT16k5** (`k = 5`; hubs
`b,c,u,w`, one `b`–`c` path of length 3 plus `b–u:2, u–c:3, b–w:2, w–c:3,
u–w:5`; `|V| = 16`, `|E| = 18`); and the double subdivisions of `K4` and
`K5 − M` (`k = 6`, the arc's control habitats and route 1's locality-gate
shapes). Every one is asserted tight (`5|E| = 6(|V|−1)`), `def = 0`,
`hcard_ok`, triangle-free at load; class-vs-(K-res) is decided per habitat by
the two agreeing certificates of *Step D3*.

Per mode, what is asserted:

- `--cap`: `V_bc ⊆ S_P` at **every** `b`–`c` path of `H` (not only shortest);
  at `k = 3`, `V_bc = S_P` exactly; `rank Q|_{V_bc} = 2 ⟺ k = 3`; the
  `C_{3+k}` rigidity dichotomy, cross-checked against
  `kslide.no_rigid_branch_union`; and `V_bc ∩ α(a) = V_bc ∩ Λ²π̂ = 0` (the
  escape) at every seed.
- `--jac`: `dim V_bc = 3`; no FIXED/UNPINNED direction moves `a`, `b` or `c`
  (the bad locus stands still); every implicit-differentiation system solvable;
  `rank dV ≤` the (D1) cap; at `k = 3` the cap **attained** and the UNPINNED
  rank `≤ 6`; at `k ≥ 4` rank 9 attained.
- `--far`: `rank dV|_{far} ≤ 3(k−3)` at every seed, and `= 0` at `k = 3`.
- `--validate`: three independent models for `V_bc` agree (the rigidity matrix
  via `pitch.H_motions_vbc`, the augmented system, the cycle kernel), with
  `dim ker(augmented) = dim mot(H)` and `dim Z = dim mot(H) − 6`; the
  augmented-system and **cycle-kernel differentials agree entry by entry** on
  every chart direction (two different matrices, two different solves); and an
  exact secant quotient `φ(t)/t` on a chart-*exact* ray (directions moving no
  hub normal keep `θ₀ + tδ` in the chart identically) converges to the computed
  differential, error halving at `t = 2^{−3..−6}`.

**Figures.**

| figure | value |
|---|---|
| `--cap` seeds | **21** over 7 habitats; containment at every `b`–`c` path; `rank Q\|_{V_bc}` = 2 at `k = 3`, 3 at `k ≥ 4`; escape holds at **21/21** |
| `--jac` FIXED rank, `k = 3` (θ(3,3,6), NT21c3) | **4** at 6/6 seeds = the (D1) cap, attained |
| `--jac` UNPINNED rank, `k = 3` | **6** at 6/6 seeds — the pin is not the cause |
| `--jac` FIXED rank, `k ≥ 4` (5 habitats) | **9** attained at each; `dim Gr(3,6) = 9`, so **dominant** |
| `--far` far block at `k = 3,4,5,6` | **0, 3, 6, 9** = `3(k−3)`, the (D2) bound, attained at every habitat |
| `--far` far directions in `ker dV` at `k = 3` | **13/13** (θ(3,3,6)), **41/41** (NT21c3) |
| `--validate` habitats | **7**; three `V_bc` models agree; two differentials agree on all 9 entries × every direction; secant errors halve |

**Confidence verdict.**

- **(D1) (the `min(9, 6k−14)` cap), (D2) (the `3(k−3)` far block), (D3)
  (`hnoRigid ⟹ k ≥ 4`), (D4) (dominance ⟹ the escape on a dense open set):
  proven-informally**, each with a driver mode asserting that sentence.
- **Dominance at the 5 probed class habitats: proven-informally per shape**
  (rank 9 at a rational seed + chart irreducibility + semicontinuity).
- **Dominance as a class-uniform statement, (K-dom): open** — and **false** on
  the (K-res) `k = 3` family, so it cannot serve `hK` in the form `hK` is
  carried.
- **§4-C1's claims (i) and (ii): REFUTED** (Step D6). C1 is **not** an
  inductive route and does not escape the ingredient-2 failure; it is not
  recommended as the phase's direction.
- **Class uniformity is untouched.** No uniform gap closes here.

**What would change this.** *(i)* A class habitat (`k ≥ 4`, `hnoRigid`) whose
FIXED rank is `< 9` at *every* seed — that would be a sharp new obstruction and
would make (K-dom) false outright; none found, and the driver's `--jac` is the
place to add shapes. *(ii)* A far-direction rank exceeding `3(k−3)` — that would
refute (D2) and, with it, Step D6's refutation of claim (i); asserted per seed.
*(iii)* An error in the differentiation itself — guarded by two independent
derivative routes agreeing entry by entry plus the secant test, so an error
would have to be shared by the augmented and cycle models. *(iv)* A `k = 3`
class habitat — impossible by (D3), whose two certificates agree at every
habitat; a disagreement would be the finding. *(v)* A mechanism making
`rank dV = 9` *combinatorially* certifiable at every class shape — that, and
only that, would turn C1 into a uniform route; nothing in the arc suggests one,
and §(K-pure) *P5* is the reason to expect none.

## §(K-σ) — the polarity as a symmetry of the split: **route σ, a CANDIDATE third escape route** (**offered for adjudication, not settled**; the σ-intertwining question **REFUTED in its literal form** and **CONFIRMED covariantly**; **σ-equivariant seed recipes DEAD**)

Read against §(K-tight) *Steps 0–3* (whose criterion it uses verbatim),
§(K-pure) *Step P3* ((PC-Z)) and §(K-Λ) *Steps 1, 4, 5* (whose two-point
failure locus it explains). Notation inherited from §(K-Λ) *Standing
notation*.

**Status, stated before the mathematics, because four things here are settled
and one is not** — and because the whole section carries a **field-scope
qualifier** stated immediately after the bullets.

- **Settled — refuted, `ℝ`-specifically.** The σ-intertwining question *in its
  literal form*: σ does **not** intertwine `α(a)` and `Λ²π̂` of one
  configuration (*Step σ1(a)*). **The argument uses `ℝ`-definiteness and does
  not port** — see *Field scope*.
- **Settled — confirmed.** The **covariant** form `σ(α_p) = β_{p^⊥}`,
  `σ(β_π) = α_{pole(π)}`, which exchanges the two branches of (PC-Z) across an
  involution of the seed space (*Step σ1(b)*).
- **Settled — refuted, `ℝ`-specifically** (the "over `ℝ`" below is load-bearing,
  not decorative; *Field scope*). **σ-equivariant seed recipes are dead**: over
  `ℝ` with
  the project's polarity there is *no* σ-fixed pencil configuration at all, and
  for a general correlation the fixed locus is degenerate — a null correlation
  forces every hinge line into a linear line complex and produces a self-stress
  per cycle (*Step σ6*, measured deficit exactly 1 at 6/6 on tight `C₆`). This
  is `notes/Pencil-strategy.md` §2.4's *"degenerate enough to compute, and you
  break the thing you're computing"* wall, now with a proof.
- **CANDIDATE, offered for adjudication — not asserted as settled.**
  **Route σ**, a third escape route obtained by running route A at the dual
  seed `σu`. If the derivation below is right it closes (K-tight) on the hard
  stratum, *length-free*. It rests on **four named obligations** (*Step σ5*),
  the first of which — σ-nondegeneracy of the transported seed — was recorded
  as *observed 63/63, not proven* and is now **verified in both directions**
  (2026-08-05, `sigma.py --hunt`): the dual conjuncts **CAN fail at a
  hard-stratum, primally nondegenerate seed** (53 constructed witnesses), so
  the 63/63 was genericity and never an implication; but only **two** of the
  four are genuinely new, and the steering repair is exhibited **exactly** on
  a chart line through the failure. **No gap-map status moves on account of
  route σ**: (K-tight) keeps its status with a candidate noted, and `hK` stays
  carried as pinned.
- **Settled — proven, and new this pass.** *Step σ3*'s side condition
  `pt(b) ∉ Π(c)` is **free**: primal nondegeneracy at the split's middle body
  `a` forbids *both* halves of (Λ0d) from failing at once (**(σ7)**), so the
  σ-completeness span is `K⁶` via `α_{pt(b)}` or via `α_{pt(c)}`. This settles
  *What would change this* item (iv) at every both-ends-hubs split. It does
  **not** make the two-sided (Λ0d) of §(K-Λ) free — see (σ7)'s scope note.
  **(σ7) is the one result here that needs no polarity at all** — see *Field
  scope* immediately below.

### Field scope — read this before quoting anything in this section

**Recorded as an open gap, 2026-08-05 (coordinator verification of `bd270bce`);
NOT settled here, and no attempt is made to settle it.** This whole section is
about a polarity that exists **in tree only over `ℝ`**, while the obligation it
aims to discharge is consumed at a **general infinite field**. Three landed
signatures, verified directly:

| object | field | source |
|---|---|---|
| `screwComplementIso` (= `σ`) | **`ℝ`-only**: `ScrewSpace ℝ 2 ≃ₗ[ℝ] ScrewSpace ℝ 2` | `Molecular/Molecule/Duality.lean:69` |
| `hasPencilPanelRealization_mapExtensor_screwComplementIso` | **`ℝ`-only**: `{F : BodyHingeFramework ℝ 2 α β}` | `Pencil/Statement.lean:257` |
| `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`, and **`hK` inside it** | **general**: `[Infinite K]`, `PencilPair K 3 G`, seed `q : α × Fin 4 × Fin 4 → K` | `Pencil/Escape.lean:555` |

`HasPencilPanelRealization`, `IsNondegPencilRealization`,
`HasGenericPencilRealization` and the whole chart/`pencilRow` engine are
**general-`K`** (Phase 33 made the core chain field-general). Exactly **five**
declarations in `Pencil/` fix `ℝ`, and **four of them are the polarity
cluster**: `screwComplementIso_mk_extensor` (`Statement.lean:166`), the two
forward predicate transports (`:185`, `:216`) and the self-duality theorem
(`:257`). The fifth, `exists_hasPencilPanelRealization_witness` (`:665`), is an
unrelated concrete `d = 3` non-vacuity certificate.

**Consequence, stated plainly.** "*Step σ5* obligation 1's conjunct 1 is free by
a landed theorem" is true **at `ℝ`**. At the general `K` where `hK` is
quantified there is no polarity in tree, so there is no `σ`, no route σ, and no
freeness claim. Nothing in this section is *wrong* — the numerics are ℚ ⊂ ℝ and
every verdict below holds over `ℝ` — but the qualifier was missing, and the gap
map advertised obligation 1 as "sized" without it.

**Which verdicts are field-neutral and which are genuinely `ℝ`-mathematics** (by
reading the arguments, not by re-deriving them):

- **Needs no polarity at all, so field-neutral outright: (σ7)** and the *Step
  σ3* span computation's linear algebra. (σ7)'s proof uses only the primal
  conjuncts and `dim M = 2`; the span computation uses the Klein form `B`, which
  is the volume form and exists over any field.
- **Field-neutral *modulo the polarity existing*: (σ1)–(σ6)**, the covariant
  statement *Step σ1(b)*, route σ itself, and the conjunct-1 freeness. Each is a
  statement about `⋆` and the standard (nondegenerate) pairing, neither of which
  needs `ℝ`.
- **Genuinely `ℝ`-mathematics, because it uses *definiteness*, not just
  nondegeneracy — and therefore **not** portable:** *Step σ1(a)*'s refutation of
  the literal intertwining (`pt(a) ∈ pt(a)^⊥ ⟹ pt(a)·pt(a) = 0 ⟹ pt(a) = 0`)
  and *Step σ6*'s "no σ-fixed pencil configuration exists". Over a field with
  isotropic vectors both arguments simply stop; whether their **conclusions**
  survive is **unknown and untested**. A successor porting this section must
  *re-derive* these two, not re-cite them.

**Does the polarity generalize past `ℝ`? OPEN — but the reading is encouraging,
and this is a reading, not a proof.** Both ingredients of `screwComplementIso`
are **already field-general in tree**: `complementIso` is
`⋀[K]^j (Fin (k+2) → K) ≃ₗ[K] ⋀[K]^(k+2−j) (…)` (`Molecular/Meet.lean:479`),
built from `wedgePairing` (injective over any field, via `Pi.basisFun K`) and
`toDualEquiv`; and `ScrewSpace.equivExteriorPower (K) [Field K] (k)` is general
(`RigidityMatrix/Basic.lean:185`). So `screwComplementIso`'s `ℝ` looks like a
**writing choice, not a mathematical obstruction** — the definition would
typecheck verbatim with `K` in place of `ℝ`. The four ℝ-fixed *theorems*'
helper inputs are general-`K` too (`mem_span_of_dotProduct_perp_pair`
`Statement.lean:133`, `exists_extensor_eq_panelSupportExtensor`,
`extensor_ne_zero_iff_linearIndependent`, `panelSupportExtensor_ne_zero_iff`).
**None of that is a proof, and no generalization is attempted here.**

**Precedent: the phase has already hit this exact mismatch once.** `Pencil/
Arms.lean`'s W3-L4 section header records it verbatim — the landed
Crapo–Whiteley projective invariance "is over `ℝ` … the pencil arm works over a
general field `K`", so that section **wrote the `K`-level transport itself**
rather than reusing the ℝ one. Same shape, same fix pattern, one section's cost.

**Headline.** The projective polarity `σ := screwComplementIso` is a genuine
symmetry of the pencil stratum, and it is *not* a symmetry of the escape
**analysis** — because that analysis is conducted in one frame of a dual pair.
In the other frame the carrier keeps a freedom the first frame's nondegeneracy
forbids. Concretely:

- §(K-Λ)'s two-point failure locus `{V_bc ⊥_B C(M)}` (recorded there as *the
  genuine (T3) failure*) and `{V_bc ⊥_B C(bc)}` (recorded as *route A escapes
  outright*) is **exactly a σ-orbit**: `σ` exchanges `C(M)` with `C(bc)`. The
  asymmetry the workbook records is therefore **not** evidence that the symmetry
  breaks; it is the signature that only one of the two dual frames is in scope.
- Transporting route A along `σ` gives **route σ**, whose uniform-failure
  criterion is `★r ∥ C(bc)`, the exact σ-image of routes A/B's `★r ∥ C(M)`. The
  two **cannot fail simultaneously**: `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)}` is all of
  `K⁶` whenever `pt(b) ∉ Π(c)`, so `r = 0`, contradicting `dim R_a = 1` — and
  when that half of (Λ0d) *does* fail, **(σ7)** (*Step σ3*) supplies the
  `c`-mirror, so no genericity hypothesis is added.
- Route σ's witness is a **nondegenerate** target-rank pencil realization of `G`
  satisfying the chart's binding point equations — the shape `hK` consumes, not
  a degenerate boundary point. It *looks* degenerate only when pulled back into
  the original frame, where it is the coincident-point configuration
  `pt(v) = pt(b)` on the carrier's forbidden locus — which is why the one-frame
  analysis could not see it.

**Why the gain is *evidence → argument*, not *bug fixed*.** The branch route σ
closes has **never been observed nonempty** (`lambda.py --adv` hunts for
`λ ∝ p⁺` and finds none; and at all 63 seeds sampled here routes A/B *already*
escape at `u`). Route σ does not repair an observed failure — it removes the
*possibility* of one, uniformly, which is precisely what "making some good seed
exist uniformly over the class" asks for.

### Step σ0 — the polarity in coordinates, and what it does to a pencil realization

`screwComplementIso` (`Molecular/Molecule/Duality.lean:69`, **`ℝ`-only** —
*Field scope*) is `complementIso`
at `j = k = 2` conjugated by `ScrewSpace.equivExteriorPower`; `Molecular/
Meet.lean:88` records that `complementIso` is built from the volume form
(`screwAlgebraTopEquiv`) and the standard dot product (`Pi.basisFun.toDual`),
*"i.e. it **is** the Hodge star `⋆`"*. So on `Λ²K⁴` in Plücker coordinates
`σ = ⋆` is the signed swap of complementary index pairs (`repin.hodge_star`),
and three facts are elementary and exact:

> **(σ1)** `σ² = id` (`⋆² = (−1)^{p(N−p)} = +1` on `Λ²` of a 4-space).
> **(σ2)** `σ` is a Euclidean isometry *and* self-adjoint, so `(σC)^⊥ = σ(C^⊥)`.
> **(σ3)** `σ` is an isometry of the Klein form: `B(x,y) = ⟨x, ⋆y⟩ = vol(x ∧ y)`
> and `vol(⋆x ∧ ⋆y) = ⟨x, ⋆y⟩`. Hence `σ` preserves `Q`, the Klein quadric and
> every `⊥_B` condition, and it exchanges the two families of maximal
> isotropics: **`σ(α_p) = β_{p^⊥}`** and **`σ(β_π) = α_{pole(π)}`**.

On a pencil realization the landed
`hasPencilPanelRealization_mapExtensor_screwComplementIso`
(`Pencil/Statement.lean:257`) carries `(F, normal, point)` to
`(F.mapExtensor σ, point, normal)` — same multigraph, roles swapped. In
coordinates this has a completely elementary form, which is what makes it
computable:

> **(σ4)** *(exact; 63/63 seeds)* Write `p̂_w` for a body's homogeneous point and
> `ν_w` for its homogeneous panel normal. Then for every edge `uw`,
> `span(ν_u, ν_w) = span(p̂_u, p̂_w)^⊥`, i.e. `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)`.
> **So `σ` is: replace every body's point by its own panel normal.** The
> incidences `ν_w · p̂_w = 0` and `ν_u · p̂_w = 0` (`w` a neighbour of `u`) are
> exactly what makes this work, and they *are* the pencil conditions.

Consequently `σu` is a pencil realization of the same `G′`, with the same
hub/non-hub combinatorics, and `rank R(σu) = rank R(u)` (transport along a
linear automorphism). Verified exactly: `rank`, `s₀`, `dim R_a` agree at 63/63.

### Step σ1 — what σ does to the split data, and the two readings

Fix the split chain `b–v–a–c` at a `G′`-seed `u`. Everything below is exact.

| object at `u` | its image at `σu` |
|---|---|
| `Π(b), Π(c)` (panels) | `p̂_b^⊥, p̂_c^⊥` |
| `M = Π(b) ∩ Π(c)` (meet line) | `σ(C(bc))` — the polar of `line(b,c)` |
| `C(bc) = line(b,c)` | `σ(C(M))` — the meet of the image panels |
| `α_{pt(a)}` (lines through `pt a`) | `β_{pt(a)^⊥}` |
| `β_{π_a}`, `π_a = plane(a,b,c)` | `α_{pole(π_a)}` |
| `V_bc` | `σ(V_bc)` (motions transport by post-composition) |
| `r` (the transmitted boundary load) | `σ(r) = ★r` (verified 63/63) |
| `dim R_a`, `s₀`, target rank | unchanged (verified 63/63) |

**(a) The literal question is answered NO — REFUTED.** `σ` does **not**
intertwine `α(a)` and `Λ²π̂` *of one configuration*: that needs
`pt(a)^⊥ = π_a` and `pole(π_a) = pt(a)`, i.e. `pt(a)` self-conjugate with `π_a`
its polar plane — a codimension-3 condition, and over `ℝ` with the project's
polarity (built on the **definite** standard dot product, `Molecular/
Meet.lean:88`) it is *impossible*: `pt(a) ∈ π_a` always, and `pt(a) ∈ pt(a)^⊥`
forces `pt(a) · pt(a) = 0`, hence `pt(a) = 0`.

**(b) The covariant statement is YES, and it is the useful one — CONFIRMED.**
`σ` carries the `(α, β)` pair of the seed to the `(β, α)` pair of the image
seed, roles swapped. Since `σu` realizes the **same** graph with the **same**
split, the two branches of (PC-Z) are exchanged by an involution of the seed
space. In particular §(K-Λ)'s two-point locus is a single σ-orbit:

> **(σ5)** Because `σ` is a `B`-isometry with `C(M') = σ(C(bc))` and
> `C(bc)' = σ(C(M))`:
> `V_bc ⊥_B C(M)` **at `u`** ⟺ `V_bc' ⊥_B C(bc)'` **at `σu`**, and
> `V_bc ⊥_B C(bc)` **at `u`** ⟺ `V_bc' ⊥_B C(M')` **at `σu`**.
> The two branch *labels* swap across `σ`; the two branch *consequences*
> recorded in §(K-Λ) (genuine failure vs. route A escapes) do not — that
> asymmetry is explained by *Step σ2*.

Equivalently on the load side, using `⟨r⟩ = (V_bc ⊕ T)^⊥` ((T1)) and
`★C(M), ★C(bc) ⊥ T`:

> `★r ∥ C(M)` ⟺ routes A/B fail uniformly at `u` ⟺ `r ⊥ β_{Π(b)} + β_{Π(c)}`;
> `★r ∥ C(bc)` ⟺ `r ⊥ α_{pt(b)} + α_{pt(c)}` ⟺ routes A/B fail uniformly at `σu`.

### Step σ2 — route σ, and why the one-frame analysis missed it

**Definition.** *Route σ at `u`* = route A run at the seed `σu`. It is a
construction of a realization of `G`, and that is all the escape needs: `hK`'s
hypothesis is only that `G′` *has* a generic realization and its conclusion is
about `G`; no compatibility between the two is required, so it is irrelevant
that the produced realization extends `σu` rather than `u`.

**Its criterion.** Route A's uniform-failure criterion at `σu` is
`r(σu) ⊥ Λ²Π̂_{σu}(b)` (§(K-tight) *Step 2.4*, whose two derivation ingredients
both hold at `σu`: `b` is still a hub, and `pt_{σu}(a) ∈ Π_{σu}(b)` ⟺
`pt_u(b) ∈ Π_u(a)`, true because `ab ∈ E(G′)`). Now
`Λ²Π̂_{σu}(b) = β_{p̂_b^⊥} = σ(α_{pt(b)})` and `r(σu) = ★r`, and `σ` is
orthogonal, so

> **(σ6)** *(exact; verified as an equivalence at 63/63 seeds)*
> **route σ fails uniformly ⟺ `r ⊥ α_{pt(b)}` ⟺ `★r ∥ C(bc)`.**

**Why it was invisible.** Pull route σ's witness back into `u`'s frame (one more
application of `σ`): it becomes the configuration with `point(v) = pt_u(b)` —
the two points of the adjacent bodies `v` and `b` *coincide* — and `point(a)`
sliding along `Π_u(a) ∩ Π_u(c)`, with `C(va) = C_ab` pinned. That is **KT's dead
route M₁**, sitting at the extreme point `pt(v) = pt(b)` of the carrier's
forbidden locus `pt(v) ∈ line(a,b)` (§(K-tight) *Step 1*, row 1). So in `u`'s
frame route σ is a nondegeneracy-violating boundary construction, correctly
excluded — *but the same family, read in the dual frame, is perfectly
nondegenerate*. `IsNondegPencilRealization`'s conjuncts (`Motive.lean:110–115`)
are **not** σ-stable (conjunct 2 asks adjacent *points* distinct; there is no
adjacent-*panel* mirror), and this is the one place in the arc where that
asymmetry bites.

> **M₁ is killed twice in this workbook, for the same reason — so route σ faces
> exactly ONE crux, not two** (coordinator scrutiny, 2026-08-05). §(K-tight)
> *Step 1* rules M₁ out as *"the nondegeneracy-forbidden locus"*, and §(K-tight)
> *Step 2.6* rules it out again as *"M₁'s span is carrier-unrealizable"* — but
> the stated reason of the second is *"its construction pins `hinge(vb) :=
> q(ab)`, forbidden"*, i.e. the **same** pinning as the first. The two are one
> obligation. This materially bounds what verifying route σ costs.

This also explains, in one line, §(K-tight) *Step 2.6*'s "the carrier keeps 5 of
KT's 6 escape dimensions": the 6th dimension is not lost, it is in the other
frame. Route σ restores a 6th direction — `α_{pt(b)}`, not KT's `Λ²Π̂(a)`.

### Step σ3 — the completeness statement (the candidate)

> **Theorem (σ-completeness of the escape at a hard-stratum split) — CANDIDATE.**
> *(informal; the criterion is §(K-tight) *Step 2*'s, the rest is exact linear
> algebra. Conditional on obligation 1 of *Step σ5*.)* Let `u` be a target-rank
> nondegenerate pencil `G′`-seed with `s₀ = 0`, `dim R_a = 1` and both chain
> ends `b, c` hubs. Then **at least one** of
>
> `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶`,  `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(c)} = K⁶`
>
> holds, so from `r ≠ 0` at least one of **route A at `u`** (`r ⊥̸ Λ²Π̂(b)`),
> **route B at `u`** (`r ⊥̸ Λ²Π̂(c)`), **route σ at the `b`-end**
> (`r ⊥̸ α_{pt(b)}`) and **route σ at the `c`-end** (`r ⊥̸ α_{pt(c)}`) attains
> the target rank for `G`. The escape does not fail.

*Proof of the span.* `(β_{Π(b)} + β_{Π(c)})^{⊥_B} = β_{Π(b)} ∩ β_{Π(c)} =
⟨C(M)⟩`, so the sum is the 5-space `C(M)^{⊥_B}`. `α_{pt(b)} ⊆ C(M)^{⊥_B}` iff
every line through `pt(b)` meets `M`, iff `pt(b) ∈ M`, iff `pt(b) ∈ Π(c)`. So
under `pt(b) ∉ Π(c)` the sum is 6-dimensional (`α_{pt(b)} ∩ (β_b + β_c) =
pencil(pt b; Π(b))` is 2-dimensional, and `3 + 5 − 2 = 6`); symmetrically for
`α_{pt(c)}` under `pt(c) ∉ Π(b)`; and (σ7) supplies one of the two. ∎

`r ≠ 0` is exactly `dim R_a = 1` (`r` spans `R_a`). The `c`-end criterion is
already driver-tested at the pinned pool: `--transport` V3 asserts
`crit_B(σu) ⟺ r ⊥̸ α_{pt(c)}` at 63/63 alongside the `b`-end one.

**The side condition is FREE — this is new (2026-08-05) and it is a proof, not
a measurement.** The earlier statement carried `pt(b) ∉ Π(c)` as a hypothesis
and noted only that it is "one half of the already-named (Λ0d)", with the
`c`-mirror available "under the other half". That leaves open whether *both*
halves could fail. They cannot:

> **(σ7)** *(proven; validated `sigma.py --hunt` H4/H5)* Let `u` be a
> **primally nondegenerate** pencil realization of `G′` at a split whose chain
> ends `b, c` are hubs and whose middle body `a` is a non-hub with
> `closedNbhd a = {a, b, c}` (which is what `orient`'s degree-`2` `a` gives
> after `splitOff` adds `ab`). Then **at least one** of `pt(b) ∉ Π(c)`,
> `pt(c) ∉ Π(b)` holds.
>
> *Proof.* `ab, ac ∈ E(G′)` and `b, c` are hubs, so the cross-incidence
> (`dotProduct_eq_zero_of_extensorInPanel_of_extensorThroughPoint`, the fact
> `closedHubNbhd` is built on) puts `pt(a) ∈ Π(b) ∩ Π(c) = M`. Conjunct 3 at
> `a` reads `LinearIndepOn normal (closedHubNbhd a)` and `closedHubNbhd a` is
> exactly `{b, c}`, so `Π(b) ≠ Π(c)` and `dim M = 2`. Suppose **both** halves
> failed: `pt(b) ∈ Π(c)` gives `pt(b) ∈ Π(b) ∩ Π(c) = M`, and likewise
> `pt(c) ∈ M`. Then `pt(a), pt(b), pt(c)` all lie in the 2-dimensional `M`,
> contradicting conjunct 4 at `a` — `LinearIndepOn point (closedNbhd a)` on the
> 3-element set `{a, b, c}`. ∎

**Scope note, stated because it is easy to over-read.** (σ7) is about the
**disjunction** and nothing more. It does *not* make §(K-Λ) *Step 6*'s
two-sided (Λ0d) free — (Λ2) needs **both** halves, and (σ7) supplies only one.
Nor does it make *Step σ5* obligation 1's dual conjunct 2 free at `a`'s two
edges: that conjunct *is* two-sided (Λ0d) (see obligation 1), and one half can
fail, as `--hunt` H4 exhibits at 35 hard-stratum primally-nondegenerate
configurations. **The span is free; the dual conjunct is not.**

**Consequence for the (K-Λ) trichotomy, IF the candidate stands.** §(K-Λ)'s
*Theorem (Λ-completeness at length-4 companions)* reads: exactly one of
`Q(z) ≠ 0` (escape by pitch), `V_bc ⊆ C(bc)^{⊥B}` (escape by route A),
`V_bc ⊆ C(M)^{⊥B}` (**the escape genuinely fails**). The third branch is
precisely `★r ∥ C(M)`, i.e. route σ's *success* case. So the trichotomy would
have **no failure branch**, and the conclusion would be length-free — route σ
never mentions a companion, so it does not pass through (K-pitch), (K-wit),
(K-Λ) or the `ℓ ∈ {5,6}` obstruction at all. Those results stand as mathematics
either way; what changes is whether they are on the escape's critical path.

### Step σ4 — machine validation (exact ℚ)

Driver `notes/scripts/w4/sigma.py` (tracked, new this pass). **63** hard-stratum
seeds across two splits of the tight control (double-subdivided `K4`,
`|V| = 16`, target 90 / `G′` target 84): seeds 440–479 at chain 0 (34 valid) and
500–529 at chain 1 (29 valid), all with `s₀ = 0`, `dim R_a = 1`. Every figure is
`n/n` over that pool.

| check | mode | result |
|---|---|---|
| homogeneous pencil data `ν_w·p̂_w = 0`, `ν_u·p̂_w = 0` on edges | `--transport` V0 | 63/63 |
| **(σ4)** `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)` on every edge | V1 | 63/63 |
| `rank R(σu) = ` target, `dim R_a`, `s₀` agree with `u` | V2 | 63/63 |
| `r(σu) ∝ ★r(u)`, and **(σ6)** `crit_A(σu) ⟺ r(u) ⊥̸ α_{pt(b)}` (+ the `c` mirror) | V3 | 63/63 |
| **`dim(β_{Π b} + β_{Π c} + α_{pt b}) = 6`** — *genericity, not necessity: see the correction below* | V4 | 63/63 |
| route A at `σu` reaches target rank for `G`; its pullback into `u`'s frame is the `pt(v) = pt(b)` family | V5 | 63/63 |
| `dim(α_{pt b} + α_{pt c}) = 5`, perp generated by `★C(bc)` | `--adv` A | 63/63 |
| `dim(β_{Π b} + β_{Π c}) = 5`, perp `★C(M)`; `C(M) ∦ C(bc)` | `--adv` B | 63/63 |
| the pullback is a legal pencil realization (nonzero hinges, incidences, target rank) | `--adv` D | 63/63 |
| `predA` (= `r ⊥̸ α_{pt b}`) true; **`predAfalse = 0/63`** | `--adv` C | 63/63 |
| routes A/B at `u` *already* escape | `--adv` | 63/63 |
| `u` satisfies all four `IsNondegPencilRealization` conjuncts | `--nondeg` | 63/63 |
| **`σu` satisfies all four conjuncts** (each reported separately) | `--nondeg` | 63/63 — *genericity, not an implication: `--hunt` H2 breaks conjuncts 2 and 4 by construction* |
| **the route-σ witness is a nondegenerate pencil realization of `G`** | `--nondeg` | 63/63 |
| the witness satisfies the chart's binding point equations | `--nondeg` | 63/63 |

*(The "chart" row checks that each body's point is the common point of its
closed-hub-neighbourhood panels — a `cross₃` where that set has three members,
an orthogonality where it has fewer; it does **not** perform the `fillHub`
solve, so it is evidence for, not proof of, chart-image membership.)*

**The (K-res) residual habitat is UNSAMPLED, not tested-and-passed.** `--adv`
also probes two `W19` splits over seeds 600–619 and finds **0** valid
hard-stratum seeds (17 of 20 draws per split are rejected at the stratum test —
`W19` has `f(V) = 2`). The driver asserts that this leg stays empty, so a
successor who makes it nonempty is forced to update this section.

### Step σ4b — the obligation-1 hunt (`--hunt`, 2026-08-05), and one correction

**Pool discipline first.** `--hunt` runs on **three pools of its own**, printed
in its header and deliberately **disjoint from the pinned 63**: random
1000–1059, coplanar-chain 2000–2029 and (Λ0d) 3000–3019, *per split*, over the
same two tight-control splits. **No figure below is over the 63-seed pool and
no *Step σ4* figure is over these.** (The discipline is explicit because the
pass that opened this section first reported its "63/63" as an aggregate across
scratch drivers running *different* pools, and only its landing dispatch caught
it before the figure was recorded. Here the separation is structural: `--hunt`
never touches `CHAIN0_SEEDS`/`CHAIN1_SEEDS` and the other four modes never touch
the hunt pools.)

| leg | what it establishes | result |
|---|---|---|
| **H0** the shape's *conjunct arithmetic* | no hub–hub edge; `closedHubNbhd v = {v}` at every hub; `closedHubNbhd v ⊆ closedNbhd v` everywhere | asserted at both splits |
| **H1** the fresh random pool | 107 fresh hard-stratum seeds, all four dual conjuncts at `σu` | **0 failures** — random draws never reach the locus |
| **H2** the **constructive** failure | a legal, hard-stratum, **primally nondegenerate** placement whose dual conjuncts **2 and 4 FAIL** at `σu` (1 and 3 hold) | **53/53** (27 + 26), exact pattern `(T, F, T, F)` |
| **H3** the **steering** | on the chart line `x(τ)`, the bracket is `τ·bracket(1)` *identically* with `bracket(1) ≠ 0`; at every `τ ≠ 0` the seed is hard-stratum with primal **and** dual 4/4 | 12 lines, 60 steered points, all `n/n` |
| **H4** (Λ0d) one-sided | `pt(b) ∈ Π(c)` **is** reachable on the hard stratum at a primally nondegenerate seed: the `b`-span drops `6 → 5`, the `c`-mirror span is 6, and the failing scalar **is** dual conjunct 2 on the edge `ac` | **35/35** (18 + 17) |
| **H5** (Λ0d) both halves | forcing both is a legal pencil placement with adjacent points distinct, but `rank(pt a, pt b, pt c) = 2` and `a` has **no panel at all** — the witness for **(σ7)** | **39/39** (19 + 20) |

**The construction (H2), because it is the whole content.** In a chain
`h – x – y – h′` with `h, h′` hubs and `x, y` degree-2, `x`'s only panel
constraint is `x ∈ Π(h)` and `y`'s is `y ∈ Π(h′)`. Pick `z` on the meet line
`Π(h) ∩ Π(h′)`, put `x` on the line `h z` and `y` on the line `h′ z`: both
constraints hold and `h, x, y, h′` are **coplanar**. Coplanarity makes `x`'s
panel (the plane `h x y`) and `y`'s (the plane `x y h′`) coincide, so at `σu`
the adjacent "points" `N[x]`, `N[y]` are projectively equal. Nothing primal
notices — **the four primal conjuncts only ever look at the points.**

> **CORRECTION to *Step σ4* (F11: this pass's own predecessor).** V4's
> "`dim(β_{Π b} + β_{Π c} + α_{pt b}) = 6` at 63/63" is a **genericity**
> observation. H4 exhibits 35 hard-stratum, primally-nondegenerate
> configurations of the *same* two splits where that span is **5**. The *Step
> σ3* theorem survives — it now quotes (σ7)'s disjunction instead of the
> `b`-form side condition — but no reading of V4 as "the span is forced" is
> licensed. The same caution applies to *Step σ5* obligation 1's "observed
> 63/63": the observation was true and the implication it suggested is
> **false**.

### Step σ5 — the four obligations, stated so they can be attacked

1. **`σ`-nondegeneracy of the seed: NOT implied — and now witnessed, reduced
   to two conjuncts, and steered.** `IsNondegPencilRealization u` does **not**
   imply it at `σu`. The four conjuncts (`Motive.lean:110–115`) split three
   ways, and the split is the useful part:

   - **Conjunct 1 is SELF-DUAL as a landed theorem, not as an observation.**
     `hasPencilPanelRealization_mapExtensor_screwComplementIso`
     (`Pencil/Statement.lean:257`) says exactly that
     `HasPencilPanelRealization G F normal point` gives
     `HasPencilPanelRealization G (F.mapExtensor σ) point normal`. That *is*
     conjunct 1 at `σu`. (Verified against the landed proof, 2026-08-05: it is
     stated at `K = ℝ`, `k = 2`, and the framework it produces is
     `F.mapExtensor screwComplementIso`, which is the right one — route σ
     works with the σ-image framework throughout.) **Free — AT `ℝ` ONLY.**
     `screwComplementIso` is `ScrewSpace ℝ 2 ≃ₗ[ℝ] ScrewSpace ℝ 2`, while `hK`
     is quantified at the general `[Infinite K]` of
     `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`, so at that `K`
     there is no `σ` in tree and this bullet says nothing. See *Field scope*:
     the gap is recorded, not settled, and the reading suggests the polarity
     generalizes.
   - **Conjunct 3 is implied by the PRIMAL conjuncts whenever no two hubs are
     adjacent.** At `σu` it reads `LinearIndepOn point (closedHubNbhd v)`. At a
     hub `v` with no hub neighbour, `closedHubNbhd v = {v}`, so it is
     `point v ≠ 0` — primal conjunct 1. At a non-hub `v`,
     `closedHubNbhd v ⊆ closedNbhd v`, so it is primal conjunct 4 restricted
     (`LinearIndepOn.mono`). Asserted combinatorially on the sampled shapes by
     `--hunt` H0, and observed to hold at all 53 constructed failures.
     **Free on the no-adjacent-hubs shapes; a genuine condition otherwise.**
   - **Conjunct 2 at the split's two edges `ab`, `ac` is exactly two-sided
     (Λ0d)**, an already-named condition rather than a new one: `a`'s panel is
     the plane through `pt(a), pt(b), pt(c)`, so `N[a] ∥ N[c] ⟺ pt(b) ∈ Π(c)`
     and `N[a] ∥ N[b] ⟺ pt(c) ∈ Π(b)`. By **(σ7)** at most one half fails —
     but one half *does* fail on the hard stratum (`--hunt` H4, 35/35), so this
     is **not** free.
   - **Conjunct 2 at the remaining edges, and conjunct 4 at every non-hub, are
     the genuinely new content — and they FAIL.** `--hunt` H2 constructs
     **53** legal, target-rank, `s₀ = 0`, `dim R_a = 1`, **primally
     nondegenerate** `G′` seeds at which dual conjuncts 2 and 4 both fail at
     `σu` (the coplanar-chain degeneration, *Step σ4b*). So the 63/63
     observation was genericity; the implication is **false**, and obligation 1
     cannot be discharged by "it always happens to hold".

   Three repairs, in increasing cost, unchanged in shape but now with a
   measured verdict on each:

   (a) carry the dual conjuncts as extra hypotheses on the induction's motive.
   They are open conditions and the ℚ-witnesses certify non-vacuity — but H2
   shows the extra hypotheses genuinely **cut** the seed space, so (a) is a
   real strengthening of the motive, not a free annotation.
   (b) re-seed. **`exists_pencilSeed_of_nondeg` (`Reseed.lean:65`) is NOT the
   bridge and would be circular if used as one** — it *takes*
   `IsNondegPencilRealization` as a hypothesis, i.e. exactly obligation 1
   (coordinator-verified against the landed statement, 2026-08-05). Repairs
   (b) and (c) are therefore **not interchangeable**, which the earlier
   wording implied.
   (c) **the named repair, and now the only one with a validated mechanism** —
   the dual conjuncts are nonvanishing polynomial conditions on the pencil
   chart, so steer to a common seed where target rank *and* they hold, via the
   landed `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`).
   Its own docstring already names its intended consumer as "W5-L7's rank
   target *and* its candidate-`M₁` escape polynomial". Three things about it
   are worth recording so the eventual Lean pass does not rediscover them:

   - **There is no chart-image side condition.** `pencilChartPointPoly` /
     `pencilChartNormalPoly` (`Engine.lean:200–235`) are polynomials in a
     *free* seed `q : α × Fin 4 × Fin 4 → K` with eval identities to
     `pencilChartPoint/Normal (PencilSeed.ofCoord q)`. The chart is a **total
     parameterization**, so the theorem's hypothesis
     `hP : ∀ i, ∃ q, eval q (P i) ≠ 0` needs merely *some* seed per polynomial
     — any seed, not a nondegenerate one and not one reproducing the ℚ
     witnesses.
   - **The LI conjuncts are not literally one polynomial's nonvanishing.**
     Dual conjuncts 2/3/4 are `LinearIndependent` / `LinearIndepOn`
     conditions, i.e. "**some** maximal minor ≠ 0" — a *union* of basic opens.
     The repair only needs **sufficiency**, so fix **one specific minor per
     conjunct** whose nonvanishing implies it. That choice is graph-dependent
     and is the actual (bounded) Lean content.
   - **The steering is exhibited exactly, not sampled** (`--hunt` H3). On the
     chart line `x(τ) = (1−τ)·x_deg + τ·x_gen` inside `Π(h)`, the offending
     scalar is the bracket `[P_h, P_x(τ), P_y, P_h′]`, which is **affine in
     `τ`** (multilinear bracket, affine `hat`) and vanishes at `τ = 0`, hence
     equals `τ·bracket(1)` identically; with `bracket(1) ≠ 0` the failure locus
     meets the line in the **one** point `τ = 0`. At every `τ ≠ 0` tested the
     seed is hard-stratum with primal **and** dual conjuncts 4/4. That is
     repair (c) in exact arithmetic: one polynomial, degree 1 along the line,
     steered off while the rank is kept.

   **Net.** Obligation 1 is not vacuous and is not free, but it is **smaller
   than it looked**: two of four conjuncts are free **at `ℝ`** (one by a landed
   theorem, one by the primal conjuncts on the shapes in scope), one is a
   re-labelling of the already-named (Λ0d), and the remaining content has a
   validated steering mechanism. It remains **Lean engineering against a landed
   pattern, not new mathematics** — with **two** design decisions, not one: the
   minor-choice above, and **the field**. Discharging `hK` at `ℝ` (instantiate
   the headline first) needs no new duality work; discharging it at the general
   `K` the landed headline quantifies over needs a **general-`K` polarity**,
   which does not exist in tree. *Field scope* prices that; the choice is not
   made here.
2. **Scope.** Verified only at `s₀ = 0`, `dim R_a = 1`, both ends hubs, on the
   tight control — and the `--hunt` pools do not widen that: they are further
   configurations of the *same* two splits of the same shape, chosen
   adversarially rather than randomly. The `dim R_a = 0` stratum is
   **untouched** — `r = 0` there and
   route σ helps no more than routes A/B; §(K-flank) *F5(d)*'s five `P21`
   uniform-failure seeds sit there and remain uniform failures (`hK`'s ∃-form
   over seeds is what covers them, unchanged). The `s₀ ≥ 1` residual habitat
   ((K-res); `W19` `s₀ = 2`, `S29`) is **unsampled** — the criterion is stated
   for the hard stratum generally, but route σ has not been run there.
3. **The criterion at `σu` is IMPORTED, not re-derived.** §(K-tight) *Step
   2.4*'s criterion is applied at a different seed with its two derivation
   ingredients checked there; `repin.py`'s per-placement 80/80 biconditional was
   validated at `u`-type seeds only. No seed with `crit_A(σu)` **false** exists
   in the pool (`predAfalse = 0/63`), so the **failure direction** of (σ6) is
   **unwitnessed**.
4. **The branch route σ closes has NEVER been observed nonempty.**
   `lambda.py --adv` hunts `λ ∝ p⁺` (= `★r ∥ C(M)`) and finds none; at all 63
   seeds here routes A/B already escape at `u`. So route σ does not repair an
   observed failure; it removes the *possibility* of one, uniformly. State the
   gain as **evidence → argument**, never as *bug fixed*.

### Step σ6 — three settled negatives, so they are not re-derived

- **Involutivity is not on the critical path.** `σ² = id` holds exactly, but
  route σ applies `σ` **once**, to the seed, and never returns; the pull-back in
  *Step σ2* is exposition. In tree: `screwComplementIso`, the two forward
  predicate transports
  (`extensorInPanel_screwComplementIso_of_extensorThroughPoint` and its dual),
  the stratum self-duality
  `hasPencilPanelRealization_mapExtensor_screwComplementIso`, and
  `complementIso_toDual` / `complementIso_map_contragredient_eq`. **Every
  `screwComplementIso` entry in that list is `ℝ`-fixed** (*Field scope*; the
  `complementIso` ones are general-`K`). **Not** in
  tree: any statement that `σ` is self-adjoint, an isometry, or an involution.
  The natural route to `σ² = id` is (i) self-adjointness — immediate from
  `complementIso_toDual` (`⟨⋆X, Y⟩ = vol(X ∨ₑ Y) = vol(Y ∨ₑ X) = ⟨⋆Y, X⟩`, even
  grades commute) — then (ii) a `Module.Basis.ext` evaluation on the six-element
  exterior-power basis of `Λ²K⁴`. One focused leaf; the `rfl` closing
  `screwComplementIso_lineExtensor` is evidence the reduction computes. (This is
  the same missing lemma the phase note's *Blockers* records as off every
  critical path.)
- **A strictly σ-equivariant seed recipe is a DEAD END, and this is a proof.**
  A σ-fixed pencil configuration needs `normal_v ∝ point_v`; the landed
  incidence conjunct `point v ⬝ᵥ normal v = 0` then forces
  `point_v · point_v = 0`, so **over `ℝ` with the project's (definite) polarity
  there are no σ-fixed configurations at all**. For a general correlation the
  fixed locus is worse than empty, it is degenerate: a *symmetric* correlation
  forces every body point onto the fixed quadric and every hinge line to lie
  **on** that quadric (a union of two one-parameter rulings); a *null*
  (symplectic) correlation `J` makes the incidence automatic and forces every
  hinge line into the **linear line complex** of `J`, whence `ω_e := c_e ★S` is
  a self-stress for every cycle-space flow `c` (`S` = the complex's screw), so
  the rank drops by at least the cycle rank. Measured on `C₆` (tight,
  `5|E| = 30 = 6(|V|−1)`, cycle rank 1): **deficit exactly 1 at 6/6**
  linear-complex placements (`sigma.py --fixed`). *Route σ does not use
  equivariance* — it applies `σ` once to move to a **different** seed, which is
  exactly why it escapes this wall.
- **The `K222` self-duality hint does not connect through `σ`.** The
  octahedron's self-duality is a *graph/planar* duality; `σ` acts on
  realizations of **every** graph without any self-duality of the graph. So `σ`
  acting non-trivially is not a discriminator of the anomalous shapes, and
  §(K-pure) *P8*'s two mechanisms get nothing from this section — except the
  observation that `V_bc ∩ Λ²π̂ ≠ 0` is the σ-image of `V_bc ∩ α(·) ≠ 0` at the
  dual seed, which is worth one probe in the mechanisms pass.

### Verification

`notes/scripts/w4/sigma.py` (tracked; opened with this section, `--hunt` added
2026-08-05; exact-ℚ, stdlib-only, no
CAS; sits beside `dominance`/`outer` as a `w4/` leaf and imports only catalogued
§1 primitives from siblings; every sampled placement star-rank guarded
(`flanks.star_span_ranks`) and every span's dimension asserted; all rng seeded;
output verified byte-identical under two different `PYTHONHASHSEED` values, so
no printed collection depends on hash order). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --transport   # (σ1)–(σ6), V0–V5
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --adv         # the adversarial half
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --nondeg      # nondegeneracy at σu
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --fixed       # σ-fixed is degenerate
PYTHONHASHSEED=0 python3 notes/scripts/w4/sigma.py --hunt        # obligation 1 (~135 s)
```

The first four modes assert every counter equals the pinned seed pool and print
`OK`; the pool size `63` is itself asserted, so a sampler change that silently
moved the pool fails the run. **`--hunt` runs on its own three pools** (*Step
σ4b*), never on the 63, and asserts each of H0–H5's counters against its own
leg — including `dualfail == 0` on the random leg, so a successor who *does*
find a random failure is forced to rewrite *Step σ4b*, and `bracket(τ) =
τ·bracket(1)` exactly, so a non-affine bracket would fail the run rather than be
averaged away. Neither pool's figures are quoted over the other.

Adding `--hunt` modified a tracked driver, so the figure-invariance gate fired
in full for `sigma.py` (a `w4/` leaf: nothing imports it, so its import closure
is itself). Baselined before the edit, re-run after: `--transport`, `--adv`,
`--nondeg`, `--fixed` all **byte-identical** at `PYTHONHASHSEED=0`, and
`--hunt` byte-identical under two different hash seeds.

**Confidence verdict.**

- **(σ1)–(σ4), (σ5), (σ6), (σ7) and the *Step σ3* span computation:
  proven-informally**, each exact and each with a driver mode asserting that
  sentence. **(σ7)** in particular is a proof from the primal conjuncts, with
  `--hunt` H5 as its witness that the excluded configuration really is
  excluded by conjunct 4 and not by the sampler.
- **The σ-intertwining question, literal form: REFUTED** (*Step σ1(a)*).
  **Covariant form: confirmed.**
- **σ-equivariant seed recipes: REFUTED** (*Step σ6*), with the `C₆` witness.
- **"the dual conjuncts hold automatically at `σu`": REFUTED** (*Step σ4b* H2,
  53 constructed hard-stratum primally-nondegenerate witnesses). The 63/63 of
  *Step σ4* was genericity.
- **Route σ as a closure of (K-tight) on the hard stratum: CANDIDATE, offered
  for adjudication — and, as landed machinery, an `ℝ`-only one.** Obligation 1
  is still the single crux, now **sized**: two of its four conjuncts are free
  **at `ℝ`**, one is the already-named (Λ0d), and the steering repair is
  exhibited exactly. Obligations 2–4 bound the scope and the claim's strength.
  **No gap-map status moves.**
- **Field scope: OPEN, recorded not settled** (*Field scope*, *What would change
  this* (vi)). `σ` is `ℝ`-only in tree; `hK` is consumed at general
  `[Infinite K]`. (σ7) and the span linear algebra are field-neutral outright;
  (σ1)–(σ6) and route σ are field-neutral *modulo the polarity existing*;
  *Step σ1(a)* and *Step σ6*'s two refutations are genuine `ℝ`-mathematics and
  do **not** port.

**What would change this.** *(i)* A seed where `crit_A(σu)` is false *and* route
A at `σu` nevertheless escapes (or vice versa) refutes (σ6) and with it *Step
σ3*. *(ii)* A hard-stratum seed where `σu` violates a nondegeneracy conjunct
**and** cannot be steered to one that does not would reduce route σ to the bare
(degeneracy-permitting) statement — still useful (that is `hbareSplit`'s shape),
but no longer a closure of `hK`. Half of this is now settled: violating seeds
**exist** (H2), and on every chart line tested the steering **works** (H3); what
is open is whether the steering survives *in Lean*, i.e. whether one can name
the specific minors and discharge their `≢ 0`-somewhere certificates.
*(iii)* Running route σ at a (K-res) residual (`W19`, `S29`, `s₀ = 2`) and
finding the span drops below 6 both ways, or `dim R_a = 1` failing there, would
cut the scope to the tight class. *(iv)* **SETTLED** at every both-ends-hubs
split by **(σ7)**: both halves of (Λ0d) cannot fail at once at a primally
nondegenerate seed, so `C(M) = C(bc)` is unreachable there and no genuine
residue is left. The one-sided failure §(K-Λ) *Step 6* exhibits at θ(3,4,5)
seed 345 is now known to be reachable on the **tight control's** hard stratum
too (H4, 35/35) — harmless for *Step σ3*, load-bearing for obligation 1.
*(v)* A class shape with **two adjacent hubs**: dual conjunct 3 stops being
free there (H0's hypothesis), and obligation 1 grows back to three conditions.
*(vi)* **THE OPEN FIELD QUESTION — does the polarity generalize past `ℝ`?**
(*Field scope*, recorded 2026-08-05, deliberately not settled.) `σ` exists in
tree only at `ℝ`, `hK` is consumed at general `[Infinite K]`. If the polarity
**does** generalize — and both of `screwComplementIso`'s ingredients are already
field-general in tree, so the reading is encouraging — route σ, conjunct-1
freeness and (σ1)–(σ6) all port, and the ported statement is what obligation 1
needs. If it does **not**, route σ closes `hK` only at `ℝ`, and using it means
instantiating the landed headline at `ℝ` first — a real narrowing of a
field-general theorem, and a decision for the user, not for a research pass.
Either way *Step σ1(a)* and *Step σ6*'s refutations do **not** port: they use
`ℝ`-**definiteness**, so over a field with isotropic vectors their conclusions
are unknown — a σ-fixed pencil configuration might well exist there, which
would revive the σ-equivariant-recipe route this section buried. That is the
one place where the field question could *change a settled verdict* rather than
merely re-scope it.

## §(K-ind) — can a numerical invariant of the failure locus be carried along the generating moves? (**NO — the transport graph on the class is edgeless; the one genuine chart relation runs the wrong way and bottoms out at `k ≤ 3`**)

Answering the question `notes/Pencil-strategy.md` §4's framing correction raises
but never poses: *the induction is already the framework, so strengthen the
inductive invariant — can a **numerical** invariant of the failure locus
(equivalently of the image of `H ↦ V_bc`) be **carried along the generating
moves**?* Read against §(K-dom) (the grading), §(K-pitch) *Steps 1, 5, 6*
(path-sum containment, the bracket monomial, the refuted naive collapse),
§(K-pure) *P3* ((PC-Z)), and the **landed** induction skeleton
`Graph.pencil_reduction` (`Molecular/Induction/ForestSurgery/Reduction.lean:850`).

**Headline.**

- **No move of the phase's induction takes one class member to another.**
  Tightness pins `(|V|,|E|) = (5c+1, 6c)` in the cycle rank `c` **(I1)**; every
  arm of `pencil_reduction` strictly drops `(|V|,|E|)`; the split arm preserves
  `c` and therefore raises `index` by exactly `1` **(I2)**, leaving the tight
  locus irreversibly; and the only index-preserving arm — rigid contraction — is
  unavailable at a class member by `hnoRigid`. So the relation "reachable by one
  generating move", restricted to the `hK` habitat, is **empty**. There is
  nothing to transport *along*.
- **The one genuine chart relation the moves do give is real, new, and runs the
  wrong way.** Un-subdividing (= `splitOff`) embeds the shorter shape's chart
  into the longer shape's chart as a closed sub-locus on which `V_bc` is
  *literally the shorter shape's* `V_bc` **(I3)** — so `Image(V_bc)` is
  **monotone under subdivision**. But the induction *descends*, so the usable
  direction is the one monotonicity does **not** give, and every descending chain
  reaches `k ≤ 3`, where §(K-dom) **(D1)** proves the invariant is `≤ 4` and
  dominance is impossible. **The base case of the only available induction is a
  proven failure of the invariant.**
- **"Numerical invariant of the failure locus" is one bit.** `F` is the pullback
  of `σ₁(α(a)) ∪ σ₁(Λ²π̂)`, i.e. a **divisor**. Its only numerical invariant is
  `codim F ∈ {0,1}`, and `codim F = 1` **is** `hK` **(I0)**. Every genuinely
  numerical candidate lives on the image side, where it is `dim Image` — i.e.
  **(K-dom)**, already run and struck.
- **The class's infinitude is entirely in the hub multigraph `G°`, and no move
  touches `G°`** **(I4)**. Within one `G°` the class is a **finite antichain**.
  So even a perfect subdivision-transport theorem compresses a finite set to a
  smaller finite set and cannot reach class uniformity.

### Standing notation (on top of §(K-dom))

Split chain `b–v–a–c` at a target-rank `G′`-seed, `b, c` hubs,
`deg v = deg a = 2`; `G′ = G.splitOff v a b e₀`; `H := G − v − a = G′ − a`;
`V_bc` the relative twist system, `k` the companion length (shortest `b`–`c`
path of `H`). `index(G) := 5|E(G)| − 6(|V(G)| − 1)`; `c(G) := |E| − |V| + 1` the
cycle rank. For a class member (2EC, `hnoRigid`, `hcard`), (R4) makes `G` a
subdivision of its **hub multigraph** `G°` (vertices = hubs, edges = branches);
`ℓ_P` are the branch lengths, `m := |E°|`, `n := |V°|`, `c° = m − n + 1 = c(G)`.
`Chart(G)` = the nondegenerate pencil chart (`IsNondegPencilRealization`,
`Molecule/Pencil/Motive.lean:110-115`), `F(G) ⊆ Chart` the failure locus.

### Step I0 — the failure locus has no numerical content beyond `hK`

By (PC-Z) (§(K-pure) *P3*) the escape fails at a seed exactly when `V_bc` meets
`α(a)` or `Λ²π̂`. "Meets a fixed 3-space" is the Schubert condition `σ₁` on
`Gr(3,6)`, which **is the hyperplane class** of the Plücker embedding
(classical); so each condition is a single hyperplane section, and

> `F(G) = Φ^{-1}(σ₁(α(a))) ∪ Φ^{-1}(σ₁(Λ²π̂))` = `{Q₁ Q₂ = 0}`,  `Φ := (H ↦ V_bc)`,

the zero divisor of **one** polynomial `Q = Q₁Q₂` on the irreducible chart. Two
consequences, both worth stating because they bound the whole question:

1. **`F` is a divisor or everything.** `codim F ∈ {0, 1}`, with `0` iff `Q₁ ≡ 0`
   or `Q₂ ≡ 0`. So *every* numerical invariant of `F` — dimension, degree of its
   components, multiplicity, Hilbert polynomial — is either constant on the class
   for trivial reasons or is a re-encoding of the single bit `Q ≢ 0`. **Carrying
   a numerical invariant of `F` inductively is carrying `hK` inductively.** The
   question as literally posed is circular, and its own parenthetical ("or
   equivalently of the image") is the only non-circular reading.
2. **On the image side the only transportable number is `dim Image Φ`.**
   `deg Image Φ` is not monotone under any containment and is unavailable
   without a description of the image (`Pencil-strategy.md` §2.4's open
   problem); `dim Image Φ = 9` is exactly **(K-dom)**.

> **Four objects, kept apart** (coordinator scrutiny, 2026-08-05; the arc's prose
> had been conflating them). **(1)** `V_bc(p)` is a **point** of `Gr(3,6)`, not a
> locus. **(2)** The graph-dependent object is the **map**
> `φ_G : chart(G) → Gr(3,6)` and its **image** — the thing `Pencil-strategy.md`
> §2.4 says we have no description of. **(3)** The bad locus `B ⊆ Gr(3,6)` is the
> union of the two Schubert divisors `σ₁(α(a))`, `σ₁(Λ²π̂)`, each the
> **hyperplane class** in the Plücker embedding, so `B` is cut by a *single
> degree-2 form that factors into two hyperplanes*, and — the point that is easy
> to miss — `B` is **graph-independent** (§(K-dom) *D0*: it depends only on
> `pt(a)` and `plane(a,b,c)`). **(4)** `F = φ_G^{-1}(B) ⊆ chart(G)` is a
> hypersurface exactly when `hK` holds there, and the whole chart when it fails.
>
> **The connection the workbook did not make.** That global factorization is
> precisely the shadow of §(K-Λ) **(Λ1)**'s local result — `Φ_loc` is always
> rank 2, a product of two distinct rational linear forms, *"the local quadric is
> a pair of rational hyperplanes"*. **The two computations are the same geometry
> at two scales**: a degree-2 form on `Gr(3,6)` cutting `B`, and the degree-2
> form on the far covector cutting the local bad locus, both factoring into two
> hyperplanes for the same reason — the two isotropic completions of (PC-Z).
>
> Orientation, not used: `deg Gr(3,6) = 42` in the Plücker embedding (the
> classical hook-length count). **Flagged UNVERIFIED, do not assert it:** whether
> the discriminant hypersurface `{det Gram_B = 0} ⊆ Gr(3,6)` — the locus §(K-dom)
> *D1* puts every `k = 3` habitat into — has class `2σ₁`. Nothing in the arc
> depends on it.

### Step I1 — (I1): a tight graph's size is a function of its cycle rank

> **(I1)** *(proven; two lines)* For any finite graph, `index(G) = 0` (tight) is
> equivalent to `|E(G)| = 6c(G)` **and** `|V(G)| = 5c(G) + 1`.

*Proof.* `c = |E| − |V| + 1` gives `|V| = |E| − c + 1`; substituting into
`5|E| = 6(|V| − 1)` gives `5|E| = 6(|E| − c)`, i.e. `|E| = 6c`, and then
`|V| = 6c − c + 1 = 5c + 1`. ∎

This is the equality case of the dictionary's **(R2)** size bound `|V| ≤ 5c + 1`,
and for a subdivision it is the recorded tightness budget `Σ_P ℓ_P = 6c°`
(§(K-pitch) *Step 6*, `index(G) = 6c° − Σℓ_P`) in disguise: `|E| = Σℓ_P`.

*Cross-check against the recorded habitats* (all six agree; re-derived
independently by the coordinator, 2026-08-05):

| habitat | `G°` | `c` | `Σℓ = |E|` | `|V|` | `6c` / `5c+1` |
|---|---|---|---|---|---|
| θ(3,4,5) | theta | 2 | 12 | 11 | 12 / 11 |
| θ(3,3,6) | theta | 2 | 12 | 11 | 12 / 11 |
| NT16k5 | 4 hubs, 6 branches | 3 | 18 | 16 | 18 / 16 |
| `K4` dbl-subdiv | `K4` | 3 | 18 | 16 | 18 / 16 |
| NT21 | 4 hubs, 7 branches | 4 | 24 | 21 | 24 / 21 |
| `K5−M` dbl-subdiv | `K5−M` | 4 | 24 | 21 | 24 / 21 |

(`P21`, `Σℓ = 24`, `|V| = 21`, `c = 4` also fits; the W4 test shapes `W19`/`S29`
have `f(V) = 2 ≠ 0` and correctly do **not** — they are not tight.)

**Immediate corollary, used throughout.** Two tight graphs of the same cycle rank
have **the same** `|V|` and `|E|`. Since every arm of `pencil_reduction` hands
its IH only graphs with `|V′| < |V|` (the loop arm being the sole
`|V|`-preserving one, and class members are `Simple`), **no arm can relate two
tight graphs of equal cycle rank at all** — before any geometry is considered.

### Step I2 — (I2): the split move raises `index` by exactly 1, and fixes `G°`

Read off the landed definition **body**, not its docstring (`Graph.splitOff`,
`Molecular/Induction/Operations.lean:769`): `splitOff v a b e₀` has
`V(G) ∖ {v}` and carries every `G`-edge avoiding `v`, plus one fresh edge `e₀`
joining `a, b`. At `deg v = 2` with distinct non-loop edges `eₐ, e_b` that is
`|V| − 1` vertices and `|E| − 1` edges; **the inverse move is exactly edge
subdivision**.

> **(I2)** *(proven)* For `deg_G v = 2`:
> `index(G.splitOff v a b e₀) = index(G) + 1`, `c(G.splitOff v a b e₀) = c(G)`,
> and the hub set, the hub multigraph `G°`, and every branch length except the
> one containing `v` are unchanged (that one drops by 1).

*Proof.* `5(|E|−1) − 6(|V|−2) = [5|E| − 6(|V|−1)] + 1`; `c = |E|−|V|+1`, both
drop by 1. `splitOff` changes no vertex's degree except deleting `v` (`a` trades
`eₐ` for `e₀`, `b` trades `e_b` for `e₀`), so `{deg ≥ 3}` — the hub set — is
untouched, and the branch through `v` merely loses one interior vertex. ∎
(Checked numerically at NT21: `index 0 → 1`, `c` preserved.)

Consequences, in the descending direction the induction actually runs:

- **The tight locus is left irreversibly by splitting.** `index` strictly
  increases at every step, so a class member (`index = 0`) is the **top** of its
  chain and no class member sits below another.
- **`G°` and `c` are constant along a split-descent**, which shortens branches
  and terminates at `G°` itself (all branches length 1) at `index = 6c° − m`.
- **The descent is short.** By (R3) every cycle of length `≤ 6` is rigid, so a
  class member has girth `≥ 7`; each split drops by 1 the length of every cycle
  through the shortened branch, so after at most `girth − 6` splits on one cycle
  a rigid `C_{≤6}` appears and `hnoRigid` fails — the descent switches to the
  **contraction** arm. (`K4` double subdivision: girth 9, so at most **3** split
  steps.)

### Step I3 — (I3): the subdivision-monotonicity lemma (the genuine positive)

> **(I3)** *(proven-informally; **not** driver-tested)* Let `H̃` be `H` with edge
> `xy` subdivided by a new degree-2 body `u`, terminals `b, c` unchanged. Then
> the locus `Z := {pt(u) ∈ line(pt x, pt y) ∖ {pt x, pt y}} ⊆ Chart_full(H̃)` is a
> nonempty closed sub-locus on which `mot(H̃)|_{V(H)} = mot(H)` **exactly**,
> hence `V_bc(H̃)|_Z = V_bc(H)`. Consequently
> `Image(V_bc(H)) ⊆ closure(Image(V_bc(H̃)))`, and
> `dim Image(V_bc(H̃)) ≥ dim Image(V_bc(H))`.

*Proof.* Write `pt u = λ pt x + μ pt y`, `λμ ≠ 0`. Then
`C(xu) = pt x ∧ pt u = μ·(pt x ∧ pt y)` and `C(uy) = λ·(pt x ∧ pt y)`, both
`∝ C(xy)`. A body-hinge motion satisfies `m(p) − m(q) ∈ ⟨C(pq)⟩` per hinge, so on
`Z` the two hinges at `u` give `m(x) − m(y) = (ω₁μ + ω₂λ)C(xy)` — precisely
`H`'s constraint at `xy` — and conversely any `H`-motion extends by
`m(u) := m(x) − ω₁μ C(xy)`. Every other edge is shared. So the restriction map
`mot(H̃) → mot(H)` is onto with the `m(u)`-fibre, and `V_bc` agrees. `Z` is in
the pencil stratum: `u` has degree 2 so it is not a hub and carries no panel
condition; at a hub endpoint (say `x`) the hinge `C(xu) ∝ C(xy)` already lies in
`Π(x)` provided `pt y ∈ Π(x)`, one further equation on `Chart(H̃)`, satisfiable
because two planes always meet in a line. Finally `Chart_full(H̃)` is irreducible
(§(K-slide) *Step 1(e)*: a tower of affine-linear fibres) and the nondegenerate
locus is dense open in it, so `Z ⊆ closure(nondeg)`; `V_bc` is regular near any
point where `dim V_bc` attains its generic value 3 (upper semicontinuity), and
`Φ(closure(U)) ⊆ closure(Φ(U))` for a regular `Φ`. ∎

**Why this does not contradict §(K-pitch) *Step 6(a)*.** That step refutes the
naive collinear collapse as a chart move, and its refutation is *simultaneous*:
"making chords panel-resident **along every `G°`-edge** forces each closed hub
star coplanar", impossible when the chords at a hub span 3-space. (I3) makes
exactly **one** edge's endpoints panel-resident, and only when an endpoint is a
hub — for an edge interior to a branch there is no panel condition at all and `Z`
is unconstrained. *One edge vs every edge* is the whole difference, and it is
worth recording because Step 6(a) reads, at a glance, as if it forbade (I3) too.

**And it is consistent with (D2).** Subdividing a **far** edge leaves `k` fixed
and (D2) caps the far block at `3(k−3)`; (I3) only claims `≥`, so the added
parameters may (and by (D2), beyond the budget must) land in `ker dV`.
Subdividing a **companion** edge raises `k` by 1 and raises the (D1) cap. No
tension.

### Step I4 — (I4): the class is a finite antichain inside each `G°`

By (I2) the split move fixes `G°`. By (I1) every class member over `G°` has
`Σ_P ℓ_P = |E| = 6c°` — a **fixed** total. Hence:

> **(I4)** *(proven)* The class members over a fixed hub multigraph `G°` are the
> length vectors `(ℓ_P)_{P ∈ E°}` with `ℓ_P ≥ 1`, `Σℓ_P = 6c°`, satisfying
> `hnoRigid` (every branch-union cycle has length `≥ 7`) and `hcard`. This set is
> **finite**, and it is an **antichain** for the componentwise (refinement)
> order, since all its members have the same coordinate sum.

The arc already computes with exactly this set without naming it: §(K-flank)
*F3*'s `210 = C(10,4)` all-`{3,4}` `K5` shapes (`Σℓ = 36 = 6·6`), the `155`
6v11e shapes, and §(K-slide-comb)'s **877 exhaustive `K4` shapes**
(`Σℓ = 18 = 6·3`) are enumerations of (I4)'s level set for one `G°` each.

**This is the decisive deflation of (I3), and it is independent of any geometry.**
An invariant transported by (I3) can only compare a class member to shapes with
*strictly smaller* `Σℓ` — i.e. to non-class shapes. Two class members over the
same `G°` are incomparable, so (I3) transports **nothing** between them. And the
infinitude of the class is entirely in the `G°` direction (`c° → ∞`), which by
(I2) no split move reaches. *The subdivision order compresses a finite set into a
smaller finite set, and the moves never cross between finite sets.*

### Step I5 — the three cheap kill-checks, answered

**(1) The `Pencil-strategy.md` §2.5 saturation trap — evaded in form, re-entered
in substance.** `dim Image Φ` is a Jacobian rank, not a count, so §2.5's blanket
ruling does not literally apply. But the split is the familiar §2.3 asymmetry:
the **upper** bound `dim Image ≤ min(9, 6k−14)` is (D1), a pure count, *proven*;
the **lower** bound `dim Image = 9` is the open per-shape determinantal
condition. Worse, the count-predicted value and the measured value coincide at
all seven §(K-dom) habitats (`4,4,9,9,9,9,9` against `min(9,6k−14)`), so the
count is **saturated as a predictor and useless as a certificate**.

**(2) The companion-length grading — the move changes `k`, in the fatal
direction.** A split on a branch carrying a shortest `b`–`c` path lowers `k` by
1. Since the induction **descends**, the move it performs *lowers* `k`, hence
*lowers* the (D1) cap. Any dimension-carrying argument would need
`dim Image(G) ≥ dim Image(G′)`, i.e. the `≤` direction of (I3), false in general
and provably false at the `k: 4 → 3` step (`9` down to `4`). At that step the
map's *type* changes: at `k ≥ 4` `V_bc = ker Λ ∩ S_P` with far data entering only
through `Λ` ((T5)); at `k = 3` `V_bc = S_P` is forced, `rank B|_{V_bc} = 2`, and
`V_bc` lies in the discriminant hypersurface of `Gr(3,6)`.

**(3) Does the move preserve the class? No, and (I2) says by how much.** `index`
rises by exactly 1 per split, so the successor is never tight; and by (R3) the
descent hits a rigid `C_{≤6}` after at most `girth − 6` splits, so `hnoRigid`
fails too. The `k = 3` boundary is *exactly* where the split chain plus its
shortest companion closes a rigid `C₆` — which is **(D3)** — so the descent from
the class lands on the **(K-res)** family precisely when `k` reaches 3. That
gives a structural reading of a packaging decision the phase made on other
grounds: the 2026-08-02 route-3(b) adjudication had to carry (K-res) as a
byte-identical `hK` sibling because **(K-res) is the boundary of the class under
the induction's own move**, not merely a residual with the same `dim R_a`.

### Step I6 — the contraction arm has no chart morphism (why C2 inherits the same wall)

`hcontract` is the only arm that can *lower* `index` and hence the only one that
can return to the tight locus. It is unavailable at a class member (`hnoRigid`),
but any *strengthened motive* `P := PencilPair ∧ Inv` must re-establish `Inv`
there. It cannot be done by transport:

> A pencil realization of `G` does **not** induce one of `G/H₀`. Contracting `H₀`
> merges its bodies into one, whose hinges are the `G`-hinges leaving `H₀` —
> sitting at *different* points of `H₀` with *different* panels. For the
> contracted body to be a **pencil** body they must all become concurrent and
> coplanar, a positive-codimension condition on `Chart(G)` that a general
> realization does not satisfy. In the other direction a `G/H₀`-realization does
> not determine the internal geometry of `H₀`.

So the contraction move relates the two charts by **no** morphism in either
direction. This is the structural half of `notes/Pencil-strategy.md` §4-C2's
first bullet: the obstruction is not only that the conjunct would quantify over
subgraphs — it is that the arm which would have to re-establish it has no map to
pull it back along.

### Verification

**No numerics this pass.** (I0)'s Schubert/hyperplane identification is classical
(per the project's "classical" convention); (I1)–(I4), (I3)'s proof and *Step I6*
are derived arguments and carry no driver — a successor should attack them rather
than assume them. What *is* checked against landed source:

- `Graph.pencil_reduction` (`Reduction.lean:850`) — five arms
  (`hloop`/`hbase`/`hcut`/`hcontract`/`hsplit`), the lexicographic `(|V|,|E|)`
  measure, and each non-loop arm handed the IH only at strictly `|V|`-smaller
  graphs.
- **Correction to the record** (coordinator-confirmed, 2026-08-05): the pencil
  side does **not** run KT Theorem 4.9 (`Graph.minimal_kdof_reduction`,
  `Reduction.lean:673`). `pencil_conjecture_of_arms_pair` (`Pair2.lean:1222`)
  instantiates **`Graph.pencil_reduction`** at `P := PencilPair K 3` — five arms,
  no minimality, each arm handed an *arbitrary* smaller graph — and **`hK` enters
  only through `pencilPair_of_splitOff_of_habitat` (`Escape.lean:334`), i.e. only
  in the split arm**. Every statement above is against `pencil_reduction`;
  (I1)/(I2) hold verbatim for `minimal_kdof_reduction` too, since its two moves
  are the same `splitOff` and `rigidContract`.
- `Graph.splitOff` body (`Operations.lean:769`): `V(G) ∖ {v}` plus the fresh
  `a`–`b` edge `e₀`; the definition does **not** require `ab ∉ E(G)` (a split can
  create a parallel pair; irrelevant to (I1)/(I2), which are pure counts).
- `IsNondegPencilRealization` (`Motive.lean:110-115`): conjunct 4 is
  `∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v)`. At a
  degree-2 body that is exactly "`pt v`, `pt x`, `pt y` not collinear" — so
  (I3)'s locus `Z` is precisely the conjunct-4 boundary, in the *closure* of the
  nondegenerate chart but not in it. (I3) is stated with that closure,
  deliberately.
- (I1)'s arithmetic against θ(3,4,5), θ(3,3,6), NT16k5, `K4` dbl-subdiv, NT21,
  `K5−M` dbl-subdiv, `P21` — 7/7 — and correctly *failing* at `W19`/`S29`.

**Confidence verdict: the negative is proven-informally** (I0–I2, I4 are counting
and definition-chasing against landed Lean; I5's `k`-drop is (D3) restated).
**The positive by-product (I3) is proven-informally but NOT driver-tested.**

**What would change this.** *(i)* A generating move, not on `pencil_reduction`'s
list, relating two class members — this would require changing the induction
skeleton. *(ii)* A class habitat whose un-subdivision chain stays at `k ≥ 4` all
the way to a shape where dominance is provable; (I4) shows this cannot happen
inside one `G°`, but a proof that some `k ≥ 4` shape is dominant *for a
structural reason* would revive (I3). *(iii)* An error in (I1)'s arithmetic — it
is four lines and cross-checked against seven recorded habitats.

**The one honest well-posed computation this pass identifies, NOT run.** (I3)
predicts a *containment*, hence a falsifiable inequality: take `H₄` := two
`b`–`c` paths of lengths 4 and 4, and `H₅` := lengths 4 and 5 (the `H` of
θ(3,4,5), where `dominance.py --jac` already measures rank 9 in the FIXED
scoping). (I3) asserts `rank dV(H₄) ≤ rank dV(H₅) = 9`, with the sharp
prediction `rank dV(H₄) = 9`; plus `V_bc` on the collinear locus `Z` of `H₅`
equalling `V_bc(H₄)` entry by entry, and `dim V_bc = 3` preserved on `Z`. Cost:
one new mode on `dominance.py`. It confirms (I3) but cannot revive the route,
because (I4) already shows the transport has no class-level consumer — worth
landing only if a successor wants (I3) as a standalone lemma, or wants the
**short-shape-first** disproof search it suggests (a class habitat with
`dim Image < 9` would force `dim Image < 9` at *every* un-subdivision of it, so
an adversarial (K-dom) counterexample hunt should search short shapes and lift).

## §(K-Δ) — the Δ-matroid / orthogonal-matroid literature: **NO HIT, with the reason** (and the two readings it does buy)

Discharges `notes/Pencil-strategy.md` §7's single recorded unverified lead —
*does the Δ-matroid / orthogonal-matroid literature (Bouchet and successors)
contain anything bearing on the phase's structural obstruction: combinatorics
that can see a quadric?* Verdict on the dispatch's own bar (a specific theorem,
not a thematic resemblance):

> **NO HIT.** The literature is real, is exactly about "combinatorics that sees a
> quadric", and the *shape* of statement the phase wants genuinely exists in it.
> **Two of its three standing hypotheses fail on the phase's object, and each
> failure is independently fatal.**

- **(M1) The subject's objects are *totally isotropic* subspaces; `V_bc` is
  not one.** A representable orthogonal matroid **is** a maximal isotropic
  subspace of a `2n`-dimensional quadratic space (Jin–Kim, *Orthogonal matroids
  over tracts*, Example 3.29: over a field of char ≠ 2, "a strong or weak
  orthogonal `K`-matroid is the same thing as a maximal isotropic subspace of
  `K²ⁿ` in the usual sense"). `V_bc ⊆ Λ²K⁴ ≅ K⁶` is 3-dimensional — the right
  dimension for `n = 3` — but the Klein Gram on `V_bc` is measured to have
  **rank 3** at all 16 flank splits (§(K-flank) *F5(c)*) and **rank 2** at every
  serial length-3 companion (§(K-pitch) *Step 5*). Never 0. So `V_bc` is not a
  point of `OG(3,6)`, has no Wick/spinor coordinate vector, and carries **no
  Δ-matroid**. Isotropy is an `O(6)`-invariant of `V_bc`, not a choice of frame,
  so this is not a normalisation that can be fixed.
- **(M3) The ground set is `[n] = [3]`, fixed by `dim Λ²K⁴ = 6` — it never grows
  with the graph.** Even granting M1, the Δ-matroid of a maximal isotropic in
  `K⁶` lives on a 3-element ground set: its whole content is which of `2³ = 8`
  subsets are feasible. Nothing for a min-max to count, no subset-indexed family
  over `E(G)`. **This is `Pencil-strategy.md` §2.2's ingredient-2 failure
  restated in the target literature's own terms**, and it is the more damaging of
  the two, because it would survive any repair of M1.
- **(M2 — a *pass*, recorded so the verdict is honest.)** The *form* of the
  phase's condition matches the literature exactly. Under (PC-Z) the crux is
  `V_bc ∩ α(a) = 0` **and** `V_bc ∩ β(π_a) = 0` — transversality to two fixed
  maximal isotropic 3-spaces. In the Δ-matroid dictionary, transversality of a
  maximal isotropic to a *coordinate* maximal isotropic is precisely
  non-vanishing of the corresponding Wick coordinate, i.e. membership of the
  corresponding subset in the Δ-matroid (Rincón: `w_{[n]∖S} = ±Pf(A_{S△J})`).
  And the two forbidden spaces are *compatible* with one hyperbolic frame:
  `α(a)` and `β(π_a)` meet in `T` (dim 2), so they sit in opposite families —
  exactly the relation between two coordinate isotropics with `|J △ J'| = 1`.
  **So if `V_bc` were isotropic, (W4) would literally be "two prescribed Wick
  coordinates are nonzero".** The shape fits; the hypothesis does not.

### The dictionary, stated so a successor need not re-derive it

- **Δ-matroid** `(V, F)`, `F ⊆ 2^V` nonempty, with the **symmetric exchange
  axiom**: for all `F₁, F₂ ∈ F` and `x ∈ F₁ △ F₂` there is `y ∈ F₁ △ F₂` with
  `F₁ △ {x,y} ∈ F`. A Δ-matroid whose feasible sets are equicardinal is exactly a
  matroid. Introduced by **Bouchet** (1987) as *symmetric matroids*;
  independently, from distance geometry, by **Dress–Havel** (1986) as *metroids*.
- **Linear / representable Δ-matroid.** `A` skew-symmetric with rows and columns
  indexed by `V`; `S ∈ F` iff the **principal** submatrix `A[S]` is nonsingular.
  (General linear Δ-matroids are *twists* `F △ S` of these.)
- **The geometry.** Row-reduce a maximal isotropic `U ⊆ K^{2n}` to `[I | A]`;
  `U` isotropic ⟺ `A` skew-symmetric. Wick (= spinor) coordinates
  `w_{[n]∖S} = Pf(A_S)`; the pure spinors are cut out by the quadratic **Wick
  relations**, generalising Plücker. `supp(w)` is an even Δ-matroid. **Even
  Δ-matroids = orthogonal matroids = Coxeter matroids of type `D_n`**;
  symplectic matroids are `B_n`/`C_n`; ordinary matroids are `A_n`.

**What the subject supplies is ingredient 3, not ingredient 2.** Against
`Pencil-strategy.md` §2.1: the irreducible parameter space is the spinor variety;
min-max theorems exist in quantity (Geelen–Iwata–Murota's linear Δ-matroid
parity, Bouchet–Cunningham's jump systems / bisubmodular polyhedra,
Koana–Wahlström's union and delta-sum); the subset-indexed family
`S ↦ Pf(A_S)` exists but on the **ambient** index `[n]`, never on the graph.

> **The missing ingredient is not "a min-max theorem for quadric conditions" —
> that exists. It is the ground set.** The literature manufactures exchange and
> min-max *for a ground set it is handed*; nothing in it manufactures a
> graph-indexed ground set carrying the Klein condition.

A second, structural way to say the same thing: Coxeter-matroid combinatorics
attaches to a point of `G/P`, a flag variety **of the smaller group**. `Gr(3,6)`
is a flag variety of `GL₆`, not of `SO₆`, and `SO₆` does not act transitively on
it (Witt: the orbits are exactly the strata `rank Q|_V ∈ {0,1,2,3}`). So a
non-isotropic 3-space sits in a space that is **not homogeneous** for the group
preserving `Q`, and its `O(6)`-invariant is a single integer — here `3` (or `2`
on serial chains), already recorded by the workbook and carrying no information
about *which* isotropics it meets. **There is no Coxeter-matroid combinatorics
for it, and the reason is a theorem (Witt), not a gap in the literature.**

### The one honest near-miss — Dress–Havel metroids, and (N1)/(N2)

Reported as a near-miss and priced as new mathematics, not a literature lookup.
Dress–Havel 1986: `V` a metric vector space with bilinear form `B`, `E` a finite
set of vectors, the **discriminant** `d_B(F) := det((B(f,g))_{f,g ∈ F})`, and
`J := { F ⊆ E : d_B(F) ≠ 0 }` — a matroid when `B` is anisotropic, and in general
a **metroid** (Bouchet–Dress–Havel 1992: metroids are a special class of
Δ-matroids).

Instantiate on the phase's data: `V = Λ²K⁴`, `B` = the Klein form, `E` = a set of
hinge/companion lines. The Gram entries are *literally* the workbook's four-point
brackets, by its own pairing dictionary (§(K-Λ) *Standing notation*):
`B(C(uv), C(pq)) = [u,v,p,q]`. Every diagonal entry is `0`, because a line is
Klein-null. And at `ℓ = 3` the escape criterion translates exactly. With
`C₁ = C(bx)`, `C₂ = C(xy)`, `C₃ = C(yc)`, `C_ab = C(ab)`, `C_ac = C(ac)`, the
landed closed form (§(K-pitch) *Step 5*) is
`Q(z) = 2·[x,y,a,b]·[b,x,a,c]·[y,c,a,b]·[x,y,a,c]·[b,x,y,c]`, and term by term

```
[x,y,a,b] = B(C₂, C_ab)   [b,x,a,c] = B(C₁, C_ac)   [y,c,a,b] = B(C₃, C_ab)
[x,y,a,c] = B(C₂, C_ac)   [b,x,y,c] = B(C₁, C₃)
```

Since the diagonal vanishes, `d_B({u,v}) = −B(u,v)²`, so each factor is nonzero
**iff** that pair is feasible in the metroid of `E`.

- **(N1)** At `ℓ = 3`, `Q(z) ≠ 0` ⟺ **five prescribed 2-element subsets are all
  feasible** in the Dress–Havel metroid of `{C₁, C₂, C₃, C_ab, C_ac}` under the
  Klein form — a bona fide Δ-matroid-language form of the escape criterion.
- **(N2)** *(verified by the coordinator against the landed `ℓ = 3` closed form,
  2026-08-05)* The five pairs are exactly the five **diagonals of a pentagon**.
  Taking the closed chain `b–x–y–c–a–b` as a pentagon, the structurally-zero Gram
  entries are its five **sides** — `C₁C₂` (meet at `pt(x)`), `C₂C₃` (at `pt(y)`),
  `C₃C_ac` (at `pt(c)`), `C_ac C_ab` (at `pt(a)`), `C_ab C₁` (at `pt(b)`) — and
  the five brackets of `Q(z)` are, up to sign, its five **diagonals**. So
  **`Q(z) ≠ 0` ⟺ no two non-consecutive edges of the pentagon meet.** That is a
  third, purely incidence-geometric reading of the five brackets, beside
  §(K-pitch) *Step 5*'s monomial and §(K-Λ) *Step 1(i)*'s
  `S ∩ α_a = S ∩ β_{π_a} = 0`, and it explains cleanly why `ℓ = 3` is the easy
  case: there `V_bc = S_P` exactly ((D1)'s proof), so the condition is a pure
  incidence condition on the frame; at `ℓ ≥ 4` the annihilator `λ` enters and it
  stops being one.

**Why this is still a MISS, flatly.** *(a)* The ground set does not grow with the
graph: `E` has 5 elements, and more generally path-sum containment gives
`V_bc ⊆ S_P` with `dim S_P = k`, so the whole crux lives inside a configuration
of size `k + 2` — bounded by the **companion length**, the same cap as (D2),
reached from a different direction. Ingredient 2 is *not* restored. *(b)*
Feasibility is **per-placement** — the metroid is the metroid of a
*configuration*, exactly the per-seed object §(K-pure) *P5* names as the wall.
*(c)* The literature's theorems point the wrong way: greedy, parity min-max,
intersection, union all take a Δ-matroid **as input** and optimise over its
feasible sets, whereas the phase asks whether a *prescribed* set stays feasible
across a *family* of configurations. *(d)* The transfer trap: even the metroid of
the *ambient* line configuration would be an ambient object, and §(K-pure) *P6*'s
`P21` witness is the standing warning that ambient hypotheses do not descend to
the decoration variety.

**The ceiling was real and would have bound.** Even a full HIT could not have
reached **(K-chord)**, which is a question inside the generic 3-dimensional
rigidity matroid `R_3` — a type-`A` object with no quadratic form in sight, and
with no combinatorial characterisation. A HIT would at best have addressed the
pitch side and left (K-chord) where the *State of (K)* map leaves it.

**Cross-check against the prior NO HIT.** The 2026-07-30 rigidity-side hunt
(White–Whiteley, Whiteley, Schulze–Tanigawa, Garamvölgyi — all MISSes) and this
one fail for **complementary** reasons: those authors work with **rank**
conditions, so the Klein quadric is invisible to them by construction (§(K-pure)
*P5*); these authors work with the **quadric** but only for objects *on* it, on a
ground set fixed by the ambient dimension. Between them they bracket the phase's
object: a subspace *off* the quadric, in a space the quadric's group does not act
transitively on, indexed by a graph neither subject indexes. §2.2's diagnosis is
confirmed from the outside.

**One pointer offered as possibly better-targeted literature and explicitly NOT
verified in detail:** `V_bc` is a **three-system of screws**, and the classical
screw-theory literature (Ball's theory of screws; Hunt's and Gibson–Hunt's
classification of screw systems) studies exactly the `O(6)`-geometry of such
systems, including the quadric attached to a three-system. It is geometric rather
than combinatorial and would not supply ingredient 2 either, but it is where the
`Gr(3,6)`-with-a-Klein-form object is a *named classical object* rather than an
ad-hoc one. **Anyone pursuing it must verify every citation from scratch.**

**Confidence verdict: NO HIT — proven-informally as a literature verdict** (M1
and M3 are each checked against a primary source and each independently fatal).
**(N1)/(N2) are derivations, (N2) coordinator-verified against the landed closed
form, neither driver-tested.** They change no gap's status.

**What would change this.** *(i)* A construction making the phase's object
**totally isotropic** — the only canonical isotropics in sight are `α(a)`,
`β(π_a)`, `T` and the hinge lines, none of which is `V_bc`. *(ii)* A
**graph-indexed** ground set carrying the Klein condition — the metroid above is
the only candidate found, and its ground set is capped by the companion length.
*(iii)* A theorem converting "prescribed feasibility across a family of
configurations" into a matroid-theoretic statement about one member; not found,
and the literature's theorems run the other way.

### Sources (every entry verified this pass; verification route noted)

No section numbers are asserted except where quoted from a document actually
read. **Two hallucinated attributions were caught and corrected mid-recon and are
recorded here so they are not re-introduced.**

**Founding Δ-matroid / metroid line.** A. Bouchet, *Greedy algorithm and
symmetric matroids*, Math. Programming **38** (1987) 147–159, DOI
`10.1007/BF02604639` (Springer metadata). — A. W. M. Dress, T. F. Havel, *Some
combinatorial properties of discriminants in metric vector spaces*, Adv. Math.
**62** (1986) 285–312, DOI `10.1016/0001-8708(86)90104-0` (Semantic Scholar
record incl. abstract; Havel's own publication list). — A. Bouchet, A. Dress,
T. Havel, *Δ-matroids and metroids*, Adv. Math. **91** (1992) 136–142, DOI
`10.1016/0001-8708(92)90013-B` (Crossref). — A. Bouchet, *Representability of
Δ-matroids*, in Combinatorics (Eger, 1987), Colloq. Math. Soc. János Bolyai
**52**, North-Holland 1988, 167–182. — A. Bouchet, *Maps and Δ-matroids*,
Discrete Math. **78** (1989) 59–71, DOI `10.1016/0012-365X(89)90161-1`. —
W. Wenzel, *Pfaffian forms and Δ-matroids*, Discrete Math. **115** (1993)
253–266, DOI `10.1016/0012-365X(93)90494-E`.

**Coxeter-matroid framework.** I. M. Gelfand, V. V. Serganova, *Combinatorial
geometries and torus strata on homogeneous compact manifolds*, Russian Math.
Surveys **42** (1987) 133–168, DOI `10.1070/RM1987v042n02ABEH001308`. —
A. V. Borovik, I. M. Gelfand, N. White, *Coxeter Matroids*, Progress in
Mathematics **216**, Birkhäuser 2003, xxii+264 pp., ISBN 0-8176-3764-8, DOI
`10.1007/978-1-4612-2066-4`. — Borovik–Gelfand–White, *Symplectic matroids*,
J. Algebraic Combin. **8** (1998) 235–252. — **A. Vince, N. White**, *Orthogonal
matroids*, J. Algebraic Combin. **13** (2001) 295–315, DOI
`10.1023/A:1011212331779` — *a plausible-looking attribution of this paper to
Borovik–Gelfand–White (or to a "Booth–Borovik–Gelfand–Stone") was checked and is
**wrong**.* — **A. Vince** (single author), *The greedy algorithm and Coxeter
matroids*, J. Algebraic Combin. **11** (2000) 155–178, DOI
`10.1023/A:1008780132748`.

**Isotropic subspaces ↔ Δ-matroids (the load-bearing dictionary).** F. Rincón
(**sole author** — a WebFetch summariser reporting "Rincón, Vinzant, Williams" was
a hallucination, contradicted by the publisher record and the PDF header),
*Isotropical linear spaces and valuated Delta-matroids*, J. Combin. Theory Ser. A
**119** (2012) 14–32, DOI `10.1016/j.jcta.2011.08.001`; extended abstract FPSAC
2011, DMTCS proc. **AO** (2011) 801–812, DOI `10.46298/dmtcs.2954`. — T. Jin,
D. Kim, *Orthogonal matroids over tracts*, Forum of Mathematics Sigma **13**
(2025) e130, arXiv:2303.05353 — **PDF read directly**; the quoted Example 3.29,
the `OG(n,2n)`/Wick-equations paragraph and "orthogonal matroids also coincide
with the class of Coxeter matroids of type `D_n`" are from it. — M. Baker,
T. Jin, *Representability of orthogonal matroids over partial fields*, Algebr.
Comb. **6** (2023) 1301–1311.

**Algorithmic / min-max side.** J. F. Geelen, S. Iwata, K. Murota, *The linear
delta-matroid parity problem*, JCTB **88** (2003) 377–398, DOI
`10.1016/S0095-8956(03)00039-X`. — A. Bouchet, W. H. Cunningham,
*Delta-matroids, jump systems, and bisubmodular polyhedra*, SIAM J. Discrete
Math. **8** (1995) 17–32, DOI `10.1137/S0895480191222926`. — T. Koana,
M. Wahlström, *Faster algorithms on linear delta-matroids*, STACS 2025, LIPIcs
**327**, Art. 62, pp. 62:1–62:19, DOI `10.4230/LIPIcs.STACS.2025.62`; full
version arXiv:2402.11596 — **PDF read directly** (the Δ-matroid / symmetric
exchange / linear Δ-matroid definitions quoted above are from its §1.1).

**Surveys.** I. Moffatt, *Delta-matroids for graph theorists*, in Surveys in
Combinatorics 2019, LMS Lecture Note Ser., Cambridge Univ. Press 2019, 167–220,
DOI `10.1017/9781108649094.007` — **the LNS volume number is deliberately
omitted**: sources disagreed (445 / 446 / 456) and the project's rule is to omit
rather than guess; verify against the printed book before any blueprint cite. —
C. Chun, I. Moffatt, S. D. Noble, R. Rueckriemen, *Matroids, delta-matroids and
embedded graphs*, JCTA **167** (2019) 7–59, DOI `10.1016/j.jcta.2019.02.023`.

**Adjacent / negative evidence.** J. P. S. Kung, *Pfaffian structures and
critical problems in finite symplectic spaces*, Ann. Combin. **1** (1997)
159–172, DOI `10.1007/BF02558472` — the one item whose subject is *avoidance*
conditions in a formed space with combinatorial content, but it is the
Crapo–Rota critical problem over **finite** symplectic spaces, not a genericity
statement in characteristic 0. **MISS**; cited for title/subject only, not read.
— J. Cruickshank, B. Jackson, T. Jordán, S. Tanigawa, *Rigidity of Graphs and
Frameworks: A Matroid Theoretic Approach*, arXiv:2508.11636, to appear in Surveys
in Combinatorics 2026, Cambridge Univ. Press, 42 pp. — the corroborating
negative: **zero occurrences** of each of `delta-matroid`, `∆-matroid`,
`Coxeter`, `symplectic`, `isotropic`, `Klein`, `quadric`, `Pfaffian` (checked
mechanically over the extracted PDF text). The two literatures have not met, and
the survey's authors include three of the four people most likely to have noticed
if they should.

**Classical facts used without a bibliographic pointer**, per the project's
"classical" convention: Witt's theorem and the `O(6)`-orbit classification on
`Gr(3,6)` by `rank Q|_V`; the α/β classification of the Klein quadric's maximal
isotropics (already so cited in the workbook); the Plücker/spinor correspondence;
`deg Gr(3,6) = 42`.

## §(K-bare-ext) — stub

The minimal open statement isolated by the (K-bare) extension-route recon:
the arbitrary-seed insertion lemma, with the def-equal caveat folded into its
`∃` as a line-avoidance side condition. Statement, the corank stratification
that produced it, the DZ/cube/Wagner danger gadgets and the option-C probe
results are in `notes/Phase39-design.md` §"(K-bare) extension-route recon".

**Scope note (2026-08-02).** W4 routes 1/3 do **not** touch this kernel: a
residual is feasible by hypothesis, so the split producer's `hbareSplit`
branch is unreachable there — `notes/Pencil-W4-informal.md` §"widened kernels
(routes 1/3)" *Step 0*.

**What the (K-tight) re-pin settles for this statement (2026-08-02,
pointer-level).** Its named prerequisite — the KT pp. 684–691 boundary-load
re-pin — is **done** (§(K-tight) Steps 0–2), and the calculus is exact at
*any* target-rank seed, not just chart-generic ones. Consequences for the
eventual statement:

- The right shape is the **determinantal criterion**: at a target-rank bare
  seed, a placement attains ⟺ the two functionals `⟨·, C(va)⟩, ⟨·, C(vb)⟩`
  are independent on the seed's obstruction space `U`, with
  `dim U = dim R_a + 1` forced (`= corank(G′) − s₀ + 1`); higher corank
  makes the failure locus thinner (rank-≤1 of a `2 × dim U` matrix of
  linear forms), matching the C2/C3 corank-stability observations.
- The C3 gloss "the failure set is exactly the line" is **corrected**: on
  the `dim U = 2` stratum the route-A failure locus is
  `line(a,b) ∪ P′` — a second line, exhibited at the control
  (§(K-tight) Step 3). The `∃`-form side condition survives unchanged; a
  `∀`-form "off-line ⟹ attains" would be false.
- The genuinely open core is now sharply two-part: (i) at an adversarial
  IH seed, show `dim R_a ≥ 1` — some `G′`-stress engages the fresh-edge
  fiber; a `dim R_a = 0` seed fails at **every** placement — and (ii) a
  rank-2 point exists in the confinement space (the criterion's
  non-vanishing at that seed), with no chart available to supply
  genericity for either part.

**Verdict: open.** To be filled by the dispatch that attacks it; nothing is
being developed here yet.
