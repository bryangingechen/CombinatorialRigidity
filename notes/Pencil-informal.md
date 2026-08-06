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
| *Shared dictionary* + test shapes `W19`/`S29` | 97–191 | serves **both** workbooks | `SD-` |
| ***State of (K)* — the gap map** | 192–422 | **the entry point; a pass updates it in place** | — |
| §(K-tight) | 423–682 | criterion proven-informally; **(K-tight) open — the phase's hardest item** | `KT-` |
| §(K-pitch) | 683–1116 | (T1)–(T5) proven-informally; closed at `ℓ = 3`; uniform form open | `PT-` |
| §(K-slide) | 1117–1408 | (S1) proven-informally; settled per member | `SL-` |
| §(K-slide-cl) | 1409–1700 | reduction proven; **refuted as stated**; the `∃Σ` form open | `SC-` |
| §(K-slide-comb) | 1701–2052 | **refuted as a class statement**; (C6)/(C7) proven-informally | `SB-` |
| §(K-flank) | 2053–2605 | per shape, not a uniform gap; half 2 proven-informally | `FL-` |
| §(K-pure) | 2606–3161 | direction C **refuted**; (PC-Z)/(PC-OBS) proven-informally; **(K-chord)** the successor | `PC-` |
| §(K-Λ) | 3162–4117 | **refuted as an independent gap**; (Λ1) an identity; **(OUT)** lives here | `Λ` |
| §(K-dom) | 4118–4511 | dominance holds at every probed habitat; **C1 not a route**; (D2) gains its mechanism from §(K-ann) | `DM-` |
| §(K-σ) | 4512–5229 | **route σ a CANDIDATE** — the one live candidate; its *Field scope* is settled by §(K-clos), and two of its refutations reverse there | `σ` |
| §(K-clos) | 5230–5856 | the field question **settled** ((AC-1)/(AC-7)); **(AC-6) refuted as a class statement**, open only on the tight stratum | `AC-` |
| §(K-ann) | 5857–6425 | the **recipe** ((ANH-2)/(ANH-3)) and (ANH-1)/(ANH-4) proven; the residue is **(ANH-R1)**, relocation #4 | `ANH-` |
| §(K-out) | 6426–6933 | (OUT)'s hypothesis **measured**: **(OC-3)** proves it is never automatic (no counting route); availability pointwise; **(OC-7)** a harness defect; residue **(OC-8)** | `OC-` |
| §(K-ind) | 6934–7279 | **refuted as a route** | `IN-` |
| §(K-Δ) | 7280–7546 | **NO HIT — the lead is discharged** | `DL-` |
| §(K-bare-ext) | 7547–7585 | open, nothing being developed | `BE-` |
| §(K-grid) | 7752–8156 | **reduction proven** — the tight-stratum residual of (AC-6) in final combinatorial form; residual = (GR-4) + (GR-6), open | `GR-` |

**Live vs settled**, using the division of the 2026-08-05 reorganization pass.
Live: §(K-tight), §(K-Λ), §(K-σ), §(K-pure), **§(K-ann)** — whose live residue is
(ANH-R1), everything else in it being settled — **§(K-out)**, whose live residue
is likewise only **(OC-8)** (its (OC-3) negative and its two pool measurements
are settled, and its (OC-7) is a *harness* item, not mathematics) — and
**(K-wit)** (owned jointly by
§(K-pitch) *Step 3* and §(K-Λ) *Steps 3–6*). Settled or refuted, so **do not
re-derive**: §(K-slide-comb), §(K-Δ), §(K-ind), §(K-slide-cl) as stated,
§(K-dom)'s C1 verdict, and §(K-clos) — whose tight-stratum residue now lives in
**§(K-grid)** (live) as the pair **(GR-4) + (GR-6)**, the class statement staying
refuted. The
gap map's *Settled, so not to be re-derived* blocks are authoritative for the
per-item detail.

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
- **(SD-6) branches are short: length `≤ 5`.** *(New 2026-08-06; §(K-ann)
  calls it **(ANH-8)** and points here — this is the only copy. The `SD-`
  form is forced by `notes/Pencil-labels.md` clause L1: `(R6)` is taken by
  `Pencil-strategy.md` §4.6.)* Let `β` be a branch (maximal degree-2 chain)
  of a class member `G` — tight, `def = 0`, `hnoRigid`, `|V| ≥ 2` — of
  length `ℓ`. Then `ℓ ≤ 5`.
  *Proof.* `G` is 2-edge-connected: a bridge would split `V` into `A, B`
  with `f(A) + f(B) = f(V) + 1 = 1 > 0`, so one side violates sparsity.
  Hence `G′ := G − int(β)` is connected (two edge-disjoint `u`–`w` paths
  cannot both use an edge of `β`). Counting,
  `f(V(G′)) = f(V(G)) − 5ℓ + 6(ℓ−1) = ℓ − 6`. For `ℓ ≥ 7` that is `> 0`,
  contradicting sparsity; for `ℓ = 6` it is `0`, so `def(G′) = 0` and `G′`
  is a **proper** rigid subgraph (`V(G′) ⊊ V(G)` because `β` has interior
  vertices; `|V(G′)| ≥ 2` because `G` has two hubs), contradicting
  `hnoRigid`. ∎ Verified over 4296 triples plus a past-length-6 stress test
  (`notes/scripts/w4/annih.py --census`; §(K-ann) *Step A6*).

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
| **(K-tight)** | (K-tight) 5; (K-σ) | **open**, true with strong evidence; no genuine escape failure anywhere in the corrected numerics **on the hard stratum `dim R_a = 1`** (and above it) — the claim is **false without that qualifier**: §(K-flank) F5(d) exhibits 5 legal nondegenerate target-rank `G′` seeds at `P21` with `s₀ = 1`, `dim R_a = 0`, `dim U = 1`, which the Step-2.3 calculus *proves* fail at every placement (8/8 observed each); `hK`'s ∃-form is untouched (30/35 escape). **A CANDIDATE closure now exists and this row does NOT move on it**: §(K-σ)'s **route σ** (route A run at the dual seed `σu`) would close the hard stratum *length-free* via the 6-dimensional span `Λ²Π̂(b) + Λ²Π̂(c) + α_{pt(b)} = K⁶` (or its `c`-mirror — the side condition is **free** by (σ7)), but it rests on four named obligations, the first of which — σ-nondegeneracy of the transported seed — is **NOT implied**: 45 constructed hard-stratum, primally-nondegenerate seeds violate the dual conjuncts (`sigma.py --hunt`, 2026-08-05), so the earlier "observed 47/47" was genericity. Two of the four conjuncts are free **at `ℝ`** (1 by the landed `hasPencilPanelRealization_mapExtensor_screwComplementIso`, 3 by the primal conjuncts when no two hubs are adjacent) and the steering repair is exhibited exactly on a chart line. **FIELD-SCOPE CAVEAT (2026-08-05, recorded not settled):** route σ is an `ℝ`-only construction — `screwComplementIso` is `ScrewSpace ℝ 2 ≃ₗ[ℝ] ScrewSpace ℝ 2` — aimed at an `hK` quantified at general `[Infinite K]`, so this candidate closes the row only at `ℝ` unless the polarity generalizes (§(K-σ) *Field scope*) — **which since 2026-08-06 it DOES**, at the price of one section with every input landed (§(K-clos) (AC-1)), and `ℝ` is moreover the **narrowest** field choice rather than a safe default, since `hK` over `ℂ̄` implies it over every infinite characteristic-0 field and not conversely (§(K-clos) (AC-7)) | (K-move), (K-pitch), **or** discharging §(K-σ) *Step σ5* obligation 1 — the named repair is `exists_common_seed_pencilRow_and_polynomials` (`Engine.lean:476`), whose remaining design decisions are **which maximal minor** to fix per LI conjunct (they are unions of basic opens, not single hypersurface complements) **and at which field** (`ℝ`, instantiating the headline first, or general `K`, which needs a general-`K` polarity). **`exists_pencilSeed_of_nondeg` is NOT the bridge** — it takes obligation 1 as a hypothesis |
| **(K-move)** | (K-tight) 5 | **open — the sharpest gap** on the stress side; N8 refutes block-determined `[r]` at both probed families | `[r]`-as-chart-rational-function infrastructure (option B, **not** commissioned) |
| **(K-pitch)** | (K-pitch); (K-pure) P3; (K-Λ) | (T1)–(T5) **proven-informally**; **closed** at length-3-companion splits (bracket monomial, θ(3,3,6)); uniform form **open**. Step 2's (F-A)/(F-B) dichotomy is **upgraded to the algebraic form (PC-Z)** (§(K-pure), proven-informally): `Q(z) = 0 ⟺ V_bc` meets `α(a)` or `Λ²π̂`, the only two maximal totally isotropic 3-spaces containing `T` — the exact target of any future non-vanishing argument (its *reason* is Witt's theorem — §(K-Λ) *Step 1*). The `ℓ = 3` verdict is unchanged but now has a **two-line proof that *explains* its five brackets**: they are the coordinate form of `S ∩ α_a = S ∩ β_{π_a} = 0` (§(K-Λ) *Step 1*(i)). The bracket **closed form extends from `ℓ = 3` to `ℓ = 4`**, as a **product of two bracket-linear forms in the far covector** ((Λ1), since 2026-08-05 a **symbolic identity over the function field** — `M2 --script notes/scripts/m2/lambda1.m2`) — a positive standalone result, but **not** a non-vanishing theorem: its zero locus is nonempty exactly at the two structurally meaningful configurations | one seed with `Q(z) ≠ 0` per (graph, split), uniformly — by (PC-Z), one seed where `V_bc` misses **both** isotropic 3-spaces |
| **(K-wit)** | (K-pitch) 3; (K-Λ) 3–6 | **open**; the weakest exact form — per habitat+split *equivalent* to the escape at a good seed — and now the **single live form of the pitch route at companion splits**: it inherits (K-Λ)'s status and gains a *necessary-and-sufficient* companion form (§(K-Λ) *Theorem (Λ-completeness at length-4 companions)*: the escape holds at some target-rank seed **iff** the pitch certificate is nonzero at some target-rank seed). The **two-point failure locus is this row's content** — `{V_bc ⊥_B C(M)}` (the failure itself) and `{V_bc ⊥_B C(bc)}` (route A escapes, `★r ∝ C(bc)`); since 2026-08-05 those two points are known to be **exactly a σ-orbit** (§(K-σ) (σ5)), so the recorded asymmetry between their consequences is a *one-frame artifact*, not a broken symmetry — and if §(K-σ)'s candidate route σ stands, this row's trichotomy loses its failure branch and (K-wit) leaves the escape's critical path. Two load-bearing side conditions are newly **named**, neither present in the prior formulation: **(Λ0d)** panel non-incidence in **both** directions (`pt(c) ∉ Π(b)` *and* `pt(b) ∉ Π(c)`; witness θ(3,4,5) seed 345, where `span_t ω⁻` collapses `3 → 1`) and **(Λ0f)**, now **PROVEN at the generic point and WIDER than first stated** (2026-08-05, `m2/lambda0.m2`): the exact criterion is **(Λ0f′)** `span_t ω⁺ = 3 ⟺ p⁺₂p⁺₃·g₁₃g₁₄g₂₄ ≠ 0` (and `q₂q₃·g₁₃g₁₄g₂₄ ≠ 0` for `ω⁻`), where `g₁₃g₂₄ ≠ 0` is `rank Q|_S = 4` and **`g₁₄ = [b,x₁,x₃,c] ≠ 0` was asserted nowhere** — the two outer companion lines must not meet. Since 2026-08-05 (§(K-Λ) *Step 3a*, `outer.py`) that clause is **located, not merely named**: geometrically it says the two marked points `C₁ ∩ M`, `C₄ ∩ M` of the meet line coincide **(Λ0g)**; wherever a companion end is free it is **implied by (Λ0d)** **(Λ0i)** (3628/4280 swept pairs); **no class habitat in scope forces it** (`g₁₄ ≠ 0` at 4280/4280 exact pairs over 1357 class shapes, `d g₁₄ ≠ 0` at 684/684 chart points), so **Λ-completeness stands as written**; but it *is* reachable at a target-rank `dim R_a = 1` seed of all four habitats by an explicit chart move, both spans dropping `3 → 2`, so the clause is load-bearing. Residual: class shapes with **two or more hubs on the companion interior**, which no swept family realizes. **New 2026-08-05, a sufficient condition rather than a status change:** since `p⁺` and `q` both have their *outer* entries vanishing structurally, the whole (Λ2) bad set lies on the single line `{λ₁ = λ₄ = 0}` of `P(S*)`, so **(OUT)** (§(K-Λ) *Step 5a*) — *either outer companion line not a relative twist* — already forces the escape by pitch at `k = 4`; it is conditional on (Λ0) in full. **Its hypothesis is MEASURED since 2026-08-06 (§(K-out)), and the measurement cuts both ways**: available pointwise (356/357 POOL-G, 270/270 POOL-S, every probed (split, companion) pair) but **never automatic** — (OC-3) proves `{λ₁ = 0}` is nonempty on *every* class shape's chart, so no counting argument can ever discharge (OUT), and the residual **(OC-8)** is a rank *lower* bound on the whole-graph chart | one `H`-motion pairing non-trivially with `C(M)`, uniformly — **or, at length-4 companions only, the strictly cheaper (OUT)**: `C₁ = C(b x₁) ∉ V_bc` or `C₄ = C(x₃ c) ∉ V_bc`, a far-side, panel-free, `a`-free condition (§(K-Λ) *Step 5a*; conditional on (Λ0d) + the widened (Λ0f′), sufficient and never necessary, and a rank *lower* bound so §2.3's asymmetry is relocated, not evaded). **Caveat, mandatory since 2026-08-06 — §(K-out) (OC-3):** (OUT)'s hypothesis is **never automatic**, its bad locus being nonempty on the chart of every class shape in scope (one marked direction of `x₁`'s pencil, since `dim R₁ = 5` and `dim L_b = 2`), so this route can be discharged only by a genericity argument on the whole-graph chart — **(OC-8)** — and **never by a count**; what is delivered is *availability*, measured pointwise, not uniformity. **New 2026-08-06, a second `k = 4`-only sufficient route: §(K-ann) (ANH-R1)** — `τ_β ≠ 0` at the pencil placement, i.e. `H/P − β` is pencil-rigid. Its consumer is the class-uniform **recipe** (ANH-7) (one named far-chart move, one 4-point bracket, 89 % coverage), and by §(K-Λ)'s Λ-completeness discharging it would close the **whole length-4-companion stratum**, not one shape. It is **relocation #4** and, like (OUT), a rank *lower* bound — §2.3 relocated onto a smaller contracted graph, not evaded; **whether it is easier than its parent or merely smaller is OPEN** |
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
| **(K-dom)** *(new, 2026-08-05)* | (K-dom) D0–D7 | **open as the uniform statement, and provably FALSE off the class**, so the strategy doc's §4-C1 route is **not recommended**. Writing `k` for the *companion length* (the shortest `b`–`c` path of `H`; `k ≥ 3`): **(D1)** `rank d(H ↦ V_bc) ≤ min(9, 6k − 14)` in the bad-locus-frozen scoping, **proven** from path-sum containment — so `≤ 4` at `k = 3`, where `V_bc` is moreover always in the discriminant hypersurface of `Gr(3,6)`; **(D2)** the far block is `≤ 3(k−3)` (a corollary of (T5)), **attained** at `0,3,6,9` for `k = 3,4,5,6` — and since 2026-08-06 that number has a **mechanism** rather than a measurement: §(K-ann) **(ANH-1)** identifies the annihilator as the self-stress space of the contracted framework `H/P`, so `3(k−3)` is `dim Gr(k−3,k)` **for that stress space** and the dimension `k−3` is forced by a *count*; **(D3)** `hnoRigid` forces `k ≥ 4` (= §(K-slide) *Step 5*'s `ℓ₁+ℓ₂ ≥ 7`), so the cap bites exactly on **(K-res)**. Measured: rank **9 — dominance — at all 5 probed class habitats** (θ(3,4,5), NT21, NT16k5, `K4`/`K5−M` dbl-subdiv; `k ∈ {4,5,6}`) and exactly **4** at both `k = 3` habitats. **(D4)**: rank 9 at one rational seed ⟹ the escape on a *dense open* subset of that shape's chart — a strictly stronger per-shape statement than an `∃`-witness, and no more useful. §4-C1's two claimed values are **REFUTED** (D6): the image does **not** grow with the far graph (it is capped by the local `k`), and the 2026-07-30 locality gate was run at `k = 6`, the *maximal* far-dependence grade, so it is not evidence for dominance. **Class uniformity untouched** — "rank 9 at every class shape" is one determinantal condition per (shape, split), the same per-shape object §(K-pure) *P5* names as the wall | a class habitat with `rank dV < 9` at every seed (a sharp new obstruction; none found), **or** a mechanism making `rank dV = 9` combinatorially certifiable class-wide — the only thing that would turn C1 into a uniform route |
| **(K-σ)** *(new, 2026-08-05)* | (K-σ) *Field scope*, σ0–σ6, σ4b | **four settled verdicts + one CANDIDATE, offered for adjudication; the FIELD-SCOPE caveat they carried is DISCHARGED** (§(K-clos), 2026-08-06 — see the row below and the sentence marked SETTLED here). `σ = screwComplementIso` exists in tree **only over `ℝ`** (`Duality.lean:69`), and so does the self-duality theorem the conjunct-1 freeness cites (`Statement.lean:257`), while **`hK` is quantified at the general `[Infinite K]`** of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Escape.lean:555`). Whether the polarity generalizes is **SETTLED — YES** (§(K-clos) (AC-1), 2026-08-06): bookkeeping, one section, and the general-`K` **transport is already landed** as `BodyHingeFramework.mapSupport` with its rank lemma, so `ProjectiveInvariance.lean` needs no generalization; source-level, **not compiler-checked**. **(σ7) needs no polarity and is field-neutral outright**; (σ1)–(σ6) and route σ are field-neutral *modulo the polarity existing*, so they **port**; the two refutations below use `ℝ`-**definiteness** and do **not** port — indeed **both REVERSE over `ℂ̄`** (§(K-clos) (AC-2)/(AC-3): σ-fixed configurations exist and are nondegenerate at the Tay target), **and the verdict they support survives anyway** on the field-neutral §(K-clos) (AC-5). Settled: the σ-intertwining question is **REFUTED in its literal form** (`pt(a) ∈ π_a` forces `pt(a)·pt(a) = 0`, impossible over ℝ with the project's *definite* polarity — `Molecular/Meet.lean:88` records it is the Hodge star of the standard dot product) and **CONFIRMED covariantly** (`σ(α_p) = β_{p^⊥}`, `σ(β_π) = α_{pole(π)}`), which makes §(K-Λ)'s two-point failure locus **exactly a σ-orbit**; and **σ-equivariant seed recipes are DEAD** — no σ-fixed pencil configuration exists over ℝ, and a null polarity puts every hinge line in a linear line complex, giving a self-stress per cycle (**deficit exactly 1 at 6/6** on tight `C₆`). Fourth settled verdict, **new 2026-08-05** (`sigma.py --hunt`, three pools of its own, disjoint from the pinned 47): **(σ7)** *Step σ3*'s side condition `pt(b) ∉ Π(c)` is **FREE** — primal conjunct 4 at the split's middle body `a` forbids both halves of (Λ0d) from failing at once (39/39 witnesses that forcing both leaves `a` with no panel), settling *What would change this* (iv); **and, in the other direction, the dual conjuncts at `σu` are NOT implied** — 45 constructed hard-stratum, primally-nondegenerate seeds violate dual conjuncts 2 and 4 (coplanar-chain degeneration), so *Step σ4*'s 47/47 was genericity. Candidate: **route σ**, whose uniform-failure criterion `★r ∥ C(bc)` is the σ-image of routes A/B's `★r ∥ C(M)` and cannot hold simultaneously with it. Scope of the validation: `s₀ = 0`, `dim R_a = 1`, both ends hubs, tight control only (the hunt pools widen the *configurations*, not the shape) — `dim R_a = 0` **untouched**, (K-res) `s₀ = 2` **unsampled**; the criterion at `σu` is **imported, not re-derived**, and its failure direction is **unwitnessed** (`predAfalse = 0/47`); and the branch route σ closes has **never been observed nonempty**, so the gain is **evidence → argument**, never *bug fixed*. **No gap-map status moves on account of route σ** | obligation 1 of §(K-σ) *Step σ5* — now **sized, not just named** (all of it **at `ℝ`** — see the caveat opposite): conjunct 1 free by a landed theorem, conjunct 3 free by the primal conjuncts on no-adjacent-hub shapes, conjunct 2 at the two `a`-edges = two-sided (Λ0d), leaving two genuinely new conditions with a steering repair exhibited exactly (`bracket(τ) = τ·bracket(1)`). Route σ faces exactly **one** crux: the workbook's two kills of M₁ (§(K-tight) *Step 1* and *Step 2.6*) have the **same** stated reason, the `hinge(vb) := q(ab)` pinning |
| **(K-clos)** *(new, 2026-08-06)* | (K-clos) Z0–Z8 | **The field question of §(K-σ), settled — plus one construction REFUTED as a class statement and left OPEN only on the tight stratum.** Read the two halves separately. **Settled, proven-informally:** **(AC-1)** the polarity **generalizes** — bookkeeping, one section, and the general-`K` transport is already in tree (`BodyHingeFramework.mapSupport`, `Molecular/GenericLift/HingeGeneric.lean:462`, rank lemma `:544`), so `ProjectiveInvariance.lean`'s 19-declaration `ℝ`-fixed `mapExtensor` API needs **no** generalization (source-level, **not compiler-checked** — the dispatch carried a no-Lean constraint, and a ~20-line typecheck spike would settle it); **(AC-2)** the σ-fixed locus over `ℂ̄` is exactly the `P¹ × P¹` **grid** on the fixed quadric, with the conjugacy law `p ⬝ᵥ p′ = 2[s,s′][u,u′]`; **(AC-3)** those grids are **nondegenerate at the Tay target**, so §(K-σ) *Step σ6*'s "degenerate" is **REFUTED for the symmetric correlation** (it stands for the null one); **(AC-4)** the `⋆`-eigen decoupling `rank = rank₊ + rank₋` and the three conditions target rank forces (balance, both classes forests, both blocks isostatic); **(AC-5)** at a σ-fixed seed **route σ IS route A** (32/32, as subspaces), which is the **field-neutral replacement** for the `ℝ`-definiteness kill — so *"σ-equivariant seed recipes are DEAD" survives algebraic closure*; **(AC-7)** `hK` over `ℂ̄` **implies** `hK` over every infinite characteristic-0 field, converse **false**, so `ℝ` is the **narrowest** choice and the residual content of `[Infinite K]` is **positive characteristic only** — never probed; **(AC-8)** char 2 breaks the geometry (double plane, no splitting) but not (AC-1). **REFUTED as a class statement, OPEN on the tight stratum: (AC-6)** — the grids are a *combinatorial recipe* (a ruling 2-colouring of `E(G)`) for target-rank nondegenerate pencil realizations, reaching the target at **15/15 tight** shapes of a pinned 21-shape pool (all eight §(K-flank) flank shapes among them) and at the (K-res) inhabitant `W19` (1/1, rigid but not count-tight), 2/5 not-rigid, **18/21** overall. It **fails at three**, and the habitat attribution is the point: θ(1,2,9) and θ(2,3,7) are **out** of `hK`'s habitat (`hnoRigid` false) — θ(1,2,9)'s miss is *correct behaviour*, its triangle with two hubs already forbidden by `not_pencilNondegFeasible_of_triangle_two_hubs` — while **`C11`, a bare odd cycle, is IN the habitat and refutes the class statement by itself**. The mechanism is **parity and is complete**: no admissible colouring exists **iff** `G` has a bare odd cycle component (`C3…C14` → exactly `[3,5,7,9,11,13]`; 19/19 non-cycle pool shapes admit one) — and it **cannot** be the tight-stratum obstruction, since a tight shape has hubs and is never a bare cycle. **This row must not be read as "open" unqualified: the habitat-level statement is settled NEGATIVELY.** Chart-image membership for the grids is **proven and machine-verified** since 2026-08-06 (§(K-grid) (GR-5), 5/5 end-to-end) | for the *narrow* remainder only: the tight-stratum residual now lives in **§(K-grid)** (2026-08-06, direction T) as the pair **(GR-4) + (GR-6)** — the counting criterion's sufficiency at conic labels, and the admissible-colouring existence — both geometry-free. The direction-network statement this cell used to name ("isostatic whenever (AC-4)(i)–(ii) hold") is **refuted and corrected** there ((GR-2)/(GR-3): the mono-hub bond, and two proven counting families), the cheap-kill census is run and extended 15/15 → **907/907** (θ(2,5,5) + the exhaustive `K4` stratum included, no miss), and chart-image membership is proven ((GR-5)), so a target-rank grid **is** `hK`'s conclusion object. Discharging (GR-4) + (GR-6) discharges `hK` on the tight stratum **directly**, then over every infinite characteristic-0 field by (AC-7). Nothing here would ever make the statement habitat-uniform: `C11` is permanent. **(AC-9), new 2026-08-06:** every σ-fixed body of degree `≥ 3` carries a **coincident hinge line** (pigeonhole against the two-ruling-lines cap), so the σ-fixed locus lies entirely inside the free-rotor locus and the composite guard accepts **0 of 64** `ds-K4` colourings — this **qualifies** (AC-3) (the four conjuncts and the Tay target still hold, so *Step σ6*'s claim stays refuted about that predicate) and forbids reading any σ-fixed witness as *generic* |
| **(K-grid)** *(new, 2026-08-06, direction T)* | (K-grid) G0–G7 | **The tight-stratum residual of (AC-6), reduced with proven reductions to two geometry-free gaps.** (GR-1) each `⋆`-eigen-block is a **conic direction network = generalized C¹-quadratic spline system** on the contracted multigraph, with the exact rank identity `rank = 3n_c − 3 − dim Z` verified 688/688 through two independent matrices; (GR-2) the former proof target "(AC-4)(i)–(ii) ⟹ both blocks isostatic" is **refuted** — 8 of `ds-K4`'s 64 colourings are balanced/both-forests at rank 89, mechanism a **bond of the contracted graph inside one ruling class** (mono hub = free rotor; the rank-costing boundary case of (AC-9)); (GR-3) two proven, mutually non-subsuming counting obstruction families bound `dim Z`; (GR-4) their max **equals** generic `dim Z` at all 688 pool instances (**true-modulo-named-gap** — the ≤ direction at conic labels; the construction's component-index labels are NOT generic, 10/688 special-value overshoots); (GR-5) chart-image membership **proven-informally class-uniformly + machine-verified 5/5 end-to-end** — a target-rank grid IS `hK`'s conclusion object (`Escape.lean:555`) over `ℚ(i)`, hence over every infinite char-0 field by (AC-7); census **907/907** (877 exhaustive `K4` + 6 + 21 sweeps + 3 thetas incl. the new θ(2,5,5)), first-hit 835 at the first filter-passing colouring | **(GR-4)** — the matroid-union tensor realization pushed through the moment-curve confinement (valuation/degeneration refinement of the classical specialization argument) — **plus (GR-6)** — an admissible colouring satisfying (GR-3)(a)/(b)/(c) in both blocks exists at every tight class shape (open; 907/907 evidence; Nash-Williams/Edmonds-shaped, cf. (C6); **no min-max yet**, and until one exists `Pencil-strategy.md` §2.3's base-rate warning applies). Together they discharge `hK` on the tight stratum over every infinite characteristic-0 field |
| **(K-ann)** *(new, 2026-08-06)* | (K-ann) A1–A9 | **A recipe delivered and an input relocated — read the two halves separately, and do not let the first warm up the second.** **Delivered, and the arc's first *formula* rather than a search** (`Pencil-strategy.md` §2.2's sense): **(ANH-2)** the reciprocity identity `dλ(π_P ω) = Σ_e ω_e B(τ_e, δC_e)`, local at the moved vertex, no genericity hypothesis, class-uniform, verified at 276 far-chart directions × 828 motions against an independent implicit differentiation; **(ANH-3)** at the named move (translate one non-hub 2-valent far body) it collapses to **one Klein pairing**, 192 single-vertex moves. Carry its caveat: *the formula's kernel is bounded-size and class-uniform; what it pairs against (`τ`, `ω`) is not* — so U1 is **half** delivered, the move and the formula but not the inputs. **Proven, and the mechanism behind (D2):** **(ANH-1)** `λ` **is a self-stress** — of the *contracted* framework `H/P` (weld the companion into one body), stress dimension exactly `k−3` (18 seeds, 9 habitats, `k = 3..6`), so (T5)/(D2) stop being measured bounds. **Proven, `k = 4`-only:** **(ANH-4)** `E(H/P)` is a **circuit of the generic Tay matroid**, from 5/6-sparsity + `hnoRigid`, the count `5k+10 ≤ 6k+6` tight exactly at `k = 4` — the same equality case as (D3)'s `k ≥ 4`; realized side, the support is the **whole** far edge set at 14/14 class seeds, so the named move needs **no support-location step**, with an off-class control (`hnoRigid` dropped) where the circuit is a proper 5-cycle and moves off it leave `V_bc` exactly fixed. **(ANH-7)**: on the **89 %** (3820/4296) of triples with a length-5 `H/P` branch the whole criterion is **one 4-point bracket**, correct 56/56. Corrections recorded here because they were written down before the pass ran: option B and U2 are **not** the same object (`λ` is a self-stress of the contracted **far** framework, not `[r]`); U2's cocircuit reading is the **dual** of what the recipe needs (`supp τ` is a *circuit*); and the pass's own `⟨C(z₁z₂)⟩` kill set is wrong at `dim U_y = 1`, the general criterion being `ρ_y ⊥_B (V_y ∧ U_y)`. **`k`-grading:** (ANH-1/2/3/5/6) and (SD-6) are length-free (`k = 3..6`); **(ANH-4) is provably `k = 4` only**, and with `k = 4` the `hnoRigid` equality case **no `k`-graded mechanism including this one can close the class** — the verdict `Pencil-strategy.md` §4.6 already carries. **No gap-map *status* moves; class uniformity untouched** | **(ANH-R1)** `τ_β ≠ 0` at the pencil placement — `H/P − β` (count exactly 0, generically isostatic) is **rigid** there. This is **relocation #4**, of a *different kind* for three reasons and *not thereby easier*: it crosses into a matroid that **has** a min-max (Tay, Phases 12–15) whose combinatorial half (ANH-4) **proves**; it lands on a **strictly smaller graph** (`\|E(G)\|−12` edges); and by §(K-ind) *Step I6* the welded body is not a pencil body, so it sits on the **mixed stratum** — not the same problem shrunk, and `Pencil-strategy.md` §4-C3's second concrete consumer after (OUT). It does **not** evade §2.3 (a rank *lower* bound): **limiting, not fatal** — the smaller graph's matroid is Tay's, where independence *is* combinatorially characterised, so the wall changes from "no matroid sees this" to "the matroid sees it and the pin may not respect the matroid" (the weak-map / specialization-stability lead of §4.6, which now has a statement to attach to). **OPEN and stated as open: whether (ANH-R1) is genuinely easier than its parent, or merely smaller — nothing in this pass settles that.** What it *would* close: the **length-4-companion stratum outright**, via §(K-Λ)'s Λ-completeness, since `dλ ≢ 0` makes `{λ = p⁺}` proper on an irreducible chart |
| **(K-out)** *(new, 2026-08-06)* | (K-out) O1–O8 | **(OUT)'s hypothesis, measured — and the headline is the NEGATIVE. Read the two halves separately, and do not let the second warm up the first.** **The negative, proven-informally and load-bearing: (OC-3)** on the pencil chart `C₁ = C(b,x₁)` is confined to the 2-dimensional pencil `L_b = α_{pt(b)} ∩ β_{Π(b)}` while the far relative twist space `R₁` does not see `pt(x₁)`, so `dim R₁ = 5` forces `dim(R₁ ∩ L_b) ≥ 5 + 2 − 6 = 1` — **`{λ₁ = 0}` is nonempty at every class shape in the enumerated scope**, exactly one marked direction of `x₁`'s pencil. Therefore **no counting argument, no matroid statement and no placement-blind argument can ever deliver (OUT)'s hypothesis**; measured on-chart `dim R = 5`, `dim(R ∩ L) = 1` (never 2) at 46/46 frames, so the bad locus is also *proper*. **The combinatorial half does NOT deliver availability: (OC-2)**'s uniform 4296-pair result (`χ = 0`, `def(H/X) = def(H/Y) = 0`, `(μ, dim R, A) = (1,5,0)` on both sides) collapses to **one** measured fact — rigidity of `H/X`, the rest being arithmetic — and `deficiency` is the ***ambient*-generic** count, blind to the chart confinement. **The positives are pointwise, over two DISJOINT pinned pools, never aggregated: (OC-5)** POOL-G (4 habitats × seeds 200–299, 357 frames) distribution `322/17/17/1`, hypothesis **356/357**, conclusion separately verified **356/356**, (Λ0d) failing **0/357**; **(OC-6)** POOL-S (41 shapes / 90 splits / 270 frames) **270/270** with **0** silent (split, companion) pairs; **(OC-1)** *Step 5a*'s hinge-rate reading is exact and driver-asserted (`λ₁ = 0 ⟺ C₁ ∈ V_bc ⟺ dim W₁ = 1 ⟺ C₁ ∈ R₁`, 46 frames); **(OC-4)** the bad line is **reached by a legal chart move** at all four habitats — 3 of them with no coincident hinge line — keeping every (Λ0) clause, target rank, `dim R_a = 1` and all four `IsNondegPencilRealization` conjuncts, and with `deg_t Q(z(t)) = 4` there, so the escape holds exactly where (OUT) is blind. **(OUT) is therefore available, never automatic, and not contradicted.** **A HARNESS DEFECT, escalated: (OC-7)** — `widened.place_pencil_general`'s single-hub-interior sampler degenerates via `localtest.plane_basis` at **32 of 357** POOL-G frames (≈ 9 %) and that degeneracy **implies** `λᵢ = 0` (15/15 `b`-side, 18/18 `c`-side), uncaught by `flanks.star_span_ranks` (*documented* as the guard against exactly that artifact) and excluded by no `IsNondegPencilRealization` conjunct. **Standing rule: no `place_pencil_general` battery may be quoted as a *rate* or as evidence about a generic chart point** — POOL-G figures are quoted over the **318 coincidence-free** frames, never the raw 357. Second `plane_basis` contamination, **first with the documented guard failing**; `notes/scripts/README.md` *Harness debt* item 4. §(K-ann) is flagged for a **check, not an error**: its claims are identities and pointwise attainments, which degenerate frames make *harder* to satisfy (conservative); rates are what the defect distorts. **Verdict: availability, MEASURED, not proven. No gap-map *status* moves; class uniformity untouched** — the (K-wit) row's *what would close it* cell gains the (OC-3) caveat on (OUT) | **(OC-8)**: at every class shape, a hard-stratum target-rank point of the **whole-graph** chart with `L_b ⊄ R₁` or `L_c ⊄ R₄`. That is a rank **lower** bound at a pencil placement — `Pencil-strategy.md` §2.3's wall **relocated** onto the smaller `H/{e₂,e₃,e₄}` and **weakened, not crossed** — and (OC-3) says the relocation **cannot be discharged combinatorially**, so any proof must be a genericity argument on the whole-graph chart (needing its hard-stratum component not to lie inside `{λ₁ = 0} ∩ {λ₄ = 0}`), which the arc has never established because `λ` is a **far** datum. The one symbolically tractable piece: `L_b ⊄ R₁` as a polynomial non-vanishing (`Pencil-strategy.md` §5.3). **(OC-7) is CLEARED** (2026-08-06 re-baselining round S1/S2: the composite guard `repin.star_generic` exists, is adversarially tested on both a constructed and a sampled witness, and is adopted at every `w4/` acceptance site except this section's two measuring modes); **(OC-9)** measures that the guard rejects 58/357 and strictly contains the two-end diagnostic's 39 |
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
  refuted **over `ℝ`** (it reverses over `ℂ̄` — (K-clos) (AC-2)), the
  **covariant** one confirmed field-neutrally, and the two-point failure locus is
  a σ-orbit. **σ-equivariant seed recipes are dead** with a proof — do not
  re-attempt one — but since 2026-08-06 the proof is **(K-clos) (AC-5)**, not
  `ℝ`-definiteness, and a symmetric-configuration construction is *not* the
  thing that fails: it exists, it is nondegenerate, and it collapses route σ
  onto route A.
- **The field scope of §(K-σ) is SETTLED** ((K-σ) *Field scope* + (K-clos),
  2026-08-06; recorded as open 2026-08-05): `σ` and the four polarity theorems
  are `ℝ`-only in tree while `hK` is consumed at general `[Infinite K]` — do not
  re-derive that signature census — but the polarity **does** generalize
  ((AC-1)), the transport is landed (`mapSupport`), (σ1)–(σ6) and route σ port,
  and *Step σ1(a)*/*Step σ6*'s two refutations **reverse** over `ℂ̄` without
  moving their verdict. Do **not** re-open "does the polarity generalize?", and
  do not budget for `ProjectiveInvariance.lean`.
- **The obligation-1 hunt is DONE, in both directions** ((K-σ) σ3/σ4b,
  `sigma.py --hunt`; three pools of its own): the dual conjuncts at `σu` are
  **not implied** by the primal ones (45 constructed hard-stratum,
  primally-nondegenerate counterexamples — the coplanar-chain degeneration), so
  no future pass should read a `n/n` dual-conjunct census as an implication;
  **random** search cannot find them (0 in 92 fresh draws), so a re-hunt must
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

**Settled 2026-08-06, the over-`ℂ̄` batch ((K-clos)) — also not to be
re-derived.**

- **The σ-fixed locus IS the `P¹ × P¹` grid on `Q`**, with the conjugacy law
  `p ⬝ᵥ p′ = 2·[s,s′]·[u,u′]` — two points of `Q` are conjugate iff they share a
  ruling parameter ((AC-2)) — and the lines on `Q` are exactly the `⋆`-fixed
  points of the Klein quadric.
- **The `⋆`-eigen decoupling and its three forced conditions** ((AC-4)):
  `rank = rank₊ + rank₋`, and at a tight shape target rank forces balance, both
  ruling classes forests, and both blocks isostatic at `3|V| − 3`.
- **The route-σ collapse at a σ-fixed seed** ((AC-5)) — the field-neutral reason
  σ-equivariant recipes are dead.
- **The parity characterization, complete**: a graph admits **no** alternation
  colouring, hence no σ-fixed nondegenerate configuration, **iff** it has a bare
  odd cycle component ((AC-6)). So `C11` refutes the grid recipe class-wide, and
  **no tight shape can fail that way** — do not re-run the odd-cycle census, and
  do not use parity to rescue the tight-stratum question.
- **The characteristic-0 descent** ((AC-7)): `hK` over `ℂ̄` gives `hK` over every
  infinite characteristic-0 field, converse false. **In particular, do not
  re-open "should we instantiate the headline at `ℝ`" as if `ℝ` and `ℂ̄` were
  symmetric options** — `ℝ` is the narrowest. The unprobed residue is
  characteristic `p`.
- **The char-2 degeneration** ((AC-8)): `Q` is a double plane and `Λ²` does not
  split, so (AC-2)–(AC-6) need `char ≠ 2` while (AC-1) does not.

**Settled 2026-08-06, the annihilator batch ((K-ann)) — also not to be
re-derived.**

- **What `λ` IS** ((ANH-1)): the hinge violation of the unique self-stress of the
  **contracted** framework `H/P`, whose stress space has dimension `k−3` by a
  count. So (T5)'s annihilator and (D2)'s `3(k−3)` have a mechanism — do not
  re-measure the far block, and do not re-derive "which `Gr(k−3,k)` point".
  Corollary for anyone re-reading the option-B adjudication: this stress is **not**
  `[r]`, so option B's infrastructure is not needed and its NO-GO is unaffected.
- **The reciprocity identity** ((ANH-2)/(ANH-3)): `dλ(π_P ω) = Σ_e ω_e B(τ_e, δC_e)`,
  local at the moved vertex, one Klein pairing at the named move. Proven and
  driver-checked at 276 × 828; do not re-derive it, and do not quote it without its
  caveat (bounded-size **kernel**, unbounded **inputs**).
- **`E(H/P)` is a Tay circuit at `k = 4`, and only there** ((ANH-4)) — proven from
  5/6-sparsity + `hnoRigid`, tight exactly at `k = 4`. Two consequences to reuse
  rather than re-derive: the named move needs **no support-location step**, and
  `girth(H/P) ≥ 6` unless `G = θ(3,4,5)`, which is the **unique** `k = 4` class shape
  whose whole annihilator is the Klein-perp of a single 5-cycle.
- **Branch lengths are `≤ 5` on the class** — promoted to the *Shared dictionary* as
  **(SD-6)**, elementary, with a past-length-6 census stress test. Do not re-run it.
- **The two dual objects on `E(H)`**: `supp(λ)` is a **cocircuit** (that is (OUT)'s
  half, and U2 read it correctly); `supp(τ)` is a **circuit** (that is the recipe's
  half). Do not conflate them, and do not re-open "option B and U2 are the same
  object".

**Settled 2026-08-06, the outer-line batch ((K-out)) — also not to be
re-derived.**

- **The hinge-rate reading of (OUT) is exact** ((OC-1)): `λ₁ = 0 ⟺ C₁ ∈ V_bc ⟺
  dim{m(b) − m(X)} = 1 ⟺ C₁ ∈ R₁` (at `μ₁ = 1`), two lines from (Λ0a) alone, and
  `μ₁ ≥ 2` makes `λ₁ ≠ 0` outright. Do not re-derive it and do not re-measure the
  welded model.
- **The combinatorial map of (OUT) is uniform and it is the WRONG object**
  ((OC-2)): `χ = 0`, `H/X` tight, `(μ, dim R, A) = (1,5,0)` at all 4296 pairs —
  but `deficiency` is the **ambient**-generic count, so this is *not* evidence
  about a pencil-generic placement. Do not quote it as availability.
- **(OUT) is never automatic** ((OC-3)) — the bad locus is nonempty on every
  class shape's chart, one marked direction of `x₁`'s pencil. **Do not propose a
  counting / matroid / placement-blind route to (OUT)'s hypothesis again**; the
  residual is (OC-8), a whole-graph genericity statement.
- **The measurement itself, over two disjoint pinned pools** ((OC-5)/(OC-6)):
  356/357 and 270/270, conclusion 356/356, `(Λ0d)` failing 0/357. Do not
  re-sample either pool, and **never aggregate them**.
- **The harness rule this pass forced** ((OC-7)), **now DISCHARGED by the
  guard** (2026-08-06, re-baselining round slices S1/S2). It read: *no
  `widened.place_pencil_general`-sampled battery may be quoted as a rate or as
  evidence about a generic chart point* — the in-plane sampler degenerates at
  ≈ 9 % of habitat frames, the degeneracy *implies* `λᵢ = 0`, and
  `star_span_ranks` does not catch it. **The replacement rule, which is
  positive rather than prohibitive:** a battery may be quoted as a rate exactly
  when its acceptance gate is the composite guard `repin.star_generic`
  (closed-star ranks **and** no two hinge lines coinciding at a body), which
  every `w4/` acceptance site now uses. The two deliberate exceptions are
  `outerline --pool` and `--build`, which *measure* the coincidence and say so.
  Quote POOL-G over the **318** coincidence-free-at-the-ends frames, or over
  the **299** the guard itself accepts ((OC-9)). Negatives and existence
  witnesses were unharmed throughout.
- **`--adv`'s `λ`-bearing denominator is `≤ 400`, not 1497** ((K-out) *Step O8*):
  `λ ∝ p⁺`, `λ ∝ q` and `Q(z) = 0` are computed only in the habitat loop; the
  1140 local-strata frames carry no far covector. `C(M) ∈ S` and the span
  histogram *do* run over all 1497. Do not re-quote 1497 for the first three.

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

`flanks.py --degen`, at the 5-chromatic flank, seeds 1..40 (**restated and
re-measured 2026-08-06**, slice S2 — see the correction below): **17** samples
the *composite* guard accepts, **all** at rank 180 = target; **11** rejected by
the closed-star rank test, each short of the target by **exactly** the number
of hubs whose closed star collapsed to a line (deficits 1 and 2 observed);
**10** rejected *only* by the coincident-hinge clause, **every one at the full
target rank 180**; 2 unplaceable. So

- every rank deficit ever seen at these shapes is a sampler artifact, and the
  closed-star rank test is *exact for the rank deficit* on this shape — it
  detects precisely the rank-deficient samples and predicts the deficit;
- a **coordinate** test would not do: `--degen` exhibits samples with two
  zero-coordinate normals whose stars are nonetheless generic, and one with a
  single zero-coordinate normal that collapses. Only the structural rank
  condition classifies correctly. (This is the `plane_basis` precedent
  generalized: the right guard is a rank assert on the sampled *object*, not a
  test on the sampled *parameter*.)

> **CORRECTION (2026-08-06; F13, and one of the four claims it falsified).**
> This step used to say the star-rank guard "is *exact* on this shape — it
> detects precisely the affected samples", and the driver printed the same
> sentence. That is true of the **rank-deficient** samples and false of the
> **sampler-degenerate** ones: **10 of the 38 placeable seeds here** pass the
> closed-star rank test, satisfy all four `IsNondegPencilRealization`
> conjuncts, sit at the **full target rank** — and carry a coincident hinge
> line, i.e. a body with two of its hinges on one line, a free rotor. That is
> §(K-out) (OC-7)'s blind spot, reproduced independently on a different shape,
> in a different driver, at a **26 %** rate rather than (OC-7)'s ≈ 9 %. The
> acceptance site of this module (`flanks.clean_pencil_seed`) now applies the
> composite guard `repin.star_generic`, and `--degen` reports both columns side
> by side so the difference between the two tests stays measured. Nothing in
> half 1 or half 2 moves: a coincidence costs no rank, so every attainment
> witness this section quotes is still an attainment witness — it is now also
> drawn from a strictly cleaner pool.

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
| `--degen` | 4 s | the sampler control at the 5-chromatic flank *(re-measured 2026-08-06, slice S2)*: **17** composite-guard-clean samples, all at the target; **11** rejected by the closed-star rank test, each short by exactly the number of collapsed stars; **10** rejected only by the coincident-hinge clause, all at the FULL target rank — the *Step F4* correction |
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
  recorded (Λ0f) predicts the opposite. Until 2026-08-06 that showed up as
  `lambda.omega_curves`' own coded equivalence **firing as an
  `AssertionError`** here, caught and reported by `outer.py` but not repaired
  (harness-debt item 2). **Repaired by re-baselining slice S3**
  (`notes/scripts/README.md` *The build plan*): `omega_curves` now codes
  (Λ0f′), so at these four points it **accepts** and reports the drop to
  `(2, 2)` with `g₁₄` the single vanishing factor — the criterion and the
  independent `raw_spans` measurement now agree instead of contradicting;
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

**MEASURED, 2026-08-06 — §(K-out) is the canonical home of the answer and it is
not restated here.** `--adv` reports `λ ∝ p⁺` and `λ ∝ q` at **0** hits over its
**habitat leg only** (≤ 400 frames — *not* the 1497 this paragraph used to quote;
see §(K-out) *Step O8*), and it reports **nothing about `λ₁` and `λ₄`
separately**, so (OUT)'s hypothesis had never been evaluated anywhere in the arc.
The new driver mode is `notes/scripts/w4/outerline.py`. Headline of what it
found, in the order that matters: **§(K-out) (OC-3)** — on the pencil chart `C₁`
is confined to the 2-dimensional pencil `L_b` and `dim R₁ = 5` forces
`dim(R₁ ∩ L_b) ≥ 1`, so `{λ₁ = 0}` is **nonempty at every class shape in scope**
and **no counting argument can ever deliver this hypothesis**; **(OC-5)/(OC-6)**
the hypothesis nevertheless holds at 356/357 (POOL-G) and 270/270 (POOL-S),
pointwise; **(OC-4)** the bad line is reached by a legal chart move at a fully
nondegenerate point where the pitch certificate still fires. So (OUT) is
*available and never automatic*, and the sharpest single datum at `k = 4` is
exhibited rather than hunted.

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
| `--adv` frames examined | **1497** (357 real habitat seeds + 1140 local frames) — but see the next row: only the habitat leg carries a `λ` |
| `--adv`: `λ ∝ p⁺` / `λ ∝ q` / `Q(z) = 0` / `C(M) ∈ S` | **0 / 0 / 0 / 0**. **Denominators, corrected 2026-08-06** (§(K-out) *Step O8*): the first three are computed **only in the habitat loop**, so their denominator is `≤ 400` (4 habitats × seeds 200–299; consistent with exactly 357 by `357 + 1140 = 1497`), **not** 1497 — the 1140 local-strata frames carry no far covector at all. `C(M) ∈ S` *is* counted in both loops, so its `0` is over all 1497 |
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
| `outer.py --geom`: the constructed `g₁₄ = 0` point | **4/4 habitats**; `g₁₃, g₂₄ ≠ 0` and all four middle brackets survive; both spans **3 → 2**; still **target-rank, `dim R_a = 1`, `dim V_bc = 3`**. **Repointed 2026-08-06** (re-baselining slice S3, the round's single moved figure): `lambda.omega_curves` used to **raise** at each of the four — it coded the superseded (Λ0f) — and now codes (Λ0f′), so it **accepts** the point and *predicts* the drop, reporting `(span ω⁺, span ω⁻) = (2, 2)` with `(g₁₃, g₁₄, g₂₄) ≠ 0` = `(True, False, True)`. This is (Λ0f′)'s Gram half confirmed by the harness's own criterion rather than by the driver's independent `raw_spans` alone |
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
  asymmetry is relocated rather than evaded. It closes nothing; it is a cheaper,
  far-side, panel-free test at `k = 4` and a bridge to the mixed stratum. **No
  gap-map *status* moves on it** (the (K-wit) row's *what would close it* cell
  gains it as a scoped sufficient condition).
  **Its hypothesis is MEASURED since 2026-08-06 — §(K-out), the canonical home,
  and the driver is `outerline.py`.** Two things that pass changes here, neither
  a status move: the hypothesis is *available* pointwise (356/357 POOL-G,
  270/270 POOL-S, shape-level at every probed (split, companion) pair), **and**
  §(K-out) (OC-3) proves the bad locus `{λ₁ = 0}` is **nonempty on every class
  shape's chart**, so (OUT) is *never automatic* and **no counting argument can
  ever discharge it**. Quote (OUT)'s availability only with that caveat
  attached.
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

*(viii)* **ANSWERED, 2026-08-06 (§(K-out), `outerline.py`): such a frame exists,
is sampled *and* constructible, and the bad locus is nonempty on every class
shape's chart.** The question was for **a length-4-companion frame with `λ₁ = 0`
and `λ₄ = 0`** — *both* outer companion lines relative twists (*Step 5a*) —
which puts the habitat on the bad line `{λ₁ = λ₄ = 0}` of `P(S*)`, makes
**(OUT)** inapplicable there, and leaves only the full ratio test
`p⁺₃λ₂ = p⁺₂λ₃` between it and an escape failure. Three findings, in decreasing
strength:

- **(OC-3), the negative, is the load-bearing one.** `C₁` is confined to the
  2-dimensional pencil `L_b` while `dim R₁ = 5`, so `dim(R₁ ∩ L_b) ≥ 1`: the bad
  locus of the first disjunct is **nonempty at every class shape in scope**, one
  marked direction of `x₁`'s pencil. So the "uniform reason some class shape
  cannot have `C₁ ∈ V_bc`" this item asked for **does not exist**, and no count,
  matroid statement or placement-blind argument can supply one — §2.3's
  prediction, now a proof rather than a prediction.
- **Availability holds pointwise anyway** — (OC-5) 356/357 (POOL-G), (OC-6)
  270/270 over a disjoint POOL-S, with **0** (split, companion) pairs silent at
  every probed seed — and (OUT)'s *conclusion* is separately verified at 356/356.
- **One sampled silent frame** (θ(3,4,5) seed 233) and **four constructed** ones
  ((OC-4), all four habitats, 3 of them with no coincident hinge line): at every
  one the escape still holds by the pitch certificate (`deg_t Q(z(t)) = 4`), so
  (OUT) is silent, not violated.

The residual is **(OC-8)**: class uniformity of (OUT) ⟺ a hard-stratum chart
point with `L_b ⊄ R₁` or `L_c ⊄ R₄` at every class shape — §2.3's wall relocated
onto `H/{e₂,e₃,e₄}` and weakened, **not crossed**. One caveat rides with every
POOL-G rate quoted from that section: **(OC-7)**, a harness defect —
`widened.place_pencil_general`'s in-plane sampler degenerates at 32/357 frames
and that degeneracy *implies* `λᵢ = 0`, uncaught by `star_span_ranks`.

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
sampled object rank/dimension asserted, including `repin.star_generic` as the
`plane_basis` genericity guard; all rng seeded, `PYTHONHASHSEED=0` pinned;
all four modes verified byte-deterministic across repeated runs). Run from the
repo root:

> **RE-BASELINED 2026-08-06 (slice S2), and every figure below is UNCHANGED or
> STRONGER.** `base_seed`'s guard was `star_span_ranks` alone, and its
> docstring's promise *"a seed failing this is rejected, not measured"* was
> false for the free-rotor half of the `plane_basis` artifact ((OC-7), F13);
> it is now the composite `repin.star_generic`. Effect: **the seeds moved**
> (the first clean seed per habitat is a later integer) and **three per-seed
> readings improved to the bound** — `--jac`'s FIXED rank is now **9 at every**
> `k ≥ 4` seed (three contaminated seeds used to report 8), `--far`'s far
> block is now `3(k−3)` at **every** seed (`k = 6` used to report 5 and 7 of
> 9), and `--cap`'s `dim span(P)` at `K4` dbl-subdiv is now `[6]`, not
> `[5, 6]`. So the *table below is untouched*, and what changed is that
> "attained at every habitat" is now "attained at every **seed**": the
> exceptions were the contaminated draws.

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
- **Settled — refuted; the verdict is field-neutral, its original `ℝ` argument
  is not.** **σ-equivariant seed recipes are dead**: over
  `ℝ` with
  the project's polarity there is *no* σ-fixed pencil configuration at all, and
  for a **null** correlation the fixed locus is degenerate — it
  forces every hinge line into a linear line complex and produces a self-stress
  per cycle (*Step σ6*, measured deficit exactly 1 at 6/6 on tight `C₆`). This
  is `notes/Pencil-strategy.md` §2.4's *"degenerate enough to compute, and you
  break the thing you're computing"* wall, now with a proof. **Over `ℂ̄` the `ℝ`
  half REVERSES** — σ-fixed configurations exist and are *nondegenerate* at the
  Tay target (§(K-clos) (AC-2)/(AC-3)) — **and the verdict survives anyway**, on
  the field-neutral §(K-clos) (AC-5): at a σ-fixed seed route σ *is* route A.
- **CANDIDATE, offered for adjudication — not asserted as settled.**
  **Route σ**, a third escape route obtained by running route A at the dual
  seed `σu`. If the derivation below is right it closes (K-tight) on the hard
  stratum, *length-free*. It rests on **four named obligations** (*Step σ5*),
  the first of which — σ-nondegeneracy of the transported seed — was recorded
  as *observed 47/47, not proven* and is now **verified in both directions**
  (2026-08-05, `sigma.py --hunt`): the dual conjuncts **CAN fail at a
  hard-stratum, primally nondegenerate seed** (45 constructed witnesses), so
  the 47/47 was genericity and never an implication; but only **two** of the
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
NOT settled here — and SETTLED SINCE, in §(K-clos): read its (AC-1) (the
polarity generalizes; the general-`K` transport is landed) and (AC-7) (`ℂ̄`
dominates `ℝ` within characteristic 0) before quoting this subsection.** This whole section is
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
  isotropic vectors both arguments simply stop, and **§(K-clos) has now settled
  what happens to their conclusions: both REVERSE** — self-conjugacy is the
  defining condition of the σ-fixed grid locus ((AC-2)), which is non-empty and
  nondegenerate at the Tay target ((AC-3)). Do not re-cite these two as
  refutations over a general field; the *verdict* they were supporting
  ("σ-equivariant seed recipes are dead") survives on the field-neutral (AC-5).

**Does the polarity generalize past `ℝ`? SETTLED — YES, and the bill is one
section** (§(K-clos) (AC-1), 2026-08-06; source-level, **not compiler-checked**).
The reading recorded here was right, and §(K-clos) adds the piece it was
missing: **the general-`K` transport is already in tree** as
`BodyHingeFramework.mapSupport` (`Molecular/GenericLift/HingeGeneric.lean:462`,
with its rank lemma `finrank_span_rigidityRows_mapSupport` at `:544`) — the same
construction as the `ℝ`-fixed `BodyHingeFramework.mapExtensor` route σ's
statement is phrased through, at the general field. So **nobody should budget
for generalizing `Molecular/Molecule/ProjectiveInvariance.lean`'s 19-declaration
`mapExtensor` API**: phrase the general-`K` statement through `mapSupport` and
that file needs no change at all. The recorded reading, unchanged:
both ingredients of `screwComplementIso`
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
**No generalization is carried out here or there** — §(K-clos) (AC-1) prices it
(one `def` plus four theorems restated with `mapSupport`) and flags the one
instrument it could not use: a ~20-line typecheck spike.

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
`λ ∝ p⁺` and finds none; and at all 47 seeds sampled here routes A/B *already*
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

> **(σ4)** *(exact; 47/47 seeds)* Write `p̂_w` for a body's homogeneous point and
> `ν_w` for its homogeneous panel normal. Then for every edge `uw`,
> `span(ν_u, ν_w) = span(p̂_u, p̂_w)^⊥`, i.e. `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)`.
> **So `σ` is: replace every body's point by its own panel normal.** The
> incidences `ν_w · p̂_w = 0` and `ν_u · p̂_w = 0` (`w` a neighbour of `u`) are
> exactly what makes this work, and they *are* the pencil conditions.

Consequently `σu` is a pencil realization of the same `G′`, with the same
hub/non-hub combinatorics, and `rank R(σu) = rank R(u)` (transport along a
linear automorphism). Verified exactly: `rank`, `s₀`, `dim R_a` agree at 47/47.

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
| `r` (the transmitted boundary load) | `σ(r) = ★r` (verified 47/47) |
| `dim R_a`, `s₀`, target rank | unchanged (verified 47/47) |

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

> **(σ6)** *(exact; verified as an equivalence at 47/47 seeds)*
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
`crit_B(σu) ⟺ r ⊥̸ α_{pt(c)}` at 47/47 alongside the `b`-end one.

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

Driver `notes/scripts/w4/sigma.py` (tracked, new this pass). **47** hard-stratum
seeds across two splits of the tight control (double-subdivided `K4`,
`|V| = 16`, target 90 / `G′` target 84): seeds 440–479 at chain 0 (23 valid) and
500–529 at chain 1 (24 valid), all with `s₀ = 0`, `dim R_a = 1`. Every figure is
`n/n` over that pool.

> **POOL RE-BASELINED 2026-08-06 — 63 → 47, and every `n/n` below survives
> verbatim.** Slice S2 of the harness re-baselining round adopted the composite
> genericity guard `repin.star_generic` at `sigma.hard_stratum_seed`
> (`notes/scripts/README.md` *Harness debt* item 4): **16 of the former 63
> seeds carried a coincident hinge line** — a body with two of its hinge lines
> equal, which the closed-star rank test alone passes and no
> `IsNondegPencilRealization` conjunct excludes ((OC-7)). The pool is now
> `23 + 24 = 47`, strictly cleaner, and **not one check changed its verdict**:
> every row of the table below reads `47/47` where it read `63/63`, and the
> `--hunt` counts moved the same way (H1 `52 + 55` → `45 + 47`, H2 `27 + 26 =
> 53` → `22 + 23 = 45`; H4's 35 and H5's 39 are unchanged). The numerals in
> this section are the **new** ones throughout; the three places a `63/63`
> survives are explicitly about the *2026-08-05 defect* of quoting an aggregate
> across inconsistent pools (F11), not about this pool.

| check | mode | result |
|---|---|---|
| homogeneous pencil data `ν_w·p̂_w = 0`, `ν_u·p̂_w = 0` on edges | `--transport` V0 | 47/47 |
| **(σ4)** `ν_u ∧ ν_w ∝ ⋆(p̂_u ∧ p̂_w)` on every edge | V1 | 47/47 |
| `rank R(σu) = ` target, `dim R_a`, `s₀` agree with `u` | V2 | 47/47 |
| `r(σu) ∝ ★r(u)`, and **(σ6)** `crit_A(σu) ⟺ r(u) ⊥̸ α_{pt(b)}` (+ the `c` mirror) | V3 | 47/47 |
| **`dim(β_{Π b} + β_{Π c} + α_{pt b}) = 6`** — *genericity, not necessity: see the correction below* | V4 | 47/47 |
| route A at `σu` reaches target rank for `G`; its pullback into `u`'s frame is the `pt(v) = pt(b)` family | V5 | 47/47 |
| `dim(α_{pt b} + α_{pt c}) = 5`, perp generated by `★C(bc)` | `--adv` A | 47/47 |
| `dim(β_{Π b} + β_{Π c}) = 5`, perp `★C(M)`; `C(M) ∦ C(bc)` | `--adv` B | 47/47 |
| the pullback is a legal pencil realization (nonzero hinges, incidences, target rank) | `--adv` D | 47/47 |
| `predA` (= `r ⊥̸ α_{pt b}`) true; **`predAfalse = 0/47`** | `--adv` C | 47/47 |
| routes A/B at `u` *already* escape | `--adv` | 47/47 |
| `u` satisfies all four `IsNondegPencilRealization` conjuncts | `--nondeg` | 47/47 |
| **`σu` satisfies all four conjuncts** (each reported separately) | `--nondeg` | 47/47 — *genericity, not an implication: `--hunt` H2 breaks conjuncts 2 and 4 by construction* |
| **the route-σ witness is a nondegenerate pencil realization of `G`** | `--nondeg` | 47/47 |
| the witness satisfies the chart's binding point equations | `--nondeg` | 47/47 |

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
in its header and deliberately **disjoint from the pinned 47**: random
1000–1059, coplanar-chain 2000–2029 and (Λ0d) 3000–3019, *per split*, over the
same two tight-control splits. **No figure below is over the pinned pool and
no *Step σ4* figure is over these.** (The discipline is explicit because the
pass that opened this section first reported its "63/63" as an aggregate across
scratch drivers running *different* pools, and only its landing dispatch caught
it before the figure was recorded. Here the separation is structural: `--hunt`
never touches `CHAIN0_SEEDS`/`CHAIN1_SEEDS` and the other four modes never touch
the hunt pools.)

| leg | what it establishes | result |
|---|---|---|
| **H0** the shape's *conjunct arithmetic* | no hub–hub edge; `closedHubNbhd v = {v}` at every hub; `closedHubNbhd v ⊆ closedNbhd v` everywhere | asserted at both splits |
| **H1** the fresh random pool | 92 fresh hard-stratum seeds (45 + 47), all four dual conjuncts at `σu` | **0 failures** — random draws never reach the locus |
| **H2** the **constructive** failure | a legal, hard-stratum, **primally nondegenerate** placement whose dual conjuncts **2 and 4 FAIL** at `σu` (1 and 3 hold) | **45/45** (22 + 23), exact pattern `(T, F, T, F)` |
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
> "`dim(β_{Π b} + β_{Π c} + α_{pt b}) = 6` at 47/47" is a **genericity**
> observation. H4 exhibits 35 hard-stratum, primally-nondegenerate
> configurations of the *same* two splits where that span is **5**. The *Step
> σ3* theorem survives — it now quotes (σ7)'s disjunction instead of the
> `b`-form side condition — but no reading of V4 as "the span is forced" is
> licensed. The same caution applies to *Step σ5* obligation 1's "observed
> 47/47": the observation was true and the implication it suggested is
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
     `--hunt` H0, and observed to hold at all 45 constructed failures.
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
     `σu` (the coplanar-chain degeneration, *Step σ4b*). So the 47/47
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
   made here — but it is no longer a symmetric one. **§(K-clos) (AC-7): `hK`
   over `ℂ̄` implies `hK` over every infinite characteristic-0 field, and the
   converse fails**, so "instantiate at `ℝ`" is the **narrowest** available
   option, not merely *a* narrowing; and **§(K-clos) (AC-1)** prices the
   general-`K` polarity at one section with every input already landed
   (`mapSupport`). The residual content of `[Infinite K]` after a
   characteristic-0 proof is **positive characteristic only**.
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
   in the pool (`predAfalse = 0/47`), so the **failure direction** of (σ6) is
   **unwitnessed**.
4. **The branch route σ closes has NEVER been observed nonempty.**
   `lambda.py --adv` hunts `λ ∝ p⁺` (= `★r ∥ C(M)`) and finds none; at all 47
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
- **A strictly σ-equivariant seed recipe is a DEAD END — and since §(K-clos) the
  reason is field-neutral, not `ℝ`-definiteness.**
  A σ-fixed pencil configuration needs `normal_v ∝ point_v`; the landed
  incidence conjunct `point v ⬝ᵥ normal v = 0` then forces
  `point_v · point_v = 0`, so **over `ℝ` with the project's (definite) polarity
  there are no σ-fixed configurations at all**. Over a field with isotropic
  vectors they **do** exist: a *symmetric* correlation
  forces every body point onto the fixed quadric and every hinge line to lie
  **on** that quadric (a union of two one-parameter rulings) — that confinement
  is exactly §(K-clos) (AC-2), and it is **not** a degeneracy. §(K-clos) (AC-3)
  exhibits σ-fixed configurations satisfying all four nondegeneracy conjuncts at
  the Tay target, so the *"worse than empty, it is degenerate"* framing this
  bullet used to attach to the **symmetric** branch is **REFUTED**; what earned
  that framing is the **null** branch, and only it. A *null*
  (symplectic) correlation `J` makes the incidence automatic and forces every
  hinge line into the **linear line complex** of `J`, whence `ω_e := c_e ★S` is
  a self-stress for every cycle-space flow `c` (`S` = the complex's screw), so
  the rank drops by at least the cycle rank. Measured on `C₆` (tight,
  `5|E| = 30 = 6(|V|−1)`, cycle rank 1): **deficit exactly 1 at 6/6**
  linear-complex placements (`sigma.py --fixed`). **The verdict stands on
  §(K-clos) (AC-5)**: at a σ-fixed seed `σu = u`, so route σ's uniform-failure
  criterion and route A's *coincide* as subspace conditions — an equivariant
  recipe would buy obligation 1 for free and **delete route σ in the same
  stroke**. *Route σ does not use
  equivariance* — it applies `σ` once to move to a **different** seed, which is
  exactly why it escapes this wall; (AC-5) upgrades that remark from an aside to
  the reason.
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
§1 primitives from siblings; every sampled placement guarded by the composite
`repin.star_generic` (`flanks.star_span_ranks` alone until 2026-08-06, slice
S2) and every span's dimension asserted; all rng seeded;
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
`OK`; the pool size `47` is itself asserted, so a sampler change that silently
moved the pool fails the run. **`--hunt` runs on its own three pools** (*Step
σ4b*), never on the pinned pool, and asserts each of H0–H5's counters against its own
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
- **σ-equivariant seed recipes: REFUTED** (*Step σ6*) — the verdict stands, but
  since 2026-08-06 **on §(K-clos) (AC-5)** (at a σ-fixed seed route σ *is* route
  A), not on `ℝ`-definiteness. The `C₆` witness still carries the **null**-
  correlation half; the *symmetric* half's "degenerate" is refuted by (AC-3).
- **"the dual conjuncts hold automatically at `σu`": REFUTED** (*Step σ4b* H2,
  45 constructed hard-stratum primally-nondegenerate witnesses). The 47/47 of
  *Step σ4* was genericity.
- **Route σ as a closure of (K-tight) on the hard stratum: CANDIDATE, offered
  for adjudication — and, as landed machinery, an `ℝ`-only one.** Obligation 1
  is still the single crux, now **sized**: two of its four conjuncts are free
  **at `ℝ`**, one is the already-named (Λ0d), and the steering repair is
  exhibited exactly. Obligations 2–4 bound the scope and the claim's strength.
  **No gap-map status moves.**
- **Field scope: SETTLED by §(K-clos)** (2026-08-06), where it was recorded here
  as open. `σ` is still `ℝ`-only *in tree* and `hK` is still consumed at general
  `[Infinite K]`, but the polarity **does** generalize — bookkeeping, one
  section, transport already landed ((AC-1)) — so (σ1)–(σ6), route σ and the
  conjunct-1 freeness all port; (σ7) and the span linear algebra were
  field-neutral outright; and *Step σ1(a)* and *Step σ6*'s two refutations
  **reverse** over `ℂ̄` ((AC-2)/(AC-3)) without moving the verdict they support
  ((AC-5)). Field choice is no longer symmetric: `ℝ` is the **narrowest** option
  ((AC-7)).

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
*(vi)* **ANSWERED, 2026-08-06 — §(K-clos).** The field question was recorded
here as open in all three of its parts, and all three are now settled. **The
polarity generalizes** ((AC-1)): bookkeeping, one section, and the general-`K`
transport is already landed as `mapSupport` — so route σ, conjunct-1 freeness
and (σ1)–(σ6) port, which is what obligation 1 needs. **The σ-fixed
configurations this item guessed "might well exist" DO exist** ((AC-2)) and are
nondegenerate at the Tay target ((AC-3)), so *Step σ1(a)* and *Step σ6*'s two
refutations **reverse** rather than merely failing to port — **but they do
NOT revive the σ-equivariant-recipe route**, because at a σ-fixed seed route σ
collapses onto route A ((AC-5)). And the field choice is **not** symmetric:
`hK` over `ℂ̄` implies `hK` over every infinite characteristic-0 field with the
converse false ((AC-7)), so instantiating at `ℝ` is the narrowest option, and
the residual content of `[Infinite K]` is positive characteristic. Nothing here
is left for a successor except the ~20-line typecheck spike (AC-1) names.

## §(K-clos) — the polarity over an algebraically closed field: generalizing it is **bookkeeping**, one of §(K-σ)'s two `ℝ`-refutations **REVERSES**, the route it buried stays buried **for a new and field-neutral reason**, and `hK` splits cleanly into *characteristic 0* (all of it equivalent to the `ℂ̄` case) and *characteristic p*

Read against §(K-σ) — this section extends its *Field scope* three-way
classification rather than restating it, and corrects it in two places. Notation
inherited from §(K-Λ) *Standing notation*; `⋆` is the project's polarity
`screwComplementIso` (`Molecular/Molecule/Duality.lean:69`), `Q ⊂ P³` its fixed
quadric `{x ⬝ᵥ x = 0}`, and `Λ²₊`, `Λ²₋` the `±1` eigenspaces of `⋆` on `Λ²K⁴`.

**Status, stated before the mathematics.**

- **Settled — the polarity generalizes, and the cost is one section.** **(AC-1)**.
  Nothing is obstructed, characteristic 2 included *for the definition*. The
  general-`K` **transport** the route needs is not a new object either: it is
  already in tree as `BodyHingeFramework.mapSupport`
  (`Molecular/GenericLift/HingeGeneric.lean:462`), with its rank lemma
  (`:544`). Source-verified; **no compiler witness** was taken (the dispatch
  carried a no-Lean constraint), and a ~20-line typecheck spike would settle it
  outright.
- **Settled — one of §(K-σ)'s two `ℝ`-refutations REVERSES.** **(AC-2)**,
  **(AC-3)**. Over `ℂ̄` σ-fixed pencil configurations **exist**; they are exactly
  the `P¹ × P¹` grids on `Q`; and — refuting the *degeneracy* framing §(K-σ)
  *Step σ6* attaches to them — they are **nondegenerate** (all four
  `IsNondegPencilRealization` conjuncts, every star of rank 3) and **reach the
  Tay target**, at all **15 tight** shapes of the pinned pool (all eight
  §(K-flank) flank shapes among them) and at the (K-res) inhabitant `W19`,
  which is rigid but *not* count-tight.
- **Settled — but §(K-σ)'s VERDICT survives, on a new and field-neutral
  argument.** **(AC-5)**: at a σ-fixed seed `σu = u`, so **route σ *is* route A**
  — the two uniform-failure criteria coincide as subspace conditions. A
  σ-equivariant seed recipe buys route σ's obligation 1 for free and deletes
  route σ in the same stroke. *"σ-equivariant seed recipes are dead" stands; its
  stated reason (`ℝ`-definiteness) does not port and is replaced by this one.*
- **REFUTED as a class statement; OPEN only on the tight stratum.** **(AC-6)**:
  the same grids are a **combinatorial recipe** — a ruling 2-colouring of `E(G)`
  — for target-rank nondegenerate pencil realizations. Over a **pinned 21-shape
  pool** it reaches the Tay target at **15/15 tight** shapes (all eight §(K-flank)
  flank shapes among them) and at `W19`, and **fails at three**. One of the three,
  the bare odd cycle **`C11`**, satisfies *every* hypothesis `hK` carries, so the
  class statement is **refuted, not open** — with the mechanism identified and
  complete: *no admissible colouring exists iff `G` has a bare odd cycle
  component*, a **parity** obstruction, which a tight shape cannot have. The other
  two misses are at shapes outside `hK`'s habitat, and one of them is *correct
  behaviour* (the shape has no nondegenerate pencil realization at all). What is
  left open is the narrow question — does the recipe reach the target at every
  **tight** shape — and only that; if it did it would discharge `hK` there
  **directly, with no escape route at all**. This arc's record says the base rate
  for such a question is "no" (`Pencil-strategy.md` §2.3).
- **Settled — the field-generality of `hK` factors.** **(AC-7)**: `hK` over
  `ℂ̄` **implies** `hK` over every infinite field of characteristic 0, `ℝ` and
  `ℚ` included. Working over `ℂ̄` is therefore **not** a weakening; it is the
  strongest characteristic-0 instance. The residual content of the headline's
  `[Infinite K]` is **positive characteristic only**.
- **Settled — characteristic 2 is a genuine exception, but only to the
  *geometry*.** **(AC-8)**: `x ⬝ᵥ x = (∑ xᵢ)²` there, so `Q` degenerates to a
  double plane, and `⋆` is unipotent rather than diagonalizable, so `Λ²` does
  not split. **(AC-1)** is unaffected; **(AC-2)**–**(AC-6)** all need `char ≠ 2`.

### Step Z0 — the question, and what "over `ℂ̄`" is modelled by

Three sub-questions, from the dispatch: does the polarity generalize; do
§(K-σ)'s two `ℝ`-refutations reverse; and is the conjecture easier over `ℂ̄`.

**The model.** All computation is over the **Gaussian rationals `ℚ(i) ⊂ ℂ`**,
the smallest extension of `ℚ` in which `∑ xᵢ² = 0` has a nonzero solution — and
that single fact is the *whole* difference the dispatch is about. The driver uses
the harness's **own** `⋆` (`repin.hodge_star`), its **own** rigidity-row builder
(`hybrid_gates.build_rigidity_extensors`) and its **own** nondegeneracy checker
(`flanks.nondeg_conjuncts`), unchanged; only the scalar field is enlarged
(`closure.py`'s `Gauss`, exact, no floating point). An **existence** statement
verified over `ℚ(i)` is an existence statement over `ℂ̄`; a **non**-existence
statement over `ℚ(i)` is not, and none is claimed.

### Step Z1 — (AC-1): the polarity generalizes; the general-`K` transport is already landed

> **(AC-1)** *(proven-informally from the landed source; no compiler witness).*
> `screwComplementIso` has a verbatim general-`K` companion. Both ingredients
> are already field-general in tree, all the helper inputs of the four
> `ℝ`-fixed theorems are field-general, and the missing transport is **not**
> missing.

Verified declaration by declaration (each opened, not taken from a docstring):

| ingredient | field | source |
|---|---|---|
| `ScrewSpace (K) [Field K] (k)` | general | `Molecular/RigidityMatrix/Basic.lean:117` |
| `ScrewSpace.equivExteriorPower (K) [Field K] (k)` | general | `…/Basic.lean:185` |
| `complementIso {j} (hj : j ≤ k+2)` | general, **no characteristic hypothesis** | `Molecular/Meet.lean:479` |
| `structure BodyHingeFramework (K) [Field K] (k) (α β)` | general | `…/Basic.lean:310` |
| `BodyHingeFramework.mapSupport (M : ScrewSpace K k ≃ₗ[K] ScrewSpace K k)` | **general** | `Molecular/GenericLift/HingeGeneric.lean:462` |
| `finrank_span_rigidityRows_mapSupport` | **general** | `…/HingeGeneric.lean:544` |
| `mem_span_of_dotProduct_perp_pair` | general | `Pencil/Statement.lean:133` |
| `dotProduct_eq_zero_of_mem_span` | general | `Pencil/Statement.lean:114` |
| `exists_extensor_eq_panelSupportExtensor` | general | `AlgebraicInduction/PanelLayer.lean:649` |
| `panelSupportExtensor`, `panelSupportExtensor_ne_zero_iff`, `normalsJoin` | general | `PanelLayer.lean:233, 244, 67` |
| `extensor_ne_zero_iff_linearIndependent` | general | `Molecular/Extensor.lean:343` |
| `finrank_toDualPerp_pair_eq` | general | `Molecular/Meet.lean:1562` |

**(a) The definition is a writing choice.** `screwComplementIso :=
equivExteriorPower ≪≫ₗ complementIso ≪≫ₗ equivExteriorPower.symm`; every factor
is `[Field K]`-general, so the composite typechecks verbatim with `K` for `ℝ`.
**Nothing in it uses definiteness** — `complementIso` is built from the volume
form `screwAlgebraTopEquiv` and the basis pairing `Pi.basisFun.toDual`
(`Meet.lean:88`), and the pairing is nondegenerate over **any** field because its
Gram matrix is the identity. Definiteness is used nowhere in the construction and
is not available over `ℂ̄`; only nondegeneracy is, and only nondegeneracy is
needed.

**(b) Characteristic 2 does not obstruct the definition.** `complementIso` is
landed at `[Field K]` with **no** characteristic hypothesis, so it compiles in
char 2; `⋆² = (−1)^{p(N−p)} = (−1)^4 = +1` at `p = 2`, `N = 4` in every
characteristic. What char 2 *does* break is the geometry — *Step Z8*.

**(c) The transport is already general — this corrects §(K-σ)'s pricing.**
§(K-σ) *Field scope* counts "exactly five declarations in `Pencil/` fix `ℝ`",
which is **correct as stated** (`Pencil/Statement.lean:166, 185, 216, 258, 665`;
`Pencil/Arms.lean`'s only `ℝ` is in prose — re-verified this pass). But the
*machinery* those theorems are phrased in — `BodyHingeFramework.mapExtensor` and
its 19-declaration API in `Molecular/Molecule/ProjectiveInvariance.lean` — is
**also `ℝ`-fixed**, and route σ's statement is literally about
`F.mapExtensor screwComplementIso`. That looks like a much larger bill than "one
section". **It is not**, because `mapExtensor` and `mapSupport` are the *same*
construction at two field generalities (`mapSupport F M` has
`supportExtensor e := M (F.supportExtensor e)`, exactly `mapExtensor`'s field),
and `mapSupport` is general-`K` **with its rank lemma**. So the general-`K`
statement is phrased through `mapSupport` and `ProjectiveInvariance.lean` needs
no generalization at all.

**(d) The precedent §(K-σ) cites is exactly right, and stronger than it says.**
`Pencil/Arms.lean`'s W3-L4 section header records the same mismatch verbatim and
supplies "the `K`-level transport, built on the change-of-screw-coordinates
machinery (`BodyHingeFramework.screwEquivOfLinearEquiv`, `mapSupport`)". Note the
scope: `screwEquivOfLinearEquiv g` covers **collineations** (automorphisms of
`K⁴`); the polarity is a **correlation** and is *not* of that form, so the W3-L4
section does not already contain the polarity. `mapSupport` does cover it.

**Net bill for a general-`K` polarity:** one `def` (`Duality.lean:69`), one
extensor-level bridge (`Statement.lean:166`), two predicate transports (`:185`,
`:216`), and one self-duality theorem (`:258`) restated with `mapSupport` in
place of `mapExtensor`. Every input is already general. **No new mathematics.**

*Confidence: proven-informally, source-level. Not compiler-checked.*
*What would change this: a typecheck spike that fails — most plausibly on an
instance-resolution or `rfl` step in `screwComplementIso_lineExtensor` /
`screwComplementIso_mk_extensor`, both of which close by `rfl` at `ℝ`. This is
the one claim in this section whose right instrument is a 20-line scratch
`.lean`, and the dispatch's no-Lean constraint is why it was not taken.*

### Step Z2 — (AC-2): the σ-fixed locus over `ℂ̄` is the `P¹ × P¹` grid on the fixed quadric

A pencil configuration is **σ-fixed** in the sense §(K-σ) *Step σ6* uses:
`normal_v ∝ point_v` for every body (projectively fixed — the hinge extensors are
then `⋆`-eigenvectors up to sign, which is all the predicate and the rank see).

> **(AC-2)** *(proven; driver leg `--fixed` AC-C0)* Over a field with isotropic
> vectors, a σ-fixed pencil configuration is exactly the following. Every body
> point lies on the fixed quadric `Q = {x ⬝ᵥ x = 0}`; adjacent body points are
> conjugate; hence **every hinge line lies on `Q`**. Writing `Q ≅ P¹ × P¹` by
> its two rulings and `p(s:t ; u:v)` for the corresponding point,
>
> `p ⬝ᵥ p′ = 2 · (s t′ − s′ t) · (u v′ − u′ v)`,
>
> so **two points of `Q` are conjugate iff they share a ruling parameter**. A
> σ-fixed pencil configuration is therefore a map `V(G) → P¹ × P¹` in which
> adjacent bodies agree in exactly one coordinate: a **grid**. Each edge is
> labelled by the ruling its hinge lies in, and — the reason this is a *finite*
> combinatorial object — the hinge screw of a ruling-A edge lies in `Λ²₊` and of
> a ruling-B edge in `Λ²₋`.

*Proof of the last clause.* A line `ℓ ⊂ P³` lies on `Q` iff `ℓ ⊆ ℓ^⊥`, and
`dim ℓ = dim ℓ^⊥ = 2`, so iff `ℓ = ℓ^⊥ = σ(ℓ)`: **the lines on `Q` are exactly
the `⋆`-fixed points of the Klein quadric**, i.e. the decomposable vectors of
`Λ²₊ ∪ Λ²₋`. Each eigenspace is 3-dimensional and `ℚ`-rational, they are
`⬝ᵥ`-orthogonal to each other (`⟨x,⋆y⟩ = ⟨⋆x,y⟩` and `⋆x = x`, `⋆y = −y` give
`2⟨x,y⟩ = 0`), and on each the ambient form restricts to `2(α²+β²+γ²)` — a smooth
conic, **empty over `ℝ`** (definiteness: this is *Step σ1(a)*'s and *Step σ6*'s
argument, seen from the Plücker side) and a `P¹` over `ℚ(i)`. ∎

**So §(K-σ) *Step σ6*'s structural sentence is exactly right and its scope is now
sharp**: "a *symmetric* correlation forces every body point onto the fixed
quadric and every hinge line to lie on that quadric (a union of two
one-parameter rulings)". That is (AC-2). What *Step σ6* got wrong is what
follows from it — see *Step Z3*.

**Two `ℝ`-verdicts of §(K-σ), re-classified.** *Step σ1(a)*'s refutation of the
**literal** intertwining question also reverses: it needs `pt(a)` self-conjugate,
i.e. `pt(a) ∈ Q`, which over `ℝ` forces `pt(a) = 0` and over `ℂ̄` is simply a
codimension-1 condition on that body, satisfied by **every** body of a σ-fixed
configuration. So over `ℂ̄` the literal intertwining is not impossible; it is the
defining condition of the grid locus. The **covariant** statement *Step σ1(b)* is
field-neutral and unaffected.

### Step Z3 — (AC-3): the grids are nondegenerate and reach the Tay target — *Step σ6*'s "degenerate" is REFUTED for the symmetric correlation

§(K-σ) *Step σ6* priced the σ-fixed locus as *"worse than empty, it is
degenerate"*. For the **null** (symplectic) correlation that is proven there
(every hinge in a linear line complex, a self-stress per cycle, measured deficit
exactly 1 at 6/6 on tight `C₆`). For the **symmetric** correlation — which is the
project's polarity, and the only one at issue over `ℂ̄` — the degeneracy was
asserted, never measured. It is **false**.

> **(AC-3)** *(exact, over `ℚ(i)`; driver leg `--fixed`)* At the tight control
> `ds-K4` (`|V| = 16`, `|E| = 18`, target 90) there is a σ-fixed pencil
> configuration that satisfies **all four `IsNondegPencilRealization` conjuncts**
> (checked by the canonical `flanks.nondeg_conjuncts`), has **every closed-star
> rank 3**, and has body-hinge rank **exactly 90 = the Tay target**. Twelve of
> the 64 ruling colourings do. *(The parenthetical "the `plane_basis`
> genericity guard" stood after "closed-star rank 3" until 2026-08-06; it is
> one of the four claims F13 falsified, and (AC-9) below is what it was
> hiding.)*

The confinement of (AC-2) is real; it simply **costs nothing**. Intuition for
why: the pencil condition *asks* each body's hinges to be concurrent and coplanar,
and at a point of `Q` the tangent plane `T_pQ = p^⊥` meets `Q` in exactly the two
ruling lines through `p` — so the pencil conditions are satisfied **by
construction**, not by accident. That is the same fact that makes the locus
non-empty and the same fact that caps each body at two distinct hinge directions.

**And that cap has a consequence nobody drew until the guard was adopted.**

> **(AC-9)** *(new 2026-08-06, slice S2; proven from the cap above, measured at
> every configuration `closure.py` builds)* **At a σ-fixed pencil configuration,
> every body of degree `≥ 3` carries a COINCIDENT HINGE LINE** — two of its
> hinges are projectively the same line, so the body is a free rotor about it.
> *Proof:* at `p ∈ Q` the tangent plane meets `Q` in exactly **two** lines
> through `p`, and every hinge at that body is one of them; a body of degree
> `≥ 3` has at least three hinges, so by pigeonhole two coincide. *Measured:*
> at the (AC-3) witness the coincidences are exactly one per hub —
> `(0, 4, 6)`, `(1, 12, 5)`, `(2, 11, 14)`, `(3, 15, 9)` — and over `--sweep`'s
> exhaustive 64 colourings the composite guard `repin.star_generic` accepts
> **0 of 64**, asserted in the driver.

What (AC-9) does and does not do. It does **not** touch (AC-3): all four
`IsNondegPencilRealization` conjuncts still hold, the closed-star ranks are
still 3, and the rank is still the Tay target — and those are the predicates
`hK` is quantified over, so *Step σ6*'s "the fixed locus is degenerate" stays
**refuted as a statement about that predicate**. What it does is tell you what
"nondegenerate" is worth here: the σ-fixed witnesses are **never generic** in
the harness's composite sense, so no rate, no genericity argument and no
"a σ-fixed seed is a typical seed" reading may be built on them — and *Step
σ6*'s instinct was right in a sense it did not state, namely the free-rotor
one, which costs no rank and violates no conjunct. It also explains, without
any appeal to sampling, why (AC-6) fails as a class statement whenever a body
has degree `≥ 3`.

### Step Z4 — (AC-4): the `⋆`-eigen decoupling, and the three conditions target rank forces

> **(AC-4)** *(proven, and driver-tested as an equality at every sampled
> configuration)* At a σ-fixed configuration the body-hinge rigidity matrix
> **decouples** over `Λ²₊ ⊕ Λ²₋` into two independent systems on `3|V|`
> variables each:
> `rank = rank₊ + rank₋`, with `rankₑ ≤ 3|V| − 3`.
> For an edge whose hinge lies in `Λ²₊`, the relative-screw condition splits into
> **3** equations in the `−` block (`m_u = m_w` there) and **2** in the `+` block
> (`m_u − m_w` parallel to the hinge); and symmetrically. Consequently, at a
> **tight** shape (`5|E| = 6(|V|−1)`), reaching the target forces all three of
>
> (i) **balance** `|E_A| = |E_B| = |E|/2`;
> (ii) **both ruling classes are forests** (a cycle in one class makes 3
> equations of the *other* block dependent);
> (iii) **both blocks isostatic** at `3|V| − 3`.
>
> and, separately, `IsNondegPencilRealization`'s conjunct 4 at a degree-2 body
> forces the two colours at that body to **differ** — so the colouring
> **alternates along every branch**, i.e. it is one free bit per branch.

*Why (i).* Summing the two blocks' equation counts gives `5|E|`, which at a tight
shape equals `6|V| − 6` exactly, so both blocks must be at their maxima with
**zero slack**: `2|E_A| + 3|E_B| = 3|E_A| + 2|E_B| = 3|V| − 3`, whence
`|E_A| = |E_B|`. *Why the alternation.* At a degree-2 body `v` with neighbours
`u, w`, if both edges took the same ruling then `pt(v), pt(u), pt(w)` would be
three points of one line — `LinearIndepOn point (closedNbhd v)`
(`Motive.lean:115`, imposed exactly at non-hubs) fails. *Why star rank 3 at a
hub.* A hub's neighbours lie on the ≤ 2 ruling lines through it; if all its edges
take one ruling, the whole closed star is collinear and the panel is not
determined.

Driver: at `ds-K4`, all **64** colourings satisfy `rank = rank₊ + rank₋`; every
target-rank colouring is balanced with both classes forests and both blocks at
`3|V| − 3 = 45`; every unbalanced colouring falls short. The identity
`rank = rank₊ + rank₋` is a *test*, not a restatement: the two blocks are built
from the eigen-structure and the full matrix from
`hybrid_gates.build_rigidity_extensors`, independently.

**Note the shape of the residual system.** Solving the `E_B` equations out of the
`+` block contracts every `E_B`-component to one node and leaves a **direction
network** in `K³` — place the `E_B`-components as points so that, for each
`E_A`-component, the points it meets are collinear in that component's ruling
direction. That is a 3-dimensional parallel-drawing / incidence system, with the
directions constrained to a conic exactly as body-hinge screws are constrained to
the Klein quadric in `K⁶`. Its generic combinatorics is the natural target of a
uniformity proof and is **not attempted here**.

### Step Z5 — (AC-5): at a σ-fixed seed **route σ IS route A** — the field-neutral replacement for *Step σ6*'s `ℝ` kill

This is the answer to the dispatch's sub-question 2 as posed ("would it revive
the σ-equivariant-recipe route §(K-σ) buried?"), and the answer is **no for route
σ**, for a reason that has nothing to do with the field.

> **(AC-5)** *(proven; driver leg `--collapse`, 32/32)* Let `u` be a σ-fixed
> hard-stratum seed. Then `σu = u`, and for **every** body `b`
>
> `r ⊥ Λ²Π̂(b)` **⟺** `r ⊥ α_{pt(b)}` as conditions on the residual load `r`,
>
> i.e. route A's uniform-failure criterion at `b` (§(K-tight) *Step 2.4*) and
> route σ's (§(K-σ) (σ6)) **coincide**. Route σ contributes no escape direction
> route A does not already contribute.

*Proof.* σ-fixedness gives `Π(b) = pt(b)^⊥`, hence `Λ²Π̂(b) = β_{pt(b)^⊥} =
⋆ α_{pt(b)}`. The decoupling (AC-4) puts the 1-dimensional `R_a` inside one
eigenspace, so `⋆r = εr` with `ε = ±1`. Then, for every `a ∈ α_{pt(b)}`,
`⟨r, ⋆a⟩ = ⟨⋆r, a⟩ = ε⟨r, a⟩`, so `r ⊥ ⋆α_{pt(b)} ⟺ r ⊥ α_{pt(b)}`. ∎
Equivalently in §(K-Λ)'s coordinates: `C(M) = ⋆C(bc)` there, and
`★r ∥ C(M) ⟺ ★r ∥ C(bc)` once `★r ∝ r`. The driver checks the two conditions as
**subspaces** of each eigenspace (a basis-wise check would not settle an iff),
16 bodies × 2 eigenspaces, 32/32.

**Reading, and the correction it makes.** A σ-equivariant seed recipe would make
§(K-σ) *Step σ5* obligation 1 — the σ-nondegeneracy of the transported seed, the
route's single crux — **free by construction**, since `σu = u` and `u` is
nondegenerate by hypothesis. That is exactly the revival the dispatch asked
about, and it is real. But it is worthless: at the same seeds the route it would
discharge **degenerates onto route A**. §(K-σ) *Step σ6*'s own sentence *"route σ
does not use equivariance — it applies `σ` once to move to a **different** seed,
which is exactly why it escapes this wall"* is, with (AC-5), upgraded from a
remark to the **reason**: route σ's content is precisely `σu ≠ u`, so the fixed
locus is the one place it cannot help. **The verdict "σ-equivariant seed recipes
are DEAD" survives algebraic closure; the `ℝ`-definiteness argument for it does
not, and (AC-5) replaces it.**

### Step Z6 — (AC-6): the grids as a **direct** recipe — **REFUTED as a class statement over `hK`'s habitat**, with the mechanism identified, and a partial recipe left standing

The grids are not useless — they are just not useful *to route σ*. What they are
is a **combinatorial recipe for target-rank nondegenerate pencil realizations**:
input a ruling 2-colouring of `E(G)`, output an exact configuration. That is the
shape of thing `Pencil-strategy.md` §2.2 says the whole arc lacks, and it exists
only over a field with isotropic vectors. **It is not class-uniform, and the same
run that produced it produced the counterexample.**

**The pool, pinned.** Every figure below is over exactly the **21** shapes of the
`--shapes` and `--flanks` tables and nothing else; the aggregate is printed by
`--pool` from those same rows, so it cannot drift from them. (This is the
`63/63`-across-inconsistent-pools defect, `notes/dispatch-log.md`; the aggregate
is not hand-counted here.) Note `def = 0` and *count-tightness*
(`5|E| = 6(|V|−1)`) are **different** predicates and the pool separates them.

> **(AC-6)** *(measured, `--shapes` / `--flanks` / `--pool` / `--parity`)*
> **REFUTED as a class statement over the habitat `hK` is quantified over**, and
> **OPEN, with no identified obstruction, on the tight stratum**. Over the pinned
> 21-shape pool:
>
> | group | at the Tay target |
> |---|---|
> | **tight** (`def = 0` **and** `5\|E\| = 6(\|V\|−1)`) | **15 / 15** |
> | rigid but **not** count-tight (`def = 0`, excess 2) — `W19` alone | **1 / 1** |
> | **not rigid** (`def > 0`) | **2 / 5** |
> | overall | 18 / 21 |
>
> The 15 tight shapes are `ds-K4`, `ds-(K5−M)`, θ(3,4,5), θ(4,4,4), θ(3,3,6),
> θ(2,4,6), θ(1,5,6), and **all eight** §(K-flank) named flank shapes — `K5`
> 5-chromatic, 6v11e, `K222`, `K5+v`, wheels `W5`/`W7`, the menu-blocked `K4`,
> `P21` — i.e. every shape *no* class-uniform mechanism of this arc covers. The
> 16th `def = 0` shape is the **(K-res)** inhabitant `W19`, also at the target.
>
> **The three misses, attributed by the driver against `hK`'s own hypotheses:**
>
> | miss | `def` | cause | `hnoRigid` | feasibility-necessary | in `hK`'s habitat? |
> |---|---|---|---|---|---|
> | θ(1,2,9) | 3 | the colouring forces two bodies to **coincide** | ✗ | ✗ | **no** |
> | θ(2,3,7) | 1 | all 4 legal colourings give rank 58 vs target 59 | ✗ | ✓ | **no** |
> | `C11` (bare odd cycle) | 5 | **no proper alternation colouring exists** | ✓ | ✓ | **YES** |
>
> `C11` is the counterexample: simple, 2-edge-connected, `hnoRigid`, `\|V\| ≥ 5`,
> with a degree-2 body — every hypothesis `hK` carries — and the construction
> does not merely fall short there, it **does not exist**.

**The mechanism at `C11` is parity, and it is completely characterized.** An
alternation chain closes into a cycle only if every body along it has degree 2,
i.e. only inside a component of `G` that *is* a cycle, and that cycle is odd
exactly when the component has odd length. So:

> **no admissible ruling colouring exists ⟺ `G` has a bare odd cycle component.**

Driver `--parity`: over `C3 … C14` the shapes with no admissible colouring are
exactly `{3,5,7,9,11,13}`, and all **19** non-cycle shapes of the pool admit one.
The two `θ` misses are **not** parity — one is a coincidence of bodies, one a
rank shortfall — and both sit at shapes `hK` never sees. **θ(1,2,9)'s miss is
correct behaviour, not a defect**: its length-1 and length-2 branches form a
triangle with two hubs, which `not_pencilNondegFeasible_of_triangle_two_hubs`
already forbids, so it has **no** nondegenerate pencil realization at all,
σ-fixed or otherwise.

**What survives, stated so it cannot be over-read.** A **partial** recipe: at
every shape of the pool that `hK` actually quantifies over, the construction
reaches the target; the single in-habitat failure is a bare odd cycle, which is
an `index ≥ 1` habitat already discharged by the corank stratification (gap map,
*the arc in one paragraph*) and **cannot** be a tight shape, since a tight shape
has hubs. So the refutation is real, mechanistically understood, and **does not
transfer to the tight stratum, where (K-tight) lives**. That leaves exactly one
live question, and it is the *narrow* one:

> **Open.** Does an admissible colouring reaching the Tay target exist at *every*
> **tight** class shape? Measured: yes at 15/15. No obstruction identified.

**What that narrow question would be worth, stated exactly.** `hK`'s conclusion
(`Escape.lean:555`) is `∃ hubSel q s`, `|s| = 6(|V|−1) − def`, with
`pencilRow hubSel G.endsOf q` linearly independent on `s`: *the pencil rigidity
matrix at some chart seed has rank ≥ the target*. It does **not** require the
realization to be nondegenerate. A uniform recipe delivering a target-rank
realization at `G` **in the chart's image** would therefore discharge `hK` on the
tight stratum **directly — no escape route, no split, and no use of the inductive
hypothesis `HasGenericPencilRealization K 3 (G.splitOff …)`**.

**Chart-image membership — argued, not verified.** At a hub `v`,
`pencilChartNormal` reads the free seed and `pencilChartPoint v` is
`cross₃` of the hub-slot normals of `closedHubNbhd v` padded by free fills, so it
realizes *any* point of `v`'s panel; the grid asks for `point_v = normal_v`, legal
precisely because `pt(v) ⬝ᵥ pt(v) = 0` on `Q`. At a non-hub `v`,
`pencilChartNormal v = cross₃` of the closed-neighbourhood slot points, which is
`pt(v)` exactly when the star has rank 3 — which the driver asserts. So the grid
looks chart-realizable. **This is a prose argument against the chart definitions
(`Engine.lean:154–235`, `Chart.lean:393–412`), not a compiler-checked one**, and
it is the second place a small Lean spike is the right instrument.

**Three reasons to distrust even the narrowed question.** (1) The isostaticity of
the two contracted direction networks is **measured, never proven**, and it is
exactly the "rank condition becomes combinatorial" step `Pencil-strategy.md` §2.2
identifies as this arc's recurring failure. (2) The flank rows probe only the
**first 6 filter-passing colourings per shape** — the `hit` column there
*saturates* at 6 and is **not** a fraction of `pass`; the load-bearing column is
`best`. A full census was run only at `ds-K4` (64/64 colourings) and in
`--shapes` (all colourings, ≤ 8 alternation chains). (3) 15 tight shapes is a
small pool, and this arc's record is that every uniform claim so far has been a
negative (`Pencil-strategy.md` §2.3) — the base rate says the tight-stratum
answer is "no" and the obstruction has simply not been probed for yet.

*Confidence: **refuted** as a class statement over `hK`'s habitat (one exhibited
in-habitat shape, one identified mechanism, both driver-backed). On the tight
stratum — **superseded by §(K-grid)** (2026-08-06, direction T): the census ran
(907/907, no kill), the direction-network hope as worded here is refuted
((GR-2)) and corrected to two proven counting families ((GR-3)/(GR-4)), and the
residual is **(GR-4) + (GR-6)**, both geometry-free.*
*What would change this: see §(K-grid)'s own "what would change this" — the
tight-stratum question is owned there now; the habitat-level refutation (`C11`)
is permanent.*

### Step Z7 — (AC-7): `hK` over `ℂ̄` **implies** `hK` over every infinite characteristic-0 field

This is the dispatch's sub-question 3, and the answer inverts the expected sign:
over `ℂ̄` the statement is not weaker, it is **at least as strong**.

> **(AC-7)** *(proven; source-level, no driver)* Let `K ⊆ L` with `K` infinite.
> Then **`hK` at `L` implies `hK` at `K`**. In particular `hK` over `ℂ`
> implies `hK` over `ℝ`, `ℚ`, `ℚ̄`, every number field and every infinite
> subfield of `ℂ`; and since for fixed finite `α, β` the statement is a
> first-order sentence in the language of rings, `hK` over one algebraically
> closed field of characteristic 0 gives it over all of them, hence over
> **every infinite field of characteristic 0**.

*Proof.* Three observations, each verified against the landed statement.
(i) `hK`'s **antecedent** base-changes upward: `HasGenericPencilRealization K 3 G′`
is a conjunction of equalities, non-vanishings and `LinearIndependent`s at an
explicit configuration, all preserved by `K ↪ L` (matrix rank does not change
under field extension). (ii) `hK`'s **conclusion** existentially quantifies
`hubSel` and `s`, which are **field-free**, and a seed `q : α × Fin 4 × Fin 4 → K`
subject to `LinearIndependent K (pencilRow hubSel G.endsOf q)` on the finite `s` —
i.e. the non-vanishing of **some** `|s| × |s|` minor. (iii) That minor is a
polynomial in `q` with **coefficients in the image of `ℤ → K`**: the chart's point
and normal polynomials are `cross₃Poly` = `Matrix.det` of rows built from seed
variables and `Pi.single i 1` (`Engine.lean:117–119, 154, 207`), and `pencilRow`
is `hingeRow ∘ annihRow` of `extensor ![·,·]`, a `2 × 2` minor (`Engine.lean:318`).
So: given `hK` at `L`, apply it to the base-changed antecedent, get `q₀ ∈ L^N`
with `P(q₀) ≠ 0` for some ℤ-coefficient minor `P`; hence `P ≢ 0` as a polynomial;
hence `P ≢ 0` over `K`, whose prime ring contains the same coefficients; hence,
`K` being infinite, some `q ∈ K^N` has `P(q) ≠ 0`, and the same `hubSel`, `s`
work. ∎

**Three consequences, stated plainly.**

1. **Descending from `ℂ̄` to `ℝ` costs nothing** — *provided what you produce is a
   non-vanishing certificate for a `ℤ`-defined polynomial on the chart*, which is
   what the chart's **totality** (a free seed, no chart-image side condition —
   §(K-σ) *Step σ5* repair (c), first bullet) makes automatic. The dispatch's
   caution ("a complex realization need not be real") is correct about
   *realizations* and irrelevant to *`hK`*, because `hK` quantifies a seed over a
   free affine space, not a point of a variety with no real points. **(AC-6)'s
   `ℚ(i)` witnesses therefore already certify target rank over `ℝ` and `ℚ`** — a
   conclusion §(K-flank) *F2* reaches independently by direct `ℚ`-sampling, which
   is a useful consistency check on (AC-7) rather than a new result.
2. **The converse fails, and this is the asymmetry that matters.** `hK` at `ℝ`
   does **not** give `hK` at `ℂ`: a graph can have a `ℂ`-generic pencil
   realization and no `ℝ`-one, and then the `ℝ`-statement is silent about it. So
   **route σ discharged at `ℝ` closes `hK` at `ℝ` only**, while a proof over `ℂ̄`
   closes all of characteristic 0. If a field must be chosen, `ℂ̄` is the correct
   one — the opposite of the usual "algebraically closed = easier = weaker"
   reflex. (§(K-σ) *Step σ5*'s "instantiate the headline at `ℝ` first" is
   therefore the **narrowest** of the available options, not merely *a*
   narrowing.)
3. **The residual content of `[Infinite K]` is positive characteristic, and only
   that.** By (AC-7) the whole characteristic-0 family collapses to one
   statement. For char `p` the same minor `P` must be non-zero **mod `p`**, which
   is a genuinely separate condition on the same integer coefficients. Nothing in
   this arc has ever probed it. The `--char2` leg exhibits the phenomenon at the
   proxy level (a rational target-rank `ds-K4` configuration whose row matrix,
   denominators cleared, drops rank mod 2, 3, 5, 7, 11, 13 while holding at
   `10⁹+7`); that is a statement about **one seed**, not about the polynomial,
   and is reported as such.

*Confidence: proven-informally. The `ℤ`-coefficient step is a source-level
reading of four definitions and is the one place to attack it.*
*What would change this: a `pencilRow` entry whose construction introduces a
denominator (none does — `cross₃Poly` is a determinant and `annihRow` a minor),
or a chart-image side condition that makes `q` range over less than `K^N` (the
landed `pencilChartPointPoly_eval` / `pencilChartNormalPoly_eval` identities say
it does not).*

### Step Z8 — (AC-8): characteristic 2

> **(AC-8)** *(proven; driver leg `--char2`)* In characteristic 2 the polarity
> still **exists** (`complementIso` carries no characteristic hypothesis and
> `⋆² = id`), but its **geometry** collapses twice over:
> (i) `x ⬝ᵥ x = ∑ xᵢ² = (∑ xᵢ)²` — the quadratic form is the square of a linear
> form, so the "fixed quadric" is the **double plane** `{∑ xᵢ = 0}`, not a
> smooth quadric, and there are no rulings; (ii) `⋆ − 1 = ⋆ + 1`, so `⋆` is
> unipotent, its two "eigenspaces" coincide in one 3-space, and `Λ²K⁴` does
> **not** split.
> Hence **(AC-2)–(AC-6) all require `char K ≠ 2`**; **(AC-1)** does not; and
> **(AC-7)** is a characteristic-0 statement by construction.

Checked exactly: the identity on all 16 vectors of `𝔽₂⁴`; `rank(⋆−1) =
rank(⋆+1) = 3` over `ℚ` with the two kernels intersecting in `0`, against
`⋆−1 ≡ ⋆+1` entrywise mod 2.

### Verification

`notes/scripts/w4/closure.py` (**new with this section**; exact `ℚ(i)`,
stdlib-only, no CAS, no rng — nothing to seed, no `set` printed; a `w4/` leaf, so
its import closure is itself). It imports the canonical `⋆` (`repin.hodge_star`),
rigidity rows (`hybrid_gates.build_rigidity_extensors`), nondegeneracy
(`flanks.nondeg_conjuncts`, `repin.star_generic`), deficiency
(`nogood_subdiv.deficiency`), the shape generators (`pencil_escape`,
`pitch.theta_edges`, `widened.W19`, `flanks.named_shapes`,
`kslidecomb.shape_data`) and `kbare_common.rank_modp`; the only new primitive is
the scalar field. Every sampled configuration is guarded: all points asserted
isotropic, all edges asserted conjugate, every hinge asserted a `⋆`-eigenvector
whose sign matches its colour, every eigen-direction asserted on the conic, every
span's dimension asserted, and the contracted subsystem cross-checked against the
uncontracted one and against the full `6|V|`-column matrix.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --fixed     # (AC-2), (AC-3)
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --sweep     # (AC-4), ds-K4 census
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --shapes    # (AC-6), the 13-shape table
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --flanks    # (AC-6), the 8 flank shapes
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --pool      # (AC-6) THE PINNED AGGREGATE
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --parity    # (AC-6) the C11 mechanism
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --collapse  # (AC-5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --char2     # (AC-8) + the char-p proxy
PYTHONHASHSEED=0 python3 notes/scripts/w4/closure.py --validate  # all eight, ~43 s
```

**`--pool` is the only place an aggregate figure may be read from.** It runs over
exactly the union of the `--shapes` and `--flanks` rows, tallies them into three
disjoint groups (**tight**; rigid-but-not-count-tight; not rigid), prints the
three fractions and the overall, and then attributes every miss against `hK`'s
own hypotheses (`hnoRigid` via `rigid_vertex_sets`, and the landed *necessary*
feasibility conditions `hcard` + no-two-hub-triangle). Quoting an aggregate from
anywhere else is what the σ recon's `63/63` did. **`--flanks`'s `hit` column
saturates at the probe cap (6) and is not a fraction of `pass`** — the driver
prints that caveat above the table, and the load-bearing column there is `best`.

`--validate` verified **byte-identical** under two different `PYTHONHASHSEED`
values (`0` and `999`), exit 0, 43 s each (re-verified at landing). Adding this
driver modified no tracked script, so the figure-invariance gate discharged on
the `git diff --name-only -- '*.py' '*.m2'` check alone
(`notes/scripts/README.md`, first bullet).

> **RE-BASELINED 2026-08-06 (slice S2).** `closure.py` *was* modified, by the
> guard adoption, so the full obligation ran. Four legs moved and each is
> repointed here: `--fixed` and `--sweep` now report the **composite** guard in
> the column that used to read `starOK` (hence (AC-9) above), `--validate`
> carries both, and `--char2`'s rational seed moved `2 → 6` because its
> `flanks.clean_pencil_seed` now applies the composite guard — its mod-`p` table
> is an explicitly-labelled *proxy* and its rank drops moved with the seed
> (`p = 2, 3, 5, 11` now `76, 78, 80, 76`). `--shapes`, `--flanks`, `--pool`,
> `--parity` and `--collapse` are **byte-identical**, so every (AC-6) and
> (AC-5) figure below is untouched.

**Which driver tests which sentence (F11).**

| claim | leg | figure |
|---|---|---|
| (AC-1) | — | **none; source-level only.** Named as such, not asserted more strongly |
| (AC-2) | `--fixed` AC-C0 | no `ℚ`-isotropic vector in `[−3,3]⁴`; explicit `ℚ(i)` one; eigenspaces `3+3`, `ℚ`-rational, mutually orthogonal; the two rulings realize both `⋆`-signs; the conjugacy law on 3 configurations |
| (AC-3) | `--fixed` | 4/4 conjuncts + star ranks 3, rank 90 = target at `ds-K4` |
| **(AC-9)** | `--fixed`, `--sweep` | the (AC-3) witness' four coincident hinge lines printed, one per hub; and the composite guard `repin.star_generic` accepts **0 of 64** colourings, asserted |
| (AC-4) | `--sweep` | `rank = rank₊ + rank₋` at **64/64** colourings; every target-rank colouring balanced, both classes forests, both blocks at 45; every unbalanced one short |
| (AC-5) | `--collapse` | 32/32 (16 bodies × 2 eigenspaces), as a **subspace** equality |
| (AC-6) positives | `--pool` (over `--shapes` + `--flanks`) | **tight 15/15**, rigid-not-count-tight **1/1**, not-rigid **2/5**, overall **18/21** — one pool, one leg, three disjoint groups |
| (AC-6) refutation | `--pool`, `--parity` | the three misses attributed: θ(1,2,9) and θ(2,3,7) **out of** `hK`'s habitat, `C11` **in** it; and `C3…C14` with no admissible colouring = exactly the odd ones, all 19 non-cycle pool shapes admitting one |
| (AC-7) | — | **none; source-level only** (four definitions read). The `--char2` leg's mod-`p` table is a *proxy* for its third consequence and is labelled so |
| (AC-8) | `--char2` | 16/16 on `𝔽₂⁴`; the two rank tables |

### Confidence verdict

- **(AC-1) the polarity generalizes: proven-informally**, source-level, **not
  compiler-checked**. Nothing obstructed; char 2 fine for the definition; the
  general-`K` transport already landed as `mapSupport`. The dispatch's question
  "is anything actually obstructed, or is this bookkeeping?" — **bookkeeping.**
- **(AC-2), (AC-3), (AC-4), (AC-5), (AC-8): proven-informally**, each exact and
  each with a driver leg asserting that sentence.
- **(AC-9) (every σ-fixed body of degree `≥ 3` carries a coincident hinge
  line): proven** — pigeonhole against the two-ruling-lines cap of *Step Z3* —
  and measured at 0/64 by the guard. It **qualifies (AC-3) without weakening
  it**: the σ-fixed witnesses satisfy the Lean predicate and reach the target,
  and are nevertheless never *generic*. New 2026-08-06 with the re-baselining
  round's slice S2, which is what made the harness able to see it.
- **(AC-6): REFUTED as a class statement over `hK`'s habitat** — `C11`, a bare
  odd cycle, satisfies every hypothesis `hK` carries and admits **no** σ-fixed
  nondegenerate configuration at all; the mechanism (parity) is identified and
  characterized exactly. **Open only on the tight stratum**, where all three
  misses are absent by construction and the measurement is 15/15 with no
  obstruction found. The per-shape positives are exact; the narrowed class
  statement is neither proven nor refuted.
- **(AC-7): proven-informally**, source-level.
- **The dispatch's sub-question 2, answered:** §(K-σ)'s two `ℝ`-refutations
  **both reverse as arguments** — over `ℂ̄` a σ-fixed pencil configuration exists,
  and it is *not* degenerate. But the **verdict** they support survives, on the
  field-neutral (AC-5). Net effect on route σ: **nil**. Net effect on the arc: one
  partial construction, (AC-6), which is *not* route σ and which is already
  refuted as a class statement.
- **The dispatch's honesty bar.** The field question is largely bookkeeping
  ((AC-1)) plus one clean structural payoff ((AC-7)); §(K-σ)'s route-σ verdicts
  are unmoved; and the one thing that did change — the σ-fixed locus being
  non-empty and non-degenerate — buys route σ nothing. **No route was
  manufactured**, and the one construction that looked like a route was
  **refuted by its own driver in the same run**, with the counterexample named
  and its mechanism characterized. What survives is a *partial* recipe with a
  known boundary, which is worth having and is not a closure of anything.

### What would change this

*(i)* A typecheck spike that fails on the general-`K` `screwComplementIso` or one
of its four theorems — the one instrument this dispatch could not use — would
downgrade (AC-1) from *bookkeeping* to *a real gap*.
*(ii)* A **tight** class shape at which no admissible ruling colouring reaches the
Tay target closes (AC-6)'s remaining question negatively. The cheapest probe is a
census over the `kslidecomb` class-shape pool, and the most likely failure mode is
combinatorial, not geometric: an admissible colouring must simultaneously
alternate along every branch, avoid a monochromatic hub, keep both ruling classes
acyclic **and** balance `|E_A| = |E_B|`, and those four can conflict — θ(1,2,9)
shows the conflict is real (there it forces two bodies to coincide), at a
non-tight shape. **Parity is already excluded as the tight-stratum obstruction**
by (AC-6): a tight shape has hubs, so it is not a bare cycle, so it always admits
*some* alternation colouring. Whatever kills the tight case, if anything does, it
is one of the other three conditions or the geometry.
*(iii)* A proof that the contracted direction network of *Step Z4* is isostatic
whenever (AC-4)(i)–(ii) hold would turn (AC-6) into a **tight-stratum-uniform**
theorem (never a habitat-uniform one — `C11` is permanent), and with it discharge
(K-tight) on the tight stratum directly, with `hK` then
following over every infinite characteristic-0 field by (AC-7). This is the
highest-value single item this section produces and it is **squarely inside the
project's existing formalized technology**: it is a 3-dimensional
body-hinge/Tay-style packing question (screws on a conic in `K³`, hinges shared
by more than two bodies), not new geometry.
*(iv)* A verified chart-image membership for the grid configurations (a small
Lean spike against `pencilChartPoint` / `pencilChartNormal`) is a **prerequisite**
for (iii) buying anything for `hK`; without it (AC-6) certifies target-rank
*realizations*, which §(K-flank) *F2* already has per shape, rather than
target-rank *chart seeds*, which is what `hK` asks for.
*(v)* Any characteristic-`p` probe at all: (AC-7) shows this is the **entire**
residual content of `[Infinite K]`, and the arc has never looked at it. A single
class shape whose escape minor vanishes identically mod some `p` would refute
`hK` at that characteristic and force a re-pin of the headline's typeclass — a
cheap, high-information experiment nobody has run.

## §(K-ann) — the annihilator as a self-stress of the contracted framework: a class-uniform bracket recipe for `dλ`, and the mixed-stratum independence statement it still needs (**the recipe's KERNEL is delivered — the arc's first *formula* rather than a search — and its two INPUTS are not; the crux moves to (ANH-R1), relocation #4**)

Answering the second fan-out's **direction A** — `notes/Pencil-strategy.md` §4.6's
**U1** (retarget the image problem from `Gr(3,6)` to the annihilator), **U2** (the
hinge-rate / cycle-space presentation, whose ground set is `E(H)`) and kernel-(K)
**option B** (the stress-function reading), fused. Read against §(K-pitch)
*Step 5b* ((T5)), §(K-Λ) *Steps 3–5a* ((Λ2), *Theorem (Λ-completeness at length-4
companions)*, (OUT)) and §(K-dom) *Steps D1/D2*, whose notation is inherited
verbatim. Option B's infrastructure is **not** used and its standing NO-GO is
untouched — everything below is pointwise exact linear algebra, and `τ` is a
kernel, not a chart rational function.

**Status, stated before the mathematics.**

- **The headline is (ANH-2)/(ANH-3): a *recipe*, in `Pencil-strategy.md` §2.2's
  sense — a formula, not a search, and the first the arc has produced.** The
  **reciprocity identity** `dλ(π_P ω) = Σ_e ω_e B(τ_e, δC_e)` is local at the
  moved vertex, holds at every class member with no genericity hypothesis, and at
  the named move (translate one non-hub 2-valent far body) collapses to **one
  Klein pairing**. Carry its caveat with it wherever it is quoted: *the formula's
  kernel is bounded-size and class-uniform; what it pairs against (`τ`, `ω`) is
  not.* That is exactly why the pass delivers half of U1 and not all of it.
- **(ANH-1) upgrades (T5)/(D2) from measured bounds to a mechanism.** `λ` **is a
  self-stress** — of the *contracted* framework `H/P` (weld the whole companion
  into one body) — with stress dimension exactly `k − 3`. So §(K-dom) *(D2)*'s far
  block `3(k−3)`, until now a measured attainment, is `dim Gr(k−3, k)` **for that
  stress space**: a previously unexplained number now has its reason. 18 seeds, 9
  habitats, `k = 3..6`.
- **(ANH-4) is a proof, and it is `k = 4`-only, provably.** At `k = 4` the far
  edge set `E(H/P)` is a **circuit of the generic Tay matroid** — from 5/6-sparsity
  plus `hnoRigid`, with the count `5k + 10 ≤ 6k + 6` tight **exactly** at `k = 4`.
  That reproduces §(K-dom) *(D3)*'s `k ≥ 4` with `k = 4` as the equality case. On
  the realized side the support is the **whole** far edge set at every class seed
  (14/14), so the named move needs **no support-location step**.
- **(ANH-7): on the ~89 % of triples whose `H/P` carries a length-5 branch the
  whole criterion is ONE 4-point bracket**, correct at 56/56 sites.
- **The residual is one sentence, and it is (ANH-R1)** — *`τ_β ≠ 0` at the pencil
  placement*, i.e. `H/P − β` is pencil-rigid. **That is relocation #4** (after C1's
  `rank dV = 9` and the ∀λ seed's realizability), it is a *different kind* of
  relocation for three reasons given in *Step A8*, and **whether it is genuinely
  easier than its parent or merely smaller is OPEN** — nothing in this pass settles
  it, and the three reasons must not be read as settling it. It does **not** evade
  `Pencil-strategy.md` §2.3: `τ_β ≠ 0` is a rank **lower** bound. Limiting, not
  fatal.
- **No gap-map *status* moves.** The (K-wit) row's *what would close it* cell gains
  (ANH-R1) as a named, scoped, `k = 4`-only sufficient route; the (K-dom) row gains
  (ANH-1) as the mechanism behind (D2). Class uniformity is untouched.

**Three corrections this pass owes the record**, all of them to claims that were
written down before it ran:

1. The coordinator's dispatch reading — *"`λ` is an annihilator covector, escape
   failure is a stress condition, and cocircuits are minimal supports in an
   orthogonal complement, so option B and U2 are the same object from opposite
   ends"* — is **directionally right and specifically wrong**, and correcting it is
   what makes the pass work. `λ` *is* a stress, but a self-stress of the contracted
   **far** framework `H/P`; it is **not** `[r]`, the transmitted wrench of the split
   that option B is about. Different frameworks, no shared infrastructure.
2. **U2's cocircuit reading is the DUAL of what the recipe needs.**
   `Pencil-strategy.md` §4.6-U2 is right that `supp(λ)` is a **cocircuit** of the
   linear matroid on `E(H)` — that is the object §(K-Λ) *Step 5a*'s (OUT) half
   needs. The *recipe* question turns on `supp(τ)`, a **circuit** of the contracted
   framework. Same ground set, dual objects; everything below is about the circuit.
3. **This pass's own first analysis was wrong**, and its driver caught it: the kill
   set of (ANH-5) is *not* `⟨C(z₁z₂)⟩` always — that holds only at `dim U_y = 2`,
   and at `dim U_y = 1` the kill set is the strictly larger `α_{u₀}`. The general
   criterion is `ρ_y ⊥_B (V_y ∧ U_y)`.

### Standing notation (on top of §(K-Λ) and §(K-dom))

Split chain `b–v–a–c` at a hard-stratum target-rank `G′`-seed; `H := G − v − a`;
`P = b x₁ … x_{k−1} c` a shortest `b`–`c` path of `H` (the companion, of length
`k`); `S_P := span{C_e : e ∈ P}`; `V_bc ⊆ S_P` by path-sum containment;
`Λ := {λ ∈ S_P* : λ ⊥ V_bc}`, of dimension `k − 3`, is (T5)'s annihilator — the
*only* channel through which the far graph reaches `V_bc`. `B` is the Klein form,
`α_p` / `β_π` the two families of maximal isotropic 3-spaces.

**Hinge rates.** A motion of `H` is `m(x) − m(y) = ω_e C_e` per edge (§(K-ind)
*Step I3*'s identity), so `Z(H) = ker N` with `N` the cycle-condition matrix
(`dominance.cycle_data`), and `W := Z(H)^⊥ ⊆ (K^{E(H)})*`. Writing `π_P` for the
restriction of `ω` to the companion coordinates, `Λ ≅ W ∩ (K^P)*`.

**`H/P`** is `H` with the companion path contracted: weld `b, x₁, …, x_{k−1}, c`
into a single body `X`. It is a body-hinge multigraph on `|V(H)| − k` vertices with
`|E(H)| − k` edges (no loops: a chord among companion vertices would be a cycle of
`G` of length `≤ 4`, and 5/6-sparsity forces girth `≥ 6`), and

>  `5|E(H/P)| − 6(|V(H/P)| − 1) = k − 3`.

### Step A1 — (ANH-1): the annihilator IS the self-stress space of `H/P`

> **(ANH-1)** *(proven-informally)* At a hard-stratum target-rank seed, the map
> `τ ↦ (B(τ_e, C_e))_{e ∈ P}` is an isomorphism
>
>  `{ self-stresses of the contracted body-hinge framework H/P }  ⟶  Λ`,
>
> `H/P` is **rigid** there, and its stress space has dimension exactly `k − 3`.
> Equivalently: **the far graph reaches `V_bc` only through the self-stresses of
> the graph obtained by welding the companion.**

*Proof.* `W = im(Nᵀ)`, and an element of `im(Nᵀ)` is exactly `μ_e = B(τ_e, C_e)`
for a **screw circulation** `τ ∈ 𝒵(H) ⊗ Λ²K⁴` — `𝒵(H)` the graph cycle space, i.e.
`Σ_{e ∋ u} ± τ_e = 0` at every body `u`. Such a `μ` is supported inside `P` iff
`B(τ_e, C_e) = 0` for every `e ∉ P`, i.e. iff each non-companion hinge transmits
`τ_e` legitimately. Equilibrium plus transmissibility off `P` is verbatim the
self-stress system of `H/P`: the companion's own `τ_e` are recovered as partial
sums of the residuals along `P`, and the whole map is injective because `H` itself
carries **no** self-stress (`5|E(H)| − 6(|V(H)|−1) = −3`, and `H` is independent at
a target-rank seed). Finally `dim Λ = k − 3` forces `dof(H/P) = 0`, i.e. rigidity —
welding the companion kills exactly `V_bc`'s three degrees of freedom. ∎

Two immediate readings, and the first is the one to quote.

**(i) (D2) gets a mechanism, so a measured number becomes an explained one.**
§(K-dom) *(D2)* bounds the far block of `d(H ↦ V_bc)` by `3(k−3)` because the
annihilator is a point of `Gr(k−3, k)`, and *Step D4* measures that bound attained
at `0, 3, 6, 9` for `k = 3, 4, 5, 6`. (ANH-1) says **which** `Gr(k−3,k)`-point: the
self-stress space of `H/P`, whose dimension `k−3` is forced by a **count**, not by
a rank measurement. The `3(k−3)` is `dim Gr(k−3, k)` for that stress space. This is
the pass's contribution to the *settled* part of the arc: (T5) and (D2) stop being
bounds that happen to be attained.

**(ii) U2's ground set survives contact — with the correction above.** `E(H)`
really is the index set, and the matroid really has exchange (it is linear). Its
*generic* form is combinatorial: for `A ⊆ E(H)`, `r(A) = |A| − dof(H/(E∖A))`, and
`dof` of a generic body-hinge graph is Tay's count — so `Pencil-strategy.md` §2.2's
ingredient 3 (Edmonds / Nash-Williams, the project's Phase-12/13/14 machinery) is
available too. What U2 named is the **cocircuit** `supp(λ)`; the recipe turns on the
**circuit** `supp(τ)`.

### Step A2 — (ANH-2): the reciprocity identity, and why it is local

> **(ANH-2)** *(proven)* Let `δ` be any chart direction and `ω ∈ Z(H)`. Then
>
>  `dλ(π_P ω)  =  Σ_{e ∈ E(H)} ω_e · B(τ_e, δC_e)`,
>
> and `δC_e = 0` unless `e` is incident to a vertex the direction moves. Both sides
> are independent of how `λ(t)` is scaled and of which particular solution of the
> derived system is taken.

*Proof.* `λ(t)·ω(t) = 0` for a curve `ω(t) ∈ Z(t)` gives `dλ(π_P ω) = −λ·ω̇`.
Differentiating the cycle condition `Σ_{e ∈ Z} ± ω_e C_e = 0` and pairing with
`τ`'s cycle certificate gives `Σ_e (ω̇_e B(τ_e,C_e) + ω_e B(τ_e, δC_e)) = 0`; the
first sum is `λ·ω̇` because `B(τ_e,C_e)` vanishes off `P`. ∎ Well-posedness:
`π_P ω` ranges over `ker λ`, on which the ambiguity `λ̇ ↦ λ̇ + ḟλ` dies; and
`λ ∈ im(Nᵀ)` kills the `ker N` ambiguity in `ω̇`.

This is a **virtual-work / reciprocity** statement: the rate at which the
annihilator moves under a far-chart deformation is the pairing of the motion
against the stress, evaluated **only at the moved hinges**. It is the formula U1
asked for, and it is bounded-size: two terms at a 2-valent body.

### Step A3 — (ANH-3): the named move, and the one-pairing form

> **The named move.** *Translate a single non-hub far body `y` of `H`-degree 2,
> inside the intersection of its hub neighbours' panels.* (Legal in the pencil
> chart: `y` appears in a hub's incidence constraint only through its hub
> neighbours, so the admissible velocities are `⋂_u n_u^⊥`, of dimension
> `3 − #(hub neighbours)`.)

> **(ANH-3)** *(proven)* With `y`'s neighbours `z₁, z₂`, `ρ_y` the screw
> transmitted through `y` (equilibrium at a 2-valent body makes the two incident
> `τ`'s equal up to orientation) and `v` the velocity,
>
>  `dλ_y(v)(π_P ω)  =  B( ρ_y ,  v̂ ∧ (ω_{e₁} ẑ₁ − ω_{e₂} ẑ₂) )`,
>
> **one Klein pairing** — a bracket-linear form, degree 1 in `v` and 1 in the hinge
> rates. (It is a *single* 4-point bracket `[w₀,w₁,v,u]` exactly when `ρ_y` has zero
> pitch; measured **0 of 192**, so in practice it is the Klein pairing, not one
> bracket.)

### Step A4 — (ANH-4): at `k = 4`, `E(H/P)` is a circuit of the Tay matroid

This is the pass's main *combinatorial* theorem, and it is what makes the named
move need no support-location step.

> **(ANH-4)** *(proven-informally)* At a `k = 4` class habitat (tight, `def = 0`,
> `hnoRigid`, both chain ends hubs), **every proper subset of `E(H/P)` is
> independent** in the generic body-hinge (Tay) matroid. Since `E(H/P)` itself has
> excess 1, it is a **circuit**: the generic self-stress of `H/P` is nonzero at
> **every** edge.

*Proof.* Suppose `A ⊊ E(H/P)` is dependent. By Tay + Lee–Streinu some vertex set
`W′` of `H/P` is over-braced: `5|E_A(W′)| > 6(|W′|−1)`.

*Case `X ∉ W′`.* Then `W′ ⊆ V(H) ∖ V(P)` and `E_A(W′) ⊆ E_G(W′)`, contradicting
`G`'s 5/6-sparsity (`f(W) ≤ 0` for every `W`, which `def(G) = 0` at a tight `G`
forces).

*Case `X ∈ W′`.* Put `W := (W′ ∖ {X}) ∪ V(P) ⊆ V(H)` and `W̃ := W ∪ {v, a}`, so
`|W̃| = |W′| + k + 2` and `|E_G(W̃)| ≥ |E_A(W′)| + k + 3` (the `A`-edges, the
companion's `k`, the split chain's 3). Then

>  `5|E_G(W̃)| ≥ 5|E_A(W′)| + 5k + 15 ≥ (6(|W′|−1) + 1) + 5k + 15 = 6|W′| + 5k + 10`,
>
>  `6(|W̃| − 1) = 6(|W′| + k + 1) = 6|W′| + 6k + 6`,

and `G`'s sparsity `5|E_G(W̃)| ≤ 6(|W̃|−1)` therefore forces `5k + 10 ≤ 6k + 6`,
i.e. `k ≥ 4`. **At `k = 4` that is an equality**, so every inequality in the chain
is tight and `f(W̃) = 0`. With every subset of `G` sparse that makes
`def(G[W̃]) = 0`, and `W̃ ⊊ V(G)` with `|W̃| ≥ 2` — a **proper rigid subgraph**,
contradicting `hnoRigid` (`Graph.IsProperRigidSubgraph`,
`Molecular/Deficiency.lean:483`: `H ≤ G ∧ H.IsKDof n 0 ∧ 2 ≤ |V(H)| ∧
V(H) ⊊ V(G)` — properness is on the *vertex* set, which is what this argument
produces). ∎

**Why `k = 4` and not `k ≥ 5`, and the (D3) calibration.** The inequality
`5k + 10 ≤ 6k + 6` is tight exactly at `k = 4`; at `k ≥ 5` it has slack, no
contradiction follows, and indeed the stress space then has dimension `k − 3 ≥ 2`
so `E(H/P)` cannot be a circuit. **The theorem is intrinsically a `k = 4`
theorem** — and note what its own count reproduces: §(K-dom) *(D3)* derives
`hnoRigid ⟹ k ≥ 4` from the proper cycle `C_{3+k}`, and the chain above derives the
same `k ≥ 4` from an over-braced set, with **`k = 4` the equality case** of both.
The two are the same tightness seen twice.

**Two independent corollaries, both verified.** *(a)* `girth(H/P) ≥ 6` unless
`|E(H/P)| = 5`, i.e. unless `G` is θ(3,4,5) itself (a `C_j` has body-hinge excess
`6 − j`, so a *proper* `C₅` would be a proper dependent subset). *(b)* no branch of
`H/P` has length `≥ 6` — which is the *Shared dictionary*'s **(SD-6)**, proved
there *independently and elementarily*, so the two agree and neither is assumed.

**And an incidental worth keeping.** θ(3,4,5) is the **unique** `k = 4` class shape
whose entire annihilator is the Klein-perp of a single 5-cycle (it is the only shape
in the whole census with `|E(H/P)| = 5`). That is a concrete reason for its role as
the arc's exemplar, rather than an accident of who picked it first.

### Step A5 — (ANH-5)/(ANH-6): branch constancy, and the exact vanishing criterion

> **(ANH-6)** *(proven)* Equilibrium at a 2-valent body transmits the wrench
> unchanged, so `τ` is **one screw per branch** of `H/P`, and transmissibility makes
> that screw `B`-orthogonal to **all `ℓ` of the branch's hinge lines**. Hence
> `dim Λ = 6·c(H/P) − |E(H/P)| = k − 3`, and a branch of length `ℓ` whose lines span
> `K⁶` carries a **forced-zero** screw.

> **(ANH-5)** *(proven)* At a **free** 2-valent far body `y` (no hub neighbour, so
> `v` sweeps the whole plane at infinity `H_∞`), with
> `U_y := {ω_{e₁} ẑ₁ − ω_{e₂} ẑ₂ : ω ∈ Z(H)} ⊆ K⁴`:
>
>  `dλ_y ≡ 0  ⟺  ρ_y ⊥_B (H_∞ ∧ U_y)`.
>
> When `dim U_y = 2` the right-hand kill set is exactly `⟨C(z₁ z₂)⟩`, i.e.
> **`dλ_y ≡ 0` iff the transmitted wrench is the pure force along the line joining
> `y`'s two neighbours.** When `dim U_y = 1` (spanned by `u₀`) the kill set is the
> larger `α_{u₀}`, so the criterion is weaker there.

*Reason for the `dim U_y = 2` form.* `B(ρ, v̂ ∧ ẑ_i) = 0` for all `v̂ ∈ H_∞` says
`ρ ⊥_B α_{z_i}`; an α-plane is maximal isotropic hence self-`B`-perpendicular, so
`ρ ∈ α_{z₁} ∩ α_{z₂} = ⟨C(z₁z₂)⟩`. The driver asserts the **subspace identity**
directly, not just the coincidence of two booleans.

*The general form is the correction of item 3 above.* The `⟨C(z₁z₂)⟩` reading was
this pass's first analysis and it is **false at `dim U_y = 1`**; `ρ_y ⊥_B (V_y ∧ U_y)`
is the criterion that holds at both, with `V_y` the space of admissible velocities.

**A collinearity corollary worth keeping.** On a chain of *consecutive* free
2-valent bodies the screw is one and the same, so `dλ ≡ 0` would force
`ρ ∝ C(w_{i−1}w_{i+1})` at two consecutive `i` — which makes four consecutive branch
points **collinear**, refuted at any generic chart point. So on such a chain the
only way `dλ ≡ 0` is `ρ = 0`.

### Step A6 — (ANH-8): every branch of a class member has length `≤ 5`

> **(ANH-8)** *(proven, elementary)* Every branch (maximal degree-2 chain) of a
> class member `G` has length `≤ 5`.

**This is promoted out of the section.** It is an elementary rigid-graph fact of
exactly the kind both workbooks reuse, so its statement and proof live **once**, in
the *Shared dictionary* as **(SD-6)**; `(ANH-8)` is this section's name for it and
is not restated here. Its consequence for the argument above is what this step
carries:

**Consequence.** Every branch screw lives in a space of dimension `6 − ℓ ≥ 1` —
**no branch is forced to zero**, which is exactly what (ANH-4) needs, and the two
proofs are independent. At `ℓ = 5` the screw is pinned to a **1-dimensional
Klein-perp `κ_β`**: an explicit bracket vector of the branch's six points, computed
by a `5 × 6` Laplace expansion, with **no global solve**.

### Step A7 — (ANH-7): the recipe, in one named move and one bracket

Let `β = w₀ w₁ w₂ w₃ w₄ w₅` be a length-5 branch of `H/P` (endpoints nodes, `w₁..w₄`
free 2-valent bodies), and take `y = w₂`.

`C(w₁w₃)` shares a point with `D₁ = C(w₀w₁)`, `D₂ = C(w₁w₂)`, `D₃ = C(w₂w₃)` and
`D₄ = C(w₃w₄)`, so it is automatically `B`-perpendicular to **four of the five**
branch lines. `κ_β` is the unique common perp of all five. Hence `κ_β ∝ C(w₁w₃)` iff
`C(w₁w₃)` is perpendicular to the fifth as well:

> **(ANH-7)** *(proven-informally, **conditional** — the two inputs below)* At a
> `k = 4` class habitat with a length-5 branch `β` of `H/P`, and at the free middle
> body `w₂` with `dim U_{w₂} = 2`,
>
>  **`dλ_{w₂} ≢ 0  ⟺  τ_β ≠ 0  and  [w₁, w₃, w₄, w₅] ≠ 0`.**
>
> One named far-chart move, one 4-point bracket, no quadric, no panel, no `pt(a)`,
> no `M`, and nothing whose size grows with the graph.

**The two inputs, named precisely.**

- **(ANH-R1) `τ_β ≠ 0`.** Generically forced: (ANH-4) makes `E(H/P)` a circuit, so
  the generic stress is nonzero on every edge. At the **pencil** placement it is the
  statement that `H/P − β` — a graph with count exactly 0, generically isostatic —
  is **rigid**, i.e. independent. Specialization only ever runs the other way
  (`dim S_pen ≥ dim S_gen`, hence `supp_pen ⊆ supp_gen`), so this is **not
  implied**. Measured `τ_β ≠ 0` at 56/56 sites and full support at 14/14 class
  seeds. *Step A8* is about this and nothing else.
- **(ANH-R2) `dim U_{w₂} = 2`.** Measured 32 of 56 sites; at the other 24 the kill
  set is the larger `α_{u₀}` and the *conclusion* still held (`dλ ≠ 0` at all 56), so
  (ANH-R2) restricts the **closed form**, not the conclusion.

**And the payoff, if the two inputs are discharged.** `dλ ≢ 0` on the FIXED-scoping
far chart makes `{λ = p⁺}` a *proper* closed subset there (`p⁺` is frozen in that
scoping), hence proper in the whole irreducible pencil chart; by §(K-Λ)'s **(Λ2)**
and *Theorem (Λ-completeness at length-4 companions)*, at a generic seed the escape
then holds — by pitch off the bad line, and by route A on the `λ ∝ q` branch. So a
class-uniform (ANH-7) would **close (K-wit)/(K-pitch) at every length-4-companion
class (shape, split)**, under (Λ0) in full and the standing (T1)/(T5) hypotheses. It
would *not* close the class — see *Step A9*.

### Step A8 — (ANH-R1) is relocation #4: what makes it a different kind, and the question it leaves open

**Is this relocation #4? Yes, and the record should say so in those words.** C1
relocated `Q(z) ≢ 0` to `rank dV = 9` (§(K-dom), struck as a route); the ∀λ seed
relocated it to `λ`'s realizability (`Pencil-strategy.md` §4.6); this relocates it
to **(ANH-R1)**. Three things distinguish it, and none of them is "it is smaller so
it must be easier":

1. **It crosses `Pencil-strategy.md` §2.2's ingredient-2 boundary in the right
   direction.** `Q(z) ≠ 0` is a Klein-form condition, invisible to any matroid
   (§(K-pure) *P5*). (ANH-R1) is an **independence** condition in the body-hinge
   matroid — a matroid whose ground set grows with the graph *and* which **has** a
   min-max (Tay + Nash-Williams / Edmonds, formalized in Phases 12–15). Its
   combinatorial half is not merely expressible, it is **proven**: that is (ANH-4).
   What is left is *only* the generic-vs-pencil gap.
2. **It lands on a strictly smaller graph.** `H/P − β` has `|E(G)| − 12` edges and
   `|V(G)| − 10` vertices. Every prior relocation stayed on `G`. This is the shape an
   induction needs — though §(K-ind) *Step I6* is exactly why `pencil_reduction` does
   not supply one: the welded body `X` carries non-concurrent hinges, so (ANH-R1)
   lives on the **mixed stratum**. It is therefore **not the same problem shrunk**,
   and it is `Pencil-strategy.md` §4-C3's **second** concrete consumer, alongside
   §(K-Λ) *Step 5a*'s (OUT).
3. **It does not escape §2.3, and `Pencil-strategy.md` §4.6-U2's honesty flag is
   confirmed as *limiting, not fatal* — say both halves.** (ANH-R1) is a rank
   **lower** bound, so the asymmetry is relocated onto a smaller contracted graph
   exactly as flagged, not evaded. The flag is *not* fatal because the smaller
   graph's matroid is Tay's, where independence **is** combinatorially
   characterised — unlike `R_3`, where §2.3's asymmetry is an open problem of the
   subject. The wall changes character: from *"no matroid sees this"* to *"the
   matroid sees it and the pin may not respect the matroid"*. That second wall is
   the **weak-map / specialization-stability** direction `Pencil-strategy.md` §4.6
   named as the only remaining (M3)-passing literature lead, and it now has a
   specific statement to attach to, which that subsection said it could not supply.

> **The open question, stated as open.** *Is (ANH-R1) genuinely easier than its
> parent, or merely smaller?* **Nothing in this pass settles that.** The three
> reasons above say the relocation is of a different *kind*; they do **not** say it
> is a *reduction in difficulty*, and they must not be read as saying so. The arc's
> own base rate for "smaller and better-structured, therefore tractable" is
> unencouraging (`Pencil-strategy.md` §2.3), and the honest position is that
> relocation #4 has better structure than #1–#3 and an unmeasured difficulty.

### Step A9 — scope and the `k`-grading: the machinery transports, the target does not

- **(ANH-1), (ANH-2), (ANH-3), (ANH-5), (ANH-6)** and the *Shared dictionary*'s
  **(SD-6)** are **length-free**, and were verified at `k = 3, 4, 5, 6`.
- **(ANH-4) is `k = 4` only — provably**, the count being tight exactly there. At
  `k ≥ 5` the stress space has dimension `≥ 2`, `E(H/P)` is not a circuit, and "every
  far edge is stressed" is *measured* (`k = 5`: 10/10; `k = 6`: 9/9 and 15/15) but
  **not** forced. (ANH-7)'s closed form goes with it.
- **The target transports worse than the machinery.** At `k = 4`, `Bad_Λ` is two
  points of `P³`, so non-constancy of `λ` suffices. At `k = 5` the bad set is
  3-dimensional in the 6-dimensional `Gr(2,5)` (§(K-Λ) *Step 7*) and non-constancy
  buys nothing; at `k = 6` the target is `Gr(3,6)` again.
- **So no `k`-graded mechanism, this one included, can close the class** — `k = 4`
  is the `hnoRigid` **equality** case (§(K-dom) *(D3)*, (ANH-4) above) with `k ≥ 5`
  the interior, and both populations are non-empty in the arc's habitat table. This
  is the same verdict `Pencil-strategy.md` §4.6 already carries, reached again from
  the inside; this pass does not claim otherwise.
- **What (ANH-R1) *would* close, if it fell, is the length-4-companion stratum
  outright** — a well-defined, non-empty chunk of `hK` — via §(K-Λ)'s Λ-completeness,
  since `dλ ≢ 0` makes `{λ = p⁺}` proper on an irreducible chart. That would be the
  first stratum an *argument* rather than a search delivers.

**Coverage, measured.** Over 4296 class (shape, split, length-4 companion) triples:
**3820 (89 %)** carry a length-5 branch of `H/P`, which is exactly where (ANH-7)'s
closed form applies (and exactly the triples carrying two consecutive free interior
bodies, so (ANH-5)'s collinearity corollary covers the same set). The remaining
**476** have every `H/P` branch of length `≤ 4`; there the branch screw is not pinned
by its own lines and the criterion needs `τ_β` itself. `girth(H/P) ≥ 6` at all but 8
triples, all of them θ(3,4,5).

### Verification

`notes/scripts/w4/annih.py` (**new with this section**; exact ℚ, stdlib only, no
CAS; a `w4/` leaf sitting beside `dominance`/`outer`/`sigma`/`closure`, importing
only catalogued §1 primitives — `dominance`'s `cycle_data` / `build_chart` /
`dV_rank` / `solve_multi` / `dC_along` / `base_seed`, `outer`'s `split_data` /
`companions4` / `named_inventory` / `sweep_shapes`, `repin`'s `hodge_star` /
`span_basis` / `in_span`, `pitch`'s `klein` / `Q` / `paths_graph`,
`nogood_subdiv`'s `deficiency` / `count_matroid_rank`, `kslide`'s
`no_rigid_branch_union`, and `lambda.HABITATS4` through `importlib`; the
composite `repin.star_generic` genericity guard rides in through
`dominance.base_seed`, since slice S2). All rng
seeded through `repin.seed_probe`'s integer seeds. Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --stress    # (ANH-1)
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --rate      # (ANH-2), (ANH-3), (ANH-5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --supp      # (ANH-4), realized side
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --recipe    # (ANH-7)
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --census    # (ANH-4) corollaries, (SD-6), coverage
PYTHONHASHSEED=0 python3 notes/scripts/w4/annih.py --validate  # the machinery
```

All six modes verified **byte-identical** under two different `PYTHONHASHSEED`
values (`0` and `999`), exit 0 at every one; runtimes at landing 8/9 s
(`--validate`), 30/30 s (`--stress`), 20/19 s (`--rate`), 81/87 s (`--supp`),
37/41 s (`--recipe`), 23/22 s (`--census`). Adding this driver modified no tracked
script, so the figure-invariance gate discharged on the
`git diff --name-only -- '*.py' '*.m2'` check alone (`notes/scripts/README.md`,
first bullet).

> **THE OWED §(K-ann) RE-READ, DONE 2026-08-06 (slice S2), and it is CLEAN.**
> `dominance.base_seed`'s genericity guard gained its coincident-hinge clause,
> so this section's seeds were re-drawn (`annih.py` is inside `flanks`' closure
> and all six modes re-ran). Result, exactly as F13's classification predicted
> for a section whose claims are **identities, ranks and pointwise
> attainments**: `--census` and `--validate` **byte-identical**; `--stress`,
> `--rate` and `--recipe` differ **only in which seed integer** each habitat's
> first clean draw is, with every dimension, rank, `yes`, "identity holds on all
> of them" and one-bracket verdict unchanged. **One figure improved**:
> `--supp`'s far block of `rank dλ` now attains (D2)'s bound `3(k−3)` at
> **every** seed, where the two contaminated `k = 6` draws used to report 5 and
> 7 of 9 — so *Step A4*'s "reproduces (D2)'s `3(k−3)`" is now an equality at
> every seed rather than at the clean ones. No (ANH-n) verdict moves.

Habitats: the four `lambda.HABITATS4` length-4-companion class shapes (θ(3,4,5),
NT21, NT24, NT30) plus the seven `dominance.HABITATS` (`k = 3..6`), plus **six swept
probes** — the first `(shape, split)` pairs of `outer.sweep_shapes`' `K4` family
whose `H/P` carries a length-5 branch, so (ANH-7) is tested on shapes nobody
hand-picked — plus one deliberate **off-class control**, `θ4(3,4,5,6)`, which is
tight with `def = 0`, `hcard` and triangle-free but **fails `hnoRigid`** (asserted at
load). The control is what makes the off-support tests non-vacuous: (ANH-4)'s
hypothesis is exactly what it violates, so its `H/P` is allowed the **proper**
circuit that no class shape has.

Per mode, what is asserted:

- `--stress`: `dim Z = dim mot(H) − 6`; the screw-circulation space has dimension
  exactly `k − 3`; it spans the **same** annihilator as the motion-side
  `nullspace(π_P Z)`; `H/P` is rigid both at the pencil placement
  (`dim(Z ∩ K^{E∖P}) = 0`) and combinatorially (`deficiency = 0`); the count
  `5|E(H/P)| − 6(|V|−1) = k−3`; `H` itself carries no self-stress.
- `--rate`: the reciprocity identity, direction by direction and `ω` by `ω`, against
  implicit differentiation of `ker N`; the locality of `dC`; the one-pairing form at
  every single-vertex move; and (ANH-5) **as a subspace identity** — that
  `(H_∞ ∧ U_y)^{⊥B}` is literally `⟨C(z₁z₂)⟩` — not merely as a coincidence of two
  booleans.
- `--supp`: `C_pen ⊆ C_gen` with `C_gen` from `count_matroid_rank` on `5(H/P)`;
  `C_pen` computed **twice** (from the full solve, and from a stress space rebuilt on
  the reduced edge list); `girth(H/P) ≥ 5`; the generic stress dimension `= k−3`; the
  closed form at every girth-5 case; and `dV = 0` at every single-vertex far move off
  `supp(τ)`.
- `--recipe`: `κ_β` is the 1-dimensional Klein-perp of the five branch lines;
  `τ_β ∝ κ_β`; the equivalence `κ_β ∝ C(w₁w₃) ⟺ [w₁,w₃,w₄,w₅] = 0`; the general
  `(V_y ∧ U_y)^{⊥B}` criterion; and, at `dim U_y = 2`, the one-bracket form.
- `--census`: `girth(H/P) ≥ 6` unless `|E(H/P)| = 5`; `E(H/P)` a circuit (budgeted);
  **every** `H/P` branch of length `≤ 5`; and the same generators re-run past length 6
  as an (SD-6) stress test.
- `--validate`: the Hodge dictionary `⟨★τ, C⟩ = B(τ, C)`; `λ` annihilates `π_P(Z)`;
  `λ ∈ row(N)`; transmissibility off `P`; and `V_bc` reconstructed from `Z` in the
  `C`-basis.

**Figures.**

| figure | value |
|---|---|
| `--stress` seeds | **18** over **9** habitats, `k = 3..6`; `dim(screw circulations) = k−3` and equal to the motion-side annihilator at every one; `dof(H/P) = def(H/P) = 0` at every one |
| `--rate` | the reciprocity identity at **276** far-chart directions × **828** motions, exact; the one-pairing form at **192** single-vertex moves |
| `--rate`: zero-pitch `ρ_y` | **0 / 192** — so it is one Klein pairing, never literally one 4-point bracket |
| `--supp` seeds | **16** (14 class + 2 control); `C_pen ⊆ C_gen` at all, with **equality** at all |
| `--supp`: `\|C_pen\|` vs `\|E(H/P)\|` at class seeds | equal at **14/14** — the support is the WHOLE far edge set, so the named move needs no support-location step |
| `--supp`: off-support single-vertex moves | **0** at every class seed (there are none), **13** at each control seed — and `dV = 0` at **13/13**, twice |
| `--supp`: `rank dλ` (far block) | **3** at all eight `k = 4` class seeds (and at both control seeds); **6** at both `k = 5` seeds; `9 / 5 / 9 / 7` at the four `k = 6` seeds — reproducing §(K-dom) *(D2)*'s `3(k−3)` through the annihilator, with the two sub-maximal `k = 6` values the usual non-generic seeds semicontinuity handles |
| `--recipe` sites | **56** (length-5 branch, free middle body); criterion correct at **56/56**, all with `dλ ≠ 0`; **32** with `dim U_y = 2` (one-bracket form), **24** with `dim U_y = 1` (general form) |
| `--recipe`: `[w₁,w₃,w₄,w₅] = 0` | **0 / 56** |
| `--census` triples | **4296** (shape, split, length-4 companion) over the named inventory + `outer.sweep_shapes` |
| `--census`: `girth(H/P)` | `{5: 8, 6: 2206, 7: 1822, 8: 260}`; all 8 girth-5 cases have `\|E(H/P)\| = 5`, i.e. `G = θ(3,4,5)` |
| `--census`: `E(H/P)` a circuit | certified at **400** triples (budgeted), no failures |
| `--census`: `H/P` branch lengths | `{1: 920, 2: 1924, 3: 3214, 4: 4184, 5: 6426}` — **max 5**, as (SD-6) predicts |
| `--census`: (SD-6) stress test past length 6 | θ3 to length 12, θ4 to length 12, `K4` to 7, `K4+par` to 7 — **identical shape counts** (2 / 0 / 540 / 740) and **max branch length still 5** |
| `--census`: coverage of the closed form | **3820 / 4296 = 89 %** carry a length-5 branch |
| determinism | all six modes byte-identical across two `PYTHONHASHSEED` values |

**Which driver tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (ANH-1) | `--stress` | the screw-circulation space and the motion-side annihilator are compared **as subspaces** at 18 seeds; `dof(H/P) = def(H/P) = 0`; the count `= k−3` |
| (ANH-2) | `--rate` | the identity itself, against an **independent** implicit differentiation of `ker N`, at 276 × 828 |
| (ANH-3) | `--rate` | the collapsed one-pairing form at 192 single-vertex moves, plus the zero-pitch census that keeps it from being over-claimed as one bracket |
| (ANH-4), combinatorial half | `--census` | the circuit certificate at 400 triples (budgeted) and both corollaries; the **proof** is the argument in *Step A4*, not the census |
| (ANH-4), realized half | `--supp` | `C_pen ⊆ C_gen`, equality at 16/16, full support at 14/14 class seeds, and the off-class control's proper 5-cycle with `dV = 0` off it |
| (ANH-5) | `--rate`, `--recipe` | the **subspace** identity `(H_∞ ∧ U_y)^{⊥B} = ⟨C(z₁z₂)⟩` at `dim U_y = 2`, and the general `(V_y ∧ U_y)^{⊥B}` criterion at both dimensions |
| (ANH-6) | `--stress`, `--recipe` | one screw per branch and its `B`-orthogonality to all `ℓ` lines; `κ_β` 1-dimensional at `ℓ = 5` |
| (ANH-7) | `--recipe` | the equivalence at 56/56 sites, on 6 swept shapes + 2 named exemplars + the control |
| (SD-6) | `--census` | branch-length histogram capped at 5 over 4296 triples, plus the past-length-6 stress test; the **proof** is elementary and lives in the *Shared dictionary* |
| **(ANH-R1)** | — | **none, and this is the point.** `--supp`/`--recipe` measure `τ_β ≠ 0` at the sampled placements (56/56, 14/14); *that the pencil placement can never shrink the support* is what no driver tests and what *Step A8* is about |
| (ANH-R2) | `--recipe` | `dim U_y` reported at all 56 sites (32 / 24) |

### Confidence verdict

- **(ANH-1)** (the annihilator is the self-stress space of `H/P`; `H/P` rigid;
  `dim = k−3`): **proven-informally**, length-free, with a driver mode asserting that
  sentence at 18 seeds over 9 habitats spanning `k = 3..6`, and three independent
  routes to `V_bc` agreeing in `--validate`. Its arc-level value is that **(T5) and
  (D2) stop being measured bounds**.
- **(ANH-2)** (the reciprocity identity) and **(ANH-3)** (the one-pairing form at the
  named move): **proven**, with a two-line derivation and 276 × 828 exact checks
  against an independent implicit differentiation. **This is the pass's headline**: a
  recipe in `Pencil-strategy.md` §2.2's sense, and the first the arc has produced.
  Quote it with its caveat — *the formula's kernel is bounded-size and
  class-uniform; what it pairs against (`τ`, `ω`) is not.*
- **(ANH-4)** (`E(H/P)` is a Tay circuit at `k = 4`): **proven-informally** from
  5/6-sparsity + `hnoRigid` + the tight count, `hnoRigid` read off the landed
  `Graph.IsProperRigidSubgraph`. Its two corollaries are verified independently over
  4296 triples, and one of them ((SD-6)) has its own elementary proof. **This is the
  pass's strongest positive** and the first class-uniform discharge of a needed
  non-vanishing's *combinatorial* half in the arc. It is `k = 4`-only, provably.
- **(ANH-5)**, **(ANH-6)**: **proven**, each with its own asserted driver sentence.
  (ANH-8) is **proven** and lives in the *Shared dictionary* as **(SD-6)**.
- **(ANH-7)** (the one-move, one-bracket recipe): **true-modulo-named-gap** — the gap
  is exactly **(ANH-R1)** `τ_β ≠ 0` (plus (ANH-R2) `dim U_{w₂} = 2` for the closed
  form). Verified at 56/56 sites, 0 failures, on 6 shapes nobody hand-picked plus 2
  named exemplars plus the control.
- **U1 as posed — "a single named far-chart move with a bracket formula for `dλ`,
  valid at every class member at `k = 4`": HALF DELIVERED, and the halves must not be
  conflated.** The **move** and the **formula** are delivered: named, bounded-size,
  class-uniform, no genericity hypothesis. The **inputs** are not: the formula pairs
  against `τ` and `ω`, and while (ANH-4) discharges what `τ`'s support must be
  *generically*, whether the pencil placement respects that is open. The answer to
  U1's own honesty flag: **the move is not per-shape, but its certificate is** — a
  strictly better position than the arc's other per-shape positives, and still not a
  proof.
- **(ANH-R1): OPEN, and its difficulty is unmeasured.** *Step A8* argues it is a
  relocation of a different *kind*; it does not argue, and this section does not
  claim, that it is *easier*.
- **Class uniformity is untouched. No gap-map *status* moves on this pass.** The
  (K-wit) row's *what would close it* cell gains (ANH-R1) as a named, scoped,
  `k = 4`-only sufficient route; the (K-dom) row gains (ANH-1) as the mechanism behind
  (D2).

### What would change this

*(i)* **A class habitat + seed with `τ_β = 0` on every length-5 branch** — that would
exhibit the pencil specialization genuinely shrinking `supp(τ)` at a class shape, kill
(ANH-7) as stated, and be a sharp new obstruction of the same species as §(K-pure)
*P6*'s `P21` exhibit. Not found: 56/56 sites and 14/14 class seeds have full support.
The off-class control shows the phenomenon is real once `hnoRigid` is dropped.

*(ii)* **A proof that the pencil placement cannot shrink `supp(τ)`** — i.e. that
`H/P − β` is pencil-rigid whenever it is generically isostatic. That is **(ANH-R1)**,
and it closes `dλ ≢ 0` at `k = 4` outright and, with §(K-Λ)'s Λ-completeness, the whole
length-4-companion stratum of `hK`. It is a **mixed-stratum** statement (§(K-ind)
*Step I6*: `X` is not a pencil body) on a strictly smaller graph, and it is the second
concrete consumer `Pencil-strategy.md` §4-C3 has, after (OUT).

*(iii)* **One of the 476 triples whose `H/P` branches are all of length `≤ 4`**, with
`dλ ≡ 0`. That is where the closed form does not reach, and it is the cheapest place to
look for a counterexample to non-constancy.

*(iv)* **A class shape with a branch of length `≥ 6`** — that would refute the *Shared
dictionary*'s (SD-6) and, with it, (ANH-4)'s second corollary. The proof is elementary
and the census stress test looked for one to length 12 (θ families) and 7 (`K4`,
`K4+par`) without finding any, but the sweep's hub multigraphs stop at `|V°| = 5`.

*(v)* **An error in the identification (ANH-1)** — guarded by three independent `V_bc`
routes, two independent `C_pen` routes, an independent implicit differentiation, and
the Hodge dictionary check, all in `--validate`/`--supp`.

*(vi)* **A `k ≥ 5` analogue of (ANH-4)** — measured true at 3 habitats but with no
proof, and provably not derivable from the count. Since the *target* does not transport
past `k = 4` (§(K-Λ) *Step 7*), this would be worth having only as part of a different
attack on `Gr(k−3,k)`.

## §(K-out) — (OUT)'s hypothesis, measured: the bad locus is **nonempty on every class shape's chart**, so no counting argument can ever deliver it ((OC-3)); availability is confirmed **pointwise** over two disjoint pools, the **combinatorial half does not deliver it**, and the pass surfaced a **harness defect** ((OC-7))

Answering §(K-Λ) *What would change this* item (viii) and §(K-Λ) *Step 5a*'s
*"(OUT)'s hypothesis has never been evaluated anywhere in the arc … That is a
**new driver mode**, not run by this pass."* Read against §(K-Λ), whose
notation this section inherits verbatim: (OUT), (Λ0a)–(Λ0i), (Λ0f′), (Λ1),
(Λ2), (Λ3) are all §(K-Λ)'s, and their qualified form is used here per
`notes/Pencil-labels.md` clause L3.

**Headline, negative first, because the negative is the load-bearing result.**

- **(OC-3) — no counting argument can ever deliver (OUT)'s hypothesis.** On the
  pencil chart `C₁ = C(b, x₁)` is confined to the 2-dimensional pencil `L_b` of
  lines through `pt(b)` inside the panel `Π(b)`, while the far relative twist
  space `R₁` does not see `pt(x₁)` at all; `dim R₁ = 5` then forces
  `dim(R₁ ∩ L_b) ≥ 5 + 2 − 6 = 1`. So **`{λ₁ = 0}` is nonempty at every class
  shape in the enumerated scope** — exactly one marked direction of `x₁`'s
  pencil — and no count, no matroid statement, and no argument that does not
  see the placement can ever conclude `λ₁ ≠ 0`. Verified on-chart at every
  frame it was computed: `dim R = 5` and `dim(R ∩ L) = 1`, never 2.
- **The combinatorial half does not deliver availability, and this must not be
  quoted as though it did.** **(OC-2)**'s clean 4296-pair result — uniform
  `χ = 0`, `def(H/X) = def(H/Y) = 0`, `(μ, dim R, A) = (1, 5, 0)` on both sides
  — collapses to **one** measured fact (rigidity of `H/X`; the rest is
  arithmetic), and `deficiency` is the ***ambient*-generic** count, which cannot
  see the chart confinement (OC-3) is about. It does **not** discharge (OUT).
- **The positives are real, and they are pointwise.** **(OC-5)** POOL-G (4
  habitats × seeds 200–299, 357 frames): distribution `322/17/17/1`; (OUT)'s
  hypothesis — the disjunction — holds at **356/357**, its *conclusion*
  separately verified at **356/356**, and (Λ0d) fails at **0/357** so the
  conditionality guard never fires in this pool. **(OC-6)** POOL-S (41 shapes /
  90 splits / 270 frames, **disjoint** from POOL-G): **270/270**, and **zero**
  (split, companion) pairs are silent at every probed seed. **(OC-1)** *Step
  5a*'s hinge-rate reading is exact and now driver-asserted:
  `λ₁ = 0 ⟺ C₁ ∈ V_bc ⟺ dim{m(b) − m(X)} = 1 ⟺ C₁ ∈ R₁`, at 46 frames.
  **(OC-4)** `--build` constructs `λ₁ = λ₄ = 0` at all four habitats keeping
  every (Λ0) clause, the target rank, `dim R_a = 1` and all four
  `IsNondegPencilRealization` conjuncts — at 3 of the 4 with **no** coincident
  hinge line — and `deg_t Q(z(t)) = 4` there, so **the escape holds exactly
  where (OUT) is blind**. (OUT) is therefore *never automatic*, and it is not
  contradicted.
- **(OC-7) is a harness defect and an escalation.**
  `widened.place_pencil_general`'s single-hub-interior sampler degenerates via
  `localtest.plane_basis` at **32 of 357** POOL-G frames (≈ 9 %), and that
  degeneracy **implies `λᵢ = 0`** (15/15 on the `b` side, 18/18 on the `c`
  side). **`flanks.star_span_ranks` — documented in its own docstring
  (`flanks.py:201`) as the genericity guard against exactly the `plane_basis`
  artifact, and invoked as that guard at `dominance.base_seed` (`dominance.py:554`)
  — does not catch it, and no `IsNondegPencilRealization` conjunct excludes
  it.**
  Restricted to the **318 coincidence-free** frames the distribution is uniform
  (`318/318`).
- **(OC-8), the residual, is OPEN.** Class uniformity of (OUT) ⟺ at every class
  shape the whole-graph chart carries a hard-stratum point with `L_b ⊄ R₁` or
  `L_c ⊄ R₄` — a rank **lower** bound at a pencil placement, i.e.
  `notes/Pencil-strategy.md` §2.3's wall **relocated** onto the smaller
  `H/{e₂,e₃,e₄}` and **weakened, not crossed** — and (OC-3) says the relocation
  cannot be discharged combinatorially.

> **Standing rule for the whole arc, not a note on one table.** **No
> `place_pencil_general`-sampled battery may be quoted as a *rate*, or as
> evidence about a *generic* chart point.** Pool figures from this section are
> quoted over the **318 coincidence-free** frames, never the raw 357, and the
> same applies to every other habitat battery in the harness that draws through
> that sampler. What such a battery still supports unharmed is a *negative*
> (`0 hits`) or a *positive existence witness*: a degenerate draw can create
> neither a false hit nor a false witness. It is the **rate** reading, and only
> that reading, the defect destroys. Harness-side record:
> `notes/scripts/README.md` *Harness debt* item 4 and §4 convention 1.

**Verdict, stated at the strength the measurement supports: this is
availability, MEASURED, not proven.** What the section mainly establishes is
the negative (OC-3) plus a per-shape existence result; do not write it warmer
than that.

### Standing notation (on top of §(K-Λ))

`H := G − v − a`; the length-4 companion `P = b–x₁–x₂–x₃–c` with lines `C_i`,
`S = ⟨C₁,…,C₄⟩`, `V_bc ⊆ S` of dimension 3, and `λ ∈ S*` its annihilator, so
`λ_i = λ(C_i)` and `λ_i = 0 ⟺ C_i ∈ V_bc`. Write

- `X := {x₁, x₂, x₃, c}` and `Y := {b, x₁, x₂, x₃}` — the two **welds**;
- `μ₁` := the number of `H`-edges between `b` and `X` (`μ₄` symmetrically);
- `W₁` := `{m(b) − m(X)}` in `H` with `X` welded — the relative twist space
  §(K-Λ) *Step 5a* names;
- `R₁` := the same in `H − e₁` with `X` welded — the **far** relative twist
  space, which the placement of `x₁` does not enter;
- `L_b := α_{pt(b)} ∩ β_{Π(b)}` — the **2-dimensional pencil** of lines through
  `pt(b)` inside the panel `Π(b)`. Every nonzero element is a genuine line of
  that pencil (`b ∧ u` is decomposable), so every one of them is realizable as
  `C(b, x₁)` for a legal placement of `x₁`.

Welding is imposed as explicit equality rows on the rigidity matrix, never by
contracting the graph: a contracted edge would lose its hinge *line*, and the
hinge lines are the entire content here.

### Step O1 — (OC-1): the hinge-rate reading, made exact

§(K-Λ) *Step 5a* asserts the reading in one line and leaves it untested. It is
exact, needs no genericity beyond §(K-Λ) (Λ0a), and now has a driver.

> **(OC-1)** At any placement with `C₁,…,C₄` independent ((Λ0a)):
> `λ₁ = 0` ⟺ `C₁ ∈ V_bc` ⟺ `dim W₁ = 1` ⟺ (when `μ₁ = 1`) `C₁ ∈ R₁`.
> Symmetrically on the `c` side with `Y`, `W₄`, `R₄`, `e₄`.

*Proof.* `λ₁ = λ(C₁)` and `V_bc = ker λ ∩ S` give the first equivalence for
free. For the second: a relative twist has *unique* companion coordinates by
(Λ0a), so `m(b) − m(c) = C₁` forces `ω = (1,0,0,0)`, i.e.
`m(x₁) = m(x₂) = m(x₃) = m(c)` — `X` is welded — and conversely any motion of
`H` with `X` welded has `m(b) − m(c) = m(b) − m(X) ∈ W₁`. For the third: with
`μ₁ = 1` the only `b`–`X` hinge is `e₁`, so `W₁ = R₁ ∩ ⟨C₁⟩`, which is nonzero
iff `C₁ ∈ R₁`. ∎ (With `μ₁ ≥ 2` the intersection of two distinct hinge lines is
`0`, so `λ₁ ≠ 0` — §(K-Λ) *Step 5a*'s "further `b`–`X` edges only make `b` more
attached", now with its reason.)

*Exact, per frame:* `--pool` asserts the whole chain at **46** POOL-G frames —
every frame with `λ₁ = 0` or `λ₄ = 0` plus three controls per habitat — with
`(μ₁, dim W₁, dim R₁, dim(R₁ ∩ L_b) | μ₄, dim W₄, dim R₄, dim(R₄ ∩ L_c))`
taking only the four values `(1, ε₁, 5, 1 | 1, ε₄, 5, 1)`, `ε ∈ {0,1}`, and
`dim W = 1` occurring exactly when the corresponding `λᵢ` vanishes.

### Step O2 — (OC-2): the combinatorial availability map, and what it does *not* say

`nogood_subdiv.deficiency` gives the **ambient-generic** value of every
dimension above, via `dim Mot(G) = 6 + def(G)` and the fact that welding two
bodies is vertex identification: the generic dimension of `{m(u) − m(w)}` is
`def(G) − def(G/uw)`. Write `A₁ := def(H/X) − def(H/(X ∪ {b}))`, the
ambient-generic value of `dim W₁`.

> **(OC-2)** Over the enumerated class scope — the four certified
> length-4-companion habitats, the 19-shape named inventory, and the whole
> systematic sweep `outer.sweep_shapes()` (1357 class shapes), **4296
> (split, companion) pairs in all** — the map is *uniform*:
> `χ = 0` (the companion has no chord), `def(H/X) = def(H/Y) = 0`, and
> `(μ₁, dim R₁, A₁, μ₄, dim R₄, A₄) = (1, 5, 0, 1, 5, 0)` at every pair.

**The map collapses to one measured statement.** With `χ = 0` the arithmetic is
forced: `H` has trivial-partition count `6(|V(H)|−1) − 5|E(H)| = 3`, and welding
`X` removes 3 vertices and 3 edges, so `H/X` is **tight** (count `5χ = 0`;
asserted per pair). Then rigidity of `H/X` gives `A = 0` (a contraction of a
rigid graph is rigid) *and* `dim R = 5` (deleting one independent edge of a
tight rigid graph costs exactly 5). Tightness is arithmetic; **rigidity of
`H/X` is not**, and it is what the 4296 `deficiency` calls measure.

**What this does not say, stated because a one-line quotation will get it
wrong.** `deficiency` is the **unconstrained** generic count. The pencil chart
is a proper subvariety of the placement space, so `A₁ = 0` is *not* evidence
that `λ₁ ≠ 0` at a pencil-generic placement — it is the ambient-generic
statement, and the gap between the two is precisely
`notes/Pencil-strategy.md` §2.3's asymmetry. **The combinatorial half therefore
does not deliver availability.** Step O3 is where the pencil constraint enters,
and it changes the answer qualitatively.

### Step O3 — (OC-3): on the pencil chart the bad locus is **always nonempty** (the load-bearing negative)

`C₁` is not a free line of `P³`. `x₁ ∈ N_{G′}(b)`, so `pt(x₁) ∈ Π(b)` and
`C₁ = C(b, x₁)` is confined to the 2-dimensional pencil `L_b`. Since `R₁` does
not involve `pt(x₁)`, and `μ₁ = 1`:

> **(OC-3)** `λ₁ = 0 ⟺ C₁ ∈ R₁ ∩ L_b`, and
> `dim(R₁ ∩ L_b) ≥ dim R₁ + dim L_b − 6 = 5 + 2 − 6 = 1`.
> So with everything but `pt(x₁)` held fixed there is **always at least one
> direction of `x₁`'s pencil that kills `λ₁`** — the bad locus of (OUT)'s first
> disjunct is nonempty on the chart of every class shape with `dim R₁ = 5`,
> which by (OC-2) is every shape in the enumerated scope. Measured
> `dim(R₁ ∩ L_b) = dim(R₄ ∩ L_c) = 1` **exactly** — never 2 — at all 46
> POOL-G frames of *Step O1*, so the locus is also **proper**: `λ₁ ≢ 0` along
> the `x₁`-slide at every measured chart point.

This is the (OUT) analogue of §(K-Λ) (Λ0g)/(Λ0i) for `g₁₄`, with the signs
reversed: (Λ0i) shows the `g₁₄` clause is *implied by* (Λ0d) wherever a
companion end is free, whereas (OC-3) shows the `λ₁` clause is **never** implied
by anything combinatorial. **That is the load-bearing negative of this
section:** a class-uniform proof of (OUT)'s hypothesis cannot be a count, a
matroid statement, or any argument that does not see the placement — because
the bad set is nonempty at every shape, and is exactly one point of a `P¹`.

`dim R₁ = 5` is itself the ambient-generic value; it was *measured* to hold at
the pencil placement at 46/46 frames, and that is the only sense in which the
pencil chart has been checked not to inflate it.

### Step O4 — (OC-5): the measurement (POOL-G)

POOL-G is the four `lambda.habitat_specs` habitats × placement seeds
**200–299** — deliberately the same integer pool `lambda.py --adv` uses for its
habitat leg. A frame is kept when the placement is target rank with
`dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4` and `star_span_ranks` green;
**(Λ0d) failures are kept and reported rather than dropped**, because that is
precisely where (OUT) stops applying. 400 seeds give **357 frames** (16 with no
placement, 27 rejected by the star-span guard); on a fixed 20-frame subsample
`λ` is asserted identical up to scale to `lambda.habitat_frame`'s.

| `(λ₁ = 0, λ₄ = 0)` | reading | count |
|---|---|---|
| `(0, 0)` | both outer coordinates nonzero — (OUT) applies | **322** |
| `(1, 0)` | `λ₁ = 0` only — (OUT) still applies, via `C₄` | 17 |
| `(0, 1)` | `λ₄ = 0` only — (OUT) still applies, via `C₁` | 17 |
| `(1, 1)` | **both vanish — (OUT) SILENT** | **1** |

Per habitat: θ(3,4,5) 98/99, NT21 89/89, NT24 91/91, NT30 78/78.

- **(OUT)'s hypothesis holds at 356 of 357.**
- **(OUT)'s conclusion is verified, separately, at 356 of 356** frames where the
  hypothesis holds and (Λ0)+(Λ0f′) are green: `λ ∦ p⁺`, `λ ∦ q`, and
  `Q(z(t)) ≢ 0` along the `a`-line. This is the sentence (OUT) actually
  asserts, and it is now driver-tested rather than inherited from (Λ2).
- `λ ∝ p⁺`: **0**. `λ ∝ q`: **0**. `(Λ0d)` fails at **0 of 357**, so the
  conditionality warning never fires in this pool.
- Codimension-1 calibration over the *same* pool: `g₁₃`, `g₁₄`, `g₂₄`, `p⁺₂`,
  `p⁺₃`, `q₂`, `q₃` and (Λ0d) vanish at **0/357** each; `λ₁` and `λ₄` at
  **18/357** each. *Step O5* explains the whole of that gap — **and forbids
  reading either as a rate.**

**The single silent frame, in full.** θ(3,4,5) **seed 233**: (Λ0a)–(Λ0f′) all
green, `λ ∦ p⁺`, `λ ∦ q`, `deg_t Q(z(t)) = 4` — so the escape holds there by the
pitch certificate and (OUT) simply cannot see it. It is also doubly
sampler-degenerate (*Step O5*), which is why *Step O6* exists.

### Step O5 — (OC-7): every failure is a coincident hinge line, most are manufactured, and the documented guard does not fire

> **(OC-7)** At **all 35** POOL-G frames with `λ₁ = 0` or `λ₄ = 0`, the
> vanishing outer line **coincides projectively with another hinge line at its
> hub**: `C(b, x₁) = C(b, u)` for some `u ∈ N_{G′}(b) \ {x₁}`, i.e.
> `pt(b), pt(x₁), pt(u)` collinear. Moreover — **asserted per frame, and the
> driver prints all 36 rows** (36 side-events over 35 frames; seed 233 carries
> both) — the coincidence list *exhausts* the hub's other `H`-neighbours at
> every one: the hub's whole hinge pencil has collapsed to a single line, so the
> hub is a **free rotor** about it and `ω C₁ ∈ V_bc` for trivial reasons. The
> converse fails (2 frames per side carry a coincidence with `λᵢ ≠ 0`), so the
> coincidence is necessary, not sufficient. Restricted to the **318**
> coincidence-free frames the distribution is `(0,0) : 318` — a clean
> `318/318`.

> **(OC-9)** *(new 2026-08-06, slice S2 — the FIELD half of the coincident-hinge
> guard's adversarial test; driver leg `--pool`)* The composite guard
> `repin.star_generic` **rejects 58 of the 357** POOL-G frames, and its
> rejection set **strictly contains** the two-end diagnostic's 39 (asserted
> frame by frame, 0 violations): **19 further frames** are coincidence-free at
> `b` and `c` and carry a coincidence somewhere else in the configuration, and
> the driver prints all 19 with their coincidence lists. So the plan's
> expectation that the guard's output *equals* the hand-restriction is
> **refuted, in the safe direction**: the guard is the wider test.
> Consequences, both recorded because they point opposite ways. (i) The 318
> restriction is **not wrong** — every `λᵢ = 0` frame carries a coincidence at
> the hub its coordinate belongs to (the assertion above), so all 19 extra
> frames have both outer coordinates nonzero and the `318/318` reading is
> unaffected. (ii) But the **strictest** sub-pool this harness can certify is
> the guard's own **299 of 357**, whose distribution the driver now also prints
> (`(0,0) : 299`), and a rate quoted over 299 is the one that needs no
> hand-restriction argument at all.

**Where the coincidences come from.** `widened.place_pencil_general` places
every *single-hub interior* through `localtest.in_plane_point`, whose
`plane_basis` is the **degenerate** member of the README's *Divergences* table:
for some normals it returns two **parallel** in-plane directions, and then every
single-hub interior of that hub lands on **one line** through `pt(h)`. Measured
implication, per side:

| | sampler degenerate at the hub | `λᵢ = 0` | count |
|---|---|---|---|
| `b` | no | no | 339 |
| `b` | no | **yes** | 3 |
| `b` | **yes** | **yes** | **15** |
| `c` | no | no | 339 |
| `c` | **yes** | **yes** | **18** |

So the degeneracy **implies** `λᵢ = 0` (15/15 and 18/18, no exceptions), and 33
of the 36 coordinate-vanishing events in POOL-G are manufactured by it. The
remaining 3 (θ(3,4,5) seeds 205, 225, 280, all `λ₁ = 0`) are ordinary rng
coincidences of the same geometric type. The driver prints the union directly:
**32 of the 357 frames have a degenerate in-plane sampler at `b` or at `c`**
(both at 1, θ(3,4,5) seed 233 — which is exactly the silent frame).

**Three things this costs the harness, stated precisely.**

1. **`flanks.star_span_ranks` is not the guard its docstring says it is.** Its
   docstring (`flanks.py:201`) says rank 3 at every vertex is *"simultaneously
   the genericity guard against the `plane_basis` artifact and
   `IsNondegPencilRealization`'s fourth conjunct"*, and every consumer invokes
   it under exactly that reading (`dominance.py:554`, `annih.py:67`,
   `outer.py`, `sigma.py`). It passes at all 33 manufactured frames, because a
   hub's star still spans its panel through a *third* neighbour (here `pt(a)`, which
   sits on the meet line `M` and is placed by a different branch). Nor does any
   of the four conjuncts of `IsNondegPencilRealization`, as
   `flanks.nondeg_conjuncts` implements them, exclude two coincident hinge lines
   at a hub. The cheap correct guard is the one this driver uses: **no two hinge
   lines at a hub coincide.** This is the **second** recorded `plane_basis`
   contamination (the first, 2026-08-02, is the `(K-tight)` re-pin's sampler
   artifact — `notes/dispatch-log.md`) and the **first where the documented
   guard failed**; it is `notes/scripts/README.md` *Harness debt* **item 4**.
   **REPAIRED 2026-08-06** by the re-baselining round: slice S1 defined the
   composite guard `repin.star_generic` with a constructed adversarial witness
   (`repin.py --hinge`), slice S2 adopted it at every acceptance site in
   `w4/` — this driver's two modes deliberately excepted, because they are the
   measurement — repaired all four falsified docstrings, and added the FIELD
   half of the adversarial test here, (OC-9). The finding stands as measured;
   what changed is that the harness now rejects the configuration everywhere it
   is not being measured.
2. **No recorded figure moves, and the reason is one-directional.** Every
   `place_pencil_general`-sampled figure in the arc that this could touch is
   either a *negative* (`0 hits for λ ∝ p⁺`, `0 hits for Q(z) = 0`) or a
   *positive existence witness* (`g₁₄ ≠ 0` at a chart point, refuting forcing);
   a degenerate draw can create neither a false hit nor a false witness. What it
   does damage is any reading of those batteries as **rates** or as evidence
   about a *generic* chart point — hence the standing rule in this section's
   headline block: **32 of 357 (≈ 9 %)** of the habitat frames here are drawn
   from a strictly non-generic sub-family.
3. **§(K-ann) was flagged for a CHECK, not accused of an error — and the check
   was DONE on 2026-08-06 (slice S2) and came back CLEAN** (§(K-ann)
   *Verification*, the re-read blockquote). `annih.py:67`
   took its genericity guard from the same `star_span_ranks`, through
   `dominance.base_seed`, so it inherited the same exposure. The asymmetry that
   decides which figure classes are exposed, recorded so a successor does not
   have to re-derive it: **§(K-ann)'s claims are identities and structural facts
   verified at every tested frame** (`def(H/P) = 0`, stress dimension `= k − 3`,
   the reciprocity identity, full support), so including degenerate frames makes
   them **harder** to satisfy, not easier — the defect is *conservative* there —
   **whereas this section's are rates**, which the defect distorts. The claim
   that would need re-running under the new guard is any §(K-ann) statement read
   as *generic* rather than *pointwise*. **Done, clean** — see item 3's
   opening sentence.

### Step O6 — (OC-4): (OUT) silent at a **nondegenerate** chart point

(OC-3)'s marked direction is *constructible*. In the §(K-Λ) (Λ0i) free-end
pattern `pt(x₁)`'s only chart constraint is `pt(x₁) ∈ Π(b)`, so aiming it along
`R₁ ∩ L_b` is legal; and the two ends are **independent**, because welding
`Y = {b,x₁,x₂,x₃}` for the `c`-side computation absorbs `e₁` and `e₂`, so
`pt(x₁)` does not enter `R₄` (and symmetrically). `--build` slides both at
once.

> **(OC-4)** At all four certified habitats, at placement seed 200 and slide
> parameters `(t₁, t₃) = (1, 1)`, the result is an exact chart point with
> `λ₁ = λ₄ = 0` — **(OUT) SILENT** — at which
> `C₁, C₄ ∈ V_bc`; (Λ0a)–(Λ0e) all hold; both middle brackets of `p⁺` and of
> `q` survive ((Λ0f)); `g₁₃, g₁₄, g₂₄ ≠ 0` ((Λ0f′)); the placement is still
> target rank (54 / 114 / 114 / 144) with `dim R_a = 1`, `dim V_bc = 3`,
> `dim Mot(H) = 9`; **all four `IsNondegPencilRealization` conjuncts hold**;
> and `λ ∦ p⁺`, `λ ∦ q`, `deg_t Q(z(t)) = 4`.

**And at 3 of the 4 the point carries no coincident hinge line at `b` or `c`**
(NT21, NT24, NT30), so the locus is reached without collapsing any hub's hinge
pencil: the phenomenon is real, not only the artifact of *Step O5*. At θ(3,4,5)
it *is* the artifact — `b` has only two `H`-neighbours there, so `R₁ ∩ L_b`
is forced to be `⟨C(b, y₁)⟩` and the marked direction aims straight at the far
neighbour (driver prints `aims at [[17], [20]]`). That is also why θ(3,4,5)
alone contributes non-manufactured sampled hits: at a degree-2 `b` the bad
direction is a *first*-neighbour coincidence, which small rational sampling
occasionally meets.

Read together with *Step O4*: **(OUT) is strictly weaker than §(K-Λ) (Λ2)**, and
now with a witness. §(K-Λ) *Step 5a*'s own "sufficient, never necessary … silent
on the whole line" is confirmed at an exhibited nondegenerate point, not merely
argued.

### Step O7 — (OC-6): shape-level availability, which is what the route needs

(OUT) is a per-*seed* sufficient condition and the escape needs *some*
target-rank seed, so the question that matters is per shape.

> **(OC-6)** POOL-S — the 19-shape named inventory plus the first 4 shapes of
> each `outer.sweep_shapes()` family (41 class shapes), every eligible split,
> placement seeds 1–39, ≤ 3 hard-stratum frames per split, every length-4
> companion — gives **270 frames over 90 (split, companion-bearing) splits**.
> Distribution `(0,0) : 254`, `(1,0) : 8`, `(0,1) : 8`, `(1,1) : 0`. **(OUT)'s
> hypothesis holds at 270 of 270**, and **0** (split, companion) pairs have no
> available frame. 16 of the 270 carry a coincident hinge line, and every
> `λᵢ = 0` frame is one of them (asserted).

POOL-S is **disjoint from POOL-G** and its figures are never summed with
POOL-G's.

### Step O8 — a denominator correction to §(K-Λ) *Step 5a*

§(K-Λ) *Step 5a* recorded *"`--adv` reports `λ ∝ p⁺` and `λ ∝ q` at **0 of 1497**
frames"* (and its *Verification* table carried the same denominator). By code
reading of `lambda.py --adv`, those tests run **only inside the habitat loop**,
whose pool is seeds 200–299 at 4 habitats — at most **400** frames. The
remaining count comes from the local-strata loop, where `sample_local_frame`
deliberately leaves the far covector **free**: those frames carry no `λ` at all.
The strata leg's maximum is exactly `38 strata × 30 seeds = 1140`, and
`357 + 1140 = 1497`, consistent with POOL-G's 357 and with zero strata
rejections. So the `λ`-bearing denominator behind the recorded `0 of 1497` is
**`≤ 400`**, not 1497. Nothing about the *result* changes — 0 hits is 0 hits —
but the figure is quoted with the smaller denominator, here and at the two other
sites that carried it (§(K-Λ) *Verification*, `notes/scripts/w4/README.md`).

*One extension of the correction, from the same code read and flagged as this
pass's own:* `Q(z) = 0` is computed in the habitat loop too, so its `0` carries
the same `≤ 400` denominator. `C(M) ∈ S` and the `(span ω⁺, span ω⁻)` histogram
**do** run over all 1497 frames, and §(K-Λ) *What would change this* item (iii)'s
"6 of 1497" is therefore correct as written.

### Verdict

**Availability: CONFIRMED at the probed scope; class uniformity OPEN, and now
demonstrably out of reach of any counting argument.** Component by component:

| | claim | standing |
|---|---|---|
| **(OC-1)** | the hinge-rate reading, as an exact equivalence chain | **proven-informally** (two lines, no genericity beyond (Λ0a)); driver-tested at 46 frames |
| **(OC-2)** | `χ = 0`, `H/X` tight and rigid, hence `(μ, dim R, A) = (1,5,0)` on both sides | tightness **proven** (arithmetic); rigidity **measured** at 4296 pairs over an enumerated, non-exhaustive scope. **Ambient-generic — it does not discharge (OUT)** |
| **(OC-3)** | `{λ₁ = 0}` nonempty on every chart, exactly one direction per pencil | **proven-informally** given `dim R = 5` (pure linear algebra); `dim R = 5` and `dim(R ∩ L) = 1` measured on the pencil chart at 46 frames. **The section's headline** |
| **(OC-4)** | an (OUT)-silent nondegenerate chart point | **exhibited**, 4 habitats, 3 of them coincidence-free |
| **(OC-5)/(OC-6)** | the distributions | **measured**, pointwise, over two disjoint pinned pools; POOL-G's rates only over the 318 coincidence-free frames |
| **(OC-7)** | every failure is a coincident hinge; 33/36 manufactured; the documented guard misses it | **measured**, with the implication asserted per frame; **a harness defect, escalated — and CLEARED 2026-08-06 by the re-baselining round's slices S1/S2** |
| **(OC-9)** | the composite guard rejects **58/357** and its rejection set strictly contains the two-end diagnostic's 39 (19 extra, printed) | **measured**, asserted per frame — the FIELD half of the guard's adversarial test |
| **(OC-8)** | the residual (below) | **OPEN** |

> **(OC-8) what (OUT) now reduces to, exactly.** Class uniformity of (OUT) at
> length-4-companion splits is *equivalent* to: at every class shape, the
> whole-graph pencil chart carries a hard-stratum target-rank point with
> `L_b ⊄ R₁` or `L_c ⊄ R₄`. That is a rank **lower** bound at a pencil
> placement — the class of statement `notes/Pencil-strategy.md` §2.3 identifies
> as the arc's wall — relocated onto the *smaller* graph `H/{e₂,e₃,e₄}` and
> *weakened* (it asks for one constraint between `b` and `X`, not the full
> escape), but **not crossed**. (OC-3) shows the relocation cannot be discharged
> combinatorially: the bad set is nonempty at every shape, so any proof must be
> a genericity argument on the **whole-graph** chart, and that needs the
> chart's irreducibility (or at least that its hard-stratum component is not
> contained in `{λ₁ = 0} ∩ {λ₄ = 0}`) — which the arc has never established,
> because `λ` is a far datum and §(K-Λ)'s class-uniformity bridge is about the
> *local* frame only.

**This measurement is informative, not decisive, and the reason is sharper than
"it is pointwise."** It measures a hypothesis never measured, so it is not a
re-run of a saturated question (`notes/Pencil-strategy.md` §5.2). But what it
can establish is *availability* — that (OUT) is not vacuous and not dead —
whereas what (OUT) as a route needs is *uniform* availability, and (OC-3) shows
that the natural cheap route to uniformity (a count on the contracted graph) is
structurally unavailable. A clean `n/n` here must not be read as more than: at
every shape we could place exactly, (OUT) applies at a generic hard-stratum
seed.

### What would change this

1. **A class shape with `dim R₁ = dim R₄ = 6`** would kill both disjuncts
   identically and make (OUT) *dead* there. `--comb` finds none in 4296 pairs
   and the arithmetic (*Step O2*) says it needs `H/X` non-rigid, hence a chord
   (`χ ≥ 1`) or a count violation. Extending `--comb` past the `|V°| ≤ 5`
   caps and the `lmax` bounds of `outer.sweep_shapes()` is cheap (14 s for the
   present scope) and is the first thing to widen.
2. **A class shape with `dim R₁ ≤ 4` or `μ₁ ≥ 2`** would make the first
   disjunct hold at *every* chart point, closing (OUT) unconditionally there —
   a genuine partial closure. None in 4296 pairs, and *Step O2*'s arithmetic says
   `χ = 0` forces `dim R = 5`, so this needs a chorded companion.
3. **`L_b ⊆ R₁` at a chart point** would put a whole pencil's worth of `x₁`
   placements on the bad locus; measured `dim(R₁ ∩ L_b) = 1`, never 2, at 46
   frames. A hit would sharpen (OC-8) from "not automatic" to "sometimes
   forced".
4. **Pushing the constructed point from the bad *line* to the bad *point*
   `p⁺`.** (OC-4) lands `λ` on `{λ₁ = λ₄ = 0}` with both slide parameters
   spent; the residual chart freedom (`pt(x₂)`, the far graph) is untouched. A
   `λ ∝ p⁺` hit at a nondegenerate hard-stratum point is §(K-Λ) *Step 4*'s
   genuine (T3) escape failure — **not** a disproof of the pencil conjecture,
   since a constructed point is not a generic realization, and it should not be
   reported as one. Deliberately not attempted here.
5. **Re-running any `place_pencil_general`-sampled battery under the
   coincident-hinge guard.** (OC-7) says ≈ 9 % of habitat frames are non-generic
   in a way no existing guard catches. The right fix is the coordinator's
   deliberate re-baselining commit (`notes/scripts/README.md` *Harness debt*,
   which now carries this as item 4), not a research dispatch's side errand.
6. **Symbolic (Macaulay2) treatment of `R₁ ∩ L_b` on the local frame.** `R₁` is
   a far object, so `m2/lambda0.m2`'s gauge slice does not reach it; but the
   *statement* `dim(R₁ ∩ L_b) = 1` is a `5 + 2` transversality in `K⁶` and
   would follow from `L_b ⊄ R₁` as a polynomial non-vanishing. That is the one
   piece of (OC-8) that looks symbolically tractable
   (`notes/Pencil-strategy.md` §5.3).

### Verification

`notes/scripts/w4/outerline.py` (tracked, new this pass; exact ℚ; a `w4/` leaf
beside `flanks`/`pure`/`lambda`/`dominance`/`outer`/`sigma`, importing only
catalogued §1 primitives and **modifying nothing**). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --comb     # (OC-2)
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --pool     # (OC-1),(OC-5),(OC-7)
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --shapes   # (OC-6)
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --build    # (OC-3),(OC-4)
```

Times as landed: `--comb` 14 s, `--build` 10 s, `--pool` 358 s, `--shapes`
322 s. All four re-run **byte-identical** under two different `PYTHONHASHSEED`
values. `--pool` and `--shapes` do **not** fit together in one 600 s
foreground budget; run them separately.

**Pools, pinned; every figure above is quoted over exactly one of them and none
is aggregated across two.**

- **POOL-C** (`--comb`) — deterministic, no rng: the 4 `lambda.habitat_specs`
  habitats, `outer.named_inventory()`, and every family of
  `outer.sweep_shapes()`. 4296 (split, companion) pairs.
- **POOL-G** (`--pool`) — the 4 habitats × placement seeds **200–299**;
  357 frames, of which the **318** coincidence-free-at-the-companion-ends ones
  are a legitimate denominator for a rate (the standing rule above) and the
  **299** the composite guard accepts are the strictest one ((OC-9),
  2026-08-06). The frame set itself is deliberately **not** guard-restricted:
  the coincidence is what (OC-7) measures, so `--pool` reports it instead of
  rejecting it — slice S2's per-site adoption judgement.
- **POOL-S** (`--shapes`) — 41 class shapes × every eligible split × seeds
  **1–39**, ≤ 3 frames per split; 270 frames.
- **POOL-B** (`--build`) — the 4 habitats × seeds **200–259**; slides from the
  fixed list `1, 2, −1, 3, 1/2, 5, −3, 7`; all four constructions land at seed
  200, slides `(1,1)`.

The only rng is `random.Random(seed)` inside `widened.place_pencil_general`.
The aux point `w` is fixed at `(1, −2, 5)`; the pencil `L_h` and every marked
direction come from `repin.robust_plane_basis` and are **deterministic**.

*Figures-do-not-move gate* (`notes/scripts/README.md`): the pass that opened
this section **added** a driver and modified none, so the gate discharged by
the check itself. **Re-baselined 2026-08-06 (slice S2)**, which did modify
`outerline.py`: `--comb` and `--shapes` came back **byte-identical**; `--pool`
gained the (OC-9) block and `--build` one reported line per construction (the
composite guard's verdict, `False` at exactly the one non-coincidence-free
construction, `True` at the other three — so (OC-4)'s `3 of 4` is now the
guard's own count and not a hand-count). The transient duplicate
`outerline.hinge_coincidences` was retired in the same commit and this file's
copy is now `repin`'s.

Per mode, what is asserted:

- `--comb`: per pair, the `5χ` count identity for `H/X`; `def(H/X)`,
  `def(H/Y)`; `μ`, `dim R`, `A` on both sides; the uniformity of the histogram;
  and that no pair kills both disjuncts.
- `--pool`: per frame, `λᵢ = 0 ⟺ C_i ∈ V_bc`; the full (Λ0a)–(Λ0f′) clause
  battery; (OUT)'s **conclusion** (`λ ∦ p⁺`, `λ ∦ q`, `Q(z(t)) ≢ 0`) wherever
  its hypothesis holds and the clauses are green; the codimension-1 rates of
  every (Λ0) bracket over the same pool; the (OC-1) chain at 46 frames; the
  (OC-7) implications *degenerate sampler ⟹ `λᵢ = 0`* and *`λᵢ = 0` ⟹
  coincident hinge*, both as per-frame asserts; the **free-rotor exhaustion**
  (the coincidence list contains every other `H`-neighbour of the hub) as a
  per-frame assert at all 36 rows, each printed; and `λ` agreement with
  `lambda.habitat_frame` at 20 frames.
- `--shapes`: the same `λ` measurement per shape, plus that no (split,
  companion) pair is silent at every probed seed.
- `--build`: the construction, every (Λ0) clause at the constructed point, the
  target rank and `dim R_a = 1`, all four `IsNondegPencilRealization`
  conjuncts, `λ` off both bad points, `deg_t Q(z(t)) ≥ 0`, and that ≥ 3 of the
  4 constructions carry no coincident hinge line.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean
(`DESIGN.md` *Formalize everything the argument uses*). Nothing in `lambda.py`
or `outer.py` was modified; both are read.

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

## §(K-grid) — the tight-stratum grid residual: the direction network becomes a **generalized-spline** problem, the "(AC-4)(i)–(ii) ⟹ isostatic" statement is **REFUTED as named**, its correction is a pair of **proven counting obstructions** that are **empirically exact**, chart-image membership is **proven and machine-verified**, and the census extends 15/15 to **907/907**

Read against §(K-clos): this section discharges the two deliverables its
(AC-6) verdict block names for the tight stratum — *Step Z4*'s direction
network, and the chart-image membership left "argued, not verified" — and
runs the cheap kill its *what-would-change-this* line asks for. Notation
inherited from §(K-clos) *Steps Z2–Z6*: `⋆`, the fixed quadric `Q`, the
ruling 2-colouring `col : E(G) → {A, B}`, the eigenspaces `Λ²₊`/`Λ²₋`, the
per-ruling-component parameters of the grid construction. Everything here is
over `ℚ(i) ⊂ ℂ̄`; descent is (AC-7)'s and is quoted, not re-derived.

**Status, stated before the mathematics.**

- **Refuted — the gap-map sentence as literally written.** The *State of (K)*
  map asked for *Step Z4*'s contracted direction network "proven isostatic
  whenever (AC-4)(i)–(ii) hold". That statement is **false**, and was already
  false in the pinned data: 8 of `ds-K4`'s 64 colourings are balanced with
  both ruling classes forests and sit at rank 89 < 90 (the `--sweep` rows
  with one eigen-block at 44). Mechanism identified and complete on the
  pool: a **bond of the contracted graph inside a single ruling class** —
  at `ds-K4`, a monochromatic hub, i.e. a free rotor ((GR-2)).
- **Proven — the reduction.** At a legal colouring each `⋆`-eigen-block is,
  after contracting the other ruling class, a **direction network in `K³`
  whose directions lie on a fixed conic and are constant on ruling
  classes** — equivalently a **generalized C¹-quadratic spline system** on
  the contracted multigraph, with edge moduli `(t − t_X)²`, one parameter
  per class. Its failure space `Z` (deficit from isostatic) has three
  equivalent exact descriptions and satisfies a rank identity verified at
  688/688 pool colouring-blocks ((GR-1)).
- **Proven — two obstruction families; empirically exact.** Two independent
  counting families bound `dim Z` from below ((GR-3)); at **generic** class
  parameters their max equals `dim Z` at every one of the 688 pool
  instances ((GR-4) — conjectured in general, exact on the pool). The
  concrete construction's component-index parameters are **not generic**
  (10/688 instances overshoot — a special-value artifact, not a property of
  the recipe).
- **Proven-informally AND machine-verified — chart-image membership.** Every
  σ-fixed grid configuration with linearly independent closed-hub-
  neighbourhood point triples is projectively a point of the landed chart's
  image, at an explicit seed; the `pencilRow` rank at that seed is the
  configuration's body-hinge rank. Verified end-to-end at 5 shapes — the
  chart-constructed points *rebuild* the Tay-target rank ((GR-5)). "Argued,
  not verified" is retired.
- **The cheap kill came back empty, 907/907.** Over the full `kslidecomb`
  class pool — the **exhaustive `K4` stratum (877 shapes**, the same 877 the
  workbook's §(K-slide-comb) `--k4full` row counts — an independent
  consistency check on the pool enumeration**)**, a `|V°| ≤ 5` sweep (6
  shapes), a `|V°| = 6` seeded sweep (21 shapes), and the three tight
  thetas including the previously unpooled θ(2,5,5) — an admissible
  target-rank colouring **exists at every shape**, and at 835 of 907 shapes
  the *first* filter-passing colouring already hits ((GR-6) evidence).
- **What is left is combinatorial, and exactly two gaps.** Discharging `hK`
  on the tight stratum now needs precisely: a proof of (GR-4) (sufficiency
  of the counts at conic labels), and (GR-6) (an admissible colouring
  satisfying the counts exists at every tight class shape — the statement
  the census tests). No geometric residue remains: this is the
  "rank condition becomes combinatorial" step `Pencil-strategy.md` §2.2
  says the arc lacks, delivered for the tight stratum — with the arc's
  base-rate caveat now attached to a colouring-existence statement instead
  of a rank statement.

### Step G0 — the question, and what would count as an answer

§(K-clos) (AC-6) leaves one live question: does the grid recipe reach the
Tay target at every tight class shape? A negative with mechanism refutes the
tight-stratum residual; a positive **proof** would discharge `hK` there
directly (no escape route, no split, no inductive hypothesis), then over
every infinite characteristic-0 field by (AC-7). The section attacks it in
the order the map prescribes: census first (Step G5), then the two named
deliverables — the direction network (Steps G1–G4) and chart membership
(Step G6).

### Step G1 — (GR-1): the eigen-block is a conic direction network, i.e. a generalized-spline system, and its deficit has an exact linear-algebra form

Fix a legal colouring (all bodies distinct) whose class `B` is a forest,
and work in the `+` block; everything dualizes with `A ↔ B`, `+ ↔ −`.

**(a) Hinge lines are constant on ruling classes.** Two adjacent bodies of
an `A`-edge share their ruling-`A` parameter, so the hinge is *the* ruling-A
line at that parameter ((AC-2)); all edges of one `A`-component `X` (in this
section: one **class**) carry the **same projective hinge line**, whose
`Λ²₊`-coordinate vector `d_X` is a point of the conic
`Q₃ = {α² + β² + γ² = 0}` — the decomposable locus of the eigenspace
(§(K-clos) *Step Z2*). Distinct classes get distinct, freely choosable conic
points (one `P¹`-parameter each).

**(b) Contraction.** By (AC-4), the `+`-block unknowns are `m_v ∈ K³` with
`m_u = m_w` across `B`-edges (3 rows) and `(m_u − m_w) ∥ d_X` across
`A`-edges of class `X` (2 rows). With `E_B` a forest its rows are
independent, so writing `H₊ = G/E_B` (nodes = the `n_c` `B`-components):

> `rank₊ = 3|E_B| + rank(DN₊)`,

where `DN₊` is the **direction network** on the contracted multigraph: place
the `B`-components as points of `K³` such that, for each class `X`, the
nodes it meets are collinear along `d_X`. *Legality already sanitizes the
contraction*: two bodies coincide iff they share both ruling components, so
at a legal colouring `H₊` has no loops and no same-class parallel pairs.

**(c) The spline form.** Over `ℂ̄` (char ≠ 2) the conic is projectively the
moment curve: a fixed `ℚ(i)`-linear change of basis of the eigenspace puts
`d(t) = (1, t, t²)`. Writing `q_v(t) = m_v² − 2t·m_v¹ + t²·m_v⁰`, the edge
condition `(m_u − m_w) ∥ d(t_X)` becomes

> `q_u − q_w ∈ span (t − t_X)²`,

i.e. `DN₊`-solutions are exactly the **generalized C¹ splines of degree ≤ 2**
on `H₊` with edge moduli `(t − t_X)²` — one modulus per class, repeated on
the class's edges. (Generalized splines on graphs are a classical object —
GKM theory; Gilbert–Polster–Tymoczko, *Generalized splines on arbitrary
graphs*, Pacific J. Math. **281** (2016), no. 2, 333–364 — but the matroid
theory of *repeated* moduli needed here appears not to be off the shelf;
nothing below is cited from that literature.)

**(d) The failure space.** Global constants (dimension 3) are always
splines; the deficit is jump-valued. Writing `m = |E_A|`,
`cut(H₊) ⊆ K^{E_A}` for the cut space of the contracted multigraph, and
`s : E_A → K` for the class-parameter function (`s_e = t_{X(e)}`):

> **(GR-1)** *(proven; driver `--spline`, 688/688 exact)* Let `H₊` be
> connected. Then
>
> `rank(DN₊) = 3·n_c − 3 − dim Z₊`,  where
> `Z₊ = { c ∈ K^{E_A} : c, s·c, s²·c ∈ cut(H₊) }`
>
> (entrywise products). Equivalently, `Z₊` is the space of spline jump
> assignments mod constants; equivalently again, with `π : K^{E_A} → H₁(H₊)`
> the quotient by the cut space, `H_X := π(K^X)` and
> `ℓ_X := span(1, t_X, t_X²) ⊂ K³`,
>
> `dim Z₊ = m − dim Σ_X H_X ⊗ ℓ_X`  inside `H₁ ⊗ K³`.
>
> At a **tight balanced** colouring, `2m = 3n_c − 3` and
> `dim(H₁ ⊗ K³) = 3h = m`, so: **target rank ⟺ Z₊ = Z₋ = 0 ⟺ the class
> subspaces `H_X ⊗ ℓ_X` fill `H₁ ⊗ K³` exactly.**

*Proof.* Rank–nullity: `rank(DN₊) = 3n_c − dim(splines)`, and
`splines / constants ≅ Z₊` by reading off jumps (`c_e` = the coefficient of
`(t − s_e)²` in `q_u − q_w`); membership of the jump vector in the
coboundary space is, coefficient-by-coefficient in `t`, the condition
`c, sc, s²c ⊥ cycle space = cut membership`. The tensor form is the same
kernel computed through `π` class-by-class. ∎ The driver computes the two
sides through genuinely different matrices (the eigen-block rref over `ℚ(i)`
with the actual conic directions vs. the `3h × m` rational cycle/parameter
matrix) and finds them equal at all 688 legal both-forest colouring-blocks
of the five-shape pool (`ds-K4`, `ds-(K5−M)`, θ(2,5,5), θ(3,4,5), θ(4,4,4)).

**Balance check.** `2m ≥ 3n_c − 3` with equality iff the colouring is
balanced at a tight shape — so (AC-4)(i) is the *square count* of the
direction network, and any row dependency costs target rank exactly.

### Step G2 — (GR-2): the gap-map statement is refuted; the mechanism is a bond inside one class

> **(GR-2)** *(refuted/proven; driver `--mech`)* "(AC-4)(i)–(ii) ⟹ both
> blocks isostatic" is **false**. At `ds-K4`: of 20 balanced colourings with
> both classes forests, **8 sit at rank 89**, every one carrying a
> **monochromatic hub**; the 12 filter-passing ones (adding: no
> monochromatic hub) are exactly the 12 target-rank colourings of the
> pinned (AC-6) sweep. The mechanism, in both languages: all hinges at a
> monochromatic hub are **one projective line** (they share the hub's
> ruling component), so the body is a **free rotor** about it — dually, the
> hub's star cut is a **bond of `H₊` lying inside a single class** `X`, and
> any cut vector `c` supported inside one class has `s·c = t_X·c`, so
> `c ∈ Z₊` survives the parameter conditions that kill every generic cut
> vector.

Relation to (AC-9), stated so the two do not blur: *every* body of degree
≥ 3 in *any* σ-fixed configuration carries a coincident hinge **pair**
(pigeonhole against the two rulings — (AC-9)); a pair costs no rank, which
is why (AC-3) reaches the target anyway. Rank is lost exactly when the
coincidence is **total** at a body — all its hinges one line — which is the
monochromatic-hub case; (GR-2) is thus the rank-costing boundary case of
(AC-9), and the filter's no-monochromatic-hub clause is its exclusion.

### Step G3 — (GR-3): two proven counting obstructions, mutually non-subsuming

> **(GR-3)** *(proven)* For any legal colouring with the other class a
> forest, `dim Z₊` is bounded below by each of:
>
> **(a) class-cut defects.** `Z₊ ⊇ ⊕_X (cut(H₊) ∩ K^X)`, of dimension
> `Σ_X (comp(G ∖ X) − 1)` — a nonzero term exactly when deleting the edges
> of the single class `X` disconnects `G`. *(The monochromatic hub is the
> case `X = the star of a hub`.)*
>
> **(b) class-union counts.** For every union `F` of classes:
> `dim Z₊ ≥ |F| − 3·dim H_F` with `dim H_F = |F| − comp(G ∖ F) + 1`; so
> `Z₊ = 0` requires **`3(comp(G∖F) − 1) ≤ 2|F|` for every union of ruling-A
> classes** (and dually for `B`).
>
> **(c) contracted sparsity.** For every node subset `S` of `H₊` with
> `e_in(S)` induced edges: `rank(DN₊) ≤ 2(m − e_in) + 3|S| − 3·comp(S)`,
> hence `dim Z₊ ≥ (3n_c − 3) − 2m + 2·e_in(S) − 3|S| + 3·comp(S)`. At a
> tight **balanced** colouring (`2m = 3n_c − 3`) this says `Z₊ = 0`
> requires the class-blind `(2,3)`-count **`2·e_in(S) ≤ 3|S| − 3·comp(S)`
> for every `S`**, whose sharpest failure witness is a **mixed digon**: a
> cycle of `G` with exactly two `A`-edges from *different* classes (its
> `B`-arcs contract to two nodes, so four rows act on one 3-dimensional
> difference space).
>
> None of the three subsumes another: the monochromatic hub violates (a)
> but neither count; the mixed digon violates (c) but neither (a) nor (b);
> the global balance count is (b) at `F = E_A`.

*Proofs.* (a): supports over distinct classes are disjoint and each vector
is an `s`-eigenvector, as in (GR-2). (b): the restriction of the tensor map
to `⊕_{X⊆F} K^X` has image inside `H_F ⊗ K³`. (c): the rows split into the
`e_in(S)` induced ones (killing the constants of each induced component)
and the rest. ∎

### Step G4 — (GR-4): at generic parameters the two families are exact — and the concrete construction's parameters are NOT generic

> **(GR-4)** *(conjectured in general; **exact at all 688 pool instances**,
> driver `--counts`)* At generic per-class parameters,
> `dim Z = max(bound (a), bound (b), bound (c), 0)`, for both blocks.

Two measured facts sharpen this.

1. **Label genericity is real and cheap to miss.** The concrete recipe
   (`closure.build_fixed_config`) uses component indices as ruling
   parameters. At 10 of the 688 pool instances that *specific* parameter
   point overshoots the generic `dim Z` by 1 (first flagged as a possible
   "conic-specific third mechanism"; re-testing at seeded random rational
   parameters collapses all 10 to the bound — a special-value artifact).
   Consequence, binding on any future use: **a rank miss of the literal
   construction at one parameter point is not a miss of the recipe** — the
   census (Step G5) retries every miss at random parameter draws before
   calling it structural.
2. **On filter-passing colourings the criterion is trivially met on the
   pool**: all 62 legal filter-passing pool colourings have generic
   `dim Z₊ = dim Z₋ = 0` (both blocks; measured). So on the pool the
   filter (balance + both forests + no monochromatic hub + distinct
   bodies) is already sufficient — but (GR-3)(c)'s mixed digon shows it
   cannot be sufficient in general, and the counts are the correct
   hypothesis.

**Why (GR-4) is stated as a conjecture, precisely.** The ≥ direction is
(GR-3). The ≤ direction is a generic-arrangement statement of matroid-union
type: for *fully generic* lines `ℓ_X ⊂ K³` and singleton classes it is the
classical realization of the 3-fold union of the linear matroid of
`{π(δ_e)}` (matroid union: Edmonds; the tensor-realization argument is the
one used for body-bar frameworks, cf. Whiteley, *Some matroids from
discrete applied geometry*, in *Matroid Theory*, Contemp. Math. **197**
(1996), 171–311, whose subjects include exactly the parallel-drawing and
cofactor matroids these direction networks and splines sit between). Two
genuine gaps separate that from (GR-4): (i) the class
structure (repeated `ℓ` within a class) is *not* the free union — it is
exactly what lets the class-cut family (a) survive; (ii) the lines are
confined to the **conic**, and the moment curve contains only two of the
three coordinate directions a partition-specialization proof would use, so
the standard specialization argument needs a valuation/degeneration
refinement. The pool evidence (688/688, including every unbalanced and
every count-violating colouring) is that neither gap changes the answer.

### Step G5 — the census: 907/907, no kill

> *(driver `--census`, seed 20260806, probe cap 48 filter-passing
> colourings/shape, early exit at the first legal target-rank hit, every
> non-hit retried at 3 random parameter draws)* Over **907 tight class
> shapes** — the three tight thetas (θ(2,5,5) **new**, not in §(K-clos)'s
> pinned 21-shape pool; θ(3,4,5); θ(4,4,4)), the **exhaustive `K4`
> stratum** (every length assignment in `{1..5}⁶` summing to 18 with a
> length-3 split edge that passes the class predicate `shape_ok`), and a
> seeded `|V°| ≤ 5` / `|V°| = 6` sweep of `kslidecomb.candidate_graphs` —
> **an admissible target-rank nondegenerate colouring exists at every
> shape**: 907/907, no misses, structural or otherwise. First-hit
> histogram: 835 shapes hit at the first filter-passing colouring, 60 at
> the second, 9/2/1 at the third/fourth/fifth.

Read with the right polarity: this is the ∃-per-shape statement (the
recipe's), tested against `hK`'s own habitat predicates (`shape_ok` =
tight + `def = 0` + `hnoRigid`; `hcard` and no-two-hub-triangle asserted
per shape). It extends §(K-clos)'s 15/15 by two orders of magnitude and
adds the previously unprobed θ(2,5,5). It is **not** a proof, and the
∀-colouring question is settled *negatively* by (GR-2) — existence of a
*good* colouring is the right open form, named (GR-6) below.

### Step G6 — (GR-5): chart-image membership, proven and verified — `hK`'s conclusion object is reached

`hK`'s conclusion (`Escape.lean:555`) asks for `∃ hubSel q s` with
`hubSel w` a correct `Fin 3`-selector of `closedHubNbhd w` at every body,
`s ⊆ E(G) × (…)²`, `|s| = 6(|V|−1) − def`, and the `pencilRow hubSel
G.endsOf q` family linearly independent on `s`. `pencilRow` reads **only**
the chart's constructed points (`Engine.lean:318`: `hingeRow ∘ annihRow` of
`extensor ![point u, point v]`); normals never enter it, and nondegeneracy
is not required.

> **(GR-5)** *(proven-informally, class-uniformly; machine-verified at 5
> shapes, driver `--chart`)* Let `G` satisfy `hcard` and let `pt` be a
> σ-fixed grid configuration from an admissible colouring (all bodies
> distinct) such that at every body `v` the point set
> `{pt_w : w ∈ closedHubNbhd(v)}` is linearly independent. Then there are
> `hubSel` and an explicit seed `q` over `ℚ(i)` with
>
> `pencilChartPoint (PencilSeed.ofCoord q) hubSel v ∝ pt_v` at **every**
> body, and `pencilChartNormal … v ∝ pt_v` (= the σ-fixed normal) at every
> body.
>
> Consequently the `pencilRow` family at `q` has the same rank as the
> configuration's body-hinge matrix; at a target-rank grid this **is**
> `hK`'s conclusion at `G` over `ℚ(i) ⊆ ℂ̄` — and over every infinite
> characteristic-0 field, since the certifying maximal minor is a
> `ℤ`-coefficient polynomial in the seed ((AC-7)'s argument, applied
> per-shape).

*Proof.* Take `hubNormal w := pt_w` (read only at hubs, since
`closedHubNbhd` contains only hubs). At any body `v`, every selected input
of the point construction lies in the 3-space `pt_v^⊥`: `pt_v` itself
because grid points are isotropic, and each hub-neighbour's `pt_w` because
adjacent grid points are conjugate ((AC-2)); `hcard` caps the selected
inputs at 3, and the LI hypothesis lets the unused slots be filled inside
`pt_v^⊥` keeping the triple independent (`fillHub`). `cross₃ x y z`
represents `w ↦ det[x,y,z,w]`, so it spans the 1-dimensional
`{x,y,z}^⊥` (nonzero by `cross₃_ne_zero_iff_linearIndependent`), which
contains `pt_v` — hence `∝ pt_v`. For normals: at a hub the chart returns
the seed's `hubNormal v = pt_v`; at a non-hub (degree 2, closed
neighbourhood of exactly 3 members on a 2-edge-connected class shape) it
returns `cross₃` of the three neighbouring chart points
`∝ cross₃(pt_v, pt_u, pt_w) ∝ pt_v` by the same isotropy/conjugacy
argument, the star-rank-3 condition supplying the LI. Rank transfer:
per-body scalars rescale each `pencilRow` row by a nonzero factor
(`annihRow` is linear in the extensor, the extensor bilinear in the
points), preserving linear independence; the per-edge row spans of the
harness's rigidity builder and of `annihRow` are both the full 5-dimensional
annihilator of the hinge extensor — the Lean side by the landed
`span_annihRow_eq_dualAnnihilator` (`PanelLayer.lean`) composed with
`hingeRow u v r = r(S u − S v)` (`RigidityMatrix/Basic.lean:494`), the
harness side by `perp_basis` coordinatizing the same annihilator through the
Euclidean pairing — so the ranks agree. The `ofCoord`
coupling `fillNbr = fillHub` (`Engine.lean`) is vacuous here: `nbrSel`
leaves no slot unassigned at a non-hub, and is never read at a hub. ∎

The driver verifies, at the first target colouring of each of the five pool
shapes: selector correctness (the three `IsFin3SelectorOf` clauses),
proportionality of the *chart-built* point and normal to the grid data at
every body, and — the end-to-end check — that the rigidity matrix rebuilt
**from the chart output** has rank exactly the Tay target (`ds-K4` 90,
`ds-(K5−M)` 120, the three thetas 60). §(K-clos) *Step Z6*'s "argued, not
verified" clause is retired; the second small-Lean-spike instrument named
there is no longer needed at the informal tier.

**Witness class, per (AC-9)'s discipline:** every configuration here is
σ-fixed, hence never composite-guard generic; every claim above is an
existence witness or an exact identity — no rates are quoted, and
rank-attainment at a σ-fixed point certifies the generic chart rank by
lower semicontinuity.

### Step G7 — what remains, named exactly: (GR-6)

> **(GR-6)** *(open — the tight-stratum residual in its final combinatorial
> form)* At every tight class shape there exists an admissible ruling
> colouring — alternating at degree-2 bodies, all bodies distinct, balanced,
> both classes forests — satisfying (GR-3)(a)/(b)/(c) in both blocks.

Together with (GR-4), (GR-6) implies target rank at every tight class
shape; with (GR-5) and (AC-7), that discharges `hK` on the tight stratum
over every infinite characteristic-0 field. Both remaining gaps are
geometry-free: (GR-4) is a generic-arrangement/matroid-union statement,
(GR-6) a colouring-existence statement whose counts are Nash-Williams/
Edmonds-shaped (the packing side of the arc already lives in Phases 12–15
machinery, cf. §(K-slide-comb) (C6)). Evidence for (GR-6): 907/907 with
first-hit concentrated at the first filter-passing colouring — the good
colourings are not rare. The honest caveat cuts the other way: every
class-uniform *combinatorial-existence* claim this arc has previously
relied on has eventually been either proven by a min-max or refuted by a
parity/chromatic flank ((AC-6) itself, (K-slide-comb)); (GR-6) has no
min-max yet, and until it does the base-rate warning of
`Pencil-strategy.md` §2.3 applies to it.

### Verification

`notes/scripts/w4/grid.py` (**new with this section**; imports `closure.py`
and the catalogued §1 primitives read-only; exact ℚ and ℚ(i); the census
rng and the generic-label draws seeded, seeds printed; no `set` printed).
Every sampled object carries the standing guards (isotropy, conjugacy,
eigen-sign, span dimensions) through `closure.probe`/`extensors`.

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --mech      # 1 s   (GR-2): 20 balanced-forest / 8 below target / 8 mono-hub; 12 filter-passing = the pinned sweep's 12
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --spline    # 21 s  (GR-1): rank identity, 688/688
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --counts    # 6 s   (GR-3)/(GR-4): 688/688 at generic labels; 10 construction-label overshoots; filter-passing 62/62
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --census    # 86 s  907/907 (877 K4 + 6 V5 + 21 V6 + 3 theta); first-hit histogram 1:835, 2:60, 3:9, 4:2, 5:1
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --chart     # 6 s   (GR-5): 5/5 end-to-end through the landed chart constructions
PYTHONHASHSEED=0 python3 notes/scripts/w4/grid.py --validate  # all five (~2 min)
```

*Confidence verdict.* **(GR-1) proven** (informal proof + 688/688 exact
identity). **(GR-2) proven refutation** of the gap-map sentence, mechanism
complete on the pool. **(GR-3) proven.** **(GR-4) true-modulo-named-gap**
(the ≤ direction at conic labels; exact at every censused instance).
**(GR-5) proven-informally** class-uniformly, machine-verified at 5 shapes
(the Lean-tier transcription remains future work, as for every section of
this workbook). **(GR-6) open**, with 907/907 evidence. The tight-stratum
question of (AC-6) is thereby **reduced, with proven reductions, to
(GR-4) + (GR-6)**; nothing here re-opens the habitat-level refutation
(`C11` is permanent).

*What would change this.* (i) A tight class shape where the census's
early-exit + random-parameter retry finds no target colouring — refutes
(GR-6) and the tight-stratum residual with it. (ii) A colouring-block
anywhere with generic `dim Z` strictly above the (GR-3) max — a third
obstruction family, refuting (GR-4) as stated. (iii) A proof of (GR-4)
(most plausibly: the matroid-union tensor realization pushed through the
moment-curve confinement by a valuation argument) — upgrades the criterion
to a theorem. (iv) A min-max proof of (GR-6) — closes the tight stratum,
and with it `hK` there, over every infinite characteristic-0 field.
