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
| *Shared dictionary* + test shapes `W19`/`S29` | 109–202 | serves **both** workbooks | `SD-` |
| ***State of (K)* — the gap map** | 204–448 | **the entry point; a pass updates it in place** | — |
| §(K-tight) | 450–708 | criterion proven-informally; **(K-tight) open — the phase's hardest item** | `KT-` |
| §(K-pitch) | 710–1142 | (T1)–(T5) proven-informally; closed at `ℓ = 3`; uniform form open | `PT-` |
| §(K-slide) | 1144–1434 | (S1) proven-informally; settled per member | `SL-` |
| §(K-slide-cl) | 1436–1726 | reduction proven; **refuted as stated**; the `∃Σ` form open | `SC-` |
| §(K-slide-comb) | 1728–2078 | **refuted as a class statement**; (C6)/(C7) proven-informally | `SB-` |
| §(K-flank) | 2080–2651 | per shape, not a uniform gap; half 2 proven-informally | `FL-` |
| §(K-pure) | 2653–3229 | direction C **refuted**; (PC-Z)/(PC-OBS) proven-informally; **(K-chord)** the successor | `PC-` |
| §(K-Λ) | 3231–4579 | **refuted as an independent gap**; (Λ1) an identity; **(OUT)** lives here; item (vii) **REALIZED**, floor-classified | `Λ` |
| §(K-dom) | 4192–4598 | dominance holds at every probed habitat; **C1 not a route**; (D2) gains its mechanism from §(K-ann) | `DM-` |
| §(K-σ) | 4600–5332 | **route σ a CANDIDATE** — the one live candidate; its *Field scope* is settled by §(K-clos), and two of its refutations reverse there | `σ` |
| §(K-clos) | 5334–6009 | the field question **settled** ((AC-1)/(AC-7)); **(AC-6) refuted as a class statement**, open only on the tight stratum | `AC-` |
| §(K-ann) | 6011–7536 | the **recipe** ((ANH-2)/(ANH-3)) and (ANH-1)/(ANH-4) proven; the residue is **(ANH-R1)**, relocation #4 — since Steps A10–A13 (direction R) **one-point-decidable per shape, discharged at every probed triple, pointwise REFUTED** ((ANH-12)); since Steps A14–A17 (direction Q) the M2 "upgrade" is **struck as redundant** ((ANH-16)), the bare-cycle stratum is governed by **one universal irreducible degree-12 polynomial** ((ANH-14)), and the residue is **chart-to-frame dominance, no rank condition left** | `ANH-` |
| §(K-out) | 7539–10558 | (OUT)'s hypothesis **measured**: **(OC-3)** proves it is never automatic (no counting route); availability pointwise; **(OC-7)** a harness defect, its necessity clause **refuted** ((OC-14)); since Steps O9–O12 (direction O) the combinatorial half is **proven** ((OC-10), items 1–2 struck) and residue **(OC-8)** is a **containment** question — at degree-3 hubs the bad locus is the explicit panel line `C₀`; since Steps O13–O18 (direction OCON) **(OC-8) reshaped**: the hard-stratum qualifier is free ((OC-17)); since Steps O19–O24 (direction ZNEQ) chart irreducibility (CIRR) discharges input (b), and (OC-19) input (a) `Z ≠ ∅` itself **factors**: a necessary-for-`hK` half **dominated** by §(K-grid) (GR-10), and a target-rank half whose failure is a codimension-2 Schubert jump, measured 138/138 witnesses — **OPEN as a class-uniform statement, NOT an independent gap** | `OC-` |
| §(K-ind) | 9366–9710 | **refuted as a route** | `IN-` |
| §(K-Δ) | 9712–9977 | **NO HIT — the lead is discharged** | `DL-` |
| §(K-bare-ext) | 9979–10017 | open, nothing being developed | `BE-` |
| §(K-grid) | `notes/Pencil-informal-grid.md` | **reduction proven** — (AC-6)'s tight-stratum residual reduces via a long chain of proven results on `G°` to the single open gap **(GR-15)**; the min-max form, the uniform `g ≤ 1` cap, the bounded-deviation selection form and the growth law's bounded-shift-correction reading are all refuted (the last two at the necklace family — (GR-43) proves the shift-metric layer unbounded) while the `d_fg = d_adm` law is verified EXHAUSTIVELY on the whole `n_hub ≤ 6` habitat stratum ((GR-58)), its stronger per-matching variant REFUTED ((GR-59)); the parity layer is exactly `d_par(M) = w_M` with the Hall/SDR step automatic ((GR-44)), and **route-ledger entry 5 is PROVEN in both halves ((GR-49)–(GR-54)): balance existence is a degree-constrained-orientation theorem, discharging the named input (X)** — the (GR-45)–(GR-48) move-calculus apparatus is subsumed, not contradicted; since Steps G80–G85 (direction YLOC) **input (Y)'s pinned GBAL-localization route is DEMOTED BY WITNESS** — full goodness is not a function of the degree data at a proper chunk ((GR-62)), the coordinator's predicted break point REFUTED as stated and located two links earlier ((GR-63)) — leaving a colouring-free collision bound on `d_fg` ((GR-64)) and a coordinate-free fit identity ((GR-65)) as the positive residue; input (Y) stays OPEN, **E3 (ARMED by GBAL) does not fire**; since Steps G86–G91 (direction BALB) **(b′)'s PRICE half is PROVEN outright ((GR-68)) and its imbalance ceiling is a THEOREM at `n_hub ≤ 6`, FALSE from `n_hub = 8` at an exact boundary ((GR-69))** — its availability half reduces to one clause (GR-70), exhaustive on the stratum's landed T1 instance but REFUTED there from `n_hub = 8`, repaired at price 0 by a named successor; **(b′) stays OPEN, NOT a HIT**; no flank found; class uniformity untouched | `GR-` |
| §(K-frame) | 17870–19540 | residue **(FR-R1) PROVEN** since Steps FR7–FR11 (direction PEX); the bare-cycle stratum is finite (22 iso classes / 76 sites / 1976 labelled) and exhaustively enumerated; since Steps FR12–FR15 (direction FRES) **(FR-4)'s named gap is CLOSED** — the discharge is unconditional on the whole bare-cycle stratum ((FR-17)) | `FR-` |
| §(K-chart) | 19931–20754 | **new, 2026-08-19, direction CIRR — a HIT.** The pencil chart of `G′` is a proven, irreducible, ℚ-rational variety (a tower of affine-linear fibres), the constant-fibre-dimension clause identified as `IsNondegPencilRealization` conjunct 3, and all four consumers (§(K-out) (OC-19), §(K-slide) (S1)(e), §(K-dom) (D4), §(K-ann) (ANH-9)(ii)) audited clean; one correction to §(K-frame) *Step FR13*'s hypothesis list (girth ≥ 4, not ≥ 3, for nonemptiness) | `CH-` |
| §(K-mech) | 20756–21137 | **both §(K-pure) *P8* anomalies mechanised** in one calculus (the load space `Ω`); **6v11e RESCUED** ((MX-7)) — the slide device closes it after all; the σ rider settled NO ((MX-8)); the `\|V°\| ≤ 6` predictor measured complete-and-sound ((MX-9)) | `MX-` |

**Live vs settled**, using the division of the 2026-08-05 reorganization pass.
Live: §(K-tight), §(K-Λ), §(K-σ), §(K-pure), **§(K-ann)** — whose live residue is
(ANH-R1), everything else in it being settled — **§(K-out)**, whose live residue
is likewise only **(OC-8)** (its (OC-3) negative and its two pool measurements
are settled, and its (OC-7) is a *harness* item, not mathematics) — and
**(K-wit)** (owned jointly by
§(K-pitch) *Step 3* and §(K-Λ) *Steps 3–6*). Settled or refuted, so **do not
re-derive**: §(K-slide-comb), §(K-Δ), §(K-ind), §(K-slide-cl) as stated,
§(K-dom)'s C1 verdict, and §(K-clos) — whose tight-stratum residue now lives in
**§(K-frame)** (live) — no residue of its own left named, since Steps
FR12–FR15 (direction FRES) closed **(FR-4)** with no rider ((FR-17)) — and
**§(K-grid)** (live) as — since Steps G24–G28 (direction CFLANK) — the residual
**(GR-15)** (unchanged in status: OPEN, no flank found, despite ten proven
structural results now reducing it to a statement about `(G°, ℓ, bits)` at
`D = 0`, exhaustively swept to 40 742 shapes with no hit; formerly, since
Steps G19–G23 (direction TCOL), the same residual before the excess-law
reduction; before that (GR-10), which stays open as the strictly stronger
statement with its min-max refuted as posed; before that the pair (GR-4) +
(GR-6)), the class statement staying refuted. The
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
| **(K-wit)** | (K-pitch) 3; (K-Λ) 3–6 | **open**; the weakest exact form — per habitat+split *equivalent* to the escape at a good seed — and now the **single live form of the pitch route at companion splits**: it inherits (K-Λ)'s status and gains a *necessary-and-sufficient* companion form (§(K-Λ) *Theorem (Λ-completeness at length-4 companions)*: the escape holds at some target-rank seed **iff** the pitch certificate is nonzero at some target-rank seed). The **two-point failure locus is this row's content** — `{V_bc ⊥_B C(M)}` (the failure itself) and `{V_bc ⊥_B C(bc)}` (route A escapes, `★r ∝ C(bc)`); since 2026-08-05 those two points are known to be **exactly a σ-orbit** (§(K-σ) (σ5)), so the recorded asymmetry between their consequences is a *one-frame artifact*, not a broken symmetry — and if §(K-σ)'s candidate route σ stands, this row's trichotomy loses its failure branch and (K-wit) leaves the escape's critical path. Two load-bearing side conditions are newly **named**, neither present in the prior formulation: **(Λ0d)** panel non-incidence in **both** directions (`pt(c) ∉ Π(b)` *and* `pt(b) ∉ Π(c)`; witness θ(3,4,5) seed 345, where `span_t ω⁻` collapses `3 → 1`) and **(Λ0f)**, now **PROVEN at the generic point and WIDER than first stated** (2026-08-05, `m2/lambda0.m2`): the exact criterion is **(Λ0f′)** `span_t ω⁺ = 3 ⟺ p⁺₂p⁺₃·g₁₃g₁₄g₂₄ ≠ 0` (and `q₂q₃·g₁₃g₁₄g₂₄ ≠ 0` for `ω⁻`), where `g₁₃g₂₄ ≠ 0` is `rank Q|_S = 4` and **`g₁₄ = [b,x₁,x₃,c] ≠ 0` was asserted nowhere** — the two outer companion lines must not meet. Since 2026-08-05 (§(K-Λ) *Step 3a*, `outer.py`) that clause is **located, not merely named**: geometrically it says the two marked points `C₁ ∩ M`, `C₄ ∩ M` of the meet line coincide **(Λ0g)**; wherever a companion end is free it is **implied by (Λ0d)** **(Λ0i)** (3628/4280 swept pairs); **no class habitat in scope forces it** (`g₁₄ ≠ 0` at 4280/4280 exact pairs over 1357 class shapes, `d g₁₄ ≠ 0` at 684/684 chart points), so **Λ-completeness stands as written**; but it *is* reachable at a target-rank `dim R_a = 1` seed of all four habitats by an explicit chart move, both spans dropping `3 → 2`, so the clause is load-bearing. Residual **ANSWERED 2026-08-19** (§(K-Λ) *Steps Λ8–Λ12*): such shapes **EXIST**, at all four patterns, with a **proven size floor** ((Λ6): `|V| ≥ 21` at two interior hubs, `≥ 26` at three) attained by the witnesses `LT21a`/`LT21b`/`LT26` — each at a hard-stratum target-rank chart point with (Λ0d), (Λ0g), `g₁₄ ≠ 0` and `d g₁₄ ≠ 0`; **(Λ0i) covers none of them** ((Λ8)). Λ-completeness stands as written; the live residual is the **uniform** `g₁₄` statement over that named family. **New 2026-08-05, a sufficient condition rather than a status change:** since `p⁺` and `q` both have their *outer* entries vanishing structurally, the whole (Λ2) bad set lies on the single line `{λ₁ = λ₄ = 0}` of `P(S*)`, so **(OUT)** (§(K-Λ) *Step 5a*) — *either outer companion line not a relative twist* — already forces the escape by pitch at `k = 4`; it is conditional on (Λ0) in full. **Its hypothesis is MEASURED since 2026-08-06 (§(K-out)), and the measurement cuts both ways**: available pointwise (356/357 POOL-G, 270/270 POOL-S, every probed (split, companion) pair) but **never automatic** — (OC-3) proves `{λ₁ = 0}` is nonempty on *every* class shape's chart, so no counting argument can ever discharge (OUT), and the residual **(OC-8)** is a rank *lower* bound on the whole-graph chart | one `H`-motion pairing non-trivially with `C(M)`, uniformly — **or, at length-4 companions only, the strictly cheaper (OUT)**: `C₁ = C(b x₁) ∉ V_bc` or `C₄ = C(x₃ c) ∉ V_bc`, a far-side, panel-free, `a`-free condition (§(K-Λ) *Step 5a*; conditional on (Λ0d) + the widened (Λ0f′), sufficient and never necessary, and a rank *lower* bound so §2.3's asymmetry is relocated, not evaded). **Caveat, mandatory since 2026-08-06 — §(K-out) (OC-3):** (OUT)'s hypothesis is **never automatic**, its bad locus being nonempty on the chart of every class shape in scope (one marked direction of `x₁`'s pencil, since `dim R₁ = 5` and `dim L_b = 2`), so this route can be discharged only by a genericity argument on the whole-graph chart — **(OC-8)** — and **never by a count**; what is delivered is *availability*, measured pointwise, not uniformity — and since §(K-out) *Steps O9–O12* (2026-08-06, direction O) the bad locus at a **degree-3 hub** is exactly the coincident-hinge locus together with **one explicit line `C₀` of the panel** (§(K-out) (OC-12)/(OC-13)), the first rejected by every harness gate and the second **reachable by construction** (§(K-out) (OC-14)), so (OC-8) there is a containment question with no rank condition left. **New 2026-08-06, a second `k = 4`-only sufficient route: §(K-ann) (ANH-R1)** — `τ_β ≠ 0` at the pencil placement, i.e. `H/P − β` is pencil-rigid. Its consumer is the class-uniform **recipe** (ANH-7) (one named far-chart move, one 4-point bracket, 89 % coverage), and by §(K-Λ)'s Λ-completeness discharging it would close the **whole length-4-companion stratum**, not one shape. It is **relocation #4** and, like (OUT), a rank *lower* bound — §2.3 relocated onto a smaller contracted graph, not evaded; **whether it is easier than its parent or merely smaller is OPEN**. **Since §(K-out) *Steps O13–O18* (2026-08-19, direction OCON):** the genericity argument (OC-3) demands needs **no hard-stratum qualifier** ((OC-17)) — its incremental content is exactly one chart point, anywhere on the (shape, split) chart, at which the welded far framework `H/X` is infinitesimally rigid ((OC-18)/(OC-19)) |
| **(K-pitch-∞)** | (K-pitch) 4 | **open**; sufficient for (K-pitch) at a split; all five quartic coefficients nonzero at 4/4 habitats | `Q(z_∞) ≢ 0` on the `a`-free chart |
| **(K-Λ)** | (K-Λ) 1–6; (K-pitch) 5b | **REFUTED as an independent gap** (§(K-Λ), fan-out direction B): at a length-4-companion split it is *equivalent* to **(K-wit)** (Steps 3–5), so **closing (K-Λ) *is* closing (K-wit)** and no local argument can close it. `Φ_loc`'s non-degeneracy is **PROVEN, class-uniformly** — `Φ_loc` is always a **rank-2** form, the product of two distinct rational linear forms ((Λ1), an **identity over the function field** since 2026-08-05: `m2/lambda1.m2`, the harness's first Macaulay2 driver; it needs none of (Λ0) and none of the panel data) — so the previously-flagged "`Φ_loc ≡ 0`" degeneration is **impossible** and the "local quadric" is a pair of rational hyperplanes. Using (T4)'s `a`-line freedom, the far covectors bad for the whole line shrink to **two points**, with failure locus `{V_bc ⊥_B C(M)}` (= the genuine (T3) failure) and `{V_bc ⊥_B C(bc)}` (= route A escapes outright, `★r ∝ C(bc)`). Its exemplar θ(3,4,5) is separately closed by a reduced-support slide witness (§(K-pure) P7) | — refuted as an independent gap; the live form is **(K-wit)** (row above) |
| **(K-slide)/(S1)** | (K-slide) 1–4 | **(S1) proven-informally**; per-member (K-slide) **witness-decidable and discharged at every probed member** (23/23, 7 members, 11 split-classes) — `K4`/`W4` control habitats closed at **every** split. Status unchanged by the sixth pass, but (S1) **remark (iii)'s support freedom is promoted from a proof convenience to *the* load-bearing parameter**: `E_chord(Σ)` shrinks with `Σ`, so the support choice alone decides whether the limit is pitched (§(K-pure) P1/P7) | — settled per member; the class form is (K-slide-cl) |
| **(K-slide-cl)** | (K-slide-cl), (K-slide-comb), (K-pure) | **REFUTED as stated** (§(K-pure), at the full support): the chord obstruction **(PC-OBS)** kills (W4) — or (W3) — at *every* decoration of three `K5` class shapes and of θ(3,4,5). This is a **statement**-level refutation by `R_3`-dependence, a **different mechanism** from (K-slide-comb)'s antecedent-level colouring refutation below — do not conflate them. The **repaired** statement quantifies `∃Σ` over slide supports and in that form is **open**. The **covered sub-class grows**: the collapse-solvable shapes (all 7 battery members) *plus* the three `K5` 5-chromatic shapes, `K222` and θ(3,4,5), which now carry **reduced-support** (S1) witnesses | for the `∃Σ` form: **(K-chord)** below, plus a mechanism for the residual (W2)/(W4) failures. The "generic pure condition of the limit system instead of the collapse" route is itself **REFUTED** (§(K-pure) P0/P5: that condition sees only (W1) ∧ (W2)) |
| **(K-slide-comb)** | (K-slide-comb) | **REFUTED as a class statement** (two structural flanks at explicit class members satisfying `hcard`/`htf`); per shape still a finite certificate-bearing problem, and "(K-slide-comb) at a shape ⟹ (K-slide-cl) there" stays **proven** | — refuted; the needed invariant is **acyclic** 4-colourability, which 3-degeneracy does *not* give |
| **(C6)** | (K-slide-comb) D1 | **proven-informally at every class shape** — the unrestricted 6-fold base packing exists because Edmonds' matroid-partition min-max hypothesis for it *is* 5/6-sparsity; so the packing content is never the obstruction (and is Phase-12/13/14-reachable). **Status unchanged, role downgraded** (§(K-pure) P2/P6): it certifies the *ambient* hypothesis of a theorem that does **not** transfer to the decoration variety, and it is about the 6-fold **graphic union** — the wrong matroid for the pitch, which `R_3`-dependence governs | — settled; only a non-tight shape could break it |
| **(C7)** | (K-slide-comb) D4 | **proven-informally combinatorially** (the length-4 menu is *all* five 2-subsets containing `L_ij`; 12/12 exact; `K4` coverage 439 → 702/877, octahedron flank rescued); two honest gaps — no full (W1)–(W4) witness at a repaired member, and `ℓ ∈ {1,2,5}` open (at `ℓ = 5` the mandatory-`L_ij` claim is itself suspect) | a geometric witness at a repaired member + the `ℓ ∈ {1,2,5}` analogues; cannot touch either structural flank |
| **(K-chord)** *(new, 2026-08-05)* | (K-pure) P1–P4, P9 | **open**, and the *replacement* combinatorial residue: `∃Σ` with `e₀ ∉ cl_{R_3}(E_chord(Σ))` at generic hub points — **necessary** for the slide device by (PC-OBS). Per shape it is checkable by **exact rank** — done exhaustively over the 23 candidate hub graphs with `|V°| ≤ 6` (`R_3`-dependence ⟺ Maxwell-overbraced; 5 dependent, 18 independent; smallest `K5`) — but unlike (K-slide-comb) it lives in a matroid with **no combinatorial characterisation** (generic 3-dimensional rigidity), so a class argument has nothing to reduce to. *Since 2026-08-06 (§(K-mech), direction M):* the device's necessary-condition set at a support `Σ` **widens to three named, decoration-free items** — (K-chord) itself, both pole-cluster bounds ≤ 1 ((MX-4)/(MX-5)), and no forced flex route ((MX-6)) — and on the sampled `\|V°\| ≤ 6` strata the three-way predictor is **measured complete and sound** ((MX-9): 21/21, one new (W4)-failing shape found-and-explained, 0 unexplained) | a support menu wide enough to satisfy it *together with* (W1)–(W4) at every class shape — P9 item 5's probe is now **RUN** (§(K-mech): 6v11e **rescued** (MX-7), the sweep measured) and the residue is the **sufficiency** of the three-condition set beyond the sampled strata — or a class shape satisfying it at **no** support, which would refute the device class-wide (still unexhibited; the covered sub-class grew by 6v11e) |
| `P21` / parallel `G°` edges | (K-slide) 5, (K-flank) F5, (K-pure) P4/P7 | **mechanism corrected and scope sharpened** (§(K-pure)): at a *class* parallel shape the full-support obstruction is the **chord stress at (W4)**, not (S5) at (W1), and it needs only a `bc`-parallel edge of length `≤ 4`. (S5)'s `(3,3)` row-dependence mechanism is **proven impossible inside tight + `hnoRigid`** (`C_k` rigid for `k ≤ 6` forces `ℓ₁ + ℓ₂ ≥ 7`), so **`P21` is a (K-res) residual, not a tight class member**. `P21`'s own obstruction is unchanged and is **not confined to the `ε = 0` limit** — §(K-flank) F5(d)/(e) exhibits the same theta-circuit stress (`{12, 13, 23a, 23b}`, 12 edges, line rank 6) on a **nonempty locus of the pencil chart itself** (5 of 35 rational seeds), where it forces `dim R_a = 0`. **θ(3,4,5) is CLOSED** by a reduced support, without (K-Λ) | for `bc`-parallel class shapes: a reduced support (done at θ(3,4,5)) or the companion forms — the monomial at `ℓ = 3`, and at `ℓ = 4` **(K-wit)**, since §(K-Λ) shows the companion form there is *equivalent* to it rather than an independent gap. At `ℓ = 5,6` **the (T5) frame is REFUTED as the route** (§(K-Λ) *Step 7*: at `k ≥ 5` the (F-A) bad locus gains a second, equal-dimensional component — a smooth conic, so nonempty over `K̄` — and at `k = 6` `C(M) ∈ S` removes even the local guard), so those shapes need **something else, none identified** (this refutes the *argument shape*, not the conjecture and not their closability; whether a *rational* point of that component is realized by a real habitat is open). For `P21`-type (K-res) shapes: a new `G°`-local mechanism — none identified |
| **(K-flank)** | (K-flank) F0–F7 | **per shape, not a uniform gap: half 2 proven-informally** by exact `∃`-witnesses at the Tay target (8 named + 843 stratum shapes, 0 failures); half 1 carries **no `hK` counterexample and no re-pin** (16/16 `e₀`-end splits, 26/26 eligible splits of the 5-chromatic flank, both KT routes); **(K-pitch) closed at all 16 flank splits** by `ε = 1` certificates; the full-support slide limit is **degenerate at all four structural flanks**; **class uniformity untouched** | — n/a: a per-shape result, not a gap. *Settled per shape; the uniform statement is unchanged* (the disproof risk is removed, no uniform gap moves) |
| **(K-dom)** *(new, 2026-08-05)* | (K-dom) D0–D7 | **open as the uniform statement, and provably FALSE off the class**, so the strategy doc's §4-C1 route is **not recommended**. Writing `k` for the *companion length* (the shortest `b`–`c` path of `H`; `k ≥ 3`): **(D1)** `rank d(H ↦ V_bc) ≤ min(9, 6k − 14)` in the bad-locus-frozen scoping, **proven** from path-sum containment — so `≤ 4` at `k = 3`, where `V_bc` is moreover always in the discriminant hypersurface of `Gr(3,6)`; **(D2)** the far block is `≤ 3(k−3)` (a corollary of (T5)), **attained** at `0,3,6,9` for `k = 3,4,5,6` — and since 2026-08-06 that number has a **mechanism** rather than a measurement: §(K-ann) **(ANH-1)** identifies the annihilator as the self-stress space of the contracted framework `H/P`, so `3(k−3)` is `dim Gr(k−3,k)` **for that stress space** and the dimension `k−3` is forced by a *count*; **(D3)** `hnoRigid` forces `k ≥ 4` (= §(K-slide) *Step 5*'s `ℓ₁+ℓ₂ ≥ 7`), so the cap bites exactly on **(K-res)**. Measured: rank **9 — dominance — at all 5 probed class habitats** (θ(3,4,5), NT21, NT16k5, `K4`/`K5−M` dbl-subdiv; `k ∈ {4,5,6}`) and exactly **4** at both `k = 3` habitats. **(D4)**: rank 9 at one rational seed ⟹ the escape on a *dense open* subset of that shape's chart — a strictly stronger per-shape statement than an `∃`-witness, and no more useful. §4-C1's two claimed values are **REFUTED** (D6): the image does **not** grow with the far graph (it is capped by the local `k`), and the 2026-07-30 locality gate was run at `k = 6`, the *maximal* far-dependence grade, so it is not evidence for dominance. **Class uniformity untouched** — "rank 9 at every class shape" is one determinantal condition per (shape, split), the same per-shape object §(K-pure) *P5* names as the wall | a class habitat with `rank dV < 9` at every seed (a sharp new obstruction; none found), **or** a mechanism making `rank dV = 9` combinatorially certifiable class-wide — the only thing that would turn C1 into a uniform route |
| **(K-σ)** *(new, 2026-08-05)* | (K-σ) *Field scope*, σ0–σ6, σ4b | **four settled verdicts + one CANDIDATE, offered for adjudication; the FIELD-SCOPE caveat they carried is DISCHARGED** (§(K-clos), 2026-08-06 — see the row below and the sentence marked SETTLED here). `σ = screwComplementIso` exists in tree **only over `ℝ`** (`Duality.lean:69`), and so does the self-duality theorem the conjunct-1 freeness cites (`Statement.lean:257`), while **`hK` is quantified at the general `[Infinite K]`** of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Escape.lean:555`). Whether the polarity generalizes is **SETTLED — YES** (§(K-clos) (AC-1), 2026-08-06): bookkeeping, one section, and the general-`K` **transport is already landed** as `BodyHingeFramework.mapSupport` with its rank lemma, so `ProjectiveInvariance.lean` needs no generalization; source-level, **not compiler-checked**. **(σ7) needs no polarity and is field-neutral outright**; (σ1)–(σ6) and route σ are field-neutral *modulo the polarity existing*, so they **port**; the two refutations below use `ℝ`-**definiteness** and do **not** port — indeed **both REVERSE over `ℂ̄`** (§(K-clos) (AC-2)/(AC-3): σ-fixed configurations exist and are nondegenerate at the Tay target), **and the verdict they support survives anyway** on the field-neutral §(K-clos) (AC-5). Settled: the σ-intertwining question is **REFUTED in its literal form** (`pt(a) ∈ π_a` forces `pt(a)·pt(a) = 0`, impossible over ℝ with the project's *definite* polarity — `Molecular/Meet.lean:88` records it is the Hodge star of the standard dot product) and **CONFIRMED covariantly** (`σ(α_p) = β_{p^⊥}`, `σ(β_π) = α_{pole(π)}`), which makes §(K-Λ)'s two-point failure locus **exactly a σ-orbit**; and **σ-equivariant seed recipes are DEAD** — no σ-fixed pencil configuration exists over ℝ, and a null polarity puts every hinge line in a linear line complex, giving a self-stress per cycle (**deficit exactly 1 at 6/6** on tight `C₆`). Fourth settled verdict, **new 2026-08-05** (`sigma.py --hunt`, three pools of its own, disjoint from the pinned 47): **(σ7)** *Step σ3*'s side condition `pt(b) ∉ Π(c)` is **FREE** — primal conjunct 4 at the split's middle body `a` forbids both halves of (Λ0d) from failing at once (39/39 witnesses that forcing both leaves `a` with no panel), settling *What would change this* (iv); **and, in the other direction, the dual conjuncts at `σu` are NOT implied** — 45 constructed hard-stratum, primally-nondegenerate seeds violate dual conjuncts 2 and 4 (coplanar-chain degeneration), so *Step σ4*'s 47/47 was genericity. Candidate: **route σ**, whose uniform-failure criterion `★r ∥ C(bc)` is the σ-image of routes A/B's `★r ∥ C(M)` and cannot hold simultaneously with it. Scope of the validation: `s₀ = 0`, `dim R_a = 1`, both ends hubs, tight control only (the hunt pools widen the *configurations*, not the shape) — `dim R_a = 0` **untouched**, (K-res) `s₀ = 2` **unsampled**; the criterion at `σu` is **imported, not re-derived**, and its failure direction is **unwitnessed** (`predAfalse = 0/47`); and the branch route σ closes has **never been observed nonempty**, so the gain is **evidence → argument**, never *bug fixed*. **No gap-map status moves on account of route σ** | obligation 1 of §(K-σ) *Step σ5* — now **sized, not just named** (all of it **at `ℝ`** — see the caveat opposite): conjunct 1 free by a landed theorem, conjunct 3 free by the primal conjuncts on no-adjacent-hub shapes, conjunct 2 at the two `a`-edges = two-sided (Λ0d), leaving two genuinely new conditions with a steering repair exhibited exactly (`bracket(τ) = τ·bracket(1)`). Route σ faces exactly **one** crux: the workbook's two kills of M₁ (§(K-tight) *Step 1* and *Step 2.6*) have the **same** stated reason, the `hinge(vb) := q(ab)` pinning |
| **(K-clos)** *(new, 2026-08-06)* | (K-clos) Z0–Z8 | **The field question of §(K-σ), settled — plus one construction REFUTED as a class statement and left OPEN only on the tight stratum.** Read the two halves separately. **Settled, proven-informally:** **(AC-1)** the polarity **generalizes** — bookkeeping, one section, and the general-`K` transport is already in tree (`BodyHingeFramework.mapSupport`, `Molecular/GenericLift/HingeGeneric.lean:462`, rank lemma `:544`), so `ProjectiveInvariance.lean`'s 19-declaration `ℝ`-fixed `mapExtensor` API needs **no** generalization (source-level, **not compiler-checked** — the dispatch carried a no-Lean constraint, and a ~20-line typecheck spike would settle it); **(AC-2)** the σ-fixed locus over `ℂ̄` is exactly the `P¹ × P¹` **grid** on the fixed quadric, with the conjugacy law `p ⬝ᵥ p′ = 2[s,s′][u,u′]`; **(AC-3)** those grids are **nondegenerate at the Tay target**, so §(K-σ) *Step σ6*'s "degenerate" is **REFUTED for the symmetric correlation** (it stands for the null one); **(AC-4)** the `⋆`-eigen decoupling `rank = rank₊ + rank₋` and the three conditions target rank forces (balance, both classes forests, both blocks isostatic); **(AC-5)** at a σ-fixed seed **route σ IS route A** (32/32, as subspaces), which is the **field-neutral replacement** for the `ℝ`-definiteness kill — so *"σ-equivariant seed recipes are DEAD" survives algebraic closure*; **(AC-7)** `hK` over `ℂ̄` **implies** `hK` over every infinite characteristic-0 field, converse **false**, so `ℝ` is the **narrowest** choice and the residual content of `[Infinite K]` is **positive characteristic only** — never probed; **(AC-8)** char 2 breaks the geometry (double plane, no splitting) but not (AC-1). **REFUTED as a class statement, OPEN on the tight stratum: (AC-6)** — the grids are a *combinatorial recipe* (a ruling 2-colouring of `E(G)`) for target-rank nondegenerate pencil realizations, reaching the target at **15/15 tight** shapes of a pinned 21-shape pool (all eight §(K-flank) flank shapes among them) and at the (K-res) inhabitant `W19` (1/1, rigid but not count-tight), 2/5 not-rigid, **18/21** overall. It **fails at three**, and the habitat attribution is the point: θ(1,2,9) and θ(2,3,7) are **out** of `hK`'s habitat (`hnoRigid` false) — θ(1,2,9)'s miss is *correct behaviour*, its triangle with two hubs already forbidden by `not_pencilNondegFeasible_of_triangle_two_hubs` — while **`C11`, a bare odd cycle, is IN the habitat and refutes the class statement by itself**. The mechanism is **parity and is complete**: no admissible colouring exists **iff** `G` has a bare odd cycle component (`C3…C14` → exactly `[3,5,7,9,11,13]`; 19/19 non-cycle pool shapes admit one) — and it **cannot** be the tight-stratum obstruction, since a tight shape has hubs and is never a bare cycle. **This row must not be read as "open" unqualified: the habitat-level statement is settled NEGATIVELY.** Chart-image membership for the grids is **proven and machine-verified** since 2026-08-06 (§(K-grid) (GR-5), 5/5 end-to-end) | for the *narrow* remainder only: the tight-stratum residual now lives in **§(K-grid)** (2026-08-06, direction T) — since direction G (Steps G8–G13) as a single geometry-free residual — since direction E (Steps G14–G18) **(GR-15)** (both-block generic `dim Z = 0` colouring existence; (GR-10)'s min-max is refuted as posed and (GR-10) stays open as the strictly stronger form; the former pair (GR-4)+(GR-6) is superseded, (GR-9) discharging the geometry wherever a triple exists) — since direction TCOL (Steps G19–G23) reduced further to a pure statement about `(G°, ℓ, bits)` (the branch reduction (GR-16), the circuit run law (GR-17), the 6-tree packing statement (GR-18), and a collapse-order-4 certificate at all 18 separators (GR-19)), **(GR-15) itself unchanged in status: still open, no flank found**. The direction-network statement this cell used to name ("isostatic whenever (AC-4)(i)–(ii) hold") is **refuted and corrected** there ((GR-2)/(GR-3): the mono-hub bond, and two proven counting families), the cheap-kill census is run and extended 15/15 → **907/907** (θ(2,5,5) + the exhaustive `K4` stratum included, no miss), and chart-image membership is proven ((GR-5)), so a target-rank grid **is** `hK`'s conclusion object. Discharging **(GR-15)** (equivalently (GR-10) with the proven (GR-9)) discharges `hK` on the tight stratum **directly**, then over every infinite characteristic-0 field by (AC-7). Nothing here would ever make the statement habitat-uniform: `C11` is permanent. **(AC-9), new 2026-08-06:** every σ-fixed body of degree `≥ 3` carries a **coincident hinge line** (pigeonhole against the two-ruling-lines cap), so the σ-fixed locus lies entirely inside the free-rotor locus and the composite guard accepts **0 of 64** `ds-K4` colourings — this **qualifies** (AC-3) (the four conjuncts and the Tay target still hold, so *Step σ6*'s claim stays refuted about that predicate) and forbids reading any σ-fixed witness as *generic* |
| **(K-mech)** *(new, 2026-08-06, direction M)* | (K-mech) (MX-1)–(MX-9) | **Both §(K-pure) *P8* anomalies mechanised, in one calculus** — the realizable-load space `Ω := V_bc^{⊥_B}` and the α-confinement of slid chain spans ((MX-2), a per-line strengthening of (PC1)). 6v11e's `dim V_bc = 2` drop = a **forced welded flex**, two overlapping α-routes through the hub-5 meet ((MX-6)); the `K222` / `K4 (1,1,3,5,4,4)` incidence = a **forced pole-cluster load** through `pt(c)` ((MX-4)/(MX-5), bounds 2/2 met with equality; the all-`{3,4}` `K5` strong-containment branch is the bound-3 case); the chord obstruction (PC3) is the special case `ω = C_bc`. **6v11e RESCUED** ((MX-7)): omitting one far-side interior kills both routes, full (W1)–(W4) witnesses 3/3 seeds × 5 supports, 9/9 prediction table — the slide device closes it after all. σ rider settled **NO** within the probed family ((MX-8); the ℓ1 hub-hub chord is the one forced exception). (MX-9): the three-mechanism predictor measured complete-and-sound on `\|V°\| ≤ 6`, finding one **new** (W4)-failing shape (`\|E°\| = 11`, cluster bound 2) it had never seen | the **sufficiency** of the three decoration-free conditions ((K-chord) + cluster ≤ 1 + no flex route) beyond the sampled strata — a wider census could surface a fourth mechanism, which would be a finding, not a defect; class uniformity untouched |
| **(K-grid)** *(new, 2026-08-06, direction T)* | (K-grid) G0–G79 | **The tight-stratum residual of (AC-6) reduces, via a chain of proven results on the contracted multigraph `G°`, to one open geometry-free gap, (GR-15). Several further targets are refuted or reshaped with exact `n_hub` boundaries — class uniformity remains untouched.** **Proven / proven-informally.** (GR-1): each `⋆`-eigen-block is a generalized `C¹`-quadratic spline system on `G°`, exact rank identity `rank = 3n_c − 3 − dim Z` (688/688 verified). (GR-3)/(GR-8): two counting families bound `dim Z`, unified as (GR-8) (rank-1 members = ≤-2-class cycles). (GR-5): chart-image membership — a target-rank grid IS `hK`'s conclusion object (`Escape.lean:555`), class-uniform over every infinite char-0 field via (AC-7); census 907/907. (GR-9)/(GR-12): the tree-triple certificate theorem in three equivalent forms; (GR-11) an ε-adic hierarchical fallback (undeveloped). (GR-16): `dim Z` reduces to an exact `3c × 3c` system on `G°` alone. (GR-17): a circuit run-count identity forces `runs(γ) ≥ 3` whenever `dim Z = 0`. (GR-18): `def(G) = 0` forces exactly 6 spanning trees, one both-block tree-triple length-compatible. (GR-19): the collapse-hierarchy certifies every census-pool separator at `r = 4` (unproven in general). At `Λ = ∅` unless noted: the binding-circuit-rich stratum is exactly `D = 0` (GR-21); five sparsity caps hold at `D = 0` (GR-22); an injective flip repair bounds violated colourings (GR-23); an unbounded-`T,Q` repair applies when every binding circuit owns a private even branch (GR-24); a `2^{n_hub}` cut criterion is the canonical `D = 0` oracle (GR-25). (GR-27): `g` is additive over 2-edge-connected blocks. (GR-28)(i)–(iii), at `Λ = ∅`: a closed defect formula; automatic `a = 0`; NC1 `⟹ g = 1` at `k = 2`. (GR-20)'s certificate-3: proven per swept `D = 0` shape (the uniform all-`n_hub` form is not). (GR-32)/(GR-33): the capacity theorem (`cap(S) ≥ 7` at every proper habitat chunk) and the weakness lemma (binding needs `save_A ≥ N − 2` aligned weaknesses). (GR-35): the defect formula is submodular. (GR-36): a structural charge bounding defect below by interior adjacency in both blocks; its **binding-capable** family strictly contains the capacity-tight one. (GR-37): admissible colourings are exactly (majority-colour, minority-dart) pairs, solvable iff the even-branch vector lies in `Cut(G°)`. (GR-38): a slack identity and attachment lemma classify every chunk crossing; at `n_hub ≤ 6` no two same-block binding chunks ever cross (0/53 740 instances, 4920 shapes). (GR-39): capacity-tight proper chunks have a proven local structure; three kills close the all-triangle-type cell. (GR-40): the corner charge prunes the fully-capable-hot census 815 → 573. (GR-41): the parity floor `⌈φ*/2⌉`, superseded by (GR-44)'s exact formula. (GR-42): a polynomial habitat-membership criterion and the pentagon necklaces `NK(m)`, `φ(NK(m)) ≥ m`, every member rank-certified fully-good. (GR-43): the odd-cycle-packing shift floor gives `d_par = d_adm = d_fg = m` **exactly** at NK(2)/6/8/10 (rank-certified) — the shift-metric layer is UNBOUNDED. (GR-44): the Hall/SDR selection step is AUTOMATIC and the parity layer has an exact per-matching coset formula `d_par(M) = w_M`, repairing (GR-37)(iii)'s parity half to statement-equals-proof; certified at 415 pairs, gap 0. (GR-45)–(GR-48): the legal-move calculus (T1/T2 moves, one-move transitivity, the coset/SDR normal form, the stuck-case reduction criterion) — kept as record, subsumed by (GR-49)–(GR-54) and, for move pricing, (GR-68). (GR-49)–(GR-53): the z-form absorbs the (c, m)/coset/SDR/matching apparatus into one bit per branch (GR-49); a balanced odd-branch pattern turns the rest into a degree-constrained orientation deciding balance EXACTLY in polynomial time (GR-50), whose two-sided Hall condition collapses to a local weight inequality (GR-51) that at most one same-colour-odd-branch hub per side can violate harmlessly (GR-52), and exhaustion over all maximal constraint structures (1/44/4837 at `2k = 2/4/6`) shows a balanced split always exists (GR-53). (GR-54): the balance theorem chains these into: every connected cubic loop-free hub multigraph with evenly many `2k ≤ 6` odd branches carries a balanced admissible configuration, discharging input (X) and re-deriving (GR-44)'s nonemptiness without Petersen. (GR-55): every minority map at distance `d` from a perfect matching `M` is a `(y, Z, φ)` triple; the `M`-avoiding coset space is affine of dimension `n/2 − 1`. (GR-56): the SPLIT identity `defect_A(S) − defect_B(S) = δ_S − σ_S` collapses full-goodness to ONE inequality per chunk — the balance rider is its whole-graph instance. (GR-57): the SDR exchange calculus (optimal stratum factors over path/cycle components; the elementary shift crosses μ-classes) — superseded by the z-form apparatus, kept as record. (GR-58): `d_fg = d_adm` verified at ALL 4920 `n_hub ≤ 6` habitat shapes, no cap, and at the first odd-carrying `n = 30` tests, rank-certified. (GR-60): input (Y), (a′)'s named residual — by (GR-56)(iv), inputs (X) and (Y) are the whole-graph and proper-chunk instances of one inequality; GBAL's proof (GR-54) is whole-graph-only, so (Y) stays open. (GR-61): the (GR-56) chunk invariants carry into the z-form exactly. (GR-64): a colouring-free collision bound prices the coupling between (Y)'s distance quantifier and its chunk constraints, with a proven `≤ 2` per-chunk ceiling. (GR-65): the fit identity — `dist(m, M)` and `z_mono(S)` are the **same statistic**. (GR-67): the M-anchored z-form gives the deviation count as a 2-factor sign-change count and a **PARITY LAW** (every per-matching layer gap EVEN). (GR-68): every legal move priced in closed form — matching branches and whole 2-factor cycles FREE, a single-path repair costing at most 2, proving (b′)'s price half outright. (GR-69): the imbalance ceiling `\|δ\| ≤ 2·min(k, ⌊n_hub/4⌋)`, proven from (GR-51)(i)(a)'s necessity alone, exactly 2 at `n_hub ≤ 6`, rising to 4 from `n_hub = 8` (a Wagner-graph witness), downgrading GDESC's small-sample reading there to forced arithmetic. (GR-73): `slack = 0` iff the pair shares no X-hub, forcing every hub of `T := S ∩ S′` to `deg_T ∈ {2, 3}` with each attachment family `≥ 2` members; the (GR-36)(iii) J-charge extends, componentwise, to any branch set. (GR-74): at `n_hub = 8` the AA-glue configuration is pinned to exactly **one** template — `T` covers all 8 hubs at 10 branches, `R`/`R′` single branches, `S ∪ S′ = E(G°)` — EXHAUSTIVE at all 44 premise-satisfying pairs of all 20 classes; the same counting explains (GR-38)'s `n_hub ≤ 6` vacuity. (GR-75): the AA-glue configuration and its whole kill residual (`slack + defect(T) ≤ 1`) are **NOT realizable** at `n_hub = 8` — a contradiction with (GR-32)(iii)'s balance identity, independently certified by an EXHAUSTIVE, uncapped scan of the complete stratum (39 689 shapes, 9 617 854 colourings, 0 instances) that also reproduces (GR-38)'s own `n_hub ≤ 6` headline exactly; so the (GR-38) intersection kill is a **THEOREM** at `n_hub = 8`, **non-vacuously**, and the **maximal** binding chunk family of each block is laminar. (GR-76): a general-`n` charge `\|W\| ≥ \|F₂\| + q_T` forces **`n_hub ≥ 10`**, so the AA-glue configuration is impossible at **every** `n_hub ≤ 8`; `n_hub = 10` narrows to exactly **three** counting-satisfiable templates. **Refuted, and what replaced it.** (GR-2): "(AC-4)(i)–(ii) ⟹ both blocks isostatic" — refuted (`ds-K4`). (GR-4): the (GR-3) bound equals generic `dim Z` — refuted as stated, repaired by **(GR-4′)**, true-modulo-named-gap. **(GR-4′) is off the critical path in one sense, load-bearing in another**: (GR-9) discharges `hK` with no generic-arrangement input, but route (i)/certificate-3 yields (GR-15) only *modulo (GR-4′)*. (GR-10): the min-max form is refuted as posed, **(GR-10) itself staying open** — grouped-packing is NP-complete at exact balance (GR-13). (GR-28)(iv): the `g ≤ 1` cap at `k ≥ 3` — refuted with an exact boundary (a THEOREM at `n_hub ≤ 6` (GR-29), FALSE from `n_hub = 8` on (GR-30)'s four witnesses, per-shape (GR-15) holding at all four (GR-31)). (GR-34): the uncorrelated union-bound mechanism is refuted by a constructed `CL10` witness (every member still fully-good); a correlated rung-minority rule closes the probed instances. **The bounded-deviation selection form**: **REFUTED as posed** ((GR-41)+(GR-42): `d(NK(m)) ≥ m/2` unbounded while every member stays fully-good). (GR-59): the PER-MATCHING variant of (a′) is REFUTED — 1278 of 24 638 pairs carry a finite `d_adm(M) < d_fg(M)`, gaps exactly `{2, 4}`; `min_M` is LOAD-BEARING, no (a′) proof may fix its anchor matching. (GR-62): full goodness is **NOT** a function of the (GR-50) degree data (7982/217 468 fibres split at 1499/4924 shapes) — no (GR-51)-shaped criterion applies to the chunk system. (GR-63): the coordinator's predicted parity obstruction is **REFUTED as stated** — (GR-52) is a per-hub-subset identity, valid at every subset, so it localizes for free; the (Y)-chain actually breaks two links earlier, at (GR-50)→(GR-51). (GR-70): per-matching (b′) reduces to one availability clause, EXHAUSTIVE on the whole stratum in its landed T1-only instance — REFUTED from `n_hub = 8` by stuck witnesses, each repaired at price 0 by a named mixed-pair successor. (GR-77): the dispatch's predicted consequence — that (GR-75) makes outright binding laminarity a theorem — is **REFUTED**: 3 774 crossing same-block binding pairs exist over the complete `n_hub = 8` stratum (against 0 at `n_hub ≤ 6`); what survives is only (GR-75)(iii)'s uncrossing of the maximal family per block, not laminarity of the family itself. **Measured, not proved.** (GR-14): a proven certificate, nil habitat applicability. (GR-26): an exhaustive 40 742-shape `D = 0` sweep, zero (GR-15) misses. (GR-31)'s flip-distance-≤-`g` law: sweep-local, breaks at `n_hub = 16`. (GR-39)'s hot-dart census, exhaustive over all 4920 `n_hub ≤ 6` shapes: zero fully-hot hubs on the capacity-tight and realized-binding families; the **binding-capable** family (GR-36) carries 761 on a 184-shape subsample. The deviation decomposes into the parity layer (GR-44) and a balance layer costing `{0, 1, 2}` everywhere probed (W3: 1 shift-metric + 1 balance unit); `d_fg = d_adm` at every shape measured, up to `d = 10`, rank-certified. (GR-66): GBAL's own certificate measured against (Y) misses the distance optimum at 3514/4924 shapes and full goodness at 651/4924. (GR-71): (b′) extended to 536 exact shapes at `n_hub = 8/10/12` and cap-free per-matching certificates at `n = 30`. (GR-78): every one of the 39 689 `n_hub = 8` shapes carries a fully-good colouring — EXHAUSTIVE, no cap — at 86.9% of 9 833 022 colourings, every shape `≥ 10`; counting-side only. Ledger entry 5 (per-shape admissibility): **PROVEN in both halves** (GR-54) — a **HIT**. **E3 is ARMED, targeting entry 1's (a′), and does NOT fire.** **(b′) stays OPEN, NOT a HIT**: price half proven, the ceiling proven-with-an-exact-boundary, availability refuted-with-a-named-successor; by-product, (GR-67) Cor. 1 corroborates (GR-59)'s per-matching (a′) gaps as forced even. Attack (c) is now **SETTLED at `n_hub = 8`** (GR-75) and pushed to `n_hub ≥ 10` (GR-76); binding itself is **not** laminar from `n_hub = 8` (GR-77). **(GR-15) stays OPEN throughout, unchanged in status, no gap-map status move** — the arc's sole remaining open gap; see *what would close it*. | **(GR-15)** *(the re-aimed discharge residual, Step G17, the critical-path form — (GR-10) stays open as the strictly stronger statement, its min-max refuted as posed)* — every tight class shape admits an admissible colouring with generic `dim Z₊ = dim Z₋ = 0` in both blocks. Implied by (GR-10); one-point-decidable per shape ((GR-7) remark (i); τ-side analogue §(K-ann) (ANH-9)), so the census's 907/907 exact hits are already **per-shape proofs** and only the uniformity gap remains. Its per-block min-max question is **(GR-4′)'s equality** — counting-shaped, untouched by (GR-13)'s hardness — a pure statement about `(G°, ℓ, bits)` alone (GR-16), exhaustively swept to 40 742 `D = 0` shapes with no hit (GR-26). Any successor route must discharge `hK` on the tight stratum over **every infinite characteristic-0 field** ((GR-1)/§(K-clos) (AC-4), (GR-5), (AC-7)). **Four live routes, none closed:** (i) a colouring-existence argument over Step G12's branch bits ("some admissible colouring has `a = 0 ∧ max g ≤ 0` in both blocks" + (GR-4′)), free at 98.6% of circuits by (GR-17); (ii) a bound on the collapse order `κ` (measured `≤ 4` on the census pool by (GR-19), unproven in general); (iii) a characterization of which `r`-co-independent groupings certify beyond `r = 3`; (iv) an exchange argument on (GR-18)'s guaranteed 6-tree packing supplying a length-compatible 3+3 split. **Dead or unselected, with homes — do not re-derive, and do not re-run as routes:** the (GR-27)/(GR-28) exact computation and the `g ≤ 1` cap on the (GR-8) family, hence the whole certificate-3-uniformity route ((GR-28)(iv) refuted at an exact boundary, (GR-29)/(GR-30)); the bounded-deviation selection form ((GR-42)); (GR-31)'s three offered candidates; and the bounded {T1, T2} / {T1, T2, K3} descent and (GR-45)–(GR-47) matching-flexibility routes, **superseded not contradicted** — (GR-54) and (GR-68) prove the statement they were chasing. **The growth-law decomposition is the best-understood target** (Steps G48–G91). Parity layer: **exact**, `d_par(M) = w_M` ((GR-44)), unbounded along the necklaces ((GR-43)); whether `w_M` admits a min-max/packing or polynomial certificate is open and deliberately untouched ((GR-13) caution). Balance layer: existence **PROVEN at every shape** ((GR-54)), and its price is `≤ 2` for a single-path repair, any legal move, any shape, no cap ((GR-68)). Fully-good layer: measured **zero everywhere ever probed**, including `d = 10`, rank-certified at the optimum to `n_hub = 50`. **The two sharpest open statements.** **(a′)** the `d_fg = d_adm` law — exhaustive at all 4920 `n_hub ≤ 6` habitat shapes at no cap and true at the first odd-carrying `n = 30` tests ((GR-58)); residual **input (Y)** ((GR-60)), a joint matching-and-representative selection in the (GR-55) coordinates; per-matching variant **REFUTED** ((GR-59): `min_M` load-bearing, no proof may fix its anchor matching). Its route is re-scoped, not replaced: the `z`-form serves the chunk/balance rung ((GR-61)), the coset coordinates the distance rung, bridged by (GR-65)'s `fit`, over a Hall/deficiency condition on the tight-chunk hypergraph of exit selections (GORIENT *Step G43*) — a (GR-51)-shaped degree-constraint criterion is **excluded** ((GR-62)), on a 10-shape exceptional family aside. **(GR-64)(R2)** is the sharpest cheap successor named. **(b′)** `d_adm − d_par ≤ 2` — price half **PROVEN** ((GR-68)); imbalance ceiling **PROVEN at `n_hub ≤ 6`, FALSE from `n_hub = 8`** at an exact boundary ((GR-69)); availability reduced to one clause (Clause A′, (GR-70)) — exhaustive on the stratum's T1 instance, refuted there from `n_hub = 8`, repaired at price 0. Residual: the **doubly-blocked** case; untried third route — minimizing `dist(·, M)` at a fixed balanced pattern is a min-cost degree-constrained orientation by (GR-50), an exchange between two flow problems. **Four named dispatchable attacks:** **(a′)** and **(b′)** above; **(c)** AA-glue realizability at `n_hub ≥ 10` — **`n_hub = 8` SETTLED NEGATIVE** ((GR-75): a non-vacuous THEOREM, the **maximal** binding family laminar per block; binding itself is **not** laminar, (GR-77)) — now a **three-template** counting question, (GR-76)'s charge `\|W\| ≥ \|F₂\| + q_T` the named instrument; **(d′)** the corner-armed realized-binding fully-hot seed hunt past GDEV's caps (not a flank by itself, E1's clarification). |
| **(K-frame)** *(new, 2026-08-07, direction J)* | (K-frame) FR0–FR11 | **The shared chart-to-frame dominance residue of directions O/Q/G, attacked via §(K-grid) *Step G13*'s lemma shape — which is delivered, and is smaller than its name.** **(FR-1)** proven: "dominance" over-asks — both residues are non-containment-in-one-hypersurface, settled by one witness point + irreducibility of the *source*; (ANH-14)'s source is the whole chart (irreducibility owned by §(K-ann) (ANH-9)(ii)), (OC-16)'s is the un-owned hard-stratum target-rank locus, needed **only** to combine separately-witnessed open conditions ((FR-7)). **(FR-2)/(FR-3)** proven: at a σ-fixed grid point every hinge line is a ruling line, the two families span complementary 3-spaces (= §(K-clos) (AC-4)'s `⋆`-eigenspaces, each a Veronese conic), and **any 6×6 hinge-line determinant — both bad divisors included — is nonzero ⟺ its edges are coloured 3–3 with pairwise-distinct components per family** (`det = 128·Vdm(s)·Vdm(u)`, an identity over the function field, `framedom.m2`); incidentally makes (AC-9) obvious with the coincident pair located exactly. **(FR-4)** true-modulo-named-gap (the (GR-5)-at-`G′` restatement, hypotheses machine-checked per instance): the transport works by **regridding at `G′ = G − v + ab`** (alternation makes `pt(a) ∈ M` automatic), and a *pattern colouring* yields an exact ℚ(i) chart witness proving the (ANH-R1) β-clause at its site via (ANH-9)(iii). **(FR-5)** measured: pattern availability **1904/1904** bare-cycle sites (census pin = (ANH-13)'s 1904), **30/30 exact end-to-end certificates** with negative controls. **(FR-6)** exact per point: at θ(3,4,5), 4/8 admissible colourings land on the hard stratum at target rank — the first **constructed** inhabitants — each a literal (OC-8) witness; the **strict** availability package is **0/8**, mechanism (AC-9) (structurality open). **Since Steps FR7–FR11 (2026-08-07, direction PEX): (FR-R1) is PROVEN.** The bare-cycle stratum is **finite** (a bare-cycle site forces `c(G) = 3`, hence `n_hub ≤ 4`) and **exhaustively enumerated**: **22 isomorphism classes, 76 sites, 1976 labelled instances**, every one pattern-available, both by a uniform structural argument ((FR-9)–(FR-12): the frame's normal form, the component law, and vacuity of legality (i)) and independently by the exhaustive scan itself ((FR-8)). The former sweep-boundedness caveat **dissolves rather than widens**: `outer.sweep_shapes` covers 14 of the 22 iso classes (58 of 76 sites) and misses none of what it carries ((FR-14)). **No gap-map status moves; class uniformity — `hK`'s status — is untouched.** **Since Steps FR12–FR15 (2026-08-19, direction FRES): (FR-4)'s named gap is CLOSED.** **(FR-15)** transports (GR-5) to `G′` verbatim, minus its target-rank clause (`G′` is not tight). **The correction this direction found:** (GR-5) is a chart-**MAP** statement (hub normals free, body points derived), while (ANH-9)(iii)'s semicontinuity needs membership in the chart-**VARIETY** of (ANH-9)(ii), whose parametrization runs the opposite way (hub points free, panel normals derived — literally `widened.place_pencil_general`) — a different sentence the first does not imply. **(FR-16)** supplies it: at a σ-fixed configuration the normals *are* the points, so the two parametrizations' genericity loci coincide on the single clause `framedom.legality_free` already tests, and it also retro-certifies (FR-6)'s θ(3,4,5) points as honest `G′`-chart points. **(FR-17)** then proves the (ANH-R1) β-clause at every bare-cycle site of every `k = 4` class triple (76 class-level sites, 22 iso classes) with **no named gap**, at the arc's ordinary proven-informally standing; no driver was run — every hypothesis is already asserted per instance by the landed `framedom.py`. **No gap-map status moves; class uniformity untouched.** | **Nothing on the (ANH-14) side.** (FR-17) (direction FRES, 2026-08-19) is the unconditional discharge on the whole bare-cycle stratum, no rider. The (OC-16)-side residual ingredient (irreducibility of the hard-stratum locus, or a per-shape simultaneous witness) stays with §(K-out) (OC-8), untouched |
| **(K-chart)** *(new, 2026-08-19, direction CIRR)* | (K-chart) CH1–CH8 | **A HIT — the arc's most-consumed un-driver-tested fact, written down once.** **(CH-1)** proves the pencil chart of `G′` (loopless, `hcard`, min degree 2, girth ≥ 4) is a nonempty, irreducible, ℚ-rational variety, a tower of affine-linear fibres; the constant-fibre-dimension restriction is **identified, not assumed** — it **is** `IsNondegPencilRealization` conjunct 3 ((CH-6)), which `hK`'s own hypothesis already supplies at `G′`. **(CH-4)** shows the restriction costs no closure (an off-restriction legal realization is still on the same irreducible variety); **(CH-5)** finds *Step FR13*'s stated hypotheses (girth ≥ 3) do **not** give nonemptiness — a Λ-triangle with a non-hub on two of its hubs empties the tower at every seed — and girth ≥ 4 does, free at `G′` three independent ways (the girth-6 table row, `gridcol.class_shape`'s two-hub-triangle filter, and the landed `not_pencilNondegFeasible_of_triangle_two_hubs`). **(CH-7)** audits all **four** named consumers — §(K-out) (OC-19), §(K-slide) (S1)(e), §(K-dom) (D4), §(K-ann) (ANH-9)(ii) — clean, two needing strictly more than bare irreducibility (rationality; the closure clause), both supplied. **(CH-8)** is a **pointer, not a new claim**: the triangle-with-two-hubs infeasibility it first derived is already landed and compiler-checked, strictly stronger, as `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563`); this section's own addition there is only the chart-side contrast (`𝒜(Γ) ≠ ∅` at 174/200 seeds of a triangle-carrying control while `PencilNondegFeasible` is false there). **No gap-map status moves; (OC-8), (ANH-R1), (GR-15), class uniformity, the balance layer and route-ledger entry 5 all untouched** | — settled; not a gap. The one open thread is *Step FR13*'s own hypothesis-list correction (girth ≥ 4), carried as a rider there ((FR-16)'s row), not a residual here |
| **(K-ann)** *(new, 2026-08-06)* | (K-ann) A1–A17 | **A recipe delivered and an input relocated — read the two halves separately, and do not let the first warm up the second.** **Delivered, and the arc's first *formula* rather than a search** (`Pencil-strategy.md` §2.2's sense): **(ANH-2)** the reciprocity identity `dλ(π_P ω) = Σ_e ω_e B(τ_e, δC_e)`, local at the moved vertex, no genericity hypothesis, class-uniform, verified at 276 far-chart directions × 828 motions against an independent implicit differentiation; **(ANH-3)** at the named move (translate one non-hub 2-valent far body) it collapses to **one Klein pairing**, 192 single-vertex moves. Carry its caveat: *the formula's kernel is bounded-size and class-uniform; what it pairs against (`τ`, `ω`) is not* — so U1 is **half** delivered, the move and the formula but not the inputs. **Proven, and the mechanism behind (D2):** **(ANH-1)** `λ` **is a self-stress** — of the *contracted* framework `H/P` (weld the companion into one body), stress dimension exactly `k−3` (18 seeds, 9 habitats, `k = 3..6`), so (T5)/(D2) stop being measured bounds. **Proven, `k = 4`-only:** **(ANH-4)** `E(H/P)` is a **circuit of the generic Tay matroid**, from 5/6-sparsity + `hnoRigid`, the count `5k+10 ≤ 6k+6` tight exactly at `k = 4` — the same equality case as (D3)'s `k ≥ 4`; realized side, the support is the **whole** far edge set at 14/14 class seeds, so the named move needs **no support-location step**, with an off-class control (`hnoRigid` dropped) where the circuit is a proper 5-cycle and moves off it leave `V_bc` exactly fixed. **(ANH-7)**: on the **89 %** (3820/4296) of triples with a length-5 `H/P` branch the whole criterion is **one 4-point bracket**, correct 56/56. Corrections recorded here because they were written down before the pass ran: option B and U2 are **not** the same object (`λ` is a self-stress of the contracted **far** framework, not `[r]`); U2's cocircuit reading is the **dual** of what the recipe needs (`supp τ` is a *circuit*); and the pass's own `⟨C(z₁z₂)⟩` kill set is wrong at `dim U_y = 1`, the general criterion being `ρ_y ⊥_B (V_y ∧ U_y)`. **`k`-grading:** (ANH-1/2/3/5/6) and (SD-6) are length-free (`k = 3..6`); **(ANH-4) is provably `k = 4` only**, and with `k = 4` the `hnoRigid` equality case **no `k`-graded mechanism including this one can close the class** — the verdict `Pencil-strategy.md` §4.6 already carries. **No gap-map *status* moves; class uniformity untouched** | **(ANH-R1)** `τ_β ≠ 0` at the pencil placement — `H/P − β` (count exactly 0, generically isostatic) is **rigid** there. This is **relocation #4**, of a *different kind* for three reasons and *not thereby easier*: it crosses into a matroid that **has** a min-max (Tay, Phases 12–15) whose combinatorial half (ANH-4) **proves**; it lands on a **strictly smaller graph** (`\|E(G)\|−12` edges); and by §(K-ind) *Step I6* the welded body is not a pencil body, so it sits on the **mixed stratum** — not the same problem shrunk, and `Pencil-strategy.md` §4-C3's second concrete consumer after (OUT). It does **not** evade §2.3 (a rank *lower* bound): **limiting, not fatal** — the smaller graph's matroid is Tay's, where independence *is* combinatorially characterised, so the wall changes from "no matroid sees this" to "the matroid sees it and the pin may not respect the matroid" (the weak-map / specialization-stability lead of §4.6, which now has a statement to attach to). **"Easier or merely smaller" — SETTLED AS SCOPED (2026-08-06, Steps A10–A13, direction R): merely smaller in difficulty class**, with two structural gains and one proven loss. **(ANH-9)**: (ANH-R1) per triple ⟺ one exact rank computation at one rational chart point (weak-map formulation; `Pencil-strategy.md` §4.6's lead gets its precise statement); **(ANH-10)**: the pinned census probe is a clean negative at generic guarded seeds — 26/26 `dim S_pen = 1` with full support, 58/58 length-5-branch sites `τ_β ≠ 0`, so (ANH-R1) is **discharged at the generic point of every probed triple**; **(ANH-11)/(ANH-12)**: the bad locus is **INHABITED** — exact rational guard-accepted points (8/9 target-rank hard-stratum) where `H/P − β` goes dependent and `supp` strictly drops (11 → 6 at six exact witnesses) — so **the pencil pin respects Tay's matroid only generically, never pointwise, and no counting/matroid/placement-blind route to (ANH-R1) exists** (the τ-side analogue of (OC-3), by construction). Remaining: a **class-uniform independent-point recipe** ((ANH-9)(iii)) — the same missing technology as §(K-grid)'s residual (directions T and R converge; since direction G that residual is **(GR-10)**). The per-shape M2 identity `C(H/P − β) ≢ 0` was **RUN (2026-08-06, direction Q — Steps A14–A17): no shape refuted, and the "upgrade" reading was WRONG** ((ANH-16)(i): (ANH-9)(iii) already makes each census row a proof, so the identity is the pointwise restatement of (ANH-R1)); what survives is structure — **(ANH-13)** the branch-core normal form with the exact size law `deg C(H/P − β) = 12(c(G) − 2)`, bounded exactly on the finite part of the class; **(ANH-14)** the whole **bare-cycle stratum** (1904/6426 length-5-branch sites) governed by **ONE universal irreducible degree-12 bracket polynomial**, proven `≢ 0` over the function field with `det Gram = −C²`, so (ANH-R1) there is a **chart-to-frame dominance question with no rank condition left** (the **third** independent arrival at §(K-out) (OC-16)'s residue) — **since §(K-frame) (2026-08-07, directions J/PEX) that residue is CLOSED AS AN ARGUMENT on the whole bare-cycle stratum**: (FR-R1) is **PROVEN** — the stratum is finite (22 iso classes / 76 sites / 1976 labelled instances) and exhaustively enumerated with a pattern colouring at every site — via (ANH-9)(iii) each such point is a proof of the (ANH-R1) β-clause at its site, and since 2026-08-19 (direction FRES) that gap is **CLOSED** — §(K-frame) (FR-16)/(FR-17) discharge the stratum with no rider — and, by irreducibility, **no (ANH-7)-style one-bracket recipe exists for (ANH-R1)'s own certificate**; **no gap-map status moves and `hK`'s status is untouched**; **(ANH-15)** the bad locus **strictly contains** (ANH-11)'s transversal locus (a second, axis-free mechanism; all 9 (ANH-12) witnesses verified inside `{C = 0}`); **(ANH-16)** the M2 layer's reach bracketed from both sides (degree 12 in 24 indeterminates finishes at 578 s; the θ core at the generic point does not finish at 600 s). What it *would* close: the **length-4-companion stratum outright**, via §(K-Λ)'s Λ-completeness, since `dλ ≢ 0` makes `{λ = p⁺}` proper on an irreducible chart |
| **(K-out)** *(new, 2026-08-06)* | (K-out) O1–O18 | **(OUT)'s hypothesis, measured — the headline is the NEGATIVE.** **(OC-3)**, load-bearing: `{λ₁ = 0}` is nonempty at every class shape's chart (`dim R₁ = 5` forces `dim(R₁ ∩ L_b) ≥ 1`), so **no counting argument, no matroid statement and no placement-blind argument can ever deliver (OUT)'s hypothesis**; the bad locus is also proper (`dim(R ∩ L) = 1`, never 2, at 46/46 sampled frames) — though `dim(R ∩ L) = 2` is reachable by construction (**OC-14**: a hub slide onto the explicit bad line `C₀`, 38/38 fully-nondegenerate target-rank points, no coincident hinge — (OC-7)'s necessity direction fails beyond this pool). **The combinatorial half alone does not deliver availability: (OC-2)**'s uniform 4296-pair result collapses to **one** measured fact — rigidity of `H/X` — which **(OC-10)** proves **forced at every class shape** (four hypotheses load-bearing, girth-6 plus one `hnoRigid`-discharged boundary case), striking availability items 1–2; θ(3,4,5) is the unique theta class member. **The positives are pointwise, over two disjoint pinned pools: (OC-5)** POOL-G (357 frames), hypothesis 356/357, conclusion 356/356; **(OC-6)** POOL-S (270 frames), 270/270, 0 silent pairs; **(OC-1)**'s hinge-rate identity, exact; **(OC-4)** the bad line reached by a legal chart move at all four habitats — the escape holds exactly where (OUT) is blind. **(OUT) is available, never automatic, not contradicted. No `place_pencil_general` battery may be quoted as a rate or as evidence about a generic chart point** — POOL-G figures over the 318 coincidence-free frames, never the raw 357. **(OC-7) is CLEARED**: the sampler's single-hub-interior degeneracy (32/357 POOL-G frames, implying `λᵢ = 0`) is fixed by the composite guard `repin.star_generic`, adopted everywhere except this section's two measuring modes; **(OC-9)** measures it rejects 58/357, strictly containing the two-end diagnostic's 39. **(OC-17)** frees the hard-stratum qualifier: `dim R_a = corank(G′) − s₀` at **every** legal chart point, so at `index(G) = 0`, `def(G′) = 0` the hard-stratum locus `Z` is an intersection of two maximal-rank conditions — Zariski open, not a stratum (`Z ≠ ∅` a separate input). **(OC-18)**: `H/X` infinitesimally rigid at a chart point ⟹ `L_b ⊄ R₁`, degree-free, open, at both ends of every class pair (5226/5226). **(OC-19)** reduces (OC-8) at a (shape, split) to `Z ≠ ∅` + chart irreducibility + one chart point with `H/X` rigid — one-point decidable, **two named inputs**. **`Z ≠ ∅` alone does NOT give (OC-8)**: `--control` builds 3 constructed points in `Z`, guard-accepted, coincidence-free, `L_b ⊆ R₁`, `H/X` flexible — `Z` meets the bad divisor, so the reduction needs openness **plus** irreducibility **plus** a witness. **(OC-20)/(OC-21)** restate the bad case in perp form and strip `x₁` from availability; **(OC-22)** lands the residue in §(K-ann) (ANH-R1)'s object class. **Chart irreducibility (input (b)) is PROVEN**: §(K-chart) **(CH-1)(a)**, unconditional at `Γ = G′`. **Input (a), `Z ≠ ∅`, itself factors: (OC-23)** its `s₀` half is exactly independence of `H = G − v − a` alone, at every chart point; **(OC-24)** the dichotomy — `Z ≠ ∅ ⟺` both halves nonempty, one-point witnessable — and `{σ = 0} = ∅` at a class shape would make `hK` **FALSE there** (a **PENCIL event**, not a (K-tight) one), so the `s₀` half is **necessary for `hK`** and can never be the binding obstruction; **(OC-25)** the target-rank half **is** §(K-tight) *Step 2* item 1's attainment criterion one split down; **(OC-26)** its failure has a closed form — a **disjunction**, both branches forcing a codimension-2 Schubert jump of `D` (the far framework's relative twist space), corrected after this pass's own first closed form was refuted by construction; **(OC-27)** measures 138/138 (shape, split) witnesses of `Z ≠ ∅`, no miss; **(OC-28)** the `s₀` half is **dominated** by §(K-grid) (GR-10) — one grid point per shape covers every split, free at 907/907 of that pool — with `{σ = 0}` a **proper** open, witnessed at the (K-res) shape `P21`. **Input (a) stays OPEN as a class-uniform statement and is NOT an independent gap; (OC-8) stays OPEN, reshaped; no gap-map status move.** | **(OC-8)**: at every class shape, a hard-stratum target-rank point of the **whole-graph** chart with `L_b ⊄ R₁` or `L_c ⊄ R₄`. That is a rank **lower** bound at a pencil placement — `Pencil-strategy.md` §2.3's wall **relocated** onto the smaller `H/{e₂,e₃,e₄}` and **weakened, not crossed** — and (OC-3) says the relocation **cannot be discharged combinatorially**, so any proof must be a genericity argument on the whole-graph chart (needing its hard-stratum component not to lie inside `{λ₁ = 0} ∩ {λ₄ = 0}`), which the arc has never established because `λ` is a **far** datum. The one symbolically tractable piece — `L_b ⊄ R₁` as a polynomial non-vanishing (`Pencil-strategy.md` §5.3) — is **DELIVERED on the `ℓ_min = 5` stratum** ((OC-16): `Δ = [a,u,b] · C₀(pt b) ≢ 0` at the local frame's generic point, the bad line `C₀` in **closed form**) and **blocked off it** ((OC-15): the path-span form carries no information at `ℓ_min ≥ 6`; the stratum is 8 of 5226 pairs); at a **degree-3 hub** (3081/5226 pairs at the `b` end) (OC-8) restates with **no rank condition left** — availability ⟺ the hard-stratum target-rank locus `⊄ {pt(b) ∈ C₀}` — with **chart-to-frame dominance** the named residue ((OC-16)'s gap); the non-containment is **witnessed by construction** at θ(3,4,5) (4/8 admissible `G′`-colourings on the hard stratum at target rank, each with `Δ ≠ 0` at one end — §(K-frame) (FR-6)), the strict availability package is **0/8 at σ-fixed witnesses** with the (AC-9) coincidence the named mechanism (structurality open), and at grid points `Δ` is **combinatorial** ((FR-3)). **Input (a), `Z ≠ ∅`, itself factors** (§(K-out) direction ZNEQ): a **necessary-for-`hK`** half — `H` independent at some chart point, equivalently at the generic one — **dominated** by §(K-grid) (GR-10), free at 907/907 of its pool once **re-keyed** against this section's class-shape population (a combinatorial cross-pool job, no new mathematics; the two pools are labelled-instance pools with different keys and are **not** re-keyed here); and a **target-rank** half, the Schubert **non-jump** `dim(D ∩ (M̂ ∧ W)) ≤ 1` (`D` the far framework `H`'s relative twist space, `W` the hub line's 2-space) — one-point decidable, `x₁`-free, `λ`-free, stratum-free, in the same object class as (OC-20)'s perp form; measured to fail nowhere (138/138 (shape, split) witnesses, (OC-27)) but a **recipe** is missing, exactly as for (OC-19) input (c). Neither half is proven class-uniformly. **The only known failure mechanism for the necessary half is a self-stress of a short theta sub-multigraph inside `H`** (§(K-flank) *F5(d)*'s support) — a hit there would make `hK` **FALSE** at that shape, a **PENCIL event**, not a (K-tight) one, and needs the direction-A pivot rule (`Pencil-fanout.md` §"Direction A") in force before any dispatch.|
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
θ(3,4,5) by a reduced support, and **6v11e by the slide device at a
mechanism-guided reduced support** (§(K-mech) (MX-7), 2026-08-06 — previously by
its chart certificate only; the old 5-support menu omitted only b/c-side
interiors, which the ledger shows keep both flex routes alive). So what remains
uncovered is no longer a *shape* list: it is the **class-uniform** statement.
The two formerly unexplained mechanisms of §(K-pure) *P8* — 6v11e's
`dim V_bc = 2` drop and the `V_bc ∩ Λ²π̂ ≠ 0` incidence at `K222` /
`K4 (1,1,3,5,4,4)` — are both **mechanised in §(K-mech)** ((MX-6) the welded
flex, (MX-4)/(MX-5) the pole-cluster load), in one calculus.

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
**6v11e acyclicity flank** failed **(W2)** (`dim V_bc = 2`) at all four nonempty
probed supports, with only the degenerate `Σ = ∅` (the `ε = 1` chart, where (S1)
is **vacuous**) pitched; its split closed anyway, by the (K-pitch) Step-0
one-witness argument — full chart transfer certificates ((T1)–(T3) +
`Q(r) ≠ 0`, `dim R_a = 1`, the (T2) side conditions) at **11/11** valid seeds.
`pure.py --support`. *(Superseded 2026-08-06, §(K-mech): the four probed
supports all omitted b/c-side interiors — exactly the omissions (MX-6)'s flex
ledger shows keep both routes alive; a single far-side omission rescues the
device, (MX-7), so 6v11e is now closed by the slide device too.)* **This answers
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
  supports *of this 5-support menu* — **superseded 2026-08-06, §(K-mech)
  (MX-6)/(MX-7): the drop is a forced welded flex whose routes these
  b/c-side omissions cannot kill; a far-side single omission rescues the
  device (9/9 prediction table)**. Only `Σ = ∅` is pitched here — but that is
  the `ε = 1` chart, where the
  slide is the identity and **(S1) is vacuous**: the "witness" is just a chart
  seed. The *split* is nevertheless closed, by (K-pitch) Step-0 one-witness
  logic: full chart transfer certificates ((T1)–(T3) + `Q(r) ≠ 0`, which also
  check `dim R_a = 1` and the (T2) side conditions that (W1)–(W4) do not) at
  **11/11** valid seeds. *(Both halves of the closing sentence this bullet used
  to carry — "the slide device does not reach this shape and no mechanism for
  its (W2) drop is known" — are **withdrawn 2026-08-06, §(K-mech)**: the
  mechanism is the welded flex (MX-6), and the device reaches the shape at a
  mechanism-guided support (MX-7).)*

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

**Both questions are ANSWERED (2026-08-06, §(K-mech))**: the incidence is a
forced pole-cluster load through `pt(c)` ((MX-4)/(MX-5), bound 2 met with
equality, the chord stress being the special case `ω = C_bc`), and the 6v11e
drop is a forced welded flex ((MX-6)) — both in one calculus on the
realizable-load space `Ω`. They were the two honest gaps of this pass, and
(PC-Z)'s reduction — "why does the pitch vanish?" to "why does `V_bc` meet one
of two named isotropic 3-spaces?" — is exactly the form the mechanisms answer.

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
   sub-class. 6v11e is where to start. **RUN 2026-08-06 as fan-out direction M
   (§(K-mech))**: 6v11e rescued ((MX-7)), the sweep measured
   complete-and-sound for the three-mechanism predictor ((MX-9)), one new
   (W4)-failing shape found-and-explained; the class-level refutation remains
   unexhibited.

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
— *and, since 2026-08-06, by the slide device itself at a mechanism-guided
support (§(K-mech) (MX-7))*. So every
probed §(K-slide-comb) Step-D5 flank shape now has its split closed, per shape,
and §(K-flank) *Step F7* item 2 is answered. **Open** *(updated 2026-08-06)*:
the two anomalies this verdict used to list — 6v11e's (W2) drop and the
`K222` / `K4 (1,1,3,5,4,4)` incidence — are **mechanised in §(K-mech)**
((MX-6), (MX-4)/(MX-5)); what remains open is whether `∃Σ` with the
three-condition set ((K-chord) + cluster bounds ≤ 1 + no flex route) and
(W1)–(W4) is class-uniform.
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

> **Step numbering, flagged because it is new in this section.** §(K-Λ)'s
> existing steps are bare numbers (*Step 0* … *Step 8*, plus *Step 3a* and
> *Step 5a*), and `notes/Pencil-labels.md`'s measured diagnosis clause 4
> records that bare step numbers collide with claim labels — §(K-Λ) already
> mints driver blocks (P1)–(P7) against §(K-pure)'s *Steps P0–P9*. The steps
> below therefore use the **`Λ`-prefixed form**: ***Step Λ8*** is a **new**
> step and is **not** the existing *Step 8*. Cite them as *Step Λ8* … *Step
> Λ12*, never as a bare parenthesized token ((L2)).

### Step Λ8 — the branch calculus: class membership is a statement about `G°` alone

Everything §(K-Λ) needs about *which* companion shapes exist is decided one
level below the subdivision. Let `G` be feasible ((R4)) and 2-edge-connected,
so that `G` is the subdivision of its **hub multigraph** `G°` (vertices = the
hubs, `n° := |V°|`, edges = the branches, `e° := |E°|`) with branch lengths
`ℓ : E° → ℤ_{≥1}`; write `c(F) := |F| − |W(F)| + comps(F)` for the cycle rank
of a branch subset `F ⊆ E°` on its incident hub set `W(F)`, and
`c° := c(E°) = e° − n° + 1`.

> **(Λ4) the branch calculus** *(proven-informally; the reduction is the
> classical one, the `G°`-form is what is new here)*. With the notation above:
>
> **(i)** `G` is **tight** (`5|E| = 6(|V| − 1)`) ⟺ `Σ_{e ∈ E°} ℓ_e = 6·c°`;
> and then `|V| = 5c° + 1`, `|E| = 6c°`.
> **(ii)** Given (i), `def(G) = 0` ⟺ `Σ_{e ∈ F} ℓ_e ≥ 6·c(F)` for **every**
> branch subset `F ⊆ E°`.
> **(iii)** Given (i) and (ii), `hnoRigid` ⟺ that inequality is **strict** for
> every **proper** `F ⊊ E°`.
>
> So the class predicate — tight ∧ `def = 0` ∧ `hnoRigid` ∧ `hcard` ∧
> triangle-free — is a finite statement about the pair `(G°, ℓ)`, with `hcard`
> reading *"the length-1 branches form a subgraph of maximum degree ≤ 2"* and
> triangle-freeness a **consequence**, not a hypothesis.

*Proof.* Write `f(W) := 5|E(W)| − 6(|W| − 1)` (*Shared dictionary*). (i) is
`f(V) = 0` rewritten: `|V| = n° + Σ(ℓ_e − 1)` and `|E| = Σℓ_e`.

For (ii): `def(G) = 6(|V| − 1) − 5|E| + max_P Σ_{parts} f(part)` and, under
(i), `f(V) = 0`, so `def(G) = 0` ⟺ `Σ_{parts} f ≤ 0` for every partition.
Singletons have `f = 0`, so taking `P = {W} ∪ singletons` gives `f(W) ≤ 0` for
every `W`, and conversely that suffices. Now `f(W ∖ {u}) = f(W) − 5·deg_{G[W]}(u)
+ 6`, so any `f`-maximizer has `deg_{G[W]} ≥ 2` throughout; a degree-2 vertex
of `G` in such a `W` therefore brings both its neighbours, so `W` is a **union
of whole branches**. On a branch union `F` one computes directly
`f = 6·c(F) − Σ_F ℓ`. Hence `f ≤ 0` everywhere ⟺ `Σ_F ℓ ≥ 6c(F)` for every
branch subset.

For (iii): under (i)+(ii) every `W` has `f(W) ≤ 0`, so
`def(G[W]) = −f(W)` and `G[W]` is rigid ⟺ `f(W) = 0`; the same maximizer
argument makes every such `W` a branch union. ∎

**Four consequences, one line each, and all of them are facts the arc already
uses:**

- **girth `≥ 7`.** `F` a cycle of `G°` has `c(F) = 1`, so `Σ_F ℓ ≥ 7` by
  (iii) — i.e. every cycle of `G` has length `≥ 7`. (Sparsity alone gives
  `≥ 6`; `hnoRigid` removes the rigid `C₆`.) In particular triangle-freeness
  and simplicity of `G` are consequences, and `G°` is **loopless**.
- **(SD-6) re-derived.** `F = E° ∖ {β}` has `c(F) = c° − 1` (no bridges, by the
  same count), so `6c° − ℓ_β > 6(c° − 1)`, i.e. **`ℓ_β ≤ 5`**. This is
  §(K-ann) (ANH-8)'s statement with a two-symbol proof.
- **(D3) re-derived.** The split branch (length 3) plus a companion of length
  `k` is a cycle, so `3 + k ≥ 7`, i.e. `k ≥ 4` — and `k = 4` is the
  **equality** case, which is the calibration `hnoRigid` is tight at.
- **parallel branches.** Two parallel branches have `Σℓ ≥ 7`; three have
  `Σℓ ≥ 13`; so multiplicity is at most 5.

*Standing of (Λ4).* It is a **reformulation**, not new mathematics: (ii)/(iii)
are the branch-union reduction that `kslide.no_rigid_branch_union` already
codes. What it buys is that the class predicate becomes cheap enough to
enumerate **exhaustively** rather than sampled or capped — which is what
*Step Λ11* does — and that *Step Λ9* can be stated as one inequality.

### Step Λ9 — the companion-cycle lemma, and the size floor it forces

Fix a class shape `G`, a **split** (a length-3 branch `e₀` whose two ends
`b, c` are hubs — by *Standing notation* and `widened.orient`, eligible splits
are exactly the length-3 branches between two hubs, in either orientation) and
a **length-4 companion** `P = b–x₁–x₂–x₃–c`. Let

> `Z := {e₀} ∪ {branches of P}`, `W₀ := ` its hub set, `j := #{i : x_i a hub}`.

Because `P` traverses whole branches, `Z` has exactly `j + 2` branches on
`j + 2` hubs, `c(Z) = 1`, and `Σ_Z ℓ = 3 + 4 = 7` — it is (D3)'s proper `C₇`,
seen in `G°`.

> **(Λ5) the companion-cycle lemma** *(proven-informally)*. **No branch of
> `G°` outside `Z` has both of its ends in `W₀`** — unless `E° = Z ∪ {β}` and
> `V° = W₀`, which forces `j = 0` and `G = θ(3,4,5)`.

*Proof.* Let `β ∉ Z` have both ends in `W₀`. Then `F := Z ∪ {β}` is connected
with `c(F) = 2` and `Σ_F ℓ = 7 + ℓ_β ≤ 12` by (Λ4)'s `ℓ ≤ 5`. (Λ4)(iii)
demands `Σ_F ℓ > 12` whenever `F` is proper, so `F = E°` and `W₀ = V°`; then
(Λ4)(i) gives `7 + ℓ_β = 6·c° = 12`, `ℓ_β = 5`, `c° = 2`, `|V| = 11`. Every
hub of `W₀` has `Z`-degree 2 and gains at most 1 from `β`, so at most two hubs
reach degree 3 — hence `|W₀| = j + 2 = 2`, `j = 0`, and `G` is a θ-graph with
branch lengths `(3, 4, 5)`. ∎

*(The exceptional case is not decoration: it is exactly **θ(3,4,5)**, the
arc's own §(K-Λ) exemplar — `G°` is then three parallel branches of lengths
3, 4, 5. Consistent with §(K-out) (OC-10), which reaches the same shape by an
independent route; that is a cross-check, not a second result, and this pass
does not re-derive (OC-10).)*

> **(Λ6) the size floor** *(proven-informally)*. Off the θ(3,4,5) boundary,
> put `t := n° − (j + 2)` and `m' := e° − (j + 2)`. Then
>
> `t ≥ 1`, `m' ≥ j + 2`, `2m' ≥ (j + 2) + 3t`,
>
> hence `n° ≥ j + 3` and `c° ≥ ⌈(2j + 7)/3⌉`, i.e. `|V| ≥ 5c° + 1` and
> `|E| ≥ 6c°`:
>
> | `j` | `n° ≥` | `c° ≥` | `|V| ≥` | `|E| ≥` |
> |---|---|---|---|---|
> | 0 | 3 | 3 | 16 | 18 |
> | 1 | 4 | 3 | 16 | 18 |
> | **2** | **5** | **4** | **21** | **24** |
> | **3** | **6** | **5** | **26** | **30** |
>
> (The `j = 0` row is the off-boundary bound; the (Λ5) boundary case itself is
> θ(3,4,5), with `n° = 2`, `c° = 2`, `|V| = 11`.)
>
> Moreover at `t = 1` the hub multigraph is **forced**: the `j + 2` branches
> outside `Z` all join the unique non-frame hub to the `j + 2` hubs of `Z`,
> one each, so `e° = 2j + 4`, `n° = j + 3`, `c° = j + 2`, and `G°` is the
> **wheel** on the `(j+2)`-cycle `Z` — for `j = 2` the wheel `W₄`, which is
> `K5` minus a perfect matching (`pencil_escape.K5_minus_matching`'s base
> graph), and for `j = 3` the wheel `W₅`.

*Proof.* Each hub of `W₀` has `Z`-degree 2 and needs degree `≥ 3`, so carries
a branch outside `Z`; by (Λ5) that branch's other end is off `W₀`, whence
`t ≥ 1` and `m' ≥ |W₀| = j + 2` (each outside branch supplies at most one
`W₀`-end). Counting ends of the `m'` outside branches: `2m' ≥ (j+2) + 3t`,
since the `t` non-frame hubs draw all `≥ 3` of their incidences from outside
`Z`. Now `c° = e° − n° + 1 = m' − t + 1`. The first bound gives
`c° ≥ j + 3 − t`, i.e. `t ≥ j + 3 − c°`; substituting into
`c° ≥ (j + 2 + 3t)/2 − t + 1 = (j + 4 + t)/2` gives `2c° ≥ j + 4 + j + 3 − c°`,
i.e. `3c° ≥ 2j + 7`. At `t = 1` the only non-frame hub is `h`, `G°` is
loopless (girth `≥ 7`), so every outside branch is `h`–`W₀`; `m' ≥ j + 2` and
one per `W₀`-hub forces `m' = j + 2` exactly, with no parallel pair. ∎

**What (Λ6) explains.** The families the arc swept are θ (`n° = 2`), `K4` and
`K4 + parallel` (`n° = 4`), and the three simple hub graphs on `n° = 5`. By
(Λ6) a `j = 2` companion needs `n° ≥ 5` **and** — combined with (Λ5) at
`t = 1` — `e° = 8`, i.e. the wheel `W₄`; and a `j = 3` companion needs
`n° ≥ 6`, so it **cannot** appear in any `|V°| ≤ 5` family at all. That is one
half of the recorded "4 of 8 patterns" boundary turned into a theorem. The
other half is *Step Λ11*'s cap.

### Step Λ10 — the witnesses: item (vii) is REALIZED

The (Λ6) floors are **attained**, at all four patterns, by class shapes that
also carry a hard-stratum target-rank pencil-chart point.

> **(Λ7) the two-hub-interior witnesses** *(constructed and harness-certified;
> the class predicate is the tracked oracle's, the geometry is one guarded
> chart point per split)*. The three shapes below are class shapes — tight,
> `def = 0`, `hnoRigid`, triangle-free, `hcard` — and each carries a length-4
> companion with `j ≥ 2` interior hubs at an eligible split:
>
> | name | `G°` | `|V|`, `|E|` | `n°`, `e°`, `c°` | patterns realized |
> |---|---|---|---|---|
> | **`LT21a`** | wheel `W₄` | 21, 24 | 5, 8, 4 | `(1,1,0)` and `(0,1,1)` |
> | **`LT21b`** | wheel `W₄` | 21, 24 | 5, 8, 4 | `(1,0,1)` (both orientations) |
> | **`LT26`** | wheel `W₅` | 26, 30 | 6, 10, 5 | `(1,1,1)` (both orientations) |
>
> In `kslidecomb`'s `specs` form (`specs[0]` the length-3 split branch,
> hubs `b = 0`, `c = 1`, companion interior hubs `2, 3(, 4)`, non-frame hub
> last):
>
> ```
> LT21a  [(0,1,3), (0,2,1), (2,3,1), (3,1,2), (4,0,5), (4,2,5), (4,3,5), (4,1,2)]
> LT21b  [(0,1,3), (0,2,1), (2,3,2), (3,1,1), (4,0,5), (4,2,5), (4,3,4), (4,1,3)]
> LT26   [(0,1,3), (0,2,1), (2,3,1), (3,4,1), (4,1,1),
>         (5,0,3), (5,2,5), (5,3,5), (5,4,5), (5,1,5)]
> ```
>
> At each of the **6** (witness, split) pairs a guarded pencil-chart point of
> `G′` — `outer.chart_point`, i.e. `widened.place_pencil_general` plus the
> composite guard `repin.star_generic` plus `verify_pencil_witness` — is found
> **on the first draw** from `random.Random(20260819)`, and there:
>
> - the placement is at **target rank** on the **hard stratum**,
>   `dim R_a = 1` (`outer.stratum_at`: rank 114 at `|V| = 21`, 144 at 26);
> - **(Λ0d)** holds in both directions;
> - **(Λ0g)** is asserted in both directions (`outer.geom_checks`), so the
>   *Step 3a* geometry is confirmed on the previously-unrealized patterns;
> - **`g₁₄ ≠ 0`**, and **`d g₁₄ ≠ 0`** in 8–10 of the 46 (resp. 60) directions
>   of the FIXED-scoping chart tangent space (`dominance.build_chart`).
>
> **Class membership is certified by more than one oracle, and for the two
> `|V| = 21` witnesses `hnoRigid` is certified beyond branch granularity.**
> All three pass `kslidecomb.shape_ok` (the pebble-game `def` oracle plus
> `kslide.no_rigid_branch_union`), are 2-edge-connected, and have
> `saferes.treepack_deficiency = 0` (the matroid-union oracle). At
> `|V| = 21` the `2^|V|` partition oracle `kbare_common.exact_deficiency`
> is affordable, and over **all** `2^21` vertex subsets it reports `def = 0`,
> `f(V) = 0`, **zero** subsets with `f > 0` (full 5/6-sparsity), **zero**
> proper subsets with `f = 0`, and `max f` over proper `|W| ≥ 2` equal to
> **`−1`**. That is `hnoRigid` verified against every vertex subset, not only
> against branch unions — an independent confirmation of (Λ4)'s reduction on
> the witnesses. `LT26` (`|V| = 26`, `2^26` subsets) is **not** run through
> that oracle: its `hnoRigid` rests on the two affordable oracles plus branch
> granularity, and that is disclosed rather than smoothed over.
>
> `LT21a` / `LT21b` / `LT26` are keyed to `|V|`, **not** to `|E|`: their
> `|E|` are 24, 24, 30, and the arc's `NT<|E|>` convention is already taken by
> `NT24` and `NT30`.

**The naming of the residual population, made exact.** Since `j ≥ 2` forces
two of `x₁, x₂, x₃` to be hubs, at least one of `x₁, x₂` is a hub and at least
one of `x₂, x₃` is. Reading *Step 3a*'s (Λ0i):

> **(Λ8) (Λ0i)'s exact coverage** *(proven-informally; one line)*. `x₁` is
> (Λ0i)-free ⟺ neither `x₁` nor `x₂` is a hub, and `x₃` is free ⟺ neither
> `x₃` nor `x₂` is. So **(Λ0i) covers exactly the three patterns `(0,0,0)`,
> `(1,0,0)`, `(0,0,1)`**, and it covers **no** companion with `j ≥ 2` and none
> with `x₂` a hub. In particular the `g₁₄` clause of (Λ0f′) is **never**
> implied by (Λ0d) at a two-hub-interior companion, and *Step 3a*'s 3628/4280
> free-end discharge extends to none of them.

*(This is the general classification behind *Step 3a*'s measured sentence
"the 652 uncovered pairs are all the single hub pattern `x₂` a hub": that
sentence is true **of the swept scope**, where — see *Step Λ11* — the `j ≥ 2`
patterns were hidden by a cap. The (Λ0i)-uncovered class is five patterns, not
one.)*

### Step Λ11 — the exhaustive census, and the cap that hid three patterns

`outer.py --patterns` reported *4 of 8 patterns realized, at a widened length
bound of 8, cap 400 shapes per hub multigraph* — a coverage boundary, as it
says. **Three of the four missing patterns were inside its own scope.**

**The census, uncapped.** By (Λ4) the class predicate is a `2^{e°}` test on
`(G°, ℓ)`, and by (Λ4)'s `ℓ ≤ 5` a length bound of 5 is **exhaustive**, not a
cap. Running exactly the `--patterns` family list — θ3, θ4, `K4`,
`K4 + parallel`, and the three simple hub graphs on 5 hubs — over **all**
length assignments with a length-3 split branch (`ltwo.py --census`;
convention: one row per (hub multigraph, length assignment, split **branch**,
companion), so each length-3 branch is counted once rather than once per
orientation — the totals are **not** comparable with `--patterns`' 7002):

| leg | (shape, split) pairs with a length-4 companion | patterns |
|---|---|---|
| `theta3` | 6 | `(0,0,0)`: 6 |
| `theta4` | 0 | — |
| `K4` | 540 | `(1,0,0)`/`(0,1,0)`/`(0,0,1)`: 180 each |
| `K4+par` | 740 | `(0,0,0)`: 380; the three one-hub patterns: 120 each |
| **`V5e8`** (wheel `W₄`) | **7064** | `(1,0,0)`: 2268, `(0,1,0)`: 2280, `(0,0,1)`: 2276, **`(1,1,0)`: 80, `(0,1,1)`: 80, `(1,0,1)`: 80** |
| `V5e9` | 15066 | the three one-hub patterns: 5022 each |
| `V5e10` | 35370 | the three one-hub patterns: 11790 each |

**7 of 8 patterns are realized inside the swept family list.** Only `(1,1,1)`
is absent, and (Λ6) proves it **cannot** occur at `|V°| ≤ 5`. (Λ5) is
asserted at all **58 786** (shape, split, companion) triples of the census:
**0 failures**.

**The cap, made reproducible.** `outer.shapes_from('V5e8', 5, E0, lmax=8,
cap=400)` — the exact call `--patterns` makes on that leg — returns 400 shapes
after 19 041 length tuples with `capped = True`, and **every one of the 400
sits at split index 0 of 8**: split indices 1…7 are never reached. The witness
shapes `LT21a` / `LT21b` live on that same hub multigraph (canonical-form
match against `kslidecomb.candidate_graphs(5)`'s `|E°| = 8` graph, asserted).
So the recorded "`(1,1,0)`, `(0,1,1)`, `(1,0,1)` unrealized **in scope**" is a
**cap artifact**, not a `|V°| ≤ 5` boundary — while "`(1,1,1)` unrealized" is
the genuine boundary, now with a proof.

**Both halves of the floor are attained, exhaustively** (`ltwo.py --floor`).
At `t = 1`, (Λ6) forces the wheel and the enumeration is finite: for `j = 2`,
60 length tuples on `W₄`, of which **all 60** are class shapes carrying a
`j = 2` companion (20 per pattern); for `j = 3`, 15 tuples on `W₅`, **all 15**
class shapes carrying `(1,1,1)`. So the floors `|V| = 21` and `|V| = 26` are
attained and are exactly the (Λ6) bounds.

### Step Λ12 — what this does, and does not do, to Λ-completeness

**It does not weaken the theorem.** Λ-completeness is stated *"under (Λ0) and
the standing (T1)/(T5) hypotheses"*, and (Λ0)'s hypothesis package is
**local-frame** data: (Λ0a)–(Λ0f′) mention only the points
`{b, x₁, x₂, x₃, c, a}`, the panels `Π(b)`, `Π(c)`, `M` and `line(bc)`. Three
facts make the two-hub-interior population no harder than the rest:

1. **The local-frame machinery already quantifies over all eight patterns.**
   `lambda.py`'s `HUBPATS` is the full `2³`, and `STRATA4 + STRATA4X` is
   `8 × 3 + 7 × 2 = 38` — the recorded 38 strata of the `--span` battery.
   `(1,1,0)`, `(0,1,1)`, `(1,0,1)` and `(1,1,1)` are among them and were
   measured at `(span ω⁺, span ω⁻, deg ω⁺, deg ω⁻) = (3,3,3,2)` there.
2. **`m2/lambda0.m2` block (P6)'s bridge reaches them on the same terms as
   every other stratum.** Its construction gives a companion hub the panel
   `plane(x_{i−1}, x_i, x_{i+1})` and places far hub neighbours freely inside
   it, with `hcard` capping the count at 2. At a two-hub-interior companion an
   interior hub has **two** hub neighbours already inside the frame, hence
   **zero** far hub neighbours; `sample_local_frame`'s own
   `nfar = min(nfar, 2 − #local hub neighbours)` is exactly that case, and the
   normal space is 1-dimensional — the tightest stratum, not a degenerate one.
   No (Λ0) quantity mentions an interior hub's panel, so no new constraint
   enters the 14-coordinate slice. **The qualifier the verdict block already
   carries rides unchanged:** (P6)'s *"every stratum arises this way"* half is
   the reading of `sample_local_frame`'s model, not a computation. That
   conditional is **uniform across all eight patterns** — the two-hub
   population inherits it neither better nor worse than the six-of-eight the
   arc has been quoting.
3. **The clause the residual was really about — `g₁₄` — holds at the
   witnesses.** *Step Λ10*: `g₁₄ ≠ 0` and `d g₁₄ ≠ 0` at all six
   (witness, split) chart points.

**It does change three things, and they are not cosmetic.**

- **The residual is a live case, not a vacuity.** Before this pass "no swept
  family realizes one" left open the reading that the population is empty and
  the scope hole harmless by accident. It is non-empty, at `|V| = 21` — the
  same size as `NT21` / `NT24`, and smaller than `NT30`.
- **(Λ0i) provably never discharges it** ((Λ8)). At every two-hub-interior
  companion **both** ends are pinned, so the cheap "implied by (Λ0d)" route of
  *Step 3a* is unavailable by a theorem, not by an accident of sampling. The
  `g₁₄` clause there rests on (Λ0f′)'s generic-point proof plus the tangent
  certificate, and on nothing else.
- **The measured record now reaches the population — barely, and that is the
  honest scope.** *Step 3a*'s figures are `g₁₄ ≠ 0` at **4280/4280** exact
  (split, companion) pairs over 1357 class shapes and `d g₁₄ ≠ 0` at
  **684/684** chart points; **none** of those touch a `j ≥ 2` companion. This
  pass adds **6** (split, companion) pairs at **3** shapes and **6** guarded
  chart points. Six is a spot check, not a sweep, and must be quoted as one.

**Verdict for item (vii): ANSWERED, in the negative direction for the
"forbidden" branch.** The class does **not** forbid two or more hubs on a
length-4 companion's interior; it forbids them only below `|V| = 21` (resp.
`|V| = 26` for `(1,1,1)`), by (Λ6). *Step 3a*'s parenthetical "prove the
pattern impossible inside tight + `hnoRigid` + `hcard` (the same shape of
argument as §(K-slide) *Step 5*'s `ℓ₁ + ℓ₂ ≥ 7`)" is therefore **refuted as a
route**: that argument shape *is* (Λ5), and what it delivers is a size floor,
not an impossibility.

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
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --witness   # (Λ7): the three witnesses
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --floor     # (Λ6): the floor, attained
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --census    # (Λ5) + Step Λ11's census
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --validate  # (Λ4) vs the tracked oracle
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
| `ltwo.py --witness`: the three two-hub-interior witnesses | **3 shapes / 6 (split, companion) pairs**, patterns `(1,1,0)`, `(0,1,1)`, `(1,0,1)`, `(1,1,1)`; every one at **target rank with `dim R_a = 1`**, (Λ0d) holding, (Λ0g) asserted both ways, `g₁₄ ≠ 0` and `d g₁₄ ≠ 0` (in 9/9/8/8/10/10 of 46/46/46/46/60/60 chart tangent directions); guarded chart point found on the **first** draw at all 6 |
| `ltwo.py --witness`: independent class certification | all three: pebble `def = 0`, **`treepack_deficiency = 0`**, 2-edge-connected; the two `|V| = 21` witnesses additionally through the `2^21` **partition** oracle — `0` subsets with `f > 0`, `0` proper subsets with `f = 0`, `max f` over proper `\|W\| ≥ 2` = **`−1`** — so `hnoRigid` there is certified over **every** vertex subset, not only branch unions. `LT26` is **not** run through it (`2^26`); disclosed |
| `ltwo.py --floor`: the (Λ6) floor, attained | `j = 2`: **60/60** length tuples on the wheel `W₄` are class shapes carrying a `j = 2` companion (20 per pattern), `|V| = 21`; `j = 3`: **15/15** on `W₅`, `|V| = 26` |
| `ltwo.py --census`: the uncapped pattern census | **7 of 8** patterns realized over the `--patterns` family list at the exhaustive bound `ℓ ≤ 5`; `(1,1,0)`/`(0,1,1)`/`(1,0,1)` at **80 each, all on `V5e8`**; only `(1,1,1)` absent, and (Λ6) proves it needs `|V°| ≥ 6`. (Λ5) asserted at **58 786** triples, **0** failures |
| `ltwo.py --census`: the `--patterns` cap, reproduced | `outer.shapes_from('V5e8', 5, E0, 8, cap=400)` returns **400 shapes after 19 041 tuples, `capped = True`**, all at **split index 0 of 8** — so the `V5e8` leg of `--patterns` never reached 7 of its 8 split positions |
| `ltwo.py --validate`: (Λ4) against `shape_ok` + `triangles` + `hcard_ok` | **12 035/12 035** length tuples agree, **0** disagreements (θ3, θ4, `K4`, `K4+par` exhaustive; `V5e8` split-0 strided 1-in-8), plus the companion enumerator cross-checked against `outer.companions4`/`hub_pattern` at every eligible split of all three witnesses |

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
  space at all 684 probed points.

  > **Scope of those two figures, sharpened 2026-08-19 (*Steps Λ8–Λ12*):**
  > neither denominator contains a companion with **two or more interior
  > hubs** — that population is now known to be **non-empty** ((Λ7), three
  > witnesses at `|V| = 21`, `21`, `26`), and by (Λ8) **(Λ0i) covers none of
  > it**. Six further (split, companion) pairs at three shapes were measured
  > there, all with `g₁₄ ≠ 0` and `d g₁₄ ≠ 0` at a guarded hard-stratum chart
  > point; **six is a spot check, not a sweep**. The 4280 / 684 figures are
  > unchanged and stay true as measured.

  It is nevertheless **reachable at a good seed** of every probed habitat by
  an explicit chart move, so the clause is not decorative.
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
*Scope of that answer, corrected 2026-08-19 (*Step Λ11*).* The recorded
`--patterns` reading *"only 4 of the 8 companion hub patterns are realized
by any class shape in scope"* is **true of that run and false of the
families it ran on**: its `V5e8` leg is capped at 400 shapes of 19 041
length tuples and terminates inside split index 0 of 8. Uncapped at the
exhaustive bound `ℓ ≤ 5`, the same family list realizes **7 of 8**
patterns — `(1,1,0)`, `(0,1,1)` and `(1,0,1)` all occur on the `|V°| = 5`,
`|E°| = 8` wheel. `(1,1,1)` is genuinely out of `|V°| ≤ 5` scope, by
**(Λ6)**. The 7002-companion and 4-of-8 figures stay true **as measured**.

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

*(vii)* **ANSWERED, 2026-08-19 (*Steps Λ8–Λ12*, `ltwo.py`): a class shape
whose length-4 companion carries two or more hubs on its interior EXISTS —
at every one of the four patterns, at the exact size floor, and at a
hard-stratum target-rank chart point.** Three findings, in decreasing
strength:

- **The floor is a theorem, and it is what the sweeps were seeing.**
  (Λ5): no branch outside the split-plus-companion `C₇` joins two of its
  hubs (else cycle rank 2 at total length `≤ 12`), the sole exception being
  θ(3,4,5). (Λ6): hence `j` interior hubs force `n° ≥ j + 3` and
  `c° ≥ ⌈(2j+7)/3⌉` — `|V| ≥ 21` at `j = 2`, `|V| ≥ 26` at `j = 3` — and at
  one non-frame hub the hub multigraph is the **wheel**.
- **The population is non-empty and reaches the floor.** (Λ7): `LT21a`
  (`(1,1,0)`/`(0,1,1)`), `LT21b` (`(1,0,1)`), `LT26` (`(1,1,1)`), all
  class-certified by the tracked oracles — and at `|V| = 21` by the `2^|V|`
  partition oracle, so `hnoRigid` there holds over **every** vertex subset,
  not only branch unions — each with a guarded chart point at
  target rank with `dim R_a = 1`, (Λ0d) and (Λ0g) holding, `g₁₄ ≠ 0` and
  `d g₁₄ ≠ 0`. **Λ-completeness stands as written on them** — the (Λ0)
  package is local-frame data, `lambda.py`'s 38 strata already span all
  eight hub patterns, and `lambda0.m2` (P6)'s bridge covers a companion hub
  with zero far hub neighbours by construction.
- **But (Λ0i) is provably unavailable there** ((Λ8)): both companion ends
  are pinned at every `j ≥ 2` pattern, so the `g₁₄` clause is carried by
  (Λ0f′)'s generic-point proof and a **six-point** spot check, not by the
  3628/4280 free-end discharge and not by the 4280/684 sweeps.

**The impossibility route named in the old item (vii) is refuted**: "prove
the pattern impossible inside tight + `hnoRigid` + `hcard`" is exactly the
argument (Λ5) runs, and what it yields is a size floor, not an
impossibility. **What is still open** is the *uniform* statement — whether
`g₁₄ ≠ 0` (equivalently, whether `{g₁₄ = 0}` stays a proper hypersurface)
at **every** two-hub-interior class shape's chart, rather than at the three
exhibited. That is the residual form of item (vii), and it is now a
statement about a **named, non-empty, floor-classified** family: at `t = 1`
the wheels `W_{j+2}` with `Σℓ = 6(j+2)`, exhaustively enumerated in
*Step Λ11*; at `t ≥ 2` unenumerated.

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
residual — since direction G (Steps G8–G13) — is **(GR-10)** alone,
geometry-free ((GR-9) discharging the geometry; (GR-4) refuted-as-stated and
repaired off the critical path).*
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

**Pointer (2026-08-19, direction OCON).** Since §(K-out) *Steps O13–O18*, (OUT)'s own residue
(OC-8) sits on the same object class as (ANH-R1) — one contraction tower apart,
`H/P = (H/X)/(b ∼ v*)` — so a rigidity statement at `H/X` is one weld away from a rigidity
statement at `H/P`. No status moves on either side.

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

---

**Continuation (2026-08-06, second fan-out direction R) — pencil-rigidity of the contracted framework: (ANH-R1) is one-point-decidable per shape and discharged at every probed triple, its bad locus is INHABITED by exact rational points of the honest chart, and the "easier or merely smaller" question is settled as scoped.**

Answering the second fan-out's **direction R** (`notes/Pencil-fanout.md`
§"Second fan-out" → Direction R). Read against *Steps A4/A7/A8* above
((ANH-4), (ANH-7), (ANH-R1)), §(K-out) *Steps O3/O6* ((OC-3)/(OC-4), whose
shape *Step A12* mirrors on the τ side), and `Pencil-strategy.md` §§2.3/4.6
(the rank-lower-bound asymmetry and the weak-map lead). Driver:
`notes/scripts/w4/shrink.py` (imports `annih` read-only).

**Status, stated before the mathematics.**

- **(ANH-R1) stays OPEN as a class statement, and no gap-map status moves.**
  What moves is its *epistemic profile*, in both directions at once:
  per shape it is now **witness-decidable by one exact rank computation and
  discharged at every probed triple** ((ANH-9) + (ANH-10), 26/26 guarded
  seeds, 58/58 length-5-branch sites); pointwise it is now **refuted** —
  (ANH-12) exhibits exact rational legal chart points, most of them
  guard-accepted at target rank on the hard stratum, where `H/P − β` is
  dependent and the support strictly drops.
- **The pinned census probe (`notes/Phase39.md` (g)) is run and is a clean
  negative at random guarded seeds** — no class seed with
  `supp_pen ⊊ supp_gen` was found — **and a clean positive at constructed
  ones**: the same strict drop the census hunts is *reached deliberately*, at
  six class shapes, by two legal single-vertex chart moves, with every
  habitat predicate green. Weak-map specialization **does bite** on the
  pencil chart; it just does not bite at a *generic* point of any probed
  shape.
- **The sharp form of the "easier or merely smaller" question is answered:
  the pencil pin does NOT respect Tay's matroid pointwise — only
  generically, per shape.** So (ANH-R1) can never be delivered by a
  counting, matroid, or placement-blind argument (the τ-side analogue of
  §(K-out) (OC-3)), and the remaining geometric half has exactly the profile
  of §(K-out) (OC-8): a whole-chart genericity statement. That is
  `Pencil-strategy.md` §2.3's wall, met from inside the relocation itself —
  see *Step A13* for what this does to §2.3's recorded stop-rule prediction.

### Step A10 — (ANH-9): the weak-map formulation, and one-point decidability

Fix a class (shape, split, length-4 companion) triple and write `M_gen` for
the generic Tay matroid on `E(H/P)` — a **circuit** by (ANH-4) — and
`M_pen(p)` for the linear matroid the hinge lines realize at a legal pencil
chart point `p`.

> **(ANH-9)** *(proven-informally)*
> (i) For every chart point `p`, `M_pen(p)` is a weak-map image of `M_gen`
> (rank of every subset can only drop under specialization).
> (ii) The pencil chart is the image of an irreducible rational
> parametrization (hub points, panel normals, panel-constrained interiors —
> the same standing fact §(K-dom) *(D4)* already consumes), so **"the matroid
> at the generic pencil placement" `M_pen^gen` is well-defined**, and it is
> the weak-map-maximal one among the `M_pen(p)`.
> (iii) (ANH-R1) at the triple ⟺ `E(H/P) − β` is independent in `M_pen^gen`
> ⟺ **some** chart point has `H/P − β` independent ⟺ **some rational** chart
> point does (ℚ-density of a nonempty open in the parameter affine space).
> So (ANH-R1) is **decidable per triple by one exact rank computation at one
> rational point**.
> (iv) At `k = 4`: `M_pen^gen = M_gen` ⟺ `supp(τ) = E(H/P)` at one guarded
> generic seed ⟺ `τ_β ≠ 0` for **every** branch `β` (the support is a union
> of branches, by (ANH-6)'s branch constancy).

*Proof.* (i) is rank lower-semicontinuity: realized rank ≤ generic rank,
subset by subset. (ii) irreducibility of the image of an irreducible variety;
the matroid at the generic point is the common matroid on a dense open where
all the finitely many subset-ranks are simultaneously maximal over the chart.
(iii) forward: generic point; backward: the rank of `H/P − β`'s matrix is a
lower-semicontinuous function of the parameters, so full rank at one point
forces full rank on a dense open, hence at the generic point; a rational
witness exists because a nonempty Zariski-open subset of affine space over ℚ
has rational points. (iv) `M_gen` is a circuit, so `M_pen^gen = M_gen` iff
every single-edge deletion stays independent generically, iff the (unique,
`dim = k − 3 = 1`) generic pencil stress has full support. ∎

Two immediate consequences. First, the *Shared dictionary*-level reading:
**the weak-map / specialization-stability lead of `Pencil-strategy.md` §4.6
now has its precise statement** — *(ANH-R1) class-uniformly = the
specialization `M_gen ⇝ M_pen^gen` restricts to the identity weak map on the
co-branch family, at every `k = 4` class contraction* — which is what that
subsection said it could not supply. Second, **θ(3,4,5) is the trivial
case, proven at every chart point**: its `H/P` is the bare 5-cycle
(*Step A4*'s incidental), so `H/P − β` is empty and (ANH-R1) holds
unconditionally there (asserted in `--validate`).

### Step A11 — (ANH-10): the census — the pinned probe, run

> **(ANH-10)** *(measured; guard-gated, so quotable as a rate)* Over a pinned
> pool of **26** class `k = 4` (shape, split) pairs — the 4 named
> length-4-companion habitats plus **22 swept shapes nobody hand-picked**
> (2 theta3, 4 `K4`, 4 `K4+par`, 4 `V5e8`, 4 `V5e9`, 4 `V5e10`; the theta4
> family is empty of class shapes, matching *Step A6*'s census) — one
> `dominance.base_seed`-guarded seed each (composite guard
> `repin.star_generic`), all 26 on the hard stratum (`dim R_a = 1`):
>
> - `dim S_pen = 1` (H/P pencil-rigid) at **26/26**;
> - `supp_pen = E(H/P)` — every branch stressed — at **26/26**: **no strict
>   support drop at any guarded seed**;
> - **58** length-5-branch sites, `τ_β ≠ 0` at every one — so by (ANH-9)(iii)
>   **(ANH-R1) is discharged at the generic point of every pooled triple**;
> - an independent cross-check at every seed: the stress space of `H/P − β`
>   **rebuilt from scratch on the reduced edge list** is 0-dimensional exactly
>   when `τ_β ≠ 0` (both directions, every length-5 branch plus a shorter
>   spot-check per seed);
> - the generic side re-asserted per shape (`gen_stress_dim(H/P) = 1`,
>   Lee–Streinu pebble game).
>
> The **off-class control** θ4(3,4,5,6) (`hnoRigid` FAILS there) is the
> positive control: the machinery **finds** its zero branch — the length-6
> branch, whose screw is forced to zero by six independent lines, (ANH-6)'s
> mechanism — so "no drop found" is not an artifact of the hunt being unable
> to see one.

This extends *Step A4*'s realized-side 14/14 to 26/26 over a pool whose swept
majority was never hand-picked, and it upgrades each pointwise `τ_β ≠ 0`
into a per-shape generic-point discharge via (ANH-9). It does **not** touch
class uniformity: 26 shapes is evidence, not an argument — exactly
`Pencil-strategy.md` §2.3's "every positive is per-shape".

### Step A12 — (ANH-11)/(ANH-12): the bad locus is inhabited, exactly

The census asks about generic seeds; (ANH-R1) as *Step A8* poses it is a
generic-point statement. What no prior step settled is whether the **bad
locus** `{p : H/P − β dependent at p}` even meets the honest (nondegenerate,
guard-accepted) part of the chart. It does — and not merely over `K̄` or at
sampler-degenerate boundary points, but at exact rational points satisfying
**every predicate the arc's habitat carries**.

> **(ANH-11)** *(proven)* — **the common-transversal mechanism.** Let `p` be
> a legal pencil chart point, `Z` a `c`-cycle of `H/P` edge-disjoint from a
> branch `β`, and `L` a line of `P³` such that **every hinge line of `Z`
> meets `L`**. Then the Klein extensor `C(L)` propagates to a self-stress of
> `H/P` at `p` supported on `Z` (together with the compensating flow along
> the **companion** edges when `Z` passes through the welded body `X` —
> allowed exactly because the weld demands no transmissibility there),
> vanishing on `β`. In particular `E(H/P) − β` — **independent in `M_gen`**
> by (ANH-4) — is **dependent in `M_pen(p)`**; and `Z` itself, a
> Tay-**isostatic** `c = 6`-cycle (*Shared dictionary* (R3): `def(C₆) = 0`),
> goes dependent.
>
> *Proof.* Lines meeting `L` are exactly the **special linear complex** of
> axis `L`: `B(C, C(L)) = 0` (the arc already uses "hinge lines in a linear
> line complex ⟹ a self-stress per cycle" at §(K-σ) *Step σ6* /
> `Pencil-strategy.md` §2.4's null-correlation exhibit; this is its localized,
> single-cycle form). Put `τ_e = ±C(L)` along a traversal of `Z`, `0` on all
> other far edges, and the telescoping partial sums on the companion edges
> between `Z`'s two attachment vertices when `X ∈ Z`. Equilibrium: at a far
> cycle body the two incident cycle screws cancel; at a companion vertex the
> path flow balances by construction; elsewhere everything is zero.
> Transmissibility off `P`: `B(±C(L), C_e) = 0` for `e ∈ Z` since `C_e` meets
> `L`, and trivially off `Z`. `τ ≠ 0`, `τ|_β = 0`, and its restriction to
> `E − β` is a self-stress of `H/P − β`. ∎

> **(ANH-12)** *(proven at witnesses — exact, existence claims, so exempt
> from rate-gating; guard status reported anyway)* — **reachability.**
> Anchor `L = line(pt(u₀), pt(u₃))` at two opposite real bodies of `Z`. The
> four `Z`-edges incident to `u₀` or `u₃` meet `L` automatically; each of the
> remaining `c − 4` incidences is `[u₀, u₃, q, x] = 0` — **affine-linear in
> one movable far vertex `x`** (a plane condition), solvable exactly inside
> `x`'s legal move space (the intersection of its hub-neighbours' panels).
> So the bad point has **rational coordinates** and is reached from a guarded
> seed by `c − 4` legal single-vertex pencil-chart moves. Run at the 4 named
> habitats + the 6 swept probes (`shrink.py --bad`, 92 s):
>
> - **9/9 shapes constructed** (θ(3,4,5) is the proven trivial case), **all 9
>   guard-accepted** (`repin.star_generic`), `verify_pencil_witness` green at
>   every witness, and **8/9 at target rank on the hard stratum
>   (`dim R_a = 1`)**;
> - at the **six swept `K4`-family shapes**: `β` of **length 5** (count 0 —
>   the exact (ANH-R1) object), 6-cycles, and at the witness
>   `dim S(H/P) = 1` — **`H/P` still pencil-rigid** — with the unique stress
>   supported on the 6-cycle: **`supp` drops `11 → 6`**. This is *verbatim*
>   the strict `supp_pen ⊊ supp_gen` drop the census probe hunts, exhibited
>   at a guard-accepted, target-rank, hard-stratum legal chart point;
> - NT24 and NT30 (no length-5 branch in `H/P`): 7-cycles, `β` of length 4
>   (the matroid-drop form — `E − β` independent-with-slack generically),
>   same full predicate set, `supp` drops `17 → 7` and `23 → 7` with
>   `dim S = 1`;
> - NT21: an 8-cycle witness, guard-accepted but off target rank
>   (`dim S = 2` there); the dependency of `H/P − β` is still certified.
>
> Every witness is certified three ways: the constructed stress satisfies
> the stress system **equation by equation** (equilibrium body-by-body,
> transmissibility edge-by-edge — no solve), it lies in the independently
> **solved** stress space, and the reduced space of `H/P − β` is rebuilt from
> scratch and is nonzero. One witness in full (the others print from the
> driver): `swept:K4 (3,1,1,3,5,5) split 0/v100`, seed 1, anchors
> `(109, 3)`, moved `108 → (-135149673/59575628, 60222846/74469535,
> -217797/146738)`, `110 → (14145707/2039430, 7, -4/5)`.

**Consequences, and their exact strength.** (a) **(ANH-R1)'s bad locus meets
the honest chart — indeed the guard-accepted target-rank hard stratum — at
every probed shape**, so no counting, matroid, or placement-blind argument
can ever deliver (ANH-R1); any proof must be a genericity argument on the
whole-graph chart. This is the τ-side analogue of §(K-out) (OC-3), reached
by *construction* rather than by (OC-3)'s dimension count, and it lands
**inside** the stratum where (ANH-7)'s consumer runs — the analogue of
§(K-out) (OC-4)'s silent point. (b) **The pencil pin does not respect Tay's
matroid pointwise**: a Tay-isostatic set goes dependent at a legal
nondegenerate pencil placement. The pin respects the matroid only
*generically, per shape* — (ANH-10). (c) Nothing here refutes (ANH-R1) or
(ANH-7): the witnesses are deliberately special points, and the census says
generic guarded seeds show no drop.

**Combinatorial availability of the 6-cycle form** (`--comb`, 12 s,
placement-free): over the 4296-triple pool of *Step A9*, `3812 + 8 trivial
θ(3,4,5) = 3820` triples carry a length-5 branch (reconciling exactly with
*Step A9*'s 3820 — the bare-cycle `H/P` counts as one cyclic length-5 branch
there and as trivial here), and the 6-cycle construction is combinatorially
available at **2066** of the 3812 (edge-disjoint 6-cycle + real anchors + a
movable vertex per condition). `--bad` shows the reach is wider in practice:
the 7/8-cycle forms cover NT21/NT24/NT30, whose `H/P` has girth 7, 7, 7.

### Step A13 — the verdict: "easier or merely smaller", settled as scoped; and §2.3's prediction, checked

*Step A8* left one question open in those words: *is (ANH-R1) genuinely
easier than its parent, or merely smaller?* This pass answers the parts of
it that are answerable without closing the gap itself:

1. **The pointwise escape hatch is closed.** If the relocation had been
   "easier" in the strong sense — the smaller graph's independence provable
   pointwise from Tay's min-max — (ANH-12) forbids it: the matroid statement
   is false at legal nondegenerate chart points of every probed shape.
   What remains is a generic-point rank lower bound at a pencil placement of
   a contraction of `H` — **exactly §(K-out) (OC-8)'s profile**, now with the
   nonemptiness of the bad locus *witnessed inside the habitat stratum*
   rather than inferred.
2. **`Pencil-strategy.md` §2.3's recorded prediction is checked, not
   admired.** The prediction said a third independent route should terminate
   on a rank lower bound at a pencil placement of a contraction of `H`, and
   that if it does, "stop looking for routes: the productive target becomes
   the wall itself". This pass is not a third route — it attacked one of the
   two named residuals directly — and its outcome *sharpens the wall's
   description*: the wall is precisely **generic-point** rank lower bounds
   (pointwise ones are now refuted objects), its bad loci are inhabited by
   rational points of the honest chart, and its per-shape instances are
   one-point-decidable. The stop-rule's premise is therefore *strengthened*:
   there is no cheaper reformulation left on this side.
3. **What a uniform route now needs, named exactly.** By (ANH-9)(iii),
   (ANH-R1) class-uniformly ⟺ a **class-uniform recipe producing, per
   triple, one legal chart point with `H/P − β` independent**. That is the
   same missing technology as §(K-grid)'s residual — since direction G,
   **(GR-10)** — a uniform constructed-witness generator for tight class
   shapes at the Tay target, with chart-image membership already proven there
   ((GR-5)) — so **directions T and R converge on one technology**: uniform
   constructed chart witnesses of rank attainment. If §(K-grid)'s recipe
   closes, the natural follow-up is whether a grid/counting recipe evaluates
   on the *mixed* contracted object `H/P − β` (the welded body `X` is not a
   pencil body — §(K-ind) *Step I6* — so this is strictly outside (GR-5)'s
   current scope; recorded as a lead, not a claim).
4. **The one symbolically tractable per-shape upgrade** (parallel to
   `Pencil-strategy.md` §5.3): by White–Whiteley (WW87 Prop. 2.6, verified in
   `notes/Phase39.md` *Citations*), `H/P − β` at `k = 4` is count-0, so
   (ANH-R1) per shape is "`C(H/P − β)` (the pure condition, a bracket
   polynomial) does not vanish identically on the chart" — an M2-checkable
   **identity over the function field** per shape, which would upgrade
   (ANH-10)'s per-seed witnesses to per-shape symbolic proofs. Note this
   does *not* collide with §(K-pure) *P5*'s refutation of direction C: the
   target here is a rank statement, which is exactly what a pure condition
   sees; it was the *pitch* that the pure condition could not see.

So the honest one-line answer to *Step A8*'s question: **merely smaller in
difficulty class — the geometric half is the same wall — with two genuine
structural gains ((ANH-4)'s proven combinatorial half, and (ANH-9)'s
one-point decidability per shape) and one now-proven loss (pointwise
matroid-respect fails, (ANH-12)).**

### Verification (Steps A10–A13)

`notes/scripts/w4/shrink.py` (**new with this continuation**; exact ℚ, stdlib
only; imports `annih` and, through it / beside it, only catalogued §1
primitives — `annih`'s `prepared` / `stress_space` / `contracted_edges` /
`hp_branches` / `branch_lengths` / `branch_screw` / `girth` /
`gen_stress_dim` / `habitats4` / `control_shapes` / `swept_probes` /
`path_edges` / `single_vertex_dirs`, `outer`'s `split_data` / `companions4` /
`named_inventory` / `sweep_shapes` / `eligible_splits` / `stratum_at`,
`repin`'s `span_basis` / `in_span` / `star_generic`, `pitch`'s `klein` /
`det4`, `kbare_common.verify_pencil_witness`, `dominance.cycle_data`,
`exactcore`'s `rank` / `nullspace` / `wedge2` / `hat` / `dot` / `neighbors`;
it reimplements nothing and adds **no rng** — every sampled configuration
arrives through `dominance.base_seed`'s composite guard). Run from the repo
root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --census    # (ANH-10)   ~106 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --bad       # (ANH-11/12) ~92 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --comb      # availability ~12 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/shrink.py --validate  # machinery    ~7 s
```

All four modes verified **byte-identical** under `PYTHONHASHSEED=0` and
`999`, exit 0. Adding this driver modified no tracked script, so the
figure-invariance gate discharges on the `git diff --name-only -- '*.py'
'*.m2'` check alone (`notes/scripts/README.md`, first bullet).

Per mode, what is asserted: `--census` — per seed: `gen_stress_dim(H/P) = 1`
(pebble game), `dim S_pen` from the full solve, branch screws via
`branch_screw` (constancy asserted), and the reduced-rebuild equivalence
`τ_β = 0 ⟺ dim S(H/P − β) ≥ 1` in both directions at every length-5 branch
plus a shorter spot-check; the off-class control must exhibit its drop.
`--bad` — per witness: every cycle line's Klein pairing against `C(L)` is
zero; `verify_pencil_witness` green; the constructed stress satisfies
equilibrium body-by-body and transmissibility edge-by-edge, lies in the
independently solved stress space, and `H/P − β`'s reduced space is nonzero;
guard and stratum reported per witness, never assumed. `--comb` — the
combinatorial precondition per triple, placement-free. `--validate` — the
contraction bookkeeping against `annih.contracted_edges`, the trivial
θ(3,4,5) case, reproduction of *Step A4*'s `--supp` verdicts at 2 habitats,
exactness of the affine plane-solver, the special-linear-complex fact on
synthetic data (rank 5, co-kernel `⟨C(L)⟩`), and the cycle finder against
`girth`.

**Figures.**

| figure | value |
|---|---|
| `--census` pool | **26** class `k = 4` (shape, split) pairs (4 named + 22 swept over 6 families; theta4 empty of class shapes), 1 guarded seed each, **26/26 hard stratum** |
| `--census`: `dim S_pen` | **1 at 26/26** (H/P pencil-rigid) |
| `--census`: `supp_pen = E(H/P)` | **26/26** — no strict drop at any guarded seed |
| `--census`: length-5-branch sites | **58**, `τ_β ≠ 0` at every one |
| `--census`: off-class control | drop **found** (the length-6 branch), 1/1 |
| `--bad` witnesses | **9/9 shapes** (+ θ(3,4,5) trivial), **9/9 guard-accepted**, **8/9 target-rank hard-stratum** |
| `--bad`: (ANH-R1)-exact witnesses | **6** (β length 5, count 0; all six: `dim S = 1`, supp drop **11 → 6**) |
| `--bad`: matroid-drop witnesses | NT24 **17 → 7**, NT30 **23 → 7** (`dim S = 1`); NT21 8-cycle, off target rank, `dim S = 2` |
| `--comb` | 4296 triples; `3812 (+8 trivial) = 3820` with a length-5 branch (matches *Step A9*); 6-cycle form available at **2066/3812** |
| determinism | all four modes byte-identical across two `PYTHONHASHSEED` values |

**Which driver tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (ANH-9)(i)/(ii) | — | **none; proof-level** (semicontinuity + parametrized chart). Named as such, not asserted more strongly; its (iii) consumes the census witnesses |
| (ANH-9)(iii)/(iv) per shape | `--census` | the one-point witnesses themselves: `τ_β ≠ 0` at 58/58 sites, full support at 26/26, with the reduced-rebuild equivalence asserted both ways |
| (ANH-10) | `--census` | the sentence is the aggregate; guard-gated via `dominance.base_seed`; the positive control proves the hunt can see a drop |
| (ANH-11) | `--bad`, `--validate` | per witness, the constructed stress is verified **equation by equation** (no solve) *and* against the independent full solve; the synthetic special-complex leg (`rank 5`, co-kernel `⟨C(L)⟩`) |
| (ANH-12) | `--bad` | the witnesses: rationality (exact coordinates printed), legality (`verify_pencil_witness`), guard, stratum, and the reduced dependency, per shape |
| "the drop the census hunts is exhibited" | `--bad` | `dim S = 1` **and** `supp` strictly smaller, printed and asserted at the six exact witnesses |
| the 6-cycle form's availability | `--comb` | the combinatorial precondition, per triple; explicitly **not** a success rate — the geometric halves are measured only in `--bad` |
| **(ANH-R1)** | — | **still none, and still the point**: what no driver can test is class uniformity; the census discharges the generic point per probed shape, the construction bounds what any future argument may assume |

### Confidence verdict (Steps A10–A13)

- **(ANH-9): proven-informally** (semicontinuity, chart irreducibility as
  already consumed by §(K-dom) *(D4)*, ℚ-density); its per-shape consequence
  is exercised 26 times by the census.
- **(ANH-10): measured**, guard-gated, 26/26 + 58/58 with an off-class
  positive control; a rate over a pinned pool, quotable as such.
- **(ANH-11): proven** (five lines; classical special-linear-complex
  geometry, the localized form of the arc's §(K-σ) *Step σ6* device), with
  every witness certified equation-by-equation.
- **(ANH-12): proven at 9 witnesses** (exact rational points; existence
  claims). The class-wide statement "the bad locus is inhabited at every
  class shape" is **measured-plus-mechanism, not proven** — the 6-cycle
  form's combinatorial precondition holds at 2066/3812 triples and the
  7/8-cycle forms covered every probed shape, but no proof is offered that
  some workable cycle/labeling exists at *every* shape.
- **(ANH-R1): OPEN**, unchanged in status, sharpened in profile: per-shape
  one-point-decidable and discharged at every probed triple; pointwise
  refuted; class-uniformly exactly as hard as a uniform
  constructed-witness recipe ((ANH-9)(iii)), the technology §(K-grid)'s
  residual (since direction G: (GR-10)) is building for the tight stratum.
- **Class uniformity is untouched. No gap-map status moves.** The (K-wit) /
  (K-ann) rows gain the (ANH-12) caveat (no placement-blind route to
  (ANH-R1)) and the (ANH-9) reduction, not a status change.

### What would change this (Steps A10–A13)

*(i)* **A guarded random seed with a zero branch at a class shape** — the
census extended (more swept families, more seeds per pair) finding
`supp_pen ⊊ supp_gen` generically would kill (ANH-7) as stated at that shape
and be the sharpest new obstruction since §(K-pure) *P6*.
*(ii)* **A class-uniform independent-point recipe** ((ANH-9)(iii)'s right
side) — closes (ANH-R1), hence via §(K-Λ)'s Λ-completeness the whole
length-4-companion stratum. The concrete candidate to watch is §(K-grid)'s
machinery, if its (GR-6)-style colouring existence can be made to evaluate
on the mixed contracted object.
*(iii)* **A per-shape M2 identity** `C(H/P − β) ≢ 0` over the function field
(*Step A13* item 4) — **RUN 2026-08-06 (direction Q, Steps A14–A17), and the
"upgrade" premise was WRONG**: (ANH-9)(iii) already makes each census row a
proof at its triple, so the identity is the pointwise restatement, not an
upgrade ((ANH-16)(i)); item 4 is **struck as an upgrade route**. What survives
is **(ANH-14)** — the whole bare-cycle stratum governed by ONE universal
irreducible degree-12 polynomial — and no shape was refuted anywhere.
*(iv)* **A shape where no cycle/labeling makes the construction work *and*
no other mechanism inhabits the bad locus** would weaken (ANH-12)'s
class-wide reading (currently measured at 9/9 probed); it would not affect
(ANH-11) or the consequences at the probed shapes.
*(v)* **An error in the witness certification** — guarded by the
equation-by-equation check being solve-free and independent of the solver
whose output it is compared against, and by `verify_pencil_witness` /
`star_generic` / `stratum_at` being imported from their canonical homes, not
reimplemented.


**Continuation (2026-08-06, third fan-out direction Q) — (ANH-R1) as a PURE CONDITION: a branch-core normal form and an exact size law, one UNIVERSAL irreducible degree-12 bracket polynomial governing the whole bare-cycle stratum, a bad locus strictly larger than (ANH-11)'s, and the verdict that the M2 identity is the *pointwise restatement* of (ANH-R1) rather than an upgrade of it.**

Answering `notes/Pencil-fanout.md` §"Third fan-out" → Direction Q, i.e. *Step A13*
item 4 and *What would change this (Steps A10–A13)* item (iii). Read against
*Steps A4/A6/A7* ((ANH-4), (ANH-6), (ANH-7)) and *Steps A10–A13* ((ANH-9)'s
one-point decidability, (ANH-10)'s census, (ANH-11)/(ANH-12)'s inhabited bad
locus); against §(K-pure) *Step P0*, whose reading of White–Whiteley's pure
condition this pass re-uses **verbatim on the τ side**; against §(K-out)
*Step O12* ((OC-16)'s chart-to-frame dominance residue, which turns out to be
this section's residue too); and against `Pencil-strategy.md` §§5.2/5.3/5.4.
Drivers: `notes/scripts/w4/anhr1.py` (imports `annih` / `shrink` / `outer`
read-only) and `notes/scripts/m2/anhr1.m2`.

**Status, stated before the mathematics.**

- **No shape is refuted, and the experiment's *positive* half turns out to be
  logically redundant.** The dispatch's premise — *"a positive at a shape
  upgrades that shape's (ANH-10) census row from witness to proof"* — is
  **REFUTED**, and by this section's own predecessor: *Step A10*'s (ANH-9)(iii)
  already makes one exact rational chart point with `H/P − β` independent a
  **proof** of (ANH-R1) at that triple, by rank lower-semicontinuity on an
  irreducible chart. (ANH-10)'s 26/26 rows are therefore already proofs, not
  witnesses awaiting one. This is §(K-pure) *Step P0*'s point transposed to the
  τ side: WW87 offers two routes to `C ≢ 0`, **Cor. 2.7 pointwise** — which is
  the restatement, and which the exact-ℚ harness already executes in seconds —
  and **Thm 2.18 combinatorially**, which (ANH-11)/(ANH-12) have already closed
  off here (no counting / matroid route). An M2 identity per shape is Cor. 2.7
  again, at 10²–10³× the cost.
- **What the symbolic layer does buy is structure, and it is worth having.**
  Three results the sampling harness structurally cannot reach, all
  class-uniform over a named stratum: **(ANH-13)** the reduced object's
  branch-core normal form and the exact size law `deg C(H/P − β) = 12(c(G) − 2)`;
  **(ANH-14)** at the bare-cycle stratum (29.6 % of length-5-branch sites) the
  pure condition is ONE polynomial, the same at every shape of the stratum,
  **irreducible** of degree 12 — so (ANH-R1) there is *exactly* the statement
  that the shape's pencil chart does not lie inside one fixed hypersurface, a
  chart-to-frame dominance question with **no rank condition left**, the precise
  analogue of §(K-out) (OC-16); **(ANH-15)** the bad locus **strictly contains**
  (ANH-11)'s common-transversal locus.
- **The one-bracket recipe does NOT extend.** (ANH-14)'s irreducibility is a
  *negative* with teeth: `C(H/P − β)` admits no factorization into smaller
  bracket conditions, so there is no (ANH-7)-style "one named move, one 4-point
  bracket" certificate for (ANH-R1) itself, and no §(K-Λ) (Λ1)-style
  "product of two linear forms" either. The arc's two closed forms both came
  from *reducible* objects; this one is irreducible.
- **The M2 reach is measured and it stops at the bare-cycle stratum.** Generic
  point, all coordinates indeterminate: degree 12 in 24 point indeterminates
  **finishes at 578 s**; the next stratum up (a θ core, 12 free points, 48
  indeterminates) **does not finish at 600 s**. Together with §(K-Λ)'s recorded
  kill (degree 52 in 28, no finish) the layer's practical boundary is now
  bracketed from both sides.
- **Class uniformity is untouched. No gap-map *status* moves.** The (K-ann) row
  gains (ANH-13)–(ANH-16) as a sharpening of (ANH-R1)'s profile — the residue is
  now named identically to §(K-out)'s — not as a status change.

**The answer to the dispatch's question, per stratum.** (`c′ = c(G) − 2`; the
site counts are over the 4296-triple pool's 6426 length-5-branch sites. "Shape"
here means (shape, split, companion, β) site — the object depends on all four.)

| stratum | sites | the object | is `C ≢ 0` ? |
|---|---|---|---|
| `c′ = 0` (θ(3,4,5)) | 8 | empty (one body) | **TRUE at every chart point** — *Step A10*, unconditional |
| `c′ = 1`, `n = 0` | **1904** | ONE universal irreducible degree-12 bracket polynomial, the 7-point open chain | **TRUE**, proven *uniformly for the whole stratum* over the function field; (ANH-R1) at a shape then needs only chart-to-frame dominance, and needs nothing at a shape (ANH-10) probes |
| `n = 1` | 134 | a **product** of `c′` bare-cycle conditions | **TRUE**, by the same computation applied factorwise |
| `n = 2` (θ core) | 3812 | an order-6 branch-screw determinant; at the θ(5,5,2) length profile it collapses further to a **2 × 2** in two pinned screws (`κ_1, κ_2`, degree-10 brackets) | **TRUE at an exact witness** (the θ(5,5,2) profile, moment-curve points); the generic-point symbolic form is **M2-INFEASIBLE** (600 s kill) and the local frames are panel-constrained, so no universality |
| `n = 3` | 568 | order-12 branch-screw determinant | **not attempted** — infeasible by the same measurement |
| **refuted anywhere** | **0** | — | no stratum, no shape |

### Standing notation (on top of *Steps A1–A13*)

`β` a length-5 branch of `H/P`; **`H/P − β`** means: delete `β`'s five edges
**and its four interior bodies** (its two end bodies are nodes of `H/P` and
survive; an isolated body would make the framework disconnected, hence
dependent for a reason that has nothing to do with (ANH-R1)). `c(·)` is cycle
rank; `c' := c(H/P − β)`. `C(·)` is the White–Whiteley pure condition
(WW87 Prop. 2.6; the citation is verified in `notes/Phase39.md` *Citations*,
`.refs` copy, 2026-08-04). Nodes of a body-hinge multigraph are its bodies of
degree ≠ 2; `n` = their number, `m` = the number of branches.

### Step A14 — (ANH-13): the branch-core normal form, and the exact size law

> **(ANH-13)** *(proven; driver-asserted)* At a `k = 4` class (shape, split,
> length-4 companion) triple with a length-5 branch `β` of `H/P`:
>
> (i) **Size law.** `H/P − β` is connected with
> `|V′| = 5c′ + 1`, `|E′| = 6c′`, and
>
>  `c′ = c(H/P) − 1 = c(G) − 2`.
>
> (ii) **Normal form.** By (ANH-6)'s branch constancy a self-stress is one
> screw per branch, so the `5|E′| × 6(|V′|−1)` rigidity matrix reduces to the
> **square `6m × 6m` branch-screw matrix**: `ℓ_j` transmissibility rows
> `B(S_j, C_e) = 0` per branch, and `6(n−1)` equilibrium rows
> `Σ_{j at u} ±S_j = 0`. Its determinant **is** `C(H/P − β)`, up to a nonzero
> scalar.
>
> (iii) **Degree.** `deg C(H/P − β) = 2|E′| = 12c′ = 12(c(G) − 2)` in the point
> coordinates — so the pure condition's size **grows linearly with the shape**,
> and the object is bounded exactly on the finite part of the class.
>
> (iv) **Bare cycle.** `c′ = 1` ⟺ `c(G) = 3`, and — since every body of
> `H/P − β` has degree `≥ 2` unless `β` is a *loop* at a degree-3 node — a
> connected cycle-rank-1 object of min degree 2 is a **bare cycle**, `n = 0`
> (measured: `n = 0` at exactly the 1904 + 8 sites with `c′ ≤ 1`). There
> `C(H/P − β) = det[C_0; …; C_5]`, the 6 × 6 Plücker determinant of the cycle's
> hinge lines. `c′ = 0` ⟺ `H/P − β` is a single body — the trivial case
> *Step A10* already settles at every chart point (`G = θ(3,4,5)`).

*Proof.* (i) `G` tight gives `(|V|,|E|) = (5c+1, 6c)` (§(K-ind) *(I1)*);
`H = G − v − a` drops 2 vertices and 3 edges, so `c(H) = c − 1`; contracting the
companion path changes no cycle rank, so `c(H/P) = c − 1`; deleting a branch of
a connected graph, with its interiors, drops the cycle rank by exactly 1. Then
`|E′| = |E(H/P)| − 5 = (6c − 7) − 5 = 6(c−2)` and `|V′| = 5(c−1) − 4 = 5(c−2)+1`.
Connectivity: `H/P − β` disconnected would put its rank below `5|E′|`, so
(ANH-4)'s generic independence of `E(H/P) − β` already forbids it.

(ii) A self-stress is a screw circulation with `B(τ_e, C_e) = 0` off the
companion (*Step A1*); equilibrium at a 2-valent body makes `τ` constant along
a branch ((ANH-6)), so the unknowns are `m` screws and the constraints are the
`Σ_j ℓ_j = |E′|` transmissibility rows plus `6n` equilibrium rows of which
exactly 6 are dependent (each branch enters two nodes with opposite signs).
Squareness: `|E′| + 6(n−1) = 6c′ + 6(n−1) = 6(m−n+1) + 6(n−1) = 6m`. ∎

(iii) Each transmissibility row is linear in a hinge line, hence quadratic in
the points; the equilibrium rows are constant. So the determinant has degree
`2|E′|`.

(iv) At `n = 0` there is one branch, the whole cycle, and one screw `S`; the
matrix is the 6 × 6 matrix of `hodge C_e`, whose determinant equals
`det[C_0;…;C_5]` up to the sign of the Hodge permutation. This is the classical
statement that a closed 6-body loop is mobile exactly when its six hinge lines
lie in a **linear line complex**.

**Two traps this normal form sets, both worth recording.** *(a)* The reduced
object's branches may be **longer than 5**: deleting `β` drops two nodes of
`H/P` to degree 2 and merges their branches. (SD-6) bounds the branches of `G`,
not of `H/P − β`, and the driver observes reduced branches of length 6. Where
some `ℓ_j ≥ 6` the screw space `K_j = ⋂_e C_e^{⊥_B}` is generically **0** and
the branch is forced dead; the `6m × 6m` matrix is still the right object and
still square, but the "reduced order `6(n−1)` in the branch screws" reading is
only valid when every reduced branch has `ℓ_j ≤ 5`. *(b)* The welded body `X` is
**always** a body of `H/P − β` (it is a node of `H/P`, hence never a branch
interior), so at a bare-cycle site `X` always lies **on** the cycle.

**Measured** (`anhr1.py --size`, placement-free, over the full 4296-triple pool
of *Step A9*): 3820 triples carry a length-5 branch, giving **6426** labelled
instances of the pinned pool (not sites of the class — see the class-level
figures below); `c′` histogram `{0: 8, 1: 1904, 2: 3846, 3: 276, 4: 392}`
counts those same labelled instances; core-node histogram
`{0: 1912, 1: 134, 2: 3812, 3: 568}`; equilibrium-block order `6(n−1)`
histogram `{0: 142, 6: 5716, 12: 568}`. The identity `c′ = c(H/P) − 1` is
**asserted at all 6426 sites**. Cross-check of (ii) against the landed
machinery (`--reduce`): at all **58** length-5-branch sites of the (ANH-10)
census pool, the `6m × 6m` matrix's corank equals the dimension of the
`H/P − β` stress space rebuilt from scratch on the reduced edge list —
**58/58**, corank 0 at every one, reproducing (ANH-10)'s discharge through a
different matrix.

**Framing repair (2026-08-07, direction PEX) — the numbers above do not
change; every cell is a true labelled-instance count of the pinned pool.**
At the **class** level (§(K-frame) (FR-8)/(FR-14)): `c′ = 0` (`c(G) = 2`) is
**2** sites over **1** isomorphism class — θ(3,4,5), its unique inhabitant;
`c′ = 1` (`c(G) = 3`, the bare-cycle stratum) is **76** sites over **22**
isomorphism classes. At `c′ ≤ 1` the sweep above is **incomplete at the
iso-class level**: it carries 14 of the 22 `c′ = 1` classes, and §(K-frame)
(FR-8) supplies the complete list. The **29.6 %** ratio (`1904/6426`, *Step
A17*'s Verification table) survives as a **pool** ratio and should be read
as one — no class-level ratio is available, since the `c′ ≥ 2` cells sit
where the `|V°| ≤ 5` sweep cap genuinely binds.

**The boundedness is an artifact of the sweep, and the degree law is not.**
`n ≤ 3` and order `≤ 12` hold over the pool only because `outer.sweep_shapes`
caps `|V°| ≤ 5`; `n` is essentially the number of surviving hubs, `≤ 2c(G) − 1`,
and unbounded over the class — while `deg C = 12(c(G) − 2)` is unbounded
outright. The bounded end is therefore the **finite** end: `c(G) = 3` pins
`(|V|,|E|) = (16,18)`, finitely many graphs, and §(K-ind) *(I4)* says the
class's infinitude lives entirely in the `G°` direction, which is exactly the
direction `deg C` grows in. **`Pencil-strategy.md` §2.2's ingredient-2 boundary appears here in
the mirror of §(K-Δ)'s (M3):** there the ground set was frozen at `[3]` and
never grew with the graph; here the certificate's *degree* grows with the graph,
and a bounded-size symbolic identity is impossible for exactly that reason.

### Step A15 — (ANH-14): the bare-cycle stratum has ONE pure condition, and it is irreducible

> **(ANH-14)** *(proven-informally; the algebra is an identity over the function
> field, the local-frame half is a placement-free combinatorial theorem with a
> driver over the whole pool)* At every bare-cycle site (`c′ = 1`):
>
> (a) **The local frame is a 7-point open chain** (or, degenerately, a 6-point
> closed hexagon). `X` always lies on the cycle ((ANH-13)'s trap (b)), and the
> six hinge lines are `C_i = z_i ∨ z_{i+1}`, `i = 0..5`, on seven points: five
> real far bodies and `X`'s **two companion attachment points**, which break
> the hexagon open. If those two coincide the chain closes and the object is
> (e)'s closed hexagon instead. **Either way one of two universal polynomials
> governs the site**, so the universality claim does not depend on which.
> (Measured: 7 distinct points at 6/6 bare-cycle sites of the (ANH-10) census
> pool; distinctness was **not** measured over the full 1904.)
>
> (b) **No panel of the pencil chart constrains that frame.** A panel `Π(u)`
> imposes a condition on the local points only when it carries `≥ 4` of them
> (three points always span a plane, and `pt(u)` may then be chosen inside it).
> **No bare-cycle site has such a panel: 1904/1904** over the whole 4296-triple
> pool, placement-free. Therefore the pure condition at a bare-cycle site is
> the pullback of **one shape-independent polynomial** in seven free points.
>
> (c) **That polynomial is irreducible of degree 12, and it is `≢ 0`.**
>
> (d) **Its square is an explicit bracket expression:**
> `det(Gram) = −C²`, where `Gram_{ij} = B(C_i, C_j) = [z_i, z_{i+1}, z_j, z_{j+1}]`
> has the five adjacent entries zero and ten surviving brackets. `C` itself is
> **not** a rational combination of the five non-adjacent perfect matchings of
> the six lines.
>
> (e) **The closed hexagon — the object at any loop whose body-cycle carries no
> `X`-break (the degenerate bare-cycle case of (a), and each factor of an
> `n = 1` site whose node is not `X`) — does have a two-term closed form:** for
> six points in a closed cycle,
>
>  `det[C_0;…;C_5] = B(C_1,C_3)B(C_3,C_5)B(C_5,C_1) − B(C_0,C_2)B(C_2,C_4)B(C_4,C_0)`,
>
> the ODD Gram triangle minus the EVEN one — an identity over the function
> field. It does **not** survive the break at `X`: (d) says the open chain has
> no such form.

*Proof of (c)'s irreducibility, which is the only non-computational step.*
`GL(4)` is connected, so it permutes — hence fixes — the irreducible factors of
the relative invariant `C`; each factor is therefore itself a relative invariant,
i.e. a bracket polynomial, and a relative invariant of weight `w` has total
degree `4w`. `deg C = 12`, so a factorization has a factor of degree 4, i.e. a
**single bracket**. On the gauge slice `z_0..z_3 = e_0..e_3` every bracket
meeting `{z_4, z_5, z_6}` stays non-constant, so irreducibility of the
restriction rules out every candidate factor except `[z_0z_1z_2z_3]`, which the
slice sends to 1; and that one is killed by a second specialization
(`z_0 = z_1+z_2+z_3`, which makes the bracket vanish while all six lines stay
nonzero) at which `C ≠ 0`. ∎

**On the gauge** (the same argument as §(K-Λ) `lambda1.m2` (M4)): `C` and every
triple-bracket product transform by `det(g)³` under `p ↦ gp`, so their
difference is a weight-3 relative invariant; for a configuration with
`z_0..z_3` independent, `g = [z_0|z_1|z_2|z_3]^{-1}` is the unique element of
`GL(4)` carrying them to the standard basis, so the slice meets that orbit
exactly once and vanishing on the slice gives vanishing on the dense open
`[z_0z_1z_2z_3] ≠ 0`, hence identically.

**What (ANH-14) does to (ANH-R1) at the bare-cycle stratum — say the logic
exactly, because the two directions are NOT symmetric.**

- **Refutation transports for free.** The pencil chart maps *into* the local
  frame's configuration space, so `C ≡ 0` on the latter would give `C ≡ 0` on
  every such shape's chart. (ANH-14)(c) says this does **not** happen: no shape
  of the stratum is refuted, and none can be by this route.
- **Identities transport for free.** (d), (e) and the irreducibility hold a
  fortiori on every shape's chart. This is the entire logical yield of the
  symbolic computation, and it is real.
- **Non-vanishing does NOT transport.** `C ≢ 0` on the local frame says nothing
  about `C ≢ 0` on a given shape's chart unless the chart **dominates** the
  frame. So at a bare-cycle shape,
  > **(ANH-R1) ⟺ the shape's pencil chart is not contained in the single fixed
  > irreducible hypersurface `{C = 0}`** — no rank condition, no matroid
  > condition, nothing but chart-to-frame dominance.
  That is **verbatim §(K-out) (OC-16)'s residue** on the other side of the arc,
  and it is the second time the same missing technology has been reached from
  an independent direction (the first pair being *Step A13* item 3's
  T/R convergence).
- **At any shape (ANH-10) covers, dominance is not needed:** the census's exact
  rational chart point already proves `C ≠ 0` there, by (ANH-9)(iii).

**A consequence for the `n = 1` stratum (134 sites), derived from the normal
form and (ANH-4).** There the equilibrium block is empty (`6(n−1) = 0`) and
`m = c′`, so the branch-screw matrix is **block-diagonal**, one `ℓ_j × 6` block
per loop, with `Σ_j ℓ_j = 6c′ = 6m`. If any `ℓ_j ≠ 6` some block is wider than
tall and the determinant vanishes **identically** — which (ANH-4)'s generic
independence of `E(H/P) − β` forbids. So every loop has length exactly 6, and

>  `C(H/P − β) = ∏_{j=1}^{c′} det[C_{j,0}; …; C_{j,5}]`,

a **product of `c′` bare-cycle pure conditions**, each an instance of (e) or of
(a)–(d) according to whether that loop's node is `X`. So the M2-computable
strata are `c′ = 0` (8 sites), `c′ = 1` (1904) and `n = 1` (134) —
**2046 of 6426 = 31.8 %** of length-5-branch sites. Note this is the arc's only
*genuine factorization* of a pure condition on this side, and it is a
consequence of the graph splitting, not of the algebra: the factors themselves
are irreducible by (c).

**And a contrast that shows the universality is special.** At the *other* sites
the local frames **are** constrained: the forced-coplanarity histogram is
`{0: 122, 1: 3396, 2: 540, 3: 264, 4: 200}`. So no shape-independent polynomial
governs them, and the θ-core computation below is per-type, not universal.

### Step A16 — (ANH-15): the bad locus strictly contains (ANH-11)'s

> **(ANH-15)** *(proven; (a) symbolically over the function field, (b) at an
> exact rational witness — an existence claim)*
>
> (a) **(ANH-11) on the chain object.** Anchor `L = z_1 ∨ z_4`. The four lines
> incident to `z_1` or `z_4` meet `L` automatically; placing `z_3` in the plane
> `⟨z_1, z_4, z_2⟩` and `z_6` in `⟨z_1, z_4, z_5⟩` makes the other two meet it.
> On that locus all six lines are `B`-perpendicular to `C(L)` and
> `C(H/P − β) ≡ 0` **identically**. So (ANH-11)'s mechanism is now a symbolic
> identity on the universal object, not only a property of nine sampled
> witnesses.
>
> (b) **A second, AXIS-FREE mechanism.** The screw `S = C(e_0e_1) + C(e_2e_3)`
> has `B(S,S) ≠ 0`, so it is no line extensor and its linear complex has no
> axis: lines in it have **no common transversal**. An explicit integer 7-point
> chain lies entirely in that complex, its six lines have `B(C_i, S) = 0`, their
> Plücker matrix has rank exactly **5** (so the perp is exactly `⟨S⟩`), and
> `C = 0` there. Hence
>
>  `{C = 0}` ⊋ `{`the six lines have a common transversal`}`,
>
> and (ANH-11) reaches only part of the bad locus. This is the localized form of
> §(K-σ) *Step σ6* / `Pencil-strategy.md` §2.4's null-correlation device.
>
> (c) **Consistency with (ANH-12), checked in this section's own object.**
> Re-running `shrink.construct_at` read-only and evaluating the branch-screw
> matrix at each constructed bad point: at the **6 (ANH-R1)-exact** witnesses
> (β of length 5, count 0) the matrix is square and has **corank 1 — the pure
> condition vanishes at 6/6** — and the three matroid-drop witnesses
> (NT21/NT24/NT30, count `< 0`) also show corank 1. All **9** (ANH-12) witnesses
> lie in the pure condition's zero locus, as they must.

**What (b) does and does not say.** It says the *universal local* bad locus has
a component (or components) beyond the transversal locus, so
(ANH-12)'s *What would change this* item (iv) — *"a shape where no
cycle/labeling makes the construction work"* — would not by itself empty the bad
locus: a second mechanism is available in principle. It does **not** say the
pencil chart reaches that component at any class shape; whether it does is
open, and settling it is the same dominance question as everywhere else here.

### Step A17 — (ANH-16): the verdict on the method, and what is per-shape versus uniform

> **(ANH-16)** *(the pass's methodological finding; the cost figures are
> measured)*
>
> (i) **The per-shape M2 identity is the pointwise restatement of (ANH-R1)**
> (WW87 Cor. 2.7, in §(K-pure) *Step P0*'s reading), so at any shape carrying a
> guarded chart point it adds **no logical strength** over (ANH-9)(iii) + the
> exact-ℚ census — which decides the same question in seconds where the
> symbolic route takes minutes and, past the bare-cycle stratum, does not
> terminate. *Step A13* item 4 is hereby answered and **struck as an upgrade
> route**; what survives of it is (ANH-14).
>
> (ii) **Measured reach.** Generic point, ungauged: degree 12 in 24 point
> indeterminates, 10944 terms, **578 s** (finishes). A θ(5,5,2) core at the
> generic point: 12 free points, 48 indeterminates, two 5 × 6 Klein-perp
> kernels — **does not finish at 600 s**. With §(K-Λ)'s recorded kill (degree 52
> in 28 indeterminates) the layer's boundary is bracketed from both sides. On a
> **gauge slice** the bare-cycle identity is ~0.4 s, which is why the driver
> gauges.
>
> (iii) **Per-shape versus uniform, stated as the dispatch requires.** The
> *identity's proof* at the bare-cycle stratum **is uniform** — one polynomial,
> one computation, every shape of the stratum, with the local frame's
> unconstrainedness verified combinatorially at **1904/1904** sites. But the
> *transfer* to (ANH-R1) is **not**: it needs chart-to-frame dominance per shape
> (or, at a probed shape, the census witness). **Class uniformity therefore does
> not move**, and this section does not claim it does. What moves is the shape
> of the residue: at the bare-cycle stratum (ANH-R1) has **no rank condition
> left**, exactly as §(K-out) (OC-16) reports at degree-3 hubs.
>
> (iv) **No (ANH-7)-style recipe exists for (ANH-R1)'s own certificate**, by
> (ANH-14)(c)'s irreducibility. The arc's two closed forms — §(K-Λ) (Λ1)'s
> product of two linear forms and (ANH-7)'s single 4-point bracket — both came
> from reducible objects. This one is irreducible, and that is a theorem, not a
> failure to find a factorization.

### Verification (Steps A14–A17)

`notes/scripts/w4/anhr1.py` (**new with this continuation**; exact ℚ, stdlib
only, **no rng of its own** — every placement arrives through
`dominance.base_seed`'s composite guard `repin.star_generic` via
`annih.prepared`; imports only catalogued §1 primitives and the two owning
drivers read-only: `annih`'s `prepared` / `stress_space` / `hp_branches` /
`branch_screw` / `habitats4` / `control_shapes` / `swept_probes` /
`path_edges`, `shrink`'s `hp_edge_rows` / `branch_edge_ix` / `census_pool` /
`stress_dim_without` / `construct_at`, `outer`'s `split_data` / `companions4` /
`named_inventory` / `sweep_shapes`, `repin`'s `hodge_star`, `pitch`'s `klein`,
`kbare_common.verts_of`, and `exactcore`'s `rank` / `nullspace` / `wedge2` /
`hat` / `neighbors`). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --types     # (ANH-13)(ii), the local-type census   62 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --reduce    # (ANH-13)(ii) against the full solve   80 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --size      # (ANH-13)(i)/(iii), (ANH-14)(b)        12 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --frame     # (ANH-14)(a)/(b) at the census sites   63 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --witness   # (ANH-15)(c)                           81 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/anhr1.py --validate  # the machinery                         <1 s
M2 --script notes/scripts/m2/anhr1.m2                          # (ANH-14)(c)(d)(e), (ANH-15)(a)(b)     <1 s
```

All six Python modes verified **byte-identical** under `PYTHONHASHSEED` `0` and
`999`, exit 0 at every one; the M2 driver byte-identical across two runs, 18
assertions, final line `PASSED`. Every invocation fits the 600 s foreground
budget with room to spare — which is itself the point of (ANH-16)(i): the
decision procedure the symbolic route would replace costs seconds.

`notes/scripts/m2/anhr1.m2` (**new**; the M2 layer's third driver, after
`lambda1.m2` and `lambda0.m2`). It obeys the layer's four conventions
(`notes/scripts/m2/README.md`): its output is **evidence, never a substitute for
a Lean proof**; it prints the pinned version line `1.26.06` second and
`randomness: none`; it lives only in `m2/`; and it is **additive** — it ports no
Python driver, and `annih.py` / `shrink.py` keep every recorded figure
unchanged. Convention 3's divergence pin is block **(ANH-Q0)**: the bracket
dictionary `B(C(uv), C(pq)) = [u,v,p,q]` tying the M2 re-derivation of
`PL` / `wedge2` / `hodge_star` / `klein` / `det4` to their canonical Python
homes, plus the two structural corollaries (line extensors are isotropic; two
lines through a common point pair to 0 — which is why a body-hinge cycle placed
by *joins* always has a banded Gram).

Adding these two drivers modified **no** tracked script, so the
figure-invariance gate discharges on the `git diff --name-only -- '*.py' '*.m2'`
check alone (`notes/scripts/README.md`, first bullet).

Per mode, what is asserted. `--types`: per site, that the branch-screw matrix is
square (`6m = |E′| + 6(n−1)`), the excess is 0, and the local type signature.
`--reduce`: corank of the branch-screw matrix **equals** `stress_dim_without`'s
independent from-scratch rebuild, both directions, at every site. `--size`:
`c′ = c(H/P) − 1` at every site, and **`forced == 0` at every bare-cycle site**
(the (ANH-14)(b) assertion). `--frame`: per census bare-cycle site, the point
chain and the panel local-incidence histogram, asserting no forced coplanarity.
`--witness`: at each (ANH-12) witness, corank `≥ 1` of *this* driver's matrix,
asserted where the object has count 0. `--validate`: the core decomposition and
the count identity on a synthetic bare 6-cycle and a synthetic θ(4,4,4) core.
M2 blocks: **(ANH-Q0)** the dictionary pin; **(ANH-Q1)** the closed-hexagon
identity; **(ANH-Q2)** the open chain — not in the matchings' span, `≢ 0`,
`det Gram = −C²`, irreducible on the slice, and no `[z_0z_1z_2z_3]` factor;
**(ANH-Q3)** both bad-locus mechanisms; **(ANH-Q4)** the θ(5,5,2) core's 2 × 2
form and its exact witness.

**Figures.**

| figure | value |
|---|---|
| `--size` pool | **4296** (shape, split, length-4 companion) triples; **3820** with a length-5 branch; **6426** length-5-branch sites |
| `--size`: `c′ = c(G) − 2` | histogram `{0: 8, 1: 1904, 2: 3846, 3: 276, 4: 392}`; the identity `c′ = c(H/P) − 1` asserted at **6426/6426** |
| `--size`: core nodes `n` | `{0: 1912, 1: 134, 2: 3812, 3: 568}` |
| `--size`: `deg C = 12c′` | `{0: 8, 12: 1904, 24: 3846, 36: 276, 48: 392}` |
| `--size`: bare-cycle stratum | **1904 / 6426 = 29.6 %**; with the `n = 1` and trivial strata, **2046 / 6426 = 31.8 %** is M2-computable |
| `--size`: unconstrained local frames | **1904 / 1904** bare-cycle sites have NO panel forcing a coplanarity (asserted) |
| `--size`: the other sites | forced-coplanarity histogram `{0: 122, 1: 3396, 2: 540, 3: 264, 4: 200}` — universality is special to the bare-cycle stratum |
| `--types` | **26** triples with a guarded seed, **58** length-5-branch sites (matching (ANH-10)'s 58), **44** distinct local types |
| `--reduce` | branch-core normal form agrees with the from-scratch solve at **58/58** sites; corank **0** at every one |
| `--frame` | **6** bare-cycle census sites; **7** distinct points at each; **6/6** with an unconstrained local frame |
| `--witness` | **6** (ANH-R1)-exact witnesses, pure condition vanishes at **6/6**; 3 matroid-drop witnesses also corank 1; 1 trivial θ(3,4,5) |
| M2 `(ANH-Q1)` | `det[C] = B(C_1,C_3)B(C_3,C_5)B(C_5,C_1) − B(C_0,C_2)B(C_2,C_4)B(C_4,C_0)` |
| M2 `(ANH-Q2)` | `C` irreducible, degree 12; `det Gram = −C²`; **not** in the 5 matchings' span |
| M2 driver | **18** assertions, ~0.4 s, version line `1.26.06`, `randomness: none`; byte-identical across two runs |
| feasibility, ungauged | degree 12 / 24 indeterminates, 10944 terms: **578 s wall clock, finishes** (whole-script, the determinant dominating); θ core at the generic point (48 indeterminates): **no finish at 600 s** |
| determinism | all six Python modes byte-identical across `PYTHONHASHSEED` `0` and `999` |

**Which driver tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (ANH-13)(i) | `--size` | `c′ = c(H/P) − 1` asserted per site over the whole pool; the arithmetic `c(H/P) = c(G) − 1` is *Step A14*'s proof, not the census |
| (ANH-13)(ii) | `--types`, `--reduce` | squareness `6m = |E′| + 6(n−1)` per site, and corank equality against an **independently rebuilt** stress space at 58/58 |
| (ANH-13)(iii) | — | **proof-level** (each transmissibility row is quadratic in the points); its input histogram is `--size`'s |
| (ANH-13)(iv) | `--size`, `--reduce` | `n = 0` at exactly the `c′ ≤ 1` sites in the two histograms; at `n = 0` `core_matrix` **is** the 6 × 6 Plücker matrix, and `--reduce` checks its corank against the from-scratch solve |
| (ANH-14)(a) | `--frame` | the point chain printed per site, with the count of distinct points |
| (ANH-14)(b) | `--size`, `--frame` | the panel local-incidence histogram, with `forced == 0` **asserted**, at 1904/1904 pool sites and 6/6 census sites |
| (ANH-14)(c) | `(ANH-Q2)` | `C ≠ 0`; `#factor == 2` on the slice; and the second specialization killing the one bracket the slice cannot see. The `GL(4)`-connectedness step is **proof-level** and named as such |
| (ANH-14)(d) | `(ANH-Q2)` | the matching-span solve returning `null`, and `det Gram + C² == 0` |
| (ANH-14)(e) | `(ANH-Q1)` | the identity itself on the gauge slice, plus the recorded ungauged 578 s confirmation |
| (ANH-15)(a) | `(ANH-Q3)` | all six pairings with `C(L)` zero **and** `det == 0`, symbolically |
| (ANH-15)(b) | `(ANH-Q3)` | the explicit chain: `ω(z_i,z_{i+1}) = 0`, all lines nonzero, `B(C_i,S) = 0`, `det = 0`, **rank exactly 5** |
| (ANH-15)(c) | `--witness` | corank at the reconstructed (ANH-12) bad points, in this section's matrix |
| (ANH-16)(i) | — | **argument**, from (ANH-9)(iii) + §(K-pure) *Step P0*; no driver can test a redundancy claim |
| (ANH-16)(ii) | — | **measured wall-clock**, both the finish and the kill; the kill's reconstruction recipe is in the driver's header comment |
| **(ANH-R1)** | — | **still none, and still the point.** Nothing here tests class uniformity; (ANH-14) tests one polynomial, (ANH-16)(iii) says what that does and does not buy |

### Confidence verdict (Steps A14–A17)

- **(ANH-13): proven** — (i) and (ii) are counting and linear algebra, (iii) is
  immediate, and (ii) has a driver comparing it to an independent solve at
  58/58 sites. The size law is the pass's most transportable output.
- **(ANH-14): proven-informally.** (a) is measured (6/6) with the degenerate
  closure **not excluded combinatorially** — a named soft spot. (b) is a
  placement-free combinatorial theorem asserted at 1904/1904 pool sites, but
  the pool is `outer.sweep_shapes`, so "every class shape" is **not** proven —
  what is proven is the criterion (`≥ 4` local incidences) and its verification
  over the pool. (c)/(d)/(e) are identities over the function field, gauge-
  transported by the argument above; (c)'s irreducibility rests on the
  `GL(4)`-connectedness step, which is standard but is **prose, not machine-
  checked**.
- **(ANH-15): (a) proven** (an identity), **(b) proven at an exact witness**
  (an existence claim), **(c) measured** at 9/9 reconstructed witnesses.
  The class-wide reading "the extra component is reachable inside the pencil
  chart" is **NOT claimed** — it is open.
- **(ANH-16): (i) is an argument, and it is only as strong as (ANH-9)(ii)** —
  it is (ANH-9)(iii) plus §(K-pure) *Step P0*, both already in the workbook, and
  it inherits (ANH-9)(ii)'s **proven-informally** irreducibility of the pencil
  chart. That dependence is shared, not differential: an M2 identity needs the
  same irreducibility to mean "the generic point", so nothing about the
  comparison changes if (ANH-9)(ii) is ever sharpened. (ii) is **measured**;
  (iii)/(iv) are the honest statements of what this pass did and did not
  deliver.
- **(ANH-R1): OPEN, unchanged in status.** Its profile sharpens once more: at
  the bare-cycle stratum it is a chart-to-frame dominance question against one
  fixed irreducible hypersurface, with no rank condition left — the same shape
  as §(K-out) (OC-8)/(OC-16), reached independently for the third time.
- **Class uniformity is untouched. No gap-map status moves.**

### What would change this (Steps A14–A17)

*(i)* **A chart-to-frame dominance theorem** — that a class shape's pencil chart
dominates its bare-cycle local frame — would close (ANH-R1) on the **whole**
`c(G) = 3` stratum in one step, since (ANH-14) has already done the algebra.
It is the same missing statement as §(K-out) (OC-16)'s residue, and the two
should be attacked together: a single dominance lemma for "the chart surjects
onto the free configuration of a panel-unconstrained local frame" would serve
both. **This is the direction's chief hand-off.**

*(ii)* **A bare-cycle class shape whose chart lies inside `{C = 0}`** would
refute (ANH-R1) there and, with it, (ANH-7) at that shape. None exists among the
shapes (ANH-10) probes (the census witnesses forbid it), so the hunt would have
to run at unprobed `c(G) = 3` shapes — where a single exact rank computation is
still the cheapest test, by (ANH-16)(i).

*(iii)* **A degenerate bare-cycle site where `X`'s two cycle edges hang off the
SAME companion vertex** would make the local object the *closed* hexagon of
(ANH-14)(e) rather than the open chain, and would then inherit that stratum's
two-term closed form. Not observed (0/6 census sites); not excluded by any
argument here.

*(iv)* **A pencil-chart witness inside (ANH-15)(b)'s axis-free component** would
show the bad locus is inhabited by a mechanism (ANH-11) cannot construct, and
would strengthen (ANH-12)'s class-wide reading from "measured at 9/9 by one
construction" to "two independent constructions". The construction is
one linear condition per chain step, so it is a plausible target for a
`shrink.py --bad`-style solver.

*(v)* **A symbolic route past the bare-cycle stratum** — the θ-core generic
point is a 600 s kill as posed, but the object is a **2 × 2** determinant in two
pinned branch screws `κ_1, κ_2` (each a degree-10 bracket vector, *Step A6*), so
a formulation that carries `κ` symbolically without expanding the 5 × 6 kernel
might get through. That would extend the universality question — though not the
universality itself, since those local frames are panel-constrained
(3396 sites carry a forced coplanarity).

*(vi)* **An error in the branch-core normal form** — guarded by `--reduce`'s
comparison against a from-scratch rebuild of the reduced stress space at 58/58
sites, by `--validate`'s synthetic bare-cycle and θ-core checks, and by
`--witness` finding corank exactly where (ANH-12) says it must be.


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
tight rigid graph costs exactly 5). Tightness is arithmetic; rigidity of
`H/X` **is since 2026-08-06 a theorem** — *Step O9*'s (OC-10) proves it at
every class shape (direction O); the 4296 `deficiency` calls remain as a
check of the proof's conclusion.

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
> coincidence is not sufficient — and its **necessity beyond this pool is
> REFUTED by construction** (*Step O11* (OC-14), 2026-08-06, direction O: 38
> constructed fully-nondegenerate target-rank chart points, 34 guard-accepted,
> with `λᵢ = 0` and **no** coincident hinge; the correct general statement is
> (OC-12)'s dichotomy, and this pool's rates and the 318 / 299 denominators
> are **unaffected** — a codimension-1 locus is invisible to rational
> sampling, which is *why* 35/35 was measured). Restricted to the **318**
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
neighbour (driver prints `aims at [[17], [20]]`) — an observation *Step O10*'s
(OC-12) has since promoted from a θ(3,4,5)-specific remark to the general
degree-3-hub theorem. That is also why θ(3,4,5)
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

1. *(and 2.)* **STRUCK as unrealizable** (2026-08-06, direction O — *Step O9*
   (OC-10)): the hunted shapes — `dim R = 6`, or `dim R ≤ 4` / `μ ≥ 2` — do
   not exist at **any** class shape; the availability map is forced, so the
   widened 5226-pair sweep's 0-rates are theorems, not measurements. These
   items were never hunts.
2. *(struck with item 1 — see (OC-10).)*
3. **`L_b ⊆ R₁` at a chart point** — **HIT, by construction** (2026-08-06,
   direction O — *Step O11* (OC-14)): the hub slide onto `C₀` lands 38/38
   exact fully-nondegenerate target-rank points with `L_h ⊆ R`, sharpening
   (OC-8) past "sometimes forced" to *Step O11*'s restated containment
   question. The 46-frame `dim(R₁ ∩ L_b) = 1` figure stands as a statement
   about sampled frames only.
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
6. **Symbolic (Macaulay2) treatment of `R₁ ∩ L_b` on the local frame** —
   **ANSWERED on the `ℓ_min = 5` stratum, structurally BLOCKED off it**
   (2026-08-06, direction O — *Step O12*): (OC-16) proves `Δ ≢ 0` at the
   generic point of the length-5-chain local frame with the bad line `C₀` in
   closed form, and (OC-15) shows the path-span (bracket) form carries no
   information for `ℓ_min ≥ 6` (the stratum is 8 of 5226 pairs). The residue
   is the chart-to-frame dominance plus the block decomposition of *What
   would change this (Steps O9–O12)* item 3.

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

### Steps O9–O12 (2026-08-06, fan-out direction O) — the negative half got stronger, and the residue got smaller and sharper

Drivers `notes/scripts/w4/outerwide.py` (imports `outerline.py` read-only) and
`notes/scripts/m2/outerwide.m2`, both new this pass; labels **(OC-10)–(OC-16)**.
Everything cited that this pass did not mint is qualified: **(OUT)**,
**(Λ0a)–(Λ0i)**, **(Λ0f′)** are §(K-Λ)'s; **(K-wit)** is owned jointly by
§(K-pitch) *Step 3* and §(K-Λ) *Steps 3–6*; POOL-C / POOL-G / POOL-S / POOL-B are
this section's earlier pools and **nothing below is aggregated with them**.


Four things, in the order they change the reading of (OUT).

- **(OC-10) — the combinatorial availability map is FORCED, not measured, and
  §(K-out) *What would change this* items 1 and 2 are UNREALIZABLE.** At every
  **class** shape — tight, `def(G) = 0`, both chain ends **hubs**, and
  **`hnoRigid`**; all four hypotheses are needed and each is shown
  load-bearing — every eligible split and every length-4 companion has
  `χ = 0`, `μ₁ = μ₄ = 1`, `H/X` and `H/Y` **isostatic**, `A₁ = A₄ = 0`,
  `dim R₁ = dim R₄ = 5`. So the hunt items 1–2 commission (a shape with
  `dim R = 6`, or with `dim R ≤ 4` / `μ ≥ 2`) cannot succeed at any class shape
  whatsoever: the widening is not merely a no-hit, it is a **theorem that no
  widening can hit**. §(K-out) (OC-2)'s "rigidity of `H/X` is the one measured
  fact" is superseded — that fact is now proven. **A process note the
  coordinator should keep:** the first draft of this proof discharged the
  boundary case by a pigeonhole argument that is valid only when the violating
  subgraph has no interior-to-interior edge; the F11 minimality driver
  (`--adv`, rows 7–8) refuted it, and row 8 is a graph satisfying *every* other
  hypothesis with `dim R₁ = 6`, whose only broken hypothesis is `hnoRigid`.
  The repaired proof is below and is the one to land.
- **(OC-11)/(OC-12) — (OC-3)'s marked direction acquires a FORMULA, and at a
  degree-3 hub it *is* the other hinge line.** `dim R₁ = 5` being a theorem
  makes `R₁` a **hyperplane**; inside the panel, `dim(R₁ ∩ β_b) ≥ 2` always
  (`β_b` := the 3-dimensional, totally `B`-isotropic space of lines of `Π(b)`),
  and where the meet is exactly 2 it is the **pencil of a single point `p` of
  `Π(b)`**. Then `λ₁ = 0 ⟺ p, pt(b), pt(x₁)` collinear, and
  `L_b ⊆ R₁ ⟺ p = pt(b)`. At a **degree-3 hub** (`deg_G(b) = 3`, so
  `deg_H(b) = 2` with other `H`-neighbour `u`) one has `C(b,u) ∈ R₁`
  unconditionally, hence `p ∈ C(b,u)` and the marked direction **is** `C(b,u)`:
  `λ₁ = 0 ⟺ C(b,x₁) = C(b,u)`, a **coincident hinge line at `b`** — so
  **§(K-out) (OC-7)'s measured implication is a THEOREM at a degree-3 hub**
  (`repin.star_generic` accepting the frame *implies* `λ₁ ≠ 0` there), and
  *Step O6*'s remark that θ(3,4,5) is special because "`b` has only two
  `H`-neighbours there" is not a special case but the general degree-3 statement.
  Census: `deg_G(b) = 3` at **3081 of 5226** POOL-CW pairs, and at least one
  companion end has degree 3 at **3702 of 5226**.
- **(OC-13)/(OC-14) — the exceptional locus is a LINE of the panel, it is
  REACHABLE, and reaching it REFUTES (OC-7)'s necessity claim.** With
  `T_u := {m(u) − m(v*)}` in `(H/X) − b` (4-dimensional and **independent of
  `pt(b)`, `pt(x₁)` and `pt(a)`**), `R₁ = ⟨C(b,u)⟩ ⊕ T_u` and
  `R₁ ∩ β_b = ⟨C(b,u)⟩ ⊕ (T_u ∩ β_b)`, so `L_b ⊆ R₁` ⟺ `dim(T_u ∩ β_b) = 2`
  or `pt(b) ∈ C₀`, where `C₀` is the line of `Π(b)` spanning `T_u ∩ β_b`.
  Because `T_u` and `β_b` do not see `pt(b)`, **sliding `pt(b)` inside its own
  panel** is a legal chart move whenever `b` has no hub `G′`-neighbour, and
  `C₀` is *fixed* along it. Run exactly: the slide **onto** `C₀` lands **38 of
  38** attempts at θ(3,4,5), each an exact chart point that is target rank with
  `dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4`, **all four**
  `IsNondegPencilRealization` conjuncts, **(Λ0a)–(Λ0f′) all green**, `λ ∦ p⁺`,
  `λ ∦ q`, `deg_t Q(z(t)) = 4` — and with `λᵢ = 0` **identically in `pt(xᵢ)`**
  and **no coincident hinge line at the hub** (34 of the 38 are accepted by the
  whole-configuration guard `repin.star_generic`). So: **(OC-7)'s "the
  coincidence is necessary" is REFUTED as a general statement** (it survives as
  a statement about POOL-G's *sampled* frames, and the pool restriction to 318 /
  299 is unaffected — see the correction list), and **(OC-8)'s bad case is
  inhabited at a real class habitat by an explicit construction**, not merely
  possible. Four of the 38 are (OUT)-**silent** (both outer coordinates vanish),
  strengthening (OC-4): the escape still holds there by the pitch certificate.
- **(OC-15)/(OC-16) — §(K-out) *What would change this* item 6 is ANSWERED on
  one stratum and structurally BLOCKED off it.** `R₁` is contained in the
  hinge-line span of **every** `b`-to-`v*` path of `K = (H/X) − e₁` (each edge
  contributes `m(u) − m(w) ∈ ⟨C(u,w)⟩`), and `dim R₁ = 5` therefore forces every
  such path to have `≥ 5` edges. Where some path has **exactly** 5 the
  containment is an equality, `R₁` is a **bracket** object, and the whole (OC-8)
  clause becomes one `6×6` Plücker determinant in seven points —
  `m2/outerwide.m2` then proves, at the **generic point** of the gauge-sliced
  local frame, that `Δ ≢ 0` (so `L_b ⊄ R₁` generically), that `Δ` factors into
  **exactly two** simple irreducible factors, and that the non-degenerate factor
  is **linear in `pt(b)`** — i.e. **`C₀` in closed form**, its coefficients
  brackets of the far chain points only. Off that stratum the route is blocked
  and the blockage is measured: for `ℓ_min ≥ 6` the path spans are already all of
  `K⁶` and their intersection carries no information (`(2, 6, False) : 38`,
  `(3, 6, False) : 70`), and the census says `ℓ_min = 5` holds at only **8 of
  5226** POOL-CW pairs. **This is the honest boundary of the symbolic route**,
  and it is a boundary of the *bracket* form, not of (OC-11)–(OC-13), which need
  only `deg_H(b) = 2`.

**Verdict, stated at the strength the work supports.** The *combinatorial*
half of §(K-out) is now **proven** rather than measured, and two of its six
*What would change this* items are struck as unrealizable. (OC-8) is **still
open**, but it is no longer "a rank lower bound on the whole-graph chart": at a
degree-3 hub it is the single sentence *the hard-stratum target-rank locus is not
contained in the hypersurface `{pt(b) ∈ C₀}`*, with `C₀` an explicit line of the
panel — in closed bracket form on the `ℓ_min = 5` stratum. **Class uniformity of
(OUT) is not established and no gap-map status moves.**

---

### Step O9 — (OC-10): the availability map is forced

Notation is §(K-out)'s *Standing notation* verbatim: `H = G − v − a` at the
split `v` with `b–v–a–c` the length-3 split branch (`deg v = deg a = 2`, `b` and
`c` hubs), `P = b–x₁–x₂–x₃–c` a length-4 companion, `X = {x₁,x₂,x₃,c}`,
`Y = {b,x₁,x₂,x₃}`, `μᵢ`, `Rᵢ`, `Aᵢ`, `χ` as *Step O2* defines them. Write
`cnt(W) := 6(|W| − 1) − 5|E_G(W)|` for `W ⊆ V(G)`.

> **(OC-10)** Let `G` be **tight** (`5|E| = 6(|V| − 1)`) with `def(G) = 0` —
> i.e. **isostatic** in the count matroid `nogood_subdiv.deficiency` computes —
> and satisfying **`hnoRigid`**: no *proper* branch-union of `G` is rigid
> (`kslide.no_rigid_branch_union`, the class predicate's own certificate). Let
> `v` be an **eligible** split, so both chain ends `b`, `c` are **hubs**
> (`outer.split_data`'s filter). Then at every length-4 companion:
> `χ = 0`; `μ₁ = μ₄ = 1`; `H/X` and `H/Y` are **tight and isostatic**
> (`def = 0`); `A₁ = A₄ = 0`; and `dim R₁ = dim R₄ = 5`.
> **Corollary.** Every `b`-to-`v*` path of `K = (H/X) − e₁` has `≥ 5` edges,
> and symmetrically at the `c` end.
>
> **All four hypotheses are used, and each is load-bearing** (`--adv`): drop
> tightness of `H`'s count, or `def(G) = 0`, or girth (a consequence of the
> first two), or `χ = 0`, or *`b`, `c` hubs*, or **`hnoRigid`**, and a witness
> with `dim R₁ = 6` or `μ ≥ 2` appears at once. In particular `hnoRigid` is
> **not** decoration: `--adv` row 8 is tight, isostatic, girth 8, `χ = 0`, has
> both chain ends hubs and no vertex with two weld-neighbours — and still has
> `def(H/X) = 1` and `dim R₁ = 6`.

*Proof.*

**(a) Isostatic ⟹ 5/6-sparse.** `def(G) = 0` means
`rank_{(6,6)}(5G) = 6(|V| − 1)`, which tightness makes `= 5|E| = |5G|`: the
multiset `5G` is **independent**. A sub-multiset supported on `W ⊆ V` is largest
when it takes all five copies of every `G`-edge inside `W`, so independence is
*equivalent* to `cnt(W) ≥ 0` for every `W`. (Only necessity is used until step
(e); sufficiency is used there. `kslidecomb.shape_ok`'s own docstring already
records this equivalence — "tight (def = 0, which with the count
`5|E| = 6(|V|−1)` forces 5/6-sparsity of every subgraph)" — so nothing here is
a new convention.)

**(b) Girth ≥ 6.** A cycle on `L` vertices has `cnt = 6(L − 1) − 5L = L − 6`,
so `L ≥ 6`. In particular `G` is triangle-free and has no 4- or 5-cycle —
*independently* of the class predicate's own `triangles(E)` test.

**(c) `χ = 0`.** The six candidate chords of `P` close cycles of `G` of lengths
3 (`bx₂`, `x₁x₃`, `x₂c`), 4 (`bx₃`, `x₁c`) and 5 (`bc`, via the companion). All
`< 6`. (`bc` is doubly excluded: with the split branch it also closes a
4-cycle.)

**(d) `μ₁ = 1`.** A second `b`–`X` edge is one of `bx₂`, `bx₃`, `bc`, excluded
by (c). Symmetrically `μ₄ = 1`.

**(e) `H/X` is isostatic.** `cnt_H := 6(|V(H)| − 1) − 5|E(H)| = 3` (removing
`v, a` drops 2 vertices and 3 edges from a graph of count 0), and with `χ = 0`,
welding `X` drops 3 vertices and 3 edges, so `H/X` has count `0` — **tight**
(this is *Step O2*'s `5χ` identity at `χ = 0`, and the driver asserts it per
pair). For independence, suppose `W′ ⊆ V(H/X)` is a **minimal** violating set:
`5|E_{H/X}(W′)| > 6|W′| − 6`, every vertex of `W′` incident to an edge inside
(minimality — deleting an isolated vertex only strengthens a violation). If
`v* ∉ W′` then `W′ ⊆ V(H)` and `E_{H/X}(W′) = E_H(W′)`, contradicting (a). So
`v* ∈ W′`; put `W := W′ ∖ {v*}`, `s := |W|`, and let `K` be the corresponding
`H`-edge set — edges with both ends in `W ∪ X`, at least one end in `X`, none of
them the three `X`-internal path edges. The violation reads **`5|K| > 6s`**.

- *If `b ∈ W`:* apply (a) at `U := W ∪ X ∪ {v, a}`, `|U| = s + 6`. `E_G(U)`
  contains `K`, the three internal edges `x₁x₂, x₂x₃, x₃c`, the three split-path
  edges `bv, va, ac`, and `bx₁` — at least `|K| + 6` distinct edges (`bx₁` may
  already lie in `K`). So `5(|K| + 6) ≤ 6(s + 5)`, i.e. `5|K| ≤ 6s`.
  **Contradiction.**
- *If `b ∉ W`:* apply (a) at `U := W ∪ X ∪ {b, v, a}`, `|U| = s + 7`. Now `bx₁`
  cannot be in `K` (its end `b` is outside `W ∪ X`), so `E_G(U)` contains
  `|K| + 7` distinct edges and `5(|K| + 7) ≤ 6(s + 6)`, i.e.
  **`5|K| ≤ 6s + 1`**. Together with the violation `5|K| > 6s` this forces
  `5|K| = 6s + 1` **exactly** — and then `cnt(U) = 0` with `E_G(U)` **equal**
  to the listed `|K| + 7` edges (one more `G`-edge inside `U` would give
  `5|K| ≤ 6s − 4`). So `U` is a **tight** subgraph of `G`; being a subgraph of
  an independent set it is independent; so **`U` is isostatic, hence rigid**.
  Three observations finish it.
  - *`U` has minimum degree `≥ 2`.* A vertex `y` of degree `≤ 1` in `U` gives
    `cnt(U − y) = cnt(U) − 6 + (5 or 0) < 0`, contradicting independence.
  - *`U` is a union of COMPLETE branches of `G`.* If a `G`-degree-2 vertex lies
    in `U` then both of its edges do (min degree `≥ 2`), so its neighbours lie
    in `U`; induction along the branch puts the whole branch, both hub ends
    included, in `U`. Hubs of `U` need no such closure. Hence `V(U)` is exactly
    the vertex union of a set of branches and `E_G(U)` their induced edge set —
    which is precisely the object `kslide.no_rigid_branch_union` enumerates.
  - *`U` is PROPER.* Here is where `b` being a **hub** is used: `deg_G(b) ≥ 3`
    while `b`'s `U`-edges are only `bv` and `bx₁`, so `b` has a third `G`-edge
    `bz`; if `z ∈ U` then `bz ∈ E_G(U)` beyond the list, contradicting the
    equality above. So `z ∉ U` and `U ⊊ G`.

  So `U` is a **rigid proper branch-union**, contradicting `hnoRigid`.

So no violating set exists; `H/X` is independent, and being tight it is
isostatic. Symmetrically for `H/Y`, with `U := W ∪ Y ∪ {c, v, a}` (resp.
`W ∪ Y ∪ {v, a}` when `c ∈ W`), the internal edges `bx₁, x₁x₂, x₂x₃`, the extra
edge `x₃c`, the same split path, and `c` the hub supplying properness.

*Remark (what the first draft got wrong, kept because it is the useful special
case).* If every `K`-edge joins `W` to `X` — no interior-to-interior edge —
then `5|K| = 6s + 1` forces `|K| > s`, every vertex of `W` carries a `K`-edge,
and pigeonhole gives some `u ∈ W` with **two** `X`-neighbours; each such pair
closes a cycle of length `≤ 5` through the `X`-path (`x₁,x₂`: 3; `x₁,x₃`: 4;
`x₁,c`: 5; `x₂,x₃`: 3; `x₂,c`: 4; `x₃,c`: 3), contradicting (b) with **no**
appeal to `hnoRigid`. That sub-case is what the driver asserts per pair (and it
holds at 5226/5226). It is *not* the general case: with `W`-`W` edges allowed
the violating configuration exists as a graph (`--adv` rows 7–8) and only
`hnoRigid` excludes it.

**(f) `A = 0` and `dim R = 5`.** `A₁ = def(H/X) − def(H/(X ∪ {b}))`; welding two
bodies of a rigid body-hinge framework is satisfied by its trivial motions, so a
contraction of a rigid graph is rigid and both terms vanish. For `dim R₁`: with
`μ₁ = 1`, `K = (H/X) − e₁` is independent of count 5, so `def(K) = 5`; and
`(K)/(b,v*) = (H/X)/e₁` is a contraction of a rigid graph, so its deficiency is
0. Hence `dim R₁ = 5 − 0 = 5`. ∎

**Corollary (the path bound).** `e₁` together with any `b`-to-`v*` path of `K`
of length `ℓ` closes a cycle of `H/X` of length `ℓ + 1`, and (b) applies to
`H/X` too (it is isostatic by (e)), so `ℓ ≥ 5`.

**Why items 1–2 are dead, stated as the consequence.** §(K-out) *What would
change this* item 1 asks for `dim R₁ = dim R₄ = 6` and item 2 for
`dim R₁ ≤ 4` or `μ₁ ≥ 2`; (OC-10) forbids all three at every class shape, so the
`0 of 4296` of (OC-2) and the `0 of 5226` of *Step O10*'s widened pool are not
rates at all. Both items should be **struck** from §(K-out) *What would change
this* and replaced by a pointer here.

**A remark that explains the sweep's zeros, and is worth recording because it
shrinks the class.** For a *theta* shape (2 hubs, `m` branches) tightness gives
`Σl = 6(m − 1)`, and a `k`-subset `S` of branches spans a subgraph of count
`Σ_S − 6(k − 1)`, so independence needs `Σ_S ≥ 6(k − 1)` and `hnoRigid`
(`kslidecomb.no_rigid_branch_union`) needs **strict** inequality for proper
subsets. With the split branch pinned at 3 and a companion branch at 4, the
`(m−1)`-subsets give `l_i ≤ 6` for every `i`, so the other `m − 2` branches sum
to `6(m−2) − 1` with each `≤ 6`: exactly one of them is 5 and the rest are 6.
But then `{3, 4, 5}` is a proper branch-union of count exactly 0 — **rigid** —
which `hnoRigid` forbids. Hence **no theta shape with `m ≥ 4` branches is a
class shape**, and θ(3,4,5) is the unique theta member. Driver-checked
exhaustively: `theta4` (`lmax = 13`, 364 tuples) and `theta5` (`lmax = 18`,
5700 tuples) both yield **0** class shapes.

---

### Step O10 — the widened sweep (POOL-CW), and (OC-11)/(OC-12): the hyperplane form

**POOL-CW.** `outer.named_inventory()` plus a widened family list: `theta3`
(exhaustive), `theta4` and `theta5` (exhaustive, both empty — see the remark
above), **two new 3-hub multigraphs** `M3a` (5 branches, exhaustive; 20 shapes)
and `M3b` (6 branches, exhaustive; 60 shapes), `K4` and `K4+par` at raised
bounds (540 / 740 shapes, unchanged from `outer.sweep_shapes()`, so those
`lmax` values were already effectively exhaustive), **`K4 +` two parallel edges**
(8 branches, capped; 60 shapes), the `|V°| = 5` families at `lmax = 6` capped at
60 each (180 shapes, versus 75 at the old cap 25 / `lmax` 5), and **`|V°| = 6`**
at `|E°| ≤ 10`, `lmax = 6`, cap 12 each (72 shapes over 6 hub graphs) — a family
`outer.sweep_shapes()` does not reach at all. Total **5226 (split, companion)
pairs over 1693 class shapes** (POOL-C: 4296 / 1376). **Disjoint in intent from
POOL-C but overlapping in content — POOL-CW figures are never summed with
POOL-C's, and POOL-CW supersedes rather than extends them.**

- `(μ₁, dim R₁, A₁, μ₄, dim R₄, A₄) = (1,5,0,1,5,0)` at **5226 of 5226**;
  `(χ, def(H/X), def(H/Y)) = (0,0,0)` at **5226 of 5226**. Hits for items 1 and
  2: **0 and 0** — and by (OC-10) that is forced, not measured.
- Per pair the driver asserts the proof's own steps: the `5χ` count identity,
  `χ = 0`, `μ = 1`, `def(H/X) = def(H/Y) = 0`, no vertex outside a weld with two
  weld-neighbours (the pigeonhole configuration), and `ℓ_min ≥ 5` at both ends;
  girth `≥ 6` is asserted on the first 250 pairs' shapes (the proof itself uses
  only the two *local* consequences, which are asserted at all 5226).
- **Coverage boundary, stated as a boundary.** `|V°| = 6` is reached only at
  `|E°| ≤ 10`: one `|E°| = 11` hub graph costs **137 s** at cap 8 — a measured
  cost, not a claim about those shapes. The `|V°| = 5,6` and `K4+2par` families
  are **capped**, so their shape lists are not exhaustive.

**The census, which is what the widening actually buys.** Two of these rows are
inputs to (OC-12)/(OC-13) and had never been measured:

| datum | histogram over the 5226 pairs |
|---|---|
| `(deg_G b, deg_G c)` | `(3,3) 2460`, `(3,4) 606`, `(4,3) 606`, `(4,4) 1522`, `(3,5) 15`, `(5,3) 15`, `(4,5) 1`, `(5,4) 1` |
| `(ℓ_min at b, at c)` | `(6,6) 1616`, `(7,7) 1478`, `(6,7)/(7,6) 317` each, `(8,8) 500`, `(6,8)/(8,6) 203` each, `(7,8)/(8,7) 246` each, `(8,9)/(9,8) 40` each, `(5,5) **8**`, `(6,9)/(9,6) 4`, `(7,9)/(9,7) 2` |
| `b` has no hub `G′`-neighbour / `c` has none | `(T,T) 1478`, `(T,F)/(F,T) 1749` each, `(F,F) 250` |
| companion hub pattern `(x₁,x₂,x₃)` | `(0,0,0) 1172`, `(0,0,1)/(1,0,0) 1634` each, `(0,1,0) 758`, `(1,0,1) 24`, `(0,1,1)/(1,1,0) 2` each |

So **(OC-12) applies at the `b` end at 3081 of 5226 pairs** and at **at least
one end at 3702 of 5226**; **(OC-13)'s hub slide is additionally legal at the
`b` end at 1715 of 5226**; and the bracket/M2 form of *Step O12* applies at
**8 of 5226**.

**Now the geometry.** `β_h` := the space of lines of the panel `Π(h)`. It is
`Λ²` of a 3-dimensional subspace of `K⁴`, hence **3-dimensional, every nonzero
element decomposable** (so every element is a genuine line of `Π(h)`) and
**totally `B`-isotropic** (four vectors in a 3-space have determinant 0) — all
three asserted per end. `L_h = α_{pt(h)} ∩ β_{Π(h)} ⊆ β_h` is a 2-dimensional
subspace, and *every* 2-dimensional subspace of `β_h` is the pencil of exactly
one point of `Π(h)` (a line of the dual plane).

> **(OC-11)** At any chart point with `dim Rᵢ = 5` (so, by (OC-10), at every
> one): `dim(Rᵢ ∩ β_h) ≥ 5 + 3 − 6 = 2`, and where the meet is exactly 2 it is
> the pencil `L_p` of a single point `p ∈ Π(h)`. Then
>
> - `λᵢ = 0 ⟺ Cᵢ ∈ Rᵢ ∩ β_h ⟺ p, pt(h), pt(xᵢ)` **collinear** — so §(K-out)
>   (OC-3)'s "exactly one marked direction of `x₁`'s pencil" is the direction
>   `pt(b) → p`, a formula rather than an existence statement;
> - `L_h ⊆ Rᵢ ⟺ p = pt(h)` — a **single point coincidence in the panel plane**.
>
> *Proof.* Both `Cᵢ` and every element of `L_h` lie in `β_h`, so the first
> equivalence is §(K-out) (OC-1) intersected with `β_h`; a line through `pt(h)`
> lies in the pencil `L_p` iff it passes through `p`; and `L_h = L_p` iff their
> centres agree. ∎

> **(OC-12)** Suppose `deg_G(b) = 3`, i.e. `deg_H(b) = 2` with `b`'s
> `H`-neighbours `x₁` and one other `u`. Then `C(b,u) ∈ R₁`
> **unconditionally**, hence `p ∈ C(b,u)`, hence — as long as `p ≠ pt(b)` —
> the marked direction of (OC-3) is exactly `C(b,u)` and
>
> `λ₁ = 0 ⟺ C(b,x₁) = C(b,u)`, i.e. `pt(b), pt(x₁), pt(u)` collinear.
>
> *Proof.* In `K = (H/X) − e₁` the body `b` carries the single hinge `b–u`, so
> the twist rotating `b` about `C(b,u)` and fixing everything else is a motion
> of `K`, and it realizes `m(b) − m(v*) ∝ C(b,u)`. `pt(u) ∈ Π(b)` (the closed
> star spans the panel), so `C(b,u) ∈ L_b ⊆ β_b`; thus
> `C(b,u) ∈ R₁ ∩ β_b = L_p` and `p ∈ C(b,u)`. If `p ≠ pt(b)` then
> `pt(b) ∨ p = C(b,u)` and (OC-11)'s first equivalence reads
> `pt(x₁) ∈ C(b,u)`. ∎
>
> **Two consequences.** (i) §(K-out) **(OC-7)'s implication is a theorem at a
> degree-3 hub**, together with its free-rotor reading: the coincidence
> exhausts `b`'s other `H`-neighbours because at degree 3 there is only one.
> (ii) **`repin.star_generic` implies `λ₁ ≠ 0`** at a degree-3 hub off the
> exceptional locus `{p = pt(b)}` — the guard the 2026-08-06 re-baselining
> round adopted is, at these ends, not merely a genericity hygiene measure but
> *the hypothesis of (OUT)*.

*Measured (POOL-W, `--wrench`).* The 4 `lambda.habitat_specs` habitats × seeds
**200–219**, accepted exactly as `outerline.frame_at` accepts them, with
`repin.star_generic` **reported** rather than applied (it is what (OC-12) is a
statement about): **73 frames, 146 companion ends**. `dim R = 5` at 146/146
(the theorem, re-checked); `dim(R ∩ β_h) = 2` at 146/146 (never 3);
`L_h ⊆ R` **false** at 146/146. Degree-3 ends: **38** (all θ(3,4,5)), at every
one of which `C(b,u) ∈ R` and `p ∈ C(b,u)` are asserted, `dim(T_u ∩ β_h) = 1`,
and `λᵢ = 0 ⟺` the coincidence is asserted. The guard sentence, tested as
itself: over the degree-3 ends, `(star_generic accepts, λᵢ = 0)` is
`(accepted, False) 30`, `(rejected, False) 4`, `(rejected, True) 4` — **0
violations of the implication, asserted per end**, not observed as a rate.

---

### Step O11 — (OC-13)/(OC-14): the bad locus is a line of the panel, and the hub slide reaches it

> **(OC-13)** At a degree-3 hub `b`, let `T_u := {m(u) − m(v*)}` in
> `(H/X) − b`. Then `dim T_u = 4`, `C(b,u) ∉ T_u`, `R₁ = ⟨C(b,u)⟩ ⊕ T_u`, and
> — because `C(b,u) ∈ β_b` —
> `R₁ ∩ β_b = ⟨C(b,u)⟩ ⊕ (T_u ∩ β_b)` with `dim(T_u ∩ β_b) ∈ {1, 2}`. Hence
>
> `L_b ⊆ R₁ ⟺ dim(T_u ∩ β_b) = 2, or pt(b) ∈ C₀`,
>
> where `C₀` is the line of `Π(b)` spanning `T_u ∩ β_b` in the 1-dimensional
> case. `T_u` involves **no** panel datum and **not** `pt(b)`, `pt(x₁)` or
> `pt(a)` (the body `b` is deleted from the system and `a ∉ V(H)`), and `β_b`
> depends only on the *plane* `Π(b)`. Therefore, whenever `b` has **no hub
> `G′`-neighbour**, sliding `pt(b)` inside `Π(b)` with the panel and every other
> point held fixed is a **legal chart move** along which `C₀` is constant, and
> the bad locus of `pt(b)` is exactly the line `C₀`.
>
> *Proof of the dimension count.* `(H/X) − b` has count `0 − 6 + 5·2 = 4` and is
> independent, so `def = 4` and `dim T_u ≤ 4`; `dim R₁ = 5` ((OC-10)) with
> `R₁ ⊆ ⟨C(b,u)⟩ + T_u` (split `m(b) − m(v*)` across the single hinge `b–u`)
> forces `dim T_u = 4` and `C(b,u) ∉ T_u`. `dim(T_u ∩ β_b) ≥ 4 + 3 − 6 = 1`; it
> cannot be 3, since that would put `C(b,u) ∈ β_b ⊆ T_u`. Legality of the slide:
> `Π(b)` unchanged keeps every `G′`-neighbour of `b` inside it and keeps every
> meet line through it (so `pt(a)` stays on `M = Π(b) ∩ Π(c)`), and `pt(b)`
> stays in the panels of its hub neighbours vacuously when there are none. ∎

> **(OC-14)** *(the experiment, `--slide`)* At θ(3,4,5), at every one of the
> **38** degree-3, hub-neighbour-free ends of POOL-SL (the 4 habitats × seeds
> 200–219; only θ(3,4,5) qualifies), the slide of `pt(b)` **onto** `C₀` lands —
> `38 of 38`, **zero** rejections — at an exact chart point which is
>
> - **target rank** with `dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4`,
>   `pt(a)` still on `M`, no coincident adjacent points, closed-star ranks 3;
> - **all four `IsNondegPencilRealization` conjuncts** green (38/38);
> - **(Λ0a)–(Λ0f′) all green**, with `λ ∦ p⁺`, `λ ∦ q` and
>   `deg_t Q(z(t)) = 4` (38/38) — so **the escape still holds there**, by the
>   pitch certificate, exactly as at §(K-out) (OC-4);
> - carrying `λᵢ = 0` **and** `L_h ⊆ R` (both asserted), i.e. `λᵢ` vanishes
>   *identically in the placement of `xᵢ`*;
> - with **no coincident hinge line at the hub** (38/38), and accepted by the
>   whole-configuration guard `repin.star_generic` at **34 of 38**.
>
> Conversely the slide **off** `C₀` lands at 38 chart points, at every one of
> which `λᵢ ≠ 0` and `L_h ⊄ R` — asserted, which is (OC-13)'s positive half.
> Four of the 38 on-`C₀` points have **both** outer coordinates zero, i.e.
> (OUT) **silent** at a point where one disjunct has died identically.

**What (OC-14) costs and what it buys, stated separately.**

*It costs §(K-out) (OC-7) its necessity claim.* (OC-7) records "the converse
fails …, so the coincidence is **necessary**, not sufficient". Necessity is
**refuted**: a guard-accepted, fully nondegenerate, target-rank hard-stratum
chart point of a real class habitat has `λ₁ = 0` with no coincident hinge at
`b`. The correct statement is (OC-12)'s **dichotomy** — at a degree-3 hub,
`λ₁ = 0` implies *either* the coincidence *or* `p = pt(b)`. Nothing else in
(OC-7) moves: the 33/36 manufactured-by-`plane_basis` finding, the standing rule
that no `place_pencil_general` battery may be quoted as a **rate**, and the
restriction of POOL-G rates to the **318** coincidence-free (or the **299**
guard-accepted) frames are all untouched, because the exceptional locus
`{pt(b) ∈ C₀}` has codimension 1 and random rational sampling never meets it.
That is also *why* (OC-7) measured 35/35: the second branch of the dichotomy is
invisible to sampling and visible only to a construction.

*It buys the sharpest available form of (OC-8).* Combining (OC-12) and (OC-13):
at a degree-3 hub, `(OUT)`'s first disjunct holds at **every** chart point
outside the union of two explicit hypersurfaces — `{C(b,x₁) = C(b,u)}` (which
`repin.star_generic` already rejects everywhere in the harness) and
`{pt(b) ∈ C₀}`. So

> **(OC-8), restated at a degree-3 hub.** (OUT)'s first disjunct is available at
> some hard-stratum target-rank chart point **iff** that locus is not contained
> in `{pt(b) ∈ C₀}`. One explicit line of one panel plane; no rank condition
> left in the statement.

This is §(K-out) (OC-8)'s "relocated and weakened, not crossed" made concrete:
the wall is now a containment question about the target-rank locus, and the
object it must avoid is written down.

---

### Step O12 — (OC-15)/(OC-16): the path-span form, its exact reach, and the M2 computation

> **(OC-15)** `R₁ ⊆ span{C_e : e ∈ π}` for **every** `b`-to-`v*` path `π` of
> `K = (H/X) − e₁`, since `m(u) − m(w) ∈ ⟨C(u,w)⟩` at every hinge and
> `m(b) − m(v*)` telescopes along `π`. With `dim R₁ = 5` this re-proves the
> corollary of (OC-10) (`|π| ≥ 5`) and gives, when some `|π| = 5`, the
> **equality** `R₁ = span{C_e : e ∈ π}` — `R₁` is then a **bracket** object,
> computed from five hinge lines with no rigidity matrix.
> **The converse is REFUTED for `ℓ_min ≥ 6`:** the intersection over all paths
> is then already all of `K⁶` and carries no information. Measured per end over
> POOL-W, `(#paths, dim of the intersection, the intersection equals `R`)`:
> `(1, 5, True) : 38`, `(2, 6, False) : 38`, `(3, 6, False) : 70`. The
> containment itself is asserted per path at all 146 ends.

So the bracket form is exactly the **`ℓ_min = 5` stratum**, and *Step O10*'s
census prices it: **8 of 5226** POOL-CW pairs. That is the honest reach of the
symbolic route, and it is a limit on the *bracket* form only — (OC-11)–(OC-13)
need nothing but `deg_H(b) = 2`.

**The variety, and the computation.** On the `ℓ_min = 5` stratum, with the
chain `b–u–w₂–w₃–w₄–x` (`x ∈ X`) and `pt(a) ∈ M ⊆ Π(b)` giving a second
generator `C(b,a)` of `L_b`,

`L_b ⊆ R₁ ⟺ Δ := det₆[C(b,u), C(u,w₂), C(w₂,w₃), C(w₃,w₄), C(w₄,x), C(b,a)] = 0`

— **one `6×6` Plücker determinant in seven points**, and `R₁`'s far-ness has
dissolved: this is a statement about the **local frame**, inside
`notes/Pencil-strategy.md` §5.3's boundary, which is what item 6 asked for and
what the arc has never had on the `λ` side. `m2/outerwide.m2` computes it on the
gauge slice `Π(b) = {x₄ = 0}`, `Π(c) = {x₃ = 0}`, `pt(c) = e₄`, `pt(a) = e₁`
(legitimate: `PGL(4)` is transitive on (ordered distinct planes, a point of the
second off the meet, a point of the meet), and `Δ`'s vanishing is
`PGL(4)`-invariant), leaving `pt(b)` **free** in `Π(b)` because the locus of
`pt(b)` is the point of the exercise:

> **(OC-16)** *(`M2 --script notes/scripts/m2/outerwide.m2`, M2 1.26.06,
> deterministic)* On that local frame: the five chain hinge lines are
> independent at the generic point; `Δ ≠ 0` **as a polynomial** (degree 10, 148
> terms), so `L_b ⊄ R₁` at the generic point — an identity over the function
> field rather than 38 rational witnesses; and `Δ` factors into **exactly two**
> simple irreducible factors,
>
> `Δ = [a, u, b] · C₀(pt b)`,
>
> the first being the in-panel collinearity bracket (the degenerate case where
> `C(b,u)` and `C(b,a)` fail to span `L_b` at all — a coincident hinge at `b`,
> which `repin.star_generic` rejects) and the second **linear in `pt(b)`**, with
> coefficients involving only `pt(u), pt(w₂), pt(w₃), pt(w₄)`. That second
> factor **is (OC-13)'s `C₀`, in closed form**; the two lines are distinct
> (asserted), and `C₀` passes through neither `pt(u)` nor `pt(a)`. The
> `pt(b)`-freeness of the coefficients is (OC-13)'s "`T_u` and `β_b` do not see
> `pt(b)`" read symbolically — the symbolic certificate of the hub slide's
> legality.

**What (OC-16) does not establish, named as the residue.** It is a statement at
the generic point of the **local frame**. Carrying it to a class shape needs the
**chart-to-frame map to be dominant** — the same step `m2/lambda0.m2` had for
free because (Λ0) is a local-frame statement with the far graph absent, and the
same step §(K-out) (OC-8) says the arc has never established because `λ` is a
far datum. Here the far datum has been compressed to four chain points, so the
dominance question is *smaller* than (OC-8) as recorded, but it is not
discharged: at a shape whose chain interiors are constrained by other hubs'
panels, the frame's parameters are not free. **That is the residue this pass
leaves**, and it is a finite check per chain hub pattern (the census's
`(x₁,x₂,x₃)` histogram is the companion-side analogue).

---

### Confidence verdict (Steps O9–O12)

| | claim | standing |
|---|---|---|
| **(OC-10)** | `χ = 0`, `μ = 1`, `H/X`, `H/Y` isostatic, `A = 0`, `dim R = 5` at every class shape (tight + isostatic + chain ends hubs + `hnoRigid`); hence *What would change this* items 1–2 are unrealizable | **proven-informally** (Step O9: the count-matroid sparsity equivalence that `kslidecomb.shape_ok`'s docstring already records, girth-6, and one boundary case discharged by `hnoRigid` via a rigid-proper-branch-union). Conclusion corroborated at **5226/5226** POOL-CW pairs with the proof's steps asserted per pair; **all four hypotheses shown load-bearing** by eight adversarial non-class graphs (`--adv`), 6 realizing item 1 and 5 item 2, one of them isolating **`hnoRigid`** as the single broken hypothesis. **The first draft of the proof was wrong and this driver refuted it** — treat the hypothesis list as part of the claim |
| **theta remark** | no theta shape with `m ≥ 4` branches is a class shape; θ(3,4,5) is the unique theta member | **proven-informally** (arithmetic + `hnoRigid`); exhaustively driver-checked at `m = 4, 5` (0 shapes over 364 + 5700 tuples) |
| **(OC-11)** | `dim(Rᵢ ∩ β_h) ≥ 2` always; where `= 2` it is a pencil `L_p`; `λᵢ = 0 ⟺ p` on `C(h,xᵢ)`; `L_h ⊆ Rᵢ ⟺ p = pt(h)` | **proven-informally** (two lines of projective geometry on top of (OC-10)); both equivalences asserted per end at **146/146** POOL-W ends |
| **(OC-12)** | at `deg_G(b) = 3`: `C(b,u) ∈ R₁`, `p ∈ C(b,u)`, and off `{p = pt(b)}` `λ₁ = 0` **is** the coincident-hinge condition; so `star_generic ⟹ λ₁ ≠ 0` there | **proven-informally**; asserted per end at all **38** degree-3 ends of POOL-W, **0 violations** of the guard implication. Applies at **3081 of 5226** POOL-CW pairs at the `b` end, **3702** at some end |
| **(OC-13)** | `R₁ = ⟨C(b,u)⟩ ⊕ T_u`, `R₁ ∩ β_b = ⟨C(b,u)⟩ ⊕ (T_u ∩ β_b)`, the bad `pt(b)`-locus is the line `C₀`, and the hub slide is legal when `b` has no hub `G′`-neighbour | **proven-informally**; `dim T_u = 4`, `C(b,u) ∉ T_u`, `R₁ = ⟨C(b,u)⟩ ⊕ T_u`, `dim(R₁∩β) = 1 + dim(T_u∩β)` and `pt(b) ∈ C₀ ⟺ p = pt(b)` all asserted at 38/38 degree-3 ends; legality at **1715 of 5226** pairs at the `b` end |
| **(OC-14)** | `L_h ⊆ R` is **reachable** at θ(3,4,5) — 38 exact, fully nondegenerate, guard-accepted (34/38) chart points with `λᵢ = 0` and **no** coincident hinge at the hub, the escape still holding; hence (OC-7)'s **necessity** claim is refuted | **exhibited by construction** (38 points, deterministic slide targets, zero rejections); the refutation of (OC-7)'s necessity is therefore **settled**, and the corrective dichotomy is (OC-12) |
| **(OC-15)** | `R₁ ⊆` every path's hinge-line span (hence `ℓ_min ≥ 5`), with equality iff some path has length 5; the intersection form is **useless** for `ℓ_min ≥ 6` | containment **proven-informally** and asserted per path at 146/146 ends; the equality's failure **measured** (`(2,6,False) 38`, `(3,6,False) 70`); reach priced at **8 of 5226** pairs |
| **(OC-16)** | `Δ ≢ 0` at the generic point of the length-5-chain local frame; `Δ` has exactly two simple irreducible factors; the non-degenerate one is linear in `pt(b)` and **is** `C₀` | **proven at the generic point of the local frame** (M2 1.26.06, exact, deterministic) — **not** a class statement: the chart-to-frame dominance is not computed |
| **(OC-8)** | the residue, restated: at a degree-3 hub, availability ⟺ the hard-stratum target-rank locus `⊄ {pt(b) ∈ C₀}` | **OPEN**, and now a containment question about the target-rank locus rather than a rank lower bound |

**No gap-map status moves, and class uniformity is untouched.** What moves is
the *content* of two rows: §(K-out)'s (which gains (OC-10)–(OC-16), loses items
1–2 of its *What would change this*, and must record the (OC-7) correction) and
the **(K-wit)** row's *what would close it* cell, whose (OUT) caveat should now
read: *never automatic ((OC-3)), but at a degree-3 hub the bad locus is exactly
the coincident-hinge locus together with one explicit line `C₀` of the panel
((OC-12)/(OC-13)), the first of which every harness gate already rejects and the
second of which is reachable by construction ((OC-14))*.

### What would change this (Steps O9–O12)

1. **A degree-3 hub with `dim(T_u ∩ β_b) = 2`** would make `L_b ⊆ R₁` for
   *every* `pt(b)` of the panel — the shape-level bad case, a codimension-2
   Schubert condition on `T_u ∈ Gr(4,6)` against the fixed 3-plane `β_b`. Not
   seen: `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends. The cheap next
   probe is the same `--wrench` leg over a **shape** pool (POOL-S-style, many
   shapes × few seeds) rather than four habitats × many seeds. **Promoted
   from a hunt to the exact residue (2026-08-19, direction OCON):** at the
   1715 slide-legal `b` ends this condition (in its perp form
   `T_u^{⊥_B} ∩ β_b ≠ 0`) is exactly the failure of availability, an **iff**
   by §(K-out) (OC-21).
2. **A `deg_H(b) ≥ 3` analogue of (OC-12).** At degree `≥ 3` no hinge rotation
   survives in `K`, so `C(b,u) ∈ R₁` fails and the marked direction is not a
   neighbour direction; `dim(R₁ ∩ β_b) = 2` and `p ≠ pt(b)` were nevertheless
   measured at all 108 non-degree-3 POOL-W ends. Whatever replaces `C(b,u)`
   there would extend (OC-12) from 3702 to all 5226 pairs. **Answered in a
   different shape (2026-08-19, direction OCON):** §(K-out) (OC-18) makes a
   `deg_H(b) ≥ 3` analogue of (OC-12) unnecessary for (OC-8) — its
   degree-free sufficient condition covers both ends of every class pair —
   though the marked-direction *formula* this item originally asked for is
   still open.
3. **`R₁` as an iterated span/intersection of hinge lines along `K`'s block
   structure.** (OC-15) kills the naive path-intersection at `ℓ_min ≥ 6`, but
   the two structural cases seen so far both decompose: a serial prefix
   contributes its span, and a branch vertex where two paths diverge should
   contribute the **intersection of the two branch spans** (dimension
   `4 + 4 − 6 = 2` in the one worked example). If that decomposition is a
   theorem, `R₁` is a bracket object at **every** end and (OC-16)'s M2 object
   generalizes off the 8-pair stratum. This is the single highest-value next
   step of this section, and it is a pure screw-system statement about a
   subdivision of a small multigraph — no pencil pin needed.
4. **The chart-to-frame dominance for (OC-16).** Per chain hub pattern, does a
   class shape's pencil chart dominate the local frame? Finitely many patterns;
   `hcard_ok` caps hub-hub adjacency at 2, which bounds the zoo. A negative at
   some pattern would be a class shape with `Δ ≡ 0` — i.e. (OUT)'s first
   disjunct dead on the whole chart, the strongest possible negative and a
   genuine kill for that shape.
5. **Sliding both ends onto their bad lines simultaneously.** `C₀` at the `b`
   end depends on `pt(c)` and vice versa, so the two slides are **coupled** and
   a sequential slide breaks the first condition. A joint solve (two equations,
   four panel parameters) would decide whether **both** disjuncts can die
   identically at one chart point — which is the first thing that would make
   (OUT) *dead*, not merely silent, at a class habitat. Four of the 38
   constructed points already have both outer coordinates zero, but only one
   disjunct dies *identically* there.
6. **Deliberately not attempted, again:** §(K-out) *What would change this* item
   4 (pushing a constructed point to the bad point `p⁺`). The 38 constructed
   points of (OC-14) are a natural launch pad for it — they keep every (Λ0)
   clause and spend only the `pt(b)` freedom — which is a reason to record the
   restraint explicitly rather than let a successor assume it was tried.

### Verification (Steps O9–O12)

`notes/scripts/w4/outerwide.py` (new, untracked; exact ℚ; a `w4/` leaf **above**
`outerline`, which it imports read-only for the welded relative-twist model —
`weld_motions`, `rel_span`, `line_pencil`, `comb_data`, `frame_at`, `clauses` —
so nothing is re-derived) and `notes/scripts/m2/outerwide.m2` (new, untracked;
M2 1.26.06 printed as the second output line; `randomness: none`; an (M0)
convention pin against `exactcore.wedge2`'s `PL` order and `pitch.klein` on a
fixed rational instance, per `notes/scripts/m2/README.md` convention 3).
Nothing existing is modified. From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wide     # (OC-10), POOL-CW + the census
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --adv      # (OC-10)'s minimality, POOL-A
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wrench   # (OC-11),(OC-12),(OC-13),(OC-15), POOL-W
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --slide    # (OC-14), POOL-SL
M2 --script notes/scripts/m2/outerwide.m2                         # (OC-16)
```

Times as run: `--wide` **122 s**, `--adv` **0.2 s**, `--wrench` **87 s**,
`--slide` **75 s**, the M2 driver **0.5 s**. Each fits a single 600 s foreground
budget comfortably; all four Python modes and the M2 driver re-run
**byte-identical** under two different `PYTHONHASHSEED` values (`0` and
`12345`), the *figures-do-not-move* gate (`notes/scripts/README.md`) — which
this pass discharges by the check itself, having **added** two drivers and
modified none.

**Pools, pinned; every figure above is quoted over exactly one of them, and
none is aggregated with POOL-C / POOL-G / POOL-S / POOL-B.**

- **POOL-CW** (`--wide`) — deterministic, no rng: `outer.named_inventory()`
  plus `wide_shapes()`. **5226 (split, companion) pairs over 1693 class
  shapes.** Per-family coverage boundary printed (`EXHAUSTIVE` when the `lmax`
  provably cannot bind, else `BOUNDED`/`CAPPED` with the arithmetic bound).
- **POOL-A** (`--adv`) — **eight** hand-built **non-class** graphs, no rng. Not
  class figures, and labelled as such in the output. Rows 7 and 8 are the ones
  that refuted Step O9's first draft; row 8 isolates `hnoRigid`.
- **POOL-W** (`--wrench`) — the 4 habitats × seeds **200–219**; **73 frames,
  146 companion ends**; `star_generic` reported, not applied.
- **POOL-SL** (`--slide`) — the same habitats × seeds, restricted to degree-3,
  hub-neighbour-free ends (only θ(3,4,5) qualifies); **38 ends**, deterministic
  slide targets from a fixed coefficient ladder.

Per mode, what is asserted:

- `--wide`: per pair, the `5χ` count identity for `H/X`; `χ = 0`; `μ = 1`;
  `def(H/X) = def(H/Y) = 0`; no vertex outside a weld with two weld-neighbours;
  `ℓ_min ≥ 5` at both ends; `G` tight and `def(G) = 0`; the histogram's
  uniformity; girth `≥ 6` on the first 250 pairs' shapes.
- `--adv`: per graph, which of (OC-10)'s **eight** named hypotheses it breaks —
  computed, not asserted by hand: `count(H) = 3`, `G` tight, `def(G) = 0`,
  `b, c` hubs, `hnoRigid` (by brute-force enumeration of rigid proper subgraphs
  with min degree `≥ 2`, which in a subdivision are exactly the branch-unions),
  girth `≥ 6`, `χ = 0`, no 2-into-weld vertex — and that **every** graph
  exhibiting a hit breaks at least one. That assertion is the one that fired on
  Step O9's first draft.
- `--wrench`: per end, `dim R = 5`; `β_h` 3-dimensional and totally
  `B`-isotropic; `dim(R ∩ β_h) ≥ 2`; the pencil centre `p` on both meet lines;
  (OC-11)'s two equivalences; at degree-3 ends `C(b,u) ∈ R`, `p ∈ C(b,u)`,
  `R = ⟨C(b,u)⟩ ⊕ T_u`, `dim T_u = 4`,
  `dim(R ∩ β) = 1 + dim(T_u ∩ β)`, `pt(b) ∈ C₀ ⟺ p = pt(b)`, and
  `λᵢ = 0 ⟺` the coincidence; (OC-15)'s containment per path; the chain
  equality at `ℓ_min = 5`; and the guard implication `star_generic ⟹ λᵢ ≠ 0`
  at every degree-3 end.
- `--slide`: at every slid point the whole acceptance battery re-run from
  scratch on the modified placement (panels, adjacent-point distinctness,
  closed-star ranks, target rank, `dim R_a = 1`, panels non-parallel,
  `dim V_bc = 3`, `rank{C_i} = 4`, `λ` a point of `P(S*)`, `pt(a)` on `M`, all
  four nondeg conjuncts, the (Λ0a)–(Λ0f′) battery); that every on-`C₀` point
  has `λᵢ = 0` **and** `L_h ⊆ R`; that every off-`C₀` point has neither; and
  that `λ` is proportional to **neither** `p⁺` **nor** `q` and
  `Q(z(t)) ≢ 0` at every constructed point (the sentence that would be the
  headline if it failed).
- `outerwide.m2`: (M0) the convention pin; the chain's independence at the
  generic point; `Δ ≠ 0`; exactly two simple irreducible factors; the
  collinearity bracket divides `Δ`; the complementary factor is linear in
  `pt(b)` and not a multiple of the collinearity line.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics and the M2 layer — **never** a substitute for
Lean (`DESIGN.md` *Formalize everything the argument uses*). Nothing in
`outerline.py`, `outer.py`, `lambda.py` or `repin.py` was modified; all are
read.

### Steps O13–O18 (2026-08-19, sixth fan-out, direction OCON) — (OC-8)'s **hard-stratum target-rank qualifier is FREE**: the stratum is an *open* subvariety of the chart ((OC-17)), so §(K-frame) (FR-7)'s un-owned irreducibility object is **struck**, one chart point *anywhere* suffices, and the sufficient condition that point has to satisfy is **`H/X` infinitesimally rigid** ((OC-18)) — degree-free, at **both ends of every class pair** — which lands (OC-8)'s residue in the **same object class as §(K-ann) (ANH-R1)**; (OC-8) stays **OPEN**, no gap-map status moves

Driver `notes/scripts/w4/ocon.py` (new this pass; imports `outerline` and
`outerwide` read-only, modifies nothing); labels **(OC-17)–(OC-22)**. Everything
cited that this pass did not mint is qualified: **(OUT)**, **(Λ0a)–(Λ0i)** are
§(K-Λ)'s; **(FR-1)**/**(FR-3)**/**(FR-4)**/**(FR-6)**/**(FR-7)** are §(K-frame)'s;
**(ANH-9)**/**(ANH-R1)** are §(K-ann)'s; **(S1)** is §(K-slide)'s; **(D4)** is
§(K-dom)'s; **(K-tight)** *Step 2*'s items are §(K-tight)'s. POOL-C / POOL-G /
POOL-S / POOL-B / POOL-CW / POOL-A / POOL-W / POOL-SL are this section's earlier
pools and **nothing below is aggregated with them**.

Write `Z` for the **hard-stratum target-rank locus** of the pencil chart of
`G′ = G − v + ab` at an eligible split — the set (OC-8) quantifies inside.

Five things, in the order they change the reading of (OC-8).

- **(OC-17) — `Z` is an OPEN subvariety of the chart, not a stratum.** At
  **every** legal chart point, with no genericity anywhere,
  `dim R_a = corank(G′) − s₀`: the stress space of `G′` maps *onto* `R_a`, and
  its kernel is exactly the stress space of `G′ − ab = G − v`, whose dimension
  is `s₀`. With `index(G) = 0` (tight) and `def(G′) = 0` (§(K-tight) *Step 2*'s
  declared scope) that reads `dim R_a = 1 − s₀`, so
  `Z = {rank R(G′) = 6(|V(G)| − 2) − def(G′)} ∩ {rank R(G − v) = 5|E(G − v)|}`
  — an intersection of **two maximal-rank conditions**, hence Zariski open.
  Consequence, and the reason this matters: **an open subset of an irreducible
  variety is irreducible and dense.** §(K-frame) **(FR-7)**'s named residual
  ingredient — *"the smallest object is the hard-stratum target-rank locus of
  the (shape, split) chart … whose irreducibility nobody owns"* — is therefore
  **owned as soon as the chart is**, and §(K-ann) **(ANH-9)(ii)** /
  §(K-slide) *Step 1(e)* / §(K-dom) **(D4)** already own that. The one thing
  (OC-17) does *not* supply is `Z ≠ ∅`, which is a separate input — see (OC-19).
- **(OC-18) — a degree-free sufficient condition, at both ends of every pair:
  `H/X` infinitesimally rigid.** `W₁ = {m(b) − m(v*)}` in the welded framework
  `H/X` (with `e₁` **present**) is exactly (OC-1)'s space, and (OC-1) gives
  `λ₁ = 0 ⟺ dim W₁ = 1`. If `H/X` is infinitesimally rigid at the chart point
  then every motion is trivial, so `W₁ = 0`, so **`λ₁ ≠ 0`, hence `C₁ ∉ R₁`,
  hence `L_b ⊄ R₁`** — a witness of (OC-8)'s first disjunct at that point.
  `{H/X infinitesimally rigid}` is `{rank = 6|V(H)| − 6}`, a **maximal-rank
  hence open** condition, and (OC-10)(e) proves `def(H/X) = 0`, so it is
  non-empty in the **ambient** placement space. **No degree hypothesis is
  used** — only (Λ0a) and `μ = 1`, which (OC-10) proves at every class pair —
  so it applies at **both ends of every class pair**, where (OC-12)
  additionally needs `deg_G(b) = 3` and (OC-13)'s slide additionally needs no
  hub `G′`-neighbour. For comparison, over POOL-CW's **labelled** pairs
  (harness README §4 convention 7 — labelled instances, never a class-level
  ratio): **5226 of 5226** against (OC-12)'s 3081 (`b` end) / 3702 (some end)
  and (OC-13)'s slide-legal 1715. §(K-out) *What would change this (Steps
  O9–O12)* **item 2 is answered, though not in the shape it asked for**: it
  wanted the replacement for
  `C(b,u)` at `deg_H(b) ≥ 3` — the *marked direction*'s formula — and (OC-18)
  instead makes the marked direction unnecessary for (OC-8)'s purpose.
- **(OC-19) — the reduction: (OC-8) factors into three inputs, one of which is
  not (OUT)'s to pay.** At a class (shape, split, length-4 companion), (OC-8)'s
  `b`-end disjunct **follows from**: **(a)** `Z ≠ ∅`; **(b)** the pencil chart
  of `G′` is irreducible; **(c)** *one* chart point — **anywhere on the chart,
  with no rank-stratum condition on it** — at which `H/X` is infinitesimally
  rigid. Proof: (b) makes the open sets of (a) and (c) dense, and two dense
  opens of an irreducible variety meet. **Input (a) is a prerequisite of the
  whole (K-tight) criterion, not of (OUT)**: §(K-tight) *Step 2* item 3 records
  that `dim R_a = 0` forces uniform failure of routes A **and** B at every
  placement, so a shape with `Z = ∅` loses the KT-route escape entirely,
  independently of (OUT). What is genuinely (OUT)'s is (c), and it is
  **one-point decidable per (shape, split)** by one exact rank computation at
  one rational chart point — the `λ`-side analogue of §(K-ann) **(ANH-9)(iii)**.
- **(OC-20)/(OC-21) — the bad case, in its perp form, with `x₁` deleted from
  the statement.** `β_h` is a **maximal** totally `B`-isotropic 3-space, so
  `β_h^{⊥_B} = β_h` and for any subspace `T`,
  `dim(T ∩ β_h) = dim T + 3 − 6 + dim(T^{⊥_B} ∩ β_h)`. At `dim T_u = 4` that is
  `dim(T_u ∩ β_h) = 1 + dim(T_u^{⊥_B} ∩ β_h)`, so **(OC-13)'s shape-level bad
  case `dim(T_u ∩ β_b) = 2` is exactly `T_u^{⊥_B} ∩ β_b ≠ 0`** — one 2-space of
  wrenches meeting one 3-space of panel lines, a Schubert condition written
  down. Separately, `R₁^{⊥_B} = ⟨ρ⟩` is one wrench and (OC-11)'s marked point
  `p` is the point of `Π(h)` cut out by `B(ρ, ·)|_{β_h}` — **and `ρ` is
  measured NOT `B`-isotropic at 4/4 degree-3 POOL-OC ends**, so the tempting
  reading *"`p = ρ ∩ Π(h)`"* is valid only in the non-generic decomposable
  case and is recorded here as the trap it is. And (OC-21): at a degree-3 hub
  with `pt(b), pt(u), pt(a)` non-collinear, `L_b = ⟨C(b,u), C(b,a)⟩` with
  `C(b,u) ∈ R₁` free, so **`L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁`** — the condition is about
  the **split-edge** hinge line and `x₁` has left the statement altogether.
- **(OC-22) — where the residue lands: the same object class as (ANH-R1).**
  After (OC-19), (OC-8)'s own content is *"the welded far framework `H/X` is
  infinitesimally rigid at one pencil chart point"*. §(K-ann) **(ANH-R1)** is
  *"`H/P − β` is infinitesimally rigid at the pencil placement"*, and
  `H/P = (H/X)/(b ∼ v*)`, so the two objects sit on one contraction tower. The
  arc had recorded three independent arrivals at the *same missing technology*
  ((ANH-9)(iii)'s class-uniform independent-point recipe: §(K-grid)'s residual,
  §(K-ann)'s, §(K-out) (OC-16)'s); this is the first arrival at the **same kind
  of object**, which is what makes §(K-frame)'s (FR-1)+(FR-4) machinery apply
  to (OC-8) verbatim rather than by analogy.

**Verdict, stated at the strength the work supports.** **(OC-8) stays OPEN and
no gap-map status moves.** What moves is its *shape*: the hard-stratum
target-rank qualifier — the thing §(K-frame) (FR-7) named as the un-owned
ingredient and §(K-frame) (FR-6) spent 4 of its 8 colourings satisfying — is
**free**, and the residue is a pencil-rigidity statement about a welded far
framework, degree-free and one-point decidable. **Class uniformity is untouched**,
and the honest boundary is (OC-19)'s input (c) at *every* class shape, which no
argument here supplies.

---

### Step O13 — (OC-17): the hard stratum at target rank is an **open** subvariety of the chart

Notation is §(K-out)'s *Standing notation* plus: `G′ = G − v + ab`
(`outer.split_data`'s `Gp`), `s₀` = the **row corank** of the shared rows
(the edges of `G − v = G′ − ab`; `repin.py:252`, `s0 = 5·|E| − rank`), `R_a` the
boundary-load space of §(K-tight) *Step 2* item 2 (`outer.stratum_at`),
`index(G) := 5|E(G)| − 6(|V(G)| − 1)` (§(K-ind) *Standing notation*), `corank(G′)`
the dimension of `G′`'s stress space at the placement.

> **(OC-17)** *(proven-informally)* At **every** chart point with
> `pt(a) ≠ pt(b)` — no genericity, no target-rank hypothesis:
>
> `dim R_a = corank(G′) − s₀`.  (†)
>
> At a target-rank point `corank(G′) = index(G) + 1 + def(G′)`, so for a class
> shape (`index(G) = 0`) inside §(K-tight) *Step 2*'s scope (`def(G′) = 0`),
> `dim R_a = 1 − s₀` and
>
> `Z := {target rank} ∩ {dim R_a = 1}`
> ` = {rank R(G′) = 6(|V(G)| − 2) − def(G′)} ∩ {rank R(G − v) = 5|E(G − v)|}`,
>
> an intersection of **two maximal-rank conditions** — hence a **Zariski-open**
> subset of the pencil chart.
>
> **Corollary (the one that matters).** If the chart is irreducible and
> `Z ≠ ∅`, then `Z` is **dense open and irreducible**. So §(K-frame) **(FR-7)**'s
> *"the smallest object is the hard-stratum target-rank locus … whose
> irreducibility nobody owns"* is **struck**: its irreducibility is the
> chart's, which §(K-ann) **(ANH-9)(ii)**, §(K-slide) *Step 1(e)* and §(K-dom)
> **(D4)** already own and consume.

*Proof of (†).* `R_a` is by definition the image of the map
`σ : {stresses of G′} → K⁶`, `λ ↦ Σ_{r ∈ ab-rows} λ_r · r|_{a-block}`
(`outer.stratum_at`, `repin.seed_probe`). The five `ab` rows restricted to the
`a` block are the five rows of that hinge and span `C(ab)^⊥`, of dimension 5,
whenever `C(ab) ≠ 0` — i.e. whenever `pt(a) ≠ pt(b)`, which
`IsNondegPencilRealization` conjunct 2 supplies. So the composite
`λ ↦ λ|_{ab} ↦ σ(λ)` is injective on the `ab`-coordinates, and
`ker σ = {λ : λ|_{ab} = 0}` = the stress space of `G′ − ab = G − v`, of dimension
`s₀`. Rank–nullity gives (†). ∎

*Proof of the two displayed forms.* At target rank,
`corank(G′) = 5|E(G′)| − [6(|V(G′)| − 1) − def(G′)] = index(G′) + def(G′)`, and
`index(G′) = index(G) + 1` (§(K-ind) *Step I2*), which is
`notes/Pencil-W4-informal.md`'s recorded count identity
`corank(G′) = index(G) + 1 + def(G′)`. With `index(G) = 0`, `def(G′) = 0`:
`dim R_a = 1 − s₀`, so on the target-rank locus `dim R_a = 1 ⟺ s₀ = 0`. And
`s₀ = 0` is `rank R(G − v) = 5|E(G − v)|`, the maximum a matrix with that many
rows can have; `rank R(G′) = 6(|V(G)| − 2) − def(G′)` is likewise the maximum
(rank is bounded above by the generic rank). Both are non-vanishing of a
maximal minor, hence open. ∎

*Two remarks, each recorded because a one-line quotation will get it wrong.*

*(i)* **§(K-tight) *Step 2* item 3 is not corrected, it is completed.** That
item states `dim R_a = index(G) + 1 − s₀` "at a target-rank seed"; (†) carries
the extra `+ def(G′)`, which vanishes inside *Step 2*'s own declared scope
(`def(G) = def(G′) = 0`). Outside that scope the `def(G′)` term is live, and
(†) itself needs neither scope clause nor target rank.

*(ii)* **`Z` open does not make `Z` big, and it does not make (OC-8) true.**
`Z` is cut out by two *non-vanishing* conditions on the chart, so it is open —
but a nonempty open of an irreducible variety is dense, and that is the whole
force of the corollary. `Z ≠ ∅` is a genuinely separate input; it is **measured
`≠ ∅`** at every probed (split, companion) pair (POOL-S: 270 frames over 90
splits, *Step O7*) and at all four habitats, and the arc's only recorded
`dim R_a = 0` chart points are §(K-flank) *F5(d)*'s five `P21` seeds — at a
shape carrying **no** length-4 `bc`-companion, so not a counterexample to
(OC-8), which is vacuous there.

---

### Step O14 — (OC-18): `H/X` infinitesimally rigid at a chart point ⟹ (OUT)'s first disjunct, at **every** class pair

> **(OC-18)** *(proven-informally; asserted per end)* Let a class (shape,
> split, length-4 companion) be given, and let a chart point be one at which
> the **welded** framework `H/X` — `X = {x₁,x₂,x₃,c}` welded into one body
> `v*` by explicit equality rows, with `e₁ = bx₁` **present** — is
> **infinitesimally rigid** (`dim Mot(H/X) = 6`). Then at that point
>
> `λ₁ ≠ 0`, hence `C₁ ∉ R₁`, hence `L_b ⊄ R₁`.
>
> `{H/X infinitesimally rigid}` = `{rank = 6|V(H)| − 6}` is a **maximal-rank,
> hence Zariski-open** subset of the chart; and (OC-10)(e) proves
> `def(H/X) = 0`, so it is **nonempty in the ambient placement space**.
> Symmetrically at the `c` end with `H/Y`.
>
> **Coverage.** The statement uses **no degree hypothesis** — only (Λ0a) and
> (OC-1). By (OC-10) `μ₁ = μ₄ = 1` at **every class pair**, so (OC-18) applies
> at **both ends of every class (split, companion) pair**, with no census
> needed. For comparison against the two degree-gated predecessors, over
> POOL-CW's **labelled** pairs (harness README §4 convention 7 — labelled
> instances, never a class-level ratio): (OC-18) **5226 of 5226**, (OC-12)
> **3081** (`b` end) / **3702** (some end), (OC-13)'s slide legal at **1715**
> (`b` end).

*Proof.* `H/X` infinitesimally rigid means every infinitesimal motion is a
global (trivial) twist, which assigns the same screw to every body; so
`m(b) − m(v*) = 0` for every motion, i.e. `W₁ = {m(b) − m(X)} = 0`. (OC-1)'s
chain reads `λ₁ = 0 ⟺ C₁ ∈ V_bc ⟺ dim W₁ = 1`, so `λ₁ ≠ 0`. With `μ₁ = 1`,
(OC-1) also gives `λ₁ = 0 ⟺ C₁ ∈ R₁`, so `C₁ ∉ R₁`; and `C₁ = C(b, x₁) ∈ L_b`
(the pencil of lines through `pt(b)` in `Π(b)`, since `pt(x₁) ∈ Π(b)`), so
`L_b ⊄ R₁`. The rank statement: `dim Mot ≥ 6` always, so `dim Mot = 6` is
`rank = 6|V(H)| − 6`, maximal. ∎

**What this is and is not.** It is **not** a proof of (OUT)'s hypothesis: the
pencil chart is a proper subvariety of the placement space, and (OC-2)'s
warning — *"the combinatorial half does not deliver availability"* — applies
verbatim to `def(H/X) = 0`. (OC-3) stands unchanged: the bad locus is nonempty
on every class shape's chart, so no count can discharge (OUT). What (OC-18)
supplies is a **transfer-shaped** criterion in place of a chart-geometric one:
the ambient-generic fact is `def(H/X) = 0`, the chart-side question is whether
its *open* consequence survives to one chart point, and the object doing the
work is a rigidity statement rather than a containment.

*Measured, POOL-OC (`--check`).* At all **12** companion ends of the 6 frames:
`(dim Mot(H/X), H/X rigid, dim W_i, λ_i = 0)` takes exactly two values —
`(6, True, 0, False) : 11` and `(7, False, 1, True) : 1`. Both
`λ_i = 0 ⟺ dim W_i = 1` (a re-check of (OC-1)) and the implication
`H/X rigid ⟹ λ_i ≠ 0` are **asserted per end**, not observed as rates; the one
`(7, False, 1, True)` end is a naturally-occurring instance that the condition
must and does reject, and `--control` adds three **constructed** ones.

---

### Step O15 — (OC-19): the reduction, and the input that is not (OUT)'s to pay

> **(OC-19)** *(proven-informally, conditional on the two named inputs)* Fix a
> class (shape, split, length-4 companion) and write `X` for the pencil chart
> of `G′`. Suppose
>
> **(a)** `Z ≠ ∅` — the chart carries some hard-stratum target-rank point;
> **(b)** `X` is irreducible (§(K-ann) (ANH-9)(ii); §(K-slide) *Step 1(e)*'s
>   *"a tower of affine-linear fibers: free hub points, normals in
>   hub-dependent linear subspaces, interiors in panels / meet lines / free
>   space"*, already consumed by §(K-dom) (D4));
> **(c)** **some** chart point — anywhere on `X`, with **no** rank-stratum
>   condition attached to it — has `H/X` infinitesimally rigid (or `H/Y`, for
>   the `c` end).
>
> Then **(OC-8) holds at that (shape, split)**: `Z` contains a point with
> `L_b ⊄ R₁` (resp. `L_c ⊄ R₄`).
>
> *Proof.* By (OC-17) and (a), `Z` is a nonempty open of `X`; by (OC-18) and
> (c), `{H/X inf. rigid}` is a nonempty open of `X`. By (b) both are dense, so
> they meet; at a common point (OC-18) gives `L_b ⊄ R₁` and membership of `Z`
> gives the stratum. ∎
>
> **Corollary (one-point decidability).** (c) is decided by **one exact rank
> computation at one rational chart point** — the `λ`-side analogue of §(K-ann)
> **(ANH-9)(iii)**, and of §(K-grid) (GR-7)'s remark (i) on the `τ` side.

**The re-attribution, which is the strategically useful half.** Input (a) is
**not (OUT)'s**. §(K-tight) *Step 2* item 3 records that `dim R_a = 0` means
*"failure at every placement"* on routes A and B alike, so a (shape, split)
with `Z = ∅` has already lost the KT-route escape before (OUT) is consulted;
(a) is a hypothesis of the **whole (K-tight) criterion**, shared by every route
on the (K-wit) row. Input (b) is a standing, thrice-consumed fact of the arc.
So the *incremental* content of (OC-8) at a (shape, split) is exactly (c) —
and (c) has no `λ`, no `V_bc`, no `L_b`, no `C₀`, no `x₁`-pencil and no
stratum in it.

**Two things this immediately buys, both about existing landed work.**

*(i)* **§(K-frame) (FR-6)'s stratum filter is unnecessary for (OC-8).** (FR-6)
reports *"4 of 8 colourings land on `(rank, dim R_a) = (54, 1)` — target rank,
hard stratum"* and treats exactly those four as (OC-8) witnesses. Under
(OC-19) **any** of the 8 that carries the open condition is a witness, because
the point need not lie in `Z`. (Unchanged, and still riding: a grid point is a
chart point of `G′` only modulo §(K-frame) **(FR-4)**'s named gap, the (GR-5)
restatement at `G′`. (OC-19) removes the *stratum* requirement from a grid
witness; it does not touch that gap.) Whether the other four in fact carry it is not
measured here — the (FR-6) follow-on battery is out of this pass's scope — but
the *requirement* is gone, and with it the (FR-7) foothold of §(K-frame) *What
would change this* item (iii) (*"certify generic `dim R_a = 1` along that
irreducible family — the first named irreducible subvariety inside the
hard-stratum locus"*), which (OC-17) makes **unnecessary rather than open**.

*(ii)* **The pointwise pools keep exactly the standing they had.** POOL-G's 46
frames and POOL-S's 270 frames were already *in* `Z` with `λ₁ ≠ 0`, so they
were already per-shape witnesses of (OC-8) at their (shape, split); nothing
about their reading changes, and §(K-out)'s *Verdict* sentence — *"what (OUT)
as a route needs is uniform availability"* — stands verbatim. (OC-19) widens
what a **recipe** may use, not what the samples proved.

**The adversarial control, and why the argument cannot be shortened.** `Z ≠ ∅`
alone does **not** give (OC-8): `--control` rebuilds (OC-14)'s hub slide onto
`C₀` at θ(3,4,5) and lands, at seeds 200/201/202, three exact chart points that
are **in `Z`** (`(rank, dim R_a) = (54, 1)`), `star_generic`-accepted, carrying
**no** coincident hinge at `b`, and with `L_b ⊆ R₁` — at which `H/X` is
**flexible** (`dim Mot = 7`), so (OC-18)'s open condition correctly rejects
them. `Z` genuinely meets the bad divisor; the reduction must run through
openness **plus** irreducibility **plus** a witness, and no two of the three
suffice.

---

### Step O16 — (OC-20)/(OC-21): the perp form of the shape-level bad case, and the disappearance of `x₁`

> **(OC-20)** *(proven-informally; asserted per end and at 200 synthetic
> spans)* `β_h = Λ²Π̂(h)` is a **maximal** totally `B`-isotropic 3-space of
> `Λ²K⁴`, so `β_h^{⊥_B} = β_h`, and therefore for **any** subspace `T`
>
> `dim(T ∩ β_h) = dim T + 3 − 6 + dim(T^{⊥_B} ∩ β_h)`.
>
> At `dim T_u = 4` ((OC-13)) this is `dim(T_u ∩ β_h) = 1 + dim(T_u^{⊥_B} ∩ β_h)`,
> so **(OC-13)'s shape-level bad case is exactly**
>
> `L_b ⊆ R₁ for every pt(b) of Π(b)` ⟺ `T_u^{⊥_B} ∩ β_b ≠ 0`,
>
> a 2-dimensional space of wrenches meeting a 3-dimensional space of panel
> lines. Separately, `dim R₁ = 5` makes `R₁^{⊥_B} = ⟨ρ⟩` one wrench; then
> `dim(R₁ ∩ β_h) = 3 ⟺ ρ ∈ β_h`, and where the meet is 2-dimensional
> (OC-11)'s marked point `p` is the point of `Π(h)` **cut out by the
> functional `B(ρ, ·)|_{β_h}`**.
>
> **Trap, recorded because the pass walked into it.** `ρ` is *not* in general
> decomposable: `B(ρ, ρ) ≠ 0` at **4 of 4** degree-3 POOL-OC ends. So the
> tempting reading *"`p = ρ ∩ Π(h)`, the point where the annihilator line
> pierces the panel"* holds **only** on the non-generic locus `{B(ρ,ρ) = 0}`;
> the functional form above is the correct one everywhere.
>
> *Proof.* `dim(A ∩ B) = dim A + dim B − dim(A + B)` and
> `dim(A + B) = 6 − dim(A^{⊥_B} ∩ B^{⊥_B})` for the nondegenerate `B`; put
> `B := β_h` and use `β_h^{⊥_B} = β_h` (a maximal totally isotropic subspace of
> a nondegenerate 6-dimensional form is self-perpendicular; `β_h` is
> 3-dimensional and totally isotropic — both asserted per end by
> `outerwide.panel_line_space`). For `ρ`: `R₁` is a hyperplane, so `R₁^{⊥_B}`
> is a line; `R₁ ∩ β_h = β_h ∩ ρ^{⊥_B}` is the kernel of the functional
> `B(ρ, ·)` restricted to `β_h`, of dimension 2 unless that functional is zero,
> i.e. unless `ρ ∈ β_h^{⊥_B} = β_h`. A 2-dimensional subspace of `β_h` is the
> pencil of exactly one point of `Π(h)` ((OC-11)). ∎
>
> *A reading, marked as one (the algebra above is what the driver tests).* A
> wrench pairs to zero with a relative twist exactly when the corresponding
> single bar is redundant, so `T_u^{⊥_B}` is the **2-dimensional space of
> wrenches `(H/X) − b` transmits from `u` to `v*`**, and the shape-level bad
> case says one of them is a **pure force along a line of `b`'s own panel**.

> **(OC-21)** *(proven-informally; asserted per degree-3 end)* At a degree-3
> hub `b` (so `deg_H(b) = 2` with other `H`-neighbour `u`) at which
> `pt(b), pt(u), pt(a)` are **not collinear** — the bracket `[a,u,b] ≠ 0`,
> (OC-16)'s first factor, a coincident hinge pair at `b` that
> `repin.star_generic` rejects:
>
> `L_b = ⟨C(b,u), C(b,a)⟩` and `C(b,u) ∈ R₁` ((OC-12)), hence
> **`L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁`**.
>
> The condition is about the **split-edge** hinge line `C(b,a)` alone: `x₁`,
> whose pencil direction was the whole subject of (OC-3), has **left the
> statement**. (This is what (OC-16)'s `Δ = det₆[…, C(b,a)]` was already
> computing on the `ℓ_min = 5` stratum; (OC-21) is the same fact with no
> stratum hypothesis.)
>
> **The slide dichotomy, sharpened.** `T_u`, `β_b` and hence `C₀` do not see
> `pt(b)` ((OC-13)), so along any chart move of `pt(b)` inside `Π(b)`, `C₀` is
> fixed. Therefore, with (OC-19):
>
> - **`b` has no hub `G′`-neighbour** (`pt(b)` free in `Π(b)`, 2 dimensions;
>   **1715 of 5226** POOL-CW pairs at the `b` end): (OC-8)'s `b`-end disjunct
>   holds **iff** `T_u^{⊥_B} ∩ β_b = 0` at some chart point — a line cannot
>   contain a plane, so `pt(b) ∈ C₀` cannot hold identically.
> - **`b` has exactly one hub `G′`-neighbour `h`** (`pt(b)` confined to the
>   line `N = Π(b) ∩ Π(h)`, 1 dimension): the same, with the extra clause
>   `N ≠ C₀`. *(Proven-informally on the same chart-legality reading (OC-13)
>   uses for its own slide; **not driver-tested here**, and its census share is
>   **not measured** — the recorded numbers give only `deg_G(b) = 3` at 3081
>   and hub-neighbour-free-at-`b` at 3227, whose overlap is the 1715 above.)*
> - **`b` has two hub `G′`-neighbours** (`hcard` caps it there): `pt(b)` is
>   pinned and the slide is unavailable; (OC-19) still applies, via any other
>   chart move or via (OC-18).

---

### Step O17 — (OC-22): the residue's object class, and the exact reach of the grid form

> **(OC-22)** *(assessment; no driver)* After (OC-19), the incremental content
> of (OC-8) at a (shape, split) is
>
> *the welded far framework `H/X` is infinitesimally rigid at **one** pencil
> chart point*,
>
> which is the **same kind of statement** as §(K-ann) **(ANH-R1)** (*`H/P − β`
> is infinitesimally rigid at the pencil placement*), on the same contraction
> tower: `H/P = (H/X)/(b ∼ v*)`, so `H/X` rigid at a point implies `H/P` rigid
> there (welding two bodies of a rigid framework preserves rigidity). Both are
> **rank lower bounds on a smaller welded far graph at a pencil placement**;
> both are one-point decidable ((ANH-9)(iii) and (OC-19)); both are consumed by
> §(K-frame) **(FR-1)** with the chart's own irreducibility. The arc had
> recorded three arrivals at the *same missing technology*; this is the first
> arrival at the **same kind of object**, so §(K-frame)'s (FR-4) transport
> recipe applies to the (OC-8) side **verbatim** rather than by analogy.

**The grid form, and exactly how far it reaches — a derivation, deliberately
not a battery.** At a σ-fixed grid point of `G′` — a chart point modulo
§(K-frame) **(FR-4)**'s named (GR-5)-at-`G′` gap, untouched here — §(K-frame)
(FR-3)(iii) makes span-membership in a set of hinge lines combinatorial, and (OC-15) gives
`R₁ ⊆ span{C_e : e ∈ π}` **pointwise** for every `b`-to-`v*` path `π` of
`K = (H/X) − e₁`. Hence a purely combinatorial **sufficient** criterion:

> `C(b,a) ∉ span{C_e : e ∈ π}` for some path `π` ⟹ `C(b,a) ∉ R₁` ⟹
> `L_b ⊄ R₁`, and at a grid point that is: `π` contributes **≤ 2 distinct
> colouring components** in `C(b,a)`'s family, and `C(b,a)`'s component is not
> one of them.

**Its reach is bounded by alternation, and that is the combinatorial
explanation of the `ℓ_min = 5` boundary.** `closure.alternation_classes` (the
admissibility constraint §(K-clos) (AC-2) and §(K-frame) (FR-4) use) forces the
two edges at a **`G′`-degree-2 body** into opposite families. A path all of
whose interior bodies have `G′`-degree 2 therefore alternates strictly, giving
`⌈ℓ/2⌉` and `⌊ℓ/2⌋` maximal same-family runs; unless two runs of one family
land in the *same* colouring component, the span has dimension
`min(3, ⌈ℓ/2⌉) + min(3, ⌊ℓ/2⌋)` — which is **5 at `ℓ = 5`** (matching (FR-6)'s
measured *"the alternating chain always splits 3–2 with distinct lines"*) and
**6, i.e. vacuous, from `ℓ = 6` on** (matching (OC-15)'s measured
`(2, 6, False) : 38`, `(3, 6, False) : 70`). So the bracket route's `8 of 5226`
reach is not an accident of the `ℓ_min = 5` stratum: it is what strict
alternation forces. **What a general-`ℓ` grid certificate must supply, named
exactly:** a path carrying **interior hubs with two same-family consecutive
edges** (an immediate component merge, and by §(K-clos) (AC-9) a σ-fixed hub of
degree ≥ 3 always has such a pair somewhere), or a global colouring in which
two runs of one family share a component. This is *What would change this
(Steps O9–O12)* item 3 (the block decomposition of `R₁`) restated on the grid
side; it is **not** attempted here, and it is **not** §(K-frame) *What would
change this* item (ii)'s battery, which this pass leaves alone.

---

### Step O18 — where this leaves (OC-8) (hand-off)

**Status, unchanged: (OC-8) is OPEN, class uniformity is untouched, and no
gap-map status moves.** The (K-wit) row's (OUT) caveat gains one clause and
loses none.

What a successor should pick up, in descending value:

1. **Input (c) of (OC-19), class-uniformly** — *`H/X` infinitesimally rigid at
   one pencil chart point, at every class (shape, split, length-4 companion)*.
   This is the whole residue. It is **one-point decidable per triple**, so a
   census is a set of per-triple proofs, and the missing piece is a **recipe**.
   The two recipes the arc owns are §(K-frame) (FR-4)'s pattern colouring
   (which transports a *combinatorial* criterion to an exact chart point) and
   §(K-ann) (ANH-9)(iii)'s one-point discharge. Because (OC-22) puts input (c)
   in (ANH-R1)'s object class, **(FR-4) applies to it verbatim** — the open
   question is whether a pattern colouring exists making `H/X` rigid at the
   grid point, which is a **rank** condition and therefore *not* as cheap as
   (FR-R1) was. Say so plainly: this is (GR-15)-flavoured, not (FR-R1)-flavoured.
2. **Input (a), `Z ≠ ∅`, as a statement in its own right.** It is a
   prerequisite of the *whole* (K-tight) criterion and it is currently carried
   implicitly by every route on the (K-wit) row. It is measured at 90/90
   POOL-S splits, and the only recorded `dim R_a = 0` chart points anywhere in
   the arc are §(K-flank) *F5(d)*'s five `P21` seeds. Making it explicit —
   *at every class (shape, split), the chart carries a target-rank point with
   `s₀ = 0`* — is cheap to state and would clean up several rows at once.
3. **`T_u^{⊥_B} ∩ β_b = 0`** ((OC-20)) at the **1715** slide-legal `b` ends,
   where (OC-21) makes it an **iff**. This is *What would change this (Steps
   O9–O12)* item 1 promoted from a hunt to the exact residue at those ends;
   still measured `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends and 4/4
   POOL-OC ones, i.e. `T_u^{⊥_B} ∩ β_b = 0` at 4/4.
4. **The one-hub-neighbour extension of the slide** ((OC-21)'s second bullet)
   and its census share — a cheap `--wide`-style leg, not run here.
5. **Deliberately not attempted, again**, and recorded so a successor does not
   assume otherwise: §(K-out) *What would change this* item 4 (pushing a
   constructed point to `p⁺`), item 5's coupled two-end slide, and every
   §(K-frame) *What would change this* item (ii)–(iv).

---

### Verification (Steps O13–O18)

`notes/scripts/w4/ocon.py` (new, untracked at draft time; exact ℚ, stdlib only;
a `w4/` leaf **above** `outerwide`, which it imports read-only — `panel_line_space`,
`far_twist_space`, `hub_free_end`, `collinear`, `klein_point_on`,
`pencil_centre`, `slide_targets`, `slide_placement`, `check_slid`, `wrench_row`
— together with `outerline` (`frame_at`, `weld_motions`, `rel_span`,
`line_pencil`); everything else is a catalogued §1 primitive. **Nothing existing
is modified**: `outerline.py`, `outerwide.py`, `outer.py`, `repin.py`,
`pitch.py`, `lambda.py`, `widened.py` are all read.) From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --validate   # (OC-20)'s algebra, POOL-OV
PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --check      # (OC-17),(OC-18),(OC-20),(OC-21), POOL-OC
PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --control    # (OC-17)/(OC-19)'s controls, POOL-OZ
```

Times as run: `--validate` **0.3 s**, `--check` **17 s**, `--control` **4 s** —
21 s in total, a derivation pass's budget. All three re-run **byte-identical**
under two different `PYTHONHASHSEED` values (`0` and `12345`), the
*figures-do-not-move* gate (`notes/scripts/README.md`), which this pass
discharges by the check itself: it **added** one driver and modified none
(`git status --porcelain notes/scripts/` shows exactly the one new file).

**Pools, pinned; every figure above is quoted over exactly one of them, and
none is aggregated with POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A /
POOL-W / POOL-SL.**

- **POOL-OV** (`--validate`) — synthetic exact-ℚ subspaces of `K⁶` from
  `random.Random(20260819)` (seed printed), plus **two constructed witnesses**.
  No graph, no placement.
- **POOL-OC** (`--check`) — the 4 `lambda.habitat_specs` habitats × placement
  seeds **200–201**, accepted exactly as `outerline.frame_at` accepts them.
  **6 frames, 12 companion ends, 4 of them degree-3.** Deliberately tiny: this
  is a derivation pass and every sentence under test is an **identity**, so the
  pool is a witness set, not a sample — **no figure here is a rate**.
- **POOL-OZ** (`--control`) — θ(3,4,5) × placement seeds **200–214**,
  **unfiltered** (15 placements), plus **3 constructed** chart points from the
  (OC-14) hub slide onto `C₀` rebuilt here.

Per mode, what is asserted:

- `--validate`: `β = Λ²` of a 3-space is 3-dimensional, totally `B`-isotropic
  and `β^{⊥_B} = β`; the (OC-20) identity
  `dim(A ∩ β) = dim A + 3 − 6 + dim(A^{⊥_B} ∩ β)` at **200** random spans of
  every dimension 1–5, with the `(dim A, dim(A ∩ β))` histogram printed; the
  **constructed** bad case (a 4-space `T ⊆ C^{⊥_B}` for a panel line `C ∈ β`)
  has `T^{⊥_B} ∩ β ≠ 0` and `dim(T ∩ β) = 2`; and the **negative control** —
  60 random 4-spaces with `T^{⊥_B} ∩ β = 0`, every one with `dim(T ∩ β) = 1`
  (README §4 convention 6).
- `--check`: per frame, `index(G) = 0`, `def(G′) = 0`, `def(G − v) = 4`,
  `corank(G′) = index(G) + 1 + def(G′) = 1`, **(†) `dim R_a = corank(G′) − s₀`**
  against `outer.stratum_at`'s independently-computed `dim R_a`, and both
  maximal-rank readings (`rank R(G′) = tgt`, `rank R(G − v) = 5|E(G − v)|`);
  ledger `(index, def(G′), corank(G′), s₀, dim R_a) = (0,0,1,0,1)` at **6 of 6**.
  Per companion end (12 of 12): (OC-1)'s `λ_i = 0 ⟺ dim W_i = 1`, and
  **(OC-18)**'s `H/X` rigid ⟹ `λ_i ≠ 0`, both as per-end asserts; histogram
  `(6, True, 0, False) : 11`, `(7, False, 1, True) : 1`. Per degree-3 end (4 of
  4): `dim T_u = 4`, `dim T_u^{⊥_B} = 2`, **(OC-20)**'s
  `dim(T_u ∩ β) = 1 + dim(T_u^{⊥_B} ∩ β)`, (OC-13)'s
  `dim(R₁ ∩ β) = 1 + dim(T_u ∩ β)`, `dim R₁^{⊥_B} = 1`,
  `dim(R₁ ∩ β) = 3 ⟺ ρ ∈ β`, the marked point `p` agreeing with `ρ`'s panel
  trace (and with `outerwide.pencil_centre`), `p = pt(h) ⟺ L_h ⊆ R₁`, and
  **(OC-21)**'s `L_h ⊆ R₁ ⟺ C(h,a) ∈ R₁` with `[a,u,h] ≠ 0` asserted.
  Histogram `(dim(R∩β), dim(T∩β), dim(T^{⊥_B}∩β), L_h ⊆ R, non-collinear,
  ρ B-isotropic, hub-free) = (2, 1, 0, False, True, **False**, True) : 4` — the
  `False` in the sixth slot is the (OC-20) trap, measured.
- `--control`: at all 15 unfiltered placements, (†) is asserted wherever the
  placement reaches target rank, together with `dim R_a = 1 ⟺ s₀ = 0` there;
  the histogram is printed and the boundary is stated as one (**no sampled
  placement of this window falls off `Z`** — which is what a dense open `Z`
  predicts, and which means the *off-`Z`* side of the control is **not**
  exercised by sampling). The **constructed** half is the one that bites: the
  (OC-14) slide onto `C₀` lands at seeds 200/201/202 at points that
  `outerwide.check_slid` accepts — so target rank, `dim R_a = 1`,
  `dim V_bc = 3`, `rank{C_i} = 4`, `pt(a)` on `M`, star-span green — with
  `L_b ⊆ R₁` and **no** coincident hinge at `b`, `star_generic` accepting, and
  `dim Mot(H/X) = 7` (**not** rigid), all asserted. That is (OC-18)'s
  adversarial witness and (OC-19)'s "`Z ≠ ∅` is not enough" control in one
  object.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean
(`DESIGN.md` *Formalize everything the argument uses*).

---

### Confidence verdict (Steps O13–O18)

| | claim | standing |
|---|---|---|
| **(OC-17)** | `dim R_a = corank(G′) − s₀` at every legal chart point; hence, at `index(G) = 0`, `def(G′) = 0`, `Z` is an intersection of two maximal-rank loci and so **Zariski open**; its irreducibility is the chart's | **proven-informally** (rank–nullity on the stress space, plus the landed count identity `corank(G′) = index(G) + 1 + def(G′)`); the identity and both maximal-rank readings **asserted per frame** at 6/6 POOL-OC frames and at every target-rank POOL-OZ placement |
| **(OC-18)** | `H/X` infinitesimally rigid at a chart point ⟹ `λ₁ ≠ 0` ⟹ `L_b ⊄ R₁`; the condition is maximal-rank hence open, ambient-nonempty by (OC-10)(e); **no degree hypothesis** — both ends of 5226/5226 pairs | **proven-informally** (two lines on top of (OC-1)); the implication **asserted per end** at 12/12 POOL-OC ends, with one naturally-occurring rejecting instance and **three constructed** ones (`--control`) |
| **(OC-19)** | (OC-8) at a (shape, split) follows from (a) `Z ≠ ∅` + (b) chart irreducibility + (c) one chart point with `H/X` rigid; one-point decidable; (a) is the **whole (K-tight) criterion's** input, not (OUT)'s | **proven-informally — (b) proven, §(K-chart) (CH-1)** (2026-08-19, direction CIRR: the chart is irreducible, ℚ-rational, and the constant-fibre-dimension restriction (ANH-9)(ii)/(S1)(e)/(D4) each relied on costs nothing, per (CH-4)/(CH-6)/(CH-7)). **(a) and (c) are inputs, not results**: neither is established class-uniformly here |
| **(OC-20)** | `β_h^{⊥_B} = β_h` gives `dim(T ∩ β_h) = dim T − 3 + dim(T^{⊥_B} ∩ β_h)`; so (OC-13)'s shape-level bad case is `T_u^{⊥_B} ∩ β_b ≠ 0`; `R₁^{⊥_B} = ⟨ρ⟩` and `p` is `ρ`'s panel trace **as a functional** | **proven-informally**; asserted at 200 synthetic spans + a constructed bad case + 60 negative controls, and per degree-3 end at 4/4. **`ρ` is measured non-decomposable at 4/4** — the "`p = ρ ∩ Π(h)`" reading is refuted as a general one |
| **(OC-21)** | `L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁` at a degree-3 hub off `{[a,u,b] = 0}` — `x₁` leaves the statement; and the slide dichotomy makes availability **iff** `T_u^{⊥_B} ∩ β_b = 0` at the 1715 slide-legal `b` ends | equivalence **proven-informally**, asserted per degree-3 end at 4/4; the hub-free dichotomy **proven-informally** on (OC-13)'s own legality reading; the **one-hub-neighbour extension is proven-informally and NOT driver-tested**, its census share **not measured** |
| **(OC-22)** | (OC-8)'s residue is in §(K-ann) (ANH-R1)'s object class (same contraction tower, both one-point decidable), so (FR-4)'s transport applies verbatim; and strict alternation is why the grid/bracket form stops at `ℓ_min = 5` | **assessment** (argument, no driver). The alternation half is a derivation from `closure.alternation_classes`'s landed constraint and reproduces (FR-6)'s and (OC-15)'s measured 3–2 / `(·, 6, False)` figures |
| **(OC-8)** | the residue | **OPEN** — reshaped, not closed; class uniformity untouched |

**No gap-map status moves. Class uniformity of (OUT), and of `hK`, is exactly
where it was.** What moves is the *content* of two rows: §(K-out)'s (which gains
(OC-17)–(OC-22)) and **(K-wit)**'s (OUT) caveat, which gains the sentence that
the genericity argument (OC-3) demands needs **no hard-stratum qualifier**.

### What would change this (Steps O13–O18)

1. **A class shape with `Z = ∅` at a length-4-companion-bearing split** would
   make (OC-8) **false** there — and would simultaneously kill routes A and B
   at that split by §(K-tight) *Step 2* item 3, so it is a (K-tight) event, not
   an (OUT) event. Nothing in the arc exhibits one; §(K-flank) *F5(d)*'s `P21`
   seeds are the only recorded `dim R_a = 0` chart points and `P21` carries no
   length-4 companion. **The cheap probe:** extend `--control`'s unfiltered leg
   to a POOL-S-style shape pool and report the `s₀` histogram per (shape,
   split) rather than per seed.
2. **A failure of chart irreducibility** ((OC-19) input (b)) would break this
   pass, §(K-slide) (S1)(e), §(K-dom) (D4) and §(K-ann) (ANH-9)(ii) at once. It
   is the arc's most-consumed un-driver-tested fact; a pass that *writes it
   down* — the tower of affine-linear fibres, with the constant-fibre-dimension
   clause made explicit — would be cheap insurance for four sections.
   **Cross-direction convergence (2026-08-19, sixth fan-out):** FRES landed
   the *other* half of this same fact independently, the same day, without
   either direction seeing the other's — its (ANH-9)(ii) correction records
   that "irreducible rational parametrization" is literally true only on
   `place_pencil_general`'s **constant-fibre-dimension locus**, not
   unconditionally. Consumers (this pass included) are undisturbed because
   every one needs only irreducibility, which the constant-fibre-dimension
   restriction still supplies — but the fact itself is now **load-bearing for
   at least two independent routes and owned by nobody**: written down once,
   not four times.
3. **A class (shape, split) at which `H/X` is infinitesimally rigid at NO chart
   point.** By (OC-19) that is exactly the failure of (OUT)'s first disjunct
   there, and by (OC-10)(e) it would be a chart-vs-ambient separation at a
   *rigidity* statement — the sharpest possible negative on this side, and a
   genuine kill for that shape's first disjunct (the `c` end would still have
   to be checked). Not seen: `H/X` rigid at 11 of 12 POOL-OC ends, the twelfth
   being a `λ = 0` end.
4. **A `deg_H(b) ≥ 3` formula for the marked direction** — §(K-out) *What would
   change this (Steps O9–O12)* item 2 in its original shape. (OC-18) makes it
   unnecessary for (OC-8), but (OC-11)–(OC-13)'s *geometry* (which point `p`,
   which line `C₀`) is still confined to degree-3 ends, and the (OC-21)
   dichotomy with it.
5. **The (OC-22) grid criterion, run** — a pattern-colouring existence question
   for `H/X` rigidity at a σ-fixed grid point. **This one carries a rank
   condition** and is therefore (GR-15)-flavoured rather than (FR-R1)-flavoured;
   it is named here as the successor, not commissioned, and it overlaps
   §(K-frame) *What would change this* item (ii), which this pass leaves alone.
6. **The `X°` refinement of (OC-19), if a converse is ever wanted.** (OC-19)'s
   direction is sufficient only. On the dense open `X° ⊆ X` where
   `rank M_K` and `rank[M_K; P]` are both maximal, `{L_b ⊆ R₁}` is *closed*, so
   (OC-8) there is **iff** one point of `X°` has `L_b ⊄ R₁`; nothing in this
   pass needs the converse and it is stated only so a successor does not
   re-derive it.

### Steps O19–O24 (2026-08-19, seventh fan-out, direction ZNEQ) — (OC-19) input **(a)** written down as a statement in its own right, and it **factors**: `s₀ = 0` is *independence of the far framework `H`* alone ((OC-23)), which is a **necessary condition for `hK` at the shape** ((OC-24)) and is **dominated by §(K-grid) (GR-10)** — one grid point per shape covering **every** split at once ((OC-28)); the target-rank half is the (K-tight) criterion **one split down** ((OC-25)), whose failure is a **codimension-2 Schubert jump** of the far framework's relative twist space ((OC-26), whose first closed form this pass **refutes by construction** and replaces); measured with an exact-ℚ **witness at 138/138** (shape, split) pairs ((OC-27)). **Input (a) is OPEN as a class-uniform statement and is NOT an independent gap; no gap-map status moves.** (Written before §(K-chart) landed; CIRR's **(CH-1)**/**(CH-2)** then *proved* this pass's one structural input and its ℚ-descent step — see *Step O24*'s convergence note.)

Driver `notes/scripts/w4/zneq.py` (new this pass; imports `ocon`, `outerline`,
`outer`, `flanks`, `kslidecomb`, `widened`, `repin` **read-only** and modifies
nothing); labels **(OC-23)–(OC-28)**, Steps **O19–O24**. Everything cited that
this pass did not mint is qualified per `notes/Pencil-labels.md` clause L3:
**(OUT)**, **(Λ0a)–(Λ0i)** are §(K-Λ)'s; **(FR-4)**/**(FR-6)**/**(FR-7)** are
§(K-frame)'s; **(ANH-9)**/**(ANH-R1)** are §(K-ann)'s; **(S1)** is §(K-slide)'s;
**(D4)** is §(K-dom)'s; **(CH-1)**/**(CH-2)**/**(CH-5)** are §(K-chart)'s
(direction CIRR, landed **the same day and after this pass's mathematics was
written** — see the convergence note in *Step O24*); **(GR-5)**/**(GR-9)**/**(GR-10)** are §(K-grid)'s;
**(AC-3)**/**(AC-7)** are §(K-clos)'s; **(PC-OBS)** is §(K-pure)'s; *F5(d)* is
§(K-flank)'s; **(K-tight)** *Step 2*'s items are §(K-tight)'s. POOL-C / POOL-G /
POOL-S / POOL-B / POOL-CW / POOL-A / POOL-W / POOL-SL / POOL-OV / POOL-OC /
POOL-OZ are earlier pools of this section and **nothing below is aggregated with
them**; POOL-G and POOL-S are pinned and are neither re-sampled nor extended.

Standing notation is §(K-out)'s, plus: `orient`'s split frame is the chain
`b — v — a — c` with `v`, `a` interior (degree 2) and `b`, `c` hubs
(`widened.orient`); `G′ = G − v + ab`; `H = G − v − a` (§(K-out)'s `H`);
`σ := corank R(H)` at a chart point; `Z` = the hard-stratum target-rank locus of
the pencil chart of `G′`; `M = Π(b) ∩ Π(c)` the panels' meet line, with `M̂ ⊆ K⁴`
its 2-dimensional cone and `t` an affine parameter on it;
`D := {m(b) − m(c) : m ∈ Mot(H)}` the relative twist space of `H`;
`U_H := D^⊥ = {u : ⟨u, m(b) − m(c)⟩ = 0 ∀ m ∈ Mot(H)}` — §(K-tight) *Step 2*'s
obstruction space `U` at the substituted instance `(G′, a)`.

Six things, in the order they change the reading of input (a).

- **(OC-23) — the pendant-edge reduction: `s₀ = corank R(H)` at *every* chart
  point.** `E(G − v) = E(H) ∪ {ac}` and `a` has degree **one** in `G − v`, so the
  five `ac` rows, restricted to the `a` block, span `C(ac)^⊥` (5-dimensional
  whenever `pt(a) ≠ pt(c)`, which `IsNondegPencilRealization` conjunct 2
  supplies) and every `G − v` stress vanishes on them. Hence the `s₀` half of
  input (a) contains **no `v`, no `a`, no split edge, no `λ`, no `V_bc`, no
  stratum**: it is *independence of the far framework `H`*, the same object
  §(K-out) has been about since *Step O1*. This is (OC-17)'s own one-line
  argument, run on a pendant edge instead of on the `ab` rows.
- **(OC-24) — the dichotomy, and the sharp corollary the dispatch did not
  anticipate.** With the chart irreducible — **§(K-chart) (CH-1)(a)**, landed by
  CIRR the same day, and unconditional at `Γ = G′` — `Z ≠ ∅`
  ⟺ `{target rank} ≠ ∅` **and** `{σ = 0} ≠ ∅` on the chart, each open, each
  one-point decidable. And **`{σ = 0} = ∅` on the chart implies `hK` is FALSE at
  that shape**: `H ⊆ G`, so a self-stress of `H` at every chart point is a
  self-stress of `G` at every pencil realization, and `G` is tight with
  `def(G) = 0`, so `G` never attains `6(|V| − 1) = 5|E(G)|`. **So the `s₀` half
  of input (a) is a *necessary condition* for the phase's own target** — it
  cannot fail at a class shape without disproving the pencil conjecture there.
  That **refines the dispatch's decisive-negative wording**: a `Z = ∅` shape via
  the `s₀` half is a **PENCIL event** (a disproof at that shape, §(K-flank)
  direction-A pivot class), strictly stronger than the (K-tight) event; a
  `Z = ∅` shape via the target-rank half is the **(K-tight) event** the dispatch
  named, and only that branch.
- **(OC-25) — input (a) is an instance of the (K-tight) criterion, one split
  down the chain.** §(K-tight) *Step 2* item 1 at the substituted instance
  `(G, v, a, b) ↦ (G′, a, b, c)` gives, at every chart point with
  `pt(a) ∉ {pt(b), pt(c)}`,

  > `corank R(G′) = σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)`,  `dim D = 3 + σ`,
  > `dim U_H = 3 − σ`,

  so a chart point lies in `Z` **iff** `σ = 0` **and** the two placement
  functionals `⟨·, C(ab)⟩`, `⟨·, C(ac)⟩` are linearly independent on the
  3-space `U_H` — *Step 2* item 1's own attainment criterion. The prerequisite of
  the criterion **is** the criterion, one split down; and the regress
  **terminates in exactly one step**, because `orient`'s chain has exactly two
  interior vertices and `G′ − a = H`. Consequence: every §(K-tight) tool applies
  to input (a) verbatim — and the P21 `s₀`-jump seeds are its `dim U = 1`
  analogue one level up (measured: `dim U_H = 2`, `dim D = 4` there).
- **(OC-26) — the `pt(a)`-fibre over `M`, and the closed form of failure.**
  `pt(a)` is confined to `M` (its two `G′`-neighbours are the hubs `b`, `c`), and
  `C(ab)`, `C(ac)` are **affine-linear in `t`** along `M`. At `σ = 0` the
  functional matrix is `2 × 3`, so its **three** `2 × 2` minors are quadratics in
  `t` and the bad set is their **common** zero locus — three conditions on one
  parameter, hence **generically empty**, and when empty the *whole* `pt(a)`-fibre
  over that `H`-part lies in `Z`. Bad at **every** `t` has an exact closed form —
  and it is a **disjunction**, not the single containment the first derivation
  gave (that reading is **refuted by construction** below, POOL-ZQ Case C):

  > bad at every `t` ⟺ `dim(D ∩ (M̂ ∧ W)) ≥ 3` **or** `M̂ ∧ w ⊆ D` for some
  > `w ∈ W`,  where `W = ⟨pt(b)^, pt(c)^⟩`.

  Both disjuncts force `dim(D ∩ (M̂ ∧ W)) ≥ 2` — a **codimension-2** Schubert
  jump in `Gr(3, 6)` off the generic value 1. Measured (POOL-ZF): `ℚ[t]`-GCD of
  the three minors of degree **0 at 32 of 32** `σ = 0` frames (*no* bad `t` in
  **any** extension of ℚ, so the entire meet line is good), with
  `dim(D ∩ (M̂ ∧ W)) = 1` and no pencil inside `D` at all 32 — and the closed
  form asserted **against** the GCD test per frame.
- **(OC-27) — the measurement the dispatch asked for, run.** POOL-ZN, the
  unfiltered leg extended to a POOL-S-*style* shape pool: **138 (shape, split)
  pairs — 90 carrying a length-4 companion plus 48 others — every one of them
  carrying an exact-ℚ *certified* chart point of `Z`**, and the first
  guard-accepted draw sufficed at every one. `Z ≠ ∅` is therefore **proven
  individually** at each of the 138: one point suffices, so neither openness nor
  irreducibility is consumed. **No miss, hence no candidate (K-tight) event and
  no candidate PENCIL event in scope.**
- **(OC-28) — the `s₀` half is *dominated* by §(K-grid) (GR-10), one grid point
  per shape covering every split.** `H` omits **both** `v` and `a`, and the
  `G`-chart and the `G′`-chart impose *identical* constraints on the `H`-data
  (hub points free, hub normals constrained only by their `H`-neighbours,
  `H`-interiors in their hub-neighbours' panels), so their `H`-projections have
  the same image and an `H`-part extends to a `G′`-chart point by re-placing
  `pt(a)` anywhere on `M` off a proper closed subset. That extension is
  **performed as a construction**, guards and all: at **30 of 30** (shape,
  split) pairs a target-rank chart point of the whole graph `G` transfers to a
  guard-accepted `G′`-chart point which is **in `Z`** (POOL-ZT). **No rank claim
  crosses, so §(K-frame) (FR-4)'s gap is *not* invoked**. At a configuration
  where `G`
  attains the Tay target, `corank R(G) = 0`, hence `σ = 0` — and that is exactly
  what §(K-grid) **(GR-9)** *proves* wherever its both-block tree-triple
  colouring exists, which **(GR-10)** measures at **907/907** shapes of
  §(K-grid)'s pool. So: **(GR-10) ⟹ the `s₀` half of input (a) at every tight
  class shape and every eligible split**, from *one* grid point per shape. The
  converse boundary is exhibited, not assumed: at `P21` — a (K-res) shape that
  **fails `hnoRigid`** — the arc's five recorded `dim R_a = 0` seeds have
  `s₀ = σ = 1`, so `{σ = 0}` is a **proper** open with a complement that is not
  thin in the sampler's rational range (5 of 35), and the class predicate's
  `hnoRigid` conjunct is the only tool the arc has against it.

**Verdict, stated at the strength the work supports.** **Input (a) stays OPEN as
a class-uniform statement, and no gap-map status moves.** What changes is that it
is **no longer an unowned prerequisite**: it factors into a half that is a
*necessary condition* for the phase's own target and is dominated by §(K-grid)'s
own residual, and a half that is the (K-tight) criterion one split down whose
failure has a closed form. **Class uniformity is untouched**, and the honest
boundary is that neither half is *proven* class-uniformly here: the `s₀` half
waits on (GR-10) (or on any class-uniform independence statement for `H` at
pencil placements — the hard direction of `Pencil-strategy.md` §2.3), and the
target-rank half waits on a class-uniform non-containment `M̂ ∧ w ⊄ D`.

---

### Step O19 — (OC-23): `s₀` is `corank R(H)`, at every chart point

> **(OC-23)** *(proven-informally; asserted per frame)* At **every** legal chart
> point of `G′` with `pt(a) ≠ pt(c)` — no genericity, no target-rank hypothesis —
>
> `s₀ = corank R(G − v) = corank R(H)`,  `H = G − v − a`.
>
> Hence, with (OC-17), `dim R_a = corank(G′) − corank R(H)`, and inside
> §(K-tight) *Step 2*'s scope (`index(G) = 0`, `def(G′) = 0`) the second defining
> condition of `Z` is exactly **`H` has independent rows**.

*Proof.* `orient` gives `deg_G v = 2` with neighbours `a`, `b`, `deg_G a = 2`
with neighbours `v`, `c`. So `E(G − v) = E(G) ∖ {va, vb} = E(H) ∪ {ac}` and `a`
is incident, in `G − v`, to the single edge `ac`. Let `λ` be a row dependency of
`R(G − v)`. Its `a`-block reads `Σ_{i} λ_{(ac)i} · r_i(C(ac))|_a = 0`, and the
five rows of a hinge restricted to one endpoint block span `C(ac)^⊥`, which is
5-dimensional and their images independent whenever `C(ac) ≠ 0`, i.e.
`pt(a) ≠ pt(c)`. So `λ_{(ac)i} = 0` for all `i`, and `λ` restricted to `E(H)` is
a dependency of `R(H)` — bijectively, since any `R(H)` dependency extends by
zero. ∎

*Two remarks.* *(i)* This is the **same** lemma (OC-17) proves for the `ab` rows
(*Step O13*): "five hinge rows on one block span a 5-space, so a stress cannot
touch a degree-1 body". (OC-17) uses it to peel `ab`; (OC-23) uses it to peel the
pendant `ac`. Together they say the whole `dim R_a` ledger of a class split is
carried by `H`. *(ii)* The reduction is **exact and unconditional**, so it applies
at off-`Z` points too, which is what makes *Step O24*'s P21 leg a test of it
rather than of its scope: at the five `s₀`-jump seeds `corank R(H) = 1` as well.

*Exact, per frame:* asserted at **32/32** POOL-ZF frames, at **138/138**
POOL-ZN witnesses, and at **all 35** valid POOL-ZR (P21) seeds — including the
five that reject.

---

### Step O20 — (OC-24): the dichotomy, and why the `s₀` half cannot fail without disproving `hK`

> **(OC-24)** *(proven-informally; the first clause conditional on chart
> irreducibility)* Fix a class (shape, split) and let `X` be the pencil chart of
> `G′`.
>
> **(i)** `{target rank}` and `{σ = 0}` are Zariski-open in `X` ((OC-17),
> (OC-23)), and `X` **is** irreducible (§(K-chart) **(CH-1)(a)**, unconditional
> at `Γ = G′` for a class shape and an eligible split), so
>
> `Z ≠ ∅ ⟺ {target rank} ≠ ∅ and {σ = 0} ≠ ∅`,
>
> and each is **witnessed** by **one** exact rank computation at **one** rational
> chart point — the *positive* answer is one-point certifiable, the negative is
> not (it quantifies over the chart). A single point satisfying **both** needs no
> irreducibility at all.
>
> **(ii)** *(unconditional in `X`; needs the shared-sub-tower clause of (OC-28)
> only to move between the two charts)* If `{σ = 0} = ∅` — `H` dependent at every
> chart point — then **`hK` is false at that shape**. Consequently the `s₀` half
> of input (a) is a **necessary condition** for `hK` at the shape.

*Proof.* (i) is (OC-17) plus (OC-23) plus "two dense opens of an irreducible
variety meet", exactly (OC-19)'s argument — with the irreducibility now
**proven** rather than cited (§(K-chart) (CH-1)(a)), so (OC-19)'s input (b) has
stopped being a hypothesis of this reduction as well. For (ii): `E(H) ⊆ E(G)`, so a
self-stress of `H` at a placement is a self-stress of `G` at that placement. `G`
is tight (`index(G) = 0`) with `def(G) = 0`, so its Tay target is
`6(|V(G)| − 1) = 5|E(G)|` — **full row rank**, i.e. `hK`'s conclusion at `G` is
`corank R(G) = 0`. If `H` is dependent at every point of the `H`-image of the
chart, and (OC-28)'s shared-sub-tower clause identifies that image with the
`H`-image of `G`'s own chart, then `corank R(G) ≥ 1` at every pencil realization
of `G` and the Tay target is never attained. ∎

**Why this matters more than the reduction does.** The dispatch's framing —
correct as far as it goes — is that a `Z = ∅` class shape at a
length-4-companion-bearing split is *"a (K-tight) event, not an (OUT) event"*,
because §(K-tight) *Step 2* item 3 makes `dim R_a = 0` a uniform failure of routes
A and B. (OC-24)(ii) splits that event in two, and the two halves have very
different consequences:

| branch of `Z = ∅` | mechanism | consequence |
|---|---|---|
| **`{σ = 0} = ∅`** — `H` dependent at every chart point | a self-stress of the far framework, i.e. §(K-pure) (PC-OBS)'s *combinatorially certifiable* direction | **`hK` FALSE at that shape.** A **PENCIL event** — the phase's target theorem is false, §(K-flank) direction-A pivot class. Strictly stronger than a (K-tight) event |
| **`{target rank} = ∅`** with `{σ = 0} ≠ ∅` — identical badness on `M` ((OC-26)) | the Schubert containment `M̂ ∧ w ⊆ D` | **(K-tight) event**, exactly as the dispatch names it: (OC-8) false there, routes A and B dead **at that split**; `hK` at the shape untouched (another split, or §(K-grid)'s route, may still carry it) |

Nothing in the arc exhibits either branch at a class shape. **Surface the first
branch to the coordinator in those words**: the `s₀` half of input (a) is a
necessary condition for the theorem, so the only way it bites is by being false,
and then the phase pivots rather than re-routes.

**And the converse reading, which is the strategically useful one.** Because the
`s₀` half is *implied by* `hK` at the shape, it can never be the *binding*
obstruction: any proof of `hK` at a shape — the grid route included — hands it
over for free. That is what *Step O24* makes quantitative.

---

### Step O21 — (OC-25): input (a) is §(K-tight) *Step 2* item 1, one split down

> **(OC-25)** *(proven-informally — a substitution instance of §(K-tight) *Step 2*
> item 1, itself proven-informally; asserted per frame, and this is the first
> time that item has been driver-tested at a substituted instance)* At every
> chart point of `G′` with `pt(a) ∉ {pt(b), pt(c)}`:
>
> **(a)** `corank R(G′) = σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)`;
> **(b)** `dim D = 3 + σ` and `dim U_H = 3 − σ`;
> **(c)** hence, inside §(K-tight) *Step 2*'s scope,
>
> > the chart point lies in `Z` ⟺ `σ = 0` **and** the two functionals
> > `u ↦ ⟨u, C(ab)⟩`, `u ↦ ⟨u, C(ac)⟩` are linearly **independent** on the
> > 3-space `U_H`,
>
> which is *Step 2* item 1's attainment criterion with `(G, v, a, b)` replaced by
> `(G′, a, b, c)`.

*Proof.* §(K-tight) *Step 2* item 1 reads: at the split of a degree-2 vertex `x`
with neighbours `y`, `z`, `corank R(Γ) = corank R(Γ − x) + dim(U ∩ C(xy)^⊥ ∩
C(xz)^⊥)` with `U = {u : ⟨u, m(y) − m(z)⟩ = 0 ∀ m ∈ Mot(Γ − x)}`, valid at any
placement with `pt(x) ∉ {pt(y), pt(z)}`. Apply it with `Γ = G′`, `x = a`,
`{y, z} = {b, c}`: `a` has degree 2 in `G′` (its `G`-neighbour `v` is replaced by
`b`), `G′ − a = H`, and `U = U_H`. That is (a). For (b): *Step 2* item 3's count,
at the same substitution, gives `dim{m(y) − m(z)} = 4 + corank − index(Γ)` with
`index(G′) = index(G) + 1 = 1` (§(K-ind) *Step I2*), i.e. `dim D = 3 + σ`, and
`U_H = D^⊥` gives `dim U_H = 3 − σ`. For (c): at target rank
`corank R(G′) = index(G′) + def(G′) = 1`, so with `σ = 0` and `dim U_H = 3`, (a)
forces `dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥) = 1`, i.e. the two functionals cut `U_H`
down by 2, i.e. they are independent on it; conversely independence gives
`corank R(G′) = 1`, which *is* target rank since `5|E(G′)| − 1 = 6(|V(G)| − 2)`.
And `σ = 0` is `s₀ = 0` by (OC-23). ∎

**The regress terminates in one step, and that is a fact about the frame, not
luck.** `orient` requires `deg a = 2` and `deg c ≥ 3`, so the chain carrying the
split is `b — v — a — c` with exactly **two** interior vertices; peeling `v`
gives `G′`, peeling `a` gives `H`, and `H` has no further degree-2 vertex on that
chain to peel. A longer chain would iterate — which is worth recording, because a
naive reading of "the criterion's prerequisite is the criterion" suggests an
infinite regress and there is none here.

**Relation to KT's route B, so the two are not confused.** KT's `p₃` (pp.
684–691, §(K-tight) *Step 1*) uses the isomorphism `ρ : G^{vc}_a ≅ G^{ab}_v`
between two splits of the **same** `G`; (OC-25) is a different move — the split
of the **already-split** `G′` at `a` — and it produces the `H`-level obstruction
space, not a second route. They are compatible: both are the observation that
`v` and `a` are an adjacent degree-2 pair.

*Exact, per frame:* (a), (b), (c) asserted at **32/32** POOL-ZF frames, at the
first POOL-ZN witness of each family, and — the informative case — at the
**five** POOL-ZR (P21) `σ = 1` seeds, where `(dim U_H, dim D, rank of the two
functionals, dim W) = (2, 4, 2, 0)`: `corank R(G′) = 1 + 0 = 1`, target rank
with `dim R_a = 0`. The ledger holds off `Z` as well as on it.

---

### Step O22 — (OC-26): the `pt(a)`-fibre over the meet line, and the closed form of failure

> **(OC-26)** *(proven-informally; asserted per frame, with all three
> configurations CONSTRUCTED and 60 negative controls)* Fix a chart point with
> `σ = 0`, let `t` parametrize `M = Π(b) ∩ Π(c)` (the locus of `pt(a)`), write
> `W = ⟨pt(b)^, pt(c)^⟩` for the hub line's 2-space and
> `Φ : M̂ ∧ W → U_H^*`, `x ↦ ⟨·, x⟩|_{U_H}`, so that `ker Φ = D ∩ (M̂ ∧ W)`. Then
>
> **(i)** `C(ab)` and `C(ac)` are **affine-linear in `t`**, so the functional
> matrix of (OC-25)(c) is a `2 × 3` matrix of affine functions and its three
> `2 × 2` minors are quadratics in `t`. The **bad set** — the `pt(a)` for which
> the point leaves `Z` — is their **common** zero locus: three conditions on one
> parameter, hence **generically empty**. When it is empty the *whole*
> `pt(a)`-fibre over that `H`-part lies in `Z`.
>
> **(ii)** *(an equivalence, and a disjunction)* the bad set is **all** of `M`
> ⟺ `rank Φ ≤ 1` (i.e. `dim(D ∩ (M̂ ∧ W)) ≥ 3`) **or** `M̂ ∧ w ⊆ D` for some
> `w ∈ W`. Both disjuncts force `dim(D ∩ (M̂ ∧ W)) ≥ 2`, a **codimension-2**
> Schubert condition in `Gr(3, 6)` (generic value 1).
>
> **(iii)** the weaker degeneracy `D ∩ (M̂ ∧ pt(b)^) ≠ 0` (the `b`-side
> functional pair dependent on `U_H`) makes **exactly one** point of `M` bad, not
> the whole line.

*Proof.* (i) `pt(a) = P₀ + t·P_d` with `{P₀, P_d}` a basis of `M̂`, so
`C(ab) = pt(a)^ ∧ pt(b)^ = P₀ ∧ pt(b)^ + t · P_d ∧ pt(b)^` and likewise for
`C(ac)`; the pairing is linear, so each matrix entry is affine in `t` and each
`2 × 2` minor is a quadratic. By (OC-25)(c) the point is in `Z` iff the matrix
has rank 2, i.e. iff some minor is nonzero.

(ii) `{P₀ ∧ pt(b)^, P_d ∧ pt(b)^, P₀ ∧ pt(c)^, P_d ∧ pt(c)^}` is a basis of the
4-space `M̂ ∧ W` (using `M̂ ∩ W = 0`, i.e. `pt(b), pt(c) ∉ M`, which (Λ0d)
supplies), and `Φ` sends it to `(f₀, f₁, g₀, g₁)` where
`f_t = ⟨·, C(ab)⟩|_{U_H} = f₀ + t f₁` and `g_t = ⟨·, C(ac)⟩|_{U_H} = g₀ + t g₁`.
*(⟸)* If `rank Φ ≤ 1` all four lie in one line of `U_H^*`, so
`f_t ∧ g_t = 0` for every `t`. If `M̂ ∧ w ⊆ D = U_H^⊥` with
`w = pt(c)^ − c·pt(b)^` then `g_t = c f_t` for every `t`, likewise bad.
*(⟹)* Bad at every `t` says `f_t ∧ g_t = 0` in `Λ²U_H^*` identically, i.e.
`f₀ ∧ g₀ = 0`, `f₁ ∧ g₁ = 0`, `f₀ ∧ g₁ + f₁ ∧ g₀ = 0`. If `f₀ ∧ f₁ ≠ 0`, the
first two give `g₀ = c₀ f₀`, `g₁ = c₁ f₁` and the third `(c₀ − c₁) f₀ ∧ f₁ = 0`,
so `c₀ = c₁ =: c` and `Φ(q ∧ (pt(c)^ − c·pt(b)^)) = 0` for every `q ∈ M̂`, i.e.
`M̂ ∧ w ⊆ D`. If `f₀ ∧ f₁ = 0`, all `f_t` lie in one line `⟨φ⟩` (or vanish);
`g_t ∈ ⟨f_t⟩` for all but at most one `t`, and an affine map into a line agreeing
with it at ≥ 2 points has both coefficients in it, so `g₀, g₁ ∈ ⟨φ⟩` and
`rank Φ ≤ 1`. Finally `rank Φ = 4 − dim ker Φ = 4 − dim(D ∩ (M̂ ∧ W))`, and
`M̂ ∧ w ⊆ D` gives `dim ker Φ ≥ 2`; so either disjunct forces
`dim(D ∩ (M̂ ∧ W)) ≥ 2`, whose generic value in `Gr(3, 6)` against a fixed
4-space is `3 + 4 − 6 = 1` and whose jump locus has codimension 2 (choose the
2-plane inside the 4-space, 4 parameters, then extend to a 3-space of `K⁶`, 3
more: `7 < 9 = dim Gr(3, 6)`). ∎

**The first closed form this pass derived was WRONG, and the correction is a
constructed refutation, not a hedge.** The `f₀ ∧ f₁ = 0` branch above was first
read as also forcing `M̂ ∧ w ⊆ D` — "a ≥3-dimensional subspace of a 4-space
contains a pencil". It does not: identifying `M̂ ∧ W ≅ M̂ ⊗ W ≅ K^{2×2}`, a
hyperplane is `{X : tr(AᵗX) = 0}` and it contains the column space
`{q ⊗ w : q ∈ M̂}` iff `Aw = 0`, i.e. iff `A` is **singular**. POOL-ZQ **Case C**
constructs a nonsingular one: `D` = a nonsingular hyperplane of `M̂ ∧ W`, giving
`rank Φ = 1` (whole line bad) with **no** pencil inside `D` — asserted. So the
single-containment reading is **refuted by construction**, and (ii)'s
disjunction is the exact form. (iii) is the same computation stopped one step earlier: a nonzero element
of `D ∩ (M̂ ∧ pt(b)^)` is a relation `λ f₀ + μ f₁ = 0` on `U_H`, which makes the
`b`-row of the matrix proportional to a fixed functional and leaves a single
root; the constructed witness has GCD degree exactly 1. ∎

**Reading (i) correctly, because it is stronger than a codimension count.** With
`dim U_H = 3` there are **three** minors, so badness is *three* equations in one
unknown — not one, as the `2 × 2` case would give. That is why the generic fibre
is bad **nowhere** rather than at ≤ 2 points, and it is what makes the measured
figure below a statement about the whole line rather than about the sampled
`pt(a)`.

*Exact, per frame (POOL-ZF).* At **32 of 32** `σ = 0` frames: the three minors
have **ℚ[t]-GCD of degree 0** — no common root in **any** extension of ℚ — so
*every* legal `pt(a) ∈ M` gives a target-rank point and the entire `pt(a)`-fibre
lies in `Z`; `dim(D ∩ (M̂ ∧ W)) = 1` (the generic value) and no pencil lies
inside `D`; no minor vanishes identically; and **(ii)'s closed form is asserted
against the GCD test at every frame** — the disjunction and the GCD agree 32/32.

*The must-reject witnesses (POOL-ZQ, synthetic, `random.Random(20260819)`;
README §4 convention 6 — a criterion observed only passing is untested).*
**Case A**, the first disjunct: `M̂ ∧ w ⊆ D` for `w = pt(c)^ − 2 pt(b)^`
constructed by hand — all three minors vanish **identically in `t`**
(`dim(D ∩ M̂ ∧ W) = 2`, pencil present), so the whole meet line is bad and
`σ = 0` alone does **not** put a chart point in `Z`.
**Case B**, the *weaker* degeneracy `D ∩ (M̂ ∧ pt(b)^) ≠ 0` — the `b`-side pair
is rank 1 at every `t` and the bad-`t` GCD has degree **1**: exactly one bad
point, so meeting one pencil is strictly weaker than identical badness.
**Case C**, the **refutation**: `D` a nonsingular hyperplane of `M̂ ∧ W` —
`dim(D ∩ M̂ ∧ W) = 3`, **no** pencil inside `D`, and yet all three minors vanish
identically. **Negative control:** 60 random 3-spaces `D`, all with
`dim(D ∩ M̂ ∧ W) = 1`, no pencil, and bad-`t` GCD degree **0** — the generic
behaviour the three constructions must be read against.

---

### Step O23 — (OC-27): the probe *Step O18* asked for, run — POOL-ZN

> **(OC-27)** *(measurement; witnesses, never a rate)* Over POOL-ZN — 19 named
> class shapes plus the first 4 shapes of each `outer.sweep_shapes()` family
> (POOL-S's **shape** construction) at seed window **400–405** with **no stratum
> filter** — **138 (shape, split) pairs** were probed: the **90** eligible splits
> carrying a length-4 companion, plus **48** further eligible splits (every 4th
> of the remaining 190). At **138 of 138** the first guard-accepted chart point
> is an **exact-ℚ certified point of `Z`**: `rank R(G′) = 6(|V(G)| − 2) −
> def(G′)` and `corank R(G − v) = 0`, with (OC-23)'s `s₀ = corank R(H)` asserted
> at each. **No miss.**

**What this is.** Each row is a **witness**: one exact-ℚ chart point in `Z`
*proves* `Z ≠ ∅` at that (shape, split), with no appeal to openness,
irreducibility or genericity. So this measurement is exactly the kind the (OC-7)
standing rule leaves unharmed — *"a positive existence witness: a degenerate draw
can create neither a false hit nor a false witness"* — and the pass takes **no**
rate reading from it. (For the record: the acceptance gate here is
`outer.chart_point`, i.e. the composite `repin.star_generic` plus
`verify_pencil_witness`, which per `notes/scripts/README.md` §4 convention 1 is
the condition under which a `place_pencil_general` battery *may* be quoted as a
rate. The pass does not lean on that permission, and no figure above is a rate.)

**What this is not.** It is not class uniformity, and no seed pool can make it
so — §(K-out)'s standing caveat, repeated verbatim. Nor is it a claim about the
shapes and splits outside the disclosed bounds: the **caps are disclosed**
(README §4 convention 8) — per-family shape cap **4**, seed window **6** seeds,
stride **4** on the non-companion splits, so **142 of the 190** non-companion
eligible splits of the same pool, and every shape beyond each family's first
four, are **not covered**, and nothing here reports on them. Counts are
**labelled instances** (README §4 convention 7), never isomorphism classes:
`outer.sweep_shapes()` carries measured ~31× duplication (§(K-frame) (FR-14)).

**The two things the probe was for, answered.** *(1) Does any (shape, split) fail?*
No candidate in scope — hence no candidate (K-tight) event and, by (OC-24)(ii),
no candidate PENCIL event either. *(2) Is `s₀ = 0` per-seed luck or per-shape
structure?* Structure: with (OC-23) it is a property of the `H`-part alone, and
with (OC-26) the whole `pt(a)`-fibre over a good `H`-part is in `Z` at 32/32
POOL-ZF frames. The **per-(shape, split)** granularity the dispatch asked for is
therefore the right one, and the per-seed histogram it replaces would have been
measuring the `H`-part twice.

---

### Step O24 — (OC-28): the transfer from `G`, the grid domination, and the proper-open boundary

> **(OC-28)** *(proven-informally, conditional on the shared-sub-tower clause;
> the domination is a conditional, the boundary is exhibited)*
>
> **(i) Shared sub-tower.** Read against §(K-chart) **(CH-2)**'s stage table,
> the towers of `G` and of `G′` **coincide stage by stage over `V(H)`**:
> `H(G) = H(G′)` (the two chain interiors `v`, `a` have degree 2 and are not
> hubs), so **stage 1** — the free hub points — is literally the same space;
> **stage 2**'s matrix `A_h(q)` is built from `h`'s **hub** neighbours `N_Λ(h)`
> only, and `N_Λ(w)` is unchanged for every `w ∈ V(H)` (at `b`, the neighbour
> that changes, `v` and `a` are *both* non-hubs and so enter no `A_b`), so the
> hub-normal stage is the same too; **stage 4**'s fibre over an `H`-non-hub `s`
> is `⋂_{h ∼ s, h ∈ H} Π(q_h, n_h)`, again unchanged. The two towers differ
> **only** in the fibres over the chain interiors — `{v, a}` for `G` (both at
> `e = 1`, an in-panel point) versus `{a}` for `G′` (at `e = 2`, the meet line
> `M`) — and in **stage 3**'s open condition, which `G′` imposes at `a`
> (`n_b, n_c` independent, i.e. `Π(b) ≠ Π(c)`) and `G` does not. Hence the
> `H`-projection of `G′`'s chart is the `H`-projection of `G`'s chart intersected
> with that **dense open**, and an `H`-part of a `G`-chart point extends to a
> `G′`-chart point by re-placing `pt(a)` on `M`. **No rank claim crosses**, so
> §(K-frame) **(FR-4)**'s named gap — the (GR-5) restatement at `G′` — is
> **not** invoked. **Constructed** (POOL-ZT): at **30 of 30** (shape, split)
> pairs, a `G`-chart point at the Tay target, with its `H`-part copied verbatim
> and `pt(a)` slid to a pinned rational point of `M`, is accepted by the
> harness's own `G′` chart-point guards (`repin.star_generic` +
> `verify_pencil_witness`) with `corank R(H)` **unchanged** and the landed point
> **in `Z`**.
>
> **(ii) Transfer.** If `G` attains its Tay target at a pencil configuration then
> `corank R(G) = 0` (tight, `def(G) = 0`), hence `corank R(H) = 0` there, hence by
> (i) and (OC-23) `{σ = 0} ≠ ∅` on the chart of `G′` — **at every eligible split
> simultaneously**, since one `corank R(G) = 0` point kills every subgraph's
> stresses at once. Asserted per transfer at **30/30** POOL-ZT points
> (`corank R(G) = 0 ⟹ corank R(H) = 0`), and the transferred point landed in `Z`
> at all 30 — so at those pairs `hK`-at-a-chart-point yields a point of `Z` by an
> **explicit** construction rather than by the density argument.
>
> **(iii) Domination.** §(K-grid) **(GR-9)** *proves* that a legal alternating
> colouring with both-block tree-triple certificates reaches the Tay target
> `6(|V| − 1)` at a σ-fixed grid configuration, and **(GR-5)** puts that
> configuration in the chart's image. So **(GR-10) ⟹ the `s₀` half of input (a)
> at every tight class shape and every eligible split**; and it is *already*
> free at every shape where the certificate has been exhibited — **907/907** of
> §(K-grid)'s census pool ((GR-10)'s evidence, `--treetriple`).
>
> **(iv) Boundary — `{σ = 0}` is a *proper* open.** At `P21` (§(K-flank) *F5(d)*;
> a **(K-res)** shape that **fails `hnoRigid`**, §(K-pure) P4/P7) the five
> recorded `dim R_a = 0` seeds have `s₀ = σ = 1` — measured here, with (OC-23) and
> (OC-25) asserted at each — while **30** of the same window's valid seeds have
> `σ = 0`. So the complement of `{σ = 0}` is not thin in the sampler's rational
> range, the pinned counter-fact being that the **count** predicts
> `dim R_a = 5 + def(G′) − def(G − v) = 1`, i.e. `s₀ = 0`, at every placement.

*Proof of (i).* Both `G` and `G′` satisfy §(K-chart) (CH-1)'s hypotheses — a
class shape has `hcard`, min degree 2 and girth ≥ 6, and (CH-1)'s own last
paragraph discharges all three at `G′` — so the tower description applies to
each. §(K-chart) **(CH-2)**'s four stages are indexed by bodies, and
each body's fibre condition reads only that body's **hub** neighbourhood: stage 1
frees the hub points, stage 2 puts `n_h ∈ ker A_h(q) ∖ 0` with `A_h` the matrix
of `q_u − q_h` over `u ∈ N_Λ(h)` (hub neighbours only — `widened.py:160`'s
`cons = [… for u in nb[h] if u in hubset]`), stage 4 puts a non-hub `s` in
`⋂_{h ∼ s, h ∈ H} Π(q_h, n_h)`. Now `deg v = deg a = 2`, so neither is a hub and
`H(G) = H(G′)`; and for every `w ∈ V(H)`, `N_Λ^{G′}(w) = N_Λ^{G}(w)` — the only
neighbourhood that changes at all is `b`'s, where the non-hub `v` is replaced by
the non-hub `a`, and non-hubs enter no `A_h`. So stages 1, 2 agree identically and
stage 4 agrees over every body of `H`. The towers therefore differ only over the
chain interiors and in stage 3's condition, which `G′` imposes at `a` (`e_a = 2`:
`n_b, n_c` independent) and `G` does not (`e_v = e_a = 1` there). Extension:
`a`'s `G′`-fibre is `M`, an affine line whenever `Π(b) ≠ Π(c)`; the acceptance
guards remove a proper closed subset of it. ∎

**Cross-direction convergence, recorded because it is the fan-out's own
mechanism.** This pass's mathematics was written **before** §(K-chart) landed,
with (i) flagged as "this pass's one structural input, tower-level, owned by
CIRR". CIRR then landed **(CH-2)** the same day — the tower written down stage by
stage against `place_pencil_general`'s source — and its stage table is exactly
what turns (i) from a flagged input into the proof above: the *hub*-only
dependence of stage 2 is the clause that does the work, and no prose description
of the tower before (CH-2) said it. Same shape as the sixth fan-out's
OCON/FRES convergence: two directions, same day, neither seeing the other, and
the pair is worth more than the sum.

*Proof of (ii)/(iii).* `G` tight with `def(G) = 0` makes its Tay target
`6(|V(G)| − 1) = 5|E(G)|`, i.e. full row rank, i.e. `corank R(G) = 0`; row-subset
monotonicity gives `corank R(H) = 0`; (i) transports the `H`-part; (OC-23)
converts it to `s₀ = 0`. For (iii), (GR-9) is quoted, not re-derived: its
conclusion is the Tay target at a grid configuration, and (AC-3) supplies the
nondegeneracy (GR-5) needs. The grid points are over `ℚ(i)`; a maximal minor of
`R(H)` nonvanishing there is nonvanishing at the generic point of the ℚ-chart,
hence at a ℚ-point, because §(K-chart) **(CH-1)(a)/(e)** makes the chart
ℚ-rational **with dense ℚ-points** — the step this pass would otherwise have had
to flag, supplied outright, on the same descent shape as §(K-clos) **(AC-7)**. ∎

**Two honest limits on (iii), stated because a one-line quotation will drop
them.** *(a)* §(K-grid)'s census pool (877 exhaustive `K4`-stratum shapes + 6 + 21
sweep shapes + 3 tight thetas) and §(K-out)'s class-shape population are **keyed
differently** and are labelled-instance pools (README §4 convention 7); "907/907"
is §(K-grid)'s pool, **not** "every class shape", and this pass does **not**
re-key either. *(b)* (GR-10) discharging would close `hK` on the whole tight
stratum outright ((GR-9) + (GR-5) + (AC-7)), which makes the domination a
*strategic* fact rather than a shortcut: it says the `s₀` half **cannot become the
binding obstruction before the grid route does**, not that either is closed.
Symmetrically — and this is the useful direction — any *partial* progress on the
grid route hands the `s₀` half over at the shapes it covers, because
independence of a proper subgraph is strictly weaker than rigidity of `G`.

**The mechanism of a failure, named.** (iv)'s `σ = 1` is not arithmetic noise: at
every one of the five seeds §(K-flank) *F5(d)* measured the `G − v` self-stress to
be supported on the theta sub-multigraph `{12, 13, 23a, 23b}` — 12 edges, line
rank 6 — the same support §(K-slide) *Step 5* exhibits for `P21`'s limit stress.
By (OC-23) that stress lives in `H`. So **the only known mechanism for the `s₀`
half to fail is a self-stress of a *subframework* of `H` forced by the pencil
pin** — §(K-pure) **(PC-OBS)**'s dependence side, which is exactly the
*combinatorially certifiable* direction of `Pencil-strategy.md` §2.3. Two
consequences: a future proof of the `s₀` half should look for a counting /
`hnoRigid`-driven exclusion of such subframework circuits rather than for a
genericity argument; and a search for a *counterexample* should look at class
shapes whose `H` contains a short theta sub-multigraph, which is where
`hnoRigid` is closest to failing.

---

### Where this leaves input (a) (hand-off)

**Status: OPEN as a class-uniform statement; not an independent gap; no gap-map
status moves.** *Step O18* item 2 asked for input (a) *"as a statement in its own
right"*; here it is, in the form the factorization leaves:

> **(a₂)** at every class (shape, split), `H = G − v − a` has **independent rows**
> at some pencil chart point — equivalently, at the generic one; and
> **(a₁)** at some such point, `D = {m(b) − m(c) : m ∈ Mot(H)}` contains **no**
> pencil `M̂ ∧ w` with `w` on the line `pt(b) pt(c)`.

What a successor should pick up, in descending value:

1. **(a₂) class-uniformly, via the grid route.** By (OC-28)(iii) this is
   *implied* by §(K-grid) (GR-10) and free at 907/907 of its pool, so the
   cheapest genuine progress is **not** a new argument here but a re-keying:
   check that every §(K-out) class shape carrying a length-4 companion is in
   §(K-grid)'s certified set (the two pools are keyed differently, (OC-28)(a)),
   which is a **combinatorial** cross-pool job with no new mathematics — and the
   transfer itself is already **machinery**, not an argument: `zneq --transfer`
   turns any target-rank chart point of `G` into a guard-accepted point of `Z` on
   every eligible split's `G′`-chart (30/30). Failing that, the honest target is a
   counting/`hnoRigid` exclusion of the subframework circuits *Step O24* names.
2. **(a₁) class-uniformly.** The Schubert non-jump `dim(D ∩ (M̂ ∧ W)) ≤ 1` —
   one condition, `x₁`-free, `λ`-free, stratum-free, and in the same object class
   as §(K-out) (OC-20)'s perp form (a subspace-meets-subspace count in `Λ²K⁴`).
   It is measured to fail nowhere (GCD degree 0 and `dim(D ∩ M̂ ∧ W) = 1` at
   32/32 POOL-ZF frames) and it is **one-point decidable**; a *recipe* is what is
   missing, exactly as for (OC-19) input (c). Worth trying first: `D` is the
   relative twist space of `H` with **no** hinge deleted and **no** weld, so
   §(K-out) (OC-18)'s `H/X`-rigidity criterion and `D` are near neighbours —
   `H/X` rigid forces `W₁ = 0`, and `D` is the un-welded analogue. Second: `D`
   depends only on the `H`-part, so (OC-28)(i) makes this too a statement about
   `G`'s own chart.
3. **A `σ > 0`-everywhere hunt at class shapes whose `H` carries a short theta
   sub-multigraph** — the only known failure mechanism (*Step O24*). A hit is a
   **PENCIL event** (disproof at that shape), so this is the highest-variance
   item on the list and should be run with the direction-A pivot rule in force.
4. **Deliberately not attempted**, recorded so a successor does not assume
   otherwise: (OC-19) input (c) (`H/X` rigid class-uniformly — OCON's verdict
   stands: (GR-15)-flavoured, not (FR-R1)-flavoured); chart irreducibility
   itself (§(K-chart), landed this wave — **cited**, not re-derived); pushing a constructed
   point to `p⁺` (§(K-out) *What would change this* item 4); the coupled two-end
   slide (item 5); every §(K-frame) *What would change this* item (ii)–(iv); and
   any counting / matroid route to (OUT)'s hypothesis ((OC-3) refutes the whole
   class).

---

### Verification (Steps O19–O24)

`notes/scripts/w4/zneq.py` (new, untracked at draft time; exact ℚ, stdlib only;
a `w4/` leaf **above** `ocon`, which it imports read-only — `stratum_numbers`,
`perp_B`, `meet` — together with `outerline` (`weld_motions`, `rel_span`),
`outer` (`split_data`, `eligible_splits`, `named_inventory`, `sweep_shapes`,
`companions4`, `chart_point`, `stratum_at`, `panel_frame`), `flanks`
(`P21_SPECS`), `kslidecomb` (`shape_data`), `widened` (`orient`,
`split_report`), `repin` (`rank_at_V`, `span_basis`, `star_generic`,
`seed_probe`), `kbare_common` (`rank_modp`, `verify_pencil_witness`,
`verts_of`), `pencil_escape` (`build_rigidity`), `nogood_subdiv`
(`deficiency`) and catalogued §1 primitives. **Nothing existing is modified**: `outer.py`,
`outerline.py`, `outerwide.py`, `ocon.py`, `repin.py`, `flanks.py`,
`kslidecomb.py`, `widened.py` are all read.) From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --factor   # (OC-23),(OC-25),(OC-26); POOL-ZF, POOL-ZQ
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --sweep    # (OC-27); POOL-ZN
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --reject   # (OC-28)(iv); POOL-ZR
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --transfer # (OC-28)(i)/(ii) CONSTRUCTED; POOL-ZT
```

Times as run: `--factor` **97 s**, `--sweep` **242 s**, `--reject` **76 s**,
`--transfer` **106 s** — 521 s in total. All four re-run **byte-identical** under
two different `PYTHONHASHSEED` values (`0` and `12345`), the
*figures-do-not-move* gate
(`notes/scripts/README.md`) — `--sweep` modulo the elapsed-second progress marks
it prints per family, which are wall-clock, not figures. The pass **added** one
driver and modified none (`git status --porcelain notes/scripts/` shows exactly
the one new file).

**Harness debt recorded, not paid.** `ocon.meet` — the dimension-asserting
wrapper of `lambda.span_meet` — now has **two** consumers, which is
`notes/scripts/README.md` §2 rule 2's own trigger to move it one layer down
beside `span_meet`. This pass may not modify a landed file, so the move is
**recorded for a successor**, not made; `zneq` imports it read-only meanwhile.

**Pools, pinned; every figure above is quoted over exactly one of them, and none
is aggregated with POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A /
POOL-W / POOL-SL / POOL-OV / POOL-OC / POOL-OZ.**

- **POOL-ZF** (`--factor`) — the 4 `lambda.habitat_specs` habitats × **every**
  eligible split × placement seeds **300–303**, **unfiltered** (no target-rank,
  no stratum filter) but guard-accepted through `outer.chart_point`
  (`repin.star_generic` + `verify_pencil_witness`): **30 splits probed, 32 chart
  points accepted, 88 draws rejected by the guards.** A derivation pool: every
  sentence under test is an identity, so it is a witness set, and **no figure
  from it is a rate**.
- **POOL-ZQ** (`--factor`) — synthetic exact-ℚ subspaces of `Λ²K⁴` from
  `random.Random(20260819)` (seed printed), plus **three constructed**
  configurations (Cases A, B, C — C being the refutation of this pass's own first
  closed form) and **60 negative controls**. No graph, no placement.
- **POOL-ZN** (`--sweep`) — `outer.named_inventory()` (19 named class shapes)
  plus the **first 4** shapes of each `outer.sweep_shapes()` family — POOL-S's
  *shape* construction — at seed window **400–405** with **no stratum filter**;
  population = every eligible split carrying a length-4 companion (**90**) plus
  **every 4th** of the remaining 190 (**48**). **138 (shape, split) pairs, 138
  chart points drawn.** *Caps disclosed* (README §4 convention 8): shape cap 4
  per family, seed window 6, stride 4; the other 142 non-companion splits and
  every shape past each family's fourth are **not covered**.
- **POOL-ZT** (`--transfer`) — the 4 habitats × **every** eligible split ×
  placement seeds **500–507** of the **whole graph `G`** (not of `G′`),
  guard-accepted for `G` by `repin.star_generic` + `verify_pencil_witness`, then
  `pt(a)` slid onto `M` at the first of **8 pinned rational parameters**
  (`1, −1, 2, ½, −3, 3, 5, −⅓`) the `G′` guards accept. **30 transfers
  constructed, 30 accepted, 0 failures.** The slide-parameter list is a
  disclosed bound: a (shape, split) where none of the eight is accepted would be
  reported, and none was.
- **POOL-ZR** (`--reject`) — `P21` (`flanks.P21_SPECS`), split `v = 100`
  (`a = 101`, `b = 0`, `c = 1`), seeds **101–140**: the same window §(K-flank)
  *F5(d)* used, re-read in `s₀` / `corank R(H)` coordinates. `P21` **fails
  `hnoRigid`** and is a **(K-res)** shape, not a tight class member — it is here
  as the arc's only recorded `σ = 1` witness.

Per mode, what is asserted:

- `--factor`: per frame — (OC-23)'s `s₀ = corank R(H)`; (OC-25)(a) against
  independently computed coranks; (OC-25)(b)'s `dim D = 3 + σ`,
  `dim U_H = 3 − σ`; (OC-25)(c)'s `Z`-membership equivalence; (OC-17) against
  the catalogued `outer.stratum_at` (`dim R_a = 1 − s₀` at target rank, and
  `stratum_at is None` off it); `pt(a)` **on** the meet line `M`, exactly; the
  affine-linearity of `C(ab)`, `C(ac)` along `M` spot-checked at `t = 2`; the
  three minors' ℚ[t]-GCD, with an assert that **no** minor vanishes identically;
  **(OC-26)(ii)'s disjunction asserted against that GCD**; and the sampled `t`'s
  goodness against `Z`-membership. Histograms:
  `(target rank?, s₀, σ, dim U_H, dim W, in Z) = (True, 0, 0, 3, 1, True) : 32`;
  `(minors, identically-zero minors, deg GCD, dim(D ∩ M̂ ∧ W), pencil?) =
  (3, 0, 0, 1, False) : 32`.
  POOL-ZQ: Case A — three minors identically zero, `dimK = 2`, pencil present;
  Case B — `b`-row rank 1, bad-`t` GCD degree exactly 1; **Case C** — `dimK = 3`,
  **no** pencil, three minors identically zero (the refutation); 60 random
  controls at `dimK = 1`, no pencil, GCD degree 0.
- `--sweep`: per (shape, split) — a GF(p) screen (`rank_modp`, a **certified
  lower bound**, README §4 convention 2) selects a candidate seed, and the
  accepted witness is **rechecked in exact ℚ**: `rank R(G′) = 6(|V(G)| − 2) −
  def(G′)`, `corank R(G − v) = 0`, plus (OC-23). An assert catches any screen
  mis-prediction (none fired). The (OC-25) leg runs at the first witness of each
  family (disclosed). Outcome: `('WITNESS in Z', has length-4 companion) =
  (True) : 90`, `(False) : 48`; first-witness seed histogram
  `{400: 62, 401: 47, 402: 25, 403: 4}`.
- `--transfer`: per (shape, split) — the `G`-side guards (`star_generic`,
  `verify_pencil_witness`) on the **whole-graph** placement; `corank R(H) ≤
  corank R(G)`; at every target-rank `G`-point `corank R(G) = 0` **and**
  `corank R(H) = 0`; after the slide, the `H`-part asserted **equal
  point-by-point** to the `G`-point's, `corank R(H)` asserted **unchanged**, the
  `G′` guards asserted to accept, and the full (OC-23)/(OC-25) ledger at the
  landed point. Histogram `(G at target rank?, corank R(H), G′ at target rank,
  in Z) = (True, 0, True, True) : 30`.
- `--reject`: per valid seed — `s₀` cross-checked against `repin.seed_probe`'s
  own `s₀`, (OC-23) asserted, and at each `dim R_a = 0` seed the full (OC-25)
  ledger `(s₀, σ, dim U_H, dim D, rank of the two functionals, dim W) =
  (1, 1, 2, 4, 2, 0)` with `rank R(G′) = tgt` asserted. Tally: **30** seeds with
  `σ = 0`, **5** with `σ = 1`, 5 invalid.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean (`DESIGN.md`
*Formalize everything the argument uses*).

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (OC-23) `s₀ = corank R(H)` | `--factor`, `--sweep`, `--reject` | both coranks computed **independently** in exact ℚ and asserted equal, per frame — 32/32 POOL-ZF, 138/138 POOL-ZN witnesses, 35/35 valid POOL-ZR seeds **including the 5 that reject** |
| (OC-24)(i) openness / one-point witnessing | — | **proof-level** ((OC-17) + (OC-23) + §(K-chart) (CH-1)(a), **proven** not cited). Its *operational* content — one point certifies — is what `--sweep` exercises 138 times |
| (OC-24)(ii) `{σ = 0} = ∅ ⟹ hK` false | `--transfer` for its ingredient | **proof-level** (row-subset monotonicity + tightness), resting on (OC-28)(i). **Not driver-testable as stated**: no driver can quantify over a whole chart. What *is* tested is the implication it contraposes — `corank R(G) = 0 ⟹ corank R(H) = 0`, asserted at every target-rank `G`-chart point (30/30, POOL-ZT) — plus `corank R(H) = 0` wherever `Z` is reached (138/138, POOL-ZN) |
| (OC-25)(a) the corank identity | `--factor` (per frame), `--sweep` (first witness per family), `--reject` (per jump seed) | `corank R(G′)` from an exact rank vs `σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)` from the motion space — the two sides computed by disjoint routes |
| (OC-25)(b) the two dimension counts | same | `dim D = 3 + σ` and `dim U_H = 3 − σ` asserted inside `u_space`, at `σ = 0` (POOL-ZF, 32) **and** `σ = 1` (POOL-ZR, 5) |
| (OC-25)(c) the `Z`-membership equivalence | same | `(rank = tgt ∧ s₀ = 0) == (σ = 0 ∧ the functional pair independent)` asserted per frame — an **iff**, so both directions are exercised (the 5 POOL-ZR seeds exercise the false side) |
| (OC-26)(i) affine-linearity + the 3-minor count | `--factor` | the matrix is rebuilt from its `t = 0` / `t = 1` values and **spot-checked against a direct evaluation at `t = 2`**; the minor count is `C(dim U_H, 2) = 3`, printed |
| (OC-26)(i) "generically empty" | `--factor` | the exact ℚ[t] **GCD** per frame: degree 0 at 32/32, i.e. no bad `t` in any extension of ℚ. This is the sentence a rational-root search would have *under*-tested |
| (OC-26)(ii) the disjunction | `--factor` (per frame) | `(GCD identically zero) == (dim(D ∩ M̂ ∧ W) ≥ 3 or a pencil M̂ ∧ w ⊆ D)` asserted at **every** frame, the two sides computed by disjoint routes (a ℚ[t] GCD vs two exact rank computations); the pencil test is exact — `∃w` iff a `(2·dim U_H) × 2` matrix has rank ≤ 1, no `P¹` parametrization |
| (OC-26)(ii) ⟸, both disjuncts | `--factor` POOL-ZQ | **constructed** Case A (`M̂ ∧ w ⊆ D`, `dimK = 2`) and **constructed** Case C (`dimK = 3`, **no** pencil) each asserted to make all three minors vanish identically |
| (OC-26)(ii) the *first* closed form, REFUTED | `--factor` POOL-ZQ Case C | Case C is asserted to have `dimK = 3` **and** no pencil **and** identical badness — a constructed counterexample to "identically bad ⟺ a pencil inside `D`", which is what this pass first derived |
| (OC-26)(iii) one bad point, not the line | `--factor` POOL-ZQ | the **constructed** Case B asserted to have `b`-row rank 1 **and** GCD degree exactly 1 |
| (OC-26) as a criterion (F13) | `--factor` POOL-ZQ | **three** constructed must-**reject** objects plus **60** negative controls, each asserted at `dimK = 1`, no pencil, GCD degree 0 — the guard is not observed only passing |
| (OC-27) the witness census | `--sweep` | per (shape, split), an exact-ℚ certified point of `Z` or an explicit miss row; a screen mis-prediction assert; caps printed in the mode's own header |
| (OC-28)(i) shared sub-tower | `--transfer` | **constructed**: a `G`-chart point's `H`-part, copied point-by-point, plus `pt(a)` on `M`, is asserted to pass the harness's own `G′` chart-point guards, with `corank R(H)` asserted unchanged — 30/30. The *general* statement is **proven** against §(K-chart) (CH-2)'s stage table (hub-only stage 2), not merely sampled |
| (OC-28)(ii) transfer | `--transfer` | `corank R(G) = 0 ⟹ corank R(H) = 0` asserted at every target-rank `G`-point (30/30), and the landed `G′` point asserted through the full `Z` ledger — in `Z` at 30/30 |
| (OC-28)(iii) domination | — | **quotation**: (GR-9) proven, (GR-10) measured 907/907 in §(K-grid)'s own driver. Nothing re-derived here, and the pools are **not** re-keyed |
| (OC-28)(iv) the proper-open boundary | `--reject` | 5 `σ = 1` seeds against 30 `σ = 0` at the same window, with the **count-theoretic counter-fact** (`widened.split_report` = 1) printed beside them |
| `Z ≠ ∅` class-uniformly | — | **not tested and not claimed.** 138 labelled (shape, split) witnesses under disclosed caps, never a class-level statement |

---

### Confidence verdict (Steps O19–O24)

| | claim | standing |
|---|---|---|
| **(OC-23)** | `s₀ = corank R(H)` at every legal chart point with `pt(a) ≠ pt(c)`; so input (a)'s `s₀` half is independence of `H` alone | **proven-informally** (the pendant-edge case of (OC-17)'s own lemma); asserted per frame at 32/32 POOL-ZF, 138/138 POOL-ZN witnesses and 35/35 valid POOL-ZR seeds |
| **(OC-24)(i)** | `Z ≠ ∅ ⟺` both halves nonempty; each one-point witnessable; one point satisfying both needs no irreducibility | **proven-informally** — and its irreducibility hypothesis is now **PROVEN**, not cited: §(K-chart) **(CH-1)(a)**, unconditional at `Γ = G′`, with (CH-1)(b) making FRES's constant-fibre-dimension restriction inessential |
| **(OC-24)(ii)** | `{σ = 0} = ∅` at a class shape ⟹ **`hK` FALSE** there; so the `s₀` half is a **necessary condition** for the phase's target, and that branch of a `Z = ∅` negative is a **PENCIL event**, not a (K-tight) event | **proven-informally**, conditional on (OC-28)(i)'s shared-sub-tower clause. Not driver-testable (a whole-chart quantifier). **This is the pass's sharpest finding and the one to surface** |
| **(OC-25)** | `corank R(G′) = σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)`, `dim D = 3 + σ`, `dim U_H = 3 − σ`; hence membership of `Z` **is** §(K-tight) *Step 2* item 1's attainment criterion at `(G′, a)`, and the regress terminates in one step | **proven-informally** (a substitution instance of a proven-informally item); asserted per frame at 32/32 POOL-ZF, at 5/5 POOL-ZR jump seeds and at the first POOL-ZN witness per family. **First driver test of that item at a substituted instance** |
| **(OC-26)** | along `M` the bad set is the common zero locus of **three** quadratics, generically empty; bad-at-every-`t` ⟺ `dim(D ∩ M̂ ∧ W) ≥ 3` **or** `M̂ ∧ w ⊆ D` — both forcing a codimension-2 Schubert jump; the weaker `D ∩ (M̂ ∧ b^) ≠ 0` gives exactly one bad point | **proven-informally**, equivalence in both directions, and the closed form **asserted against the GCD at every frame** (32/32). ℚ[t]-GCD degree **0**, `dim(D ∩ M̂ ∧ W) = 1`, no pencil, at 32/32; three configurations **constructed** + 60 controls (F13). **This pass's own first closed form was REFUTED by its Case C** — record it as the correction it is |
| **(OC-27)** | 138/138 labelled (shape, split) pairs of POOL-ZN carry an exact-ℚ certified point of `Z` — 90 companion-bearing, 48 others | **measurement; witnesses, not a rate.** Caps disclosed; no class-level reading; no candidate (K-tight) or PENCIL event in scope |
| **(OC-28)** | the two charts share their `H`-sub-tower, so `corank R(H) = 0` transfers from a target-rank configuration of `G`; hence **(GR-10) ⟹ the `s₀` half at every tight class shape and split**, free at 907/907 of §(K-grid)'s pool; and `{σ = 0}` is a **proper** open, witnessed at `P21` | **(i) proven-informally** against §(K-chart) (CH-2)'s stage table (hub set unchanged; stage 2 depends on **hub** neighbours only, and both chain interiors are non-hubs) **and constructed** at 30/30 POOL-ZT pairs — it was flagged as this pass's one structural input and CIRR's same-day landing discharged it; **(ii) proven-informally, asserted 30/30**, with the transferred point landing **in `Z`** at all 30; **(iii) a conditional plus a quotation** — (GR-9) proven, (GR-10) measured, the ℚ-descent supplied by (CH-1)(e), pools **not** re-keyed; **(iv) measured**, 5 vs 30 at a **non-class** shape |
| **input (a)** | `Z ≠ ∅` at every class (shape, split) | **OPEN as a class-uniform statement — and NOT an independent gap.** Reduced to (a₂) + (a₁) above; neither proven class-uniformly here |

**No gap-map status moves. Class uniformity of (OUT), of (OC-8) and of `hK` is
exactly where it was.** What moves is the *content* of §(K-out)'s row (which
gains (OC-23)–(OC-28)) and the reading of (OC-19)'s input (a): from an unowned
prerequisite to a two-half statement, one half necessary for `hK` and dominated
by (GR-10), the other the (K-tight) criterion one split down.

### What would change this (Steps O19–O24)

1. **A class shape whose `H` is dependent at every chart point** — `{σ = 0} = ∅`.
   By (OC-24)(ii) that **disproves `hK` at that shape**: a **PENCIL event**, not
   a (K-tight) event, and the phase pivots rather than re-routes. The hunt with
   the best prior is class shapes whose `H` contains a short theta
   sub-multigraph, the *only* known mechanism (§(K-flank) *F5(d)*'s support, via
   (OC-23)); it would simultaneously refute §(K-grid) (GR-10) at that shape.
2. **A class (shape, split) at which the (OC-26)(ii) disjunction holds** at
   every `σ = 0` chart point — the (K-tight) event the dispatch named. Measured
   nowhere: GCD degree 0, `dim(D ∩ M̂ ∧ W) = 1` and no pencil, at 32/32 POOL-ZF
   frames. **Constructed** instances of *both* disjuncts exist synthetically
   (Cases A and C), so the configuration is not impossible in `Λ²K⁴` — the open
   question is whether a class chart can realize it. Note the two disjuncts are
   genuinely different loci: Case C carries no pencil at all, which is why the
   single-containment reading had to be replaced.
3. **A failure of the shared-sub-tower clause** ((OC-28)(i)) would break
   (OC-24)(ii) and (OC-28)(ii)–(iii) at once, leaving (OC-23), (OC-25), (OC-26)
   and (OC-27) intact. It is **no longer an input**: §(K-chart) (CH-2)'s stage
   table proves it (stage 2 reads **hub** neighbours only, and both chain
   interiors are non-hubs), and 30/30 POOL-ZT transfers are guard-accepted. What
   *would* break it is a change to `place_pencil_general`'s stage 2 that let a
   **non-hub** neighbour constrain a hub normal — worth naming because that is
   precisely the difference between the two charts. It remains **cheaper than
   §(K-frame) (FR-4)**, which it deliberately does not invoke: nothing about rank
   crosses between the two charts.
4. **A failure of chart irreducibility** ((OC-24)(i)) would break the *two-point*
   form of the reduction but **not** the one-point form, so it would not touch
   (OC-27)'s 138 witnesses. Since §(K-chart) **(CH-1)** it is **proven**, so this
   item is now a pointer to (CH-1)'s own hypotheses (`hcard`, min degree 2,
   girth ≥ 4 — all unconditional at `G′`) rather than an open risk.
5. **Re-keying §(K-grid)'s 907 against §(K-out)'s class-shape population.** The
   cheapest genuine progress on (a₂) and the one thing this pass deliberately did
   **not** do: the two pools are labelled-instance pools with different keys
   (README §4 convention 7), so "907/907" cannot be read as "every §(K-out) class
   shape". A combinatorial cross-pool check, no new mathematics.
6. **A longer split chain.** (OC-25)'s regress terminates in one step because
   `orient`'s chain has exactly two interior vertices. If a future frame admits a
   split whose chain interior is longer, input (a) at that frame iterates the
   substitution and the peeling bottoms out further down — worth recording so a
   successor does not assume the one-step form is structural.
7. **A `σ = 1` chart point at a *class* shape** (as opposed to `P21`, which fails
   `hnoRigid`). None is recorded anywhere in the arc; exhibiting one would be item
   1 in progress, and its absence is currently the whole empirical content of
   (a₂).

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

## §(K-frame) — the shared chart-to-frame dominance residue: the lemma shape delivered in its honest minimal form, both bad divisors made **combinatorial** at grid points, the **(ANH-14) residue discharged at every enumerated bare-cycle site by a colouring recipe** (1904/1904 + 30 exact certificates), and the (OC-16) residue's non-containment half witnessed **by construction** at θ(3,4,5) — with the strict availability package measured **0/8** and its (AC-9) mechanism named

Answering `notes/Pencil-fanout.md` §"Fourth fan-out" → Direction J, i.e.
§(K-grid) *Step G13*'s candidate lemma shape, aimed at the two terminal
residues of the third fan-out: §(K-out) (OC-16)'s (at degree-3 hubs,
availability ⟺ the hard-stratum target-rank locus `⊄ {pt(b) ∈ C₀}`) and
§(K-ann) (ANH-14)'s (the universal irreducible degree-12 polynomial `C`
nonzero somewhere on the frame's reachable locus). Read against §(K-grid)
*Step G6* ((GR-5)) and *Step G13*; §(K-ann) *Steps A10/A14–A17* ((ANH-9),
(ANH-13), (ANH-14)); §(K-out) *Steps O11–O12* ((OC-12)/(OC-13)/(OC-15)/
(OC-16)); §(K-clos) (AC-2)/(AC-4)/(AC-9). Drivers:
`notes/scripts/w4/framedom.py` (imports the canonical layer plus `anhr1` /
`shrink` / `outerwide` / `grid` / `closure` read-only) and
`notes/scripts/m2/framedom.m2` (the M2 layer's fourth driver).

**Status, stated before the mathematics.**

- **The lemma shape *Step G13* names is delivered, and it is smaller than
  its name.** "Dominance" is never needed: both residues are
  *non-containment-in-one-hypersurface* questions, and those are settled by
  **one point off the divisor plus irreducibility of the stratum** ((FR-1),
  two lines of algebraic geometry). The content is entirely in the two
  ingredients — constructing the point, and owning the irreducibility — and
  the two residues differ exactly there: (ANH-14)'s stratum is the **whole
  pencil chart**, whose irreducibility §(K-ann) (ANH-9)(ii) already owns;
  (OC-16)'s is the **hard-stratum target-rank locus**, whose irreducibility
  nobody owns — and is needed *only* to combine separately-witnessed open
  conditions ((FR-7)).
- **The transport step — the unattempted one — works, and it lands on `G′`,
  not `G`.** The grid witnesses live at pencil placements; the residues'
  charts are the split graph `G′ = G − v + ab`'s (that is where
  `pt(a) ∈ M` comes from). Building the σ-fixed grid **at `G′`** makes
  `pt(a) ∈ M` *automatic* (alternation at the degree-2 body `a` forces its
  two edges into opposite rulings, so `pt(a)` is conjugate to both `pt(b)`
  and `pt(c)`), and `verify_pencil_witness` accepts the built ℚ(i)
  placement at every instance run.
- **At a grid point BOTH bad divisors are combinatorial.** Every hinge line
  of a σ-fixed grid configuration is a *ruling line* of the fixed quadric;
  the two ruling families span complementary 3-spaces (which are exactly
  the `⋆`-eigenspaces of §(K-clos) (AC-4)); so **any** 6×6 hinge-line
  determinant — (ANH-14)'s `C` and (OC-16)'s `Δ` in particular — is nonzero
  **iff** its six edges are coloured 3–3 with the three lines per family
  pairwise distinct, and "same line" is *same colouring-component*
  ((FR-2)/(FR-3), an identity over the function field: `framedom.m2`
  (FR-M1), `det = 128·Vdm(s)·Vdm(u)`).
- **The (ANH-14) residue is discharged at every enumerated bare-cycle site,
  by a recipe.** A *pattern colouring* — admissible on `G′`, the site's six
  frame edges 3–3 in pairwise-distinct components, plus two placement-free
  legality tests — exists at **1904 of 1904** bare-cycle sites of the full
  §(K-ann) pool (the census reproduces (ANH-13)'s 1904 exactly), and at 30
  sites (all 6 census sites + 24 sweep sites) the built ℚ(i) grid point was
  checked end-to-end: pencil witness green, `C ≠ 0` exact, with a
  criterion-violating colouring of the same site giving `C = 0` (negative
  control). Via §(K-ann) (ANH-9)(iii), each such point **proves** the
  (ANH-R1) β-clause at its site. What remains for class uniformity is
  **(FR-R1)**: pattern-existence at every class shape — a colouring
  question with **no rank, no count, no balance and no tree-triple in it**,
  strictly cheaper than §(K-grid) (GR-15)'s.
- **On the (OC-16) side the non-containment is witnessed by construction at
  θ(3,4,5), and the strict form hits a wall with a name.** Of the 8
  admissible `G′`-colourings, **4 land on the hard stratum at target rank**
  (`(rank, dim R_a) = (54, 1)` — the first constructed, non-sampled
  inhabitants of that locus), and each has `Δ ≠ 0` at exactly one end — so
  (OC-8)'s literal statement (a hard-stratum target-rank chart point with
  `L_b ⊄ R₁` or `L_c ⊄ R₄`) is **inhabited by an explicit combinatorial
  construction**. But the *strict* package — additionally `λ ≠ 0` at the
  same point — is **0/8**, and the mechanism is §(K-clos) (AC-9): a σ-fixed
  degree-3 hub always carries a coincident hinge pair, and at every
  on-stratum colouring the coincidence lands on the pair `{e₁, C(b,u)}` at
  the `Δ ≠ 0` end, killing `λ` there. Whether that anti-correlation is
  structural or θ(3,4,5)-specific is **open**.
- **Class uniformity is untouched. No gap-map status moves in this draft.**
  The (K-ann) row's residue changes *shape* (dominance → (FR-R1)
  pattern-existence) at the coordinator's hand, not its status.

### Standing notation (on top of §(K-clos) and §(K-ann))

`G` a class shape, `v` an eligible split with ends `b, c`,
`G′ = G − v + ab` (`outer.split_data`'s `Gp`), `H = G − v − a`. Grid data
per §(K-clos) (AC-2): a 2-colouring `col : E(G′) → {A, B}` assigns each
body the point `pt_w = s_w ⊗ u_w` on the fixed quadric, the `A`-parameter
`s` constant on components of `E_A` and injective across them (likewise
`B`); "admissible" = proper on the alternation constraint graph
(`closure.alternation_classes`). `W_A, W_B ⊂ Λ²K⁴` are the spans of the two
ruling families. A **bare-cycle site** is a (shape, split, length-4
companion, β) with `H/P − β` a bare 6-cycle (§(K-ann) (ANH-13)(iv)); its
**frame edges** are the six `H`-edges of that cycle. Everything is exact:
ℚ(i) points (`closure.Gauss`), `exactcore.rank`/`wedge2` throughout.

### Step FR0 — (FR-1): the lemma, in its honest minimal form

> **(FR-1)** *(proven-informally; standard)* Let `X` be an irreducible
> variety over a field `k ⊆ K̄` (or the image of an irreducible rational
> parametrization defined over `k`), `f : X → 𝔸^N` a morphism, and
> `D = {P = 0}` a hypersurface. If **one** point `x ∈ X(K)` (any extension
> `K`) has `P(f(x)) ≠ 0`, then `P ∘ f ≢ 0`, hence `f(x′) ∉ D` for `x′` in a
> dense open of `X` — in particular at the generic point, and at ℚ-rational
> points when `X`'s parameter space is rational over ℚ. Conversely
> `f(X) ⊆ D` iff `P ∘ f ≡ 0`.

Two remarks that do the strategic work. *(i)* **Dominance of `f` is never
needed** — *Step G13*'s phrase "gives dominance" over-asks; non-containment
in the *one named divisor* is all either residue consumes, and that is
one witness point + irreducibility of the *source*. *(ii)* The lemma
splits the two residues by who owns the irreducibility: for §(K-ann)
(ANH-14) the source is the whole chart of the triple and §(K-ann)
(ANH-9)(ii) owns it, so **the entire remaining content is the witness
point**; for §(K-out) (OC-16) the natural source is the hard-stratum
target-rank *sublocus*, un-owned — see *Step FR5*.

### Step FR1 — (FR-2): the ruling decomposition of `Λ²K⁴`

> **(FR-2)** *(proven; (FR-M1)–(FR-M3) are identities over the function
> field, the eigen identification measured exactly)* Under
> `Λ²(K² ⊗ K²) ≅ (Sym²K² ⊗ Λ²K²) ⊕ (Λ²K² ⊗ Sym²K²)`:
>
> (i) the Plücker images of the two ruling families of the fixed quadric
> span **complementary 3-spaces** `W_A ⊕ W_B = Λ²K⁴`, each family a
> **Veronese conic** in its own 3-space (`A(s)` is quadratic in `s`);
>
> (ii) any **3 distinct** same-family lines are linearly independent (3
> distinct points of a Veronese conic span its plane), and any **4** are
> dependent;
>
> (iii) `W_A` and `W_B` are exactly the `+1` and `−1` eigenspaces of the
> Hodge star (measured: `rank(x − ⋆x) = 0` on `W_A`, `rank(x + ⋆x) = 0` on
> `W_B`, driver `--rulings`) — so at a grid point the `⋆`-eigen decoupling
> of §(K-clos) (AC-4) *is* the family-block decomposition of any hinge-line
> matrix.

### Step FR2 — (FR-3): the determinant law — both bad divisors are combinatorial at grid points

> **(FR-3)** *(proven: the algebra is (FR-M1)/(FR-M2)/(FR-M3) over the
> function field; the hinge-line-is-a-ruling-line step is two lines below;
> driver-asserted in both directions at every built instance)* At a
> σ-fixed grid configuration with all bodies distinct:
>
> (i) **every hinge line is a ruling line** — an edge's endpoints are
> conjugate (§(K-clos) (AC-2)), and the restriction of the quadric to the
> line through two conjugate quadric points vanishes identically, so the
> line lies on the quadric; its family is the edge's colour, its *identity*
> is the edge's colouring-component (the family parameter is constant on
> components, injective across them);
>
> (ii) for any six edges `e₀…e₅`,
>
> `det₆[C_{e₀}, …, C_{e₅}] ≠ 0 ⟺` the colours split **3–3** and the three
> lines in each family are **pairwise distinct**;
>
> and on the nose, with `A(s)`/`B(u)` the ruling Plücker vectors,
>
> `det₆[A(s₁), A(s₂), A(s₃), B(u₁), B(u₂), B(u₃)] = 128 · Vdm(s₁,s₂,s₃) · Vdm(u₁,u₂,u₃)`
>
> — an identity over `ℚ(i)(s, u)` (`framedom.m2` (FR-M1); the constant is
> pinned cross-language at the instance `det[A(2),A(3),A(5),B(2),B(3),B(5)]
> = 4608`, asserted independently by `framedom.py --validate` and
> `framedom.m2` (FR-M0)).
>
> (iii) span membership is equally combinatorial: a further ruling line
> `C` lies in the span of a set `S` of ruling lines **iff** `C`'s family
> contributes ≥ 3 distinct lines to `S`, or `C`'s line is one of `S`'s (a
> conic meets a plane section in ≤ 2 points; `span S = (span S ∩ W_A) ⊕
> (span S ∩ W_B)`).

Both bad divisors are instances: §(K-ann) (ANH-14)'s `C` is the 6×6
Plücker determinant of a bare-cycle site's frame edges ((ANH-13)(iv));
§(K-out) (OC-16)'s `Δ` is `det₆[five chain hinge lines, C(b,a)]` — and at a
`G′`-grid point `C(b,a)` is itself a hinge line (of the split edge `ab`).
*Step G13*'s "evaluability battery" answer is therefore stronger than
evaluable-in-closed-form: **at grid points, evaluation is O(1) reading of
the colouring**, no algebra at all — with the exact ℚ(i) determinant kept
as the per-instance certificate.

An incidental with independent value: §(K-clos) (AC-9) becomes obvious in
this language — a σ-fixed body of degree ≥ 3 has two same-colour edges,
which share the body, hence share the component, hence **are the same
ruling line**: the coincident hinge pair, with its exact combinatorial
location (which pair coincides = which pair shares a colour).

### Step FR3 — (FR-4): the transport theorem, (ANH-14) side

> **(FR-4)** *(true-modulo-named-gap; the gap is the (GR-5)-at-`G′`
> chart-membership re-read, stated below and machine-checked per instance)*
> Let a bare-cycle site of a class triple be given, and let `col` be an
> admissible colouring of `G′` such that
>
> - **(pattern)** the six frame edges are coloured 3–3 with
>   pairwise-distinct components per family;
> - **(legality, placement-free)** all bodies distinct (the
>   `(comp_A, comp_B)` pairs injective) and no `closedHubNbhd` forced
>   collinear (no 3-member closed hub neighbourhood mono-component in
>   either family).
>
> Then the grid configuration of `G′` at `col` (generic injective family
> parameters, exact ℚ(i)) is a pencil chart point of the triple with
> `C ≠ 0` at its frame image; by §(K-ann) (ANH-9)(iii) — rank lower
> semicontinuity on the irreducible chart, never a genericity guard — this
> **proves the (ANH-R1) β-clause at the site**: `H/P − β` is independent at
> the generic pencil placement.

*Why `G′` and not `G`.* The §(K-ann)/§(K-out) charts place the split graph
`G′` (that is `dominance.base_seed`'s object, and where `pt(a) ∈ M` lives:
`a` is adjacent to both `b` and `c` in `G′`). At a `G`-grid the conjugacy
`pt(a) ⊥ pt(b)` is *not* forced (`a ~ b` fails in `G`); at a `G′`-grid it
is free: `a` has degree 2, alternation puts `(a,b)` and `(a,c)` in opposite
families, and both conjugacies hold — `pt(a) ∈ Π(b) ∩ Π(c) = M`
automatically. This settles the fan-out's "transport to the contracted
objects" question: the construction transports by **regridding at `G′`**,
after which the contracted objects' data (frame points, chain lines,
`C(b,a)`) are read off the one placement.

*Chart membership — the named gap, and what is checked.* §(K-grid) (GR-5)
proves grid configurations are pencil-chart points *for a class shape `G`
with `hcard`*; the object here is `G′`, not a class shape (its count
exceeds tightness by one). The proof of (GR-5) consumes no tightness — its
inputs are `hcard`, all-bodies-distinct, the closed-hub-neighbourhood LI
condition, isotropy/conjugacy, and degree-2 bodies having 3-member closed
neighbourhoods on a 2-edge-connected shape — and every one of those
hypotheses is **asserted per instance** by the driver (`hcard_ok(G′)` and
`is_2ec(G′)` hold at all 1540 splits carrying sites, 0 failures; the LI
ranks and distinctness exactly at every built point). Independently of the
(GR-5) reading, each built placement is certified as a pencil-panel
realization of `G′` by `kbare_common.verify_pencil_witness` — green at
every instance run. What is *not* re-proven here is the (GR-5) statement
restated at `G′` as a theorem; that two-line adaptation is the named gap,
and it is the only one. (The witness being ℚ(i) rather than ℚ is harmless:
the chart's parametrization is defined over ℚ and irreducible, so
independence at any extension-field point forces generic independence,
and (ANH-9)(iii)'s own ℚ-density argument then supplies rational points.)

### Step FR4 — (FR-5): the battery, and the residue's new shape (FR-R1)

> **(FR-5)** *(measured, with exact per-point certificates)* Over the full
> §(K-ann) triple pool (named inventory + `outer.sweep_shapes`; the site
> census **reproduces (ANH-13)'s 1904 exactly**, asserted):
>
> - **pattern availability 1904/1904** — every bare-cycle site admits a
>   pattern colouring meeting (FR-4)'s hypotheses; 0 splits hit the
>   colouring cap, 0 `G′` hypothesis failures (`--pattern`, 13 s);
> - **30/30 exact certificates** — at all 6 census-pool bare-cycle sites
>   (the (ANH-10) pool) and the first 24 sweep sites, the built ℚ(i) point
>   passes every gate (bodies distinct, isotropy + conjugacy per edge,
>   closedHubNbhd ranks, `verify_pencil_witness`) and has `C ≠ 0` by two
>   routes (`rank = 6` and `det₆ ≠ 0`), each with a **negative control**:
>   a criterion-violating colouring of the same site builds to a point
>   with `C = 0` exactly (`--transport`, 25 s).

So on the bare-cycle stratum the chart-to-frame residue is **discharged at
every site the arc can enumerate, and discharged by a recipe rather than a
sample** — the first time either side's dominance residue has moved by an
argument-shaped step. What is left for class uniformity is exactly:

> **(FR-R1)** *(open — the (ANH-14) residue's reduced form)* Every
> bare-cycle site of every `k = 4` class triple admits a pattern colouring
> ((FR-4)'s hypotheses). This is a **colouring-existence question with no
> rank, no counting, no balance and no tree-triple content**: the six-edge
> pattern forces alternation around the cycle (consecutive frame edges
> sharing a real body must differ — same-family adjacency is
> automatically the *same line*), and the remaining content is that the
> three same-family edges can be kept in **three distinct components**,
> plus the two placement-free legality clauses. Per shape it is decidable
> by the same finite scan the driver runs; measured, no shape needs more
> than the 8192-colouring budget and none misses. Compare §(K-grid)
> (GR-15): both are colouring-existence residues, but (FR-R1) carries no
> spline/rank side at all — it is strictly closer to pure graph theory,
> and Step G12's one-free-bit-per-branch structure applies verbatim.

The boundedness caveat transports from (ANH-14)(b) unchanged: the pool is
`outer.sweep_shapes` (`|V°| ≤ 5` families plus the named habitats), so
"every class shape" is **not** established — what is established is the
criterion, its per-site decidability, and a 1904/0 record over the sweep.

### Step FR5 — (FR-6): the (OC-16) side at θ(3,4,5) — constructed non-containment, and the (AC-9) wall

θ(3,4,5) is the `ℓ_min = 5` stratum's unique named class inhabitant
(§(K-out) *Step O12*: 8 of 5226 POOL-CW pairs; the theta remark of
(OC-10)). Its `G′` has 8 admissible colourings; both companion ends are
degree-3 hubs; per end the length-5 chain of `K = (H/X) − e₁` exists and
`R` at any placement satisfies (OC-15)'s pointwise containment
`R ⊆ span{chain lines}`.

> **(FR-6)** *(exact per point; the criterion equivalences asserted per
> colouring per end; `--outer`, 5 s)* At every one of the 8 colourings ×
> 2 ends:
>
> - `dim span{chain lines} = 5` (the alternating chain always splits 3–2
>   with distinct lines), and both `Δ = det₆[chain, C(h,a)]` and the outer
>   line's span membership match their combinatorial predictions ((FR-3)(ii)
>   applied to `Δ`; (FR-3)(iii) for membership) — **16/16, asserted**;
> - **4 of 8 colourings land on `(rank, dim R_a) = (54, 1)`** — target
>   rank, hard stratum, by `outer.stratum_at` at the dehomogenized ℚ(i)
>   placement; the other 4 are off target rank;
> - every on-stratum colouring has `Δ ≠ 0` at **exactly one** end — so
>   **(OC-8)'s literal statement is inhabited by construction**: an
>   explicit, combinatorially-specified, exact chart point of the
>   hard-stratum target-rank locus with `L_b ⊄ R₁` (or the `c`-mirror).
>   4/8 colourings are such witnesses;
> - the **strict availability package** — additionally `λ ≠ 0` at the same
>   point — is **0/8**, and the failure is exact and named: at a σ-fixed
>   degree-3 hub the (AC-9) coincidence must land on one of the three edge
>   pairs, and at every on-stratum colouring it lands on `{e₁, C(b,u)}` at
>   the `Δ ≠ 0` end (`λ = 0` by the coincidence, §(K-out) (OC-12)'s first
>   branch), while the colourings whose coincidence pair is `{e₁, C(b,a)}`
>   — which give `Δ ≠ 0 ∧ λ ≠ 0` — are exactly the off-target ones.

Three readings, kept apart. *(i)* For (OC-8) as recorded the constructed
points are already witnesses — non-containment needs no `λ`. Per shape
this adds nothing at θ(3,4,5) (POOL-G's sampled frames witness more), but
the witness is now **recipe-shaped**: its conditions are a colouring
pattern plus one measured rank pair, the ingredients a class-uniform
statement could quantify. *(ii)* For the *availability* consumer the
σ-fixed witnesses hit a genuine wall: (AC-9) makes *some* coincidence at
the hub unavoidable, and the measured anti-correlation (on-stratum ⟺ the
coincidence sits on the availability-killing pair) means **no σ-fixed
point of θ(3,4,5) is a strict witness**. Whether the anti-correlation is
structural (an interaction of the (AC-4) block ranks with the hub's colour
pattern) or shape-specific is **open** — it is this section's sharpest
open question, and a mechanism either way would be informative: structural
⟹ σ-fixed witnesses can never serve the strict form and the witness half
needs a non-σ-fixed deformation (e.g. (OC-14)'s slide launched *from* a
grid point); shape-specific ⟹ a wider `deg_H = 2` battery (item 2 of
*What would change this*) finds strict witnesses elsewhere. *(iii)* The
`dim R_a = 1` finding is independently valuable: it is the first evidence
that the σ-fixed locus **meets the hard stratum at target rank** — the
(K-tight) frame's habitat — constructively, not by sampling.

### Step FR6 — (FR-7): the irreducibility ingredient, located

> **(FR-7)** *(assessment; the (ANH-14) half is an argument, the (OC-16)
> half names an open object)* The fan-out asked where irreducibility must
> hold. The answer splits:
>
> - **(ANH-14) side: nothing new is needed.** The stratum is the whole
>   chart of the triple; §(K-ann) (ANH-9)(ii) supplies its irreducibility;
>   (FR-1) + one witness point finishes. This is why *Step FR4* could run
>   to completion with no new geometry.
> - **(OC-16) side: the smallest object is the hard-stratum target-rank
>   locus of the (shape, split) chart** — and it is needed **only** to
>   combine separately-witnessed open conditions (availability off `C₀`,
>   the coincidence off, (Λ0) clauses, …) without exhibiting one point
>   satisfying all simultaneously. A single simultaneous witness evades it
>   entirely — which is what POOL-G's sampled frames de facto are, and
>   what *Step FR5*'s constructed points are for the non-containment
>   conjunction. What would prove it: exhibit the locus as the image of an
>   irreducible parametrization, the same trick (ANH-9)(ii) uses for the
>   chart. A concrete foothold now exists: each on-stratum colouring's
>   grid family (one Fraction parameter per colouring component) is an
>   irreducible rational family whose sampled member lies on the locus; if
>   `dim R_a = 1` holds generically along it (one exact point off the
>   rank-drop divisor decides, per colouring), the locus contains a named
>   irreducible subvariety through each constructed witness — not the
>   whole locus, but enough to run (FR-1) *relative to that subvariety*
>   for any condition evaluable on it.
>
> **Struck as unnecessary (2026-08-19, direction OCON).** §(K-out) (OC-17)
> shows the (OC-16) side needs no dedicated irreducibility argument at all:
> the hard-stratum target-rank locus is Zariski **open** in the whole pencil
> chart (an intersection of two maximal-rank conditions), so its
> irreducibility is inherited from the chart's own — already owned by
> §(K-ann) (ANH-9)(ii) — and the foothold above is unnecessary rather than
> open. *What would change this* item (iii) below is struck on the same
> ground.

### Verdict — what this buys each residue, exactly

- **§(K-ann) (ANH-14) / the (K-ann) gap-map cell**: the chart-to-frame
  dominance residue on the bare-cycle stratum is **replaced by (FR-R1)**
  (pattern-existence), discharged at 1904/1904 enumerated sites with 30
  exact certificates. One named gap rides along ((GR-5) restated at `G′`).
  Coordinator action at landing: the (K-ann) row's residue sentence gains
  the (FR-R1) form; **status does not move** (class uniformity is exactly
  (FR-R1) + the sweep boundary).
- **§(K-out) (OC-16)/(OC-8) / the (K-out) row**: the evaluability battery
  is answered (combinatorial at grid points); (OC-8)'s non-containment is
  witnessed by construction at θ(3,4,5) with the witness on the hard
  stratum at target rank; the strict availability package is refuted for
  σ-fixed witnesses at θ(3,4,5) (0/8) with the (AC-9) mechanism named and
  its structurality open. **Status does not move.**
- **§(K-grid) *Step G13***: the convergence rider's assessment is now a
  theorem-shaped record: the candidate supplier works, the lemma shape is
  (FR-1), and the two cautions it carried (semicontinuity not guards;
  transport to contracted objects) are both discharged — the second by
  regridding at `G′`.

### Verification

`notes/scripts/w4/framedom.py` (new, untracked; exact ℚ/ℚ(i), stdlib only;
seeded rngs, seed 20260807 printed per mode; no `set` printed). Imports
only catalogued primitives and the owning drivers read-only: `exactcore`
(`rank`, `wedge2`, `dot`), `closure` (`colourings`, `components`,
`grid_point`, `ruling_A_line`/`ruling_B_line`, `Gauss`), `grid`
(`build_fixed_config_params`, `proportional`), `repin` (`span_basis`),
`outer` (`split_data`, `companions4`, `stratum_at`, `named_inventory`,
`sweep_shapes`), `annih` (`habitats4`, `path_edges`), `shrink`
(`hp_edge_rows`, `census_pool`), `anhr1` (`core_decompose`), `outerwide`
(`companion_sets`, `chain_to_weld`), `kbare_common` (`verts_of`, `is_2ec`,
`verify_pencil_witness`), `nogood_subdiv` (`hcard_ok`). Two local devices,
each named as such in its docstring: `det6` (no 6×6 determinant primitive
exists; always cross-checked against `exactcore.rank`) and `chn_sets` (the
*set-valued* closed hub neighbourhoods; the catalogued
`kbare_common.closed_hub_nbhds` returns cardinalities only — a candidate
*Divergences* row for the landing commit). `notes/scripts/m2/framedom.m2`
(new, untracked; the layer's fourth driver; version line `1.26.06` second,
`randomness: none`; convention-3 pin (FR-M0) ties `grid_point` / `wedge2` /
`PL` to their canonical Python homes through the shared instance value
4608). Nothing existing is modified
(`git diff --name-only -- '*.py' '*.m2'` empty), so the figure-invariance
gate discharges on that check alone. From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --rulings    #  2 s  (FR-2) + (FR-3) measured
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --pattern    # 13 s  (FR-5) availability, 1904/1904
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --transport  # 25 s  (FR-5) exact certificates, 30/30
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --outer      #  5 s  (FR-6) at theta(3,4,5)
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --validate   #  2 s  machinery + the cross-language pin
M2 --script notes/scripts/m2/framedom.m2                           #  1 s  (FR-M0)-(FR-M3)
```

All five Python modes byte-identical under `PYTHONHASHSEED` 0 and 999; the
M2 driver byte-identical across two runs; every invocation far inside the
600 s budget. No figure anywhere in this section is a
`place_pencil_general` rate; nothing gates on `repin.star_generic`
(σ-fixed points never pass it, (AC-9)); every claim is an existence
witness, an exact identity, or an exhaustive scan of a pinned finite pool.

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (FR-1) | — | **proof-level** (two lines of algebraic geometry); no driver can test a lemma statement |
| (FR-2)(i)/(ii) | `--rulings`, `(FR-M2)`/`(FR-M3)` | rank 3 per family over 8 params + all 3-subsets independent + all 4-subsets dependent; the function-field rank statements |
| (FR-2)(iii) | `--rulings` | `rank(x − ⋆x) = 0` on `W_A`, `rank(x + ⋆x) = 0` on `W_B` |
| (FR-3)(i) | `--validate` | hinge line of a conjugate pair ∝ the shared ruling line, both families |
| (FR-3)(ii) | `(FR-M1)` + `--rulings` + `--transport` | the identity over the function field; the constant at 20 draws; **both directions** at built sites (criterion ⟹ `det ≠ 0`; violation ⟹ `det = 0`, the negative controls) |
| (FR-3)(iii) | `--outer` | span-membership prediction == exact membership, 16/16 colouring-ends |
| (FR-4) | `--transport` | every hypothesis of the statement asserted at each of 30 built points (distinctness, LI, isotropy/conjugacy, `verify_pencil_witness`, `C ≠ 0` two routes) |
| (FR-4)'s named gap | — | **not driver-testable**: (GR-5) restated at `G′` is prose; its hypotheses are what `--pattern`/`--transport` assert per instance |
| (FR-5) | `--pattern` | the 1904-site scan, the census pin `== 1904`, 0 caps, 0 hypothesis failures |
| (FR-6) | `--outer` | the 8-colouring table: `stratum_at`, `Δ`, membership, and both criterion equivalences asserted per row |
| (FR-7) | — | **assessment**; its foothold's testable half (generic `dim R_a` along a colouring family) is *What would change this* item 3, not run |
| (FR-R1) | — | **still open, and still the point**: `--pattern` tests the pool, not the class |

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(FR-1)** | the minimal dominance lemma; "dominance" over-asks | **proven-informally** (standard) |
| **(FR-2)** | ruling decomposition, Veronese structure, ⋆-eigen identification | **proven** ((FR-M1)–(FR-M3) identities; eigen half measured exactly) |
| **(FR-3)** | at grid points every 6×6 hinge-line determinant — both bad divisors included — is the 3–3-distinct colouring criterion | **proven-informally** (conjugate-pair step + (FR-2) + (FR-M1); asserted both directions at every built instance) |
| **(FR-4)** | pattern colouring ⟹ exact chart witness ⟹ (ANH-R1) β-clause at the site | **true-modulo-named-gap** — the (GR-5)-at-`G′` restatement (hypotheses machine-checked per instance; `verify_pencil_witness` green throughout) |
| **(FR-5)** | availability 1904/1904; 30/30 exact certificates with negative controls | **measured** (exhaustive over the pinned pool; each certificate is itself a proof at its site via (ANH-9)(iii)) |
| **(FR-6)** | θ(3,4,5): 4/8 colourings on the hard stratum at target rank, each a literal (OC-8) witness; strict package 0/8 with the (AC-9) mechanism | **exact per point**; the anti-correlation's structurality **open** |
| **(FR-7)** | irreducibility located: un-needed on the (ANH-14) side, needed only for condition-combination on the (OC-16) side, smallest object named | **assessment** (argument, no driver) |
| **(FR-R1)** | class-uniform pattern-existence | **open** — the reduced residual this section leaves |

**Class uniformity is untouched. No gap-map status moves.**

### What would change this

*(i)* **A proof of (FR-R1)** — alternation around the cycle is nearly free
(forced at real degree-2 bodies, chosen at hubs); the content is keeping
the three same-family edges in distinct components. Step G12's
one-free-bit-per-branch structure plus girth 6 look sufficient for a
direct argument, and a refutation would need a shape whose *every*
admissible colouring merges two non-adjacent frame edges in both
families' component structures — none among 1904. This is the direction's
chief hand-off, and it would close the (ANH-14) residue on the whole
bare-cycle stratum *as an argument*.

*(ii)* **A `deg_H(h) = 2` battery beyond θ(3,4,5)** for the (OC-16) side:
(FR-6)'s machinery needs only a degree-3 hub end and the chain form of
`R`, i.e. §(K-out) (OC-15)'s `ℓ_min = 5` stratum — 8 POOL-CW pairs, all
reachable by the same driver pattern. It would decide whether the strict
package's 0/8 is θ(3,4,5)-specific or structural.

*(iii)* **The (FR-7) foothold — struck as unnecessary (2026-08-19, direction
OCON), not closed or delivered.** The original ask: per on-stratum colouring,
one more exact point of the same colouring family off the `dim R_a` rank-drop
divisor would certify generic `dim R_a = 1` along that irreducible family —
the first named irreducible subvariety inside the hard-stratum locus. §(K-out)
(OC-17) removes the need for it: the locus is already an open subset of the
(irreducible) whole chart, so no dedicated subvariety needs naming. This item
is one of the un-commissioned (FR-6) follow-ons; striking it as unnecessary is
the **opposite** of entering it — no bar was crossed.

*(iv)* **A structural account of the on-stratum ⟺ coincidence-pair
anti-correlation** ((FR-6)) — an (AC-4)-block-rank computation over the
colouring's class structure at `G′`, finite per shape. Either verdict
re-routes the strict-witness question.

*(v)* **The (GR-5)-at-`G′` restatement, written** — two lines of prose in
§(K-grid) or here, discharging (FR-4)'s named gap; a compiler spike is
not needed at the informal tier, but the Lean-side chart objects exist
(`Engine.lean`) if a later pass wants the pin exact.

*(vi)* **An (ANH-16)(ii)-style cost note is unnecessary here** — every
mode is seconds — but a *wider* pattern scan (lifting `sweep_shapes`'
`|V°| ≤ 5` cap) would move the (FR-5) boundary; a miss found there would
be a genuine (FR-R1) counterexample and would re-aim item (i) at repair.

**Continuation (2026-08-07, fifth fan-out direction PEX) — (FR-R1) is PROVEN: the bare-cycle stratum is *finite*, its frame has a normal form that makes the 3–3 split and the distinct-component clause automatic, the legality clauses are read exactly (one of them is a proper edge-2-colouring of the hub-hub graph, the *only* place a refutation could have lived), and the whole stratum is enumerated exhaustively (22 isomorphism classes, 76 sites, 1976 labelled instances, all pattern-available) — so (ANH-14)(b)'s boundedness caveat dissolves rather than widens, with the sweep's coverage measured at 14 of 22 classes and §(K-ann) *Step A14*'s `c′ ≤ 1` cells re-derived.**

Answering `notes/Pencil-fanout.md` §"Fifth fan-out" → Direction PEX, i.e.
§(K-frame) *Step FR4*'s residual **(FR-R1)** and *What would change this*
item (i) — the section's own chief hand-off. Read against §(K-frame) *Steps
FR0–FR3* ((FR-1)/(FR-3)/(FR-4)); §(K-ann) *Steps A14/A15* ((ANH-13)(i)/(iv),
(ANH-14)(a)/(b)); §(K-grid) *Step G12*; and the *Shared dictionary*'s (R3)
`def(C_k) = max(0, k−6)`, (R4) `hcard`, (SD-6) branch length ≤ 5, §(K-ind)
*Step I2* (girth ≥ 7). Driver: `notes/scripts/w4/patexist.py` (new,
untracked; imports `framedom` / `closure` / `outer` / `shrink` / `annih` /
`nogood_subdiv` read-only). **No Macaulay2 leaf was opened** — the question
is combinatorial and stayed combinatorial; the reserved `m2/patexist.m2` is
returned unused.

**Status, stated before the mathematics.**

- **(FR-R1) is PROVEN on the bare-cycle stratum, and the proof is not a
  wider battery.** Two independent halves. *(i)* A **uniform structural
  argument** ((FR-9)–(FR-11)) that derives the 3–3 split and the
  distinct-component clause outright, with no case left over, and reads
  legality clause (ii) as an exact equivalence. *(ii)* An **exhaustive
  enumeration of the whole stratum** — because the stratum is **finite**:
  a bare-cycle site forces `c(G) = 3` ((ANH-13)(iv)), hence
  `(|V|,|E|) = (16,18)`, `n_hub ≤ 4`, and finitely many branch-length
  tuples. Four hub multigraphs; **22 isomorphism classes of shape carrying
  a bare-cycle site, 76 sites among them**; enumerated as 470 labelled
  shapes and **1976 labelled sites, 1976 pattern-available**, none scarcer
  than 16 pattern colourings out of 32 admissible.
- **(ANH-14)(b)'s boundedness caveat is not widened — it is discharged.**
  (FR-5)'s 1904 sites came from `outer.sweep_shapes` (`|V°| ≤ 5` plus named
  habitats). On this stratum the cap **cannot bind** (`n_hub ≤ 4`), and the
  sweep's *shape* coverage was nevertheless incomplete, and (FR-14)
  measures the shortfall at the only granularity that means anything —
  **isomorphism classes of shapes**. Of the four possible hub multigraphs
  the sweep carries **two** (`θ³`-at-`c = 2` aside, `θ⁴` contributes nothing
  and `K4` contributes everything it has); the `n = 3` multigraph with
  multiplicities `(1,2,2)` and the `n = 4` "C₄ with two opposite edges
  doubled" are **outside the sweep entirely**. Result: the sweep pool covers
  **14** of the stratum's **22** iso classes — all 14 inside the `K4` family
  — carrying **58** of its **76** sites; the 8 unswept classes carry the
  other **18**. **No iso class the pool knows is missing from the
  enumeration (0/14).**
- **Neither `1904` nor `1976` counts distinct mathematical objects, and
  (FR-14) says so with the arithmetic.** Both are *labelled-instance* counts
  over shape lists that carry isomorphic duplicates by design (the sweep
  families overlap each other and `named_inventory` re-lists habitats): one
  `K4` iso class alone is carried **49 times** in the pool. Exactly,
  `1904 = 58 + 1846` and `1976 = 76 + 1900`, the second summand being the
  duplicate-induced over-count in each. So the `1904` vs `1896` gap that
  looked like eight missing sites is **a multiplicity artifact of two
  differently-built lists over the same 14 classes** — neither census is
  missing anything, and the canonical figures are **14 classes / 58 sites**
  (swept) against **22 classes / 76 sites** (complete).
- **The one place a refutation could have lived is named, constructed, and
  then shown unrealizable.** Legality clause (ii) is **exactly** "the
  hub-hub subgraph `Λ` of `G′` is properly edge-2-coloured" ((FR-10)(ii),
  asserted over 8728 (split, colouring) pairs). So a shape whose `Λ` has an
  **odd cycle** would have *no legal admissible colouring at all*, refuting
  (FR-R1) at every one of its bare-cycle sites. The driver **constructs**
  such a graph and confirms 0 legal colourings out of 1024, with an
  even-cycle negative control at 4 of 4096 — parity, not size, is the
  mechanism. It cannot happen here: a `Λ`-cycle is a cycle of `G` on hubs
  only, of length ≥ 7 (girth), while `n_hub ≤ 4`.
- **Legality clause (i) ("all bodies distinct") is *vacuous* on this
  stratum**, not merely satisfied: over **every** admissible colouring of
  **every** site of the complete stratum the collision count is **0**
  ((FR-12)), and the characterization behind it (a collision is always a
  pair of length-2-branch interiors) is asserted, not assumed. The uniform
  reason is a short girth-7 + branch-length count, given in *Step FR11*.
- **The recipe is a formula, not a search.** (FR-11) builds one colouring
  per site from the site's combinatorics — frame branch bits forced to
  alternate, `Λ` properly 2-coloured, every other bit the constant 0 — and
  its **first** variant is a pattern colouring at **1904/1904** pool sites
  and **1976/1976** stratum sites. The A/B swap and the second constant are
  never needed.
- **What does not move.** (FR-4)'s named gap — §(K-grid) (GR-5) restated at
  `G′` — stays exactly as named; this direction does not touch it. The
  (OC-16) side is untouched. **Class uniformity of `hK` is untouched**: what
  closes is the (ANH-14) chart-to-frame residue *on the bare-cycle stratum*
  — (ANH-13)'s `c′ = 1` column, 1904 of the swept 6426 length-5-branch
  sites (29.6 %), i.e. the (ANH-R1) β-clause is now proven at those sites
  and untouched at the other ~70 %.

### Standing notation (on top of §(K-frame) *Standing notation*)

`G` a `k = 4` class shape; `v` an eligible split with `b — v — a — c` the
split branch (`deg v = deg a = 2`, `b, c` hubs); `G′ = G − v + ab`;
`H = G − v − a = G′ − a`; `P = [b,x₁,x₂,x₃,c]` a length-4 companion; `X` the
weld. A **hub** is a vertex of degree ≥ 3; a **branch** is a maximal path
with degree-2 interior and hub ends; `G°` is the hub multigraph, `Λ` the
hub-hub subgraph of `G′` (equivalently: the length-1 branches). `Γ_A`, `Γ_B`
are the two colour classes of `Λ` under an admissible `col`. `n_hub = |V(G°)|`.
`--frame` etc. name modes of `patexist.py`.

### Step FR7 — (FR-8)/(FR-14): the bare-cycle stratum is FINITE, here is all of it, and here is what the sweep was missing

> **(FR-8)** *(proven; census driver-asserted, `--strat`)* Every bare-cycle
> site has `c(G) = 3`, and therefore:
>
> (i) `(|V(G)|, |E(G)|) = (16, 18)`; `Σ_{hubs} deg = 2c − 2 + 2n_hub` with
> every hub of degree ≥ 3 gives **`n_hub ≤ 2c − 2 = 4`**; `G` has exactly
> `c − 1 + n_hub = n_hub + 2` branches, of total length 18 and each of
> length ≤ 5 ((SD-6)); and `G°` has **no loop** (a loop branch is a cycle of
> `G` of length ≤ 5).
>
> (ii) Hence `G°` is one of exactly **four** connected loopless multigraphs
> with `n + 2` edges and min degree 3 on `n ∈ {2,3,4}` vertices:
> `n = 2` with a single 4-fold edge; `n = 3` with multiplicities `(1,2,2)`;
> `n = 4` cubic — either `K4` or `C₄` with two opposite edges doubled.
>
> (iii) The `n = 2` family carries **no** `k = 4` triple (four branches of
> total 18 with the split branch 3 and each ≤ 5 forces `(3,5,5,5)`, which
> has no length-4 `b`–`c` companion). So the stratum lives over
> `n_hub ∈ {3,4}`.
>
> (iv) Enumerating all branch-length tuples over (ii): **600** class shapes
> carrying a (length-3 split branch, length-4 companion) pair; **470** of
> them carry a bare-cycle site; **1976** bare-cycle sites in total. Every
> shape met has `girth(G) = 7` and `girth(G′) = 6` exactly, and every branch
> of every `G′` has length ≤ 5.

*Why this is exhaustive, and where it exceeds `outer.sweep_shapes`.* Each
filter the enumeration applies is a **necessary** condition of the object
being enumerated — `c(G) = 3` ((ANH-13)(iv)); loopless and `n_hub ≤ 4` by
(i); split branch of length exactly 3 (that is what `orient`/`split_data`
means); a length-4 `b`–`c` companion (that is what `k = 4` means); branch
lengths in `[1,5]` ((SD-6), and the driver runs `lmax = 6` and observes the
maximum is 5, so the bound is not doing hidden work). `kslidecomb.shape_ok`
is the *class* certification and its `hnoRigid` half is tested at branch
granularity, i.e. it accepts a **superset** of class shapes — which is the
safe direction for an exhaustiveness claim. The sweep, by contrast, runs
`theta3` / `theta4` / `K4` / `K4+par` plus **simple** 5-hub graphs; at
`c(G) = 3` only `theta4` and `K4` are in range, so the `n = 3` `(1,2,2)`
multigraph and the `n = 4` doubled-`C₄` were never swept. Labelled site
counts per family are `K4` 1896, doubled-`C₄` 48, `n = 3` 32; but **labelled
counts are the wrong unit for comparing the two censuses** — see (FR-14).

**This is the sentence (ANH-14)(b) and (FR-5) had to hedge, and it no longer
needs hedging.** "Every class shape" *is* established on the bare-cycle
stratum, because on that stratum "every class shape" is a finite list.

> **(FR-14)** *(proven; asserted by `--recon`, which keys both censuses by
> shape isomorphism class — canonical over the ≤ 24 hub permutations, exact
> since `n_hub ≤ 4`)*
>
> (i) **The enumeration misses nothing.** Of the **14** isomorphism classes
> the (ANH-9) pool carries with a bare-cycle site, **0** are absent from the
> complete-stratum enumeration; all 14 lie inside the swept `K4` family. The
> enumeration carries **22**, so the 8 extra classes — 4 over the `n = 3`
> `(1,2,2)` multigraph, 4 over the `n = 4` doubled-`C₄` — are exactly what
> the sweep never saw.
>
> (ii) **Site counts are class-level invariants; the published totals are
> not.** The number of bare-cycle sites of a labelled shape depends only on
> its isomorphism class (asserted). Summed over classes: **58** for the
> pool's 14, **76** for the complete 22. The *labelled* totals are
> `1904 = 58 + 1846` and `1976 = 76 + 1900`, the second summand in each
> being the duplicate-induced over-count of a shape list that carries
> isomorphic copies (433 labelled shapes for 14 classes; 470 for 22). One
> `K4` class — hub multigraph `K4`, branch lengths `(1,1,3,5,3,5)`, 8 sites
> — is carried **49 times** in the pool, once by `named_inventory` (as
> `flank:K4 menu-blocked`) and 48 times by the `K4` sweep family.
>
> (iii) **Consequently the `1904` vs `1896` difference is a multiplicity
> artifact, not a missing-site gap in either direction.** Both lists cover
> the same 14 classes over the `K4` family; they weight them differently.
>
> (iv) **At `c(G) = 3` every length-5-branch site is a bare-cycle site**
> (`other5 = 0`, and no `e0 is None` branch occurs), asserted over all 470
> labelled shapes — which is (ANH-13)(iv) measured over the complete
> stratum rather than over the sweep.

**The `c′ ≤ 1` columns of §(K-ann) *Step A14*, re-derived over the complete
strata** (`--recon` part 3). The `c′` histogram
`{0: 8, 1: 1904, 2: 3846, 3: 276, 4: 392}` counts (shape, split, length-4
companion, length-5 branch) instances over the same pinned pool, so its
cells are labelled counts of the same kind:

| cell | complete stratum, per iso class | complete stratum, labelled | the landed pool figure |
|---|---|---|---|
| `c′ = 0` (`c(G) = 2`) | **2**, over **1** iso class — `θ(3,4,5)`, 2 eligible splits × 1 companion × 1 loop branch | 4 | **8** |
| `c′ = 1` (`c(G) = 3`) | **76**, over **22** iso classes | 1976 | **1904** |

`c(G) = 2` has one hub multigraph (three parallel edges), and with the split
branch pinned at 3, lengths ≤ 5 summing to 12 and a length-4 companion
required, **θ(3,4,5) is its unique inhabitant** — which re-derives §(K-out)
*Step O12*'s "unique theta class member" from the length arithmetic alone.

**What this does to the landed histogram: a framing fix, not a number
change.** Every cell is a *true statement about the pinned pool's labelled
shape list*, which is what `anhr1.py --size` measures and what its own
prose says ("over the full 4296-triple pool of *Step A9*"). It becomes wrong
only under a class-level reading — "1904 bare-cycle sites *exist*", "8
`c′ = 0` sites *exist*" — which the surrounding text does not quite make,
but which a reader can easily take. The repair is therefore (a) say
*labelled instances of the pinned pool*, not sites of the class; (b) record
the class-level figures above alongside; (c) record that at `c′ ≤ 1` the
sweep is **incomplete at the iso-class level** (14 of 22 at `c′ = 1`) and
that (FR-8) supplies the complete list. The 29.6 % ratio (`1904/6426`)
survives as a pool ratio and should be labelled as one; it is **not** a
class-level ratio, and no class-level ratio is available, since the `c′ ≥ 2`
cells sit where the `|V°| ≤ 5` cap genuinely binds.

### Step FR8 — (FR-9): the frame's normal form in `G′`

> **(FR-9)** *(proven; every clause asserted per site at 1904/1904 pool
> sites (`--frame`) and 1976/1976 stratum sites (`--strat`))* At a
> bare-cycle site:
>
> **(a) `H/P` is exactly (bare 6-cycle) ∪ β and nothing else.**
> `|E(H/P)| = 11 = 6 + 5` and `|V(H/P)| = 10 = 6 + 4`; β is not a loop
> (a loop of length 5 would be a 5-cycle of `H/P`, and `girth(H/P) ≥ 6`
> off `|E(H/P)| = 5` — §(K-ann) *Step A9*). So β joins two distinct cycle
> nodes, of `H/P`-degree 3; every other cycle node has degree 2.
>
> **(b) The frame is a 7-point open path in `G′`.** The cycle's nodes are
> `X` (always on it, (ANH-13) trap (b)) and five far bodies `z₁…z₅`; far
> bodies satisfy `deg_{G′} = deg_H = deg_{H/P}`. Reading the cycle from `X`
> gives `x — z₁ — … — z₅ — x′` in `H ⊆ G′`, with `x, x′ ∈ P` the two
> companion attachment points. (The closed-hexagon degeneration `x = x′` of
> (ANH-14)(a) occurs **0 times** in the whole stratum; the argument below
> does not depend on that.)
>
> **(c) `x` and `x′` are hubs of `G′`.** `b` and `c` are hubs by
> `split_data`; an interior companion vertex carries two `P`-edges plus its
> frame edge.
>
> **(d) `S := {i : deg_{G′}(z_i) ≥ 3}` has `|S| ∈ {1, 2}`.** `≤ 2` by (a);
> `≥ 1` because the frame has length 6 while every branch of `G′` has length
> ≤ 5 — `G′`'s branch multiset is `G`'s with the length-3 split branch
> shortened to 2, and `G′` has the same hubs as `G`. Measured over the
> stratum: `{1: 1928, 2: 48}`.
>
> **(e) Each hub `z_j` has all of its hub-hub edges on the frame.** Its
> three `G′`-neighbours are its two frame neighbours and β's first interior
> node, which has `H/P`-degree 2. So `z_j`'s `Λ`-edges are among
> `{f_{j−1}, f_j}`, and are present only when the corresponding frame
> neighbour is a hub — i.e. only at `j = 1` (`f₀ = x z₁`) or `j = 5`
> (`f₅ = z₅ x′`).
>
> **(f) No `H`-edge joins two frame vertices except the six frame edges and
> possibly the `P`-edge `x x′`.** Such an edge would be an extra
> `H/P`-edge between two cycle nodes, contradicting (a) (β has length 5, not
> 1); edges inside `P` are contracted away, and by girth the only `P`-chord
> is a `P`-edge. (`x x′ ∈ E(H)` at **576** of the 1976 sites.)
>
> **(g) When `|S| = 2`, EVERY hub-hub edge of `G′` is a frame edge.** Then
> both β-endpoints are far bodies, so `deg_{H/P}(X) = 2`, i.e.
> `Σ_{p∈P} deg_H(p) = 10`, i.e. `deg_G(b) = deg_G(c) = 3` and
> `deg_G(x_i) = 2`; hence `x = b`, `x′ = c`, the hubs are exactly
> `{b, c} ∪ {z_j}_{j∈S}`, and by (e)/(f) every edge between two of them is a
> frame edge.
>
> **(h) `Λ` is a disjoint union of paths on ≤ 4 vertices.** (R4) gives max
> degree ≤ 2; a `Λ`-cycle would be a cycle of `G′` on hubs only, hence
> (it cannot use `ab`, `a` having degree 2) a cycle of `G`, of length ≥ 7,
> while `n_hub ≤ 4`. Measured: only paths on 2 or 3 vertices occur.
>
> **(i) The frame is exactly `|S| + 1 ∈ {2,3}` COMPLETE, pairwise-distinct
> branches of `G′`.** Each maximal run between consecutive frame hubs has
> degree-2 interior and hub ends, hence is a whole branch; two runs are
> edge-disjoint and separated by a hub, so they are different branches.
> Run-length profiles over the stratum: `(1,5) 368, (2,4) 368, (3,3) 464,
> (4,2) 368, (5,1) 360` at `|S| = 1`, and `(1,2,3) (1,3,2) (1,4,1) (2,2,2)
> (2,3,1) (3,2,1)` at 8 each at `|S| = 2`.

### Step FR9 — (FR-10): the component law, and what the two legality clauses actually say

> **(FR-10)** *(proven; both halves driver-asserted, `--validate`)*
>
> **(i) Only hub-hub edges propagate a ruling component.** Within a branch
> the colours alternate ((AC-2) conjunct 4 / *Step G12*), so two same-family
> edges of one branch are never adjacent. Consequently: two hubs lie in the
> same `A`-component **iff** they are joined by a path of `A`-coloured
> hub-hub edges; a frame edge with **no** hub endpoint is a **singleton**
> ruling component; and every `A`-component is a star at a hub, a double
> star across an `A`-coloured `Λ`-edge, or a single interior edge. (Asserted
> hub-pairwise over every admissible colouring of every census split.)
>
> **(ii) Legality clause (ii) IS "`Λ` is properly edge-2-coloured".**
> `closedHubNbhd u` has three members exactly when `u` is a hub with two hub
> neighbours, and then it is `{u, w₁, w₂}` with `uw₁, uw₂ ∈ Λ`. If both are
> `A`, all three sit in one `A`-component and the clause fails. Conversely
> if no hub carries two same-family `Λ`-edges, `Γ_A` and `Γ_B` are
> matchings, every `Γ_A`-component has ≤ 2 hubs, and `{u,w₁,w₂}` is never
> mono. (Asserted as an **iff** over 8728 (split, colouring) pairs.)

**The one place a refutation could have lived, and the constructed witness
that shows the mechanism is real.** By (ii), a graph whose `Λ` contains an
**odd cycle** admits *no legal admissible colouring whatsoever*, so (FR-R1)
would fail at every one of its bare-cycle sites — a clean structural flank,
of exactly the shape `Pencil-strategy.md` §2.3 warns to look for. `--kill`
**constructs** such a graph (a 5-cycle of hubs, each with a pendant 2-path
to a common body): 1024 admissible colourings, **0** legal; and its
6-cycle-of-hubs control has 4 legal of 4096. So the mechanism fires and the
mechanism is **parity**, not size. It is unrealizable on this stratum by
(FR-9)(h) alone — and that is the whole of the argument's dependence on
`hnoRigid` beyond the class definition.

### Step FR10 — (FR-11): the recipe, and (FR-R1) proven

> **(FR-11)** *(proven; the construction runs green at 1904/1904 pool sites
> and 1976/1976 stratum sites, in its **first** variant every time)* At any
> bare-cycle site define a colouring of `G′` by:
>
> 1. **frame branches** — set the `|S| + 1` free bits so that the frame path
>    *alternates*: `col(f_i) = A ⟺ i` even;
> 2. **`Λ`** — properly edge-2-colour it (alternate along each `Λ`-path),
>    seeded by whatever step 1 already forced;
> 3. **every other branch** — the bit 0.
>
> This is well defined (step 1 by (FR-9)(i); step 2 by (FR-9)(h) plus the
> observation that the frame's `Λ`-edges are *consecutive* frame edges,
> hence already alternating; step 3 vacuously), and it is a **pattern
> colouring**: it meets (FR-4)'s (pattern) clause and both legality clauses.

*Proof of the pattern clause.*

**3–3.** The frame path has even length 6 and alternates. ∎

**Three distinct components per family.** Say `A = {f₀, f₂, f₄}`. By
(FR-10)(i) a frame edge with no hub endpoint is a singleton component, so it
is automatically distinct from everything; only *anchored* frame edges (those
with a hub endpoint) can collide, and two same-family anchored frame edges
collide iff some hub of one and some hub of the other are joined by a path
of same-family `Λ`-edges.

*Case `|S| = 1`, `S = {j}`.* By (FR-9)(e):

- `j ∈ {2,3,4}`: `z_j` has `Λ`-degree **0**, so its component is `{z_j}`.
  The anchored `A`-edges are `f₀` (at `x`) and, when `f_{j−1}` or `f_j` is
  `A`, that edge (at `z_j`); `x ≠ z_j`, so they are distinct. Mirror for `B`
  with `x′`.
- `j = 1`: `f₀ = x z₁` is `z₁`'s only `Λ`-edge and is `A`. Then `f₀` is the
  **only** anchored `A`-edge (`f₂`, `f₄` have no hub endpoint), so there is
  nothing to separate; and `Γ_B(z₁) = {z₁} ∌ x′`, so the anchored `B`-edges
  `f₁` (at `z₁`) and `f₅` (at `x′`) are distinct.
- `j = 5`: the mirror image.

*Case `|S| = 2`.* By (FR-9)(g) every `Λ`-edge is a frame edge; consecutive
frame edges alternate, so `Γ_A` and `Γ_B` are matchings, and a same-family
`Λ`-edge joining the hubs of two anchored same-family frame edges would be a
second same-family frame edge at a common frame vertex — impossible under
alternation unless it *is* one of them, which forces the two anchored edges
to coincide. ∎

**Legality (ii)** is step 2 plus (FR-10)(ii). **Legality (i)** is *Step
FR11*. ∎

> **(FR-R1) — PROVEN.** *Every bare-cycle site of every `k = 4` class triple
> admits a pattern colouring.* The pattern clause and legality (ii) hold by
> (FR-11) uniformly; legality (i) holds by (FR-12); and independently of the
> argument, the whole (finite) stratum is enumerated with a pattern
> colouring exhibited at every one of its **1976** sites, the scarcest
> having **16** of 32 admissible colourings pass.

**What this buys, said exactly.** By §(K-frame) (FR-4), a pattern colouring
at a site gives an exact ℚ(i) chart point of the triple with the universal
polynomial `C ≠ 0` there, and by §(K-ann) (ANH-9)(iii) that **proves** the
(ANH-R1) β-clause at that site. So **the (ANH-14) chart-to-frame dominance
residue is discharged on the entire bare-cycle stratum as an argument** —
1904 of §(K-ann)'s 6426 length-5-branch sites — with (FR-4)'s single named
gap ((GR-5) restated at `G′`) riding along unchanged. Nothing here touches
the other 4522 sites, the (OC-16) side, or class uniformity of `hK`.

### Step FR11 — (FR-12): legality clause (i) is *vacuous* on this stratum

> **(FR-12)** *(proven; characterization asserted and count measured over
> **every** admissible colouring of **every** stratum site, `--strat`)*
>
> (i) **Characterization.** Two bodies of `G′` share a grid point iff they
> lie in the same `A`-component and the same `B`-component. Such a pair is
> always **two interiors of length-2 branches**: hubs never collide with
> hubs (a `Γ_A`-link and a `Γ_B`-link would be the same `Λ`-edge in two
> colours); a hub never collides with a non-hub, and two *adjacent*
> non-hubs never collide, because each such configuration closes a cycle of
> `G′` of length ≤ 4, hence a cycle of `G` of length ≤ 5; and a degree-2
> body whose `A`-neighbour is a non-hub has `A`-component of size 2, which
> forces the partner to be that neighbour.
>
> (ii) **Vacuity.** No such pair exists at any colouring of any bare-cycle
> site. Let `u` (between hubs `p_A`, `p_B`) and `w` (between `q_A`, `q_B`)
> collide. If `{p_A,p_B} = {q_A,q_B}` the two branches close a 4-cycle of
> `G′` — impossible (`girth(G′) = 6`). Otherwise the `Γ_A`-path from `p_A`
> to `q_A` (length `t ≥ 1`) and the `Γ_B`-path from `p_B` to `q_B` (length
> `s ≥ 0`) close a cycle of `G′` of length `4 + t + s`, so `t + s ≥ 2`.
> Every `Λ`-edge on those paths is a **length-1 branch**, and every hub it
> meets is a distinct hub, so `t + s ≤ 3` by `n_hub ≤ 4`; and `t + s ≥ 3`
> already needs ≥ 5 distinct hubs. So `t + s = 2`, the cycle has `G′`-length
> 6 and therefore `G`-length 7 (it must run through the split branch, since
> `girth(G) = 7`), and it consists of two length-2/3 branches and two
> length-1 branches — total 7 of the 18 edge-lengths across 4 of the
> `n_hub + 2 ≤ 6` branches, leaving ≤ 2 branches to carry 11 with each
> ≤ 5. Contradiction. **Measured: 0 collisions.**

*(Read (FR-12)(ii) as the uniform reason behind a measured 0, not as a
substitute for it: the count is what the driver asserts; the argument is why
it had to be 0. The two together are why legality (i) needs no repair step
in the recipe.)*

### The (`≤3`-closedHubNbhd) line — which side this argument sits on

`notes/Phase39.md` *Blockers* records that feasibility propagation **as a
proposition** is refuted for any purely combinatorial `≤3`-closedHubNbhd
criterion (`not_pencilNondegFeasible_of_triangle_two_hubs`). **This
direction's results sit entirely on the other side of that line, and
(FR-10)(ii) is the clause that has to say so out loud.**

- (FR-10)(ii) is an equivalence about **one constructed configuration**: it
  says that the σ-fixed grid point built from a given `col` has, at each
  3-member closed hub neighbourhood, three non-collinear quadric points
  **iff** `col` 2-colours `Λ` properly. It quantifies over *colourings of a
  fixed graph*, never over placements, and it concludes about a **point**,
  never about `PencilNondegFeasible G`.
- Nothing here propagates: (FR-11) *constructs* a witness and (FR-4) reads
  its consequence through rank lower semicontinuity on the irreducible chart
  ((ANH-9)(iii)), exactly as §(K-frame) already does. There is no step of
  the form "the combinatorial criterion holds, therefore the graph is
  feasible".
- The two statements are in fact **logically independent**, and the
  `--kill` witness makes that concrete: its odd-`Λ`-cycle graph is one where
  *the σ-fixed grid construction can never be legal*, which says nothing
  about whether that graph is `PencilNondegFeasible` (a question about all
  placements). Reading (FR-10)(ii) as a feasibility criterion would be
  exactly the move the landed refutation forbids — so **do not**; it is a
  criterion for *this construction's* hypotheses.

**The coordinator's flagged hypothesis (F14) is therefore confirmed as
stated**, and the confirmation is sharper than the hypothesis: it is not
merely that (FR-4)'s clause is checked at a constructed point, it is that
the clause's exact combinatorial content ((FR-10)(ii)) is a statement about
`Λ`'s edge-colouring — an object that only exists once a colouring is
chosen, i.e. only downstream of the construction.

### Verdict — what this buys, exactly

- **§(K-frame) (FR-R1): PROVEN**, and the section's *What would change this*
  item (i) is discharged in the affirmative. The route item (i) sketched —
  "alternation is nearly free; the content is keeping the three same-family
  edges in distinct components; *Step G12*'s branch bits plus girth 6 look
  sufficient" — is **correct in shape and understated in strength**: the
  three same-family edges are kept apart *automatically* once the frame's
  normal form ((FR-9)(e)/(g)) is available, and the binding girth number is
  **7**, not 6, which is what makes legality (i) vacuous ((FR-12)).
- **§(K-ann) (ANH-14) / the (K-ann) gap-map cell**: the chart-to-frame
  residue on the bare-cycle stratum is **closed as an argument**, with
  (FR-4)'s named (GR-5)-at-`G′` gap the only rider. The residue sentence's
  (FR-R1) form can be retired in favour of "proven; one named gap".
  *Coordinator's call whether the cell moves; the status of `hK` does not.*
- **(ANH-14)(b)'s boundedness caveat: DISCHARGED on this stratum** (not
  widened). This is the first time in the arc that a "the pool is not the
  class" caveat has been removed rather than enlarged, and the reason is
  structural (`c(G) = 3` is finite), not computational.
- **A latent sweep gap, measured and bounded**: `outer.sweep_shapes` misses
  two of the four `c(G) = 3` hub multigraphs, i.e. **8 of the 22**
  isomorphism classes of the bare-cycle stratum, carrying **18 of its 76**
  class-level sites ((FR-14)(i)/(ii)). §(K-ann) *Step A14*'s `c′`
  histogram is the place this shows: its `c′ = 0` and `c′ = 1` cells are
  labelled pool counts, true as such and incomplete as class statements —
  the repair is spelled out in *Step FR7* and is **framing, not
  arithmetic**.
- **An incidental §(K-ann) gain, worth recording where (ANH-14) lives.**
  (ANH-14)(a) measured its "seven distinct points" clause at **6/6**
  census-pool sites and explicitly noted that distinctness was *not*
  measured over the full 1904. (FR-9)(b) measures it at **1904/1904** and
  at **1976/1976** over the complete stratum — and the degenerate
  closed-hexagon alternative `x = x′` **never occurs**. So (ANH-14)(a)'s
  hedge ("either way one of two universal polynomials governs the site")
  can be simplified: on this stratum it is always the **open 7-point
  chain**, hence always the single irreducible degree-12 `C` of
  (ANH-14)(c)/(d), never (e)'s closed-hexagon two-term form.
- **Class uniformity is untouched. No gap-map *status* moves.**

### Verification

`notes/scripts/w4/patexist.py` (new, untracked; graph-combinatorial only —
no placement is built, no arithmetic beyond graph search, so there is no
sampled object to guard and no exactness question to raise; the single
`random.Random` is `--kill`'s tie-break, seeded 20260807 and printed).
Imports only catalogued primitives and owning drivers read-only:
`exactcore` (`neighbors`), `kbare_common` (`verts_of`, `is_2ec`),
`nogood_subdiv` (`hcard_ok`, `triangles`), `closure`
(`alternation_classes`, `colourings`, `components`), `outer` (`split_data`,
`eligible_splits`, `shapes_from`, `companions4`), `shrink` (`census_pool`),
`annih` (`girth`, `path_edges`), `shrink` (`hp_edge_rows`), `anhr1`
(`core_decompose`), `framedom` (`bare_sites`, `pool_splits`, `chn_sets`,
`line_ids`, `crit_33`, `legality_free`). Seven local devices, each named as
such in its docstring: `branches_with_ends` and `shape_key` (the canonical
`closure.alternation_classes` returns a branch as an *edge set* with
parities and does not name its two hub ends, which is exactly what an
isomorphism key needs), `len5_sites` (`framedom.bare_sites` with the
`e0 is None` arm counted rather than skipped — and asserted equal to it on
the two arms they share), `frame_path` (the frame ordering — `bare_sites`
returns the six edges in the *contracted* cycle's order, which does not say
where the weld breaks them open), `lambda_graph` / `lam_components`,
`c3_hub_multigraphs`, and `collisions` / `both_len2_interiors`. Nothing
existing is modified (`git diff --name-only -- '*.py'` empty), so the
figure-invariance gate discharges on that check alone. From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --frame     # 12 s  (FR-9) at 1904/1904 pool sites
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recipe    # 12 s  (FR-11) constructed, 1904/1904
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --strat     #  3 s  (FR-8)+(FR-12), the COMPLETE stratum, 1976/1976
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recon     # 15 s  (FR-14) + the c' <= 1 cells re-derived
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --kill      # 12 s  cheap kill + the odd-Lambda-cycle witness/control
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --validate  # 12 s  (FR-10)(i)/(ii) + the free-bit dictionary
```

All six modes byte-identical under `PYTHONHASHSEED` 0 and 999; every
invocation far inside the 600 s budget. Nothing gates on `repin.star_generic`
(no placement is sampled anywhere), no figure is a `place_pencil_general`
rate, and every claim is an exhaustive scan of a pinned finite object, an
asserted equivalence, or a constructed witness.

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (FR-8)(i)–(iii) | — | **proof-level** (three lines of counting); the multigraph list it predicts is what (iv) enumerates |
| (FR-8)(ii) | `--validate`, `--strat` | the multigraph census printed and pinned at 4, with multiplicities |
| (FR-8)(iii)/(iv) | `--strat` | 0 shapes over the `n = 2` family; 600 shapes / 470 with sites / 1976 sites; `lmax = 6` with max branch 5; `(girth G, girth G') = (7,6)` at 470/470 |
| (FR-9)(a)–(i) | `--frame`, `--strat` | every clause asserted **per site**, 1904/1904 and 1976/1976, 0 misses; the histograms are the by-product |
| (FR-10)(i) | `--validate` | for every admissible colouring of every census split, `same A-component` == `connected in the A-coloured hub-hub graph`, hub-pairwise |
| (FR-10)(ii) | `--validate` | legality clause (ii) == `Λ properly edge-2-coloured`, as an **iff**, 8728 (split, colouring) pairs |
| the odd-`Λ`-cycle mechanism | `--kill` | a **constructed** odd-`Λ`-cycle graph: 0 legal of 1024; even-cycle control: 4 legal of 4096 (F13: the guard has a witness it must reject *and* a negative control) |
| (FR-11) | `--recipe`, `--strat` | the recipe's colouring passes `crit_33` **and** `legality_free` at 1904/1904 and 1976/1976, in variant `(flip=False, other=0)` every time — i.e. no search |
| (FR-12)(i) | `--strat` | every collision found over every colouring of every site is asserted to be a length-2-branch-interior pair (the assert stands whether or not any is found) |
| (FR-12)(ii) | `--strat` | the collision count over the complete stratum: **0** |
| (FR-14)(i) | `--recon` | both censuses keyed by iso class; `set(pool) − set(stratum)` **asserted empty**, and `set(pool) ⊆ K4-family classes` reported |
| (FR-14)(ii) | `--recon` | site count asserted constant on each iso class; `labelled == iso total + duplicate over-count` asserted for both lists; the 49-fold duplicate exhibited |
| (FR-14)(iv) | `--recon` | `other5 == 0` and `loop0 == 0` asserted at all 470 `c(G) = 3` labelled shapes; `len5_sites` asserted equal to `framedom.bare_sites` per split |
| the `c′ ≤ 1` cells | `--recon` | the complete `c(G) ∈ {2,3}` strata enumerated and their `c′ = 0` / `c′ = 1` counts printed at both granularities |
| (FR-R1) | `--strat` | the exhaustive colouring scan: **0** sites with zero pattern colourings, scarcest 16/32 |
| (FR-4)'s named gap | — | **untouched and not driver-testable**: (GR-5) restated at `G′` is prose |

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(FR-8)** | the bare-cycle stratum is finite: 4 hub multigraphs, 600 shapes, 470 with sites, **1976** sites | **proven** (counting + exhaustive enumeration; every filter a necessary condition, `shape_ok` accepting a superset) |
| **(FR-9)** | the frame's normal form: 7-point path, hub ends, `\|S\| ∈ {1,2}`, hub `z_j`'s `Λ`-edges are frame edges, no other frame chords, 2-or-3 complete distinct branches | **proven** (from `\|E(H/P)\| = 11` and girth; every clause asserted at 3880 site-instances) |
| **(FR-10)** | hub-hub edges are the only component propagators; legality (ii) **is** the proper edge-2-colouring of `Λ` | **proven** (both halves asserted as equivalences) |
| **(FR-11)** | the recipe; pattern clause + legality (ii) | **proven-informally** (uniform case analysis, no residue; construction green 1976/1976 first variant) |
| **(FR-12)** | legality (i) is vacuous on the stratum | **proven-informally** (girth-7 + branch-count argument), **measured 0** over every colouring of every site |
| **(FR-14)** | the two censuses reconciled by isomorphism class: 0 missing, 14 of 22 swept, the gap a multiplicity artifact; the `c′ ≤ 1` cells re-derived | **proven** (canonical keying, exact at `n_hub ≤ 4`; every step asserted) |
| **(FR-R1)** | class-uniform pattern-existence on the bare-cycle stratum | **PROVEN** — by (FR-11)+(FR-12) uniformly, and independently by exhaustive enumeration of the finite stratum |

**Class uniformity of `hK` is untouched. No gap-map *status* moves.**

### What would change this

*(i)* **RESOLVED in this draft, by (FR-14) and *Step FR7*'s table.** The
open item this slot carried — "a `c(G) = 3` figure quoted from
`outer.sweep_shapes` is suspect" — is settled: the sweep's `c′ ≤ 1` figures
are **correct as labelled pool counts** and **incomplete as class
statements** (14 of 22 iso classes at `c′ = 1`; 1 of 1 but 4× duplicated at
`c′ = 0`). The concrete edit to §(K-ann) *Step A14* is: keep the histogram,
say *labelled instances of the pinned pool*, add the class-level line
(`c′ = 0`: 2 sites over the single class θ(3,4,5); `c′ = 1`: 76 sites over
22 classes), and mark the 29.6 % as a pool ratio. **No landed number is
wrong.** What is *not* settled, and stays out of scope here, is the
`c′ ≥ 2` cells: there `|V°| ≤ 5` genuinely binds and no complete
enumeration is available (nor is one finite — `c(G) ≥ 4` shapes are
unbounded in `n_hub`).

*(i′)* **The duplication itself is worth a one-line note wherever pool
figures are quoted.** `--recon` measures 433 labelled shapes for 14 iso
classes (a 31× average, 49× at the worst class). That is by design — the
sweep families overlap and `named_inventory` re-lists habitats — but it
means **no pool count is a count of mathematical objects**, and any future
"N of M" over `outer.sweep_shapes` inherits the same caveat. This is a
`notes/scripts/README.md`-level observation, not a §(K-frame) one.

*(ii)* **Closing (FR-4)'s named gap** — (GR-5) restated at `G′` — would turn
(FR-R1)+(FR-4) into an unconditional discharge of the (ANH-14) residue on
the bare-cycle stratum. Two lines of prose in §(K-grid); the hypotheses are
already asserted per instance by `framedom.py --transport`.

*(iii)* **The same technique on the `c′ ≥ 2` strata.** Everything above
turns on `H/P` being *exactly* a 6-cycle plus one branch. At `c′ = 2`
(3846 sites, the largest stratum) `H/P − β` has 12 edges and 11 nodes and is
no longer bare, so (FR-9)(a) fails and the determinant law (FR-3) no longer
reduces to a 6×6 pattern — the pure condition there is (ANH-13)'s
`6m × 6m` branch-screw determinant. Whether a *pattern-colouring* analogue
exists for that determinant is the natural successor question, and it is
**not** a corollary of anything here.

*(iv)* **A transfer to §(K-grid) (GR-15)** (direction TCOL's target). The
transferable technique is not the recipe but its two enablers: *reduce the
colouring question to a statement about `Λ` alone*, and *use `hcard` + girth
to bound `Λ` so hard that the statement becomes vacuous*. (GR-15) carries a
spline/rank side that (FR-R1) does not, and its shapes are tight (hence
`c(G)` unbounded, hence `n_hub` unbounded), so the *finiteness* half — the
decisive one here — does **not** transfer. Say so plainly to TCOL: the
useful export is (FR-10)(i)'s component law and (FR-10)(ii)'s reading of the
closed-hub-neighbourhood clause, both of which are statements about
admissible colourings in general and hold verbatim at any shape.

*(v)* **A refutation would have to come from the mechanism (FR-10)(ii)
names** — an odd `Λ`-cycle, or a `Λ`-parity clash between two forced frame
`Λ`-edges. Both are constructible as graphs (`--kill` builds the first) and
both are excluded here by `n_hub ≤ 4`. Any future stratum with more hubs
should be checked against them **first**; they are the cheap kill for this
family of questions.

**Continuation (2026-08-19, sixth fan-out direction FRES) — (FR-4)'s named gap is CLOSED, and the closing needed a clause the gap's own name did not carry: (GR-5) restates at `G′` verbatim ((FR-15), every hypothesis either free or already driver-asserted), but (GR-5) is a *chart-MAP* statement — hub normals free, body points derived — while (ANH-9)(iii)'s semicontinuity consumes membership in the *chart VARIETY* of (ANH-9)(ii), whose parametrization runs the other way (hub points free, panel normals derived); (FR-16) supplies that second statement, and the mechanism is that at a σ-fixed configuration `normal ∝ point` makes the two parametrizations' genericity loci COINCIDE — both are exactly the closed-hub-neighbourhood LI clause `framedom.legality_free` already tests — so (FR-17) discharges the (ANH-14) residue on the WHOLE bare-cycle stratum with NO named gap, by formula rather than by search, and with no driver run at all.**

Answering `notes/Pencil-fanout.md` §"Sixth fan-out" → Direction FRES, i.e.
§(K-frame) *Step FR3*'s **(FR-4) named gap** and *What would change this* item
(v) — "the (GR-5)-at-`G′` restatement, written". Read against §(K-grid) *Step
G6* ((GR-5)) and *Step G13*; §(K-frame) *Steps FR3/FR4* ((FR-4)/(FR-5)) and
*Steps FR7–FR11* ((FR-8)–(FR-14), (FR-R1)); §(K-ann) *Steps A10/A15*
((ANH-9)(ii)/(iii), (ANH-14)); §(K-clos) (AC-2)/(AC-4)/(AC-9); §(K-ind) *Step
I2* ((I2), girth `≥ 7`); the *Shared dictionary*'s (R1)/(R3)/(R4). **No driver
was run and no driver was written**: every hypothesis this block consumes is
already asserted per instance by the landed `framedom.py --pattern` /
`--transport`, and everything on top is proof. The reserved
`notes/scripts/w4/fres.py` is **returned unused**.

**Status, stated before the mathematics.**

- **The restatement is real, and it is as cheap as the record predicted —
  but it is not the statement the consumer needs.** (FR-15) transports (GR-5)
  to `G′` hypothesis by hypothesis: `hcard` is **free** (it is a consequence of
  `hK`'s own `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` hypothesis,
  and independently of §(K-ind) (I2): the split leaves the hub set and the
  hub-hub subgraph `Λ` untouched); the non-hub star-rank-3 condition is **free**
  (admissible alternation at a degree-2 body *is* that condition); the
  3-member-`closedNbhd` clause is **free** (`girth(G′) ≥ 6`); the two remaining
  inputs are (FR-4)'s own legality clauses. Its **final** clause — "at a
  target-rank grid this *is* `hK`'s conclusion" — does **not** transport, and is
  dropped: `G′` is not tight.
- **The clause the gap's name did not carry.** (GR-5) concludes
  `pencilChartPoint (PencilSeed.ofCoord q) hubSel u ∝ pt_u`: the grid is
  reproduced by a **seed** of `Chart.lean`'s construction, whose free data are
  the **hub normals** and whose body points are *derived*. (ANH-9)(iii) instead
  runs rank lower semicontinuity **on the irreducible chart of (ANH-9)(ii)**,
  which is the image of the **opposite** parametrization — hub **points** free,
  panel normals derived, interiors panel-constrained — i.e. literally
  `widened.place_pencil_general`, what `outer.chart_point` and
  `dominance.base_seed` sample and what every §(K-ann)/§(K-out) figure is
  measured on. Being a point of the first parametrization's image makes a
  configuration a *pencil configuration*; it does **not**, by itself, put it on
  the second's irreducible chart, and a witness sitting on a different component
  of the pencil-configuration variety would make the semicontinuity step void.
  **This is the direction's one genuine finding**, and it is the reason the
  outcome is "gap closed **plus** a stated extra ingredient" rather than
  "restatement immediate".
- **The extra ingredient is discharged, and by the clause already tested.**
  (FR-16): identify planes with points through the σ-fixed quadric's form and a
  σ-fixed configuration's panel normal at a hub **is** that hub's point. The
  points-first parametrization needs two open conditions — *hub points in
  general position along `Λ`* (so the panel normal is determined) and *panel
  normals pairwise distinct at every degree-2 body with two hub neighbours* (so
  the interior meets are lines) — and σ-fixity makes both of them the **same**
  condition, namely `{pt_w : w ∈ closedHubNbhd(u)}` linearly independent at
  every body `u`. That is (GR-5)'s own LI hypothesis, `framedom.legality_free`'s
  clause (ii) (plus (i)), and it is asserted exactly at every one of the 30
  built points by `--transport`. So the σ-fixed grid point is in the image of
  the (ANH-9)(ii) parametrization **at its generic-fibre locus** — not merely in
  its closure.
- **What that buys: an unconditional discharge on the whole bare-cycle
  stratum.** (FR-17). With (FR-R1) proven ((FR-11)+(FR-12), and independently
  the exhaustive enumeration of the finite stratum), (FR-3)'s determinant law,
  (FR-16), (ANH-14) and (ANH-9)(ii)/(iii), the (ANH-R1) `β`-clause holds at
  **every** bare-cycle site of **every** `k = 4` class triple — 76 class-level
  sites over 22 isomorphism classes — with **no named gap**. The witness is a
  **formula**: (FR-11)'s recipe colouring with *any* injective assignment of
  **positive** rationals to the ruling components; `framedom.build_at`'s seeded
  retry loop is a convenience, not a step of the argument.
- **"Unconditional" is a statement about named gaps, not about tier.** The
  chain's standing is the arc's ordinary **proven-informally** — its weakest
  links are (ANH-14)(c), (ANH-9)(ii)/(iii), (FR-1) and (FR-16), all
  informal-tier algebraic geometry, none Lean-checked. Nothing here is a rate, a
  sample, or a genericity guard, and nothing gates on `repin.star_generic` —
  σ-fixed points never pass it ((AC-9)), and the argument never asks them to.
- **What does not move.** The (OC-16) side gains one retro-certification and
  nothing else ((FR-16) applies verbatim to (FR-6)'s θ(3,4,5) points, so those
  four on-stratum colourings are honest chart points of `G′` — which is what
  "the first constructed, non-sampled inhabitants of that locus" was asserting).
  The (FR-6) follow-ons ((ii)/(iii)/(iv) of *Steps FR0–FR6*'s *What would change
  this*) are **untouched and remain un-commissioned**. §(K-grid) (GR-15) and
  **`hK`'s class uniformity are untouched**; the other ~70 % of §(K-ann)'s
  length-5-branch sites are untouched. **No gap-map *status* moves.**

### Standing notation (on top of §(K-frame) *Standing notation* and *Steps FR7–FR11*'s)

For a loopless multigraph `Γ`: `H(Γ)` its hubs (degree `≥ 3`), `Λ(Γ)` its
hub-hub subgraph, `d_h` the number of hub neighbours of a hub `h` and `e_s` the
number of hub neighbours of a non-hub `s`. `hcard` (= (R4)) says `d_h ≤ 2`;
`e_s ≤ 2` is automatic. `closedHubNbhd_Γ(u) = {w : deg_Γ w ≥ 3 and (w = u or
w ∼ u)}` (`Motive.lean:82`) — so at a **hub** it is `{h} ∪ {hub neighbours}`
(`1 + d_h` members) and at a **non-hub** it is `{hub neighbours}` (`e_s`
members). `closedNbhd_Γ(u) = {u} ∪ N_Γ(u)`. We write `Chart(Γ)` for the pencil
chart of `Γ` in the precise sense fixed in *Step FR13* below. Points are
homogeneous over `ℚ(i)`; `⟨·,·⟩` is the standard symmetric form `Σ x_i y_i`,
whose isotropic quadric is (AC-2)'s fixed quadric `Q`, and it is used
throughout to identify `(P³)^*` with `P³` — under that identification a plane
and its pole are the same vector, which is exactly what "σ-fixed" (`normal ∝
point`, §(K-clos) *Step Z2*) says at every body.

### Step FR12 — (FR-15): (GR-5) at `G′`, hypothesis by hypothesis — and the one clause that does not transport

> **(FR-15)** *(proven-informally, at exactly (GR-5)'s own standing; every
> transported hypothesis is either a two-line graph argument given below or
> asserted per instance by `framedom.py --pattern` / `--transport`)* Let `G` be
> a `k = 4` class shape, `v` an eligible split with `b — v — a — c`, and
> `G′ = G − v + ab = G.splitOff v a b e₀`. Let `pt` be a σ-fixed grid
> configuration of `G′` from an admissible colouring such that
>
> - all bodies are pairwise distinct as projective points, and
> - at every body `u` of `G′`, `{pt_w : w ∈ closedHubNbhd_{G′}(u)}` is linearly
>   independent.
>
> Then there are selectors `hubSel`, `nbrSel` and an explicit seed `q` over
> `ℚ(i)` with
>
> `pencilChartPoint (PencilSeed.ofCoord q) hubSel u ∝ pt_u` and
> `pencilChartNormal (PencilSeed.ofCoord q) hubSel nbrSel G′ u ∝ pt_u`
>
> at **every** body `u` of `G′`.
>
> **(GR-5)'s final clause does not transport and is dropped.** "at a
> target-rank grid this **is** `hK`'s conclusion at `G`" is a statement about
> the *tight* shape `G`: `f(V(G′)) = f(V(G)) + 1`, so `G′` misses tightness by
> one and the count `6(|V|−1) − def` that `hK`'s conclusion carries is not the
> one a `G′`-grid attains. Nothing here re-derives it, and (FR-4)'s consumer
> does not want it.

*Proof.* (GR-5)'s proof is replayed verbatim; only its **inputs** need
transporting, and the table below does each one. The two clauses that are
genuinely graph-dependent are the last two rows, and both come out *free* at
`G′`.

| (GR-5)'s input | at `G` | at `G′` | why |
|---|---|---|---|
| `hcard` | class shape + feasibility | **free**, two independent ways | *(i)* `hK`'s own hypothesis `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` (`Escape.lean`, the `hK` slot of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`; **`hK` names `v`'s two neighbours `a, b` — the workbook's `b, a` — so `hK`'s `G.splitOff v a b e₀` is this section's `G′ = G − v + ab`, letters swapped and object identical**) unfolds to `IsNondegPencilRealization G′ …`, and the landed `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) gives `(G′.closedHubNbhd u).ncard ≤ 3` at every body — **`hcard` at `G′` is a hypothesis `hK` already carries about `G′` itself, not something transported from `G`.** *(ii)* Combinatorially, from `hcard` at `G`: by §(K-ind) (I2) `splitOff` at a degree-2 body leaves the hub set and the hub multigraph `G°` unchanged and shortens only the branch through `v` (here `3 → 2`), so the length-1 branches — i.e. `Λ` — are untouched; `v` and `a` are non-hubs, so neither the deleted edge `bv` nor the new edge `ab` is a hub-hub edge, and `closedHubNbhd_{G′}(h) = closedHubNbhd_G(h)` at every hub `h`. Asserted per instance: `hcard_ok(G′)` at all 1540 site-carrying splits, 0 failures ((FR-4)'s *Verification*, `--pattern`). |
| all bodies distinct | hypothesis | hypothesis | supplied by (FR-4) legality clause (i); **vacuous** on the bare-cycle stratum by (FR-12), and asserted exactly at every built point (`config_asserts`). |
| closed-hub-neighbourhood LI | hypothesis | hypothesis | supplied by (FR-4) legality clause (ii), whose exact combinatorial content is (FR-10)(ii)'s proper edge-2-colouring of `Λ`; asserted as an exact rank equality at every body of every one of the 30 built points (`--transport`). |
| isotropy / conjugacy of the configuration | (AC-2) | (AC-2) | graph-free; asserted per body and per edge at every built point (`config_asserts`). |
| non-hub **star rank 3** | hypothesis | **free from admissibility** | Let `s` be a degree-2 body of `G′` with neighbours `u, w`. Admissibility (`closure.alternation_classes`: the two edges at a degree-2 body get opposite rulings) gives `col(su) ≠ col(sw)`. Writing the grid map as the Segre embedding composed with a fixed `ℚ(i)`-linear isomorphism (`closure.grid_point` is bilinear in `(s:t)` and `(u:v)`, with invertible coefficient matrix), `pt_s = e_{s_s} ⊗ f_{u_s}`, `pt_u = e_{s_s} ⊗ f_{u_u}`, `pt_w = e_{s_w} ⊗ f_{u_s}` with `u_u ≠ u_s` and `s_w ≠ s_s` by distinctness — three tensors that are linearly independent in `K² ⊗ K²`. **So the alternation clause of admissibility *is* the star-rank-3 condition**, at `G′` and at `G` alike. |
| degree-2 bodies have **3-member** `closedNbhd` | "on a 2-edge-connected class shape" | **free** | Every non-hub of `G′` has degree exactly `2`: `G` is rigid so `deg_G ≥ 2` ((R1)), and by (I2) `splitOff` changes no surviving vertex's degree. Its two neighbours are distinct from it and from each other because `girth(G′) ≥ 6`: a `G′`-cycle either avoids `ab`, and is then a `G`-cycle, or uses `ab` and lifts to a `G`-cycle one edge longer, while `girth(G) ≥ 7` by (R3) + `hnoRigid` (§(K-ind) *Step I2*). Hence `IsFin3SelectorOf (G′.closedNbhd s) (nbrSel s)` is satisfiable with **no slot unassigned**, and `PencilSeed.ofCoord`'s `fillNbr := fillHub` coupling (`Engine.lean:89`) stays vacuous — the one clause of (GR-5)'s proof that reads the ambient graph at all. (`is_2ec(G′)` is asserted per instance anyway, 0 failures; 2-edge-connectivity of `G′` follows from that of `G` since suppressing a degree-2 body preserves it — but the proof needs only min degree 2 and girth `≥ 3`.) |

With the inputs in place the body of (GR-5)'s proof is unchanged and
graph-free: take `hubNormal w := pt_w`; at any body `u` every selected input of
`pencilChartPoint` lies in `pt_u^⊥` (isotropy for `u` itself, conjugacy for a
hub neighbour), `hcard` caps the selected inputs at 3, the LI hypothesis lets
the unused slots be filled inside `pt_u^⊥` keeping the triple independent, and
`cross₃` then returns a nonzero vector of the 1-dimensional annihilator, which
contains `pt_u`. Normals: at a hub the chart returns the seed's `hubNormal`; at
a non-hub it returns `cross₃` of the three `closedNbhd` chart points, each
`∝` its grid point, hence `∝ cross₃(pt_u, pt_{u'}, pt_{u''}) ∝ pt_u` by the same
isotropy/conjugacy argument, with the star-rank-3 row above supplying the LI. ∎

**What (FR-15) is worth, said plainly.** It is the statement the gap was
*named* after, it is true, and it is what `hK`'s conclusion object would need if
a later pass wanted `hK` itself at `G′`. It is **not** what (FR-4)'s consumer
needs — see *Step FR13*.

### Step FR13 — (FR-16): the clause the gap's name did not carry — chart-VARIETY membership, and why σ-fixity makes it free

**The correction, stated before the theorem.** §(K-grid) (GR-5) and §(K-ann)
(ANH-9)(ii) describe **two different parametrizations of the same incidence**,
and they run in opposite directions.

- **(GR-5) / `Chart.lean` — normals first.** Free data: the hub normals
  (`PencilSeed.hubNormal`, read only at `closedHubNbhd` members, i.e. only at
  hubs) plus the fill vectors. Derived: every body point, as
  `cross₃` of the selected normals. At a hub with two hub neighbours the point
  is fully **determined**; at a non-hub with two hub neighbours it sweeps the
  2-dimensional space `{n_{h₁}, n_{h₂}}^⊥`, i.e. the meet line of the two
  panels.
- **(ANH-9)(ii) / `widened.place_pencil_general` — points first.** Free data:
  the hub **points**. Derived: each panel normal, in the `≤ 2` linear
  conditions its hub neighbours impose; then each interior point, on the
  intersection of its hub neighbours' panels. This is the parametrization
  `outer.chart_point` and `dominance.base_seed` sample, and it is the one whose
  irreducibility (ANH-9)(ii) asserts and (ANH-9)(iii) consumes.

Both land inside the pencil-configuration variety of `G′`; neither is
*a priori* inside the other. So "the grid point is a chart point" in (GR-5)'s
sense does **not** license "(ANH-9)(iii) applies to it": the semicontinuity step
needs the witness on the **irreducible variety whose generic point defines
`M_pen^gen`**, and a witness on a different component of the configuration
variety would make the step void. **That is the clause (FR-4)'s named gap did
not name, and it is the one this step supplies.**

**The chart, made precise.** For `Γ` loopless with `hcard`, min degree 2 and
girth `≥ 3`, define the tower

1. `U_H ⊆ (𝔸³)^{H(Γ)}` — hub points, restricted to the open locus where at
   every hub `h` the `1 + d_h` points `{p_h} ∪ {p_u : u a hub neighbour of h}`
   are affinely independent (equivalently: their homogeneous lifts have rank
   `1 + d_h`);
2. `N → U_H` — fibre at `h` the punctured linear space
   `{n_h ≠ 0 : ⟨n_h, p_u − p_h⟩ = 0 ∀ hub neighbours u}`, of dimension
   `3 − d_h` **constantly on `U_H`**;
3. `N° ⊆ N` — the open locus where at every non-hub `s` with `e_s = 2` the two
   hub-neighbour panels meet in an **affine** line, i.e. their affine normals
   are independent (`widened.meet_line`'s nonzero-direction test);
4. `𝒫 → N°` — fibre at `s` the intersection of `s`'s `e_s` hub-neighbour
   panels, an affine subspace of dimension `3 − e_s`, constant on `N°`;

and `Φ : 𝒫 → (𝔸³)^{V(Γ)}` forgetting the normals, `Chart(Γ) := \overline{Φ(𝒫)}`.
Each stage is a Zariski-locally-trivial bundle of **constant** fibre dimension
over the previous, and `U_H` is a nonempty open subset of an affine space, so
`𝒫` is irreducible and rational over `ℚ`, `Φ(𝒫)` is irreducible and contains a
dense open of `Chart(Γ)`, and `Chart(Γ)` is irreducible. `hcard` is what makes
step 2 work at all (`d_h ≤ 2`, so the normal space is never `0`;
`place_pencil_general` returns `None` on `d_h ≥ 3` for exactly that reason).
**The restriction to `U_H` and `N°` is not decoration** — it is what makes the
fibre dimensions constant, hence what makes (ANH-9)(ii)'s phrase "the image of
an irreducible rational parametrization" literally true. This is the reading
this section uses, and the only one under which that phrase holds.

> **(FR-16)** *(proven-informally; its hypothesis is exactly (GR-5)'s LI clause,
> asserted per body at every one of the 30 built points by `framedom.py
> --transport` and equivalent, at injective ruling parameters, to
> `framedom.legality_free`)* Let `Γ` be loopless with `hcard`, min degree `2`
> and girth `≥ 3`, and let `pt : V(Γ) → P³` be a **σ-fixed** pencil
> configuration — every body isotropic, adjacent bodies conjugate — such that
>
> (i) all bodies are pairwise distinct as projective points and none is at
> infinity, and
> (ii) at every body `u`, `{pt_w : w ∈ closedHubNbhd_Γ(u)}` is linearly
> independent.
>
> Then `pt` lies in `Φ(𝒫)` — the **image** of the (ANH-9)(ii) parametrization at
> its generic-fibre locus, not merely in its closure — hence on the irreducible
> chart `Chart(Γ)` whose generic point defines `M_pen^gen`.
>
> *(Of the three standing hypotheses on `Γ` only **`hcard`** is used in the
> proof — it is what makes `d_h ≤ 2`, hence what makes the normal fibre of
> *Step FR13* stage 2 nonzero and `place_pencil_general`'s `return None` branch
> at three independent hub neighbours unreachable. Min degree 2 and girth `≥ 3`
> are carried because they are what makes the harness's degree bookkeeping
> (`neighbors`, `hn`) agree with the tower — a loop or a parallel pair at a
> degree-2 body would be counted once, not twice. Both hold at `G′` by
> *Step FR12*'s last table row. The affinity clause in (i) is likewise not a
> restriction: *Step FR14*'s parameter recipe supplies it outright.)*

*Proof.* Identify `(P³)^*` with `P³` by `⟨·,·⟩` and set `n_h := pt_h` at every
hub.

*(a) It is an incidence point.* `⟨n_h, pt_h⟩ = ⟨pt_h, pt_h⟩ = 0` is isotropy,
and `⟨n_h, pt_u⟩ = ⟨pt_h, pt_u⟩ = 0` for every neighbour `u` of `h` — hub or
not — is conjugacy. So each hub's whole closed star lies on the plane `n_h`.

*(b) The hub points lie in `U_H`.* At a hub `h`,
`{p_h} ∪ {p_u : u a hub neighbour}` **is** `{pt_w : w ∈ closedHubNbhd_Γ(h)}`,
because `closedHubNbhd` of a hub is that hub together with its hub neighbours
and nothing else. Hypothesis (ii) makes it linearly independent as homogeneous
`4`-vectors, i.e. of rank `1 + d_h`, which for affine points is exactly affine
independence — `U_H`'s condition.

*(c) The normal lies in the fibre, and the fibre has its generic dimension.*
`n_h = pt_h` satisfies the defining conditions by (a); and the fibre's dimension
is `3 − d_h` — its generic value — **precisely** because the rank in (b) is
`1 + d_h`.

*(d) `N°`.* At a non-hub `s` with `e_s = 2` and hub neighbours `h₁, h₂`,
`{n_{h₁}, n_{h₂}} = {pt_w : w ∈ closedHubNbhd_Γ(s)}` — `closedHubNbhd` of a
non-hub is exactly its hub neighbours — independent by (ii), so the two panels
are **projectively** distinct planes; (f) upgrades that to `N°`'s affine form.

*(e) The interior points lie in their fibres.* `⟨pt_s, n_{h_i}⟩ = ⟨pt_s,
pt_{h_i}⟩ = 0` is conjugacy again, for each hub neighbour `h_i` of `s`; for
`e_s ≤ 1` the fibre is a plane or all of space and there is nothing to check.

*(f) The one place the affine model needs a word.* At `e_s = 2` two **distinct**
planes of `P³` always meet in a line, but two distinct *affine* planes of `𝔸³`
meet in a line only when their affine normals are independent — otherwise the
projective meet is the line at infinity and `widened.meet_line` returns a zero
direction. Here that cannot happen: `pt_s` lies on the meet by (e) and is an
affine point by (i), so the meet is not the line at infinity and the affine
normals are independent. **The no-body-at-infinity clause is exactly what
discharges this**, which is why it is stated rather than waved at.

So `pt = Φ(x)` for the explicit point `x = ((p_h), (n_h), (p_s)) ∈ 𝒫`. ∎

**The sentence to carry away.** The points-first parametrization asks for *two*
independent open conditions — hub points in general position along `Λ` (so the
panel normal is determined) and panel normals pairwise distinct at every
two-hub-neighbour interior (so the meets are lines). At a σ-fixed configuration
the normals **are** the points, so those two conditions are literally the same
condition, and it is the **single** clause
`{pt_w : w ∈ closedHubNbhd(u)}` LI (the affine/projective seam of (f) being the
only bookkeeping left) — which is (GR-5)'s own hypothesis,
`framedom.legality_free`'s clauses (i)+(ii) together, and the exact rank
equality `--transport` asserts at every body of every built point. **The
transport therefore costs nothing beyond what the driver already tests — but it
is a different theorem from (FR-15), and stating only (FR-15) would have left
the consumer's step unlicensed.**

**Three riders, named so they are not silently assumed.**

- **The guard is irrelevant here, and must be.** §(K-clos) (AC-9) says a
  σ-fixed point never passes `repin.star_generic`. That is not an obstruction:
  the guard cuts out a **dense open** subset of `Chart(Γ)` (nonempty at the
  pooled shapes by (ANH-10)'s 26/26 guard-accepted seeds), so it does not change
  the generic point, and (FR-16) + (ANH-9)(iii) never evaluate it. This is
  §(K-frame) (FR-4)'s "rank lower semicontinuity on the irreducible chart, never
  a genericity guard", made explicit at the level of the variety.
- **`ℚ(i)` is harmless, for a reason worth writing once.** `Φ` is defined over
  `ℚ` and `𝒫` is `ℚ`-rational, and the frame determinant is a `ℤ`-coefficient
  polynomial in the placement; so a nonzero value at any `ℚ(i)`-point of `𝒫`
  makes the pullback a nonzero element of `ℚ[𝒫]`, nonvanishing on a dense open,
  and (ANH-9)(iii)'s own `ℚ`-density argument then supplies rational points.
- **The tower's stated girth `≥ 3` is one clause short of nonemptiness — a
  correction, not a hole in this theorem** (§(K-chart) (CH-5), direction CIRR,
  2026-08-19). At girth 3 a Λ-triangle carrying a non-hub on two of its hubs
  makes stage 3 (`N°`) empty at *every* seed, so *Step FR13*'s tower is
  vacuous there; girth `≥ 4` restores nonemptiness. This costs (FR-16) nothing
  — its witness `pt` already exists, so nonemptiness at that `Γ` is not in
  question — and it costs no consumer anything, because girth ≥ 4 is free at
  `G′` three independent ways: this section's own last table row
  (girth `(G′) ≥ 6`), the class predicate `gridcol.class_shape`'s two-hub-
  triangle filter, and the landed `not_pencilNondegFeasible_of_triangle_
  two_hubs` (`Motive.lean:563`).

**Reach.** (FR-16) hypothesizes nothing about the bare-cycle stratum, nothing
about `k`, and nothing about tightness — only `hcard`, min degree 2, girth `≥ 3`
and the two legality clauses. So it certifies **every** σ-fixed grid witness
this arc has built on a legality-clean colouring as an honest point of that
graph's (ANH-9)(ii) chart. In particular it applies verbatim to §(K-frame)
(FR-6)'s θ(3,4,5) points (`--outer` skips illegal colourings and runs
`config_asserts` + `verify_pencil_witness` on the rest), which is exactly the
content "the first **constructed**, non-sampled inhabitants of that locus" was
asserting and had not licensed.

### Step FR14 — (FR-17): (FR-4) with no named gap, and the unconditional discharge on the whole bare-cycle stratum

> **(FR-17)** *(proven-informally, **no named gap**; a composite whose standing
> is its weakest link — see the *Confidence verdict*)* Let `G` be a `k = 4`
> class shape, `v` an eligible split, `P` a length-4 companion of `(b, c)` and
> `β` a branch with `H/P − β` a bare 6-cycle — i.e. a **bare-cycle site**. Then
> the §(K-ann) **(ANH-R1) `β`-clause holds at that site**: `H/P − β` is
> independent at the generic pencil placement of `G′`. This holds at **every**
> bare-cycle site of **every** `k = 4` class triple — all **76** class-level
> sites over the stratum's **22** isomorphism classes ((FR-8)/(FR-14)), i.e.
> 1904 of the pinned pool's labelled instances — with **no residual hypothesis
> and no named gap**.

*Proof.* Six steps, each at its own standing.

1. **A pattern colouring exists** — (FR-R1), **PROVEN** (*Step FR10*): (FR-11)'s
   recipe meets (FR-4)'s (pattern) clause and legality (ii) uniformly, (FR-12)
   makes legality (i) vacuous, and independently the finite stratum is
   enumerated with a pattern colouring exhibited at all 1976 labelled sites.
2. **The grid point exists, by formula.** Assign the `A`-components and the
   `B`-components any injective families of **positive** rationals. Then
   `pt_w = grid_point((1, s_w), (1, u_w)) = [1 + s_w u_w,\ −i(1 − s_w u_w),\
   u_w − s_w,\ −i(u_w + s_w)]`, whose last coordinate is nonzero (both
   parameters positive), so **no body is at infinity**; and two bodies coincide
   iff they share both ruling parameters, iff they share both components, which
   legality (i) forbids. Isotropy and conjugacy are (AC-2). So the exact `ℚ(i)`
   witness is **constructed, not searched** — `framedom.build_at`'s seeded retry
   loop is a convenience, not a step.
3. **`C ≠ 0` at the frame image** — (FR-3)(ii): at a σ-fixed grid configuration
   the `6 × 6` hinge-line determinant of the site's six frame edges is nonzero
   **iff** they are coloured 3–3 with pairwise-distinct components per family,
   which is exactly the (pattern) clause; the identity
   `det = 128·Vdm(s)·Vdm(u)` over the function field is `framedom.m2` (FR-M1),
   and both directions are asserted at every built site with a negative control
   (`--transport`, 30/30). (ANH-14)(d)'s `det(Gram) = −C²` identifies that
   determinant with (ANH-14)'s universal polynomial `C` up to sign, and
   (FR-9)(b) settles that on this stratum the governing object is always
   (ANH-14)(a)'s open 7-point chain, never (e)'s closed hexagon.
4. **The grid point is on the irreducible chart of the triple** — **(FR-16)**,
   whose hypotheses are supplied by step 2 (distinctness) and legality (ii)
   (the closed-hub-neighbourhood LI), with `hcard` at `G′` free by (FR-15)'s
   first table row. *This is the step (FR-4) had to name as a gap.*
5. **Semicontinuity** — (FR-1) with `X = Chart(G′)` (irreducible, *Step FR13*),
   `f` the morphism reading the six frame hinge lines off the placement (all six
   frame edges are `H`-edges of `G′` by (FR-9)(b), so `f` is polynomial in the
   placement), `D = {C = 0}`: one point off `D` forces `C ≢ 0` on `X`, hence
   `C ≠ 0` on a dense open of `X`, hence at its generic point.
6. **The generic point is the pencil placement** — (ANH-9)(ii) defines
   `M_pen^gen` there, and (ANH-9)(iii) reads `C ≠ 0` at the generic point as
   `E(H/P) − β` independent in `M_pen^gen`, which is (ANH-R1)'s `β`-clause at
   the site. ∎

**"Unconditional" — say exactly what it means, because the word is doing
work.**

- **What is closed.** No clause of the argument is left unwritten. (FR-4)'s
  "true-modulo-named-gap" becomes **(FR-17)**, plain. In particular the
  1904/1904 pattern battery and the 30/30 exact certificates stop being the
  *evidence* for the stratum and become *instances of a theorem*; (FR-5)'s
  boundedness caveat was already dissolved by (FR-8)/(FR-14), so nothing hedges
  the quantifier "every class triple" either.
- **What its standing is.** **proven-informally**, the arc's ordinary tier —
  the weakest links being (ANH-14)(c)'s irreducibility argument,
  (ANH-9)(ii)/(iii), (FR-1) and (FR-16), none of which is Lean-checked and all
  of which are standard-but-informal algebraic geometry. "No named gap" is not
  "machine-verified"; the two are independent axes and this block moves only the
  first.
- **What it does *not* reach.** (a) The **other ~70 %** of §(K-ann)'s
  length-5-branch sites: 1904 of 6426 pool instances are bare-cycle, and
  (FR-9)(a) — `H/P` is exactly a bare 6-cycle plus `β` — fails immediately at
  `c′ ≥ 2`, so neither (FR-3)'s `6 × 6` reduction nor (FR-11)'s recipe has an
  analogue there. (b) The **(OC-16) side**: (FR-16) certifies (FR-6)'s
  constructed points as chart points and changes nothing else; the strict
  availability package stays 0/8 with (AC-9) the named mechanism, and the
  irreducibility of the hard-stratum target-rank locus stays un-owned ((FR-7))
  — **struck as unnecessary since 2026-08-19 (direction OCON)**: §(K-out)
  (OC-17) shows this locus is open in the whole chart, so its irreducibility
  is the chart's, owned by (ANH-9)(ii); see Step FR6.
  (c) **`hK`**: (ANH-R1) is one input of one route; discharging it on one
  stratum of one `k` moves no gap-map status, and §(K-grid) (GR-15) is
  untouched.

### Step FR15 — the scope line: what this block does NOT say

Four sentences, so no later reader has to reconstruct them.

- **It does not touch class uniformity.** `hK`'s status is exactly what it was.
  Nothing here is a flank against §(K-grid) (GR-15), and nothing here bears on
  the `g`-detector, the balance layer, or route-ledger entry 5.
- **It does not re-open the `≤3`-closedHubNbhd line.** *Steps FR7–FR11*'s
  §"The (`≤3`-closedHubNbhd) line" applies verbatim and its reasoning is
  unchanged: (FR-16) quantifies over **one constructed configuration** and
  concludes about a **point** of a variety; it never says "the combinatorial
  criterion holds, therefore the graph is `PencilNondegFeasible`". The one place
  feasibility appears is the *opposite* direction — `hK`'s hypothesis
  `HasGenericPencilRealization K 3 G′` **supplying** `hcard` at `G′` — which is
  a hypothesis being consumed, not a criterion being propagated.
- **It does not develop the (FR-6) follow-ons.** Items (ii) (the
  `ℓ_min = 5` / `deg_H(h) = 2` battery beyond θ(3,4,5)), (iii) (the (FR-7)
  irreducibility foothold) and (iv) (the structural account of the on-stratum ⟺
  coincidence-pair anti-correlation) of *Steps FR0–FR6*'s *What would change
  this* are **untouched and remain un-commissioned**. (FR-16) makes item (iii)
  marginally cheaper to state — the foothold's "irreducible rational family" is
  the colouring's grid family, and *Step FR13*'s tower is the ambient it sits in
  — but running it is a separate commission.
- **It does not move any gap-map *status*.** The (K-frame) row's *what would
  close it* cell changes ("(FR-4)'s named gap alone" → "closed; (FR-17)"), and
  the (K-ann) row's §(K-frame) clause loses its rider. Both are wording, not
  status.

### Verdict — what this buys, exactly

- **§(K-frame) (FR-4): the named gap is CLOSED.** (FR-15) is the restatement as
  named; (FR-16) is the clause the name did not carry and is what the consumer
  actually needed. (FR-4) may be re-read as **(FR-17)**: proven-informally, no
  named gap.
- **§(K-ann) (ANH-14) / the (K-ann) gap-map cell**: the chart-to-frame residue
  on the bare-cycle stratum is now discharged **with no rider at all**. The
  row's §(K-frame) clause should drop "what remains is (FR-4)'s one named gap
  alone" and say "closed as an argument, no rider (§(K-frame) (FR-17))".
  **Status does not move**: (ANH-R1) at the other ~70 % of length-5-branch
  sites, and class uniformity, are exactly where they were.
- **§(K-grid) (GR-5) / *Step G6***: gains a companion, not a correction. (GR-5)
  is untouched and true as landed; what this block adds is that its LI
  hypothesis has a **second** meaning nobody had drawn — at a σ-fixed
  configuration it is precisely the (ANH-9)(ii) parametrization's genericity
  locus — and that the (GR-5) statement alone is a chart-**map** fact, not a
  chart-**variety** fact.
- **§(K-ann) (ANH-9)(ii)**: gains a precise reading. Its "irreducible rational
  parametrization" is literally true of the tower of *Step FR13*, i.e. of
  `place_pencil_general` **restricted to its constant-fibre-dimension locus**;
  without that restriction the fibres jump and the phrase is not a
  parametrization. Recording this costs nothing and removes a latent ambiguity
  that this direction had to resolve before it could proceed.
- **§(K-frame) (FR-6)**: retro-certified. Its four on-stratum θ(3,4,5)
  colourings are honest points of θ(3,4,5)'s `G′`-chart by (FR-16); the
  section's "first constructed, non-sampled inhabitants of that locus" now has
  its licence. **No other (OC-16)-side statement moves.**

### Verification

**No driver was run, and no driver was written.** The reserved
`notes/scripts/w4/fres.py` is **returned unused**, and the file does not exist.
The reason is structural, not budgetary: every hypothesis this block consumes at
an instance is *already* asserted by the landed `framedom.py`, and everything on
top of those hypotheses is proof, which no driver mode can test (F11). Nothing
existing is modified (`git diff --name-only -- '*.py' '*.m2'` empty), so the
figure-invariance gate discharges on that check alone, and no new invocation row
is owed to `notes/scripts/README.md` §3.

The landed runs each claim rests on, per driver and mode
(§(K-frame) *Steps FR0–FR6* and *Steps FR7–FR11* *Verification*; re-runnable
from the repo root):

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --pattern    # 13 s  1904/1904; `hcard_ok(G')`/`is_2ec(G')` at 1540 site-carrying splits, 0 failures
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --transport  # 25 s  30/30 exact certificates: distinctness, isotropy/conjugacy, the per-body closedHubNbhd RANK equality, `verify_pencil_witness`, `C != 0` two routes, negative controls
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --outer      #  5 s  the theta(3,4,5) table (FR-16)'s reach clause cites
PYTHONHASHSEED=0 python3 notes/scripts/w4/framedom.py --rulings    #  2 s  (FR-2)/(FR-3) measured
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --strat      #  3 s  the COMPLETE stratum, 1976/1976 (FR-R1)
PYTHONHASHSEED=0 python3 notes/scripts/w4/patexist.py --recipe     # 12 s  (FR-11) constructed, first variant
M2 --script notes/scripts/m2/framedom.m2                           #  1 s  (FR-M1) `det = 128*Vdm(s)*Vdm(u)`
```

**Source facts read off the landed definitions, not their docstrings** (the
CLAUDE.md "docstrings are not evidence" clause; each was opened this pass):

| fact | where | what was read |
|---|---|---|
| `closedHubNbhd u = {w : PencilHub w ∧ (w = u ∨ w ∼ u)}` | `Molecule/Pencil/Motive.lean:82` | the **definition body** — hence "hub ⟹ `{u} ∪` hub neighbours; non-hub ⟹ hub neighbours", the identity *Step FR13* (b)/(d) turns on |
| `hcard` at `G′` is `hK`'s own hypothesis | `Molecule/Pencil/Escape.lean`, the `hK` slot of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` | `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)` → `IsNondegPencilRealization G′ …` (`Motive.lean:140`) → `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) |
| the chart map reads hub normals only | `Molecule/Pencil/Chart.lean:393,412` (`pencilChartPoint`, `pencilChartNormal`) + `Engine.lean:89` (`PencilSeed.ofCoord`, `fillNbr := fillHub`) | the normals-first direction of (GR-5), and that the `fillNbr` coupling is vacuous exactly when `nbrSel` fills all three slots |
| the (ANH-9)(ii) parametrization is points-first | `notes/scripts/w4/widened.py:160` (`place_pencil_general`) | hub points sampled free; `nrm[h]` from `nullspace` of the **hub**-neighbour differences; non-hubs on `meet_line` / `in_plane_point` / free; `return None` at three independent hub neighbours (unreachable under `hcard`) |
| the chart is `G′`'s, not `G`'s | `notes/scripts/w4/outer.py:242` (`chart_point`), `dominance.py:547` (`base_seed`), `repin.py:225` (`seed_probe`) | all three call `place_pencil_general(Gp, …)` with `Gp = G − v + ab` |
| the legality clauses are the LI clause | `notes/scripts/w4/framedom.py:176` (`legality_free`), `:433` (`site_certificate`) | `legality_free` = pairs injective + no 3-member `closedHubNbhd` mono-component; `site_certificate` additionally asserts `rank([pt[w] for w in S]) == len(S)` at **every** body |
| admissibility = alternation at degree-2 bodies | `notes/scripts/w4/closure.py:254` (`alternation_classes`) | the constraint graph links the two edges at a degree-2 body only — nothing else |
| the grid map is Segre ∘ (linear iso) | `notes/scripts/w4/closure.py:160` (`grid_point`) | bilinear in `(s:t)`, `(u:v)` with invertible coefficient matrix — the step *Step FR12*'s star-rank-3 row uses |

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (FR-15) | — | **proof-level**: a hypothesis-transport theorem. Its *transported hypotheses* are asserted per instance — `hcard_ok(G′)`/`is_2ec(G′)` by `--pattern` (0 failures at 1540 splits), distinctness + isotropy/conjugacy + the per-body `closedHubNbhd` rank equality by `--transport` (30 points) |
| (FR-15)'s dropped clause | — | **proof-level, negative**: `f(V(G′)) = f(V(G)) + 1` is arithmetic; nothing measures it because nothing claims it |
| (FR-16) | — | **proof-level**; its hypothesis is `--transport`'s per-body rank assertion, and `--outer`'s `legality_free` filter for the θ(3,4,5) reach clause. **No driver can test the conclusion** (membership in a variety's parametrized image is not a finite check) |
| (FR-16)'s guard rider | `--transport` (indirectly) | that the argument never evaluates `repin.star_generic` — `site_certificate` does not call it, by design; §(K-clos) (AC-9) is why it must not |
| (FR-17) step 1 | `patexist.py --strat`, `--recipe` | (FR-R1) exhaustively at 1976/1976 |
| (FR-17) step 2 | — | **proof-level** (an explicit parameter recipe). `--transport`'s seeded `build_at` is the same object built by search; the recipe removes the search |
| (FR-17) step 3 | `framedom.m2` (FR-M1), `--rulings`, `--transport` | the function-field identity; both directions of the criterion at 30 built sites with negative controls |
| (FR-17) steps 4–6 | — | **proof-level**: (FR-16) + (FR-1) + (ANH-9)(ii)/(iii). Semicontinuity on an irreducible variety is not a driver-testable sentence |
| (FR-17)'s reach | `patexist.py --strat`, `--recon` | 22 iso classes / 76 class-level sites / 1976 labelled — the quantifier "every class triple" is the enumeration, not a sample |
| the 30 % / 70 % split | `anhr1.py --size` (landed) | 1904 of 6426 length-5-branch **pool instances**; a pool ratio, per (FR-14)(iii) |

### Confidence verdict

| | claim | standing |
|---|---|---|
| **(FR-15)** | (GR-5) restates at `G′` verbatim, minus its target-rank clause; `hcard`, star-rank-3 and the 3-member-`closedNbhd` clause all come out free | **proven-informally**, at exactly (GR-5)'s own standing (the transported hypotheses are additionally asserted per instance) |
| **(FR-16)** | a legality-clean σ-fixed grid configuration of an `hcard` graph lies in the **image** of the (ANH-9)(ii) parametrization at its generic-fibre locus; at σ-fixity the points-first and normals-first genericity loci coincide, and both are the `closedHubNbhd` LI clause | **proven-informally** (bundle-tower irreducibility + explicit membership; no driver can test the conclusion, its hypothesis is what `--transport` asserts) |
| **(FR-17)** | the (ANH-R1) `β`-clause at **every** bare-cycle site of **every** `k = 4` class triple — 76 class-level sites, 22 iso classes | **proven-informally, NO named gap** — a composite of (FR-R1) (PROVEN), (FR-3) (proven-informally), (FR-16), (ANH-14) (proven-informally), (ANH-9)(ii)/(iii) (proven-informally) and (FR-1) (proven-informally, standard) |
| the (ANH-9)(ii) reading | the chart is the image of `place_pencil_general` **restricted to its constant-fibre-dimension locus**; without that restriction it is not a parametrization | **proven-informally** (fibre-dimension bookkeeping); recorded because the direction had to fix it before proceeding |
| the (FR-6) retro-certification | θ(3,4,5)'s four on-stratum colourings are honest `G′`-chart points | **proven-informally** ((FR-16) applied; `--outer` supplies the hypotheses per colouring) |

**Class uniformity of `hK` is untouched. No gap-map *status* moves.**

### What would change this

*(i)* **The natural successor is the `c′ ≥ 2` strata, and nothing here is a
head start on them.** (FR-17) is a bare-cycle theorem end to end: (FR-9)(a)
gives `H/P = ` bare 6-cycle `∪ β`, (FR-3) reduces the pure condition to a
`6 × 6` colouring pattern, and (FR-11) builds the colouring. At `c′ = 2`
(3846 pool instances, the largest stratum) the pure condition is (ANH-13)'s
`6m × 6m` branch-screw determinant and none of the three survives. **(FR-16),
however, transfers unchanged** — it is a statement about σ-fixed configurations
of any `hcard` graph — so a `c′ ≥ 2` attack would inherit the chart-membership
half for free and owe only the determinant half.

*(ii)* **A Lean pin, if a later pass wants the tier moved.** The objects exist
(`Chart.lean`, `Engine.lean`, `Motive.lean`), and (FR-15) is the statement a
compiler spike would formalize; (FR-16) is not — it is algebraic geometry over a
variety the Lean side does not carry. So the honest reading is that (FR-15) is
Lean-pinnable and (FR-17) is not, and that closing the *named gap* is a
different achievement from moving the *tier*. This is the same distinction the
(FR-4) → (FR-17) move makes, and it should not be blurred.

*(iii)* **A `--chartmem` reconstruction mode would add rhetoric, not
evidence.** One could write a driver that, at each built point, recovers the
`place_pencil_general` parameters (hub points; `nullspace` of the hub-neighbour
differences; `meet_line` for each two-hub-neighbour interior) and re-runs the
parametrization to reproduce the grid exactly. It would assert **nothing**
`--transport` does not already assert: the reconstruction succeeds *iff* the
per-body `closedHubNbhd` rank equality holds, which is the assertion already in
`site_certificate`. Written down here so a later pass does not spend a dispatch
rediscovering that.

*(iv)* **A refutation would have to attack (FR-16), and the shape it would
take is worth naming.** The claim is that σ-fixity collapses two genericity
conditions into one. It would fail if the (ANH-9)(ii) parametrization needed a
condition **not** expressible in `closedHubNbhd` terms — e.g. if
`place_pencil_general` constrained a panel normal by a *non-hub* neighbour
(it does not: `widened.py:183` filters `if u in hubset`), or if a body could
have three hub neighbours (`hcard` forbids it, and the code's `return None`
branch is unreachable for that reason). Those two source facts are the whole
load-bearing surface; both were read this pass and both are recorded in
*Verification*.

*(v)* **The (FR-6) follow-ons stay open and un-commissioned**, unchanged by
this block: the `deg_H(h) = 2` battery beyond θ(3,4,5), the (FR-7)
irreducibility foothold, and the structural account of the on-stratum ⟺
coincidence-pair anti-correlation. The only thing that moved for them is that
(FR-16) licenses their σ-fixed witnesses as chart points, which the foothold
((iii)) in particular was implicitly assuming.

## §(K-chart) — the pencil chart is irreducible, written down once: the tower of affine-linear fibres, the constant-fibre-dimension clause identified as `IsNondegPencilRealization`'s **conjunct 3**, and a nonemptiness clause that FRES's stated hypotheses do **not** supply

Answering `notes/Pencil-fanout.md` §"Seventh fan-out" → direction **CIRR**
(twenty-fourth kernel-(K) direction, 2026-08-19), landed as a **HIT**. Read
against §(K-out) *Steps O13–O18* ((OC-19)), §(K-slide) *Step 1(e)* ((S1)),
§(K-dom) *Step D4* ((D4)), §(K-ann) *Steps A10/A14–A17* ((ANH-9)) and
§(K-frame) *Step FR13* ((FR-16)) — its four consumers, plus the section that
found the same gap independently the same day. Driver:
`notes/scripts/w4/cirr.py` (three modes, `--empty`/`--guard`/`--fibre`, run
together by `--all`).

**Why this section exists.** The fact "the pencil chart of `G′` is irreducible"
is consumed by §(K-out) **(OC-19)** input (b), §(K-slide) **(S1)(e)**, §(K-dom)
**(D4)** and §(K-ann) **(ANH-9)(ii)** — four sections, at least two independent
routes — and until this pass it was **stated nowhere as a theorem**: (S1)(e)
carries it in a parenthesis, (ANH-9)(ii) as a phrase, (D4) and (OC-19) by
citation. §(K-out)'s *What would change this* item 2 calls it *"the arc's
most-consumed un-driver-tested fact"*; §(K-frame) *Step FR13* (direction FRES,
same day) found (ANH-9)(ii)'s phrase *"irreducible rational parametrization"*
literally true only on `place_pencil_general`'s **constant-fibre-dimension
locus**. This section states it once, proves it, identifies that locus with a
hypothesis the pin **already carries**, and audits all four consumers.

**Three things came out other than the expected bookkeeping.**

1. **The constant-fibre-dimension clause is not an extra hypothesis at all.**
   It is **conjunct 3** of `IsNondegPencilRealization`
   (`LinearIndepOn K normal (G.closedHubNbhd v)`, `Motive.lean:110`) — at hubs
   it forces the tower's stage-1 locus `U_H`, at non-hubs its stage-3 locus
   `N°`. `hK`'s own hypothesis `HasGenericPencilRealization K 3 G′` carries it
   **about `G′`**, and the harness gate `repin.star_generic` implies it too. So
   FRES's restriction costs the consumers nothing, and not for the reason one
   would guess (see item 2) — **(CH-6)**.
2. **The restriction costs nothing for the *closure* either, and that is what
   (S1)(e) needs.** The whole incidence locus `𝒜(Γ)` — including its
   fibre-jump strata — is the **closure** of the constant-fibre-dimension part,
   because the jump is codimension **2** in the base while the fibre gains only
   **1**. So a witness off the locus is still on the irreducible variety, which
   is exactly what (S1)(e)'s contradiction step needs of `data₀` — **(CH-4)**.
3. **Nonemptiness is NOT free at FRES's stated hypotheses, and this is the one
   correction.** *Step FR13*'s tower is stated for `Γ` loopless with `hcard`,
   min degree 2 and **girth ≥ 3**. At girth 3 the stage-3 locus `N°` can be
   **empty**: a Λ-**triangle** `h₁h₂x` (whose three hub-degrees are forced to
   `2` by `hcard`) carrying a non-hub `s` with hub neighbours `h₁, h₂` makes
   `Π(h₁) = Π(h₂)` **identically**, so `place_pencil_general` returns `None` at
   every seed — **0/200**, with the reason asserted, `cirr.py --empty`. Girth
   `≥ 4` suffices; at `G′` girth is `≥ 6`, and the class predicate
   `gridcol.class_shape`'s *no two-hub triangle* filter excludes it a second,
   independent way, as does — strongest of the three, and **compiler-checked** —
   the landed `not_pencilNondegFeasible_of_triangle_two_hubs`. **No consumer is
   disturbed** — every one lives at `G′` — but the hypothesis list in
   *Step FR13* should gain the clause — **(CH-5)**.

---

### Step CH1 — the ambient, named: which variety, over which field, of which `(shape, split)`

Notation is §(K-frame) *Steps FR12–FR15* *Standing notation*, reused verbatim:
for a loopless multigraph `Γ`, `H(Γ)` its hubs (degree `≥ 3` — `PencilHub`,
`Motive.lean:73`), `Λ(Γ)` its hub-hub subgraph, `d_h = |N_Λ(h)|`, `e_s` the
number of hub neighbours of a non-hub `s`; `hcard` (= (R4)) says `d_h ≤ 2`, and
`e_s ≤ 2` is automatic since a non-hub has degree `≤ 2`.
`closedHubNbhd_Γ(u) = {w : deg_Γ w ≥ 3 and (w = u or w ∼ u)}` (`Motive.lean:82`,
the **definition body**) — at a hub, `{h} ∪ N_Λ(h)`, `1 + d_h` members; at a
non-hub, its `e_s` hub neighbours. `closedNbhd_Γ(u) = {u} ∪ N_Γ(u)`.

**Whose chart.** The chart every consumer means is **`G′`'s, not `G`'s**:
`outer.chart_point` (`outer.py:242`), `dominance.base_seed`
(`dominance.py:547`, via `repin.seed_probe`, `repin.py:225`) each call
`place_pencil_general(Gp, …)` with `Gp = splitOff(edges, v, a, b) = G − v + ab`.
`G′` misses tightness by one (`f(V(G′)) = f(V(G)) + 1`, §(K-frame) (FR-15)), so
no statement below mentions a rank target.

**Two ambients, and they are not interchangeable.** Fix a field `K` of
characteristic `0` (the consumers run at `K = ℚ` and `K = ℚ(i)`; class
uniformity over every infinite characteristic-`0` field is (AC-7)'s, not this
section's).

- **Upstairs** — `𝔸(Γ) := (𝔸³_K)^{V(Γ)} × (𝔸³_K)^{H(Γ)}`, coordinates
  `(q, n) = (`body points`, `hub panel normals`)`. This is
  `place_pencil_general`'s **full** return `(placed, nrm)` and the space
  §(K-slide) (S1)'s "chart coordinates" and §(K-dom) (D4)'s frozen
  `Π(b), Π(c)` live in.
- **Downstairs** — `(𝔸³_K)^{V(Γ)}`, the placement alone. This is where
  §(K-out) (OC-17)'s `Z` (rank conditions on `R(G′)`, `R(G − v)`), (OC-19)'s
  `{H/X` inf. rigid`}` and §(K-ann) (ANH-9)'s hinge-line matroid live.

> **Definition (the pencil incidence locus).** `𝒜(Γ) ⊆ 𝔸(Γ)` is the locally
> closed subset cut out by
>
> (i) `n_h ≠ 0` for every hub `h`;
> (ii) `⟨n_h, q_u − q_h⟩ = 0` for every hub `h` and every `u ∈ closedNbhd(h)`;
> (iii) `q_u ≠ q_w` for every edge `uw` of `Γ`,
>
> where `⟨·,·⟩` is the standard form on `K³`. `Φ : 𝒜(Γ) → (𝔸³)^{V(Γ)}` forgets
> the normals, and **`Chart(Γ) := \overline{Φ(𝒜(Γ))}`** (Zariski closure).

(i)–(iii) are **exactly** `place_pencil_general`'s two closing check loops
(`widened.py:206–212`: the `# pencil condition` loop over every hub and every
neighbour, hub or not, and the `# nonzero hinge extensors` loop over every
edge) plus its `if all(x == 0 for x in nrm[h])` guard — read off the source, not
a docstring. So a returned `(placed, nrm)` **is** a `K`-point of `𝒜(Γ)`, and
`𝒜(Γ)` is the honest geometric object the arc samples. In the projective model
(`point, normal : α → Fin 4 → K`) the same locus is cut by
`HasPencilPanelRealization`'s own-panel conjunct plus the landed cross-incidence
theorem `dotProduct_point_eq_zero_of_mem_closedNbhd` (`Motive.lean:363`), and
conjunct 2's link-point independence in place of (iii).

---

### Step CH2 — (CH-1): the statement

> **(CH-1)** *(proven-informally; every clause's proof is below, and the three
> clauses that could have been false are driver-tested — see *Verification*)*
> Let `Γ` be a loopless multigraph with **`hcard`**, **min degree 2** and
> **girth ≥ 4**, and let `K` have characteristic `0`. Write
> `𝒫(Γ) ⊆ 𝒜(Γ)` for the **constant-fibre-dimension locus** of *Step CH3*'s
> tower. Then:
>
> **(a) Irreducible and rational.** `𝒜(Γ)` is a **nonempty, irreducible**
> variety, **rational over the prime field** `ℚ ⊆ K`; and so is
> `Chart(Γ)`.
> **(b) The restriction is inessential.** `𝒫(Γ)` is a **dense open** subset of
> `𝒜(Γ)`, and `𝒜(Γ) = \overline{𝒫(Γ)}` — so a point of `𝒜(Γ)` off the
> constant-fibre-dimension locus is still a point of the same irreducible
> variety.
> **(c) The image contains a dense open.** `Φ(𝒜(Γ))` — hence
> `Φ(𝒫(Γ))` — contains a dense open subset of `Chart(Γ)`, so any nonempty
> open subset of `Chart(Γ)` contains an **honest pencil placement**, not merely
> a point of a closure.
> **(d) Dimensions.**
> `dim 𝒜(Γ) = 3|H| + Σ_{h ∈ H}(3 − d_h) + Σ_{s ∉ H}(3 − e_s)` and
> `dim Chart(Γ) = dim 𝒜(Γ) − |H|`.
> **(e) ℚ-points are dense** in `𝒜(Γ)` and in `Chart(Γ)`.
>
> **The hypotheses, and where each is used.** `hcard` is what makes the tower's
> normal stage nonzero (**(CH-3)**); min degree 2 and girth `≥ 3` (= simple: no
> loop, no parallel pair) are what make the harness's set-valued adjacency
> agree with the multigraph degrees (FRES's rider, *Step FR13*); **girth ≥ 4**
> is what makes `𝒜(Γ)` **nonempty** (**(CH-5)**) — and it is the clause
> *Step FR13* does not carry.
>
> **At the consumers' object it is unconditional.** All three hold at
> `Γ = G′ = G − v + ab` for `G` a class shape and `v` an eligible split:
> `hcard` two independent ways ((FR-15)'s first table row — it is `hK`'s own
> hypothesis about `G′`, and separately combinatorial from `hcard` at `G` via
> (I2)); min degree 2 from (R1) + (I2); **girth(G′) ≥ 6** from (R3) +
> `hnoRigid` via (I2) ((FR-15)'s last table row).

Clause (a) is what all four consumers cite. Clause (b) is what §(K-slide)
(S1)(e) needs and nobody had. Clause (c) is what §(K-out) (OC-19) needs and
nobody had. Clause (e) is what §(K-ann) (ANH-9)(iii) needs — **more than
irreducibility**, and supplied.

---

### Step CH3 — (CH-2)/(CH-3): the proof — the tower, and `hcard`'s exact job

The tower is *Step FR13*'s, restated against `widened.place_pencil_general`'s
source (`widened.py:160`, read this pass) so that each stage names the code that
realizes it.

| stage | what is free | the fibre | its dimension | in `place_pencil_general` |
|---|---|---|---|---|
| **1** | hub points `(q_h)_{h ∈ H}` | — | `3\|H\|` | `pt = {h: rvec3(rng) for h in hubs}` |
| **2** | hub normals `(n_h)` | `ker A_h(q) ∖ 0`, `A_h(q)` the `d_h × 3` matrix of `q_u − q_h`, `u ∈ N_Λ(h)` | `3 − d_h` | `cons = [...for u in nb[h] if u in hubset]`; `basis = nullspace(cons)`; `nrm[h] = Σ co_i b_i` |
| **3** | — | (open condition, no coordinates) | — | `if all(x == 0 for x in d): return None` |
| **4** | non-hub points `(q_s)` | `⋂_{h ∼ s, h ∈ H} Π(q_h, n_h)`, affine of dim `3 − e_s` | `3 − e_s` | `meet_line` (`e_s = 2`), `in_plane_point` (`e_s = 1`), `rvec3` (`e_s = 0`) |

Two open loci make the fibre dimensions **constant**:

- **`U_H`** (stage 1→2): at every hub, `rank A_h(q) = d_h` — equivalently the
  `1 + d_h` points `{q_h} ∪ {q_u : u ∈ N_Λ(h)}` are **affinely independent**.
  Off `U_H` the kernel is **larger** and the stage-2 fibre **jumps**.
- **`N°`** (stage 3): at every non-hub `s` with `e_s = 2` and hub neighbours
  `h₁, h₂`, the affine normals `n_{h₁}, n_{h₂}` are **independent**, so the two
  panels meet in an affine line. This is `localtest.meet_line`'s
  zero-direction test, whose own body shows the three pivot minors **are**
  `±(n₁ × n₂)`'s components, so "no pivot" and "`d = 0`" are the same condition
  (`localtest.py:57–87`).

`𝒫(Γ) := 𝒜(Γ) ∩ U_H ∩ N°`.

> **(CH-2)** *(proven-informally)* `𝒫(Γ)` is a **Zariski-locally-trivial tower
> of fibrations** over the nonempty open `U_H ⊆ (𝔸³)^H`, with irreducible
> fibres of **constant** dimension at every stage. Hence `𝒫(Γ)` is
> **irreducible** and **rational over ℚ**, of the dimension in (CH-1)(d), and
> its ℚ-points are dense.

*Proof.* `U_H` is a nonempty open subset of the affine space `(𝔸³)^H` (nonempty
by (CH-5)(i) below), hence irreducible and ℚ-rational. Stage 2: on `U_H` the
matrix `A_h` has constant rank `d_h`, so `ker A_h` is a **locally free
subsheaf of constant rank `3 − d_h`** of the trivial rank-3 bundle — Zariski-
locally trivial, since a constant-rank kernel is locally cut by the same
nonvanishing `d_h × d_h` minor. Removing the zero section leaves fibres
`𝔸^{3−d_h} ∖ 0`, which are irreducible for `3 − d_h ≥ 1` — **this is where and
only where `hcard` enters, see (CH-3)** — and a Zariski-locally-trivial
fibration with irreducible base and irreducible fibres has irreducible total
space (each trivializing piece `U_i × F` is irreducible, and over an irreducible
base any two nonempty opens meet, so the pieces glue irreducibly). Stage 3
removes a closed subset, leaving an open (nonempty by (CH-5)(ii)). Stage 4 is
again a locally trivial affine bundle: `meet_line`'s base point is given by a
fixed `2 × 2` cofactor formula on each of the three pivot opens and its
direction is `n_{h₁} × n_{h₂}`, so the fibre `⋂ Π` is an affine subspace of
constant dimension `3 − e_s` varying algebraically; `in_plane_point`'s plane
likewise. Each stage is therefore birational over ℚ to base × affine space, so
`𝒫(Γ)` is ℚ-rational, its dimension is the sum of the column, and its ℚ-points
are dense. ∎

*(The parameter count is a cross-check with no proof content: the sampler draws
`3` rationals per hub point, `3 − d_h` coefficients per normal, and `3 − e_s`
per non-hub — exactly (CH-1)(d)'s first sum, and each coefficient-to-vector map
is a linear isomorphism onto its fibre, so the count **is** the dimension.)*

> **(CH-3)** *(proven; arithmetic of the tower, and asserted per sample)*
> `hcard` is **exactly** the hypothesis that makes stage 2's fibre nonzero:
> `d_h ≤ 2` gives `rank A_h ≤ 2`, so `dim ker A_h ≥ 1` at **every** point of
> `(𝔸³)^H` — on `U_H` or not. Consequently
> `place_pencil_general`'s `return None` on `if not basis:` — its
> *"3 independent hub neighbours"* branch — is **unreachable** under `hcard`.
> The companion cap `e_s ≤ 2` needs no hypothesis (a non-hub has degree `≤ 2`),
> so stage 4's `len(hn) >= 2` branch is always `e_s = 2` exactly and its
> `hn[0], hn[1]` slicing discards nothing.

*Proof.* `nullspace(cons)` returns `[]` only when `rref(cons)` has a pivot in
every column, i.e. `rank cons = 3` (`exactcore.py:68–83`, read this pass);
`cons` has `d_h ≤ 2` rows. ∎

---

### Step CH4 — (CH-4): the fibre jumps do **not** add a component — the restriction is free even for the closure

This is the clause that turns FRES's *"literally true only on the
constant-fibre-dimension locus"* from a caveat about a phrase into **no loss at
all**, and it is the clause §(K-slide) (S1)(e) needs.

> **(CH-4)** *(proven-informally)* `𝒫(Γ) ⊆ 𝒜(Γ)` is **dense open**, and
> `𝒜(Γ) = \overline{𝒫(Γ)}`. Hence `𝒜(Γ)` is irreducible, `Chart(Γ)` is
> irreducible, and **no point of `𝒜(Γ)` lies off the irreducible variety
> whose generic point defines `M_pen^gen`** — in particular a legal pencil
> realization that fails the constant-fibre-dimension condition is *still* a
> point of the same chart, and semicontinuity from it is still valid.

*Proof.* Open: `U_H` and `N°` are defined by non-vanishing of minors and of a
cross product, both polynomial in the coordinates. Dense: it suffices that
every point of `𝒜(Γ)` is a limit of points of `𝒫(Γ)`, which we exhibit.

**There are two jump strata, not one** — this is worth saying because `𝒜(Γ)` is
defined by **equations**, so it contains configurations the *sampler* rejects:
stage 2's (`rank A_h < d_h`, the normal space too big) and stage 4's (the two
panels at an `e_s = 2` non-hub **coincide**, so the "meet line" is a plane and
`meet_line` returns a zero direction). Both are handled.

*(a) The jump is codimension 2 while the fibre gains only 1.* Under `hcard`,
`rank A_h < d_h` is possible only at `d_h = 2` with `rank A_h = 1` (at
`d_h = 1` a rank drop means `q_u = q_h`, excluded by (iii) on the hub-hub edge
`hu`; `d_h = 0` is vacuous). `rank A_h = 1` says `q_h, q_{u₁}, q_{u₂}` are
**collinear**, which is **codimension 2** in the `q`-coordinates, while the
stage-2 fibre grows from `1` to `2` — dimension `−2 + 1 = −1`. So every jump
stratum has dimension **strictly less** than `dim 𝒫`, and no jump stratum can
be a top-dimensional component. *(This is not yet the claim: a lower-
dimensional extra component would still destroy irreducibility. (b) rules it
out.)*

*(b) Every jump-stratum point is a limit of `𝒫`-points.* Let
`(q⁰, n⁰) ∈ 𝒜(Γ)` with `rank A_{h}(q⁰) = 1` at the hubs of some set `S`, so
`n⁰_h ∈ ker A_h(q⁰)`, a 2-plane. Fix `h ∈ S`, write `e` for the common
direction of `q⁰_{u₁} − q⁰_h` and `q⁰_{u₂} − q⁰_h`, so
`ker A_h(q⁰) = e^⊥`. Perturb one hub point: `q_{u₂}(t) = q⁰_{u₂} + t·w`. Then
`A_h(q(t))` has rows `e`-parallel and `(q⁰_{u₂} − q⁰_h) + t w`, so for `t ≠ 0`
its kernel is the **line** `⟨e × w⟩`, **independent of `t`**; and as `w` ranges
over `K³` the line `⟨e × w⟩` ranges over **every** line of `e^⊥`. Choose `w`
with `⟨e × w⟩ = ⟨n⁰_h⟩` and rescale the stage-2 coefficient so that
`n_h(t) ≡ n⁰_h`; do this independently at each `h ∈ S` (the perturbed points
are distinct hubs' coordinates, so the choices do not interact — and if two hubs
of `S` share a neighbour, perturb along a curve in the shared coordinate, which
the same computation allows since only the *direction* `e × w` matters). At the
non-hubs, `q_s(t) := p̄_s(q(t), n(t)) + Σ λ_i d_i(q(t), n(t))` with `p̄, d`
the cofactor base point and direction of stage 4 and `λ` the coordinates of
`q⁰_s` in that frame at `t = 0`; these are rational in `t`, defined at `t = 0`,
and reduce to `q⁰_s` there. All of (i)–(iii), `U_H` and `N°` are open
conditions holding at `t = 0` for the *limit* data or by construction for
`t ≠ 0`, so the curve lies in `𝒫(Γ)` for all but finitely many `t` and tends to
the given point.

*(c) The stage-4 jump stratum is also in the closure.* Suppose instead that at
some non-hub `s` with `e_s = 2` the two panels **coincide** (on `𝒜(Γ)` they
cannot be parallel-and-distinct — equation (ii) puts `q_s` on both), so `q_s^0`
is an arbitrary point of the common plane while `𝒫`'s fibre there is a line.
Codimension: `n_{h₁} ∥ n_{h₂}` is **2** conditions and equality of the two
offsets a **third**, against a fibre gain of `1` — again a strict dimension
drop. Membership in the closure: perturb so that plane 2 becomes
`⟨n + tm, x⟩ = c + ts`; the meet with plane 1 is then
`{⟨n, x⟩ = c, ⟨m, x⟩ = s}`, a line **inside** plane 1 that is independent of
`t` and that sweeps **every** line of plane 1 as `(m, s)` varies. Choose
`(m, s)` so the line passes through `q_s^0` and take `q_s(t) ≡ q_s^0`. The
perturbation is realizable inside the tower for the same reason as in (b): if
`d_{h_i} ≤ 1` the normal has free directions; if both are `2` the two normals
are pinned by two **different** hub-point triples (girth `≥ 4` via (CH-5)(iii)
rules out equal triples), so moving a hub point exclusive to one triple tilts
that panel alone. Hence `𝒜(Γ) ⊆ \overline{𝒫(Γ)}`. ∎

*(d) `Chart(Γ)` and clause (c) of (CH-1).* `Φ` is a morphism, so
`Φ(𝒜) ⊆ \overline{Φ(𝒫)}` and the two closures agree; `Chart(Γ)` is the closure
of the image of an irreducible variety, hence irreducible, and by Chevalley
`Φ(𝒫)` is constructible and dense in it, hence contains a dense open. For
rationality of `Chart(Γ)`: on the open subset where each hub's **closed star**
spans its panel, `n_h` is determined by `q` up to scale (*Step CH6*), so fixing
the first nonvanishing coordinate of each `n_h` to `1` gives a ℚ-rational
section of `Φ` over a dense open; `Φ` restricted to that slice is generically
injective, hence birational onto `Chart(Γ)`, which is therefore ℚ-rational, and
`Φ(𝒫(ℚ))` is dense in `Chart(Γ)`. The generic `Φ`-fibre is then
`(K^*)^{|H|}`, giving (CH-1)(d)'s second formula. ∎

---

### Step CH5 — (CH-5): nonemptiness, the twin-plane obstruction, and the clause *Step FR13* does not carry

Irreducibility of an **empty** variety is worthless, and every consumer needs
`Chart(G′)` to carry points. `U_H` is always fine; `N°` is not.

> **(CH-5)** *(proven-informally; the negative half is **driver-exhibited**,
> `cirr.py --empty`)*
> **(i) `U_H ≠ ∅` always**, for any `Γ` with `hcard`: choose hub points with no
> three collinear (a nonempty open condition on `(𝔸³)^H` over an infinite
> field); since `d_h ≤ 2`, `U_H`'s condition at `h` is exactly that
> `q_h, q_{u₁}, q_{u₂}` are not collinear.
> **(ii) `N° ≠ ∅` iff there is no *twin-plane pair*.** A **twin-plane pair** is
> a non-hub `s` with two hub neighbours `h₁ ≠ h₂` such that
> `d_{h₁} = d_{h₂} = 2` and `{h₁} ∪ N_Λ(h₁) = {h₂} ∪ N_Λ(h₂)`. At a twin-plane
> pair the two panels **coincide identically on `U_H`**, so `N° = ∅` and
> `place_pencil_general` returns `None` at every draw.
> **(iii) A twin-plane pair forces a 3-cycle.** `{h₁} ∪ N_Λ(h₁) =
> {h₂} ∪ N_Λ(h₂)` with `h₁ ≠ h₂` forces `h₁ ∼ h₂`, hence with `h₁ ∼ s ∼ h₂` a
> triangle `h₁ s h₂` of `Γ` (and a Λ-triangle `h₁h₂x` on the common third
> hub). **So `girth(Γ) ≥ 4` ⟹ `N° ≠ ∅` ⟹ `𝒜(Γ) ≠ ∅`.**
> **(iv) `girth ≥ 3` is NOT enough**, so *Step FR13*'s standing hypothesis list
> is one clause short — see the witness below.
> **(v) At `G′` it is free, three times over** — the third leg is landed Lean
> and is strictly the strongest: **`not_pencilNondegFeasible_of_triangle_two_
> hubs`** (`Motive.lean:563`, see (CH-8)) says a triangle with two adjacent hubs
> makes `PencilNondegFeasible` **false**, and by (iii) every twin-plane pair
> carries one (take the triangle `s – h₁ – h₂`, with `h₁, h₂` the adjacent
> hubs). So **no graph the pin talks about has a twin-plane pair**, with no
> girth hypothesis and no appeal to the generators. The two combinatorial legs
> stand as they were: `girth(G′) ≥ 6` ((FR-15)'s last
> table row) kills (iii)'s 3-cycle; independently, the landed class predicate
> `gridcol.class_shape` **rejects any shape with a two-hub triangle**
> (`gridcol.py:181`, the body: `if any(len(t & hubs) >= 2 for t in
> triangles(edges)): return None`) — and a Λ-triangle is a triangle with
> **three** hubs, so a fortiori one with `≥ 2`. Since (I2) gives
> `Λ(G′) = Λ(G)`, the Λ-triangle (iii) needs cannot exist at `G′` either.

*Proof.* (i) as stated. (ii) ⇐: if some `h_i` has `d_{h_i} ≤ 1` its normal
fibre has dimension `≥ 2`, so `n_{h₁} ∦ n_{h₂}` is a nonempty open condition on
that fibre; if both have `d = 2` the normals are determined up to scale as the
normals of `aff({q_{h_i}} ∪ {q_u : u ∈ N_Λ(h_i)})`, two planes determined by two **triples**
of free hub points. If the triples differ, pick `x` in one and not the other:
`q_x` is a free coordinate and tilting it moves that plane's direction through a
2-parameter family, so non-parallelism holds on a nonempty open. Finitely many
nonempty opens on the irreducible `U_H` meet. ⇒: if the triples are equal the
two planes are literally the same plane, at every point of `U_H`. (iii) `h₁` is
in the left set and `h₁ ≠ h₂`, so `h₁ ∈ N_Λ(h₂)`; the three-element sets then
share a third hub `x`. ∎

**The witness for (iv)** (`cirr.py --empty`, exact ℚ, seeds `0..199`). `Γ_bad`
on 6 bodies: hubs `h₁, h₂, x` forming a Λ-triangle, a non-hub `s` adjacent to
`h₁` and `h₂`, and `t, t′` padding `x` to degree 3. It is **loopless, simple
(girth 3), min degree 2, and satisfies `hcard`** — every standing hypothesis of
(FR-16) — and `place_pencil_general` places it **0/200**. The **reason**, not
the symptom, is asserted at all 200 draws by a deliberate stage mirror of the
sampler's stages 1–2: `rank(n_{h₁}, n_{h₂}, n_x) = 1`, i.e. all three panels
coincide. **Two controls separate the two halves of the obstruction**, and this
is the part that makes the characterization sharp rather than a guess:

| graph | Λ-triangle | a non-hub on two triangle hubs | placeable |
|---|---|---|---|
| `Γ_bad` | yes | yes (`s` on `h₁, h₂`) | **0 / 200** |
| control (a) — subdivide the Λ-edge `h₁h₂` | **no** | — | 187 / 200 |
| control (b) — subdivide `h₁s` instead | **yes** | **no** | 174 / 200 |

Control (b) is the informative one: **a Λ-triangle alone is harmless to the
tower.** Its panels still coincide identically — nothing asks for their meet.
(What it is *not* harmless to is `IsNondegPencilRealization`: see (CH-8).)

---

### Step CH6 — (CH-6): the constant-fibre-dimension clause **is** `IsNondegPencilRealization`'s conjunct 3

The dispatch asked for the constant-fibre-dimension hypothesis to be made
explicit. It is explicit — and it turns out to be a hypothesis the pin already
carries, at which point it stops being a hypothesis of this section at all.

Read off the definition body (`Motive.lean:110`, not its docstring):

```
IsNondegPencilRealization G F normal point :=
  HasPencilPanelRealization G F normal point ∧
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧   -- 2
  (∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v)) ∧              -- 3
  (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v))  -- 4
```

> **(CH-6)** *(proven; the hub half is driver-exhibited two-sidedly,
> `cirr.py --guard`)* At a pencil realization of `Γ`:
> **(i)** conjunct 3 at a **hub** `h` implies `U_H`'s condition at `h`;
> **(ii)** conjunct 3 at a **non-hub** `s` with `e_s = 2` is exactly `N°`'s
> **projective** form (the two panels are distinct hyperplanes), and the affine
> form follows whenever no body is at infinity — (FR-16)'s step (f), verbatim;
> **(iii)** hence conjunct 3 **cuts out the tower's constant-fibre-dimension
> locus**, and `hK`'s hypothesis `HasGenericPencilRealization K 3 G′` — which
> unfolds to `IsNondegPencilRealization G′ …` — supplies it **about `G′`
> itself**, exactly as (FR-15)'s first table row supplies `hcard`;
> **(iv)** harness-side, `repin.star_generic`'s second clause (`no two hinge
> lines at a body coincide`) implies `U_H` as well, and
> `place_pencil_general` enforces `N°` itself — so every seed accepted by
> `outer.chart_point` or `dominance.base_seed` (both of which apply
> `star_generic`) is on `𝒫(Γ)`. **Stated precisely, because one entry point
> differs:** bare `repin.seed_probe` applies **no** `star_generic` (read this
> pass, `repin.py:225–348`; the gate is applied by its callers), so a raw
> `seed_probe` seed is `N°`-clean but **not** `U_H`-certified — which costs
> nothing, by (CH-4).

*Proof.* (i) Suppose `U_H` fails at `h`, necessarily with `d_h = 2` and
`point h, point u₁, point u₂` spanning only a **2-dimensional** subspace `L` of
`K⁴`. The landed theorem
`dotProduct_point_eq_zero_of_mem_closedNbhd` (`Motive.lean:363`, statement read
this pass: from `IsNondegPencilRealization`, `w ∈ G.closedNbhd v` gives
`point v ⬝ᵥ normal w = 0`) gives `normal h ⊥ point h, point u₁, point u₂`, so
`normal h ∈ L^⊥`; and `normal u_i ⊥ point u_i` (own panel) and
`⊥ point h` (cross-incidence, `h ∈ closedNbhd u_i`), and
`span(point h, point u_i) = L` because conjunct 2 makes the two linked points
independent and `L` is only 2-dimensional — so `normal u_i ∈ L^⊥` too.
`dim L^⊥ = 2`, so the three normals of `closedHubNbhd(h) = {h, u₁, u₂}` are
**dependent**: conjunct 3 fails at `h`. At `d_h = 1`, `U_H`'s condition is
`point u ≠ point h`, which is conjunct 2 on the hub-hub edge; at `d_h = 0` it
is vacuous. (ii) `closedHubNbhd(s)` of a non-hub is its hub neighbours, so
conjunct 3 at `s` says `normal h₁, normal h₂` independent, i.e. the panels are
distinct hyperplanes; two distinct hyperplanes of `P³` meet in a line, and in
the affine model the meet is an affine line exactly when the affine normals are
independent — which holds because `q_s` lies on the meet and is an affine point
((FR-16) step (f)). (iii)/(iv) are (i)+(ii) plus a source read: `star_generic`
is `all star ranks == 3 and not coincident_hinges` (`repin.py:214`), and
`coincident_hinges` is empty iff no vertex has two neighbours collinear with it
(`repin.py:179–211`, the body: `rank([C(h,x), C(h,u)]) == 1`), which at
`x, u ∈ N_Λ(h)` is exactly `¬U_H` at `h`. ∎

**The witness that (i) is not vacuous, and the pinned counter-fact**
(`cirr.py --guard`, constructed not sampled, so it does not depend on a seed).
On control (b)'s 7-body graph, place the three Λ-triangle hubs **collinear**
at `(0,0,0), (1,0,0), (2,0,0)` with panels `z = 0`, `y = 0`, `y + z = 0` and the
four non-hubs on the appropriate panels. Then:

- `kbare_common.verify_pencil_witness` is **green** — it is a bona fide pencil
  realization (conjunct 1);
- `repin.star_span_ranks` is **3 at every body** — the **fourth** conjunct
  holds, so the fourth conjunct alone does **not** see the defect (the
  (OC-7)-shaped counter-fact, here in its hub-hub form, which
  `repin.hinge()`'s single-hub-interior slide does not cover);
- and yet `rank A_h = 1 < d_h = 2` at **all three** hubs: the stage-2 fibre is
  **2**-dimensional, so the witness is **off `U_H`** — a legal pencil
  realization in `𝒜(Γ) ∖ 𝒫(Γ)`, which is what makes (CH-4) load-bearing rather
  than decorative;
- `flanks.nondeg_conjuncts` rejects it at **`conjunct 3 (closedHubNbhd normals
  LI)`, witness `('h1', ['h1','h2','x'])`** — (CH-6)(i) exhibited;
- `repin.star_generic` rejects it too (three coincident hinge pairs);
- negative control on a Λ-triangle-**free** graph: a sampled point is on `U_H`
  with conjunct 3 and `star_generic` both green.

---

### Step CH7 — (CH-7): the consumer audit — the exact sentence each of the four needs, and whether (CH-1) supplies it

> **(CH-7)** *(audit; each row's "needs" is the consumer's own wording, and
> each verdict is against (CH-1) as proven above)* **All four consumers are
> clean.** Two of them need **strictly more than irreducibility**, and both
> extras are supplied.

**1. §(K-ann) (ANH-9)(ii)/(iii) — needs irreducibility *and rationality*.**
Its sentence: *"The pencil chart is the image of an irreducible rational
parametrization (hub points, panel normals, panel-constrained interiors …), so
`M_pen^gen` is well-defined, and it is the weak-map-maximal one among the
`M_pen(p)`"*; and (iii) adds *"some **rational** chart point does (ℚ-density of
a nonempty open in the parameter affine space)"*.
**Supplied.** (CH-1)(a) gives irreducibility, so the generic point exists and
the common matroid on the dense open where all finitely many subset-ranks are
simultaneously maximal is well-defined; (CH-1)(e) gives the ℚ-density (CH-2)'s
ℚ-rational tower is the source of. **Flag — this consumer needs more than
irreducibility** (rationality), and it is the reason (CH-2) is stated with
*"rational over ℚ"* rather than just *"irreducible"*. **Refinement of
(ANH-9)(ii)'s phrase**: (FR-16)'s reading (*"literally true of
`place_pencil_general` restricted to its constant-fibre-dimension locus"*) is
correct as a statement about the **parametrization**, and (CH-4) now shows the
restriction changes **no closure**, so the phrase is also true unrestricted as a
statement about the **variety**. Both readings survive; neither is disturbed.

**2. §(K-slide) (S1)(e) — needs irreducibility of the *ambient the witness sits
in*.** Its sentence: *"The chart is irreducible (a tower of affine-linear
fibers: free hub points, normals in hub-dependent linear subspaces, interiors in
panels / meet lines / free space), so `U` is irreducible"* — where
`U ⊆ chart × 𝔸¹` is the maximal-rank locus and the contradiction step needs
`(data₀, 0) ∈ U`.
**Supplied, and this is the consumer for which (CH-4) is not optional.** `U` is
open in `𝒜(G′) × 𝔸¹`, and (CH-4) makes `𝒜(G′)` — not merely `𝒫(G′)` —
irreducible; so `U` is irreducible **and contains `(data₀, 0)`** whether or not
`data₀` is on the constant-fibre-dimension locus. Read the restriction as a
restriction of the *variety*, (S1)(e) would have needed a
constant-fibre-dimension assert on `data₀` that `kslide.py` never made. **Flag:
this consumer needs the closure clause (CH-4), not just (CH-2).** Note (S1)
lives **upstairs** — `slide_ε` moves a chart coordinate and the limit lines read
the panels — so the variety it needs irreducible is `𝒜`, which is what (CH-4)
delivers.

**3. §(K-dom) (D4) — needs irreducibility of a *different variety*.** Its
sentence: *"The chart with `pt(a), pt(b), pt(c), Π(b), Π(c)` frozen is an
irreducible tower of affine-linear fibres (§(K-slide) *Step 1(e)*, with the
first stages frozen)"*.
**Supplied, by a corollary that has to be stated separately — irreducibility of
`𝒜(G′)` does not give it.** A fibre of a projection need not be irreducible.
The corollary: freezing `q_b, q_c` (stage-1 coordinates), `n_b, n_c` (stage-2)
and `q_a` (stage-4) leaves the *same* tower on the remaining coordinates —
remaining hub points free in an affine subspace, remaining normals in
constant-rank kernels of matrices that may now involve frozen points, remaining
non-hubs in constant-dimension affine fibres — so *Step CH3*'s argument runs
verbatim over the sliced base, **provided the slice's own `U_H ∩ N°` is
nonempty**. That is where (D4)'s hypothesis pays for itself: its frozen data
comes from a `dominance.base_seed` seed, and `base_seed` applies
`repin.star_generic` (`dominance.py:569`) which by (CH-6)(iv) puts the seed on
`U_H`, while `place_pencil_general` enforces `N°`. So the sliced locus is
nonempty at the frozen data and the slice is irreducible. **Flag — this
consumer needs a different variety, and its irreducibility rests on the guard
its own seed passes.** Dating rider, recorded not repaired: the composite
`star_generic` was **adopted at `base_seed` on 2026-08-06** (README *Harness
debt* item 4, slice S2); before that the gate was `star_span_ranks` alone,
which the (CH-6) witness shows does **not** imply `U_H`. This pass did **not**
re-run (D4)'s battery; the claim above is about the guard as landed today.

**4. §(K-out) (OC-19) input (b) — needs irreducibility *plus* that the meeting
point is an honest placement.** Its sentence: *"`X` is irreducible … By (OC-17)
and (a), `Z` is a nonempty open of `X`; by (OC-18) and (c),
`{H/X inf. rigid}` is a nonempty open of `X`. By (b) both are dense, so they
meet; at a common point (OC-18) gives `L_b ⊄ R₁` and membership of `Z` gives
the stratum."*
**Supplied.** `Z` and `{H/X` inf. rigid`}` are restrictions to `Chart(G′)` of
maximal-rank opens of the ambient placement space (both are **downstairs**
conditions — a rank of `R(G′)`, `R(G − v)`, `R(H/X)` at a placement), and
(CH-1)(a) makes `Chart(G′)` irreducible, so two nonempty opens meet. **Flag —
the step needs (CH-1)(c) as well, and (OC-19) does not say so:** `Chart(G′)` is
a **closure**, so a point of `Z ∩ {rigid}` need not *a priori* be a genuine
pencil placement, and (OC-8)'s conclusion is about a point *of `Z`*. (CH-1)(c)
supplies it — intersect the two opens with the dense open contained in
`Φ(𝒫(G′))`, three nonempty opens of an irreducible variety, and the common
point is an honest placement. Also: inputs (a) and (c) are unaffected by
anything here; they remain (OC-19)'s named inputs, and **(a) `Z ≠ ∅` is exactly
the nonemptiness this section does *not* supply** — (CH-5) gives `𝒜(G′) ≠ ∅`,
never `Z ≠ ∅`.

**Nobody needs a fifth thing.** In particular no consumer needs *density* of
the constant-fibre-dimension locus **in a stronger sense** than (CH-4)'s
closure statement, no consumer needs irreducibility of `Z` itself ((OC-17)
derives that from the chart's), and no consumer evaluates `repin.star_generic`
inside its argument — (FR-16)'s guard rider applies verbatim, and (AC-9) stays
irrelevant here for the same reason.

---

### Step CH8 — (CH-8) corrected to a POINTER, the duplicate check across (CH-1)–(CH-7), and the scope line

**This entry was written as a new incidental and is corrected to a pointer**
(coordinator verification, 2026-08-19). The fact it stated is landed:

> **`not_pencilNondegFeasible_of_triangle_two_hubs`**
> (`CombinatorialRigidity/Molecular/Molecule/Pencil/Motive.lean:563`; call sites
> at `Witness.lean:303`, `:307`, `:730`, `:734`). Signature read this pass:
> given `x ≠ y`, `y ≠ z`, `x ≠ z`, links `e₁ : x–y`, `e₂ : y–z`, `e₃ : z–x`, and
> `hy : G.PencilHub y`, `hz : G.PencilHub z` — **two** hubs, `x`'s hub status
> irrelevant, and **no `hcard` hypothesis at all** — it concludes
> `¬ PencilNondegFeasible K G`.

> **(CH-8)** *(**cited, not proven here**)* The infeasibility of a `Γ` carrying
> a triangle with two adjacent hubs is `not_pencilNondegFeasible_of_triangle_
> two_hubs`, above. **The landed form is strictly stronger than what this pass
> derived** — two hubs instead of three, and no `hcard` — and its proof runs
> the same mechanism this section uses elsewhere: conjunct 3 at `y` to get
> `normal y, normal z` independent, then
> `dotProduct_point_eq_zero_of_mem_closedNbhd` to force all three triangle
> points into the `2`-dimensional common perp (`finrank_toDualPerp_pair_eq`),
> then conjunct 4 (or conjunct 3 at `x` plus `finrank_toDualPerp_triple_eq`) for
> the contradiction. A Λ-triangle is a triangle with three hubs, hence a
> fortiori one with two adjacent hubs, so **every graph this pass's version
> covered was already covered**.
>
> **What this pass adds is the chart-side contrast, and only that.** At such a
> `Γ` the pin's nondegenerate stratum is empty, but the **harness chart is
> not**: `place_pencil_general` places control (b) at **174/200** seeds, and
> conjunct 3 fails at **every one of the 174** (`cirr.py --guard`, asserted on
> `verify_pencil_witness`'s derived normals). So `𝒜(Γ) ≠ ∅` and
> `PencilNondegFeasible K Γ` **come apart**, and they come apart exactly here.
> That contrast is what (CH-5) needs and what the landed theorem does not say.

**Scope line.** The landed theorem is a **negative** feasibility criterion, not
a step of the *(`≤3`-closedHubNbhd) line* (which is about *propagating*
feasibility); §(K-frame) *Step FR15*'s paragraph on that line applies verbatim
and is untouched. `gridcol.class_shape`'s *no two-hub triangle* filter is named
*two-hub* **because** the landed theorem needs only two — the reason was already
a theorem, and this section does not supply it.

**The duplicate check across (CH-1)–(CH-7).** (CH-8) reached the coordinator as
a new incidental because nobody grepped the Lean tree for a landed statement of
it. So: one line per claim, against actual **declaration signatures** read this
pass — and note that two citations below were first taken from a docstring
(`Motive.lean:513`'s and `:133`'s) and then **re-verified against the decls**,
which moved one of them to a different file.

The tree-level fact that settles most rows at once: **there is no algebraic
geometry in this project's Lean.** `grep -rlE
"Irreducible|IrreducibleSpace|ZariskiTopology|AlgebraicGeometry"
CombinatorialRigidity/` returns **zero files**. Nothing in the Lean tree states,
or could state without new imports, an irreducibility, closure, or
variety-dimension fact.

| claim | landed Lean declaration? | which, and how it relates |
|---|---|---|
| **(CH-1)** the chart is irreducible, ℚ-rational, `Φ(𝒜)` dense, dims | **none, and none possible** | no AG content in the tree. The nearest landed relatives are its **hypothesis discharges**, not the statement: `ncard_closedHubNbhd_splitOff_le_three_of_safe` (`Habitat.lean:90`) is `hcard` at `G` ⟹ `hcard` at `G′` (with an extra `hsafe : ¬PencilHub a ∨ ¬PencilHub b`, satisfied in the habitat because `a` is a degree-2 body) — the **compiler-checked** form of (FR-15)'s first table row route (ii), which this draft previously cited only as workbook prose |
| **(CH-2)** the tower is an irreducible ℚ-rational bundle | **none** | same reason. `linearIndepOn_pencilChartNormal_closedHubNbhd` (`Chart.lean:613`) is the closest object and runs the **other way**: from the seed's three hub-slot normals being independent it *produces* conjunct 3 for the chart's normals. It is a chart-**map** fact ((GR-5)'s direction), not a chart-**variety** fact |
| **(CH-3)** `hcard` makes stage 2 nonzero / the `None` branch unreachable | **none for the sentence; the projective arithmetic IS landed** | `finrank_toDualPerp_single_eq` (`Molecule/Pencil/Statement.lean:410`, dim 3), `finrank_toDualPerp_pair_eq` (`Molecular/Meet.lean:1562`, dim 2 — stated at general `Fin (m+2)`, not just `Fin 4`) and `finrank_toDualPerp_triple_eq` (`Motive.lean:513`, dim 1) are the landed perp-dimension counts whose affine analogue (CH-3) uses. The **converse** direction is landed and strictly stronger in its own direction: `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) *derives* `hcard` from nondegeneracy, where (CH-3) *consumes* `d_h ≤ 2`. (CH-3)'s own content — that a **Python** branch is unreachable — is not a Lean-statable sentence |
| **(CH-4)** `𝒜 = closure(𝒫)` | **none** | a closure statement; no AG in the tree |
| **(CH-5)** nonemptiness ⟺ no twin-plane pair | **none for the chart** — see (v)'s new third leg | `PencilNondegFeasible` is a **different object** (see (CH-8)); the one landed positive-existence witness, `exists_isNondegPencilRealization_parallel_pair` (`Pair.lean:113`), is about that object **and** at one specific graph — its hypotheses are `V(G) = {x, y}`, `E(G) = {e, f}`, a 2-body parallel pair with no hub at all — so it says nothing about `𝒜(Γ)` at a habitat shape |
| **(CH-6)(i)** conjunct 3 at a hub ⟹ `U_H` there | **no declaration; the mechanism is landed inline, for the triangle case only** | `not_pencilNondegFeasible_of_triangle_two_hubs`'s proof (`Motive.lean:563–690`) runs exactly (CH-6)(i)'s perp count, but at a **triangle**. (CH-6)(i) is the **Λ-path** case `u₁ – h – u₂` with `u₁ ≁ u₂`, which no landed declaration covers — and `hcard` permits `d_h = 2` with no triangle, so the path case is the one the habitat actually presents. **Honest calibration: (CH-6)(i) is a re-use of a landed mechanism at a new configuration, not a new mechanism** — the same three lines of perp counting. It earns its place as a *statement* only because the configuration is different and is the one the tower needs |
| **(CH-6)(ii)–(iv)** conjunct 3 at a non-hub is `N°`; the guards | **none** | (ii) is (FR-16) step (f) restated; (iii)/(iv) are source reads of `Escape.lean`'s `hK` slot and of `repin.py` / `outer.py` / `dominance.py` |
| **(CH-7)** the consumer audit | **none, and none applicable** | an audit of four workbook sentences against (CH-1); nothing in Lean states a workbook consumer's needs |

**Consequence for (CH-6)'s standing.** The **triangle** witness of *Step CH6*
lies inside `not_pencilNondegFeasible_of_triangle_two_hubs`'s scope, so on its
own it exhibits only what the landed theorem already predicts. `cirr.py
--guard` therefore also carries a **path-case witness** on control (a) — a
legal pencil realization (`verify_pencil_witness` green) with
`h₁ – x – h₂` a Λ-**path**, `h₁ ≁ h₂`, and **no two-hub triangle in the graph at
all** (asserted, so the non-duplication is itself driver-tested): `U_H` fails at
`x` (`rank = 1 < d_x = 2`) and conjunct 3 at `x` fails (`rank 2 < 3`), and it is
the only conjunct-3 failure. Two riders, stated because they narrow the witness:
the assertions are on the **hand-chosen** normals, not
`verify_pencil_witness`'s derived ones (at this witness `h₁`'s star is
collinear, so the derived normal is not unique — the derivation picks the same
vector at `h₁` and `h₂`); and the **fourth conjunct also fails** here (star
ranks `2`), so the *"the fourth conjunct alone does not see it"* counter-fact is
carried by the **triangle** witness alone.

**No third duplicate turned up.** Rows (CH-1), (CH-2), (CH-4), (CH-7) are
settled by the absence of AG in the tree; (CH-3) and (CH-6) are calibrated
above; (CH-5) is settled by the object mismatch and gains a citation rather than
losing a claim.

**The scope line — four things this section does not say**, so no later reader
has to reconstruct them.

- **No gap-map status moves.** Writing down a consumed fact is insurance, not a
  status move. (OC-8), (ANH-R1), (GR-15), `hK`'s class uniformity, the balance
  layer and route-ledger entry 5 are **exactly** where they were. Two *content*
  cells change wording — §(K-out)'s (OC-19) row may drop *"conditional on
  (b)"* for *"(b) proven, §(K-chart) (CH-1)"*, and §(K-frame)'s (FR-16) rider
  may gain (CH-5)'s girth clause — and the coordinator decides both.
- **§(K-frame) (FR-7) stays struck.** This section does **not** re-open
  §(K-frame) *What would change this* item (iii): (OC-17) struck the (FR-7)
  irreducibility foothold as unnecessary by showing `Z`'s irreducibility is the
  **chart's**, and (CH-1) is precisely the chart's — the opposite of entering
  the foothold. Nothing below (CH-1) is a foothold for the hard-stratum
  target-rank locus.
- **It says nothing about `Z ≠ ∅`, and nothing about rank.** Every rank
  statement in the arc is a condition **on** the chart; this section is about
  the chart. (OC-19)'s inputs (a) and (c) are untouched.
- **The section placement is the coordinator's call.** The material would sit
  equally well as a §(K-out) sub-block (its heaviest consumer) or as its own
  section (four consumers, none of them owners). It is minted under `CH-`
  either way, so no rename is needed.

---

### Confidence verdict — per claim

| claim | verdict | weakest link |
|---|---|---|
| **(CH-1)** the statement | **proven-informally, no named gap** | the composite of (CH-2)/(CH-4)/(CH-5); ordinary informal-tier algebraic geometry (locally trivial fibrations, Chevalley), none Lean-checked |
| **(CH-2)** the tower is an irreducible ℚ-rational bundle | **proven-informally** | "constant-rank kernel ⟹ Zariski-locally-trivial subbundle" is standard and stated without proof |
| **(CH-3)** `hcard` makes the `None` branch unreachable | **proven** | arithmetic (`rank ≤ 2` rows), plus a per-sample assert |
| **(CH-4)** `𝒜 = \overline{𝒫}` | **proven-informally** | the explicit deformation at several jump hubs simultaneously is written for independent coordinates and waved at the shared-neighbour case in one clause |
| **(CH-5)** nonemptiness ⟺ no twin-plane pair | **proven-informally**, negative half **driver-exhibited** | the ⇐ direction's "tilting a free hub point moves the plane through a 2-parameter family" is a genericity argument, not a computation |
| **(CH-6)** conjunct 3 cuts out the locus | **proven** (hub half from the landed `Motive.lean:363` theorem; non-hub half is (FR-16) step (f)) | the affine/projective seam, which needs "no body at infinity" exactly as (FR-16) does |
| **(CH-6)(i)** at the Λ-**path** configuration | **proven**, and driver-exhibited **outside** the landed theorem's reach | a re-use of the landed triangle theorem's perp count at a new configuration, not a new mechanism |
| **(CH-7)** the consumer audit | **audit, clean at all four** | rows 3 and 4 rest on source reads of guards (`dominance.py:569`, `outer.py:242`) and on **no** re-run of those batteries |
| **(CH-8)** triangle-with-two-hubs ⟹ infeasible | **CITED, not proven here** — landed and **compiler-checked** as `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563`), in a **strictly stronger** form (two hubs, no `hcard`) | none: the only thing this pass adds is the chart-side contrast (`𝒜(Γ) ≠ ∅` while the graph is infeasible), which is measured |

**Headline: a HIT.** The statement is proven-informally with no named gap and
all four consumers audit clean — with the one correction that *Step FR13*'s
stated hypotheses need `girth ≥ 4` (or an explicit nonemptiness clause), which
disturbs no consumer because every one lives at `G′`.

**One self-correction, recorded rather than quietly dropped** (coordinator
verification, 2026-08-19). (CH-8) was drafted as a new incidental and is
**already landed, compiler-checked, and strictly stronger** as
`not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563` — the decl
lives in `Motive.lean`; `Witness.lean:303` is a *call site*). It is now a
pointer, and *Step CH8* carries the duplicate check across (CH-1)–(CH-7) that
would have caught it. Nothing else in this section duplicates a landed
declaration, and the only claim whose standing changed as a result is
(CH-6)(i)'s witness coverage — see *Step CH8*'s closing paragraph.

---

### What would change this

1. **A `Γ` in the class habitat with a twin-plane pair** would empty its chart
   outright — no seed, no witness, every §(K-out)/§(K-dom)/§(K-slide) battery
   silently skipping the shape. (CH-5)(v) says there is none, **three** independent
   ways: the girth bound, a filter the generators already apply, and the landed
   `not_pencilNondegFeasible_of_triangle_two_hubs` — which makes the question
   moot for any graph the pin talks about, since such a `Γ` is not
   `PencilNondegFeasible` at all. The
   cheap probe if anyone doubts it: run `gridcol.class_shape`'s triangle filter
   and (CH-5)(ii)'s twin-plane test over the pooled shape sweeps and report
   0 hits per pool.
2. **A consumer that reads the chart as `Φ(𝒫)` rather than `\overline{Φ(𝒫)}`,
   or vice versa**, in a step where the difference bites. (CH-1)(c) is the
   clause that makes the two interchangeable for *"a point of a nonempty
   open"*, and (CH-7) rows 2 and 4 are the two places the arc already relied on
   it without saying so. A future step that needs a point of a **closed**
   condition on the chart cannot use (CH-1)(c) and must say so.
3. **A `d_h = 2` hub whose two hub neighbours are forced collinear by some
   *other* class condition.** (CH-5)(i)'s nonemptiness of `U_H` uses only that
   hub points are free; a future pass that *freezes* hub points (as (D4) does)
   inherits a nonemptiness obligation on the **slice**, and (CH-7) row 3
   discharges it only through the guard `base_seed` applies. A frozen-scoping
   battery that drops `star_generic` re-opens it.
4. **A characteristic-`p` reading.** Everything here is stated in
   characteristic `0` (the cofactor formulas and the cross product are
   characteristic-free, but "generic point / dense open / ℚ-density" is used in
   the arc's characteristic-0 sense). §(K-clos)'s split of `hK` into
   characteristic 0 and characteristic `p` is the place that question belongs;
   this section does not answer it.
5. **A Lean formalization of (CH-1).** Nothing here is Lean-checked and the
   standing 2026-08-05 Lean hold is not touched. If it ever is, (CH-6) is the
   useful half — it says the constant-fibre-dimension clause needs **no new
   hypothesis**, only `IsNondegPencilRealization`'s conjunct 3, which the pin
   already carries.

---

### Verification

**A driver WAS written, contrary to the dispatch's expectation, and the reason
is F11.** FRES's precedent (a pass may return no driver when every hypothesis
it consumes is already asserted by a landed driver and everything above them is
proof) covers (CH-1)/(CH-2)/(CH-4)/(CH-7): those are proof and source-reading.
It does **not** cover (CH-5), whose content is that a **landed statement's
hypothesis list is one clause short** — a sentence about the *sampler's
behaviour at a specific graph*, which is exactly what a driver tests and what
no amount of prose settles. (CH-6)'s hub half is likewise a *must-reject
witness* claim in the sense of `repin.hinge()`. So `cirr.py` exists, with one
mode per driver-testable sentence.

**Nothing existing was modified** (`git diff --name-only` empty before this
commit; the only addition is `notes/scripts/w4/cirr.py`), so the
figure-invariance gate discharges on that check alone.

**Invocation rows landed in `notes/scripts/README.md` §3, `w4/` subsection**
(runtimes measured on the dispatch machine, `PYTHONHASHSEED=0`, seeds
`0..199`):

```
python3 notes/scripts/w4/cirr.py --empty   # <1 s  (CH-5): Gamma_bad 0/200 placeable with the twin-plane REASON asserted at all 200 draws; controls (a) 187/200, (b) 174/200
python3 notes/scripts/w4/cirr.py --guard   # <1 s  (CH-6): TWO constructed off-`U_H` legal realizations -- the TRIANGLE case (conjunct 1 green, fourth conjunct green, conjunct 3 REJECTS) and the PATH case on a graph asserted to have NO two-hub triangle, which is the part `not_pencilNondegFeasible_of_triangle_two_hubs` does not cover; two-sided collinearity/extensor identity; and (CH-8)'s chart-side contrast, 174/174
python3 notes/scripts/w4/cirr.py --fibre   # <1 s  (CH-3): hcard keeps the `None` branch unreachable; `U_H` at 188/188 and 189/189; the pi_q-fibre = 1 <=> star_span_rank = 3 equivalence at 1508 (hub, sample) pairs, both sides witnessed
python3 notes/scripts/w4/cirr.py --all     #  1 s  all three
```

**Which mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (CH-1)(a),(c),(e) | — | **proof-level**: irreducibility, Chevalley, ℚ-density on a rational variety. No finite check can assert membership in, or the irreducibility of, a parametrized image |
| (CH-1)(d) dimensions | `--fibre` (partially) | the only non-arithmetic input is "the generic `Φ`-fibre is `\|H\|`-dimensional", i.e. `dim ker(closed-star differences) = 1` per hub, asserted at **every hub of every sample** (1508 pairs) |
| (CH-2) | — | **proof-level** (bundle argument). Its *hypothesis* `U_H` is asserted per sample by `--fibre` (188/188, 189/189) |
| (CH-3) | `--fibre` + `--empty` | `not cons or len(nullspace(cons)) >= 1` at every hub of every sample; and the stage mirror in `--empty` carries a hard `assert basis` labelled *"(CH-3) VIOLATED"* that has never fired |
| (CH-4) | — | **proof-level**: a limit argument. Not driver-testable. Its *premise* — that legal points off `𝒫` exist at all — **is** exhibited, by `--guard`'s constructed witness |
| (CH-5)(ii)–(iv) | `--empty` | `Γ_bad`: 0/200 placeable **and** `rank(n_{h₁}, n_{h₂}, n_x) = 1` asserted at all 200 draws (the reason, not the symptom); **two controls** isolate each half of the obstruction (187/200 with the triangle broken, 174/200 with the triangle kept and `s` demoted) |
| (CH-5)(i),(v) | — | **proof-level** (i); **source read** (v): `gridcol.class_shape`'s body and (FR-15)'s girth row |
| (CH-6)(i) | `--guard` | the constructed must-reject witness: `nondeg_conjuncts` returns `('conjunct 3 (closedHubNbhd normals LI)', ('h1', ['h1','h2','x']))` while `verify_pencil_witness` is green and `star_span_ranks` is 3 at every body — **the counter-fact is asserted, not narrated**; plus the two-sided collinearity ⟺ extensor-rank-1 identity |
| (CH-6)(i), the Λ-**path** case | `--guard` | the second constructed witness, on control (a): `verify_pencil_witness` green, `rank(hub-nbr diffs at x) = 1 < d_x = 2`, conjunct 3 at `x` of rank `2 < 3` and no other conjunct-3 failure — **plus an assertion that the graph has no two-hub triangle**, so the non-duplication with `not_pencilNondegFeasible_of_triangle_two_hubs` is itself driver-tested. Riders: asserted on the **hand** normals (the derived ones are non-unique here), and the fourth conjunct **also** fails, so the counter-fact is the triangle witness's alone |
| (CH-6)(ii)–(iv) | — | **proof-level** / **source read** (`repin.py:214`, `:179`; `outer.py:242`; `dominance.py:569`) |
| (CH-7) | — | **audit**: proof-level against (CH-1) plus source reads of the four consumers' own sentences. **No battery was re-run**, and the audit says so where it matters (row 3's dating rider) |
| (CH-8) | **not this pass's claim** — `Motive.lean:563` is compiler-checked | what `--guard` measures is only the **chart-side contrast**: control (b) is placeable at 174/200 while conjunct 3 fails at **all 174**, asserted on the **derived** normals (`verify_pencil_witness`'s own) so the test reads conjunct 3 itself and is not pre-empted by the star-rank precondition. The infeasibility itself is cited, not measured and not proven here |

**Source facts read off the landed definitions and driver source, not their
docstrings** (the CLAUDE.md clause; every row opened this pass).

| fact | where | what was read |
|---|---|---|
| `closedHubNbhd u = {w \| PencilHub w ∧ (w = u ∨ ∃ e, IsLink e u w)}` | `Molecule/Pencil/Motive.lean:82` | the **definition body** — hub ⟹ `{h} ∪ N_Λ(h)`, non-hub ⟹ its hub neighbours. Confirms (FR-16)'s reading |
| `PencilHub v = v ∈ V(G) ∧ 3 ≤ G.degree v` | `Motive.lean:73` | hubs are degree-`≥ 3` in the **multigraph** degree |
| the **four conjuncts** of `IsNondegPencilRealization`, conjunct 3 in particular | `Motive.lean:110` | `(∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v))` — the whole of (CH-6) |
| the cross-incidence is a **theorem**, not a docstring claim | `Motive.lean:363` `dotProduct_point_eq_zero_of_mem_closedNbhd` | statement + proof body: from `IsNondegPencilRealization`, `w ∈ closedNbhd v ⟹ point v ⬝ᵥ normal w = 0`. (CH-6)(i) uses exactly this |
| `HasPencilPanelRealization`'s conjuncts (own-panel incidence, nonzero point, through-point) | `Molecule/Pencil/Statement.lean:88` | conjunct 1's content — the cross-incidence is **derived**, not a conjunct |
| the chart map is **normals-first** | `Chart.lean:393` (`pencilChartPoint`), `:412` (`pencilChartNormal`) + `Engine.lean:89` (`PencilSeed.ofCoord`, `fillNbr := fillHub`) | `pencilChartNormal` returns the seed's `hubNormal` at a hub — (GR-5)'s direction, the **opposite** of the tower's; `fillNbr` coupling vacuous when `nbrSel` fills all slots |
| the (ANH-9)(ii) parametrization is **points-first**, and its exact stages | `notes/scripts/w4/widened.py:160` `place_pencil_general` | hub points `rvec3`; `nrm[h]` from `nullspace` of the **hub**-neighbour differences; `return None` on `if not basis` (3 independent hub neighbours); non-hubs via `meet_line` / `in_plane_point` / `rvec3`; the two closing check loops that **are** `𝒜(Γ)`'s equations |
| the chart is `G′`'s, not `G`'s | `outer.py:242` (`chart_point`), `dominance.py:547` (`base_seed`), `repin.py:225` (`seed_probe`) | all three call `place_pencil_general(Gp, …)` with `Gp = splitOff(edges, v, a, b) = G − v + ab` |
| `nullspace` returns `[]` exactly at full column rank | `exactcore.py:68` | the `if not basis: return None` branch is `rank cons = 3` — (CH-3) |
| `meet_line` signals "no affine meet" by a zero direction, and the three pivot minors **are** `±(n₁ × n₂)` | `escape/localtest.py:57` | `N°`'s exact algebraic form; the base point is a `2 × 2` cofactor solve — the rationality (CH-2) needs |
| `star_generic = all star ranks 3 ∧ no coincident hinges`; `coincident_hinges` is a collinearity test | `repin.py:214`, `:179` | `rank([C(h,x), C(h,u)]) == 1` — (CH-6)(iv)'s implication |
| `base_seed` applies `star_generic` (since slice S2) | `dominance.py:569` | (CH-7) row 3's discharge, and its dating rider |
| a triangle with **two adjacent hubs** makes `PencilNondegFeasible` **false** — landed, compiler-checked, and **strictly stronger than this pass's (CH-8)** | `Molecule/Pencil/Motive.lean:563` `not_pencilNondegFeasible_of_triangle_two_hubs` (call sites `Witness.lean:303,307,730,734`) | the **signature**: `(hxy) (hyz) (hxz) (h₁ : IsLink e₁ x y) (h₂ : IsLink e₂ y z) (h₃ : IsLink e₃ z x) (hy : PencilHub y) (hz : PencilHub z) : ¬ PencilNondegFeasible K G` — two hubs, `x` arbitrary, **no `hcard`**; and the proof body's first step, which is (CH-6)(i)'s perp count at a triangle |
| `hcard` at `G` ⟹ `hcard` at `G′`, in **Lean** | `Molecule/Pencil/Habitat.lean:90` `ncard_closedHubNbhd_splitOff_le_three_of_safe` | the signature: adds `hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b` to `hcard`, and concludes `∀ w, ((G.splitOff v a b e₀).closedHubNbhd w).ncard ≤ 3`. The compiler-checked form of (FR-15)'s first-row route (ii); `hsafe` holds in the habitat because `a` is a degree-2 body |
| the chart **produces** conjunct 3 (the opposite direction to (CH-6)) | `Molecule/Pencil/Chart.lean:613` `linearIndepOn_pencilChartNormal_closedHubNbhd` | hypothesis is LI of the **seed's** three hub-slot normals; conclusion is `LinearIndepOn K (pencilChartNormal …) (G.closedHubNbhd v)`. A chart-**map** fact, (GR-5)'s direction |
| there is **no algebraic geometry** in the project's Lean | `grep -rlE "Irreducible\|IrreducibleSpace\|ZariskiTopology\|AlgebraicGeometry" CombinatorialRigidity/` | **zero files** — which is what settles the (CH-1)/(CH-2)/(CH-4)/(CH-7) rows of the duplicate check |
| the class predicate rejects two-hub triangles | `w4/gridcol.py:181` `class_shape` | `if any(len(t & hubs) >= 2 for t in triangles(edges)): return None` — (CH-5)(v)'s second route |
| `hcard_ok` is `closedHubNbhd ≤ 3` ⟺ `d_h ≤ 2` | `w4/nogood_subdiv.py:170` | the harness form of (R4) |
| the adjacency is **set**-valued, so a parallel pair counts once | `exactcore.py:132` `neighbors`, and `deg = {v: len(nb[v])}` in `place_pencil_general` | why the statement carries girth `≥ 3` (= simple), FRES's rider made concrete |
| `in_plane_point` routes through the **degenerate** `localtest.plane_basis` | `escape/localtest.py:31`, `:52` | a *sampler-coverage* rider, **not** a defect in `𝒜(Γ)`: at `n₃ = 0` the two in-plane directions are parallel and the `e_s = 1` fibre is sampled on a **line**, not the plane (README §4 convention 1, ≈9 % of POOL-G frames, (OC-7)). Consequence, stated so nobody over-reads it: a landed *positive* witness is unaffected (the point still satisfies every incidence, so it is still a point of `𝒜(Γ)` and semicontinuity from it is valid); what is weakened is any **negative** reading ("no escaping seed found") from a raw sampled battery. `--fibre` sees this artifact directly: it is the mechanism behind the 8 fibre-jump `(hub, sample)` pairs, all at the `d_h = 0` hub, all rejected by `star_generic` |

**Pools.** No pool is minted or aggregated. `--fibre`'s two targets are a
**single** `gridcol.class_shape` shape (`G° = K4`, branch lengths
`(1,1,3,5,3,5)` — chosen because it is the smallest landed class shape carrying
a `d_h = 2` hub, so that `U_H` is not vacuous) and one of its `G′`s. Nothing
here is quotable as a class-level rate, and nothing here is aggregated with
POOL-G / POOL-OC / POOL-W or any other section's pool.

## §(K-mech) — the mechanisms of the residual (W2)/(W4) anomalies: the load space Ω, the α-confinement calculus, and the 6v11e rescue

Sibling of §(K-pure), answering its *Step P8* and *Step P9* item 5 (the
second fan-out's direction M, `notes/Pencil-fanout.md` §"Direction M").
Standing notation inherited from §(K-pure): the slide-limit carrier at a
support `Σ`, witnesses (W1)–(W4), chain spans `S_P`, available bars
`R_P = S_P^{⊥_B}`, loaded stresses and loads, `T = ⟨C_ab, C_ac⟩`,
`π = plane(pt a, pt b, pt c)`, the two maximal totally isotropic 3-spaces
`α(a)` and `Λ²π̂` of §(K-pure)'s (PC-Z), `α(p) = p̂ ∧ K⁴`. One new object:

- **Ω := V_bc^{⊥_B}, the realizable-load space.** A covector
  `m ↦ B(m(b) − m(c), ω)` vanishes on the limit motion space iff it lies in
  the limit system's row space, i.e. iff `ω` is the load of a loaded stress;
  so Ω is exactly the set of realizable loads, and it is computable as a
  perp. (Under (W1) the realizing stress is unique.)

**Verdict (2026-08-06, second fan-out direction M).**

(i) **Both residual anomalies of §(K-pure) *Step P8* now have mechanisms,
and both mechanisms live in one calculus** — forced elements of Ω produced
by the α-confinement of slid chain spans (MX-2). The 6v11e `dim V_bc = 2`
drop is a forced **welded flex** with two overlapping α-routes (MX-6); the
`V_bc ∩ Λ²π̂ ≠ 0` incidence at `K222` and `K4 (1,1,3,5,4,4)` is a forced
**pole-cluster load** through `pt(c)` (MX-4/MX-5), with §(K-pure)'s chord
stress (PC3) as the special case `ω = C_bc`.

(ii) **6v11e is RESCUED — the slide device closes it after all** (MX-7).
The mechanism names its own off switches; omitting a **single interior**
(the 5-side end of chain `b–5` or `c–5`) kills both flex routes, and the
resulting nonempty-support limit systems carry full (W1)–(W4) witnesses
(3/3 sampled seeds each, `repin.star_generic` green). §(K-pure) *Step P7*'s
"the slide device does not reach this shape" is therefore **withdrawn**: its
5-support menu omitted only b/c-side interiors, and every one of those
supports keeps both routes alive — exactly as the ledger predicts. The
gap map's 6v11e entry ("chart certificate the only closure") moves: the
device closes the split.

(iii) The full prediction table — 3 single-omission rescues, 2 two-omission
rescues, 4 predicted-stuck controls — is verified 9/9 by `mech.py --wide`.
A wrong ledger would have missed on at least one row.

### (MX-1) — self-duality of the (PC-Z) incidence *(proven)*

> For `W` a maximal totally isotropic 3-space of `(Λ²K⁴, B)` (so
> `W^{⊥_B} = W`) and any subspace `V_bc ⊆ Λ²K⁴`,
>
>     dim(Ω ∩ W) = dim(V_bc ∩ W) + 3 − dim V_bc.

*Proof.* `Ω ∩ W = V_bc^⊥ ∩ W^⊥ = (V_bc + W)^⊥`, so
`dim(Ω ∩ W) = 6 − dim V_bc − 3 + dim(V_bc ∩ W)`. ∎

Consequences, with (PC-Z): under (W1)–(W3) with `dim V_bc = 3`, **the escape
fails at a decoration iff some realizable load is a line through `pt(a)` or
a line in `π`** (`Ω` meets `α(a)` or `Λ²π̂`). The chord obstruction (PC3) is
the case `ω = C_bc ∈ Λ²π̂`. And at `dim V_bc = 2` both incidences are
automatic — so a (W2) failure subsumes the (W4) question. Asserted at every
guarded seed of every driver mode.

### (MX-2) — α-confinement of slid chain spans *(proven; strengthens (PC1))*

> Every limit line of a chain of length `ℓ ≤ 4` passes **through one of the
> two hub points** — not merely meets the chord — provided the same slide
> pattern (PC1) requires for chord-obstruction, and in the following
> refined per-line form. For `P = uw`, `[u, y₁, …, y_{ℓ−1}, w]`:
> hub-incident lines are pencil lines (through the hub point, always);
> a line with a slid end passes through that end's hub point; so
>
>     S_P ⊆ α(u) + α(w)   for  ℓ ≤ 2 (any support);  ℓ = 3 with ≥ 1 end
>                          slid;  ℓ = 4 with both ends slid,
>
> and `S_P` splits into an α(u)-part and an α(w)-part of sizes
> (by `(ℓ, slide)`-case) `(1,1), (1,2), (2,1), (2,2)` etc. — read off the
> (S1)(b) dictionary exactly as in (PC1)'s proof.

*Proof.* The same case analysis as §(K-pure) *Step P1*, keeping the stronger
observation at each case: `(slid, slid) ↦` the chord (through both);
`(hub, nbr) ↦` a pencil line at the hub; `(slid, fixed) ↦ p̂t(h) ∧ x̂`
(through `pt(h)`); only `(fixed, fixed)` middle lines are unconfined, and
they occur exactly in the complementary cases. ∎

Everything below is bookkeeping on top of (MX-2); the driver measures each
containment it uses rather than trusting the rule (and asserts the rule
against the measurement).

### (MX-3) — two-path forced loads *(proven-informally)*

> For an internal hub `h` adjacent to both `b` and `c`, every element of
> `R_bh ∩ R_hc = (S_bh + S_hc)^{⊥_B}` is a realizable load (the loaded
> stress puts the same bar on both chains, equilibrium at `h` is
> automatic). Its dimension is `6 − dim(S_bh + S_hc)`, and (MX-2) forces it
> positive in enumerable patterns: for two ℓ3 chains with their h-side ends
> slid, `S_bh + S_hc ⊆ ⟨L_b⟩ + α(h) + ⟨L_c⟩` is ≤ 5-dimensional, so a load
> exists **at every decoration** — it lies in `α(h)` (a line through
> `pt(h)`) and B-annihilates `L_b`, `L_c`. For `ℓ_bh = 1` (a hub-hub edge)
> the count `dim R_bh = 5` gives a forced load against any `ℓ_hc ≤ 4`
> chain; the bar can be taken to be the **chord `C_hc` on both edges**.

At 6v11e (hubs 3, 4, 5 all joined to both `b` and `c` by ℓ3 chains) this
already forces three independent loads `ω₃, ω₄, ω₅ ∈ Ω`, each in `α(pt h)`,
measured 3-dimensional at every guarded seed — but three loads alone do not
drop `dim V_bc`. The drop is the flex (MX-6).

### (MX-4) — pole-cluster stresses *(proven-informally; `--inc` green)*

> Fix the split end `c` (the *pole*; everything mirrors for `b`) and a hub
> set `X ∋ c` with `b ∉ X`. Consider stresses built from: one **chord** bar
> per chord-obstructed chain inside `X` ((PC1)); the **α-bars**
> `α(h) ∩ R_P` on each chain from `h ∈ X` to `b` (dimension
> `δ = 3 − #(non-α(h) lines of the chain)` by (MX-2) — at the full support
> `δ = 3` at ℓ1, `2` at ℓ2 and ℓ3, `1` at ℓ4, `0` at ℓ5; the driver
> computes the space directly, support-aware); zero on chains leaving `X`
> elsewhere. Every bar at a hub `h ∈ X` passes through `pt(h)`,
> so each internal equilibrium drops from 6 conditions to 3, and with
> `U := #chords + Σ δ`:
>
>     dim(Ω ∩ α(pt c)) ≥ U − 3(|X| − 1).
>
> If the bound reaches **2**, then since `α(c) ∩ Λ²π̂ = pencil(pt c; π)` is
> 2-dimensional (`pt(c) ∈ π`), two planes inside the 3-space `α(c)` must
> meet: **`Ω ∩ Λ²π̂ ≠ 0`, and by (MX-1)+(PC-Z) the pitch vanishes at every
> decoration.** If it reaches **3**, `Ω ⊇ α(c)` forces `Ω = α(c) = V_bc`
> (both 3-dim, `α(c)` self-perp): the strong-containment branch where (W3)
> fails.

*Proof of the bound.* The constrained stress system has `U` unknowns and at
most `3(|X|−1)` independent conditions (each non-pole hub's vertex sum lies
in its own 3-dim `α(h)`); a solution's load at `c` is the sum of `c`'s bars,
all through `pt(c)`, hence in `α(c)`; a zero-load solution would be an
unloaded stress of the limit system, impossible under (W1); realizability is
by construction. ∎

### (MX-5) — the incidence anomalies, explained *(proven-informally; `--inc` green)*

Measured (`mech.py --inc`, acceptance gated on `repin.star_generic`, 2
guarded seeds per shape; the cluster bound is additionally *asserted* ≤ the
measured `dim(Ω ∩ α(pole))` at every shape/seed, and every cluster load is
asserted realizable and through the pole point):

| shape | best c-cluster bound (at X) | measured `dim(Ω∩α_c)` | measured `dim(Ω∩α_b)` | verdict |
|---|---|---|---|---|
| `K222` | **2** (X = all internal + c) | 2 | 0 | W4 FAILS |
| `K4 (1,1,3,5,4,4)` | **2** (X = {c, 2, 3}) | 2 | 0 | W4 FAILS |
| `K5 (3,3,3,3,4,...)` | **3** (X = {c, 2, 3, 4}) | 3 (`V_bc = α(pt c)`) | 1 | W3 FAILS |
| dbl-subdiv `K4` | 1 | 1 | 1 | PITCHED |
| `K4` mixed | 1 | 1 | 1 | PITCHED |
| `K4 (1,1,3,5,3,5)` | 1 (X = {c, 2}) | 1 | 0 | PITCHED |
| `K4 (1,1,3,5,5,3)` | 1 (X = {c, 3}) | 1 | 0 | PITCHED |

- **`K4 (1,1,3,5,4,4)`** (relabeled: `b` has ℓ1 hub-hub edges to hubs 2, 3;
  `c` has ℓ4 chains to both; the ℓ5 edge `2–3` is never chord-obstructed):
  `X = {c, 2, 3}` gives `U = 2 + 3 + 3 = 8`, bound `8 − 6 = 2`. The unique
  (up to scale) incidence load passes through `pt(c)`; the realizing stress
  is supported on the two 2-paths `b–2–c`, `b–3–c`, carrying the chords
  `C_{2c}`, `C_{3c}` as uniform bars; the loads span the 2-plane
  `⟨C_{2c}, C_{3c}⟩ ⊆ α(c)`, whose forced meet with `pencil(c; π)` is the
  line `π ∩ plane(pt 2, pt 3, pt c)` — through `pt(c)`, exactly as measured.
- **`K222`**: `X = {c, 2, 3, 4, 5}` gives `U = 8 chords + (2+2+2) α-bars on
  the three ℓ3 b-chains = 14`, bound `14 − 12 = 2`. Incidence load through
  `pt(c)` at every seed; stress supported on all 11 chains — chords on the
  8 internal ones, α-bars (through the far hub point, meeting `L_b`) on the
  three `b`-chains.
- **`K5 (3,3,3,3,4,4,4,4,4,4)`**: bound `12 − 9 = 3` — **the mechanism of
  the strong-containment branch** `V_bc = α(pt c)` that §(K-pure) (PC3)
  could only observe; (W3) fails exactly as its parenthetical predicts.
- **The two pitched menu-blocked `K4` controls** show the sharpness: their
  ℓ5 edge replaces one ℓ4, killing one path's chord, and the bound drops to
  1 — no incidence, pitched.
- **The b/c asymmetry and the silent α(a) branch are structural**: the
  b-side best bound is 0 at all three anomaly shapes (measured `dim(Ω∩α_b)`
  0, 0, 1); and `a` is not a hub of the limit carrier, so no cluster
  produces loads through `pt(a)` — matching `dim(Ω ∩ α(a)) = 0` ((MX-1)
  duality asserted) at every probed class seed. The α-branch of (PC-Z)
  never fires in this family.

### (MX-6) — the 6v11e welded flex, mechanised *(proven-informally; `--flex` green)*

> `dim V_bc = 3 − dim F` where `F` is the space of limit motions with
> `m(b) = m(c) = 0` (the *welded flex*; the map `ker → V_bc` has exactly
> the trivial twists and `F` in its kernel). Dually `dim Ω = 3 + dim F`.
> At 6v11e (hubs `b=0, c=1, 2, 3, 4, 5`; ℓ3 on all six b/c chains and on
> `2–3`; ℓ4 on `2–4`, `2–5`, `3–4`), `dim F ≥ 1` is forced at every
> decoration of every support that keeps the far-side ends of the six
> b/c chains slid and both ends of `3–4` slid, through **two overlapping
> α-routes**:
>
> - **Route A (localized on hubs 2, 5).** Parameters: `φ₅ = t·ξ₅` with
>   `ξ₅` spanning the forced 1-dim `S_{b5} ∩ S_{c5} ⊆ α(5)` ((MX-3)'s
>   primal twin: two 2-dim α(5)-parts meet inside the 3-dim `α(5)`), and
>   `φ₂ = s·ζ₂` with `ζ₂` spanning the 1-dim `S_{23} ∩ S_{24}`, which is
>   forced into `α(2)` (from `S_{23}` an element is in `α(2) + ⟨L₃⟩`, from
>   `S_{24}` in `α(2) + α(4)`-parts; generically the extra directions
>   miss). One condition: `φ₂ − φ₅ ∈ S_{25}`, which costs **1**, not 2,
>   because `⟨ζ₂⟩, ⟨ξ₅⟩, S_{25}` all lie in the 5-dim `α(2) + α(5)` where
>   the 4-dim `S_{25}` has codimension 1. Count `2 − 1 = 1`.
> - **Route B (spread over 2, 3, 4, 5).** Parameters: the three forced
>   meets `ξ₃, ξ₄, ξ₅` plus `φ₂` free: `3 + 6 = 9`. Conditions:
>   `3 + 2 + 2` at hub 2's chains, plus **1** — not 2 — at the edge `3–4`
>   (its constraint lives in the 5-dim `α(3) + α(4)` ⊇ the fully-slid
>   4-dim `S_{34}`). Count `9 − 8 = 1`.
>
> Both routes pass through the hub-5 meet `ξ₅`. Since the decoration
> variety is irreducible ((S1)(e), as used in §(K-pure) *Step P0*), a
> generic forcing extends to every decoration by upper semicontinuity of
> kernel dimension; hence (W2) fails identically wherever a route is live —
> which includes all four supports the 5-menu probed (their omissions are
> all b/c-side, touching no ingredient).

Measured (`mech.py --flex`, acceptance gated on `repin.star_generic`,
2 guarded seeds × 4 supports + controls): `dim F = 1`, flex localized on
hubs `{2, 5}` with `φ₅ ∈ S_{b5} ∩ S_{c5}`, `φ₂ ∈ S_{23} ∩ S_{24} ⊆ α(2)`,
all containments as stated; controls (dbl-subdiv `K4`, `K4` mixed):
`dim F = 0`. Hub 5 is the only common neighbour of `b, c` whose single
other chain closes a route — hubs 3 and 4 have their candidate routes
killed by the extra `3–4` edge condition, and the driver's stuck-support
rows confirm the asymmetry.

### (MX-7) — the widened support menu and the rescue *(verified 9/9)*

`mech.py --wide` runs the ledger's full prediction table at 6v11e:

| support (omissions from the full slide) | ledger predicts | measured (3 seeds) |
|---|---|---|
| 5-side end of chain `b–5` (1 interior) | A+B dead → rescue | **PITCHED (W1)–(W4) ×3**, `star_generic` green |
| 5-side end of chain `c–5` (1 interior) | rescue | **PITCHED ×3** |
| both of the above (2) | rescue | **PITCHED ×3** |
| 3-side of `3–4` + both interiors of `2–3` (3) | B and A dead separately → rescue | **PITCHED ×3** |
| 3-side of `3–4` + 2-side of `2–5` (2) | rescue | **PITCHED ×3** |
| 3-side of `3–4` only (1) | route A survives → stuck | W2 FAILS ×3 |
| both interiors of `2–3` (2) | route B survives → stuck | W2 FAILS ×3 |
| 2-side of `2–4`, `2–5` (2) | route B survives → stuck | W2 FAILS ×3 |
| 3-side of `b–3` (1) | route A survives → stuck | W2 FAILS ×3 |

Since (S1) consumes exactly one full (W1)–(W4) limit witness, **the slide
device closes the 6v11e split** at (e.g.) the single-omission support. The
rescue rows are existence witnesses (guard-exempt by the standing rule) and
nevertheless pass the composite guard.

### (MX-8) — the σ rider (§(K-σ) *Step σ6* / the dispatch's rider probe) *(`--sigma` green)*

The rider asked whether the two incidence configurations are σ-images of
one another (`V_bc ∩ Λ²π̂ ≠ 0` being the σ-image of `V_bc ∩ α(·) ≠ 0` at
the dual seed). Verdict: **NO — inside the probed family**, for three
verified reasons and one structural surprise:

1. **The transport itself is exact** (asserted at 2 guarded seeds × both
   shapes): starring every limit line gives a system whose motion space is
   `σ`-conjugate, so its `V′_bc = σ(V_bc)` (asserted as spans), and the
   incidence transports to `σ(V_bc) ∩ α(pole π) ≠ 0` — an **α-branch**
   incidence at `pole(plane abc)`, per §(K-σ) *Step σ1(b)*'s covariant
   dictionary. The pole point is asserted distinct from `pt(a)`, `pt(b)`,
   `pt(c)` and every hub point, so this α-space is one the carrier family
   never produces.
2. **But the starred system is not a slide-limit carrier of the dual
   placement**: a starred chord `σ(C_uw)` is the meet line of the two dual
   panels, not the dual seed's chord — asserted on every chain of length
   ≥ 2 whose ends are both hubs. **Structural exception, forced and now
   proven (the probe's assert caught it)**: on an ℓ1 (hub-hub) chain the
   hinge lies in *both* panels, so `C_uw = Π(u) ∩ Π(w)` and its polar IS
   the dual chord — the one bar type the polarity maps back into the
   dual-seed carrier family.
3. **Both measured incidences are the same c-side β-branch type** (loads
   through `pt(c)` in `π`, (MX-5)), so `K222` and `K4 (1,1,3,5,4,4)` are
   parallel instances of one mechanism, not a σ-dual pair; each one's
   σ-image lives at a meet-line carrier outside the probed family.

### (MX-9) — the |V°| ≤ 6 strata sweep *(measured; `--sweep` green)*

One sampled class shape per candidate hub graph (23 graphs, simple,
connected, min degree ≥ 3; length assignments drawn from
`random.Random(20260806)` with `e₀` at ℓ3, certified by
`kslidecomb.shape_ok`; full support; one `star_generic`-guarded chart seed
each; two shapes skipped at the |V| ≤ 41 cost cap — the |E°| ∈ {14, 15}
Maxwell-overbraced stratum, where §(K-pure) *Step P4*'s chord census
already speaks). Predictor per shape: CHORD (a chord stress through `e₀`,
(PC2)/(PC3)) ∨ CLUSTER ≥ 2 (MX-4) ∨ FLEX ≥ 1 (MX-6). Result, 21/21:

- **20 shapes PITCHED, all with every mechanism silent** (chord absent,
  cluster bounds ≤ 1, flex 0);
- **1 new (W4) failure found in the wild** — `|V°| = 6, |E°| = 11`, lens
  `(3,4,3,4,4,1,4,3,3,4,3)` — with cluster bound **2** and no chord, no
  flex: a fresh instance of the (MX-4)/(MX-5) mechanism, predicted by the
  calculus that was built from `K222`/`K4`, on a shape it had never seen;
- **0 unexplained failures, 0 mechanism-fired-yet-pitched rows** (the
  latter asserted — a violation would abort the driver).

So on the sampled strata the three-mechanism predictor is *measured
complete and sound* at the full support. This is a measurement, not a
theorem: sufficiency of "all three silent" for (W1)–(W4) remains open
(and is exactly the shape of the honest next question §(K-pure) *Step P9*
item 5 asked).

### What this buys (K-chord) and the class program

The dispatch named the target shape: *"a structural characterization of when
the incidence happens ... feeds (K-chord)"*. The calculus delivers exactly
that, in load form:

- **Exact reformulation ((MX-1) + (PC-Z)):** under (W1)–(W3), the escape
  fails at a decoration **iff** some realizable load lies in
  `Λ²π̂ ∪ α(a)`; and (W2) fails iff `dim Ω ≥ 4`.
- **The forced part of Ω is combinatorially computable per (shape, Σ):**
  chord stresses (§(K-pure) (PC2)/(PC3), governed by `R_3`), two-path loads
  (MX-3), pole-cluster loads (MX-4), and welded-flex routes (MX-6). So the
  slide device at support `Σ` now carries **three named necessary
  conditions**, all decoration-free:
  1. `e₀ ∉ cl_{R_3}(E_chord(Σ))` — (K-chord), unchanged;
  2. both pole-cluster bounds ≤ 1 — else (MX-5) kills (W4) or (W3);
  3. no forced flex route — else (MX-6) kills (W2).
  Whether these three are jointly *sufficient* on the |V°| ≤ 6 strata is
  what `--sweep` measures (a measured completeness, not a theorem).
- **6v11e closes**, so §(K-pure) *Step P9* item 5's "6v11e first" is
  discharged with a *rescue*, not a refutation: no class shape is currently
  known where the device fails at every support — the class-level
  refutation possibility named in the (K-chord) row's "what would close it"
  cell remains unexhibited, and the covered sub-class grows by 6v11e.
- The pole-cluster bound also gives the arc's first mechanism for the
  **strong-containment branch** of §(K-pure) (PC3) (`V_bc = α(pt c)` at the
  all-{3,4} `K5`), and explains the b/c- and α/β-branch asymmetries as
  structural, not accidental.

### Verification

`notes/scripts/w4/mech.py` (untracked in this dispatch; imports `pure` /
`kslide` / `repin` / `kslidecomb` / `widened` and — via `importlib` —
`lambda.span_meet`; exact ℚ; `RNG_SEED = 20260806` is the file's only
randomness literal, used by `--sweep`'s length sampler; every limit system
is built by `pure.limit_data` from an honest `repin.seed_probe` chart seed;
every sampled object carries a rank/dimension assert; batteries quoted as
rates gate acceptance on the composite guard `repin.star_generic`, and the
(W1)–(W4) rescue rows are existence witnesses reported with their guard
status). Reproduce, from the repo root:

| invocation | ~time | what it asserts |
|---|---|---|
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --flex` | ~4 min | (MX-6) at 6v11e: dim V_bc = 2, dim F = 1, the flex's hub support, every ledger containment (the three 1-dim α-meets, `S_34 ⊆ α(3)+α(4)`, `S_25 ⊆ α(2)+α(5)`, `φ₂ ∈ S_23∩S_24 ⊆ α(2)`), at all four probed supports × 2 guarded seeds; controls dim F = 0; (MX-1) asserted per seed |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --wide` | ~5 min | (MX-7): the 9-row prediction table — 5 rescue rows each with a full (W1)–(W4) witness (asserted present), 4 stuck controls (asserted `W2 FAILS` at every seed) |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --inc` | ~4 min | (MX-3)/(MX-4)/(MX-5): the cluster bound vs measured `dim(Ω∩α(pole))` at 3 anomaly shapes + 4 controls (per-X assert that the bound never exceeds the measured value; per-load asserts realizable + through the pole); the forced incidence and its `pencil(c;π)` meet; (MX-1) at every seed |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sigma` | ~3 min | (MX-8): `V′_bc = σ(V_bc)` as spans; the branch swap to `α(pole π)`; pole ≠ any carrier point; the ℓ1 (forced equality) vs ℓ≥2 (forced difference) starred-chord dichotomy |
| `PYTHONHASHSEED=0 python3 notes/scripts/w4/mech.py --sweep` | ~10 min | the |V°| ≤ 6 strata predictor pass (one guarded seed per sampled class shape; asserts no mechanism-fired-yet-pitched row) |

### Confidence verdict

- **(MX-1), (MX-2): proven** (two-line linear algebra; the (S1)(b) case
  analysis, the same casework as §(K-pure) (PC1) with a stronger per-line
  conclusion).
- **(MX-3), (MX-4), (MX-6): proven-informally**, each ingredient asserted
  by a driver mode at every guarded seed; the genericity step in (MX-6)
  rests on the decoration variety's irreducibility ((S1)(e)) exactly as
  §(K-pure) *Step P0* already uses it.
- **(MX-5): proven-informally** (`--inc` green: bounds 2, 2, 3 met with
  equality at the three anomaly shapes, ≤ 1 at all four controls; every
  cluster load asserted realizable and through the pole).
- **(MX-7), the 6v11e rescue: proven-informally** — exact (W1)–(W4)
  witnesses at five distinct reduced supports, 3/3 sampled seeds each; the
  claim consumed is (S1)'s one-witness transfer, unchanged; the 9-row
  prediction table (5 rescues, 4 stuck controls) verified with per-row
  asserts.
- **(MX-8): the σ-rider verdict is settled as NO within the probed
  family**, with the transport identity, the pole-point disjointness, and
  the ℓ1/ℓ≥2 starred-chord dichotomy asserted (the ℓ1 equality being a
  small proven fact: a hub-hub hinge is its panels' meet line, so σ maps
  it to the dual chord).
- **(MX-9): measured** (a 21-shape sampled census, not a theorem).
- **Class uniformity: untouched.** These are mechanisms and per-shape
  closures; no uniform gap moves. What changes is the *shape* of the
  residue: §(K-pure) *Step P8*'s "two measured anomalies with no
  mechanism" is now empty, and the slide device's failure modes on the
  probed strata are exactly three named, decoration-free conditions.

**What would change this.** *(For (MX-6))* a decoration where the asserted
containments fail — they are open conditions verified per guarded seed; a
failure would break the driver's asserts, not the semicontinuity step.
*(For (MX-4))* an unloaded stress at a (W1) seed — excluded by (W1)
itself. *(For the rescue)* the witnesses are exact; only an error in
`pure.limit_data`'s construction (shared with the whole §(K-pure) arc)
could void them. *(For (MX-5))* a control with cluster bound ≥ 2 or an
incidence shape with every bound ≤ 1 — none exists in the probed pool.
*(For (MX-9))* it is one guarded seed per shape and one sampled length
assignment per hub graph at the full support only; a wider census could
surface a fourth mechanism — that, not a refutation of (MX-1)–(MX-6),
is the live risk, and finding one would be a finding, not a defect.
