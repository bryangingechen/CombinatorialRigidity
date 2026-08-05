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

**Recon verdict history lives elsewhere.** The dated recon record — what was
asked, what method was used, what was refuted — is
`notes/Phase39-design.md`; the one-line decisions are `notes/Phase39.md`
*Decisions made*. This file carries only the mathematics, in its current
state.

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
| **(K-tight)** | (K-tight) 5 | **open**, true with strong evidence; no genuine escape failure anywhere in the corrected numerics | (K-move) or (K-pitch) |
| **(K-move)** | (K-tight) 5 | **open — the sharpest gap** on the stress side; N8 refutes block-determined `[r]` at both probed families | `[r]`-as-chart-rational-function infrastructure (option B, **not** commissioned) |
| **(K-pitch)** | (K-pitch) | (T1)–(T5) **proven-informally**; **closed** at length-3-companion splits (bracket monomial, θ(3,3,6)); uniform form **open** | one seed with `Q(z) ≠ 0` per (graph, split), uniformly |
| **(K-wit)** | (K-pitch) 3 | **open**; the weakest exact form — per habitat+split *equivalent* to the escape at a good seed | one `H`-motion pairing non-trivially with `C(M)`, uniformly |
| **(K-pitch-∞)** | (K-pitch) 4 | **open**; sufficient for (K-pitch) at a split; all five quartic coefficients nonzero at 4/4 habitats | `Q(z_∞) ≢ 0` on the `a`-free chart |
| **(K-Λ)** | (K-pitch) 5b | **open**; sufficient at length-4-companion splits; exact at θ(3,4,5) + NT21 (5/5) | one projective point `λ` off one local quadric `{Φ_loc = 0}` |
| **(K-slide)/(S1)** | (K-slide) 1–4 | **(S1) proven-informally**; per-member (K-slide) **witness-decidable and discharged at every probed member** (23/23, 7 members, 11 split-classes) — `K4`/`W4` control habitats closed at **every** split | — settled per member; the class form is (K-slide-cl) |
| **(K-slide-cl)** | (K-slide-cl), (K-slide-comb) | **OPEN**; covered exactly on the sub-class where the collapse's assignment problem is solvable (all 7 battery members, hence the control habitats) | a decoration with >4 hub positions; or non-basis rows on long paths ((C4) trade generalized); or the generic pure condition of the limit system instead of the collapse |
| **(K-slide-comb)** | (K-slide-comb) | **REFUTED as a class statement** (two structural flanks at explicit class members satisfying `hcard`/`htf`); per shape still a finite certificate-bearing problem, and "(K-slide-comb) at a shape ⟹ (K-slide-cl) there" stays **proven** | — refuted; the needed invariant is **acyclic** 4-colourability, which 3-degeneracy does *not* give |
| **(C6)** | (K-slide-comb) D1 | **proven-informally at every class shape** — the unrestricted 6-fold base packing exists because Edmonds' matroid-partition min-max hypothesis for it *is* 5/6-sparsity; so the packing content is never the obstruction (and is Phase-12/13/14-reachable) | — settled; only a non-tight shape could break it |
| **(C7)** | (K-slide-comb) D4 | **proven-informally combinatorially** (the length-4 menu is *all* five 2-subsets containing `L_ij`; 12/12 exact; `K4` coverage 439 → 702/877, octahedron flank rescued); two honest gaps — no full (W1)–(W4) witness at a repaired member, and `ℓ ∈ {1,2,5}` open (at `ℓ = 5` the mandatory-`L_ij` claim is itself suspect) | a geometric witness at a repaired member + the `ℓ ∈ {1,2,5}` analogues; cannot touch either structural flank |
| `P21` / parallel `G°` edges | (K-slide) 5 | parallel `G°`-edges **proven** to obstruct the slide device at order 0 under the full support (every decoration), and the probed reduced support does not rescue it | for `bc`-parallel shapes: the companion forms (monomial at `ℓ = 3`, (K-Λ) at `ℓ = 4`, the (T5) frame at `ℓ = 5,6`); for `P21`-type shapes: a new `G°`-local mechanism — none identified |
| **(K-bare)/(K-bare-ext)** | (K-bare-ext) | **open**, nothing being developed; `hbareSplit` carried as pinned, off W4 routes 1/3's path; the (K-tight) re-pin fixes the criterion's shape and corrects "the failure set is exactly the line" to `line(a,b) ∪ P′` | (i) `dim R_a ≥ 1` at an adversarial IH seed and (ii) a rank-2 point in the confinement space — with no chart supplying genericity for either |

**Shapes no mechanism covers** (the class program's uncovered flanks, all from
§(K-slide-comb) *Step D5* + §(K-slide) *Step 5*): `χ(G°) ≥ 5` — exactly `K5` or
`Δ(G°) ≥ 5` by Brooks, since four hub positions cap the collapse; hub graphs
with no **acyclic** 4-colouring; shapes where the (pure) menu is unsolvable
even though the colouring premise holds (438 of the 877 exhaustive `K4` shapes,
of which (C7) rescues enough to reach 702/877); non-`bc`-parallel `G°`-edges
with no length-`≤ 4` `bc`-companion (`P21`); and the (K-res) length-6 flank,
unprobed.

**Settled, so not to be re-derived:** the carrier escape criterion and the
`dim U = dim R_a + 1` structure ((K-tight) 0–3); routes 1 and 2 of the original
(K) pin, **REFUTED** by the locality gate; the naive collinear collapse,
**REFUTED** as a chart move ((K-pitch) 6a); the (T1)–(T5) motion-side transfer;
(S1) and its (S2) carrier; (C6). Every recorded escape *failure* in the phase's
numerics was a placement-sampler artifact ((K-tight) 3).

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
  `nrm[b][2] = 0`). Corrected record: **every target-rank seed ever probed
  escapes** — 34/34 tight control, 6/6 θ(4,4,3), 12/12 `W19`, 4/4 `S29`,
  24/24 the `(def 0, dim R_a 1)` pool stratum. (Positive records — on-line
  failures, rank attainments — are unaffected; the artifact only ever
  *suppressed* escapes.)
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
split, and the named gaps are now **(K-Λ)** and **(K-slide-cl)** —
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
change this* carries the sharper conditions); a companion habitat whose
local quadratic `Φ_loc` is the zero form (that would blunt (K-Λ) to the
trivial reduction).

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
is vacuous. The reduced gap on such habitats:

> **(K-Λ)** *(sufficient for (K-pitch) at a length-4-companion split)* —
> some target-rank chart seed's far covector `λ` avoids the local quadric
> `{Φ_loc = 0}`.

One projective point against one locally-computable quadric — the entire
far graph enters through `λ` alone. Machine-validated exactly
(`--companion4`): at θ(3,4,5) (where `λ` is independently recomputable as
the far arc's span normal — cross-checked) and at **NT21**, a new
non-theta tight habitat (hub multigraph on 4 hubs with `b`–`c` paths of
lengths 3 and 4 plus five more; `Σℓ = 24 = 6·4`; certified `def = 0` and
no proper rigid branch-union over all `2⁷` branch subsets): `λ` unique,
`z` reproduced from `(λ, m, n)` alone, the `Φ_loc` identity exact, and
`Q ≠ 0` with the (T2) sign law against the independently computed stress,
5/5 seeds.

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
to (K-Λ) (companion habitats) and (K-slide-cl), whose combinatorial
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

23/23 witnesses pitched; 12/12 certificates passed ((T1)–(T3) re-validated
at every new habitat). Consequences: **(K-pitch) holds at every listed
split, proven-informally** ((S1) + (S3)); the `K4` and `W4` rows close
their habitats at *every* split (orbit-complete), so the
double-subdivision (K-tight) control class over `K4`/`W4` is **closed
with no residual side condition**.

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
chords through hub points. At **P21** — `G°` = `K4 − 02` plus doubled
`23`, lengths `(3; 3,3; 4,5,3,3)`, 21 vertices, residual-shaped (the
parallel pair is a rigid `C₆`) — leaving one parallel chain fully
unslid still yields exactly one limit stress, now supported on the theta
sub-multigraph `{12, 13, 23a, 23b}` (12 edges, line rank 6; exhibited).
Half-measures are worse: a half-slid chain's middle line passes through
the hub point and rebuilds the short circuit.

**Division of labor, updated from Step 6(e).** `bc`-parallel shapes go
to the companion forms (Steps 5/5b: monomial at `ℓ = 3`, (K-Λ) at
`ℓ = 4`, the (T5) frame at `ℓ = 5, 6`). Non-`bc`-parallel shapes with no
length-≤4 `bc`-companion — exemplar `P21` — are covered by **neither**
mechanism: closable per-split by Step-0 seed logic (P21's certificate
seed escapes), but with no `G°`-local argument. The named residue:

> **(K-slide-cl)** *(class-uniform; supersedes the per-member (K-slide),
> which is now witness-decidable and discharged at every probed
> member)* — for every tight/(K-res) habitat shape `(G°, ℓ, e₀)` without
> parallel `G°`-edges, generic decorations of the slide-in limit system
> satisfy (W1)–(W4).

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

## §(K-slide-cl) — the tetrahedral collapse: the class statement reduced to a combinatorial assignment problem (**reduction proven; antecedent refuted — OPEN**, see §(K-slide-comb))

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
  all-`{3,4}` assignments qualify), and `χ(K5) = 5`. A **proper** colouring
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
