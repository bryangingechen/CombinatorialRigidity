## §(K-ins) — option B's insertion calculus: **BOTH KT-inherited routes REFUTED** at `corank(G′) = 3` (route A by KBARE-FALSIFY, route B here, each cap-free at the same 8 seeds), the mechanism identified as a **chain-end panel collapse**, and — since direction INSJOINT (ordinal 90) — **the last endpoint EXCLUDED**: the joint sweep's own `U′` grows by exactly the dimension its required rank grows, so the deficit is preserved and **option B is SPENT OUTRIGHT**

Direction **BINSERT** (arc ordinal 82; `notes/pencil/fanout.md` §"BINSERT"), the design pass
`notes/pencil/strategy.md` §8 ranked **4**: *does option B for `hbareSplit` — the insertion
calculus — still have an endpoint?* Read against `notes/Phase39-design.md` §"(K-bare)
extension-route recon" (the chain, the corank stratification, the danger gadgets),
§(K-bare-ext) *Steps BE1–BE8* (the route-A refutation this section extends) and §(K-tight)
*Steps 0–2* (KT's three constructions and the boundary-load calculus). Driver
`notes/scripts/w4/binsert.py` (`routeb|strata|combined`); all exact ℚ.

**Scope declaration for this section's citations (L3), a coordinator call at the landing and
not a registry deviation:** unqualified `(BE-n)` and `(E4)` mean §(K-bare-ext); `(GR-n)`
§(K-grid); `(OC-n)` §(K-out); `(RS-n)` §(K-res); `(L n)` `notes/pencil/labels.md`'s minting
rule. The owning section stays authoritative for meaning and status.

**Verdict.** Option B is **SPENT, not declined**. Its chain has **no un-run link**: link 1
(the KT pp. 684–691 re-pin) landed 2026-08-02, link 2 (the corank-stratified boundary-load
lemma at arbitrary seeds) landed 2026-08-20 **as (BE-2)**, and link 3 — **(K-bare-ext)** —
was refuted *by link 2's own device*. This pass closes the two escapes the route-A refutation
left untested: **route B fails at every one of (BE-5)'s 8 hit seeds, cap-free**, and the
mechanism is a **collapse of the two chain-end hub panels onto one plane**. **What survived —
shape 4, §(K-tight) *Step 1*'s *"NEW, not in KT"* joint sweep — is now EXCLUDED** (INSJOINT,
(INS-12)): its own `U′` satisfies `need′ − need = dim U′ − dim U` against `U ⊆ U′`, so
BINSERT's deficit of 1 is **preserved** and `rank⟨U′, Λ²Π̂⟩ = 2 < 3 = need′` at 8/8 —
**option B is SPENT OUTRIGHT**, with no un-run measurement left. **Link 2 is NOT re-opened**
((INS-16)): a one-sided subspace bound needs no bi-affine calculus. `hbareSplit` is **UNTOUCHED**: this is
a tier-**T1** *route* finding throughout ((BE-1)'s tiering), not a refutation of the kernel.

**What would change this.** For the refutations: an error in the model-to-Lean dictionary
(the scripts' five-rows-per-hinge Euclidean-perp carrier vs
`BodyHingeFramework.rigidityRows`) — the same single point of failure §(K-tight) and
§(K-bare-ext) both name, **not discharged here**, and **not option-B-specific**; or a
route-B escape at a seed outside (BE-5)'s battery. For the verdict as a whole: (INS-3) itself
falling, which would hand option B an endpoint **without** shape 4 — the joint-sweep endpoint
is now closed, and the three hypotheses its exclusion rests on are (INS-14)(i)–(iii).

### Standing notation

§(K-bare-ext)'s, restated only where it changes. `G`, `v`, `a`, `b`, `G′ = G.splitOff v a b e₀`,
`index`, `c_G`, `s₀`, `U`, `R_a`, `Λ²Π̂(·)` are as there. **New here:** `c` is the far
neighbour of the degree-2 chain end, `G′_A = G − v + \{a,b\}` and `G′_B = G − a + \{v,c\}` the
two splits, and `ρ : G′_B → G′_A` the map `v ↦ a` fixing everything else.

### Step INS1 — option B's chain, link by link, and the KT re-pin re-verified at source

`notes/Phase39-design.md`'s option-B bullet: *"first the owed KT pp. 684–691 re-pin, then the
corank-stratified boundary-load lemma at arbitrary seeds, then (K-bare-ext) on top"*.

| link | status | classification |
|---|---|---|
| 1 — the KT pp. 684–691 re-pin | **LANDED 2026-08-02**, §(K-tight) *Step 0* | landed brick (informal), machine-validated (`w4/repin.py`) |
| 2 — the corank-stratified boundary-load lemma at arbitrary seeds | **LANDED 2026-08-20 as (BE-2)**, on this carrier | informal theorem — *exact, no genericity, no `def` hypothesis*, 192/192 |
| 3 — **(K-bare-ext)** | **REFUTED** ((BE-5)), tier T1, cap-free | refuted, **by link 2** |

> **(INS-6)** *(proved from the record; each cell verified at its own source, not at strategy
> §8.4's prose)* Option B's chain has **no un-run link**. Link 2 is not merely *"transported"*:
> it **is** (BE-2), and its machine validation is the very device
> (`breakhunt.uniform_failure_exact`, which decides (BE-2) item 2's rank criterion) that
> produced (BE-5). **Option B's middle link, once run, refuted its own endpoint.** So §8.4's
> *"un-commissioned by choice, not by blocker"* is wrong in the only sense that matters —
> there is nothing left to commission — and that row's kill condition (*"commissioned and run,
> or (BE-14) closing `hbareSplit` without it"*) fired **by its first disjunct** on 2026-08-20.

**Link 1's source verification** (`CLAUDE.md` *Referencing prior work*; the `.refs` copy read
this pass with `pypdf` per `REFS.md`). **Katoh–Tanigawa, *A Proof of the Molecular
Conjecture*, Discrete Comput. Geom. 45 (2011), 647–700, DOI 10.1007/s00454-011-9348-6**;
printed pp. 647–700 across 54 pdf pages, so the offset is 646. Every pointer §(K-tight)
*Step 0* claims holds: **Lemma 6.10** at printed **p. 680** (§6.4.1, `D = 6`; the adjacent
degree-2 pair via **Lemma 4.6**, both splits minimal 0-dof by **Lemma 4.8**); **Claim 6.11**
at **p. 684**, its proof consuming minimality exactly as *Step 0* says (*"Since `G^{ab}_v` is
a minimal k-dof-graph (with k = 0), **Lemma 4.3(ii)** says that there exists a base `B′` …
satisfying `|B′ ∩ ãb| < 5`"*); **Claim 6.12** at **pp. 690–691** with `M₁/M₂/M₃` as display
**(6.42)**, the identity **(6.44)** and the span **(6.45)** whose six-dimensionality at a
generic nonparallel seed forces `r = 0`. **Cap:** pp. 680, 684, 690, 691 were opened;
*Step 0*'s finer equation pointers ((6.12), (6.16)–(6.19), (6.24)–(6.33), (6.35)–(6.41)) were
**not** individually checked — not found wrong, not verified.

### Step INS2 — what the route-A refutation left standing, and why route B is in scope

(BE-5) refutes the statement the design doc wrote, and that statement quantifies over
**placements of `v` only** — KT's `M₂`, i.e. §(K-tight) *Step 1*'s **route A**. But *Step 1*'s
own table kills **only `M₁`**: **route B** (`M₃`, via `ρ`, KT (6.44)) survives, and so does
the **joint sweep** `(pt v, pt a) ∈ Π̂(b) × Π̂(c)`, which *Step 1* calls *"strictly larger than
A ∪ B — un-analyzed; can only enlarge the escape"*. **KT's Claim 6.12 needs only one of the
three.** So the refutation left two of the three carrier-surviving escapes untested.

Route B needs KT Lemma 6.10's adjacent degree-2 pair, which `hbareSplit`'s antecedent list
does **not** state. It supplies it anyway:

> **(INS-1)** *(proved, off the Lean definition bodies — not off a docstring or an antecedent
> list)* `Graph.PencilHub G w := w ∈ V(G) ∧ 3 ≤ G.degree w`
> (`Molecule/Pencil/Motive.lean:73`). `hbareSplit` (`Molecule/Pencil/Escape.lean:351`) carries
> `G.TwoEdgeConnected`, under which every vertex has degree `≥ 2`, so on the habitat
> **`¬ PencilHub w ⟺ G.degree w = 2`** — the equivalence `Induction/ReducibleVertex.lean:1196`
> states in prose. Hence `hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b` forces
> **`G.degree a = 2` or `G.degree b = 2`**, and with `G.degree v = 2` already an antecedent
> `hbareSplit` **delivers an adjacent degree-2 pair**. **Route B is available to a prover of
> `hbareSplit`, not an extra assumption**; `c` is the unique second neighbour of that end.

### Step INS3 — route B is route A at the chain's other end, on the ρ-pullback

> **(INS-2)** *(proved; asserted per seed in the driver rather than argued)* `ρ : G′_B → G′_A`
> sending `v ↦ a` and fixing everything else is an **isomorphism of edge sets** — both sides
> equal `shared + \{ab\} + \{ac\}` after relabelling, `shared` being the edges of `G` incident
> to neither `v` nor `a`. So a `G′_A`-seed `ptp` pulls back to `ptp_B[v] := ptp[a]`,
> `ptp_B[w] := ptp[w]` otherwise — and **that pullback IS** *Step 1*'s *"`pt(v) := old pt(a)`,
> new `pt(a)` sweeps `Π̂(c)`"*. Route B is therefore **route A's own machinery on
> `split_ctx(G, a)` with the pulled-back seed**: (BE-2)'s corank identity, `need_rank`,
> `hub_domain`, `uniform_failure_exact` and `pairing_rank` all apply verbatim, with **no new
> mathematics**. The driver asserts, rather than assuming: the edge-set identity itself, the
> pullback's legality as a `G′_B` pencil witness, `ρ`'s rank preservation
> (`rank R(G′_A, ptp) = rank R(G′_B, ptp_B)`), the pulled-back seed's target-rank, and
> grid-vs-exact agreement of every verdict.

Because `ρ` is an isomorphism, (BE-2) item 4 **forces** the two contexts to agree on the
calculus data, and the run confirms it: `s₀ = 0`, `dim R_a = 3`, `dim U = 4`, required rank 2
on **both** sides at every seed. That agreement is an internal check on the transport.

### Step INS4 — the decision: route B fails too, cap-free

`binsert.py routeb` (≈ 330 s; seeds, batteries and `seed0 = 52000` are **(BE-5)'s own**, so
route A is a reproduction and route B the new measurement):

| case | `index` | `corank(G′)` | route-A uniform-failure seeds | route B also fails | route B escapes |
|---|---|---|---|---|---|
| **Q3 index-2 hub-end** | 2 | **3** | **8** | **8** | **0** |
| DZ non-hub-ends | 1 | 2 | 0 | — | — |
| DZ hub-end | 1 | 2 | 0 | — | — |

At Q3 the chain is `b = s1 — v = p1_5_1 — a = p1_5_2 (deg 2) — c = s5 (deg 3, HUB)`, so
(INS-1)'s pair is present and route B's domain is the panel `Π̂(s5)`.

> **(INS-3)** *(measured; cap-free per seed)* At **all 8** of (BE-5)'s legal target-rank hit
> seeds **route B also fails at every placement** — all six `2×2` minors of route B's own
> criterion matrix vanishing **identically** on `Π̂(c)`, by the same identical-vanishing test
> that certified route A, with the grid verdict asserted equal to the exact one at every seed;
> `rank⟨U, Λ²Π̂(c)⟩ = 1` at 8/8, mirroring route A's `rank⟨U, Λ²Π̂(b)⟩ = 1`. **The combined
> route-A-or-route-B insertion statement is refuted too.**

**Cap:** the seeds are (BE-5)'s battery — 6 sampler strata × 10 seeds × 3 (gadget, split)
cases. A route-B escape at an **untested** seed is **not excluded**. *Not found under cap*,
never *"does not exist"*.

**A cap in the landed record, named here:** (BE-5)'s battery contains **no
`Q3 index-2 non-hub-ends` case**, so whether uniform failure also occurs at an index-2
non-hub-end split is **unmeasured**. It changes no verdict — a hub-end hit already refutes a
`∀`-statement quantifying over hub-end splits, and `hsafe` permits them — but the record did
not disclose it.

### Step INS5 — the mechanism: the chain-end hub panels coincide

`binsert.py combined` (≈ 80 s). KT's Claim 6.12 works because the span **(6.45)** is
**6-dimensional** at a generic nonparallel seed; §(K-tight) *Step 2.6* records that the
carrier keeps **5** of those 6 (`M₁`'s `Λ²Π̂(a)` being the lost one).

| population | seeds | `dim(Λ²Π̂(b) + Λ²Π̂(c))` | `rank⟨U, Λ²Π̂(b)⟩` | `rank⟨U, Λ²Π̂(c)⟩` | `rank⟨U, sum⟩` | uniform failure |
|---|---|---|---|---|---|---|
| **(BE-5) hit** (`cycleflat`) | **8** | **3** | 1 | 1 | **1** | **yes** |
| control (`None`, robust generic) | 10 | 5 | — | — | **4** | no |
| control (`hubplane`, global hub-coplanar) | 9 | 5 | — | — | **4** | no |

> **(INS-4)** *(measured; a total dichotomy, 8/8 against 19/19)* The controls reproduce
> §(K-tight) *Step 2.6*'s figure **independently, at a different kernel and a different
> corank** — `dim = 5`, pairing rank **4**, comfortably above the required 2. At every hit
> seed both collapse to **3** and **1**. Two *distinct* planes' `Λ²`s span `3 + 3 − 1 = 5`
> (they meet in the `Λ²` of the planes' meet line), so **`dim = 3` ⟺ `Π̂(b) = Π̂(c)`**: at the
> hit seeds **the two hubs bounding the KT chain share one panel plane**. That is the whole
> mechanism, and it explains why the two routes fail *together* rather than independently —
> both sweep inside that single 3-dimensional `Λ²Π̂`, and the degeneracy is a property of `U`
> against the **whole** carrier-surviving escape span, not of either route. This is the locus
> KT's Claim 6.12 proves empty, reached by a legal seed.

> **(INS-8)** *(proved definitionally; the certificate measured)* And it is legal
> **structurally, not accidentally**: `hbareSplit`'s antecedent `¬ PencilNondegFeasible K G`
> is precisely what **permits** the collapse. A nondegenerate realization caps every closed
> hub neighbourhood at 3 (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, the
> lemma `Escape.lean`'s feasible branch consumes), and the gadget's **infeasibility
> certificate is a 4-member closed hub neighbourhood** (`max closedHubNbhd = 4`, reproduced
> exactly this pass) — an apex hub adjacent to three hubs, which under (BE-4)'s propagation
> rule is exactly the configuration that spreads forced coplanarity across hub panels. **The
> certificate that puts `G` in the habitat is the structure that lets two chain-end hub
> panels coincide.** `notes/Phase39-design.md` item 1 had this definitionally (*"the landed
> genericity machinery is provably dead at infeasible `G` — by definition, both sides"*);
> what is new is the **specific** degeneracy that consumes KT's Claim 6.12 hypothesis. **There
> is no genericity to supply.**

**A correction to a recorded reading, because it changes what a repair must control.**
§(K-bare-ext)'s *"Why the seed is in scope"* says the design doc *"named this as a worry (its
item (iii): the calculus's genericity step 'is not automatic at an opaque IH seed'); it is now
a **refutation**"*. Item (iii) names the **`s₀ = 0`** step (shared-subrank genericity) — and
**`s₀ = 0` holds at every one of the 8 hit seeds** (`s₀ = 0`, 8/8). The calculus's own named
assumption is **satisfied**, and the route fails anyway, through a *different* non-genericity.
At these seeds item (iii)'s worry would have been **discharged**. Consequence: **a repair
supplying `s₀`-genericity fixes nothing**; the quantity needing control is
`rank⟨U, Λ²Π̂(b) + Λ²Π̂(c)⟩ ≥ 2`, which is *Step BE8*'s shape 2 — already recorded there as
*"needs its own supply lemma, i.e. it reduces to shape 1"*.

### Step INS6 — the refutation is corank-stratified, and the stratification is complete

`binsert.py strata` (≈ 65 s). §(K-bare-ext) **(BE-8)**'s four-stratum table (driver
`breakhunt.py c1b`) **omits the local-flat (`cycleflat`) row** — the one the (BE-5) hit lives
on. Its prose names the stratum; its table does not carry it. Supplied:

| case | `index` | `corank(G′)` | legal | AT `target(G′)` | uniform failure |
|---|---|---|---|---|---|
| DZ non-hub-ends | 1 | 2 | 10 | **0** | 0 |
| DZ hub-end | 1 | 2 | 10 | **0** | 0 |
| Q3 hub-end | 2 | **3** | 9 | **8** | **8** |

> **(INS-5)** *(measured; the datum (BE-8)'s table omits)* The local-flat stratum is
> **target-INCOMPATIBLE at `index = 1`** (0 of 20 legal witnesses across DZ's two splits reach
> `target(G′)`) and **target-COMPATIBLE at `index = 2`** (8 of 9). So the stratum carrying the
> refutation is **excluded by (K-bare-ext)'s own target-rank antecedent** at corank 2, and the
> refutation is **confined to `index(G) = 2` / `corank(G′) = 3`**. With **(BE-6)**
> (`index ∈ \{1,2\}`, a theorem by arithmetic, reproduced this pass) the picture is complete:
>
> | `corank(G′)` | habitat | route A | source |
> |---|---|---|---|
> | 0 | count-independent, def-drop | required rank **0** — attains at every legal placement | (BE-3), 8/8 |
> | 1 | count-independent, def-equal | failure locus one line; line-avoidance suffices | (BE-3) |
> | 2 | dependent, `index = 1` | no uniform failure under cap; the side condition must widen from the line to `line ∪ P′` / a curve | (BE-7), §(K-tight) *2.4*, (INS-5) |
> | **3** | dependent, `index = 2` | **uniform failure on BOTH routes — no placement side condition repairs it** | **(BE-5) + (INS-3)** |

The refuted stratum is (i) the **top** one, (ii) **certified inhabited** — `optc.py c2`
reproduced exactly this pass: cube `Q3` and Wagner `V8` at `|V| = 24`, `|E| = 28`, `def = 0`,
`f(V) = +2`, `max f(W)` proper `= −1`, 2EC, `max closedHubNbhd = 4` (**INFEASIBLE**) — and
(iii) inside `hbareSplit`'s `∀`, which quantifies over the whole habitat. **So a corank-2-only
repair buys nothing:** corank 3 would still need *Step BE8*'s shape 1 or 3, and shape 3 is
seed-free and subsumes corank 2 anyway.

### Step INS7 — the successor shapes, and the one that is option B's own

*Step BE8* states three shapes; strategy §8.4's *"two"* is a correct compression, shape 2
reducing to shape 1. (Note §8.4's `(i)`/`(ii)` are **not** *Step BE8*'s `1`/`2`/`3` — §8.4's
`(ii)` is *Step BE8*'s shape **3**; cite the shape, not the roman numeral.)

| shape | option B's? | price |
|---|---|---|
| 1 — `∃`-seed + **seed-repair** | no | a deformation inside `HasPencilRealization K 3 G′`'s attainment locus **with no chart** — *Step BE8*: *"the same wall §(K-tight) Step 5 meets one level up"*. **`hK`'s own wall**, so it does not decouple `hbareSplit` from `hK` |
| 2 — a seed side condition | no | reduces to shape 1; and (INS-4) shows the condition fails against the **whole** span, not one panel |
| 3 — **bypass the antecedent** | no | **IS** the running (BE-14) thread: seed-free, one open step (S-mark) |
| **4 — the joint sweep** | **YES** | (INS-7) |

> **(INS-7)** *(OPEN; (i) a structural argument, (ii)/(iii) asserted — explicitly **not** a
> proof, and **the reason option B is not refuted outright**)* The one surviving candidate
> endpoint that is genuinely **option B's own** is §(K-tight) *Step 1*'s *"NEW, not in KT"*
> **joint sweep** `(pt v, pt a) ∈ Π̂(b) × Π̂(c)`. **(i)** Its escape space lies **inside the
> collapsed plane**: at the hit seeds `Π̂(b) = Π̂(c)` ((INS-4)), and every hinge it can move —
> `C(va)`, `C(vb)`, `C(ac)` — is a wedge of two points of that one plane, hence lies in the
> same 3-dimensional `Λ²Π̂` against which `U` pairs to rank **1**. **(ii)** But the joint sweep
> deletes **two** vertices from the shared framework, so its own `U′` is a *different*,
> potentially larger space, and `rank⟨U′, Λ²Π̂⟩ ≥ 2` is **not excluded** by anything measured
> here. **(iii)** Deciding it needs a **two-parameter (bi-affine) extension of (BE-2)** —
> three moving hinges, a bilinear rather than affine-linear criterion matrix, a re-derived
> `need_rank` — which **does not exist**, so taking shape 4 **re-opens link 2**, the link
> §8.4 records as discharged. **The cheapest measurement that would price it:** derive `U′`
> for the two-vertex-deleted shared framework and measure `rank⟨U′, Λ²Π̂⟩` at these 8 seeds —
> one direction, and a *necessary* condition rather than the full criterion. *Kill condition
> for this section: that measurement run, or (BE-14) closing `hbareSplit` without it.*
> **DISCHARGED 2026-09-09 (INSJOINT, ordinal 90): the measurement ran and (ii) is settled
> NEGATIVE — see (INS-12); the threshold in this paragraph's cheapest-measurement sentence is
> corrected by (INS-15), and (iii)'s re-opening of link 2 does not apply to a one-sided bound
> ((INS-16)).**

### Step INS8 — `U′` for the two-vertex-deleted framework, derived off the matrix rows

Direction **INSJOINT** (arc ordinal 90; `notes/pencil/fanout.md` §"INSJOINT"), the design
pass `notes/pencil/strategy.md` §8 ranked **4**, answering *Step INS7*'s own kill condition.
Driver `notes/scripts/w4/insjoint.py` (`uprime|pairing|deficit|sweep|dz`); all exact ℚ.

**How `U′` differs from `U`, and why — stated before any number.** `binsert.py` mode
`combined` measures `rank⟨U, Λ²Π̂(b) + Λ²Π̂(c)⟩` for the **one**-vertex-deleted `U`. Route A
moves `pt(v)` only, so its shared framework is `G − v`, which still **contains `a` and the
edge `ac`**; hence `U = \{u : ⟨u, m(a) − m(b)⟩ = 0 ∀ m ∈ ker R(G−v)\}` **depends on the
seed's own `pt(a)`**. The joint sweep moves `pt(v)` **and** `pt(a)`, so its shared framework
is `G − v − a` and its space must be independent of `pt(a)`. Different framework, different
space: a new derivation, not a re-run of `combined`.

With `deg v = deg a = 2`, `E(G) = E(G−v−a) ⊔ \{vb, va, ac\}`. Let `ω` be a left-nullvector
(self-stress) of `R(G)`, carrying a block `ν_e ∈ K⁵` on each hinge, and write
`U_e := Σ_j ν_e[j] w_j(C_e) ∈ perp(C_e)` with `w_j = perp_basis(C_e)` — exactly the row set
`kbare_common.build_rigidity` emits. The column blocks of the two **deleted** bodies are
touched by nothing else: block `v` (edges `vb`, `va`) forces `U_vb = U_va =: u`, and block
`a` (edges `va`, `ac`) forces `U_ac = u`. So **one** vector carries all three hinges, and the
blocks at the two chain **ends** leave the shared framework loaded by `(−u at b, +u at c)`.

> **(INS-9)** *(proved from the row structure of `build_rigidity`, not from a docstring;
> machine-validated against the exact rank of `R(G)` per placement)* With `s₀′` the row
> corank of `R(G−v−a)`,
> `U′ = \{u ∈ K⁶ : ⟨u, m(c) − m(b)⟩ = 0 for every motion m of G − v − a\}
> = \{u : (−u at b, +u at c) ∈ rowspan R(G−v−a)\}`, and at `(pt v, pt a) = (x_v, x_a)`
> `corank R(G) = s₀′ + dim(U′ ∩ C(vb)^⊥ ∩ C(va)^⊥ ∩ C(ac)^⊥) = s₀′ + dim U′ − rank M′`,
> where `M′ = [[⟨u_i, C(vb)⟩], [⟨u_i, C(va)⟩], [⟨u_i, C(ac)⟩]]` is **3 × dim U′**. So `U′` is
> **the same construction as `U`** with the deleted vertex's two **neighbours** `(a, b)`
> replaced by the deleted path's two **ends** `(b, c)`; `M′` gains a third row and its middle
> entry `C(va) = hat(x_v) ∧ hat(x_a)` is **bilinear** — precisely the shape (INS-7)(iii)
> priced as needing a two-parameter extension of (BE-2). Specializing `x_a` to the seed's
> `pt(a)` recovers (BE-2)'s own identity, by (INS-10)(i)/(ii). **Validation:** the identity
> is checked against the exact rank of `R(G)` at **48/48** sampled joint placements over the
> 8 hit seeds and at **117/117** on the DZ gadget, assert-gated so one failure raises.

### Step INS9 — the three facts that link the two calculi

> **(INS-10)** *(proved; asserted per seed in the driver rather than argued there)*
> **(i) `s₀′ = s₀`.** `G − v` is `G − v − a` plus the vertex `a` and the single edge `ac`;
> `a` has degree **1** there, its 5 rows are a `perp_basis` (independent) and its column
> block is touched by nothing else, so any self-stress charges them zero — the two
> left-nullspaces are isomorphic. **(ii) `U = U′ ∩ C(ac)^⊥`**, with `C(ac)` built from the
> **seed's** `pt(a)`: motions of `G − v` are motions of `G − v − a` with
> `m(a) = m(c) + t·C(ac)`, so `\{m(a) − m(b)\} = image(δ) + ⟨C(ac)⟩` for
> `δ : m ↦ m(c) − m(b)`. Hence **`U ⊆ U′` with `dim U′ − dim U ∈ \{0, 1\}`**, the value `1`
> exactly when `C(ac) ∉ image(δ)`. This **sharpens** *Step INS7*'s *"its `U′` differs"*: the
> difference is one specific linear condition. **(iii) `need′ − need = dim U′ − dim U`**,
> because `need = s₀ + dim U − c_G` and `need′ = s₀′ + dim U′ − c_G` with the **same** `c_G`
> — `c_G = 5|E(G)| − target(G)` is a function of `G` alone, so it cannot move when a vertex
> is deleted from the *shared* framework — and `s₀′ = s₀` by (i). *(Attainment of
> `target(G)` is `corank R(G) = c_G`, and `rank R(G) ≤ target(G)` always, so attainment ⟺
> `rank M′ = need′`.)* **Measured:** `s₀′ = s₀ = 0` at 8/8 and 117/117; `dim U = 4 → 5` and
> `need = 2 → need′ = 3` at **8/8** hits; **both** branches of (ii) are witnessed — the `+1`
> branch at 116 of 117 DZ seeds and the `0` branch at one (`dim U = dim U′ = 4`,
> `need = need′ = 3`).

### Step INS10 — the measurement (INS-7)'s kill condition asked for

At a hit seed `Π̂(b) = Π̂(c) =: Π̂` ((INS-4)) — **re-verified here on the `pt(a)`-EXCLUDED
reading of `Π̂(c)`**, which is the object the joint sweep needs and a sharper check than
(INS-4)'s (that one computes `Π̂(c)` with the seed's `hat(pt a)` among the anchors). All
three hinges then lie in the 3-dimensional `Λ²Π̂`: `C(vb)` and `C(ac)` by the sweep's own
domain, and `C(va) = hat(x_v) ∧ hat(x_a)` because **both** moving points lie in that one
plane. Every row of `M′` is therefore `u ↦ ⟨u, C⟩` with `C ∈ Λ²Π̂`, so
`rank M′ ≤ rank⟨U′, Λ²Π̂⟩` **at every point of the domain**.

| seeds (stratum `cycleflat`) | collapse | `dim U` | `dim U′` | `rank⟨U,Λ²Π̂⟩` | `rank⟨U′,Λ²Π̂⟩` | `need` | `need′` | shape 4 |
|---|---|---|---|---|---|---|---|---|
| 0, 1, 2, 3, 4, 5, 7, 9 | **yes**, 8/8 | 4 | **5** | **1** | **2** | 2 | **3** | **EXCLUDED** |

> **(INS-11)** *(measured; cap-free per seed)* At all **8** of (BE-5)'s legal target-rank
> route-A hit seeds — the identical set, obtained through `binsert.verdict` itself, every one
> in the `cycleflat` stratum — `rank⟨U′, Λ²Π̂⟩ = **2**` and `need′ = **3**`. The one-vertex
> figure is reproduced exactly: `rank⟨U, Λ²Π̂⟩ = 1` at 8/8, **asserted equal to
> `breakhunt.pairing_rank`'s own return** at each seed, so this is BINSERT's number and not a
> re-derivation of it. Rank-nullity then gives a structural reading, machine-checked:
> `dim U = 4`, `dim Λ²Π̂ = 3` and pairing rank `1` force **`(Λ²Π̂)^⊥ ⊂ U ⊆ U′`** — `U` already
> annihilates a full 3-dimensional complement and `U′` adds one dimension that pairs
> nontrivially, which is the whole content of the `1 → 2` step.

### Step INS11 — deficit preservation: shape 4 is EXCLUDED and option B is SPENT OUTRIGHT

> **(INS-12)** *(proved, given the hypotheses (INS-14) names; the verdict of this direction)*
> Let `U ⊆ U′` with codimension `k := dim U′ − dim U`. Extending a basis of `U` to one of
> `U′` adds `k` rows to the pairing matrix, so `rank⟨U′, L⟩ ≤ rank⟨U, L⟩ + k` for **any**
> `L`. With (INS-10)(iii)'s `need′ − need = k`, subtract:
> **`rank⟨U′, Λ²Π̂⟩ − need′ ≤ rank⟨U, Λ²Π̂⟩ − need = 1 − 2 = −1`.**
> Hence `rank M′ ≤ rank⟨U′, Λ²Π̂⟩ ≤ need′ − 1 < need′` **at every point of `Π̂(b) × Π̂(c)`
> simultaneously**, so the joint sweep fails uniformly and **shape 4 — (INS-7), option B's
> one surviving endpoint — is EXCLUDED**. Because the bound is a *subspace containment*
> rather than an identical-vanishing test, the per-seed verdict is **cap-free** and needs no
> sweep. **Option B is therefore SPENT OUTRIGHT:** its chain has no un-run link ((INS-6)),
> both KT-inherited routes are refuted ((BE-5)/(INS-3)), and its one un-analyzed endpoint is
> dead — **no un-run measurement remains under the "spent" verdict**. *The mechanism, in one
> sentence:* the joint sweep buys one extra dimension of escape and pays for it with one
> extra unit of required rank, so **the degeneracy the panel collapse creates is invariant
> under enlarging the sweep by another deleted body**. **Measured:** the deficit is `−1` at
> **8/8** hits and `+2` at **19/19** non-hit target-rank controls — the same total dichotomy
> (INS-4) found, now in the joint-sweep quantity. **The inequality is tested as its own
> sentence** (`notes/scripts/README.md` §4 conventions 1/6): valid on 400 random
> `(U ⊂ U′, L)` triples with **0** violations, **ATTAINED** on 200 constructed triples of the
> measured shape (`rank 1 → 2` at codimension 1 — the random family is *slack*, both pairings
> saturating at `dim L`, so it tests validity and **not** tightness), and **SATISFIED** on
> 200 constructed deficit-**zero** triples (`rank 2 → 3 = need′`), so the bound **does not
> reject an escape that exists**. That last test is the honest scope of the kill: it
> **inherits** from route A failing by a strictly positive margin.

### Step INS12 — the direct sweep, and the negative control

> **(INS-13)** *(measured; sampled corroboration, never the verdict's basis)* The joint
> domain is **INHABITED**, so the exclusion is not vacuous: at the 8 hit seeds **160**
> sampled `(x_v, x_a) ∈ Π̂(b) × Π̂(c)` are legal pencil witnesses of `G`
> (`verify_pencil_witness`, per placement), and every one has **exact rank 137 against
> `target(G) = 138`** — `0` attain — with `rank M′ = 2` at **160/160**, matching the subspace
> bound exactly rather than merely respecting it. **Negative control** (dispatch-log F13 /
> §4 convention 6 — a test observed only rejecting is untested): the identical sweep at the
> non-hit target-rank seeds **ATTAINS at 20/20 placements per seed**, so the instrument finds
> escapes where they exist. *(Legality is exactly the two panel constraints: `v`'s own closed
> star `\{v,a,b\}` and `a`'s `\{a,v,c\}` are three points each and coplanar for free, so the
> whole constraint is `hat(x_v) ∈ Π̂(b)` — forced because `b`'s star minus `v` has rank 3 —
> and `hat(x_a) ∈ Π̂(c)`, forced the same way at `c`. Note `a ∉ N_G(b)`, so `Π̂(b)` is fixed
> by the seed and independent of both moving points; the fresh edge `ab` exists only in
> `G′`.)*

### Step INS13 — the scope of the exclusion, and a second population

> **(INS-14)** *(proved; a scope statement, and it is what keeps (INS-12) from being
> over-read)* (INS-12) needs **three** hypotheses, each true at the 8 hits and each
> nameable: **(i)** the chain's far end `c` is a **hub** — only then is `pt(a)` confined to a
> 3-space `Π̂(c)` and `C(ac) ∈ Λ²Π̂`; **(ii)** the **panel collapse** `Π̂(b) = Π̂(c)`, without
> which `C(va)` need not lie in `Λ²Π̂(b) + Λ²Π̂(c)` at all; **(iii)** route A's margin at that
> seed is **strictly positive** (`rank⟨U,Λ²Π̂⟩ ≤ need − 1`), which is where the `−1` comes
> from. So the exclusion is **seed-generic, not seed-enumerated**: it holds at *any* seed
> satisfying (i)–(iii), measured or not. What it does **not** cover, stated so the row does
> not read as stronger than it is: a **non-hub-end `index = 2` split** (there `pt(v)` is
> unconstrained, the joint domain is not a product of two panels, and (INS-12)'s containment
> fails — the same split *Step INS4* recorded as unmeasured anywhere), and a hypothetical
> hub-end route-A hit **without** the collapse (`Π̂(b) = Π̂(c)` is measured 8/8 against 0/19,
> **not proved**). Neither moves the row's status word: `hsafe` permits hub-end splits, so a
> hub-end refutation already kills a `∀`-statement. **Second population:** (INS-9)/(INS-10)
> are *proved*, so they must hold off the Q3 stratum, and they do — **117/117** DZ seeds
> across **4** chains at `index = 1`, `corank(G′) = 2`, which is the one axis the Q3
> generator cannot vary.

### Step INS14 — the kill condition's recorded threshold was wrong, and by exactly the drop

> **(INS-15)** *(a correction to the landed record, not a mathematical claim of its own —
> and the most consequential line of this direction)* *Step INS7*'s closing sentence and the
> `§(K-ins)` gap-map row both compressed the kill condition to *"`rank⟨U′, Λ²Π̂⟩ ≥ 2` would
> give option B an endpoint of its own; `≤ 1` closes the route outright"*. **`2` is the
> ONE-vertex `need`.** The joint sweep's required rank is `need′ = need + (dim U′ − dim U)`
> ((INS-10)(iii)), which equals `2` only in the branch `dim U′ = dim U` and is **3** at every
> one of the 8 hit seeds. The measurement is **exactly 2** — so a reader applying the
> recorded threshold to the correct number would have concluded **"option B SURVIVES"** and
> resurrected a dead route. The defect is not in (INS-7)'s mathematics, whose (ii) says only
> that `≥ 2` *"is not excluded"* — true as written; it is in the **compression** of that
> sentence into a threshold, which silently reused route A's `need`. **The general lesson,
> stated because it is not specific to this row:** when a kill condition is written as
> `measured ≥ CONSTANT`, the constant must be **derived in the same breath as the object it
> is compared against** — a threshold inherited from the predecessor's object is a threshold
> for the predecessor's object. A related, weaker correction: (INS-7)(i)'s ground for
> pessimism (the escape space *"lies inside the collapsed plane"*) proves nothing on its own,
> since `U′` also grows; the actual ground is that the growth is **exactly cancelled**
> ((INS-10)(iii)).

### Step INS15 — link 2 is NOT re-opened

> **(INS-16)** *(proved)* (INS-7)(iii) prices shape 4 as needing a **two-parameter
> (bi-affine) extension of (BE-2)** — three moving hinges, a bilinear criterion matrix, a
> re-derived `need_rank` — *"which does not exist, so taking shape 4 re-opens link 2"*. That
> is correct for a **criterion** (deciding attainment *iff*), and it is exactly what this
> direction did **not** need. A **one-sided** bound suffices to kill: `rank M′ ≤
> rank⟨U′, Λ²Π̂⟩` requires only that the three hinges lie in a *fixed* 3-space, and the
> `need′` side is arithmetic. So **link 2 stays discharged** ((INS-6)) and the calculus is
> not re-opened by this landing; the bi-affine extension remains non-existent and is now also
> **unnecessary**, the endpoint it was needed for being dead. *(Corollary for the (BE-14)
> thread: nothing here touches S-mark, (BE-E4′) or the `ρ₁ + ρ₂` residue.)*

### Verification

`python3 notes/scripts/w4/binsert.py routeb` (≈ 330 s, (INS-2)/(INS-3): route B at (BE-5)'s
8 hit seeds, plus DZ's two splits as corank-2 controls); `strata` (≈ 65 s, (INS-5)); `combined`
(≈ 80 s, (INS-4), the panel collapse against 19 controls). Reproductions of landed drivers,
unmodified: `notes/scripts/kbare/breakhunt.py arith` (1 s, (BE-6) + the 216-member census),
`notes/scripts/kbare/optc.py c2` (≈ 154 s, the index-2 habitat certification — the
load-bearing premise of the whole verdict), `notes/scripts/kbare/breakhunt.py rzero` (≈ 340 s,
the 8 T1 hits).

**Steps INS8–INS15 (direction INSJOINT, ordinal 90).**
`python3 notes/scripts/w4/insjoint.py uprime` (149–153 s, (INS-9)/(INS-10): `U′` at the 8 hit
seeds, the two-vertex corank identity at 48 joint placements, the three structure facts
asserted per seed); `pairing` (159–160 s, (INS-11): the measurement, with
`breakhunt.pairing_rank` asserted equal at each seed); `deficit` (240 s, (INS-12): the
inequality on 400 random + 200 tight + 200 deficit-zero triples, the 8 hits and the 19
controls); `sweep` (277–320 s, (INS-13): 160 legal joint placements plus the attaining
negative control); `dz` (424–439 s, (INS-14): 117 DZ seeds on a second gadget). The 8 hit
seeds are obtained **through `binsert.verdict` itself**, so the set is identical by
construction rather than by reproduction. Every mode assert-gated: a structure-fact failure
raises rather than printing.

**What did NOT move.** `hbareSplit` (open, pinned; tier T1 throughout — its consequent is an
`∃` over frameworks and the gadget **attains**, 138/138); `PencilPair K 3 G` (**not** a PENCIL
event); (BE-14)/S-mark; `hK`, (GR-15), (GR-10), (OC-8), class uniformity, (K-res); the Lean
hold (no `.lean`, none proposed). E1/E2 did not fire; **E3 is ARMED (by GBAL) and did NOT
fire** — reported, never fired. Direction-A pivot-rule classification: a **T1-style *route*
refutation**, neither a half-1 re-pin nor a half-2 conjecture failure. **Unchanged at
INSJOINT (ordinal 90)**, which adds only that (BE-E4′) and S-mark are untouched by the
shape-4 exclusion ((INS-16)).

