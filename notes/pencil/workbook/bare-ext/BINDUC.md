## §(K-bare-ext) — continuation (direction BINDUC): the induction's **BASE IS FREE** — 3-connectivity forces `def₂ = 0`, so the declined `def₂ = def₃` slice covers the whole base — BZAVOID's asserted 2-cut `− 6` is **REFUTED** and replaced by an exact `max`-law, the rank half is reduced to **one named composition lemma** with its free sub-case proved and its obstruction located, and a **named construction** proves (BE-14) at 5 824 further graphs, 2 441 of them beyond every witness the arc had

Direction **BINDUC** (`notes/pencil/fanout.md` §"BINDUC", ordinal 42), the arc's
fiftieth and the **max-impact pick under a user-supplied criterion** (2026-08-26:
*"the direction that is most likely to have most impact towards either proving or
disproving the target theorem"*). Read against *Steps BE14–BE18* (direction
BZAVOID) and *Steps BE9–BE13* (direction BATTAIN), whose figures are **cited,
never re-run**. Driver `notes/scripts/w4/binduc.py`
(`base|flatwit|gate|twocut|rank2|hubplane|force|validate`); all exact ℚ, every
rng seeded and printed.

**Status, stated before the mathematics.**

- **HIT shape 1, and the part the spec said had "no named answer" turns out to be
  FREE.** *Job 2* asked whether the 3-connected base is attackable. It is not
  merely attackable: **a 3-connected graph has `def₂ = 0`**, by a four-line
  elementary argument, hence `def₃ = 0`, hence the **flat** witness attains in
  closed form. **(BE-20)**. So BATTAIN's declined `def₂ = def₃` slice — which the
  user declined *as a deliverable* and the spec explicitly re-authorized *as a
  base case* — **covers the entire base of the connectivity induction**, and the
  contrapositive is the sentence that reframes the whole problem: **`def₂ > def₃`
  forces a cut of size `≤ 2`**, so *every* graph on which (BE-14) is not already
  closed is 1-cut- or 2-cut-decomposable.
- **BZAVOID's asserted 2-cut law is FALSE, not merely unchecked.**
  `def₃(G) = def₃(G₁) + def₃(G₂) − 6` goes **negative** — at two triangles
  sharing an edge it reads `−4` against the true `0` — and is right at only
  **0.5 %** of 10 804 enumerated gluings. The exact law, derived from `def₃`'s own
  maximand as the spec required, is
  **`def₃(G) = max(g₁ + g₂, f₁ + f₂ − 6) = f₁ + f₂ − min(δ₁ + δ₂, 6)`**, where
  `g_i` is the same maximand restricted to partitions putting the two cut
  vertices in **one part** and `δ_i = f_i − g_i ∈ [0, 6]`. Both directions
  proved; **both branches of the `max` are needed**. **(BE-21)**.
- **The rank half is NOT routine, and now it is exactly priced.**
  `M(G)` is the fibre product of `M(G₁), M(G₂)` over the **pair** of shared
  bodies, so `dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁ + ρ̄₂)` with `ρ̄_i` the
  space of **relative screws** of `v` against `u` realized inside `G_i`; with
  attaining pieces, **`G` attains iff `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)`**. Two
  obligations fall out, and they are what BZAVOID's "routine" was hiding: **(a)**
  `ρ_i ≤ δ_i` always, with equality iff the **welded** framework attains *its*
  target — so the induction must run on a **strengthened statement**; **(b)** a
  **general-position** condition on two subspaces of the 6-dimensional screw
  space, which the residual gauge group (dimension **7** at an adjacent cut pair,
  **5** at a non-adjacent one) cannot supply by a dimension count alone. The
  **free sub-case is proved**: `δ₁ = δ₂ = 0` — in particular both pieces rigid,
  which by (BE-20) is every 3-connected piece — makes the condition vacuous. And
  the **sharpening that names the successor's target**: with *one* rigid side the
  criterion collapses to the single condition `ρ = δ` on the *other* side, with
  no general-position content at all — measured as a **biconditional** at 296
  ear additions to 3-connected bases (240 attaining, 56 short by exactly the
  shortfall of `ρ`). **(BE-22)**.
- **The induction is assembled and (BE-14) is reduced to ONE lemma.** Base
  {3-connected} ∪ {max degree `≤ 2`} ∪ {`def₂ = def₃`}, plus the 1-cut
  composition (BE-18), plus the 2-cut composition — that is the whole induction,
  and only the last item is open. A by-product: the landed Phases-24–26 gate
  `IsGeneralPositionPlacement` is satisfiable on the pencil stratum **exactly on
  the hub-free class**, so (BE-17)'s dead route is **alive on the max-degree-`≤ 2`
  base** and dead everywhere else. **(BE-20)(iii)**, **(BE-23)**.
- **A named construction, and 5 824 new theorems.** The **hub-plane**
  construction — one plane per hub, feasible with generic planes exactly when
  every closed neighbourhood holds `≤ 3` hubs — and its class refinement (one
  plane per **forced hub class**) attain the target at **5 824** graphs
  (4 881 + 312 + 31 of them **exhaustively** at `n ≤ 6`, 600 sampled at
  `n = 7…10`), **zero failures**, of which **2 441 have `def₂ > def₃`**, i.e. the
  flat witness provably misses. Each is a **theorem for that graph** (rank `≤`
  target is universal). The class refinement also reaches **necklace(3) and
  necklace(4)**, reproducing BATTAIN's `localcone` attainment by a systematic
  construction. **(BE-23)(i)**.
- **The disproof side: the new-cap mechanism the spec asked for EXISTS, is
  strictly more general than BZAVOID's, and fires EMPTY too.** BZAVOID's
  flatness propagation runs on **triangles**; the general rule is *"`π_v` is
  forced to `π` as soon as `closedNbhd(v)` holds three independent points already
  in `π`"*, which fires **without a triangle** — `K_{3,3}` is forced flat and is
  triangle-free. Hunted: **27 470 connected graphs exhaustively** at `n ≤ 6`
  (20 963 forced flat) plus 4 800 sampled at `n = 7…10` (4 307 forced flat),
  **zero with `def₂ > def₃`**, and the largest `def₂` at a forced-flat graph is
  **5**, so the measured statement is the strictly stronger *"forced flat ⇒
  `def₂ = def₃`"* rather than *"⇒ `def₂ = 0`"*. **(BE-23)(ii)**.
- **Verdict: (BE-14) remains OPEN; nothing is refuted except a claim of
  BZAVOID's own and a route.** `PencilPair K 3 G`, `hbareSplit` and
  (BE-14)-for-all-`G` are all untouched. **Not a PENCIL event.** **(BE-24)**.

### Standing notation

Inherited from *Steps BE9–BE18* verbatim (`n := normal`, `p := point`, `W_e`,
`closedNbhd`, hub, `target(G) = 6(|V|−1) − def₃(G)`, `Y(G)`, `Z(G)`,
`def₂ := max_P 3(|P|−1) − 2d(P)`, `def₃ := max_P 6(|P|−1) − 5d(P)`). Added here:

- **`f(G) := def₃(G)`**, and for an ordered pair `{u,v} ⊆ V`,
  **`g_{uv}(G) := max{6(|P|−1) − 5d(P) : P a partition with u, v in ONE part}`**,
  and **`δ_{uv}(G) := f(G) − g_{uv}(G)`**. `g_{uv}(G) = def₃(G / uv)` with the
  contraction taken as a **multigraph** (parallel edges kept, the loop from `uv`
  dropped) — the two descriptions are the same maximand.
- **flat configuration**: all points distinct in one plane of `P³`. **Hub
  load** `h(G) := max_w #{hubs in closedNbhd(w)}`.
- **`ρ̄_{uv}(F)`**: the image of the motion space `M(F)` under
  `m ↦ m(v) − m(u)`, a subspace of the 6-dimensional screw space `Λ²K⁴`;
  `ρ_{uv} := dim ρ̄_{uv}`.

**Carrier check, done off the Lean bodies rather than the prose.**
`Graph.partitionDef G n f = bodyBarDim n · (numParts − 1) − (bodyBarDim n − 1) ·
|crossingEdges|` (`Molecular/Deficiency.lean:262`) with
`bodyBarDim n = n(n+1)/2` (`BodyBar/Framework.lean:61`), and
`Graph.deficiency G n = ⨆_f partitionDef G n f` (`ibid.:273`). So `def₃` **is**
`deficiency G 3` (`bodyBarDim 3 = 6`, giving `6(q−1) − 5d`) and — this had not
been said in the workbook — **`def₂` is literally `deficiency G 2`**
(`bodyBarDim 2 = 3`, giving `3(q−1) − 2d`), i.e. the arc's "planar deficiency" is
the same landed definition at `n = 2`, not a harness-only device. Non-negativity
is the one-part partition (`partitionDef_one`), as the docstring says and the
body confirms.

### Step BE19 — the base of the induction is FREE

> **(BE-20)(i)** *(proven; elementary, and enumerated)* **A 3-connected graph has
> `def₂ = 0`, hence `def₃ = 0`.**
>
> *Proof.* First, every proper nonempty `S ⊆ V` has `|∂S| ≥ 3`. If `|S| = 1` this
> is `deg(v) ≥ 3` (3-connectivity forces minimum degree `≥ 3`); if `|S| = 2`,
> say `S = {a,b}`, then `|∂S| = deg a + deg b − 2·[ab ∈ E] ≥ 3 + 3 − 2 = 4`; and
> symmetrically when `|V∖S| ≤ 2`. Otherwise `|S| ≥ 3` and `|V∖S| ≥ 3`, and if
> `|∂S| ≤ 2` then picking one endpoint in `S` of each boundary edge gives a set
> `T ⊆ S` with `|T| ≤ 2` whose removal leaves `S∖T ≠ ∅` disconnected from
> `V∖S ≠ ∅` — a cut of size `≤ 2`, contradiction. Now let `P` be a partition with
> `q ≥ 2` parts; each part is a proper nonempty subset, so
> `2d(P) = Σ_i |∂V_i| ≥ 3q`, whence
> `3(q−1) − 2d(P) ≤ 3q − 3 − 3q = −3 < 0` and `6(q−1) − 5d(P) ≤ 6(q−1) − 7.5q < 0`.
> The `q = 1` partition contributes `0`, which is therefore the maximum in both
> cases. ∎
>
> The `def₃` half also follows from BZAVOID's (BE-15)(a) (`def₂ = 0 ⇒ def₃ = 0`);
> the direct derivation above is given because it costs one extra inequality and
> keeps the base case independent of that corollary.

> **(BE-20)(ii)** `[INFORMAL]` *(the flat cone law on the POINT side — measured here for the
> first time; proven-informally, inheriting (BE-13))* At the **flat**
> configuration — all points distinct in one plane — every closed star is
> coplanar, so it is a **legal (BE-14) configuration at every graph**, and its
> exact rank is
>
> **`rank(flat) = 6(|V|−1) − def₂(G)`.**
>
> This is the projective **dual** of BATTAIN's (BE-13) cone law and it matters
> that it is the dual rather than the same statement: BZAVOID's cap 6 records
> that at BATTAIN's cone **all points coincide**, which (BE-14) as restated in
> *Step BE18* forbids (*"adjacent points distinct"*). The flat configuration is
> the legal representative of that dual pair. Combined with (BE-20)(i):
>
> **(BE-14) holds at EVERY 3-CONNECTED GRAPH, with a closed-form witness and no
> genericity argument at all.**
>
> Measured (`binduc.py flatwit`, 1.3 s, 4 seeded draws per shape, max taken): the
> law is **exact at all 14 battery shapes with a computable `def₂`** —
> `K₄ 18/18`, `K₅ 24/24`, `prism 30/30`, `K_{3,3} 30/30`, `cube 42/42`,
> `Petersen 54/54` (all `def₂ = 0`, all **attaining**), and
> `θ(3,3,3) 39 = 42 − 3`, `θ(4,4,4) 54 = 60 − 6`, `θ(4,5,6) 69 = 75 − 6`,
> `C₆ 27 = 30 − 3`, `C₈ 37 = 40 − 3`, `necklace(4) 89 = 90 − 1`,
> `spider(5,5,5)+c 81 = 90 − 9`, and **`DZ 103 = 114 − 11`** — the last an
> independent corroboration of BATTAIN's recorded `def₂(DZ) = 11` through a
> completely different quantity (the exact rank of a flat point configuration).

> **(BE-20)(iii)** *(proven; the gate, read off the Lean body)* The landed
> Phases-24–26 gate `SimpleGraph.IsGeneralPositionPlacement`
> (`GeneralPositionPlacement.lean:59`) is, verbatim,
> `∀ s : Finset V, s.card ≤ 4 → AffineIndependent ℝ (fun i : s => p i)`. (BE-17)(i)
> recorded that the pencil condition **negates** it at every hub. The converse is
> the useful direction: **`G` has no hub (max degree `≤ 2`) iff the gate is
> satisfiable simultaneously with the pencil condition**, because there the
> pencil condition is *vacuous* and a general-position placement exists
> (`exists_isGeneralPositionPlacement`). So the landed dictionary
> `molecular_finrank_motions_eq_square_ker` and `molecule_rank_formula` are
> available on **exactly** the hub-free class — which is precisely the *cycles
> and paths* base the induction needs.
>
> Measured (`binduc.py gate`, 0.1 s): at generic exact-ℚ points, `C₄`, `C₆`, `C₈`
> and `P₅` are pencil-legal **and** general-position **and** attaining
> (`18/18`, `30/30`, `40/40`, `20/20`); at the flat witness the gate is violated
> at **1 of 1** 4-subsets of `K₄` and **330 of 330** of `θ(4,4,4)`; and at the
> hub-plane witness of `θ(4,4,4)` every hub's closed star is still affinely
> dependent, so the gate stays negated there too — the hub-free case is not a
> loophole in (BE-17), it is its exact complement.

**Machine validation of (BE-20)(i)** (`binduc.py base`, 433 s). **EXHAUSTIVE over
all connected graphs on `n = 4…7`: 226 891 3-connected labelled graphs
(1 / 26 / 1 768 / 225 096), every one with `min|∂S| ≥ 3`, `def₂ = 0` and
`def₃ = 0`, zero exceptions**; the `2^n`-subset boundary sweep ran on 2 920 of
them (all of `n ≤ 6`, every 200th at `n = 7`), and the independent
set-partition oracle confirms at `n ≤ 6` that the **worst** `partitionDef₂` over
`q ≥ 2` partitions is exactly `−3`, so the bound in the proof is tight. Plus
1 200 sampled 3-connected graphs at `n = 8, 9, 10`. The contrapositive is checked
in the same mode: **EXHAUSTIVE `n = 4…6`, 16 214 connected graphs with
`def₂ > 0`, NOT ONE of them 3-connected.**

**What this does to the spec's job 2.** The spec asked whether the base is
attackable and offered the `def₂ = def₃` slice as a legitimate base case. The
answer is that the offer is **exactly right and the base is free**: on the
3-connected class `def₂ = def₃ = 0`, so the slice is not a weaker partial there —
it is the whole of it. The residual difficulty of (BE-14) is therefore **entirely
in the composition steps**, and since `def₂ > def₃ ⇒ κ(G) ≤ 2`, every graph that
needs a composition step has one available.

### Step BE20 — the 2-cut `def₃` law, and the refutation of the inherited `− 6`

Let `G = G₁ ∪ G₂` with `V₁ ∩ V₂ = {u,v}`, `E₁ ∩ E₂ = ∅` (the edge `uv`, if
present, belongs to exactly one side), and each side carrying a private vertex.

> **(BE-21)(i)** *(refutation; explicit witness)* **BZAVOID's asserted 2-cut law
> is false.** With `G₁` the triangle `012` and `G₂` the path `0–3–1`, so
> `G = K₄ − e`: `def₃(G₁) = 0`, `def₃(G₂) = 2`, `def₃(G) = 0`, and the asserted
> `def₃(G₁) + def₃(G₂) − 6 = −4` — **negative**, which `def₃` never is (the
> one-part partition witnesses `0`). The claim is not off by a constant either:
> across 10 804 enumerated gluings it is correct at **54** (0.5 %) and
> **impossible** at 9 425 (87.2 %).

> **(BE-21)(ii)** *(proven, both directions; enumerated)* **The exact law is**
>
> **`def₃(G) = max(g₁ + g₂, f₁ + f₂ − 6) = f₁ + f₂ − min(δ₁ + δ₂, 6)`,**
>
> with `f_i = def₃(G_i)`, `g_i = g_{uv}(G_i)`, `δ_i = f_i − g_i`.
>
> *`≤`.* Let `P` be a partition of `V`, `P_i := P|_{V_i}`, `a = |P₁|`, `b = |P₂|`,
> and `m` the number of parts of `P` meeting **both** `V₁` and `V₂`. Every edge of
> `G` lies in exactly one `G_i` and crosses `P` iff it crosses `P_i`, so
> `d(P) = d₁ + d₂` exactly; and `|P| = a + b − m`. Hence
> `val(P) = val(P₁) + val(P₂) − 6(m−1)`. If `m = 1` the unique part meeting both
> sides contains `u` **and** `v`, so `val(P_i) ≤ g_i` and `val(P) ≤ g₁ + g₂`. If
> `m ≥ 2` then `val(P) ≤ f₁ + f₂ − 6`. (`m ≥ 1` always, since `u`'s part meets
> both.)
> *`≥`.* Given partitions `P₁, P₂` let `P` be their **join** (glue along `u`,`v`).
> The gluing graph has two edges, so its rank is `1` when `u,v` share a part on
> both sides and `≤ 2` otherwise; hence `|P| ≥ a + b − 2`, with `|P| = a + b − 1`
> in the first case, and `d(P) ≤ d₁ + d₂` since `P` is coarser. Taking `P_i`
> optimal-with-`u,v`-together gives `def₃(G) ≥ g₁ + g₂`; taking `P_i` optimal
> gives `def₃(G) ≥ f₁ + f₂ − 6`. ∎
>
> *`δ_i ∈ [0,6]`.* `g_i ≤ f_i` is immediate; and merging the `u`-part and the
> `v`-part of an optimal `P_i` loses `6 − 5·e(A,B) ≤ 6`, so `g_i ≥ f_i − 6`. ∎
>
> **Both branches are needed.** Over the enumeration the `g₁+g₂` branch attains
> the max at 10 798 gluings and the `f₁+f₂−6` branch at 54, of which **6 are
> strict** — the `f`-branch is the only one that sees, e.g., `C₁₀` cut at
> antipodes (`f₁ = f₂ = 5`, `g₁ = g₂ = 0`, law `= 4 = def₃(C₁₀)`).

**Machine validation** (`binduc.py twocut`, 3.3 s). **10 804 gluings** built from
all connected spanning pieces on `n = 3, 4, 5` (4 / 38 / 728, each piece's
`(f, g)` computed once by the **independent set-partition oracle** and `f`
cross-checked against `kbare_common.exact_deficiency` at every one, with
`0 ≤ f − g ≤ 6` asserted): **the law holds at every gluing**, both forms of it
(`max` and `min`) agreeing identically. Observed `δ` range `0…4`.

**Why the `− 6` is nonetheless the right *shape*.** `min(δ₁+δ₂, 6)` is `6` exactly
when the two sides between them can free all six degrees of the relative screw,
so BZAVOID's `−6` is the **worst case** of the correction, not its value; and the
`GL₄` transitivity the spec flagged is what the rank half spends it on (*Step
BE21*). The spec's warning that a 2-cut needs **two flags aligned at once** is
confirmed and quantified there.

### Step BE21 — the rank half: the exact composition law, its free case, and where it obstructs

> **(BE-22)(i)** *(proven; elementary, verified exactly)* With `M(F)` the motion
> space (the kernel of the `5|E| × 6|V|` body-hinge matrix, so
> `dim M = 6|V| − rank`),
>
> **`dim M(G) = dim M(G₁) + dim M(G₂) − 6 − dim(ρ̄₁ + ρ̄₂)`.**
>
> *Proof.* `M(G) = {(m₁,m₂) ∈ M₁ × M₂ : m₁ = m₂ on {u,v}}`, the kernel of
> `(m₁,m₂) ↦ (m₁(u) − m₂(u), m₁(v) − m₂(v))`, whose image is `R₁ + R₂` for
> `R_i ⊆ S ⊕ S` the image of `M_i` at `(u,v)`. Each `R_i` contains the diagonal
> `Δ = {(s,s)}` (the constant motions of a connected piece), so
> `dim(R₁+R₂) = 6 + dim((R₁+R₂)/Δ) = 6 + dim(ρ̄₁ + ρ̄₂)`. ∎

> **(BE-22)(ii)** *(proven)* **`ρ_i ≤ dim M_i − 6 − g_i`, with equality iff the
> WELDED framework attains.** Welding `u` to `v` keeps every hinge line and drops
> the (now looping) `uv` constraint, so the welded framework is a body-hinge
> framework on the **multigraph** `G_i / uv` and obeys the same elementary
> partition cap `dim M ≥ 6 + def₃`; and
> `dim M(welded) = dim M_i − ρ_i` by definition of `ρ̄_i`. Since
> `def₃(G_i/uv) = g_i`, the bound follows. **When the piece attains
> (`dim M_i = 6 + f_i`) this reads `ρ_i ≤ δ_i`.** ∎

> **(BE-22)(iii)** *(proven; the criterion)* If both pieces attain, then
>
> **`G` attains `⟺ dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)`,**
>
> by (i), (ii) and the (BE-21) law. So the 2-cut composition needs **two**
> things, neither of them a restatement: **(a)** `ρ_i = δ_i`, i.e. each piece's
> chosen configuration must make the **welded** framework attain too — an
> obligation about a *contracted multigraph*, so the induction has to be run on a
> **strengthened statement**; and **(b)** the two subspaces `ρ̄₁, ρ̄₂` of the
> 6-dimensional screw space must be in **general position**.
>
> > **FORWARD POINTER, 2026-09-01 (direction BGENUINE, *Step BE85* /
> > (BE-86)(i)) — the HYPOTHESIS is load-bearing, and quoting the criterion
> > without it has already misled a spec.** *"If both pieces attain"* is not
> > decoration. With `a_i := dim M_i − 6 − f_i ≥ 0` the side's own attainment
> > loss at the chosen configuration, the same three ingredients give the
> > criterion **unconditionally**:
> >
> > **`G` attains ⟺ `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6) + a₁ + a₂`,**
> >
> > of which the clause above is the `a₁ = a₂ = 0` case. The `(K-bare)`
> > gap-map row quoted this statement **with the proviso dropped**, and the
> > BGENUINE spec inherited the drop; at 100 of BONEONE's 392 forced
> > witnesses one side does **not** attain, and reading those rows against
> > `min(δ₁+δ₂,6)` alone shows an apparent *excess* of `1` that is entirely
> > the missing `a_i`. The row is corrected; this is the originating prose.

> **(BE-22)(iv)** *(proven; the free sub-case)* **`δ₁ = δ₂ = 0` makes the
> composition automatic:** then `ρ_i ≤ δ_i = 0`, so `dim(ρ̄₁+ρ̄₂) = 0 = min(0,6)`
> and (iii) fires with no general-position content. In particular **two rigid
> pieces always compose over a 2-cut** — and by (BE-20) every 3-connected piece
> is rigid. This is why the *base* of the induction never meets the hard case.

> **(BE-22)(v)** *(the obstruction, located and dimension-counted; NOT closed)*
> The alignment the 1-cut argument got for free is a `PGL₄` transitivity on
> **(plane, point-on-plane) flags**; a 2-cut needs the *pair* aligned. Two
> regimes, and they are genuinely different:
> **(α) `uv ∈ E(G)`** — then `p_v ∈ n_u` and `p_u ∈ n_v`, so both planes contain
> the line `L = p_u ∨ p_v` and the shared datum is *(a line, two points on it, two
> planes through it)*: `PGL₄` **is** transitive there (it acts as `PGL₂ × PGL₂`
> on `L` and on the pencil of planes through `L`, and `PGL₂` is 3-transitive), and
> the residual gauge group has dimension **`15 − 8 = 7`**.
> **(β) `uv ∉ E(G)`** — the shared datum is two flags with no cross-incidence,
> orbit dimension `10`, residual gauge group dimension **`5`**.
> **Consequence, and it is the honest bad news:** `ρ̄₂`'s orbit under a
> `≤ 7`-dimensional group inside `Gr(δ₂, 6)` (dimension up to `9`) is a proper
> subvariety, so **general position is not free by a gauge count** — it has to
> come from the *piece's own moduli* inside its pencil stratum. Worse for regime
> (β): a realization of `G₂` with **generic** flags at `u,v` cannot be carried by
> any projective map onto a realization of `G₁` whose flags satisfy an incidence,
> because `PGL₄` preserves incidence — so when the cut pair is adjacent on one
> side only, the *other* side must be realized with the matching incidences
> imposed, which is the 2-sum-with-a-virtual-edge shape rather than a plain
> union.

> **(BE-22)(vi)** *(proven; the sharpening that names the successor's target)*
> **If one side is rigid the general-position half disappears.** When `δ₂ = 0`,
> (ii) gives `ρ₂ = 0`, so `dim(ρ̄₁ + ρ̄₂) = ρ₁` while
> `min(δ₁ + δ₂, 6) = min(δ₁, 6) = δ₁` (as `δ₁ ≤ 6` by (BE-21)(ii)); the criterion
> (iii) collapses to the **single condition `ρ₁ = δ₁`** — *the flexible side's
> welded framework attains* — with **no general-position content whatsoever**. By
> (BE-20) every 3-connected side is rigid, so this is the ordinary case in a
> 3-block decomposition, and it is the honest first target: **the successor lemma
> is a statement about ONE piece and its welding, not about two pieces in
> relative position.**
>
> Measured (`binduc.py ear`, 55 s, exact ℚ): **296 ear additions** — a path with
> `m = 1…4` interior vertices attached at *every* vertex pair of each of `K₄`,
> `K₅`, `prism`, `K_{3,3}`, `cube` — with the fibre-product identity (i)
> **asserted at every one**. **240 attain**; the **56** that do not are all
> `cube` with `m ∈ {3,4}`, and their diagnostics confirm the criterion in the
> *negative* direction with the cause localized to one number: **both pieces
> attain, `δ₁ = 0` and `ρ₁ = 0` on the rigid side, but `ρ₂ = 3` against
> `δ₂ ∈ {4,5}`** — the ear's welded framework (a cycle `C_{m+1}`) fails to attain
> at the *flat* configuration, which is exactly the flat witness's own known
> defect (`def₂(C₄) = 1`, `def₂(C₅) = 2`). **All 56 have hub load `4`**, so the
> construction ladder is infeasible there and falls back to flat; they are
> **"not found under this constructor", never "does not exist"** (`rank ≤ target`
> is universal, so a measured rank is a *lower* bound on the stratum maximum).
> So the 296 instances confirm (iii) as a **biconditional**: 240 positive with
> `dim(ρ̄₁+ρ̄₂)` maximal, 56 negative with it short by exactly the shortfall of
> `ρ₂`.

**Machine validation** (`binduc.py rank2`, 2.7 s). Seven 2-cut splits, each at
both the flat and the best ladder configuration, all exact ℚ: **the fibre-product
law (i) holds identically at every one of the 12 configurations**, `ρ_i` respects
(ii) at every one, and the criterion (iii) is confirmed in both directions.
Three rows worth quoting, because they show the criterion **decomposing a
failure**:

| split | `δ₁, δ₂` | config | rank / target | `dim M` decomposition | `ρ₁, ρ₂` | `dim(ρ̄₁+ρ̄₂)` / max |
|---|---|---|---|---|---|---|
| `θ(4,4,4)` at `{u,v}` | `4, 2` | flat | `54 / 60` | `12 = 10 + 11 − 6 − 3` | `3, 3` | `3 / 6` |
| `θ(4,4,4)` at `{u,v}` | `4, 2` | hub-plane | **`60 / 60`** | `6 = 10 + 8 − 6 − 6` | `4, 2` | `6 / 6` |
| `C₁₀` at antipodes | `5, 5` | generic | **`50 / 50`** | `10 = 11 + 11 − 6 − 6` | `5, 5` | `6 / 6` |

The `θ(4,4,4)` flat row is the diagnostic: its miss of `6` is **exactly**
`3` (side 2's welded framework fails: `dim M₂ = 11` against `8`) plus `3` (general
position fails: `3` against `6`) — the two mechanisms of (iii)(a) and (iii)(b),
separated and measured. `C₁₀` is the case where `δ₁ + δ₂ = 10 > 6`, so the
criterion asks for the **full** screw space and gets it.

**Why the route is by connectivity and not by the landed KT reduction moves —
the spec's TRAP, re-read in the source.** `Graph.minimal_kdof_reduction`
(`Molecular/Induction/ForestSurgery/Reduction.lean:673`) does have premises
`hbase` / `hsplit` / `hcontract`, and its conclusion is
`∀ G, G.IsMinimalKDof n 0 → 2 ≤ V(G).ncard → P G` — **so it cannot reach
(BE-14)'s `∀ G` at all**, confirmed off the signature. On the `hcontract`
comparison the spec's reading needs **one correction**: the principle's premise
is
`∀ G, G.IsMinimalKDof n 0 → 3 ≤ ncard → (∃ H, H.IsProperRigidSubgraph G n) →
(∀ G', G'.IsMinimalKDof n 0 → 2 ≤ ncard → ncard < → P G') → P G`, whereas the
phase's carried item (`Molecule/Pencil/Escape.lean:451`) is
`∀ G, G.Loopless → 3 ≤ ncard → (∃ H, …) → (∀ G', V(G').Nonempty → ncard < → PencilPair K 3 G') → PencilPair K 3 G`.
These are the **same obligation shape with `P := PencilPair K 3`, not
byte-for-byte**: the phase's version quantifies over *loopless* graphs (strictly
more) and hands a *weaker* IH (strictly harder). Instantiating the principle
would therefore hand back not the parked `hcontract` itself but a **sibling of
it** over `IsMinimalKDof n 0` — a new obligation of the same kind. **The trap
conclusion stands, and this is a refinement of it, not a dissent:** scaffolding
(BE-14) there re-imports a contraction-closure premise, which is exactly what
(BE-14) is valuable for avoiding. Recorded as a finding per the spec, not acted
on.

### Step BE22 — the induction assembled, a named construction, and the generalized forcing mechanism

> **(BE-23)** *(the reduction; proven modulo the single named lemma)* Induct on
> `|V|`. A connected `G` falls into one of:
> **(a) 3-connected** — attains by (BE-20), and *rigidly*, so it also satisfies
> the strengthened statement of (BE-22)(iii) trivially;
> **(b) max degree `≤ 2`** — attains at generic points, with the landed
> Phases-24–26 dictionary available by (BE-20)(iii);
> **(c) `def₂ = def₃`** — attains at the flat witness by (BE-20)(ii);
> **(d) a cut vertex** — composes by (BE-18);
> **(e) 2-connected with a 2-cut** — composes **iff** (BE-22)(iii) can be met.
> Since a graph on `≥ 4` vertices that is not 3-connected has a separator of size
> `≤ 2`, (a)–(e) are exhaustive. **So (BE-14) is equivalent to the strengthened
> 2-cut composition lemma (e)**, everything else being in hand.

> **(BE-23)(i)** *(a named construction; 5 824 measured theorems)* The
> **hub-plane construction**: choose a plane `π_v` per hub and solve, per vertex
> `w`, the system `{p_w ∈ π_v : v a hub of closedNbhd(w)}`. With **generic**
> planes it is feasible exactly when the **hub load** `h(G) ≤ 3` (four generic
> planes have no common point), and its refinement gives one plane per **forced
> hub class** (hubs `u,v` with `|closedNbhd(u) ∩ closedNbhd(v)| ≥ 3` share a
> plane), degenerating to the flat witness when one class holds every hub.
>
> Measured (`binduc.py hubplane`, 256 s, exact ℚ): **5 824 connected graphs with
> `h(G) ≤ 3` — EXHAUSTIVE at `n = 4, 5, 6` (31 / 312 / 4 881) plus 150 sampled at
> each of `n = 7, 8, 9, 10` — ATTAIN the target, with ZERO failures**, and
> **2 441 of them have `def₂ > def₃`**, i.e. the flat witness provably misses
> there by `def₂ − def₃ > 0`. Since `rank ≤ target` is universal, **each
> attaining draw is a proof for that graph**, so this is 5 824 theorems, not a
> statistic. On the named battery: `θ(3,3,3) 42/42` (flat `39`),
> `θ(4,4,4) 60/60` (flat `54`), `θ(4,5,6) 75/75` (flat `69`), `C₆ 30/30`,
> `C₈ 40/40`, and — via the **class** refinement — `necklace(3) 66/66` and
> `necklace(4) 90/90`, which reproduces BATTAIN's `localcone` attainment by a
> systematic construction rather than a per-family derivation.
>
> **The honest limit, stated as a limit.** At hub load `≥ 4` the construction is
> infeasible with generic planes, and that is where `DZ` (`h = 4`, best ladder
> rank `103 / 114`) and `spider(5,5,5)+c` (`h = 4`, `81 / 90`) sit. Their
> attainment is BATTAIN's recorded `sample_Y` / `localcone` result (`DZ 114/114`,
> **cited, not re-run**), and what that sampler supplies is exactly what the
> generic-plane construction lacks: a **concurrency structure** on the hub planes.
> Systematizing it — one plane per **3-block**, cut pairs pinned to plane
> intersection lines — is the named next slice.

> **(BE-23)(ii)** *(the new-cap mechanism: it exists, it is strictly more
> general, and it fires empty — MEASURED, not proved)* BZAVOID's (BE-15)
> propagation forces `π_u = π_v` along **triangle** edges. The general rule is
> *"`π_v` is forced to `π` once `closedNbhd(v)` holds three independent points of
> `π`"*, and it fires **without any triangle**: at a `K_{2,3}` (two vertices with
> three common neighbours), and in chains — **`K_{3,3}` is forced FLAT and is
> triangle-free** (checked in the driver: forced flat `True`, has a triangle
> `False`). So the mechanism BZAVOID killed is a *special case*, and the
> generalization is a genuine candidate for the new universal cap the spec's HIT
> shape 3 asks about.
>
> **It fires empty as well.** Hunted with the *aggressive* combinatorial closure
> (which assumes every three forced points independent, so it **over**-claims
> forcing and an empty result under it is the stronger statement):
> **EXHAUSTIVE over 27 470 connected graphs at `n ≤ 6` (20 963 forced flat) plus
> 4 800 sampled at `n = 7…10` (4 307 forced flat) — ZERO with `def₂ > def₃`.**
> The largest `def₂` observed at a forced-flat graph is **5**, so — with
> BZAVOID's `def₂ ≥ def₃` — the measured statement is the strictly stronger
> **"forced flat ⇒ `def₂ = def₃`"**, not "⇒ `def₂ = 0`" as the triangle case
> gave. Where the flat witness is forced, it therefore **attains**, and the
> mechanism is harmless.
>
> **The structural reason, which is (BE-20) again, and it is a sketch not a
> proof.** `def₂ > def₃` forces a cut of size `≤ 2`; across a 2-cut `{u,v}` a
> vertex `z` on one side has `closedNbhd(z) ∩ (other side) ⊆ {u,v}` — **two**
> points, never three — so propagation can only cross through `closedNbhd(u) ∪
> closedNbhd(v)` and must re-accumulate three independent points locally on the
> far side to continue. That is a real barrier but **not** an impossibility (a
> tight far side can re-accumulate), which is exactly why (BE-23)(ii) is
> recorded as measured rather than proved.

### Step BE23 — verdict, classification, and the price

**Which HIT shape this is: shape 1, advanced on all three of the spec's jobs;
shape 3 answered and reported as a candidate that fires empty; shape 2 NOT
reached.**

**Job 1 (the 2-cut composition).** `def₃` half: **the asserted law is REFUTED and
replaced by a proved exact law** ((BE-21)). Rank half: **not routine** — reduced
to a precisely stated criterion with its free sub-case proved and its obstruction
dimension-counted ((BE-22)). The spec's instruction *"do not inherit the `− 6`"*
was correct: the `−6` is the worst case of the correction `min(δ₁+δ₂,6)`, and the
`GL₄`-flag warning is confirmed and quantified (residual gauge group dimension 7
adjacent / 5 non-adjacent, against a Grassmannian of dimension up to 9).

**Job 2 (the base class).** **Free** ((BE-20)): 3-connectivity forces
`def₂ = 0`, the flat witness attains in closed form, and the declined
`def₂ = def₃` slice — legitimate as a base case by the spec's own authorization —
covers the base exactly. The hub-free base is covered too, and by the *landed*
apparatus ((BE-20)(iii)).

**Job 3 (where it obstructs).** The induction obstructs at **exactly one place**:
the 2-connected-with-a-2-cut step when some `δ_i > 0`, canonically an **ear
addition** (a path with `m` interior vertices has `δ = min(m+1, 6)`). Whether
that failure suggests a new universal cap: **a candidate mechanism does exist and
is strictly more general than the one BZAVOID killed, and it fires EMPTY under an
exhaustive aggressive hunt** ((BE-23)(ii)). Reported as a candidate, **never as a
refutation**.

**Classification, mandatory and explicit — (BE-24).** **Nothing is refuted.** Not
`PencilPair K 3 G`; not `hbareSplit`; not (BE-14)-for-all-`G`. What *is* refuted
is **one asserted claim of BZAVOID's own** ((BE-18)'s 2-cut `−6`, its disclosed
cap 8) and **no route**. Two routes are *revived in restricted form*: (BE-17)'s
`G²` dictionary on the hub-free class, and the `def₂ = def₃` slice as the base
case. **Not a PENCIL event.**

**The price, re-quoted against BZAVOID's.**

- **(BE-14) got substantially cheaper, and for the first time the reduction is to
  a single lemma.** After BZAVOID the problem was "construct one coplanar-star
  configuration per 2-connected graph". Now: base free, 1-cuts done, 2-cuts
  reduced to a criterion in the 6-dimensional screw space with the free case
  proved. The remaining lemma is *small enough to state in one sentence*, which
  none of its predecessors was.
- **What it will cost.** The strengthened statement has to carry welded
  attainment at every cut pair — a statement about *contracted multigraphs*, so
  the induction's motive changes shape (this is the *flag, don't force* item: it
  is a motive-level change and it is named, not smuggled). And the general-position
  half needs the piece's own moduli, not the gauge group.
- **The `∃`-seed + repair alternative is unchanged.** §(K-tight) *Step 5*'s
  chartless wall is untouched; this direction did not go near it.
- **What a successor should attack, in this pass's ranking.** (1) **The
  strengthened 2-cut lemma against a RIGID side**, which by (BE-22)(vi) is the
  single condition *"the flexible side's welded framework attains"* — one piece,
  no general position, and by (BE-20) every 3-connected side is rigid. The 56
  `cube + ear` rows say exactly what has to be built: a configuration at which
  the ear's welded cycle attains, which the flat witness cannot supply and the
  generic-plane ladder cannot reach at hub load `4`. (2) **The 3-block plane construction**: one plane per
  3-block, cut pairs pinned to plane intersection lines — the systematic form of
  BATTAIN's `localcone`, which would lift (BE-23)(i) past hub load 3 and cover
  `DZ`. (3) **A proof of (BE-23)(ii)** (forced flat ⇒ `def₂ = def₃`), which would
  close the disproof side of (BE-14) the way (BE-15)(ii) closed the triangle case.

### Verification

`python3 notes/scripts/w4/binduc.py base` (433 s — the exhaustive `n ≤ 7`
3-connected sweep, 226 891 graphs, plus the `n = 8, 9, 10` samples and the
exhaustive contrapositive census); `flatwit` (1.3 s — 15 shapes, 4 seeded draws
each); `gate` (0.1 s); `twocut` (3.3 s — 10 804 gluings against the independent
set-partition oracle); `rank2` (2.7 s — 7 splits × 2 configurations, exact ℚ); `ear` (55 s — 296 ear
additions to five 3-connected bases, the fibre law asserted at every one);
`hubplane` (256 s — the battery, the class ladder, and the 5 824-graph sweep);
`force` (228 s — 27 470 exhaustive + 4 800 sampled). `validate` runs reduced
tiers of all eight in **~2 min** (it skips `base`'s `n = 7` tier and `hubplane`'s
sweep; run those modes separately for the full figures).

**F25 bar, read off the shipped driver.** Eight modes, one per headline sentence;
every "always"/"never"/"every" sentence backed by an **enumerating** tier
((BE-20)(i) exhaustive to `n = 7`; (BE-21) exhaustive over all pieces on
`n ≤ 5`; (BE-23)(i) and (ii) exhaustive to `n = 6`); **two independent
deficiency oracles cross-checked at every enumerated entry** of `twocut` (the
`2^{|V|}`-part-sum oracle `exact_deficiency` against a from-scratch
set-partition oracle `def_by_partitions`); every rng seeded with a printed
literal; every sampled configuration passing `assert_generic_star` (adjacent
points distinct **and** no two hinge lines at a body coincide — the
`plane_basis`-class guard of README §4, here a collinearity assert on every
path of length 2) **and** `kbare_common.verify_pencil_witness`; and a
rank/dimension assert on every solved linear system and every kernel
(`motion_space` asserts `dim ker = 6|V| − rank`). **All figures exact ℚ**; no
GF(p) anywhere, deliberately, since two of the three claim types here are
shortfall claims. **No scratchpad probe backs any claim in this section.**

### Caps, disclosed rather than smoothed

1. **(BE-20)(ii) inherits (BE-13)'s *proven-informally* status.** The flat rank
   law is the projective dual of BATTAIN's cone law and rests on the same
   imported **planar body-pin rank formula**; it is *measured* exactly at 14
   shapes here but not proved in this pass. **(BE-20)(i) does NOT inherit it** —
   it is elementary and self-contained.
2. **The duality step is stated, not proved.** That the point-side flat
   configuration and the panel-side cone have the *same* rank is asserted from
   the landed self-duality (BE-16)(ii) /
   `hasPencilPanelRealization_mapExtensor_screwComplementIso`; what this pass
   *measures* is the point-side law directly, so nothing downstream depends on
   the duality argument.
3. **`base`'s exhaustive tier stops at `n = 7`** (`2^{21}` edge sets); `n = 8, 9,
   10` are 400 sampled 3-connected graphs each. The general claim rests on the
   **proof**. The `2^n` boundary sweep ran on all of `n ≤ 6` and every 200th
   graph at `n = 7` (2 920 in total), the rest of `n = 7` being covered by the
   `def₂`/`def₃` asserts only.
4. **`twocut`'s enumeration uses pieces on `≤ 5` vertices** and subsamples the
   piece-pair product to 30 000/9 cells per tier; the law itself is **proved both
   directions**, so the enumeration is corroboration. Observed `δ` reached only
   `4` of the proved range `[0,6]`.
5. **(BE-22)(v) is a dimension count, not an obstruction proof.** It shows
   general position is *not free from the gauge group*; it does **not** show it
   fails. The piece's own moduli are not counted here at all, and they are the
   likely source. This is the (K-tight)-style honest gap, named.
6. **(BE-23)(i)'s 5 824 attainments are per-graph theorems, not a class
   theorem.** Each is exact and decisive *for that graph* (one attaining draw
   suffices, since `rank ≤ target` is universal), but "the hub-plane construction
   attains whenever `h(G) ≤ 3`" is **measured, not proved** — 5 824 instances,
   zero failures, and the tiers at `n ≥ 7` are samples of 150.
7. **The hub-plane construction is one seeded family.** Its planes are drawn
   generically from a bounded integer box; a graph whose attainment needs
   *non-generic* planes reports INFEASIBLE rather than a shortfall, and two such
   are in the battery (`DZ`, `spider(5,5,5)+c`) with their attainment supplied by
   BATTAIN's recorded certificates instead.
8. **(BE-23)(ii)'s closure is combinatorial and AGGRESSIVE.** It assumes every
   three forced points independent, so it over-claims forcing. That makes the
   empty hunt *stronger* evidence for "no new cap", but it also means the set it
   calls "forced flat" is an **over**-estimate; a conservative closure would be
   smaller. The exhaustive tier stops at `n = 6`, `n = 7…10` being 1 200 samples
   each. **The statement is MEASURED, not proved** — the structural sketch given
   is not a proof.
9. **The strengthened statement is named but not verified as a whole.** (BE-22)
   shows what the induction must carry; that a configuration exists satisfying
   attainment *and* welded attainment at **every** cut pair simultaneously is
   measured only at the seven `rank2` splits. **DISCHARGED 2026-08-26 (BTWOCUT,
   (BE-25)(i)): the worry is VACUOUS.** Every quantity in play is the rank of a
   matrix polynomial in the configuration, hence lower semicontinuous, hence
   maximal on a dense open subset of an irreducible component; a **finite
   intersection of dense opens is dense open**, so at the generic point all are
   simultaneously maximal. The induction never has to argue that two good
   configurations can be chosen at once — only whether the maxima **equal** the
   combinatorial caps, which is where the whole difficulty actually lives.
10. **The 56 `ear` misses are constructor caps, not shortfall claims about the
    stratum.** They are reported as *"not found under the ladder"*; the ladder's
    planes are generic, and at hub load `4` a *concurrent* plane arrangement is
    required and not attempted. Read as attainment failures they would be a
    misreading of exactly the kind F27 warns about. **CONFIRMED AND CLEARED
    2026-08-26 (BTWOCUT, (BE-26)): the cap was right — all 56 were a
    `flat_config` artifact** (it flattens the ear's *pencil-unconstrained
    interior*, capping `ρ ≤ dim Λ²π = 3`), and under the `hubflat` rung the
    concurrent-plane arrangement this cap names as "not attempted" **296/296 now
    attain**. Exemplar `cube+ear(m=4)`: flat gives `64/66` with `ρ₂ = 3 < δ₂ = 5`,
    hubflat gives **`66/66`, `ρ₂ = 5 = δ₂`**. The fix is the **ear's own moduli**;
    the general-position half was never involved.
11. **No `.lean`** — the standing 2026-08-05 Lean hold. Every Lean citation here
    is a *read* of a landed body (`Graph.partitionDef`, `Graph.deficiency`,
    `bodyBarDim`, `SimpleGraph.IsGeneralPositionPlacement`,
    `Graph.minimal_kdof_reduction`,
    `pencil_conjecture_of_hcontract_hK_hbareSplit`), never an edit.

### Harness note — the `kbare/` sibling-import set gains its THIRD `w4/` consumer

`notes/scripts/README.md` *Harness debt* → *the `kbare/` sibling imports;
**UNPAID***. BATTAIN was the first `w4/` consumer, `bzavoid` the second;
`binduc.py` is the **third**, and it is also the **first external consumer of any
`bzavoid` device**. **No move made** (a dispatch may not edit a landed driver
another direction may be importing in flight — ZJACOB ran concurrently).
Recorded consumer list, extended:

| name | current home | consumers |
|---|---|---|
| `dz_gadget` | `danger` | `optc`, `breakhunt`, `w4/battain`, `w4/bzavoid`, **`w4/binduc`** (5) |
| `verts_of`, `exact_deficiency`, `build_rigidity`, `verify_pencil_witness`, `spider` | `kbare_common` | …, `w4/battain`, `w4/bzavoid`, **`w4/binduc`** |
| `def2_exact`, `necklace` | `w4/battain` | `w4/bzavoid`, **`w4/binduc`** (2) |
| `adj_of`, `connected_spanning`, `def3_of`, `edges_of_mask` | `w4/bzavoid` | **`w4/binduc`** (1 — first external consumer of any `bzavoid` device) |

If the eventual move-down happens, `binduc.py` joins the acceptance test
alongside `battain.py` and `bzavoid.py`.

### TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator re-runs it

- **(E1) NO.** No `g`-flank. This direction is on **(K-bare)**, not the §(K-grid)
  ledger; it computes deficiencies, connectivity and ranks of the pencil /
  molecular rigidity matrix, and touches no colouring, matching, or `d_adm`
  object. Clauses (i)–(v) have nothing to fire on.
- **(E2) NO.** One landed claim is **refuted** — BZAVOID's asserted 2-cut `−6`,
  which was disclosed as its own cap 8 (*"asserted as 'looks routine', not proved
  or measured"*) — and it is refuted **with its successor in hand** ((BE-21)),
  which is the shape E2 explicitly does not fire on. No ledger entry is refuted
  or shown unprovable-as-posed; `hbareSplit` is unchanged and (BE-14) is
  unchanged in status.
- **(E3) ARMED by GBAL, DOES NOT FIRE, and this direction does not fire it.** E3
  fires only on a HIT completing **entry 1 / (a′)**; this pass is on (K-bare) and
  does not touch (a′).

### Confidence verdict

- **(BE-20)(i) — 3-connected ⇒ `def₂ = def₃ = 0`: PROVEN.** Elementary and
  self-contained (no import from (BE-13) or (BE-15)), enumerated at 226 891
  3-connected graphs with zero exceptions, and the bound shown tight
  (`partitionDef₂ = −3` at the worst `q ≥ 2` partition).
- **(BE-20)(ii) — the flat rank law and the 3-connected base: PROVEN-INFORMALLY**,
  inheriting (BE-13)'s imported planar body-pin formula, and **MEASURED exactly**
  at 14 shapes including `DZ` (`103 = 114 − 11`).
- **(BE-20)(iii) — the gate is satisfiable exactly on the hub-free class:
  PROVEN** (read off the Lean body; the pencil condition is vacuous at max degree
  `≤ 2` and negates the gate at every hub), measured at 4 + 2 shapes.
- **(BE-21)(i) — BZAVOID's 2-cut `−6`: REFUTED.** Explicit witness, exact.
- **(BE-21)(ii) — the exact 2-cut `def₃` law: PROVEN**, both directions, plus
  `δ ∈ [0,6]`; enumerated at 10 804 gluings against an independent oracle.
- **(BE-22)(i)–(iv) — the fibre-product law, `ρ_i ≤ δ_i`, the attainment
  criterion, the free sub-case: PROVEN.** Elementary linear algebra, verified
  identically at 12 exact-ℚ configurations.
- **(BE-22)(vi) — one rigid side kills the general-position half: PROVEN**
  (one line from (iii) and `δ ≤ 6`), and the criterion confirmed as a
  **biconditional** at 296 ear additions (240 positive, 56 negative with the
  cause localized to `ρ₂ < δ₂`).
- **(BE-22)(v) — the alignment/general-position obstruction: a DIMENSION COUNT,
  not a proof of failure.** The transitivity claims (regimes α, β) are proven;
  the "not free" conclusion is a count, and the piece's moduli are uncounted.
- **(BE-23) — the reduction of (BE-14) to the single 2-cut lemma: PROVEN modulo
  (BE-20)(ii)'s informal ingredient and (BE-18).**
- **(BE-23)(i) — the hub-plane construction: 5 824 PER-GRAPH THEOREMS** (each
  exact and decisive), **the class-level statement MEASURED not proved**, and the
  hub-load-`≥ 4` limit disclosed.
- **(BE-23)(ii) — the generalized forcing mechanism fires empty: MEASURED**
  (25 270 forced-flat instances, zero candidates), with a structural sketch and
  **not** a proof. Strictly generalizes (BE-15)'s triangle rule, whose closure
  *is* proved.
- **(BE-14): OPEN**, unchanged in status, now with a free base and a single named
  residual lemma. **`hbareSplit`: OPEN and unchanged, carried as pinned.** **Not
  a PENCIL event.**

**What would change this.** For **(BE-20)(i)**, a 3-connected graph with a proper
nonempty vertex subset of edge-boundary `≤ 2` — impossible by the proof, and
226 891 exhaustive checks agree. For **(BE-20)(ii)**, an error in the duality
step or in the imported planar body-pin formula, which is where (BE-13)'s
informal ingredient lives; a *direct* proof of the flat law on the point side
would remove the dependence entirely and is a small, self-contained target. For
**(BE-21)**, nothing: it is proved both directions and enumerated. For
**(BE-22)(iii)**, a 2-cut composition that attains with `dim(ρ̄₁+ρ̄₂)` *below*
`min(δ₁+δ₂,6)` — impossible by the identity, so the only thing that can change is
whether the criterion is *achievable*, which is the open lemma. For
**(BE-23)(i)**, a graph with `h(G) ≤ 3` at which the hub-plane construction
**misses** — the one measured class-level claim, and the first thing a successor
should re-run with more seeds and larger `n`. For **(BE-23)(ii)**, a forced-flat
graph with `def₂ > def₃`; that would be a **new universal-cap mechanism** and the
first live disproof route since (BE-15) closed the triangle one, so it is the
highest-value single search on the board — 25 270 instances say no.
