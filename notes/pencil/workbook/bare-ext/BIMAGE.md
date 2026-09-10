## §(K-bare-ext) — continuation (direction BIMAGE): the image is **BOUNDED and CLASSIFIED** — the ear's `ρ̄₂` is the span of a **chain on the Klein quadric**, its bad locus is **exactly three trapping mechanisms**, every one of them is a **configuration artifact at 607/607 escalated instances**, and job 2's candidate bound is **REFUTED as an equality** by the series/parallel recursion that replaces it

Direction **BIMAGE** (`notes/Pencil-fanout.md` §"BIMAGE", ordinal 45), the arc's
fifty-third and the **second** consecutive whose selection was forced: BTWOCUT
reduced the strengthened 2-cut composition lemma — hence (BE-14) — to one
geometric sentence, *the image of a piece's realization space in `Gr(δ₂,6)` is
not contained in `ρ̄₁`'s bad locus*, and ranked the **ear** case first. Read
against *Steps BE24–BE28* (BTWOCUT), *Steps BE19–BE23* (BINDUC), *Steps
BE14–BE18* (BZAVOID) and *Steps BE9–BE13* (BATTAIN), whose figures are **cited,
never re-run**. Driver `notes/scripts/w4/bimage.py`
(`chain|sprec|combi|alpha|badA|image|hunt|probe|validate`), importing `btwocut`
and `binduc` **read-only**; all exact ℚ, every rng seeded and printed.

**Status, stated before the mathematics.**

- **BTWOCUT's *"nothing in the arc bounds that image"* is now FALSE, and this is
  the direction's headline.** For an ear the image is described **exactly**:
  `ρ̄₂ = ⟨ℓ₁,…,ℓ_{m+1}⟩` with equality (a path is a tree), and the **achievable
  tuples are exactly the chains** `ℓ₁ ∈ Π_u`, `ℓ_{m+1} ∈ Π_v`, consecutive
  members **conjugate on the Klein quadric** — a *bijection* with a classical
  object, not an inclusion. **(BE-30)**.
- **The coordinator's Klein-chain hypothesis: CONFIRMED as stated, with one
  correction it does not predict.** `Π_v = p_v ∧ π_v` is indeed a 2-dimensional
  **totally singular** space — a line **ruled** on the quadric — and consecutive
  conjugacy is the only constraint *for `m ≥ 3`*. What the hypothesis misses is
  that at small `m` the two ends **interact**: three exact **confinement laws**,
  one of which (`π_u = π_v`, `m = 2`) collapses the image to a **single point of
  `Gr(3,6)`**. Its own cheapest consequence (`δ₂ ≤` shortest-path length) is
  **proved**, not just confirmed. **(BE-30)(ii)–(iv)**.
- **Job 2 answered, and the coordinator's candidate bound REFUTED as an
  equality.** `ρ̄` obeys an exact **series/parallel recursion** — series
  **sums**, parallel **intersects** — verified as an identity of *subspaces*.
  The intersection-over-`u–v`-paths bound is a genuine **upper bound** and is
  **strictly larger** at an exhibited witness (`2` against `1`). So a hinge-line
  description exists for **every series-parallel piece**, down its SPQR tree,
  and the residue is exactly the **R-node**. **(BE-31)**.
- **Three elementary combinatorial theorems kill the two sharpest confinement
  obstructions before any geometry**, and one of them is the arc's cheapest
  falsification test: `u ~ v ⇒ δ_{uv} ≤ 1`; **`u,v` on a common triangle
  `⇒ δ_{uv} = 0`**; `u,v` with `≥ 3` common neighbours `⇒ δ_{uv} = 0`. All by
  one partition-merging inequality. Plus the **necessary condition
  `δ_{uv} ≤ dist(u,v)`** for the strengthened statement — purely combinatorial,
  no configuration — swept over **542 893** `(graph, pair)` instances
  (**exhaustive** `n ≤ 6`: 27 474 graphs / 408 080 pairs) with **zero**
  violations. **(BE-32)**.
- **The bad locus, classified exactly — three trapping mechanisms and no
  others.** Pencil swallowing (`Π_u ≤ A` or `Π_v ≤ A`), confinement
  (`dim(A ∩ Z) + c₂ > dim Z` for the confining space `Z`), and, at `m = 1`, the
  **opposite ruling** of the quadric surface the image sweeps. Each is a
  **proved lower bound** on the loss; that the loss is **exactly** their maximum
  is **MEASURED at 358/358** over a structured-plus-random battery, with **zero
  disagreements**. **(BE-33)**.
- **Every trap a real piece exhibits is a CONFIGURATION ARTIFACT.** Over a
  census, **934** `(piece, m)` pairs are predicted trapped at the drawn
  configuration; **682** have `π_u = π_v` **chosen by the constructor** and not
  forced, **230** have it aggressively forced, **22** have `π_u ≠ π_v`. Rebuilt
  as composed graphs and re-measured with side 1 free to move as well:
  **607 / 607 reach the criterion AND the whole-graph target rank.** And the
  battery of 43 real `G₁ ∪ ear(m)` instances reaches
  `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6)` **by moving the ear alone**, at `δ₁` up to `6`.
  **(BE-34)**.
- **Verdict: (BE-14) OPEN and unchanged in status. Nothing is refuted except one
  coordinator-offered candidate bound (job 2's path intersection) and BTWOCUT's
  own *"nothing bounds that image"*, both with successors in hand.** `PencilPair
  K 3 G`, `hbareSplit` and (BE-14)-for-all-`G` are untouched. **Not a PENCIL
  event.** **(BE-34)(iv)**.

### Standing notation

Inherited from *Steps BE9–BE28* verbatim (`f := def₃`, `g_{uv}`,
`δ_{uv} := f − g_{uv} ∈ [0,6]`, `ρ̄_{uv}`, `ρ_{uv}`, hub, hub load, free vertex,
flat / hubflat / bundle configuration, `Π_v := p_v ∧ π_v`, `M(F)`). Added here:

- **the Klein form** `⟨x,y⟩ := x ∧ y ∈ Λ⁴K⁴ ≅ K` on `Λ²K⁴ ≅ K⁶`. In the
  harness's Plücker order `(01,02,03,12,13,23)` it is
  `⟨x,y⟩ = x₀y₅+x₅y₀ − x₁y₄−x₄y₁ + x₂y₃+x₃y₂`. A bivector is a **line** of `P³`
  iff `⟨x,x⟩ = 0` (the **Klein quadric**), and two lines **meet** iff their
  Plücker points are **conjugate**. `B^{⊥K}` is the Klein-orthogonal complement.
- **`S_p := p ∧ K⁴`**, the 3-dimensional **α-plane**: the lines *through* `p`.
- **`Λ²π`**, the 3-dimensional space of lines *inside* the plane `π`.
  `Π_v = S_{p_v} ∩ Λ²π_v` is 2-dimensional and **totally singular**; the pencils
  are exactly the lines **ruled** on the Klein quadric, and
  `Π_v^{⊥K} = S_{p_v} + Λ²π_v` is 4-dimensional.
- **`M := p_u ∨ p_v`** and, when `π_u ≠ π_v`, **`L := π_u ∩ π_v`**; and
  **`E := Π_u + Π_v`**, which is `M ∧ L` (4-dimensional) when `uv ∉ E(G)`, and
  3-dimensional when `uv ∈ E(G)` (there `Π_u ∩ Π_v = ⟨p_u ∧ p_v⟩`).
- **the confining space `Z`**: `Z := E` when `π_u ≠ π_v`, `Z := Λ²π` when
  `π_u = π_v`; and **`c₂ := dim(ρ̄₂ ∩ Z)`**, which is `2` in every case except
  `π_u = π_v` with `m = 2`, where it is `3`.

**Carrier check, done off the landed bodies rather than the prose.** No new Lean
object is read beyond the four BINDUC read (`Graph.partitionDef`,
`Graph.deficiency`, `bodyBarDim`, `SimpleGraph.IsGeneralPositionPlacement`); the
screw-space convention used throughout is read off
`kbare_common.build_rigidity`, whose row block for an edge is
`perp_basis(wedge2(hat p_u, hat p_w))` — i.e. the constraint is literally
`m_u − m_w ∈ K·ℓ_{uw}`, which is what makes every identity below elementary.
**No `.lean` was opened for edit; the standing 2026-08-05 Lean hold binds.**

### Step BE29 — the ear's image, exactly: a chain on the Klein quadric, and three confinement laws

> **(BE-30)(i)** *(proven; elementary, and verified as an identity of
> subspaces)* For an ear `u = w₀, w₁, …, w_m, w_{m+1} = v` with every interior
> vertex of degree 2,
>
> **`ρ̄₂ = ⟨ℓ₁, …, ℓ_{m+1}⟩`, with EQUALITY**, where `ℓ_i = p_{w_{i−1}} ∧ p_{w_i}`.
>
> *Proof.* `⊆`: `m(v) − m(u) = Σ_i (m(w_i) − m(w_{i−1}))` and each summand lies
> in `K·ℓ_i`. `⊇`: a path is a **tree**, so the `m+1` edge multipliers are
> unconstrained — given any `(λ_i)` set `m(w_j) := Σ_{i ≤ j} λ_i ℓ_i`, which is
> a motion. ∎
>
> This is the identity BTWOCUT's *Step BE28* successor ranking item (1) records;
> it is **cited there and proved here**, and checked against binduc's own
> `rel_screw_space` at **44 / 44** draws (`m = 1 … 11`, four seeded draws each),
> as an identity of *subspaces*, not of dimensions.

> **(BE-30)(ii)** *(proven; the achievable set, both directions — this is the
> coordinator's hypothesis, TESTED)* Fix the shared flags. The tuples
> `(ℓ₁,…,ℓ_{m+1})` arising from legal ear configurations are **exactly** the
> tuples with
>
> - every `ℓ_i` on the **Klein quadric** (a line of `P³`),
> - `ℓ_i` and `ℓ_{i+1}` **conjugate** (they meet), consecutive ones distinct,
> - `ℓ₁ ∈ Π_u` and `ℓ_{m+1} ∈ Π_v`, the two ends ranging over **lines ruled on
>   the quadric**,
>
> and **nothing further** for `m ≥ 3`.
>
> *Proof.* Forward: `ℓ_i, ℓ_{i+1}` share `p_{w_i}`; the pencil condition at `u`
> puts `closedNbhd(u)` in `π_u`, so `ℓ₁` passes through `p_u` inside `π_u`, i.e.
> `ℓ₁ ∈ Π_u`; likewise at `v`; a degree-2 vertex imposes no condition of its own
> (three points are always coplanar), so `w₂,…,w_{m−1}` are **free vertices** in
> btwocut's sense. Converse: given such a chain set `p_{w_i} := ℓ_i ∩ ℓ_{i+1}`;
> then `p_{w_1} ∈ ℓ₁ ⊆ π_u` and `p_{w_m} ∈ ℓ_{m+1} ⊆ π_v`, so the point
> configuration is legal. ∎
>
> **VERDICT ON THE COORDINATOR'S HYPOTHESIS: CONFIRMED as stated**, and it is a
> *bijection*, which is more than it claimed. Measured: `Π_u, Π_v` totally
> singular in all three flag regimes; every `ℓ_i` on the quadric; consecutive
> pairings `0`; **all** non-consecutive pairings nonzero at a generic draw
> (`3/3`, `6/6`, `10/10` at `m = 3,4,5`).

> **(BE-30)(iii)** *(proven; THE CORRECTION the hypothesis does not predict —
> three CONFINEMENT laws)* The ends do **not** stay free at small `m`:
>
> **(a) `m = 1`.** The one interior vertex is adjacent to **both** ends, so
> `p_{w_1} ∈ π_u ∩ π_v = L` and `ρ̄₂ = p_{w_1} ∧ M ⊆ Π_u + Π_v = E`, a **fixed
> 4-dimensional subspace**, at every configuration. Moreover the decomposable
> elements of `E = M ∧ L` form a **smooth quadric surface**, and the image is
> **exactly one of its two rulings**, `{x ∧ M : x ∈ L}` — a `P¹`, of dimension
> `1` inside a `Gr(2,6)` of dimension `8`.
>
> **(b) `π_u = π_v = π` and `m ≤ 2`.** Then every point of the ear lies in `π`,
> so `ρ̄₂ ⊆ Λ²π` (3-dimensional); and at `m = 2` the three lines are
> independent, so **`ρ̄₂ = Λ²π` exactly — the image is a SINGLE POINT of
> `Gr(3,6)` and the ear has no freedom at all.**
>
> **(c) `uv ∈ E(G)` with `π_u ≠ π_v` and `m = 1` is FORCED DEGENERATE.** Both
> planes contain `M`, so `π_u ∩ π_v = M`, so `p_{w_1} ∈ M`, so `p_u, p_{w_1},
> p_v` are collinear and the two hinge lines **coincide** — the gate
> `assert_generic_star` fails. Hence a length-2 ear on an **adjacent** pair
> **forces `π_u = π_v`**: this is BZAVOID's (BE-15) triangle propagation,
> re-derived from the ear side, and it is why (a) and (b) do not overlap.
>
> Measured: the `m = 1` union of drawn `ρ̄₂` spans **exactly `Π_u + Π_v`** (dim
> 4) and no more; with `π_u = π_v` it spans **3**; at `m = 2` with `π_u = π_v`
> the union of forty draws still spans **3**; at `m ≥ 3` the union spans **6**
> in every regime. In regime (c) every one of thirty draws fails
> `legal_chain`.

> **(BE-30)(iv)** *(proven; the hypothesis's own cheapest consequence, which the
> spec named as the first falsification to run)* For **every** `u–v` path `P` of
> a piece `H`, `ρ̄_{uv}(H) ⊆ ⟨ℓ_e : e ∈ P⟩` (the telescoping of (i)); hence
>
> **`ρ_{uv}(H) ≤ dist_H(u,v)` unconditionally**,
>
> and, at a configuration where `H` **and** `H/uv` attain (so `ρ = δ` by
> (BE-22)(ii)), **`δ_{uv} ≤ dist_H(u,v)`**. On the ear itself this is **tight**
> for `m ≤ 5` (`δ₂ = min(m+1,6) = dist`), so the hypothesis's consequence is not
> merely true but sharp. Its contrapositive is the falsification test of
> (BE-32)(iv).

### Step BE30 — what `ρ̄` is for a piece that is NOT an ear: the series/parallel recursion, and the refutation of the candidate bound

> **(BE-31)(i)** *(proven; two identities of SUBSPACES)* Let `H = H₁ ∪ H₂`.
>
> **SERIES** (`H₁ ∩ H₂ = {z}`, `u ∈ H₁`, `v ∈ H₂`):
> **`ρ̄_{u,v}(H) = ρ̄_{u,z}(H₁) + ρ̄_{z,v}(H₂)`**.
> *Proof.* `⊆` by telescoping through `z`. `⊇`: given `m₁ ∈ M(H₁)` and
> `m₂ ∈ M(H₂)`, translate `m₂` by the constant `m₁(z) − m₂(z)`; the two agree at
> the only shared vertex, so they glue to a motion of `H`, whose relative screw
> is the sum. ∎
>
> **PARALLEL** (`H₁ ∩ H₂ = {u,v}`):
> **`ρ̄_{u,v}(H) = ρ̄_{u,v}(H₁) ∩ ρ̄_{u,v}(H₂)`**.
> *Proof.* `⊆` is restriction. `⊇`: given `s` in both, pick `m_i ∈ M(H_i)` with
> `m_i(v) − m_i(u) = s`, translate `m₂` so that `m₂(u) = m₁(u)`; then
> `m₂(v) = m₂(u) + s = m₁(v)`, so they agree on `{u,v}` and glue. ∎
>
> Verified as identities of subspaces at **12 / 12** seeded draws, zero
> exceptions.

> **(BE-31)(ii)** *(the answer to job 2, POSITIVE with a named limit)* Iterating
> (i) down a **series-parallel decomposition** computes `ρ̄_{u,v}` for every
> series-parallel piece from its hinge lines alone: `S`-node **sums**, `P`-node
> **intersects**, the leaf is a single edge with `ρ̄ = ⟨ℓ_e⟩`. The ear is the
> all-`S` case, which is why it was the tractable one. What has **no** such
> description is the **R-node** — a 3-connected block with its virtual edges
> replaced by children. **LANDED 2026-09-01 as (BE-59)/(BE-60), direction
> BRNODE: the description exists — the decorated-skeleton law extends the
> recursion over the whole SPQR tree, the R-node case a kernel computation
> rather than a lattice expression.**
>
> **Exactly how far (BE-25)(iii) reaches, corrected by the coordinator at
> landing.** It closes the **LEAF** R-node only — BTWOCUT's own consequence line
> reads *"every SPQR **leaf** 3-block is rigid"* — where the piece **is** the
> 3-connected skeleton minus its parent virtual edge, hence rigid, hence
> `dim M = 6` and `ρ̄ = 0`, and the recursion terminates. An **INTERNAL** R-node,
> with flexible children substituted for its virtual edges, is **not** covered
> and is **not** rigid: `K₄` with one virtual edge replaced by an ear is exactly
> BINDUC's `K₄ + ear(m)`, with `δ ∈ {4,5}`. **So the residue is the INTERNAL
> R-node**, which is this direction's own ranked successor (3) — the draft's
> first wording said (BE-25)(iii) made the residue small, which reads as closing
> what successor (3) is queued to open.

> **(BE-31)(iii)** *(the coordinator's candidate bound, REFUTED as an equality —
> with a witness)* The spec's *"obvious candidate upper bound is the
> intersection over `u–v` paths of the path spans"* is a genuine **upper bound**
> (immediate from (BE-30)(iv)) but **NOT an equality**. At `G₂ = θ(3,3)` with a
> pendant edge (`P, Q` two 3-edge `u–x` paths, `R` the edge `xv`):
>
> `ρ̄ = (ρ̄_P ∩ ρ̄_Q) + ρ̄_R` has dimension **1**, while
> `(ρ̄_P + ρ̄_R) ∩ (ρ̄_Q + ρ̄_R)` has dimension **2**.
>
> The gap is structural, not accidental: intersection does not distribute over
> sum. **So the SP recursion REPLACES the candidate, rather than refining it.**

### Step BE31 — the combinatorial half: three elementary theorems, and the arc's cheapest falsification test

Everything in this step is about `δ_{uv} = def₃(H) − def₃(H/uv)` **alone** — no
configuration, no genericity, no constructor. One inequality does all the work.

> **THE MERGE INEQUALITY.** Let `P` attain `f = def₃(H)` with
> `value(P) = 6(q−1) − 5d(P)`. Merging `k+1` of its parts into one gives a
> partition of value `f − 6k + 5c`, where `c` is the number of edges running
> between distinct merged parts. If the merge puts `u` and `v` together its
> value is `≤ g_{uv} ≤ f`, so **`5c ≤ 6k`**.

> **(BE-32)(i)** *(proven)* **`u ~ v ⇒ δ_{uv} ≤ 1`.** If some optimal `P`
> separates `u ∈ A` from `v ∈ B`, merging `A, B` gives `k = 1`, hence `c ≤ 1`;
> and `c ≥ 1` because `uv` is an edge, so `c = 1` and `g ≥ f − 1`. (If no
> optimal partition separates them, `g = f` and `δ = 0`.) ∎

> **(BE-32)(ii)** *(proven)* **`u, v` on a common triangle `uvz` `⇒ δ_{uv} = 0`.**
> Suppose an optimal `P` separates `u ∈ A`, `v ∈ B`. By (i), `c = 1`. If `z ∈ A`
> then `zv` also crosses `A–B`, so `c ≥ 2`; likewise if `z ∈ B`. So `z` lies in
> a third part `C` — and then merging `A, B, C` has `k = 2` and `c ≥ 3` (all
> three triangle edges), giving value `≥ f + 3 > f`, against `≤ g ≤ f`. So **no**
> optimal partition separates `u` and `v`, i.e. `g = f`. ∎

> **(BE-32)(iii)** *(proven)* **`u, v` with `≥ 3` common neighbours
> `⇒ δ_{uv} = 0`.** By the same count: at most one common neighbour can lie in
> `A ∪ B` (a second forces `c ≥ 2`), so two of them, `y, z`, lie outside. If they
> lie in one part `C`, merging `A,B,C` has `k = 2, c ≥ 4`, value `≥ f + 8`; if in
> two, merging four parts has `k = 3, c ≥ 4`, value `≥ f + 2`. Both contradict
> `≤ f`. ∎
>
> **What (ii) and (iii) buy, and it is the reason they are here.** They are
> exactly the two mechanisms that **force `π_u = π_v`** — BZAVOID's (BE-15)
> triangle propagation and BINDUC's (BE-23)(ii) `K_{2,3}` generalization — so
> **wherever the sharpest confinement law (BE-30)(iii)(b) is forced by one of
> the two known forcing mechanisms inside a piece, that piece has `δ = 0` and
> (BE-22)(vi) makes the composition free.** The obstruction and the deficiency
> are in tension, which is the same shape (BE-15) found on the disproof side.

> **(BE-32)(iv)** *(the arc's cheapest falsification test, swept)* By (BE-30)(iv),
> **`δ_{uv} ≤ dist_H(u,v)` is NECESSARY** for the strengthened statement at
> `{u,v}` — so a single `(H,u,v)` with `δ > dist` would refute **S-all** and
> **S-mark** outright, with no geometry and no configuration.
>
> Measured (`bimage.py combi`, 33 s, exact): **EXHAUSTIVE over every connected
> labelled graph on `n = 3 … 6` — 27 474 graphs, 408 080 `(graph, pair)`
> instances — plus 3 000 seeded masks at each of `n = 7, 8`, for 32 958 graphs
> and 542 893 instances in total**:
>
> | claim | instances of the hypothesis | violations |
> |---|---|---|
> | (i) `u ~ v ⇒ δ ≤ 1` | 287 570 adjacent pairs | **0** |
> | (ii) triangle `⇒ δ = 0` | 208 095 triangle pairs | **0** |
> | (iii) `≥3` common nbrs `⇒ δ = 0` | 44 542 pairs | **0** |
> | (iv) `δ ≤ dist` | **542 893** pairs | **0** |
> | (+) aggressively forced `π_u = π_v ⇒ δ = 0` | 208 418 pairs | **0** |
>
> Row (+) is **measured, not proved**, and its predicate is the **aggressive**
> plane-class closure (it assumes every three forced points independent, so it
> **over**-claims forcing) — which is the direction that makes an empty sweep
> the **stronger** statement: every genuinely forced pair is among the 208 418.

### Step BE32 — the bad locus, classified: three trapping mechanisms and no others

Fix the shared flags. The ear's own moduli — `p_1 ∈ π_u`, `p_2,…,p_{m−1}` free
in `P³`, `p_m ∈ π_v` — form an **irreducible** rational parameter space, and
`dim(A + ρ̄₂)` is the rank of a matrix polynomial in those parameters, hence
**lower semicontinuous**. So its maximum is attained on a dense open subset and
**one draw reaching it settles that `(A, m)` outright** ((BE-25)(i)'s mechanism,
applied on the ear's own parameter space).

> **(BE-33)(i)** *(proven; the α-plane escape lemma, and it is what makes the
> chain greedy run)* For a subspace `B ⊊ Λ²K⁴`,
>
> **`Bad(B) := {p ∈ P³ : S_p ⊆ B} = {p : B^{⊥K} ⊆ S_p}`**,
>
> which is **empty or a single point when `dim B ≤ 4`**, and empty, a point, or
> **exactly the point set of the line `ℓ_ξ`** when `dim B = 5` with
> `B^{⊥K} = ⟨ξ⟩` and `ξ` decomposable.
>
> *Proof.* `S_p ⊆ B ⟺ ∀ξ ∈ B^{⊥K}: p ∧ x ∧ ξ = 0 (∀x) ⟺ p ∧ ξ = 0 ⟺ ξ ∈ p ∧ K⁴
> = S_p`. For `p ≠ q`, `S_p ∩ S_q = ⟨p ∧ q⟩` is 1-dimensional, so a `B^{⊥K}` of
> dimension `≥ 2` lies in at most one `S_p`; and `dim B ≤ 4` forces
> `dim B^{⊥K} ≥ 2`. ∎
>
> Measured: the identity holds at **5 000 / 5 000** `(B,p)` draws over
> `dim B = 1…5`, with **0 of 25** random `p` bad at every dimension; and in the
> one extremal shape `B = ℓ^{⊥K}` **every** sampled point of `ℓ` is bad
> (`12/12`) — the single case where `Bad(B)` is a whole line.
>
> **Consequence (the greedy).** At every interior vertex of the ear there is a
> line through the current point escaping the space built so far, and a point on
> that line whose own α-plane escapes the enlarged space (choose
> `ℓ ∈ S_p ∖ (B ∪ B^{⊥K})`, which exists because a 3-dimensional space over an
> infinite field is not a union of two proper subspaces). **What this does NOT
> close is the last step**, where `p_m` must satisfy *two* conditions inside the
> 2-parameter plane `π_v` (`ℓ_m ∉ W_{m−1}` **and** `ℓ_{m+1} ∉ W_m`) — see the
> caps.

> **(BE-33)(ii)** *(the classification: three mechanisms, each a PROVEN lower
> bound on the loss)* Write `d₁ = dim A`, `d₂ = min(m+1,6)`, and
> `loss := min over configurations of dim(A ∩ ρ̄₂)`. Then
> `max dim(A + ρ̄₂) = min(6, d₁ + d₂ − loss)`, and
>
> **(P) PENCIL SWALLOWING.** `ℓ₁` ranges over `Π_u` and `ℓ_{m+1}` over `Π_v`, so
> each pencil that `A` contains **outright** costs exactly one dimension:
> `loss ≥ #{Π ∈ {Π_u, Π_v} : Π ⊆ A}`.
>
> **(Z) CONFINEMENT.** The two **end** lines always lie in `Z`, so
> `dim(ρ̄₂ ∩ Z) ≥ c₂` and therefore
> `loss ≥ max(0, dim(A ∩ Z) + c₂ − dim Z)` — with `c₂ = 3` in the one case
> `π_u = π_v, m = 2` (where `ρ̄₂ = Λ²π` outright) and `c₂ = 2` otherwise.
>
> **(R) THE OPPOSITE RULING** (`m = 1` only). The image is one ruling of the
> quadric surface in `E`; a line of the **opposite** ruling — i.e. `y ∧ L` for
> some `y` on `M = p_u ∨ p_v` — meets **every** member, so `loss ≥ 1`. (`y = p_u`
> recovers `Π_u`, `y = p_v` recovers `Π_v`: (P) is the special case of (R) at the
> two distinguished points of `M`.)
>
> **Each of (P), (Z), (R) is PROVEN as a lower bound. That the loss is EXACTLY
> `max(P, Z, R)` is MEASURED**, not proved: `bimage.py badA` compares the
> predicted reach against the measured maximum over 45 seeded ear draws at every
> `(regime, A, m)` of a battery of structured subspaces (`A ⊇ Π_u`, `A ⊇ Π_v`,
> `A ⊇ y∧L`, `A ⊆ Z`, `A ⊆ Λ²π`, at every dimension) **and** random `A` of every
> dimension `0…6`, in all three flag regimes — **358 / 358 agree, zero
> disagreements**.
>
> **Read this the right way.** A row the classification marks *trapped* is **not
> a counterexample to (BE-14)**: it is a subspace of the screw space, exhibited
> by hand, at which the **ear alone** cannot reach the criterion. Whether any of
> them is the `ρ̄₁` of an actual piece is a different question — (BE-34).
>
> **Bar respected (ZJACOB (JC-6)).** Nothing in this step derives properness,
> generic smoothness or transversality from a codimension count, a Jacobian
> criterion or Cohen–Macaulayness. There is **no dimension count** here at all:
> (P), (Z) and (R) are containments of explicit subspaces, and the exactness
> claim is measured against per-configuration exact-ℚ ranks.

### Step BE33 — the image at real graphs, the hunt, and the escalation

> **(BE-34)(i)** *(measured; the headline sentence tested directly)* For a
> battery of **43** real composed graphs `G = G₁ ∪ ear(m)` — `K₄`, prism,
> `K_{3,3}`, cube, `θ(a,a,a)`, `C₈`, a two-private-hub side, and **both sides
> ears** (a cycle, the only family in which `δ₁` grows with the piece) — build
> one legal whole-graph pencil configuration, then **freeze side 1 and the
> shared flags** and vary **only** the ear's own moduli:
>
> **43 / 43 reach `dim(ρ̄₁ + ρ̄₂) = min(δ₁+δ₂, 6)` by moving the EAR ALONE**, and
> **43 / 43 reach the whole-graph target rank `6(|V|−1) − def₃(G)`**, with `δ₁`
> ranging over `0 … 6` and `m` over `1 … 5`, in both flag regimes. Each such row
> is a **theorem for that graph** (`rank ≤ target` is universal).

> **(BE-34)(ii)** *(the hunt: does a real `ρ̄₁` ever satisfy the bad
> predicate?)* Over **420** instances subsampled from btwocut's 12 203-instance
> both-`δ`-positive census (exhaustive `n = 5,6` with max degree `≤ 4`, plus
> 1 500 seeded masks at `n = 7`), one ladder configuration each, both pieces
> read off: **840** `(piece, flag)` subspaces, **768** of them attaining with
> `ρ₁ < 6` (the only ones at which the question has content). Against the
> (BE-33)(ii) predicate at `m = 1…5`:
>
> - **934** trapped `(piece, m)` pairs, of which
> - **682** have `π_u = π_v` **in the drawn configuration but NOT forced by the
>   graph** — a **constructor artifact**, the same shape as BINDUC's 56 ear
>   misses ((BE-26));
> - **230** have `π_u = π_v` **aggressively forced**;
> - **22** have `π_u ≠ π_v` — the genuinely geometric family, and every one of
>   them is the (Z) mechanism with `ρ̄₁` (3-dimensional) sitting **inside**
>   `E = Π_u + Π_v`.
> - **0** hits on the `m = 1` opposite-ruling predicate anywhere.

> **(BE-34)(iii)** *(F27 escalation: every trap is a CONFIGURATION ARTIFACT)* A
> trapped row is a statement about **one drawn configuration of side 1**, and the
> composition is free to move side 1 too. So each trapped row was **rebuilt as a
> composed graph** `G' = (side 1) ∪ ear(m)` and measured outright under the full
> BTWOCUT ladder plus the ear's moduli, multi-seeded:
>
> **607 / 607 distinct `(side 1, m)` trapped rows REACH the criterion AND the
> whole-graph target rank**, under 2 independent ladder seeds × 16 ear draws
> each. **Zero residual candidates.**
>
> So the answer to the direction's question, as far as it is measured, is: **the
> ear image escapes `ρ̄₁`'s bad locus at every instance tested, and every
> apparent trap dissolves once side 1 is allowed to move.** This is **MEASURED**;
> the class-level statement has no argument, and saying otherwise would be the
> overclaim the spec's bars single out.

### Verdict, classification, and the price

**Which HIT shape this is.** **NOT shape 1** — (BE-14) is not proved. **NOT
shape 2 in full** — the ear case is *reduced*, not *proved*: the reach formula's
lower bounds are proved and its exactness is measured, and "no real piece
produces a bad `ρ̄₁`" is measured, not argued. **NOT shape 3** — the hunt fires
empty after escalation. **What is delivered sits strictly between shapes 2 and
4**, and the honest name for it is: *the image is now bounded and classified,
and the ear case is reduced from an unbounded geometric question to one explicit
non-containment condition on `ρ̄₁` relative to the shared flags.*

**Job 1 (the ear case).** The image is described **exactly** ((BE-30)), its bad
locus is **classified into three mechanisms** ((BE-33)), each mechanism is a
proved lower bound, the two sharpest are **killed combinatorially** wherever
they are forced ((BE-32)(ii)/(iii)), and the residue is measured empty
((BE-34)). What is **not** proved: that the reach equals the classification's
prediction (the greedy's last step), and that no piece realizes a bad `ρ̄₁`.

**Job 2 (`ρ̄` off the ear).** **Answered positively with a named limit**: the
series/parallel recursion computes `ρ̄` from hinge lines for every
series-parallel piece, down the SPQR tree; the coordinator's candidate
intersection bound is **refuted as an equality** with a witness; the residue is
the **INTERNAL R-node** — (BE-25)(iii) closes the **leaf** R-node only (`ρ̄ = 0`
there, recursion terminates), and an internal one is not rigid at all
(`K₄ + ear(m)`). Corrected by the coordinator at landing; see (BE-31)(ii).

**Job 3 (BTWOCUT's successor (2), the bundle construction).** **SKIPPED
EXPLICITLY**, exactly as the spec authorizes: job 1 did not close early, and job
2 grew into a proof rather than a note.

**Classification, mandatory and explicit — (BE-34)(iv).** **Nothing is
refuted.** Not `PencilPair K 3 G`; not `hbareSplit`; not (BE-14)-for-all-`G`.
What **is** refuted is **one coordinator-offered candidate** (job 2's
path-intersection bound, as an *equality*) and **one standing sentence of
BTWOCUT's own** (*"nothing in the arc bounds that image"* — the ear's image is
now bounded exactly). **No route is closed. No route is opened.** **Not a PENCIL
event.**

**HIT shape 4's assessment.** The connectivity induction is **still the right
frame**, and the ear case has moved from *"a geometric statement nothing
bounds"* to *"a finite, explicitly classified non-containment condition"*. The
`∃`-seed + repair alternative is **unchanged**: §(K-tight) *Step 5*'s chartless
wall is untouched and nothing here went near it.

**The price, re-quoted against BTWOCUT's.**

- **(BE-14) got cheaper in a new currency: the residue is now NAMED rather than
  unbounded.** BTWOCUT reduced it to one sentence and said nothing bounds the
  image; this pass bounds the image exactly for the ear and names the three ways
  it can fail.
- **What it will cost.** Two things, both small enough to state. **(α)** Close
  the greedy's last step — the simultaneous choice of `p_m ∈ π_v` making both
  `ℓ_m` and `ℓ_{m+1}` escape — which would turn the reach formula from measured
  to proved. **(β)** Prove that no piece satisfying the strengthened statement
  has `Π_u ⊆ ρ̄₁` (or the (Z)/(R) variants) at **every** configuration with the
  given flags. (β) is the whole remaining content of the ear case and it is a
  statement about **one** piece, not two.
- **What a successor should attack, in this pass's ranking.**
  **(1)** **(β) above** — *a piece satisfying the strengthened statement admits a
  configuration with `Π_u ⊄ ρ̄₁` and `Π_v ⊄ ρ̄₁` and `dim(ρ̄₁ ∩ Z) ≤ dim Z − c₂`* —
  which, with (α), **proves the ear case outright**.
  > **CORRECTED 2026-08-27 by BEARCASE (BE-36), and left in place because it
  > propagated:** the third clause as written is **UNSATISFIABLE for `δ₁ ≥ 5`** —
  > `dim(ρ̄₁ ∩ Z) ≥ δ₁ + dim Z − 6` always, and `dim Z` cancels. **The correct
  > target is `loss ≤ slack = max(0, δ₁ + δ₂ − 6)`**, which is what the landed
  > `bimage.py hunt` already tests; (β)'s `loss = 0` is its `δ₁ + δ₂ ≤ 6` case.
  > **No measurement changes** — the defect was in the prose that travelled with
  > them, and it reached this direction's spec and the phase note's hand-off
  > before a one-line Grassmann check caught it. The SP recursion (BE-31) is
  the tool: for a series-parallel piece `ρ̄₁` is computed from its own hinge
  lines, so the condition becomes a statement about sums and intersections of
  chain spans.
  **(2)** **(α)**, the greedy's last step — self-contained projective geometry,
  no graph theory, and the smallest item in the arc's queue.
  **(3)** The **R-node** case of (BE-31)(ii): what `ρ̄` is for a 3-connected block
  with flexible children. This is the step from *ear* to *general piece*.
  **(4)** BTWOCUT's successor (2), the bundle-construction proof — unchanged in
  value, **skipped here**.

### Verification

`python3 notes/scripts/w4/bimage.py chain` (1.4 s — the chain identity at 44
draws, the Klein dictionary in all three flag regimes, the three confinement
laws with their unions measured, and `δ₂ ≤ dist` on the ear); `sprec` (0.6 s —
the two SP identities as subspace identities, plus the path-intersection
witness); `combi` (33 s — exhaustive `n = 3…6` plus sampled `n = 7,8`, 542 893
`(graph, pair)` instances, five predicates); `alpha` (2.8 s — the α-plane
identity at 5 000 draws plus the extremal `B = ℓ^{⊥K}` case); `badA` (8.5 s —
the classification against a structured-plus-random battery in three regimes,
358 comparisons); `image` (159 s — 43 real composed graphs, side 1 frozen);
`hunt` (20 s — 420 census instances, 840 `ρ̄₁` subspaces, the predicate);
`probe` (282 s — the hunt plus the F27 escalation of all 607 distinct trapped
rows). `validate` runs reduced tiers of all eight in **~125 s**.

**F25 bar, read off the shipped driver.** Nine modes, one per headline sentence;
every *"every" / "always" / "exactly"* sentence backed by an **enumerating**
tier ((BE-32) exhaustive to `n = 6` over all connected labelled graphs;
(BE-33)(ii) over the full structured battery × every dimension × three regimes ×
`m = 1…5`; (BE-34)(iii) over **all** 607 distinct trapped rows, not a sample of
them). Every subspace claim is an identity of **spaces** (`same_space`,
`contains`), never of dimensions; `isect` **asserts** the dimension formula on
every call; every rng is seeded with a printed literal; every sampled
configuration passes binduc's `assert_generic_star` **and**
`kbare_common.verify_pencil_witness`; every whole-graph rank is asserted `≤`
target. **All figures exact ℚ**; no GF(p) and no floating point anywhere. **No
scratchpad probe backs any claim in this section** — the exploratory scripts
that preceded the driver were discarded and every figure above is a shipped
driver mode.

### Caps, disclosed rather than smoothed

1. **The ear case is NOT proved.** (BE-33)(ii)'s three mechanisms are proved as
   **lower bounds** on the loss; the claim that the loss is **exactly** their
   maximum is **measured at 358/358** and has no argument. This is the headline
   cap and everything else is subordinate to it.
2. **The greedy's last step is open.** (BE-33)(i) closes every interior step of
   the chain; the final choice of `p_m ∈ π_v` must satisfy **two** conditions in
   a **2**-parameter family and is not shown to be satisfiable in general. A
   bad case is characterizable (it forces `⟨x,y⟩ ∧ (p_v + λ p_{m−1}) ⊆ W_{m−1}`
   for some `λ`), and it is **not** ruled out here.
3. **"No real piece produces a bad `ρ̄₁`" is MEASURED, over configurations the
   BTWOCUT ladder produces**, not over every configuration of every piece. The
   hunt is one ladder draw per instance; the escalation is 2 seeds × 16 ear
   draws per row.
4. **The census is subsampled twice.** btwocut's census is exhaustive only at
   `n = 5, 6` with max degree `≤ 4` and sampled at `n = 7`; this direction
   subsamples **420** of its 12 203 instances (seed printed). The escalation
   covers **all** 607 distinct trapped rows *of that subsample*, not of the
   census.
5. **(BE-32)(iv)'s sweep is exhaustive to `n = 6` and SAMPLED at `n = 7, 8`.**
   It reports *"no `(H,u,v)` with `δ > dist` found under the cap"*, **never**
   *"none exists"*.
6. **(BE-32)(+) is measured and uses the AGGRESSIVE closure**, which over-claims
   forcing. That direction makes an empty sweep the stronger statement, but the
   row is still **not** a theorem.
7. **(BE-30)(ii)'s converse assumes consecutive lines distinct.** A chain with
   `ℓ_i = ℓ_{i+1}` does not determine `p_{w_i}`, and such configurations are
   excluded by the gate rather than handled.
8. **The `image` battery is 43 hand-chosen instances**, not a census; its value
   is that it reaches `δ₁ = 6` and both flag regimes, which the census's
   `max degree ≤ 4` tier does not.
9. **`m = 1` in the adjacent regime is excluded, not handled.** (BE-30)(iii)(c)
   shows it is forced degenerate; the `adj` battery therefore runs `m ≥ 2` only.
10. **No `.lean`** — the standing 2026-08-05 Lean hold. No Lean file was opened
    for edit and no Lean body was read that BTWOCUT had not already read.

### Harness note — the `kbare/` sibling-import set gains its FIFTH `w4/` consumer

`notes/scripts/README.md` *Harness debt* → *the `kbare/` sibling imports;
**UNPAID***. BATTAIN was the first `w4/` consumer, `bzavoid` the second,
`binduc` the third, `btwocut` the fourth; `bimage.py` is the **fifth**, and the
chain is now **five deep** (`battain → bzavoid → binduc → btwocut → bimage`).
**No move made** (a dispatch may not edit a landed driver another direction may
be importing in flight). Recorded consumer list, to be extended by the
coordinator at landing:

| name | current home | consumers |
|---|---|---|
| `exactcore.{rank,nullspace,hat,wedge2,neighbors}` | `notes/scripts/` | + `w4/bimage.py` |
| `kbare_common.{verts_of,build_rigidity,exact_deficiency,verify_pencil_witness}` | `notes/scripts/kbare/` | + `w4/bimage.py` |
| `bzavoid.{adj_of,connected_spanning,edges_of_mask}` | `w4/` | + `w4/bimage.py` (**third external consumer**) |
| `binduc.{assert_generic_star,cycle,def_by_partitions,ear,hubs_of,motion_space,path,rel_screw_space,split_at_pair,theta}` | `w4/` | + `w4/bimage.py` (**second external consumer**) |
| `btwocut.{deltas_at,delta_all_pairs,extended_construction,g_exact,split_battery,two_cut_census}` | `w4/` | `w4/bimage.py` (**FIRST external consumer of any `btwocut` device**) |

### Confidence verdicts, per claim

- **(BE-30)(i) (`ρ̄₂` is the chain span): PROVEN** — two lines from the tree
  structure of a path; confirmed as a subspace identity at 44 draws.
- **(BE-30)(ii) (the achievable set = chains; the coordinator's hypothesis):
  PROVEN as a bijection**, both directions, with the distinctness caveat of cap
  7. The hypothesis is **CONFIRMED**, not merely un-refuted.
- **(BE-30)(iii) (the three confinement laws): PROVEN**, each from the pencil
  condition alone; measured exactly (unions spanning 4 / 3 / 3 / 6).
- **(BE-30)(iv) (`ρ ≤ dist`): PROVEN** — telescoping. The `δ ≤ dist` corollary
  is **conditional on welded attainment**, which is what makes it a necessary
  condition rather than a theorem about `δ`.
- **(BE-31)(i) (series/parallel): PROVEN** — elementary gluing; verified as
  subspace identities at 12 draws.
- **(BE-31)(ii) (the SP description of `ρ̄`): PROVEN for series-parallel pieces**
  by iterating (i); **the R-node case is OPEN and named**.
- **(BE-31)(iii) (the path-intersection bound is not an equality): PROVEN by a
  witness** — one exact-ℚ instance suffices to refute an equality.
- **(BE-32)(i)/(ii)/(iii): PROVEN** — one merge inequality each, self-contained;
  confirmed exhaustively at 287 570 / 208 095 / 44 542 instances.
- **(BE-32)(iv) (`δ ≤ dist`): MEASURED, empty at 542 893 instances**, exhaustive
  to `n = 6`. It is a **necessary condition** for S-all/S-mark, so an empty sweep
  is corroboration of the strengthened statement, never a proof of it.
- **(BE-32)(+) (forced `π_u = π_v ⇒ δ = 0`): MEASURED** under the aggressive
  closure, 208 418 instances, zero exceptions. No argument is offered.
- **(BE-33)(i) (the α-plane escape lemma): PROVEN** — three lines from the Klein
  form; verified at 5 000 draws plus the extremal case.
- **(BE-33)(ii) (the classification): the three LOWER BOUNDS are PROVEN; the
  EXACTNESS is MEASURED**, 358/358, zero disagreements. The distinction is the
  cap 1 above and must travel with the figure.
- **(BE-34)(i): 43 per-graph theorems** — each attaining draw settles its graph.
- **(BE-34)(ii)/(iii): MEASURED**, and the escalation's **607/607** is the
  load-bearing figure. The class-level statement *"the ear image always escapes"*
  is a **candidate**, never a refutation of anything and never a proof.
- **(BE-34)(iv) (classification): PROVEN** — nothing refuted but one coordinator
  candidate and one sentence of BTWOCUT's, both with successors in hand.

### What would change this

For **(BE-30)**, a legal ear configuration whose hinge lines are not a chain —
excluded by the pencil condition, which is read off the landed
`build_rigidity`/`verify_pencil_witness` pair rather than from prose. For
**(BE-31)**, a series-parallel piece where the recursion disagrees with a
directly measured `ρ̄` — swept and not found. For **(BE-32)**, an error in the
merge inequality, which is four lines and independently swept at half a million
instances. For **(BE-33)**, an `(A, m)` where the measured reach **exceeds** the
classification's prediction (which would mean a mechanism is not a bound — none
found) or falls **below** it (which would mean a **fourth** trapping mechanism —
none found in 358 comparisons, and this is the one a successor should re-run
first). For **(BE-34)**, a `(G₁, u, v, m)` at which the composed graph resists a
genuinely exhaustive search over the pencil stratum rather than over a
constructor family — which would be the first real candidate for a new universal
cap since (BE-23)(ii), and would have to be classified against it.

### TERMINATION riders

**E1: NO.** **E2: NO** — one coordinator-offered candidate is refuted (job 2's
path-intersection bound *as an equality*) and one landed sentence corrected
(BTWOCUT's *"nothing bounds that image"*), but **both with their successors in
hand** (the SP recursion; the exact classification), which is the shape E2
explicitly does not fire on. **E3: ARMED by GBAL, not fired.**
