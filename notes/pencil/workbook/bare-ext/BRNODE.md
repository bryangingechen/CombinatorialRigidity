## §(K-bare-ext) — continuation (direction BRNODE): the INTERNAL R-NODE IS DESCRIBED — `ρ̄` at every 2-connected piece is computed by ONE law over the SPQR tree, because a child's whole boundary trace is a function of its `ρ̄` alone (the **decorated-skeleton law**), so job 1's sharp question comes back **YES**; the (BE-22)(vi) collapse at an R-node peel is an exact **checkable condition on `B`** that `K₄` passes at the opposite edge and the **prism fails at two rungs** — the both-flexible case is nonempty already at ONE flexible child; and the routing verdict is that the description was never what the consumer was short of — the residue is the **achievable-decorations** class statement, the (BE-30)(ii)-analogue

Direction **BRNODE** (`notes/pencil/fanout.md` §"BRNODE", ordinal 52), the arc's
sixtieth, at **(BE-31)(ii)'s named residue** — the internal R-node, the step
from *ear* to *general piece*, **user-selected 2026-08-29** and confirmed on the
critical path by (BE-43)(v). Read against *Steps BE29–BE33* (BIMAGE, the SP
recursion), *Steps BE24–BE28* (BTWOCUT, the S-mark frame), *Steps BE19–BE23*
(BINDUC, (BE-22)) and *Steps BE53–BE57* (BWIN, the opaque-subspace precedent),
whose figures are **cited, never re-run**. Driver `notes/scripts/w4/brnode.py`
(`law|rec|carve [named|full]|route|validate`), importing `bwin` / `bsharp` /
`bimage` / `binduc` **read-only**, and through them the rest of the chain; all
exact ℚ, every rng seeded from the printed literal `20260901`, every drawn
configuration through `assert_generic_star` **and**
`kbare_common.verify_pencil_witness`.

**WHICH DELIVERABLE THIS IS — said at the top, as the spec demands.** Job 1's
sharp sub-question (*is `ρ̄` at an R-node a function of the children's `ρ̄` at
all?*) is answered **YES, by a proof**, and the answer is constructive: **HIT
shape 1** — the SP recursion is **extended to a complete recursion over the
SPQR tree** ((BE-59)/(BE-60)), with the R-node case a *kernel computation*
rather than a lattice expression. Job 2's routing verdict is the direction's
second deliverable (**HIT shape 3**): the description is **cheap** — one
elementary lemma — and what (BE-22)(iii) is short of at the R-node is located
**elsewhere**, in the class-level achievable-decorations statement ((BE-62)).
The carve-out comes back as the spec expected, **negative with an exact
boundary** ((BE-61)): no peel order always keeps one side collapsible, and the
controlling quantity is a checkable function of `B`.

**Status, stated before the mathematics.**

- **JOB 1's SHARP QUESTION: YES, PROVED — and the proof is one lemma.** The
  full boundary trace of a connected child `C_e` with terminals `{x, y}` —
  the image of `M(C_e)` at `(x, y)` inside `K⁶ ⊕ K⁶` — is
  **`Δ ⊕ ({0} ⊕ ρ̄_{x,y}(C_e))`**, a function of `ρ̄_e` **alone** ((BE-59)(i),
  extracted from (BE-22)(i)'s own proof, where the space appears as `R_i`).
  Hence `M(H)` restricted to `V(B)` **is** the motion space of the
  **decorated skeleton** — each edge `e` of `B` constrained by
  `m_x − m_y ∈ ρ̄_e` in place of a hinge line — and
  **`ρ̄_{u,v}(H)` is its image at `(u, v)`**, exact at every configuration,
  no genericity ((BE-59)(ii)). HIT shape 4 does **not** fire. Asserted as
  identities of spaces at 36 guarded draws over nine pieces (`K₄`- and
  `K₃,₃`-skeleton, ear/theta/mixed children) plus 6 interior-redraw pairs
  with equal `ρ̄_e` and different geometry. **(BE-59)**.
- **THE RECURSION OVER THE SPQR TREE IS COMPLETE.** Leaf: `ρ̄ = ⟨ℓ_e⟩`;
  `S`-node: **sum**; `P`-node: **intersection**; `R`-node: the **decorated
  kernel** of its 3-connected skeleton. The first three are the decorated
  law at a path, a bundle, and (BE-31)(i)'s two cases; the fourth is new.
  So `ρ̄_{u,v}` for **every** 2-connected piece is computed from its hinge
  lines by one bottom-up pass — (BE-31)(ii)'s residue is **closed as a
  computation**. What the R-node case is *not* is a sum/intersection
  expression in the children's `ρ̄` — the skeleton's own graph structure
  enters through the kernel — which is why the arc's lattice-shaped
  recursion could not see it. **(BE-60)**.
- **THE CARVE-OUT: negative, with an exact boundary.** At the peel of child
  `e`, (BE-22)(vi) collapses the criterion iff a side has `δ = 0`; an ear
  child never does, so the collapse must come from the remainder, and for
  an all-leaf remainder that is **`δ_{xy}(B − uv − e) = 0` — a checkable
  condition on `B` alone**. `K₄` passes it exactly at the edge **disjoint**
  from `uv` (6 of 30 triples — the adjacent-edge triples fail, refining the
  spec's parenthetical) and the **prism fails at two rungs**
  (`δ = 1`), so **a single flexible child already suffices to leave no
  collapse peel**. Enumerated exhaustively: `n = 4, 5, 6` — 1 + 26 + 1 768
  labelled 3-connected skeletons (sum 1 795, **independently reproducing
  btwocut's landed census count**), 198 360 `(B, uv, e)` triples, collapse
  at 20.0 % / 70.9 % / 84.8 %. Constructed both-flexible pieces exist and
  **draw**: `K₄` with three long ears is flexible at the marked pair
  (`dim M = 7`, `ρ̄_{u,v} ≠ 0`) with **every** peel both-sides-flexible.
  **(BE-61)**.
- **JOB 2, THE ROUTING VERDICT: the description was never what the consumer
  is short of — CONFIRMING the coordinator's trace in its central clause,
  with one reframe.** At 24 measured peels over the constructed both-flexible
  R-node pieces the criterion `dim(ρ̄₁ + ρ̄₂) = min(δ₁ + δ₂, 6)` held
  **outright** — welded attainment `ρ_i = δ_i` at every side, general-position
  shortfall `0` at every peel — so at drawn instances there is no (α)- or
  (β)-shaped obstruction to see, exactly as BTWOCUT's 13 484/13 484 sweep
  found from the other side. **The R-node's real content is the CLASS
  quantifier**: which decoration tuples `{ρ̄_e}` are simultaneously
  achievable by pencil configurations — the analogue of (BE-30)(ii)'s
  achievable-set half, which for the ear was a bijection and free. The
  reframe: the peel's failure to reduce to a series-parallel piece is
  **immaterial** — the decorated skeleton is the right object and it is
  bounded. **(BE-62)**.
- **JOB 3: the chord step is the STRICTLY HARDER coordinate for this
  obligation.** Its geometric half fights **upper** semicontinuity
  (specialization points the wrong way, (BE-43)(iii), no landed mechanism);
  the decorated route's residue is attainment statements in the **right**
  direction (exhibit a configuration; (BE-37)(i)(3) makes one exact-ℚ
  witness a proof on the attaining locus) plus one class statement of
  BWIN's opaque-subspace species. **(BE-63)**.
- **Verdict: HIT shapes 1 and 3. Nothing landed is refuted** — one landed
  prose surface is **annotated at source** (F12): (BE-31)(ii)'s *"What has
  no such description is the R-node"*, now closed by this landing.
  `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the 2-cut step,
  S-mark and (BE-32)(+) are untouched; **not a PENCIL event**; the
  phase-boundary consequence is **reported, not acted on**.
- **Reservation FULLY CONSUMED.** Labels **(BE-59)–(BE-63)** and *Steps
  BE58–BE62*; nothing returned.

### Standing notation

Inherited from *Steps BE9–BE57* verbatim (`f := def₃`, `g_{uv}`,
`δ_{uv} := f − g_{uv}`, `ρ̄_{uv}`, `ρ_{uv}`, hub, `Π_v := p_v ∧ π_v`, `M(F)`,
attainment, the S-mark frame of (BE-25)(ii)). Added here:

- an **internal R-node piece**: a 2-connected `H` with marked pair `{u, v}`
  whose SPQR tree (of `H + uv`) has an R-node `B` with `uv ∈ E(B)` virtual
  and at least one other virtual edge carrying a flexible child. In the
  constructions below `B` is a named 3-connected graph, the **parent edge**
  `uv` is deleted, and each remaining edge `e = xy` of `B` carries a
  **child** `C_e`: the edge itself (a **leaf**), an **ear** (path with
  `m ≥ 1` interior vertices), or a **theta**;
- the **decorated skeleton** `(B − uv; {ρ̄_e})`: the linear space
  `M(B; dec) := {m : V(B) → K⁶ : m_x − m_y ∈ ρ̄_e for every child edge e}`,
  and its relative-screw image at `(u, v)`;
- a **peel at `e`**: `H = H'_e ∪ C_e` over `{x, y}`, with
  `H'_e = H − int(C_e)` the remainder (which still contains `B − uv − e`).

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read; the screw-space convention is
`kbare_common.build_rigidity`'s own (`m_x − m_w ∈ K·ℓ_{xw}`, enforced by
`perp_basis` rows), read off the driver chain as in *Steps BE29–BE57* — which
is exactly why the decorated rows below (`perp_std(ρ̄_e)` in place of
`perp_basis(ℓ)`) are the same constraint shape with a subspace in place of a
line. **No `.lean` was opened; the standing 2026-08-05 Lean hold binds.**

### Step BE58 — the boundary-pair lemma and the decorated-skeleton law

> **(BE-59)(i)** *(proven; **THE BOUNDARY-PAIR LEMMA** — extracted from
> (BE-22)(i)'s proof, where the space appears as `R_i`)* Let `C` be a
> connected piece with terminals `x, y`, at any configuration, and let
> `β : M(C) → K⁶ ⊕ K⁶`, `β(m) = (m_x, m_y)`. Then
>
> **`im β = Δ ⊕ ({0} ⊕ ρ̄_{x,y}(C))`, of dimension `6 + ρ_{x,y}(C)`.**
>
> *Proof.* `⊇`: constants give `Δ`; for `r ∈ ρ̄` pick `m` with
> `m_y − m_x = r` and translate by `−m_x`. `⊆`:
> `(m_x, m_y) = (m_x, m_x) + (0, m_y − m_x)`. ∎
>
> So a child's **entire interface** to the rest of any graph it sits in is a
> function of `ρ̄_e` alone — nothing else about its realization can be seen
> across its terminals. Asserted as an identity of subspaces of `K¹²` at
> **every child of every draw** (leaf, ear, theta, nested).

> **(BE-59)(ii)** *(proven; **THE DECORATED-SKELETON LAW**)* Let
> `H = ⋃_e C_e` with the children glued along the edges `e = xy` of a graph
> `B₀` on the shared vertex set `V(B₀)` (children pairwise sharing only
> vertices of `B₀`, interiors disjoint — the SPQR piece shape with
> `B₀ = B − uv`), and let `u, v ∈ V(B₀)`. Then restriction
> `M(H) → M(B₀; {ρ̄_e})` is well defined and **surjective**, and
>
> **`ρ̄_{u,v}(H) = ρ̄_{u,v}(B₀; {ρ̄_e})`** — exact at every configuration.
>
> *Proof.* Well defined: each child's constraint on `(m_x, m_y)` is
> membership of `im β_e`, which by (i) is exactly `m_y − m_x ∈ ρ̄_e`.
> Surjective: given a decorated motion on `V(B₀)`, extend each child
> independently ((i) supplies an interior extension; interiors are
> disjoint). ∎ In particular job 1's sharp question — *is `ρ̄` at an R-node
> a function of the children's `ρ̄` at all?* — is **YES**: `ρ̄_{u,v}(H)` is a
> function of the skeleton configuration on `V(B₀)` and the tuple `{ρ̄_e}`,
> and of nothing else about the children. Asserted as an identity of spaces
> (the decoration recomputed on the child subgraph alone) at every draw of
> every battery piece; the two interior-redraw pair tests (an `ear(5)` child
> at the full-span mechanism, an `ear(2)` child at the flat `Λ²π` mechanism
> of (BE-30)(iii)(b)) exhibit equal `ρ̄_e` with different child geometry and
> `ρ̄(H)` unmoved, 6/6 pairs.

> **(BE-59)(iii)** *(proven; the **dim law** — the many-piece fibre-product
> law, labelled a count)* `ker(restriction) = ⊕_e {m ∈ M(C_e) : m_x = m_y
> = 0}`, of dimension `dim M(C_e) − 6 − dim ρ̄_e` per child by (i), so
>
> **`dim M(H) = dim M(B₀; dec) + Σ_e (dim M(C_e) − 6 − dim ρ̄_e)`.**
>
> The 2-vertex skeleton with two children is exactly (BE-22)(i)
> (`dim M(B₀; dec) = 6 + dim(ρ̄₁ ∩ ρ̄₂)` there). ∎ Asserted at every draw.

### Step BE59 — the recursion over the SPQR tree, complete

> **(BE-60)(i)** *(proven; the uniform law)* Down a rooted SPQR tree, `ρ̄` of
> every node's piece is computed by **one** law — the decorated-skeleton law
> at that node's skeleton:
>
> - **leaf** (`Q`, a real edge): `ρ̄ = ⟨ℓ_e⟩`;
> - **`S`-node** (skeleton a cycle; minus the parent edge, a path): the
>   decorated path gives **`ρ̄ = Σ_e ρ̄_e`** (telescoping; a decorated path
>   is a tree, so the per-edge contributions are free) — (BE-31)(i)'s
>   series law with subspaces in place of lines;
> - **`P`-node** (skeleton a bundle): **`ρ̄ = ⋂_e ρ̄_e`** — (BE-31)(i)'s
>   parallel law, same generalization;
> - **`R`-node** (skeleton 3-connected): **`ρ̄ = ρ̄_{u,v}(B − uv; {ρ̄_e})`**,
>   the decorated kernel — new here.
>
> So `ρ̄_{u,v}(H)` for **every** 2-connected piece is computed from its
> hinge lines alone by one bottom-up pass, and **(BE-31)(ii)'s named
> residue is closed as a computation.** Verified end-to-end (leaf lines →
> sums → intersections → decorated kernel, against the direct `ρ̄`, as
> spaces) at three nested pieces — an R-node atop a `P`-of-`S` theta child;
> the same plus an ear sibling; an R-node atop an `S`-node child whose own
> children are a theta and a path — 3 draws each, zero mismatches.

> **(BE-60)(ii)** *(the honest limit of the description, disclosed)* At `S`-
> and `P`-nodes the law is a lattice expression in the children's `ρ̄`; at an
> R-node it is a **kernel**, into which the skeleton's graph structure and
> its `V(B)`-configuration enter. It is a *computation*, not a formula —
> which is why the sum/intersect recursion could not reach it, and why the
> consumer-facing questions ((BE-62)) do not fall out of it for free.

### Step BE60 — the carve-out: (BE-22)(vi)'s reach at the R-node

> **(BE-61)(i)** *(proven; the collapse condition is a checkable condition
> on `B`)* At the peel `H = H'_e ∪ C_e`, (BE-22)(vi) removes the
> general-position half iff **some side has `δ = 0`**. An ear child never
> supplies one: `f(ear(m)) = m + 1` while welding gives the cycle `C_{m+1}`
> (`g = max(0, m − 5)`, (R3)), so `δ ≥ 2`; a leaf peel's edge side has `δ = 1`; a **theta or leaf-R
> child** is rigid and collapses its own side trivially, but removes no
> flexible child from the remainder. So the load-bearing case is the peel
> **at a flexible child**, where the collapse condition is
> `δ_{x,y}(H'_e) = 0` — and when every other child is a leaf,
> **`δ_{x,y}(B − uv − e) = 0`, a function of `B`, `uv`, `e` alone**,
> decidable by the partition oracle. (Attainment of the remainder at the
> drawn configuration is the (vi) hypothesis's other half; measured at every
> `route` draw.)

> **(BE-61)(ii)** *(measured EXHAUSTIVELY at `n ≤ 6`; the `K₄` refinement)*
> Over **all** labelled 3-connected skeletons `B` on `n = 4, 5, 6` vertices
> — `1`, `26`, `1 768` (total 1 795, **independently reproducing** the
> btwocut `spqr` census count) — and all ordered pairs of distinct edges
> `(uv, e)`: `δ_{xy}(B − uv − e) = 0` at **6/30 (20.0 %)**, **1 170/1 650
> (70.9 %)**, **166 800/196 680 (84.8 %)**. At `K₄` the collapse holds
> **exactly** at `e` disjoint from `uv` (the remainder is `C₄`) and fails at
> every adjacent pair (remainder a triangle with a pendant edge, `δ = 1`) —
> refining the spec's parenthetical, which read the `K₄ + ear` numbers as if
> the skeleton side never collapsed. Named `n = 6` skeletons: prism 41.7 %,
> `K₃,₃` 50.0 %, wheel `W₅` 66.7 %, **octahedron 100 %**.

> **(BE-61)(iii)** *(the spec's expected negative, with a witness)* **The
> prism at two rungs**: `uv` and `e` both rungs leaves
> `H'_e ⊇ prism − 2 rungs` with `f = 1`, `g_{xy} = 0`, so `δ_{xy} = 1` — **a
> single flexible child already leaves no collapse peel** (the only
> flexible-child peel has both sides flexible; every leaf peel has the edge
> side at `δ = 1`). So there is **no peel order that always keeps one side
> collapsible**, and the both-flexible case of (BE-22)(iii) is the R-node's
> irreducible case — reached already at one flexible child whenever
> `δ_{xy}(B − uv − e) > 0`, and at `K₄` from two flexible children on
> non-short-cycle remainders (an `ear(1)` sibling closes the remainder into
> `C₅` and restores the collapse — the short-cycle law (BE-40) is exactly
> what fires).

> **(BE-61)(iv)** *(constructed; the both-flexible case is populated and
> draws)* `K₄ − uv` with ears (3, 3, 2) on `ua`, `vb`, `ab` is an internal
> R-node piece with `dim M = 7`, **`ρ̄_{u,v} ≠ 0`** at every guarded draw,
> and **every** peel both-sides-flexible (`δ = (3, 4)` / `(3, 4)` /
> `(4, 3)`); `K₄ − uv` with ears (3, 3) has both peels at `δ = (1, 4)`.
> These are the `route` battery.

### Step BE61 — job 2: the routing verdict

> **(BE-62)(i)** *(the verdict on the consumer trace — F26, tested as
> required)* **CONFIRMED in its central clause**: a description of
> `ρ̄_{u,v}(H)` at the R-node is **cheap** — (BE-59) is one elementary lemma
> — so the description alone was never going to be the R-node's content,
> exactly as the ear precedent ((BE-30) exact, (α)/(β) still five
> directions' work) predicted. **REFRAMED in one clause**: the trace's *"the
> peel does not reduce to a series-parallel piece"* is true but immaterial —
> the peel does not need to reduce; the decorated skeleton (bounded, one
> kernel) is the object the induction step should hold, the same move BWIN
> made when the middle entered as one opaque subspace `W`.

> **(BE-62)(ii)** *(measured; the drawn (α)/(β) content is EMPTY)* At **24
> measured peels** (4 pieces × 3 draws × their flexible-child peels, every
> configuration through both gates): the fibre-product identity (BE-22)(i)
> **asserted** at every one; both sides **attained** (`dim M_i = 6 + f_i`),
> welded attainment `ρ_i = δ_i` held at **every side**, and the
> general-position shortfall `min(ρ₁ + ρ₂, 6) − dim(ρ̄₁ + ρ̄₂)` was **0 at
> 24/24** — the criterion of (BE-22)(iii) held outright at every drawn
> both-flexible R-node peel, consistent with BTWOCUT's 13 484/13 484 sweep.
> Constructor-capped and disclosed: these are `K₄`-skeleton pieces from one
> sampler; a shortfall elsewhere would be "not attained by this
> constructor", and none was seen.

> **(BE-62)(iii)** *(where the R-node's content actually sits — the named
> residue)* What (BE-22)(iii) at an internal R-node still needs is not a
> computation but a **class statement**: *which decoration tuples `{ρ̄_e}`
> are simultaneously achievable by pencil configurations of `H`* — the
> analogue of (BE-30)(ii)'s achievable-set half, which for the ear was an
> exact bijection. The structure is already visible: children incident to a
> shared branch vertex `z` are coupled **only through the flag
> `(p_z, π_z)`** (the pencil condition at `z` reads on the union of the
> incident children's boundary neighbours, and each child's interior
> constraints see only its own vertices and its terminal flags), so the
> achievable tuples form a **fibred product over flag assignments on
> `V(B)`** of per-child achievable sets — known exactly for leaves
> (`ℓ ∈ Π_x ∩ Π_y`) and ears ((BE-30)(ii)), open in general. That fibred
> statement, plus attainment of the decorated skeleton at the coupled
> flags, is the R-node residue **in its honest minimal form** — the
> successor this direction names.
>
> **LANDED 2026-09-01 as (BE-64)–(BE-68), direction BDECOR — TWO
> annotations at source (F12).** *"Open in general" is CLOSED, by the
> reduction rather than by new geometry*: recursed down to the
> **topological skeleton** the fibration bottoms out at **ears**, and at a
> fixed flag assignment the configurations are a **product** of ear
> chains **modulo the cross-branch proviso `G`** ((BE-64)); per-child sets past ears are never needed, and the
> theta child is a corollary ((BE-66)(i)). And *the quantifier above is
> WIDER than the consumer's*: (BE-22)(iii)'s hypothesis is that both pieces
> **attain**, and the achievable set is strictly larger than the
> attaining-achievable set — its extra members are exactly the `π_x = π_y`
> flag coincidences, measured non-attaining at 7 of 7 ((BE-66)(iii)/(iv)).
> **Read the residue as the ATTAINING-achievable set.**

### Step BE62 — job 3: the chord step, priced against the decorated route

> **(BE-63)** *(pricing verdict, from named landed facts)* The chord step —
> *(BE-14) + the S-mark clause for `G` ⟹ for `G + uv`* — has its
> combinatorial half free ((BE-43)(ii)) and its geometric half priced **not
> soft** ((BE-43)(iii)): `Y°(G + uv)` is a proper closed subset of `Y°(G)`
> and `dim M` is **upper** semicontinuous, so the transfer must defeat
> specialization — the wrong-way direction, with no landed mechanism. The
> decorated route's residue ((BE-62)(iii)) consists of **right-way**
> statements: attainment claims discharged by exhibiting configurations
> (one exact-ℚ witness a proof on the attaining locus, (BE-37)(i)(3)) and
> one class statement of the species BWIN already closed once (quantify
> over an opaque subspace). **Verdict: for the R-node obligation the chord
> step is the strictly harder coordinate**; it remains a coordinate worth
> keeping only where the SPQR frame itself is the obstruction (it needs no
> tree), not as a route to this residue.

### Verdict, classification, and the price

- **HIT shape 1**: `ρ̄` at an internal R-node is **DESCRIBED** — the SP
  recursion extends to a complete recursion over the SPQR tree, by the
  decorated-skeleton law; job 1's sharp question is **YES, proved**.
- **HIT shape 3**: the routing verdict — the R-node's content is in the
  **achievable-decorations class statement** ((BE-62)(iii)), not in the
  description (cheap, delivered) and not in any measured (α)/(β) shortfall
  (empty at 24/24 drawn peels). The board re-ranks around that residue.
- **The price, stated as a price.** The decorated law is exact but is a
  kernel, not a formula ((BE-60)(ii)); the drawn (α)/(β) emptiness is
  constructor-capped (`K₄`-skeleton pieces, one sampler; prism-skeleton
  pieces need a shared-plane sampler the chain does not have — their
  two-hub triangles make the independent-planes draw degenerate, the
  (BE-30)(iii)(c) mechanism); and the achievable-decorations statement is
  open in general, with only leaves and ears known exactly.
- **Untouched.** `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the
  2-cut composition lemma, S-mark, (BE-32)(+), the short-cycle law, BWIN's
  window theorem. **Not a PENCIL event.**

### Verification

Every claim above is reproduced by
`python3 notes/scripts/w4/brnode.py {law|rec|carve [named|full]|route|validate}`,
run from the repo root; `validate` runs all four modes at a reduced tier in
~17 s; the full tiers are `law` 8 s, `rec` 2 s, `carve full` 4 s, `route`
14 s. The load-bearing asserts (a failure stops the run):

1. **Every configuration is a pencil configuration** — `assert_generic_star`
   **and** `verify_pencil_witness` on every draw, interior redraws re-gated.
2. **Every space claim is an identity of SPACES** (`same_space`, and a
   width-agnostic variant for the `K¹²` boundary traces — bimage's `span`
   has a rank-6 shortcut that is wrong at width 12 and is not used there):
   the boundary-pair lemma per child, the decorated law per draw, the
   recursion vs the direct `ρ̄`, the pair tests' equal decorations.
3. **The dim law and (BE-22)(i) are asserted, not reported**, at every draw
   and every measured peel respectively.
4. **The carve enumeration is exhaustive** at `n = 4, 5` in every mode and
   at `n = 6` in `carve full`; `validate`'s `n = 6` tier is the four named
   skeletons plus a 300-graph sample, **disclosed in the output**; the
   1 795 total cross-checks btwocut's landed census.
5. **Exact ℚ throughout**, every rng seeded from the printed literal
   `20260901`, zero floating point.

### Caps, disclosed rather than smoothed

1. **The battery skeletons are `K₄` and `K₃,₃`** (drawing) plus the prism
   (combinatorial only): `sample_piece_config_adj` cannot draw a two-hub
   triangle with independent planes (forced collinear — the
   (BE-30)(iii)(c) mechanism), so prism-skeleton pieces appear in `carve`
   but not in `law`/`route`; a shared-plane (class) sampler would lift
   this.
2. **The pair test runs at two mechanisms** (full-span `ear(5)`, flat
   `Λ²π`), not at every equal-`ρ̄` mechanism; the law itself is proved, so
   the pairs are corroboration, not the evidence.
3. **(BE-62)(ii) is a measurement**, 24 peels over 4 constructed pieces —
   it locates no obstruction; it does not prove the class statement.
4. **`carve`'s named/sampled `n = 6` tier in `validate`** is not
   exhaustive; `carve full` is, and its figures are the quoted ones.
5. **Attainment figures are constructor lower bounds** (F27,
   one-directional): every drawn piece attained, so nothing here rests on
   the cap.

### Harness note — the `kbare/` sibling-import set gains its THIRTEENTH consumer

`brnode.py` imports `bwin` (`dehom`), `bsharp` (`guarded_draw`,
`sample_piece_config_adj`, `_relabel`), `bimage` (the space helpers,
`rho_bar_of`, `lam2`) and `binduc` (`assert_generic_star`,
`def_by_partitions`, `motion_space`, `set_partitions`, `theta`,
`vertex_connectivity_at_least`) **read-only**, and through them the rest of
the chain, so the recorded **unpaid** sibling-import debt
(`notes/scripts/README.md` *Harness debt*) gains its **thirteenth** `w4/`
consumer and the chain is now **eleven** deep: `battain → bzavoid → binduc →
btwocut → bimage → bearcase → bearfull → bsharp → brule → bwin → brnode`.
**NO MOVE MADE**; the consumer list is extended in the README, exactly as
the previous twelve did. The new primitives (`build_piece`,
`decorated_motion`, the width-agnostic `K¹²` helpers, the carve oracle) are
local to this driver.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-59)(i) the boundary-pair lemma | **PROVED** (two lines, from (BE-22)(i)'s proof); asserted in `K¹²` at every child of every draw |
| (BE-59)(ii) the decorated-skeleton law; job 1's sharp question YES | **PROVED**; asserted at 36 draws + 6 equal-`ρ̄` interior-redraw pairs |
| (BE-59)(iii) the dim law | **PROVED** (a count, labelled one); asserted per draw |
| (BE-60)(i) the complete SPQR recursion | **PROVED** (the law at each skeleton shape); lines-only recursion asserted at 3 nested pieces × 3 draws |
| (BE-60)(ii) kernel-not-formula at the R-node | **DISCLOSED** (a statement about the description's form, not a theorem that no formula exists) |
| (BE-61)(i) the collapse condition `δ_{xy}(B − uv − e) = 0` | **PROVED** (from (BE-22)(vi) + the peel structure) |
| (BE-61)(ii) the enumeration; the `K₄` refinement | **MEASURED, EXHAUSTIVE at `n ≤ 6`** (198 360 triples; census cross-check 1 795) |
| (BE-61)(iii) the prism negative — no collapse peel at one flexible child | **PROVED** (the `δ = 1` partition computation) + measured |
| (BE-61)(iv) the both-flexible case draws, `ρ̄_{u,v} ≠ 0` | **CONSTRUCTED** (guarded draws) |
| (BE-62)(i) the F26 verdict on the consumer trace | **CONFIRMED with one reframe**, per the spec's own job |
| (BE-62)(ii) drawn (α)/(β) content empty | **MEASURED** (24/24 peels; constructor-capped, cap 3) |
| (BE-62)(iii) the residue = the achievable-decorations class statement, fibred over flags | **LOCATED** (the flag-coupling factorization is proved; the per-child sets are known for leaves and ears only) |
| (BE-63) the chord step strictly harder for this obligation | **PRICED** (from (BE-43)(ii)/(iii) + this landing; a comparison, not a refutation) |

### What would change this

- **A child whose boundary trace is not `Δ ⊕ 0⊕ρ̄`** would refute (BE-59)(i)
  — impossible for connected children at legal configurations (the proof is
  two lines), so a counterexample would mean a broken carrier convention;
  the first place to look would be the driver chain's `build_rigidity`.
- **A both-flexible R-node peel with a persistent criterion shortfall**
  (welded or general-position, surviving resampling and constructor
  escalation per (GR-83)/(GR-113)) would be the first (α)/(β)-shaped
  obstruction of the R-node case — it would land in (BE-62)(iii)'s residue
  as a genuine class obstruction and re-rank the board toward the disproof
  side. None was seen.
- **The achievable-decorations statement** ((BE-62)(iii)) is the named
  successor: per-child achievable sets past ears (theta children first —
  their `ρ̄` is an intersection of chain spans, so the ear machinery
  composes), then attainment of the decorated skeleton over the coupled
  flags — the (α)-analogue whose window-style class form is what
  (BE-22)(iii) at the R-node actually consumes.
- **The one-end-series case and the spread step** (BWIN's ranked
  successors) are unaffected by this landing and stay ranked.

### TERMINATION riders

**E1: NO** — this direction is one gluing lemma, one kernel construction,
one partition-oracle enumeration and one measurement pass; no `g`-flank is
involved and none is produced. **E2: NO** — nothing landed is refuted; the
one annotated prose surface ((BE-31)(ii)) is closed, not corrected, and
every landed measurement is intact. **E3: ARMED by GBAL, not fired** — this
direction is on the §(K-bare-ext) path, not (a′); reported, not acted on.
