## §(K-bare-ext) — continuation (direction BBASE): **THE FLAG BASE IS FREE, AND IT WAS NEVER (CH-1)'s OBJECT** — the base is the FLAG variety of `B_real`, a flag at *every* vertex, so it is §(K-chart)'s tower with the hub set taken to be **all of `W`** and therefore **stages 1–2 only**; stages 3 and 4 — the ones where min degree `2` and girth `≥ 4` are spent — **do not exist**, because `B_real` has no non-hub vertices. It is a **complete intersection of the expected dimension `5|W| − 2|E|`**, it **factors over `B_real`'s components**, and on a **FOREST** component it is nonempty, irreducible, ℚ-rational with dense ℚ-points **unconditionally** — no genericity, no degree bound — because the flag tower's fibre `F_Π` is irreducible of **constant** dimension `3` at every `Π`; a **unicyclic** component follows on `Base°`, so **every component of cyclomatic number `≤ 1` is covered**, which is every component the census meets. That kills the coordinator's reading (3): the fibre-dimension jump at `p_i = p_{i+1}` is an artifact of **splitting the flag** into point-then-plane. Reading (2) is **refuted** — (CH-1) does not apply to `B_real` at all — and reading (1) is **refuted as stated**, because `W` is the *marked-pair-augmented* hub set and `hcard` caps `Λ(H)`, not `B_real` (`Δ = 3` at **737** class-tier pieces). The one genuine obstruction is a **short cycle**: the FULL base is **REDUCIBLE** at a `B_real`-triangle (flag dims `10 > 9`) and at a `B_real`-4-cycle (`12 = 12`), both extra components living entirely off the constant-rank locus that the arc's own proviso `G` already imposes — and both **excluded outright on the class**, where a `B_real`-cycle is a cycle of `G` and girth is `≥ 6`. Measured: `B_real` is a **forest at 78 564 / 78 564** class-tier peel pieces, `hcard` at **0 / 78 564** failures, and a component of cyclomatic number `≥ 2` — the one shape no clause here reaches — occurs **0 / 78 564** on the class against **22 / 10 678** off it, where **118** triangle components also live

Answering `notes/pencil/fanout.md` §"BBASE" (sixty-second ordinal, 2026-09-02),
the (BE-14) thread's **candidate 1**: the flag base off the no-adjacent-hubs
class, (BE-65)(i) / (BE-68)(ii) item 1. Read against §(K-bare-ext)'s BDECOR
block (*Steps BE63–BE67*), §(K-chart) *Steps CH1–CH6* ((CH-1)/(CH-5)/(CH-6))
and (BE-72). Driver: `notes/scripts/w4/bbase.py` (five modes,
`census`/`dim`/`forest`/`tri`/`cross`, run together by `validate`).

**Why this direction was priced small and came out structural.** (BE-65)(i)
calls the off-class base *"the phase's own problem one level down, on a graph
with `|W|` vertices"*, and (BE-68)(ii) carries that sentence forward as one of
half (B)'s two residue items. It is the wrong reading of the object, in a way
that makes the residue **larger** than it is: the base has a flag at **every**
vertex of `B_real`, while `𝒜(Γ)` — the object (CH-1) is about — has a normal
only at a vertex of degree `≥ 3`. Under `hcard` those two sets are nearly
disjoint. Once the base is written down in the right ambient, its whole
difficulty is a **short cycle**, and short cycles are what the class forbids.

**Three things came out other than the expected bookkeeping.**

1. **All three coordinator readings are wrong, in three different ways, and
   each correction is worth more than the reading was.** Reading (1)'s
   `Δ(B_real) ≤ 2` fails at **737** class-tier pieces — but for a reason that
   is itself a theorem, and one that *localizes* the failure: `W` is the
   marked-pair-augmented hub set, so `d_z(B_real) = d_z(Λ(H)) + |N_H(z) ∩
   ({u,v} ∖ hubs(H))|`, and `hcard` caps only the first term. Reading (2)'s
   *"(CH-1) settles the cycles of length `≥ 4` verbatim"* is **inapplicable**,
   not merely unproven. Reading (3)'s feared jump is real in the tower the
   coordinator staged and **absent** in the right one.
2. **The base is free on a FOREST with no hypothesis at all** — not `hcard`,
   not min degree, not girth, not genericity, not a degree bound. That is a
   strictly stronger statement than anything (CH-1) supplies, and it is what
   the pieces actually need: `B_real` is a forest at **78 564 / 78 564**
   class-tier peel pieces, and every component met is of cyclomatic number
   `≤ 1`, which (BE-91)(iii) also covers — **(BE-90)**.
3. **The obstruction that does exist is REDUCIBILITY, not emptiness — and it
   is at cycles, not at paths.** At a `B_real`-triangle the collinear stratum
   is a component of flag dimension **10** against the good component's **9**;
   at a `B_real`-4-cycle the two are both **12**. Nonemptiness is never in
   question. This is *not* the (CH-5)/(BE-72) triangle phenomenon — that one
   is emptiness of a *meet*, and there is no meet to be empty here — so
   (BE-72)'s existential absorption is not what saves it; girth is —
   **(BE-92)**.

---

### Standing notation

Inherited from *Steps BE9–BE87* verbatim, and in particular BDECOR's
(*Steps BE63–BE67*): the hub set `W := {u, v} ∪ {z : deg_H(z) ≥ 3}`
(**coarser** than §(K-chart)'s degree-`≥ 3` set), the topological branch and
its length, `B_real` the graph on `W` whose edges are the **length-1**
branches, the flag `(p_z, π_z)`, and the genericity proviso `G` (points
pairwise distinct, no two hinge lines coincident at a hub). Added here:

- the projective carrier is the arc's own (`bimage`/`bdecor`, and
  `kbare_common.verify_pencil_witness`'s reading of the pencil condition): a
  point is a nonzero `p ∈ K⁴` up to scale, a plane a nonzero covector `n` up
  to scale, and `p ∈ π` is `⟨n, p⟩ = 0`. `Fl := {(p, π) ∈ P³ × P̌³ : p ∈ π}`
  is the **point-plane flag variety**, irreducible, ℚ-rational, homogeneous
  under `PGL₄`, of dimension `5`;
- **`Base(B) ⊆ Fl^W`**, for a graph `B` on `W`: the tuples `(Π_z)_{z ∈ W}`
  with `p_{z'} ∈ π_z` **and** `p_z ∈ π_{z'}` for every edge `zz'` of `B`.
  `Base(B_real)` **is** (BE-65)(i)'s flag base, verbatim;
- `d_z := deg_B(z)`; `r_z := rank({p_z} ∪ {p_w : w ∼_B z})` as vectors of
  `K⁴`, so the planes through the closed `B`-star of `z` form a `P^{3−r_z}`,
  **nonempty iff `r_z ≤ 3`**;
- the **constant-fibre-dimension locus** `U := {r_z = min(1 + d_z, 3)
  ∀ z}` and `Base°(B) := Base(B) ∩ (U × ⋯)`. At `d_z = 2`, `U`'s condition at
  `z` is *`p_z, p_{z'}, p_{z''}` not collinear* — which is **exactly** the
  hinge-coincidence half of `G`, and §(K-chart)'s `U_H` at a hub ((CH-6)(i));
- `F_Π := {(p, π) ∈ Fl : p ∈ π₀, p₀ ∈ π}` for `Π = (p₀, π₀) ∈ Fl` — the
  **flag tower's fibre**, the set of flags incident to a given one.

**Carrier check, done off the landed bodies rather than the prose.** The
conditions above are `bdecor.flag_assignment`'s own (`bdecor.py:253`, the
**body** read this pass: `cons[z] = {z} ∪ ha[z]` required to have `rank ≤ 3`,
the plane then read off that span), and `ha` is `bdecor.hub_adjacency`, whose
**body** adds `zp` to `ha[z]` exactly when a branch `(z, zp, ints)` has
`ints == []` — i.e. exactly on the length-1 branches, (BE-65)(i)'s `B_real`
verbatim. **No `.lean` was opened; the standing 2026-08-05 Lean hold binds**,
so job 2's Lean input is read at one remove, from the sibling workbook's own
quotation of it (see *Step BE92*).

### Step BE88 — (BE-89): the base, identified — the FLAG variety of `B_real`, and why (CH-1) is not about it

> **(BE-89)(i)** *(proven; the base as a variety, and it is a complete
> intersection of the expected dimension)* `Base(B)` is the closed subvariety
> of `Fl^W` cut out by the `2|E(B)|` bilinear equations `⟨n_z, p_{z'}⟩ = 0`,
> one per **ordered** end of each edge. Hence every component has dimension
> `≥ 5|W| − 2|E(B)|`, and at a point where the Jacobian of those equations
> (together with the `|W|` own-incidence equations, on the affine cone) has
> full rank `|W| + 2|E(B)|`, `Base(B)` is **smooth of dimension exactly
> `5|W| − 2|E(B)|`**.
>
> *Proof.* The cone over `Fl^W` in `(K⁴)^W × (K⁴)^W` is cut by the `|W|`
> equations `⟨n_z, p_z⟩ = 0`; adding the `2|E|` cross-incidences gives
> `|W| + 2|E|` equations in `8|W|` variables, so the cone has dimension
> `≥ 7|W| − 2|E|` everywhere and `= 7|W| − 2|E|` at a full-rank point.
> Subtracting the `2|W|` scalings gives the flag count. ∎
>
> Verified exact-ℚ at drawn base points over **19** shapes (`bbase.py dim`):
> paths of `1–7` vertices, cycles of `3–8`, `K_{1,3}`, `K_{1,4}`, a
> caterpillar, a disconnected pair, a tadpole (`C₄` + pendant) and a theta —
> full rank and `dim = 5|W| − 2|E|` at **19/19**, matching the flag tower's
> independent count `5 + 3(m−1)` on a path and `3m` on a cycle.

> **(BE-89)(ii)** *(proven; the base FACTORS over components — reading (2)'s
> one correct half)* Every defining equation of `Base(B)` involves the flags
> of **one edge** only, so for `B = ⨆_i C_i` a decomposition into connected
> components, `Base(B) = ∏_i Base(C_i)` as varieties. Nonemptiness,
> irreducibility, rationality and density of ℚ-points are therefore each
> **component-local**.

> **(BE-89)(iii)** *(a correction to (BE-65)(i)/(BE-68)(ii), and the load-
> bearing observation of this direction)* The flag base is **not** `𝒜(B_real)`
> in §(K-chart)'s sense, and **(CH-1) does not apply to it**. §(K-chart)'s
> ambient `𝔸(Γ) = (𝔸³)^{V(Γ)} × (𝔸³)^{H(Γ)}` carries a normal only at a vertex
> of **degree `≥ 3`** (`PencilHub`, *Step CH1*'s own notation), whereas the
> flag base carries one at **every** vertex of `B_real`. Under `hcard`,
> `Λ(H)` has max degree `≤ 2`, so a `B_real` component that is a path or a
> cycle has `H(B_real) = ∅` and `𝒜(B_real)` has **no normals at all** — it is
> the configuration space of distinct points, a different variety. In
> particular the coordinator's reading (2) — *"(CH-1) already settles the
> cycles of length `≥ 4` verbatim"* — is **inapplicable**, not merely
> unproven, and (BE-65)(ii)'s *"this direction cites §(K-chart) rather than
> re-deriving it"* does **not** extend from the piece `H` to the base.

> **(BE-89)(iv)** *(proven; what IS true, and it is strictly better)* Read
> §(K-chart) *Step CH3*'s tower with the hub set taken to be **all** of `W`.
> Then the flag base is exactly its **stages 1 and 2** — free points, then one
> normal per vertex in `ker A_z(p) ∖ 0` — and **stages 3 and 4 do not exist**,
> because `B_real` has no non-hub vertices. Stage 3 is `N°`, the meet-line
> locus, and stage 4 is the non-hub placement; **those are precisely the
> stages (CH-5) shows can be empty**, and they are where (CH-1)'s *girth
> `≥ 4`* is spent ((CH-5)(iii)) and where *min degree 2* enters (FRES's rider
> at *Step FR13*). So the base's hypotheses are strictly **weaker** than
> (CH-1)'s, and the (BE-72)/(CH-5) twin-plane obstruction — *"a non-hub `s`
> with two hub neighbours whose two panels coincide"* — **cannot even be
> stated** here: there is no `s`, and no meet to be empty.
>
> *Corollary (nonemptiness, unconditional).* `Base(B) ≠ ∅` for **every**
> graph `B`: put all points at one `p` and all planes at one `π ∋ p`. Every
> incidence holds. So no `B_real` empties the base, ever — which is the
> clause (BE-65)(iii)'s consumer would have lost first, and it costs nothing.

### Step BE89 — (BE-90): the FOREST theorem — free, with no hypothesis at all

> **(BE-90)(i)** *(proven-informally; the fibre)* For every `Π ∈ Fl`, the
> fibre `F_Π = {(p, π) ∈ Fl : p ∈ π₀, p₀ ∈ π}` is **irreducible of dimension
> `3`**, ℚ-rational over `ℚ(Π)`, with dense ℚ-points; it is smooth away from
> the single point `Π` itself.
>
> *Proof.* Project `F_Π → π₀ ≅ P²` by `(p, π) ↦ p`. Over `p ≠ p₀` the fibre
> is the **pencil** of planes through the line `p₀p`, a `P¹`; so
> `F_Π ∖ {p = p₀}` is a `P¹`-bundle over the irreducible `π₀ ∖ {p₀}`, hence
> irreducible of dimension `2 + 1 = 3`, and ℚ-rational (the pencil has an
> obvious ℚ-rational parameter). Over `p = p₀` the fibre is `{π ∋ p₀} ≅ P²`,
> of dimension `2`; every one of its points is a limit of the bundle part —
> given `π ∋ p₀`, if `π ≠ π₀` move `p` to `p₀` along the line `π ∩ π₀`
> keeping `π` fixed, and if `π = π₀` move `p` to `p₀` inside `π₀` keeping
> `π = π₀`. Hence `F_Π` is the closure of an irreducible `3`-fold. ∎
>
> Measured (`bbase.py forest`): `25/25` drawn fibre points are **smooth** of
> flag dimension `8 = 5 + 3` for the two-vertex base; the constructed
> degenerate point `Π₂ = Π₁` is **legal** with tangent dimension `9 > 8` —
> the fibre's only singular point, and it is *inside* the same irreducible
> `F_Π`, not beside it.

> **(BE-90)(ii)** *(proven-informally; **the forest theorem**)* If `B` is a
> **forest** — any degrees, any number of components — then `Base(B)` is
> **nonempty, irreducible, ℚ-rational with dense ℚ-points**, of dimension
> `5|W| − 2|E(B)|`. **No genericity condition, no degree bound, no girth and
> no min-degree hypothesis is used.**
>
> *Proof.* By (BE-89)(ii) it suffices to treat one tree component. Order its
> vertices `z₁, …, z_m` so that each `z_i` (`i ≥ 2`) has **exactly one**
> neighbour among `z₁, …, z_{i−1}` — a BFS order of a tree. Then
> `Base` is built as a tower: `Π_{z₁} ∈ Fl` free, and at step `i` the whole
> flag `Π_{z_i}` ranges over `F_{Π_{parent}}`, because the *only* conditions
> `Π_{z_i}` must meet are the two incidences with its unique placed
> neighbour. Each stage is therefore **surjective onto an irreducible base
> with every fibre irreducible of the same dimension `3`** ((BE-90)(i)), which
> makes the total space irreducible (Shafarevich I.6.3, Thm 8). Rationality
> and density of ℚ-points come from the *explicit* fibre parametrization
> rather than from that theorem: over the open where a fixed pair of
> coordinates trivializes `π₀` and a fixed coordinate trivializes the pencil,
> the stage is birational over ℚ to base `× 𝔸³`, so the tower is a chain of
> ℚ-birational maps to affine space. Hence `Base` is irreducible and
> ℚ-rational of dimension `5 + 3(m−1) = 5m − 2(m−1)`, with dense ℚ-points. ∎

> **(BE-90)(iii)** *(the correction to the coordinator's reading (3) — the
> reading the spec flagged as most likely to be wrong, and it is)* Reading (3)
> proposed the greedy tower *`p₁` free (3), `π₁ ∋ p₁` (2), then per step
> `p_{i+1} ∈ π_i` (2) and `π_{i+1} ∋ p_i, p_{i+1}` (1)*, and worried that the
> last fibre **jumps** from `1` to `2` where `p_i = p_{i+1}`. **The count is
> right and the staging is wrong.** The jump is real *in that staging* and is
> an artifact of it: the two sub-stages `p_{i+1}` and `π_{i+1}` are not
> individually equidimensional, but their **product**, the single stage
> `Π_{i+1} ∈ F_{Π_i}`, is — dimension `3` at every `Π_i`, by (BE-90)(i). So
> min degree `2` is **not** (CH-1)'s hypothesis *because of* that jump, and a
> path is not harder at its ends; it is **freer** than a cycle, because a tree
> needs no genericity at all.
>
> Measured (`bbase.py forest`): `25` **constructed** base flags with
> `p₁ = p₂` exactly — the configuration reading (3) feared — every one legal
> and a **smooth** point of the same `5|W| − 2|E| = 11` component. Path bases
> **built by the tower** at `m = 2, …, 7` give flag dimension `5 + 3(m−1)` at
> `6/6`.

### Step BE90 — (BE-91): max degree `≤ 2` — the point-first bundle, and `U` is the arc's own gate

> **(BE-91)(i)** *(proven-informally)* Let `B` have `d_z ≤ 2` at every vertex
> (so its components are paths, cycles and isolated vertices). Then the point
> projection `Base(B) → (P³)^W` is **surjective**, and over the nonempty open
> `U ⊆ (P³)^W` it is a Zariski-locally-trivial fibration with fibre
> `∏_z P^{2−d_z}`. Hence `Base°(B)` is **nonempty, irreducible, ℚ-rational
> with dense ℚ-points**, of dimension `3|W| + Σ_z (2 − d_z) = 5|W| − 2|E(B)|`.
>
> *Proof.* For **fixed** points the conditions are linear in `n_z` and involve
> **one** `z` each, so the fibre is the product over `z` of the planes through
> `{p_z} ∪ {p_w : w ∼ z}`, a `P^{3−r_z}`; and `r_z ≤ 1 + d_z ≤ 3`, so it is
> nonempty at **every** `p` — this is (CH-3)'s arithmetic, with `d_z ≤ 2`
> doing exactly the same job. `U` is nonempty (take the `p_z` on the moment
> curve: no three collinear), open, and irreducible as an open subset of
> `(P³)^W`; over it each factor is a projective subbundle of constant rank of
> the trivial bundle, locally trivialized by the same nonvanishing
> `r_z × r_z` minor. ∎
>
> **(BE-91)(iii)** *(proven-informally; the UNICYCLIC corollary — what
> actually turns up)* Let `C` be a connected component of `B` with **exactly
> one** independent cycle (cyclomatic number `1`): a cycle `Z` with trees
> hanging off it. Order `C` by taking `Z` first and then BFS outward; every
> vertex after `Z` has **exactly one** placed neighbour, so `Base(C)` is an
> iterated `F_Π`-fibration over `Base(Z)` — irreducible over any irreducible
> piece of `Base(Z)`, by (BE-90)(i) and the same criterion. Hence `Base(C)`
> restricted over `Base°(Z)` is irreducible and ℚ-rational, and `Base°(C)`,
> being a **nonempty open** subset of it, is irreducible and ℚ-rational too.
> Together with (BE-90)(ii) this covers **every component of cyclomatic
> number `≤ 1`**,
> which is every component the census meets ((BE-93)(iii)) — including the
> arc's own nested battery piece, whose `B_real` is `6` vertices, `6` edges
> with a degree-`3` vertex.
>
> **The same statement covers `d_z ≥ 3` on its own constant-rank locus:** the
> fibre is nonempty iff `r_z ≤ 3`, so the point base is cut down to the
> determinantal locus `{r_z ≤ 3}` and `U` asks for `r_z = 3` exactly. What is
> lost is only that the point stage is no longer free; the fibre argument is
> unchanged. Verified at the arc's own **nested** battery piece, whose
> `B_real` has a degree-`3` vertex: `2/2` drawn flags are smooth points of the
> `5|W| − 2|E| = 18` component (`bbase.py cross`).

> **(BE-91)(ii)** *(the identification that makes (i) free for the consumer)*
> `U`'s condition at a `d_z = 2` vertex is *`p_z` and its two `B_real`-
> neighbours are not collinear* — which is **verbatim** the hinge-coincidence
> half of the proviso `G` that (BE-64)(ii)'s product theorem is already stated
> modulo (`binduc.assert_generic_star`; and `repin.star_generic`'s second
> clause, per (CH-6)(iv)). So the base the consumers of (BE-64)–(BE-67)
> actually range over **is** `Base°`, not `Base`, and (BE-91)(i) is a
> statement about the object in play rather than a restriction of it.

### Step BE91 — (BE-92): the short-cycle correction — the FULL base is REDUCIBLE at `m = 3` and `m = 4`

> **(BE-92)(i)** *(proven; the triangle identity)* On a `B_real`-triangle,
> at every point of `U`, the three planes **coincide**: `A_{z₁}`'s two rows
> `p₂ − p₁, p₃ − p₁` and `A_{z₂}`'s `p₁ − p₂, p₃ − p₂` span the **same**
> plane of directions, so `π₁ = π₂ = π₃` is forced. Equivalently, in the
> projective carrier, all three closed stars are the same three points.
> Measured: `200/200` draws on `U` (`bbase.py tri`).

> **(BE-92)(ii)** *(proven; the extra component, exhibited)* The **collinear
> stratum** of `Base(C_m)` — all `m` points on one line `L`, all `m` planes
> in the pencil through `L` — is a legal, irreducible, locally closed subset
> of flag dimension `4 + 2m` (`4` for `L ∈ Gr(2,4)`, `1` per point on `L`,
> `1` per plane through `L`), and it is **disjoint from `U`**. Against the
> good component's `3m`:
>
> | `m` | good `3m` | collinear `4 + 2m` | verdict |
> |---|---|---|---|
> | 3 | 9 | **10** | **REDUCIBLE**, the extra component is *strictly bigger* |
> | 4 | 12 | **12** | **REDUCIBLE**, two components of equal dimension |
> | `≥ 5` | `3m` | `4 + 2m < 3m` | strictly smaller; measured tangent `3m`, so it creates **no** component of its own |
>
> *The separation argument, and it is purely dimensional.* `Base°(C_m)` is
> irreducible of dimension `3m` by (BE-91)(i), and it is a nonempty **open**
> subset of its own closure. A collinear point lies off `U`. If the collinear
> stratum `S` were contained in `\overline{Base°}` then, being irreducible of
> dimension `≥ 3m`, its closure would **equal** `\overline{Base°}`, so `S`
> would be dense there and would have to meet the nonempty open `Base°` —
> which it cannot, being disjoint from `U`. Hence at `m = 3, 4` the closure of
> `S` is a **second component**. ∎
>
> At `m = 3` there is a second, independent argument: by (BE-92)(i) the good
> component has `π₁ = π₂ = π₃` identically, a **closed** condition, and the
> exhibited witness has three **pairwise distinct** planes.
>
> Driver-exhibited exact-ℚ (`bbase.py tri`): a constructed collinear triangle
> flag, legal, planes pairwise distinct, tangent flag dimension `10 > 9`; the
> stratum drawn as a family, `40/40` legal; the same construction at
> `m = 3, …, 8` with the tangent dimension measured at each.

> **(BE-92)(iii)** *(what it costs, and why it is not the (BE-72)/(CH-5)
> phenomenon)* It costs **nothing to nonemptiness** — (BE-89)(iv)'s corollary
> is unconditional — and it is not the twin-plane obstruction, which is about
> a *meet* being empty at a non-hub and has no analogue here ((BE-89)(iv)).
> What it breaks, if it ever occurred at a consumer, is (BE-65)(iii)'s
> **one-draw** mechanism, which needs an irreducible parameter space. Two
> things keep it away:
>
> - **the arc's own proviso.** Both extra components lie entirely off `U`, and
>   `G ⟹ U` by (BE-91)(ii). Every landed figure of (BE-64)–(BE-67) is drawn
>   under `G`, so none of them is disturbed;
> - **girth, on the class.** A `B_real`-cycle of length `m` is a cycle of `H`
>   of length `m`, hence a cycle of `G` (`binduc.split_at_pair`'s body returns
>   genuine subgraphs — `E₁ ∪ E₂ = E`, `E₁ ∩ E₂ = ∅`, **no virtual edge** —
>   read this pass), so `m ≥ girth(G) ≥ 6` ((FR-15)'s last table row). **So no
>   class shape has a `B_real`-triangle or a `B_real`-4-cycle**, and the two
>   reducible shapes are unreachable. Measured: girth `≥ 7` at `1 606 / 1 606`
>   class members of three exhaustive/sampled skeleton tiers.
>
> **The shape is nonetheless real, and reachable one step away.** Two of the
> seven `R_BATTERY` pieces of (BE-64)/(BE-66) — `K4 + th(3,3,3)/ab` and
> `K4 + th(5,5,5)/ab` — have `B_real` a **4-cycle** with `girth(H) = 4`, so
> their flag base is reducible in exactly this way; and off the class,
> `bpeel.constructed_tier` reaches **118** triangle components and **68**
> 4-cycle components in `10 678` pieces. At the battery the landed sampler
> draws inside `Base°` at `16/16`, so no landed figure moves.

### Step BE92 — (BE-93): job 2's transport, the consumer verdict, and half (B)'s residue

> **(BE-93)(i)** *(job 2, answered in two halves — and the second half is what
> refutes reading (1))* **`hcard` DOES transport to the pieces**, by
> monotonicity and for a reason with nothing measured in it: a piece `H` of a
> peel is a **subgraph** of `G` (`split_at_pair`, body read this pass), so
> `deg_H ≤ deg_G`, so `hubs(H) ⊆ hubs(G)` and `Λ(H) ⊆ Λ(G)[V(H)]`; hence
> `deg_{Λ(H)}(z) ≤ deg_{Λ(G)}(z) ≤ 2`. The `≤ 2` at `G` is the sibling W4
> arc's **(EL-1)** — *in a `PencilNondegFeasible` graph every hub has at most
> two hub neighbours*, a **necessary condition**, not a modelling choice —
> and it is a landed, compiler-checked Lean theorem
> (`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`). **Read at one
> remove**: the 2026-08-05 Lean hold binds this direction, so the statement
> and the `closedHubNbhd` definition body are taken from
> `notes/pencil/workbook/W4.md`'s own quotation of them, not from the file.
> **`hcard` is therefore not the sampler's cap** — (BE-65)(ii)'s sentence was
> about the sampler; this is about the pieces, and it holds at `0 / 78 564`
> failures over the class tier.
>
> **But it does not cap `B_real`.** `W` is the **marked-pair-augmented** hub
> set, so
>
> **`d_z(B_real) = d_z(Λ(H)) + |N_H(z) ∩ ({u,v} ∖ hubs(H))|`**,
>
> asserted per vertex at every piece of the census, and `hcard` bounds only
> the first term. Since `deg_H(u), deg_H(v) ≤ 2` when they are not hubs, the
> excess is at most `2`, so `Δ(B_real) ≤ 4` in principle and `Δ(B_real) = 3`
> is **realized at 737 class-tier pieces**. **Reading (1) is refuted as
> stated**, and what survives it is sharper: `B_real ∖ {u,v} = Λ(H)` has max
> degree `≤ 2`, so `B_real` is a disjoint union of paths and cycles with at
> most two further vertices of degree `≤ 2` attached.

> **(BE-93)(ii)** *(the consumer verdict — which of the four properties, and
> which are actually needed)* On the class:
>
> | property | delivered | by | who needs it |
> |---|---|---|---|
> | **nonempty** | **yes, unconditionally, for every `B_real`** | (BE-89)(iv) | (BE-64)(ii)/(BE-64)(iv) — the product is over legal flags, and an empty base would empty the achievable set |
> | **irreducible** | **yes** on every forest component (unconditionally) and on `Base°` of a cycle component | (BE-90)(ii), (BE-91)(i) | **(BE-65)(iii)**, and only (BE-65)(iii): semicontinuity on an irreducible parameter space is what makes *one exact-ℚ draw settle the generic value* |
> | **ℚ-rational** | **yes**, same two clauses | (BE-90)(ii), (BE-91)(i) | nobody, strictly — but it is what makes `bdecor.flag_assignment` correct **by construction**, since that sampler *is* the tower |
> | **dense ℚ-points** | **yes**, same two clauses | (BE-90)(ii), (BE-91)(i) | every exact-ℚ driver in *Steps BE63–BE87*: a ℚ-draw must be able to land at a generic point |
>
> So all four hold, and the two the consumer genuinely needs — nonemptiness
> and irreducibility — hold on the **strongest** hypotheses of the four: the
> first with none at all, the second with none at all on a forest.

> **(BE-93)(iii)** *(half (B)'s residue, and (BE-68)(ii) rewritten)*
> (BE-68)(ii)'s **item 1 is DISCHARGED** on the class, with its two named
> caveats above the line rather than hidden: the base is free, and the only
> way it could fail — a `B_real` cycle of length `3` or `4` — is a cycle of
> `G` of length `≤ 4` and so is excluded by girth `≥ 6`. **Half (B)'s residue
> drops from TWO items to ONE**: the class quantifier (BE-67)(iii). The
> (BE-14) thread's open step is unchanged — S-mark, the 2-cut composition
> lemma — and `hbareSplit`, `hK`, (GR-15) and class uniformity are untouched.
>
> **The residue, named exactly.** (BE-90)(ii) covers every **forest**
> component; (BE-91)(i)/(iii) cover every component of cyclomatic number `1`.
> **What no clause here covers is a component of cyclomatic number `≥ 2`** —
> and that shape occurs **`0` times in `78 564` class-tier pieces** and **`22`
> times in `10 678` off-class ones**. It is not obviously hard: at the
> smallest such shape, a **theta**, `U`'s conditions at the two degree-`3`
> vertices already force all five points into one plane and then every plane
> into that plane, and a constructed `U`-point is a smooth point of the
> expected `5|W| − 2|E| = 13` component (`bbase.py dim`). What is missing is
> an argument, not a witness.
>
> **What is NOT claimed.** That `B_real` is a forest **in general** on the
> class. It is a forest at `78 564 / 78 564` pieces of three skeleton tiers,
> but those tiers have `≤ 6` hubs while girth `≥ 7` forces a `B_real`-cycle to
> have length `≥ 7`, so **the tiers cannot exhibit one** — a cap-boundary
> fact, not evidence about the class beyond it (`notes/scripts/README.md` §4
> convention 8). A larger class shape could carry a `Λ`-cycle of length `≥ 7`;
> (BE-91)(i)/(iii) then covers it, on `Base°`, which is where `G` puts it
> anyway.

---

### Verdict, classification, and the price

**Classification: HIT shape 1** — *the flag base is FREE off the
no-adjacent-hubs class, half (B)'s residue drops to the single item
(BE-67)(iii), and (BE-68)(ii) is rewritten* — plus **HIT shape 4** (job 2's
`hcard` verdict, load-bearing, and it comes out *yes* for the transport and
*no* for reading (1)) and **HIT shape 5** (job 3). **HIT shape 3 partially**:
an obstruction exists and is classified **reducible, not empty** — the exact
distinction job 1 asked for — but it is unreachable on the class. All three
coordinator readings are **corrected**, which the spec records as a reportable
result in its own right.

**Confidence.** (BE-89)(i)–(iv), (BE-90)(i)–(iii), (BE-91)(i)–(ii) and
(BE-92)(i)–(ii) are **proven-informally**, by arguments with no measurement in
them; (BE-91)(iii) likewise; every one is *also* driver-exercised, and the driver's role is to catch a
mis-stated dimension, not to establish a claim. (BE-92)(iii)'s girth clause is
**proven** given (FR-15)'s girth row, which is **cited**. (BE-93)(i)'s
transport is **proven**; its `≤ 2` input is **cited** at one remove under the
Lean hold. Every census figure is **measured**, with its denominator named.

**The price, stated as a price.** **(1)** The *class* statements rest on
(FR-15)'s `girth(G′) ≥ 6`, which this direction cites and does not re-derive;
if that row were wrong, the `m = 3, 4` exclusion goes with it (the `Base°`
clause does not). **(2)** `B_real`-forest-ness is **measured**, not proved,
and the tiers that measured it are structurally incapable of a counterexample
— disclosed at (BE-93)(iii). **(3)** Irreducibility of the **full** `Base` at
a cycle component of length `≥ 5` is **not** proved: the measured full tangent
rank at the collinear witness says that stratum makes no component, but other
strata are not enumerated. `Base°` is unaffected, and `G` puts the consumer
there. **(4)** A `B_real` component of cyclomatic number `≥ 2` is covered by **no**
clause here — measured `0 / 78 564` on the class, `22 / 10 678` off it.
**(5)** Nothing here touches the *chains over* the base — (BE-30)'s
ear content, the proviso `G`'s own nonemptiness, or (BE-67)(iii).

**Untouched.** `PencilPair K 3 G`, `hbareSplit`, `hK`, (BE-14)-for-all-`G`,
S-mark, the 2-cut composition lemma, (BE-32)(+), BWIN's window theorem,
(GR-15), class uniformity, (K-res). **Not a PENCIL event.**

### Verification

`python3 notes/scripts/w4/bbase.py validate` (13 s), five modes; the full
tiers are `census` (43 s) and each of `dim` / `forest` / `tri` / `cross`
(`< 1 s` each), all within one foreground budget.

- **`census`** — the `B_real` census and job 2. **CLASS TIER:** the K4
  skeleton **exhaustively** (every branch-length profile in `[1,6]^6` at sum
  `18`, the skeleton's own tightness equation), certified by
  `gridcol.class_shape` — `1 163` class members, `53 952` peel pieces over
  every 2-cut; plus prism and K33, `400` sampled `Λ ≠ ∅` length tuples each of
  `140 142` at sum `24` — `175` and `268` members, `9 718` and `14 894`
  pieces. **`B_real` a forest at 78 564 / 78 564; chart-`hcard` failures
  0 / 78 564; `Δ(B_real) = 3` at 737; girth of the member `≥ 7` at
  1 606 / 1 606.** The transport identity of (BE-93)(i) is **asserted per
  vertex** at every piece. **OFF-CLASS CONTRAST** (`bpeel.constructed_tier`,
  not class-filtered): `10 678` pieces, forest at `10 274`, with `118`
  triangle and `68` 4-cycle components and `36` `hcard` failures — so the
  reducible shapes are reachable one step off the class and unreached on it.
- **`dim`** — (BE-89)(i) at `19/19` shapes: exact-ℚ Jacobian rank
  `= |W| + 2|E|` and flag dimension `= 5|W| − 2|E|`. Plus one **harness
  datum, reported not claimed**: at the theta the landed
  `bdecor.flag_assignment` lands **off** `U` at `30/30` draws — every one
  legal, every one of tangent dimension `14 > 13` — so the theta's `U`-point
  is **constructed**, not sampled.
- **`forest`** — (BE-90): `25/25` smooth fibre points; the constructed
  `Π₂ = Π₁` singular point, legal, tangent `9 > 8`; path bases built by the
  tower at `m = 2..7`, `6/6`; and reading (3)'s coincidence `p₁ = p₂`
  constructed `25` times, every one legal and smooth on the same component.
- **`tri`** — (BE-92): the triangle identity at `200/200` draws on `U`; the
  constructed collinear witness (legal, planes pairwise distinct, tangent
  `10 > 9`); the stratum as a family `40/40`; the `m = 3..8` table with the
  tangent dimension **measured** at each; and the **F13 adversarial pair** —
  the `U` gate must *reject* the collinear witness (it does) while bare
  legality accepts it, with the generic triangle as the negative control
  (both accept).
- **`cross`** — `16/16` flag assignments drawn by the **landed**
  `bdecor.flag_assignment` on the seven `R_BATTERY` pieces plus the nested
  piece satisfy (BE-65)(i) verbatim, lie in `Base°`, and are smooth points of
  the `5|W| − 2|E|` component. The `B_real` shape of each piece is printed —
  which is how the two 4-cycle battery pieces of (BE-92)(iii) were found.

**Figure-invariance gate (`notes/scripts/README.md`).** This commit **adds**
`notes/scripts/w4/bbase.py` and modifies **no** tracked driver, so the gate
discharges by that check alone: `git diff --name-only -- '*.py' '*.m2'` is
empty and `git status --porcelain notes/scripts/` shows the one addition. No
existing figure can have moved.

### Caps, disclosed rather than smoothed — with the denominator named

1. **The class tier is `gridcol.class_shape`-certified and skeleton-capped.**
   K4 is **exhaustive** at `[1,6]^6`, sum `18`; prism and K33 are **sampled**,
   `400` of `140 142` `Λ ≠ ∅` length tuples each, `[1,5]^9` at sum `24`.
   Every prism/K33 figure is evidence about that sample.
2. **All three tiers have `≤ 6` hubs.** With girth `≥ 7` measured at
   `1 606/1 606`, a `B_real`-cycle would need length `≥ 7 > 6`, so **no tier
   here can exhibit one**. The `78 564 / 78 564` forest figure is therefore a
   cap-boundary fact about these tiers, **not** evidence that the class has no
   `B_real` cycle.
3. **`Δ(B_real) ≤ 4` is an argument; `Δ(B_real) = 3` at 737 is a
   measurement.** No piece here realized `Δ = 4`; that is a *none-found under
   this cap*, not a nonexistence.
4. **The off-class contrast is `bpeel.constructed_tier(maxlen=3, nsamp=200)`**
   — the K4 profiles exhaustively at branch lengths `1..3` plus `200` seeded
   prism/K33 profiles — not a census of non-class pieces.
5. **`dim`, `forest` and `tri` are one exact-ℚ draw per row** (or the stated
   `25` / `200` / `40`). A full-rank Jacobian at one point is a **proof** for
   that point and a **generic** statement only via the tower; the tower is the
   proof, and the draws are the check on the count.
6. **Only the constructed witnesses are load-bearing in `tri`.** The
   collinear stratum is *constructed*, per §4 convention 6's preference: it
   does not depend on a seed and survives a change of sampler. So is the
   theta's `U`-point, for the reason the `dim` datum records.
7. **The `22` cyclomatic-`≥ 2` components are over the off-class contrast
   only**, and the `0` is over the three class tiers, whose own cap is
   item 2.

### Harness note — the `kbare/` sibling-import set gains its NINETEENTH consumer

`bbase.py` imports `bdecor` / `bpeel` / `bimage` / `gridcol` / `cflank` /
`kbare_common` (and `exactcore`) **read-only**, and reimplements nothing: the
hub set and branches come from `bdecor.hubs_and_branches`, `B_real` from
`bdecor.hub_adjacency`, the flag sampler from `bdecor.flag_assignment`, the
peel from `bpeel.split_at_pair`, the class filter from `gridcol.class_shape`
and the length tuples from `cflank.length_tuples`. It is the first `w4/` driver
to import **both** `gridcol`'s class filter and `bpeel`'s peel machinery, which
is what makes the class-tier census possible at all. **No move made**, per the
standing rule.

### Confidence verdicts, per claim

| claim | verdict |
|---|---|
| (BE-89)(i) complete intersection, `5\|W\| − 2\|E\|` | **proven**; exact-ℚ Jacobian at 17/17 shapes |
| (BE-89)(ii) the base factors over components | **proven** (one edge per equation) |
| (BE-89)(iii) it is not `𝒜(B_real)`; (CH-1) inapplicable | **proven** (off §(K-chart) *Step CH1*'s own hub set) |
| (BE-89)(iv) stages 1–2 only; nonempty unconditionally | **proven** |
| (BE-90)(i) `F_Π` irreducible of dimension 3 | **proven-informally**; smoothness measured 25/25 |
| (BE-90)(ii) the forest theorem | **proven-informally** (tower + homogeneity) |
| (BE-90)(iii) reading (3) corrected | **proven**, plus 25 constructed coincidence witnesses |
| (BE-91)(i) the point-first bundle at `Δ ≤ 2` | **proven-informally** ((CH-3)'s arithmetic, `d_z ≤ 2`) |
| (BE-91)(iii) the unicyclic corollary | **proven-informally** ((BE-90)(i) + open-subset-of-irreducible) |
| (BE-91)(ii) `U` = `G`'s hinge-coincidence half | **proven** (off `binduc.assert_generic_star`, and (CH-6)(iv)) |
| (BE-92)(i) the triangle identity | **proven**; 200/200 on `U` |
| (BE-92)(ii) reducible at `m = 3, 4` | **proven** (dimension + separation); witnesses **constructed** exact-ℚ |
| (BE-92)(iii) girth excludes it on the class | **proven** given (FR-15)'s girth row, which is **cited** |
| (BE-93)(i) `hcard` transports; the excess identity | **proven**; the `≤ 2` input **cited at one remove** (Lean hold); identity asserted at 78 564 pieces |
| (BE-93)(ii) the consumer table | **verdict on the consumer**, not a theorem |
| (BE-93)(iii) residue two → one | **verdict**, with its two caveats disclosed |
| `B_real` a forest on the class | **measured**, 78 564/78 564, **cap-bounded** (see *Caps* 2) |
| cyclomatic `≥ 2` uncovered; 0 on class, 22 off | **measured**; the gap is an **argument**, not a witness |

### What would change this

- **A class shape with a `Λ`-cycle of length `≥ 7` all of whose vertices sit
  in one piece's `W`.** Then `B_real` has a cycle on the class. It changes
  nothing about freeness — (BE-91)(i) covers it on `Base°`, and `G` puts the
  consumer there — but it would retire the *"forest at 78 564/78 564"* reading
  and make (BE-91) rather than (BE-90) the load-bearing clause. The first
  place to look is a skeleton with `≥ 7` hubs.
- **A consumer that needs the FULL `Base`, not `Base°`.** (BE-91)(ii) says
  none of (BE-64)–(BE-67)'s do, because they all carry `G`. A consumer that
  dropped `G` would meet the reducibility at a cycle component directly.
- **(FR-15)'s girth row being wrong.** Everything class-level in (BE-92)(iii)
  rides on `girth(G′) ≥ 6`. The forest theorem and the `Base°` bundle do not.
- **A `B_real` component of cyclomatic number `≥ 2`.** Zero of `78 564`
  class-tier pieces have one; `22` of `10 678` off-class pieces do. It is the
  one shape neither (BE-90)(ii) nor (BE-91)(i)/(iii) reaches, and the theta
  datum says the expected dimension survives there, so the missing piece is
  an argument that `U`'s determinantal point locus is irreducible.
- **A `B_real` with `Δ = 4`.** Combinatorially possible ((BE-93)(i)), not
  realized here. It would put the point stage on a codimension-`2`
  determinantal locus; the forest theorem still covers it if the component is
  a tree, and it is exactly the case where neither clause applies if it is
  not.

### TERMINATION riders

**E1 / E2 / E3 — reported, never fired; E3 remains ARMED (by GBAL).** Read
against their actual definitions in `notes/pencil/fanout-archive.md`, with the
2026-09-02 correction (`61e046a6`) in force: **"the target" in E1–E3 is the
ARC's target, `PencilPair K 3 G`**, never a direction's local obligation. The
corpus carries **two** E3 texts; **this reading is `:1700`'s two-conjunct
form** (*the target is proven **and** every remaining ledger entry is
adjudication-gated*), with `:2098`'s deliberate one-conjunct deviation (*the
target is proven — full stop*) noted and **not** used. The further wrinkle
WGROW recorded holds on inspection: **E2's literal text says "the direction's
target"** (`:1697`) while **E3's says "the target"** (`:1700`), so the standing
correction is to **E2's letter**, not a restatement of it.

- **E1** — a g-flank, i.e. a `D = 0` shape whose every admissible colouring is
  binding. **Does not fire**: nothing here is about colourings, and no g-flank
  was exhibited.
- **E2** — the arc's target refuted or unprovable-as-posed **and** no ledger
  entry left open-with-a-named-dispatchable-attack. **Does not fire on either
  conjunct**: `PencilPair K 3 G` is neither refuted nor unprovable-as-posed,
  and the ledger gains dispatchable room rather than losing it (half (B)'s
  residue is now the single item (BE-67)(iii), which is dispatchable).
- **E3** — the arc's target proven **and** every remaining entry
  adjudication-gated. **Does not fire on either conjunct**: `PencilPair K 3 G`
  is not proven, and (BE-67)(iii) is dispatchable, not gated.

**F11** is honoured in the direction that matters: every *"free"*,
*"irreducible"* and *"the only obstruction"* here is carried by an **argument**
((BE-90)(ii), (BE-91)(i), (BE-92)(ii)'s dimension count), with the drivers
checking counts rather than establishing exhaustiveness — and the one
none-found claim (`Δ = 4` unrealized) is disclosed as such with its
denominator. **F12** is paid at source: (BE-65)(i) and (BE-68)(ii) item 1 are
annotated where they stand. **F21**: the `(K-bare)` gap-map row is
**recomputed to a target**, with label preservation verified by a scripted
set-diff. **The convergence the spec asked about** — `K₂,₃` on both threads —
is **not** built: nothing in this direction reaches `K₂,₃`, and manufacturing a
connection is what the rider forbids.

**Reservation, and what is returned.** Labels **(BE-89)–(BE-93)** and
***Steps BE88–BE92*** were reserved and are **consumed in full**; nothing is
returned. The driver `w4/bbase.py` landed at the reserved path. No new
configuration-level object needed a name beyond the prose ones already in the
corpus (`B_real`, a `B_real`-component, the collinear stratum, the flag base).
