## §(K-main) — the main component `X₀`: over a fixed planar picture the pencil condition is linear in the heights, the flat rank is an exact identity in `dim L(q)`, and the census of `X₀`

Answering `notes/pencil/W4-reopen.md` **P1** (the main-component census, ranked first by the
2026-09-23 strategy re-think; nothing in it commissioned beyond that ranking). Tag `MC-`
(`notes/pencil/labels.md`). Driver: `notes/scripts/w4/maincomp.py`. The object is the smark brief's
§1 pencil configuration (`notes/attacks/smark/brief.md`), read here in an affine chart; the
derivation is the hand-off's (F1)–(F3), written out and checked. **(MC-4)** was not in the
hand-off: it makes the flat rank an exact identity rather than a citation.

**Verdict.** (MC-1)–(MC-6) and (MC-9) are *proven-informally* and elementary; (MC-1)–(MC-6) were
second-read on 2026-09-25 (with Step MC10), and the Plücker bookkeeping was checked by hand. The one citation
any of them uses, Jackson–Jordán's pin-collinear theorem (the smark brief §3(a); published, not
formalized, checked only over `ℝ` — `notes/Phase39-design.md` field-hypothesis recon, row S5; beyond `ℝ`, (MC-33)), is
needed only for the *equality* case of (MC-4)(b), and every use of it below is flagged.
**The census RAN on 2026-09-23. Its outcome is row A′ of the decision table fixed before any run**
(*The census — results*). `X₀` attains at all 10 252 members, including every simple 2EC graph on
at most 8 vertices; there are 0 `SHORT`s. At every drawn point the first-order term alone reached
the target ((MC-7), (MC-8)). The exception is nondegeneracy: at 28 distinct certified-feasible graphs, all
with a proper rigid subgraph, `X₀` supplies the distinct motive but not the generic one ((MC-9)).
The class statements (MC-10) are *open*. What follows is the PI's call.
**2026-09-24 (no census re-run), *After the census*.**
- (MC-11): the gain is **exact** at every admissible point. So (MC-8) is a theorem, and
  (MC-10)(a) ⟺ (MC-10)(b), a plane-framework statement.
- (MC-14): settles (MC-10)(c), with its converse. `X₀` is nondegenerate iff `hcard` holds and no
  `def₂`-rigid subgraph holds two hubs of a common `closedHubNbhd`. This is modulo Jackson–Jordán,
  and it is checked on all of `exh8`.
- (MC-15): `hK`'s habitat has no `def₂`-rigid subgraph at all. So there (MC-10)(a) alone would give
  `hK`'s conclusion.
- Step MC10, the ear step on `X₀`:
  - Closed ears and open ears with `k ≥ 5` are unconditional (MC-20).
  - `k = 4` is proved under strong induction (MC-24)/(MC-25).
  - So **every θ-graph attains on `X₀`** (MC-21), the first infinite class.
  - Open ears with `k ≤ 3` were left open (MC-27). **Step MC13** (a second reading, 2026-09-24)
    closes most of them with the antecedent `X₀(G′ + ear_{k−1})`: `k = 3` in every orbit (MC-45);
    `k = 2` when the generic flags are in orbit (i)/(ii) and `dim U ≠ 1` (MC-46); the chord gives
    every (R_k) (MC-44); `k = 1` at `δ ≥ 5` (MC-49), (MC-31); every short ear at `δ = 0` (MC-54). Open: (MC-51)(a)–(c) at `δ ≥ 1`. On `hK`'s
    habitat only `k = 1`, `δ ≤ 4` remains, modulo Jackson–Jordán (MC-48).
    *(2026-09-26, ORBIT recon, found by formalization and second-read the same day: on (MC-89)'s
    route the `k = 2` cell is (MC-176), through the refined link (MC-173), the parametrized
    incidence (MC-174) and (MC-175); (MC-46)'s orbit count and (MC-138) are off the route. The
    second reading added (MC-177), the path brick, and (MC-178), (MC-175)(iii) with equality.)*
    *(2026-09-27, SHORT recon, found by formalization and second-read the same day: on (MC-89)'s route the
    `k = 4` and `k = 3` steps are (MC-180) and (MC-181). Each counts against the antecedent `G` with
    `x₂` suppressed, then puts `x₂` back along a curve ((MC-179)(d)); the gain comes from a tetrahedron
    at `k = 4` and from the bilinear lemma at `k = 3`. (MC-24), (MC-136), (MC-45)'s `r`-split and
    (MC-26)'s links are off the route. Deficiency: (MC-182).)*
  - The relative-dof conjecture (MC-23) is certified on ≤ 7 vertices, and reduced to (MC-10)(a)
    at `G′` and `G′ + ab` when `a ≁ b` and `δ ≤ 5` (MC-44).
  - A second reader re-derived Steps MC7–MC9; its fixes are applied.
  - The ear-step claims (MC-16)–(MC-27) were **re-derived by a second reader on 2026-09-25**,
    with Steps MC1–MC6: nothing on (MC-89)'s path refuted; (MC-25), (MC-26) repaired in scope;
    (MC-27)'s bad set repaired; (MC-169), (MC-170) added.
- Step MC11 (from the 2026-09-24 feasibility recons of W4-reopen's unranked directions), the
  split-off step on `X₀`: putting the split vertex on the line of its neighbours gives rank exactly
  `+5` and a point of `X₀` (MC-28)–(MC-30), so **`X₀(G.splitOff)` attaining puts `X₀(G)` within one of
  its target, and attaining when `δ ≥ 5`** (MC-31); the missing `+1` is first order at every
  instance tested, not a class statement (MC-32).
- Step MC12, the contraction step on `X₀`: Katoh–Tanigawa's contraction case in `X₀` form. For a
  proper rigid `W` with `G/H` simple, **`X₀(H)` and `X₀(G/H)` attaining give `X₀(G)` attaining**,
  under two linear-algebra conditions checked per graph at one exact picture (MC-39); OPEN as class
  statements (MC-41). Every sampled run where they are certified attains (MC-40). **Second-read
  2026-09-24**: confirmed, (MC-37) steps 3–4 filled in, and at a `def₂`-rigid core Jackson–Jordán is
  needed only at `H` and `G/H` ((MC-59)(c3)), which makes the `K₄` necklaces citation-free (MC-60)(b).
- Step MC14, the reach of the `X₀` induction (`w4/x0arms.py`): cut vertices and bridge chains are
  fibre products (MC-52), (MC-53); an open ear with `k ≤ 4` at `δ = 0` needs no antecedent (MC-54),
  closing (MC-51)'s cells there; a `def₂`-rigid core needs no contraction certificate, modulo
  Jackson–Jordán (MC-59), so **every `K₄` necklace attains on `X₀`** (MC-60), with no citation at all
  since the second reading. **Every tested graph is
  covered** — all 7 980 simple 2EC graphs on ≤ 8 vertices (MC-57), every census population (MC-58),
  `N(3..8)` — **but that is a measurement: there is no coverage theorem** (MC-61). Proving one, both
  its structural and its certificate half, is the remaining problem for this strategy. Second-read
  2026-09-24: (MC-52)–(MC-55) and the `a ≁ b` reading confirmed; (MC-22) and (MC-55)(iii) repaired.
- Step MC15, the per-graph certificates as partition counts, modulo Jackson–Jordán: `dim U = min(δ₂, 3)`
  (`a ≁ b`) and the generic flag orbit is combinatorial (MC-62)–(MC-64); CONTRACT's (i) core-free is
  exactly the additivity `def₂(G) = def₂(H) + def₂(G/H)`, which also gives (ii) (MC-68), (MC-69), so
  **CONTRACT needs no per-graph certificate** at an additive core (MC-71), and additivity is automatic
  at a maximal proper rigid `W` with `G/H` simple outside one exceptional case (MC-70). Second-read in
  full (2026-09-24 and 2026-09-25): no gap; (MC-64)'s Case 2 gained a missing merge step; (MC-159)–(MC-161)
  added.
- **Step MC16, the structural half and the coverage theorem, modulo Jackson–Jordán** (second-read
  2026-09-24 by two readers; confirmed, with minor repairs). Maximal `def₂`-rigid sets have simple
  quotients (MC-75), which leaves the sparse class 𝒮 (MC-76). There every chain is usable except in
  two cells (MC-79), and Theorem S (MC-80) supplies a proper rigid core with a simple quotient
  wherever no chain is usable. Every such core is additive (MC-87), so (MC-71) applies. Hence
  **(MC-89): every graph satisfying (H) is covered, and (MC-10)(a) holds modulo Jackson–Jordán.**
  Also `δ₂ = 1 ⟹ δ ≤ 1` (MC-88), which closes (MC-51)(a) for `a ≁ b`. Stuck families exist (MC-83),
  (MC-84), so CONTRACT at cores with `def₂(H) > 0` is necessary.
- Steps MC17 and MC18, the ear cells (not on (MC-89)'s path; not yet second-read). Relative
  deficiency is a minimum over induced subgraphs (MC-90), so `δ₂ ≤ 2 ⟹ δ ≤ δ₂` (MC-91). For `a ∼ b`
  the triangle is the chord gadget (MC-94), which closes cell (a′) (MC-105). (MC-50)'s gap is closed
  and its reduction is a theorem (MC-108)–(MC-110). Every ear cell closes except (MC-117): `k = 1`,
  `δ₂ = 3`, `δ ∈ {3, 4}`, where the chord criterion fails. Closing it would give a second proof of
  (MC-89), by the EAR route in 𝒮. The (MC-26) erratum is (MC-97).
- **Step MC19, the generic motive** (second-read 2026-09-25; repaired in place, (MC-157), (MC-158) added). Feasibility means (F1) every hub has
  `≤ 2` hub neighbours and (F2) no triangle holds two hubs (MC-123). The hub-plane chart `Z(G)`
  carries every nondegenerate realization (MC-124). The generic motive reduces, with no
  hypothesis, to feasible graphs with no `def₂`-rigid subgraph (MC-130), where it is (MC-10)(a).
  With (MC-89): **every feasible simple connected graph of minimum degree `≥ 2` has the generic
  pencil motive, modulo Jackson–Jordán, in characteristic 0 (MC-133).** And every simple graph
  satisfying (H), feasible or not, has `HasDistinctPencilRealization`, modulo Jackson–Jordán, in
  characteristic 0 (MC-157). *2026-09-28 (MOTIVES recon, found by formalization; second-read the
  same day, confirmed with repairs, (MC-188) and (MC-189) added):* route B, (MC-183)–(MC-189): the generic motive inside the pencil reduction's induction, the
  planned fibre route refuted at two hubs with three common neighbours (MC-187). *2026-09-29 (EARS
  recon, found by formalization; landed and second-read the same day, confirmed with repairs,
  (MC-193) added):* (MC-190)–(MC-192), the steering and the pendant triangle in the forms the Lean
  proves.
- **Step MC20** (second-read 2026-09-25, confirmed with repairs; the argument leaves audited for
  characteristic, (MC-166); (MC-167), (MC-168) added): every computational certificate under (MC-89) has a hand proof
  over every infinite field (MC-134)–(MC-139), so (MC-89) rests on arguments and Jackson–Jordán
  alone (MC-141).
- **Step MC21** (second-read 2026-09-25, confirmed with repairs; (MC-162)–(MC-165) added; off (MC-89)'s critical path): **EAR alone covers 𝒮** (MC-148),
  a second proof of (MC-89)'s in-𝒮 half without Theorem S, (MC-87) or CONTRACT at cores with
  `def₂(H) ≥ 1`. It still uses the reduction to 𝒮, the landed usable steps, (MC-68)(d) and Jackson–Jordán, and (MC-105) (Step MC17). The engine
  is the rigid-set closure (MC-143), fed by a count (MC-146), (MC-147). The last ear cell (MC-117)
  narrows to "Case II-cyclic" (MC-154), which coverage does not need.
- *Jackson–Jordán beyond `ℝ`* (MC-33): a second reading finds every step of their proof field-free
  after two small repairs and one bypass (`INFORMAL`), and `jjchar.py` exhibits (MC-4)(b)'s
  equality in characteristics 2, 3, 101 and 10 007 at every simple 2EC graph on ≤ 8 vertices.
**What would change this:** an admissible `q` where `maincomp.py`'s (MC-4) assert fires (the
identity is false), an error in the Plücker bookkeeping of *Step MC3* (checked per instance by the
(MC-3) assert), or a `SHORT` in an extended population.

**Standing hypotheses (H).** `G` is finite, simple and connected, with minimum degree `≥ 2`. `K` is
an infinite field. A **planar picture** is `q : V → K²`, `q_v = (x_v, y_v)`; it is **admissible**
if `q_u ≠ q_v` for every edge `uv` and `q(N[v])` is not collinear for every `v` (`|N[v]| ≥ 3` by the
minimum degree). A configuration in the affine chart is `p_v = (x_v, y_v, z_v, 1) ∈ K⁴`, written
`p = (q, z)` with `z ∈ K^V` the **heights**. `Aff(q) ⊆ K^V` is the 3-dimensional space of heights
`z_w = αx_w + βy_w + γ`, the restrictions of global affine functions (dimension 3 because an
admissible `q` is not collinear).

---

### File index

Steps MC10–MC21 live one file per step (`K-main-MC10.md` …
`K-main-MC21.md`), picked up by the `workbook/*.md` glob in
`notes/ledger.py`. Each opens with a `## §(K-main) — Step MCnn — …`
heading, so every claim keeps section key `§(K-main)` (the ledger keys a
section on its `§(…)` token, never the heading text). This file
(`K-main.md`) carries the header above, Steps MC1–MC9 below, and the
Literature section at the end.

- `K-main-MC10.md` — Step MC10 — the ear step on `X₀` (P3 Track 1)
- `K-main-MC11.md` — Step MC11 — the split-off step on `X₀` (Jackson–Jordán's Claim 6.5 Case 1, transferred); also carries “Jackson–Jordán beyond ℝ — a second reading (2026-09-24)”
- `K-main-MC12.md` — Step MC12 — the contraction step on `X₀` (W4-reopen P1, option 2)
- `K-main-MC13.md` — Step MC13 — the short ear step with the antecedent (a second reading of (MC-27))
- `K-main-MC14.md` — Step MC14 — which graphs the `X₀` induction reaches (W4-reopen P1, step 4)
- `K-main-MC15.md` — Step MC15 — the per-graph certificates are partition counts (modulo Jackson–Jordán)
- `K-main-MC16.md` — Step MC16 — the structural half, and the coverage theorem (modulo Jackson–Jordán)
- `K-main-MC17.md` — Step MC17 — relative deficiency, the triangle gadget for `a ∼ b`, and most of the ear cells (modulo Jackson–Jordán)
- `K-main-MC18.md` — Step MC18 — the chord point, and the ear route's last open cell (modulo Jackson–Jordán)
- `K-main-MC19.md` — Step MC19 — the generic motive: feasibility, the hub-plane chart, and the reduction to (MC-10)(a)
- `K-main-MC20.md` — Step MC20 — the coverage theorem's certificate leaves, proved by hand over every field
- `K-main-MC21.md` — Step MC21 — the rigid-set closure: EAR alone covers 𝒮, and the last ear cell narrows to Case II-cyclic (modulo Jackson–Jordán)

---

### Step MC1 — the pencil condition is linear in the heights

> **(MC-1)** `[PROVED]` *(the hand-off's (F1))* Let `q` be admissible. Then `p = (q, z)` has every
> closed neighbourhood coplanar **iff** `z ∈ L(q)`, where
> `L(q) := {z ∈ K^V : for every v, z|N[v] is the restriction to q(N[v]) of an affine function of K²}`.
> Every such `p` is a pencil configuration: adjacent points are distinct, and the plane `π_v` is unique
> and non-vertical at every vertex. `L(q)` is a linear subspace containing `Aff(q)`.

*Proof.* (⇐) If `z_w = α_v x_w + β_v y_w + γ_v` on `N[v]`, the points of `N[v]` lie on the plane
`z = α_v x + β_v y + γ_v`. (⇒) Let `ax + by + cz + d = 0` contain `N[v]`'s points. If `c = 0` then
`ax + by + d` vanishes on the non-collinear set `q(N[v])`, forcing `a = b = d = 0`. So `c ≠ 0` and
`z = −(ax + by + d)/c` on `N[v]`. The plane is unique because `q(N[v])` is not collinear. Adjacent
points are distinct because `q_u ≠ q_v`. Linearity: the condition at `v` says `z|N[v]` lies in the
image of the evaluation map `Aff(K²) → K^{N[v]}`. That map is injective (non-collinear), so the
image is a 3-dimensional subspace, of codimension `deg v − 2`. ∎

So `dim L(q) ≥ max(3, 3|V| − 2|E|)`. Only hubs impose conditions: `deg v − 2 = 0` at a degree-2 vertex.

### Step MC2 — the main component `X₀`

> **(MC-2)** `[PROVED]` *(the hand-off's (F2))* Let `ℓ₀` be the minimum of `dim L(q)` over
> admissible `q`, and let `U` be the set of admissible `q` with `dim L(q) = ℓ₀`. Then `U` is a
> nonempty Zariski-open subset of `K^{2V}`, `B := {(q, z) : q ∈ U, z ∈ L(q)}` is a vector bundle over
> `U`, and its closure `X₀` is irreducible of dimension `2|V| + ℓ₀`. `X₀` contains the **flat
> configurations** `(q, 0)`, `q ∈ U`. Rank is lower semicontinuous, so the maximum of the molecular
> rank over `B` is attained on a dense open subset of `B`. One point of `B` at the target rank
> therefore proves that `X₀`'s generic point attains. It also gives, at `G`, a rank-attaining pencil
> configuration with adjacent points distinct: the rank and distinctness content of
> `HasDistinctPencilRealization K 3 G`, via the rank bridge (smark brief §3.3(a)).

*Proof.* Admissibility is a finite conjunction of non-vanishing conditions (`q_u − q_v ≠ 0`, a
nonzero `3 × 3` minor of `[1, x_w, y_w]_{w ∈ N[v]}`), so it is open. It is nonempty because `K` is
infinite. By (MC-1), over an admissible `q`, `L(q)` is the projection to `z` of the kernel of the
matrix `M(q)` of the linear system `z_w = h_v(q_w)` (`v ∈ V`, `w ∈ N[v]`) in the unknowns `(z, h)`,
`h_v ∈ Aff(K²)`. The projection is injective because `h_v` is determined by `z` on the
non-collinear `q(N[v])`. `M(q)` has entries linear in `q`, so `rank M(q)` is lower semicontinuous
and `U` (maximal rank) is open. On `U` the rank is constant, so the kernel is a vector bundle.
Its total space is irreducible because `U` is. The zero section lies in `B`. The last two sentences
of the claim are semicontinuity on the irreducible `X₀`. ∎

A point `(q, z)` with `q` admissible but `q ∉ U` is still a pencil configuration by (MC-1), so it is
still a witness for the conjecture at `G`, but it lies on a jump stratum and is not certified to be
on `X₀`. The driver certifies `q ∈ U` through (MC-4)(b): `dim L(q) = 3 + def₂` is the least value
`dim L` can take, so at such a `q` we have `ℓ₀ = 3 + def₂` and `q ∈ U`.

For the **generic** motive the point must also satisfy `IsNondegPencilRealization`'s four
conjuncts (`Motive.lean`, `IsNondegPencilRealization`). On `B`, conjunct 1 (the panel realization),
conjunct 2 (adjacent points distinct) and conjunct 4 (closed neighbourhoods of non-hubs
independent: three non-collinear points) hold by (MC-1). **Conjunct 3** (the normals of
`closedHubNbhd v` linearly independent) is not automatic on `X₀`. The census reports it per
instance.

### Step MC3 — the hinges are affine in the heights

> **(MC-3)** `[PROVED]` *(the hand-off's (F3))* For fixed `q`, the hinge extensor
> `C_e = p_u ∧ p_v` of an edge `e = uv` is affine in `z`. In the Plücker order `(01, 02, 03, 12, 13, 23)`
> of `exactcore.PL`,
> `C_e = (x_u y_v − y_u x_v, 0, x_u − x_v, 0, y_u − y_v, 0) + (0, x_u z_v − z_u x_v, 0, y_u z_v − z_u y_v, 0, z_u − z_v)`,
> and the second term is linear in `z`. Hence the **augmented motion matrix** `A(q, z)` (rows `(e, k)`:
> `(m_u − m_v − ω_e C_e)_k`; columns `6|V| + |E|`) is `A₀(q) + A₁(q; z)`, with `A₁` linear in `z` and
> supported on the `ω` columns. If every `C_e ≠ 0`, then `rank A = |E| + rank R`, where `R` is the
> 5-rows-per-hinge rigidity matrix (the landed `rigidityRows` model, `kbare_common.build_rigidity`).
> The rank at `(q, z)` is invariant under `z ↦ tz + a` for `t ≠ 0` and `a ∈ Aff(q)`, so on the fibre
> it depends only on the class of `z` in `P(L(q)/Aff(q))` when `z ∉ Aff(q)`; at `z ∈ Aff(q)` it is the
> flat rank. *(Scope added at the second reading, 2026-09-25.)*

*Proof.* `p = (x, y, z, 1)`. Each Plücker coordinate `p_u[i] p_v[j] − p_u[j] p_v[i]` has at most one
of `i, j` equal to `2` (the `z` index), so it has no `z_u z_v` term. On `ker A`, `ω_e` is determined
by `m` whenever `C_e ≠ 0`. So `ker A ≅ {m : m_u − m_v ∈ span C_e for all e} = ker R`, and
`rank A = 6|V| + |E| − dim ker R = |E| + rank R`. The map `(x, y, z) ↦ (x, y, tz + αx + βy + γ)` is an
affine, hence projective, transformation of `K³` when `t ≠ 0`, and the molecular rank is
projectively invariant. ∎

The quadric condition on hinge lines (the Klein quadric) never appears: the parametrization by
`(q, z)` absorbs it, and the rank question over a fixed `q` is the generic rank of an affine matrix
family over the linear space `L(q)`. The last sentence of (MC-3) says the fibre is effectively
`P^{ℓ₀ − 4}`. Under Jackson–Jordán (MC-4(b)) that is `P^{def₂ − 1}`: at `def₂ = 1` (for example `C₄`)
every non-flat point of the fibre has the same rank.

### Step MC4 — the flat rank is an identity in `dim L(q)`

> **(MC-4)** `[PROVED]` Under (H), at every admissible `q`:
> **(a)** `rank R(q, 0) = 6|V| − 3 − dim L(q)`, exactly;
> **(b)** `dim L(q) ≥ 3 + def₂(G)`, where `def₂(G) = max_P [3(|P| − 1) − 2d(P)]` (Lean `deficiency G 2`);
> **(c)** hence `rank R(q, 0) ≤ 6(|V| − 1) − def₂(G)`, with **equality iff `dim L(q) = 3 + def₂(G)`**.
> The corpus's flat law `rank(flat) = 6(|V|−1) − def₂` (§(K-bare-ext) (BE-20)(ii), inheriting
> (BE-13); the smark brief §3(a)) is therefore **exactly** the statement that equality holds in (b)
> at generic `q`. That equality is where the Jackson–Jordán theorem enters, and it is the only place.

*Proof.* At `z = 0`, (MC-3)'s formula puts every `C_e` in `W_Π := span(e₀₁, e₀₃, e₁₃)`, the Plücker
coordinates of lines in the plane `Π = {z = 0}`. Split `K⁶ = W_Π ⊕ W′`, with
`W′ = span(e₀₂, e₁₂, e₂₃)`, and write `m_v = (m_v^Π, m_v′)`. The motion condition
`m_u − m_v ∈ span C_e` splits into `m_u′ = m_v′` (three conditions) and
`m_u^Π − m_v^Π ∈ span C_e` (two conditions, since `C_e ≠ 0`).
*The glued block.* Because `G` is connected, `m′` is constant: a 3-dimensional contribution to the
kernel.
*The 2-condition block.* `W_Π = Λ²Π̂` with `Π̂ = span(e₀, e₁, e₃) ≅ K³`, and `p̂_w = (x_w, y_w, 1)`.
Identify `Λ²K³ ≅ (K³)^∨` by `a ∧ b ↦ det(a, b, ·)`, and `(K³)^∨` with the affine functions `h` on
`K²` (`h(x, y) = ⟨h, (x, y, 1)⟩`). Under this identification `span(p̂_u ∧ p̂_v)` is the line of affine
functions vanishing at `q_u` and `q_v`. So the block's kernel is
`F(q) = {(h_v)_v : (h_u − h_v)(q_u) = (h_u − h_v)(q_v) = 0 for every edge uv}`.
*The bijection `F(q) ≅ L(q)`.* Define `Φ(h)_w := h_w(q_w)`. For `u ∈ N(v)`: `Φ(h)_u = h_u(q_u) = h_v(q_u)`,
and `Φ(h)_v = h_v(q_v)`. So `Φ(h)|N[v] = h_v|q(N[v])` is affine, and `Φ(h) ∈ L(q)`. Conversely, for
`z ∈ L(q)` let `Ψ(z)_v` be the unique affine interpolant of `z` on the non-collinear `q(N[v])`. For an
edge `uv`, both `q_u` and `q_v` lie in `N[u] ∩ N[v]`, so `Ψ(z)_u` and `Ψ(z)_v` agree there, and
`Ψ(z) ∈ F(q)`. The composites are the identity: `Φ∘Ψ` by construction, `Ψ∘Φ` by uniqueness of the
interpolant. Hence `dim ker R(q, 0) = 3 + dim L(q)`, which is (a).
*(b).* The 2-condition block has 3-dimensional bodies and 2 rows per edge. For a partition `P`, the
rows of edges inside a part vanish on part-wise constant `h` (a `3|P|`-dimensional space), so they
have rank `≤ 3|V| − 3|P|`. The crossing edges contribute `≤ 2d(P)`. So
`dim F(q) ≥ 3|P| − 2d(P) = 3 + [3(|P| − 1) − 2d(P)]`; maximize over `P`.
*(c)* is (a) and (b) together. ∎

The bijection `Φ` is the classical correspondence between liftings of a plane picture and
motions of its dual framework: the projective duality of Maxwell–Cremona and scene analysis
(Whiteley; Crapo–Whiteley). **Citation to be verified before transcription.** The proof above is
self-contained and does not use it.

### Step MC5 — consequences, none of which uses Jackson–Jordán

> **(MC-5)** `[PROVED]` Under (H):
> **(i)** `def₃(G) ≤ def₂(G)`. Partition by partition, `[6(|P|−1) − 5d] − [3(|P|−1) − 2d] =
> 3(|P| − 1 − d(P)) ≤ 0`, because the parts of a connected graph are joined by `≥ |P| − 1` crossing
> edges. (This is BZAVOID's `def₂ ≥ def₃`, §(K-bare-ext) (BE-15); recorded here with its one-line
> proof because (ii) uses it.)
> **(ii)** The flat configuration at an admissible `q` attains `6(|V|−1) − def₃` **iff**
> `dim L(q) = 3 + def₃`, iff equality holds in (MC-4)(b) at `q` **and** `def₂ = def₃`.
> **(iii)** *(the W4-reopen "dichotomy worth trying to prove", on `X₀`)* If `X₀` is **flat** — that
> is, `ℓ₀ = 3`, so every configuration of `B` is planar — then `def₂ = def₃ = 0`, and the flat
> configuration at every admissible `q` with `dim L(q) = 3` has rank `6(|V| − 1)`: `G` is rigid, and
> `X₀` attains.

*Proof of (ii), (iii).* (ii): (MC-4)(a) gives flat rank `= 6|V| − 3 − dim L(q)`, which equals
`6(|V| − 1) − def₃` iff `dim L(q) = 3 + def₃`. By (MC-4)(b) and (i), `dim L(q) ≥ 3 + def₂ ≥ 3 + def₃`.
(iii): `ℓ₀ = 3` and (MC-4)(b) give `def₂ ≤ 0`, so `def₂ = 0`, and `def₃ = 0` by (i). Then
(MC-4)(a) gives flat rank `6|V| − 6`. ∎

**What (MC-5)(iii) does to §(K-bare-ext) (BE-23)(ii).** BINDUC measured *"forced flat ⇒
`def₂ = def₃`"* under an *aggressive* combinatorial plane-forcing closure. It reported the largest
`def₂` at a forced-flat graph as **5**, and flagged the closure as over-claiming. (MC-5)(iii) proves
the `X₀` form outright: flatness of `X₀` forces `def₂ = 0`, not merely `def₂ = def₃`. Any graph a
forcing closure flags as flat with `def₂ > 0` therefore has **non-flat** configurations on `X₀`,
because `dim L(q) ≥ 3 + def₂ > 3` at every admissible `q`. Such a flag is an over-claim of the
closure, as BINDUC said it might be. That section's statement is not changed; its measured
*"forced flat ⇒ `def₂ = def₃`"* is subsumed on `X₀`.

**The by-product for (α), restated with its dependency.** The W4-reopen hand-off's by-product —
*"wherever `def₂ = def₃` the flat configuration already attains with adjacent points distinct"* —
is (MC-5)(ii) **plus Jackson–Jordán at `G`**. Without the citation, what holds is: wherever
`dim L(q) = 3 + def₃` at some admissible `q`, the flat configuration at `q` attains with adjacent
points distinct. The census measures that equality directly (the `JJ` column).
*(2026-09-26, BRIDGE recon: the by-product is now unconditional over every infinite field, by
(MC-172) (Step MC11). Lean `Graph.x0Attains_of_deficiency_two_eq_three`, `cor:pencil-jj-flat`.)*

### Step MC6 — the first-order structure at the flat point is a symmetric form on the lifting space

*Written after the spec commit `9e8aaec2`, while the census ran.* It changes no row of the decision
table.

At `(q, 0)` the motion space is the glued block (3 dimensions, trivial) plus `F(q) ≅ L(q)`, and the
perturbation directions are `L(q)` too. The **first-order gain** in direction `z` is
`rank(S₀ᵀ A₁(z) K₀)`, with `K₀` and `S₀` the kernel and left kernel of `A₀`. It lower-bounds
`rank A(q, z) − rank A₀` (and, by (MC-11)(ii), equals it). The reason: `P(A₀ + tA₁)Q` in a basis adapted to `A₀` has Schur
complement `t(S₀ᵀA₁K₀ + O(t))`, and by (MC-3) `rank A(q, tz)` does not depend on `t ≠ 0`. The
needed gain is `def₂ − def₃`. The step below computes it.

**Notation.** An affine function `h = αx + βy + γ` is written as the vector `ĥ = (α, β, γ)`, so that
`h(q_w) = ĥ · p̂_w` with `p̂_w = (x_w, y_w, 1)`. For an edge `e = (u, w)` (in `edges` order), set
`ℓ_e := p̂_u × p̂_w ≠ 0`. A flex `h ∈ F(q)` has `ĥ_u − ĥ_w = ω_e(h) ℓ_e`. `Z₁(G)` is the cycle space
(signed edge vectors, zero net flow at every vertex).

> **(MC-6)** `[PROVED]` Under (H), at an admissible `q`, define the bilinear map
> `β : F(q) × F(q) → (Z₁(G) ⊗ K³)^∨` by `β(k, h)(μ) := Σ_{e = (u,w)} det(μ_e, k̂_w, ĥ_u − ĥ_w)`.
> **(i)** `β` is **symmetric**. **(ii)** `β(k, h) = 0` whenever `k` or `h` is a trivial (constant)
> flex, so `β` descends to `Sym²(L(q)/Aff(q)) → (Z₁ ⊗ K³)^∨`. **(iii)** For `z ∈ L(q)`, the
> first-order gain in direction `z` equals `rank β(Ψz, ·)`, with `Ψ` the bijection of *Step MC4*.
> So, at `q ∈ U`, `X₀` attains **to first order** iff some `z ∈ L(q)` has
> `dim ker β(Ψz, ·) = 3 + def₃` on `F(q)`, i.e. `def₃` beyond the trivial flexes.

*Proof.* (iii) first. By the block split of *Step MC4*, the left kernel of `A₀` is the direct sum
of the 2-condition block's stresses (supported on `W_Π`) and the glued block's stresses. The
latter are `λ′ ∈ (K³)^E` with zero net flow at every vertex, i.e. `Z₁ ⊗ K³`, supported on `W′`
(the `ω`-column constraint `λ_e · C_e = 0` involves only `W_Π`). `A₁(z)` is supported on the `ω`
columns, and by (MC-3) its values `−C′_e(z)` lie in `W′`, where
`C′_e = (x_u z_w − z_u x_w, y_u z_w − z_u y_w, z_u − z_w) = J a_e`,
`a_e := z_w p̂_u − z_u p̂_w`, `J = diag(1, 1, −1)`. So only glued-block stresses pair. In `K₀`, the
trivial `W′` motions have `ω = 0` and pair to zero. What is left is
`sᵀA₁(z)f = −Σ_e ⟨Jλ′_e, a_e⟩ ω_e(h)`. With `k = Ψz`, (MC-1) gives `z_u = k̂_w · p̂_u` and
`z_w = k̂_w · p̂_w`, because `u, w ∈ N[w]`. Hence `a_e = k̂_w × ℓ_e` by `a × (b × c) = b(a·c) − c(a·b)`,
and `ω_e(h) a_e = k̂_w × (ĥ_u − ĥ_w)`. Put `μ := −Jλ′`; `J` preserves zero net flow. Then
`sᵀA₁(z)f = Σ_e det(μ_e, k̂_w, ĥ_u − ĥ_w) = β(k, h)(μ)`. The identification of the `W_Π`-coordinates
of a flex with `ĥ` is the linear map `(c₀₁, c₀₃, c₁₃) ↦ (c₁₃, −c₀₃, c₀₁)`. It sends
`C_e|_{W_Π}` to `ℓ_e`, so `ω_e` is the same scalar in both pictures.
(i). Write `ĥ_u = ĥ_w + bℓ_e` and `k̂_u = k̂_w + aℓ_e`. Then
`det(μ_e, k̂_u, ĥ_u) − det(μ_e, k̂_w, ĥ_w) = det(μ_e, k̂_w, ĥ_u − ĥ_w) − det(μ_e, ĥ_w, k̂_u − k̂_w)`,
because the `ab` term has `ℓ_e` twice. Summing over `e`, the left side is
`Σ_v det(net flow of μ at v, k̂_v, ĥ_v) = 0`. So `β(k, h)(μ) = β(h, k)(μ)`.
(ii). A constant `h` has `ĥ_u − ĥ_w = 0`. A constant `k` then follows by (i). ∎

**Checked in the driver** (`beta_check`, run whenever `--gain` is given): `rank β(Ψz, ·)` over `ℚ`
equals the Schur-pairing gain, asserted per instance. Also asserted: symmetry on two basis pairs,
and vanishing on the constant flex. This was added to `maincomp.py` after the first census runs.
The re-runs with it in place are byte-identical to those runs (*The census — results*).

**What (MC-6) is for.** The census (below) finds the first-order gain **equal to `def₂ − def₃` at
every instance tested**. If that is a theorem, the rank question on `X₀` becomes a statement
about **plane** frameworks only: for generic `q` and `z` in the lifting space, the symmetric form
`β(Ψz, ·)` on the `def₂`-dimensional space `L(q)/Aff(q)` has kernel of dimension exactly `def₃`
(it is `≥ def₃` always, by the target bound). This is the P3 candidate. It is **not** argued here.

---

### The census — spec, fixed before any census run

**Question.** On each population below, does `X₀`'s generic point attain `6(|V|−1) − def₃`?

**Instrument** (`maincomp.py`; its docstring states the sampler support per `HARNESS.md`
*Evidence*). Per draw: `q` uniform on integers in `[−30, 30]`, rejected until admissible; an exact
basis of `L(q)`; `z` a uniform `[−30, 30]` integer combination of it. The rank is computed mod
`2⁶¹ − 1`. Since `rank_p ≤ rank_ℚ ≤ target`, **`rank_p = target` is a certificate**: an exhibited
attaining point, a theorem for that graph. A shortfall is recomputed in exact ℚ and redrawn, up to
4 more draws. The best draw is a **lower bound** on `X₀`'s generic rank, never a measurement of it.
A `SHORT` verdict is therefore *measured, not proved*, and travels with its cap (5 draws, scale 30).
Asserted per draw: (MC-1) forward (every closed neighbourhood coplanar, adjacent points distinct);
(MC-3) exact affineness along the fibre (first draw of each instance); (MC-4)(a) and (b).
Reported: `def₂`, `def₃`, `dim L(q)`, the flat rank, `JJ` (`dim L(q) = 3 + def₂`, which also
certifies `q ∈ U`, *Step MC2*), the rank, and the verdict. Also reported: whether the best draw
satisfies all four `IsNondegPencilRealization` conjuncts (`flanks.nondeg_conjuncts`, failing
conjunct named) and, with `--gain`, the first-order gain of *Step MC6*.
**Oracles:** `def₃` by the (6,6) pebble game and `def₂` by the (3,3) pebble game on `2G`. Both are
checked against brute-force partition maxima at `n ≤ 8` in `--selftest`, and `def₃` also against
`kbare_common.exact_deficiency`.

**Populations** (`maincomp.py --pool NAME`). Every member is kept iff it is simple and 2EC.
Counts were measured by building each population, which involves no census run.
- `battery` (9): `C₄`, `C₅`, `C₇`, `K₄`, `K_{3,3}`, `θ(2,2,2)`, `θ(3,4,5)`, `θ(5,3,4)`, `W19`.
- `exh8` (7 980): **every isomorphism class** of simple 2EC graphs on 3–8 vertices
  (1 / 3 / 11 / 60 / 502 / 7 403). They are generated in-driver by vertex augmentation with a
  stdlib canonical form. The connected-graph counts match OEIS A001349 and the 2EC counts match
  A007146 through `n = 8` (both asserted in `--selftest`). **This is the only exhaustive
  population.** It contains every small member of every habitat below.
- `thetas` (109): `θ(a, b, c)`, `a ≤ b ≤ c`, `b ≥ 2`, `a + b + c ≤ 16`. This covers the tight
  habitat thetas (`Σ = 12`) and smark's `thetacores.py` shapes (`Σ = 13`), rebuilt with
  `pitch.theta_edges` rather than imported.
- `habitats` (888): the kernel-(K) class shapes. These are `lambda.habitat_specs` (`θ(3,4,5)`,
  `NT21`, `NT24`, `NT30`), `kslidecl.MEMBERS` (7), and the exhaustive `G* = K₄` stratum of
  `kslidecomb.py --k4full` (877 shapes).
- `smark` (81 built, 78 kept): `G = side + ear_m`, `m ∈ {2, 3, 4}`, over the 27 sides of smark's
  `splitoff.py --sides all`. They are imported read-only from `notes/attacks/smark/drivers/`
  (`sideprof`, `adversarial`, `earcompose.ear_edges`). The 3 dropped members are not 2EC.
- `residuals` (260): the 255 recorded residual inhabitants (`wtri.recorded_pool()`, the (RS-12)
  pool, `|V|` 19–31), plus `W19`, `R20`, `S29` (`saferes.w29()`), `T32` (`weloc.T32`) and `NT21c3`.
- `peels` (928): `bgenuine.family()`, `G = H₁ + H₂` (`K₄` R-sides glued to free sides). The
  392 forced-coincident-flag peels are marked, and the count is asserted.
- **W4 branch 2** (the P2 population) is not a separate list. It is the members of all the above
  that are certified infeasible (`nogood_subdiv.provably_infeasible`, a *sufficient* certificate
  only) and have a proper rigid subgraph (`nogood_subdiv.rigid_vertex_sets`). The summary lists its
  `def₂ > def₃` members; by the hand-off's P2 those are (α)'s whole content.
- **Not included, with the reason:** smark's Case-2 hub graphs (`case2m2.CASES`: D3, E13, E15,
  E55, T10, …) are reduced sides `Γ` with leaves and connectors, not graphs `G`. The corpus has no
  canonical completion of them to a full `G`, and their 2-cores are trees or hub cycles (smark
  S27(vi)). smark's `census.py` girth-`≥ 7` pieces are also left out: their kept set is replayable
  only through that driver's own rng.

Each member is also classified as `feas` (`provably_feasible`: `hcard` and triangle-free, the
landed-sufficient criterion), `infeas` or `middle`, and as `rigid` or `norigid` (a proper rigid
subgraph exists or not). These classes let the summary separate the hand-off's habitats.

**Decision table** (the hand-off's, made operational; **written before any census run**):

| outcome | condition | what follows (nothing without a PI call) |
|---|---|---|
| **A** | every instance of every population certified `ATTAINS` | P3 becomes "prove the rank on `X₀`", an architecture change; `kres`, the contraction kernels and smark's O7e become unnecessary in principle; the PI decides what to stop |
| **A′** | as A, but at some **feasible** graph the attaining draws all fail conjunct 3 | `X₀` supplies the distinct motive there but not the generic one; P3 must also produce a nondegenerate point on `X₀` or elsewhere |
| **B** | some `G` is `SHORT` after all draws, and a project chart attains at `G` (an attaining witness recorded in the corpus, or one produced by an existing sampler run on `G`) | witnesses live off the main component; every generic-point strategy dies at those `G`; they are the hard core, and P3 asks which component attains and why |
| **C** | some `G` is `SHORT` after all draws, and no chart the project has attains at `G` | a counterexample candidate. First strengthen the `SHORT` (more draws, larger scale, an exact symbolic rank if feasible), then check the special components: the admissible `q` where `L(q)` jumps, and the non-admissible charts (vertical planes) |

The census ends at this table.

**Disclosure — the order of work.** Before this spec was written, a prototype of the driver's
core (not retained; `maincomp.py` supersedes it) was run on seven named graphs: `C₄`, `K₄`,
`K_{3,3}`, `θ(2,2,2)`, `θ(3,4,5)`, `θ(5,3,4)`, `W19`. It showed `ATTAINS` and `JJ` at all seven. It
motivated (MC-4)(a), which was then proved. Those seven are re-run in the committed `--battery`
mode. No population above was run before this table was fixed.

---

### The census — results (2026-09-23): outcome **A′**

*Run after the spec commit `9e8aaec2`. Seed `20260923`, 1 draw and up to 4 retries, scale 30,
`--gain`. Commands and times: `notes/scripts/README.md` §3. The first runs used the spec-commit
driver. The figures below come from re-runs with three additions: (MC-6)'s check, the corrected
gain yardstick (the needed gain at the drawn `q`, not `def₂ − def₃`), and the genericity column.
The re-runs differ from the first runs only in those lines and the wall-clock `built in` line;
`exh8`'s first run was stopped before it finished, so it has no such comparison. The landed
driver differs from the one that ran the census pools only by docstrings and the `--draw0`,
`--jjprobe` and `--k23` modes. `battery`, `thetas` and `smark` were re-run on it byte-identically,
apart from the timing line.*

> **(MC-7)** `[CONSTRUCTED]` `maincomp.py --pool` **`X₀` attains at every member of every population:
> 10 252 members, 0 `SHORT`.** Some graphs recur across populations: `W19`, `θ(3,4,5)`, and the
> small members inside `exh8`. Each `ATTAINS` is an exhibited point of `B` at the target rank
> (the `JJ` column certifies `q ∈ U`, *Step MC2*), i.e. a proof for that graph that `X₀`'s generic
> point attains. At the 3 members whose attaining census draw failed `JJ` (2 peels and
> `x8_261840905`), `--jjprobe` exhibits an attaining point over a certified `q ∈ U` instead. With it comes a rank-attaining pencil configuration with adjacent points distinct.
>
> | population | members | `def₂ > def₃` | `X₀` attains | nondegenerate at the attaining draw | class (`feas`/`infeas` × `rigid`/`norigid`) |
> |---|---|---|---|---|---|
> | `battery` | 9 | 6 | 9 | 6 (fails conjunct 3: `K₄`, `K_{3,3}`, `θ(2,2,2)`) | 5 feas-norigid, 2 feas-rigid, 2 infeas-rigid |
> | `thetas` | 109 | 106 | 109 | 96 (13 fail conjunct 3) | 38 feas-norigid, 59 feas-rigid, 12 infeas-rigid |
> | `smark` | 78 | 78 | 78 | 78 | 65 feas-norigid, 13 feas-rigid |
> | `habitats` | 888 | 888 | 888 | 888 | 888 feas-norigid |
> | `residuals` | 260 | 260 | 260 | 260 | 260 feas-rigid |
> | `peels` | 928 | 928 | 928 | 0 (all fail conjunct 3; all infeasible) | 928 infeas-rigid |
> | `exh8` | 7 980 | 134 | 7 980 | 46 (7 934 fail conjunct 3, 7 858 of them certified infeasible) | 6 feas-norigid, 55 feas-rigid, 7 858 infeas-rigid, 43 infeas-`rigid?` (the rigid-subgraph enumeration's branch cap), 18 middle-rigid |
>
> The `exh8` row is **exhaustive**: every simple 2EC graph on at most 8 vertices has `X₀` attaining.
> That is a finite theorem, 7 980 exhibited certificates. Each certificate is over `ℚ`, so it
> proves its statement over every field of characteristic 0. Positive characteristic is not
> addressed (smark brief §2, O11). **Draw-level shortfalls:** 6 members fell short by 1 at their
> first draw and attained at a retry (`--draw0`: `θ(1,3,7)`, `pool210`, `pool218`, `pool228`,
> `T32`, `x7_1986081`). Only `x7_1986081`'s first `q` was a jump point
> (`dim L(q) > 3 + def₂`). The other five fell short at a `q ∈ U`: an unlucky `z` or `q` for a
> condition the dimension count does not see. Semicontinuity makes such draws expected, and they
> bound nothing. `JJ` failed at 4 first draws (2 peels, 2 in
> `exh8`). All four are unlucky `q`: one fresh `q` exhibits `dim L(q) = 3 + def₂` at each
> (`--jjprobe`). So Jackson–Jordán's equality is exhibited at every member of every population.

> **(MC-8)** `[CONSTRUCTED]` `maincomp.py --gain` **The first-order gain equals the needed gain at every
> drawn point.** At every member where the flat point misses, `rank β(Ψz, ·) = dim L(q) − 3 − def₃`
> at the census draw. The count is 2 266 outside `exh8` and 135 in `exh8`, 2 401 in all. Since
> `rank A₀ + gain ≤ rank A(q, z) ≤ target`, each equality is a certificate that **the first-order
> term alone** proves attainment at that `q`. No higher-order term was needed anywhere.

> **(MC-9)** `[PROVED]` *(checked by `maincomp.py --k23`, 20/20)* **The A′ mechanism at
> `K_{2,3} = θ(2,2,2)`.** This graph is certified feasible (`hcard`, triangle-free) and rigid, with
> a proper rigid `C₄`. On `X₀`, the hub planes `π_a` and `π_b` both contain the three non-hub points.
> At an admissible `q` those points are not collinear, so `π_a = π_b` and conjunct 3 fails at each
> non-hub. `X₀` is flat: `dim L = 3`, `def₂ = 0`. The flat point attains (MC-5)(iii), so `X₀`
> supplies the distinct motive but **not** the generic one. On the jump stratum where `q_x, q_y, q_z`
> are collinear (hubs off the line), `z` restricted to the line is affine (1 condition) and `z_a`,
> `z_b` are free, so `dim L(q) = 4`. That stratum has dimension `2|V| − 1 + 4 = 13 = dim X₀`. Every
> point of `X₀` satisfies the closed condition `π_a = π_b`, and the stratum's generic point does not.
> So the stratum lies on a **second irreducible component**, of dimension `≥ 13`. Its points are
> nondegenerate and attain. The generic motive of `K_{2,3}` lives there. This is the hand-off's "special components (the
> planar positions `q` where `L(q)` jumps)", found at the smallest feasible graph that has one.

**Reading the table against the decision table — outcome A′.** No `SHORT` anywhere, so neither
B nor C. At the certified-feasible graphs, the attaining `X₀` point is nondegenerate except at the
feasible graphs listed by the A-prime watch. Those are `θ(2,2,2)` outside `exh8`, and 28 graphs
in `exh8` (on 5–8 vertices, `θ(2,2,2)` among them). **Every one of them has a proper rigid
subgraph**, so no member of `hK`'s habitat (no proper rigid subgraph) is A′ on this library. Concretely:
- **`hK`'s conclusion** (`HasGenericPencilRealization` at feasible, no-proper-rigid `G`) holds at
  every `feas`-`norigid` member (996 outside `exh8`, 6 inside), at `X₀`'s generic point. Where
  the flat point misses, first-order gain alone reaches the target. This is the conclusion
  outright, with none of `hK`'s antecedents used.
- **(K-res)'s conclusion** holds at all 260 residuals, including `R20`, where the grid route's
  (RS-5) is refuted (§(K-res)). It holds at `X₀` and is nondegenerate.
- **(α)** (W4 branch 2, `def₂ > def₃`, the P2 population) holds at every one of the 928 peels, the
  10 `θ(1, 2, k)` and the 86 `exh8` members: `X₀` gives the distinct motive at each. The P2
  list is **not empty**, but `X₀` covers it, so on this library (α) is a consequence of the `X₀`
  rank statement rather than a kernel of its own.

**What this does and does not establish.** Every figure above is an exhibited certificate for one
graph. **Nothing** here is a class statement. The class statements that would carry an
architecture change are:

> **(MC-10)** `[CONJECTURED]` For every finite simple connected graph `G` of minimum degree `≥ 2`:
> **(a)** `X₀`'s generic point attains `6(|V| − 1) − def₃(G)`;
> **(b)** more strongly, at generic `q` and generic `z ∈ L(q)`,
> `dim ker β(Ψz, ·) = 3 + def₃(G)` on `F(q)`. That is a statement about **plane** frameworks and
> their liftings only ((MC-6));
> **(c)** if `G` is feasible and no two hubs of a common `closedHubNbhd` lie in a common
> `def₂`-rigid subgraph, `X₀`'s generic point is nondegenerate. This is the guess `K_{2,3}`
> suggests ((MC-9)); it is **not tested**, because the driver records only whether a proper rigid
> subgraph exists.

*(2026-09-24: (a) ⟺ (b) by (MC-11). (c) and its converse are (MC-14), `[INFORMAL]` modulo
Jackson–Jordán, so (c) is no longer a guess. (a) is claimed proved modulo Jackson–Jordán by
(MC-89), Step MC16, second-read 2026-09-24.)*

(b) ⟹ (a) by *Step MC6*. (a) would prove `HasDistinctPencilRealization K 3 G` for every simple
connected `G` of minimum degree `≥ 2`, **with no induction**. Jackson–Jordán is not needed for
that implication; the census uses it only to certify that a drawn `q` lies in `U`. With
(c), (a) also gives the generic motive wherever `X₀` is nondegenerate. At A′ graphs the generic
motive needs another component, as at `K_{2,3}`.

**What would change this:** a `SHORT` in any extension of the populations (outcome B or C). Since
(MC-11) the first-order gain *is* the rank gain, so a member where it falls below the needed gain
generically is a `SHORT`, refuting (a) and (b) alike. An A′ graph in `hK`'s habitat would break the reading that A′ is confined to graphs
with a proper rigid subgraph.

**Where the A′ exposure sits, and why it may be bounded (a sketch, not a proof).** At `K_{2,3}`
the mechanism is two hubs inside a common subgraph `H` with `def₂(H) = 0`. By (MC-4) plus
Jackson–Jordán applied to `H`, such an `H` is flat on `X₀`. **Whether each of the 28 `exh8` A′
graphs has this shape is not checked.** A `def₂`-rigid subgraph is also `def₃`-rigid
((MC-5)(i)), so in `hK`'s habitat (no proper rigid subgraph) this mechanism can occur only when
`G` itself has `def₂ = 0`. The census found **no** A′ graph without a proper rigid
subgraph. The exposure is therefore W4's generic motive at graphs that have rigid subgraphs,
i.e. branches 3a–3c. The distinct motive is not exposed at all.

**The census ends at this table** (W4-reopen P1); what follows is the PI's call. Outcome A′'s row
says P3 becomes "prove the rank on `X₀`", an architecture change. If (MC-10)(a) holds, the
distinct motive no longer needs smark's O7e programme, `hbareSplit` or (K-bare-c)/(α). On `hK`'s
habitat the same goes for `hK`, given nondegeneracy there. `kres` and (K-c) become unnecessary
wherever `X₀` is nondegenerate, which is all 260 residuals measured. P3 must also supply
nondegenerate points at A′ graphs, whose generic motive lives off `X₀` (as at `K_{2,3}`).

---

### After the census (2026-09-24): the gain is exact, and nondegeneracy on `X₀` is combinatorial

*Written 2026-09-24, continuing W4-reopen P1 at the PI's direction ("see if we can make progress
on the math without a new census first"). No census population was re-run, and no row of the
decision table moves. Two new drivers each check one identity or one equivalence per instance:
`w4/exactgain.py` checks (MC-11), `w4/nondegx0.py` checks (MC-12)/(MC-13).*

#### Step MC7 — the gain is exact

Step MC4 split the motion equations into a `W_Π`-block and a `W′`-block at `z = 0`. **The split
holds at every `z`.** The `W_Π`-coordinates of `C_e` are (MC-3)'s first summand, which does not
involve `z`. The `W′`-coordinates are `C′_e = J a_e(z)` with `a_e(z) := z_w p̂_u − z_u p̂_w`; this is
Step MC6's computation, which uses (MC-3)'s formula and not `z ∈ L(q)`. For `r : E → K³` write
`H(r) := {ω ∈ K^E : Σ_{e ∈ C} σ_C(e) ω_e r_e = 0 for every cycle C}`. This is the angular-velocity
space of the planar body-and-pin framework with pin `r_e` on edge `e`. Write `ℓ_e := p̂_u × p̂_w`, as
in Step MC6.

> **(MC-11)** `[PROVED]` *(the gain is exact)* Let `G` be connected, and let `q` have `q_u ≠ q_w` on
> every edge. Let `z ∈ K^V` be arbitrary: the framework at `p = (q, z)` is molecular (hinges
> concurrent at each `p_v`), not necessarily a pencil framework.
> **(i)** Its motion space is `{(h, m′) : h ∈ F(q), m′_u − m′_w = ω_e(h) J a_e(z) for every e = (u, w)}`.
> Hence its flexes modulo the six trivial ones are `H(ℓ) ∩ H(a(z))`, and
> `rank R(q, z) = 6(|V| − 1) − dim(H(ℓ) ∩ H(a(z)))`. The first factor depends on `q` alone (the
> flat, pin-collinear framework of Step MC4). The heights enter only through the trace pins
> `a_e(z)`, which are linear in `z`. `a_e` is the homogeneous point where the hinge line crosses
> `Π`, with last coordinate `z_w − z_u`. At a horizontal hinge it is the direction's point at
> infinity, scaled by the common height.
> **(ii)** If `q` is admissible and `z ∈ L(q)`, then **exactly**
> `rank R(q, z) = rank R(q, 0) + rank β(Ψz, ·) = 6|V| − 3 − dim ker_{F(q)} β(Ψz, ·)`, at every such
> point, with no genericity.

*Proof.* (i) The six equations `m_u − m_w − ω_e C_e = 0` of edge `e` separate into three
`W_Π`-coordinates and three `W′`-coordinates. The `W_Π`-block does not involve `z`. By Step MC4
its solutions `(m^Π, ω)` are the flat flexes `h ∈ F(q)`, with `ω = ω(h)` because `C_e|_{W_Π} ≠ 0`.
The `W′`-block, `m′_u − m′_w = ω_e J a_e`, is a coboundary equation for `m′ : V → K³`. It is
solvable iff the edge vector `(ω_e J a_e)_e` is orthogonal to `Z₁(G) ⊗ K³`, because over any field
the cut space of `K^E` is the orthogonal complement of the cycle space. Since `J` is invertible,
that is `ω ∈ H(a)`, and then `m′` is unique up to a constant. The constant `h` (3 dimensions) and
the constant `m′` (3 more) are the six trivial motions, and `F(q)/constants ≅ H(ℓ)` by
`h ↦ ω(h)`. Hence `dim ker R = 6 + dim(H(ℓ) ∩ H(a))`. (ii) Step MC6's proof identifies the pairing
of `(ω_e(h) J a_e)_e` with `λ′ ∈ Z₁ ⊗ K³` as `β(Ψz, h)(Jλ′)`, when `z ∈ L(q)` at admissible `q`.
Step MC6's `μ := −Jλ′` carries the opposite sign, which comes from `A₁ = −C′`; vanishing is
unaffected. So
the solvability condition is `β(Ψz, h) = 0` and `dim ker A(q, z) = 3 + dim ker_{F(q)} β(Ψz, ·)`. At
`z = 0` this is `3 + dim F(q)`, and (MC-3)'s `rank A = |E| + rank R` finishes. ∎

**Checked** in exact ℚ at every point drawn. (i) is checked by `exactgain.py --molecular`: 204
points on the battery, every simple 2EC graph on ≤ 5 vertices, and `θ` with sum ≤ 8. The heights
`z` are arbitrary and the pictures are only edge-injective, with scale 1 forcing degenerate
positions; the run takes about 4 s, first as the second reader's scratch check and then committed.
(ii) is checked by `exactgain.py`: 1 830 points over the battery,
every simple 2EC graph on ≤ 6 vertices, and `θ(a, b, c)` with `a + b + c ≤ 9`. The points include
131 jump points `q` (`dim L(q) > 3 + def₂`, found by `--jump 200` at scale 2) and special `z`
(each basis vector of `L(q)`, and a sum of two). The run takes about 50 s. Command:
`python3 notes/scripts/w4/exactgain.py --battery --exh 6 --thetas 9 --jump 200`.

> **(MC-11)(iii)** `[PROVED]` *(what (MC-11) does to the census)* The first-order gain of Step MC6
> *is* the gain, at every admissible point. So **(MC-8) at a draw is equivalent to (MC-7)'s
> attainment at that draw**, and carries no further information. **(MC-10)(a) ⟺ (MC-10)(b).** Two
> further forms are plane-framework statements too. The existence form of the conjecture at `G`
> (one witness, which the Lean motive needs) is: *some admissible `q` and some `z ∈ L(q)` have
> `dim ker_{F(q)} β(Ψz, ·) = 3 + def₃`.* (MC-10)(a) asks for this with `q ∈ U`.
> **(iv)** `[PROVED]` *(reciprocity)* For `z, z′ ∈ L(q)`: `Ψz′` is the vertical part of a motion of the
> framework at `(q, z)` iff `Ψz` is the vertical part of a motion at `(q, z′)`. This is (MC-11)(ii)
> with (MC-6)(i).
> **(v)** `[PROVED]` *(the gain as the image of a quadratic map)* With `P = Ψz`,
> `β(P, P)(μ) = Σ_e det(μ_e, P_w, P_u) = Σ_e μ_e · (P_w × P_u)`. So
> `Q_q : L(q)/Aff(q) → (K³)^E / (B¹ ⊗ K³) ≅ (Z₁ ⊗ K³)^∨`, `z ↦ [e ↦ P_w × P_u]`, is a quadratic map
> with differential `2β(Ψz, ·)`. In characteristic 0 the gain at generic `z ∈ L(q)` equals the
> dimension of the closure of `Q_q`'s image (generic smoothness). So (MC-10)(b) at `q` says: that
> image has dimension `dim L(q) − 3 − def₃`.
> **(vi)** `[PROVED]` *(what the pencil constraint adds to the molecular theorem)* By (i), for fixed
> `q` the heights enter only through the linear family `T_q(z) : H(ℓ(q)) → (K³)^{cycles}`,
> `ω ↦ (Σ_{e ∈ C} σ_C(e) ω_e a_e(z))_C`, with `rank R(q, z) = 6(|V| − 1) − dim ker T_q(z)`. The
> molecular theorem (Katoh–Tanigawa 2011, attaining at generic `p`) says `T_q` reaches kernel
> dimension `def₃` at generic `z ∈ K^V`, for generic `q`. It is formalized in this project over any
> infinite field (ROADMAP §33), and the hinge-concurrent case follows from the panel case by the
> Phase 25 duality; the generic form follows from the existential one by semicontinuity.
> **(MC-10)(a) says exactly that `T_q` keeps that generic rank on the linear subspace
> `L(q) ⊆ K^V`**, where `T_q(z)` is the symmetric `β(Ψz, ·)`. It is a rank question about one
> linear matrix family restricted to one linear subspace.
> **(vii)** `[PROVED]` *(the obstruction is a vector area)* `F(q)` is the space of **parallel drawings**
> of `G` in `K³` with prescribed edge directions: maps `P : V → K³` with `P_u − P_w ∈ K ℓ_e`. For a
> cycle `C` and `c ∈ K³`, `β(P, P)(1_C ⊗ c) = −2 c · A_C(P)`, where
> `A_C(P) := ½ Σ_{(a → b) along C} P_a × P_b` is the **vector area** of the closed spatial polygon
> that `P` traces around `C`. It is translation-invariant, as `β` is on constants. So the 3D
> pencil framework at `(q, z)` has, beyond the trivial ones, exactly the flat flexes `h` whose
> **mixed** vector area with `P = Ψz` vanishes around every cycle. In characteristic 0, by (v),
> (MC-10)(b) says: *for generic `q`, the map `P ↦ (A_C(P))_C` on parallel drawings has generic
> fibre dimension `3 + def₃`.* In
> the edge coordinates `ω` of a parallel drawing, this is
> `A_C = ½ Σ_{i < j along C} (σω ℓ)_i × (σω ℓ)_j`. Its coefficients `ℓ_i × ℓ_j` are the intersection
> points of pairs of edge-lines of the picture `q`, and consecutive edges at `v` meet at `q_v`
> itself.

#### Step MC8 — nondegeneracy on `X₀` is combinatorial

Planes are written in the chart as `π_w : z = α_w x + β_w y + γ_w`, with `P_w := (α_w, β_w, γ_w)`
(so `P = Ψz` on `B`). The normal of `π_w` in `K⁴` is `(α_w, β_w, −1, γ_w)`, up to scale. Linear
independence of such normals is therefore **affine** independence of the points `P_w ∈ K³`. For
`w ∈ N(v)`, `P_w − P_v = ±ω_{vw}(P) ℓ_{vw}`.

> **(MC-12)** `[PROVED]` Under (H), let `q` be in **general position**: admissible, with no three
> points of any `q(N[v])` collinear (a nonempty Zariski-open condition). General position is
> sufficient, not necessary. The proof uses it only for the triple `{q_v, q_{w₁}, q_{w₂}}` at a hub
> `v` with two hub neighbours; at such a collinear triple conjunct 3 fails for every `z`. Let `z ∈ L(q)` and
> `P = Ψz`. Then conjuncts 1, 2 and 4 of `IsNondegPencilRealization` hold at `(q, z)` (Step MC2),
> and **conjunct 3 holds iff**
> **(i)** `|closedHubNbhd v| ≤ 3` for every `v`;
> **(ii)** `P_u ≠ P_w` (that is, `π_u ≠ π_w`, that is, `ω_{uw}(P) ≠ 0`) for every edge `uw` joining two
> hubs;
> **(iii)** `P_a ≠ P_b` (that is, `(ω_{va}(P), ω_{vb}(P)) ≠ (0, 0)`) for every degree-2 vertex `v`
> whose two neighbours `a, b` are both hubs.

*Proof.* Put `S = closedHubNbhd v ⊆ N[v]`. Every plane `π_w`, `w ∈ S`, contains `p_v`, so the
normals lie in the 3-dimensional `p_v^⊥`. So `|S| ≥ 4` fails conjunct 3, which gives (i). `|S| ≤ 1`
is automatic. For `|S| ∈ {2, 3}` there are two cases. If `v` is a hub, `S = {v, w₁(, w₂)}` with
`P_{w_i} − P_v = ±ω_i ℓ_i`. The `ℓ_i` are independent by general position, so the `P`'s are
affinely independent iff every `ω_i ≠ 0`. Each `vw_i` is a hub–hub edge, and every hub–hub edge
`uw` arises this way (in `closedHubNbhd u`); this gives (ii). If `v` is not a hub, then
`deg v = 2` and `S ⊆ {a, b}`. Then `P_a − P_b = ±ω_{va} ℓ_{va} ∓ ω_{vb} ℓ_{vb}`, which is nonzero iff
the pair `(ω_{va}, ω_{vb})` is not zero; this gives (iii). ∎

A `def₂`-**rigid subgraph** is `H ⊆ G` with `|V(H)| ≥ 2` and `def₂(H) = 0`. It is connected, and
by (MC-5)(i) it is also `def₃`-rigid. In a simple graph it has at least 3 vertices. Triangles
and `K_{2,3}` are examples. For an edge `e = uw` let `G_e` be `G` plus one new vertex `x` adjacent
to exactly `u` and `w`.

> **(MC-13)(a)** `[PROVED]` For `(q, q_x)` admissible for `G_e` with `q_x` off the line `q_u q_w`,
> `F(G_e) ≅ {P ∈ F(G, q) : P_u = P_w}`, with `P_x := P_u`.
> **(MC-13)(b)** `[PROVED]` `def₂(G_e) = def₂(G)` if `u` and `w` lie in a common `def₂`-rigid
> subgraph of `G`, and `def₂(G_e) = def₂(G) − 1` otherwise. The first case holds iff some
> `def₂`-maximizing partition of `V(G)` has `u` and `w` in one part.
> **(MC-13)(c)** `[INFORMAL]` *(not argued here: Jackson–Jordán's pin-collinear theorem, at `G_e` and at a rigid subgraph)*
> At generic `q`, **the planes of `u` and `w` coincide on the whole fibre `L(q)`** (`ω_e ≡ 0` on
> `F(G, q)`) **iff `u` and `w` lie in a common `def₂`-rigid subgraph of `G`.** The "only if"
> direction uses Jackson–Jordán at `G_e` only, together with the elementary (MC-4)(b) at `G`. The
> "if" direction uses it at the rigid subgraph. Only the hard direction of Jackson–Jordán's
> Thm 7.1 (TR p.21) is used: generic `dim F ≤ 3 + def₂`, for simple graphs. Their theorem is over
> `ℝ` with genericity over `ℚ`, so (c) is claimed in **characteristic 0** (over any infinite field
> modulo (MC-33)(i); in characteristics 2, 3, 101 and 10 007 wherever `G_e` has ≤ 8 vertices, by
> (MC-33)(ii)).

*Proof.* (a) A flex of `G_e` has `P_x − P_u ∥ ℓ_{xu}` and `P_x − P_w ∥ ℓ_{xw}`, and `P_u − P_w = ω_e ℓ_e`.
So `ω_e ℓ_e + ω_{wx} ℓ_{wx} + ω_{xu} ℓ_{xu} = 0`, where the three `ℓ`'s are the sides of the
non-degenerate triangle `q_u q_w q_x`. That forces every `ω` to vanish, so `P_x = P_u = P_w`.
Conversely, any `P ∈ F(G)` with `P_u = P_w` extends by `P_x := P_u`. The closed neighbourhoods
`N[x] = {x, u, w}` and `N[u] ∪ {x}` are non-collinear.
(b) Write `val(P) := 3(|P| − 1) − 2d(P)`. Take a partition of `V(G_e)` and look at where `x` goes.
If `x` is alone, the value is `val_G(P) − 1`. If `x` sits in `u`'s part (or `w`'s), the value is
`val_G(P) − 2·[u, w separated by P]`. If `x` sits in any other part, it is `val_G(P) − 4`. Hence
`def₂(G_e) = max(max_{P : u ∼ w} val_G(P), def₂(G) − 1)`, which is the dichotomy.
Parts of maximizing partitions are rigid. Refining a part `X` by a partition `Q` of `X` changes
`val` by `3(|Q| − 1) − 2d_{G[X]}(Q) ≤ 0`, so `def₂(G[X]) = 0`. Conversely, let `H ∋ u, w` be
rigid and `P` maximizing. Merge the `t` parts that meet `V(H)`. This changes `val` by
`−3(t − 1) + 2·(edges of G between the merged parts)`, which is `≥ −3(t − 1) + 2d_H(P|_H) ≥ 0`. So
the merged partition is still maximizing, and `u ∼ w` in it.
(c) *Only if.* Suppose no rigid subgraph contains `u, w`. By (a), (b), Jackson–Jordán at `G_e`
(generic `(q, q_x)`, so generic `q` for `G`) and (MC-4)(b) at `G`:
`dim{P ∈ F(G, q) : P_u = P_w} = dim F(G_e) = 3 + def₂(G_e) = 2 + def₂(G) < 3 + def₂(G) ≤ dim F(G, q)`.
*If.* Suppose `u, w ∈ V(H)` with `H` rigid. Every `P ∈ F(G, q)` restricts to a flex of `H` at `q|_H`
(generic for `H`). By Jackson–Jordán at `H`, `dim F(H) = 3 + def₂(H) = 3`, so the restriction is
constant and `P_u = P_w`. ∎

> **(MC-14)** `[INFORMAL]` *(not argued here: Jackson–Jordán's pin-collinear theorem, at the `G_e` and at rigid subgraphs)*
> *(settles (MC-10)(c) and adds its converse; characteristic 0)* Under (H), at generic `q`, **`X₀`'s generic point
> satisfies `IsNondegPencilRealization` iff every `|closedHubNbhd v| ≤ 3` and no `def₂`-rigid
> subgraph of `G` contains two members of a common `closedHubNbhd`.** The "if" direction uses
> Jackson–Jordán only at the graphs `G_e`, for `e` a hub–hub edge or an edge at a degree-2 vertex
> with two hub neighbours. On the A′ graphs this is exactly the `K_{2,3}` mechanism of (MC-9).

*Proof.* **If.** Fix a hub–hub edge `e`. It lies in no rigid subgraph, so `ω_e ≢ 0` on `F(q)` by
(MC-13)(c). Now take a degree-2 vertex `v` with hub neighbours `a, b`. Suppose both `ω_{va} ≡ 0` and
`ω_{vb} ≡ 0`. By (MC-13)(c) there are rigid `H₁ ∋ v, a` and `H₂ ∋ v, b`. Their union is rigid.
*Proof of the union lemma* (the second reader's):
- Let `P` partition `V₁ ∪ V₂` into `k` parts. Let `P₁ = P|_{V₁}`, with `t₁` parts.
- Let `P₂′` be `P|_{V₂}` with every part that meets `V₁` merged into one; it has `k − t₁ + 1`
  parts.
- An `H₂`-edge crossing `P₂′` has an endpoint outside `V₁`, so it is not an `H₁`-edge. Hence
  `d(P) ≥ d_{H₁}(P₁) + d_{H₂}(P₂′)`.
- So `val(P) ≤ val_{H₁}(P₁) + val_{H₂}(P₂′) ≤ 0`. One shared vertex suffices.
So the union contains `a` and `b`, which is excluded.
(The edge form checked by the driver is equivalent to the pair form stated. Use the union lemma,
and note that adding a degree-2 vertex to a rigid graph keeps it rigid.) Hence at least one of `ω_{va}`, `ω_{vb}` is not
identically zero. Only finitely many nonzero linear functionals on `F(q)` are involved, so
generic `z` avoids all their kernels, and (MC-12) gives conjunct 3.
**Only if.** If some `|closedHubNbhd v| ≥ 4`, (MC-12)(i) fails everywhere. Suppose instead that
`w₁, w₂ ∈ closedHubNbhd v` lie in a rigid `H`. Then `P_{w₁} = P_{w₂}` on all of `F(q)`, as in the
"if" half of (MC-13)(c). So their normals coincide, and conjunct 3 fails on all of `B`. (Linear dependence is a closed
condition holding on a dense subset of `B`.) ∎

**Checked** by `nondegx0.py` over every simple 2EC graph on ≤ 8 vertices (7 980 graphs, 121 208
edge checks), the battery and `θ(a, b, c)` with `a + b + c ≤ 10`. It uses one scale-30 admissible
`q` per graph. The (MC-13) equivalence is asserted edge by edge wherever that `q` and a drawn
`q_x` exhibit Jackson–Jordán's equality at `G` and at `G_e`; 12 edge checks at 1 graph were skipped
for that reason. The (MC-12)/(MC-14) prediction is asserted against `flanks.nondeg_conjuncts`, with
up to 4 drawn `z` per graph. On `exh8` the prediction and the observation agree at all 7 980
graphs: **7 934 predicted = 7 934 observed conjunct-3-degenerate on `X₀`**, which is the census's
own count in (MC-7)'s `exh8` row. Of these, 7 701 fail `hcard` and 233 pass `hcard` but have a rigid
hub pair (the census's 28 feasible A′ graphs are among the 233). Runs: `exh8` about 170 s;
`python3 notes/scripts/w4/nondegx0.py --battery --thetas 10 --exh 6 --list` about 1 s.

#### Step MC9 — kernel (K)'s habitat has no `def₂`-rigid subgraph

> **(MC-15)(i)** `[PROVED]` Let `G` be simple and 2-edge-connected, with `|V| ≥ 4`, a vertex of
> degree 2, and **no proper rigid subgraph**: no `H ≤ G` with `2 ≤ |V(H)|`, `V(H) ⊊ V(G)` and
> `deficiency H 3 = 0` (Lean `IsProperRigidSubgraph`, `n = 3`). Then **no subgraph of `G` on at least
> two vertices is `def₂`-rigid, `G` itself included.**
> **(ii)** `[INFORMAL]` *(not argued here: Jackson–Jordán's pin-collinear theorem, at the `G_e`)* Hence, on `hK`'s habitat
> (`Escape.lean`'s `hK` assumes `G.Simple`, `5 ≤ |V(G)|`, `G.TwoEdgeConnected`, no proper rigid
> subgraph, and a degree-2 vertex), wherever every `|closedHubNbhd v| ≤ 3`, `X₀`'s generic point
> is **nondegenerate** (MC-14). On that habitat **(MC-10)(a) alone would give `hK`'s conclusion
> `HasGenericPencilRealization K 3 G` outright, without its split-off antecedent or its induction
> hypothesis**, over the fields where (MC-10)(a) and Jackson–Jordán hold.

*Proof of (i).* A `def₂`-rigid subgraph `H` with `V(H) ⊊ V(G)` is connected and `def₃`-rigid by
(MC-5)(i), so it is excluded. A subgraph spanning all of `V(G)` is **not** excluded by
`IsProperRigidSubgraph`, but it has `def₂(H) ≥ def₂(G)`, having fewer edges. So it suffices to
show `def₂(G) > 0`. Suppose `def₂(G) = 0`. For `X ⊊ V` let `c(X)` be
the number of edges leaving `X`.
- *Step 1.* `def₂(G[X]) ≤ 2c(X) − 3`. Add the single part `V ∖ X` to a partition of `X`.
- *Step 2.* If `def₂(H) ≤ 1`, then `H` is connected, and `def₃(H) = 0` iff `H` is bridgeless. From
  `2d(P) ≥ 3|P| − 4`: `6(|P| − 1) − 5d(P) ≤ (8 − 3|P|)/2 < 0` for `|P| ≥ 3`, and `|P| = 2` needs
  `d ≥ 2`.
- *Step 3.* Let `c(X) = 2` and `|X| ≥ 2`. Then `G[X]` has a bridge, else it would be a proper rigid
  subgraph. The bridge splits `X` into `X₁`, `X₂`. Since `G` is 2EC and
  `c(X₁) + c(X₂) = 2 + c(X) = 4`, both have `c(X_i) = 2`.
- *Step 4.* By induction on `|X|`, every vertex of such an `X` has degree 2 in `G`.
- *Step 5.* Apply this to `X = V ∖ {v}`, `v` of degree 2: `c(X) = 2`. So `G` is a cycle, and
  `def₂(C_n) = n − 3 = 0` forces `n = 3`, against `|V| ≥ 4`. ∎

(ii) is (i) with (MC-14): no rigid subgraph exists at all.

**Where this leaves the A′ exposure.** Under Jackson–Jordán it is now exactly the graphs with a
`def₂`-rigid subgraph containing two hubs of a common `closedHubNbhd` (MC-14). By (MC-15) that
set is disjoint from `hK`'s habitat; the census's "no A′ graph in `hK`'s habitat" is now a theorem
(mod Jackson–Jordán). **Residuals** (packaging (b)'s (K-res) habitat) have proper rigid subgraphs,
so (MC-15) does not reach them. For each residual, (MC-14) turns "nondegenerate on `X₀`" into a
finite check of `def₂`-rigid subgraphs; the census found all 260 nondegenerate.

#### Literature, checked 2026-09-24 (a read-only agent over `.refs/` plus the web; bibliographic data from Crossref)

- **Jackson–Jordán**, "Pin-collinear body-and-pin frameworks and the molecular conjecture",
  *Discrete Comput. Geom.* 40(2) (2008) 258–278, doi:10.1007/s00454-008-9100-z. Read in its
  report form, EGRES TR-2006-06 (`.refs/`).
  - Thm 6.1 (TR p.14) and Thm 7.1 (p.21): simple graphs; the generic rank is
    `3|V| − 3 − def(G)`, with `def` exactly our `def₂` (p.7).
  - Thm 7.3: rigidity is equivalent to 2G packing 3 spanning trees.
  - p.21: the rod-and-pin 2-polymatroid **equals** the body-and-pin one, so the formula gives the
    rank of **every edge subset**. That is the form (MC-13)(c) and (MC-14) use, at `G_e` and at
    rigid subgraphs.
  - Setting: `ℝ²`, generic meaning algebraically independent over `ℚ` (TR p.4 for bar-joint, p.12
    for body-and-pin and rod-and-pin), with the genericity placed on the pin-lines, each pin being
    `L_u ∩ L_v`. This is exactly our dual picture: pin-line `L_v` dual to `q_v` (`p(v) = −q_v`),
    pin `ℓ_e`, and motion coordinates changed by `diag(1, −1, 1)`. The rank statement is about
    polynomials over the prime field. **It transfers to characteristic 0.** Beyond that, see
    *Jackson–Jordán beyond ℝ* (MC-33):
    - a second reading finds every step field-free over any infinite field after two small repairs
      and one bypass (`INFORMAL`);
    - `jjchar.py` exhibits the equality in characteristics 2, 3, 101 and 10 007 at all 7 980 simple
      2EC graphs on ≤ 8 vertices.
  - Proof technique: a minimal counterexample. The geometric steps are bar-joint 0-extensions,
    1-extensions and vertex splits on the body-and-pin graph; the combinatorics is the theory of
    bricks and superbricks.
- **The flat correspondence of Step MC4** (`F(q) ≅ L(q)`).
  - Crapo–Whiteley, "Statics of frameworks and motions of panel structures: a projective geometric
    introduction", *Structural Topology* 6 (1982) 43–82. Example 4.4 (pp. 72–73) is the flat
    tetrahedron: motions of the flat panel structure ↔ polyhedra over it, "true in great
    generality, as we shall see in the sequel".
  - Whiteley, "A correspondence between scene analysis and motions of frameworks", *Discrete Appl.
    Math.* 9(3) (1984) 269–295, doi:10.1016/0166-218X(84)90027-1. By its abstract this is the
    general isomorphism between scenes over a picture and motions of a plane framework. **Not read
    in full; read it before citing it for Step MC4.**
  - The scene-analysis count is Whiteley, "A matroid on hypergraphs, with applications in scene
    analysis and geometry", *Discrete Comput. Geom.* 4 (1989) 75–95, doi:10.1007/BF02187716
    (Sugihara's conjecture; Whiteley 1996 §8.3).
- **Katoh–Tanigawa**, "A proof of the molecular conjecture", *Discrete Comput. Geom.* 45 (2011)
  647–700, doi:10.1007/s00454-011-9348-6, checked against the local text (running head and DOI
  line), for Step MC12. The places used are all in §6.2, "G contains a proper rigid subgraph"
  (p. 673): Lemma 6.2 with eq. (6.3), p. 673; Lemma 6.3 with the hinge choice (6.6), p. 674;
  Claim 6.4 with (6.7)–(6.9), p. 675, where `v*` "may be realized as a d-dimensional body";
  Lemma 6.5 with Claim 6.6, p. 676. Also Lemma 3.5 (contraction of a rigid subgraph, p. 658) and
  Lemma 5.1 (column deletion, p. 667).
- **Vertical/horizontal split, (MC-11)(i): not found.** Searched Crapo–Whiteley 1982; the
  nearest is its Prop. 5.1 on cross-sections of panel structures. Also searched Whiteley 1988,
  1996, 1999, 2005, Katoh–Tanigawa 2011 and Jordán 2016.
- **The pencil statement itself: not found**, in any local source or by web search. The hinge
  coplanar and hinge concurrent cases always appear separately. Whiteley 1999 p.25 notes only that
  three coplanar concurrent hinges are dependent. One place could not be checked: Whiteley 1989
  p.93, cited by Jackson–Jordán §8 for "a similar conjecture for 3-dimensional frameworks". The
  download was blocked.
- Also verified, for P3's Edmonds-problem idea: Lovász, "Singular spaces of matrices and their
  application in combinatorics", *Bol. Soc. Brasil. Mat.* 20(1) (1989) 87–99,
  doi:10.1007/BF02585470. Sugihara, *Machine Interpretation of Line Drawings*, MIT Press, 1986.
