## §(K-main) — the main component `X₀`: over a fixed planar picture the pencil condition is linear in the heights, the flat rank is an exact identity in `dim L(q)`, and the census of `X₀`

Answering `notes/pencil/W4-reopen.md` **P1** (the main-component census, ranked first by the
2026-09-23 strategy re-think; nothing in it commissioned beyond that ranking). Tag `MC-`
(`notes/pencil/labels.md`). Driver: `notes/scripts/w4/maincomp.py`. The object is the smark brief's
§1 pencil configuration (`notes/attacks/smark/brief.md`), read here in an affine chart; the
derivation is the hand-off's (F1)–(F3), written out and checked. **(MC-4)** was not in the
hand-off: it makes the flat rank an exact identity rather than a citation.

**Verdict.** (MC-1)–(MC-6) and (MC-9) are *proven-informally* and elementary. The one citation
any of them uses, Jackson–Jordán's pin-collinear theorem (the smark brief §3(a); published, not
formalized, checked only over `ℝ` — `notes/Phase39-design.md` field-hypothesis recon, row S5), is
needed only for the *equality* case of (MC-4)(b), and every use of it below is flagged.
**The census RAN on 2026-09-23. Its outcome is row A′ of the decision table fixed before any run**
(*The census — results*). `X₀` attains at all 10 252 members, including every simple 2EC graph on
at most 8 vertices; there are 0 `SHORT`s. At every drawn point the first-order term alone reached
the target ((MC-7), (MC-8)). The exception is nondegeneracy: at 28 distinct certified-feasible graphs, all
with a proper rigid subgraph, `X₀` supplies the distinct motive but not the generic one ((MC-9)).
The class statements (MC-10) are *open*. What follows is the PI's call.
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
> it depends only on the class of `z` in `P(L(q)/Aff(q))`.

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

### Step MC6 — the first-order structure at the flat point is a symmetric form on the lifting space

*Written after the spec commit `9e8aaec2`, while the census ran.* It changes no row of the decision
table.

At `(q, 0)` the motion space is the glued block (3 dimensions, trivial) plus `F(q) ≅ L(q)`, and the
perturbation directions are `L(q)` too. The **first-order gain** in direction `z` is
`rank(S₀ᵀ A₁(z) K₀)`, with `K₀` and `S₀` the kernel and left kernel of `A₀`. It lower-bounds
`rank A(q, z) − rank A₀`. The reason: `P(A₀ + tA₁)Q` in a basis adapted to `A₀` has Schur
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
> So `X₀` attains **to first order** iff some `z ∈ L(q)` has
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

(b) ⟹ (a) by *Step MC6*. (a) would prove `HasDistinctPencilRealization K 3 G` for every simple
connected `G` of minimum degree `≥ 2`, **with no induction**. Jackson–Jordán is not needed for
that implication; the census uses it only to certify that a drawn `q` lies in `U`. With
(c), (a) also gives the generic motive wherever `X₀` is nondegenerate. At A′ graphs the generic
motive needs another component, as at `K_{2,3}`.

**What would change this:** a `SHORT` in any extension of the populations (outcome B or C). A
member where the first-order gain falls below the needed gain would not refute (a), but it would
refute (b). An A′ graph in `hK`'s habitat would break the reading that A′ is confined to graphs
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
