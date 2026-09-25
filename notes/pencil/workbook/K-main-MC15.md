## §(K-main) — Step MC15 — the per-graph certificates are partition counts (modulo Jackson–Jordán)

#### Step MC15 — the per-graph certificates are partition counts (modulo Jackson–Jordán)

*Worked 2026-09-24 by a read-only agent (W4-reopen P1, open direction 4, "the certificate half";
the third 2026-09-24 session's Track C), from the coordinator's derivation of `dim U`. The
coordinator re-derived (MC-62), (MC-65), (MC-68) and (MC-70) at the level of their written proofs.
**Second-read in full.** (MC-68)–(MC-71) on 2026-09-24. (MC-62)–(MC-67) on 2026-09-25, by a fresh
reader who re-derived each and ran independent exact checks (MC-161). All six hold; there is no
mathematical gap. One proof step was asserted without justification: (MC-64)'s Case 2 applies
(MC-66) after the first contraction. The reader supplied the missing merge lemma, now in place.
Its other notes:
- the converse of (MC-66) is false (MC-160), and (MC-64) uses only the sound direction;
- Jackson–Jordán in flex form reduces to graphs satisfying (H) (MC-159);
- (MC-64)'s "on all of `X₀(G′)`" presupposes (H); for a general simple `G′` read it in flex form;
- every graph at which (MC-62)–(MC-64) invoke Jackson–Jordán has at most `|V(G′ + ab + x)|` vertices;
- (MC-67)(c)'s clause about "any one part" is vacuous, because `(G/H)[𝒮*]` is rigid, hence connected;
- (MC-89)'s proof text mentions (MC-62), and Step MC20's table lists (MC-67), but neither is
  logically needed: (MC-79)(v) uses (MC-48)(ii)'s count, and (MC-87) gives additivity directly. Drivers `w4/orbitrule.py`,
`w4/contractcheck.py`, `w4/kerm0.py` (new). The question is (MC-61)'s certificate half: replace each
step's per-graph linear-algebra certificate by a condition on the graph's partitions, as (MC-13)(c)
and (MC-48)(ii) did for flag coincidences.*

**Verdict.**
- **`dim U` and the flag orbit are combinatorial**, mod JJ: `dim U = min(δ₂, 3)` (`a ≁ b`) and
  `min(δ₂, 1)` (`a ∼ b`) (MC-62); the generic orbit is decided by `δ₂`, adjacency, and at `δ₂ = 1`
  one neighbourhood test against the `def₂`-classes (MC-64).
- **The CONTRACT certificates collapse to one count**, *additivity*
  `def₂(G) = def₂(H) + def₂(G/H)`. (i) core-free ⟺ additivity (MC-68), and additivity ⟹ (ii) no jump
  (MC-69). So CONTRACT needs no per-graph certificate: `W` proper rigid, `G/H` simple, additivity,
  mod JJ at `H` and `G/H` (MC-71).
- Additivity is a partition condition (MC-67)(c). At a **maximal** proper rigid `W` with `G/H` simple
  it holds automatically outside one exceptional case, which forces `def₃(G) = 0`, `def₂(G/H) = 0` and
  every outside degree `≥ 3` (MC-70).
- The step table's certificates, translated (MC-72): "`dim U ≥ 2`" ⟺ `a ≁ b` and `δ₂ ≥ 2`; (MC-51)(a)
  ⟺ `δ₂ = 1`; (MC-51)(b) ⟺ `δ₂ = 0`.
- Both recorded failures of (MC-41), and a constructed instance with `def₂(H) ≤ def₂(G)`, violate
  additivity (MC-74). Additivity is strictly sharper than (MC-59)(a).
- Not explained: why `δ ≤ 1` at every instance of Step MC11's histogram with `dim U = 1`.

**Notation.** Everything is in **flex form**: `F(Γ, q) = {P : V → K³ : P_u − P_w ∈ Kℓ_uw}`,
`ℓ_uw = p̂_u × p̂_w`, which needs only an edge-injective picture and no minimum degree. At an
admissible picture of a graph satisfying (H), Step MC4's bijection turns each statement into
the lifting statement of the workbook. `val(𝒫) := 3(|𝒫| − 1) − 2d(𝒫)` on partitions (multigraphs
allowed), `def₂ = max val`. A **class** of `Γ` is a maximal `def₂`-rigid vertex set (on `≥ 2`
vertices), or a singleton lying in no `def₂`-rigid subgraph; `R(v)` is the class of `v`.
For a pair `a ≠ b`: `U := {P_a − P_b : P ∈ F(G′, q)}`, `δ₂ := def₂(G′) − def₂(G′/ab)` (identify
`a, b`; a loop, if `a ∼ b`, is dropped). For a vertex set `W`: `H = G[W]`, `O = V ∖ W`, `G/H`
contracts `W` to `v*`, **additivity** means `def₂(G) = def₂(H) + def₂(G/H)`,
`ε := def₂(H) + def₂(G/H) − def₂(G)`.

**Part I — `dim U` and the generic flag orbit.**

> **(MC-62)** `[PROVED-MOD]` *((MC-33); the coordinator's derivation, checked)* Let `G′` be simple,
> `a ≠ b`, and `q` generic. Then
> - `dim U = min(δ₂, 3)` if `a ≁ b`;
> - `dim U = min(δ₂, 1)` if `a ∼ b`.
>
> The inequality `≥` uses JJ at `G′ + ab + x` (resp. `G′ + x`) only; `≤` uses JJ at `G′` only.
> At every `q` with `dim F(G′, q) = 3 + def₂(G′)` the bound `dim U(q) ≤ min(δ₂, 3)` holds with
> no citation, so a drawn equality at such a `q` **certifies** the generic value.

*Proof.* Let `a ≁ b`, and let `x` be a new vertex joined to `a` and `b`, with `q_x` off the line
`q_a q_b`.
1. **The kernel.** `P_a = P_b` already gives `P_a − P_b ∈ Kℓ_ab`. So
   `{P ∈ F(G′) : P_a = P_b} = {P ∈ F(G′ + ab) : P_a = P_b} ≅ F(G′ + ab + x)`, by (MC-13)(a) at the
   edge `ab` (with `P_x := P_a`; the three sides of the triangle `q_a q_b q_x` are independent).
   The left side does not depend on `q_x`. Hence `dim U = dim F(G′) − dim F(G′ + ab + x)`.
2. **The count.** Take a partition of `V ∪ {x}` and restrict it to `V`; call the result `𝒫′`.
   - If `𝒫′` separates `a` from `b`, the edge `ab` costs `−2`. Then `x` alone costs a further
     `3 − 4`, `x` in `a`'s part `−2`, and `x` elsewhere `−4`. The best is `−3`.
   - If `a ∼ b` in `𝒫′`, then `x` in their part costs `0`; alone it costs `−1`, elsewhere `−4`.
   So `def₂(G′ + ab + x) = max(f^sep − 3, g)`, where `f^sep` maximizes over partitions separating
   `a, b` and `g := def₂(G′/ab)`. With `f := def₂(G′) = max(f^sep, g)`:
   - if `δ₂ > 0`, then `f = f^sep` and `f − max(f − 3, f − δ₂) = min(δ₂, 3)`;
   - if `δ₂ = 0`, then `max(f^sep − 3, g) = f`.
3. **The dimensions.** (MC-4)(b) at `G′` and JJ at `G′ + ab + x` give `dim U ≥ min(δ₂, 3)`. JJ at
   `G′` and (MC-4)(b) at `G′ + ab + x` give `≤`. The certificate sentence is the second pair with
   `dim F(G′, q) = 3 + def₂` taken from the draw instead of JJ.
4. **`a ∼ b`.** `{P_a = P_b} ≅ F(G′ + x)` ((MC-13)(a) directly). The count is
   `def₂(G′ + x) = max(f^sep − 1, g)`: when `a, b` are separated, `ab` is already counted and `x`
   alone costs `−1`. This gives `min(δ₂, 1)`. ∎

> **(MC-63)** *(the structure of `δ₂`)*
> **(a)** `[PROVED]` Let `Γ` be `G′` with each class contracted to one vertex, and let `A, B` be
> the classes of `a, b`.
> - `Γ` is simple, and `2e_Γ(Y) ≤ 3|Y| − 4` for every `Y ⊆ V(Γ)` with `|Y| ≥ 2`.
> - `δ₂ = min{3(|X| − 1) − 2e_Γ(X) : X ⊆ V(Γ), A, B ∈ X}`.
> - Hence `δ₂ = 0` iff `A = B`. If `a ∼ b`, or if some edge joins `A` to `B`, then `δ₂ ≤ 1`.
> - `δ₂ = 1` iff `A ≠ B` and some `X ∋ A, B` is **tight**, i.e. `2e_Γ(X) = 3|X| − 4`.
>
> **(b)** `[PROVED-MOD]` *((MC-33); JJ at `G′`, `G′ + ab` and `G′ + ab + x`)* If `a ≁ b`, then
> `dim(U ∩ Kℓ_ab) = [δ₂ ≥ 3]`. This is (MC-30)(i) in general form: `U = Kℓ_ab` never happens.

*Proof.* (a)
- *Classes are well defined.* Two `def₂`-rigid sets sharing a vertex have a rigid union (the union
  lemma in (MC-14)'s proof). So the maximal ones are disjoint.
- *The class partition `𝒫_R` is the coarsest optimal partition.* Parts of optimal partitions are
  rigid ((MC-13)(b)'s proof), so every optimal partition refines `𝒫_R`. Merging the parts that meet
  one class never lowers `val` ((MC-13)(b)'s merge). Hence some optimal partition coarsens to
  `𝒫_R`, which is optimal.
- *At most one edge between two classes.* Two edges would make the union rigid.
- *The bound on `Γ`.* For a partition `𝒬` of `V(Γ)`,
  `val_Γ(singletons) − val_Γ(𝒬) = Σ_{X ∈ 𝒬} loss(X)`, with `loss(X) := 3(|X| − 1) − 2e_Γ(X)`.
  Every merge strictly lowers `val`, because `𝒫_R` is coarsest, so `loss(X) ≥ 1` whenever
  `|X| ≥ 2`. That is the bound.
- *The formula for `δ₂`.* In a partition with `a ∼ b`, merging along classes keeps `a ∼ b` and does
  not lower `val`. So `g = max{val_Γ(𝒬) : A ∼ B}`. Then `δ₂ = f − g = min_{X ∋ A,B} loss(X)`: take
  `𝒬 = {X} ∪ singletons`, since further parts only add loss.
- *The consequences.* If `a ∼ b`, or an edge joins `A` to `B`, then `X = {A, B}` has loss `1`.

(b) The linear map `F(G′) → U → U/(U ∩ Kℓ_ab)` has kernel `F(G′ + ab)`, since
`p̂_a^⊥ ∩ p̂_b^⊥ = Kℓ_ab`. So `dim U − dim(U ∩ Kℓ_ab) = dim F(G′) − dim F(G′ + ab)`. The count of
(MC-48)(ii), `def₂(G′ + ab) = max(f^sep − 2, g)`, makes the right side `min(δ₂, 2)` under JJ at
both graphs. Subtract this from (MC-62). ∎

**The flags.** At `P = Ψz` the plane `π_a` is `P_a`. So:
- `p_b ∈ π_a` iff `(P_a − P_b)·p̂_b = 0`;
- `p_a ∈ π_b` iff `(P_a − P_b)·p̂_a = 0`;
- `π_a = π_b` iff `P_a = P_b`.

At a generic point `u := P_a − P_b` is a generic element of `U`. So the generic orbit is:
- (iv) iff `U = 0`;
- (iii) iff `U = Kℓ_ab`;
- (ii) iff `U` lies in exactly one of `p̂_a^⊥`, `p̂_b^⊥`;
- (i) iff it lies in neither.

> **(MC-64)** `[PROVED-MOD]` *((MC-33); the generic flag orbit is combinatorial)* Let `G′` be simple
> and `q` generic. Then:
>
> | | `δ₂ = 0` | `δ₂ = 1` | `δ₂ = 2` | `δ₂ ≥ 3` |
> |---|---|---|---|---|
> | `a ∼ b` | (iv), `U = 0` | (iii), `dim U = 1` | — | — |
> | `a ≁ b` | (iv), `U = 0` | (ii) or (i), `dim U = 1` | (i), `dim U = 2` | (i), `U = K³` |
>
> For `a ≁ b` and `δ₂ = 1`:
> - **`p_b ∈ π_a` on all of `X₀(G′)` iff `b` has a neighbour in `R(a)`**, and symmetrically for
>   `p_a ∈ π_b`;
> - the two cannot both hold;
> - orbit (ii) iff one holds, orbit (i) iff neither.
>
> For `a ∼ b` the entries `δ₂ ≥ 2` are empty ((MC-63)(a)).

*Proof.* The row `a ∼ b`: `U ⊆ Kℓ_ab ⊆ p̂_a^⊥ ∩ p̂_b^⊥`, and (MC-62) gives its dimension.

The row `a ≁ b`:
- *`δ₂ = 0`.* `U = 0`.
- *`δ₂ ≥ 3`.* `U = K³` lies in no plane.
- *`δ₂ = 2`.* `dim U = 2` and `ℓ_ab ∉ U` by (MC-63)(b). Both `p̂_a^⊥` and `p̂_b^⊥` are planes
  containing `ℓ_ab`, so `U` equals neither.
- *`δ₂ = 1`.* `U = Ku` with `ℓ_ab ∉ U`, so orbit (iii) is excluded.
- *Not both incidences.* Suppose `b` has a neighbour `c ∈ R(a)` and `a` has a neighbour
  `d ∈ R(b)`. Then `cb` and `ad` are distinct edges, since `a ≁ b`, and they join `R(a)` to `R(b)`.
  That contradicts (MC-63)(a).

*The rule at `δ₂ = 1`, "if".* Let `c ∈ N(b) ∩ R(a)`. JJ at a rigid subgraph containing `a` and `c`
gives `P_a = P_c` on `F(G′)` ((MC-13)(c), "if"). So `u = P_c − P_b ∈ Kℓ_bc ⊆ p̂_b^⊥`.

*"Only if".* Suppose `b` has no neighbour in `A := R(a)`, and put `B := R(b)`.
- *Case 1: some edge `a′b′` joins `A` to `B`.* Then `b′ ≠ b`. As above, `u ∈ Kℓ_{a′b′}`, and
  `ℓ_{a′b′} · p̂_b = det(p̂_{a′}, p̂_{b′}, p̂_b) ≠ 0` at generic `q`, since `b ∉ {a′, b′}`.
- *Case 2: no edge joins `A` to `B`.* Contract the classes of size `≥ 2` one at a time. (MC-66)
  applies at each step. *(Second reading, 2026-09-25: why.)* For a `def₂`-rigid `R`, a set `S ∋ v*`
  of `G′/R` is `def₂`-rigid iff `(S − v*) ∪ R` is `def₂`-rigid in `G′`, because merging the parts
  that meet `R` never lowers `val`; a set avoiding `v*` spans the same graph in both. So the classes
  of `G′/R` are `{v*}` and the other classes of `G′`, each still a maximal `def₂`-rigid set on `≥ 3`
  vertices; `G′/R` is simple (the first bullet of (MC-66)'s proof); and the images of `a`, `b` never
  lie in one class, since `A ≠ B`. Hence `U ⊆ p̂_b^⊥` would pass to `U_{a*b*}(Γ) ⊆ p̂_{b*}^⊥` in the
  fully contracted `Γ` of (MC-63)(a). Contraction keeps `def₂` and the constrained maximum `g`, so it
  keeps `δ₂ = 1`; and `a* ≁ b*`, since no edge joins `A` to `B`. (MC-66) is used in this direction
  only: its converse is false (MC-160).
  - (MC-63)(a) gives a tight `X ∋ a*, b*` in `Γ`.
  - `U_{a*b*}(Γ) ⊆ U_{a*b*}(Γ[X])` by restriction of flexes. Both are 1-dimensional by (MC-62), since
    `δ₂` is `1` in both.
  - So `U_{a*b*}(Γ[X]) ⊆ p̂_{b*}^⊥` at generic positions. This contradicts (MC-65). ∎

> **(MC-65)** `[PROVED-MOD]` *((MC-33); tight rod linkages)* Let `Γ` be simple and **tight**:
> `2|E| = 3|V| − 4`, and `2e(Y) ≤ 3|Y| − 4` for every `Y` with `|Y| ≥ 2`. Then for every
> non-adjacent pair `a, b`, at generic `q`, `U_{ab} ⊄ p̂_b^⊥`.

*Proof.* Strong induction on `|V|`. **Setup.**
- Every vertex of `Γ` has degree `≥ 2`: removing a vertex of degree `1` would break the bound on
  `V − v`.
- `Σ(deg − 3) = −4`, so `Γ` has at least 4 vertices of degree 2. Pick one, `w ∉ {a, b}`.
- Its neighbours `y₁, y₂` are not adjacent, since a triangle breaks the bound.

*Step 1 (the condition passes to `Γ − w`).*
- By (MC-30)'s formula 1, restriction identifies `F(Γ, q)` with `ker φ_x ⊆ F(Γ − w)`, where
  `x = p̂_w` and `φ_x(P) := μ(P)·x` with `μ(P) := P_{y₁} − P_{y₂}`.
- Put `ψ(P) := (P_a − P_b)·p̂_b` on `F(Γ − w)`. It is independent of `q_w`.
- Suppose `U_{ab}(Γ) ⊆ p̂_b^⊥` on a dense open set of pictures. Fix a generic `q_{V−w}`. For `q_w` in
  a dense open subset of `K²`, `ψ` vanishes on `ker φ_{p̂_w}`, so `ψ ∧ φ_{p̂_w} = 0` in
  `Λ²F(Γ − w)*`.
- That expression is linear in `x` and vanishes on a dense subset of the plane `{x₃ = 1}`. So it
  vanishes for every `x ∈ K³`.
- If `ψ ≠ 0`, this gives `μ^T x ∈ Kψ` for all `x`, hence `dim U_{y₁y₂}(Γ − w) = rank μ ≤ 1`.
- But `δ₂^{Γ−w}(y₁, y₂) ≥ 2`. Any `X ∌ w` containing `y₁, y₂` has `2(e(X) + 2) ≤ 3(|X| + 1) − 4`,
  so `loss(X) ≥ 2`, and (MC-62) gives `dim U_{y₁y₂} ≥ 2`. So `ψ = 0`: `U_{ab}(Γ − w) ⊆ p̂_b^⊥`.

*Step 2 (descent).* `Γ − w` has no rigid subgraph, so its classes are singletons and
`δ := δ₂^{Γ−w}(a, b) = min_{X ⊆ V−w, X ∋ a,b} loss(X) ≥ 1`.
- If `δ ≥ 3`, then `U = K³`.
- If `δ = 2`, then `U` is a plane without `ℓ_ab` ((MC-63)(b)), so it is not `p̂_b^⊥`.
- If `δ = 1`, take `X ∌ w` with `loss(X) = 1`. It is tight, `a ≁ b` in it, and
  `U_{ab}(Γ − w) = U_{ab}(Γ[X])`: both are 1-dimensional by (MC-62), and restriction gives `⊆`.
  Then `U_{ab}(Γ[X]) ⊆ p̂_b^⊥` at generic `q_X`, against the induction hypothesis, since
  `|X| < |V|`.

No base case is needed: the smallest tight graph with a non-adjacent pair, `C₄` (`K₂` is tight
too, but has no such pair; second reading), falls under `δ = 2` in Step 2. There
`Γ − w` is a path, and `loss({a, d, b}) = 2`. Equivalently, directly: `U = Kℓ_cd` and
`det(p̂_c, p̂_d, p̂_b) ≠ 0`. ∎

> **(MC-66)** `[PROVED-MOD]` *((MC-33); contraction transfers the incidence; JJ at `R` and at
> `G′/R`)* Let `R` be a maximal `def₂`-rigid set of `G′` with `|R| ≥ 3`, and let `x ≠ y` not both
> lie in `R`. Write `x̄, ȳ` for their images in `G′/R` (`v*` if in `R`). If `U_{xy}(G′) ⊆ p̂_y^⊥`
> at generic `q`, then `U_{x̄ȳ}(G′/R) ⊆ p̂_ȳ^⊥` at generic pictures of `G′/R`. (The conclusion is
> vacuous when `x̄ ∼ ȳ`.)

*Proof.*
- **The limit space.** `G′/R` is simple by maximality: a vertex with two neighbours in `R` would
  join `R`. `def₂(R) = 0` gives additivity (merge the parts meeting `R`). So (MC-69)(b) applies to
  the two-scale family `q(t) = (q_O, tδ)`. At generic `(q_O, δ)` the flat limit `W₀` of the
  rescaled flex spaces `ker N(t)` equals `ker N₀`.
- **Its shape.** JJ at `R`: `F(R, δ)` is the constants. So the slope space `S` is the diagonal,
  and by (MC-69)(a)'s description
  `ker N₀ ≅ {(s, γ̃) flat core} × F⁰(G′/R, q′)`. Here
  `F⁰ := {X ∈ F(G′/R, q′) : X_{v*}(Q) = 0}`, coupled by `s = slope of X_{v*}`, with `γ̃` free.
- **The limit functional.** Put `ψ_t(P) := (P_x − P_y)·p̂_y(t)`, in the rescaled coordinates. It
  is `ψ₀ + tψ₁`. It vanishes on `ker N(t)` for all but finitely many `t`, hence on
  `ker_{K(t)} N(t)`. A basis of that kernel can be taken polynomial in `t`, and a polynomial with
  infinitely many zeros is `0`.
- **It vanishes on `W₀`.** Every `w₀ ∈ W₀` is `w(0)` for a power-series solution of
  `N(t)w(t) = 0`, which lies in `ker_{K((t))} N(t)`. So `ψ₀(w₀) = 0`.
- **The three cases.** In each, `ψ₀` is the `G′/R` condition on `F⁰`, read from the rows listed
  in (MC-69):
  - `x, y ∉ R`: `ψ₀ = (X_x − X_y)·p̂_y`, where attachments carry their far representatives
    `(a_u, 0)`, which are the `G′/R` values;
  - `x ∈ R`: `P_x = (ã_x, tγ̃_x) → (s, 0) = X_{v*}`;
  - `y ∈ R`: `p̂_y(t) = (tδ_y, 1) → Q̂` and `P_y → X_{v*}`, so `ψ₀ = (X_x − X_{v*})(Q)`.
- **The conclusion.** `F(G′/R) = F⁰ ⊕ K·(0, 0, 1)`, and the constant adds nothing to a relative
  motion. So the condition holds at `q′ = (q_O, Q)` for generic `q_O`, and by translation at
  generic pictures. ∎

**Part II — the contraction step without certificates.**

> **(MC-67)** `[PROVED]` *(combinatorics; multigraphs allowed; (a)–(c) each re-derived at the second
> reading, 2026-09-25, which found (b) to be an identity, `val_G = val_H + val_{G/H} − 2N` for the
> induced partitions)*
> **(a)** `[PROVED]` `val` is supermodular on the partition lattice, so the `def₂`-optimal partitions of any
> multigraph form a sublattice. There is a finest and a coarsest optimal partition, and the
> coarsest is the class partition.
> **(b)** `[PROVED]` For every `W ⊆ V`: `def₂(G) ≤ def₂(H) + def₂(G/H)`, and likewise for `def₃`.
> **(c)** `[PROVED]` *(additivity is a partition condition)* Let `𝒮` be the finest optimal partition of
> `G/H`, `𝒮* ∋ v*` its part, and `T := 𝒮* ∖ {v*}`. Let `Φ` be the graph on `T ∪ W` whose edges are
> the edges of `G` inside `T` or between `T` and `W`. Then **additivity holds iff every connected
> component of `Φ` meets at most one class of `H`.**
> In particular it holds when `T = ∅` (some optimal partition of `G/H` has `{v*}` as a part), and
> when the core vertices with attachments lie in one class of `H` (e.g. `def₂(H) = 0`, which
> gives (MC-59)(c)'s count).

*Proof.*
(a) *The two inequalities.*
- *Block counts.* Let `B` be the bipartite graph on `𝒫 ⊔ 𝒫′` with one edge per nonempty
  intersection. The blocks of `𝒫 ∧ 𝒫′` are the edges of `B`, and the blocks of `𝒫 ∨ 𝒫′` are its
  components. So `|𝒫 ∧ 𝒫′| + |𝒫 ∨ 𝒫′| ≥ |𝒫| + |𝒫′|`.
- *Crossing edges.* Edge by edge,
  `[crosses 𝒫 ∧ 𝒫′] + [crosses 𝒫 ∨ 𝒫′] ≤ [crosses 𝒫] + [crosses 𝒫′]`.

*The conclusion.* So `val(𝒫 ∧ 𝒫′) + val(𝒫 ∨ 𝒫′) ≥ val(𝒫) + val(𝒫′)`. Hence two maximizers have
a maximizing meet and join. The coarsest optimal partition is the class partition by (MC-63)(a)'s
proof.

(b) Let `t` parts of `𝒫` meet `W`. Then `𝒫|_W` has `t` parts, and `𝒫/W` (merge them, put `v*`
there) has `|𝒫| − t + 1` parts.
- `d_G(𝒫) = d_H(𝒫|_W) + d_{G/H}(𝒫/W) + (#non-core edges joining two distinct W-meeting parts)`.
- So `val_G(𝒫) ≤ val_H(𝒫|_W) + val_{G/H}(𝒫/W) − 2·(that number)`.
- The same computation holds with `(6, 5)`.

(c) **(⟸)** Let `𝒬` be the class partition of `H`, which is optimal.
- *The partition.* Keep the parts of `𝒮` other than `𝒮*`. Replace `𝒮*` by the parts `Y ∪ T_Y`,
  `Y ∈ 𝒬`, where `T_Y` is the set of `T`-vertices whose `Φ`-component meets `Y`. `T`-vertices in
  components meeting no `W`-vertex go into any one part; they have no edges to `W` or to other
  components.
- *No new crossings.* Every `Φ`-edge now lies inside a part. Every other non-core edge crosses
  exactly when it crosses `𝒮`.
- *The value.* `val_G = val_H(𝒬) + val_{G/H}(𝒮) = def₂(H) + def₂(G/H)`. Now use (b).

**(⟹)** Suppose `val_G(𝒫) = def₂(H) + def₂(G/H)`.
- *Equality in (b).* It forces `𝒫|_W` optimal, `𝒫/W` optimal, and no non-core edge between two
  distinct `W`-meeting parts.
- *Components of the larger graph.* Let `T′` be the outside vertices of the `W`-meeting parts.
  Each component of `Φ_{T′}` lies in one `W`-meeting part, so it meets one part of `𝒫|_W`. That
  part lies in one class, because `𝒫|_W` refines the class partition.
- *Back to `T`.* `𝒮` refines `𝒫/W`, so `T ⊆ T′` and `Φ_T ⊆ Φ_{T′}`. ∎

**Added at the second reading (2026-09-25).**

> **(MC-159)** `[PROVED]` *(Jackson–Jordán's flex form reduces to (H))* If `dim F(G, q) = 3 + def₂(G)`
> at generic `q` holds at every graph satisfying (H), it holds at every finite simple graph.

*Proof.* A degree-1 vertex adds 1 to both sides: 3 new coordinates and 2 constraints, and in the
partition count it is best as a singleton (`+3 − 2`), while any partition of `G` restricts to one of
`G − v` losing at most 1. An isolated vertex adds 3 to both sides. A disjoint union adds the flex
spaces, and `def₂(G₁ ⊔ G₂) = def₂(G₁) + def₂(G₂) + 3`. Removing degree-`≤ 1` vertices and splitting
components ends at graphs satisfying (H) or at single vertices. ∎

> **(MC-160)** `[PROVED]` *(the converse of (MC-66) is false)* Let `G′` be two triangles `{0, 2, 4}`
> and `{1, 3, 5}` joined by the edge `05`, `R = {0, 2, 4}`, and `(x, y) = (1, 2)`. In `G′`,
> `U_{12} = Kℓ_{05} ⊄ p̂_2^⊥` at generic `q`. In `G′/R`, `ȳ = v*` is adjacent to `5 ∈ R(1)`, so by
> (MC-64)'s "if" `U_{x̄ȳ}(G′/R) ⊆ p̂_{v*}^⊥`. (MC-64)'s proof uses (MC-66) only in the stated
> direction.

> **(MC-161)** `[MEASURED]` *(`mc15check.py`; stdlib only, exact `Fraction`s, string seeds, so the
> output is independent of `PYTHONHASHSEED`; shares no code with the other drivers)* Independent
> checks of (MC-62)–(MC-67), 0 failures in every mode:
> - `--allgraphs 7` (every simple graph on 2..7 vertices, counts asserted against OEIS A000088;
>   24 684 pairs): (MC-62) certified at 24 684/24 684; (MC-63)(a) exact at 24 684/24 684 and (b) at
>   12 342/12 342; (MC-64)'s orbits agree at 24 684/24 684, and its `δ₂ = 1` "only if" pairs are
>   certified off at 2 827 (Case 1: 2 381; Case 2, trivial: 272; Case 2, contracting: 174).
> - `--mc66 7`: 1 590 non-vacuous pairs. "On in `G′`" implies "on in `G′/R`" at 39/39, with 0
>   candidate counterexamples; the converse fails at 60 pairs ((MC-160)).
> - `--blowup 60`: 60 seeded blow-ups of tight graphs by rigid blobs, 7 to 31 vertices. (MC-64)
>   holds at 1 962 "if" pairs, 6 052 Case-1 pairs and 12 664 Case-2 pairs (1–8 contractions);
>   (MC-66) blob by blob at 5 054 pairs, 0 counterexamples.
> - `--tight 10 60`, `--tight 12 20`: (MC-65) certified at 3 840/3 840 and 2 000/2 000 pairs.
> - `--mc67 6 300`: (MC-67)(c)'s equivalence at every `W` of every connected simple graph on `≤ 6`
>   vertices and 300 seeded multigraphs, 15 632/15 632; (a) and (b) throughout.
>
> Support: the populations named. A draw that certifies `U ⊄ p̂_b^⊥` is a certificate; "on at every
> draw" is draw-level only (the script's docstring).
> `python3 notes/scripts/w4/mc15check.py --allgraphs 7` (~41 s), `--exh 7` (~33 s), `--mc66 7`,
> `--blowup 60`, `--tight 10 60`, `--tight 12 20`, `--mc67 6 300` (each ≤ 5 s).

> **(MC-68)** `[PROVED-MOD]` *((MC-33); (MC-39)(i) is additivity)* Let `G` be simple and
> `W ⊊ V` with `|W| ≥ 2`. Let `ρ_W : F(G, q) → F(H, q|_W)` be restriction, and
> `K := ker ρ_W = {P : P|_W = 0}`. This is the lead's "liftings vanishing on `W`": every core
> plane horizontal at height 0, every attachment at height 0, with **point** constraints
> `P_u(q_{c(u)}) = 0`.
> **(a)** `dim K ≥ def₂(G/H)` at every edge-injective `q` (multigraph `G/H` allowed).
> **(b)** If `G/H` is simple, then `dim K = def₂(G/H)` at generic `q`, mod JJ at `G/H`.
> **(c)** If `ρ_W` is onto at generic `q`, then additivity holds, mod JJ at `G`.
> **(d)** If `G/H` is simple and additivity holds, then `ρ_W` is onto at generic `q`, mod JJ at `H`
> and `G/H`.
>
> At admissible pictures with `H` of minimum degree `≥ 2`, `ρ_W` onto is exactly (MC-38)'s (i)
> (the interpolant of `N_G[c]` restricts to that of `N_H[c]`). So **(i) ⟺ additivity** at generic
> `q`, and (MC-59)(a)'s `def₂(H) ≤ def₂(G)` is the weaker consequence `def₂(G/H) ≥ 0`.

*Proof.*
- **`K` as a framework.** Let `Φ` be the body-and-pin framework on `G/H` with pin `ℓ_uc` on a
  boundary edge `uc` (the actual core point) and `ℓ_uw` on outside edges. Then
  `K ≅ {X ∈ F_Φ : X_{v*} = 0}`, which has dimension `dim F_Φ − 3`.
- **(a).** (MC-4)(b)'s partition bound holds for any body-and-pin framework with two rows per
  edge, since the rows inside parts kill part-wise constants. So `dim F_Φ ≥ 3 + def₂(G/H)`.
- **(b).** Take `q(t) = (q_O, tδ)`. Then `ℓ_uc(t) → ℓ_uQ ≠ 0`. Simplicity makes the boundary pins
  sit at distinct attachments, so `Φ(0)` is the rod framework of `G/H` at `q′ = (q_O, Q)`. Kernel
  dimension is upper semicontinuous along the curve. So at generic `t`,
  `dim F_{Φ(t)} ≤ dim F(G/H, q′) = 3 + def₂(G/H)`, using JJ at `G/H`.
- **The identity used below.** `dim F(G) = dim im ρ_W + dim K`.
- **(c).** Ontoness gives `dim F(G) = dim F(H) + dim K ≥ (3 + def₂(H)) + def₂(G/H)`, by
  (MC-4)(b) and (a). With JJ at `G` the left side is `3 + def₂(G)`. Then (MC-67)(b) gives equality.
- **(d).** `dim im ρ_W ≥ (3 + def₂(G)) − def₂(G/H)` by (MC-4)(b) and (b). By additivity this is
  `3 + def₂(H)`, which is `dim F(H)` by JJ at `H`. So `im ρ_W = F(H)`. ∎

> **(MC-69)** *(the no-jump condition (ii))* Let `G` be simple, `W ⊊ V` with `|W| ≥ 2` (rigidity
> not needed), and `G/H` simple. Take Step MC12's family `q(t) = (q_O, tδ)`, `Q` the origin.
> Write `P_v = (a_v, t g_v)` for `v ∈ N[W]` and `P_v = (a_v, g_v)` otherwise, and divide by `t`
> the rows evaluated at core points. This gives `N(t) = N₀ + tN₁` with `ker N(t) ≅ F(G, q(t))`
> for `t ≠ 0`. At admissible pictures, Step MC4's bijection identifies `ker N₀` with `ker M₀`:
> the substitution is `z_c = tζ_c`, `γ_v = tγ̃_v`.
> **(a)** `[PROVED]` *(exact, no genericity)*
>
>   `dim ker N₀ = dim F(H, δ) + dim F(G/H, q′) − 3 − (dim S − dim(S ∩ T))`,
>
> where `W_att` is the set of core vertices with attachments, and
> - `S := {(ã_c)_{c ∈ W_att} : P̃ ∈ F(H, δ)}`: the slopes of the magnified core flexes;
> - `Y′ := {(s, P_O) : outside pins at q_O, and P_u − (s_{c(u)}, 0) ∈ Kℓ_uQ for each attachment u}`;
> - `T` is the projection of `Y′` to `s`.
>
> **(b)** `[PROVED-MOD]` *((MC-33); JJ at `H` and at `G/H` only)* **If additivity holds, then at
> generic `(q_O, δ)` there is no jump**: `dim ker N₀ = dim F(G, q(t)) = 3 + def₂(G)`. Two
> by-products:
> - `S ⊆ T`;
> - JJ at `G` itself follows from JJ at `H` and `G/H`.
>
> **(c)** `[PROVED-MOD]` *((MC-33))* In general, `0 ≤ dim S − dim(S ∩ T) ≤ ε`, and (ii) holds iff
> `dim S − dim(S ∩ T) = ε`.

*Proof.* (a) **The rows of `N₀`.**
- The core rows at `δ` say `P̃ := (a, g)|_W ∈ F(H, δ)`.
- A boundary edge `uc` gives two rows. `(P̃_u − P̃_c)·δ̂_c = 0` contains `g_u`. `G/H` is simple, so
  this is the only `t`-free row containing `g_u`, and it only determines `g_u`. The other row is
  `(a_u − ã_c)·q_u = 0`.
- Outside rows use the far representatives `(a_u, 0)` of attachments.

**The fibre product.** Hence `ker N₀ ≅ F(H, δ) ×_{(K²)^{W_att}} Y′`, glued along `σ(P̃) = s`, and
`dim = dim F(H) + dim Y′ − dim(S + T)`.
- `ker(Y′ → s) = {P_u ∈ Kℓ_uQ} ≅ {X ∈ F(G/H, q′) : X_{v*} = 0}`, of dimension
  `dim F(G/H, q′) − 3`.
- So `dim Y′ = dim F(G/H) − 3 + dim T`, which gives the formula.

(b) **The chain.** Let `W₀` be the flat limit: `W₀ ⊆ ker N₀`, and `dim W₀` equals
`dim F(G, q(t))` at generic `t`.
- (MC-4)(b): `dim W₀ ≥ 3 + def₂(G)`.
- (a) with JJ at `H` and `G/H`: `dim ker N₀ ≤ dim F(H, δ) + dim F(G/H, q′) − 3 = 3 + def₂(H) + def₂(G/H)`.
- Additivity: the right side is `3 + def₂(G)`.

So every inequality in the chain is an equality.

(c) JJ at `G` gives `dim ker N₀ ≥ dim W₀ = 3 + def₂(G)`. Compare with (a) under JJ at `H` and
`G/H`. ∎

Recorded no-jump runs with `ε > 0` are the case `codim = ε` of (c); the jump at `x7_1716440` is
`codim = 0 < ε = 1`; see (MC-74).

> **(MC-70)** `[PROVED]` *(maximal cores)* Let `W` be maximal among **all** proper `def₃`-rigid
> sets of `G`, with `G/H` simple. Then additivity holds unless **the trivial partition is the only
> `def₂`-optimal partition of `G/H`**. That exceptional case forces:
> - `def₂(G/H) = def₃(G/H) = def₃(G) = 0`;
> - every outside vertex has degree `≥ 3` in `G`;
> - and additivity then reads `def₂(G) = def₂(H)`, i.e. (MC-67)(c) with `T = O`.
>
> In particular: **if `def₃(G) > 0`, or `def₂(G/H) > 0`, or some outside vertex has degree 2,
> then every maximal proper rigid `W` with `G/H` simple is additive.**

*Proof.*
- **`T ∪ W` is rigid.** Take `𝒮`, `𝒮*`, `T` as in (MC-67)(c). `(G/H)[𝒮*]` is `def₂`-rigid, being a
  part of an optimal partition. It is therefore connected and `def₃`-rigid ((MC-5)(i)). It is the
  contraction of `G[T ∪ W]` by `W`. So (MC-67)(b) with `(6, 5)` gives
  `def₃(G[T ∪ W]) ≤ def₃(H) + 0 = 0`.
- **Maximality.** If `𝒮* ≠ V(G/H)`, then `T ∪ W` is proper, so maximality gives `T = ∅`, and
  (MC-67)(c) holds trivially.
- **The exceptional case.** Otherwise `𝒮 = {V(G/H)}`. Then `def₂(G/H) = 0`, and `def₃(G) =
  def₃(G/H) = 0` by (MC-35).
- **Outside degrees.** Suppose an outside `x` had degree 2. Then for every partition `𝒫` of
  `V(G/H) − x` with `|𝒫| ≥ 2`, the partition `𝒫 + {x}` is nontrivial, so
  `val(𝒫) − 1 = val(𝒫 + {x}) ≤ −1`.
  - So `(G/H) − x` is `def₂`-rigid.
  - So `W ∪ (O − x)` is a proper rigid set containing `W`.
  - It is proper since `|O| ≥ 2`; `|O| = 1` would make `x` a leaf. This contradicts maximality. ∎

> **(MC-71)** `[PROVED-MOD]` *((MC-33); the certificate-free CONTRACT step; JJ at `H` and at `G/H`;
> resting on (MC-34)–(MC-39), second-read 2026-09-24)* Let `G` satisfy (H) and
> be 2-edge-connected. Let `W` be a proper rigid set (`def₃(G[W]) = 0`) with `G/H` simple and
> **`def₂(G) = def₂(H) + def₂(G/H)`** (equivalently, (MC-67)(c)'s partition condition). **If `X₀(H)`
> and `X₀(G/H)` attain, then `X₀(G)` attains.** By (MC-70) the count is automatic at a maximal `W`
> outside the exceptional case.

*Proof.* A generic picture lies in `U(G)`, and its restriction lies in `U(H)`. There (MC-68)(d)
gives (MC-38)'s (i). (MC-69)(b) gives (MC-37)'s (ii) at generic `(q_O, δ)`, where `q(t) ∈ U(G)`.
Then (MC-39) applies verbatim. ∎

(MC-59)(d) is the case `def₂(H) = 0`. It needs no JJ at `G`, as the second reading of (MC-59) also
found ((MC-59)(c3)): (MC-69)(b) supplies it.

> **(MC-72)** `[PROVED-MOD]` *((MC-33); the step table's per-graph certificates, made combinatorial)*
> By (MC-62) and (MC-64), for an ear with ends `a, b` on `G′`:
> - (MC-18)(b)'s dominance at `k = 1`: `dim U ≠ 1` holds iff `δ₂ ≠ 1` (for `a ∼ b`: iff `δ₂ = 0`).
> - (MC-46)'s cell "orbit (i)/(ii) with `dim U ≠ 1`": holds iff `a ≁ b` and `δ₂ ≥ 2`, and then the
>   orbit is (i). (MC-54)'s `k = 1` condition `dim U ≥ 2` is the same.
> - (MC-51)(a) (`k = 2`, `dim U = 1`): exactly `δ₂ = 1`. Its orbit-(iii) part is exactly `a ∼ b`.
> - (MC-51)(b) (orbit (iv)): exactly `δ₂ = 0`, which forces `δ = 0`.
> - (MC-51)(c): exactly `a ≁ b`, `δ₂ ≥ 2`, `1 ≤ δ ≤ 4`.
> - CONTRACT: exactly (MC-71)'s count.
>
> So the certificate half of (MC-61) reduces, mod JJ, to partition counts. The two ear cells that
> are not steps, (MC-51)(a) and (c) at `δ ≥ 1`, remain; this step does not address them.

**Part III — checks** (targeted, exact; `PYTHONHASHSEED=0`, seed `20260924`).

> **(MC-73)** `[MEASURED]` *(`orbitrule.py`; the orbit rule against the recorded cells)* Pictures
> were certified by `dim F(G′, q) = 3 + def₂(G′)`, exact ℚ, with up to 3 per instance. At a
> certified picture, a drawn `dim U` equal to `min(δ₂, 3)` certifies the generic value ((MC-62)).
> So does "`p_b ∉ π_a`", which is an open condition. The closed predictions (ii), (iii), (iv) match
> at draws, and are proved by the "if" halves.
> - **Every `k = 2` chain of every simple 2EC graph on ≤ 8 vertices** (491 cells; (MC-57)'s 31
>   evaluated cells are among them) matches (MC-62) and (MC-64) with 0 mismatches:
>   - (i): 17 with `dim U = 1`, 3 with `dim U = 2`, 3 with `dim U = 3`;
>   - (ii): 6, all `a ≁ b`, `δ₂ = 1`;
>   - (iii): 20, **all `a ∼ b`**, `δ₂ = 1`;
>   - (iv): 442, `δ₂ = 0`.
> - **The first 60 split-off instances** of Step MC11 (`G′ = G − x`, simple 2EC on 4..7 vertices):
>   60/60 match. `δ₂ = 0/1/2/3` in 18 / 13 / 18 / 11 instances, the 13 split 10 in (ii) and 3 in
>   (i). This explains Step MC11's histogram:
>   - `dim U = 0 ⇔ δ₂ = 0 ⇒ δ = 0`;
>   - `dim U = 1 ⇒ c = 1`, since `ℓ_ab ∉ U`;
>   - `dim U ≥ 2 ⇒ c = 2`.
>
>   Its "`δ ≤ 1` when `dim U = 1`" is **not** explained here.
> - **Every tight graph with `n ≤ 8`**, for (MC-65) (1 + 2 + 16 graphs, 612 ordered non-adjacent
>   pairs): `p_b ∉ π_a` certified at 612/612.
> - Worked instances:
>   - (i), `dim U = 1`: `G′ = C₄`, `a, b` opposite (`U = Kℓ_cd`).
>   - (iii): `G′ = C₄`, `a ∼ b`.
>   - (ii): `x8_165168161`, where `G′` is two triangles `{4,5,6}`, `{2,3,7}` joined by the edge
>     `6–7`, `a = 5`, `b = 7`. Here `b` has neighbour `6 ∈ R(a)`, and `U = Kℓ_67 ⊥ p̂_7`.

> **(MC-74)** `[MEASURED]` *(`contractcheck.py`, `kerm0.py`; the contraction counts against coreshrink)*
> Each run below is one targeted `coreshrink.run_member` (relaxed), exact.
> - **(MC-41)'s recorded failures violate additivity.**
>   - `x7_1716440`, `W = {0,1,3,4}` (`C₄`): `def₂ = 0 / 1 / 0` for `G / H / G/H`, not additive.
>     coreshrink: (i) fails, and (ii) fails (the recorded jump).
>   - Its other simple-quotient `W = {2,5,6}` is additive, and both hold.
>   - The 11 `C₄` fallback runs have `def₂(G) = 0 < 1 = def₂(H)`, so they are not additive, by the
>     count alone.
> - **The other named cases.**
>   - `x8_60101824`, its four 5-cycle cores: `1 / 2 / 0`, not additive; (i) fails, (ii) holds.
>   - W19 and R20: additive **with `def₂(H) > 0`**: `10 = 1 + 9` and `11 = 2 + 9`. Both (i) and
>     (ii) hold.
> - **Additivity is sharper than (MC-59)(a)** `[CONSTRUCTED contractcheck.py --extra]`. `K4pend`
>   is a `C₄` core; a triangle `u₁u₂u₃` with `u_i` joined to three core vertices, so `G/H ⊇ K₄`;
>   and a pendant `C₄` at `u₁`.
>   - The counts are `1 / 1 / 1`: `def₂(H) ≤ def₂(G)`, but `1 ≠ 1 + 1`.
>   - coreshrink finds (i) failing (`dim proj_W L_G = 3 < 4`) and the core flexible (17/18) at all
>     3 draws. As (MC-68)(c) predicts, the core is not rigid at `X₀(G)`'s generic point.
>   - (ii) holds there (`codim = ε = 1`).
> - **Small graphs** (`--hunt 8`): every simple 2EC graph on ≤ 8 vertices with `def₂(G) ≥ 1`, every
>   proper rigid `W` with `G/H` simple, 291 pairs.
>   - (MC-67)(c)'s partition form agrees with the count at 291/291.
>   - Non-additive pairs occur only with `def₂(H) > def₂(G)` (15).
>   - coreshrink on 6 per class: additive gives (i) and (ii) at 12/12, non-additive gives (i)
>     failing at 6/6.
> - **Maximal `W`**, for (MC-70) (`--maximal 8`): all 815 maximal simple-quotient pairs on ≤ 8 vertices
>   are additive. The exceptional case never occurs.
> - **The kernel identity** of (MC-69)(a) (`kerm0.py`): asserted exactly against coreshrink's `dim ker M₀` at 287
>   instances (every simple-quotient rigid `W` on ≤ 7 vertices, plus the named ones).
>   - 270 have `ε = 0`, all with no jump, as (MC-69)(b) predicts.
>   - 17 have `ε > 0`: 14 with `codim = ε` (no jump) and 3 with `codim < ε` (jump), as (MC-69)(c)
>     allows.

**Drivers** (all at `PYTHONHASHSEED=0`, seed `20260924`, exact ℚ; `coreshrink`'s sampler for the
contraction runs; sampler support in each docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/orbitrule.py --cells8 --split7 60 --sparse 8` | (MC-73): 491 `k = 2` cells, 0 mismatches; 60/60 split-off instances; (MC-65) at 612/612 pairs of the 19 tight graphs on ≤ 8 vertices | ~16 s |
| `python3 notes/scripts/w4/contractcheck.py --named --extra --hunt 8 --runs 6 --maximal 8` | (MC-74): the named cores; `K4pend`; 291 pairs, (MC-67)(c) agrees at every one; 815 maximal pairs, all additive | ~28 s |
| `python3 notes/scripts/w4/kerm0.py` | (MC-69)(a)'s identity asserted at 287 instances | ~14 s |

