*Staged verbatim from writer I's message of 2026-09-25; see `README.md` in this directory. The
driver it names is already ported to `notes/scripts/w4/jjbuild.py`, with the bootstrap fixed.*

**Verdict.** Yes: with the write-up below, (MC-33)(i) is a written proof rather than a table of verdicts. It is a one-writer proof, so it should get the corpus's usual second reading before its status moves to `PROVED`. That second reading is the only remaining step, and nothing mathematical is left open.

- **R2 in the induction.** R2 is built into the induction statement itself, (NEW-I11): every construction outputs a *non-degenerate* pin-collinear realization. The TR's Lemma 4.2 is never used. Its statement comes back as a corollary, (NEW-I26); its TR proof fails on an explicit witness.
- **Free parameters.** Every free parameter of every construction is named, with its excluded values or excluded closed set.
- **Combinatorial inputs.** The brick and superbrick lemmas (TR 3.2, 3.3) and every claim's deficiency inequality are re-proved here. None of them uses Tutte–Nash-Williams.
- **What was not found.** No step of the TR needs an order, a metric or a restriction on the characteristic.
- **Gaps the TR leaves implicit.** Beyond R0, R1 and R2, the proof closes four:
  - the base cases `K₂` and `K₃`;
  - `v₁ ≠ v₂` in the final gluing (otherwise `G₂` has a double edge);
  - the TR's undefined `L_1` in Case 2, replaced by an auxiliary line `M` (this also makes the move of `q₅(u₂)` unnecessary);
  - pin-distinctness conditions that the TR's ε-moves leave unstated.
- **Driver.** A new exact driver, `jjbuild.py`, runs every construction at 25 instances over GF(2¹⁶), GF(3¹⁰) and GF(10 007). Every intermediate rank step holds, and all 75 outputs are non-degenerate with rank `t(G)`.

---

#### Jackson–Jordán over an infinite field: the written proof (2026-09-25)

*This section fills (MC-33)(i)'s three gaps: R2 in full, a written field-general proof, and the combinatorial inputs. Page numbers are the TR's printed numbers (printed = pdf − 1). Labels `(NEW-I…)` are placeholders for the coordinator to renumber.*

**Notation.**
- `K` is an infinite field of any characteristic. On `K²`, `x·y := x₁y₁ + x₂y₂` is bilinear and non-degenerate.
- `J(x₁, x₂) := (x₂, −x₁)`. Then `x·Jx = 0` and `a·Jb = det(a, b)` in every characteristic.
- A **line** is `{x : ax₁ + bx₂ + c = 0}` with `(a, b) ≠ 0`. Two lines are **parallel** if their `(a, b)` are proportional. Two distinct lines through a common point are not parallel, and they meet only there.
- Graphs are finite and simple. For `G = (V, P)`: `V` are the bodies, `P` the pins, `n = |V|`, `m = |P|`, `E(v)` the edges at `v`, and `d(v) = |E(v)|`.
- A **framework** `(H, q)` is a graph `H = (W, F)` with `q : W → K²`.
  - `R(H, q)` is the rigidity matrix (TR p.3), `r(H, q)` its rank, and `Z(H, q)` its null space: the `m : W → K²` with `(q(a) − q(b))·(m(a) − m(b)) = 0` on every edge.
  - `df := dim Z = 2|W| − r`.
  - `(H, q)` is **infinitesimally rigid** if `|W| ≥ 2` and `r = 2|W| − 3`.
- For `S = (w₁, w₂, w₃) ∈ K³`, put `f_S(x) := w₃Jx + (w₂, w₁)` and `P(x) := (x₁, −x₂, 1)` (TR pp.6, 10).
- **Deficiency.**
  - For a partition `Q` of `V`: `def_G(Q) := 3(|Q| − 1) − 2e_G(Q)`.
  - `def(G) := max_Q def_G(Q) ≥ 0`. This is the corpus's `def₂`.
  - `Q` is **tight** if `def_G(Q) = def(G)`.
  - The **target** is `t(G) := 2(n + m) − 3 − def(G)`.
- **The body-and-pin graph** `G*` (TR p.8) has vertex set `V ∪ P`. Its edges are `vp` for `p ∈ E(v)`, and `pp′` for distinct `p, p′ ∈ E(v)`.
  - `B_v := G*[{v} ∪ E(v)]` is a complete graph.
  - Every edge of `G*` lies in some `B_v`.
  - `G*` is simple, because two distinct edges share at most one endpoint.
- **A pin-collinear realization (R0 form)** of `G` is a pair `(q, L)`, with `q : V ∪ P → K²` and a line `L(v)` for each `v ∈ V`. For every `v`:
  - (R-i) `q(p) ∈ L(v)` for each `p ∈ E(v)`;
  - (R-ii) `q` is injective on `E(v)`;
  - (R-iii) `q(v) ∉ L(v)`.

  The realization is **non-degenerate** if `L(u) ≠ L(v)` for every edge `uv`. Then `q(uv) = L(u) ∩ L(v)`.

  When `d(v) ≥ 2`, `L(v)` is determined by `q`. When `d(v) = 1`, `L(v)` is a free line through the pin (this is R0). The rank `r(G*, q)` does not involve `L`.

##### Linear algebra over `K`

> **(NEW-I1)** `[PROVED]` *(the Zariski toolkit; replaces TR Lemma 2.2(b) and every ε-move)*
> **(i)** A nonzero polynomial on `K^N` has a non-root. So finitely many nonempty Zariski-open subsets of `K^N` have a nonempty open intersection. A nonempty open subset of `K` is cofinite. `K²` is not a finite union of lines.
> **(ii)** Let `Ω ⊆ K^N` be open, and let `N(λ)` be a matrix whose entries are regular on `Ω`. For each `r`, the set `{λ ∈ Ω : rank N(λ) ≥ r}` is open.
> **(iii)** *(the move)* Let `λ ↦ q(λ)` be a regular map `Ω → K^{2W}` with `q(λ₀) = q₀`. Then `{λ ∈ Ω : r(H, q(λ)) ≥ r(H, q₀)}` is open and contains `λ₀`. When `N = 1`, it is cofinite.

*Proof.*
- (i) Induct on `N`. In one variable, a nonzero polynomial has finitely many roots and `K` is infinite.
  - Every nonempty open set contains some `D(f) = {f ≠ 0}` with `f ≠ 0`, and `D(f) ∩ D(g) = D(fg)` with `fg ≠ 0`.
  - A proper closed subset of `K` is finite.
  - For the last claim, take a line `M` outside the family. It meets each member in at most one point, and `M` is infinite.
- (ii) `rank ≥ r` holds iff some `r × r` minor is nonzero, and each minor is regular on `Ω`.
- (iii) Apply (ii) to `R(H, q(λ))`. ∎

> **(NEW-I2)** `[PROVED]` *(trivial motions; TR Lemmas 2.1, 2.8, 2.9)* Let `(H, q)` be a framework on `W`.
> **(i)** `f_{S+T} = f_S + f_T`, and `f_S(x) = 0` iff `S ∈ K·P(x)`.
> **(ii)** `f_S ∘ q ∈ Z(H, q)` for every `S ∈ K³`.
> **(iii)** If `q` takes at least two values, `S ↦ f_S ∘ q` is injective. Hence `r(H, q) ≤ 2|W| − 3` whenever `|W| ≥ 2`.
> **(iv)** If `(H, q)` is infinitesimally rigid, then `S ↦ f_S ∘ q` is an isomorphism `K³ → Z(H, q)`.

*Proof.*
- (i) `f_S(x) = (w₃x₂ + w₂, −w₃x₁ + w₁)`. It vanishes iff `S = w₃(x₁, −x₂, 1)`.
- (ii) `(q(a) − q(b))·(f_S(q(a)) − f_S(q(b))) = w₃ d·Jd = 0`, where `d = q(a) − q(b)`.
- (iii) Suppose `f_S ∘ q = 0` and `q` takes two distinct values `x, y`. Then `S ∈ KP(x) ∩ KP(y)`. Both vectors have third coordinate `1` and `P(x) ≠ P(y)`, so they are not proportional, and `S = 0`. Hence `df ≥ 3`. If `q` is constant, every row is zero and `r = 0`.
- (iv) An infinitesimally rigid framework takes two values: a constant `q` has `r = 0 < 2|W| − 3`. So the map is injective, and both spaces have dimension 3. ∎

> **(NEW-I3)** `[PROVED]` *(moves; TR Lemmas 2.3, 2.4, 2.5, and R1)* Let `(H, q)` be a framework on `W`.
> **(i)** *(complete graphs)* Let `C` be the complete graph on `W`. If `q(W)` is not contained in a line, then `(C, q)` is infinitesimally rigid, even when `q` is not injective. If `q(W)` lies on a line and `|W| ≥ 3`, then every graph on `W` has rank `≤ |W| − 1 < 2|W| − 3`.
> **(ii)** *(0-extension; pendant)* Add a new vertex `w` joined to distinct `a, b`, with `q(w), q(a), q(b)` not collinear. The rank rises by exactly 2. Joining a new `w` to a single `a` with `q(w) ≠ q(a)` raises it by exactly 1.
> **(iii)** *(1-extension)* Let `ab ∈ F` and `c ∈ W − {a, b}`, with `q(a), q(b), q(c)` not collinear. Let `X` lie on the line `q(a)q(b)`, with `X ≠ q(a), q(b)`. Delete `ab` and add `w` at `X`, joined to `a, b, c`. The rank rises by at least 2.
> **(iv)** *(vertex split)* Let the neighbours of `v` be `a₁, a₂` and the disjoint sets `N_A, N_B`. Replace `v` by `v′`, joined to `a₁, a₂` and `N_A`, and `v″`, joined to `a₁, a₂` and `N_B`. Put both at `q(v)`. If `q(v) − q(a₁)` and `q(v) − q(a₂)` are linearly independent, the rank rises by at least 2.
> **(v)** *(R1: affine invariance)* For `A ∈ GL₂(K)` and `b ∈ K²`, `R(H, Aq + b) = R(H, q)·diag(Aᵀ, …, Aᵀ)`, so the rank is unchanged. Affine maps preserve lines, incidence, parallelism and non-collinearity. So they send (non-degenerate) pin-collinear realizations to (non-degenerate) pin-collinear realizations of the same rank. Fix `a ≠ b`, `a′ ≠ b′`, and a vector `c` with `det(b − a, c) ≠ 0`. The affine maps sending `a ↦ a′` and `b ↦ b′` are exactly `x ↦ a′ + M(x − a)` with `M(b − a) = b′ − a′`. Their free parameter is `c′ := Mc`, which ranges over `{c′ : det(b′ − a′, c′) ≠ 0}`.

*Proof.*
- (i) Pick `a, b, c` with `q(a), q(b), q(c)` not collinear.
  - The triangle `abc` has rank 3: the row of `ab` is nonzero, and adding `c` is a 0-extension.
  - So the triangle's motions are the `f_S ∘ q` ((NEW-I2)(iv)).
  - Let `m ∈ Z(C, q)`. Subtract the trivial motion that agrees with `m` on `a, b, c`, so that now `m(a) = m(b) = m(c) = 0`.
  - For any `w`: `(q(w) − q(x))·m(w) = 0` for each `x ∈ {a, b, c}`.
  - These three vectors span `K²`. Otherwise `q(a), q(b), q(c)` would lie on one line through `q(w)`. So `m(w) = 0`.
  - Hence `df = 3`.
  - For the collinear case, let `δ` span the direction of the line. Every row is `(e_a − e_b) ⊗ λδ`, so the row space lies in `{(c_w δ)_w : Σ c_w = 0}`, of dimension `|W| − 1`.
- (ii) The new rows have `w`-columns `q(w) − q(a)` and `q(w) − q(b)`, which are independent. The old rows vanish on the `w`-columns. So the new rows are independent modulo the old ones. Two rows add at most 2. The pendant case is the same argument with one row.
- (iii) Write `X = q(a) + s(q(b) − q(a))`, with `s ≠ 0, 1`.
  - Choose a row basis `𝔅` of `R(H, q)` containing `ab`; its row is nonzero.
  - Suppose `Σ_{𝔅 − ab} α_e r_e + β₁r_{wa} + β₂r_{wb} + β₃r_{wc} = 0`.
  - The `w`-columns give `(sβ₁ + (s − 1)β₂)(q(b) − q(a)) + β₃(X − q(c)) = 0`. These two vectors are independent, so `β₃ = 0` and `sβ₁ + (s − 1)β₂ = 0`.
  - On the columns of `a` and `b`, `β₁r_{wa} + β₂r_{wb}` then equals `sβ₁·r_{ab}`.
  - Independence of `𝔅` forces `α = 0` and `sβ₁ = 0`. Then `β₁ = 0` (as `s ≠ 0`) and `β₂ = 0` (as `s ≠ 1`).
- (iv) This is TR p.5's proof, which is linear algebra.
  - Choose a row basis `𝔅` containing `va₁` and `va₂`; their `v`-columns are independent.
  - Let `𝔅′` replace each `va ∈ 𝔅` (`a ∈ N_A`) by `v′a`, each `va ∈ 𝔅` (`a ∈ N_B`) by `v″a`, and `va₁, va₂` by `v′a₁, v′a₂, v″a₁, v″a₂`.
  - Take a dependency `α` on `𝔅′`. Set `β_{va_i} := α_{v′a_i} + α_{v″a_i}`, and let `β` copy `α` elsewhere. Then `β` is a dependency on `𝔅`, so `β = 0`.
  - The `v′`-columns then give `α_{v′a₁}(q(v) − q(a₁)) + α_{v′a₂}(q(v) − q(a₂)) = 0`. So `α_{v′a_i} = 0`, and then `α_{v″a_i} = 0`.
  - Hence `|𝔅′| = |𝔅| + 2` rows are independent.
- (v) The row of `ab` at `(Aq + b, a)` is `(q(a) − q(b))ᵀAᵀ`. ∎

> **(NEW-I4)** `[PROVED]` *(gluing; TR Lemmas 2.6, 2.7)*
> **(i)** Let `(W₁, F₁)` and `(W₂, F₂)` be infinitesimally rigid at `q`, and let `X := W₁ ∩ W₂`. Their union has `df = 3 + dim ⋂_{x∈X} K·P(q(x))`, where the empty intersection is `K³`. So `df` is `6`, `4` or `3` when `X = ∅`, `|q(X)| = 1` or `|q(X)| ≥ 2`.
> **(ii)** Let `H = H₁ ∪ H₂` with `V(H₁) ∩ V(H₂) = X`, `|X| = t ≤ 2`, and `E(H₁) ∩ E(H₂) = E(K_X)`, where both `H₁` and `H₂` contain the complete graph `K_X`. Suppose `q` is injective on `X`, and no `q(V(H_i))` is contained in a line. Then `r(H, q) = r(H₁, q) + r(H₂, q) − |E(K_X)|`.

*Proof.*
- (i) A motion restricts on `W_i` to some `f_{S_i} ∘ q` ((NEW-I2)(iv)). On `X` the two agree iff `f_{S₁−S₂}(q(x)) = 0` for every `x ∈ X`, iff `S₁ − S₂ ∈ KP(q(x))` ((NEW-I2)(i)). Conversely, every such pair `(S₁, S₂)` glues to a motion. If `|q(X)| ≥ 2`, the intersection is `0` by the argument in (NEW-I2)(iii).
- (ii)
  - `E(K_X)` is independent: it has at most one edge, and that row is nonzero. Choose row bases `𝔅_i ⊇ E(K_X)` of `R(H_i)`.
  - Extend `𝔅_i` to a row basis `T_i` of the complete graph on `V(H_i)`. That complete graph is infinitesimally rigid by (NEW-I3)(i), so `|T_i| = 2|V(H_i)| − 3`.
  - By (i), `(V(H), T₁ ∪ T₂)` has rank `2|V(H)| − df`. This equals `|T₁| + |T₂| − |E(K_X)| = |T₁ ∪ T₂|` in each of the cases `t = 0, 1, 2`.
  - So `T₁ ∪ T₂` is independent, and hence so is `𝔅₁ ∪ 𝔅₂`.
  - `𝔅₁ ∪ 𝔅₂` also spans every row of `H`. ∎

##### The combinatorial inputs (re-proved; nothing is taken on trust)

> **(NEW-I5)** `[PROVED]` *(the deficiency calculus)* Let `G = (V, E)` be a graph.
> **(i)** *(refinement)* If `Q` refines `R`, then `def_G(Q) = def_G(R) + Σ_{A∈R} def_{G[A]}(Q|_A)`.
> **(ii)** *(merging; the one-edge property)* Merging `k ≥ 2` parts of `Q` changes `def_G` by `2e′ − 3(k − 1)`, where `e′` counts the edges between the merged parts. So two parts of a tight partition are joined by at most one edge.
> **(iii)** For every edge `e` and every `Q`, `def_{G−e}(Q) − def_G(Q) ∈ {0, 2}`. So `def(G) ≤ def(G − e) ≤ def(G) + 2`.
> **(iv)** `def(G₁ ⊔ G₂) ≥ def(G₁) + def(G₂) + 3`.
> **(v)** Let `G` be `G₁` plus a new vertex `v` with `d` edges. Then `def(G) ≥ def(G₁) + 3 − 2d`. If moreover `v`'s neighbours lie in one part of a tight partition of `G₁`, then `def(G) ≥ def(G₁)`.

*Proof.*
- (i) Use `|Q| = Σ_A |Q|_A|` and `e(Q) = e(R) + Σ_A e_{G[A]}(Q|_A)`.
- (ii) Substitute into the definition. If `k = 2` and `e′ ≥ 2`, the merged partition's deficiency exceeds `def(G)`.
- (iii) `e_G(Q)` loses 1 if `e` crosses `Q`, and 0 otherwise.
- (iv) Take the union of tight partitions of `G₁` and `G₂`.
- (v) Use `Q₁ ∪ {{v}}`. For the second claim, add `v` to the part containing its neighbours. ∎

Say `X ⊆ V` is **strong** if `def(G[X]) = 0`. Say it is **superstrong** if moreover `def_{G[X]}(Q) < 0` for every partition `Q` of `X` with `|Q| ≥ 2`. Singletons are both. A **brick** (**superbrick**) is a maximal strong (superstrong) set (TR p.7). These definitions use deficiency directly, so the TR's Thm 3.1 (Tutte–Nash-Williams) is never needed.

> **(NEW-I6)** `[PROVED]` *(bricks and superbricks; TR Lemmas 3.2, 3.3, cited there from Jackson–Jordán's molecular paper, whose Lemma 3.2 cites their "Brick partitions of graphs", EGRES TR-2007-05)*
> **(i)** In a strong `X` with `|X| ≥ 2`, every vertex has at least 2 neighbours in `X`, and `G[X]` is connected. Triangles are strong.
> **(ii)** *(union)* If `X` and `Y` are strong (superstrong) and `X ∩ Y ≠ ∅`, then `X ∪ Y` is strong (superstrong).
> **(iii)** *(Lemma 3.2)* The bricks partition `V`, and so do the superbricks.
> **(iv)** Every part of a tight partition is strong. Every part of a tight partition of maximum size is superstrong.
> **(v)** *(Lemma 3.3)* Every tight partition refines the brick partition `𝔅`. `𝔅` is tight, and it is the unique tight partition of minimum size. The superbrick partition `𝒮` is the unique tight partition of maximum size; in particular `𝒮` is tight.

*Proof.*
- (i) The partition `{{v}, X − v}` has value `3 − 2d_X(v) ≤ 0`, so `d_X(v) ≥ 2`. A split into two parts with no edge between them has value 3. For a triangle, the three partition types have values `0`, `−1` and `0`.
- (ii) Let `Q` partition `X ∪ Y`.
  - Let `Q_Y` be the trace of `Q` on `Y`, and `k := |Q_Y|`.
  - Let `B₁, …, B_l` be the parts of `Q` that miss `Y`; they lie in `X − Y`.
  - Let `R := {(⋃_{A∩Y≠∅} A) ∩ X, B₁, …, B_l}`. It partitions `X`, and its first part is nonempty.
  - The crossing edges of `Q_Y` in `G[Y]` and of `R` in `G[X]` are disjoint: each edge of the second kind has an end in some `B_j`. Both kinds cross `Q`.
  - So `2e(Q) ≥ 3(k − 1) + 3l = 3(|Q| − 1)`.
  - For superstrong sets with `|Q| ≥ 2`: if `k ≥ 2`, the `Y` term gains `+1`. If `k = 1`, then `|R| = l + 1 ≥ 2` and the `X` term gains `+1`.
- (iii) By (ii), the union `β(v)` of all strong sets containing `v` is strong. So it is the unique brick containing `v`. If `β(u)` and `β(v)` meet, their union is strong, so they are equal. The same argument works for superbricks.
- (iv) If a part `A` has a partition `Q_A` of positive value, refining by it raises the deficiency ((NEW-I5)(i)). If `A` has a partition `Q_A` with `|Q_A| ≥ 2` and value `0`, refining by it gives a larger tight partition.
- (v) By (iv), the parts of a tight `Q` lie in bricks, so `Q` refines `𝔅`.
  - By (NEW-I5)(i), `def(Q) = def(𝔅) + Σ_B def_{G[B]}(Q|_B) ≤ def(𝔅)`. So `𝔅` is tight.
  - A tight partition of minimum size refines `𝔅` and has at most `|𝔅|` parts, so it equals `𝔅`.
  - Let `Q` be tight of maximum size. By (iv) its parts are superstrong, so each lies in a superbrick.
  - Conversely, suppose a superbrick `S` meets `k ≥ 2` parts of `Q`. Merge those parts. The value changes by at least `2e_{G[S]}(Q|_S) − 3(k − 1) ≥ 1`, which contradicts tightness.
  - So `Q = 𝒮`. ∎

> **(NEW-I7)** `[PROVED]` *(each claim's deficiency inequality; `G` is simple)*
> **(a)** *(6.2)* `def(G₁ ⊔ G₂) ≥ def(G₁) + def(G₂) + 3`.
> **(b)** *(6.3)* If `d(v₁) = 1`, then `def(G) ≥ def(G − v₁) + 1`.
> **(c)** *(6.4)* `def(G) ≥ def(G − p₀) − 2` for every edge `p₀`.
> **(d)** *(6.5)* Let `d(v₁) = 2`, let its neighbours be `u₁, u₂`, and let `G₁ := G − v₁`. Always `def(G) ≥ def(G₁) − 1`. If `u₁, u₂` lie in one brick of `G₁`, then `def(G) ≥ def(G₁)`.
> **(e)** *(Case 1)* If `u₁u₂ ∉ E` and `u₁, u₂` lie in distinct bricks of `G₁`, then `def(G₁ + u₁u₂) ≤ def(G₁) − 1`.
> **(f)** *(Case 2)* Suppose `u₁u₂ ∈ E` and `u₁, u₂` lie in distinct bricks of `G₁`. Then `u₁, u₂` have no common neighbour in `G₁`, the contraction `G₃ := G₁/u₁u₂` is simple, and `def(G₃) ≤ def(G₁) − 1`.
> **(g)** *(Case 3)* If `u₁u₂ ∈ E` and `E(u₂) = {u₂v₁, u₂u₁}`, then `def(G) ≥ def(G − {v₁, u₂})`.
> **(h)** *(6.7)* If `def(G − p₀) ≥ 1` for some edge `p₀`, then some `B` with `∅ ≠ B ≠ V` has `d_G(B) ≤ 2`.
> **(i)** *(6.9)* If `G` is superstrong, then `def(G − p) ≤ def(G) + 1 = 1` for every edge `p`.
> **(j)** *(the gluing set)* Let `G` be 2-edge-connected with minimum degree `≥ 3` and `|𝒮| ≥ 2`. Then some `B₁ ∈ 𝒮` has `d(B₁) = 2`. Write its cut edges as `u₁v₁, u₂v₂` with `u_i ∈ B₁`. Then `v₁` and `v₂` lie in distinct superbricks, so `v₁ ≠ v₂`. Also `|B₁| ≥ 3`, `|V − B₁| ≥ 3`, `|E(G − B₁)| ≥ 4`, and both `G[B₁]` and `G − B₁` are connected.
> **(k)** *(6.10)* With (j)'s notation, let `G₁ := G[B₁] + w₀, w₁` with the edges `u₁w₀, w₀w₁, w₁u₂`. Let `G₂ := (G − B₁) + w₂` with the edges `v₁w₂, v₂w₂`. Then `def(G₁) = 0` and `def(G₂) ≤ def(G)`.

*Proof.*
- (a) is (NEW-I5)(iv); (b) is (NEW-I5)(v) with `d = 1`; (c) is (NEW-I5)(iii).
- (d) (NEW-I5)(v) with `d = 2` gives the first claim. The brick partition is tight ((NEW-I6)(v)), so the second clause of (NEW-I5)(v) gives the second.
- (e) Take a tight `Q` for `G₂ := G₁ + u₁u₂`.
  - If `Q` separates `u₁` and `u₂`, then `def(G₂) = def_{G₁}(Q) − 2`.
  - Otherwise `def(G₂) = def_{G₁}(Q)`. If this equalled `def(G₁)`, then `Q` would be tight for `G₁`. The part containing `u₁, u₂` would be strong ((NEW-I6)(iv)), so it would lie inside one brick. Contradiction.
- (f) A common neighbour `w` would make `{u₁, u₂, w}` a strong triangle, hence inside one brick. The partitions of `V(G₃)` are exactly the partitions of `V(G₁)` that keep `u₁, u₂` together, with the same crossing edges. Then argue as in (e).
- (g) Take a tight partition of `G − {v₁, u₂}`, and add `v₁, u₂` to the part of `u₁`. No crossing edge is added.
- (h) Take a tight `𝔅₀` for `G − p₀`. Then `2e_{G−p₀}(𝔅₀) ≤ 3|𝔅₀| − 4`, so `Σ_B d_G(B) = 2e_G(𝔅₀) ≤ 3|𝔅₀| − 2`. Also `|𝔅₀| ≥ 2`.
- (i) For `|Q| ≥ 2`: `def_{G−p}(Q) ≤ def_G(Q) + 2 ≤ 1`.
- (j)
  - `𝒮` is tight and `def ≥ 0`, so `Σ_B d(B) ≤ 3(|𝒮| − 1)`. Some `B₁` has `d(B₁) ≤ 2`, and 2-edge-connectivity forces equality.
  - `v₁` and `v₂` lie in distinct superbricks by (NEW-I5)(ii).
  - Size bounds: the degree sum over a `k`-set with 2 edges leaving is `≤ k(k − 1) + 2`, and this is `< 3k` for `k ≤ 2`. For `V − B₁`: `2|E(G − B₁)| ≥ 3·3 − 2 = 7`.
  - `G[B₁]` is strong, hence connected. Each component `C` of `G − B₁` has `d(C) ≥ 2`, and the total is 2, so there is one component.
- (k) (a) If `G₁` is not strong, its brick partition has `|𝔅| ≥ 2`.
  - `B₁` is strong, so it lies in some brick `B⁺ ⊆ B₁ ∪ {w₀, w₁}`.
  - `B⁺` is not `B₁ + w₀` or `B₁ + w₁`: in either, the new vertex has only one neighbour ((NEW-I6)(i)). `B⁺` is not all of `V(G₁)` either, because `G₁` is not strong.
  - `{w₀, w₁}` induces `K₂`, which has deficiency 1, so it is not strong.
  - So `𝔅 = {B₁, {w₀}, {w₁}}`, with value `3·2 − 2·3 = 0`. Since `𝔅` is tight, `def(G₁) = 0`. Contradiction.
- (k) (b) Take `G₂`'s brick partition `𝔅₂`, and let `B₂` be the brick containing `w₂`.
  - If `B₂ = {w₂}`, replace it by `B₁`.
  - Otherwise `v₁, v₂ ∈ B₂` by (NEW-I6)(i). Replace `B₂` by `(B₂ − w₂) ∪ B₁`.
  - In either case the result is a partition of `V` with value `def(G₂)`. ∎

##### Realizations, the rank formula and the generic input

> **(NEW-I8)** `[PROVED]` *(realizations; TR p.9 and Lemma 4.1)* Let `G` have no isolated vertices.
> **(i)** *(R0)* Let `q : V ∪ P → K²`. The following are equivalent: (1) the TR's definition holds: `q` is injective on each `{v} ∪ E(v)`, each `B_v` is infinitesimally rigid, and each `q(E(v))` is collinear; (2) `(q, L)` is a pin-collinear realization for some `L`.
> **(ii)** *(Lemma 4.1)* `r(G*, q) ≤ t(G)` for **every** `q : V ∪ P → K²`.

*Proof.*
- (i) (2)⇒(1). If `d(v) = 1`, `B_v` is an edge between two distinct points. If `d(v) ≥ 2`, `q(B_v)` is not contained in a line, so (NEW-I3)(i) applies.
- (i) (1)⇒(2). If `d(v) ≥ 2`, let `L(v)` be the line through the pins. Then `q(v) ∉ L(v)`, because otherwise `B_v` would be collinear with at least 3 points, contradicting (NEW-I3)(i). If `d(v) = 1`, take any line through the pin except the one through `q(v)`.
- (ii) Let `Q = {Q₁, …, Q_t}` be tight, and `X_i := ⋃_{v ∈ Q_i} ({v} ∪ E(v))`.
  - Every edge of `G*` lies in some `G*[X_i]`, and `|X_i| ≥ 2`.
  - Rank is subadditive over row sets. By (NEW-I2)(iii), `r ≤ Σ(2|X_i| − 3)`.
  - Each pin lies in one or two of the `X_i`, so `Σ|X_i| = n + m + e(Q)`.
  - So `r ≤ 2(n + m) + 2e(Q) − 3t = t(G)`. ∎

> **(NEW-I9)** `[PROVED]` *(TR Lemma 5.1 over `K`)* Let `(q, L)` be a pin-collinear realization. Put `Z_BP(G, q|_P) := {S : V → K³ : S(u) − S(v) ∈ K·P(q(uv)) for every edge uv}`. Then `Z(G*, q) ≅ Z_BP(G, q|_P)`. Also `dim Z_BP = 3n − rank R_BP(G, q|_P)`. Hence `r(G*, q) = 2m − n + rank R_BP(G, q|_P)`, whatever the body points.

*Proof.*
- Each `B_v` is infinitesimally rigid ((NEW-I8)(i)). So a motion `σ` restricts on `B_v` to `f_{S(v)} ∘ q` for a unique `S(v)`.
- At a pin `uv`: `f_{S(u)−S(v)}(q(uv)) = 0`, so `S(u) − S(v) ∈ KP(q(uv))`.
- The map `σ ↦ S` is injective, because the `B_v` cover `V(G*)`.
- It is surjective. Given `S`, put `σ(v) := f_{S(v)}(q(v))` and `σ(uv) := f_{S(u)}(q(uv)) = f_{S(v)}(q(uv))`. Then `σ|_{B_v} = f_{S(v)} ∘ q`, and every edge of `G*` lies in some `B_v`.
- The rows `(1, 0, −x)` and `(0, 1, y)` of `R_BP` span `P(x, y)^⊥`, which is 2-dimensional. ∎

> **(NEW-I10)** `[PROVED]` *(rod-and-pin encoding, the generic set, and TR Lemma 5.2 in non-degenerate form)* Let `G` have no isolated vertices.
> **(i)** For `p : V → K²`, put `L_v := {x : p(v)·x = 1}` and `d(u, v) := det(p(u), p(v))`. Let `A_G := {p : d(u, v) ≠ 0 for every edge uv}`. For `p ∈ A_G`, put `p̃(uv) := L_u ∩ L_v` and `R_RP(G, p) := R_BP(G, p̃)` (TR p.12). Multiplying edge `uv`'s two rows by `d(u, v)` gives a matrix `R′(p)` with polynomial entries. For `u` before `v`, its entries at `u` are `(d, 0, p₂(u) − p₂(v))` and `(0, d, p₁(u) − p₁(v))`, and at `v` their negatives. On `A_G`, `R′(p)` and `R_RP(G, p)` have the same rank.
> **(ii)** Let `r_RP(G) := max_{A_G} rank R′`. Let `U_G` be the set of `p` satisfying:
>  (a) `det(p(u), p(v)) ≠ 0` for **all** distinct `u, v ∈ V`;
>  (b) `det[p(u) 1; p(v) 1; p(w) 1] ≠ 0` for all distinct `u, v, w`;
>  (c) `rank R′(p) = r_RP(G)`.
> `U_G` is a nonempty Zariski-open subset of `K^{2V}`. Given (a), condition (b) says that no three of the lines `L_v` are concurrent.
> **(iii)** *(realizations built on `p`)* Let `p ∈ U_G`, and choose any body points `q(v) ∉ L_v`. Put `q(uv) := p̃(uv)` and `L(v) := L_v`. This is a non-degenerate pin-collinear realization, and `r(G*, q) = 2m − n + r_RP(G)`.
> **(iv)** *(TR Lemma 5.2, non-degenerate form)* Every non-degenerate pin-collinear realization `(q, L)` has `r(G*, q) ≤ 2m − n + r_RP(G)`.
> **(v)** *(the generic input)* Suppose `G` has a non-degenerate pin-collinear realization of rank `≥ t(G)`. Then every realization built on any `p ∈ U_G` has rank **exactly** `t(G)`. Its pin-lines are pairwise non-parallel, and no three of them are concurrent.

*Proof.*
- (ii) The equivalence with concurrency: if the lines meet at `x`, then `(x₁, x₂, −1)` lies in the kernel of the matrix. Conversely, a kernel vector `(x, 0)` would contradict (a).
  - (a) and (b) together are nonempty: take `p(v) = (λ_v, λ_v²)` with distinct nonzero `λ_v`. This gives a Vandermonde determinant, and `det = λ_uλ_v(λ_v − λ_u)`.
  - (c) is nonempty and open on the open set `A_G` ((NEW-I1)(ii)).
  - The intersection is nonempty by (NEW-I1)(i).
- (iii) Pins on one line are distinct: `p̃(uv) = p̃(uw)` would make three lines concurrent. The realization is non-degenerate by (a). The rank follows from (NEW-I9).
- (iv) Pick `τ` with `−τ ∉ ⋃_v L(v)` ((NEW-I1)(i)). The translate `(q + τ, L + τ)` has the same rank ((NEW-I3)(v)). Each `L(v) + τ` misses the origin, so it is `{x : p′(v)·x = 1}` for a unique `p′(v)`. By non-degeneracy, adjacent lines are distinct and share a pin, so they are not parallel. Hence `p′ ∈ A_G`, and the pins are `p̃′`. By (NEW-I9), `r = 2m − n + rank R′(p′) ≤ 2m − n + r_RP(G)`.
- (v) Combine (iv) with (iii) for `≥ t(G)`, and (NEW-I8)(ii) for `≤ t(G)`. ∎

A realization as in (NEW-I10)(v) is called a **generic realization** of `H`. It is exactly what the TR calls "pin-line-generic" (TR p.13), in Zariski form.

##### R2: the invariant carried through the induction

> **(NEW-I11)** `[PROVED]` *(the induction statement; this is R2)* For a simple graph `G` without isolated vertices, let **`A(G)`** say: *`G` has a non-degenerate pin-collinear realization `(q, L)` with `r(G*, q) ≥ t(G)`.*
> **The invariant.** Every construction's **output** satisfies:
>  (N1) every pin of every body is on its pin-line, and the pins of each body are distinct;
>  (N2) every body point is off its pin-line;
>  (N3) adjacent bodies have distinct pin-lines. By (N1), they are then non-parallel and meet exactly at their common pin.
> Nothing more is carried. (NEW-I10)(iv) needs only (N1)–(N3).
> **The input.** Every construction's **input** is a generic realization of a smaller graph, obtained from the inductive hypothesis through (NEW-I10)(v). That input has more than the invariant:
>  - (a) all pin-lines pairwise non-parallel, for every pair of vertices;
>  - (b) no three pin-lines concurrent, so every pin lies on exactly two pin-lines;
>  - maximal rank;
>  - body points in any prescribed nonempty open set.
>
> In Case 1 (the only place where the TR restricts to a subgraph), the input lies in `U_{G₁} ∩ U_{G₂}`.

`A(G)` is proved by strong induction on `n + m`. From here on, **(IH)** means: `A(H)` holds for every simple `H` without isolated vertices with `n_H + m_H < n + m`. So each such `H` has generic realizations of rank exactly `t(H)`.

##### The constructions

Each construction below states its hypotheses, its free parameters with their excluded sets, and why the output satisfies (N1)–(N3) with rank `≥ t(G)`. "Cofinite on a line" means: all but finitely many points of an explicitly parametrized line.

> **(NEW-I12)** `[PROVED]` *(base cases; the TR's "G has at least four vertices", p.14)* `A(K₂)` and `A(K₃)` hold.

*Proof.*
- `K₂`, with bodies `u, v`:
  - `def(K₂) = 1`, so `t(K₂) = 2`.
  - Take a pin `X`, two distinct lines through `X` as `L(u)` and `L(v)`, and body points off their lines.
  - `G*` is the path `u–X–v`. Each body point's column is touched by one row only, so `r = 2`.
- `K₃`, with bodies `a, b, c`:
  - `def(K₃) = 0` ((NEW-I6)(i)), so `t(K₃) = 9`.
  - Take three lines in general position ((NEW-I10)(ii)(a),(b)). The three pins are distinct and not collinear; a common line would equal two of the pin-lines.
  - `G*` contains the pin triangle, whose edges come from pins of a common body. It has rank 3. Each body point is then a 0-extension onto its two pins ((NEW-I3)(ii)), giving `3 + 3·2 = 9`.
- Both realizations are non-degenerate. ∎

> **(NEW-I13)** `[PROVED]` *(Claim 6.2, TR p.14)* Assume (IH). If `G = G₁ ⊔ G₂`, where both are nonempty with no isolated vertices, then `A(G)` holds.

*Proof.* (IH) gives realizations of `G₁` and `G₂`; take their union.
- `G* = G₁* ⊔ G₂*`, so the matrix is block diagonal and `r = t(G₁) + t(G₂) ≥ t(G)` by (NEW-I7)(a).
- (N1)–(N3) are conditions on one body or one edge at a time, so they hold. ∎

> **(NEW-I14)** `[PROVED]` *(Claim 6.3, TR pp.14–15)* Assume (IH). Let `G` be connected with `G ≠ K₂`, let `d(v₁) = 1`, and let `p₁ = u₁v₁`. Then `A(G)` holds.

*Proof.*
- **Setup.**
  - `d(u₁) ≥ 2`, since otherwise `G = K₂`.
  - `G₁ := G − v₁` has no isolated vertices, and `n₁ + m₁ = n + m − 2`.
  - Take a generic realization `(q₁, L₁)` of `G₁`, and fix `p₂ ∈ E_{G₁}(u₁)`.
- **Parameters.**
  - `Q₁ ∈ L₁(u₁)`, avoiding the pins of `u₁` in `G₁`. This is cofinite on the line.
  - `Q₂ ≠ Q₁`.
  - `L(v₁)`: a line through `Q₁`, avoiding `L₁(u₁)` and avoiding the line through `Q₂`. This excludes 2 lines of the pencil at `Q₁`; this is R0.
- **Output.** `q(p₁) := Q₁`, `q(v₁) := Q₂`.
- **Rank.**
  - A 0-extension of `p₁` onto `u₁, p₂` adds `+2`. Here `q₁(p₂)` and `Q₁` are distinct points of `L₁(u₁)`, and `q₁(u₁)` is off that line.
  - A pendant `v₁` onto `p₁` adds `+1`.
  - Total: `r ≥ t(G₁) + 3 ≥ t(G)` by (NEW-I7)(b).
- **Invariant.** (N3) holds at `p₁` because `L(v₁) ≠ L₁(u₁)`. Every other edge keeps its lines from `G₁`. ∎

> **(NEW-I15)** `[PROVED]` *(Claim 6.4, TR p.15)* Assume (IH). Let `G` be connected with minimum degree `≥ 2`, and let `p₀ = u₁u₂` be a bridge, with `G − p₀ = G₁ ⊔ G₂` and `u_i ∈ G_i`. Then `A(G)` holds.

*Proof.*
- **Setup.**
  - `G₀ := G − p₀` has no isolated vertices, and `n₀ + m₀ = n + m − 1`.
  - Take a generic realization `(q₀, L₀)` of `G₀`, and put `q(p₀) := Q := L₀(u₁) ∩ L₀(u₂)`. This is a point by (a).
  - By (b), `Q` differs from the pins of `u₁` and `u₂`: a pin `u_i w` equal to `Q` would make three lines concurrent.
  - There is no free parameter.
- **Rank.**
  - Let `H_i := G*[V(G_i*) ∪ {p₀}]`. Then `G* = H₁ ∪ H₂`, with `V(H₁) ∩ V(H₂) = {p₀}`.
  - `H_i` contains a 0-extension of `G_i*` at `p₀`, onto `u_i` and one of its pins. So `r(H_i) ≥ r(G_i*) + 2`.
  - Neither `q(V(H_i))` lies in a line, because each contains `u_i`'s body.
  - (NEW-I4)(ii) with `t = 1` gives `r(G*) = r(H₁) + r(H₂) ≥ r(G₀*) + 4 = t(G₀) + 4 ≥ t(G)`, by (NEW-I7)(c).
- **Invariant.** The pin-lines are unchanged, and (N3) holds at `p₀` by (a). ∎

> **(NEW-I16)** `[PROVED]` *(Claim 6.5, same-brick case, TR pp.15–16)* Assume (IH). Let `G` have minimum degree `≥ 2`. Let `d(v₁) = 2`, with neighbours `u₁, u₂`, and `p_i = u_iv₁`. Suppose `u₁, u₂` lie in one brick of `G₁ := G − v₁`. Then `A(G)` holds.

*Proof.*
- **Setup.** Take a generic realization `(q₁, L₁)` of `G₁`, and let `X := L₁(u₁) ∩ L₁(u₂)`.
- **Parameters.**
  - `Q_i ∈ L₁(u_i)`, avoiding `u_i`'s pins in `G₁` and avoiding `X`. This is cofinite.
  - It follows that `Q_i ∉ L₁(u_{3−i})` and `Q₁ ≠ Q₂`.
  - `L(v₁) := Q₁Q₂`, the line through `Q₁` and `Q₂`.
  - `Q ∉ L(v₁)`.
- **Output.** `q(p_i) := Q_i`, `q(v₁) := Q`.
- **Rank.** Three 0-extensions each add `+2`: `p₁` onto `u₁` and a pin of `u₁`, `p₂` onto `u₂` and a pin of `u₂`, and `v₁` onto `p₁, p₂`. So `r ≥ t(G₁) + 6 ≥ t(G)` by (NEW-I7)(d).
- **Invariant.** `L(v₁)` contains `Q₁`, which is not on `L₁(u₂)`, so `L(v₁) ≠ L₁(u₂)`. Symmetrically, `L(v₁) ≠ L₁(u₁)`. ∎

> **(NEW-I17)** `[PROVED]` *(Claim 6.5 Case 1, TR p.16)* Assume (IH). Let `G` have minimum degree `≥ 2`. Let `d(v₁) = 2`, with neighbours `u₁, u₂`, where `u₁u₂ ∉ E` and `u₁, u₂` lie in distinct bricks of `G₁ := G − v₁`. Then `A(G)` holds.

*Proof.* Let `p₀ := u₁u₂` and `G₂ := G₁ + p₀`. Then `n₂ + m₂ = n + m − 2`, and `t(G₂) ≥ t(G₁) + 3` by (NEW-I7)(e).
- **Step 1 (input).**
  - Take `p ∈ U_{G₁} ∩ U_{G₂}`; both sets live in the same space `K^{2V(G₁)}`.
  - Choose the body points off their lines, with the additional open conditions `q(u₁) ∉ L(u₂)`, `q(u₂) ∉ L(u₁)`, and `X := L(u₁) ∩ L(u₂)`, `q(u₁)`, `q(u₂)` not collinear.
  - This gives a realization `q₂` of `G₂`, whose restriction `q₁` is a realization of `G₁`.
  - By (NEW-I10)(v), `r(G₁*, q₁) = t(G₁)` and `r(G₂*, q₂) = t(G₂)`.
- **Step 2 (the edge `p₀p₄`).**
  - `G₂* = G₁* + p₀ + D`, where `D` is the set of edges at `p₀`. Modulo the row space `W` of `G₁*`, the rows of `D` span at least 3 dimensions.
  - The rows `p₀u₁` and `p₀u₂` are independent modulo `W`. Their `p₀`-columns are `X − q(u₁)` and `X − q(u₂)`, which are independent, and `W` vanishes there.
  - Extend them to a basis using elements of `D`. This gives `p₄ ∈ E_{G₁}(u₁) ∪ E_{G₁}(u₂)`.
  - After swapping `u₁ ↔ u₂` if necessary (the body conditions are symmetric), `p₄ ∈ E_{G₁}(u₁)`.
  - `H₂ := G₁* + p₀ + {p₀u₁, p₀u₂, p₀p₄}` has `r(H₂, q₂) = t(G₁) + 3`.
- **Step 3 (the move, parameter `s ∈ K`).** Let `δ` span the direction of `L(u₁)`, and put `Q₁(s) := X + sδ`. Let `H₂(s)` be `H₂` with `p₀` placed at `Q₁(s)`. Fix `p₃ ∈ E_{G₁}(u₂)`. Exclude:
  - `s = 0`;
  - `r(H₂(s)) < t(G₁) + 3`: finitely many values ((NEW-I1)(iii), since it holds at `0`);
  - `Q₁(s)` equal to a pin of `u₁` in `G₁`: finitely many;
  - `L₀(s) := Q₁(s)q(u₂)` parallel to `L(u₂)`: at most one value. The parallel to `L(u₂)` through `q(u₂)` is not `L(u₁)`, since `q(u₂) ∉ L(u₁)`, so it meets `L(u₁)` at most once;
  - `q(p₃) ∈ L₀(s)`: at most one value, by the same reason for the line `q(u₂)q(p₃)`;
  - `Q₂(s) := L₀(s) ∩ L(u₂)` equal to a pin of `u₂` in `G₁`: finitely many. The map `s ↦ Q₂(s)` is central projection from `q(u₂) ∉ L(u₁)`, so it is injective.
- **Output.** `q(p₁) := Q₁`, `q(p₂) := Q₂` (with `p_i = u_iv₁`), `L(v₁) := L₀`, and `q(v₁) := Q₀ ∉ L₀`.
- **Rank.**
  - Start from `H₂(s)` with `p₀` renamed `p₁`. Its edges `p₁u₁` and `p₁p₄` are edges of `G*`; `p₁u₂` is not.
  - Apply a 1-extension to `p₁u₂`, with third vertex `p₃`. Here `q(p₃) ∉ L₀`, and `Q₂ ∈ L₀ − {Q₁, q(u₂)}` (because `Q₁ ∉ L(u₂)` and `q(u₂) ∉ L(u₂)`). The new vertex `p₂` gets edges `p₂p₁, p₂u₂, p₂p₃`. This adds `+2`.
  - A 0-extension of `v₁` onto `p₁, p₂` adds `+2`.
  - Total: `r ≥ t(G₁) + 7 ≥ t(G)` by (NEW-I7)(d).
- **Invariant.** `L₀` contains `Q₁ ∉ L(u₂)`, and `L₀` contains `q(u₂) ∉ L(u₁)`. So `L₀` differs from both `L(u₁)` and `L(u₂)`. Every other edge keeps its generic lines. ∎

> **(NEW-I18)** `[PROVED]` *(Claim 6.5 Case 2, TR pp.16–17: the flagged step)* Assume (IH). Let `G` have minimum degree `≥ 2`. Let `d(v₁) = 2`, with neighbours `u₁, u₂`, where `p₃ := u₁u₂ ∈ E`, `d(u₁), d(u₂) ≥ 3`, and `u₁, u₂` lie in distinct bricks of `G₁ := G − v₁`. Then `A(G)` holds.

*Proof.*
- **Setup.**
  - Put `p_i := u_iv₁` for `i = 1, 2`.
  - `N₁ := N(u₁) − {u₂, v₁}` and `N₂ := N(u₂) − {u₁, v₁}`. Both are nonempty, and they are disjoint by (NEW-I7)(f).
  - `G₃ := G₁/p₃`, with new vertex `z`. It is simple. Its vertices keep their degrees, and `d(z) ≥ 2`, so it has no isolated vertices.
  - `n₃ + m₃ = n + m − 5`, and `t(G) ≤ t(G₃) + 10` by (NEW-I7)(d),(f).
  - Write `π_w := zw` for `w ∈ N₁ ∪ N₂`.
- **Step 1.**
  - Take a generic realization `(q₃, L₃)` of `G₃`.
  - Write `L_z := L₃(z)`, `L_w := L₃(w)` and `ζ := q₃(z)`. So `q₃(π_w) = L_z ∩ L_w`.
- **Step 2 (`H₀`).**
  - Fix `a ∈ N₁` and `b ∈ N₂`; these are the TR's `p₄` and `p_{j+1}`.
  - `S := {π_sπ_t : s ∈ N₁, t ∈ N₂} − {π_aπ_b}`, and `H₀ := G₃* − S`.
  - `F := H₀[{z} ∪ {π_w}]` is infinitesimally rigid:
    - The two cliques `{z} ∪ π(N₁)` and `{z} ∪ π(N₂)` are each rigid ((NEW-I3)(i); a clique with only 2 vertices is a single nonzero bar).
    - Glued at the point `ζ`, they have `df = 4`, with relative motion `S₂ = S₁ + λP(ζ)` ((NEW-I4)(i)).
    - The bar `π_aπ_b` imposes `λ·det(x_a − x_b, x_b − ζ) = 0`, where `x_w := q₃(π_w)`. The determinant is nonzero because `ζ ∉ L_z`. So `λ = 0`, and `F` is rigid by a determinant, with no metric used.
  - The edges of `S` join vertices of `F`, so their rows lie in `F`'s row span ((NEW-I2)(iii)).
  - So `r(H₀) = r(G₃*) = t(G₃)`.
- **Step 3 (`H₁`).**
  - Choose `Q₁, Q₃ ∈ L_z`, distinct and not pins of `z`. This is cofinite.
  - First 1-extension: on the edge `π_aπ_b`, with third vertex `z`. The new vertex `P₁` goes at `Q₁` and gets edges `P₁π_a, P₁π_b, P₁z`.
  - Second 1-extension: on the edge `P₁π_b`, with third vertex `z`. The new vertex `P₃` goes at `Q₃` and gets edges `P₃P₁, P₃π_b, P₃z`.
  - In both, `ζ` is off `L_z`. By (NEW-I3)(iii), `r(H₁) ≥ r(H₀) + 4`.
- **Step 4 (`H₂`).**
  - Split `z` into `u₁`, joined to `P₁, P₃` and `π(N₁)`, and `u₂`, joined to `P₁, P₃` and `π(N₂)`, both at `ζ`.
  - `ζ − Q₁` and `ζ − Q₃` are independent, so by (NEW-I3)(iv), `r(H₂) ≥ r(H₁) + 2`.
  - Rename `P₁ → p₁`, `P₃ → p₃`, `π_w → u₁w` for `w ∈ N₁`, and `π_w → u₂w` for `w ∈ N₂`. Call the positions `q₅`.
- **Step 5 (the pencil move; this replaces the TR's "small rotation of `L(z)` about `q₅(p₃)`").**
  - Fix an **auxiliary line `M` through `Q₁`** with `M ≠ L_z` and `ζ ∉ M`. This excludes 2 lines of the pencil at `Q₁`. `M` repairs the TR's undefined `L_1`.
  - Fix a direction `δ₀` of `L_z`, and `δ₁ ∉ Kδ₀`. Put `L′(θ) := Q₃ + K(δ₀ + θδ₁)`, so that `L′(0) = L_z`.
  - On the cofinite set `Ω` where `L′(θ)` is parallel neither to any `L_w` (`w ∈ N₁`) nor to `M`, define `q₅(θ)` by moving:
    - each pin `u₁w` (`w ∈ N₁`) to `L′(θ) ∩ L_w`;
    - `p₁` to `p₁(θ) := L′(θ) ∩ M`.
  - `q₅(θ)` is regular on `Ω`, and `q₅(0) = q₅`.
  - Each parallelism condition is a linear polynomial in `θ` that is nonzero at `0`, by (a) and `M ≠ L_z`.
  - Excluded `θ` (every set is finite):
    - (x1) `θ = 0`;
    - (x2) `θ ∉ Ω`;
    - (x3) `r(H₂, q₅(θ)) < r(H₁) + 2` ((NEW-I1)(iii));
    - (x4) `ζ ∈ L′(θ)`: one line of the pencil;
    - (x5) two of the moved pins of `u₁` coincide, or one equals `Q₃`. `Q₃` lies on no `L_w` (it is a non-pin point of `L_z`) and not on `M`. So `L′(θ) ∩ L_w = L′(θ) ∩ L_{w′}` forces `L′(θ)` through the point `L_w ∩ L_{w′} ≠ Q₃`: one `θ` per pair. The case of `M ∩ L_w` is the same;
    - (x6) a moved pin `u₁w` hits another pin of `w`: each such pin lies on `L_w`, hence differs from `Q₃`, so one `θ` each;
    - (x7) `L₁(θ) := p₁(θ)ζ` parallel to `L_z`;
    - (x8) `Q₃ ∈ L₁(θ)`;
    - (x9) `Q₂(θ) := L₁(θ) ∩ L_z` equal to some `q₃(π_w)`, `w ∈ N₂`.

    For (x7)–(x9): `θ ↦ p₁(θ)` is injective because `Q₃ ∉ M`, and `p ↦ pζ ∩ L_z` is injective on `M` because `ζ ∉ M`. So each excluded point excludes at most one `θ`.
  - Fix an admissible `θ`.
- **Step 6.**
  - Choose `Q₀ ∉ L₁`.
  - Apply a 1-extension to the edge `u₂p₁` of `H₂`, with third vertex `p₃`:
    - `p₁(θ) ≠ ζ`, since `ζ ∉ M`;
    - `Q₃ ∉ L₁`, by (x8);
    - `Q₂ ∉ {p₁(θ), ζ}`: `p₁(θ) ∈ M − {Q₁}` and `M ∩ L_z = {Q₁}`, while `ζ ∉ L_z`.

    This adds `p₂` with edges `p₂p₁, p₂u₂, p₂p₃`, for `+2`.
  - A 0-extension of `v₁` onto `p₁, p₂` adds `+2`.
  - Total: `r ≥ r(H₂, q₅(θ)) + 4 ≥ r(H₁) + 6 ≥ t(G₃) + 10 ≥ t(G)`.
  - The final graph is a spanning subgraph of `G*`. `S` and `π_aπ_b` are exactly the pin pairs that are not edges of `G*`, and `u₂p₁` is removed.
- **Output.** `L(u₁) := L′`, `L(u₂) := L_z`, `L(v₁) := L₁`, and `L(w) := L₃(w)` otherwise. The body points of `u₁` and `u₂` are both `ζ`; this is allowed, since neither is a pin of the other's body. `q(v₁) := Q₀`. **No move of `q₅(u₂)` is needed**, unlike the TR.
- **Invariant.**
  - (N1) and (N2) at `u₁` hold by (x4) and (x5); at `u₂` by (x8), (x9) and the choice of `Q₃`; at `v₁` because `p₁(θ) ≠ Q₂` and `Q₀ ∉ L₁`; at `w ∈ N₁` by (x6).
  - (N3) at `u₁u₂`: `L′ ≠ L_z`, by (x1).
  - (N3) at `u₁v₁`: `ζ ∈ L₁ − L′`.
  - (N3) at `u₂v₁`: `ζ ∈ L₁ − L_z`.
  - (N3) at `u₁w`: `Q₃ ∈ L′ − L_w`.
  - Every other edge: by (a). ∎

> **(NEW-I19)** `[PROVED]` *(Claim 6.5 Case 3, TR pp.17–18)* Assume (IH). Let `G` be connected with `G ≠ K₃`. Let `d(v₁) = 2`, with neighbours `u₁, u₂`, where `p₃ := u₁u₂ ∈ E` and `E(u₂) = {p₂, p₃}`. Then `A(G)` holds.

*Proof.*
- **Setup.**
  - `G₄ := G − {v₁, u₂}`.
  - `d_{G₄}(u₁) ≥ 1`, since otherwise `G = K₃`. So `G₄` has no isolated vertices.
  - `n₄ + m₄ = n + m − 5`, and `t(G) ≤ t(G₄) + 10` by (NEW-I7)(g).
  - Take a generic realization `(q₆, L₆)` of `G₄`, and fix `p₄ ∈ E_{G₄}(u₁)`.
- **Parameters.**
  - `Q₁ ≠ Q₃` on `L₆(u₁)`, avoiding the pins of `u₁` (cofinite).
  - `Q₂ ∉ L₆(u₁)`.
  - `Q₅ ∉ Q₁Q₂`.
  - `Q₆ ∉ Q₃Q₂`.
- **Output.** `L(v₁) := Q₁Q₂` and `L(u₂) := Q₂Q₃`.
- **Rank.** Five 0-extensions, each `+2`: `p₁` onto `(u₁, p₄)`; `p₃` onto `(u₁, p₄)`; `p₂` onto `(p₁, p₃)`; `v₁` onto `(p₁, p₂)`; `u₂` onto `(p₃, p₂)`. Total `+10`.
- **Invariant.**
  - `Q₂ ∉ L₆(u₁)`, so `L(v₁) ≠ L₆(u₁)` and `L(u₂) ≠ L₆(u₁)`.
  - `L(v₁) = L(u₂)` would put `Q₂` on `Q₁Q₃ = L₆(u₁)`, which it is not. ∎

> **(NEW-I20)** `[PROVED]` *(Claim 6.6, TR p.18)* Assume (IH). Let `p₁ = v₁v₂` be an edge with `def(G − p₁) = def(G)`, such that `G − p₁` has no isolated vertices. Then `A(G)` holds.

*Proof.*
- Take a generic realization `(q₁, L₁)` of `G₁ := G − p₁`.
- Put `q(p₁) := L₁(v₁) ∩ L₁(v₂)`. It differs from the other pins by (b).
- A 0-extension onto `v₁` and a pin of `v₁` gives `r ≥ t(G₁) + 2 = t(G)`.
- (N3) at `p₁` holds by (a). There is no free parameter. ∎

> **(NEW-I21)** `[PROVED]` *(Claim 6.8, TR pp.18–19)* Assume (IH). Let `G` be 2-edge-connected with minimum degree `≥ 2`. Let `{p₁, p₂}` be a 2-edge-cut with `def(G − p₁) = def(G) + 1`. Then `A(G)` holds.

*Proof.*
- **Setup.**
  - `G₁ := G − p₁` is connected, and `p₂` is a bridge of `G₁`.
  - `p₁ = uv` has its ends in different components `C_u ∋ u` and `C_v ∋ v` of `G₁ − p₂`. If both ends were in one component, `p₂` would be a bridge of `G`.
  - `t(G) = t(G₁) + 3`.
  - Fix `p₃ ∈ E_{G₁}(u)`.
- **Parameters.**
  - Take a generic realization of `G₁`, and let `Q := L₁(u) ∩ L₁(v)`. Then `Q ≠ q₁(p₂)` by (b).
  - The body point of `v` must satisfy `q(v) ∉ Q q₁(p₂)`. This is an open condition. If `p₂ ∈ E(v)`, that line is `L₁(v)`, which is already excluded.
  - This body-point condition replaces the TR's ε-move of `q₁(v)`.
- **Rank.**
  - `H₁ := G₁* + p₁` at `Q`, with edges `p₁u, p₁p₃`. This is a 0-extension, `+2`.
  - Define `Σ_u := C_u ∪ {e ∈ E(G₁) − p₂ : e ⊆ C_u}`, and `Σ_v` likewise.
  - In `G₁*`, every edge lies inside `Σ_u ∪ {p₂}` or inside `Σ_v ∪ {p₂}`. The edges of `p₁` go to `Σ_u ∪ {p₂}`.
  - Let `m := 0` on `Σ_u ∪ {p₁, p₂}`, and `m := J(q(·) − q(p₂)) = f_{P(q(p₂))} ∘ q` on `Σ_v`. Then `m ∈ Z(H₁)` by (NEW-I2)(ii).
  - On the bar `p₁v`, `m` gives `−det(Q − q(v), q(v) − q(p₂)) ≠ 0`. So `H₂ := H₁ + p₁v` has `r(H₂) = r(H₁) + 1`.
  - Total: `r(G*) ≥ t(G₁) + 3 = t(G)`.
- **Invariant.** (N3) at `p₁` holds by (a). ∎

> **(NEW-I22)** `[PROVED]` *(the final gluing, TR pp.19–20, with R1)* Assume (IH). Let `G` be 2-edge-connected with minimum degree `≥ 3` and `|𝒮| ≥ 2`. Then `A(G)` holds.

*Proof.*
- **Setup.**
  - Take `B₁`, `u_i`, `v_i`, `G₁`, `G₂` as in (NEW-I7)(j),(k), with `p₃ = u₁w₀`, `p₄ = w₀w₁`, `p₅ = w₁u₂`, `p₆ = v₁w₂`, `p₇ = v₂w₂`.
  - `G₁` and `G₂` are simple; `G₂` is simple because `v₁ ≠ v₂`. The case `u₁ = u₂` is allowed.
  - Neither has isolated vertices, and `n_i + m_i < n + m` by the sizes in (j).
  - Take generic realizations `(q₁, L₁)` and `(q₂, L₂)`. Since `def(G₁) = 0`, `G₁*` is infinitesimally rigid.
- **Parameter (R1).**
  - `a := q₂(p₆) ≠ b := q₂(p₇)`: two pins of `w₂`.
  - `a′ := q₁(p₃) ≠ b′ := q₁(p₅)`: if `u₁ ≠ u₂`, by (b); if `u₁ = u₂`, both are pins of `u₁`.
  - `α(x) := a′ + M(x − a)`, with free parameter `c′ = Mc` ((NEW-I3)(v)).
  - The direction of `L₂(v₁)` is `λ₁(b − a) + μ₁c`, with `μ₁ ≠ 0` because `L₂(v₁) ≠ L₂(w₂)` and both pass through `a`.
  - Exclude three lines of `c′`-space:
    - `det(b′ − a′, c′) = 0`;
    - `λ₁(b′ − a′) + μ₁c′ ∈ K·dir L₁(u₁)`, which is exactly the condition `α(L₂(v₁)) = L₁(u₁)`;
    - the same condition at `v₂`, for `α(L₂(v₂)) = L₁(u₂)`.
  - A similarity cannot replace `α`. Similarities scale `x·x` by a square, so they cannot send an isotropic segment to a non-isotropic one; this can happen over a field containing `√−1`, or in characteristic 2.
- **Output.**
  - Use `q₁` on `V(G₁*) − {w₀, w₁, p₃, p₄, p₅}`, and `α ∘ q₂` on `V(G₂*) − {w₂, p₆, p₇}`.
  - `q(p₁) := a′` and `q(p₂) := b′`.
  - `L := L₁` on `B₁`, and `L := α(L₂)` elsewhere.
- **Rank (TR p.20, with the references made explicit).**
  - `F₁ := G₁* − {w₀, w₁, p₄}` and `F₂ := G₂* − w₂`.
  - `G₁*` is `F₁` plus three 0-extensions: `p₄` onto `p₃, p₅`; `w₀` onto `p₃, p₄`; `w₁` onto `p₄, p₅`.
  - The points `q₁(p₃), q₁(p₄), q₁(p₅)` are not collinear: otherwise `q₁(p₅) ∈ q₁(p₃)q₁(p₄) = L₁(w₀)`, so `q₁(p₅) = L₁(w₀) ∩ L₁(w₁) = q₁(p₄)`.
  - So `r(F₁) = r(G₁*) − 6`. Likewise `r(F₁ + p₃p₅) = r(G₁* + p₃p₅) − 6 = r(F₁)`.
  - `r(F₂) = r(G₂*) − 2`, and `α` preserves ranks.
  - `G* + p₁p₂ = (F₁ + p₃p₅) ∪ α(F₂)` along the complete graph on `{p₁, p₂}`. By (NEW-I4)(ii) with `t = 2`: `r = r(F₁) + r(F₂) − 1`.
  - `p₁p₂` lies in the row span of `F₁ ⊆ G*`, so `r(G*) = r(G* + p₁p₂)`.
  - Using `n = n₁ + n₂ − 3` and `m = m₁ + m₂ − 3`: `r(G*) = 2(n + m) − 3 − def(G₂) ≥ t(G)`, by (NEW-I7)(k).
- **Invariant.** (N3) at `p₁` and `p₂` holds by the choice of `c′`. Every other edge is inherited from `G₁` or `G₂`. ∎

> **(NEW-I23)** `[PROVED]` *(the case split closes)* Let `G` be simple, without isolated vertices, and not `K₂` or `K₃`. Then `G` meets the hypotheses of one of (NEW-I13)–(NEW-I22).

*Proof.* Go through the cases in order.
1. If `G` is disconnected: (NEW-I13).
2. If `G` has a degree-1 vertex: (NEW-I14).
3. If `G` has a bridge: (NEW-I15).
4. If `G` is 2-edge-connected with a degree-2 vertex `v₁`:
   - `u₁, u₂` in one brick of `G − v₁`: (NEW-I16);
   - otherwise, `u₁u₂ ∉ E`: (NEW-I17);
   - otherwise, `u₁u₂ ∈ E` with both degrees `≥ 3`: (NEW-I18);
   - otherwise, `u₁u₂ ∈ E` with some degree 2: (NEW-I19).
5. If some edge `p` has `def(G − p) = def(G)`: (NEW-I20).
6. Otherwise `def(G − p) ≥ def(G) + 1 ≥ 1` for every edge `p`. By (NEW-I7)(h) and 2-edge-connectivity, `G` has a 2-edge-cut. For each such cut, `def(G − p₁) ∈ {def + 1, def + 2}` ((NEW-I5)(iii)).
   - If some cut gives `def + 1`: (NEW-I21).
   - If every cut gives `def + 2`: `G` is not superstrong by (NEW-I7)(i), so `|𝒮| ≥ 2`, and (NEW-I22) applies. ∎

##### The theorems

> **(NEW-I24)** `[PROVED]` *(TR Thm 6.1 over any infinite field)* Let `G` be simple without isolated vertices. Then:
> **(i)** `r(G*, q) ≤ t(G)` for every `q`;
> **(ii)** `G` has a non-degenerate pin-collinear realization with `r(G*, q) = t(G)`;
> **(iii)** every realization built on `p` in the nonempty Zariski-open set `U_G` has rank `t(G)`.
> So the maximum rank over the TR's pin-collinear body-and-pin realizations is `2(|V| + |P|) − 3 − def(G)`.

*Proof.* (i) is (NEW-I8)(ii). For (ii), induct using (NEW-I12) and (NEW-I23), where each case is proved from (IH). (iii) is (NEW-I10)(v). The final sentence follows from (NEW-I8)(i). ∎

> **(NEW-I25)** `[PROVED]` *(TR Thm 7.1 over any infinite field, and (MC-4)(b)'s equality)* Let `G` be simple without isolated vertices.
> **(i)** `r_RP(G) = 3|V| − 3 − def(G)`. It is attained exactly on the nonempty Zariski-open set `{p ∈ A_G : rank R′(p) = r_RP(G)}`.
> **(ii)** Under (H), for every `q` in a nonempty Zariski-open set of admissible `q`: `dim L(q) = dim F(q) = 3 + def₂(G)`. So `ℓ₀ = 3 + def₂(G)`, and (MC-4)(b) holds with equality at generic `q`.

*Proof.*
- (i), lower bound: (NEW-I24)(ii) and (NEW-I10)(iv) give `2m − n + r_RP ≥ t(G)`.
- (i), upper bound: for any `p ∈ A_G` and any partition `Q`, the `S` that are constant on each part form a `3|Q|`-dimensional space. They satisfy every constraint inside a part, and each crossing edge removes at most 2 dimensions. So `dim Z_RP ≥ 3 + def_G(Q)`.
- (ii), the dictionary. Put `c(q_u, q_v) := (x_u, y_u, 1) × (x_v, y_v, 1) = (y_u − y_v, x_v − x_u, x_uy_v − x_vy_u)`.
  - `F(q) = {h : h_u − h_v ∈ K·c(q_u, q_v)}`.
  - For `p := −q`, `P(p̃(uv))` is proportional to `D·c(q_u, q_v)`, with `D = diag(1, −1, 1)`.
  - So `h ↦ Dh` is an isomorphism `F(q) → Z_RP(G, −q)` whenever `−q ∈ A_G`. This is the workbook's dictionary, now derived.
  - The set of admissible `q` with `−q ∈ A_G` and `rank R′(−q) = r_RP(G)` is an intersection of two nonempty opens, so it is nonempty ((NEW-I1)(i)).
  - Step MC4's bijection gives `F(q) ≅ L(q)`. ∎

> **(NEW-I26)** `[PROVED]` *(TR Lemmas 4.2 and 5.2 recovered; the TR's proof of 4.2 fails)*
> **(i)** The *statement* of TR Lemma 4.2 holds: every pin-collinear realization has rank `≤ t(G)`, and some non-degenerate one attains `t(G)`. TR Lemma 5.2 holds too: a pin-line-generic realization, in the `U_G` sense, maximizes the rank.
> **(ii)** The TR's *proof* of Lemma 4.2 fails. **Witness.** Take `K₃` with `L(a) = L(b) = L(c)`. This is a pin-collinear realization, with rank 8 < 9 (`jjbuild.py --selftest`). The proof moves the pin `ac` along `L(c) = L(a)` onto a line `L₀ ≠ L(a)` through `q(ab)`. That forces `q(ac) = L₀ ∩ L(a) = q(ab)`, which violates (R-ii). This happens over `ℝ` as well.

*Proof.* (i) follows from (NEW-I24)(i)–(iii). ∎

> **(NEW-I27)** `[CONSTRUCTED jjbuild.py]` *(every construction, run exactly)* Over GF(2¹⁶), GF(3¹⁰) and GF(10 007), each of (NEW-I12)–(NEW-I22) was run at 25 instances (list below), with generic inputs drawn at random and checked against (a) and (b). At every instance, in every field:
> - every rank step claimed above holds;
> - the output satisfies (N1)–(N3);
> - `r(G*, q) = t(G)`, where `def` is computed by two oracles that agree;
> - (NEW-I9) holds in rank form.
>
> In total 75 of 75 outputs pass, with 0 excluded-value redraws and 0 rank failures at drawn parameters. Case 2 was run at 5 instances, including one with `def = 1`. The gluing was run at 5 instances, including `u₁ = u₂` and `def = 1`. The self-test additionally exhibits:
> - the (NEW-I26)(ii) witness;
> - the R0 witness (in characteristic 2, the TR's degree-1 pin-line contains the body point);
> - rejection witnesses for all three guards, with negative controls;
> - Lemmas 3.2 and 3.3 and (NEW-I5)(ii), checked by brute force at 36 seeded graphs on 3–6 vertices.

**What changed relative to the TR:**

| TR step (page) | status here |
|---|---|
| Lemmas 2.1, 2.3–2.9 (pp.3–6) | unchanged in substance. Proofs are written over `K` in (NEW-I2)–(NEW-I4), including 2.4 (TR cites Whiteley 1996, whose label is *Theorem* 2.2.2, pdf p.14) and 2.6. Lemma 2.7's completion step needs (NEW-I3)(i) for a non-injective `q`. |
| Lemma 2.2(b) (p.4) and every ε-move | replaced by (NEW-I1), with a named parameter and excluded set in each construction |
| §3, Thm 3.1, Lemmas 3.2, 3.3 (pp.6–8) | re-proved as (NEW-I5) and (NEW-I6); Thm 3.1 is not needed |
| degree-1 pin-line (p.9) | R0: (NEW-I8)(i) |
| Lemma 4.2 (p.9) | not used. Statement recovered in (NEW-I26); proof refuted by the witness. |
| Lemmas 5.1, 5.2 (pp.11, 13) | (NEW-I9); (NEW-I10) in non-degenerate form |
| Claims 6.2–6.10, final gluing (pp.14–20) | (NEW-I13)–(NEW-I22), with R2 carried as (NEW-I11) and R1 in (NEW-I22) |
| "G has ≥ 4 vertices" (p.14) | the base cases `K₂`, `K₃`: (NEW-I12) |
| Thm 7.1 (p.21) | (NEW-I25) |

---

**TR steps that could not be made field-general or non-degenerate: none.** These are the places where the TR is silent or slips, each with its fix and witness:

1. **The proof of Lemma 4.2 (p.9)** fails even over `ℝ`. Witness: `K₃` with one common pin-line (`jjbuild.py --selftest`). It is bypassed by R2, and its statement is recovered in (NEW-I26).
2. **Case 2's `L_1` (p.17) is undefined.** The fix is the auxiliary line `M` through `Q₁`, which makes `p₁(θ) = L′(θ) ∩ M`. It also makes the TR's move of `q₅(u₂)` unnecessary.
3. **Final gluing (p.19): `v₁ ≠ v₂` is never stated.** Without it, `G₂` has a double edge and no non-degenerate realization. It follows from tightness of `𝒮` together with the one-edge property, (NEW-I7)(j).
4. **Distinctness conditions that the ε-moves leave implicit**, now listed explicitly: in Case 1, `Q₁` must avoid `u₁`'s pins; in Case 2, (x5) and (x6).
5. **Lemma 2.7's completion (p.5)** needs the complete graph on a possibly non-injective point set to be rigid. This is (NEW-I3)(i).
6. **Thm 6.11 (multigraphs) was not addressed.** It is not needed, since `G` is simple under (H).

**Script.** `jjbuild.py` is in the writerI scratchpad directory of this session. It is seeded (`20260925`), exact, and stdlib-only. It reuses `jjchar.make_field` and `maincomp.def_k`.

**Before committing it**, move it to `notes/scripts/w4/jjbuild.py`, and replace its `_REPO` bootstrap with the canonical three-line idiom. As written, the bootstrap holds a literal local path, which must not be committed. The three-line idiom is:
```python
import os, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap
```

| command (from the repository root) | output | time |
|---|---|---|
| `python3 jjbuild.py --selftest` | witnesses rejected with negative controls passing; `r(K₃*) = 8 < 9` at one common pin-line; R0 witness True; Lemmas 3.2/3.3 etc. verified at 36 graphs; `selftest: OK` | 0.3 s |
| `python3 jjbuild.py --run` | `GF(2^16): all 25 constructions OK; excluded-value redraws 0; rank failures at drawn parameters 0`, and the same for GF(3^10) and GF(10007). Each of the 75 per-instance lines ends `r(G*)=t(G) non-degenerate`. | 0.9 s |

The output is byte-identical under `PYTHONHASHSEED` 0, 1, 7 and 12345. `git status` is clean.

Example output line (Case 2, `def = 1`): `GF(3^10): Case2 triangle + 4-cycle + 5-cycle (def > 0) … r(G3*) = t(G3) 22 == 22; H0 = G3* - S 22 == 22; H1 (two 1-extensions) 26 == 26; H2 (vertex split) 28 >= 28; H2 after the pencil move (theta) 28 >= 28; 1-ext p2 30 >= 30; 0-ext v1 32 >= 32; r(G*) vs t(G) 32 == 32`.

Two of my own instances were first labelled wrongly: "two K4 + a–d" puts u and x in one brick, and "C6 + chord" fails Claim 6.8's hypothesis. The driver's hypothesis asserts caught both before any figure was recorded, and I replaced them.
