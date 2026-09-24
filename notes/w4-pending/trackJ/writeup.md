## Track J — the last ear cell, `k = 1`, `δ₂ = 3`, `δ ∈ {3, 4}`; and whether EAR alone covers 𝒮 (W4-reopen P1, 2026-09-24)

*Read-only research track. Provisional labels `(J-n)`; the coordinator renumbers at landing. It builds on
Track B's `(B-1)`–`(B-11)` and Track F's `(F-1)`–`(F-18)` (scratch write-ups, not second-read) and on
the workbook through Step MC16. Scripts and outputs are in this directory (table at the end); every
figure names its script. "JJ at `Γ`" is Jackson–Jordán's equality at the named simple graph, as in
Step MC15; "IH" is the strong induction hypothesis of Step MC13.*

### Verdict

- **In 𝒮 the cell is closed except for one structural sub-cell, and that sub-cell is not needed for
  coverage.** The results, all under IH and modulo JJ at named smaller graphs:
  - **(J-2), the rigid-set closure.** Let a `k = 1` chain `y` with `1 ≤ δ ≤ 4` lie in a proper
    rigid set `W`, where `G/G[W]` is simple and additive. Then `X₀(G)` attains. The proof is
    the ear step plus rigidity of `G[W]` at `X₀(G)`'s generic point. That rigidity comes from
    restriction (MC-68)(d) and IH at `G[W]`. The proof uses neither CONTRACT's no-jump
    condition (ii) nor `X₀(G/H)`.
  - **(J-1), the combinatorial supply of `W`.** Every *locally minimal* set of `def₃`-classes
    through `[a], [b]` gives such a `W`, whenever that `W` is proper. This includes every
    non-rigid `G`.
  - **(J-3), what is left over (Case II).** When no such `W` exists, `G` is rigid. The class
    quotient `Γ₃` of `G − y` is then the unique minimiser, and every proper set of classes
    through `[a], [b]` has `c ≥ 5`.
  - **(J-8), Case II with `Γ₃` a path (the class ring).** This closes by the chord route:
    - at `δ = 3`, from the flat point;
    - at `δ = 4`, from a "folded" point whose dual is a skew pentagon.

  The `δ = 3` half holds for **every** `G′` whose minimiser is a path, not only in 𝒮.
- **(J-6), EAR covers 𝒮.** Every `G ∈ 𝒮` has a chain closed by one of: a landed step, Track F's
  (F-16) for (a′), or (J-2). The combinatorial core is a count, (J-6a), in the style of Theorem
  S's rigid case. If every chain is a `k = 1` chain in (c′), then some chain vertex lies inside a
  non-singleton class of `G − y`. That class is additive by a count, (J-5), so (J-2) closes that
  chain.
  - So a second proof of (MC-89) goes through with EAR in place of Theorem S (MC-80), (MC-87)
    and CONTRACT at cores with `def₂(H) ≥ 1`.
  - **It is not fully independent.** It shares (MC-68)(d) and JJ with the first proof. It also
    rests on F-16, and so on Track A's (A-11).
- **What remains open is the sub-cell (J-10), "Case II-cyclic":** the chain `y` itself, when `G` is
  rigid and `Γ₃` has a cycle.
  - The chord route reduces it exactly to two conditions at the generic point of `X₀(G′ + ab)`:
    the class-level framework of `G′` carries no self-stress there, and, at `δ = 4`,
    `ρ_Γ ⊄ n^⊥` (J-7), (J-9).
  - In 𝒮, `a′(z₀)` *equals* the number of those class-level stresses (J-9). That proves
    Track B's (B-11) whenever `Γ₃` is a forest, or its 2-core is properly additive in `G″`.
  - Every tested Case II-cyclic instance is certified: all 6 in 𝒮 on ≤ 13 vertices, plus 5
    constructed ones.
- **Bad configurations.** None was found. The analysis says where one would have to live: a class
  cycle of length ≥ 7 whose hinge lines become special at the chord point. The flag incidences
  there touch only the hinges at `a` and `b`.

### Setting and notation

Step MC10's, with Step MC13's `Pen`, `N`, `star`, `⊥` (Klein), and Track B's chord point. The graph is
`G = G′ + (a − y − b)`, with `a ≁ b`, `G′` satisfying (H), and `G″ := G′ + ab`. Also `n := p_a p_b`,
`m := π_a ∩ π_b`, and `f`, `g`, `δ`, `δ₂` as in Step MC10.

**Classes.** `Γ₃ := Γ̂(G′)` has as vertices the **classes**, which are the maximal rigid sets of `G′`
(**blobs**) and the singletons (Step MC16). `A = [a]` and `B = [b]`, and `A ≠ B` since `δ ≥ 1`.
`Γ₃` is simple and rigid-free (MC-77). For a set `Y` of classes, put
`c(Y) := 6(|Y| − 1) − 5e_{Γ₃}(Y)`. Then `δ = min{c(Y) : A, B ∈ Y}` ((F-1), (MC-79)(i)), and a
minimiser is a path of `δ + 1` classes or contains a cycle ((F-13)).

A set `Y ∋ A, B` is **locally minimal** if `c(Y) ≤ 4` and `c(Y) ≤ c(Z)` for every `Z ⊆ Y` with
`A, B ∈ Z`. Put `W_Y := ∪Y ∪ {y}`.

**Class-level framework.** The bodies are the classes and the hinges are the bridge lines
`L_e = p_u ∧ p_v`, one for each edge `uv` of `G′` joining two classes. For a class set `X`,
`ρ_X(z)` is the relative motion space of `B` against `A` in this framework on `Γ₃[X]`.

**Additivity** of `W` means `def₂(G) = def₂(G[W]) + def₂(G/G[W])`. In 𝒮 every induced subgraph
satisfies (S), so `def₂` is attained only by singletons (MC-76). Additivity at `W` is then
equivalent to the singleton partition of `G/G[W]` being optimal. That in turn is equivalent to:

  **for every nonempty `Z′ ⊆ V ∖ W`: `2(e(Z′) + e(Z′, W)) ≤ 3|Z′|`.**   (A)

Each part of a partition of `G/G[W]` contributes its own loss, and a part not containing the
contracted vertex has loss `≥ 0` by (S).

**The piece bound**, used three times. Let `Z′ ⊆ V ∖ W`, and let `Z` be the set of classes (and
`y`, if `y ∈ Z′`) meeting `Z′`. Split `Z′` into its pieces `Z′ ∩ X`. (S) gives
`2e(piece) ≤ 3|piece| − 3`. Every other edge of `Z′`, or from `Z′` to `W`, joins two distinct
classes, and there is at most one such edge per pair. Hence

  `2(e(Z′) + e(Z′, W)) ≤ 3|Z′| − 3|Z| + 2(e(Z) + e(Z, W))`,

with the last two terms counted at class level. So (A) holds as soon as
**`e(Z) + e(Z, W) ≤ 3|Z|/2`** for every nonempty set `Z` of outside classes.

---

## Part I — the rigid-set closure, and EAR covers 𝒮

> **(J-1)** `[PROVED]` *(locally minimal class sets give additive rigid sets)* Let `G ∈ 𝒮` and let
> `y` be a `k = 1` chain with `1 ≤ δ ≤ 4`. For every locally minimal `Y`:
> - **(a)** `G[W_Y]` is rigid and satisfies (H);
> - **(b)** every vertex outside `W_Y` has at most one neighbour in `W_Y`, so `G/G[W_Y]` is simple;
> - **(c)** `W_Y` is additive.
>
> Every minimiser (`c(Y) = δ`) is locally minimal.

*Proof.* **(a) Rigidity.**
- Merging the parts that meet one class never lowers `val₃` ((MC-77)'s proof). So `def₃(G[W_Y])`
  is a maximum over partitions `𝒫` of the class set `Y ∪ {y}`.
- There `val(𝒫) = c(Y ∪ y) − Σ_{Z ∈ 𝒫} c(Z)`, with `c(Y ∪ y) = c(Y) − 4`, since `y` has two edges
  into `Y`.
- Let `Z₀` be the part containing `y`.
  - If `A, B ∈ Z₀`, then `c(Z₀) = c(Z₀ − y) − 4 ≥ c(Y) − 4`, by local minimality.
  - Otherwise `c(Z₀) = c(Z₀ − y) + 6 − 5·[A or B in Z₀] ≥ 1`. This uses `c ≥ 0` on class sets
    (`c = 0` on a single class, and `c ≥ 1` otherwise by rigid-freeness).
- Every other part has `c ≥ 0`. So `val(𝒫) ≤ 0`.

**(a) Condition (H).**
- *Connected.* `Γ₃[Y]` is connected, because a disconnected `Y` has `c(Y) ≥ 6`.
- *Minimum degree.*
  - A blob vertex has 2 neighbours in its blob.
  - A singleton class `X ∉ {A, B}` of degree 1 in `Γ₃[Y]` could be deleted with
    `c(Y − X) = c(Y) − 1`, against local minimality.
  - A singleton `A` or `B` gains the edge to `y`.

**(b), (c).** Let `Z` be a nonempty set of classes outside `Y`. Then `c(Y ∪ Z) ≥ δ ≥ c(Y) − 3`, so

  `5(e(Z) + e(Z, Y)) = 6|Z| + c(Y) − c(Y ∪ Z) ≤ 6|Z| + 3`.   (★)

- `|Z| = 1`: (★) gives `e(Z, Y) ≤ 1`. That is (b), since `y`'s neighbours lie in `W_Y`. It also
  gives the piece bound's requirement.
- `|Z| ≥ 2`: `(6|Z| + 3)/5 ≤ 3|Z|/2`.

So (A) holds. ∎

> **(J-2)** `[PROVED-MOD (MC-33)]` *(the rigid-set closure; JJ at `G″` and at `G[W]`, `G/G[W]`;
> rests on (MC-68)(d))* Let `G ∈ 𝒮` satisfy IH, and let `y` be a `k = 1` chain with `1 ≤ δ ≤ 4`.
> Let `W ∋ y` be a proper subset of `V(G)` such that:
> - `G[W]` is rigid and satisfies (H);
> - `G/G[W]` is simple;
> - `W` is additive.
>
> **Then `X₀(G)` attains.**

*Proof.*
1. *The chain.* In 𝒮, `a ≁ b` and `δ₂ ≥ 2` ((MC-79)(ii)). So `dim U ≥ 2` (JJ at `G″`),
   restriction `X₀(G) → X₀(G′)` is dominant, and the generic flags are in orbit (i) ((F-10)).
   `λ = 2` at a generic `p_y ∈ m`.
2. *The count at `G′`.* (MC-44), with IH at `G′` and `G″`, gives `r = δ` at `X₀(G′)`'s generic
   point.
3. *Restriction to `W`.* (MC-68)(d) makes `F(G, q) → F(G[W], q|_W)` onto at generic `q`. Through
   Step MC4's bijection, so is `L_G(q) → L_{G[W]}(q|_W)`. So the generic point of `X₀(G)` restricts
   to a generic point of `X₀(G[W])`. There `G[W]` is rigid, by IH, since `|W| < |V|` and
   `def₃(G[W]) = 0`.
4. *At the generic point `w` of `X₀(G)`.* By (MC-16) at `G[W] = G[W − y] + ear₁`,
   `6 = dim M_{G[W]} = dim M^{weld}_{W−y} + dim(ρ_{W−y} ∩ Λ(y))`. Also
   `dim M^{weld}_{W−y} ≥ 6`. So `ρ_{W−y} ∩ Λ(y) = 0`.
5. *Conclusion.* Restricting motions gives `ρ ⊆ ρ_{W−y}`, so `ρ ∩ Λ(y) = 0`. Now (MC-16) at `G`
   gives `dim M_G = dim M^{weld}_{G′} + 0 = 6 + f − δ = 6 + g`. That is `6 + def₃(G)` by (MC-17),
   since `δ ≤ 4`. ∎

*Remarks.*
- This is the geometric twin of (MC-79)(iv) (locality). It closes the chain in any cell with
  `δ ∈ [1, 4]`. That includes (F-14)'s open "`δ = 2`, cyclic class quotient" wherever such a `W`
  exists.
- It does not need the chord point, class rigidity at `X₀(G′)`, (MC-69), (MC-70), or `X₀(G/H)`.

> **Corollary (J-2′)** *(Case I)* In the setting of (J-1), suppose some locally minimal `Y` has
> `W_Y ≠ V(G)`. Then `X₀(G)` attains. This holds whenever `G` is not rigid: `W_Y` is then rigid
> and proper. For non-rigid `G` the maximal rigid set `R ∋ y` also serves as `W`: its quotient is
> simple by (MC-77), and it is additive by (MC-70), since `def₃(G) > 0`.

> **(J-3)** `[PROVED]` *(the dichotomy)* Suppose (J-2′) does not apply to `y` (**Case II**). Then:
> - **(i)** `V(Γ₃)` is the unique set through `A, B` with `c ≤ 4` that is locally minimal. In
>   particular it is the unique minimiser, `c(V(Γ₃)) = δ`, and `G = G[W_{V(Γ₃)}]` is rigid.
> - **(ii)** Every proper class set through `A, B` has `c ≥ 5`.
> - **(iii)** Either `Γ₃` is a path `A = R₀ − ⋯ − R_δ = B` (**Case II-tree**: `G` is a ring of `δ + 2`
>   bodies, `y` among them), or `Γ₃` has a cycle (**Case II-cyclic**). In the cyclic case `Γ₃` has
>   girth `≥ 7`. Every ear of `Γ₃` without `A` or `B` inside has length `≤ δ + 1`, and every leaf
>   is `A` or `B`.

*Proof.*
- (ii): If `Y` is proper with `c(Y) ≤ 4`, a `c`-minimising subset through `A, B` is locally
  minimal and proper.
- (i) follows from (ii).
- (iii):
  - *Tree case.* A leaf other than `A`, `B` could be deleted with `c` dropping by 1.
  - *Ears.* Deleting the interior of an ear of length `ℓ` gives `c = δ + 6 − ℓ`, and (ii) needs
    this to be `≥ 5`.
  - *Girth.* (MC-77). ∎

**The unicyclic Case II-cyclic shapes** follow from (ii). Write `L` for the cycle length, `d₁, d₂` for
the arcs between the attachment classes of `A`, `B`, and `p, p′` for the pendant lengths:
- `δ = 3`: `L = 7` with arcs `(3,4)` and `p + p′ = 2`; or `L = 8` with arcs `(4,4)` and `p + p′ = 1`.
- `δ = 4`: `L = 7` (`p + p′ = 3`), `L = 8` (`p + p′ = 2`), `L = 9` with arcs `(4,5)`
  (`p + p′ = 1`), or `L = 10` with arcs `(5,5)` (`p + p′ = 0`).

Multicyclic shapes exist too, for example a `θ(5,5,6)` of classes with `A`, `B` inside two arcs.

> **(J-5)** `[PROVED]` *(blobs of `G − y` are additive in `G`)* Let `G ∈ 𝒮`, and let `y` be a `k = 1`
> chain with `δ ≥ 1`. Every blob `X` of `G′ = G − y` is a proper rigid set of `G`, with `G/G[X]`
> simple and additive, and `G[X]` satisfies (H).

*Proof.*
- *Simple quotient.* Another class has at most one edge to `X` ((MC-77)). The vertex `y` has at
  most one neighbour in `X`, since `A ≠ B`.
- *(A), by the piece bound with `W = X`.* Take a set `Z` of outside classes, possibly with `y`.
  - If `y ∉ Z`: rigid-freeness gives `c({X} ∪ Z) ≥ 1`, so `5(e(Z) + e(Z, X)) ≤ 6|Z| − 1`, and
    `2e ≤ 3|Z|` follows.
  - If `Z = {y}`: `e ≤ 1`.
  - If `Z = Z₀ ∪ {y}` with `Z₀ ≠ ∅`: `5(e(Z₀) + e(Z₀, X)) ≤ 6|Z₀| − 1`, and `y` adds at most 2.
    Then `2e ≤ (12|Z₀| − 2)/5 + 4 ≤ 3(|Z₀| + 1)`, because `|Z₀| ≥ 1`. ∎

> **(J-6a)** `[PROVED]` *(the count)* Let `G ∈ 𝒮` have only `k = 1` chains, and let `y` be one with
> `δ ≥ 1`. Then some degree-2 vertex `w ≠ y` of `G` lies in a blob of `G − y`.

*Proof.* Suppose not. Degrees are taken in `Γ₃`.
- *Blobs.* A blob `X` has at least 4 vertices of degree 2 in `G[X]`. The reason is
  `Σ_{v ∈ X}(3 − deg_X v) = 3|X| − 2e(X) ≥ 4` by (S), where each term is `≤ 1` by rigidity. By
  assumption these vertices have degree `≥ 3` in `G`, so each has an edge leaving `X`. There is
  at most one edge to each other class, and only `a`, `b` see `y`. Hence
  `deg(X) ≥ 4 − [X ∈ {A, B}]`.
- *Singleton classes.* A singleton `{v}` with `v ∉ {a, b}` has `deg = deg_G(v)`, which is 2
  exactly when `v` is a chain vertex. A singleton `A` has `deg = deg_G(a) − 1 ≥ 2`.
- *The split.* Let `T` be the classes of degree exactly 2 other than `A`, `B`. These are chain
  vertices. They are pairwise non-adjacent, since all chains have `k = 1`, and none is adjacent
  to `y`. Let `H` be the rest: `A`, `B` have degree `≥ 2`, the others degree `≥ 3`.
- *The two bounds.* With `cyc` the cyclomatic number of the connected `Γ₃`:
  - `2e(Γ₃) = 2(|T| + |H| − 1 + cyc) ≥ 2|T| + 3|H| − 2`, so `|H| ≤ 2cyc`;
  - `e(Γ₃) ≥ 2|T|`, so `|T| ≤ |H| + cyc − 1`.
- *The contradiction.* `c(V(Γ₃)) = |T| + |H| − 1 − 5cyc ≤ 2|H| − 2 − 4cyc ≤ −2`. But `c ≥ 1` by
  rigid-freeness, since `|Γ₃| ≥ 2`. ∎

> **(J-6)** `[PROVED-MOD (MC-33)]` *(EAR covers 𝒮)* Under IH, **every `G ∈ 𝒮` has a chain whose ear step
> is closed**, in one of three ways:
> - by a landed step (usable, (MC-79)(v));
> - by (F-16), for (a′);
> - by (J-2), for a `k = 1` chain in (c′) lying in a proper additive rigid set with simple quotient.

*Proof.*
- `G` has chains, since it has at least 4 degree-2 vertices.
- If none is usable or in (a′), then every chain is a `k = 1` chain in (c′), by (MC-79)(v).
- Pick one, `y`. By (J-6a), a chain vertex `w` lies in a blob `X` of `G − y`.
- By (J-5), `X` is a proper additive rigid set with simple quotient containing `w`. `w` is a
  `k = 1` chain in (c′) with `δ_w ≤ 4` ((MC-79)(ii)).
- (J-2) closes it. ∎

**What (J-6) does to (MC-89).** The reduction to 𝒮 is unchanged:
- CUT/BRIDGE, BASE, FLAT, THETA;
- CONTRACT at maximal `def₂`-rigid sets, (MC-75)/(MC-59)(d).

Inside 𝒮, (J-6) replaces Theorem S (MC-80) and its cores, (MC-87), and CONTRACT at cores with
`def₂(H) ≥ 1`.

The citations it consumes:
- (MC-68)(d), with JJ at `G[W]` and `G/G[W]`;
- (MC-44) (IH at `G′`, `G″`), and JJ at `G″`;
- (F-16), with Track A's (A-11);
- the landed steps.

It does **not** consume (MC-69) (no-jump), (MC-39)'s (ii), (MC-70), (MC-71) at `def₂(H) ≥ 1`, or
`X₀(G/H)`. The shared citations with the first proof are (MC-68)(d) and JJ. So this is a second
proof of the structural half, not a JJ-independent one.

`[CONSTRUCTED earcover.py]` The necklaces:
- The stuck families of (MC-83)/(MC-84) (`QsQsQ`, `QQQQs`, `Q⁵`, `QsQsQs`, `Q⁶`, `Q⁷`, `AsAsAs`,
  `A⁶`, `A⁷`, `TsTsTs`, `T⁶`, `T⁷`) all have closable chains.
- **Every (c′) chain in them is closed**: the bead chains are (J-2′), and the singles are
  Case II-tree, (J-8).
- At `QsQsQ`, `QsQsQs` and `TsTsTs`, `j2check.py` certifies (J-2)'s mechanism. At one exact
  certified `X₀(G)` picture, restriction `L_G → L_{G[W]}` is onto, `G[W]` is rigid (rank
  `6(|W| − 1)`), and `G` attains (78/78, 84/84, 156/156).

---

## Part II — the chord route at `y` itself (Case II), and what it leaves

Here `z₀` is Track B's generic chord point, generic in `L_{G″}(q)`, and `z(s) = z₀ + sz₁`.

> **(J-7)** `[PROVED-MOD (MC-33)]` *(ρ̄ is constant when the class level does not degenerate)* Assume:
> - IH, `a ≁ b`, `δ₂ = 3` (FG and case A, modulo JJ at `G″` and `(G″)_{ab}`), and `δ ∈ {3, 4}`;
> - the classes of `G′` are rigid at `X₀(G′)`'s generic point ((F-13): (MC-68)(d) with (MC-70),
>   or in 𝒮 the count of (J-5) applied inside `G′`).
>
> Let `X` be a minimiser, and suppose at `z₀`:
> - **(i)** the class-level framework on `Γ₃[X]` is independent (rank `5e(X)`);
> - **(ii)** its welded version (`A` glued to `B`) has motion space of generic dimension.
>
> Then `ρ̄(z₁) = ρ_X(z₀)` for generic `z₁`. It is `δ`-dimensional and independent of `z₁`.
> Hence **at `δ = 3`, `X₀(G)` attains**, and **at `δ = 4`, `X₀(G)` attains if `ρ_X(z₀) ⊄ n^⊥`**.

*Proof.*
1. *Generic points.* (i) is an open condition that holds at `z₀ ∈ L_{G″}(q) ⊆ L_{G′}(q)`, so it
   holds at generic `z ∈ L_{G′}(q)`. There `dim M_X = 6 + c(X) = 6 + δ`. Restriction to `∪X`
   gives `ρ ⊆ ρ_X`, and `dim ρ_X ≤ dim M_X − 6 = δ = dim ρ` ((MC-44)). So `ρ = ρ_X` at generic
   `z`.
2. *Regularity at `z₀`.* Near `z₀`, (i) makes `M_X(z)` a vector bundle of rank `6 + δ`. By (ii)
   and upper semicontinuity, `M_X^{weld}(z)` has constant dimension. So `ρ_X(z)` is a
   rank-`δ` bundle, and `ρ̄(z₁) = lim_{s→0} ρ(z(s)) = ρ_X(z₀)`. [This is (B-2)'s limit, now
   independent of `z₁`.]
3. *The bound.* By (B-2), `dim M_G ≤ 6 + g + dim(ρ̄ ∩ Pen(y₀, σ̄))`, with `ρ̄ ∩ ⟨n⟩ = 0`. Pencils
   through `n` meet `ρ̄` exactly when their tensor `y₀ ⊗ v̄` lies in the image `R̄` of `ρ̄ ∩ n^⊥`
   in `n^⊥/⟨n⟩` ((B-3)'s proof). If `dim R̄ ≤ 3`, the bad tensors form a fixed proper closed
   subset of the quadric `P¹ × P¹`, a conic or less.
4. *The reachable pairs.* For fixed generic `z₁`, the reachable pairs form the graph of the
   Möbius map `[s₀ : s₁] ↦ [φ₂s₀ : −φ₁s₁]`, where `θ = [φ₁(z₁) : φ₂(z₁)]` ((B-1)). Under FG, `θ`
   takes cofinitely many values on the generic `z₁`. Infinitely many distinct irreducible
   curves cannot all lie in the fixed curve. So some reachable pair avoids it, and
   `dim M_G = 6 + g = 6 + def₃(G)`.
5. *The two values of `δ`.* `dim R̄ = dim(ρ̄ ∩ n^⊥) ≤ 3` holds automatically at `δ = 3`. At
   `δ = 4` it is `ρ̄ ⊄ n^⊥`. ∎

> **(J-8)** `[PROVED-MOD (MC-33)]` *(the path case)* In (J-7)'s setting, let the minimiser `X` be a path
> `A = R₀ − ⋯ − R_δ = B` with bridges `L_j = p_{u_j} ∧ p_{v_j}`. Then (i) is automatic, since a tree of
> bodies is independent. (ii) says `L₁(z₀), …, L_δ(z₀)` are independent, and then
> `ρ_X(z₀) = ⟨L_j(z₀)⟩`.
> - **(a) `δ = 3`: `X₀(G)` attains, for every `G′` satisfying (H)** (with (F-13)'s class rigidity).
> - **(b) `δ = 4`: `X₀(G)` attains if the folded flexes of the ring `G″[∪X]` extend to `F(G″, q)`.**
>   They do when `∪X = V(G′)` (Case II-tree), or when `∪X` is additive in `G″` with simple
>   quotient ((MC-68)(d) at `G″`). **In 𝒮 the latter always holds**: by (★) with `c(X) = δ`,
>   `5(e(Z) + e(Z, X)) ≤ 6|Z|`, and `G″` satisfies (S) because `δ₂ = 3`.

*Proof.* Both conditions below are open on `L_{G″}(q)`, so it suffices to exhibit one point of
`L_{G″}(q)` where they hold.

**(a).** Take the flat point `z = 0 ∈ L_{G″}(q)`. The `L_j(0)` are the three lines of `Π` over
`ℓ_j = q_{u_j}q_{v_j}`. They are independent in `Λ²Π` iff the `ℓ_j` are not concurrent. At generic
`q` they are not concurrent: concurrency is forced only by a common vertex, and three consecutive
bridges touch four distinct classes. Then (J-7) applies.

**(b) The folded point.**
- *The flex.* Take `P ≡ σ_j` on `R_j`, with `σ_j − σ_{j−1} = t_jℓ_j`, `σ₀ − σ₄ = t₀ℓ_{ba}` and
  `Σ t_eℓ_e = 0`. Here `ℓ_e := p̂_u × p̂_v` for each bridge and for `ab`. The solution space is
  2-dimensional, and every `t_e ≠ 0` at a generic solution. Constants are flexes of each class,
  so `P` is a flex of the ring.
- *The configuration.* At `z = Φ(P)`, `R_j` lies in the plane `σ_j`, `L_j = σ_{j−1} ∩ σ_j`, and
  `n = σ₄ ∩ σ₀`.
- *Duality.* Point–plane duality preserves linear relations and incidence among lines. It sends
  these lines to the edges `s_{j−1}s_j` and `s₄s₀` of a closed pentagon in the dual space, with
  edge vectors `t_eℓ_e` in the affine chart.
- *General position.* Four of the five points are coplanar iff three cyclically consecutive edge
  vectors are dependent. That means three consecutive lines of `(ℓ₁, …, ℓ₄, ℓ_{ab})` are
  concurrent, which is excluded as in (a). So the points are in general position, and form a
  projective frame `(e₀, e₁, e₂, e₃, Σeᵢ)`. The five edges of that pentagon are independent:
  - `e₀₁`, `e₁₂`, `e₂₃`;
  - `−(e₀₃ + e₁₃ + e₂₃)`;
  - `−(e₀₁ + e₀₂ + e₀₃)`.

  So `L₁, …, L₄, n` are independent.
- *`L₂` misses `n`.* `L₂` meets `n` iff `s₁s₂` meets `s₄s₀`, iff `s₀, s₁, s₂, s₄` are coplanar,
  which is excluded. So `L₂ ∉ n^⊥`, `ρ_X ⊄ n^⊥` at the generic `z₀`, and (J-7) applies. ∎

`[MEASURED foldcheck.py]` At the folded point (exact):
- `L₁` and `L_δ` meet `n`, as the plane `σ₀` (resp. `σ_δ`) forces; the middle bridges do not;
- rank `(L_j) = δ` and rank `(L_j, n) = δ + 1`, at all six Case II-tree instances;
- at `δ = 3`, the flat point also gives rank 3.

> **(J-9)** `[PROVED-MOD (MC-33)]` *(`a′(z₀)` counts class-level stresses)* Let `G ∈ 𝒮`, with `δ₂ = 3` and
> `δ ≥ 2`. Every class of `G′` is additive in `G″` with simple quotient: this is the piece bound with
> (★) in `G″`, the edge `ab` costing at most 1. So every class is rigid at `z₀`, by (MC-68)(d) at
> `G″` and IH. Hence **`M_{G′}(z₀)` is the class-level motion space**, and
>
>   **`a′(z₀)` = the dimension of the class-level self-stresses of `G′` at `z₀`.**
>
> Two conditions each force `a′(z₀) = 0`, and then (J-7)(i) holds for `X = Γ₃`:
> - **(a)** `Γ₃` is a forest (then Case II is Case II-tree);
> - **(b)** the union `∪K` of the classes of `Γ₃`'s 2-core is proper, additive in `G″`, and has a
>   simple quotient. Restriction then makes `z₀|_{∪K}` generic for `G′[∪K]`, which attains by IH.
>   Class-level independence on `K` follows, and pendant trees carry no stress.
>
> So **(B-11)'s `a′(z₀) = 0` holds in 𝒮 (at `δ₂ = 3`) whenever `Γ₃` is a forest or (b) holds.**
> Examples of (b): the unicyclic shapes with `p + p′ ≥ 2`. At `δ = 3` this closes Case II-cyclic
> for them, via (J-7). (ii) holds in Case II because `G″` is rigid at `z₀` (IH), and welded motions
> are `G″`-motions.

> **(J-10)** `[OPEN]` *(the residue: Case II-cyclic at `y` itself)* In 𝒮, the ear step at a `k = 1` chain
> `y` with `δ ∈ {3, 4}` is proved except in two situations:
> - Case II-cyclic, where the class-level framework of `G′` carries a self-stress at the generic
>   point of `X₀(G″)`. This is `a′(z₀) ≥ 1`, possible only where (J-9)(b) fails:
>   - the pendant-free ring `L = 10`, arcs `(5,5)`;
>   - the one-pendant shapes `L = 8`, arcs `(4,4)` and `L = 9`, arcs `(4,5)`;
>   - multicyclic `Γ₃`.
> - At `δ = 4`, any Case II-cyclic shape with `ρ_Γ(z₀) ⊆ n^⊥`.
>
> **This residue is not needed for coverage** (J-6). Outside 𝒮, the cyclic class structures and the
> `δ = 4` path case without additivity remain as in (B-10) and (F-14).

*Where a proof would come from.* A sketch, not checked; the stop rule fires here: pendant-free
rings, one-pendant shapes and multicyclic shapes each need their own argument. For the `(5,5)`
ring:
- Each arc plus `A − B` is a rigid 6-ring that is additive in `G″`. Restriction and IH make each
  arc's five lines, together with `n`, independent at `z₀`.
- A stress means the two arc hyperplanes `H₁ = span(arc₁)` and `H₂ = span(arc₂)` coincide.
- `F(G″) = F(S₁) ×_{F(A∪B)} F(S₂)`, since flex conditions are edge-local. So with `A`, `B` fixed,
  the two arcs vary independently.
- `H₁ = H₂` would force `H₁` to be constant on its fibre. A dual argument on the fibre's folded
  points refutes that: `L₃*` would sweep a whole star, which forces a special complex whose axis
  contains three independent points at infinity.
- The `n^⊥` condition at `δ = 4` needs a further step that I did not find.

`[MEASURED]` Every Case II-cyclic instance tested is certified by (J-7): `ringprobe.py` and
`cycprobe.py`, exact chord point, one draw each. Each has:
- class-level `G′` independent at `z₀` (an open condition, so a certificate);
- `ρ̄(z₁) = ρ_Γ(z₀)` at two `z₁`;
- `dim(ρ_Γ(z₀) ∩ n^⊥) = δ − 1`;
- `a′ = 0`, and `X₀(G)` attaining.

The instances:
- all 6 Case II-cyclic chains of 𝒮 on ≤ 13 vertices (`findcyc.py`): 4 of shape `L = 7, (3,4)`,
  `p + p′ = 2`, which (J-9)(b) covers, and 2 of shape `L = 8, (4,4)`, `p + p′ = 1`;
- 5 constructed rings `C₁₀` of classes with `A`, `B` antipodal, `δ = 4`. They carry 0, 1 (two
  placements), 2 or 4 `C₄` blobs; the blob-free one is the θ-graph `θ(2,5,5)`.

The constructed `C₉` rings with `A`, `B` at distance `(4,5)` (`δ = 3`) are **Case I**, not Case II.
Their 4-arc together with `y` is a rigid, proper, additive 6-ring (a locally minimal `Y` with
`c = 4 > δ`), which illustrates (J-2′).

---

## Part III — measurements (exact partition counts unless noted)

`[MEASURED earcover.py]` Every biconnected, triangle-free graph with minimum degree `≥ 2` and
`2m ≤ 3n − 4` on 9–13 vertices (from `geng -C -d2 -t -q n 0:⌊(3n−4)/2⌋`, nauty 2.9.3) was run. Its
𝒮-members are 35 / 304 / 879 / 9 030 / 32 177, matching (MC-83)'s count.
- **Every one has a chain in USABLE, A′ or C′-I.**
- Every C′-I witness `W_Y` is asserted rigid, with simple quotient, additive, and satisfying (H).
- At every C′-II chain, (J-3)(i) is asserted.

The chain-cell counts over all chains:

| `n` | C′-I | C′-II-tree | C′-II-cyclic | A′ | time |
|---|---|---|---|---|---|
| 9 | 0 | 3 | 0 | 0 | 0.2 s |
| 10 | 0 | 10 | 0 | 0 | 0.3 s |
| 11 | 52 | 58 | 0 | 0 | 0.8 s |
| 12 | 135 | 233 | 0 | 12 | 8 s |
| 13 | 937 | 1 676 | **6** (`δ = 3`) | 20 | 33 s |

`[MEASURED countlemma.py]` (J-6a) and (J-5) are asserted at:
- every 𝒮 member on 11–13 vertices whose chains all have `k = 1`: 54 / 1 370 / 1 919 members,
  297 chains with `δ ≥ 1`, 595 blobs;
- the eight `k = 1` necklaces: 101 chains, 431 blobs.

On ≤ 8 vertices there is no `k = 1` chain with hub ends and `(δ₂, δ) ∈ {(3,3), (3,4)}`
(`classes.py --exh 8`: 0). Track F's 53 and 16 split-off instances there have an end of degree 2,
so `G′` fails (H).

## What would change this

- A 𝒮-member with no chain in USABLE, A′ or C′-I. That would be an arithmetic error in (J-5) or
  (J-6a). `earcover.py` and `countlemma.py` assert against it.
- A C′-I witness that fails rigidity, simplicity or additivity (asserted).
- A `k = 1` chain in 𝒮, inside a proper additive rigid `W` with simple quotient, where `X₀(G)` falls
  short. That would refute (MC-68)(d), (MC-44), or the IH bookkeeping of (J-2).
- A Case II-tree instance whose generic chord point has dependent bridges, or all bridges meeting
  `n` at `δ = 4`. That would refute the folded-pentagon computation (`foldcheck.py`).
- A Case II-cyclic instance with a class-level stress at the generic chord point. That would refute
  (B-11) there and leave (J-10) open, without touching (J-6).

## What was re-derived, and what was taken on trust

- **Derived here:**
  - (J-1), (J-3), (J-5), (J-6a): pure counts;
  - (J-2)'s assembly;
  - (J-7): the reachable-conic argument, redone with a `z₁`-independent `ρ̄`;
  - (J-8): the flat point, the folded point and the pentagon;
  - (J-9)'s identification of `a′(z₀)`.
- **Re-derived from their sources:**
  - (MC-16), (MC-17), (MC-77), (MC-79)(ii)/(iii)/(v), and (MC-76)'s singleton optimality;
  - the equivalence "additivity ⟺ singletons optimal in `G/H`" in 𝒮.
- **Re-read and used as stated:**
  - (B-1), (B-2), the chord facts, and (B-4)(d);
  - (MC-44);
  - (F-10), (F-13), (F-16);
  - (MC-68)(d), including (b). This is the one load-bearing citation of the new route. I read its
    proof but did not re-derive (MC-68)(b)'s degeneration.
- **Taken on trust:**
  - JJ, everywhere flagged;
  - Track A's (A-11) behind (F-16);
  - the landed steps behind "usable".
- **Not used:** Theorem S (MC-80), (MC-69), (MC-70) (except as an alternative in (J-2′)), (MC-71),
  (MC-87), and Track C's `dim U = min(δ₂, 3)`, beyond `≥ 2`.

## Scripts

All are in this directory, run from the repository root at `PYTHONHASHSEED=0` with seed `20260924`.
Everything is exact except the mod-`2⁶¹ − 1` attainment screens, which are certificates.

| command | output | time |
|---|---|---|
| `python3 ringprobe.py` | `out_ringprobe.txt`: 15 built instances (Case II-tree, Case II-cyclic, Case I): chord point, class level, `ρ̄`, truth | 83 s |
| `python3 foldcheck.py` | `out_foldcheck.txt`: the folded point of (J-8) at the six Case II-tree instances | 0.7 s |
| `python3 cycprobe.py` | `out_cycprobe.txt`: the 6 Case II-cyclic chains on 13 vertices | 2.3 s |
| `python3 earcover.py --necklaces` | `out_earcover_necklaces.txt` | 20 s |
| `geng -C -d2 -t -q n 0:⌊(3n−4)/2⌋ \| python3 earcover.py --hunt - --full`, `n = 9..13` | `out_earcover_hunt.txt` | 0.2–33 s |
| `python3 countlemma.py --necklaces`; the same with `geng` input for `n = 11..13` | `out_countlemma.txt`, `out_countlemma_hunt.txt` | 8 s, < 1 min |
| `geng … 13 0:17 \| python3 findcyc.py` | `out_findcyc13.txt`: the Case II-cyclic chains on 13 vertices | < 1 min |
| `python3 j2check.py` | `out_j2check.txt`: (J-2)'s mechanism at `QsQsQ`, `QsQsQs`, `TsTsTs` | 1 s |
| `python3 classes.py --exh 8` | the census on ≤ 8 vertices: none | < 1 min |

`ringprobe.py` imports Track B's `chordprobe.py` from `../trackB`.
