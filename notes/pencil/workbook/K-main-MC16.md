## §(K-main) — Step MC16 — the structural half, and the coverage theorem (modulo Jackson–Jordán)

#### Step MC16 — the structural half, and the coverage theorem (modulo Jackson–Jordán)

*Worked 2026-09-24 by a read-only agent (W4-reopen P1, open direction 3; the third 2026-09-24
session's Track A), starting from the coordinator's observations (O1), (O2). Its §6 was written
after Step MC15 and the second reading of Steps MC12/MC14 had reported. The coordinator re-derived
(MC-75), (MC-87) (both cases) and (MC-80)'s choice of cores at the level of the written proofs.
**Two second readers re-derived this step on 2026-09-24, and neither found a gap.** The first
read (MC-75)–(MC-79) and (MC-82). It filled small steps in (MC-76), (MC-77), (MC-78) and
(MC-79)(i), (ii), and made three repairs, marked where they sit: (MC-79)(i)'s sketch, (MC-79)(vi)'s
citation, and (MC-82)(iii)'s missing cycles. It also repaired Step MC10's remark after (MC-26).
The second read (MC-80), (MC-87)–(MC-89) together with Step MC15's (MC-68), (MC-69) and (MC-71).
It confirmed each of them and made two wording repairs, to (MC-88) and (MC-89). It found
(MC-81)'s (β′) bullet false as worded (MC-121), which (MC-89) does not use. It also gave an
independent proof of (MC-87) by relative maximality, (MC-119) and (MC-120). **So the coverage
theorem (MC-89) stands, modulo Jackson–Jordán, in characteristic 0.** Driver
`w4/coverstruct.py` (new).*

**Verdict.**
- **Reduction to a sparse class.** A maximal `def₂`-rigid set has a simple quotient (MC-75), so
  every graph satisfying (H) with `def₂ > def₃` and some `def₂`-rigid subgraph is reached by
  CONTRACT at a `def₂`-rigid core. What is left is the class 𝒮: 2-connected, not a cycle or θ-graph,
  and `2e(X) ≤ 3|X| − 4` for every `|X| ≥ 2` (MC-76). There `def₂ > def₃` automatically, and there are
  `≥ 4` degree-2 vertices.
- **In 𝒮 the chain cells collapse** to two (MC-79): (c′), `k = 1` with `1 ≤ δ ≤ 4`; and (a′),
  `k = 2` with `a ∼ b` (then `δ = 1`). Every other chain is usable by a landed step.
- **Theorem S** (MC-80): every `G ∈ 𝒮` has a usable chain, or a proper rigid `W` with `G/G[W]` simple
  and `1 ≤ def₂(G[W]) < def₂(G)`. **Every such core is additive** (MC-87), so Step MC15's
  certificate-free CONTRACT (MC-71) applies there.
- **The coverage theorem** (MC-89), modulo Jackson–Jordán: every graph satisfying (H) is covered,
  so **(MC-10)(a) holds**: `X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)` for every finite
  simple connected `G` of minimum degree `≥ 2`. It uses no open ear cell and no per-graph picture
  certificate.
- **The lemma `δ₂ = 1 ⟹ δ ≤ 1`** holds for every simple graph and pair (MC-88). With (MC-44) and
  (MC-26) it closes (MC-51)(a) for `a ≁ b`.
- **The cells are genuinely forced.** Infinite families have no usable chain and are reached only by
  CONTRACT at a core with `def₂(H) > 0`: necklaces of 4-cycles (MC-83), whose smallest member
  `QsQsQ` on 14 vertices is the unique stuck 𝒮-graph on `≤ 14` vertices; and 4-cycle-free necklaces
  of `θ(2,3,4)` (MC-84).
- Both candidate gaps (MC-61) named for the structural half are closed (MC-82): Katoh–Tanigawa's
  Lemma-6.5 case is never an obstruction, and minimum degree `≥ 3` never needs a chain.

**Notation.**

- `s(X) := 3|X| − 4 − 2e(X)` and `s′(X) := s(X) + 1 = 3|X| − 3 − 2e(X)`. So `s′(X)` is the
  `def₂`-value of the one-part partition of `G[X]` against its singletons, and `s′({v}) = 0`.
- `c(Y) := 6(|Y| − 1) − 5e(Y)` is the `def₃` analogue. For a partition `P` of `G`,
  `val_D(P) = val_D(singletons) − Σ_{parts Z} c_D(Z)`, where `c₂ = s′` and `c₃ = c`. This identity
  is used throughout.
- **(S)** means `s(X) ≥ 0` for every `X ⊆ V` with `|X| ≥ 2`, that is, `2e(X) ≤ 3|X| − 4`.
  Equivalently, the doubled edge set is independent in the (3,4)-count matroid, which is how
  `coverstruct.py` tests it.
- **𝒮** is the class of `G` satisfying (H) that are 2-connected, are not a cycle or a θ-graph, and
  satisfy (S).
- **Rigid** always means `def₃`-rigid (`|W| ≥ 2`, `def₃(G[W]) = 0`), unless `def₂` is named.
  `P*(G)` is the partition of `V` into maximal rigid sets and singletons. `Γ̂(G) := G/P*(G)`.
- A **chain** is a maximal path `a − x₁ − ⋯ − x_k − b` of degree-2 vertices between hubs, with
  `G′ := G − {xᵢ}`. `δ` and `δ₂` are as in Step MC10 and Step MC11.
- A chain is **usable** if a landed step applies to it, modulo JJ:
  - `k ≥ 5`: (MC-20);
  - `k = 4`: (MC-24)/(MC-25);
  - `k = 3`: (MC-45);
  - `k = 2`: (MC-46) with `dim U ≥ 2`, or (MC-54) at `δ = 0` *(since 2026-09-26 the first
    alternative is (MC-176), Step MC13, at `a ≁ b`, `δ₂ ≥ 2`)*;
  - `k = 1`: (MC-54) at `δ = 0` with `dim U ≥ 2`, or SPLITOFF (MC-31) at `δ ≥ 5`.
- **JJ** means Jackson–Jordán's equality `ℓ₀ = 3 + def₂` at the named simple graph: in
  characteristic 0 it is their theorem, and beyond that it is (MC-33).

**1. Reduction to 𝒮.**

> **(MC-75)** `[PROVED]` *(the coordinator's (O1), confirmed; and its `def₃` twin)*
> **(i)** Let `W` be `def₂`-rigid and `u ∉ W` have `≥ 2` neighbours in `W`. Then `W ∪ {u}` is
> `def₂`-rigid. The same holds with `def₃` in place of `def₂`.
> **(ii)** Two rigid sets sharing a vertex have rigid union, for `def₂` and for `def₃`. So the
> maximal ones are pairwise disjoint.
> **(iii)** Hence, if `def₂(G) > 0`, every maximal `def₂`-rigid set `W` is proper and `G/G[W]` is
> simple. It is `def₃`-rigid with `|W| ≥ 3`, so it is a proper rigid set, and (MC-59)(d) applies
> (JJ at `H` and `G/H`, (MC-59)(c3)). Likewise, if `def₃(G) > 0`, every maximal rigid set has a simple
> quotient.

*Proof.*
- (i) Let `P` partition `W ∪ u`. If `u` is alone, `val_D(P) ≤ val_D(P|_W) + D − (D−1)·2 < 0`,
  with `D = 3` or `6`. If `u` shares a part with a vertex of `W`, then `|P| = |P|_W|` and
  `d(P) ≥ d(P|_W)`, so `val(P) ≤ val(P|_W) ≤ 0`.
- (ii) This is the union lemma inside (MC-14)'s proof, re-derived. That proof never uses `D = 3`:
  - put `P₁ = P|_{V₁}`;
  - let `P₂′` be `P|_{V₂}` with every part meeting `V₁` merged into one;
  - an `H₂`-edge crossing `P₂′` has an endpoint outside `V₁`, so it is not an `H₁`-edge;
  - hence `val(P) ≤ val(P₁) + val(P₂′) ≤ 0`.
- (iii) `def₂(G) > 0` makes `V` itself non-rigid, and a maximal `W` then has no outside vertex
  with 2 neighbours in it, by (i). `def₂`-rigid graphs are connected (split into components: the
  value is `3(c − 1) > 0`), so (MC-5)(i) makes them `def₃`-rigid. In a simple graph `|W| ≥ 3`. The
  same argument works for `def₃`. ∎

Consistency: (MC-40)'s *Coverage* line (exh7 members lacking a maximal `W` with simple quotient all
have `def₂ = 0`) is consistent with (i)–(iii). It is not literally the same statement, since
"maximal" there is among `def₃`-rigid sets.

> **(MC-76)** `[PROVED]` *((O2), confirmed and sharpened)* For `G` satisfying (H) the following are
> equivalent:
> - `G` has no `def₂`-rigid subgraph at all, `G` included;
> - (S) holds;
> - the all-singletons partition is the unique `def₂`-maximizer and `def₂(G) = 3(|V| − 1) − 2|E| ≥ 1`.
>
> Then `G` is triangle-free (and `K_{2,3}`-free), `Σ_v (3 − deg v) = def₂(G) + 3 ≥ 4`, so `G` has
> at least 4 degree-2 vertices, and **`def₂(G) > def₃(G)` automatically**. "No *proper*
> `def₂`-rigid subgraph" is equivalent to (S) on `X ⊊ V` alone. That is the coordinator's form; it
> allows `def₂(G) = 0`, where FLAT applies.

*Proof.* Parts of maximizing partitions are rigid ((MC-13)(b)'s proof, re-derived). So a graph with
no rigid subgraph is maximized only by its singletons, and `def₂ = s′(V) ≥ 1`. Applied to every
`G[X]`, this gives (S).

Conversely, assume (S). Refining any part `Z` with `|Z| ≥ 2` into singletons raises the value by
`s′(Z) ≥ 1`, so the singletons are the unique maximizer on every `G[X]`.

For the "proper" form, if `2e(X) ≥ 3|X| − 3` with `X ⊊ V`, take `Y ⊆ X` minimal with this
property. Its proper subsets satisfy (S), so `def₂(G[Y]) = max(0, s′(Y)) = 0`.

*The automatic gap.* We have `val₃(P) = val₂(P) + 3(|P| − 1 − d(P))`, and `d(P) ≥ |P| − 1` since
`G` is connected.
- At the singletons, `val₃ = def₂ + 3(|V| − 1 − |E|) < def₂`, because `|E| ≥ |V|` by the minimum
  degree.
- At any other `P`, `val₂(P) < def₂` by uniqueness.

∎

**The reduction.** Let `G` satisfy (H).
- Not 2-connected and not a cycle: CUT or BRIDGE (MC-55)(ii).
- A cycle: BASE.
- `def₂ = def₃`: FLAT (JJ at `G`).
- `def₂ > def₃`, so `def₂ > 0`:
  - if `G` has a `def₂`-rigid subgraph, CONTRACT at a maximal one (MC-75)(iii), consuming `H` (FLAT)
    and `G/H`, both smaller;
  - otherwise (S) holds (MC-76). A θ-graph is THETA, and everything else is in 𝒮.

**2. The chain calculus in 𝒮.**

> **(MC-77)** `[PROVED]` *(maximal rigid sets; any graph)*
> - Distinct maximal rigid sets are disjoint and joined by `≤ 1` edge.
> - A vertex outside a maximal rigid set `R` has `≤ 1` neighbour in `R`.
> - So `Γ̂(G)` is simple, and a proper maximal rigid set has a simple quotient.
> - `Γ̂(G)` is **rigid-free**: `c(Y) ≥ 1` for every `Y ⊆ V(Γ̂)` with `|Y| ≥ 2`. Hence it has girth
>   `≥ 7` and `3(|Y| − 1) − 2e(Y) ≥ (3(|Y| − 1) + 2)/5 > 0`.
> - `P*(G)` is a maximizing partition: `def₃(G) = c(V(Γ̂))` when `|Γ̂| ≥ 2`.

*Proof.*
- Two maximal rigid sets joined by `≥ 2` edges have rigid union: if no part of a partition meets
  both, the value is at most the two values plus `6 − 10`; otherwise it is at most their sum. A
  singleton with 2 edges into `R` is (MC-75)(i).
- A rigid `Y ⊆ V(Γ̂)` lifts to a rigid union of the sets it contains: in a partition of the lift,
  merge the parts meeting each `R ∈ Y` (value non-decreasing), which leaves a partition of `Γ̂[Y]`.
  That would contradict maximality, so `Γ̂` is rigid-free.
- The bound: `5e ≤ 6(|Y| − 1) − 1` gives `2e ≤ (12(|Y| − 1) − 2)/5`.
- Any maximizing partition has rigid parts. Merging the parts inside each maximal `R` does not
  lower the value, and gives `P*`. ∎

> **(MC-78)** `[PROVED]` *(Lemma T: tight sets)* Let `Γ₀` satisfy (S), and let `X ⊆ V(Γ₀)` with
> `|X| ≥ 2` be **tight**, `s(X) = 0`. Then `X` is a single edge, or `X` lies inside one maximal
> rigid set of `Γ₀`.

*Proof.*
- Let `Q = P*(Γ₀)|_X`, with parts `X_i`. Then
  `1 = s′(X) = Σ s′(X_i) + [3(|Q| − 1) − 2d_X(Q)]`, with every `s′(X_i) ≥ 0`, and `≥ 1` when
  `|X_i| ≥ 2`, by (S).
- If `|Q| ≥ 2`, then `d_X(Q) ≤ e_{Γ̂}(Y)` for the set `Y` of maximal rigid sets that `X` meets, so
  the bracket is at least 1 by (MC-77). Hence every `X_i` is a singleton and
  `e_{Γ̂}(Y) = (3|Y| − 4)/2`.
- With `5e ≤ 6|Y| − 7` this forces `|Y| ≤ 2`, so `X` is an edge. If `|Q| = 1`, then `X` lies in
  one maximal rigid set. ∎

> **(MC-79)** *(chains in 𝒮)* Let `G ∈ 𝒮` and `C = a − x₁ − ⋯ − x_k − b` a chain (so `a ≠ b`,
> `G′` satisfies (H)).
> **(i)** `[PROVED]` `δ = 0` iff `a, b` lie in a common rigid subgraph of `G′`. If not, then
> `δ = min_Y c(Y)` over `Y ⊆ V(Γ̂(G′))` containing `[a]`, `[b]`. (`δ ≤ 6`, via `Y = {[a],[b]}`.)
> **(ii)** `[PROVED]` `k = 1`: `a ≁ b` and `δ₂ ≥ 2`.
> - If `x` lies in **no** rigid subgraph of `G`, then `δ ≥ 5`.
> - If it lies in one, then `δ ≤ 4`, and in fact `δ = def₃(G[R] − x)` for the maximal rigid
>   `R ∋ x`.
>
> **(iii)** `[PROVED]` `k = 2`: `δ₂ = 1` implies `a ∼ b` or `δ = 0`; and `a ∼ b` implies `δ ≤ 1`.
> **(iv)** `[PROVED]` *(locality)* If the chain lies in a maximal rigid set `R` of `G`, then `δ`,
> whether `δ₂ = 1`, and whether `a ∼ b` are the same computed in `G` or in `G[R]`. In the other case (no
> rigid set contains the chain), `k = 1` gives (ii) and `k = 2` gives `a ≁ b` (else the 4-cycle
> `C ∪ {a, b}` is rigid).
> **(v)** `[PROVED-MOD]` *((MC-33); what is usable)* Every chain with `k ≥ 3` is usable. A `k = 2`
> chain is usable unless it is in **(a′)**: `a ∼ b` and `δ = 1`. A `k = 1` chain is usable unless
> it is in **(c′)**: `1 ≤ δ ≤ 4`. JJ enters at `G′ + ab` (for `dim U ≥ 2`) and at `G″ = G′ + ab`
> (SPLITOFF).
> **(vi)** `[PROVED-MOD]` *((MC-33))* In 𝒮:
> - (MC-51)(b) (orbit (iv), `U = 0`) never occurs;
> - `k = 1` with `dim U ≤ 1` never occurs;
> - (c′) is in orbit (i) with `dim U ≥ 2`;
> - (a′) is in orbit (iii) with `dim U = 1`.

*Proof.*
- **(i)** Merge the maximal rigid sets as in (MC-77). *(Repaired by the second reader: "a part of a
  maximizing partition of `G′/ab` is rigid" holds only in the `δ = 0` direction; in general, coarsen
  the constrained maximizer to `P*(G′)`, which does not lower its value.)* Conversely a common rigid
  subgraph can be merged in without loss. The value
  identity `val = val(sing) − Σ c(parts)` then gives the formula, with parts not containing both
  contributing `≥ 0`.
- **(ii)**
  - *`δ₂ ≥ 2`.* For `X ∋ a, b` in `G′`, `s(X ∪ x) = s(X) − 1 ≥ 0`, so `δ₂ = 1 + min s(X) ≥ 2`.
    Triangle-freeness gives `a ≁ b`.
  - *No rigid subgraph contains `x`.* Then `x` is a singleton of `P*(G)`, and
    `P*(G′) = P*(G) − x` (a rigid set of `G′` is rigid in `G`). For `Y ∋ [a], [b]` in
    `Γ̂(G) − x`, `c(Y ∪ x) = c(Y) + 6 − 10 ≥ 1`, so `c(Y) ≥ 5`.
  - *Some rigid `R ∋ x`.* Then `a, b ∈ R`, since a rigid set has minimum degree `≥ 2` in itself.
    Let `Y` be the set of `Γ̂(G′)`-vertices meeting `R − x`. Rigidity of `G[R]`, applied to its
    partition `{Z ∩ R} ∪ {x}`, gives `6|Y| − 5d − 10 ≤ 0` with `d ≤ e(Y)`. So
    `δ ≤ c(Y) ≤ 4`.
  - *The formula.* It is (MC-17)'s count (valid for any graph) inside `G[R]`, where
    `def₃(G[R]) = 0 = def₃(G[R] − x) − min(δ_R, 4)` with `δ_R ≤ def₃(G[R] − x)`. Then (iv).
- **(iii)** Apply (MC-78) to `Γ₀ = G′`, which satisfies (S). A tight `X ∋ a, b` is the edge `ab`, or
  lies in a maximal rigid set of `G′`, and then `δ = 0` by (i). If `a ∼ b`, then
  `c({[a],[b]}) = 6 − 5 = 1`.
- **(iv)**
  - *Why `P*` is preserved.* A rigid set of `G′` is rigid in `G`, so it lies in one maximal rigid
    set of `G`, which is `R` if it meets `R − C`. Hence `P*(G′) = (P*(G) − {R}) ∪ P*(G[R] − C)`.
  - *Why the outside cannot lower `δ`.* For `Y = Y₁ ∪ Y₂`, with `Y₁` inside `R` and `Y₂` outside,
    `c(Y) = c(Y₁) + [6|Y₂| − 5e(Y₂) − 5e(Y₁, Y₂)] ≥ c(Y₁) + c_{Γ̂(G)}(Y₂ ∪ [R]) ≥ c(Y₁) + 1`,
    since `e(Y₁, Y₂) ≤ e(Y₂, [R])`. So the minimum in (i) is attained inside `R`.
  - *`δ₂`.* By (MC-78) in `G`, a tight set containing `a, b` is inside `R` or is the edge `ab`.
- **(v)** `k ≥ 3` is (MC-20), (MC-24)/(MC-25) and (MC-45), as landed. *Flag:* at `k = 4` with
  `a ∼ b` (a 6-cycle, allowed in 𝒮), this rests on Step MC14's reading that (MC-22)–(MC-25) need no
  `a ≁ b`, confirmed by the 2026-09-24 second reading. `k = 2`, `a ≁ b`:
  - by (iii), `δ = 0` (MC-54) or `δ₂ ≥ 2`;
  - `δ₂ ≥ 2` gives `dim U ≥ 2` by (MC-48)(ii)'s argument, re-derived here in general:
    `def₂(G′ + ab) = def₂(G′) − min(δ₂, 2) = def₂(G′) − 2`; with JJ at the simple `G′ + ab` and
    (MC-4)(b) at `G′`, the functionals `φ₁`, `φ₂` are independent on `L_{G′}` and factor through
    `U`;
  - `dim U ≥ 2` excludes orbits (iii) and (iv), so (MC-46) applies. *(Repaired 2026-09-26, ORBIT
    recon: the same independence gives orbit (i) itself. Both functionals are nonzero at generic
    `z`, so `p_b ∉ π_a` and `p_a ∉ π_b`, as (MC-48)(ii) states; orbit (ii) never reaches this
    cell. On (MC-89)'s route the cell's step is now (MC-176) (Step MC13), which uses orbit (i) and
    not (MC-46).)*

  `k = 2`, `a ∼ b`: `δ ∈ {0, 1}` by (iii), and `δ = 0` is (MC-54). `k = 1`: `δ₂ ≥ 2` gives
  `dim U ≥ 2` as above, so `δ = 0` is (MC-54) and `δ ≥ 5` is SPLITOFF (`a ≁ b`).
- **(vi)** `δ₂ ≥ 1` always in 𝒮: `s ≥ 0` gives `δ₂ = 1 + min s(X) ≥ 1`. `U = 0` would force
  `δ₂ = 0`, by (MC-62)'s `dim U ≥ min(δ₂, 3)` (JJ at `G′ + ab + x`). *(Repaired by the second reader:
  this first cited the remark after (MC-26), whose argument as written does not give it.)* For
  (a′): `a ∼ b` puts `π_a ∋ p_b` and `π_b ∋ p_a`, so the orbit is (iii) or (iv), and `dim U = 1` by
  the same count at `G′_{ab}`, `def₂(G′_{ab}) = def₂(G′) − min(δ₂, 1)` (JJ at `G′_{ab}` only). ∎

`coverstruct.py --exh 8` and `--witness 16 --smax 4 --cores K4,dC4` assert (MC-77), (MC-78) and
(MC-79)(ii),(iii) at every member tested:
- exh8's 16 𝒮-members;
- 1 061 𝒮-members that subdivide `K₄` or the doubled `C₄` with `≤ 4` vertices per edge, on
  `≤ 16` vertices, 180 of them non-rigid.

These are checks of proved identities at witnesses, not evidence for them.

**3. The structural theorem.**

> **(MC-80)** `[PROVED]` *(Theorem S)* Let `G ∈ 𝒮`. Then `G` has a chain outside the cells (c′) and
> (a′), or `G` has a proper rigid set `W` with `G/G[W]` simple and `1 ≤ def₂(G[W]) < def₂(G)`.
> More precisely, suppose every chain is in (c′) or (a′). Then:
> - **`G` non-rigid:** every chain lies in a proper maximal rigid set `R` of `G`, and any such `R`
>   serves as `W`;
> - **`G` rigid:** for some chain `C`, `G − C` has a non-singleton maximal rigid set `B ≠ V(G − C)`,
>   and `B` serves as `W`.

*Proof.* `G` has `≥ 4` degree-2 vertices (MC-76) and hubs, so it has chains. Assume every chain is
blocked; then every `k ≤ 2`.

*Non-rigid.*
- A blocked `k = 1` chain has `δ ≤ 4`, so it lies in a rigid set (MC-79)(ii).
- A blocked `k = 2` chain has `a ∼ b`, so it lies in the rigid 4-cycle `C ∪ {a, b}`.
- Either way it lies in a maximal rigid `R`. `R ≠ V`, since `G` is non-rigid, so `G/G[R]` is
  simple (MC-77).
- `def₂(G) = s′(V) = Σ_{R′ ∈ P*} s′(R′) + [3(|Γ̂| − 1) − 2e(Γ̂)] ≥ s′(R) + 1 = def₂(G[R]) + 1`,
  by (MC-77) with `|Γ̂| ≥ 2`.

*Rigid.* Here a chain `C` with `k ≤ 4` has `δ = def₃(G − C)`: from
`0 = def₃(G) = f − min(δ, 5 − k)` and `δ ≤ f`. So blocked means `G − C` is not rigid.
- *Some chain `C` has `k = 2`.* It has `a ∼ b`. Take another chain `C′`: one exists, since there
  are `≥ 4` degree-2 vertices and `k ≤ 2`. The 4-cycle on `C ∪ {a, b}` avoids `C′` (`a`, `b` are
  hubs). So it lies in a non-singleton maximal rigid set `B` of `G − C′`, and `B ≠ V(G − C′)`.
- *All chains have `k = 1`.* Then **`5|E| ≥ 6|V|`**. With `d` degree-2 vertices, each with two hub
  neighbours, and hubs `H`:
  - `Σ_H deg ≥ 2d` and `Σ_H deg ≥ 3|H|`;
  - so `5|E| − 6|V| = (5/2)Σ_H deg − d − 6|H| ≥ 0`.

  So for any chain `x`, `c(G − x) = 6|V| − 5|E| − 2 ≤ −2`, while `def₃(G − x) = δ ≥ 1`. Hence
  `P*(G − x)` is neither the singletons nor `{V(G − x)}`, and it has a proper non-singleton part `B`.
- *`B` has a simple quotient in `G`.* An outside `u ∉ C` with 2 neighbours in `B` would enlarge `B`
  inside `G − C` (MC-75)(i). A chain vertex has `≤ 1` neighbour in `B`, since `[a] ≠ [b]` when
  `δ ≥ 1`.
- *`def₂`.* Take the partition of `G` into the parts of `P*(G − C)` and the chain vertices:
  `def₂(G) = Σ_{blobs} s′ + [3(|Γ| − 1) − 2e(Γ)] + k − 2`, with `Γ = Γ̂(G − C)`.
  - The bracket is `≥ 1` by (MC-77). For `k = 2` this gives `def₂(G) > def₂(G[B])`.
  - For `k = 1`, equality would need the bracket `= 1` and every other part a singleton. Then
    `|Γ| = 2` by (MC-78)'s count, so `G − x = B` plus one pendant singleton. That singleton would be
    a degree-2 neighbour of `x`, contradicting `k = 1`.

∎

> **(MC-81)** `[PROVED-MOD]` *((MC-33); the coverage reduction)* Assume, for every `G ∈ 𝒮` all of
> whose chains lie in (c′) ∪ (a′), **one** of the following:
> - **(α)** the ear step holds at one of its chains;
> - **(β)** (MC-39)'s (i) and (ii) hold at one of the cores `W` of (MC-80).
>
> Then **every graph satisfying (H) is covered**, so (MC-10)(a) holds. In particular, either of
> the following suffices:
> - **(α′)** close the two cells (c′) and (a′);
> - **(β′)** prove (i)/(ii) at every core of (MC-80). *(Repaired by the second reader. As first
>   written, "at every proper rigid `W` with simple quotient and `1 ≤ def₂(G[W]) < def₂(G)`, in 𝒮", it
>   is false: (MC-121). The inequality is not needed by (MC-71).)*

*Proof.* By strong induction on `|V|`, using §1's reduction, (MC-79)(v) and (MC-80).
- Every step consumes smaller graphs satisfying (H) (MC-55)(i).
- CONTRACT at `W` consumes `H = G[W]` and `G/H`, both covered by induction.
- (MC-39)'s side conditions hold: `G` is 2EC, and `G/H` is simple.
- (MC-56) turns coverage into attainment. ∎

JJ is used at:
- `G` (FLAT);
- `H`, `G/H` ((MC-75)(iii) via (MC-59)(d), sharpened by (MC-59)(c3));
- `G′ + ab` (`dim U ≥ 2`, and SPLITOFF's `G″`).

The steps used were second-read on 2026-09-24 ((MC-37)–(MC-39), (MC-52)–(MC-55), the `k = 4` / `a ∼ b`
reading); Step MC15 and this step have not been.

> **(MC-82)** `[PROVED-MOD]` *((MC-33); what this closes)*
> **(i)** *(MC-41)(∂3), Katoh–Tanigawa's Lemma-6.5 case, is never an obstruction.* Let `G`
> satisfy (H), have a proper rigid set, and have none with a simple quotient. Then `G` has a
> usable step without CONTRACT.
> **(ii)** *Minimum degree `≥ 3` with `def₂ > def₃` never needs a chain:* such a `G` has a
> `def₂`-rigid subgraph (MC-76), so (MC-75)(iii) applies. Together with (i), this closes both
> candidate gaps named in (MC-61)'s structural half.
> **(iii)** *hK's habitat needs no open cell at its first step.* Every 2-connected habitat member
> other than a cycle or a θ-graph has a usable chain *(cycles added by the second reader: `C_n`,
> `n ≥ 5`, lies in the habitat, has no chain, and is BASE; (MC-89) does not use this item)*:
> - if it is non-rigid, every chain is usable;
> - if it is rigid, it has a chain with `k ≥ 2`, and every such chain is usable.
>
> This sharpens (MC-51)'s last sentence ("on hK's habitat only (c) with `δ ≤ 4` remains"): (c) is
> never *needed* there. The recursion still leaves the habitat, so this is not coverage of the
> habitat.

*Proof.*
- **(i)** `def₂ = def₃` is FLAT. Otherwise a `def₂`-rigid subgraph would give a simple quotient
  (MC-75)(iii), so `G ∈ 𝒮` (or CUT/BRIDGE/BASE/THETA). If `G` is non-rigid, its maximal rigid sets
  have simple quotients (MC-77). So `G` is rigid, and (MC-80) gives a chain outside the cells, since a
  core `W` is excluded.
- **(iii)**
  - The habitat has no `def₂`-rigid subgraph (MC-15)(i), so (S) holds.
  - *Non-rigid.* `G` has no rigid subgraph at all, so `k = 1` gives `δ ≥ 5` (MC-79)(ii). At `k = 2`,
    `a ≁ b`, since a 4-cycle would be a proper rigid subgraph.
  - *Rigid, all chains `k = 1`.* For a chain `x`, `G − x` has no rigid subgraph (all proper), so
    `def₃(G − x) = c(G − x) ≥ 1`. But `5|E| ≥ 6|V|` gives `c(G − x) ≤ −2`, a contradiction.
  - *Chains with `k ≥ 2`.* These are usable: `a ≁ b` at `k = 2`.
  - This matches (MC-58): every habitat member's first covering step is THETA or `k ≥ 2`. ∎

**4. The cells are forced: explicit families.**

A **unit cycle** has `u` units in cyclic order, joined by single edges (out of unit `i` into unit
`i+1`). The units are of three kinds:
- `s`, a single vertex;
- `Q`, a 4-cycle `a − p − c − r − a` entered at `a` and left at `c` (opposite corners);
- `A`, a 4-cycle `a − p − q − b − a` entered at `a` and left at `b` (adjacent corners).

> **(MC-83)** `[PROVED]` *(4-cycle necklaces with no usable chain)* Every unit cycle with `u ≥ 4`
> built from these units, with at least **two** 4-cycle beads, is in 𝒮. (With one bead it is a
> θ-graph.) The following have **no usable
> chain**:
> - **`Qᵘ`, `u ≥ 5`:** every chain is in (c′), with `δ = min(u − 4, 2)`;
> - **`Aᵘ`, `u ≥ 6`:** every chain is in (a′);
> - **`QsQsQ`** (`n = 14`, `m = 17`, `def₂ = 5`, `def₃ = 0`): (c′) with `δ = 1` (bead chains) and
>   `δ = 3` (singles).
>
> Also `AsAsAs` (`n = 15`): (a′) and (c′) at `δ = 4`. In each, a bead is a CONTRACT candidate
> with `def₂(H) = 1`.
> `[MEASURED]` *(geng + `coverstruct.py --hunt`, exhaustive)* **No 𝒮 graph on `≤ 13` vertices lacks a
> usable chain, and on 14 vertices exactly one does, `QsQsQ`.** The candidates were every
> biconnected, triangle-free graph with minimum degree `≥ 2` and `2m ≤ 3n − 4`, which contains 𝒮;
> 411 045 of the 736 012 at `n = 14` are in 𝒮.

*Proof.*
- *(S).* For `|X| ≥ 2`, `s′(X) = Σ_units s′(X ∩ U) + [3(p − 1) − 2d]`. Here `p` is the number of
  units met and `d` the number of joining edges inside `X`. Subsets of a 4-cycle of size `≥ 2` have
  `s′ ≥ 1`.
  - If `d ≤ p − 1`, the bracket is `≥ p − 1`. That is `≥ 1` if `p ≥ 2`, and for `p = 1` the set
    lies in one bead.
  - If `d = p = u`, the bracket is `u − 3 ≥ 1`.

  The graph is triangle-free and 2-connected. With two beads it has at least 4 hubs, so it is
  not a cycle or a θ-graph.
- *`δ` of a `Q`-bead chain `p`.* The units are rigid. Replacing the bead by the path `a − r − c`
  gives a quotient cycle of length `u + 2`, so `def₃(G − p) = max(0, u − 4)`. Merging `a` with `c`
  makes `{[ac], r}` rigid (a double edge), with quotient cycle `C_u`. So `δ = min(u − 4, 2)`, since
  `C_L` is rigid iff `L ≤ 6`. For `u ≥ 7` this is also (MC-79)(iv) inside the bead:
  `δ = def₃(P₃) − def₃(K₂ with a double edge) = 2`.
- *`δ` of an `A`-bead chain `p q`.* `a ∼ b`. Quotient cycles of length `u + 1` and `u` give
  `δ = min(u − 5, 1)`, which is 1 for `u ≥ 6`.
- *A single between two beads.* `G − s` has a path of `u − 1` units, `def₃ = u − 2`. Merging its
  ends joins the two end beads, leaving a cycle of `u − 2` units. So `δ = min(u − 2, 6)`, which is
  `3` at `u = 5` and `4` at `u = 6`.
- *No other landed step applies.*
  - CUT, BRIDGE, BASE and THETA are excluded by the shape.
  - FLAT is excluded because `def₂ > def₃` (MC-76).
  - O1-CONTRACT is excluded because (S) holds.
  - SPLITOFF and EAR-`δ0` are excluded because `1 ≤ δ ≤ 4`.
  - (MC-46) is excluded because `dim U = 1` at `a ∼ b`.
  - (MC-47)(i) is excluded because `δ₂ = 1 ≠ 0`.

  ∎

*Witness runs* (`coverstruct.py --necklaces`, exact):
- `QsQsQ`, `QQQQs`, `Q⁵`, `QsQsQs`, `Q⁶`, `Q⁷`, `AsAsAs`, `A⁶`, `A⁷`: 0 usable chains each;
- controls `QsQs`: 4 of 6 usable; `A⁵`: 5 of 5 usable (`δ = 0`);
- at the first bead of every row: rigid, `G/H` simple, `def₂(H) < def₂(G)`, and additivity (MC-87)
  asserted: `QsQsQ` `5 = 1 + 4`, `AsAsAs` `6 = 1 + 5`, `Q⁵` `7 = 1 + 6`, `Q⁷` `11 = 1 + 10`, `A⁷`
  `11 = 1 + 10`.

The landed driver agrees (`PYTHONHASHSEED=0`, repo root; `QsQsQ` is
`x14_1295972027609334376453636096`, `AsAsAs` is `x15_10854957034205748643466139680801`):
- `x0arms.py --tree x14_1295972027609334376453636096 --ear23 antecedent --contract off` gives
  **UNCOVERED**, with all 8 chains in "(MC-51)(c)", orbit (i), `dim U` 2 or 3 (that is,
  `min(δ₂, 3)`);
- with the default `--contract cert` it is covered by CONTRACT at a 4-cycle bead, certified at one
  exact picture;
- the same for `AsAsAs` (`--depth 0`, with `--contract off` and `--contract cert`).

> **(MC-84)** `[REFUTED]` *(witnesses `TsTsTs`, `T⁶`: the natural sharpening "every graph of 𝒮 with no
> usable chain contains a 4-cycle", which would have reduced (β′) to 4-cycle cores, is false)*
> Let `T` be `θ(2,3,4)` with hubs `h, h′` and paths `h − y − h′`, `h − t₁ − w − h′`,
> `h − v − t₂ − v′ − h′`, entered at `t₁` and left at `t₂` (graph6 `G?`e`o`, `t₁ = 0`, `t₂ = 5`).
> Then `Tᵘ` (`u ≥ 6`) and `TsTsTs` (`n = 27`, `m = 33`, `def₂ = 12`, `def₃ = 0`) are 4-cycle-free
> members of 𝒮 with no usable chain. Every chain is in (c′), with `δ ∈ {1, 2}`, plus `δ = 4` at
> the singles.
> `[CONSTRUCTED]` *(`coverstruct.py --necklaces`)* The chain data are exact, constructed at
> `TsTsTs`, `T⁶`, `T⁷` (for `u ≥ 7` the blocking is (MC-79)(iv) locality inside the bead):
> `TsTsTs` 0 of 15 chains usable (6 at `δ = 1`, 6 at `δ = 2`, 3 at `δ = 4`, all `δ₂ = 3`); `T⁶`
> (`n = 48`) 0 of 24; `T⁷` (`n = 56`, `def₃ = 1`) 0 of 28; no 4-cycle, asserted; the bead is additive,
> `12 = 3 + 9`, `21 = 3 + 18`, `25 = 3 + 22`. `x0arms.py --tree <TsTsTs> --ear23 antecedent
> --contract off --depth 0` reports UNCOVERED; with `--depth 1` and the default `--contract cert` it
> is covered by CONTRACT at a `θ(2,3,4)` bead (`def₂(H) = 3`). (`TsTsTs`'s canonical name is printed
> by `--necklaces`.)

*How it was found.* `coverstruct.py --beads` searched girth-`≥ 5` rigid (S)-graphs for "internally
stuck" framings. A framing is a set `T` of attachment vertices such that every other degree-2
vertex `y` has `B − y` non-rigid and no non-attached degree-2 neighbour. Framings with 2
attachments exist from `n = 8` on:
- counts by the least number of attachments, per `n`: `{2: 2, 3: 1, 4: 1}` at `n = 8`, up to
  `{2: 14, 3: 175, …}` at `n = 13`;
- by (MC-79)(iv) and (MC-77), such a bead in a unit cycle with `u ≥ 7` has its chains blocked exactly
  as inside the bead;
- this is a sufficient construction, not a classification.

The `geng` hunts found no stuck 4-cycle-free 𝒮-graph with girth `≥ 5` on 14–16 vertices, nor a
subcubic one on 17–18 vertices (populations and counts in the driver table; re-run at landing). They are consistent: the smallest one found has 27. So the cores in
(β′) include 5-cycles and θ-graphs, not only 4-cycles.

**5. The cell (a′).**

> **(MC-85)** `[PROVED]` *(cell (a′) is one relative-dof statement; the cell is closed by (MC-105), Step
> MC17)* Under the strong induction, at
> a (a′) chain (`k = 2`, `a ∼ b`, `δ = 1`, orbit (iii)), `X₀(G)` attains **iff `r = 1`** at
> `X₀(G′)`'s generic point. Equivalently, the hinge `ab` is not locked: some motion of `G′` has
> `X_a ≠ X_b`. Equivalently again, the welded framework on `G′/ab` attains `6 + def₃(G′/ab)`.

*Proof.*
- The (MC-22) hypotheses hold: dominance (MC-18)(a) at `k = 2`, and `λ = 3` (MC-19)(b) for any
  flag pair.
- With `δ = 1`: (R₂) is `r ≥ 1`, and `r ≤ δ = 1` (MC-16).
- (P₂) at `r = 1` holds for every `ρ` in orbits (i)–(iii) at `k = 2` by (MC-26): only orbit (iv)
  is excepted. At `r = 0` it holds trivially.
- `a ∼ b` gives `ρ ⊆ K·C_ab`. The last form is (MC-16)'s
  `r = dim M_{G′} − dim M_weld` with `dim M_weld ≥ 6 + g = 6 + f − 1`. ∎

(MC-44)'s chord gadget is unavailable at `a ∼ b`. `G′/ab` is simple, satisfies (H) and is smaller,
but the welded framework is not a pencil framework of it. This is the natural next target for
(a′).

> **(MC-86)** `[MOOT]` *(successor (MC-68): this track's own sketch that (MC-39)(i) is additivity mod
> JJ; Step MC15 proved it independently as (MC-68), with JJ at `H` and `G/H` only)* The
> sketch went through `F(G ∪ K_W)` and JJ at `G ∪ K_W`. Its "rigid case: not proved" line is now
> (MC-87).

**6. The coverage theorem.**

*Added after Step MC15 and the second reading reported. The author read (MC-67)–(MC-71) and
re-derived (MC-68)(b), (d) and (MC-69)(b)'s inequality chain, but not (MC-69)(a)'s exact row
identity, which `kerm0.py` asserts at 287 instances; its row reading agrees with the second
reader's independent reading of `M₀`'s five row types (after (MC-37)'s proof).*

> **(MC-87)** `[PROVED]` *(additivity at the Theorem-S cores)*
> **(i)** Let `G` satisfy (S) and let `W ⊊ V` have `G/G[W]` simple. Then
> `def₂(G) = def₂(G[W]) + def₂(G/G[W])` **iff `s(X) ≥ s(W)` for every `X ⊇ W`**.
> **(ii)** Every core of (MC-80) satisfies this. That covers:
> - a proper maximal rigid set of a non-rigid `G ∈ 𝒮`;
> - a non-singleton maximal rigid set `B ≠ V(G − C)` of `G − C`, for a chain `C` with
>   `G − C` non-rigid, in a rigid `G ∈ 𝒮`.
>
> So (MC-71) applies at every such core, modulo JJ at `G[W]` and `G/G[W]`.

*Proof.*

(i) By (MC-76), `def₂(G) = s′(V)` and `def₂(H) = s′(W)`, and the singleton value of `G/H` is
`s′(V) − s′(W)`. For a partition `P` of `G/H`, `val(P) = val(singletons) − Σ_{Z∈P} s′_{G/H}(Z)`.
- For `Z ∌ v*`, `s′_{G/H}(Z) = s′_G(Z) ≥ 0` by (S).
- For `Z ∋ v*`, put `Z̃ := (Z − v*) ∪ W`. Simplicity makes the boundary edges biject, so
  `s′_{G/H}(Z) = s′_G(Z̃) − s′_G(W)`.

So `def₂(G/H) = def₂(G) − def₂(H)` iff no `Z` has negative `s′_{G/H}`, iff `s′(Z̃) ≥ s′(W)` for all
`Z̃ ⊇ W`. (Take `P = {Z} ∪` singletons for "only if".)

(ii) Both cases use the same shape of bound. Let `P` be a partition of `V` with `W ∈ P`, and let `X ⊇ W`
meet the parts `Y ⊆ P`. Then

  `s′(X) = Σ_{Z ∈ Y} s′(X ∩ Z) + [3(|Y| − 1) − 2d_X(Y)] ≥ s′(W) + val₂^{G/P}(Y)`,

since every `s′(X ∩ Z) ≥ 0` and `d_X(Y) ≤ e_{G/P}(Y)`. So it suffices that
`val₂^{G/P}(Y) := 3(|Y| − 1) − 2e_{G/P}(Y) ≥ 0` for every `Y ∋ W`.
- *Non-rigid case.* `P = P*(G)` and `G/P = Γ̂(G)`. `val₂ ≥ 1` for `|Y| ≥ 2` by (MC-77), and it is 0 at
  `Y = {W}`.
- *Rigid case.* Let `P` be `P*(G − C)` together with the chain vertices. Then `G/P = Γ ∪ π`, where
  `Γ = Γ̂(G − C)` is rigid-free (MC-77) and `π = [a] − x₁ − ⋯ − x_k − [b]` is a path with
  `[a] ≠ [b]` (`δ ≥ 1`).
  - Split `Y = Y₀ ⊔ Y_C`, with `Y₀ ⊆ V(Γ)`. The path edges inside `Y` number at most
    `|Y ∩ V(π)| − (number of runs)`.
  - If both `[a], [b] ∈ Y₀` and `Y_C = C`: `val₂ ≥ val₂^Γ(Y₀) + k − 2 ≥ 1 + 1 − 2 = 0`.
  - If both are in `Y₀` but `Y_C ≠ C`: there are at least 2 runs, so `val₂ ≥ val₂^Γ(Y₀) + |Y_C| ≥ 1`.
  - Otherwise the path edges inside `Y` number at most `|Y_C|`, so
    `val₂ ≥ val₂^Γ(Y₀) + |Y_C| ≥ 0`.

∎

`[MEASURED coverstruct.py --additivity]` At every (MC-80)-type core the asserts hold: simple quotient and
additivity. The runs covered:
- every maximal rigid set of each non-rigid member;
- in each rigid member, every non-singleton maximal rigid set of `G − C` for every chain `C` with
  `G − C` non-rigid;
- 410 cores on the `--witness 14` set, and 1 723 on the `--witness 15 --smax 4 --cores K4,dC4` set;
- the `θ(2,3,4)` beads of `TsTsTs`, `T⁶`, `T⁷`: `12 = 3 + 9`, `21 = 3 + 18`, `25 = 3 + 22`.

These check a proved identity at witnesses.

> **(MC-88)** `[PROVED]` *(the lemma `δ₂ = 1 ⟹ δ ≤ 1`, conjectured from Step MC11's histogram;
> second reading: its proof applies (MC-79)(i)'s formula to an arbitrary graph and pair, which is
> sound because that formula's repaired proof uses nothing specific to 𝒮. (MC-91) is a stronger,
> independent proof)* Let `G′` be any finite simple graph and `a ≠ b`. Then
> `δ₂ = 0 ⟹ δ = 0`, and **`δ₂ = 1 ⟹ δ ≤ 1`**.
> Consequently `[PROVED-MOD]` *((MC-33))*, under the strong induction, **(MC-51)(a) holds whenever
> `a ≁ b`**: an open `k = 2` ear with `δ₂ = 1` and `a ≁ b`.

*Proof.*
- **The quotient.** Let `Γ₂` be `G′` with its `def₂`-classes contracted. By (MC-63)(a),
  re-derived here:
  - `Γ₂` is simple and satisfies (S);
  - `δ₂ = min loss₂(X)` over `X ∋ A, B`;
  - `δ₂ = 1` gives a tight `X ∋ A ≠ B`.
- **Lemma T.** (MC-78) on `Γ₂` says: either `X = {A, B}`, so an edge of `G′` joins the classes; or
  `X` lies in a maximal `def₃`-rigid set `R` of `Γ₂`.
- **The second case.** The union `L` of the classes in `R` is `def₃`-rigid in `G′`:
  - classes are `def₂`-rigid, hence connected and `def₃`-rigid ((MC-5)(i)), so merging each class
    is harmless;
  - there is at most one `G′`-edge between two classes;
  - hence a partition of `G′[L]` coarsened to classes is a partition of `Γ₂[R]` with the same
    crossings.

  So `a, b` lie in a common `def₃`-rigid set, and `δ = 0` by (MC-79)(i).
- **The first case.** Classes lie inside maximal `def₃`-rigid sets. If `a, b` share one, `δ = 0`.
  Otherwise that edge joins `[a]` to `[b]` in `Γ̂(G′)`, and (MC-79)(i) gives
  `δ ≤ c({[a],[b]}) = 6 − 5 = 1`.
- **`δ₂ = 0`.** It gives `A = B`, a common `def₃`-rigid class.
- **The corollary.** Take `k = 2`, `a ≁ b`, `δ₂ = 1`.
  - By (MC-64) (mod JJ) the orbit is (i) or (ii).
  - `δ = 0` is (MC-54).
  - `δ = 1`: (MC-44) gives `r ≥ 1`, using `X₀(G′)` and `X₀(G′ + ab)` from the induction.
    (MC-16) gives `r ≤ δ`. So `r = 1`, which is (R₂).
  - (P₂) at `r = 1` holds in every orbit but (iv) (MC-26).
  - Dominance (MC-18)(a) and `λ = 3` (MC-19)(b) hold, so (MC-22) concludes.

  ∎

`[MEASURED coverstruct.py --pairs 7]` Every pair of every connected simple graph on `≤ 7` vertices
satisfies both implications. The `(δ₂, δ)` histogram:

`{(0,0): 15390, (1,0): 526, (1,1): 2759, (2,0): 104, (2,1): 175, (2,2): 639, (3,0): 6, (3,1): 26,
(3,2): 38, (3,3): 141, (3,4): 35, (3,5): 6, (3,6): 1}`

It also suggests `δ₂ ≥ min(δ, 3)` in general (`δ₂ = 2 ⟹ δ ≤ 2`). It is proved by (MC-91)(a),
Step MC17: `δ₂ ≤ 2 ⟹ δ ≤ δ₂`, and `δ₂ = 3` is trivial.

> **(MC-89)** `[PROVED-MOD]` *((MC-33); the coverage theorem)* **Every graph satisfying (H) is
> covered by the landed steps together with (MC-71).** Hence (MC-10)(a) holds: `X₀(G)`'s generic
> point attains `6(|V| − 1) − def₃(G)` for every finite simple connected `G` with minimum degree
> `≥ 2`. This is modulo:
> - Jackson–Jordán's equality at the named graphs (list below);
> - nothing else: (MC-80), (MC-87), (MC-89) and Step MC15's (MC-68), (MC-69)(a), (MC-71) were
>   second-read on 2026-09-24 and confirmed.
>
> *Repairs (second reading):*
> - From step 3 of the proof on, `G` is 2-connected, hence 2EC. That is what CONTRACT's
>   `|δ(W)| ≥ 2` uses.
> - "No per-graph certificate" is true, but the proof consumes a fixed set of exact computations
>   inside landed proofs: `earstep.py --chains` (MC-19), `--thetas 5` (MC-21)(b), `--lamcap` (MC-25),
>   and `earante.py --orbits` with `m2/earbad.m2` (MC-46). These are exact over ℚ, so in
>   characteristic `p` the theorem also depends on them at `p`. Characteristic 0 is unaffected.
>   *(Discharged by Step MC20: each leaf has a hand proof over every infinite field (MC-134)–(MC-139),
>   so (MC-89) rests on arguments and Jackson–Jordán alone (MC-141).)*
>
> Beyond characteristic 0, read "mod JJ" as mod (MC-33)(i).

*Proof.* Strong induction on `|V|`. Every step used consumes smaller graphs satisfying (H)
((MC-55)(i); (MC-39)'s side conditions). Let `G` satisfy (H).
1. Not 2-connected and not a cycle: CUT or BRIDGE (MC-52), (MC-53), (MC-55)(ii).
2. A cycle: BASE (MC-21)(a).
3. `def₂ = def₃`: FLAT (MC-5)(ii), JJ at `G`.
4. `def₂ > def₃` and some `def₂`-rigid subgraph: CONTRACT at a maximal one ((MC-75)(iii), with the second
   reading's repair: `G` has a `def₂`-rigid set). This is (MC-59)(d), or (MC-71) with `def₂(H) = 0`; JJ at `H`, `G/H`.
5. Otherwise (S) holds (MC-76). A θ-graph is THETA (MC-21)(b). Else `G ∈ 𝒮`, and (MC-80) gives one of:
   - a chain outside (c′) ∪ (a′), usable by (MC-79)(v), with JJ at `G′ + ab` (or `G′ + ab + x`,
     (MC-62)) and at SPLITOFF's `G″`;
   - a core `W`, additive by (MC-87), where (MC-71) applies with JJ at `H` and `G/H`.

In either case the consumed graphs are covered by induction. (MC-56) turns coverage into
attainment. ∎

**Where JJ enters (every graph is smaller than `G`, except at FLAT):**
- FLAT: at `G` itself;
- CONTRACT (both kinds): at `H` and `G/H`;
- the `k ≤ 2` ears' `dim U ≥ 2`: at `G′ + ab` / `G′ + ab + x`;
- SPLITOFF: at `G″ = G′ + ab`.

The second reader's remark after (MC-60) (itself not second-read) is that `ℓ₀ = 3 + def₂` *propagates* through CUT,
BRIDGE, ears with `k ≥ 2`, `k = 1` ears with `U ≠ 0`, and CONTRACT at `def₂`-rigid cores; (MC-69)(b)
adds CONTRACT at additive cores. If SPLITOFF and (MC-46) also propagate it (not checked), then with
the motive "attains ∧ JJ", the citation would be needed **only at FLAT leaves** (`def₂ = def₃`).
Those are exactly JJ's own content at graphs such as `K₄` and the 3-edge-connected graphs. This is
not verified, and (MC-89) is stated mod JJ throughout.

**What (MC-89) does not use.**
- The open cells (MC-51)(c) at `1 ≤ δ ≤ 4` and (a′) at `a ∼ b`;
- (MC-47)(i)'s ear step (only its span identity `Λ₂ = Λ²π` is used, inside (MC-45)'s orbit-(iv)
  branch; *repaired at Step MC20's second reading, 2026-09-25*);
- any per-graph picture certificate;
- (MC-70)'s exceptional case (the cores come from (MC-80), not from maximality among all proper rigid
  sets).

The stuck families of (MC-83)/(MC-84) are covered through step 5's second alternative. `x0arms.py`
agrees at `QsQsQ`, `AsAsAs`, `TsTsTs` (CONTRACT at a bead, certified per graph).

---


**7. The second reading's own proof of (MC-87): relative maximality.** *(Written by the second
reader of (MC-80), (MC-87)–(MC-89), the third 2026-09-24 session's Track G, as an independent
cross-check. It needs no (S): it is (MC-70)'s maximality argument, run inside `V − x` for a vertex
`x` of degree `≤ 2`.)*

> **(MC-119)** `[PROVED]` *(relative maximality)* Let `G` be a simple graph. Let `X` be either empty
> or a single vertex `x` with `deg_G x ≤ 2`. Let `W` be maximal under inclusion among the rigid
> subsets of `V ∖ X`, with `W ≠ V` and `G/H` simple. Then **`W` is additive**.
> - If `X = ∅`, the hypothesis `W ≠ V` says that `G` is non-rigid.
> - If `X = {x}`, it is automatic.

*Proof.* Let `ℱ` be the **finest** `def₂`-optimal partition of `G/H` ((MC-67)(c)'s `𝒮`, renamed here to avoid a clash with the class 𝒮). It exists because the
optimal partitions are closed under meets ((MC-67)(a), re-derived below). Let `ℱ* ∋ v*` be the
part of `ℱ` containing `v*`, and put `T := ℱ* ∖ {v*}`. If `T = ∅`, additivity holds by
(MC-67)(c), "⟸". So suppose `T ≠ ∅`, and let `Γ := (G/H)[ℱ*]`.

1. **`Γ` is `def₂`-rigid, and its trivial partition is its *only* optimal partition.** Refining
   the part `ℱ*` of `ℱ` by a partition `𝒬` of `ℱ*` changes `val` by exactly `val_Γ(𝒬)`. The
   refinement adds `|𝒬| − 1` parts, and adds as crossing edges exactly the edges of `Γ` that
   cross `𝒬`. Since `ℱ` is optimal, `val_Γ(𝒬) ≤ 0`, so `def₂(Γ) = 0`. If `val_Γ(𝒬) = 0` for a
   nontrivial `𝒬`, the refinement is optimal and strictly finer than `ℱ`, a contradiction.
2. **Removing `x` from `T`.** If `X = ∅`, or `x ∉ T`, put `T′ := T`. Suppose `x ∈ T`.
   - *`x` has degree exactly 2 in `Γ`.* If `deg_Γ x ≤ 1`, the partition `{{x}, ℱ* − x}` has
     value `3 − 2 deg_Γ x ≥ 1 > 0`, against step 1.
   - *`T ≠ {x}`.* Since `G/H` is simple, `x` has at most one edge to `v*`. So `T = {x}` would give
     `deg_Γ x ≤ 1`.
   - *`Γ − x` is `def₂`-rigid.* For any partition `𝒫` of `ℱ* − x`, the partition `𝒫 + {x}` of
     `ℱ*` is nontrivial. Both edges of `x` cross it, so
     `val_Γ(𝒫 + {x}) = val_{Γ−x}(𝒫) + 3 − 4`. By step 1 the left side is `≤ −1`, so
     `val_{Γ−x}(𝒫) ≤ 0`.
   - Put `T′ := T − x`.

   In every case `T′ ≠ ∅`, `T′ ∩ X = ∅`, and `Γ′ := (G/H)[{v*} ∪ T′]` is `def₂`-rigid.
   (**Uniqueness in step 1 is essential.** A triangle is `def₂`-rigid, but deleting a vertex
   leaves an edge, with `def₂ = 1`. It cannot occur as `ℱ*`, because its singleton refinement
   is also optimal.)
3. **The lift.** `Γ′` is `def₂`-rigid, hence connected (`c` components give value `3(c − 1)`).
   Hence `Γ′` is `def₃`-rigid: `val₃ − val₂ = 3(|𝒫| − 1 − d(𝒫)) ≤ 0` partition by partition,
   which is (MC-5)(i)'s one line. Also `Γ′ = G[W ∪ T′]/H`. (MC-67)(b) with `(6, 5)` gives
   `def₃(G[W ∪ T′]) ≤ def₃(H) + def₃(Γ′) = 0`. So `W ∪ T′` is a rigid subset of `V ∖ X`
   strictly containing `W`, against maximality. ∎

*The pieces re-derived for this proof.*
- **(MC-67)(a).** `|𝒫 ∧ 𝒫′| + |𝒫 ∨ 𝒫′| ≥ |𝒫| + |𝒫′|`: in the bipartite
  intersection graph of the two partitions, edges count the blocks of the meet, and components
  count the blocks of the join. Edge by edge, `[crosses ∧] + [crosses ∨] ≤ [crosses 𝒫] + [crosses 𝒫′]`.
  So `val` is supermodular, and the meet of two maximizers is a maximizer.
- **(MC-67)(b)**, for `def₃`. Let `t` parts of `𝒫` meet `W`. Then
  `d_G(𝒫) ≥ d_H(𝒫|_W) + d_{G/H}(𝒫/W)`: a non-core edge between two distinct `W`-meeting parts
  crosses `𝒫` but not `𝒫/W`. The part counts add exactly.
- **(MC-67)(c), "⟸" at `T = ∅`.** Take the class partition `𝒬` of `H` and add the parts of `ℱ`
  other than `{v*}`. The part counts add, and the crossing edges add: a boundary edge crosses on
  both sides. So `val_G = def₂(H) + def₂(G/H)`. Together with (b), that is additivity.

> **(MC-120)** `[PROVED]` Let `G ∈ 𝒮` have every chain in (c′) ∪ (a′).
> **(i)** If `G` is non-rigid, it has a non-singleton maximal rigid set. Every such `R` is
> proper, has `G/G[R]` simple, and is additive.
> **(ii)** If `G` is rigid, some vertex `x` of a chain has a non-singleton rigid subset of
> `V − x`. Every maximal such `W` is proper and rigid, has `G/H` simple, and is additive.
>
> In both cases:
> - `G` is 2EC (2-connected on `≥ 3` vertices), so `|δ(W)| ≥ 2`;
> - `H` and `G/H` satisfy (H) and are smaller;
> - **so (MC-71) applies**: `X₀(H)` and `X₀(G/H)` attaining give `X₀(G)` attaining, modulo JJ
>   at `H` and `G/H`.
>
> The `W` of (ii) are exactly the cores `B` of Theorem S (MC-80), rigid case. The
> maximal rigid sets of `G − C` are the maximal rigid subsets of `V − x` for `x ∈ C`, since the
> other vertex of a `k = 2` chain is a leaf of `G − x`.

*Proof.*

**(i)**
- *Existence.* Take any chain. A blocked `k = 2` chain has `a ∼ b`, so `C ∪ {a, b}` is an
  induced 4-cycle, and `C₄` is rigid. A blocked `k = 1` chain has `δ ≤ 4`, so `x` lies in a
  rigid set. This is (MC-79)(ii), re-derived:
  - if `x` lies in no rigid set, then `x` is a vertex of `Γ̂(G)`;
  - for `Y ∋ [a], [b]` in `Γ̂(G) − x = Γ̂(G′)`, rigid-freeness gives `1 ≤ c(Y ∪ x) = c(Y) − 4`;
  - by (MC-79)(i) the minimum of `c(Y)` is `δ`, so `δ ≥ 5`.
- *Simplicity.* An outside vertex with two neighbours in a maximal `R` would enlarge it, by
  (MC-75)(i) with `(6, 5)`.
- *Additivity.* (MC-119) with `X = ∅`.

**(ii) Existence of `x`.** This is Step MC16's argument, re-derived. `G` has
`Σ(3 − deg) = def₂(G) + 3 ≥ 4` (MC-76), so it has `≥ 4` degree-2 vertices. Every chain has
`k ≤ 2`, so there are `≥ 2` chains. For a chain `C` with `k ≤ 4` in a rigid `G`, (MC-17) with
`δ ≤ def₃(G′)` gives `δ = def₃(G − C)`. So blocked means `G − C` is non-rigid.
- *Some chain `C` has `k = 2`.* Then it is (a′), so `a ∼ b`. Take a chain `C′ ≠ C` and
  `x ∈ C′`. The induced 4-cycle `C ∪ {a, b}` avoids `x`, since `a, b` are hubs.
- *Every chain has `k = 1`.* Let `d` be the number of degree-2 vertices and `𝐻` the set of hubs.
  Each degree-2 vertex has two hub neighbours, so `Σ_𝐻 deg ≥ 2d` and `Σ_𝐻 deg ≥ 3|𝐻|`. Hence
  `5|E| − 6|V| = (5/2)Σ_𝐻 deg − d − 6|𝐻| ≥ 0`.
  - For any chain vertex `x`, the all-singletons partition of `G − x` has
    `val₃ = 6|V| − 5|E| − 2 ≤ −2`.
  - But `def₃(G − x) = δ ≥ 1`, and `P*(G − x)` is a maximizing partition (MC-77).
  - So `P*(G − x)` has a non-singleton part.

**(ii) Simplicity.** Let `x` lie on the chain `C = a − ⋯ − b`, and let `W` be maximal rigid in
`V − x`.
- *Other outside vertices.* A vertex `u ≠ x` with two neighbours in `W` would make `W ∪ u` rigid
  inside `V − x` ((MC-75)(i)), against maximality.
- *`x` itself, `k = 2`.* The other chain vertex has degree 1 in `G − x`, so it is not in `W`.
  (A rigid set has minimum degree `≥ 2` in itself.) So `x` has at most one neighbour in `W`.
- *`x` itself, `k = 1`.* If `a, b ∈ W`, then `a, b` lie in a common rigid subgraph of `G′ = G − x`.
  Merging it into a maximizing partition of `G′` gives `def₃(G′/ab) = def₃(G′)`, so `δ = 0`. That
  contradicts (c′), where `δ ≥ 1`.

**(ii) Additivity.** (MC-119) with `X = {x}`. `W` is proper since `x ∉ W`, and it is rigid with
`|W| ≥ 3`. ∎

> **(MC-121)** `[REFUTED]` *(witness `C6pend`: the "every" in (MC-81)(β′) as first written)* Let `C6pend` be:
> - the cycle `c₀ ⋯ c₅`;
> - a path `z₁ − z₂ − z₃` with `z₁c₀`, `z₂c₂`, `z₃c₄`;
> - a 4-vertex ear `c₁ − e₁ − e₂ − e₃ − e₄ − c₃`.
>
> This graph has `n = 13` and `m = 16`, is in 𝒮, and is rigid (`def₂ = 4`, `def₃ = 0`).
> `W = {c₀, …, c₅}` is a proper rigid set with `G/H` simple and `1 ≤ def₂(H) = 3 < 4 = def₂(G)`.
> But `def₂(G/H) = 2`, and `4 ≠ 3 + 2`, so **`W` is not additive**. By (MC-68)(c), mod JJ at `G`,
> (i) fails there.
> `[CONSTRUCTED]` *(`betaprime.py`)* The counts are exact. `--cert`: coreshrink finds (i) failing
> and (ii) holding, at 2 / 2 draws.

*Why.* In 𝒮-terms, `Z′ = {z₁, z₂, z₃}` has 5 edges into `W ∪ Z′`, so
`s′(W ∪ Z′) = s′(W) + 9 − 10 < s′(W)` ((MC-119)'s *Reading in 𝒮*). The ear raises `s′(V)` by 2 without
touching `W`. `W` sits strictly inside the rigid set `V`, and nothing about it is maximal.

*Consequence.* This is not a gap in (MC-89), which uses (β) only at the cores of (MC-80), and those
are additive ((MC-87), (MC-120)). It is why (MC-81)'s (β′) bullet was repaired.

> **(MC-122)** `[MEASURED]` *(`relmax.py`; checks of proved statements at witnesses)*
> - **`--lemma 8`**: every simple 2EC graph on `≤ 8` vertices, every degree-2 `x`, every maximal
>   rigid subset `W` of `V − x`. `P*` is computed by the merge criterion and cross-checked
>   against brute force at every instance.
>   - 1 812 have `G/H` simple, and **all are additive**.
>   - 7 981 are not simple. In every one the only heavy vertex is `x` itself, on a `k = 1` chain
>     (asserted).
>   - Non-rigid `G` with a rigid set do not occur on `≤ 8` vertices; the `X = ∅` case is
>     exercised below.
> - **`--witness 16 --smax 4 --cores K4,dC4`** (Step MC16's witness set: 1 061 𝒮-members):
>   - 8 840 simple `(x, W)`, all additive;
>   - 266 maximal rigid sets of non-rigid members, all additive;
>   - 315 non-simple, all heavy at `x` only.
>
>   **`--witness 14`**: 990 𝒮-members and 4 134 simple `(x, W)`, all additive. The one stuck
>   member (`dC6111111011` = `QsQsQ`) gets a (MC-120) core `C₄` with counts `5 = 1 + 4`.
> - **`--families`**: Step MC16's stuck families and three mixed ones:
>   - the families: `QsQsQ`, `QQQQs`, `Q⁵`, `QsQsQs`, `Q⁶`, `Q⁷`, `AsAsAs`, `A⁶`, `A⁷`,
>     `TsTsTs`, `T⁶`, `T⁷`, `QsAsTs`, `QAQAQA`;
>   - each is asserted to be in 𝒮 with 0 usable chains;
>   - at every blocked chain vertex `x` and every maximal rigid `W` of `G − x`, `G/H` is simple and
>     `W` is additive (18–189 pairs per graph);
>   - the (MC-120) cores are `C₄` beads, except at `TsTsTs` and `T⁶`, where `x` on a bead's 4-path
>     leaves the 5-cycle `h y h′ w t₁` (counts `12 = 2 + 10`), and at `T⁷` (non-rigid), where it
>     is a whole `θ(2,3,4)` bead (`25 = 3 + 22`).
> - **`--cert`** (coreshrink, relaxed, exact, seeded through `contractcheck.run`): (MC-39)'s (i)
>   and (ii) are certified at one exact picture, verdict `OK`, at the (MC-120) core of **12 of the 14
>   families**, including `TsTsTs`'s `C₅` core. `T⁶` and `T⁷` (60 and 70 edges) are skipped by
>   the script's cap. This agrees with (MC-68)(d) and (MC-69)(b) at these cores. It is a
>   cross-check of (MC-71), not a proof of it.


**Drivers** (all at `PYTHONHASHSEED=0` from the repository root; exact integer deficiencies
(count-matroid ranks), no randomness; the `--hunt` populations are generated by nauty's `geng`, an
external deterministic generator, nauty 2.9.3):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/coverstruct.py --necklaces` | (MC-83), (MC-84): the stuck families, 0 usable chains; controls usable; bead additivity asserted | < 1 s |
| `python3 notes/scripts/w4/coverstruct.py --exh 8` | 16 𝒮-members (all rigid); (MC-77)–(MC-80) asserted | ~5 s |
| `python3 notes/scripts/w4/coverstruct.py --witness 14` / `--witness 16 --smax 4 --cores K4,dC4` | 990 𝒮-members, 1 stuck (`QsQsQ`) / 1 061 𝒮-members (881 rigid), 0 stuck; every assert held | ~12 s / ~40 s |
| `python3 notes/scripts/w4/coverstruct.py --additivity --witness 14` / `--additivity --witness 15 --smax 4 --cores K4,dC4` | (MC-87) at 410 / 1 723 cores | ~8 s / ~15 s |
| `python3 notes/scripts/w4/coverstruct.py --pairs 7` | (MC-88) at every pair of every connected graph on ≤ 7 vertices; the `(δ₂, δ)` histogram | ~1.5 s |
| `geng -C -d2 -t -q n 0:⌊(3n−4)/2⌋ \| python3 notes/scripts/w4/coverstruct.py --hunt -`, `n = 9..14` | (MC-83): 0 stuck at `n ≤ 13` (35 / 304 / 879 / 9 030 / 32 177 in 𝒮); at `n = 14`, 1 stuck (`QsQsQ`) of 411 045 in 𝒮 (736 012 candidates) | `n = 14`: ~140 s |
| `geng -C -d2 -tf -q n 0:⌊(3n−4)/2⌋ \| … --hunt -`, `n = 14, 15, 16`; `geng -C -d2 -D3 -tf -q n … \| … --hunt -`, `n = 17, 18` | no stuck graph without a 4-cycle: girth `≥ 5` on `n = 14–16` (24 773 / 129 911 / 1 365 792 in 𝒮), subcubic girth `≥ 5` on `17–18` (166 907 / 756 629 in 𝒮) | ~0.5 / ~1 / ~8 / ~1 / ~5 min |
| `python3 notes/scripts/w4/x0arms.py --tree <QsQsQ / AsAsAs / TsTsTs> --ear23 antecedent [--contract off] [--depth 0 \| 1]` | UNCOVERED without CONTRACT; CONTRACT at a bead with the default `--contract cert` | < 3 s each |
| `python3 notes/scripts/w4/relmax.py --lemma 8` / `--families` / `--witness 14` / `--witness 16 --smax 4 --cores K4,dC4` / `--pairs88 400` / `--cert` | (MC-122): (MC-119) at 1 812 / every blocked `x` of 14 families / 4 134 / 8 840 + 266 instances, all additive; (MC-88) at 47 883 pairs; coreshrink (i), (ii) at 12 of 14 family cores | ~52 s / ~31 s / ~11 s / ~47 s / ~13 s / ~57 s |
| `python3 notes/scripts/w4/betaprime.py --cert` | (MC-121): `C6pend` in 𝒮, `W = C₆` with `4 / 3 / 2`, not additive; coreshrink (i) = 0, (ii) = 1 at 2 / 2 draws | ~1 s |

`--beads` (the framing search behind (MC-84)) takes `geng -c -d2 -tf -q n ⌈6(n−1)/5⌉:⌊(3n−4)/2⌋` on
stdin, `n = 5..13`, with `--tmax 3`; the two histograms quoted in (MC-84) (`n = 8` and `n = 13`)
were re-run at landing and reproduce.

