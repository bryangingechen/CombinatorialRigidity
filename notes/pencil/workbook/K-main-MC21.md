## §(K-main) — Step MC21 — the rigid-set closure: EAR alone covers 𝒮, and the last ear cell narrows to Case II-cyclic (modulo Jackson–Jordán)

#### Step MC21 — the rigid-set closure: EAR alone covers 𝒮, and the last ear cell narrows to Case II-cyclic (modulo Jackson–Jordán)

*Worked 2026-09-24 by a read-only agent (the third 2026-09-24 session's Track J) on (MC-117), the last
open ear cell. It returned after that session had stopped, was committed verbatim to
`notes/w4-pending/` (`e2ec9927`), and was landed here by the next session. Its provisional labels
(J-1)–(J-10) are renumbered (MC-142)–(MC-156) in order of appearance, with the measurement blocks
given labels of their own. The coordinator checked (MC-142)–(MC-148), (MC-150), (MC-151) and (MC-153)
at the level of the written proofs, and repaired two statements in place
(marked *Coordinator's repair*); nothing else was wrong. **Second-read 2026-09-25** by a fresh
reader, together with Step MC17's (MC-105) and what it rests on. No mathematical error. The repairs
are to dependency accounting, to two over-statements in this Verdict, and to (MC-143)'s first step
and first remark, each marked *second reading*. The reader added (MC-162)–(MC-165), a further
narrowing of (MC-154) (drivers `w4/wsearch.py`, `w4/c1check.py`, `w4/cycshape.py`). None of it is on
(MC-89)'s critical path: (MC-148) is a second route to (MC-89)'s in-𝒮 half. Drivers
`w4/earcover.py`, `w4/blobcount.py`, `w4/rigidclose.py`, `w4/ringprobe.py`, `w4/cycprobe.py`,
`w4/findcyc.py`, `w4/foldcheck.py`, `w4/cellclasses.py` (new).*

**Verdict.**
- **In 𝒮 the cell (c′) closes except for one structural sub-cell, and that sub-cell is not needed
  for coverage.** All of the following are under the strong induction and modulo JJ at named smaller
  graphs:
  - **(MC-143), the rigid-set closure.** Let a `k = 1` chain `y` with `1 ≤ δ ≤ 4` lie in a proper
    rigid set `W`, where `G/G[W]` is simple and `W` is additive. Then `X₀(G)` attains. The proof is
    the ear step plus rigidity of `G[W]` at `X₀(G)`'s generic point, which comes from restriction
    (MC-68)(d) and the induction at `G[W]`. It uses neither CONTRACT's no-jump condition (MC-39)(ii)
    nor `X₀(G/H)`.
  - **(MC-142), the combinatorial supply of `W`.** Every *locally minimal* set of `def₃`-classes
    through `[a]`, `[b]` gives such a `W` whenever that `W` is proper (MC-144). This includes every
    non-rigid `G`.
  - **(MC-145), what is left over (Case II).** When every locally minimal `Y` has `W_Y = V(G)`, `G`
    is rigid, the class quotient `Γ₃` of `G − y` is the unique minimiser, and every proper set of
    classes through `[a]`, `[b]` has `c ≥ 5`. (A `W` of another shape can still exist in Case II, and
    then (MC-143) still applies: (MC-162), (MC-163).) *(Repaired at the second reading, 2026-09-25:
    first written "When no such `W` exists".)*
  - **(MC-151), Case II with `Γ₃` a path (the class ring).** This closes by the chord route: at
    `δ = 3` from the flat point, and at `δ = 4` from a "folded" point whose dual is a skew pentagon.
    The `δ = 3` half holds for **every** `G′` whose minimiser is a path, not only in 𝒮.
- **(MC-148), EAR covers 𝒮.** Every `G ∈ 𝒮` has a chain closed by a landed step, by (MC-105) for
  (a′), or by (MC-143). The combinatorial core is a count, (MC-147), in the style of Theorem S's
  rigid case: if every chain is a `k = 1` chain in (c′), then some chain vertex lies inside a
  non-singleton class of `G − y`. That class is additive by a count, (MC-146), so (MC-143) closes
  that chain.
  - So **a second proof of (MC-89)** goes through with EAR in place of Theorem S (MC-80), (MC-87)
    and CONTRACT at cores with `def₂(H) ≥ 1`.
  - **It is not fully independent.** It shares with the first proof:
    - the reduction to 𝒮, including CONTRACT at `def₂`-rigid cores;
    - the chain calculus (MC-76)–(MC-79);
    - the landed usable steps;
    - (MC-68)(d);
    - JJ.

    It also rests on (MC-105) (Step MC17; with (MC-85) and (MC-94), second-read 2026-09-25).
    *(Repaired at the second reading: the first wording listed only (MC-68)(d) and JJ.)*
- **What remains open is the sub-cell (MC-154), "Case II-cyclic":** the chain `y` itself, in
  Case II (so `G` is rigid and `V(Γ₃)` is the only locally minimal class set) with `Γ₃` cyclic, and
  with no `W` of (MC-162)'s kind.
  - The chord route closes it under two sufficient conditions at the generic point of `X₀(G′ + ab)`
    (a class-level stress blocks (MC-150), but (MC-110) can still close the step; *second reading*:
    first written "reduces it exactly to two conditions"):
    the class-level framework of `G′` carries no self-stress there, and, at `δ = 4`,
    `ρ_Γ ⊄ n^⊥` ((MC-150), (MC-153)).
  - In 𝒮, `a′(z₀)` *equals* the number of those class-level stresses (MC-153). That proves (MC-118)'s
    `a′(z₀) = 0` whenever `Γ₃` is a forest, or its 2-core is properly additive in `G″` with `A` or
    `B` outside it.
  - Every tested Case II-cyclic instance is certified: all 6 in 𝒮 on ≤ 13 vertices, plus 5
    constructed ones (MC-155).
- **Bad configurations.** None was found. The analysis says where one would have to live: a class
  cycle of length ≥ 7 whose hinge lines become special at the chord point. The flag incidences
  there touch only the hinges at `a` and `b`.
- **At landing** (all figures re-run and reproduced; *Drivers*): `ringprobe.py`'s `inS` column is
  corrected (the staged driver did not exclude θ-graphs; two rows move, and no claim used them),
  and `earcover.py` now also asserts (MC-79)(i)'s `δ = min c(Y)` at every (c′) chain.

**Setting and notation.**

Step MC10's, with Step MC13's `Pen`, `N`, `star`, `⊥` (Klein), and Step MC18's chord point. The graph
is `G = G′ + (a − y − b)`, with `a ≁ b`, `G′` satisfying (H), and `G″ := G′ + ab`. Also `n := p_a p_b`,
`m := π_a ∩ π_b`, and `f`, `g`, `δ`, `δ₂` as in Step MC10. "JJ at `Γ`" is Jackson–Jordán's equality at
the named simple graph, as in Step MC15; "IH" is Step MC13's strong induction hypothesis.

**Classes.** `Γ₃ := Γ̂(G′)` has as vertices the **classes**, which are the maximal rigid sets of `G′`
(**blobs**) and the singletons (Step MC16). `A = [a]` and `B = [b]`, and `A ≠ B` since `δ ≥ 1`.
`Γ₃` is simple and rigid-free (MC-77). For a set `Y` of classes, put
`c(Y) := 6(|Y| − 1) − 5e_{Γ₃}(Y)`. Then `δ = min{c(Y) : A, B ∈ Y}` ((MC-90), (MC-79)(i)), and a
minimiser is a path of `δ + 1` classes or contains a cycle ((MC-102)).

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

**Part I — the rigid-set closure, and EAR covers 𝒮.**

> **(MC-142)** `[PROVED]` *(locally minimal class sets give additive rigid sets)* Let `G ∈ 𝒮` and let
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
  - Otherwise `c(Z₀) ≥ 0`: it is `0` if `Z₀ = {y}`, and `c(Z₀ − y) + 6 − 5·[A or B in Z₀] ≥ 1`
    if not. This uses `c ≥ 0` on class sets (`c = 0` on a single class, and `c ≥ 1` otherwise by
    rigid-freeness).
- Every other part has `c ≥ 0`. So `Σ_{Z ∈ 𝒫} c(Z) ≥ c(Y) − 4` in both cases (in the second
  because `c(Y) ≤ 4`), and `val(𝒫) ≤ 0`.

*Coordinator's repair:* the draft had "`c(Z₀) ≥ 1`" for every `Z₀` not holding both `A` and `B`,
which fails at `Z₀ = {y}`. Only `≥ 0` is used.

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

> **(MC-143)** `[PROVED-MOD]` *((MC-33); the rigid-set closure; JJ at `G″` and at `G[W]`, `G/G[W]`;
> rests on (MC-68)(d))* Let `G ∈ 𝒮` satisfy IH, and let `y` be a `k = 1` chain with `1 ≤ δ ≤ 4`.
> Let `W ∋ y` be a proper subset of `V(G)` such that:
> - `G[W]` is rigid and satisfies (H);
> - `G/G[W]` is simple;
> - `W` is additive.
>
> **Then `X₀(G)` attains.**

*Proof.*
1. *The chain.* In 𝒮, `a ≁ b` and `δ₂ ≥ 2` ((MC-79)(ii)). So `dim U ≥ 2` (JJ at `G″`), and
   restriction `X₀(G) → X₀(G′)` is dominant ((MC-18)(b)). `dim U ≥ 2` also excludes orbits (iii) and
   (iv), so `λ = 2` ((MC-19)(b)). Directly: the generic point of `X₀(G)` has `q_y` off `q_aq_b`, so
   `p_y ∉ n`. No finer orbit claim is used. (In 𝒮 the orbit is (i), by (MC-99) or (MC-79)(vi).)
   *(Simplified at the second reading, 2026-09-25: the first version cited the orbit-(i) claim.)*
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
  `δ ∈ [1, 4]`. The proof uses 𝒮 only for `a ≁ b` and `δ₂ ≥ 2` (MC-164). So it also covers
  (MC-103)'s open "`δ = 2`, cyclic class quotient" wherever such a `W` exists, with additivity read
  as `def₂(G) = def₂(G[W]) + def₂(G/G[W])`. *(Repaired at the second reading, 2026-09-25: outside 𝒮
  the claim needed (MC-164).)*
- It does not need the chord point, class rigidity at `X₀(G′)`, (MC-69), (MC-70), or `X₀(G/H)`.

**Added at the second reading (2026-09-25).**

> **(MC-162)** `[PROVED-MOD]` *((MC-33); a supply of `W` that (MC-142) misses)* Let `G ∈ 𝒮` satisfy IH,
> and let `y` be a `k = 1` chain with `1 ≤ δ ≤ 4`. Suppose `G` has another chain
> `C = a_C − x₁ − ⋯ − x_m − b_C` with `m ≥ 2` and `G[V ∖ C]` rigid. (For `m ≤ 4` and `G` rigid, this
> is `δ_C = 0`, by (MC-80)'s count.) Then `W := V ∖ C` satisfies (MC-143)'s hypotheses, so
> **`X₀(G)` attains**.

*Proof.*
- `W` is proper and contains `y`: chains are disjoint, and `y`'s neighbours are hubs.
- `G[W]` is rigid, hence connected with minimum degree `≥ 2`, so (H) holds.
- The quotient is simple: `x₁ ≠ x_m` since `m ≥ 2`, and each has exactly one neighbour in `W`;
  interior `x_i` have none.
- (A): split `Z′ ⊆ C` into maximal runs. A run of `j` vertices has `j − 1` inner edges and at most
  one edge to `W`, unless it is all of `C` (then two). Runs are not adjacent. So
  `e(Z′) + e(Z′, W) ≤ |Z′|`, or `m + 1` when `Z′ = C`, and `2(m + 1) ≤ 3m` for `m ≥ 2`. (S) holds in
  𝒮, so (A) is additivity.
- (MC-143) applies. ∎

Such a `C` is itself usable, so this adds nothing to coverage, but it removes such `y` from
(MC-154)'s residue.

> **(MC-163)** `[MEASURED]` *(`wsearch.py`; exhaustive over every `W` with `y ∈ W ≠ V`)*
> - Of the six Case II-cyclic chains of 𝒮 on 13 vertices (1 023 candidate sets each), three have a
>   `W` satisfying (MC-143)'s hypotheses: `L??CAA_EAgDG@g` at `y = 5` and `y = 2` (`L = 7`, `(3, 4)`,
>   `p + p′ = 2`), and `L??CB@Oa@GB_?s` at `y = 4` (`L = 8`, `(4, 4)`, `p + p′ = 1`). **This shape is
>   in (MC-154)'s list.**
> - In each, the unique `W` is `V ∖ {0, 6}`, the complement of a `k = 2` chain with `δ = 0`:
>   (MC-162)'s `W`.
> - None was found in the other three, or in `ringprobe.py`'s in-𝒮 `C₁₀` rings `@2`, `@A` and `@A,B`
>   (2 047, 2 047 and 16 383 sets). `C10(v)` is not in 𝒮; `C10+C4x3` (`n = 23`) is past the
>   `n ≤ 17` cap.
>
> So "Case II" is not the same as "(MC-143) does not apply".
> `PYTHONHASHSEED=0 python3 notes/scripts/w4/wsearch.py` (< 1 s).

> **(MC-164)** `[PROVED-MOD]` *((MC-33))* (MC-143) holds for any `G` satisfying (H), in place of
> `G ∈ 𝒮`, if `a ≁ b` and `δ₂ ≥ 2`. Additivity is read as `def₂(G) = def₂(G[W]) + def₂(G/G[W])`; JJ
> at `G″`, `G[W]` and `G/G[W]`.

*Proof.* 𝒮 enters only in step 1. `def₂(G″) = f₂ − min(δ₂, 2)` is the general count ((MC-63)(b)'s
proof), (MC-68)(d) holds for any simple `G`, and steps 2–5 use only (MC-44), (MC-16), (MC-17) and
IH. `G[W]` rigid implies (H). ∎

> **(MC-165)** `[MEASURED]` *(`c1check.py`; exact ℚ at seed `20260924`, ranks mod `2⁶¹ − 1` only as
> certificates)* (MC-143)'s mechanism at every C′-I chain in (MC-117)'s open cell (`k = 1`,
> `δ₂ = 3`, `δ ≥ 3`) of every 𝒮-member on 13 vertices: 41 099 graphs, 32 177 in 𝒮, 46 chains, all
> 46 certified. At one exact certified `X₀(G)` picture per chain, restriction `L_G → L_{G[W]}` is
> onto, `G[W]` is rigid, and `G` attains.
> `geng -C -d2 -t -q 13 0:17 | PYTHONHASHSEED=0 python3 notes/scripts/w4/c1check.py` (~24 s).

> **(MC-144)** `[PROVED-MOD]` *((MC-33); Case I, a corollary of (MC-142) and (MC-143))* In the setting
> of (MC-142), suppose some locally minimal `Y` has `W_Y ≠ V(G)`. Then `X₀(G)` attains. This holds
> whenever `G` is not rigid: `W_Y` is then rigid and proper. For non-rigid `G` the maximal rigid set
> `R ∋ y` also serves as `W`: its quotient is simple by (MC-77), and it is additive by (MC-70), since
> `def₃(G) > 0`.

> **(MC-145)** `[PROVED]` *(the dichotomy)* Suppose (MC-144) does not apply to `y` (**Case II**). Then:
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
the arcs between the attachment classes of `A`, `B`, and `p, p′` for the pendant lengths. Then
`L + p + p′ = δ + 6`, and (ii) at the two `A`–`B` paths asks `p + p′ + min(d₁, d₂) ≥ 5`:
- `δ = 3`: `L = 7` with arcs `(3,4)` and `p + p′ = 2`; or `L = 8` with arcs `(4,4)` and `p + p′ = 1`.
- `δ = 4`: `L = 7` (`p + p′ = 3`), `L = 8` (`p + p′ = 2`), `L = 9` with arcs `(4,5)`
  (`p + p′ = 1`), or `L = 10` with arcs `(5,5)` (`p + p′ = 0`).

Multicyclic shapes exist too, for example a `θ(5,5,6)` of classes with `A`, `B` inside two arcs.

> **(MC-146)** `[PROVED]` *(blobs of `G − y` are additive in `G`)* Let `G ∈ 𝒮`, and let `y` be a `k = 1`
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

> **(MC-147)** `[PROVED]` *(the count)* Let `G ∈ 𝒮` have only `k = 1` chains, and let `y` be one with
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

> **(MC-148)** `[PROVED-MOD]` *((MC-33); EAR covers 𝒮)* Under IH, **every `G ∈ 𝒮` has a chain whose
> ear step is closed**, in one of three ways:
> - by a landed step (usable, (MC-79)(v));
> - by (MC-105), for (a′);
> - by (MC-143), for a `k = 1` chain in (c′) lying in a proper additive rigid set with simple quotient.

*Proof.*
- `G` has chains, since it has at least 4 degree-2 vertices.
- If none is usable or in (a′), then every chain is a `k = 1` chain in (c′), by (MC-79)(v).
- Pick one, `y`. By (MC-147), a chain vertex `w` lies in a blob `X` of `G − y`.
- By (MC-146), `X` is a proper additive rigid set with simple quotient containing `w`. `w` is a
  `k = 1` chain in (c′) with `δ_w ≤ 4` ((MC-79)(ii)).
- (MC-143) closes it. ∎

**What (MC-148) does to (MC-89).** The reduction to 𝒮 is unchanged:
- CUT/BRIDGE, BASE, FLAT, THETA;
- CONTRACT at maximal `def₂`-rigid sets, (MC-75)/(MC-59)(d).

Inside 𝒮, (MC-148) replaces Theorem S (MC-80) and its cores, (MC-87), and CONTRACT at cores with
`def₂(H) ≥ 1`.

*(Rewritten at the second reading, 2026-09-25: the first version understated what the two proofs
share.)* The citations it consumes inside 𝒮:
- (MC-68)(d), with JJ at `G[W]` and `G/G[W]`;
- (MC-44) (IH at `G′`, `G″`), and JJ at `G″` (with (MC-4)(b) at `G′`, for `dim U ≥ 2`);
- (MC-105), with (MC-85), and JJ at `G′ + x` for the (a′) orbit ((MC-95)(iii) or (MC-79)(vi));
- (MC-16)–(MC-19), (MC-76), (MC-77) and (MC-79)(i), (ii), (v);
- the landed steps behind "usable".

Inside 𝒮 it does **not** consume (MC-69) (no-jump), (MC-39)'s (ii), (MC-70), (MC-71) at
`def₂(H) ≥ 1`, or `X₀(G/H)`. The unchanged reduction to 𝒮 still does, at `def₂`-rigid cores:
(MC-59)(d) is (MC-39) with (i) from (MC-59)(b), (ii) from (MC-59)(c3), and `X₀(G/H)`.

What the two proofs share:
- the whole reduction to 𝒮;
- the chain calculus (MC-76)–(MC-79);
- every landed step behind "usable";
- (MC-68)(d), the restriction half of CONTRACT's certificate;
- JJ.

So inside 𝒮 this is a second proof of both halves, structural and certificate, of (MC-89). It is not
a JJ-independent proof, and it is not a second proof of (MC-89) outside 𝒮. Its new dependencies are
(MC-105), (MC-85) and (MC-94), which a second reader re-derived on 2026-09-25, together with (MC-44),
(MC-146) and (MC-147). The orbit-(i) claim that (MC-143) first cited is not needed ((MC-143),
step 1).

> **(MC-149)** `[CONSTRUCTED]` *(`earcover.py --necklaces`, `rigidclose.py`; the stuck families)*
> - The stuck families of (MC-83)/(MC-84) (`QsQsQ`, `QQQQs`, `Q⁵`, `QsQsQs`, `Q⁶`, `Q⁷`, `AsAsAs`,
>   `A⁶`, `A⁷`, `TsTsTs`, `T⁶`, `T⁷`) all have closable chains.
> - **Every (c′) chain in them is closed**: the bead chains are (MC-144), and the singles are
>   Case II-tree, closed by (MC-151) at `δ ∈ {3, 4}` and by (MC-112) at `δ = 2`.
> - At `QsQsQ`, `QsQsQs` and `TsTsTs`, `rigidclose.py` certifies (MC-143)'s mechanism. At one exact
>   certified `X₀(G)` picture, restriction `L_G → L_{G[W]}` is onto, `G[W]` is rigid (rank
>   `6(|W| − 1)`), and `G` attains (78/78, 84/84, 156/156).

**Part II — the chord route at `y` itself (Case II), and what it leaves.**

Here `z₀` is Step MC18's generic chord point, generic in `L_{G″}(q)`, and `z(s) = z₀ + sz₁`.

> **(MC-150)** `[PROVED-MOD]` *((MC-33); `ρ̄` is constant when the class level does not degenerate)*
> Assume:
> - IH, `a ≁ b`, `δ₂ = 3` (FG and case A, modulo JJ at `G″` and `(G″)_{ab}`), and `δ ∈ {3, 4}`;
> - the classes of `G′` are rigid at `X₀(G′)`'s generic point ((MC-102): (MC-68)(d) with (MC-70),
>   or in 𝒮 the count of (MC-146) applied inside `G′`).
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
   rank-`δ` bundle, and `ρ̄(z₁) = lim_{s→0} ρ(z(s)) = ρ_X(z₀)`. This is (MC-109)'s limit, now
   independent of `z₁`.
3. *The bound.* By (MC-109), `dim M_G ≤ 6 + g + dim(ρ̄ ∩ Pen(y₀, σ̄))`, with `ρ̄ ∩ ⟨n⟩ = 0`. Pencils
   through `n` meet `ρ̄` exactly when their tensor `y₀ ⊗ v̄` lies in the image `R̄` of `ρ̄ ∩ n^⊥`
   in `n^⊥/⟨n⟩` ((MC-110)'s proof). If `dim R̄ ≤ 3`, the bad tensors form a fixed proper closed
   subset of the quadric `P¹ × P¹`, a conic or less.
4. *The reachable pairs.* For fixed generic `z₁`, the reachable pairs form the graph of the
   Möbius map `[s₀ : s₁] ↦ [φ₂s₀ : −φ₁s₁]`, where `θ = [φ₁(z₁) : φ₂(z₁)]` ((MC-108)). Under FG, `θ`
   takes cofinitely many values on the generic `z₁`. Infinitely many distinct irreducible
   curves cannot all lie in the fixed curve. So some reachable pair avoids it, and
   `dim M_G = 6 + g = 6 + def₃(G)`.
5. *The two values of `δ`.* `dim R̄ = dim(ρ̄ ∩ n^⊥) ≤ 3` holds automatically at `δ = 3`. At
   `δ = 4` it is `ρ̄ ⊄ n^⊥`. ∎

> **(MC-151)** `[PROVED-MOD]` *((MC-33); the path case)* In (MC-150)'s setting, let the minimiser `X`
> be a path `A = R₀ − ⋯ − R_δ = B` with bridges `L_j = p_{u_j} ∧ p_{v_j}`. Then (i) is automatic,
> since a tree of bodies is independent. (ii) says `L₁(z₀), …, L_δ(z₀)` are independent, and then
> `ρ_X(z₀) = ⟨L_j(z₀)⟩`.
> - **(a) `δ = 3`: `X₀(G)` attains, for every `G′` satisfying (H)** (with (MC-102)'s class rigidity).
> - **(b) `δ = 4`: `X₀(G)` attains if the folded flexes of the ring `G″[∪X]` extend to `F(G″, q)`.**
>   They do when `∪X = V(G′)` (Case II-tree), or when `∪X` is additive in `G″` with simple
>   quotient ((MC-68)(d) at `G″`). **In 𝒮 the latter always holds**: by (★) with `c(X) = δ`,
>   `5(e(Z) + e(Z, X)) ≤ 6|Z|`, and `G″` satisfies (S) because `δ₂ = 3`.

*Proof.* Both conditions below are open on `L_{G″}(q)`, so it suffices to exhibit one point of
`L_{G″}(q)` where they hold.

**(a).** Take the flat point `z = 0 ∈ L_{G″}(q)`. The `L_j(0)` are the three lines of `Π` over
`ℓ_j = q_{u_j}q_{v_j}`. They are independent in `Λ²Π` iff the `ℓ_j` are not concurrent. At generic
`q` they are not concurrent: concurrency is forced only by a common vertex, and three consecutive
bridges touch four distinct classes. Then (MC-150) applies.

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
  which is excluded. So `L₂ ∉ n^⊥`, `ρ_X ⊄ n^⊥` at the generic `z₀`, and (MC-150) applies. ∎

> **(MC-152)** `[MEASURED]` *(`foldcheck.py`; exact)* At the folded point:
> - `L₁` and `L_δ` meet `n`, as the plane `σ₀` (resp. `σ_δ`) forces; the middle bridges do not;
> - rank `(L_j) = δ` and rank `(L_j, n) = δ + 1`, at all six Case II-tree instances of
>   `ringprobe.py`;
> - at `δ = 3`, the flat point also gives rank 3.

> **(MC-153)** `[PROVED-MOD]` *((MC-33); `a′(z₀)` counts class-level stresses)* Let `G ∈ 𝒮`, with
> `δ₂ = 3` and `δ ≥ 2`. Every class of `G′` is additive in `G″` with simple quotient: this is the
> piece bound with (★) in `G″`, the edge `ab` costing at most 1. So every class is rigid at `z₀`, by
> (MC-68)(d) at `G″` and IH. Hence **`M_{G′}(z₀)` is the class-level motion space**, and
>
>   **`a′(z₀)` = the dimension of the class-level self-stresses of `G′` at `z₀`.**
>
> Two conditions each force `a′(z₀) = 0`, and then (MC-150)(i) holds for `X = Γ₃`:
> - **(a)** `Γ₃` is a forest (then Case II is Case II-tree);
> - **(b)** the union `∪K` of the classes of `Γ₃`'s 2-core is proper, additive in `G″`, and has a
>   simple quotient, **and `A` or `B` lies outside `K`**. Restriction then makes `z₀|_{∪K}`
>   generic for `G″[∪K] = G′[∪K]`, which attains by IH. Class-level independence on `K` follows,
>   and pendant trees carry no stress.
>
> So **(MC-118)'s `a′(z₀) = 0` holds in 𝒮 (at `δ₂ = 3`) whenever `Γ₃` is a forest or (b) holds.**
> Examples of (b): the unicyclic shapes with `p + p′ ≥ 2`. At `δ = 3` this closes Case II-cyclic
> for them, via (MC-150). (ii) holds in Case II because `G″` is rigid at `z₀` (IH), and welded
> motions are `G″`-motions.

*Coordinator's check and repair.*
- *The edge `ab`.* The "at most 1" uses `δ ≥ 2`: when `A, B ∈ {X} ∪ Z`, `c({X} ∪ Z) ≥ δ ≥ 2` in
  `G′`, so `e_{G″}(Z) + e_{G″}(Z, X) ≤ (6|Z| + 3)/5`, which is `≤ 3|Z|/2` for `|Z| ≥ 2` and `≤ 1`
  for `|Z| = 1`. Otherwise rigid-freeness bounds the `G′` count as in (MC-146), and `ab` adds
  nothing. (S) in `G″` follows from `δ₂ = 3`: by (MC-90), every `Y ∋ a, b` has
  `3(|Y| − 1) − 2e_{G′}(Y) ≥ 3`, since (S) makes the singleton partition `def₂`-optimal.
- *(b)'s last clause is added here.* The draft's restriction step reads `G″[∪K]` as `G′[∪K]`, which
  needs `ab ⊄ ∪K`. In Case II, the only place (MC-153) is used, the clause is automatic: if `∪K`
  is proper, `Γ₃` has a leaf outside `K`, and every leaf is `A` or `B` ((MC-145)(iii)).

> **(MC-154)** `[OPEN]` *(the residue: Case II-cyclic at `y` itself)* In 𝒮, the ear step at a `k = 1`
> chain `y` with `δ ∈ {3, 4}` is proved except in two situations:
> - Case II-cyclic, where the class-level framework of `G′` carries a self-stress at the generic
>   point of `X₀(G″)`. This is `a′(z₀) ≥ 1`, possible only where (MC-153)(b) fails:
>   - the pendant-free ring `L = 10`, arcs `(5,5)`;
>   - the one-pendant shapes `L = 8`, arcs `(4,4)` and `L = 9`, arcs `(4,5)`;
>   - multicyclic `Γ₃`.
> - At `δ = 4`, any Case II-cyclic shape with `ρ_Γ(z₀) ⊆ n^⊥`.
>
> **This residue is not needed for coverage** (MC-148). Outside 𝒮, the cyclic class structures and
> the `δ = 4` path case without additivity remain as in (MC-117) and (MC-103).

*Where a proof would come from.* A sketch by the author, not checked; the stop rule fires here:
pendant-free rings, one-pendant shapes and multicyclic shapes each need their own argument. For the
`(5,5)` ring:
- Each arc plus `A − B` is a rigid 6-ring that is additive in `G″`. Restriction and IH make each
  arc's five lines, together with `n`, independent at `z₀`.
- A stress means the two arc hyperplanes `H₁ = span(arc₁)` and `H₂ = span(arc₂)` coincide.
- `F(G″) = F(S₁) ×_{F(A∪B)} F(S₂)`, since flex conditions are edge-local. So with `A`, `B` fixed,
  the two arcs vary independently.
- `H₁ = H₂` would force `H₁` to be constant on its fibre. A dual argument on the fibre's folded
  points refutes that: `L₃*` would sweep a whole star, which forces a special complex whose axis
  contains three independent points at infinity.
- The `n^⊥` condition at `δ = 4` needs a further step that the author did not find.

> **(MC-155)** `[MEASURED]` *(`ringprobe.py`, `cycprobe.py`, `findcyc.py`; exact chord point, one draw
> each)* Every Case II-cyclic instance tested is certified by (MC-150). Each has:
> - class-level `G′` independent at `z₀` (an open condition, so a certificate);
> - `ρ̄(z₁) = ρ_Γ(z₀)` at two `z₁`;
> - `dim(ρ_Γ(z₀) ∩ n^⊥) = δ − 1`;
> - `a′ = 0`, and `X₀(G)` attaining.
>
> The instances:
> - all 6 Case II-cyclic chains of 𝒮 on ≤ 13 vertices (`findcyc.py`; none on ≤ 12, by (MC-156)): 4 of
>   shape `L = 7, (3,4)`, `p + p′ = 2`, which (MC-153)(b) covers, and 2 of shape `L = 8, (4,4)`,
>   `p + p′ = 1`;
> - 5 constructed rings `C₁₀` of classes with `A`, `B` antipodal, `δ = 4`. They carry 0, 1 (two
>   placements), 2 or 4 `C₄` blobs; the blob-free one is the θ-graph `θ(2,5,5)`, so it is not in 𝒮.
>
> The constructed `C₉` rings with `A`, `B` at distance `(4,5)` (`δ = 3`) are **Case I**, not Case II.
> Their 4-arc together with `y` is a rigid, proper, additive 6-ring (a locally minimal `Y` with
> `c = 4 > δ`), which illustrates (MC-144).

**Part III — measurements (exact partition counts).**

> **(MC-156)** `[MEASURED]` *(`earcover.py --hunt`, `blobcount.py`, `cellclasses.py --exh 8`; exact
> partition counts)* Every biconnected, triangle-free graph with minimum degree `≥ 2` and
> `2m ≤ 3n − 4` on 9–13 vertices (from `geng -C -d2 -t -q n 0:⌊(3n−4)/2⌋`, nauty 2.9.3) was run. Its
> 𝒮-members are 35 / 304 / 879 / 9 030 / 32 177, matching (MC-83)'s count.
> - Every one has a chain in USABLE, A′ or C′-I.
> - Every C′-I witness `W_Y` is asserted rigid, with simple quotient, additive, and of minimum
>   degree `≥ 2`.
> - At every C′-II chain, (MC-145)(i) and the rigidity of `G` are asserted.
> - At every (c′) chain, `δ = min c(Y)` ((MC-79)(i)) is asserted (added at landing).
>
> The chain-cell counts over all chains:
>
> | `n` | C′-I | C′-II-tree | C′-II-cyclic | A′ | time |
> |---|---|---|---|---|---|
> | 9 | 0 | 3 | 0 | 0 | 0.2 s |
> | 10 | 0 | 10 | 0 | 0 | 0.3 s |
> | 11 | 52 | 58 | 0 | 0 | 0.8 s |
> | 12 | 135 | 233 | 0 | 12 | 8 s |
> | 13 | 937 | 1 676 | **6** (`δ = 3`) | 20 | 33 s |
>
> (MC-147) and (MC-146) are asserted by `blobcount.py` at:
> - every 𝒮 member on 11–13 vertices whose chains all have `k = 1`: 54 / 1 370 / 1 919 members,
>   297 chains with `δ ≥ 1`, 595 blobs;
> - the eight `k = 1` necklaces: 101 chains, 431 blobs.
>
> On ≤ 8 vertices there is no `k = 1` chain with hub ends and `(δ₂, δ) ∈ {(3,3), (3,4)}`
> (`cellclasses.py --exh 8`: 0). Step MC17's 53 and 16 split-off instances there ((MC-103)) have an
> end of degree 2, so `G′` fails (H).

*What the hunt does and does not test.* Every 𝒮 member on 9–13 vertices already has a **usable**
chain: `earcover.py` prints no "no usable chain" line there, in line with (MC-83) (the smallest
stuck member is `QsQsQ`, on 14 vertices). So the hunt tests (MC-142)'s witnesses, the dichotomy
(MC-145) and (MC-79)(i) at every (c′) chain, not (MC-148) itself. (MC-148)'s combinatorial content is
exercised by the twelve stuck necklaces (MC-149) and by `blobcount.py`'s assertions of (MC-147).

**What would change this.**
- A 𝒮-member with no chain in USABLE, A′ or C′-I. That would be an arithmetic error in (MC-146) or
  (MC-147). `earcover.py` and `blobcount.py` assert against it.
- A C′-I witness that fails rigidity, simplicity or additivity (asserted).
- A `k = 1` chain in 𝒮, inside a proper additive rigid `W` with simple quotient, where `X₀(G)` falls
  short. That would refute (MC-68)(d), (MC-44), or the IH bookkeeping of (MC-143).
- A Case II-tree instance whose generic chord point has dependent bridges, or all bridges meeting
  `n` at `δ = 4`. That would refute the folded-pentagon computation (`foldcheck.py`).
- A Case II-cyclic instance with a class-level stress at the generic chord point. That would refute
  (MC-118) there and leave (MC-154) open, without touching (MC-148).

**What was re-derived, and what was taken on trust** (the author's account).
- **Derived here:**
  - (MC-142), (MC-145), (MC-146), (MC-147): pure counts;
  - (MC-143)'s assembly;
  - (MC-150): the reachable-conic argument, redone with a `z₁`-independent `ρ̄`;
  - (MC-151): the flat point, the folded point and the pentagon;
  - (MC-153)'s identification of `a′(z₀)`.
- **Re-derived from their sources:**
  - (MC-16), (MC-17), (MC-77), (MC-79)(ii)/(iii)/(v), and (MC-76)'s singleton optimality;
  - the equivalence "additivity ⟺ singletons optimal in `G/H`" in 𝒮.
- **Re-read and used as stated:**
  - (MC-108), (MC-109), the chord facts, and (MC-111)(d);
  - (MC-44);
  - (MC-99), (MC-102), (MC-105);
  - (MC-68)(d), including (b). This is the one load-bearing citation of the new route. The author
    read its proof but did not re-derive (MC-68)(b)'s degeneration.
- **Taken on trust:**
  - JJ, everywhere flagged;
  - (MC-85) behind (MC-105);
  - the landed steps behind "usable".
- **Not used:** Theorem S (MC-80), (MC-69), (MC-70) (except as an alternative in (MC-144)), (MC-71),
  (MC-87), and Step MC15's `dim U = min(δ₂, 3)`, beyond `≥ 2`.

**Drivers** (all at `PYTHONHASHSEED=0` from the repository root, seed `20260924`; exact except the
mod-`2⁶¹ − 1` attainment screens, which are certificates). Every figure was re-run at landing and
reproduced, except the two corrected `inS` entries below.

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/earcover.py --necklaces` | (MC-149): the 15 necklaces, 12 of them stuck, each with a closable chain | ~20 s |
| `geng -C -d2 -t -q n 0:⌊(3n−4)/2⌋ \| python3 notes/scripts/w4/earcover.py --hunt - --full`, `n = 9..13` | (MC-156)'s table | 0.2–33 s |
| `python3 notes/scripts/w4/blobcount.py --necklaces`; the same with `geng` input for `n = 11..13` | (MC-156): (MC-147), (MC-146) asserted | 8 s; < 1 min |
| `python3 notes/scripts/w4/rigidclose.py` | (MC-149): (MC-143)'s mechanism at `QsQsQ`, `QsQsQs`, `TsTsTs` | ~1 s |
| `python3 notes/scripts/w4/ringprobe.py` | (MC-155): 15 built instances (Case II-tree, Case II-cyclic, Case I): chord point, class level, `ρ̄`, truth | ~85 s |
| `python3 notes/scripts/w4/foldcheck.py` | (MC-152): the folded point at the six Case II-tree instances | < 1 s |
| `geng -C -d2 -t -q 13 0:17 \| python3 notes/scripts/w4/findcyc.py` | (MC-155): the six Case II-cyclic chains on 13 vertices | < 1 min |
| `python3 notes/scripts/w4/cycprobe.py` | (MC-155): the six probed | ~2 s |
| `python3 notes/scripts/w4/cellclasses.py --exh 8` | (MC-156): none on ≤ 8 vertices | < 1 min |

*Changes at landing.* The staged `ringprobe.py` took 𝒮-membership from a helper that tested (S) and
2-connectivity but did not exclude cycles and θ-graphs. The landed driver uses
`coverstruct.in_class_S`, which moves `Y4:C10(v)` (`θ(2,5,5)`) and `Y3:C9(v)` (`θ(2,4,5)`) to
`inS: False`; nothing else moves, and no claim used the column. `earcover.py`'s (MC-79)(i) assertion
is new and holds everywhere.


