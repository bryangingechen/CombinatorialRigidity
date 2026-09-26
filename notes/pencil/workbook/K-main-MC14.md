## §(K-main) — Step MC14 — which graphs the `X₀` induction reaches (W4-reopen P1, step 4)

#### Step MC14 — which graphs the `X₀` induction reaches (W4-reopen P1, step 4)

*Worked 2026-09-24 by a forked agent, as step 4 of W4-reopen P1's later 2026-09-24 plan. Driver
`w4/x0arms.py` (new). It replaces four scratch probes of the feasibility recon of W4-reopen's
third unranked direction (the `X₀` hybrid): a first-arm classifier, a recursion, a necklace check
and a gluing check. The question: take an induction on `|V|` whose motive is (MC-10)(a),
"`X₀(G)`'s generic point attains `6(|V| − 1) − def₃(G)`". Which graphs does it reach, using the
landed steps and the lemmas proved here? Every `PROVED` claim below was derived by that agent end
to end. None has had a second reader. **Coverage is measured here, not proved:** there is no theorem
that every graph is covered ((MC-61)).*

**Covered.** A graph `G` satisfying (H) is **covered** if some step below applies at `G` and every
graph the step consumes is covered.
- Every step consumes graphs with fewer vertices (MC-55)(i). So "covered" is well defined by strong
  induction on `|V|`, and it does not depend on the order in which steps are tried.
- The driver reports the *first* covering step in the order of the table.
- Two switches: `--ear23 antecedent` turns on Step MC13's cells; `--delta0 off` drops (MC-54).
  The default is `--ear23 none --delta0 on`.

| step | claim | consumes | applicability |
|---|---|---|---|
| BASE | (MC-21)(a): `G` a cycle | — | structural |
| THETA | (MC-21)(b): `G` a θ-graph | — | structural |
| CUT | (MC-52): a cut vertex | the two pieces | structural |
| BRIDGE | (MC-53): a chain of bridges | the two pieces | structural |
| EAR, closed or open `k ≥ 5` | (MC-20) | `G′` | structural |
| EAR, open `k = 4` | (MC-24), (MC-25) | `G′`, `G′ + ear₂` | structural |
| EAR, open `k = 3` (`--ear23`) | (MC-45), every orbit | `G′`, `G′ + ear₂` | structural |
| EAR, open `k = 2` (`--ear23`) | (MC-46): orbit (i) or (ii), `dim U ≠ 1` | `G′`, `G′ + ear₁` | `dim U ≥ 2` certified at `q ∈ U(G′)` |
| SPLITOFF | (MC-31): `δ ≥ 5` | `G″ = G′ + ab` | structural, plus JJ at `G″` |
| FLAT | (MC-5)(ii): `def₂ = def₃` | — | structural, plus JJ at `G` |
| EAR, open `k = 2, 3` at `δ = 0` | (MC-54) | `G′` | structural |
| EAR, open `k = 1` at `δ = 0` | (MC-54) | `G′` | `dim U ≥ 2` certified at `q ∈ U(G′)` |
| EAR, open `k = 2`, orbit (iv) (`--ear23`) | (MC-47)(i), modulo JJ | `G′` | `δ₂ = 0` (combinatorial) |
| CONTRACT | (MC-39) | `H = G[W]`, `G/H` | structural (`W`, `G/H` simple), plus (i) and (ii) certified at one exact picture |

- **JJ at `G`** is the equality `ℓ₀(G) = 3 + def₂(G)`. It is Jackson–Jordán's theorem in
  characteristic 0, and (MC-33) beyond. The driver does not cite it: it **exhibits** one admissible
  `q` with `dim L(q) = 3 + def₂` at every graph where a step needs it. Such a `q` lies in `U`, so on
  the tested graphs no step uses the citation. A class statement built from these steps does.
- **The flag orbit and `dim U`** are read in exact ℚ over the whole fibre `L(q)`, at up to three
  pictures `q` certified in `U(G′)`. "`p_b ∉ π_a`", "`p_a ∉ π_b`" and "`dim U ≥ d`" are open
  conditions on the irreducible `B(G′)`. So what one certified `q` shows holds at `X₀(G′)`'s generic
  point, and conditions shown at different `q` combine. `dim U ≥ 2` also excludes orbits (iii) and
  (iv). This is the coordinator's "read at an attaining draw", in fibre form: attainment of `G′` is
  not needed for it; the induction supplies that separately.
- **Orbit (iv)** is recognised by `δ₂ := def₂(G′) − def₂(G′/ab) = 0`, that is, `a` and `b` lie in a
  common `def₂`-rigid subgraph ((MC-13)(b)'s argument, which does not use `a ∼ b`). That gives
  `U = 0` modulo JJ.
- **(MC-44)** is not a step. Where `a ≁ b`, it supplies `(R_k)` from the chord gadget and so
  removes (MC-24)'s dominance requirement for `(R₁)`, `(R₂)`. (MC-49) uses it; the table
  records the conditions as landed. *(Repaired 2026-09-26, ORBIT recon: this said "(MC-46) and
  (MC-49) use it". (MC-46)'s ear step (Step MC13) takes `(R₁)` from (MC-22) at the antecedent
  `G′ + ear₁`, not from (MC-44), and (MC-44) is not in (MC-89)'s tree (Step MC20, Part I).)*

> **(MC-52)** `[PROVED]` *(a cut vertex; the hybrid recon's "Aff-gauge fibre product", re-derived)*
> Let `G = G₁ ∪ G₂` with `V(G₁) ∩ V(G₂) = {v}` and disjoint edge sets, where `G₁` and `G₂` satisfy
> (H). Then:
> **(i)** `def₂` and `def₃` add: `def(G) = def(G₁) + def(G₂)`. Hence `tgt(G) = tgt(G₁) + tgt(G₂)`.
> **(ii)** At every configuration with adjacent points distinct, over any field,
> `rank R_G = rank R_{G₁} + rank R_{G₂}`.
> **(iii)** At every `q` admissible for `G₁` and `G₂`, `L_G(q)` is the set of pairs
> `(z¹, z²) ∈ L_{G₁} × L_{G₂}` whose planes at `v` coincide. So
> `dim L_G(q) = dim L_{G₁} + dim L_{G₂} − 3`, and both restriction maps `L_G(q) → L_{Gᵢ}` are onto.
> **(iv)** `X₀(G)` attains **iff** `X₀(G₁)` and `X₀(G₂)` attain.

*Proof.* Write `val(𝒫) = D(|𝒫| − 1) − (D − 1)d(𝒫)`, with `D = 3` for `def₂` and `D = 6` for `def₃`.
- (i) Restrict a partition `𝒫` of `V` to `𝒫ᵢ` on `V(Gᵢ)`. Every edge lies in one `Gᵢ`, and it
  crosses `𝒫` iff it crosses `𝒫ᵢ`, so `d(𝒫) = d(𝒫₁) + d(𝒫₂)`. A part meeting both sides is counted
  twice, and `v`'s part does, so `|𝒫| − 1 ≤ (|𝒫₁| − 1) + (|𝒫₂| − 1)`. Hence
  `val(𝒫) ≤ val(𝒫₁) + val(𝒫₂)`. Conversely, two partitions glued along `v`'s parts give equality.
- (ii) A motion of `G` is a pair of motions of `G₁` and `G₂` that agree at `v`. Evaluation at `v`
  maps each motion space onto `K⁶` (constant motions), so `dim M_G = dim M_{G₁} + dim M_{G₂} − 6`.
  Then use `rank R = 6|V| − dim M` and `|V| = |V₁| + |V₂| − 1`. Nothing divides.
- (iii) Only `v`'s condition changes. `N_G[v] = N₁[v] ∪ N₂[v]`, and each `Nᵢ[v]` has at least 3
  non-collinear points. So `z|N_G[v]` is affine iff the two interpolants `h¹_v`, `h²_v` coincide.
  Given any `z¹ ∈ L_{G₁}` and `z² ∈ L_{G₂}`, put `g := h¹_v − h²_v ∈ Aff`. Then `(z¹, z² + g)` lies in
  `L_G(q)`, since `z²_v + g(q_v) = z¹_v`, and `g` is the only such correction. This gives the
  dimension and ontoness onto `L_{G₁}`, and onto `L_{G₂}` by symmetry.
- (iv) By (iii), the minimum `ℓ₀(G)` is attained where both restrictions of `q` lie in `U(Gᵢ)`.
  There the restriction `B(G) → B(Gᵢ)` is dominant: the planar picture restricts onto an open set,
  and the fibres map onto by (iii). `B(G)` is irreducible, so a nonempty open set of its points maps
  into both of the open sets where `G₁` and `G₂` have their generic ranks. There (ii) and (i) give
  `rank R_G = tgt(G)` iff both pieces attain, since each rank is at most its target. ∎

> **(MC-53)** `[PROVED]` *(a chain of bridges)* Let `G` be `G₁ ⊔ G₂` plus a path
> `a − x₁ − ⋯ − x_k − b` (`k ≥ 0` new vertices), with `a ∈ V(G₁)`, `b ∈ V(G₂)`, where `G₁` and `G₂`
> satisfy (H). Then:
> **(i)** `def(G) = def(G₁) + def(G₂) + (k + 1)`, for `def₂` and for `def₃`. So
> `tgt(G) = tgt(G₁) + tgt(G₂) + 5(k + 1)`.
> **(ii)** At every configuration with adjacent points distinct, over any field,
> `rank R_G = rank R_{G₁} + rank R_{G₂} + 5(k + 1)`.
> **(iii)** At every `q` admissible for `G`, `G₁` and `G₂`,
> `dim L_G(q) = dim L_{G₁} + dim L_{G₂} + c_k`, with `c₀ = −2`, `c₁ = −1`, and `c_k = k − 2` for
> `k ≥ 2`. Both restriction maps are onto.
> **(iv)** `X₀(G)` attains **iff** `X₀(G₁)` and `X₀(G₂)` attain.

*Proof.*
- (i) Take one bridge first, with sides `A` and `B`. For a partition `𝒫`, let `s` be the number of
  parts that meet both sides.
  - If `s ≥ 1`, then `val(𝒫) ≤ val(𝒫_A) + val(𝒫_B) − D(s − 1)`.
  - If `s = 0`, the bridge crosses, and `val(𝒫) = val(𝒫_A) + val(𝒫_B) + D − (D − 1)`.

  So one bridge adds exactly 1. Apply this along the path; each `xᵢ` is a one-vertex side with
  `def = 0`.
- (ii) Choose a motion of `G₁`. Then `X_{x_{i+1}} = X_{x_i} + tᵢ C_i` with `k + 1` free scalars, and
  the last step reaches `b`. The motions of `G₂` with `X_b` prescribed form an affine space of
  dimension `dim M_{G₂} − 6`. So `dim M_G = dim M_{G₁} + dim M_{G₂} + (k + 1) − 6`.
- (iii) The path's vertices have degree 2, so they impose nothing. `a` adds
  `z_{x₁} = h_a(q_{x₁})`, and `b` adds `z_{x_k} = h_b(q_{x_k})`; for `k = 0`, read `x₁ = b` and
  `x_k = a`. Shifting `z²` by `g ∈ Aff` shifts `h_b` by `g`.
  - `k ≥ 2`: the two conditions fix `z_{x₁}` and `z_{x_k}`, and the `k − 2` middle heights are free.
  - `k = 1`: `h_a(q_x) = h_b(q_x)`. This is one condition, met by `g` with `g(q_x)` prescribed.
  - `k = 0`: `z_b = h_a(q_b)` and `z_a = h_b(q_a)`. These are two conditions, met by `g` with
    `g(q_a)` and `g(q_b)` prescribed. That is possible because `q_a ≠ q_b`.

  In each case a suitable `g` exists for every pair `(z¹, z²)`, so both restrictions are onto.
- (iv) As in (MC-52)(iv). ∎

> **(MC-54)** `[PROVED]` *(the short open ear at `δ = 0`: no antecedent, no orbit condition, no
> Jackson–Jordán)* Let `G = G′ + ear_k` be an open ear with `1 ≤ k ≤ 4`, `G′` satisfying (H), and
> `δ = def₃(G′) − def₃(G′/ab) = 0`. For `k = 1` suppose also that `dim U ≥ 2` at `X₀(G′)`'s generic
> point. If `X₀(G′)` attains, then `X₀(G)` attains.

*Proof.* Where `G′` attains, `r ≤ δ = 0` (MC-16). So `ρ = 0`, and (MC-22)'s `(R_k)` and `(P_k)`
hold with nothing to check. (MC-22) needs two more things:
- dominance: (MC-18)(a) for `k ≥ 2`; for `k = 1`, (MC-18)(b) with `dim U ≥ 2`;
- `λ = k + 1`: (MC-19)(b) for `k ≥ 2`, in every orbit. For `k = 1`, `dim U ≥ 2` excludes orbit
  (iii), where `U ⊆ p̂_a^⊥ ∩ p̂_b^⊥ = Kℓ_ab`.

Directly, (MC-16) gives `dim M_G = dim M_{G′} = 6 + def₃(G′)`, and `def₃(G) = def₃(G′)` by
(MC-17). ∎

What this does to (MC-51)'s open cells:
- (a) (`k = 2`, `dim U = 1`, orbits (i)–(iii), including `a ∼ b`) is closed wherever `δ = 0`.
- (b) (`k = 2`, orbit (iv)) is closed wherever `δ = 0`, **without** Jackson–Jordán.
  - (MC-47)(i) needs JJ only to get from `U = 0` to `r = 0`. The step itself needs only `r = 0`,
    and `δ = 0` gives that.
  - `δ = 0` is combinatorial. It holds whenever `δ₂ = 0`, since a common `def₂`-rigid subgraph is
    `def₃`-rigid, and merging it into a maximizing partition gives `def₃(G′/ab) = def₃(G′)`. The
    driver asserts this at every `δ₂ = 0` pair it meets.
- (c) (`k = 1`, `δ ≤ 4`) is closed at `δ = 0` when `dim U ≥ 2`.

(MC-45)'s proof already notes that "at `r = 0` there is nothing to prove". (MC-54) makes that
remark a step, keyed to the combinatorial `δ`. `earante.py --exh 6` finds `r = 0` at all 354 of its
non-adjacent pairs, so on small graphs this is the typical case.

> **(MC-55)** `[PROVED]` *(the induction stays inside (H))*
> **(i)** Every graph a step consumes satisfies (H) and has fewer vertices. In particular, the
> induction never meets a leaf or a disconnected graph.
> **(ii)** Let `G` satisfy (H) and be neither a cycle nor 2-connected. Then CUT or BRIDGE applies,
> with pieces satisfying (H).
> **(iii)** A 3-edge-connected `G` has `def₂(G) = def₃(G) = 0`, so FLAT applies modulo JJ at `G`.
> Hence `def₂ > def₃` forces a 2-edge-cut. So does being 2-connected and uncovered, modulo JJ.
> **(iv)** *(the leaf lemma; not used)* Let `v` be a leaf of `G` whose neighbour `u` has degree
> `≥ 3`, and drop `v`'s own non-collinearity condition from admissibility (`N[v]` has two points).
> Then `L_G(q) ≅ L_{G−v}(q)` by `z_v = h_u(q_v)`, `rank R_G = rank R_{G−v} + 5`, and
> `def(G) = def(G − v) + 1`. So `X₀(G)` attains iff `X₀(G − v)` does.

*Proof.*
- (i) For CUT and BRIDGE, the pieces are as in (ii).
  - EAR requires `G′` to satisfy (H). A closed ear at a hub of degree 3 is therefore excluded; the
    hub's third edge is then a bridge, and BRIDGE applies instead. An open ear's ends are hubs, so
    they keep degree `≥ 2`. The gadgets add a path to `G′`.
  - SPLITOFF: `a ≁ b`, and `a`, `b` keep their degrees.
  - CONTRACT: a rigid `H` has minimum degree `≥ 2` and is connected (Step MC12, notation). `G/H`
    is simple by hypothesis, and `v*` has degree `|δ(W)| ≥ 2` because `G` is 2EC.
  - Sizes: `G′ + ear_{k−1}` and `G″` have `|V| − 1` vertices, and `G/H` has
    `|V| − |W| + 1 ≤ |V| − 2`.
- (ii) `G` has a hub. Suppose it has a bridge. The bridge lies on a maximal chain `P` between hubs
  `h₁ ≠ h₂` (a closed chain lies on a cycle). Removing one edge of `P` disconnects `G` iff `h₁` and
  `h₂` are disconnected in `G − int(P)`, so every edge of `P` is a bridge. `G − int(P)` has two
  components, and each `hᵢ` loses one edge and keeps degree `≥ 2`. If `G` has no bridge but a cut
  vertex `v`, then every component `C` of `G − v` sends `≥ 2` edges to `v`. So `G[C ∪ v]` and
  `G − C` satisfy (H).
- (iii) Take a partition with `p ≥ 2` parts. Each part has `≥ 3` crossing edges, so `2d ≥ 3p` and
  `3(p − 1) − 2d ≤ −3`. Hence `def₂ = 0`, and `def₃ ≤ def₂` (MC-5)(i). *Repair (second reading):*
  this covers "`def₂ > def₃` forces a 2-edge-cut" only for 2EC `G`. If `G` has a bridge, the
  one-bridge lemma of (MC-53)(i), valid for any graph and both `D`, makes `def₂` and `def₃` each the
  sum over the 2-edge-connected components plus the number of bridges. So some component has
  `def₂ > def₃`, is not 3EC, and has a minimal 2-edge-cut, which is one of `G`.
- (iv) `u`'s plane is fixed by `N_{G−v}[u]`, which has `≥ 3` non-collinear points, and it fixes
  `z_v`. Rank and counts are (MC-53)'s one-bridge computations, with `{v}` as one side. ∎

**How the induction treats graphs that fail (H): they never arise**, by (i). For every step it
takes, the driver asserts that each consumed graph is smaller and satisfies (H). The recon's leaf
lemma is (iv), recorded but unused.

> **(MC-56)** `[PROVED]` *(covered graphs attain)* If `G` is covered, then `X₀(G)` attains.

*Proof.* Strong induction on `|V|`. Each step is a proved implication from its consumed graphs. Each
certificate a step uses is exact:
- JJ at a graph: `dim L(q) = 3 + def₂` in exact ℚ, which puts `q` in `U`;
- the flag orbit and `dim U`: exact ℚ at such a `q`;
- (MC-39)'s (i) and (ii): as `coreshrink.py` certifies them, exact ℚ at certified pictures. ∎

A covered graph is therefore proved to attain to exactly the standard of the steps it uses. The
exception is the orbit-(iv) cell (MC-47)(i), which is modulo JJ; it is reported apart and is never
needed below. The 2026-09-24 second reading confirmed (MC-37)–(MC-39), (MC-52)–(MC-55) and the
`a ≁ b` reading of (MC-19)(b), (MC-22), (MC-24), (MC-25); Step MC10's `k ≥ 4` claims have not had
an independent re-derivation beyond that reading. On `≤ 8` vertices, and in every census population, attainment is already certified graph by
graph (MC-7). What the coverage adds there is the **reach of a proof strategy**.

> **(MC-57)** `[MEASURED]` *(`x0arms.py --exh 8`; exhaustive: every simple 2EC graph on ≤ 8
> vertices, 7 980)* **The default steps cover all 7 980, and so do the default steps plus Step MC13's cells.**
> By first covering step:
>
> | | BASE | THETA | CUT | EAR `k = 4` | EAR `k = 3` (MC-45) | FLAT | EAR `δ = 0`, `k = 2, 3` | EAR `δ = 0`, `k = 1` | CONTRACT | uncovered |
> |---|---|---|---|---|---|---|---|---|---|---|
> | `--ear23 none` | 6 | 16 | 319 | 4 | — | 7 568 | 58 | 7 | 2 | 0 |
> | `--ear23 antecedent` | 6 | 16 | 319 | 4 | 40 | 7 568 | 18 | 7 | 2 | 0 |
>
> - The 134 graphs with `def₂ > def₃` are the non-FLAT entries: BASE 5, THETA 13, CUT 45, and every
>   entry to the right of CUT except FLAT.
> - (MC-46) (`k = 2`) never fires here. All 31 of its orbit-(i)–(iii) cells have `dim U = 1` at the
>   certified pictures (14 in (i), 5 in (ii), 12 in (iii)). The remaining 419 show `U = 0`.
>   (MC-47)(i) is never the first covering step.
> - JJ is exhibited at all 7 568 FLAT graphs. Both CONTRACT runs have a `def₂`-rigid core. No graph
>   is without an applicable step.
>
> **Without (MC-54)** (`--delta0 off`, i.e. only landed ear steps):
> - `--ear23 none`: CONTRACT takes 66, and 1 graph is uncovered.
> - `--ear23 antecedent`: EAR `k = 3` takes 40, CONTRACT 26, and the same 1 graph is uncovered.
>
> That graph is `x8_60101824`: the 8-cycle `4 0 5 2 7 3 6 1` with the two antipodal chords `4–7` and
> `5–6`, i.e. `K₄` with the four edges of a 4-cycle subdivided once.
> - It has `def₂ = 1`, `def₃ = 0` and four 2-edge-cuts.
> - **Stuck cell:** all four of its ears are `k = 1`, in (MC-51)(c), at `δ = 0`, orbit (i),
>   `dim U = 2`. (MC-54) closes each, consuming `G′ = θ(2, 3, 3)`.
> - CONTRACT cannot reach it. Every `W` with `G/H` simple is a 5-cycle, with `def₂ = 2 > 1`, so (i)
>   fails (MC-59)(a). (MC-39)'s last sentence (the core rigid at a point of `B(G)`, in place of (i))
>   does cover it (`--contract cert-core`), but with a rank certificate.
> - Of the 76 CONTRACT runs in the `--delta0 off` table, the 10 that failed all have
>   `def₂(H) > def₂(G)`.
>
> **Without CONTRACT** (`--contract off`), uncovered:
>
> | | `--delta0 on` | `--delta0 off` |
> |---|---|---|
> | `--ear23 none` | 2 | 67 |
> | `--ear23 antecedent` | 2 | 27 |
>
> The 27 with only the landed ear cells are stuck in (MC-51)(a) and (c). (MC-54) closes 25 of them at
> `δ = 0`. The 2 that need CONTRACT in any case are:
> - `x8_93131968`: `k = 1` at `δ = 2`, orbit (i), `dim U = 2`, which is (MC-51)(c); and `k = 1` with
>   `a ∼ b`;
> - `x8_218769729`: `k = 2` at `δ = 1`, orbit (i), `dim U = 1`, which is (MC-51)(a); and `k = 1` with
>   `a ∼ b`.

**The hybrid recon's count, re-done.** Its classifier left 48 graphs on `≤ 8` vertices with no
applicable arm (its "REST"). Its step set had no contraction and no θ-class, and its own ear rule
excluded chains with adjacent ends at `k ≤ 4`. Under the steps above (`x0arms.py --round1`):

| | THETA | EAR `k = 4` | EAR `k = 3` | EAR `δ = 0` | CONTRACT | uncovered |
|---|---|---|---|---|---|---|
| default | 6 | 3 | — | 37 | 2 | 0 |
| `--ear23 antecedent` | 6 | 3 | 26 | 11 | 2 | 0 |
| `--delta0 off` | 6 | 3 | — | — | 38 | 1 |
| `--delta0 off --contract off` | 6 | 3 | — | — | — | 39 |

- **The 3 EAR `k = 4` covers are all at chains with adjacent ends.** As landed, (MC-19)(b) holds for
  any flag pair, (MC-22), (MC-24) and (MC-25) carry no `a ≁ b` hypothesis, and (MC-25) is stated in
  all four orbits. (MC-51)'s closing paragraph says the same for `k ≥ 3` with `a ∼ b`. The recon's
  exclusion came from its own ear theorem, which went through `pencilLoss_vertexTwoCut`.
  *Confirmed by the 2026-09-24 second reading:* `a ∼ b` puts the generic flags in orbit (iii) or
  (iv), and each of the four claims covers all four orbits. `w4/earspan.py`, which shares no code
  with `earstep.py`, re-certifies `λ = 3, 4, 5` at `k = 2, 3, 4` and `⋂Λ₄ = 0` in every orbit.
- **The recon's "REST is reached from 887/888 habitat members"** counted a recursion that followed
  **only the first applicable arm** at each graph. So "reached" there did not mean "uncovered". The
  landed figure is (MC-58).
- **The recon's "REST is infinite"** (the `K₄` necklaces) was true of its own step set. CONTRACT
  supersedes it (MC-60).
- **The recon's predicted first failure**, `K₄` with every edge subdivided once, is covered. (MC-54)
  closes it with `k = 1` at `δ = 0`, consuming `θ(2, 4, 4)` (`--tree x10_3584739737600`).

> **(MC-58)** `[MEASURED]` *(`x0arms.py --pool`; the census populations; counts of labelled members)*
>
> | population | members | `--ear23 none` | `--ear23 antecedent` |
> |---|---|---|---|
> | `battery` | 9 | 9 (BASE 3, THETA 3, EAR `k = 4` 1, FLAT 2) | 9 |
> | `thetas` | 109 | 109 (THETA) | 109 |
> | `smark` | 78 | 63 (BASE 15, THETA 18, EAR `k ≥ 5` 3, `k = 4` 22, SPLITOFF 3, `δ = 0` 1, CONTRACT 1) | 78 (… EAR `k = 4` 19, `k = 3` 14, `k = 2` 9) |
> | `habitats` | 888 | 511 (THETA 1, EAR `k = 4` 510) | 888 (THETA 1, EAR `k = 4` 480, `k = 3` 353, `k = 2` 54) |
> | `peels` | 928 | 928 (EAR `k ≥ 5` 320, `k = 4` 304, `δ = 0` 304) | 928 (… EAR `k = 3` 268, `k = 2` 36) |
> | `residuals` | 260 | 208 (EAR `k ≥ 5` 144, `k = 4` 63, CONTRACT 1) | 260 (… EAR `k = 3` 1, `k = 2` 52) |
>
> - With `--delta0 off` the `antecedent` column is unchanged (888, 78, 928, 260).
> - A **terminal** graph is one where no step applies, or where every applicable step fails only a
>   certificate. It is reached from an uncovered member through consumed graphs that are themselves
>   uncovered.
> - Under `--ear23 none`, the uncovered members reach 25 terminal graphs (habitats), 63 (smark) and 1
>   (residuals). Every one has the same profile (the driver's `by structure` line): no applicable
>   step, no proper rigid set, every maximal chain with `k ≤ 3`, `def₃ = 0 < def₂`, and `δ ≤ 4` at
>   every degree-2 vertex.
> - **Stuck cells**, read at the listed terminal graphs: every `k = 2` chain is (MC-46)'s cell
>   (orbit (i), `dim U = 3`); every `k = 3` chain is (MC-45)'s; every `k = 1` chain is (MC-51)(c) at
>   `δ = 2` or `4`. So they are stuck exactly at Step MC13's cells, and `--ear23 antecedent` covers
>   every member.

**So, on everything tested, Step MC13's landed cells together with (MC-54) leave nothing
uncovered** — a measurement on finite populations, not a coverage theorem ((MC-61)). Without (MC-54), exactly one graph is left, and it sits in (MC-51)(c) at `δ = 0`.

> **(MC-59)** *(what hypothesis (i) of (MC-39) can and cannot do, and the flat core)* Let `W` be a
> proper rigid set with `G/H` simple, and let `q ∈ U(G)` with `q|_W ∈ U(H)`.
> **(a)** `[PROVED]` If (i) holds at `q`, then `ℓ₀(H) ≤ ℓ₀(G)`. At certified pictures this reads
> `def₂(H) ≤ def₂(G)`.
> **(b)** `[PROVED]` If `def₂(H) = 0` and `dim L_H(q|_W) = 3`, then (i) holds at `q`.
> **(c)** *(the flat core, `def₂(H) = 0`; three parts since the 2026-09-24 second reading)*
> **(c1)** `[PROVED]` *(no citation)* If `def₂(H) = 0`, then `def₂(G/H) = def₂(G)`.
> **(c2)** `[PROVED]` *(no citation)* At any picture of `coreshrink.py`'s construction with `δ`
> admissible for `H`, `q′` admissible for `G/H` and `dim L_H(δ) = 3`:
> `ker M₀ ≅ L⁰_{G/H}(q′) ⊕ K`, so `dim ker M₀ = dim L_{G/H}(q′)`.
> **(c3)** `[PROVED-MOD]` *((MC-33): Jackson–Jordán at `H` and at `G/H` only; sharpened by the
> 2026-09-24 second reading, which dropped `G`)* If `def₂(H) = 0`, then (ii) holds at a generic
> picture, **and `ℓ₀(G) = 3 + def₂(G)` follows**: Jackson–Jordán at `G` is a consequence, not a
> hypothesis.
> **(d)** `[PROVED-MOD]` *((MC-33): Jackson–Jordán at `H` and `G/H`)* Consequently, **at a
> `def₂`-rigid core, (MC-39) needs no per-graph certificate**. If `X₀(G/H)` attains, then `X₀(G)` attains, because `X₀(H)` attains by
> FLAT.

*Proof.*
- (a) `proj_W L_G(q) ⊆ L_H(q|_W)` always ((MC-38)'s proof), and its dimension is at most
  `dim L_G(q) = ℓ₀(G)`.
- (b) `Aff(q) ⊆ L_G(q)` projects onto `Aff(q|_W)`. That space is 3-dimensional because `q|_W` is
  not collinear, and it equals `L_H(q|_W)`, which has dimension 3.
- (c1) Merge the parts meeting `W` in a `def₂`-maximizing partition. This is (MC-35)'s proof with
  `(3, 2)` for `(6, 5)`.
- (c2) Read off the five row types of `M₀` (listed after (MC-37)'s proof).
  - The core rows say that `ζ` lies in `L_H(δ)`, with the core plane slopes `a_c`. When
    `dim L_H(δ) = 3`, that space is `Aff(δ)`: `ζ = a*·δ + γ`, every `a_c = a*`, and every
    `γ̃_c = γ`.
  - The rows "`π_c(0)` contains `A_c`" then say that every attachment lies on the plane
    `z = a*·(x, y)` through `P`. That is exactly `G/H`'s condition at `v*`, with `v*` at height 0.
  - The attachment rows say that each `π_u` passes through `P`. That is `G/H`'s condition at `u`,
    since `v* ∈ N_{G/H}[u]`. Each attachment's `γ̃_u` appears in one row only (`G/H` is simple), and
    that row fixes it.
  - The far rows are unchanged.

  So the outside data range over `L⁰_{G/H}(q′)`, the slope `a*` is fixed by them (`N_{G/H}[v*]` is
  not collinear), and `γ` is free. Given `(z_O, γ)`, every other unknown is determined.
  `dim L⁰ = dim L_{G/H}(q′) − 1`, since the constants have `z_{v*} ≠ 0`.
- (c3) Take a generic picture: `dim L_H(δ) = ℓ₀(H) = 3` (JJ at `H`), `q′ ∈ U(G/H)` (the translation
  argument after (MC-37)'s proof), and `q(t) ∈ U(G)` for cofinitely many `t`. Then
  `ℓ₀(G) = dim W₀ ≤ dim ker M₀ = ℓ₀(G/H)`, by `W₀ ⊆ ker M₀` and (c2), with no citation. And
  `ℓ₀(G/H) = 3 + def₂(G/H) = 3 + def₂(G) ≤ ℓ₀(G)`, by JJ at `G/H`, (c1) and the elementary
  (MC-4)(b) at `G`. So every inequality is an equality: `dim ker M₀ = ℓ₀(G)`, which is (ii), and
  `ℓ₀(G) = 3 + def₂(G)`. JJ at `G` alone would not do: it bounds `ℓ₀(G/H)` from the same side as
  the degeneration does. The hard direction is needed at `G/H`.
- (d) (b) gives (i), and (c3) gives (ii). FLAT at `H` (`def₂ = def₃ = 0`) gives `X₀(H)`. JJ at `H`
  is used three times: for (b) at a generic picture, for (c2) at a generic `δ`, and for FLAT at `H`. ∎

`[MEASURED x0arms.py --flatcore 8]` The kernel identity of (c2) is asserted exactly at 2 080
pictures. That is one per graph: the largest `def₂`-rigid `W` with `G/H` simple. The graphs are
every simple 2EC graph on `≤ 8` vertices that has such a `W`, plus `N(3..6)`: 2 083 graphs, 3 skipped
because the drawn `δ` was not in `U(H)`. Also asserted at all 2 080: the count
`def₂(G) = def₂(G/H)`, and no jump. JJ was exhibited at both `G` and `G/H` in every case.

> **(MC-60)** *(the `K₄` necklaces)* `N(k)` is `k` copies of `K₄` in a cycle, with bead `i`'s vertex
> 1 joined to bead `i + 1`'s vertex 0. It has minimum degree 3 and 2-edge-cuts, and
> `def₂ = k − 3`, `def₃ = max(0, k − 6)` (asserted).
> **(a)** `[CONSTRUCTED]` *(`x0arms.py --necklace 8`)* For `k = 3..8`, `N(k)` is covered: `N(3)` by
> FLAT, and `N(4..8)` by CONTRACT, with (i) and (ii) certified at every bead. `X₀(N(k))` attains at
> each: `maincomp.census` gives ranks 66/66, 90/90, 114/114, 138/138, 161/161 and 184/184.
> **(b)** `[PROVED]` *(no citation since the 2026-09-24 second reading, via (MC-59)(c3); first
> written modulo Jackson–Jordán)* **Every `N(k)`, `k ≥ 3`, attains on `X₀`.**

*Proof of (b).* Call a *unit cycle* a cycle of `j ≥ 3` units, each a `K₄` bead or a single vertex,
with consecutive units joined by one edge and a bead's two outside edges at distinct bead vertices.
- A unit cycle is 2EC and satisfies (H).
- A bead `W` in it is a proper `def₂`-rigid set.
- `G/H` is simple: the bead's two outside neighbours lie in the two adjacent units, which are
  distinct since `j ≥ 3`.
- `G/H` is again a unit cycle, with one fewer bead.

Induct on the number of beads, with the **strengthened motive** "`X₀(Γ)` attains **and**
`ℓ₀(Γ) = 3 + def₂(Γ)`" (the second reader's device).
- *Base.* `C_j` has no hubs, so `L = K^V` and `ℓ₀ = j = 3 + def₂(C_j)`; `X₀` attains by (MC-21)(a).
- *Step.* `L_{K₄}(q) = Aff(q)` at every admissible `q`, since every `N[v]` is all of `V(K₄)`. So JJ at
  the bead holds outright, and so does FLAT there (flat rank `24 − 6 = 18`). The induction
  hypothesis at the smaller unit cycle `G/H` gives both halves of the motive there. Then (MC-59)(b)
  gives (i), (MC-59)(c3) gives (ii) **and** `ℓ₀(G) = 3 + def₂(G)`, and (MC-39) gives attainment.

After `k` contractions we reach `C_k`. No step cites Jackson–Jordán. ∎

It is the corpus's first infinite family of minimum degree 3 shown to attain on `X₀`, to the
standard of (MC-19)(a)'s certificates, (MC-39) and (MC-59)(b), (c1)–(c3).

*Remark (the second reader's, not itself second-read): the equality `ℓ₀ = 3 + def₂` propagates.*
`[INFORMAL]` *(gap: SPLITOFF not checked; no second reader)* It passes from the consumed graphs to
`G` through CUT and BRIDGE ((MC-52)(iii), (MC-53)(iii) with the matching deficiency sums), EAR with
`k ≥ 2` (`ℓ₀` and `def₂` both rise by `k − 2`), EAR with `k = 1` and `U ≠ 0` (both fall by one,
since (MC-4)(b) at `G` forces `δ₂ ≥ 1`), and CONTRACT at a `def₂`-rigid core ((MC-59)(c3)). So under
the strengthened motive of (MC-60)(b)'s proof the citation is consumed only at FLAT (where `G`
itself is not consumed), at (MC-47)(i), and wherever SPLITOFF fails to propagate. FLAT covers most
small graphs (7 568 of 7 980 in (MC-57)), so this does not remove the citation from the strategy.
It says where a proof of Jackson–Jordán by the same induction would have to do its work. The hybrid recon's "REST is infinite" was an artifact
of a step set with no contraction.

> **(MC-61)** `[OPEN]` *(the coverage theorem — not proved)* **Coverage is measured, not proved.**
> (MC-57) is exhaustive only on ≤ 8 vertices, and those graphs were already certified to attain
> directly (MC-7). (MC-58) is sampled populations. The one infinite family proved is the `K₄`
> necklaces (MC-60), with no citation. By (MC-56), a theorem that **every** simple 2EC graph
> satisfying (H) is covered would prove (MC-10)(a) by this strategy. So the coverage theorem is the
> whole remaining problem here, not a side item. It has two halves, both open:
> - **The structural half:** that every such graph admits some step (a cut vertex, a bridge
>   chain, a usable ear, a split-off at `δ ≥ 5`, `def₂ = def₃`, or a proper rigid `W` with `G/H`
>   simple). There is no theorem. The candidate gaps are graphs with a proper rigid set but none with
>   a simple quotient (Katoh–Tanigawa's Lemma 6.5 case) and 2-edge-cut graphs with no degree-2 chain.
>   (MC-55)(iii) shows only that `def₂ > def₃` forces a 2-edge-cut.
> - **The certificate half:** that each step's per-graph conditions hold in general, where the
>   driver checks them at one exact picture per graph:
>   - Jackson–Jordán's equality, wherever FLAT or SPLITOFF is used, and at `H` and `G/H` where
>     (MC-59)(d) is used;
>   - `dim U ≥ 2` (and the orbit) for (MC-46), and for (MC-54) at `k = 1`;
>   - (MC-39)'s (i) and (ii) at a core with `def₂(H) > 0` ((MC-41)'s (∂1), (∂2)); (MC-59) settles
>     the `def₂`-rigid case modulo Jackson–Jordán, and (MC-59)(a) shows (i) impossible when
>     `def₂(H) > def₂(G)`;
>   - and the ear cells that are not steps at all: (MC-51)(a) and (c) at `δ ≥ 1`, and (b) where
>     Jackson–Jordán is not assumed.
>
> *(2026-09-24, Step MC15: modulo Jackson–Jordán, the `dim U`/orbit certificates and (MC-39)'s (i)
> and (ii) are partition counts, (MC-72) and (MC-71). What is left of the certificate half is
> Jackson–Jordán itself and the ear cells (MC-51)(a), (c) at `δ ≥ 1`.)*
>
> *(2026-09-24, Step MC16: both halves are claimed closed modulo Jackson–Jordán, (MC-89), with no
> ear cell needed: the structural half by (MC-75), (MC-76), (MC-80); the remaining certificates by
> (MC-87) with (MC-71). Second-read 2026-09-24.)*
>
> What was tested: with the default steps and `--ear23 antecedent`, nothing is uncovered — 7 980 /
> 7 980 on `≤ 8` vertices and every member of every population. Without (MC-54), one graph
> (`x8_60101824`) is uncovered, stuck in (MC-51)(c) at `δ = 0`; with `--ear23 none`, the uncovered pool
> members are stuck at (MC-45)/(MC-46), which have landed. The 2 graphs of (MC-57) that need
> CONTRACT are the tested instances of (MC-51)(a)/(c) at `δ ≥ 1`. The stop rule (more than 3
> structurally distinct failures, or a graph with no candidate step) does not fire on the tested
> populations. The deferred adversarial census (`n = 9–14`) is the natural test of the structural half.

**What would change this.**
- A consumed graph that is not smaller, or that fails (H). The driver asserts both.
- A covered graph where `X₀` falls short. A `maincomp.py` SHORT at a covered member would refute
  the step it used.
- A glued instance failing an (MC-52) or (MC-53) identity (`--lemmas` asserts them).
- A pair with `δ₂ = 0` and `δ > 0` (asserted never to occur).
- A `def₂`-rigid core where `dim ker M₀ ≠ dim L_{G/H}(q′)`, or where (ii) fails with JJ exhibited at
  `G` and `G/H` (`--flatcore` asserts both).
- A structural class of uncovered graphs in a larger population. The adversarial census of P1's
  first hand-off (`n = 9–14`) is the natural place to look.

**Driver** (all at `PYTHONHASHSEED=0`, seed `20260924`; certificates in exact ℚ, ranks mod
`2⁶¹ − 1` only as certificates; sampler support in the docstring; re-runs byte-identical apart from
the timing lines, checked on `--exh 7` and `--pool habitats`):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/x0arms.py --lemmas` | cut vertex 21/21, bridge path (`k = 0..3`) 84/84, leaf 6/6 glued instances; every identity asserted | 4 s |
| `python3 notes/scripts/w4/x0arms.py --exh 7` | 577/577 covered | 2 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8` / `--ear23 antecedent` | 7 980/7 980 covered ((MC-57)'s table) | 17 s / 20 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8 --delta0 off` / `--ear23 antecedent --delta0 off` | 1 uncovered, `x8_60101824`, in (MC-51)(c) at `δ = 0` | 24 s / 23 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8 --contract off` (with `--ear23 antecedent`, `--delta0 off`) | 2 / 2 / 67 / 27 uncovered, each with its cells | 17–20 s |
| `python3 notes/scripts/w4/x0arms.py --exh 8 --contract cert-core --delta0 off` | CONTRACT 66, CONTRACT* 1 (`x8_60101824`), 0 uncovered | 27 s |
| `python3 notes/scripts/w4/x0arms.py --round1` (and `--ear23 antecedent`, `--delta0 off`, `--delta0 off --contract off`) | the recon's 48: 0 / 0 / 1 / 39 uncovered | ≤ 6 s |
| `python3 notes/scripts/w4/x0arms.py --pool habitats` (and `--ear23 antecedent`, each with `--delta0 off`) | 511 / 888; 25 terminal graphs under `none` | 3–9 s |
| `python3 notes/scripts/w4/x0arms.py --pool battery,thetas,smark` (and `--ear23 antecedent [--delta0 off]`) | 9, 109, 63 / 9, 109, 78 | 9 s / 2 s / 6 s |
| `python3 notes/scripts/w4/x0arms.py --pool peels,residuals` (and `--ear23 antecedent [--delta0 off]`) | 928, 208 / 928, 260 | 51 s / 56 s / 142 s |
| `python3 notes/scripts/w4/x0arms.py --necklace 8` (and `--ear23 antecedent`) | `N(3..8)` covered, `X₀` attains at each | 18 s / 15 s |
| `python3 notes/scripts/w4/x0arms.py --flatcore 8` | the kernel identity at 2 080 / 2 080; no jump at 2 080 / 2 080 | 171 s |
| `python3 notes/scripts/w4/x0arms.py --tree x8_60101824,x10_3584739737600` (and `x8_60101824 --ear23 antecedent --delta0 off`) | both (MC-54) → THETA / uncovered, with its cells | < 1 s |

