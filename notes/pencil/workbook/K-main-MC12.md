## §(K-main) — Step MC12 — the contraction step on `X₀` (W4-reopen P1, option 2)

#### Step MC12 — the contraction step on `X₀` (W4-reopen P1, option 2)

*Worked 2026-09-24 by a forked agent, porting the device and scratch probes of the feasibility recon
of W4-reopen's first unranked direction (the multi-scale construction; its claims were
unreviewed). Every claim marked `PROVED` below was re-derived by that agent and checked by the
coordinator at sketch level. **A second reader (2026-09-24) re-derived (MC-34)–(MC-39) and (MC-59)**
against the driver's row structure and KT 2011 §6.2: nothing wrong, no gap left open; its fills and
sharpenings are recorded at the claims they touch. The driver is `w4/coreshrink.py` (new).
The question is Step MC10's last "still lacks" bullet, W4-reopen P1 (2026-09-24) option 2: does
`X₀(G)` relate to `X₀(G/H)` at all? **Yes, for a proper rigid `H` whose contraction `G/H` is
simple.** Katoh–Tanigawa's contraction case (KT 2011 §6.2, Lemma 6.3) has an `X₀` form. The
contraction step reduces to two linear-algebra conditions, (i) and (ii), which are checked per
graph at one exact picture.*

**Notation.**
- **Proper rigid set.** `W ⊊ V` with `|W| ≥ 2` and `def₃(G[W]) = 0`. Put `H := G[W]`, the
  induced subgraph. A rigid `H` has minimum degree `≥ 2`: the partition `{{v}, W ∖ v}` has value
  `6 − 5 deg_H v`. So `|W| ≥ 3`, and `H` satisfies (H).
- **Outside, contraction.** `O := V ∖ W` is the outside. `G/H` contracts `W` to one vertex `v*`
  and keeps parallel edges. It is **simple** iff no outside vertex has two neighbours in `W`.
- **Attachments.** When `G/H` is simple, each **attachment** `u` (an outside vertex adjacent to
  `W`) has exactly one core neighbour `c(u)`. `A_c` is the set of attachments of `c`, and `c` is
  **pinned** if `|A_c| ≥ 2`.
- **Ranks.** For a multigraph `Γ` with a nonzero line `L_e` on every edge,
  `M_Γ(L) := {X : V(Γ) → K⁶ : X_u − X_w ∈ K L_e}` and `rank R_Γ(L) = 6|V(Γ)| − dim M_Γ(L)`.
  `L_p` is the line set `p_u ∧ p_w` of a configuration `p`.
- **Targets.** `tgt(Γ) := 6(|V(Γ)| − 1) − def₃(Γ)`. It bounds `rank R_Γ(L)` for every `L`.
- **The collapse point.** `P` is a point, put at the origin of the chart; `Q = (0, 0)` is its
  picture. `q' := (q|_O, Q)` is a picture of `G/H` with `v*` at `Q`.
  `L⁰_{G/H}(q') := {z ∈ L_{G/H}(q') : z_{v*} = 0}`.
- **Two-scale family.** A curve `p(t)` of pencil configurations of `G` with `p_c(t) → P` for
  every `c ∈ W` and `p_u(t) → p_u(0)` for every `u ∈ O`: the core "at scale `t` around `P`".

> **(MC-34)** `[PROVED]` *(the block identity: the kernel form of KT 2011 eq. (6.3), p. 673)* Let
> `p` be any configuration of `G` with adjacent points distinct. If `(H, p|_W)` is infinitesimally
> rigid, then **exactly**
> `rank R_G(L_p) = 6(|W| − 1) + rank R_{G/H}(L_p)`.
> Here `G/H` carries the **actual** lines of `p`: a boundary edge `uc` keeps `p_u ∧ p_c`. No
> genericity is assumed, and the identity holds over any field.

*Proof.* Restrict a motion `X` of `G` to `W`. It is a motion of `H`, and `H` is infinitesimally
rigid, so it is constant: `X|_W ≡ X*`. Put `X_{v*} := X*`. This is a motion of `G/H` with the same
lines, because the conditions at edges of `H` hold trivially and the others are unchanged.
Conversely, a motion of `G/H` extends by `X|_W :≡ X_{v*}`. So `dim M_G = dim M_{G/H}`, and
`6|V| − dim M_G = 6(|W| − 1) + (6(|V| − |W| + 1) − dim M_{G/H})`. ∎

KT's (6.3) is the block-triangular shape of `R(G, p)`: the rows of `E′` are supported on `V′`.
With their Lemma 5.1 (p. 667) it gives `≥`; the kernel view gives equality. The driver asserts
(MC-34) at every sampled point where the core is rigid.

> **(MC-35)** `[PROVED]` *(the targets add; KT 2011 Lemma 3.5, p. 658, is the minimal-k-dof form)*
> If `H` is rigid, then `def₃(G) = def₃(G/H)`, so `tgt(G) = 6(|W| − 1) + tgt(G/H)`.

*Proof.* Write `val(𝒫) := 6(|𝒫| − 1) − 5 d(𝒫)`. Take a maximizing partition `𝒫` of `V` and
merge the `t` parts that meet `W`. The value changes by
`−6(t − 1) + 5·(edges between the merged parts)`. This is
`≥ −6(t − 1) + 5 d_H(𝒫|_W) = −val_H(𝒫|_W) ≥ −def₃(H) = 0`. So some maximizing partition has `W`
inside one part. Such partitions of `V` are exactly the partitions of `V(G/H)`, with the same
crossing edges. Finally, `|V(G/H)| = |V| − |W| + 1`. ∎

> **(MC-36)** `[PROVED]` *(the limit)* Let `p(t)` be a two-scale family, regular in `t` at `0`, with
> `p_u(0) ≠ P` at every attachment and `p_u(0) ≠ p_w(0)` on outside edges.
> - The lines `L(t)` of `G/H` converge to `L(0)`, with `L(0)(uc) = p_u(0) ∧ P`: in the limit every
>   hinge at `v*` passes through `P`.
> - For all but finitely many `t`, `rank R_{G/H}(L(t)) ≥ rank R_{G/H}(L(0))`.
> - `L(0)` is the line set of the configuration of `G/H` with `v*` at `P` and `u` at `p_u(0)`.
>   If `G/H` is simple, this configuration is pencil at every `u ≠ v*`. At `v*` it need not be:
>   `v*` is realized "as a d-dimensional body" (KT p. 675).

*Proof.* The augmented matrix of (MC-3) is polynomial in the points, so its entries are regular at
`t = 0`. A minor that is nonzero at `t = 0` is nonzero at all but finitely many `t`. By (MC-3),
`rank A = |E| + rank R` whenever every line is nonzero, and the distinctness hypotheses give that
at `t = 0`. For the pencil claim: coplanarity of `N_{G/H}[u]` is a closed condition. It holds at
every `t ≠ 0`, because `N_G[u]` is coplanar and, when `G/H` is simple, it meets `W` at most in
`c(u)`, whose point tends to `P`. ∎

Simplicity is what makes the limit usable. An outside `u` with two core neighbours would give two
boundary hinges converging to the same line `p_u(0) ∧ P`. This is the (α)/parallel-class
obstruction, and KT Lemma 6.3's hypothesis "`G/E′` simple".

**The construction** (`coreshrink.py --pool`). It is a linear system, not a hand construction.
1. Fix `q_u` for `u ∈ O` and `δ_c` for `c ∈ W`, and put `q_c(t) := t δ_c`.
2. Write the core heights as `z_c = t ζ_c`. For every `v ∈ N[W]`, write the constant term of `π_v`
   as `γ_v = t γ̃_v`.
3. For `t ≠ 0`, the pencil conditions `z_w = α_v x_w + β_v y_w + γ_v` (`w ∈ N[v]`) become a
   homogeneous system `M(t) = M₀ + t M₁` in `(z_O, ζ, α, β, γ̃)`, and `ker M(t) ≅ L(q(t))`. The
   only `t` in it is the `γ̃_v` of the rows `(v ∈ N[W], w ∈ O)`.
4. Let `W₀ := lim_{t→0} ker M(t)`. It is a subspace of `ker M₀` of dimension `dim L(q(t))`, and
   the driver computes it exactly, from jets. **No jump** means `ker M₀ = W₀`.
5. A family is the unique `x(t) ∈ ker M(t)` with `R x = b`, for fixed generic `R` and `b`. It is
   regular at `0`, with `x(0) ∈ W₀`. Then `p(t) := ((q_u, z_u(t))_{u ∈ O}, (tδ_c, tζ_c(t))_{c ∈ W})`
   is a two-scale family.

At `t = 0` the rows say three things:
- the outside planes are those of a configuration of `G/H` with `v*` at `P`, pencil except at `v*`;
- `π_c(0)` passes through `P` and contains `A_c`;
- the rescaled core `d_c := (δ_c, ζ_c(0))` has, at each `c`, a plane through `N_H[c]` with the
  slope of `π_c(0)`.

> **(MC-37)** `[PROVED]` *(the `X₀` form of KT's Claim 6.4, p. 675)* Let `G/H` be simple, and assume
> **(ii)** *no jump:* `dim ker M₀ = dim L(q(t))` at one picture where `q(t) ∈ U` is certified.
> Then, at `X₀(G)`'s generic point `p`, `rank R_{G/H}(L_p)` is at least the generic rank of
> `X₀(G/H)`. That rank is `tgt(G/H)` if `X₀(G/H)` attains.

*Proof.*
1. *(ii) is generic.* `dim ker M₀` is upper semicontinuous in the picture, and it is never below
   `dim W₀ = ℓ₀(G)`. So equality at one certified picture gives equality at a generic one.
2. *Containment: `L⁰_{G/H}(q') ⊆ proj_z ker M₀`.* Take `z⁰ ∈ L⁰_{G/H}(q')`. Its plane at `v*` is
   `π* : z = a*·(x, y)`, through `P` since `z⁰_{v*} = 0`. Extend `z⁰` by a flat core:
   - `ζ := a*·δ`;
   - every core plane of slope `a*`, with `γ̃_c = 0`;
   - `γ̃_u := ζ_{c(u)} − a_u·δ_{c(u)}` at each attachment `u`.

   Every row of `M₀` then holds. The two kinds that could fail do not: "`π_c(0)` contains `A_c`"
   holds because `A_c ⊆ π*`, and "an attachment's plane passes through `P`" holds because
   `v* ∈ N_{G/H}[u]`.
3. *The limit is good.* By (ii), `W₀ = ker M₀`. So for generic `(R, b)` the limit `x(0)` is a
   generic point of `ker M₀`, and its heights are a generic point of the linear space
   `proj_z ker M₀`. That space contains `L⁰_{G/H}(q')`, by 2.
   - The rank at `(q', z)` is lower semicontinuous on that linear space. So the rank at the limit
     is at least its generic value on `L⁰_{G/H}(q')`.
   - By (MC-3) (shifts by `Aff(q')`), that value is the generic value on `L_{G/H}(q')`.
   - `q'` is generic up to translation, so this is the generic rank of `X₀(G/H)`.
4. *From the limit to the generic point.* Apply (MC-36) to the family. The map
   `(q_O, δ, R, b, t) ↦ p(t)` is dominant onto `B`: `(q_O, tδ)` is a generic picture, and for
   fixed `t ≠ 0` the pinned point sweeps a dense subset of `ker M(t) ≅ L(q(t))`. So the rank
   inequality holds on a nonempty open set of parameters, hence on a dense subset of `B`, hence
   at `X₀(G)`'s generic point. ∎

*Second reading (2026-09-24): steps 3 and 4 filled in.*
- *Implicit hypothesis.* `G/H` satisfies (H), in particular `|δ(W)| ≥ 2`. Otherwise
  `N_{G/H}[v*]` has two points, no `q′` is admissible, and `X₀(G/H)` is undefined. (MC-39) supplies
  it through 2EC, which it uses for nothing else.
- *The row types of `M₀`* (read off `coreshrink.py`'s `recipe`, not the prose). There are five:
  1. core rows `ζ_w = a_c·δ_w + γ̃_c`, `w ∈ N_H[c]`;
  2. `z_w = a_c·q_w`, `w ∈ A_c`;
  3. `ζ_{c(u)} = a_u·δ_{c(u)} + γ̃_u` at each attachment `u`;
  4. `z_w = a_u·q_w`, `w ∈ N_O[u]`;
  5. the unchanged far rows.

  `γ̃_u` occurs in `M₀` only in type 3, once per `u` when `G/H` is simple. So type 3 only fixes `γ̃_u`,
  and this is the one place step 2 uses simplicity. The flat core of step 2 is KT's specialization in
  their proof of Claim 6.4 (p. 675): every core panel is set to the `v*` panel.
- *Step 3, joint genericity.* On the open set of parameters `(q_O, δ, R, b)` where (ii) holds and
  `R|_{ker M₀}` is invertible, `ker M₀` is a vector bundle over the pictures. The map to `x(0)` is
  onto its total space, so the limit heights are a generic point of `proj_z ker M₀`.
- *Step 3, `q′` is generic enough.* Translations of the plane preserve admissibility, `L` and the
  rank, so the maximal-rank locus `B°(G/H)` is translation-invariant. The slice
  `B(G/H) ∩ {q_{v*} = Q}` is a vector bundle over a nonempty open set, hence irreducible, and `B°`
  meets it (translate any point of `B°`). So for `q_O` in a nonempty open set the generic rank on
  `L_{G/H}(q′)` is the generic rank of `X₀(G/H)`.
- *Step 4.* For each fixed `t ≠ 0` the parametrization is onto `B(G)`, not just dominant. And one
  parameter in the good open set suffices: by (MC-36) it gives cofinitely many `t` with `p(t) ∈ B(G)`
  and the rank inequality. That inequality is lower semicontinuous on the irreducible `B(G)`, so it
  holds on a dense open subset.

What the recon called "the Claim-6.4 inequality comes free from linearity
(`L(G/H) ⊆ L_relaxed`)" is step 3. But containment in the relaxed space alone is not enough: the
limit must be *generic* in a space containing `L⁰_{G/H}(q')`. That is step 2 together with (ii).

> **(MC-38)** `[PROVED]` *(the core half is a statement about `X₀(G)` alone)* For `t ≠ 0`, the
> points `p(t)` of the families are generic points of `B` ((MC-37), step 4). So the hypothesis of
> (MC-34) needed here is: **`H` is infinitesimally rigid at `X₀(G)`'s generic point, restricted to
> `W`.** It holds if `X₀(H)` attains and
> **(i)** *core-free:* `proj_W L_G(q) = L_H(q|_W)` at one `q` with `q ∈ U(G)` and `q|_W ∈ U(H)`
> certified.

*Proof.*
- `proj_W L_G(q) ⊆ L_H(q|_W)` always, since `N_H[c] ⊆ N_G[c]`.
- The dimension of the left side is lower semicontinuous on `U(G)`. The right side has the
  constant dimension `ℓ₀(H)` on `U(H)`. So equality at one certified `q` gives equality at a
  generic `q`.
- Hence restriction `B_G → B_H` is dominant. `H` is rigid at `X₀(H)`'s generic point, which is
  therefore the image of a generic point of `B_G`. Rigidity is an open condition. ∎

*Second reading:* the claim's first sentence holds only for generic parameters, and nothing uses
it. (MC-39) needs only that the two dense open subsets of `B(G)` given by (MC-37) and by this claim
meet.

The two-scale limit is **not** where the core's rigidity comes from. In the `pencil` variant
below, W19's rescaled limit core is flat, with rank `17 = 18 − def₂(C₄)`, while at every `t ≠ 0`
the core has rank 18. The same happens at 4 of the 20 sampled residuals.

> **(MC-39)** `[PROVED]` *(the contraction step on `X₀`)* Let `G` satisfy (H) and be
> 2-edge-connected. Let `W` be a proper rigid set with `G/H` simple that satisfies (i) and (ii).
> Then **if `X₀(H)` and `X₀(G/H)` attain, `X₀(G)` attains.** Both `H` and `G/H` satisfy (H),
> `G/H` is 2EC, and both have fewer vertices than `G`. Without (i), the hypotheses "(i) and
> `X₀(H)` attains" can be replaced by "`H` is infinitesimally rigid at `X₀(G)`'s generic point".

*Proof.* At a generic point `p` of `B`, the core is rigid (MC-38). So
`rank R_G(L_p) = 6(|W| − 1) + rank R_{G/H}(L_p)` by (MC-34), and this is
`≥ 6(|W| − 1) + tgt(G/H)` by (MC-37), which is `tgt(G)` by (MC-35). The reverse inequality always
holds. One point of `B` at the target suffices (MC-2). For the side conditions: `v*` has degree
`|δ(W)| ≥ 2` because `G` is 2EC, and outside degrees are unchanged. ∎

This is KT 2011 §6.2's case "`G` has a proper rigid subgraph `G′` with `G/E′` simple" (Lemma 6.3,
p. 674), with two changes:
- KT's fresh hinges `Π_{G/E′,p₂}(u) ∩ Π_{G′,p₁}(v)` (6.6) are not available. A pencil hinge must
  pass through both points and lie in both planes, and the scale `t` supplies such hinges.
- KT prove Claim 6.4 by specialization plus algebraic independence. Here it becomes the
  containment (MC-37) step 2, plus linearity.

(MC-39) consumes, from the induction, **`X₀` attainment at `H` and at `G/H`**. That is the
generic-point motive, not bare existence, and it is `X₀`'s own motive, so the step composes.

> **(MC-40)** `[CONSTRUCTED]` *(`coreshrink.py --family`; the recon's certificates, re-run with the
> checks its probe lacked)* On W19 and R20, core `C₄` / `C₅` (their unique maximal rigid set;
> `G/H` has 16 vertices, target 90), the recon's recipe gives **64/64 rows at the target**:
> 2 graphs × 2 variants × 4 draws × `t ∈ {1/10, 1/100, 1/10⁴, 1/10⁸}`, ranks 108/108 and 114/114.
> The recipe keeps the outside fixed and every star exact at every `t`. At every row:
> - `q(t) ∈ U` is certified (`dim L = 13 = 3 + def₂` at W19, `14` at R20);
> - the core is rigid (18/18, 24/24);
> - `G/H` with the actual lines reaches 90/90;
> - (MC-34) is asserted.
>
> The limit `G/H` reaches 90/90 at all 16 draws, including the 8 `pencil` draws, where the limit is
> a pencil configuration of `G/H` (the induction hypothesis applies verbatim).
> *Measured, `coreshrink.py --pool` (the general construction).* The results, by pool, in the
> `relaxed` variant, over (member, maximal `W` with `G/H` simple) runs:
> - `named` 2/2; `smark` 20/20 runs (13 members); `thetas` 80/80 (69 members);
> - `exh7` 99/99 on the 85 members with such a `W`;
> - `peels` every 8th member: 196/196 (116 members);
> - `residuals` every 13th member: 20/20 (20 members).
>
> Every run with (i) and (ii) certified attains:
> - exh7 185/185, including the fallback runs below;
> - smark 20/20; thetas 80/80; peels 196/196; residuals 20/20.
>
> The `pencil` variant is OK at every run. Its points are not generic in `B`, so these runs are
> certificates for `G`, not evidence for (MC-37).

**Coverage** (the `--pool` summary lines). The figures are counts of labelled
members over the named populations and caps.
- Every sampled `residuals`, `peels` and `smark` member has a maximal rigid `W` with `G/H`
  simple. So does every `thetas` member with a proper rigid set, except 2, and those 2 are flat.
- `exh7`: of the 572 members with a proper rigid set, 85 have such a maximal `W`, and **68 of those
  85 have `def₂(G) = 0`**. Of the rest, 89 have one only among smaller rigid sets and 398 have
  none, and every one of these 487 has `def₂(G) = 0`.
- `exh8` is not classified. `--pool exh8 --classify` ran about 12 min before stopping at a member
  beyond `rigid_vertex_sets`'s 22-branch cap. The driver now skips and counts such members, but
  no `exh8` figure is recorded.
- A flat `X₀` (`def₂(G) = 0`) attains outright by (MC-5)(iii). So on `≤ 7` vertices the
  contraction step has content only at the 17 members with `def₂(G) > 0`. The larger pools are
  the informative ones.

> **(MC-41)** `[OPEN]` *(the residue (X₀-∂))* (MC-39) is conditional on (i) and (ii), and it needs
> a `W` with `G/H` simple.
> - **(∂1)** When does (i) hold?
> - **(∂2)** When does (ii) hold, or at least the containment `L⁰_{G/H}(q') ⊆ proj_z W₀` that (ii)
>   gives?
> - **(∂3)** What happens at the graphs with a proper rigid set but no rigid `W` with `G/H` simple?
>   This is KT Lemma 6.5's case, p. 676, which KT close with a degree-2 vertex (Claim 6.6).
>
> Measured:
> - (i) fails at exactly 11 exh7 runs. All are `C₄` cores (`def₂ = 1`) at non-maximal `W`, in the
>   fallback, and all have `def₂(G) = 0`: `X₀(G)` is flat, so `proj_W L_G = Aff` is 3-dimensional
>   while `dim L_H(C₄) = 4`. The core is flexible there (17/18), but `G` attains anyway, by
>   (MC-5)(iii).
> - (ii) fails at 1 relaxed run, `x7_1716440` (also flat). In the smark `pencil` sub-family it
>   fails at 3 runs, where `L0in` still holds.
> - In no relaxed run with `def₂(G) > 0`, in any of these pools, does (i) or (ii) fail.

*The recon's three predicted failure points, re-examined.*
1. **"A core with `def₂ > def₃` forced flat (N3's `C₄ + x, y`: core 17/18)."** As cited, this is
   wrong on two counts:
   - N3's instance is `K_{2,4}` with core `C₄ = 1234`. There `x` and `y` each have two core
     neighbours, 1 and 3, so `G/H` is **not simple**: the instance is failure point 2, not 1.
   - 17/18 is gate **N1**'s figure (the all-coplanar `C₄`). Gate **N3** reports **18/18** on KT's
     constrained family (`notes/Phase39-design.md`, numerics index).

   Genuine forced-flat cores with `G/H` simple do exist: the 11 exh7 runs above, all at flat
   `X₀(G)`. For a *maximal* `W` a flat core is harmless: if `H` lies in a `def₂`-rigid `K` with
   `V(K) ⊋ W`, then `K` is `def₃`-rigid (by (MC-5)(i) and connectivity), so maximality forces
   `V(K) = V`, and then `def₂(G) ≤ def₂(K) = 0`. `[PROVED]`
2. **"`G/H` with a parallel class."** This is excluded by the hypothesis of (MC-36)–(MC-39) and
   counted, not attacked: in exh7, 2 667 maximal sets have `G/H` not simple. The 487 exh7
   members with **no** maximal `W` whose `G/H` is simple are all flat (*Coverage*).
3. **"Two adjacent pinned core vertices, forcing a third scale."** This is an artifact of the
   recon's recipe, which **fixes** the outside. In the linear-system family the outside moves at
   order `t`. Adjacent pinned pairs occur at 10 exh7 runs, all OK; none occur in the other pools.

The recon's stop rule was "> 3 structurally distinct failing patterns, or a member where `X₀`
attains with no working `H`". It fires only vacuously. The failing patterns are 3 (`s = 1100`,
`1110`, `2100`: `C₄` cores with 2 or 3 attachment vertices). The members with no working `H` are
`x7_520384`, `x7_1460568` and `x7_1841496`, and every one of them has `def₂(G) = 0`.

> **(MC-42)** *(durable negatives)*
> **(a)** `[PROVED]` *(and measured, `coreshrink.py --collapse`)* *Collapsing a flexible side of a 2-cut to
> a point is lossy at leading order.* Take `θ(3,4,5)` (target 60) and collapse its 5-edge path's
> interior to `Q ∈ π_A ∩ π_B` (`POINT`). The family has rank 60 at certified points of `B`. But
> all five limit lines of the path pass through `Q`, so they span at most `dim Λ_Q = 3`, and the
> leading-order bound is `≤ 58`. It is measured 58 at 3/3 draws; the corpus's slide-in
> (§(K-pitch) Step 6) is lossless, at 60.
> The refined limit, the Grassmannian limit of the path's span, recovers 60. But it is `X^⊥`
> (Klein form) for a line `X` through `Q` with `X ≠ π_A ∩ π_B` (3/3). This is a special linear
> complex fixed by the side's internal data, so it does not decouple into a statement about the
> two sides.
> The contrast with (MC-34) is the point: a rigid core never needs a refined limit, because its
> internal motion is trivial and its internal hinges never enter `G/H`.
> **(b)** `[INFORMAL]` *(the recon's analysis; no driver, second reader owed)* At a 2-cut,
> the leading-term analysis under a one-parameter subgroup of the flag stabilizer `S(φ)` is
> smark S2's block-sum condition (B) with its exceptions (X1)–(X4)
> (`notes/pencil/workbook/attack-smark.md`, S2). Gauge families cannot change a side's rank or
> welded rank (projective invariance), so no configuration obtained this way both attains and
> welded-attains.
> **(c)** *(pointer)* The tree-packing / WW87 specialization of the contraction is §(K-slide-cl)'s
> tetrahedral collapse, refuted in §(K-slide-comb) and §(K-pure) (PC-OBS).

**What would change this.**
- A run with (i) and (ii) certified whose `G` falls short would contradict (MC-39): a proof error.
  `coreshrink.py` would still pass its (MC-34) asserts.
- A member with `def₂(G) > 0` and a maximal `W` where (i) fails, or where (ii) and the containment
  `L0in` both fail, would be the first genuine (∂1) or (∂2) witness.
- A member with `def₂(G) > 0`, a proper rigid set and no rigid `W` with `G/H` simple would be the
  first (∂3) witness.
- A second reader finding a gap in (MC-37) steps 2–4, the only non-routine step.

**Drivers** (all at `PYTHONHASHSEED=0`, seed `20260924`; exact ℚ for the family's linear algebra,
ranks mod `2⁶¹ − 1` with every shortfall recomputed in ℚ; sampler support is in the docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/coreshrink.py --family` | 64/64 rows at the target, `q(t) ∈ U` certified, core rigid; limit 16/16 at 90/90; 2 degenerate draws redrawn | 5.7 s |
| `python3 notes/scripts/w4/coreshrink.py --collapse` | POINT 60 / 58 / 60, SLIDE 60 / 60 / 60, at 3/3 draws; `in(R₃) = X^⊥`, `X ∋ Q`, `X ≠ M` | 0.6 s |
| `python3 notes/scripts/w4/coreshrink.py --pool named,smark,thetas` | relaxed OK 2/2, 20/20, 80/80; (i) and (ii) at every run | 89 s |
| `python3 notes/scripts/w4/coreshrink.py --pool exh7` | 99/99 maximal-`W` runs OK; fallback 86/89 members; 11 `C₄` core-flexible runs, all `def₂(G) = 0` | 47 s |
| `python3 notes/scripts/w4/coreshrink.py --pool peels --stride 8` | 196/196 relaxed runs OK (116 members); (i) and (ii) at every run | 132 s |
| `python3 notes/scripts/w4/coreshrink.py --pool residuals --stride 13` | 20/20 (20 members); (i) and (ii) at every run; 4 `pencil` runs with a flat limit core, rigid at `t ≠ 0` | 105 s |

