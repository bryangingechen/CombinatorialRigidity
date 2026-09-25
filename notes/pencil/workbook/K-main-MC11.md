## §(K-main) — Step MC11 — the split-off step on `X₀` (Jackson–Jordán's Claim 6.5 Case 1, transferred)

#### Step MC11 — the split-off step on `X₀` (Jackson–Jordán's Claim 6.5 Case 1, transferred)

*From the 2026-09-24 feasibility recon of W4-reopen's second unranked direction (transferring
Jackson–Jordán's proof technique). A second agent re-derived every `PROVED` step here and extended
the membership claim to both `def₂` cases. Driver `w4/splitext.py` (new). The question:
Jackson–Jordán's Case 1 (TR p.16) splits off a degree-2 vertex, realizes the smaller graph by
induction, and puts the new pin at a 1-extension position. Does that step transfer to `X₀`?*

**Notation.** `G` satisfies (H), and `x` is a vertex of degree 2 whose neighbours `a`, `b` are **not**
adjacent.
- `G′ := G − x`. This is Step MC10's `G′` for the open ear `a − x − b` with `k = 1`.
- `G″ := G′ + ab = G.splitOff x a b` (`kbare_common.split_off`). It satisfies (H) and has `|V| − 1`
  vertices.
- `δ := def₃(G′) − def₃(G′/ab)` is Step MC10's `δ`, and `δ₂ := def₂(G′) − def₂(G′/ab)`.
- For `q′ : V ∖ {x} → K²`, `U := {P_a − P_b : P ∈ F(G′, q′)}` is Step MC10's `U`.
- `ℓ_ab := p̂_a × p̂_b`, and `c := dim(U + Kℓ_ab) − 1`.
- The **special point** over `(q′, z″) ∈ B(G″)` and `s ∈ K ∖ {0, 1}` sets
  `p_x := (1 − s) p_a + s p_b`, that is, `q_x0 := (1 − s) q_a + s q_b` and
  `z_x := (1 − s) z_a + s z_b`. The hinges `xa`, `xb` and the deleted `ab` are then one line.

> **(MC-28)** `[PROVED]` *(rank exactly `+5`; field-free)* Let `(q′, z″)` be any configuration of
> `G″` with all hinges nonzero, and let `s ∉ {0, 1}`. The special configuration is a pencil
> configuration of `G`. It is not admissible, since `q(N[x])` is collinear. And
> `rank R_G(special) = rank R_{G″}(q′, z″) + 5`.

*Proof.*
- *Pencil.* `N[x] = {x, a, b}` is collinear, hence coplanar. `N_G[a] = N_{G″}[a] − b + x` lies in
  `π_a`, because `p_x ∈ p_a p_b ⊆ π_a`. The same holds at `b`. No other closed neighbourhood changes.
- *Hinges.* `p_x ≠ p_a, p_b`, because `s ∉ {0, 1}` and `p_a ≠ p_b`. So `C_{xa}` and `C_{xb}` are
  nonzero multiples of `C_{ab}`.
- *Motions.* A motion `X` of `G` has `X_x − X_a, X_x − X_b ∈ K C_{ab}`, together with `G′`'s
  conditions. So `X|_{V∖x}` is a motion of `G″`, and `X_x = X_a + t C_{ab}` with `t` free. Hence
  `dim M_G = dim M_{G″} + 1`, and `rank R_G = 6|V| − dim M_G = rank R_{G″} + 5`.

No step divides or uses an order. ∎

In Step MC10's terms (when `G′` satisfies (H)): at a point of `X₀(G″)` the flag pair of `a`, `b` is
in orbit (iii), or in orbit (iv) when `U = 0`. The special point is the `k = 1` placement on
`p_a p_b`. There `λ = 1` and `Λ = K C_{ab}` ((MC-19)(b)), and (MC-22)'s hypothesis `λ = k + 1`
excludes this placement. The split-off step uses exactly this placement.

> **(MC-29)** `[PROVED]` *(the counts)* **(a)** `def₃(G) − def₃(G″) = [δ ≥ 5]`, and
> `def₂(G) − def₂(G″) = [δ₂ ≥ 2]`. Both lie in `{0, 1}`. **(b)** Hence
> `target(G) − (target(G″) + 5) = 1 − [δ ≥ 5]`.

*Proof.* This is (MC-17)'s count. Restrict a partition to `V(G′)`. Let `f = def₃(G′)` and
`g = def₃(G′/ab)`, and let `f_sep` be the maximum over partitions separating `a` from `b`.
- The chord `ab` contributes `−5` when `a`, `b` are separated, and `0` otherwise.
- The path `a − x − b` contributes `−4` when `a`, `b` are separated (`x` alone: `6 − 2·5`). Otherwise
  it contributes `0` (`x` joins the part of `a` and `b`).

So `def₃(G″) = max(f_sep − 5, g)` and `def₃(G) = max(f_sep − 4, g)`.
- If `δ > 0`, then `f_sep = f`, and these are `f − min(δ, 5)` and `f − min(δ, 4)`.
- If `δ = 0`, both equal `f`.

For `def₂`, replace `6` and `5` by `3` and `2`. The chord then contributes `−2` and the path `−1`,
giving `f₂ − min(δ₂, 2)` and `f₂ − min(δ₂, 1)`. For (b):
`target(G) − target(G″) = 6 − def₃(G) + def₃(G″)`. ∎

So `def₃` rises by one exactly when `δ ≥ 5`. `def₂` rises exactly when `δ₂ ≥ 2`.

> **(MC-30)** `[PROVED]` *(the special point lies on `X₀(G)`)* Let `q′` be admissible for `G″` with
> `dim L_{G″}(q′) = 3 + def₂(G″)`.
> **(i)** `U ≠ Kℓ_ab`.
> **(ii)** Suppose some admissible `(q′, q_x1)` has `dim L_G(q′, q_x1) = 3 + def₂(G)`, and that
> `U = 0` or `U ⊄ p̂_{x0}^⊥`. Then for every `z″ ∈ L_{G″}(q′)` the special point over `(q′, z″, s)`
> lies on `X₀(G)`.
> **(iii)** If `def₂` rises, then `c = 2`. If `def₂` does not rise and (ii)'s `q_x1` exists, then
> `c = [U ≠ 0]`. So at a certified point, `c = 2` iff `def₂` rises. In flex form this is the
> flag-genericity condition `dim F(G′) − dim F(G″) = 2`.
> **(iv)** Suppose `ℓ₀(G″) = 3 + def₂(G″)`. Then at the generic point of `X₀(G″)`, and for every
> `s ∉ {0, 1}` except at most one, the special point lies on `X₀(G)`. No hypothesis at `G` is
> needed.

*Proof.* Two formulas come first. They hold for `q′` edge-injective on `G″` and `q_x` off the line
`q_a q_b`. Both follow from (MC-13)(a)'s computation, since `Kℓ_{xa} = p̂_x^⊥ ∩ p̂_a^⊥`.
1. `F(G, (q′, q_x)) ≅ ker φ_{q_x} ⊆ F(G′, q′)`, where `φ_{q_x}(P) := (P_a − P_b) · p̂_x`.
   `P_x` is the affine function with values `P_a·p̂_a`, `P_b·p̂_b`, `P_a·p̂_x` at `q_a`, `q_b`, `q_x`.
2. `F(G″, q′) = {P ∈ F(G′, q′) : P_a − P_b ∈ Kℓ_ab}`, so `dim F(G′) − dim F(G″) = c`.

Together they give

  `dim F(G, (q′, q_x)) = dim F(G″, q′) + c − [U ⊄ p̂_x^⊥]`.    (★)

*(i).* Suppose `U = Kℓ_ab`. Then `c = 0` and `U ≠ 0`. At an admissible `q_x` off the line
`q_a q_b`, (★) gives `dim F(G) = 2 + def₂(G″) < 3 + def₂(G)`, using (MC-29)(a). That contradicts
(MC-4)(b) at `G`.

*(ii).*
- *The curve.* Take `η ∈ K²` not parallel to `q_b − q_a`, and set `q_x(t) := q_x0 + tη`. Write
  `φ₀ := φ_{q_x0}` and `ψ(P) := (P_a − P_b) · (η, 0)`, so that `φ_{q_x(t)} = φ₀ + tψ`. For all but
  finitely many `t`, `(q′, q_x(t))` is admissible. `N_G[a] = N_{G″}[a] − b + x` can be collinear only
  when `N_{G″}[a] − b` lies on a line through `q_a` other than `q_a q_b`, and the curve meets that
  line at most once. The same holds at `b`. At such `t`, `[U ⊄ p̂_{x(t)}^⊥] = [U ≠ 0]`, because
  `φ₀ ≠ 0` when `U ≠ 0`.
- *It lies in `U(G)`.* By (★), `dim L_G(q′, q_x(t)) ≤ dim L_G(q′, q_x1) = 3 + def₂(G)`. (MC-4)(b)
  gives equality, so `(q′, q_x(t)) ∈ U(G)`.
- *The flexes.* Let `P₀ := Ψz″ ∈ F(G″, q′) ⊆ ker φ₀`. If `U = 0`, put `P(t) := P₀`. Otherwise pick
  `W₀` with `φ₀(W₀) ≠ 0`, and put `P(t) := P₀ − [tψ(P₀)/(φ₀(W₀) + tψ(W₀))] W₀`. Then
  `φ_{q_x(t)}(P(t)) = 0` and `P(t) → P₀`.
- *The limit.* `z(t) := Φ(P(t)) ∈ L_G(q′, q_x(t))`, by formula 1 and Step MC4. At `t = 0`,
  `z_w = P₀_w · p̂_w = z″_w` on `V ∖ x`. And `z_x = P₀_a · p̂_{x0} = (1 − s) z″_a + s z″_b`, because
  `P₀_a − P₀_b ∈ Kℓ_ab ⊥ p̂_b`. So the special point is a limit of points of `B(G)`.

*(iii).* If `def₂` rises, apply (MC-4)(b) at `G` and (★) at a generic `q_x`:
`1 ≤ c − [U ≠ 0]`. This forces `U ≠ 0` and `c = 2`, since `U + Kℓ_ab ⊆ K³`. If `def₂` does not
rise, (★) at `q_x1` gives `c = [U ⊄ p̂_{x1}^⊥] ≤ [U ≠ 0]`. Conversely, `c ≥ [U ≠ 0]` by (i).

*(iv).* At the generic point, `q′` is generic in `K^{2(|V|−1)}`, so
`dim L_{G″}(q′) = ℓ₀(G″) = 3 + def₂(G″)` and (i) applies. Because `U(G)` is dense and open, some
`q_x1` has `(q′, q_x1) ∈ U(G)`, with `dim L_G = ℓ₀(G)`. The proof of (ii) used only that
`dim L_G(q′, q_x1)` is the minimum `ℓ₀(G)`, so it applies unchanged. If `U ≠ 0`, then `U ⊄ Kℓ_ab`
by (i). So some `u ∈ U` does not vanish on the whole line `q_a q_b`, and `u(q_{x0})` is zero for at
most one `s`. ∎

> **(MC-31)** `[PROVED]` *(the step, within one)* If `X₀(G″)` attains and
> `ℓ₀(G″) = 3 + def₂(G″)`, then the generic rank on `X₀(G)` is at least
> `target(G) − 1 + [δ ≥ 5]`. In particular, **`X₀(G)` attains whenever `δ ≥ 5`**, with no condition
> on the flag orbit, on dominance, or on `r`.

*Proof.* Take the generic point of `X₀(G″)` and a generic `s`. By (MC-28) the special point has rank
`target(G″) + 5`, and by (MC-30)(iv) it lies on `X₀(G)`. Rank is lower semicontinuous on the
irreducible `X₀(G)` (MC-2). Then use (MC-29)(b). ∎

Where the hypothesis `ℓ₀(G″) = 3 + def₂(G″)` is available:
- in characteristic 0, by Jackson–Jordán;
- at every `G″` on at most 8 vertices in characteristic 0, by the census's `JJ` column with
  `--jjprobe` (*The census — results*);
- at the same graphs in characteristics 2, 3, 101 and 10 007, by (MC-33)(ii);
- over any infinite field, modulo (MC-33)(i).

It is used only to exclude `U = Kℓ_ab`.

> **(MC-32)** `[MEASURED]` *(`splitext.py`; the missing `+1` appears at first order)* Moving `x` off the
> line gives first-order gain `≥ 1` at every instance where one is needed. The curve is the exact
> curve of (MC-30)(ii)'s proof: `q′` fixed, `q_x(t) = q_{x0} + tη`, `P(t)` in `ker φ_{q_x(t)}`,
> `z(t) = Φ(P(t))`.
> - On `exh8` (every simple 2EC graph on ≤ 8 vertices, every eligible `x`): 4 736 of 4 736 needed
>   instances.
> - On θ-graphs: 62 of 62 (`a + b + c ≤ 10`), and 69 of 69 (`11 ≤ a + b + c ≤ 13`). Both θ
>   populations are capped at 3 eligible `x` per graph.
>
> The gain is the mod-`p` rank of `S₀ᵀA₁K₀` along the curve's 1-jet. At a certified instance,
> `rank_p A₀ = rank_ℚ A₀`, so the gain is a lower bound for the ℚ-rank along the curve. Each instance
> is therefore a certificate that `X₀(G)` attains at that `G`. The census certifies this on ≤ 8
> vertices anyway; what is new is the mechanism.
> *Control:* the curve that moves `x` along the line keeps every point special. Its gain is asserted
> to be `0`, and it is `0` at all 63 instances of `--control --exh 6`.
> **This is not a class statement.** No argument is known that the gain is positive in general.

**Measured cells** (`splitext.py --exh 8` histogram of `(dim U, c, δ)`, 4 751 certified
instances):
- `dim U = 0`: 3 247 instances, all with `δ = 0`. This is the orbit-(iv) remark after (MC-26).
- `dim U = 1`: 1 017 instances, `c = 1`, `δ ≤ 1`. Here the ear restriction is **not** dominant
  (MC-18)(b). *(2026-09-24: `δ ≤ 1` is explained by (MC-91): 1 013 of these have `δ₂ = 1`. The other 4
  have `δ₂ = 0` at a picture that jumps for `G′`, so their recorded `dim U` is an artifact of the
  picture; see (MC-91)(d).)*
- `dim U = 2`: 374 instances, and `dim U = 3`: 113 instances, all with `c = 2`.

So `def₂` rises exactly at the 487 instances with `dim U ≥ 2`, as (MC-30)(iii) requires. `δ ≥ 5`
occurs at exactly 15 instances, the pairs `(C₇, x)` and `(C₈, x)`. On the θ populations it occurs at
33 instances.

**How this relates to Step MC10.**
- *(MC-18)(b), `k = 1`.* The ear route takes its induction hypothesis at `G′ = G − x`. It needs
  dominance (`dim U ≠ 1`), `λ = 2` (not orbit (iii)), (R₁) and (P₁). The split-off route takes its
  hypothesis at `G″ = G′ + ab` instead. That graph has the same number of vertices, and it is the
  chord gadget that (MC-24) sets aside for (R₁) because a chord is not dominant.
  - It needs no dominance. It sits exactly at the placement on `p_a p_b` that (MC-22) excludes (orbit
    (iii), or orbit (iv) when `U = 0`).
  - It covers the 1 017 non-dominant instances above, up to the one missing `+1`.
- *(MC-27)'s `k = 1` cell.* That cell stays open as stated, because (MC-27) is the ear route's
  placement lemma. The split-off step closes the `k = 1` step by another route when `δ ≥ 5` (MC-31).
  On ≤ 8 vertices, and on the θ populations, the `δ ≥ 5` instances are cycles and θ-graphs, which
  already attain by (MC-21). So (MC-31) proves nothing new on the tested graphs. Its content is the
  general statement.
- *The same statement, found independently.* The 2026-09-24 recon of W4-reopen's third unranked
  direction (the `X₀` hybrid) reached (MC-28) + (MC-31) as a "subdivision" step, without the
  `X₀`-membership half, which (MC-30) supplies. It found that the step fires ahead of the cycle base
  case at no graph on ≤ 8 vertices. That is consistent: the only `δ ≥ 5` instances there are `C₇` and
  `C₈`.
- *What is still missing.* For `δ ≤ 4`, the `+1` must come from leaving the special position. That
  is a first-order statement about moving `x` off `p_a p_b` together with the heights, on `X₀(G)`.
  The direction-2 recon judged that making it uniform meets `notes/pencil/strategy.md` §2.4's Schubert/`V_bc` wall,
  which gives per-shape answers only. That judgment was not re-checked here. (MC-32) finds the `+1` at
  every instance tested.

**What would change this:**
- an instance where `splitext.py` fails the `+5` assert (then (MC-28)'s motion count is wrong);
- a certified `q′` with `U = Kℓ_ab` (then (MC-4)(b) is wrong);
- a certified instance where `def₂` rises with `c ≠ 2`;
- a needed instance whose first-order gain stays `0` under many jets. That would not refute
  anything, but it would locate a shape where the `+1` is not first order.

**Drivers** (all at `PYTHONHASHSEED=0`, seed `20260924`; exact ℚ for the flex spaces, `U`, `φ₀` and
the curve; ranks mod `2⁶¹ − 1` only as certificates or lower bounds; sampler support is in the
docstring):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/splitext.py --exh 7` | 417 instances (331 / 79 / 7 by `(Δdef₃, Δdef₂) = (0,0) / (0,1) / (1,1)`, printed `ddef3`/`ddef2`); all certified; gain `≥` needed 417/417 | 15 s |
| `python3 notes/scripts/w4/splitext.py --exh 8` | 4 751 (4 264 / 472 / 15); all certified; gain `≥` needed 4 751/4 751 | 220–265 s |
| `python3 notes/scripts/w4/splitext.py --thetas 10` | 65 (cap 3 per graph; 5 / 57 / 3); all certified | 2.7 s |
| `python3 notes/scripts/w4/splitext.py --thetas 13 --smin 11` | 99 (cap 3; 0 / 69 / 30); all certified | 8.3 s |
| `python3 notes/scripts/w4/splitext.py --thetas 13 --smin 11 --perg 1` | 33 (25 / 8): the recon's population | 2.6 s |
| `python3 notes/scripts/w4/splitext.py --control --exh 6` | 63; along-line control gain 0 at 63 | 2.3 s |

The recon's scratch-probe figures reproduce class for class: 417 (331 / 79 / 7), 65 (5 / 57 / 3)
and 33 (25 / 8), so 515 instances, 18 of which close outright. Its θ figures carried caps it did not
state, 3 and 1 eligible `x` per graph; `splitext.py` prints its caps.

#### Jackson–Jordán beyond ℝ — a second reading (2026-09-24)

*The question (`notes/Phase39-design.md`, field-hypothesis recon, row S5: "unverified beyond ℝ").*
Jackson–Jordán's pin-collinear theorem is used here only in (MC-4)(b)'s equality form. Does it hold
over every infinite field? Through Step MC4, `F(q)` is their rod-and-pin null space. The dictionary:
- JJ's pin-line `L_v : p₁x + p₂y = 1` is dual to `q_v`, with `p(v) = −q_v`;
- the pin `L_u ∩ L_v` is `ℓ_uv`, as a homogeneous point;
- the motion vectors change by `diag(1, −1, 1)`, because JJ's `P(e) = (x_e, −y_e, 1)` (TR p.10).

The dictionary is valid wherever no edge line passes through the origin, which holds generically. So
the (MC-4) form is exactly their Thm 7.1 (TR p.21). The TR was read twice: by the 2026-09-24
recon of W4-reopen's second unranked direction, and then by a second reader who re-derived each row
of the table below. Page numbers are as
printed.

> **(MC-33)** *(Jackson–Jordán's rank formula over an infinite field)*
> **(i)** `[INFORMAL]` *(gaps: a written field-general proof; the non-degeneracy of each constructed
> realization, bypass R2, was checked at sketch level only)* Thm 6.1 and Thm 7.1 (TR pp.14, 21)
> hold over every infinite field `K`, of any characteristic. "Generic" means "in a nonempty
> Zariski-open subset of `K^{2V}`" rather than "algebraically independent over ℚ". The proof needs
> two repairs (R0, R1) and one bypass (R2), listed below. Characteristics 2 and 3 are not special.
> **(ii)** `[MEASURED]` *(`jjchar.py`)* At every simple 2EC graph on ≤ 8 vertices (7 980 graphs), some
> admissible `q` over each of GF(2¹⁶), GF(3¹⁰), GF(101) and GF(10 007) has `dim L(q) = 3 + def₂`.
> Each such line is a finite theorem: for that graph, `ℓ₀ = 3 + def₂` over every infinite field of
> characteristic 2, 3, 101 or 10 007.

*Why each line of (ii) is a theorem.*
- The lower bound `dim L(q) ≥ 3 + def₂` holds over every field (MC-4)(b).
- The matrix `M(q)` of Step MC2 has entries that are polynomials over the prime field. So a nonzero
  minor at one point over `GF(pᵏ)` is a nonzero polynomial over `GF(p)`. It does not vanish at
  generic points of any infinite field of characteristic `p`, and neither does the admissibility
  polynomial.
- Step MC4's bijection `F(q) = L(q)` is field-free. It is asserted in rank form at every draw.

*The reading, step by step* (TR-2006-06; "Zariski" means: the Euclidean `ε`-move is replaced by "all
but finitely many values of a parameter on an irreducible line, pencil or plane containing the
original position", and each extra condition in the move was checked to exclude only finitely many
values):

| TR step (page) | what it uses | verdict |
|---|---|---|
| bar-joint rigidity matrix, Lemma 2.1 `r ≤ 2n − 3` (p.3) | the dot product; three trivial motions (two translations and `m_v = Jq_v`, `J` antisymmetric, so `d·Jd = 0` in every characteristic) | field-free |
| Lemma 2.2(a) (p.4) | specialization of the generic rank | field-free |
| Lemma 2.2(b) (p.4) | an `ε`-ball | Zariski form: `{q′ : r(G, q′) ≥ r(G, q)}` is open and contains `q` |
| Lemmas 2.3 (0-extension), 2.4 (1-extension, cited from Whiteley), 2.5 (vertex split) (pp.4–5) | linear algebra; 2.4 needs `Q ≠ q(v₁), q(v₂)`, and `s(s − 1) ≠ 0` works in every characteristic | field-free (2.4 re-derived) |
| Lemma 2.6 (p.5; stated, "proved similarly") | trivial motions of the two rigid parts must agree on `X` | field-free (proof supplied through Lemma 2.9) |
| Lemmas 2.7, 2.8, 2.9 (pp.5–6) | completing to `K_n` on a spanning point set, which is rigid by 0-extensions; `f_S` with `M_S` antisymmetric | field-free |
| §3, Lemma 4.1 (pp.6–9) | combinatorics; Lemma 2.1 on each part | field-free |
| degree-1 pin-line convention (p.9) | "the line through `q(p)` orthogonal to `q(v)q(p)`" | **R0 (cosmetic).** At an isotropic direction (`(1,1)` in characteristic 2; any field containing `√−1`) this line contains `q(v)`. Make the pin-line of a degree-1 body a free datum through its pin. `r(G*, q)` does not depend on it |
| Lemma 4.2 (p.9) | `ε`-moves of pins along their pin-lines; "a small rotation of `L(u)` about `q(uv)`" | **doubtful as written, over ℝ as well:** if `u` has two edges `uv`, `uv₁` with `L(u) = L(v) = L(v₁)` (a triangle with one common pin-line), the pin `uv₁` is forced onto `L′ ∩ L(u) = q(uv)`. **R2 (bypass):** carry "non-degenerate" in the induction. Every construction below has generic free choices (R1 supplies them at the gluing), so each constructed realization can be taken non-degenerate. Lemma 4.2 is then never needed |
| Lemma 5.1 (p.11) | Lemma 2.9 on each rigid body `B_v` | field-free |
| Lemma 5.2 (p.13) | generic rod-and-pin rank `≥` rank at a non-degenerate realization | Zariski form (semicontinuity on `K^{2V}`, which is irreducible); needed only for non-degenerate realizations under R2 |
| "pin-line-generic" realizations (p.13): no two pin-lines parallel, each pin on exactly two lines, restriction to a subgraph generic | finitely many nonzero polynomials | Zariski: finitely many nonempty open conditions, intersected |
| Claims 6.2–6.4 (pp.14–15) | disjoint union; 0-extensions; `Q = L(u₁) ∩ L(u₂)`; Lemma 2.7 with `t = 1` | field-free |
| Claim 6.5, same brick and Case 3 (pp.15–18) | 0-extensions only | field-free |
| Claim 6.5 Case 1 (p.16) | `r(G₂*) ≥ r(G₁*) + 3` gives three bars at `p₀` (needs `q(u₁), q(u₂), p₀` non-collinear; body points are free); `ε`-move of `p₀` along `L(u₁)`; 1-extension with `Q₂ = L′ ∩ L(u₂)`, `L′` the line `Q₁ q(u₂)` | Zariski on `L(u₁) ≅ K`: the rank condition is cofinite, and each of `Q₁ ∉ L(u₂)`, `L′ ∦ L(u₂)`, `Q₂ ≠` each pin of `u₂` excludes one point (central projection from `q(u₂)` is a bijection `L(u₁) → L(u₂)`) |
| **Claim 6.5 Case 2** (pp.16–17): the step the first reading flagged | two 1-extensions on `L(z)`; vertex split (Lemma 2.5); "small rotation of `L(z)` about `q₅(p₃)`" with `p_i = L′ ∩ L_i` (`4 ≤ i ≤ j`); `ε`-move of `q₅(u₂)`; a final 1-extension and a 0-extension | **field-free in Zariski form.** Parametrize `L′` by its slope in the pencil at `Q₃` (a `P¹`): `p_i := L′ ∩ L_i`, and `p₁` is any point of `L′` depending rationally on the slope (the TR's "`L_1`" is undefined, a slip: `p₁` needs only to lie on `L′`). The rank condition is cofinite, and pin distinctness, `L′ ≠ L(z)` and `q(u₁) ∉ L′` each exclude finitely many slopes. The move of `u₂` is Zariski on `K²`. The subframework `F` is rigid by a determinant (`z ∉ L(z)`), not a metric. No ordered-field use |
| Claims 6.6–6.9 (pp.18–19) | 0-extensions; in 6.8, the rotation of one side about the cut pin `p₂` is blocked by the bar `p₁v` iff `det(q(p₁) − q(v), q(v) − q(p₂)) ≠ 0`; a Zariski move of `q₁(v)` | field-free |
| Claim 6.10 (a), (b) (p.19) | combinatorics | field-free |
| **final gluing** (pp.19–20) | "translation, rotation, and dilation" matching `q₁(p₃) = q₂(p₆)`, `q₁(p₅) = q₂(p₇)` | **R1 (repair; the first reading's).** Use an invertible affine map. Bar-joint rank is invariant under it over any field, since `R(G, Aq + b) = R(G, q)·diag(Aᵀ)`. Two point conditions leave a 2-parameter family, which also makes the glued realization non-degenerate for R2. (Similarities cannot map an isotropic segment to a non-isotropic one over a field containing `√−1`, nor in characteristic 2.) Lemma 2.7 with `t = 2` and the rank counts via Lemma 2.3 are field-free |
| Thm 7.1 (p.21) | Thm 6.1 plus Lemmas 5.1, 5.2 | field-free; genericity in Zariski form |

What was re-derived and what was taken on trust:
- **Re-derived:** every row above, including the two lemmas the TR does not prove (2.4, cited from
  Whiteley; 2.6, "proved similarly"), and the Step MC4 dictionary.
- **Taken on trust:** the brick and superbrick lemmas (3.2, 3.3, from Jackson–Jordán's molecular
  paper [5]) and the claims' deficiency inequalities. These are combinatorial and field-free, but
  they were not re-proved.
- **Checked at sketch level only:** that each construction can be made non-degenerate (R2).

No step divides by an integer or uses an order.

**What would change this:**
- a step of the TR that needs a metric property beyond the bilinear dot product;
- a construction whose free choices cannot avoid a degenerate pair (R2);
- a graph and a characteristic where `jjchar.py` never exhibits the equality (an upper bound per
  draw, so this would prompt a search, not a refutation).

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/jjchar.py --selftest` | 5 non-fields rejected, 6 fields accepted; OK | 0.4 s |
| `python3 notes/scripts/w4/jjchar.py --exh 7` | 577/577 in each of the four fields | 2.7 s |
| `python3 notes/scripts/w4/jjchar.py --exh 8` | 7 980/7 980 in each of GF(2¹⁶), GF(3¹⁰), GF(101), GF(10 007) | 35–43 s |
| `python3 notes/scripts/w4/jjchar.py --battery --thetas 12` | 9/9 and 43/43 in each field | 0.5 s |

Arithmetic is exact in each named field. There these ranks are the object, not a proxy for ℚ, so
the harness's "GF(p) only as a bound for ℚ" rule does not apply. The GF(2¹⁶) and GF(3¹⁰)
constructors assert that `X` has order `q − 1`, which makes the polynomial primitive and so the
quotient a field. They also check the table arithmetic against slow polynomial arithmetic.

