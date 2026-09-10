## §(K-Λ) — the Λ-compression's quadric: a two-hyperplane factorization, and why (K-Λ) collapses onto (K-wit) (**(K-Λ) REFUTED as an independent gap; `ℓ ∈ {5,6}` refuted through the (T5) frame**)

Answering the fan-out's **direction B** (`notes/pencil/fanout-archive.md` §"Direction B").
Read against §(K-pitch) *Steps 0–5b*, whose notation it inherits verbatim.

**Headline, stated up front because it is a correction.** (K-Λ) was recorded
(§(K-pitch) *Step 5b*) as *"some target-rank chart seed's far covector `λ` avoids
the local quadric `{Φ_loc = 0}`"*, with the flagged risk *"a companion habitat
whose `Φ_loc` is the zero form"*. Both halves of that framing are wrong:

- `Φ_loc` is **never** the zero form. It is never a full-rank quadric either: it
  is always a **rank-2** form, the product of two *distinct rational linear*
  forms in `λ`. The flagged degeneration is impossible; there is nothing to prove
  on the non-degeneracy side. **(Λ1)** below is the exact bracket identity.
- Consequently "avoid the quadric" is "avoid two hyperplanes". And once the one
  local freedom that leaves `V_bc` untouched — `pt(a)` sliding along the meet
  line `M`, (T4)'s freedom — is used, the set of far covectors that are bad for
  the **whole** `a`-line shrinks from two hyperplanes to exactly **two points**
  of `P³`, and those two points are:
  `λ ∝ p⁺` ⟺ `V_bc ⊆ C(M)^{⊥B}` — which by (T3) **is** the genuine escape
  failure; and `λ ∝ q` ⟺ `V_bc ⊆ C(bc)^{⊥B}` — whereupon (T1) forces
  `★r ∝ C(bc)` and **route A escapes outright**.

So: **(K-Λ) at a length-4-companion split is *equivalent* to (K-wit) there.** The
pitch certificate is blind only where the escape actually fails. (K-Λ) is
therefore **not an independent gap** and no local argument can close it —
closing it *is* closing (K-wit). What the analysis does buy is positive and
standalone: the length-3 bracket **monomial** of §(K-pitch) *Step 5* becomes, at
length 4, a **product of two bracket-linear forms in the far covector**, whose
two factors are exactly (T2)'s two failure modes; the length-3 case gets a
two-line proof that explains its five brackets; both bad far covectors turn out
to lie on **one line** of `P(S*)`, giving the far-side sufficient condition
**(OUT)** (*Step 5a*); and the `ℓ ∈ {5,6}` continuation is **refuted** through
this frame, with the obstruction located exactly.

### Standing notation (on top of §(K-pitch))

Split chain `b–v–a–c` at a hard-stratum target-rank `G′`-seed (`b, c` hubs,
`dim R_a = 1`); `H := G − v − a`; `V_bc` the relative twist system (`dim = 3`);
`T := ⟨C_ab, C_ac⟩`; `B(x,y) = ⟨x, ★y⟩`, `Q(x) = B(x,x)`;
`M := Π(b) ∩ Π(c)` the meet line, `pt(a) ∈ M`, and `π_a := plane(a,b,c)`.
`α_p := Λ²(lines through p)` and `β_π := Λ²(lines in π)` — the two families of
maximal isotropic 3-spaces (α- and β-planes) of the Klein quadric. (These are
§(K-pure)'s `α(u)` and `Λ²π̂`: `α_{pt(a)} = α(a)` and `β_{π_a} = Λ²π̂`.)

A **length-4 companion** is a path `b–x₁–x₂–x₃–c` of `H` with lines
`C_i := C(x_{i−1}x_i)` (`x₀ = b`, `x₄ = c`) and `S := ⟨C₁,…,C₄⟩`; path-sum
containment (§(K-pitch) *Step 1a*) gives `V_bc ⊆ S`, and `λ ∈ S*` is the
annihilator of `V_bc` in the `C`-basis. Five bracket rows, all 4-point brackets
via the pairing dictionary `B(C(uv), C(pq)) = [u,v,p,q]`:

```
m_i = [x_{i−1}, x_i, a, b]     (m₁ = 0: C₁ and C_ab meet at pt(b))
n_i = [x_{i−1}, x_i, a, c]     (n₄ = 0: C₄ and C_ac meet at pt(c))
q_i = [x_{i−1}, x_i, b, c]     (q₁ = q₄ = 0: C₁, C₄ meet line(bc))
s_i = [x_{i−1}, x_i, a, w]     (w any point off π_a)
p⁺_i = [x_{i−1}, x_i, M₀, M₁]  (M₀, M₁ two points spanning M)
```

`cof(u)` := the Laplace cofactor vector of the `3×4` matrix `[u; m; n]` (the
existing `pitch.cross4`), so `z(λ) = Σ_i cof(λ)_i C_i` is the (T5)
Λ-compressed reciprocal twist and `Φ_loc(λ) := Q(z(λ))`.

**(Λ0) the named local genericity — all of it explicit brackets.**
(a) `rank{C₁..C₄} = 4`; (b) `S ∩ T = 0`; (c) `rank[m; n] = 2`
(⟺ `dim(S ∩ T^{⊥B}) = 2`); (d) **panels mutually non-incident**,
`pt(c) ∉ Π(b)` *and* `pt(b) ∉ Π(c)` (the §(K-pitch) *Step 6a* chart condition,
needed in **both** directions — see *Step 6*); (e) `C(M) ∉ S`;
(f) **`p⁺₂, p⁺₃ ≠ 0` and `q₂, q₃ ≠ 0`** — i.e. neither middle companion line
`C₂ = C(x₁x₂)`, `C₃ = C(x₂x₃)` meets `M`, and neither meets `line(bc)`. (The
outer entries vanish *structurally*: `C₁ ⊆ Π(b)` and `C₄ ⊆ Π(c)`, both panels
contain `M`, and two lines of one plane always meet — so `p⁺ = (0, p⁺₂, p⁺₃, 0)`
and `q = (0, q₂, q₃, 0)` always. (f) is exactly the span condition of *Step 3*;
the equivalence is asserted both ways per frame, and its necessity is
*constructed* in *Step 6*.)

Each clause is an open condition on the **local** chart of the frame
`{b, x₁, x₂, x₃, c, a, Π(b), Π(c)}`, which is the same irreducible variety for
every class habitat carrying a length-4 companion — the far graph enters the
frame only through (i) which of `x₁, x₂, x₃` are hubs and (ii) how many *far*
hub neighbours each frame hub has (`≤ 2` in total, by `hcard`), each of which
merely shrinks that hub's normal space to a generic subspace. So exact
witnesses across those finitely many strata certify (Λ0) generically for the
whole class; that is what the `--span` battery is: **38 strata** — the 2³ hub
patterns of `(x₁,x₂,x₃)` × far-hub counts `0/1/2` at `b, c`, plus, for each
pattern with a companion hub, two strata that additionally load the *companion*
hubs with `1` and with the maximal `2` far hub neighbours (the tightest
stratum: those normals are then pinned up to scale).

> **(Λ0) IS NOW PROVEN AT THE GENERIC POINT — and the 38 strata turn out to be
> irrelevant there** (2026-08-05, `M2 --script notes/scripts/m2/lambda0.m2`).
> The paragraph above is the *argument*; it is now executed rather than
> sampled. Gauge `ν_b = e₀*`, `ν_c = e₁*` (GL(4) is transitive on ordered pairs
> of independent covectors), so `Π(b) = {X₀=0}`, `Π(c) = {X₁=0}`,
> `M = ⟨e₂,e₃⟩`, `pt(a(t)) = e₂ + t·e₃`; the residual group then puts
> `P_b = e₁`, `P_c = e₀` **whenever (Λ0d) holds**, leaving 14 free coordinates
> (`x₁ ∈ Π(b)`, `x₃ ∈ Π(c)`, `x₂` free, `w` free). On that slice:
>
> - the bracket rows have **closed forms**
>   `p⁺ = (0, −u₁y₀, −y₁v₀, 0)` and `q = (0, u₃y₂−u₂y₃, y₃v₂−y₂v₃, 0)`,
>   so the structural zeros `p⁺₁ = p⁺₄ = q₁ = q₄ = 0` are visible rather than
>   argued, and (Λ0f)'s four brackets are explicit monomials/`2×2` brackets;
> - **every clause (a)–(f) is a nonzero polynomial**, hence holds on a dense
>   open subset — this is what replaces "certified generic by exact witnesses
>   in all 38 strata";
> - **the strata do not enter.** A stratum fixes which frame nodes are hubs and
>   how many far hub neighbours they carry; neither datum appears in any (Λ0)
>   quantity, and every stratum's frame data can be *completed* from a point of
>   the slice (a companion hub takes the panel `plane(x_{i−1},x_i,x_{i+1})`,
>   which satisfies the pencil condition there by construction; a far hub
>   neighbour is a free far-graph point, so it is placed inside that panel, and
>   `hcard` caps the count at 2 so the normal space never drops below dimension
>   1). So each stratum maps **onto a dense subset of one irreducible variety**
>   — driver block (P6), and the *class-uniformity bridge* of the verdict below.
>
> The gauge **consumes (Λ0d)**, so the driver's block (P7) re-runs the core with
> only `ν_b, ν_c` gauged (20 indeterminates): (Λ0d) reappears there as the
> non-vanishing of `ν_b·P_c` and `ν_c·P_b`, and the structural zeros,
> degree bounds and containments all survive — the `P_b`/`P_c` half of the
> gauge is not load-bearing.

### Step 1 — Witt: the isotropic locus of `T^{⊥B}` is `α_a ∪ β_{π_a}`

`T` is 2-dimensional and totally `B`-isotropic (both lines pass through
`pt(a)`), and the Klein form on `Λ²K⁴` is **split of Witt index 3**. Hence
`dim T^{⊥B} = 4`, `T ⊆ T^{⊥B}`, and `T^{⊥B}/T` is nondegenerate of dimension 2
and index `3 − 2 = 1`: a **hyperbolic plane**. `Q` descends to the quotient
(`Q(x + t) = Q(x)` for `x ∈ T^{⊥B}`, `t ∈ T`), a hyperbolic plane has exactly
two isotropic lines, both rational, and their preimages are two *maximal*
isotropic 3-spaces containing the pencil `T`. The only maximal isotropics
containing the pencil of lines through `pt(a)` in `π_a` are `α_{pt(a)}` and
`β_{π_a}`. Therefore

> **(Λ0′)** `{x ∈ T^{⊥B} : Q(x) = 0} = α_{pt(a)} ∪ β_{π_a}`.

This is (T2)'s failure dichotomy *(F-A)*/*(F-B)*, now with its reason: Witt's
theorem, not a case analysis.

**Relation to (PC-Z) — the same structural theorem, derived independently; not
restated here.** §(K-pure) *Step P3*'s **(PC-Z)** is the canonical, `V_bc`-level
statement of this fact (in its notation `α(a) = α_{pt(a)}` and
`Λ²π̂ = β_{π_a}`), derived there from the classical α/β-plane classification of
the Klein quadric; the Witt argument above is its **reason**. The two
derivations were produced independently — fan-out directions C and B, neither
consuming the other — and agree; that is **evidence, not a second result**. Read
(PC-Z) for the `V_bc`-level form; it is not restated here, and the Witt argument
is not restated there.

Two things fall out immediately.

**(i) Why `ℓ = 3` closes — a two-line replacement for §(K-pitch) *Step 5*'s
monomial.** `z` spans `V_bc ∩ T^{⊥B} ⊆ S ∩ T^{⊥B}`, so if
`S ∩ α_a = S ∩ β_{π_a} = 0` then `Q(z) ≠ 0` for the trivial reason that
`z ≠ 0`. At a length-3 companion `S = V_bc` is 3-dimensional and
`dim(S ∩ α_a) = 3 + 3 − 6 = 0` generically — likewise `β`. So **Step 5's
five-bracket monomial is the coordinate form of two transversality
conditions**, and the closure at θ(3,3,6)-type splits needs no monomial
computation at all. (Exact: `--habitat`, θ(3,3,6), both intersections `0` and
`Q(r) ≠ 0` at 3/3 seeds.)

**(ii) The obstruction, indexed by companion length.**
`dim(S ∩ α_a) = dim(S ∩ β_{π_a}) = k − 3` at a length-`k` companion
(`= 0, 1, 2, 3` for `k = 3, 4, 5, 6`; exact at 3 frames each,
`--l56`). `k = 4` is the **last** length at which these are 1-dimensional —
i.e. the last length at which "`V_bc` *meets* the intersection" is the same
condition as "`V_bc` *contains* it". That single fact is why the argument below
closes at `k = 4` and provably cannot at `k ≥ 5` (*Step 7*).

### Step 2 — (Λ1): `Φ_loc` factors into two bracket-linear forms

At `k = 4`, put

> `ω⁺ := cof(s)` — spans `S ∩ α_{pt(a)}`: **the unique line of the companion
> span through `pt(a)`**;
> `ω⁻ := cof(q)` — spans `S ∩ β_{π_a}`: **the unique line of the companion
> span lying in `plane(a,b,c)`**.

(Both are `cof(·)`-shaped because `α_a = ⟨C_ab, C_ac, C(a,w)⟩` and
`β_{π_a} = ⟨C_ab, C_ac, C(bc)⟩`, so membership is the vanishing of `m·ω`,
`n·ω` and one further bracket row.) Both lie in `N := S ∩ T^{⊥B}`, which
under (Λ0a–c) is 2-dimensional and — by Step 1 and `S ∩ T = 0`, so that
`N ≅ T^{⊥B}/T` as quadratic spaces — a **hyperbolic plane**. So `ω⁺`, `ω⁻` are
its two isotropic lines: distinct, rational, and `B(ω⁺, ω⁻) ≠ 0`.

> **(Λ1)** `(q·ω⁺)² · Φ_loc(λ) = −2 · B(ω⁺, ω⁻) · (λ·ω⁺) · (λ·ω⁻)`,
> an identity of quadratic forms in `λ`, with *every* entry a polynomial in the
> 4-point brackets of the six local points `{b, x₁, x₂, x₃, c, a}` (plus `w`,
> which cancels projectively). In particular `Φ_loc` is a **nonzero rank-2**
> form and `{Φ_loc = 0}` is the union of the two **distinct rational
> hyperplanes** `{λ·ω⁺ = 0}` and `{λ·ω⁻ = 0}`.

*Proof.* `λ ↦ cof(λ)` is linear with kernel `⟨m, n⟩` and image `N` (the two
conditions `m·ω = n·ω = 0` say exactly `z ∈ T^{⊥B}`). In the basis
`(ω⁺, ω⁻)` of `N` write `cof(λ) = α(λ)ω⁺ + β(λ)ω⁻`; `cof(λ) ⊥ λ` and
`m·ω± = n·ω± = 0` give `α(λ)(λ·ω⁺) + β(λ)(λ·ω⁻) = 0`, so
`cof(λ) = κ·[(λ·ω⁻)ω⁺ − (λ·ω⁺)ω⁻]` with `κ` independent of `λ` (two
proportional linear maps). Then
`Q(cof λ) = −2κ²(λ·ω⁺)(λ·ω⁻)B(ω⁺,ω⁻)`. Expanding `λ·cof(λ) = 0` at
`λ = σs + τq + (⟨m,n⟩-part)` gives `s·ω⁺ = q·ω⁻ = 0` and `s·ω⁻ = −q·ω⁺`, and
evaluating at `λ = s` (where `cof(s) = ω⁺`) pins `κ² = 1/(q·ω⁺)²`. ∎
(The driver verifies the identity with the scalar **exactly 1**, i.e. with the
`pitch.cross4` normalization of `cof` there is no residual constant. The
symbolic check below pins the *sign* as well: `κ = −1/(q·ω⁺)`.)

*Exact, per frame:* `--witt` computes `Φ_loc`'s `4×4` matrix from the linear map
`λ ↦ cof(λ)` and the banded Gram, and asserts `rank = 2`, `Φ_loc ≠ 0`,
`ω± ∈ S ∩ α/β` and that they *are* line extensors, and **(Λ1) with the scalar
exactly 1** (i.e. `(q·ω⁺)²·PhiM = −B(ω⁺,ω⁻)(ω⁺ω⁻ᵀ + ω⁻ω⁺ᵀ)`, all 16 entries)
— 23 frames: 5 hub-pattern strata × 3 local frames, plus 2 seeds at each of
four habitats.

**Symbolic, over the function field — (Λ1) is an IDENTITY, not 23 samples**
(2026-08-05, `M2 --script notes/scripts/m2/lambda1.m2`, the harness's first
Macaulay2 driver). Treating the frame's coordinates as indeterminates upgrades
(Λ1) from per-frame evidence to a statement about *every* frame at once. What
the driver establishes, in four blocks:

- **(M1) the universal cofactor identity**, with `m, n, q, s, λ` **free**
  covectors in `K⁴` (20 indeterminates, no geometry, no gauge):
  `(q·ω⁺)·cof(λ) = (λ·ω⁺)·ω⁻ − (λ·ω⁻)·ω⁺`. This is the *Proof* above's
  `cof(λ) = κ[(λ·ω⁻)ω⁺ − (λ·ω⁺)ω⁻]` together with its normalization, and it
  holds with no hypotheses whatsoever.
- **(M2) the universal quadratic expansion**, same 20 indeterminates plus a
  **free symmetric Gram** (30 in all): squaring (M1) gives
  `(q·ω⁺)²Φ_loc(λ) = (λ·ω⁺)²Q(ω⁻) − 2(λ·ω⁺)(λ·ω⁻)B(ω⁺,ω⁻) + (λ·ω⁻)²Q(ω⁺)`.
  So `Q(ω⁺) = Q(ω⁻) = 0` is the **only** geometric input (Λ1) has.
- **(M3) the α/β isotropy lemma**, gauge-free (four free points): each of
  `⟨C_ab, C_ac, C_aw⟩` and `⟨C_ab, C_ac, C_bc⟩` is totally isotropic and
  3-dimensional over the function field, hence maximal isotropic, hence
  self-`B`-perp — so anything `B`-orthogonal to one of them lies *inside* it.
  That is exactly `Q(ω⁺) = Q(ω⁻) = 0`, since `m·ω = n·ω = s·ω = 0` (resp.
  `q·ω = 0`) *is* `B`-orthogonality to those three lines. **(M1)+(M2)+(M3) is a
  gauge-free proof of (Λ1)** — the Step-1 Witt argument reappears here as the
  self-perpendicularity of a maximal isotropic, computed rather than quoted.
- **(M4) (Λ1) end-to-end**, both in its 16-entry matrix form and in the scalar
  form above, on the gauge slice `b, x₁, x₂, x₃ = e₀, e₁, e₂, e₃` with `a`, `c`,
  `w` and the far covector `λ` free. Both sides are bracket polynomials, hence
  GL(4) relative invariants of the same weight 13, and `g = [b|x₁|x₂|x₃]⁻¹` is
  the *unique* element of GL(4) carrying an independent quadruple to the
  standard basis — so the slice meets every orbit exactly once and vanishing on
  it is vanishing identically. The same run re-derives generically, rather than
  per frame, the structural zeros `m₁ = n₄ = q₁ = q₄ = 0`, the banded Gram,
  `ω±` nonzero line extensors with `ω⁺` through `pt(a)` and `ω⁻` inside
  `plane(a,b,c)`, `q·ω⁺ ≠ 0`, `B(ω⁺,ω⁻) ≠ 0`, the scalar exactly 1, and
  `rank Φ_loc = 2`.

**Two things this adds beyond confirming the 23 frames.**

1. **(Λ1) needs none of (Λ0), and none of the panel data.** In (M4) the points
   `a, c, w` and the covector `λ` are free — in particular `pt(a)` is *not*
   constrained to the meet line `M`, and no panel non-incidence is assumed. The
   identity is unconditional; (Λ0a–f) is what makes its ingredients **nonzero**
   (`ω± ≠ 0`, `q·ω⁺ ≠ 0`, `B(ω⁺,ω⁻) ≠ 0`, `rank[m;n] = 2`), and the driver shows
   each of those is nonzero *as a polynomial*, i.e. off a proper closed subset.
   So "(Λ1) under (Λ0)" is really "(Λ1) always, with (Λ0) securing the
   normalization" — a cleaner statement than the one the per-frame battery
   could support.
2. **`rank Φ_loc = 2` is now generic, not observed.** Previously 23 frames;
   now it follows from the identity plus `B(ω⁺,ω⁻) ≠ 0` and
   `rank[ω⁺; ω⁻] = 2`, both verified as polynomial non-vanishing.

*Feasibility, measured — the boundary a successor should budget for.* The
**ungauged** end-to-end expansion (all 28 point coordinates indeterminate) has
degree 52 and does **not** finish: killed at 600 s inside `cross4` on the
ungauged bracket rows. The local frame is symbolically viable; a whole-graph
placement is not (`notes/pencil/strategy.md` §5.3). That probe is recorded as
*measured, script not retained* — it is (M4) with the gauge removed, a one-line
edit of the committed driver (`notes/scripts/m2/README.md`).

*Standing of this output.* Evidence for this workbook, at the same standing as
the exact-ℚ numerics — **never** a substitute for Lean. "Verified in Macaulay2"
is not a proof the project may cite in place of a formalization
(`DESIGN.md` *Formalize everything the argument uses*; `notes/scripts/m2/README.md`
convention 1). `lambda.py --witt` is **not** superseded: its 23 frames and its
recorded figures stand unchanged, and the two are cited together.

**This kills the flagged risk.** "`Φ_loc` the zero form" cannot happen under
(Λ0), and neither can `Φ_loc` be irreducible: the quadric is always a pair of
rational hyperplanes. Any attack aimed at "uniform non-degeneracy of `Φ_loc`"
is attacking something already free.

### Step 3 — the `a`-line spans: two hyperplanes shrink to two points

`V_bc`, `S` and `q` are **`a`-free** ((T4)'s observation: `a ∉ H`). Slide
`pt(a) = p₀ + t·d` along `M`. Then `m(t)`, `n(t)`, `s(t)` are linear in `t`, so
`ω⁺(t) = cof_t(s(t))` has degree `≤ 3` and `ω⁻(t) = cof_t(q)` degree `≤ 2`
(`q` constant). Geometrically:

- every `ω⁺(t)` is a line through the point `pt(a(t)) ∈ M`, hence **meets `M`**,
  hence `ω⁺(t) ∈ C(M)^{⊥B}`;
- every `ω⁻(t)` is a line in a plane containing `line(bc)`, hence **meets
  `line(bc)`**, hence `ω⁻(t) ∈ C(bc)^{⊥B}`.

Since `p⁺` and `q` are the coordinate forms of `B(·, C(M))` and `B(·, C(bc))`
on `S`, both containers are the 3-dimensional `S ∩ C(M)^{⊥B}` and
`S ∩ C(bc)^{⊥B}` (3-dimensional because `p⁺ ≠ 0 ≠ q`, i.e. some companion line
misses `M` resp. `line(bc)`). And the curves **fill their containers**:

> **(Λ0f), certified generic** — `span_t ω⁺(t) = S ∩ C(M)^{⊥B}` with
> annihilator `⟨p⁺⟩`, and `span_t ω⁻(t) = S ∩ C(bc)^{⊥B}` with annihilator
> `⟨q⟩`; both 3-dimensional, and `p⁺ ∦ q`. Equivalently, in brackets:
> `span_t ω⁺(t) = 3 ⟺ p⁺₂ ≠ 0 ≠ p⁺₃`, and `span_t ω⁻(t) = 3 ⟺ q₂ ≠ 0 ≠ q₃`.
> *Exact:* `--span`, **164 frames** — all 38 local-chart strata × 4 frames
> each, plus 3 seeds at each of the four habitats — every one with
> `(span ω⁺, span ω⁻, deg ω⁺, deg ω⁻) = (3, 3, 3, 2)`, both annihilators
> identified, and the bracket equivalence asserted in both directions.
> (The naive expectation `span ω⁺ = 4 = dim S`, which the degree count alone
> suggests and which would have closed (K-Λ) outright with no far-side
> condition at all, is **false** — this is the pass's decisive negative
> measurement, and the reason the verdict below is a refutation rather than a
> closure.)

**(Λ0f) PROVEN, and WIDER than stated** (2026-08-05, `m2/lambda0.m2`). The
containments and the degrees are now **identities** on the local frame's
generic point: `p⁺·ω⁺(t) ≡ 0` and `q·ω⁻(t) ≡ 0` in `t` *and* in the frame
coordinates, with `deg_t ω⁺ = 3` and `deg_t ω⁻ = 2` exactly. The *equality*
half — the curves filling their containers — comes out as a closed form.
Writing `g₁₃ = B(C₁,C₃)`, `g₁₄ = B(C₁,C₄)`, `g₂₄ = B(C₂,C₄)` for the three
surviving entries of the banded Gram of `S`, and taking the `cross4` of the
`t`-coefficient triples of each curve:

> **(Λ0f′) the exact span criterion.** For every coefficient triple `j`,
> `cross4(A_{j₀}, A_{j₁}, A_{j₂}) = (−1)^j w₃^{3−j} w₂^{j} · Π⁺ · p⁺` with
> `Π⁺ := p⁺₂ p⁺₃ g₁₃ g₁₄ g₂₄`, and `cross4(B₀,B₁,B₂) = Π⁻ · q` with
> `Π⁻ := q₂ q₃ g₁₃ g₁₄ g₂₄`. Hence, with `w` off `line(bc)` (which is implied
> by the standing `w ∉ π_a`, and is exactly what the four `w`-monomials
> `w₃³, w₃²w₂, w₃w₂², w₂³` express):
>
> `span_t ω⁺(t) = 3 ⟺ Π⁺ ≠ 0` and `span_t ω⁻(t) = 3 ⟺ Π⁻ ≠ 0`.

So the recorded bracket equivalence is **incomplete**: it carries `p⁺₂p⁺₃`
(resp. `q₂q₃`) but not the three Gram factors. Two of them are old news in
new clothing — `g₁₃g₂₄ ≠ 0` is exactly `rank Q|_S = 4` (the driver checks
`det Gram = (g₁₃g₂₄)²`), which `--witt` already asserts, though nothing linked
it to the span. **`g₁₄ = B(C₁,C₄) ≠ 0` is asserted nowhere in the harness**,
and it is a genuine clause, not a consequence: degenerating `C₄`'s direction
onto `C₁`'s (`v₂ = λu₂, v₃ = λu₃`) kills `g₁₄` while (Λ0a), (Λ0b), (Λ0c),
(Λ0e) and all four `p⁺`/`q` middle brackets **survive** — and both spans drop
(driver block (P5)). Geometrically `g₁₄ = [b, x₁, x₃, c]`, so the missing
clause reads: **the two outer companion lines `C₁ = C(bx₁)` and `C₄ = C(x₃c)`
must not meet.**

*No recorded figure moves.* All 164 sampled frames have `g₁₃g₁₄g₂₄ ≠ 0` — it
is generic — so the asserted equivalence never fired there and `--span`
reproduces unchanged. What was wrong was the *general statement*, which is
precisely the failure mode sampling cannot detect: a missing hypothesis that is
generically satisfied. `lambda.py` is left untouched (`notes/scripts/README.md`
§4 convention 5).

Combining with (Λ1) evaluated at each `t`: `Q(z(t)) = 0` ⟺
`λ·ω⁺(t) = 0` or `λ·ω⁻(t) = 0`. Both are polynomials in `t`
(degrees `≤ 3` and `≤ 2`) and `λ` is constant, so

> **(Λ2)** `Q(z(t)) ≡ 0` along the whole `a`-line ⟺ `λ ⊥ span_t ω⁺(t)` or
> `λ ⊥ span_t ω⁻(t)` ⟺ **`λ ∝ p⁺` or `λ ∝ q`** ⟺
> **`V_bc ⊆ C(M)^{⊥B}` or `V_bc ⊆ C(bc)^{⊥B}`**.

(Both equivalences are two lines of linear algebra: `V_bc = ker λ ∩ S` is a
hyperplane of `S`, so `V_bc ⊆ C(L)^{⊥B}` ⟺ the coordinate form of
`B(·, C(L))` annihilates `V_bc` ⟺ it is proportional to `λ`.)

So the bad far covectors are **two points of `P³`**, not a quadric's worth —
and each is structurally meaningful. (This rests on (Λ0f′) in full, whose one
previously-unasserted factor `g₁₄` is the subject of *Step 3a*: where `g₁₄`
vanishes, `span_t ω± = 2` and (Λ2) acquires a **third** branch — a whole
hyperplane of bad `λ` on each side, not a point. *Step 3a* settles that no
class habitat in the searched scope is confined to that locus.)

### Step 3a — the `g₁₄` clause, located (2026-08-05, `outer.py`)

*What would change this* item (vi) asked whether a **class habitat can force
`g₁₄ = 0` on its whole pencil chart**, which would put a third branch into
(Λ2) and force the completeness theorem to be restated. It cannot, in the
scope searched — and the reason is two elementary facts the arc had not
written down. Both are asserted per frame by `notes/scripts/w4/outer.py`.

> **(Λ0g) the geometric form.** `x₁ ∈ N_{G′}(b)` and `x₃ ∈ N_{G′}(c)`, so
> `C₁ = C(bx₁) ⊆ Π(b)` and `C₄ = C(x₃c) ⊆ Π(c)`. Both panels contain `M`,
> and two lines of a projective plane always meet, so **each outer companion
> line always meets `M`** — which is the structural vanishing
> `p⁺₁ = p⁺₄ = 0` read backwards. Two lines of `P³` meet iff they are
> coplanar, and a meet of `C₁ ⊆ Π(b)` with `C₄ ⊆ Π(c)` lies in
> `Π(b) ∩ Π(c) = M`. Hence, whenever `Π(b) ≠ Π(c)`,
>
> `g₁₄ = 0 ⟺ C₁ ∩ M = C₄ ∩ M` **as points of `M`**.

So the clause is not "two lines of space happen to meet" but "**two marked
points of the line `M` coincide**" — one equation, on the very line along
which `pt(a)` slides. (Asserted in both directions at every frame of `--geom`,
`--habitat` and `--sweep`; the meet is projective, so a line affinely parallel
to `M` meets it at `M`'s point at infinity, and two such lines coincide there.)

> **(Λ0i) the mobility criterion.** If `x₁` has degree 2 and its other
> neighbour `x₂` is not a hub, then `b` is `x₁`'s only hub neighbour and `x₁`
> carries no panel of its own, so `pt(x₁)`'s **only** chart constraint is
> `pt(x₁) ∈ Π(b)`: it sweeps a dense subset of that plane with the entire
> rest of the placement held fixed. `g₁₄` is affine in `pt(x₁)` with zero
> locus the plane `plane(b, x₃, c)`, so `g₁₄ ≡ 0` on the chart would force
> `Π(b) = plane(b, x₃, c)`, hence `pt(c) ∈ Π(b)` — a failure of **(Λ0d)**.
> Symmetrically with `x₃` free in `Π(c)` and the other half of (Λ0d).

**Consequence: wherever either companion end is free, the `g₁₄` clause is
*implied by* (Λ0d) and is not an independent hypothesis at all.** Measured
over the systematic sweep: **3628 of 4280** (split, companion) pairs are
covered by this criterion alone. The 652 that are not are all the single hub
pattern **`x₂` a hub** — the `2 + 2` via-hub companion `b–x₁–u–x₃–c`, where
`pt(x₁) ∈ Π(b) ∩ Π(u)` and `pt(x₃) ∈ Π(u) ∩ Π(c)` are each pinned to a *line*
rather than sweeping a plane. Those are discharged one level up, at the
chart's tangent space (`dominance.build_chart`, scoping FIXED, so `pt(a)`,
`pt(b)`, `pt(c)` and both panels stand still): `d g₁₄ ≠ 0` at **684/684**
probed chart points, **all 652** uncovered companions among them. A nonzero
differential makes `{g₁₄ = 0}` a proper hypersurface of the chart, which is
strictly more than "not identically zero".

**The degeneration is nevertheless REACHABLE — at a good seed.** `--geom`
constructs it: slide `pt(x₁)` inside `Π(b)` onto the line joining `pt(b)` to
`D := C₄ ∩ M` (legal, because both points lie in `Π(b)`, and in the free
pattern that is `x₁`'s only constraint). Then `C₁ ∩ M = D = C₄ ∩ M`, so
`g₁₄ = 0` exactly. At all four habitats — θ(3,4,5), NT21, NT24, NT30 — the
result is an exact pencil realization with

- `g₁₄ = 0` while `g₁₃, g₂₄ ≠ 0` and **all four middle brackets survive**, so
  (Λ0a), (Λ0b), (Λ0c), (Λ0d), (Λ0e) and the recorded (Λ0f) all hold;
- **both spans drop, `3 → 2`** — (Λ0f′) predicts exactly this, and the
  recorded (Λ0f) predicts the opposite. Until 2026-08-06 that showed up as
  `lambda.omega_curves`' own coded equivalence **firing as an
  `AssertionError`** here, caught and reported by `outer.py` but not repaired
  (harness-debt item 2). **Repaired by re-baselining slice S3**
  (`notes/scripts/README.md` *The build plan*): `omega_curves` now codes
  (Λ0f′), so at these four points it **accepts** and reports the drop to
  `(2, 2)` with `g₁₄` the single vanishing factor — the criterion and the
  independent `raw_spans` measurement now agree instead of contradicting;
- the placement is still **target-rank with `dim R_a = 1`**, i.e. a *good
  seed* on the hard stratum, with `dim V_bc = 3`.

So this is `m2/lambda0.m2` block (P5) reproduced on **real class habitats**
rather than on the abstract slice: the third (Λ2) branch is **not vacuous**
anywhere in the class — it is a genuine, reachable stratum of every probed
habitat's chart. What it is not is *forced*: it is a hypersurface, and at each
constructed point the habitat's **own** far covector `λ` annihilates neither
collapsed span, so `Q(z(t)) ≢ 0` (degree 4) and the pitch certificate still
fires — 0 of 4 constructed points is actually blind.

### Step 4 — branch 1: `λ ∝ p⁺` is the genuine escape failure

`λ ∝ p⁺` ⟺ `V_bc ⊆ C(M)^{⊥B}` ⟺ `V_bc ⊥_B C(M)`, which is **verbatim (T3)'s
uniform-failure criterion**: no motion of `H` pairs non-trivially with the meet
line, so both routes fail and the escape genuinely does not hold at any seed of
that far configuration. The pitch certificate is not *blind* here — it is
correctly reporting a failure. (`--habitat` asserts the equivalence
`escape(T3) ⟺ ¬(λ ∝ p⁺)` at every probed seed; `--adv` hunts for `λ ∝ p⁺` and
finds none, which is the expected outcome — a hit would be a **counterexample
to the pencil conjecture** at that habitat.)

### Step 5 — branch 2: `λ ∝ q` forces `★r ∝ C(bc)`, and route A escapes

Suppose `V_bc ⊆ C(bc)^{⊥B}`, i.e. `⟨x, ★C(bc)⟩ = 0` for all `x ∈ V_bc`. Also
`B(C(bc), C_ab) = [b,c,a,b] = 0` and `B(C(bc), C_ac) = [b,c,a,c] = 0`, so
`★C(bc)` is Euclid-orthogonal to `T` as well, hence to all of
`W := V_bc ⊕ T` (5-dimensional at a target-rank seed, (T1)). Since (T1) says
`⟨r⟩ = W^⊥`:

> **(Λ3)** `V_bc ⊆ C(bc)^{⊥B}` ⟹ `★r ∝ C(bc)`: the transmitted wrench is the
> **pure force along the line joining the two hub points**.

Route A fails only if `★r ∈ Λ²Π̂(b)`, i.e. only if `line(bc) ⊆ Π(b)`, i.e. only
if `pt(c) ∈ Π(b)` — excluded by (Λ0d). So in this branch **the split escapes at
every target-rank seed**, by route A rather than by the pitch certificate.
(`--dichot` asserts each step: `★C(bc) ⊥ W`, `W^⊥ = ⟨★C(bc)⟩` with
`dim W = 5`, and `C(bc) ∉ Λ²Π̂(b)`; 18 frames across 9 strata.)

The two branches are disjoint (`p⁺ ∦ q`, asserted per frame). Reading Steps 3–5
together:

> **Theorem (Λ-completeness at length-4 companions).** At a hard-stratum split
> with a length-4 companion, under (Λ0) and the standing (T1)/(T5) hypotheses:
> **the escape holds at some target-rank seed iff the pitch certificate `Q(z)`
> is nonzero at some target-rank seed.** Concretely, for each far
> configuration exactly one of: `Q(z) ≠ 0` somewhere on the `a`-line (escape,
> by pitch); `V_bc ⊆ C(bc)^{⊥B}` (escape, by route A, with `★r ∝ C(bc)`);
> `V_bc ⊆ C(M)^{⊥B}` (the escape genuinely fails there, (T3)).

### Step 5a — (OUT): the outer-line criterion, a far-side sufficient condition (2026-08-05, no driver)

Migrated here from `notes/pencil/strategy.md` §4.6-U1, which derived it and
flagged it as having no workbook home; that file now carries only a pointer and
the strategic readings. **It is a corollary of Steps 3–5 and nothing else** —
no new geometry — but it is the one *positive* the broad class-uniformity recon
produced, and the arc under-produces those.

**The observation.** `p⁺` and `q` have their **outer** entries vanishing
*structurally*, not generically — `p⁺ = (0, p⁺₂, p⁺₃, 0)` and
`q = (0, q₂, q₃, 0)` always ((Λ0f)'s parenthetical; (Λ0g) restates the `p⁺`
half geometrically). So the *whole* (Λ2) bad set lies on **one projective line**
of `P(S*)`, namely `{λ₁ = λ₄ = 0}`. And by *Standing notation* `λ` is the
annihilator of `V_bc` in the `C`-basis, so `λ_i = λ(C_i)` and, since
`V_bc = ker λ ∩ S` is a hyperplane of `S` with `C_i ∈ S`,

>  `λ₁ = 0 ⟺ C₁ ∈ V_bc`   and   `λ₄ = 0 ⟺ C₄ ∈ V_bc`.

Hence:

> **(OUT) the outer-line criterion** *(proven-informally, **conditional** — see
> the hypothesis line below)*. At a hard-stratum, target-rank, length-4-companion
> split, if **either outer companion line fails to be a relative twist** —
> `C₁ = C(b x₁) ∉ V_bc` **or** `C₄ = C(x₃ c) ∉ V_bc` — then `λ` is proportional
> to neither `p⁺` nor `q`, so by (Λ2) `Q(z(t)) ≢ 0` along the `a`-line and the
> split **escapes by the pitch certificate** at some placement of `pt(a)` on `M`.

**Hypotheses, spelled out because a one-line quotation of (OUT) will drop them.**
(OUT) is *exactly as conditional as (Λ2)*: it needs the standing (T1)/(T5)
hypotheses, the hard-stratum target-rank seed with `dim V_bc = 3`, and **(Λ0) in
full** — in particular **(Λ0d)** (two-sided panel non-incidence) and the
**widened (Λ0f′)** including the `g₁₄` clause. Both are load-bearing here and not
decoratively so: if (Λ0d) fails, *Step 6* shows `span_t ω⁻` collapses `3 → 1` and
(Λ2)'s second branch becomes a whole **hyperplane** of bad `λ`; if the `g₁₄`
factor of (Λ0f′) vanishes, *Step 3*'s closing parenthetical gives (Λ2) a third
branch, again a hyperplane per side. A hyperplane is **not** contained in the
line `{λ₁ = λ₄ = 0}`, so the containment (OUT) rests on fails outright in either
degeneration. (OUT) inherits *Step 3a*'s scope for `g₁₄` verbatim, including the
open two-hub-interior residual, item (vii).

**What it costs.** (OUT) is **sufficient, never necessary**: it discards a
codimension-3 avoidance (`λ ∦ p⁺`, a point of `P³`) in exchange for a
codimension-2 one (`λ` off a line of `P³`), and it is silent on the whole line —
of whose points exactly one (`p⁺`) is a genuine (T3) failure and one (`q`) is a
route-A escape. It is not a strengthening of Λ-completeness; it is a *cheaper
test* that is decided by far-side data alone.

**Why the cheapness is the point.** (OUT)'s hypothesis mentions **no quadric, no
meet line `M`, no `pt(a)`, no panel and no ratio** — the two conditions
`C₁, C₄ ∈ V_bc` are statements about `H` alone. In hinge-rate coordinates
(`m(u) − m(w) = ω_e C_e` per hinge, as in §(K-ind) *Step I3*'s proof) the
companion lines are independent by (Λ0a), so a relative twist has *unique*
companion coordinates and

> `C₁ ∈ V_bc` ⟺ some motion of `H` has companion hinge-rates `(1,0,0,0)` —
> it **freezes the companion's last three hinges and bends the first** —
> ⟺ in `H/{e₂,e₃,e₄}` (weld `x₁,x₂,x₃,c` into one body `X`; any chord among
> them becomes a loop and drops out) the body `b` is **not rigidly attached to
> `X`**.

(The second equivalence in one line: `e₁` joins `b` to `X`, so any relative
motion of `b` and `X` lies in `⟨C₁⟩` and is `ω_{e₁}C₁`; it is nonzero iff
`ω_{e₁} ≠ 0`. Further `b`–`X` edges only make `b` more attached, and the
equivalence survives them.)

**Two consequences recorded, neither proven here.** *(1)* `C₁ ∉ V_bc` is a rank
**lower** bound (a rigidity statement), so `notes/pencil/strategy.md` §2.3's
asymmetry is **relocated onto a smaller contracted graph, not evaded** — and
that is the honest reason (OUT) is a reformulation rather than a closure.
*(2)* The welded body `X` carries the hinges formerly at `x₁, x₂, x₃, c`, which
are not concurrent, so `X` is **not a pencil body**: the fact (OUT) reduces to
lives on the **mixed stratum** (§(K-ind) *Step I6* is why no transport repairs
this). That gives `pencil/strategy.md` §4-C3 a consumer it did not have.

**MEASURED, 2026-08-06 — §(K-out) is the canonical home of the answer and it is
not restated here.** `--adv` reports `λ ∝ p⁺` and `λ ∝ q` at **0** hits over its
**habitat leg only** (≤ 400 frames — *not* the 1497 this paragraph used to quote;
see §(K-out) *Step O8*), and it reports **nothing about `λ₁` and `λ₄`
separately**, so (OUT)'s hypothesis had never been evaluated anywhere in the arc.
The new driver mode is `notes/scripts/w4/outerline.py`. Headline of what it
found, in the order that matters: **§(K-out) (OC-3)** — on the pencil chart `C₁`
is confined to the 2-dimensional pencil `L_b` and `dim R₁ = 5` forces
`dim(R₁ ∩ L_b) ≥ 1`, so `{λ₁ = 0}` is **nonempty at every class shape in scope**
and **no counting argument can ever deliver this hypothesis**; **(OC-5)/(OC-6)**
the hypothesis nevertheless holds at 356/357 (POOL-G) and 270/270 (POOL-S),
pointwise; **(OC-4)** the bad line is reached by a legal chart move at a fully
nondegenerate point where the pitch certificate still fires. So (OUT) is
*available and never automatic*, and the sharpest single datum at `k = 4` is
exhibited rather than hunted.

### Step 6 — two side conditions that are load-bearing, with witnesses

(Λ0) is not decorative. Two of its clauses have exhibited witnesses:

- **(Λ0d), panel non-incidence, is needed in *both* directions.** At
  θ(3,4,5) **seed 345** the sampler happens to place `pt(b) ∈ Π(c)`; then
  `pt(b)` lies *on* `M`, `plane(a(t),b,c)` is **constant** along the `a`-line,
  and `span_t ω⁻(t)` collapses `3 → 1`, so (Λ2)'s second branch becomes a whole
  hyperplane of bad `λ`. (Route A still escapes there, since `pt(c) ∉ Π(b)`.)
  Reproduced and asserted by `--adv`. The earlier arc only ever used the
  one-sided form of this condition; the two-sided form is what (Λ2) needs.
  **Two additions, 2026-08-05 (§(K-σ) *Step σ3*/*Step σ4b*, `sigma.py
  --hunt`).** (1) The one-sided failure is not peculiar to θ(3,4,5)'s sampler:
  it is reachable by construction on the **tight control's** hard stratum, at
  35/35 primally-nondegenerate configurations. (2) The **two-sided** failure is
  *impossible* at a primally nondegenerate seed whose split middle body `a` is
  a degree-2 non-hub adjacent to both hubs — **(σ7)** — so (Λ0d) can fail in at
  most one direction. That does **not** relieve (Λ2), which needs both halves;
  it only bounds how badly (Λ0d) can fail.
- **(Λ0f) is a genuine hypothesis**, not a consequence of (Λ0a–e), and its
  failure is exactly one bracket. Forcing the single non-structural bracket
  `p⁺₃ = [x₂, x₃, M₀, M₁] = 0` — i.e. moving `pt(x₃)` inside `Π(c)` so that
  `C₃` meets `M`, an affine-linear solve — collapses `span_t ω⁺(t)` from 3 to
  2, deterministically (4/4 **constructed** frames, `--adv`
  `degeneracy_witnesses`); forcing `q₃ = [x₂, x₃, b, c] = 0` collapses
  `span_t ω⁻(t)` the same way. Discovered, not postulated: θ(3,4,5) **seed 695**
  has `p⁺ = (0, ∗, 0, 0)` and `span ω⁺ = 2`. In that situation
  `λ ⊥ span_t ω⁺(t)` no longer implies `V_bc ⊥_B C(M)`, so the Step-4
  identification breaks and the pitch route *could* be blind while the escape
  holds. It is a proper closed condition (0 hits in the 164 (Λ0a–e)-generic
  frames), so a good seed always exists — but it must be **named**, which the
  prior formulation did not do.

### Step 7 — `ℓ ∈ {5, 6}`: the frame does **not** reach them, and exactly why

The gap map listed the (T5) frame as the route for the `bc`-parallel
`ℓ ∈ {5,6}` shapes. It is not, and the obstruction is sharp.

By Step 1(ii), `dim(S ∩ α_a) = k − 3`, so at `k ≥ 5` "`V_bc` meets it" is
**strictly weaker** than "`V_bc` contains it", and the Step-3 span argument —
which works precisely because at `k = 4` the intersection is a *point* of
`P(S)` — has no analogue. Concretely at `k = 5` (`dim S = 5`,
`Y := S ∩ C(M)^{⊥B}` 4-dimensional, `P_α(t) := S ∩ α_{a(t)}` 2-dimensional and
`⊆ Y`): a bad `V_bc` with `V_bc ⊄ Y` meets every `P_α(t)` inside the 2-plane
`U := V_bc ∩ Y`. Two 2-planes of the 4-dimensional `Y` meet iff their Plücker
points pair to zero under `Λ⁴Y` (the Klein form again), so such `U` exist iff
`W^⊥` contains a nonzero **decomposable** point, where
`W := span_t Plücker(P_α(t)) ⊆ Λ²Y ≅ K⁶`. Measured exactly (`--l56`, 3 frames,
both the `α/C(M)` and the `β/C(bc)` side): `dim W = 3`, `dim W^⊥ = 3`, and
`Q|_{W^⊥}` is **nondegenerate of rank 3** — a *smooth conic*. So over `K̄` the
extra component is nonempty and 1-dimensional, giving a `1 + 2 = 3`-dimensional
family of bad `V_bc`, **the same dimension as the containment component**, and
it is neither the (T3) failure nor the route-A branch. At `k = 6`, `S = Λ²K⁴`
so `C(M) ∈ S` always (asserted), removing even the (Λ0e) guard.

> **`ℓ = 5, 6` verdict: REFUTED through this frame.** The `(F-B)`/route-A half
> (Step 5) is length-free and survives verbatim; the `(F-A)` half acquires a
> second bad component at every `k ≥ 5`, so no local argument of this shape
> settles `ℓ ∈ {5,6}`. What would be needed is a reason the *realized* `V_bc`
> of a class habitat misses that conic component — a far-side statement, and a
> harder one than at `k = 4` (where the analogous far-side statement turned out
> to be (T3) itself).

**Scope, stated because it is easy to overstate.** This refutes **the (T5)
frame / an argument of this shape** at `ℓ ∈ {5,6}`. It does **not** refute the
pencil conjecture there, and it does **not** show those shapes are unclosable:
the extra `k = 5` component is a smooth conic, so it is nonempty **over `K̄`**,
and whether a *rational* point of it is realized by a real habitat's `V_bc` is
**open** — item (iv) of *What would change this*.

### Step 8 — a length-free remark, flagged as *not* fully driver-tested

Steps 3–5 used the companion only through Step 1(ii)'s dimension count. The
`(F-B)` half is **length-free**: at *any* hard-stratum split with `b, c` hubs,
if the isotropic conic `𝒞 := P(V_bc) ∩ {Q = 0}` spans `P(V_bc)` (⟸
`rank Q|_{V_bc} = 3`, observed at **357/357** real habitat seeds) and every line
of `𝒞` meets `line(bc)` — which is what `(F-B)` at every `t` forces, because the
planes `plane(a(t),b,c)` sweep the pencil through `line(bc)` — then
`V_bc ⊆ C(bc)^{⊥B}`, and (Λ3) + route A escape. The `(F-A)` half is length-free
too, but its conclusion is weaker: `M` must lie on the ruled surface of `𝒞`,
which gives `C(M) ∈ V_bc` **or** `V_bc ⊆ C(M)^{⊥B}`. So in general the pitch
route's only blind spot beyond the genuine (T3) failure is `C(M) ∈ V_bc` —
excluded at `k ≤ 5` by `C(M) ∉ S`, unavailable at `k = 6`. This remark is
**geometric, over `K̄`, and only partially driver-tested** (the ingredients
`rank Q|_{V_bc} = 3` and `C(M) ∈ S ⟺ k = 6` are; the ruled-surface case
analysis is not). **It is recorded as a lead, not as a proven step.**

> **Step numbering, flagged because it is new in this section.** §(K-Λ)'s
> existing steps are bare numbers (*Step 0* … *Step 8*, plus *Step 3a* and
> *Step 5a*), and `notes/pencil/labels.md`'s measured diagnosis clause 4
> records that bare step numbers collide with claim labels — §(K-Λ) already
> mints driver blocks (P1)–(P7) against §(K-pure)'s *Steps P0–P9*. The steps
> below therefore use the **`Λ`-prefixed form**: ***Step Λ8*** is a **new**
> step and is **not** the existing *Step 8*. Cite them as *Step Λ8* … *Step
> Λ12*, never as a bare parenthesized token ((L2)).

### Step Λ8 — the branch calculus: class membership is a statement about `G°` alone

Everything §(K-Λ) needs about *which* companion shapes exist is decided one
level below the subdivision. Let `G` be feasible ((R4)) and 2-edge-connected,
so that `G` is the subdivision of its **hub multigraph** `G°` (vertices = the
hubs, `n° := |V°|`, edges = the branches, `e° := |E°|`) with branch lengths
`ℓ : E° → ℤ_{≥1}`; write `c(F) := |F| − |W(F)| + comps(F)` for the cycle rank
of a branch subset `F ⊆ E°` on its incident hub set `W(F)`, and
`c° := c(E°) = e° − n° + 1`.

> **(Λ4) the branch calculus** *(proven-informally; the reduction is the
> classical one, the `G°`-form is what is new here)*. With the notation above:
>
> **(i)** `G` is **tight** (`5|E| = 6(|V| − 1)`) ⟺ `Σ_{e ∈ E°} ℓ_e = 6·c°`;
> and then `|V| = 5c° + 1`, `|E| = 6c°`.
> **(ii)** Given (i), `def(G) = 0` ⟺ `Σ_{e ∈ F} ℓ_e ≥ 6·c(F)` for **every**
> branch subset `F ⊆ E°`.
> **(iii)** Given (i) and (ii), `hnoRigid` ⟺ that inequality is **strict** for
> every **proper** `F ⊊ E°`.
>
> So the class predicate — tight ∧ `def = 0` ∧ `hnoRigid` ∧ `hcard` ∧
> triangle-free — is a finite statement about the pair `(G°, ℓ)`, with `hcard`
> reading *"the length-1 branches form a subgraph of maximum degree ≤ 2"* and
> triangle-freeness a **consequence**, not a hypothesis.

*Proof.* Write `f(W) := 5|E(W)| − 6(|W| − 1)` (*Shared dictionary*). (i) is
`f(V) = 0` rewritten: `|V| = n° + Σ(ℓ_e − 1)` and `|E| = Σℓ_e`.

For (ii): `def(G) = 6(|V| − 1) − 5|E| + max_P Σ_{parts} f(part)` and, under
(i), `f(V) = 0`, so `def(G) = 0` ⟺ `Σ_{parts} f ≤ 0` for every partition.
Singletons have `f = 0`, so taking `P = {W} ∪ singletons` gives `f(W) ≤ 0` for
every `W`, and conversely that suffices. Now `f(W ∖ {u}) = f(W) − 5·deg_{G[W]}(u)
+ 6`, so any `f`-maximizer has `deg_{G[W]} ≥ 2` throughout; a degree-2 vertex
of `G` in such a `W` therefore brings both its neighbours, so `W` is a **union
of whole branches**. On a branch union `F` one computes directly
`f = 6·c(F) − Σ_F ℓ`. Hence `f ≤ 0` everywhere ⟺ `Σ_F ℓ ≥ 6c(F)` for every
branch subset.

For (iii): under (i)+(ii) every `W` has `f(W) ≤ 0`, so
`def(G[W]) = −f(W)` and `G[W]` is rigid ⟺ `f(W) = 0`; the same maximizer
argument makes every such `W` a branch union. ∎

**Four consequences, one line each, and all of them are facts the arc already
uses:**

- **girth `≥ 7`.** `F` a cycle of `G°` has `c(F) = 1`, so `Σ_F ℓ ≥ 7` by
  (iii) — i.e. every cycle of `G` has length `≥ 7`. (Sparsity alone gives
  `≥ 6`; `hnoRigid` removes the rigid `C₆`.) In particular triangle-freeness
  and simplicity of `G` are consequences, and `G°` is **loopless**.
- **(SD-6) re-derived.** `F = E° ∖ {β}` has `c(F) = c° − 1` (no bridges, by the
  same count), so `6c° − ℓ_β > 6(c° − 1)`, i.e. **`ℓ_β ≤ 5`**. This is
  §(K-ann) (ANH-8)'s statement with a two-symbol proof.
- **(D3) re-derived.** The split branch (length 3) plus a companion of length
  `k` is a cycle, so `3 + k ≥ 7`, i.e. `k ≥ 4` — and `k = 4` is the
  **equality** case, which is the calibration `hnoRigid` is tight at.
- **parallel branches.** Two parallel branches have `Σℓ ≥ 7`; three have
  `Σℓ ≥ 13`; so multiplicity is at most 5.

*Standing of (Λ4).* It is a **reformulation**, not new mathematics: (ii)/(iii)
are the branch-union reduction that `kslide.no_rigid_branch_union` already
codes. What it buys is that the class predicate becomes cheap enough to
enumerate **exhaustively** rather than sampled or capped — which is what
*Step Λ11* does — and that *Step Λ9* can be stated as one inequality.

### Step Λ9 — the companion-cycle lemma, and the size floor it forces

Fix a class shape `G`, a **split** (a length-3 branch `e₀` whose two ends
`b, c` are hubs — by *Standing notation* and `widened.orient`, eligible splits
are exactly the length-3 branches between two hubs, in either orientation) and
a **length-4 companion** `P = b–x₁–x₂–x₃–c`. Let

> `Z := {e₀} ∪ {branches of P}`, `W₀ := ` its hub set, `j := #{i : x_i a hub}`.

Because `P` traverses whole branches, `Z` has exactly `j + 2` branches on
`j + 2` hubs, `c(Z) = 1`, and `Σ_Z ℓ = 3 + 4 = 7` — it is (D3)'s proper `C₇`,
seen in `G°`.

> **(Λ5) the companion-cycle lemma** *(proven-informally)*. **No branch of
> `G°` outside `Z` has both of its ends in `W₀`** — unless `E° = Z ∪ {β}` and
> `V° = W₀`, which forces `j = 0` and `G = θ(3,4,5)`.

*Proof.* Let `β ∉ Z` have both ends in `W₀`. Then `F := Z ∪ {β}` is connected
with `c(F) = 2` and `Σ_F ℓ = 7 + ℓ_β ≤ 12` by (Λ4)'s `ℓ ≤ 5`. (Λ4)(iii)
demands `Σ_F ℓ > 12` whenever `F` is proper, so `F = E°` and `W₀ = V°`; then
(Λ4)(i) gives `7 + ℓ_β = 6·c° = 12`, `ℓ_β = 5`, `c° = 2`, `|V| = 11`. Every
hub of `W₀` has `Z`-degree 2 and gains at most 1 from `β`, so at most two hubs
reach degree 3 — hence `|W₀| = j + 2 = 2`, `j = 0`, and `G` is a θ-graph with
branch lengths `(3, 4, 5)`. ∎

*(The exceptional case is not decoration: it is exactly **θ(3,4,5)**, the
arc's own §(K-Λ) exemplar — `G°` is then three parallel branches of lengths
3, 4, 5. Consistent with §(K-out) (OC-10), which reaches the same shape by an
independent route; that is a cross-check, not a second result, and this pass
does not re-derive (OC-10).)*

> **(Λ6) the size floor** *(proven-informally)*. Off the θ(3,4,5) boundary,
> put `t := n° − (j + 2)` and `m' := e° − (j + 2)`. Then
>
> `t ≥ 1`, `m' ≥ j + 2`, `2m' ≥ (j + 2) + 3t`,
>
> hence `n° ≥ j + 3` and `c° ≥ ⌈(2j + 7)/3⌉`, i.e. `|V| ≥ 5c° + 1` and
> `|E| ≥ 6c°`:
>
> | `j` | `n° ≥` | `c° ≥` | `|V| ≥` | `|E| ≥` |
> |---|---|---|---|---|
> | 0 | 3 | 3 | 16 | 18 |
> | 1 | 4 | 3 | 16 | 18 |
> | **2** | **5** | **4** | **21** | **24** |
> | **3** | **6** | **5** | **26** | **30** |
>
> (The `j = 0` row is the off-boundary bound; the (Λ5) boundary case itself is
> θ(3,4,5), with `n° = 2`, `c° = 2`, `|V| = 11`.)
>
> Moreover at `t = 1` the hub multigraph is **forced**: the `j + 2` branches
> outside `Z` all join the unique non-frame hub to the `j + 2` hubs of `Z`,
> one each, so `e° = 2j + 4`, `n° = j + 3`, `c° = j + 2`, and `G°` is the
> **wheel** on the `(j+2)`-cycle `Z` — for `j = 2` the wheel `W₄`, which is
> `K5` minus a perfect matching (`pencil_escape.K5_minus_matching`'s base
> graph), and for `j = 3` the wheel `W₅`.

*Proof.* Each hub of `W₀` has `Z`-degree 2 and needs degree `≥ 3`, so carries
a branch outside `Z`; by (Λ5) that branch's other end is off `W₀`, whence
`t ≥ 1` and `m' ≥ |W₀| = j + 2` (each outside branch supplies at most one
`W₀`-end). Counting ends of the `m'` outside branches: `2m' ≥ (j+2) + 3t`,
since the `t` non-frame hubs draw all `≥ 3` of their incidences from outside
`Z`. Now `c° = e° − n° + 1 = m' − t + 1`. The first bound gives
`c° ≥ j + 3 − t`, i.e. `t ≥ j + 3 − c°`; substituting into
`c° ≥ (j + 2 + 3t)/2 − t + 1 = (j + 4 + t)/2` gives `2c° ≥ j + 4 + j + 3 − c°`,
i.e. `3c° ≥ 2j + 7`. At `t = 1` the only non-frame hub is `h`, `G°` is
loopless (girth `≥ 7`), so every outside branch is `h`–`W₀`; `m' ≥ j + 2` and
one per `W₀`-hub forces `m' = j + 2` exactly, with no parallel pair. ∎

**What (Λ6) explains.** The families the arc swept are θ (`n° = 2`), `K4` and
`K4 + parallel` (`n° = 4`), and the three simple hub graphs on `n° = 5`. By
(Λ6) a `j = 2` companion needs `n° ≥ 5` **and** — combined with (Λ5) at
`t = 1` — `e° = 8`, i.e. the wheel `W₄`; and a `j = 3` companion needs
`n° ≥ 6`, so it **cannot** appear in any `|V°| ≤ 5` family at all. That is one
half of the recorded "4 of 8 patterns" boundary turned into a theorem. The
other half is *Step Λ11*'s cap.

### Step Λ10 — the witnesses: item (vii) is REALIZED

The (Λ6) floors are **attained**, at all four patterns, by class shapes that
also carry a hard-stratum target-rank pencil-chart point.

> **(Λ7) the two-hub-interior witnesses** *(constructed and harness-certified;
> the class predicate is the tracked oracle's, the geometry is one guarded
> chart point per split)*. The three shapes below are class shapes — tight,
> `def = 0`, `hnoRigid`, triangle-free, `hcard` — and each carries a length-4
> companion with `j ≥ 2` interior hubs at an eligible split:
>
> | name | `G°` | `|V|`, `|E|` | `n°`, `e°`, `c°` | patterns realized |
> |---|---|---|---|---|
> | **`LT21a`** | wheel `W₄` | 21, 24 | 5, 8, 4 | `(1,1,0)` and `(0,1,1)` |
> | **`LT21b`** | wheel `W₄` | 21, 24 | 5, 8, 4 | `(1,0,1)` (both orientations) |
> | **`LT26`** | wheel `W₅` | 26, 30 | 6, 10, 5 | `(1,1,1)` (both orientations) |
>
> In `kslidecomb`'s `specs` form (`specs[0]` the length-3 split branch,
> hubs `b = 0`, `c = 1`, companion interior hubs `2, 3(, 4)`, non-frame hub
> last):
>
> ```
> LT21a  [(0,1,3), (0,2,1), (2,3,1), (3,1,2), (4,0,5), (4,2,5), (4,3,5), (4,1,2)]
> LT21b  [(0,1,3), (0,2,1), (2,3,2), (3,1,1), (4,0,5), (4,2,5), (4,3,4), (4,1,3)]
> LT26   [(0,1,3), (0,2,1), (2,3,1), (3,4,1), (4,1,1),
>         (5,0,3), (5,2,5), (5,3,5), (5,4,5), (5,1,5)]
> ```
>
> At each of the **6** (witness, split) pairs a guarded pencil-chart point of
> `G′` — `outer.chart_point`, i.e. `widened.place_pencil_general` plus the
> composite guard `repin.star_generic` plus `verify_pencil_witness` — is found
> **on the first draw** from `random.Random(20260819)`, and there:
>
> - the placement is at **target rank** on the **hard stratum**,
>   `dim R_a = 1` (`outer.stratum_at`: rank 114 at `|V| = 21`, 144 at 26);
> - **(Λ0d)** holds in both directions;
> - **(Λ0g)** is asserted in both directions (`outer.geom_checks`), so the
>   *Step 3a* geometry is confirmed on the previously-unrealized patterns;
> - **`g₁₄ ≠ 0`**, and **`d g₁₄ ≠ 0`** in 8–10 of the 46 (resp. 60) directions
>   of the FIXED-scoping chart tangent space (`dominance.build_chart`).
>
> **Class membership is certified by more than one oracle, and for the two
> `|V| = 21` witnesses `hnoRigid` is certified beyond branch granularity.**
> All three pass `kslidecomb.shape_ok` (the pebble-game `def` oracle plus
> `kslide.no_rigid_branch_union`), are 2-edge-connected, and have
> `saferes.treepack_deficiency = 0` (the matroid-union oracle). At
> `|V| = 21` the `2^|V|` partition oracle `kbare_common.exact_deficiency`
> is affordable, and over **all** `2^21` vertex subsets it reports `def = 0`,
> `f(V) = 0`, **zero** subsets with `f > 0` (full 5/6-sparsity), **zero**
> proper subsets with `f = 0`, and `max f` over proper `|W| ≥ 2` equal to
> **`−1`**. That is `hnoRigid` verified against every vertex subset, not only
> against branch unions — an independent confirmation of (Λ4)'s reduction on
> the witnesses. `LT26` (`|V| = 26`, `2^26` subsets) is **not** run through
> that oracle: its `hnoRigid` rests on the two affordable oracles plus branch
> granularity, and that is disclosed rather than smoothed over.
>
> `LT21a` / `LT21b` / `LT26` are keyed to `|V|`, **not** to `|E|`: their
> `|E|` are 24, 24, 30, and the arc's `NT<|E|>` convention is already taken by
> `NT24` and `NT30`.

**The naming of the residual population, made exact.** Since `j ≥ 2` forces
two of `x₁, x₂, x₃` to be hubs, at least one of `x₁, x₂` is a hub and at least
one of `x₂, x₃` is. Reading *Step 3a*'s (Λ0i):

> **(Λ8) (Λ0i)'s exact coverage** *(proven-informally; one line)*. `x₁` is
> (Λ0i)-free ⟺ neither `x₁` nor `x₂` is a hub, and `x₃` is free ⟺ neither
> `x₃` nor `x₂` is. So **(Λ0i) covers exactly the three patterns `(0,0,0)`,
> `(1,0,0)`, `(0,0,1)`**, and it covers **no** companion with `j ≥ 2` and none
> with `x₂` a hub. In particular the `g₁₄` clause of (Λ0f′) is **never**
> implied by (Λ0d) at a two-hub-interior companion, and *Step 3a*'s 3628/4280
> free-end discharge extends to none of them.

*(This is the general classification behind *Step 3a*'s measured sentence
"the 652 uncovered pairs are all the single hub pattern `x₂` a hub": that
sentence is true **of the swept scope**, where — see *Step Λ11* — the `j ≥ 2`
patterns were hidden by a cap. The (Λ0i)-uncovered class is five patterns, not
one.)*

### Step Λ11 — the exhaustive census, and the cap that hid three patterns

`outer.py --patterns` reported *4 of 8 patterns realized, at a widened length
bound of 8, cap 400 shapes per hub multigraph* — a coverage boundary, as it
says. **Three of the four missing patterns were inside its own scope.**

**The census, uncapped.** By (Λ4) the class predicate is a `2^{e°}` test on
`(G°, ℓ)`, and by (Λ4)'s `ℓ ≤ 5` a length bound of 5 is **exhaustive**, not a
cap. Running exactly the `--patterns` family list — θ3, θ4, `K4`,
`K4 + parallel`, and the three simple hub graphs on 5 hubs — over **all**
length assignments with a length-3 split branch (`ltwo.py --census`;
convention: one row per (hub multigraph, length assignment, split **branch**,
companion), so each length-3 branch is counted once rather than once per
orientation — the totals are **not** comparable with `--patterns`' 7002):

| leg | (shape, split) pairs with a length-4 companion | patterns |
|---|---|---|
| `theta3` | 6 | `(0,0,0)`: 6 |
| `theta4` | 0 | — |
| `K4` | 540 | `(1,0,0)`/`(0,1,0)`/`(0,0,1)`: 180 each |
| `K4+par` | 740 | `(0,0,0)`: 380; the three one-hub patterns: 120 each |
| **`V5e8`** (wheel `W₄`) | **7064** | `(1,0,0)`: 2268, `(0,1,0)`: 2280, `(0,0,1)`: 2276, **`(1,1,0)`: 80, `(0,1,1)`: 80, `(1,0,1)`: 80** |
| `V5e9` | 15066 | the three one-hub patterns: 5022 each |
| `V5e10` | 35370 | the three one-hub patterns: 11790 each |

**7 of 8 patterns are realized inside the swept family list.** Only `(1,1,1)`
is absent, and (Λ6) proves it **cannot** occur at `|V°| ≤ 5`. (Λ5) is
asserted at all **58 786** (shape, split, companion) triples of the census:
**0 failures**.

**The cap, made reproducible.** `outer.shapes_from('V5e8', 5, E0, lmax=8,
cap=400)` — the exact call `--patterns` makes on that leg — returns 400 shapes
after 19 041 length tuples with `capped = True`, and **every one of the 400
sits at split index 0 of 8**: split indices 1…7 are never reached. The witness
shapes `LT21a` / `LT21b` live on that same hub multigraph (canonical-form
match against `kslidecomb.candidate_graphs(5)`'s `|E°| = 8` graph, asserted).
So the recorded "`(1,1,0)`, `(0,1,1)`, `(1,0,1)` unrealized **in scope**" is a
**cap artifact**, not a `|V°| ≤ 5` boundary — while "`(1,1,1)` unrealized" is
the genuine boundary, now with a proof.

**Both halves of the floor are attained, exhaustively** (`ltwo.py --floor`).
At `t = 1`, (Λ6) forces the wheel and the enumeration is finite: for `j = 2`,
60 length tuples on `W₄`, of which **all 60** are class shapes carrying a
`j = 2` companion (20 per pattern); for `j = 3`, 15 tuples on `W₅`, **all 15**
class shapes carrying `(1,1,1)`. So the floors `|V| = 21` and `|V| = 26` are
attained and are exactly the (Λ6) bounds.

### Step Λ12 — what this does, and does not do, to Λ-completeness

**It does not weaken the theorem.** Λ-completeness is stated *"under (Λ0) and
the standing (T1)/(T5) hypotheses"*, and (Λ0)'s hypothesis package is
**local-frame** data: (Λ0a)–(Λ0f′) mention only the points
`{b, x₁, x₂, x₃, c, a}`, the panels `Π(b)`, `Π(c)`, `M` and `line(bc)`. Three
facts make the two-hub-interior population no harder than the rest:

1. **The local-frame machinery already quantifies over all eight patterns.**
   `lambda.py`'s `HUBPATS` is the full `2³`, and `STRATA4 + STRATA4X` is
   `8 × 3 + 7 × 2 = 38` — the recorded 38 strata of the `--span` battery.
   `(1,1,0)`, `(0,1,1)`, `(1,0,1)` and `(1,1,1)` are among them and were
   measured at `(span ω⁺, span ω⁻, deg ω⁺, deg ω⁻) = (3,3,3,2)` there.
2. **`m2/lambda0.m2` block (P6)'s bridge reaches them on the same terms as
   every other stratum.** Its construction gives a companion hub the panel
   `plane(x_{i−1}, x_i, x_{i+1})` and places far hub neighbours freely inside
   it, with `hcard` capping the count at 2. At a two-hub-interior companion an
   interior hub has **two** hub neighbours already inside the frame, hence
   **zero** far hub neighbours; `sample_local_frame`'s own
   `nfar = min(nfar, 2 − #local hub neighbours)` is exactly that case, and the
   normal space is 1-dimensional — the tightest stratum, not a degenerate one.
   No (Λ0) quantity mentions an interior hub's panel, so no new constraint
   enters the 14-coordinate slice. **The qualifier the verdict block already
   carries rides unchanged:** (P6)'s *"every stratum arises this way"* half is
   the reading of `sample_local_frame`'s model, not a computation. That
   conditional is **uniform across all eight patterns** — the two-hub
   population inherits it neither better nor worse than the six-of-eight the
   arc has been quoting.
3. **The clause the residual was really about — `g₁₄` — holds at the
   witnesses.** *Step Λ10*: `g₁₄ ≠ 0` and `d g₁₄ ≠ 0` at all six
   (witness, split) chart points.

**It does change three things, and they are not cosmetic.**

- **The residual is a live case, not a vacuity.** Before this pass "no swept
  family realizes one" left open the reading that the population is empty and
  the scope hole harmless by accident. It is non-empty, at `|V| = 21` — the
  same size as `NT21` / `NT24`, and smaller than `NT30`.
- **(Λ0i) provably never discharges it** ((Λ8)). At every two-hub-interior
  companion **both** ends are pinned, so the cheap "implied by (Λ0d)" route of
  *Step 3a* is unavailable by a theorem, not by an accident of sampling. The
  `g₁₄` clause there rests on (Λ0f′)'s generic-point proof plus the tangent
  certificate, and on nothing else.
- **The measured record now reaches the population — barely, and that is the
  honest scope.** *Step 3a*'s figures are `g₁₄ ≠ 0` at **4280/4280** exact
  (split, companion) pairs over 1357 class shapes and `d g₁₄ ≠ 0` at
  **684/684** chart points; **none** of those touch a `j ≥ 2` companion. This
  pass adds **6** (split, companion) pairs at **3** shapes and **6** guarded
  chart points. Six is a spot check, not a sweep, and must be quoted as one.

**Verdict for item (vii): ANSWERED, in the negative direction for the
"forbidden" branch.** The class does **not** forbid two or more hubs on a
length-4 companion's interior; it forbids them only below `|V| = 21` (resp.
`|V| = 26` for `(1,1,1)`), by (Λ6). *Step 3a*'s parenthetical "prove the
pattern impossible inside tight + `hnoRigid` + `hcard` (the same shape of
argument as §(K-slide) *Step 5*'s `ℓ₁ + ℓ₂ ≥ 7`)" is therefore **refuted as a
route**: that argument shape *is* (Λ5), and what it delivers is a size floor,
not an impossibility.

### Verification

`notes/scripts/w4/lambda.py` (tracked, new this pass; exact-ℚ, on top of
`pitch.py`; every sampled object rank/dimension asserted; all rng seeded,
`PYTHONHASHSEED=0` pinned). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --witt      # (Λ0′), (Λ1)
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --span      # (Λ0f), the spans
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --dichot    # (Λ2), (Λ3)
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --habitat   # end-to-end + ℓ=3
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --l56       # ℓ = 5, 6
PYTHONHASHSEED=0 python3 notes/scripts/w4/lambda.py --adv       # the hunt
M2 --script notes/scripts/m2/lambda1.m2                         # (Λ1) symbolically
M2 --script notes/scripts/m2/lambda0.m2                         # (Λ0) + the spans
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --geom       # (Λ0g) + the construction
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --habitat    # named inventory
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --sweep      # the systematic sweep
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --tangent    # d g₁₄ ≠ 0 on the chart
PYTHONHASHSEED=0 python3 notes/scripts/w4/outer.py --patterns   # the coverage boundary
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --witness   # (Λ7): the three witnesses
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --floor     # (Λ6): the floor, attained
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --census    # (Λ5) + Step Λ11's census
PYTHONHASHSEED=0 python3 notes/scripts/w4/ltwo.py --validate  # (Λ4) vs the tracked oracle
```

**(OUT) (*Step 5a*) carries no driver and adds no command line**: it is a
corollary of Steps 3–5, and the quantities its hypothesis names (`λ₁`, `λ₄`) are
computed but not reported by `--adv`. Do not read any figure below as evidence
for or against it.

The last five lines are `notes/scripts/w4/outer.py` (tracked, new 2026-08-05;
exact ℚ, a `w4/` leaf beside `flanks`/`pure`/`lambda`/`dominance`), the
*Step 3a* driver. It **reads** `lambda.py` through `importlib` for the four
certified habitats and the `ω±` curve machinery and never modifies it.

The last line is the harness's **Macaulay2 layer** (`notes/scripts/m2/`, opened
2026-08-05 with this driver; conventions in `notes/scripts/m2/README.md`, M2
version **1.26.06** pinned and printed, no randomness). It is *additive*: it
does not reimplement or replace `lambda.py --witt`, whose figures below stand
unchanged.

Habitats: θ(3,4,5) and NT21 (the two `pitch --companion4` shapes) plus **two
new length-4-companion shapes** — `NT24` (hubs `b,c,u,w`; `b`–`c` paths 3, 4
plus `b–u:3, u–c:4, b–w:4, w–c:3, u–w:3`; `|V| = 21`, `|E| = 24`) and `NT30`
(5 hubs; `b`–`c` paths 3, 4 plus `b–u:4, u–c:3, b–w:3, w–c:3, u–y:4, y–c:3,
w–y:3`; `|V| = 26`, `|E| = 30`) — and θ(3,3,6) for the `ℓ = 3` corollary. All
four length-4 shapes carry the class predicate at load time: `def = 0`
(`nogood_subdiv.deficiency`), `hnoRigid` at branch granularity
(`kslide.no_rigid_branch_union`), `hcard_ok`, triangle-free.

Per mode, what is asserted:

- `--witt`: `T` totally isotropic; `dim T^{⊥B} = 4`, `rank Q|_{T^{⊥B}} = 2` with
  radical exactly `T`; `α_a`, `β_{π_a}` totally isotropic, inside `T^{⊥B}`, and
  meeting in `T`; `dim N = 2`, `S ∩ T = 0`, `rank Q|_N = 2`, `B(ω⁺,ω⁻) ≠ 0`;
  `ω±` are line extensors and span `S ∩ α_a` / `S ∩ β_{π_a}`; `rank Q|_S = 4`;
  `Φ_loc ≠ 0`, `rank Φ_loc = 2`, and **(Λ1) with scalar exactly 1**.
- `--span`: per frame the degrees (`≤ 3`, `≤ 2`), the structural zeros
  `q₁ = q₄ = p⁺₁ = p⁺₄ = 0`, `p⁺ ≠ 0 ≠ q`, `p⁺ ∦ q`, `C(M) ∉ S`, both spans
  `= 3` **and the bracket equivalence (Λ0f) in both directions**, both spans
  identified as `S ∩ C(M)^{⊥B}` / `S ∩ C(bc)^{⊥B}`, both annihilators
  `⟨p⁺⟩` / `⟨q⟩`, `q·ω⁺(t) ≢ 0`. **164 frames** over **38 strata** + 4
  habitats, `(3,3,3,2)` uniformly.
- `--dichot`: for `λ = p⁺` and `λ = q`, `Q(z(t)) ≡ 0` (exact interpolation) and
  `ker λ ∩ S` = the corresponding `S ∩ C(L)^{⊥B}`; for a sampled generic `λ`,
  `Q(z(t)) ≢ 0`; the per-`t` factorization
  `Q(z) = 0 ⟺ λ·ω⁺ = 0 ∨ λ·ω⁻ = 0`; and (Λ3): `dim W = 5`, `★C(bc) ⊥ W`,
  `W^⊥ = ⟨★C(bc)⟩`, `C(bc) ∉ Λ²Π̂(b)`. **18 frames**, 9 strata.
- `--habitat`: the Λ-compressed `z` equals `pitch.z_from`'s `z`; the (T2) sign
  law `Q(r)·Q(z) < 0` against the **independently computed stress**; (T3)
  agreement `escape ⟺ ¬(λ ∝ p⁺)`; `Q(z) ≠ 0` at every seed; plus the `ℓ = 3`
  corollary at θ(3,3,6).
- `--l56`: `dim(S ∩ α_a) = dim(S ∩ β) = k − 3` and `rank Q|_N = 2` with radical
  `S ∩ T` for `k = 3,4,5,6`; `C(M) ∈ S ⟺ k = 6`; at `k = 5` the Plücker
  reduction `(dim W, dim W^⊥, rank Q|_{W^⊥}) = (3,3,3)` on both sides, and that
  every 3-space inside `Y` is bad (the containment component).
- `--adv`: three parts. (i) The **panel-incidence witness** — θ(3,4,5) seed
  345, `pt(b) ∈ Π(c)`, `pt(b)` on `M`, `span ω⁻ = 1`. (ii) The **(Λ0f)
  necessity witnesses** — constructed (not searched): moving `pt(x₃)` inside
  `Π(c)` to force `p⁺₃ = 0` gives `span ω⁺ = 2` at 4/4 frames, and forcing
  `q₃ = 0` gives `span ω⁻ = 2` at 4/4. (iii) The **hunt** over the habitat seed
  pools (seeds 200–499 × 4 habitats) and the local strata: hits for `λ ∝ p⁺`,
  `λ ∝ q`, `Q(z) = 0` — all **0** — plus the `(span ω⁺, span ω⁻)` and
  `rank Q|_{V_bc}` histograms and the `C(M) ∈ S` count, with the assertion that
  **every** off-pattern frame found carries a vanishing *middle* bracket, i.e.
  the only way (Λ0f) fails is the named one.

**Figures.**

| figure | value |
|---|---|
| `--witt` frames (5 strata × 3 + 4 habitats × 2) | **23**, all with `dim N = 2`, `S ∩ T = 0`, `rank Q\|_N = 2`, `rank Φ_loc = 2`, (Λ1) with scalar **1** |
| `--span` frames (38 strata × 4 + 4 habitats × 3) | **164**, `(span ω⁺, span ω⁻, deg ω⁺, deg ω⁻) = (3,3,3,2)` uniformly |
| `--dichot` frames (9 strata × 2) | **18**; both bad branches give `Q(z(t)) ≡ 0`, generic `λ` does not, (Λ3) + route A per frame |
| `--habitat` seeds | **4 each** at θ(3,4,5), NT21, NT24, NT30 (`λ` off both bad points, `Q(z) ≠ 0`, sign law, (T3) agreement) + **3** at θ(3,3,6) for the `ℓ = 3` corollary |
| `--l56`: `dim(S ∩ α_a)` at `k = 3,4,5,6` | **0, 1, 2, 3**; `rank Q\|_N = 1,2,2,2`; `dim(S ∩ T) = 0,0,1,2` = `dim radical`; `C(M) ∈ S` iff `k = 6` |
| `--l56`: the `k = 5` Plücker reduction, both sides | `(dim W, dim W^⊥, rank Q\|_{W^⊥}) = (3, 3, 3)` — a **smooth conic**, so the extra bad component is nonempty over `K̄` |
| `--adv` frames examined | **1497** (357 real habitat seeds + 1140 local frames) — but see the next row: only the habitat leg carries a `λ` |
| `--adv`: `λ ∝ p⁺` / `λ ∝ q` / `Q(z) = 0` / `C(M) ∈ S` | **0 / 0 / 0 / 0**. **Denominators, corrected 2026-08-06** (§(K-out) *Step O8*): the first three are computed **only in the habitat loop**, so their denominator is `≤ 400` (4 habitats × seeds 200–299; consistent with exactly 357 by `357 + 1140 = 1497`), **not** 1497 — the 1140 local-strata frames carry no far covector at all. `C(M) ∈ S` *is* counted in both loops, so its `0` is over all 1497 |
| `--adv`: `rank Q\|_{V_bc}` histogram (real seeds) | `{3: 357}` — always the smooth-conic case |
| `--adv`: `(span ω⁺, span ω⁻)` histogram | `{(3,3): 1491, (2,3): 6}`; **all 6** off-pattern frames have a vanishing *middle* `p⁺` entry — the named (Λ0f) failure, and nothing else |
| `--adv`: the two constructed necessity witnesses | `p⁺₃ = 0 ⟹ span ω⁺ = 2` (4/4), `q₃ = 0 ⟹ span ω⁻ = 2` (4/4) |
| `lambda1.m2` (M1)/(M2)/(M3): the gauge-free half of (Λ1) | identities in **20 / 30 / 16** indeterminates, residual **0** — no geometry in (M1)/(M2), no gauge anywhere |
| `lambda1.m2` (M4): (Λ1) end-to-end, matrix + scalar form | residual **0** in `ℚ[a,c,w,λ]` (16 indeterminates, `b,x₁,x₂,x₃` gauged) — all 16 matrix entries, scalar exactly **1** |
| `lambda1.m2`: the ungauged expansion | **infeasible** — degree 52 in 28 indeterminates, killed at 600 s |
| `lambda0.m2` (P1)–(P3): closed forms, genericity, containments | identities / non-vanishing in **14** indeterminates (20 ungauged, (P7)); `deg_t ω⁺ = 3`, `deg_t ω⁻ = 2` exactly |
| `lambda0.m2` (P4): the span criterion | `cross4` of all **4** coefficient triples `= ±w₃^{3−j}w₂^{j}·Π⁺·p⁺`; `Π⁺ = p⁺₂p⁺₃g₁₃g₁₄g₂₄`, `Π⁻ = q₂q₃g₁₃g₁₄g₂₄` |
| `lambda0.m2` (P5): the missing `g₁₄` clause | not vacuous — a degeneration killing **only** `g₁₄` keeps (Λ0a,b,c,e) + all four middle brackets and drops **both** spans |
| `lambda0.m2` run time | **0.1 s** (the `a`-line parameter `t` never becomes an indeterminate) |
| `outer.py --geom`: (Λ0g) | asserted in **both** directions at **12** (seed, companion) pairs (4 habitats × 3 hard-stratum seeds); `g₁₄ ≠ 0` at every one |
| `outer.py --geom`: the constructed `g₁₄ = 0` point | **4/4 habitats**; `g₁₃, g₂₄ ≠ 0` and all four middle brackets survive; both spans **3 → 2**; still **target-rank, `dim R_a = 1`, `dim V_bc = 3`**. **Repointed 2026-08-06** (re-baselining slice S3, the round's single moved figure): `lambda.omega_curves` used to **raise** at each of the four — it coded the superseded (Λ0f) — and now codes (Λ0f′), so it **accepts** the point and *predicts* the drop, reporting `(span ω⁺, span ω⁻) = (2, 2)` with `(g₁₃, g₁₄, g₂₄) ≠ 0` = `(True, False, True)`. This is (Λ0f′)'s Gram half confirmed by the harness's own criterion rather than by the driver's independent `raw_spans` alone |
| `outer.py --geom`: does the third branch *bite*? | **0 of 4** — the habitat's own `λ` annihilates neither collapsed span, `Q(z(t)) ≢ 0` (deg 4) |
| `outer.py --habitat`: the named inventory | **7** named shapes carry a length-4 companion (θ(3,4,5), NT21, NT24, NT30, the `dominance` duplicates, and the `K4` menu-blocked flank `(1,1,3,5,3,5)`); **48** (split, seed, companion) triples, `g₁₄ ≠ 0` at every one |
| `outer.py --sweep`: the systematic sweep | **1357** class shapes with a length-4 companion, **4280** (split, companion) pairs, **4280** placed exactly — `g₁₄ = 0` at **0** |
| `outer.py --sweep`: (Λ0i) coverage | **3628 / 4280** covered by the free-end criterion alone; the 652 residual are all the single pattern `x₂` a hub |
| `outer.py --tangent`: `d g₁₄` on the chart | nonzero at **684/684** chart points, including **all 652** (Λ0i)-uncovered companions — so `{g₁₄ = 0}` is a proper hypersurface |
| `outer.py --patterns`: realizable hub patterns | **4 of 8** — `(0,0,0)`, `(0,0,1)`, `(1,0,0)`, `(0,1,0)`; **7002** companions. `(0,1,1)`, `(1,0,1)`, `(1,1,0)`, `(1,1,1)` unrealized **in scope** (a coverage boundary, not a theorem) |
| `ltwo.py --witness`: the three two-hub-interior witnesses | **3 shapes / 6 (split, companion) pairs**, patterns `(1,1,0)`, `(0,1,1)`, `(1,0,1)`, `(1,1,1)`; every one at **target rank with `dim R_a = 1`**, (Λ0d) holding, (Λ0g) asserted both ways, `g₁₄ ≠ 0` and `d g₁₄ ≠ 0` (in 9/9/8/8/10/10 of 46/46/46/46/60/60 chart tangent directions); guarded chart point found on the **first** draw at all 6 |
| `ltwo.py --witness`: independent class certification | all three: pebble `def = 0`, **`treepack_deficiency = 0`**, 2-edge-connected; the two `|V| = 21` witnesses additionally through the `2^21` **partition** oracle — `0` subsets with `f > 0`, `0` proper subsets with `f = 0`, `max f` over proper `\|W\| ≥ 2` = **`−1`** — so `hnoRigid` there is certified over **every** vertex subset, not only branch unions. `LT26` is **not** run through it (`2^26`); disclosed |
| `ltwo.py --floor`: the (Λ6) floor, attained | `j = 2`: **60/60** length tuples on the wheel `W₄` are class shapes carrying a `j = 2` companion (20 per pattern), `|V| = 21`; `j = 3`: **15/15** on `W₅`, `|V| = 26` |
| `ltwo.py --census`: the uncapped pattern census | **7 of 8** patterns realized over the `--patterns` family list at the exhaustive bound `ℓ ≤ 5`; `(1,1,0)`/`(0,1,1)`/`(1,0,1)` at **80 each, all on `V5e8`**; only `(1,1,1)` absent, and (Λ6) proves it needs `|V°| ≥ 6`. (Λ5) asserted at **58 786** triples, **0** failures |
| `ltwo.py --census`: the `--patterns` cap, reproduced | `outer.shapes_from('V5e8', 5, E0, 8, cap=400)` returns **400 shapes after 19 041 tuples, `capped = True`**, all at **split index 0 of 8** — so the `V5e8` leg of `--patterns` never reached 7 of its 8 split positions |
| `ltwo.py --validate`: (Λ4) against `shape_ok` + `triangles` + `hcard_ok` | **12 035/12 035** length tuples agree, **0** disagreements (θ3, θ4, `K4`, `K4+par` exhaustive; `V5e8` split-0 strided 1-in-8), plus the companion enumerator cross-checked against `outer.companions4`/`hub_pattern` at every eligible split of all three witnesses |

**Confidence verdict.**

- **(Λ1) (the two-hyperplane bracket factorization): PROVEN — a symbolic
  identity over the function field**, upgraded 2026-08-05 from 23 sampled
  rational frames (`lambda.py --witt`) by `m2/lambda1.m2` (*Step 2*). Its
  gauge-free half (M1)+(M2)+(M3) is a complete proof; (M4) checks the assembled
  form end-to-end on a slice that meets every GL(4)-orbit once. It needs **none**
  of (Λ0) and none of the panel data — (Λ0) secures only the non-vanishing of
  the ingredients, itself now verified at the polynomial level. This is the arc's
  first class-uniform *positive* statement of any kind; it is about `Φ_loc`'s
  shape, and (as *Steps 3–5* show) it does **not** touch the escape's own
  uniformity.
- **(Λ0) and the `a`-line spans: PROVEN AT THE GENERIC POINT, and CLASS-UNIFORM**
  (2026-08-05, `m2/lambda0.m2`; *Standing notation* + *Step 3*). Every clause
  (a)–(f) is now a nonzero polynomial on the local frame's chart rather than a
  condition certified by witnesses in 38 strata; the containments and the
  `t`-degrees are identities; and the span criterion is the **closed form
  (Λ0f′)**, which is **wider than the recorded (Λ0f)** by the three Gram
  factors `g₁₃g₁₄g₂₄`, of which `g₁₄ = [b,x₁,x₃,c] ≠ 0` was asserted nowhere
  and is shown non-vacuous by an explicit degeneration.
  **The `g₁₄` clause itself is now located** (*Step 3a*, `outer.py`): it says
  the two marked points `C₁ ∩ M`, `C₄ ∩ M` of the meet line coincide
  **(Λ0g)**; wherever a companion end is free it is *implied by* (Λ0d)
  **(Λ0i)**, so it is a new hypothesis only in the `x₂`-a-hub pattern; and
  **no class habitat in the searched scope forces it** — `g₁₄ ≠ 0` at all
  4280 swept (split, companion) pairs and `d g₁₄ ≠ 0` on the chart tangent
  space at all 684 probed points.

  > **Scope of those two figures, sharpened 2026-08-19 (*Steps Λ8–Λ12*):**
  > neither denominator contains a companion with **two or more interior
  > hubs** — that population is now known to be **non-empty** ((Λ7), three
  > witnesses at `|V| = 21`, `21`, `26`), and by (Λ8) **(Λ0i) covers none of
  > it**. Six further (split, companion) pairs at three shapes were measured
  > there, all with `g₁₄ ≠ 0` and `d g₁₄ ≠ 0` at a guarded hard-stratum chart
  > point; **six is a spot check, not a sweep**. The 4280 / 684 figures are
  > unchanged and stay true as measured.

  It is nevertheless **reachable at a good seed** of every probed habitat by
  an explicit chart move, so the clause is not decorative.
  **Why this is uniform and not 38 symbolic strata:** the proof mentions no
  habitat, no stratum and no sample — it runs on **one irreducible variety**
  (explicitly parameterized, hence irreducible), and the strata enter only in
  block (P6), where each is shown to map *onto a dense subset of that variety*.
  A dominant map pulls a dense open subset back to a dense open subset, so the
  conclusion is: **for every class habitat carrying a length-4 companion, (Λ0)
  holds on a dense open subset of its pencil chart.** That is the ∃-form (Λ0)
  is used in, uniformly over the class.
  **The one load-bearing conditional** is (P6)'s bridge, which is a geometric
  argument (hub panels are determined by local incidences or free; far hub
  neighbours are free far-graph points placed inside a panel; `hcard` caps the
  count at 2 so no normal space collapses), not a computation. Its constructive
  half is verified; its "every stratum arises this way" half is the reading of
  `sample_local_frame`'s model stated in *Standing notation*.
- **Step 1 (Witt structure `{Q = 0} ∩ T^{⊥B} = α_a ∪ β_{π_a}`), Step 1(i) (the
  `ℓ = 3` two-line closure), (Λ2) (the `a`-line dichotomy), (Λ3)
  (`★r ∝ C(bc)`), and the Λ-completeness theorem: proven-informally**, with
  (Λ0d) named as a hypothesis and (Λ0)/(Λ0f) now proven generic as above.
  (Step 1's maximal-isotropic input is separately re-derived symbolically as
  `lambda1.m2` (M3).)
- **(OUT) (the outer-line criterion, *Step 5a*): proven-informally,
  CONDITIONAL, and carrying NO DRIVER** (2026-08-05; migrated from
  `notes/pencil/strategy.md` §4.6-U1, which now points here). It is a corollary
  of Steps 3–5 with no new geometry, and it is **exactly as conditional as
  (Λ2)** — (Λ0) in full, including two-sided (Λ0d) and the widened (Λ0f′) with
  its `g₁₄` clause; either degeneration replaces a bad *point* by a bad
  *hyperplane* and destroys the containment it rests on. It is **sufficient,
  never necessary** (a codimension-2 avoidance standing in for a codimension-3
  one), its hypothesis `C₁, C₄ ∈ V_bc` is a **rank lower bound**, so §2.3's
  asymmetry is relocated rather than evaded. It closes nothing; it is a cheaper,
  far-side, panel-free test at `k = 4` and a bridge to the mixed stratum. **No
  gap-map *status* moves on it** (the (K-wit) row's *what would close it* cell
  gains it as a scoped sufficient condition).
  **Its hypothesis is MEASURED since 2026-08-06 — §(K-out), the canonical home,
  and the driver is `outerline.py`.** Two things that pass changes here, neither
  a status move: the hypothesis is *available* pointwise (356/357 POOL-G,
  270/270 POOL-S, shape-level at every probed (split, companion) pair), **and**
  §(K-out) (OC-3) proves the bad locus `{λ₁ = 0}` is **nonempty on every class
  shape's chart**, so (OUT) is *never automatic* and **no counting argument can
  ever discharge it**. Quote (OUT)'s availability only with that caveat
  attached.
- **Methodological verdict, and it cuts both ways.** This is the arc's first
  *demonstrated* per-stratum-to-class-uniform upgrade, and §5.3 was right that
  (Λ0) is where that logical form lives. But the reason it works is exactly the
  reason it does not generalize: **(Λ0) is a statement about the local frame
  alone**, in which the far graph does not appear — §(K-Λ)'s frame is designed
  to leave the far data in the free covector `λ`. The escape's uniformity,
  **(K-wit)**, quantifies over `λ`, so it is not a statement on this variety at
  all and no amount of generic-point computation on the frame reaches it. The
  upgrade therefore **confirms rather than circumvents** `notes/pencil/strategy.md`
  §2.3's diagnosis: the symbolic route can make every far-graph-free
  *hypothesis package* of the arc uniform, and stops precisely where the far
  graph enters. **No gap-map status moves.**
- **(K-Λ) as an independent gap: REFUTED** — it is equivalent to (K-wit) at
  length-4-companion splits. Therefore **(K-pitch) at length-4-companion
  splits stays open, exactly as open as (K-wit)** — this pass does *not* close
  it, and no local argument can.
- **`ℓ = 5, 6` through the (T5) frame: refuted** (Step 7); the route-A half is
  length-free and survives. The refutation is of **that argument shape**, not
  of the conjecture and not of those shapes' closability (Step 7 *Scope*).
- The bracket-monomial *closed form* does extend from `ℓ = 3` to `ℓ = 4` — as a
  **product of two bracket-linear forms in the far covector** — but it is not a
  non-vanishing theorem, because its zero locus is nonempty exactly at the two
  structurally meaningful configurations.
- **Class uniformity is untouched.** This pass removes a named gap by showing it
  was never independent; it closes none.

**What would change this.** *(i)* A class habitat + seed with `λ ∝ p⁺`: that is
an escape **failure**, hence a counterexample to the pencil conjecture there —
hunt negative over the `--adv` pools. *(ii)* A habitat with `λ ∝ q`: harmless,
but it would exhibit the route-A branch in the wild and is worth recording.
*(iii)* A local frame satisfying (Λ0a–e) with `span_t ω⁺(t) ≠ 3` or
`span_t ω⁻(t) ≠ 3`: that would put a third component into (Λ2) and break the
completeness theorem — found only with a vanishing middle bracket (6 of 1497
frames, all accounted for), and the exhibited seed-345 collapse shows the
condition is not vacuous. *(iv)* At `ℓ = 5`, a *rational* point of the extra bad
component realized by a real habitat's `V_bc`: that would be a
length-5-companion split where the pitch route is blind while the escape holds —
the first genuine loss of the pitch route, and the sharpest reason to abandon it
at `ℓ ≥ 5`. *(v)* An error in (T1) or (T5) themselves — each is re-asserted per
seed here against an independently computed stress.

*(vi)* **ANSWERED, 2026-08-05 (*Step 3a*, `outer.py`): no class habitat in
the searched scope forces `g₁₄ = 0`.** The question was whether some class
habitat's whole pencil chart lies in `{g₁₄ = 0}` — the outer companion lines
`C(bx₁)`, `C(x₃c)` necessarily meeting — which by (Λ0f′) collapses the
`a`-line spans and gives (Λ2) a third branch, forcing the Λ-completeness
theorem to be restated. Three findings, in decreasing strength:

- **The clause is a coincidence of two points on `M`** (Λ0g), and wherever a
  companion end is free it is **implied by (Λ0d)** (Λ0i) — 3628 of 4280 swept
  pairs. It is a genuinely new hypothesis only in the `x₂`-a-hub pattern.
- **`g₁₄ ≠ 0`** at every one of **4280** exact (split, companion) pairs over
  **1357** class shapes, and **`d g₁₄ ≠ 0`** on the pencil chart's tangent
  space at **684/684** probed points — including all 652 (Λ0i)-uncovered
  companions. So `{g₁₄ = 0}` is a *proper hypersurface* of every chart in
  scope, not the whole chart.
- **But it is reachable at a good seed**: an explicit chart move produces, at
  each of θ(3,4,5)/NT21/NT24/NT30, a target-rank `dim R_a = 1` realization
  with `g₁₄ = 0`, every other (Λ0) clause intact, and both spans `3 → 2`.
  The third (Λ2) branch is therefore **real, and (Λ0)'s `g₁₄` clause is
  load-bearing** — it just never becomes the *only* option for a habitat.

**Λ-completeness stands as written**, provided (Λ0) is read with the widened
(Λ0f′) — which is what the theorem's "under (Λ0)" already means, since the
theorem is an `∃ good seed` statement and the bad set is a hypersurface.

*Scope of that answer, stated because it is easy to overstate.* Exhaustive
over the θ family, over `G° = K4` (lengths ≤ 5), and over `K4` + a parallel
`bc` edge (lengths ≤ 6); **capped** at 25 shapes per `|V°| = 5` hub graph
(3 graphs, `|E°| = 8, 9, 10`); the named inventory (`lambda`, `dominance`,
`flanks`) on top. Nothing beyond `|V°| = 5`, nothing at lengths above the
per-family bound, and — the sharpest boundary — **only 4 of the 8 companion
hub patterns are realized by any class shape in scope** (`--patterns`, at a
widened length bound of 8): the four with at most one hub among `x₁, x₂, x₃`.
*Scope of that answer, corrected 2026-08-19 (*Step Λ11*).* The recorded
`--patterns` reading *"only 4 of the 8 companion hub patterns are realized
by any class shape in scope"* is **true of that run and false of the
families it ran on**: its `V5e8` leg is capped at 400 shapes of 19 041
length tuples and terminates inside split index 0 of 8. Uncapped at the
exhaustive bound `ℓ ≤ 5`, the same family list realizes **7 of 8**
patterns — `(1,1,0)`, `(0,1,1)` and `(1,0,1)` all occur on the `|V°| = 5`,
`|E°| = 8` wheel. `(1,1,1)` is genuinely out of `|V°| ≤ 5` scope, by
**(Λ6)**. The 7002-companion and 4-of-8 figures stay true **as measured**.

*(viii)* **ANSWERED, 2026-08-06 (§(K-out), `outerline.py`): such a frame exists,
is sampled *and* constructible, and the bad locus is nonempty on every class
shape's chart.** The question was for **a length-4-companion frame with `λ₁ = 0`
and `λ₄ = 0`** — *both* outer companion lines relative twists (*Step 5a*) —
which puts the habitat on the bad line `{λ₁ = λ₄ = 0}` of `P(S*)`, makes
**(OUT)** inapplicable there, and leaves only the full ratio test
`p⁺₃λ₂ = p⁺₂λ₃` between it and an escape failure. Three findings, in decreasing
strength:

- **(OC-3), the negative, is the load-bearing one.** `C₁` is confined to the
  2-dimensional pencil `L_b` while `dim R₁ = 5`, so `dim(R₁ ∩ L_b) ≥ 1`: the bad
  locus of the first disjunct is **nonempty at every class shape in scope**, one
  marked direction of `x₁`'s pencil. So the "uniform reason some class shape
  cannot have `C₁ ∈ V_bc`" this item asked for **does not exist**, and no count,
  matroid statement or placement-blind argument can supply one — §2.3's
  prediction, now a proof rather than a prediction.
- **Availability holds pointwise anyway** — (OC-5) 356/357 (POOL-G), (OC-6)
  270/270 over a disjoint POOL-S, with **0** (split, companion) pairs silent at
  every probed seed — and (OUT)'s *conclusion* is separately verified at 356/356.
- **One sampled silent frame** (θ(3,4,5) seed 233) and **four constructed** ones
  ((OC-4), all four habitats, 3 of them with no coincident hinge line): at every
  one the escape still holds by the pitch certificate (`deg_t Q(z(t)) = 4`), so
  (OUT) is silent, not violated.

The residual is **(OC-8)**: class uniformity of (OUT) ⟺ a hard-stratum chart
point with `L_b ⊄ R₁` or `L_c ⊄ R₄` at every class shape — §2.3's wall relocated
onto `H/{e₂,e₃,e₄}` and weakened, **not crossed**. One caveat rides with every
POOL-G rate quoted from that section: **(OC-7)**, a harness defect —
`widened.place_pencil_general`'s in-plane sampler degenerates at 32/357 frames
and that degeneracy *implies* `λᵢ = 0`, uncaught by `star_span_ranks`.

*(vii)* **ANSWERED, 2026-08-19 (*Steps Λ8–Λ12*, `ltwo.py`): a class shape
whose length-4 companion carries two or more hubs on its interior EXISTS —
at every one of the four patterns, at the exact size floor, and at a
hard-stratum target-rank chart point.** Three findings, in decreasing
strength:

- **The floor is a theorem, and it is what the sweeps were seeing.**
  (Λ5): no branch outside the split-plus-companion `C₇` joins two of its
  hubs (else cycle rank 2 at total length `≤ 12`), the sole exception being
  θ(3,4,5). (Λ6): hence `j` interior hubs force `n° ≥ j + 3` and
  `c° ≥ ⌈(2j+7)/3⌉` — `|V| ≥ 21` at `j = 2`, `|V| ≥ 26` at `j = 3` — and at
  one non-frame hub the hub multigraph is the **wheel**.
- **The population is non-empty and reaches the floor.** (Λ7): `LT21a`
  (`(1,1,0)`/`(0,1,1)`), `LT21b` (`(1,0,1)`), `LT26` (`(1,1,1)`), all
  class-certified by the tracked oracles — and at `|V| = 21` by the `2^|V|`
  partition oracle, so `hnoRigid` there holds over **every** vertex subset,
  not only branch unions — each with a guarded chart point at
  target rank with `dim R_a = 1`, (Λ0d) and (Λ0g) holding, `g₁₄ ≠ 0` and
  `d g₁₄ ≠ 0`. **Λ-completeness stands as written on them** — the (Λ0)
  package is local-frame data, `lambda.py`'s 38 strata already span all
  eight hub patterns, and `lambda0.m2` (P6)'s bridge covers a companion hub
  with zero far hub neighbours by construction.
- **But (Λ0i) is provably unavailable there** ((Λ8)): both companion ends
  are pinned at every `j ≥ 2` pattern, so the `g₁₄` clause is carried by
  (Λ0f′)'s generic-point proof and a **six-point** spot check, not by the
  3628/4280 free-end discharge and not by the 4280/684 sweeps.

**The impossibility route named in the old item (vii) is refuted**: "prove
the pattern impossible inside tight + `hnoRigid` + `hcard`" is exactly the
argument (Λ5) runs, and what it yields is a size floor, not an
impossibility. **What is still open** is the *uniform* statement — whether
`g₁₄ ≠ 0` (equivalently, whether `{g₁₄ = 0}` stays a proper hypersurface)
at **every** two-hub-interior class shape's chart, rather than at the three
exhibited. That is the residual form of item (vii), and it is now a
statement about a **named, non-empty, floor-classified** family: at `t = 1`
the wheels `W_{j+2}` with `Σℓ = 6(j+2)`, exhaustively enumerated in
*Step Λ11*; at `t ≥ 2` unenumerated.
