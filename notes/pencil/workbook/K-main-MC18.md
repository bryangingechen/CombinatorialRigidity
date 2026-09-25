## §(K-main) — Step MC18 — the chord point, and the ear route's last open cell (modulo Jackson–Jordán)

#### Step MC18 — the chord point, and the ear route's last open cell (modulo Jackson–Jordán)

*Worked 2026-09-24 by a read-only agent (the third 2026-09-24 session's Track B) on cell (MC-51)(c)
and the split-off step's missing `+1`, which sit at the same chord point. **Second-read 2026-09-25**,
together with Step MC17: nothing refuted.
- (MC-89) never used a false value. But the as-run `--lamcap` certificate was invalid at orbit (ii),
  `k = 3`, which lies on (MC-89)'s path through (MC-45); (MC-97) now says so.
- The chord criterion (MC-108)–(MC-110) is confirmed, with `dim U ≥ 2` made explicit.
- (MC-115)'s "every placement" is repaired, and `lamcap_recount.py`'s hinge filter is recorded as
  weaker than the span guard.
- (MC-117) states the open cell correctly; (MC-171) narrows it.

Drivers of the reading: `w4/capcheck.py`, `w4/nbarcheck.py`, `w4/iffwit.py`, `w4/replay_odd.py`.
None of it is on (MC-89)'s critical path. Drivers `w4/chordprobe.py`, `w4/thetapairs.py`,
`w4/apredraw.py`, `w4/limitcheck.py`, `w4/lamcap_recount.py`, `w4/deltacount.py`, `w4/starcap.py`,
`w4/lamab.py` (new).*

**Verdict.**
- **(MC-50)'s gap is closed** (MC-108). The first-order limit of the ear span is an explicit pencil,
  `Pen(y₀, σ̄)` with `σ̄ = ker[(1−t)φ₂(z₁)α − tφ₁(z₁)β]`. So (MC-50) becomes a theorem, the chord
  criterion (MC-110), whose stress form is: the step closes unless every self-stress of `G′ + ab` at
  the chord point carries only the axial force on the hinge `ab`. A `δ`-dimensional limit
  `ρ̄ ⊆ ρ(z₀)` removes the excess `a′(z₀)` from the bound (MC-109). `a′(z₀) = 0` is false in general
  (MC-116).
- Proved modulo Jackson–Jordán, under the strong induction, with `a ≁ b`:
  - the `k = 1` step whenever `δ ≤ 2` and `δ₂ ≥ 2` (MC-112), which with Step MC17 covers all of
    `δ ≤ 2`;
  - the whole non-dominant `k = 1` cell `dim U = 1` (MC-113), which (MC-51)(c) had listed as "open
    outright";
  - (MC-51)(a) again (MC-114), independently of (MC-93).
- The (MC-26) erratum was found independently here (MC-115).
- **The one open ear cell** (MC-117): `k = 1`, `δ₂ = 3`, `δ ∈ {3, 4}`, at chord points where the
  criterion fails, i.e. `dim(ρ(z₀) ∩ n^⊥) = 4`. Every tested instance is certified to avoid it
  (populations in (MC-117)). Conjecture (MC-118) would close it. **Closing it would give a second
  proof of (MC-89), by the EAR route alone in 𝒮**: (a′) is closed (MC-105), and (MC-79) leaves only
  (c′). *Step MC21 gives that second proof without closing the cell: in 𝒮 some chain always avoids
  it (MC-148).*

**Setting and notation.**

Step MC10's, with Step MC13's `Pen`, `N`, `star`, `⊥` (Klein). `G = G′ + (a − y − b)` with `a ≁ b` in
`G′`, where `G′` satisfies (H). `f = def₃(G′)`, `g = def₃(G′/ab)`, `δ = f − g`, and
`δ₂ = def₂(G′) − def₂(G′/ab)`. Also `n := p_a p_b`, `m := π_a ∩ π_b`, and `G″ := G′ + ab`.

**(IH)** is Step MC13's strong induction hypothesis. `X₀(G′)` and `X₀(G″)` both attain, since both
have fewer vertices than `G`.

The **chord point**: `q′` generic (so in `U(G′) ∩ U(G″)`), and `z₀` generic in `L_{G″}(q′) ⊆ L_{G′}(q′)`.
Then `G″` attains at `z₀`. Put `a′(z₀) := dim M_{G′}(z₀) − 6 − f` and
`M_weld(z) := {X ∈ M_{G′}(z) : X_a = X_b}`. We are in **case A** if `π_a ≠ π_b` at `z₀`, and in
**case B** if `π_a = π_b` there.

**Flag genericity (FG):** `φ₁(z) = z_b − h_a(q_b)` and `φ₂(z) = z_a − h_b(q_a)` are independent on
`L_{G′}(q′)`. By (MC-48)(ii)'s argument, which never uses its count (c), FG ⟸ `δ₂ ≥ 2` mod JJ at `G″`:
- `def₂(G″) = def₂(G′) − min(δ₂, 2)` by the partition count;
- JJ at `G″` makes `L_{G″}` of codimension 2 in `L_{G′}`.

FG gives orbit (i) at `X₀(G′)`'s generic point, and `dim U ≥ 2`, hence dominance (MC-18)(b).

**Facts at the chord point** (the `[PROVED]` part of (MC-50), re-derived). Assume `δ ≤ 5`.
- `M_weld(z₀) ⊆ M_{G″}(z₀)`, since the hinge `ab` only asks `X_b − X_a ∈ ⟨n⟩`.
- `dim M_{G″}(z₀) = 6 + def₃(G″) = 6 + f − min(δ, 5) = 6 + g`, by attainment and (MC-17) at `k = 0`.
- `dim M_weld(z₀) ≥ 6 + g`, by the partition bound.

Hence **`M_weld(z₀) = M_{G″}(z₀)` has dimension `6 + g`**. By (MC-16) at `k = 0`,
`dim M_{G″}(z₀) = dim M_{G′}(z₀) − r(z₀) + dim(ρ(z₀) ∩ ⟨n⟩)`, and
`r(z₀) = dim M_{G′}(z₀) − dim M_weld(z₀)`. Together these give **`ρ(z₀) ∩ ⟨n⟩ = 0`** and
**`r(z₀) = δ + a′(z₀)`**. Since `r(z₀) ≤ 5` whenever `ρ(z₀) ∩ ⟨n⟩ = 0`, **`a′(z₀) ≤ 5 − δ`**. This is
the coordinator's arithmetic, confirmed.


> **(MC-108)** `[PROVED]` *(the first-order limit pencil; closes (MC-50)'s gap)* Fix `q′` with
> `dim U ≥ 2` (for example under FG; *hypothesis added at the second reading, 2026-09-25*) and a
> chord point `z₀` in case A, a direction `z₁ ∈ L_{G′}(q′)`, and `t ∈ K ∖ {0, 1}`. Put
> `y₀ := (1−t)p_a + tp_b`, and let `α, β ∈ (K⁴)^∨` be the functionals of `π_a, π_b` at `z₀`. In the
> chart, `α(x, y, z, w) = z − h_a(x, y)w`, and `β` likewise.
> **(i)** There is a curve `s ↦ (z₀ + sz₁, q_y(s))` with `q_y(0) = q_{y₀}` that lies in `X₀(G)` for
> all but finitely many `s`.
> **(ii)** Along it, the span of the two ear hinges tends to `Pen(y₀, σ̄)`, the lines through `y₀`
> in `σ̄ := ker[(1−t)φ₂(z₁)α − tφ₁(z₁)β]`. This needs `(φ₁(z₁), φ₂(z₁)) ≠ 0`. It does not depend on
> how `q_y(s)` moves.
> **(iii)** Under FG, every pair `(y₀ ∈ n ∖ {p_a, p_b}, σ̄ ⊃ n)` occurs.
> **(iv)** Hence, with `δ ≤ 5`, `dim M_G ≤ 6 + g + dim(ρ(z₀) ∩ Pen(y₀, σ̄))` at `X₀(G)`'s generic
> point. The excess `a′(z₀)` does not appear.

*Proof.* (i) Write `u(z) := h_a(z) − h_b(z)`, an affine function on `K²`. In case A,
`u(z₀) = c₀λ_{ab}`, where `c₀ ≠ 0` and `λ_{ab}` vanishes on the line `q_aq_b`. Take `η` transverse to
that line and put `q_y(s) := q_{y₀} + τ(s)η`, with
`τ(s) := −s·u(z₁)(q_{y₀}) / (c₀dλ_{ab}(η) + s·du(z₁)(η))`. This is rational and regular at `0`, and
it solves `u(z₀ + sz₁)(q_y(s)) = 0`. So the point lies in the incidence
`I := {(z′, q_y) : u(z′)(q_y) = 0}` over `q′`, with `z_y := h_a(q_y)`. With `dim U ≥ 2`, `I` is
irreducible, and `B(G)` is dense in it, as in (MC-18)(b)'s proof. So `I ⊆ X₀(G)`. (Case A alone gives only `ℓ_ab ∈ U`. `dim U = 1` in case A would be `U = Kℓ_ab`,
which (MC-30)(i) excludes only modulo JJ at `G″`.)

(ii) Write `C₁ = p_a ∧ p_y` and `C₂ = p_y ∧ p_b`. At `s = 0` they are `tn` and `(1−t)n`. Put
`w(s) := (1−t)p_a(s) + tp_b(s)`. Then `(1−t)C₁ − tC₂ = w ∧ p_y`, and `w(0) = p_y(0) = y₀`. So
`D(s) := [(1−t)C₁ − tC₂]/s` is regular, with `D(0) = y₀ ∧ v`, where `v := p_y′(0) − w′(0)`. For
`s ≠ 0`, `span(C₁, C₂) = span(C₁, D)`, so the limit is `span(tn, y₀ ∧ v)`.

Differentiate at `0` the identities
- `α(s)(p_y(s)) = 0` (`y ∈ N[a]`),
- `α(s)(p_a(s)) = 0`,
- `α(s)(p_b(s)) = φ₁(z₀ + sz₁) = sφ₁(z₁)`.

This gives `α(v) = −α′(y₀) + α′((1−t)p_a + tp_b) − tφ₁(z₁) = −tφ₁(z₁)`. Likewise
`β(v) = −(1−t)φ₂(z₁)`. In case A, `α` and `β` are independent on `K⁴/n̂`. So `v ∉ n̂`, and
`⟨n, v⟩ = ker[(1−t)φ₂(z₁)α − tφ₁(z₁)β]`. Since `y₀ ∈ n`, `span(n, y₀ ∧ v)` is the pencil at `y₀` in
that plane. The velocity of `q_y` entered only through `v`'s component along `n̂`, which drops out.

(iii) For fixed `t`, FG makes `(φ₁(z₁), φ₂(z₁))` range over all of `K²`. So `σ̄` ranges over the whole
pencil of planes through `n`.

(iv) At `s ≠ 0`, `M_G ≅ {(X, ω̃) : X ∈ M_{G′}(z(s)), X_b − X_a = ω̃₁C₁(s) + ω̃₂D(s)}`, which is the kernel
of a matrix polynomial in `s`. Its dimension at generic `s` is at most its dimension at `s = 0`.
There, `tn` and `y₀ ∧ v` are independent, so the dimension is
`dim M_weld(z₀) + dim(ρ(z₀) ∩ Pen(y₀, σ̄)) = 6 + g + dim(ρ(z₀) ∩ Pen)`. Finally, `X₀(G)`'s generic
point has kernel dimension at most that of any of its points. ∎

`[MEASURED]` *(`limitcheck.py`)* At 126 of 126 (instance, `t`, `z₁`) triples, the closed formula agrees
exactly with `earante.py --chord`'s derivative construction. The instances are the `k = 1` chains
of the θ-graphs with sum ≤ 14 and of a habitat sample; 19 case-B instances were skipped. The
script also asserts that the curve lies in `I` to first order.

> **(MC-109)** `[PROVED]` *(the `δ`-dimensional limit)* Assume (IH) and `δ ≤ 5`, and take a chord
> point `z₀` and a generic `z₁ ∈ L_{G′}(q′)`. Put `ρ̄(z₁) := lim_{s→0} ρ(z₀ + sz₁)`, a limit in the
> Grassmannian. It exists, it is `δ`-dimensional, and **`ρ̄(z₁) ⊆ ρ(z₀)`**. In particular
> `ρ̄ ∩ ⟨n⟩ = 0`. Under (MC-108)'s hypotheses (case A, `dim U ≥ 2`), the bound of (MC-108)(iv) improves to
> `dim M_G ≤ 6 + g + dim(ρ̄(z₁) ∩ Pen(y₀, σ̄))`.

*Proof.*
- *Genericity along the line.* For generic `z₁`, the generic point of the line `z₀ + Kz₁` avoids any
  given proper closed subset `Z ⊆ L_{G′}(q′)`. The directions of lines through `z₀` inside `Z` form a
  proper cone, since otherwise `Z` would contain every line through `z₀`.
- *The limit `M̄`.* So `G′` attains at generic `s`, and `dim M_{G′}(z(s)) = 6 + f`. The kernel of
  `R_{G′}(z(s))` over the local ring `K[s]_{(s)}` is free and saturated. A basis `B(s)` reduces mod
  `s` to a basis of a `(6 + f)`-dimensional `M̄ ⊆ M_{G′}(z₀)`.
- *`Δ(M̄)` has dimension at least `δ`.* Write `Δ(X) := X_b − X_a`. Then
  `ker(Δ|_{M̄}) ⊆ M_weld(z₀)`, which has dimension `6 + g`. So `dim Δ(M̄) ≥ δ`.
- *`ρ(z(s))` has dimension exactly `δ`.* Lower semicontinuity of `rank Δ∘B(s)` gives
  `dim ρ(z(s)) ≥ δ`. The partition bound gives `dim M_weld(z(s)) ≥ 6 + g`, hence
  `dim ρ(z(s)) ≤ δ`.
- *The limit.* So `ρ(z(s)) → Δ(M̄) ⊆ ρ(z₀)`.
- *The improved bound.* Run the kernel argument of (MC-108)(iv) with `X = B(s)ξ`. At `s = 0` it gives
  `dim ker(Δ|_{M̄}) + dim(ρ̄ ∩ Pen) = (6 + f − δ) + dim(ρ̄ ∩ Pen)`. ∎

> **(MC-110)** `[PROVED]` *(the chord criterion; (MC-50) promoted)* Assume (IH), FG, case A, and
> `δ ≤ 4`. **If `dim(ρ(z₀) ∩ n^⊥) ≤ 3`, then `X₀(G)` attains.** Equivalently, the space `L_ab` of
> `ab`-components of the self-stresses of `G″` at `z₀` is not contained in `K·n^♭`, the axial force
> along the hinge line. Here `L_ab = n^⊥ ∩ ρ(z₀)^⊥` has dimension `5 − r(z₀)`. The hypothesis
> holds automatically when `r(z₀) = δ + a′(z₀) ≤ 3`. It **fails** exactly in two cases:
> - `r(z₀) = 5`;
> - `r(z₀) = 4` and `ρ(z₀) = Pen(p_a, σ_a) ⊕ Pen(p_b, σ_b)` for some planes `σ_a ∌ p_b` and
>   `σ_b ∌ p_a`. This is the "bar along `n` implied" case. It means that the relative motion of
>   `b` against `a` is that of two "planar ball joints" at `p_a` and `p_b`.
>
> Moreover, if `(P₁)` fails at `X₀(G′)`'s generic point, then `dim(ρ(z₀) ∩ n^⊥) = 4`. The
> criterion's failure is necessary for the step to fail, not sufficient.

*Proof.*
- *The quadric.* The pencils through `n` are, modulo `n`, the rank-one tensors `y ⊗ v̄` of
  `n^⊥/⟨n⟩ = n̂ ⊗ (K⁴/n̂)`. That is the smooth quadric `P¹ × P¹`, and it spans the whole space.
- *When a pencil meets `ρ(z₀)`.* Since `ρ(z₀) ∩ ⟨n⟩ = 0`, `ρ(z₀) ∩ Pen(y₀, σ̄) ≠ 0` iff `y₀ ⊗ v̄`
  lies in the image `R` of `ρ(z₀) ∩ n^⊥`, and `dim R = dim(ρ(z₀) ∩ n^⊥)`.
- *The criterion.* If `dim R ≤ 3`, the rank-one tensors in `R` form a proper closed subset of
  `P¹ × P¹`. By (MC-108)(iii) some reachable pair with `y₀ ∉ {p_a, p_b}` avoids it. (MC-108)(iv) then gives
  `dim M_G ≤ 6 + g = 6 + def₃(G)`, which is the target, since `def₃(G) = f − δ` by (MC-17) with
  `k = 1` and `δ ≤ 4`.
- *The stress form.* A load `λ` on the hinge `ab` is resolvable by `G′` iff `λ ∈ ρ(z₀)^⊥`, so
  `L_ab = n^⊥ ∩ ρ(z₀)^⊥`. `L_ab ⊆ ⟨n⟩` iff `n^⊥ ⊆ ⟨n⟩ + ρ(z₀)`, iff `dim(ρ(z₀) ∩ n^⊥) = 4`, by the
  modular law.
- *The two failure cases.* `dim(ρ ∩ n^⊥) = 4` holds automatically at `r = 5`. At `r = 4` it means
  `ρ ⊆ n^⊥ = star(p_a) + star(p_b)`. Then `ρ ∩ star(p_a)` is at least `4 + 3 − 5 = 2`-dimensional,
  and at most 2-dimensional because `n ∉ ρ`. It is therefore a pencil `Pen(p_a, σ_a)` with
  `p_b ∉ σ_a`. Likewise at `p_b`. The two pencils meet in `star(p_a) ∩ star(p_b) = ⟨n⟩`, which lies
  in neither, so their sum is `ρ`. The converse is clear.
- *The last sentence.* This uses (MC-27)'s exact orbit-(i) criterion with (MC-109), exactly as in
  (MC-112):
  - the type "`ρ ⊇ m̂ ⊗ y₀`" is excluded;
  - type 1, `dim(ρ ∩ N) ≥ 3`, passes to the limit as `dim(ρ̄ ∩ W̄₄) = 3`, where `W̄₄ = lim N(s)`.
  
  The limits `W̄₄` over the directions `θ = [φ₁(z₁) : φ₂(z₁)]` are the hyperplanes
  `{φ₂c_{aα} = φ₁c_{bβ}}` of `n^⊥/n`, in coordinates dual to `α, β`. They all contain
  `N⁰ = Pen_a + Pen_b`, and any two of them span `n^⊥`. So `ρ(z₀) + ⟨n⟩ ⊇ n^⊥`. ∎

> **(MC-111)** `[PROVED]` *(combinatorics; no JJ in (a)–(c) or in (d)'s first sentence; (d)'s geometric sentences are modulo
(MC-33), JJ at `H` and at `(G″)_ab`: second reading, 2026-09-25)* Let `G′` satisfy (H), with `a ≁ b`.
> **(a)** `δ₂ ≤ 3` always.
> **(b)** If `δ₂ ≤ 2`, then `δ ≤ 2`.
> **(c)** If `δ₂ ≤ 1`, then `δ ≤ 1`.
> **(d)** Case split. `δ₂ ≤ 2` iff `a` and `b` lie in a common `def₂`-rigid subgraph `H` of `G″`
> (then `G″[V(H)]` contains the edge `ab`). `δ₂ ∈ {1, 2}` iff moreover `a` and `b` lie in no common
> `def₂`-rigid subgraph of `G′`. (At `δ₂ = 0`, for example `G′ = K_{2,3}` at its hubs, `G″` itself is
> such an `H`: `iffwit.py`; *repaired at the second reading, 2026-09-25*.) Mod JJ at `H`, every `P ∈ F(G″, q′)` is constant on `V(H)`. So
> `π_a = π_b =: π` at every point of `X₀(G″)`, all of `H′ := H − ab` lies in `π`, and
> **`ρ(z₀) ⊆ Λ²π`** (case B, with `r(z₀) ≤ 2`). If `δ₂ = 3`, then mod JJ at `(G″)_ab` ((MC-13)(c))
> `π_a ≠ π_b` at `z₀` (case A).

*Proof.* Write `val₂(𝒫) = 3(|𝒫| − 1) − 2d(𝒫)` and `val₃(𝒫) = 6(|𝒫| − 1) − 5d(𝒫)`.

(a) Merging the parts of `a` and `b` changes `val₂` by `−3 + 2e ≥ −3`.

(b) Take `1 ≤ δ₂ ≤ 2`. By (MC-13)(b)'s count, `def₂(G″) = max(f₂ − 2, g₂)` with `g₂ = f₂ − δ₂`. So
some maximizing partition of `G″` has `a ∼ b`. Its part is `def₂`-rigid (refining a part changes
`val₂` by `≤ 0`) and contains the edge `ab`. Otherwise `a, b` would lie in a rigid subgraph of `G′`,
and then `δ₂ = 0`.

Let `𝒫` be a `def₃`-optimal partition of `V(G′)` separating `a` from `b`. If there is none, `δ = 0`.
Merge the `t ≥ 2` parts that meet `V(H)`. `val₃` changes by at least `−6(t−1) + 5d`, where `d` is the
number of `H′`-edges crossing `𝒬 := 𝒫|_{V(H)}`. Rigidity of `H` at `𝒬` (where `ab` crosses) gives
`3(t−1) − 2(d+1) ≤ 0`, so `d ≥ ⌈(3t−5)/2⌉`. The change is then:
- `≥ −1` at `t = 2`;
- `≥ −2` at `t = 3`;
- `≥ 2` at `t = 4`;
- `> 0` for `t ≥ 4`.

So `g ≥ f − 2`.

(c) Take `δ₂ = 1`. For `G₁ := G′ + (a − y − b)` the (MC-29) count gives
`def₂(G₁) = max(f₂ − 1, g₂) = g₂`. So a maximizing partition of `G₁` puts `a, b, y` in one part,
which induces a `def₂`-rigid `H_G ∋ a, b, y`. Let `H″ := H_G − y ⊆ G′`. Rigidity of `H_G` at `𝒬`
gives two bounds, one for each place `y` can go:
- `y` alone: `3t − 2(d + 2) ≤ 0`;
- `y` in `a`'s part: `3(t−1) − 2(d + 1) ≤ 0`.

So `d ≥ ⌈(3t−4)/2⌉`, and the merge changes `val₃` by at least:
- `−1` at `t = 2`;
- `3` at `t = 3`;
- `(3t − 8)/2 > 0` for `t ≥ 4`.

So `g ≥ f − 1`.

(d) The first sentence is (b)'s argument, and its converse is (MC-13)(b). Flatness is (MC-13)(c)'s
"if" direction, JJ at `H`. `H′` is connected, because a `def₂`-rigid graph is bridgeless. So for
`X ∈ M_{G′}(z₀)`, `X_b − X_a` is a sum of hinge rotations along a path in `H′`, and every hinge
line lies in `π`. Since `n ∈ Λ²π` and `n ∉ ρ(z₀)`, `r(z₀) ≤ 2`. ∎

`[MEASURED]` *(`deltacount.py 7 300`)* (a)–(c) are asserted over every non-adjacent pair of every simple 2EC
graph on ≤ 7 vertices, and of 300 random sparse `G′` on 8–16 vertices. The pairs total 21 246. In
the observed `(δ₂, δ)` table, `δ ≤ δ₂` whenever `δ₂ ≤ 2`, and `δ₂ = 3` allows `δ` up to 6. In
`chordprobe.py`'s runs, every case-B draw has `ρ(z₀) ⊆ Λ²π` and `r ≤ 2`, and every case-A draw has
`δ₂ = 3`.

> **(MC-112)** `[PROVED-MOD]` *((MC-33); `k = 1`, `δ ≤ 2`; JJ at `G″` for FG and, in case B (`δ₂ = 2`), at the `H` of (MC-111)(d))* Assume (IH), `a ≁ b`, `δ₂ ≥ 2` (FG mod JJ
> at `G″`) and `δ ≤ 2`. **Then `X₀(G) = X₀(G′ + ear₁)` attains.** This settles (MC-51)(c) at
> `δ ∈ {1, 2}` whenever `δ₂ ≥ 2`. Mod (MC-62)'s `dim U = min(δ₂, 3)`, that is the whole dominant
> (`dim U ≥ 2`) part of the cell.
>
> Without (MC-62), one dominant configuration is not covered: `dim U = 2` with `ℓ_ab ∈ U`. There
> `c = 1`, so `δ₂ ≤ 1` by (MC-30)(iii), and `δ ≤ 1` by (MC-111)(c). At `δ = 1` the step fails only if
> the generic flag is in orbit (ii) and `ρ = ⟨m⟩`, the configuration of (MC-115).

*Proof.* By FG, `X₀(G′)`'s generic flag is in orbit (i), and restriction is dominant. By (MC-44),
`r = δ`, which gives `(R₁)`. By (MC-22), it remains to show `(P₁)`.

By (MC-27)'s exact criterion (re-derived below), `(P₁)` fails at `r = δ ≤ 2` only if
`ρ(z) = m̂(z) ∧ y₀(z)` for some `y₀(z) ∈ n(z)`. That is the pencil of lines through `y₀` meeting `m`,
and it needs `δ = 2`. At `r = 1` it never fails.

Suppose it fails at the generic point. Take the line `z(s) = z₀ + sz₁` of (MC-109). The centre `y₀(s)`
is determined by `ρ(z(s))`, so it is algebraic in `s`. Let `y* := lim y₀(s) ∈ n` and
`L* := lim ρ(z(s)) = ρ̄(z₁)`. Then `L* ⊆ ρ(z₀)` by (MC-109), and `L* ⊆ star(y*)`, a closed condition.
- *Case A.* `m(s) → n`. Pick `x(s) ∈ m̂(s)` tending to some `w ∈ n̂` independent of `y*`. Then
  `x(s) ∧ y₀(s) → w ∧ y* ∈ K^×·n`, so `n ∈ L*`.
- *Case B.* `L* ⊆ star(y*) ∩ Λ²π = Pen(y*, π)` by (MC-111)(d). Both spaces are 2-dimensional, so
  `L* = Pen(y*, π)`, which contains `n` because `y* ∈ n ⊆ π`.

Either way `n ∈ ρ̄ ⊆ ρ(z₀)`, against `ρ(z₀) ∩ ⟨n⟩ = 0`. ∎

*(MC-27)'s criterion, re-derived.* In orbit (i) with `y ∈ m`, `Λ(y) = y ∧ n̂`, the lines of the ruling
`{y ⊗ n̂}` of the Segre quadric `P(m̂ ⊗ n̂) ⊆ P(W₄)`. A subspace `ρ₄ = ρ ∩ W₄` meets every line of one
ruling iff `dim ρ₄ ≥ 3`, or `ρ₄` contains a line of the other ruling, `m̂ ⊗ y₀`. Also
`W₄ = Pen_a ⊕ Pen_b = N = ⟨n, m⟩^⊥`.

*Case A alternatively* follows from (MC-109) and (MC-108). For one generic `z₁`, the reachable pencils,
taken modulo `n`, form a smooth conic spanning a plane of `n^⊥/⟨n⟩`. The image of `ρ̄ ∩ n^⊥` there
has dimension at most `δ ≤ 2`, so it meets the conic in at most two points.

> **(MC-113)** `[PROVED-MOD]` *((MC-33); `k = 1` with `dim U = 1`, the non-dominant cell)* Assume
> (IH), `a ≁ b` and `dim U = 1`. **Then `X₀(G′ + ear₁)` attains.** More precisely:
> - `X₀(G)`'s generic point is a case-B chord point `(z₀, y)`, with `y` generic in `π`;
> - `X₀(G)` attains **iff** `r(z₀) ≤ 1`;
> - `r(z₀) ≤ 1` holds.
>
> As a by-product, in this cell `δ ≤ 1` and `a′(z₀) ≤ 1 − δ`.

*Proof.*
1. *`L_{G″}(q′) = ker u`.* `U = Kφ₀`, and `φ₀ ∉ Kℓ_ab` by (MC-30)(i) (JJ equality at `G″`). Since
   `φ₁ = −u(·)(q_b)` and `φ₂ = u(·)(q_a)`, with `u(z) = c(z)φ₀`, we get
   `L_{G″}(q′) = ker c = ker u = {P_a = P_b}`.
2. *The generic point of `X₀(G)`.* For generic `(q′, q_y)`, `L_G(q′, q_y) ≅ {z′ : c(z′)φ₀(q_y) = 0} = ker c`.
   So that point is `(z₀, y)`, with `z₀` generic in `L_{G″}(q′)`, `π_a = π_b = π`, and `y` generic in
   `π`. (This re-derives (MC-18)(b) directly.)
3. *The dimension formula.* The two ear hinges are distinct lines through `y` in `π`. So
   `dim M_G = dim M_weld(z₀) + dim(ρ(z₀) ∩ Pen(y, π)) = 6 + g + dim(ρ(z₀) ∩ Pen(y, π))`.
4. *The criterion.* The target is `6 + f − δ = 6 + g`. So `X₀(G)` attains iff `ρ(z₀)` misses a generic
   `Pen(y, π)`. With `ρ(z₀) ⊆ Λ²π` (step 5), a 3-dimensional space, this holds iff `r(z₀) ≤ 1`.
5. *The rigid subgraph.* (MC-48)(ii)'s argument shows `δ₂ ≥ 2 ⟹ dim U ≥ 2` (mod JJ at `G″`), so here
   `δ₂ ≤ 1`, and `δ ≤ 1` by (MC-111)(c). If `δ₂ = 0`, then `U = 0` mod JJ, so `δ₂ = 1`. The proof of
   (MC-111)(c) gives a `def₂`-rigid `H″ + y` with `a, b ∈ H″ ⊆ G′`. Its count
   `def₂(H″) − min(δ₂(H″), 1) = 0` gives `def₂(H″) ≤ 1`, and then `H″ + ab` is `def₂`-rigid too. By
   JJ at `H″ + ab`, `H″` is flat in `π` at `z₀`.
6. *`r(z₀) ≤ 1`.* `X ∈ M_{G′}(z₀)` restricts to a motion of the flat framework `H″ ⊆ π`. The affine map
   `(x, y, z) ↦ (x, y, z − P(x, y))` sends that framework to `H″` at `(q′, 0)`. There the relative
   motions of `b` against `a` form `U_{H″}(q′)`, by (MC-11)(i) at `z = 0`. So
   `r(z₀) ≤ dim U_{H″}(q′) = def₂(H″) − def₂((H″ + ab)_x) = def₂(H″) ≤ 1`, by (MC-13)(a)/(b) and JJ at
   `H″` and at `(H″ + ab)_x`. ∎

> **(MC-114)** `[PROVED-MOD]` *((MC-33); (MC-51)(a) with `a ≁ b`)* Assume (IH), `a ≁ b` and
> `dim U = 1`, or more generally `δ₂ ≤ 1` with `U ≠ 0`. **Then `X₀(G′ + ear₂)` attains.**

*Proof.* Under `dim U = 1`, (MC-48)(ii)'s argument (`δ₂ ≥ 2 ⟹ dim U ≥ 2`, JJ at `G″`) gives `δ₂ ≤ 1`. Then `δ ≤ 1` by (MC-111)(c), and (MC-44) gives `r = δ`, hence `(R₂)`. `(MC-18)(a)` gives dominance,
and `(MC-19)(b)` gives `λ = 3`. `(P₂)` at `r ≤ 1` needs only `⋂Λ₂ = 0`, which holds in orbits
(i)–(iii) (`lamcap_recount.py`: 0, 0, 0; the proof is (MC-92), by hand, and `lamguard.py`'s guarded run agrees). Orbit (iv) is `U = 0`. Then (MC-22)
concludes. ∎

With (MC-46), which needs `dim U ≠ 1`, and (MC-54) at `δ = 0`: **every open `k = 2` ear step with
`a ≁ b` is proved, mod JJ.** Orbit (iii) needs `U ⊆ Kℓ_ab`, which (MC-30)(i) excludes when `a ≁ b`.

> **(MC-115)** `[PROVED]` *(a correction to (MC-26))* In orbit (ii) at `k = 1`, with `p_b ∈ π_a`,
> `⋂_y Λ(y) = ⟨m⟩`, the intersection taken over the placements `y ∈ m ∖ {p_b}`, which are those of
> generic span `λ = 2`. Each such `y` has `y ∧ p_b ∈ K^×·m`, so `⟨m⟩ ⊆ Λ(y)`. Equality is (MC-97)'s
> pencil argument: `Λ(y) = Pen(y, π_a)`, and two such pencils meet in `⟨m⟩`. So `(P₁)` fails at
> `r = 1` for `ρ = ⟨m⟩`. *(Repaired at the second reading, 2026-09-25: as first written, "every
> placement `y ∈ m`" was false at `y = p_b`, the very placement behind the bug.)* (MC-26)'s list of `r = 1` exceptions, "orbit (iii) at `k = 1`, orbit (iv) at
> `k = 2`", misses this cell.

`earstep.py --lamcap`'s "0" in this cell comes from one degenerate draw, with `x = p_b`, among its
12. `lamcap_recount.py` replays the same draws. Over draws with every hinge nonzero, orbit (ii) at
`k = 1` gives `1`, and a direct frame computation gives `1`. That filter is weaker than the span
guard. It keeps one span-deficient draw at (ii) `k = 3` (`λ = 3`) and one at (iv) `k = 1` (`λ = 1`),
so its figures in those two cells are not certificates. They agree in value with `lamguard.py`,
whose span-guarded run is the certificate for "every other cell unchanged". At `k = 2` and `k = 4`
the kept draws all have generic span, so "every `k = 4` cell is `0`, and (MC-25) stands" holds as
stated. *(Second reading, 2026-09-25.)* The docstring's "an intersection of 0 is a proof that the
intersection over ALL placements is 0" is true as stated, but "all" includes degenerate
placements, which `(P_k)` does not. No landed step uses `(P₁)` at `r = 1` in orbit (ii): (MC-54)
has `r = 0`, and (MC-112) is in orbit (i).

> **(MC-116)** `[REFUTED]` *(witness `C₆`: "prove `a′(z₀) = 0`")* Let `G′ = C₆` with `a, b` at distance 3. This
> is `G = θ(2, 3, 3)`, with `δ = 0` and `δ₂ = 3` (case A). **`a′(z₀) ≥ 1` at every chord point.** At
> `z₀` the hinges at `a` lie in `Pen_a⁰ ∋ n`, and those at `b` in `Pen_b⁰ ∋ n`. So the four hinges
> at `a` and `b` span at most `dim(Pen_a⁰ + Pen_b⁰) = 3`, the six hinges span at most 5, and
> `dim M_{C₆}(z₀) ≥ 7 = 6 + f + 1`. `[MEASURED]` *(`apredraw.py`)* Case-B examples with `δ = 1` and
> `a′ = 1` at each of 6 independent draws (an upper bound: generic `a′ ≤ 1`): `θ(1,3,7)` with pairs `11–19` and `12–14`;
> `x8_174485505`, `x8_194069537`, `x8_218500544`. A draw only over-estimates `a′`, so the generic
> value there is `≤ 1`. (MC-111)(d)'s flat `H′` is the heuristic reason, since it allows it (an upper bound, mod JJ): `r(z₀) ≤ def₂(H′)`, which can exceed
> `δ`.

So no argument that bounds `a′` to 0 can be right in general. (MC-110), (MC-112) and (MC-113) do not use it.
Single-draw readings of `a′ > 0` with `δ ≥ 1` in case A were draw artifacts. All three re-measured
examples (`θ(2,2,7):14–19`, `θ(2,3,8):1–16`, `r10n11:3–4`) give `a′ = 0` at 6 of 6 fresh draws.

> **(MC-117)** `[OPEN]` *(what remains of (MC-51)(c))* The `k = 1` step with `a ≁ b`, `δ₂ = 3`
> (case A; `dim U = 3` mod (MC-62)) and `δ ∈ {3, 4}`, at those `(G′, a, b)` where (MC-110)'s criterion
> fails, i.e. `dim(ρ(z₀) ∩ n^⊥) = 4` at the generic chord point. Where it holds, (MC-110) proves the
> step. *(Wording repaired at the second reading, 2026-09-25; (MC-171)(iii) adds a further necessary
> condition for failure.)* Given (MC-111)(b), this is the only cell of the `k = 1` step not covered by
> (MC-110), (MC-112), (MC-113), (MC-49), (MC-54) and the `U = 0` remark. By (MC-110), a failing instance needs
> one of:
> - `δ = 3` and `a′(z₀) ≥ 1`;
> - `δ = 4` and `a′(z₀) = 1`;
> - `δ = 4`, `a′(z₀) = 0`, and the ball-joint configuration
>   `ρ(z₀) = Pen(p_a, σ_a) ⊕ Pen(p_b, σ_b)`.
>
> `[MEASURED]` At every tested instance in the cell, one exact draw has `a′(z₀) = 0`. Since
> `a′ ≥ 0`, that certifies the generic `a′ = 0`. At `δ = 4` the draw also has
> `dim(ρ(z₀) ∩ n^⊥) = 3`. That is an open condition on the open set `r(z₀) = δ`, so (MC-110) certifies
> the instance. (At `δ = 3`, `r = 3` makes (MC-110) automatic.) The populations:
>
> | population | script | `δ = 3` | `δ = 4` |
> |---|---|---|---|
> | every non-adjacent pair without a common neighbour, of θ-graphs with sum ≤ 15 | `thetapairs.py 15 3` | 890 | 188 |
> | 60 random sparse `G′`, `n = 10..14` | `chordprobe.py --random 60 --nmin 10 --nmax 14 --extra 4 --mindelta 3` | 161 | 151 |
> | habitat class shapes, stride 12 | `chordprobe.py --habitats --stride 12` | — | 92 |
> | 40 random subdivisions of `K₄` | `chordprobe.py --subdiv K4 --maxlen 5 --nsample 40` | 15 | 12 |
>
> `earante.py --chord-habitats` adds its 1 075 `δ = 4` instances.
>
> At `δ = 4`, `starcap.py` finds `dim(ρ(z₀) ∩ star(p_a)) = dim(ρ(z₀) ∩ star(p_b)) = 1` at 56 of
> 56 `δ = 4` instances (θ-graphs with sum ≤ 14 and the habitat sample at stride 24). The ball joint needs both to be 2. `lamab.py` (default stride 8) finds the `ab`-stress
> component `λ_ab` non-decomposable, and so not `n`, at 146 of 146 `δ = 4`, `a′ = 0` instances (the
> habitat sample at stride 8 and θ-graphs with sum ≤ 14). (The agent's recorded run, 79 of
> 79, used a stride it did not record.)
>
> *Step MC21 (2026-09-24): in 𝒮 the cell closes except "Case II-cyclic" (MC-154), which coverage
> does not need; the rigid-set closure (MC-143) and the class ring (MC-151) do the rest.*

> **(MC-171)** `[PROVED]` *(the chord criterion at the limit; sharpens (MC-110); the second reader's,
> 2026-09-25)* Assume (IH), FG, case A and `δ ≤ 4`. Take a chord point `z₀` and a generic
> `z₁ ∈ L_{G′}(q′)`, and put `θ := [φ₁(z₁) : φ₂(z₁)]`. Choose `e_α, e_β ∈ K⁴` with `α(e_α) = β(e_β) = 1`
> and `α(e_β) = β(e_α) = 0` (possible in case A), and set
> `W̄₄(θ) := N⁰ + ⟨φ₁(z₁)·p_a∧e_α + φ₂(z₁)·p_b∧e_β⟩` with `N⁰ := Pen(p_a, π_a) + Pen(p_b, π_b)` at `z₀`.
> `W̄₄(θ)` does not depend on the choice of `e_α, e_β`, and it is the limit of `W₄ = N` along `z₀ + sz₁`.
> - **(i)** For fixed `z₁`, the reachable limit pencils `Pen(y₀(t), σ̄(t))` of (MC-108),
>   `t ∈ K ∖ {0, 1}`, taken modulo `n`, form a smooth conic spanning the plane `P(W̄₄(θ)/⟨n⟩)`.
> - **(ii)** If `dim(ρ̄(z₁) ∩ W̄₄(θ)) ≤ 2` for one generic `z₁`, then `X₀(G)` attains.
> - **(iii)** Hence a failing instance of (MC-117) needs `dim(ρ̄(z₁) ∩ W̄₄(θ(z₁))) = 3` for generic
>   `z₁`. At `δ = 3` this is `ρ̄(z₁) ⊆ W̄₄(θ(z₁))`, in addition to `a′(z₀) ≥ 1`.
> - **(iv)** If `ρ̄(z₁)` does not depend on `z₁`, the step closes at `δ = 3`, and at `δ = 4` unless
>   `ρ̄ ⊆ n^⊥`. That is (MC-150)'s conclusion, from (MC-109) alone.

*Proof.*
- *Well defined.* Changing `e_α` by `u ∈ n̂` changes `p_a∧e_α` by `p_a∧u ∈ ⟨n⟩ ⊆ N⁰`.
- *The limit of `N`.* Along `z(s) = z₀ + sz₁` we have `α(s)(p_b(s)) = sφ₁(z₁)` and
  `β(s)(p_a(s)) = sφ₂(z₁)`. Then `p_a(s)∧(p_b(s) − sφ₁e_α/α(s)(e_α))` lies in `Pen_a(s)`, and
  `p_b(s)∧(p_a(s) − sφ₂e_β/β(s)(e_β))` lies in `Pen_b(s)`. Their sum is
  `−s(φ₁ p_a∧e_α + φ₂ p_b∧e_β) + O(s²)`, because `n(s)` cancels exactly. So `lim N(s)` contains
  `N⁰ + ⟨φ₁ p_a∧e_α + φ₂ p_b∧e_β⟩`. That space is 4-dimensional, since FG gives `(φ₁, φ₂) ≠ 0`, and
  `N(s)` is 4-dimensional in orbit (i). So they are equal.
- *(i).*
  - Use coordinates `c_{iγ}` on `n^⊥/⟨n⟩ = n̂ ⊗ K⁴/n̂`, with `i ∈ {a, b}` along `p_a, p_b` and
    `γ ∈ {α, β}`. Then `N⁰/⟨n⟩ = {c_{aα} = c_{bβ} = 0}`, and `W̄₄(θ)/⟨n⟩ = {φ₂c_{aα} = φ₁c_{bβ}}`.
  - By (MC-108)(ii) the pencil at `t` is `⟨n, y₀ ∧ v⟩`, with `y₀ = (1−t)p_a + tp_b`, `α(v) = −tφ₁` and
    `β(v) = −(1−t)φ₂`.
  - Modulo `n` it is `κ(t) = [(1−t)tφ₁ : (1−t)²φ₂ : t²φ₁ : t(1−t)φ₂]` in the order
    `(c_{aα}, c_{aβ}, c_{bα}, c_{bβ})`, up to one common sign. `κ(t)` satisfies `φ₂c_{aα} = φ₁c_{bβ}`.
  - For generic `z₁`, `φ₁φ₂ ≠ 0` (FG), and `t ↦ κ(t)` is the Veronese conic in that plane: smooth,
    and spanning it.
- *(ii).*
  - By (MC-109) with the same `z₁`: `dim M_G ≤ 6 + g + dim(ρ̄ ∩ Pen(y₀(t), σ̄(t)))` for every `t`.
  - Since `ρ̄ ∩ ⟨n⟩ = 0`, the intersection is nonzero iff `κ(t) ∈ P(R̄)`, where `R̄` is the image of
    `ρ̄ ∩ n^⊥` in `n^⊥/⟨n⟩`. This is (MC-110)'s argument with `ρ̄` in place of `ρ(z₀)`.
  - `R̄ ⊇ W̄₄(θ)/⟨n⟩` iff `dim(ρ̄ ∩ W̄₄(θ)) = 3`, since `ρ̄ ∩ W̄₄` injects into `W̄₄/⟨n⟩`. Otherwise
    `P(R̄) ∩ P(W̄₄/⟨n⟩)` is a proper linear subspace of the plane, and it meets the smooth conic in at
    most 2 points.
  - So all but finitely many `t` give `dim M_G ≤ 6 + g = 6 + def₃(G)` ((MC-17), `k = 1`, `δ ≤ 4`).
- *(iii)* is the contrapositive of (ii). At `δ = 3`, a 3-dimensional `ρ̄ ∩ W̄₄` means `ρ̄ ⊆ W̄₄`. The
  `a′ ≥ 1` is from (MC-117)'s list.
- *(iv).*
  - At `δ = 3`: `ρ̄ ⊆ W̄₄(θ) ∩ W̄₄(θ′) = N⁰` for two generic `θ ≠ θ′`. `N⁰` is 3-dimensional and
    contains `n`, so `ρ̄ = N⁰ ∋ n`, against `ρ̄ ∩ ⟨n⟩ = 0`.
  - At `δ = 4`: `R̄ ⊇ W̄₄(θ)/n + W̄₄(θ′)/n = n^⊥/⟨n⟩` forces `dim(ρ̄ ∩ n^⊥) = 4`, i.e. `ρ̄ ⊆ n^⊥`. ∎

*Relation to what is landed.* It extends (MC-112)'s "Case A alternatively" remark from `δ ≤ 2` to
`δ ≤ 4`, and identifies the conic's plane as `W̄₄(θ)`. It sits between (MC-110)'s criterion and the
truth: failure of the step implies (iii), which implies, using two `z₁`, (MC-110)'s failure
`dim(ρ(z₀) ∩ n^⊥) = 4`. `chordprobe.py`'s "min dim(ρ̄ ∩ limit pencil)" column is the per-instance
form of (ii). It narrows (MC-117) but does not close it. `[CONSTRUCTED]` *(`nbarcheck.py`)*: the
limit formula for `W̄₄`, exact at 20 random instances, with `p_a`, `p_b` held fixed and only `α(s)`,
`β(s)` moving; the moving-point case is the hand computation above.
`python3 notes/scripts/w4/nbarcheck.py` (< 1 s).

> **(MC-118)** `[CONJECTURED]` In case A with `δ ≥ 1`, `a′(z₀) = 0`, and at `δ = 4`,
> `ρ(z₀) ⊄ n^⊥`. It would close (MC-117), and with it the `k = 1` step for `a ≁ b`. The same flat-`H′`
> mechanism that gives (MC-116)'s case-B excess is absent in case A. That is heuristic support only.
>
> *Step MC21: in 𝒮 at `δ₂ = 3`, `a′(z₀)` is the class-level stress count, and it vanishes when `Γ₃` is a
> forest or its 2-core is properly additive with `A` or `B` outside it (MC-153); what is left is
> (MC-154).*

**What the step table gains.**

| cell | before this step | after |
|---|---|---|
| `k = 1`, `δ₂ ≥ 2` (⟸ `dim U ≥ 2`, mod (MC-62)), `δ ≤ 2` | open, except `δ = 0` (MC-54) | proved mod JJ (MC-112) |
| `k = 1`, `dim U = 1` | open outright | proved mod JJ (MC-113) |
| `k = 1`, `δ₂ = 3`, `δ ∈ {3, 4}` | (MC-50) informal | proved where one exact picture certifies (MC-110)'s criterion; open otherwise (MC-117) |
| `k = 2`, `dim U = 1`, `a ≁ b` ((MC-51)(a)) | open at `δ ≥ 1` | proved mod JJ (MC-114) |

These also supply (MC-31)'s missing `+1` wherever `δ ≤ 2`, or `dim U = 1`. The price is the extra
hypothesis `X₀(G − x)` attains, which the strong induction provides. On `hK`'s habitat (case A by
(MC-48)): (MC-112) settles `δ ≤ 2`, and (MC-117) is what is left at `δ ∈ {3, 4}`.


**Drivers** (all at `PYTHONHASHSEED=0` from the repository root, seed `20260924`, exact ℚ; the
mod-`2⁶¹ − 1` attainment screens are certificates; per-draw `a′`, `r(z₀)` are upper bounds for
their generic values):

| command | output | time |
|---|---|---|
| `python3 notes/scripts/w4/chordprobe.py --exh 7` / `--exh 8 --nmin 8` | chord-point profiles, 246 / 3 201 instances | ~7 s / ~100 s |
| `python3 notes/scripts/w4/chordprobe.py --habitats --stride 12` / `--subdiv K4 --maxlen 5 --nsample 40` / `--random 60 --nmin 10 --nmax 14 --extra 4 --mindelta 3` | (MC-117)'s populations: 92 / 74 / 500 instances | ~30 s / ~20 s / ~55 s |
| `python3 notes/scripts/w4/thetapairs.py 13 1` / `thetapairs.py 15 3` | θ-pair scans (`δ ≥ 1` / `δ ≥ 3`); (MC-117)'s 890 + 188 | ~60 s / ~290 s |
| `python3 notes/scripts/w4/apredraw.py` | (MC-116): `a′` at 6 independent draws per instance | < 1 min |
| `python3 notes/scripts/w4/limitcheck.py` | (MC-108): the closed formula at 126/126 triples | < 1 min |
| `python3 notes/scripts/w4/lamcap_recount.py` | (MC-115): `--lamcap`'s draws replayed, with and without degenerate draws | < 1 s |
| `python3 notes/scripts/w4/deltacount.py 7 300` | (MC-111) asserted at every pair of the 2EC graphs on ≤ 7 vertices and 300 random sparse graphs | < 1 min |
| `python3 notes/scripts/w4/starcap.py` / `lamab.py` | (MC-117): star intersections at 56 instances; the `ab`-stress component at 146 (default stride) | < 1 min each |


