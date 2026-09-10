## §(K-bare-ext) — continuation (direction BEARCASE): **(α) IS CLOSED** — the greedy's last step is a **complete 2-line criterion**, a **reordering of the chain** removes the obstruction it names, and the reach formula is **PROVED for `m ≥ 3`**; and **(β) AS STATED IS FALSE** at `δ₁ ≥ 5`, its correct form reducing to **three generic-position statements** whose "every configuration" quantifier **collapses to one generic draw**

Direction **BEARCASE** (`notes/Pencil-fanout.md` §"BEARCASE", ordinal 46), the
arc's fifty-fourth and the **third** consecutive whose selection was forced:
BIMAGE reduced the **ear** case of the strengthened 2-cut lemma to exactly two
items, **(α)** the greedy's last step and **(β)** the `ρ̄₁` non-containment, and
said that together they prove the ear case outright. Read against *Steps
BE29–BE33* (BIMAGE), *Steps BE24–BE28* (BTWOCUT), *Steps BE19–BE23* (BINDUC)
and *Steps BE14–BE18* (BZAVOID), whose figures are **cited, never re-run**.
Driver `notes/scripts/w4/bearcase.py`
(`twostep|laststep|greedy|corners|betadim|betasp|betahunt|validate`), importing
`bimage`, and through it `btwocut` / `binduc` / `kbare_common`, **read-only**;
all exact ℚ, every rng seeded and printed.

**Status, stated before the mathematics.**

- **(α) IS CLOSED, and the answer is a complete criterion rather than a
  patch.** The two conditions the last step must satisfy simultaneously are
  **one** condition in disguise: `ℓ_m ∉ W_{m−1}` and `ℓ_{m+1} ∉ W_m` **both**
  fail exactly when some point `r` of the **line** `M := p_v ∨ p_{m−1}` has
  `p_m ∧ r ∈ W_{m−1}`, because `ℓ_{m+1} = b + μ ℓ_m` rearranges to
  `p_m ∧ (p_v + μ p_{m−1}) ∈ W_{m−1}` and `μ = ∞` is the first condition. So
  the pair `⟨ℓ_m, ℓ_{m+1}⟩` is the **pencil `p_m ∧ M`**, and the question is a
  self-contained lemma about a pencil meeting a subspace. **(BE-35)(i)** proves
  that lemma completely. **(BE-35)(ii)**.
- **The bad case BIMAGE could not rule out is NON-EMPTY — and it is an artifact
  of the ORDER the greedy makes its choices in, not of the geometry.** Its
  three clauses are `Π_v ⊆ W_{m−1}`, `S_t ⊆ W_{m−1}` for some `t` on `M`, and
  `dim(W_{m−1} ∩ λ_M^{⊥K}) ≥ 4`. The first is present **only because `p_m` is
  confined to the plane `π_v`**. **Reorder the chain** — choose *both*
  constrained end lines first (`ℓ_1 ∈ Π_u`, `ℓ_{m+1} ∈ Π_v`), run the free
  interior chain, and close with `p_{m−1}` **free in `P³`** — and the last
  choice has **three** projective parameters instead of two, the `Π_v` clause
  disappears with the constraint that produced it, and the remaining two
  clauses are dodged by **sliding** `p_{m−2}` along `ℓ_{m−2}` and `p_m` along
  `ℓ_{m+1}`: a slide changes **neither** line, so `W` stays fixed while `M`
  sweeps a **2-parameter** family of transversals against a **≤ 1-parameter**
  bad set. **(BE-35)(iii)/(iv)**.
- **Consequence: (BE-33)(ii)'s reach formula is PROVED for `m ≥ 3`** — BIMAGE's
  headline cap, and the one everything else there was subordinate to. Its `≤`
  half was already proved (the three mechanisms are lower bounds); this
  direction supplies the `≥` half by construction. At `m ≤ 2` the ear has no
  free interior point; those two corners are reduced to the same criterion with
  an explicit residue, and a **targeted** hunt for a **fourth** trapping
  mechanism there fires **empty at 1 067 instances**. **(BE-35)(iv)/(v)**.
- **(β) AS STATED IS FALSE, by a two-line count, for every piece with
  `δ₁ ≥ 5`.** `ρ̄₁` and `Z` both sit in the 6-dimensional screw space, so
  `dim(ρ̄₁ ∩ Z) ≥ δ₁ + dim Z − 6` at **every** configuration, while (β) demands
  `dim(ρ̄₁ ∩ Z) ≤ dim Z − 2`; the two are incompatible as soon as `δ₁ ≥ 5`, in
  **every** flag regime, `dim Z` cancelling. The correct target is
  **`loss ≤ max(0, δ₁ + δ₂ − 6)`** — which is what the **landed** `bimage.py
  hunt` already tests. The correction is to the **prose** of BIMAGE's ranked
  successor (1), carried verbatim into the spec and into `notes/Phase39.md`'s
  hand-off; **no measurement changes**. **(BE-36)**.
- **(β)'s unenumerable quantifier COLLAPSES.** Every quantity in
  `loss = max(P,Z,R)` is a difference of ranks of configuration-polynomial
  matrices, so `dim(ρ̄₁ ∩ X)` is **upper** semicontinuous and its minimum is
  attained on a **dense open** set, simultaneously over the three `X`. Hence
  *"at every configuration"* ⟺ *"at a generic configuration"*; a random exact
  draw computes an **upper** bound on the minimum, so a sampler can report a
  **false** trap but can **never miss a real one**; and one drawn configuration
  with `loss ≤ slack` is a **theorem** for that piece. **(BE-37)(i)**.
- **(β) then reduces to three generic-position statements, and `δ₂ ≥ 2` is what
  makes them enough.** (b1) `dim(ρ̄₁ ∩ Π_u), dim(ρ̄₁ ∩ Π_v) ≤ 1`; (b2)
  `dim(ρ̄₁ ∩ Z) ≤ max(δ₁ + dim Z − 6, dim Z − 2)`; (b3) `ρ̄₁ ∩ E` is not an
  opposite-ruling pencil. In the tight regime these give `lossZ = δ₁ − 4`, and
  `δ₂ = min(m+1,6) ≥ 2` always makes the slack `δ₁ + δ₂ − 6` cover it — 87 of
  91 arithmetic cases outright, the **4** exceptions being exactly the `c₂ = 3`
  corner (`π_u = π_v` **with** `m = 2`). **(BE-37)(ii)/(iii)**.
- **(β) PROVED for the all-S piece, and for every piece with a generic short
  path.** A path piece's `ρ̄₁` **is** a chain, by (BE-30)(i) applied to side 1,
  so the ear machinery measures it: in the (realizable) non-adjacent regime
  `dim(ρ̄₁ ∩ Π_u) = 1`, `dim(ρ̄₁ ∩ Z) = max(2, δ₁ − 2)` and
  `loss = max(0, δ₁ − 4) ≤ slack` at **every** `(k, m)`. And since
  `ρ̄₁ ⊆ ⟨ℓ_e : e ∈ P⟩` for **every** `u–v` path `P` ((BE-30)(iv)), the same
  bound transfers: a piece with a `u–v` path of length `≤ 4` whose interior
  hinge lines are generic against `Z` has `loss = 0` outright, for every ear
  length. **(BE-38)(i)/(ii)**.
- **The falsification arm answered on a sampler that OWES the BTWOCUT ladder
  nothing.** By (BE-16) the pencil condition **is** *every closed star
  coplanar*, so for a piece whose degree-`≥3` vertices form an independent set
  the stratum has a **free parametrization** — a (point, plane) flag at each
  branch vertex and at `u, v`, a free point at each degree-2 vertex inside its
  branch neighbour's plane. Over **24** pieces × **14** independent generic
  draws (paths, thetas, cycles, and subdivided `K₄` / `K_{3,3}` / prism, i.e.
  **R-nodes**), **zero candidates**; and `Π_u ⊆ ρ̄₁` occurs at **exactly** the
  `ρ₁ = 6` (vacuous) rows and nowhere else — asserted, not eyeballed.
  **(BE-38)(iii)**.
- **Verdict: (BE-14) OPEN and unchanged in status. HIT shape 2 — (α), the
  cheaper of the two, is proved.** What is refuted is **one prose statement**
  ((β) as written), with its correct form already in the landed driver.
  `PencilPair K 3 G`, `hbareSplit` and (BE-14)-for-all-`G` are untouched.
  **Not a PENCIL event.** Classification in **(BE-38)(iv)**.
- **Reservation remainder RETURNED.** Consumed: labels **(BE-35)–(BE-38)** and
  *Steps BE34–BE37*. Unconsumed, and returned to §(K-bare-ext)'s tail: label
  **(BE-39)** and ***Step BE38***.

### Standing notation

Inherited from *Steps BE9–BE33* verbatim (`f := def₃`, `g_{uv}`, `δ_{uv}`,
`ρ̄_{uv}`, `ρ_{uv}`, hub, free vertex, flat / hubflat / bundle configuration,
`Π_v := p_v ∧ π_v`, `M(F)`, the Klein form `⟨x,y⟩ = x ∧ y`, the α-plane
`S_p := p ∧ K⁴`, `Λ²π`, `M := p_u ∨ p_v`, `L := π_u ∩ π_v`, `E := Π_u + Π_v`,
the confining space `Z` and `c₂ := dim(ρ̄₂ ∩ Z)`). Added here:

- for a line `M ⊆ K⁴` (2-dimensional) with Plücker point `λ_M`, the
  **tangent hyperplane** `N_M := λ_M^{⊥K}`, which is **5-dimensional** and
  equals `K⁴ ∧ M` (asserted as an identity of spaces by the driver, not assumed);
- for a point `c ∉ M`, the **pencil** `c ∧ M`, 2-dimensional and totally
  singular, `⊆ N_M`;
- `C := W ∩ N_M` for the space `W` built so far;
- `Bad(W) := {p : S_p ⊆ W}`, (BE-33)(i)'s object, computed here **exactly** as
  a nullspace (`S_p ⊆ W ⟺ p ∧ ξ = 0` for every `ξ ∈ W^{⊥K}`) rather than
  sampled;
- **`loss := max(P, Z, R)`** as a number, recomputed in the driver from the
  three mechanisms and **asserted** equal to
  `min(6, δ₁+δ₂) − bad_predicate(...)` on every call, so the two cannot drift;
- **`slack := max(0, δ₁ + δ₂ − 6)`**, the amount of loss the composition
  criterion tolerates.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read beyond the four BINDUC read (`Graph.partitionDef`,
`Graph.deficiency`, `bodyBarDim`, `SimpleGraph.IsGeneralPositionPlacement`);
the screw-space convention is BIMAGE's, read off `kbare_common.build_rigidity`.
**No `.lean` was opened for edit; the standing 2026-08-05 Lean hold binds.**

### Step BE34 — (α): the last step is a pencil meeting a subspace, and the criterion is complete

> **(BE-35)(i)** *(proven; **THE 2-STEP LEMMA**, and it is the whole of (α))*
> Let `M ⊆ K⁴` be 2-dimensional, `N_M = λ_M^{⊥K} = K⁴ ∧ M` (5-dimensional),
> `W ⊆ Λ²K⁴` and `C := W ∩ N_M`. Then
>
> **`max_{c ∉ M} dim(W + c ∧ M) = dim W + 2 − g`**, where
> **`g = 2` iff `dim C = 5`; `g = 1` iff `dim C = 4`, or `dim C = 3` and
> `C = S_t` for some `t ∈ M`; `g = 0` otherwise.**
>
> *Proof.* Every `c ∧ M` lies in `N_M`, so `(c∧M) ∩ W = (c∧M) ∩ C`, and `c` is
> **bad** (gains `< 2`) iff the linear map `φ_c : M → N_M/C`, `r ↦ c ∧ r`, is
> not injective — i.e. iff the `2×2` minors of a `2 × (5 − dim C)` matrix whose
> entries are **linear in `c`** all vanish. Each minor is a **quadratic form**
> in `c`, so *every* `c` is bad iff every minor vanishes identically.
>
> *`dim C ≥ 4`:* `dim N_M/C ≤ 1`, so `φ_c` has a kernel for every `c` —
> everything is bad. Gain `1` is still available unless `N_M ⊆ W` (else
> `Σ_c c∧M = N_M ⊆ C`, false), and gain `0` exactly when `N_M ⊆ W`.
>
> *`dim C = 3`:* one minor. In coordinates `M = ⟨e₀,e₁⟩`,
> `N_M = ⟨e₀₁,e₀₂,e₀₃,e₁₂,e₁₃⟩`, `ψ : N_M ↠ K²` with kernel `C` and columns
> `c_{01},c_{02},c_{03},c_{12},c_{13}`, the minor is
> `Q(a) = a₀a₂[c_{01},c_{02}] + a₀a₃[c_{01},c_{03}] + a₁a₂[c_{01},c_{12}] +
> a₁a₃[c_{01},c_{13}] + a₂²[c_{02},c_{12}] +
> a₂a₃([c_{02},c_{13}]+[c_{03},c_{12}]) + a₃²[c_{03},c_{13}]`.
> If `c_{01} ≠ 0` the first four coefficients force `c_{02},c_{03},c_{12},c_{13}
> ∈ ⟨c_{01}⟩`, contradicting surjectivity of `ψ`. So `c_{01} = 0`, i.e.
> `λ_M ∈ C`; then the surviving three coefficients force either
> `c_{02}=c_{03}=0` (so `C = S_{e₀}`) or, with `c_{02},c_{03}` independent,
> `c_{12} = α c_{02}` and `c_{13} = α c_{03}` for a **common** `α` (that is what
> the mixed coefficient buys), i.e. `C = S_{t'}` with `t' = e₁ − α e₀ ∈ M`.
> Conversely `S_t ⊆ W` for `t ∈ M` makes every `c` bad, since `c ∧ t ∈ S_t ⊆ W`.
>
> *`dim C ≤ 2`:* `T_t := {c : c ∧ t ∈ C}` has dimension `1 + dim(C ∩ S_t)`, and
> `dim(C ∩ S_t) = 2` forces `C ⊆ S_t`, which can hold for **at most one** `t`
> (two distinct `S_t` meet in `⟨λ_M⟩`, 1-dimensional). So at most one `T_t` is a
> plane and the rest are lines or less: the union over the `P¹` of `t` has
> projective dimension `≤ 2 < 3`. Over an infinite field the complement has
> points. ∎
>
> **The one shape a naive dimension count gets WRONG, and it is worth naming.**
> `C = Λ²π'` with `M ⊆ π'` also has `dim(C ∩ S_t) = 2` for **every** `t ∈ M`,
> so the incidence heuristic predicts a covering `P¹`-family of planes. It is
> not: `T_t = π'` for **every** `t` — a **constant** family — so the union is
> `π'`, not `P³`, and `g = 0`. The driver constructs this shape and checks it.
>
> Measured: **2 205** `(W, M)` comparisons of predicted against measured reach
> over 45 lines `M` and seven structured families (`W ⊇ S_t` with `t` on and
> off `M`; `W ⊇ Λ²π'` with `M ⊆ π'`; `W ⊆ N_M`; `dim(W∩N_M) = 3` generic;
> `W ⊇ c∧M`; random `W` of every dimension), **zero mismatches**; and the
> `(dim W, dim C, g)` shape set is **ENUMERATED** — 14 feasible triples,
> **14 realized, 0 missing, 0 unpredicted** (a triple the lemma forbids would
> `assert`).

> **(BE-35)(ii)** *(proven; the ear's last step, and BIMAGE's bad case
> CHARACTERIZED and EXHIBITED)* In the ear, `p_m` is confined to the **plane**
> `π_v`, which meets `M = p_v ∨ p_{m−1}` in the single point `p_v`. Then
>
> **every `p_m ∈ π_v` is bad ⟺ `Π_v ⊆ W_{m−1}`, or `S_t ⊆ W_{m−1}` for some
> `t ∈ M`, or `dim(W_{m−1} ∩ N_M) ≥ 4`.**
>
> *Proof.* The same minor, restricted to `π_v`; the extra clause is the
> contribution of the point `p_v ∈ M ∩ π_v`, at which `φ_{p_v}` degenerates and
> whose pencil is `Π_v = (M ∩ π_v) ∧ π_v`. ∎
>
> **So BIMAGE's cap 2 is answered: the bad case is NOT empty.** Two witnesses
> are constructed: `W_{m−1} = S_q` with `q = p_{m−1}` itself (the schedule has
> spent the whole α-plane of its own current point — which is precisely what
> (BE-33)(i)'s greedy invariant `S_{p_i} ⊄ W_i` exists to prevent), and any
> `W_{m−1} ⊆ N_M` of dimension 4. **But every clause is a condition on the
> SCHEDULE `W_{m−1}`, not on `A`** — which is why (α) is a question about the
> ORDER of the greedy's choices, and is answered by changing it.
>
> Measured: **1 890** `(W, M, π_v)` instances, **both sides decided EXACTLY**
> and not sampled (a quadratic form on a 3-space vanishes identically iff it
> vanishes at the three basis vectors and their three pairwise sums, so the
> six-point test is a **decision procedure**), **zero mismatches**, with all
> four criterion branches exercised (720 / 360 / 270 / 540).

### Step BE35 — the reordering, the end-pair lemma, and the reach formula PROVED for `m ≥ 3`

> **(BE-35)(iii)** *(proven; **THE END-PAIR LEMMA**)* With `Z := Π_u + Π_v`,
> `a := dim(A ∩ Z)` and `P := #{Π ∈ {Π_u, Π_v} : Π ⊆ A}`,
>
> **`max_{x ∈ Π_u, y ∈ Π_v} dim(A + ⟨x,y⟩) = dim A + 2 − e`, with
> `e = max(P, max(0, a + 2 − dim Z))`.**
>
> *Proof.* `dim(A ∩ ⟨x,y⟩) = 2 − dim⟨x̄, ȳ⟩` in the quotient `Z/(A ∩ Z)`, so
> minimising the loss is maximising `dim⟨x̄, ȳ⟩` over `x ∈ Π_u`, `y ∈ Π_v`.
> Write `Π̄_u, Π̄_v` for the images. The maximum is `0` if both images vanish,
> `1` if exactly one vanishes or both are the **same** line, and `2` otherwise.
> Each case matches: both vanish ⟺ `Z ⊆ A` ⟺ `P = 2 = a + 2 − dim Z`; exactly
> one vanishes ⟺ `P = 1`, and then `a < dim Z` so `a + 2 − dim Z ≤ 1`; the same
> line ⟺ `Z ⊆ (A∩Z) + ⟨w⟩` ⟺ `a + 2 − dim Z = 1` with `P = 0`; otherwise the
> maximum is `2 ≤ dim Z − a`, i.e. `a + 2 − dim Z ≤ 0`. ∎
>
> This is the exact statement that mechanisms **(P)** and **(Z)** are **tight at
> the two ends** — no genericity, no dimension count, four cases.

> **(BE-35)(iv)** *(proven for `m ≥ 3`; **THE REORDERING AND THE SLIDE**, and
> this is what closes (α))* Choose in this order: `ℓ_1 ∈ Π_u` and
> `ℓ_{m+1} ∈ Π_v` by (BE-35)(iii); `p_1` any point of `ℓ_1 ∖ {p_u}` and `p_m`
> any point of `ℓ_{m+1} ∖ {p_v}`; the free interior points `p_2, …, p_{m−2}` by
> the (BE-33)(i) α-plane step; and finally `p_{m−1}` **free in `P³`**, closing
> `⟨ℓ_{m−1}, ℓ_m⟩ = p_{m−1} ∧ (p_{m−2} ∨ p_m)` by (BE-35)(i). Then
>
> **`max dim(A + ρ̄₂) = min(6, δ₁ + δ₂ − max(P,Z,R))`** for every `m ≥ 3`.
>
> *Proof of the `≥` half (the `≤` half is (BE-33)(ii)).* The ends give
> `dim W_0 = dim A + 2 − e` with `e = max(P, Z)`; each α-step adds one while
> `dim < 6`; the close adds two (one if `dim W = 5`) unless the 2-step lemma's
> two remaining clauses fire — `dim(W ∩ N_M) ≥ 4`, which with `dim W ≤ 4` means
> `λ_M ∈ W^{⊥K}`, and `Bad(W) ∩ M ≠ ∅`, which with `dim W ≤ 4` means the single
> point of `Bad(W)` lies on `M` ((BE-33)(i)).
>
> **THE SLIDE.** Moving `p_{m−2}` along `ℓ_{m−2}` and `p_m` along `ℓ_{m+1}`
> changes **neither** line, hence leaves `W` — and therefore `Bad(W)` and
> `W^{⊥K}` — **fixed**, while `M = p_{m−2} ∨ p_m` sweeps the **transversals** of
> two fixed lines, a 2-parameter family. The transversals through the single
> point of `Bad(W)` form a curve; the transversals with `λ_M ∈ W^{⊥K}` do too
> (`P(W^{⊥K}) ∩ Klein` is two points, one point, empty, or — when `W^{⊥K}` is a
> pencil — a `P¹`, and in the last case a bad `M` must pass through that
> pencil's vertex). Two proper closed subsets of `P¹ × P¹` over an infinite
> field leave `K`-points. Summing the gains: `dim A + 2 − e + (m−3) + 2 =
> dim A + (m+1) − e`, which is `min(6, δ₁ + δ₂ − e)`. ∎
>
> **Legality is automatic:** each `ℓ_i ∉ W_{i−1} ∋ ℓ_{i−1}` gives `ℓ_i ≠
> ℓ_{i−1}` (no three consecutive points collinear), and `c ∉ M` gives
> `p_{m−2}, p_{m−1}, p_m` non-collinear.
>
> Measured — and this is a **construction**, not a sample: over bimage's own
> `a_battery` × three flag regimes × `m = 1…5`, **1 432** instances, the
> constructed chain reaches the classification's predicted maximum at
> **1 432 / 1 432**, falls short at **0**, exceeds it at **0** (an excess would
> refute the classification). **Every restart count is 1** — the first attempt
> succeeds at all 1 432. Per step, each step's gain is **predicted by its own
> lemma before the draw**: end-pair **924 / 0** shortfalls, α-plane step
> **524 / 0**, closing 2-step **924 / 0**.

> **(BE-35)(v)** *(the `m ≤ 2` corners, and a targeted hunt for a FOURTH
> mechanism)* At `m = 2` the ear has no free interior point: with the ends
> fixed, `ℓ_2 = p_1 ∧ p_2` **is** the transversal, and it is bad for every
> `(p_1, p_2)` iff `ℓ_1 ∧ ℓ_3 ⊆ W_0` (the transversals' Plücker points span
> `ℓ_1 ∧ ℓ_3`). Two cases, and they are **decided**:
>
> - **`ℓ_1, ℓ_3` skew.** `Λ²K⁴ = Λ²ℓ_1 ⊕ (ℓ_1∧ℓ_3) ⊕ Λ²ℓ_3`, and `ℓ_1, ℓ_3 ∈
>   W_0`, so `ℓ_1∧ℓ_3 ⊆ W_0` forces `W_0 = Λ²K⁴` — nothing left to gain.
>   **So the `m = 2` middle step always gains one.**
> - **`ℓ_1, ℓ_3` meeting**, in the plane `σ`. Then `ℓ_1∧ℓ_3 = Λ²σ`, and the
>   step is blocked exactly when `Λ²σ ⊆ W_0`. In the **equal-planes** regime
>   every pair meets, with `σ = π`, and `Λ²π = Z`: this is not a residue but
>   **precisely** the classification's own `c₂ = 3` clause, i.e. (BE-30)(iii)(b)
>   collapsing the image to a single point of `Gr(3,6)`. In the other two
>   regimes a generic pair is skew, and the residue is the possibility that
>   **every optimal** end pair is forced to meet.
>
> At `m = 1` the single interior point is confined to `L = π_u ∩ π_v` and
> `ρ̄₂ = p_1 ∧ M` with `M = p_u ∨ p_v`: the constrained 2-step lemma at `U = L`,
> whose all-bad condition `A ⊇ y ∧ L` for `y ∈ M` **is** mechanism **(R)**.
>
> Measured, and this is the direction's answer to BIMAGE's own *what would
> change this*: over **1 067** targeted `(regime, A, m ≤ 2)` instances with `A`
> **built** to hit each named corner — `A ⊇ ℓ_1 ∧ ℓ_3` (340), `A ⊇ S_t` for `t`
> on `p_u ∨ p_v` (400), `A ⊇` a hyperplane of `Z` (230),
> `A = (p_v ∧ σ)^{⊥K}` (97) — the constructive greedy **agrees with the
> classification at 1 067 / 1 067**: no shortfall, hence **no fourth trapping
> mechanism found**, and no excess, hence no mechanism that is not a bound.

### Step BE36 — (β): the statement is false, the quantifier collapses, and what is left is three generic-position statements

> **(BE-36)** *(proven; **(β) AS STATED IS FALSE**, and the corrected target is
> the landed driver's own)* BIMAGE's ranked successor (1) — carried verbatim
> into this direction's spec and into `notes/Phase39.md`'s hand-off item 1 —
> asks for a configuration with `dim(ρ̄₁ ∩ Z) ≤ dim Z − c₂`. With `c₂ = 2` and
> `ρ̄₁, Z ⊆ Λ²K⁴`,
>
> **`dim(ρ̄₁ ∩ Z) ≥ δ₁ + dim Z − 6` at EVERY configuration**,
>
> so the demand is unsatisfiable as soon as `δ₁ + dim Z − 6 > dim Z − 2`, i.e.
> **`δ₁ ≥ 5`** — in every flag regime, `dim Z` cancelling. **Enumerated** over
> all 14 `(dim Z, δ₁)` rows: unsatisfiable in exactly the **4** rows with
> `δ₁ ≥ 5`, and the forced minimum is **attained** at drawn `ρ̄₁` of every
> dimension against real flags (asserted, never violated).
>
> **The correct target is `loss ≤ slack = max(0, δ₁ + δ₂ − 6)`**, which is
> exactly what `bimage.py hunt` already tests (`pred < min(δ₁+δ₂, 6)`). (β)'s
> `loss = 0` is the special case `δ₁ + δ₂ ≤ 6`. **No measurement changes**; the
> correction is to the prose that travelled with them, and it matters because
> the prose is the sentence a successor would have tried to prove.

> **(BE-37)(i)** *(proven ON THE ATTAINING LOCUS; **THE QUANTIFIER COLLAPSE** —
> the answer to the spec's own job-2 note)* `dim(ρ̄₁ ∩ X) = dim ρ̄₁ + dim X −
> dim(ρ̄₁ + X)`, and `dim ρ̄₁`, `dim(ρ̄₁ + X)` are ranks of matrices polynomial in
> the configuration, hence **lower** semicontinuous.
>
> **The hypothesis this needs, supplied by the coordinator at landing — a
> difference of two lower-semicontinuous functions is NOT upper semicontinuous
> in general.** Witness: `V(t) = ⟨(1,0,0), (0,t,0)⟩` and `X = ⟨(0,1,0)⟩` give
> `dim(V ∩ X) = 1` for `t ≠ 0` and `0` at `t = 0`, so the minimum is **not**
> attained generically once `dim V` drops. The statement is correct exactly
> where **`dim ρ̄₁` is constant** — i.e. **on the locus where the piece
> ATTAINS**, which is a dense open subset and is precisely where (β) is posed
> (its hypothesis is *"a piece satisfying the strengthened statement"*). There
> `dim(ρ̄₁ ∩ X)` **is** upper semicontinuous and attains its **minimum on a dense
> open**, simultaneously for the finitely many `X ∈ {Π_u, Π_v, Z}`, by
> (BE-25)(i)'s own argument. **All three consequences below are unaffected** —
> each is a statement about attaining configurations — and consequence 3 needs
> no semicontinuity at all. Consequences:
>
> 1. *"at **every** configuration"* ⟺ *"at a **generic** configuration"*: the
>    unenumerable quantifier is **not** the obstacle it looks like.
> 2. A random exact draw computes an **upper** bound on `min loss`, so a
>    sampler can report a **false trap** but can **never miss a real one** — an
>    empty hunt corroborates in the **safe** direction. (This is the precise
>    sense in which BIMAGE's 607/607 is stronger than "measured".)
> 3. Since (β) is **existential**, one drawn configuration with `loss ≤ slack`
>    is a **theorem for that piece**.
>
> What this does **not** give is the class-level statement over all pieces.

> **(BE-37)(ii)** *(proven; **THE REDUCTION**, enumerated)* Suppose at some
> configuration **(b1)** `dim(ρ̄₁ ∩ Π_u), dim(ρ̄₁ ∩ Π_v) ≤ 1`; **(b2)**
> `dim(ρ̄₁ ∩ Z) ≤ max(δ₁ + dim Z − 6, dim Z − 2)`; **(b3)** `ρ̄₁ ∩ E` is not an
> opposite-ruling pencil `y ∧ L`. Then `lossP = lossR = 0`, and either
> `lossZ = 0` or `lossZ = δ₁ − 4`; since **`δ₂ = min(m+1,6) ≥ 2` always**,
> `δ₁ − 4 ≤ δ₁ + δ₂ − 6 = slack`. **So (b1)+(b2)+(b3) ⟹ the composition
> criterion.** Enumerated over all **91** arithmetic cases
> `(dim Z, c₂, δ₁, m)`: the reduction **holds in 87** and **fails in 4** —
> exactly `dim Z = 3`, `c₂ = 3`, `δ₁ ≤ 3`, `m = 2`.
>
> **The INFERENCE `lossR = 0` is CORRECTED — 2026-08-28 by (BE-51), direction
> BRULE; the CONCLUSION and every landed measurement are UNCHANGED.** (b3) is an
> **equality** test, so it does not exclude `ρ̄₁` **containing** a `y ∧ L` once
> `dim(ρ̄₁ ∩ E) ≥ 3`, which (b2) permits at `δ₁ ≥ 5`. What holds instead is
> **`lossR ≤ lossZ`**: a 3-dimensional subspace of `E` is a plane of `P(E)`
> meeting the quadric surface in a **conic**, so it carries at most one member
> of each ruling, and both losses equal `dim(ρ̄₁ ∩ E) − 2`. Since the bound used
> is `max(lossP, lossZ, lossR)`, the `loss ≤ slack` conclusion, the 91-case
> enumeration and the 4-row residue all stand — and (b3) **as literally
> stated** is the right hypothesis. **Three further clarifications of this
> statement's own scope**, from (BE-49): (b3) is consulted **only at `m = 1`**
> (mechanism (R) exists nowhere else); at `π_u = π_v` it is **ill-posed** —
> `L` is not a line — and must be **struck**, its content being carried by
> (b2)'s (Z) outright; and all three clauses are posed only at
> **cross-incidence-free** flags (`p_u ∉ π_v`, `p_v ∉ π_u`), a
> configuration-level side-condition this statement omits and the existential
> (β) avoids by (i)(3).

> **(BE-37)(iii)** *(the residue, NAMED rather than smoothed)* The four failing
> rows are the corner where `π_u = π_v` **and** `m = 2`, at which
> (BE-30)(iii)(b) makes `ρ̄₂ = Λ²π` a **single point** of `Gr(3,6)` and the ear
> has no freedom whatever. That corner is **not generic** unless the graph
> **forces** `π_u = π_v`; where it does, (BE-32)(ii)/(iii) **prove** `δ_{uv} = 0`
> for the two known forcing mechanisms (a common triangle; `≥ 3` common
> neighbours) and (BE-32)(+) only **measures** it for the rest (208 418
> instances, aggressive closure, no argument). **This direction's finding is
> that (BE-32)(+) is now the SINGLE named residue of the whole ear case on the
> (β) side** — everything else reduces to (b1)/(b2)/(b3), which are
> generic-position statements about one piece.

### Step BE37 — (β) for real pieces, and the falsification arm on an independent sampler

> **(BE-38)(i)** *(proven for the all-S piece, in the realizable regime)* A path
> piece's `ρ̄₁` **is** the span of a chain from `p_u` to `p_v`, by (BE-30)(i)
> applied to side 1 — the same object the ear image is, so (BE-30)(ii)
> describes its achievable set exactly and the ear machinery measures its
> generic position. In the **non-adjacent** regime, over drawn chains of every
> length `k = 2…6`:
>
> | `k` | `δ₁` | `min dim(ρ̄₁∩Π_u)` | `min dim(ρ̄₁∩Z)` | `min loss` (`m = 1…5`) | `slack` |
> |---|---|---|---|---|---|
> | 2 | 2 | 1 | 2 | 0 | 0,0,0,1,2 |
> | 3 | 3 | 1 | 2 | 0 | 0,0,1,2,3 |
> | 4 | 4 | 1 | 2 | 0 | 0,1,2,3,4 |
> | 5 | 5 | 1 | 3 | 1 | 1,2,3,4,5 |
> | 6 | 6 | 2 | 4 | 2 | 2,3,4,5,6 — **vacuous** |
>
> i.e. exactly `dim(ρ̄₁∩Π_u) = 1` (the first hinge at `u`, and no more),
> `dim(ρ̄₁∩Z) = max(2, δ₁−2)` and `loss = max(0, δ₁−4) ≤ slack` at **every**
> `(k, m)`. The `k = 6` row is the **vacuous corner** the spec's observation 1
> names (`δ₁ = 6 ⟹ ρ̄₁ = Λ²K⁴`, criterion already met).
>
> The other two regimes are annotated rather than counted: in the **adjacent**
> regime `uv ∈ E(G₁)` (the ear has `m ≥ 1` interior vertices and therefore no
> `uv` edge), so `dist_{G₁}(u,v) = 1` and (BE-30)(iv) gives `δ₁ ≤ 1` — the
> `k ≥ 2` rows **describe no piece**; and the **equal-planes** rows are the
> (BE-37)(iii) residue, with (BE-30)(iii)(b) confining **side 1** as well.
> **Unexplained violations of the corrected (β): 0.**

> **(BE-38)(ii)** *(proven, given (i); the transfer to a general piece)* By
> (BE-30)(iv), `ρ̄₁ ⊆ ⟨ℓ_e : e ∈ P⟩` for **every** `u–v` path `P` of the piece,
> so `dim(ρ̄₁ ∩ Z) ≤ dim(⟨P⟩ ∩ Z)` at the **shortest** path. With (i)'s chain
> values that is `≤ max(2, dist + dim Z − 6)`, so
>
> **a piece with `dist_{G₁}(u,v) ≤ 4` has `dim(ρ̄₁ ∩ Z) ≤ dim Z − 2`, hence
> `loss = 0`, hence the ear composition attains — for EVERY ear length `m`** —
>
> provided the shortest path's own interior hinge lines are generic against
> `Z`, which the pencil condition constrains **only at the piece's branch
> vertices**. This is the first *class-level* statement on the (β) side, and it
> is stated with its proviso rather than without.

> **(BE-38)(iii)** *(the falsification arm, on a sampler INDEPENDENT of the
> BTWOCUT ladder — BIMAGE's cap 3, attacked head-on)* By (BE-16) the pencil
> condition **is** *every closed star coplanar*. So for a piece whose
> degree-`≥3` vertices form an **independent set** (and whose degree-2 vertices
> have at most one branch neighbour — subdivisions with each base edge split at
> least three ways), the pencil stratum has a **free parametrization**: a
> (point, plane) flag at each branch vertex **and at `u`, `v`** (whose degree
> rises by one when the ear is glued), then a free point at each degree-2 vertex
> placed in its branch neighbour's plane. Every draw passes
> `assert_generic_star` **and** `kbare_common.verify_pencil_witness`, and the
> chosen plane at `u` is **asserted** equal to `plane_at`'s closed-star plane.
>
> Over **24** pieces × **14** independent generic draws — paths of 3…7 edges
> (all-S), `θ(3,3,3)`, `θ(3,4,5)`, `θ(4,4,4)`, `θ(5,5,5)`, `θ(3,3,6)`,
> `θ(4,5,6)`, `θ(6,6,6)` (P-nodes), `C₈` / `C₁₀` / `C₁₂` at antipodes, and
> **subdivided `K₄` (×3, ×4, ×5), `K_{3,3}` (×3 at two pairs, ×4) and the
> prism (×3 at two pairs)** — i.e. **R-node** pieces, which is BIMAGE's own
> named residue —
>
> **ZERO candidates**: no piece has `min loss > slack` at any ear length
> `m = 1…5`. And `dim(ρ̄₁ ∩ Π_u)` came out `0` at 12 pieces, `1` at 7 and `2` at
> 5 — with `2` occurring at **exactly** the `ρ₁ = 6` rows, which the driver
> **asserts** rather than reports (a `Π_u ⊆ ρ̄₁` at a non-vacuous piece would be
> the (P) trap genuinely realized and would stop the run). This reproduces the
> coordinator's observation 3 on an independent sampler and sharpens it: the
> intersection is `1` for path-like sides, `0` wherever two `u–v` paths leave
> `u` by different edges, and never `2` below `ρ₁ = 6`.
>
> **The MIDDLE clause is FALSE — corrected 2026-08-28 by (BE-45)(iii), direction
> BSHARP.** Six of the rows summarised here (`K₄` ×5 at `0,1` and `0,2`,
> `K_{3,3}` ×5 at `0,3`, prism ×5 at `0,1`, `θ(5,6,7)`, `θ(5,7,9)`) have
> **three** distinct first edges at `u` and `dim(ρ̄₁ ∩ Π_u) = 1`, by **path
> saturation** ((BE-45)(ii)). Distinct first edges are **necessary, not
> sufficient**; the exact criterion is (BE-45)'s dichotomy. **The first and third
> clauses stand and no measurement in this block changes** — this was a summary
> sentence outrunning its own table, the same shape as (BE-36).
>
> **The THIRD clause is FALSE TOO — corrected 2026-09-02 by (BE-104), direction
> BSATUR, and the sentence above is corrected with it.** *"Never `2` below
> `ρ₁ = 6`"* fails at **exactly `ρ₁ = 5`**: at a terminal of side-degree `1` the
> legal planes form a **pencil**, and the one carrying a `t` with
> `p_x ∧ t ∈ ρ̄₁` has `Π_u ⊆ ρ̄₁` outright ((BE-105)(i)/(ii)). **No measurement
> in this block changes** — the assert above is real (it was read at source) but
> it ran only on the flags this sampler **draws at random**, and the bad plane is
> one member of a 1-parameter family. The middle clause over-read a *sufficient*
> condition as a *characterization*; the third over-read a **generic** statement
> as a **universal** one. The surviving form is **(PENCIL-SATURATES-GEN)**, the
> same clause at a **generic flag** ((BE-107)(i)); see §(K-bare-ext) *Steps
> BE103–BE107*.

> **(BE-38)(iv)** *(classification, mandatory and explicit)* **Nothing is
> refuted.** Not `PencilPair K 3 G`; not `hbareSplit`; not (BE-14)-for-all-`G`;
> not the 2-cut step. What **is** refuted is **one prose statement** — BIMAGE's
> ranked successor (1) as literally written, i.e. **(β) as stated** — and its
> **correct form is already what the landed driver tests**. It is a
> **candidate-side correction, not a refutation of anything the arc carries**.
> **No route is closed. No route is opened.** **Not a PENCIL event.**

### Verdict, classification, and the price

**Which HIT shape this is.** **Shape 2** of the spec's four: *one of the two
proved*, and it is **(α)** — the cheaper one, and the one whose closure turns
(BE-33)(ii)'s reach formula from **MEASURED (358/358)** into **PROVED** for
`m ≥ 3`, which is BIMAGE's own headline cap. It is **not shape 1**: (β) is not
proved at class level. It is **not shape 3**: the falsification arm fires empty,
including on a sampler that owes the ladder nothing. It carries **one element of
shape 3's obligation** — (β) as stated is refuted — and the classification is
discharged in (BE-38)(iv).

**Job 1 (α).** **CLOSED.** The last step's two conditions are one condition
about a pencil `p_m ∧ M`; the 2-step lemma decides it completely; the bad case
is non-empty but is a property of the greedy's **order**; the reordering plus
the slide removes it; the reach formula is **proved for `m ≥ 3`**, and `m ≤ 2`
is reduced to two explicit cases, one of which (the meeting end pair in the
equal-planes regime) **is** the classification's own `c₂ = 3` clause.

**Job 2 (β).** **Partially closed, and its statement corrected.** As written it
is false at `δ₁ ≥ 5`; corrected, it collapses to a generic-configuration
question, reduces to three generic-position statements because `δ₂ ≥ 2` always
covers the deficit, is **proved for the all-S piece** and for **any piece with a
generic `u–v` path of length `≤ 4`**, and leaves **(BE-32)(+)** — *forced
`π_u = π_v ⇒ δ_{uv} = 0`* — as the **single named residue**.

**Job 3 (the S+P generalization).** **SKIPPED EXPLICITLY**, exactly as the spec
authorizes: job 2 did not close, and job 1 grew into four lemmas rather than
one. Its input is nevertheless improved: (BE-38)(ii) is the S+P statement's
shortest-path half.

**The price, re-quoted against BIMAGE's.**

- **BIMAGE's headline cap is DISCHARGED for `m ≥ 3`.** *"The claim that the loss
  is exactly their maximum is measured at 358/358 and has no argument"* — it now
  has one, for every ear with a free interior vertex.
- **What it will cost next.** **(1)** **(BE-32)(+)**, promoted from measured to
  proved: *a graph that forces `π_u = π_v` has `δ_{uv} = 0`*. It is now the
  **only** thing between (b1)/(b2)/(b3) and the ear case, it is purely
  combinatorial-plus-forcing, and (BE-32)(ii)/(iii) already prove two of its
  mechanisms. **(2)** **(b2) for a general piece**: the shortest-path transfer
  (BE-38)(ii) needs the path's interior hinge lines generic against `Z`, which
  is a statement about branch vertices only. **(3)** The **internal R-node**
  ((BE-31)(ii)) — unchanged in value, and now with an independent configuration
  sampler for it ((BE-38)(iii)'s subdivisions).
- **What a successor should attack, in this pass's ranking.**
  **(1)** **(BE-32)(+) as a theorem** — the ear case's single named residue.
  **(2)** **(b2) for a general piece** via the shortest-path transfer.
  **(3)** The **internal R-node**, with the free sampler now in hand.
  **(4)** BTWOCUT's successor (2), the bundle-construction proof — unchanged,
  still skipped.

### Verification

`python3 notes/scripts/w4/bearcase.py twostep` (38 s — the 2-step lemma at
2 205 comparisons over seven structured families, plus the ENUMERATED
`(dim W, dim C, gain)` shape coverage and the two constructed extremal shapes);
`laststep` (6 s — the constrained criterion, 1 890 instances, both sides decided
exactly, plus the two constructed bad-case witnesses); `greedy` (41 s — the
reordered greedy run constructively against `bimage.bad_predicate` at 1 432
instances, with per-step lemma predictions); `corners` (87 s — 1 067 targeted
`m ≤ 2` instances hunting a fourth mechanism); `betadim` (0.5 s — the count that
refutes (β) as stated, enumerated over all 14 `(dim Z, δ₁)` rows); `betasp`
(73 s — the reduction over 91 arithmetic cases, plus the all-S chain scan per
regime and length); `betahunt` (165 s — 24 pieces × 14 generic draws on the
independent sampler). `validate` runs reduced tiers of all seven in **114 s**.

**F25 bar, read off the shipped driver.** Seven modes, one per headline
sentence; every *"every" / "always" / "the only"* sentence backed by an
**enumerating** tier — the 2-step lemma's 14 feasible `(dim W, dim C, gain)`
shapes are computed and coverage asserted, not eyeballed; the last-step
criterion is decided **exactly** on both sides by a finite six-point test that
is a decision procedure for the identical vanishing of a quadratic form, not a
sample; (BE-36) and (BE-37)(ii) enumerate their arithmetic case spaces (14 and
91 rows) in full. Every subspace claim is an identity of **spaces**
(`same_space`, `contains`), never of dimensions; `isect` asserts the dimension
formula on every call; `N_M = λ_M^{⊥K}` is **asserted** equal to `K⁴ ∧ M`;
`loss_exact` is **asserted** consistent with `bimage.bad_predicate` on every
call, so the new number and the landed classification cannot drift; every rng is
seeded with a printed literal; every sampled configuration passes
`assert_generic_star` **and** `kbare_common.verify_pencil_witness`. **All
figures exact ℚ**; no GF(p) and no floating point anywhere. **No scratchpad
probe backs any claim in this section** — the exploratory scripts that preceded
the driver were discarded and every figure above is a shipped driver mode.

### Caps, disclosed rather than smoothed

1. **The reach formula is proved for `m ≥ 3`, NOT for `m ≤ 2`.** At `m = 2` the
   proof is complete **given a skew optimal end pair**; the possibility that
   every optimal end pair is forced to meet (outside the equal-planes regime,
   where meeting is universal and is exactly the `c₂ = 3` clause) is **not
   excluded by argument**. No instance of it appears in 1 432 + 1 067 instances.
   At `m = 1` the reduction to the constrained 2-step lemma at `U = L` is
   proved and mechanism (R) is identified with its all-bad condition, but the
   `U = L` case analysis is not written out to the standard of (BE-35)(i).
2. **(β) is NOT proved at class level.** What is proved is the reduction, the
   quantifier collapse, the all-S case, and the `dist ≤ 4` transfer **with its
   genericity proviso**. The residue is (BE-32)(+), which remains **measured**.
3. **(BE-38)(ii)'s proviso is real.** *"The shortest path's interior hinge lines
   are generic against `Z`"* is a statement the pencil condition could in
   principle obstruct at branch vertices; it is verified on the (BE-38)(iii)
   battery and **not** proved.
4. **The (BE-38)(iii) sampler has a shape guard.** It covers pieces whose
   degree-`≥3` vertices form an independent set and whose degree-2 vertices
   have at most one branch neighbour — subdivisions with each base edge split
   at least three ways. It says **nothing** about pieces with adjacent branch
   vertices. Report: *"no candidate found under this cap"*, never *"none
   exists"*.
5. **`δ₁` in (BE-38)(iii) is the MEASURED `max dim ρ̄₁` over draws**, a lower
   bound on the combinatorial `δ₁`, which **under**-states the slack and so
   **over**-reports candidates. That is the conservative direction, and it is
   why an empty column there is meaningful; it is not a substitute for the
   combinatorial oracle, which is out of reach at these vertex counts.
6. **The `greedy` and `corners` modes randomize inside each lemma's guaranteed
   choice set.** Each step's target is fixed by a **proved** lemma *before* the
   draw and the driver records shortfalls per step, so the composite figure is a
   construction check rather than a search; but the individual point choices are
   drawn from dense opens rather than written in closed form.
7. **`a_battery` is BIMAGE's battery, deliberately.** Using the same `A`-battery
   is what makes 1 432 comparable to BIMAGE's 358; it inherits that battery's
   coverage and its gaps.
8. **The semicontinuity argument assumes the configuration space irreducible**,
   which is (BE-25)(i)'s own standing assumption, inherited and not re-derived.
9. **The `greedy` and `corners` modes run `m = 1…5` only.** `m ≥ 6` is covered
   by the same argument with no new case — `δ₂ = 6` and the `min(6, ·)` cap
   binds — but it is **not** in the measured tier.
10. **No `.lean`** — the standing 2026-08-05 Lean hold. No Lean file was opened
   for edit and no Lean body was read that BIMAGE had not already read.

### Harness note — the `kbare/` sibling-import set gains its SIXTH `w4/` consumer

`notes/scripts/README.md` *Harness debt* → *the `kbare/` sibling imports;
**UNPAID***. BATTAIN was the first `w4/` consumer, `bzavoid` the second,
`binduc` the third, `btwocut` the fourth, `bimage` the fifth; `bearcase.py` is
the **sixth**, and the chain is now **six deep**
(`battain → bzavoid → binduc → btwocut → bimage → bearcase`). **No move made**
(a dispatch may not edit a landed driver another direction may be importing in
flight). Recorded consumer list, to be extended by the coordinator at landing:

| name | current home | consumers |
|---|---|---|
| `exactcore.{rank,nullspace,hat,neighbors,wedge2}` | `notes/scripts/` | + `w4/bearcase.py` |
| `kbare_common.{verts_of,build_rigidity,exact_deficiency,verify_pencil_witness}` | `notes/scripts/kbare/` | + `w4/bearcase.py` |
| `binduc.{assert_generic_star,cycle,def_by_partitions,ear,hubs_of,motion_space,path,rel_screw_space,split_at_pair,theta}` | `w4/` | + `w4/bearcase.py` (**third external consumer**) |
| `btwocut.{deltas_at,extended_construction,split_battery,two_cut_census}` | `w4/` | + `w4/bearcase.py` (**second external consumer**) |
| `bimage.{I6,alpha_plane,a_battery,bad_predicate,chain_of,contains,dim,is_decomposable,isect,klein,klein_perp,lam2,legal_chain,line_points,pencil_space,pencil_vertex,perp_std,plane_at,plane_meet,pt_in,rho_bar_of,rq,sample_flags,same_space,span,target_of,v4,sample_ear_span}` | `w4/` | `w4/bearcase.py` (**FIRST external consumer of any `bimage` device**) |

### Confidence verdicts, per claim

- **(BE-35)(i) (the 2-step lemma): PROVEN** — three cases, elementary, with the
  `Λ²π'` near miss handled explicitly; enumerated over all 14 feasible shapes
  and checked at 2 205 comparisons.
- **(BE-35)(ii) (the ear's last step): PROVEN** — the same minor restricted to
  `π_v`; both sides **decided exactly** at 1 890 instances. The bad case is
  **non-empty**, with constructed witnesses.
- **(BE-35)(iii) (the end-pair lemma): PROVEN** — four cases in the quotient
  `Z/(A ∩ Z)`; no genericity and no dimension count.
- **(BE-35)(iv) (the reordering; the reach formula): PROVEN for `m ≥ 3`.** The
  slide argument is a 2-parameter-family-against-a-curve count **on `P¹ × P¹`,
  not a codimension count on a moduli space** — the object is two explicit
  proper closed subsets, and ZJACOB (JC-6) is respected.
- **(BE-35)(v) (`m ≤ 2`): PROVED at `m = 2` given a skew optimal end pair,
  otherwise MEASURED** at 1 067 targeted instances; no fourth mechanism found.
- **(BE-36) ((β) as stated is false): PROVEN** — one inequality, enumerated over
  all 14 rows. This is a **refutation of a statement**, not of a result.
- **(BE-37)(i) (the quantifier collapse): PROVEN**, on (BE-25)(i)'s standing
  irreducibility assumption.
- **(BE-37)(ii) (the reduction): PROVEN**, enumerated over 91 arithmetic cases;
  the 4 failures are the `c₂ = 3` corner and are named, not smoothed.
- **(BE-37)(iii) ((BE-32)(+) is the single residue): a ROUTE claim**, sound
  given (ii), and it is the sharpest thing this direction says about where the
  ear case now stands.
- **(BE-38)(i) ((β) for the all-S piece): PROVEN in the non-adjacent regime**,
  with the adjacent rows shown **non-realizable** and the equal-planes rows
  identified with the (BE-37)(iii) residue.
- **(BE-38)(ii) (the `dist ≤ 4` transfer): PROVEN modulo a named genericity
  proviso** at the shortest path's branch vertices.
- **(BE-38)(iii) (the falsification arm): MEASURED**, 24 pieces × 14 generic
  draws, on a sampler independent of the BTWOCUT ladder — and by (BE-37)(i)(3)
  **each non-trapped draw is a per-piece theorem**, so the column is stronger
  than a sample even though the class-level statement is not.
- **(BE-38)(iv) (classification): PROVEN** — nothing refuted but one prose
  statement, with its correct form already in the landed driver.

### What would change this

For **(BE-35)(i)**, a `(W, M)` at which the measured reach disagrees with the
three-case criterion — the shape set is finite and enumerated, so a disagreement
would be a computational error, not a new case. For **(BE-35)(iv)**, an `(A,
flags, m ≥ 3)` at which the constructed chain falls **short** of
`bad_predicate` (a fourth mechanism) or **exceeds** it (a mechanism that is not
a bound); the driver reports both and both are 0 at 1 432 + 1 067. For
**(BE-35)(v)**, an `(A, flags)` in the non-adjacent or adjacent regime at which
**every optimal end pair meets** — the one corner where the `m = 2` proof is
conditional. For **(BE-36)**, nothing: it is an inequality. For **(BE-37)(i)**,
a configuration space for the pencil stratum that is **reducible**, which would
break the "one generic draw computes the minimum" reading and is (BE-25)(i)'s
assumption, not this direction's. For **(BE-38)**, a piece whose **generic**
loss exceeds its slack — which, by (BE-37)(i), would now be visible at a
**single** generic draw rather than needing an exhaustive search, and would be
the first genuine candidate for a new universal cap since (BE-23)(ii); the
sharpest place to look is a piece with **adjacent branch vertices**, which the
(BE-38)(iii) sampler's shape guard excludes.

### TERMINATION riders

**E1: NO** — this direction is rank-free projective geometry plus one
semicontinuity argument; no `g`-flank is involved and none is produced. **E2:
NO** — one landed **prose** sentence is corrected ((β) as stated) and its
successor is **in hand and already in the landed driver**, which is the shape E2
explicitly does not fire on; the ear case **narrows** rather than dying, with a
named successor ((BE-32)(+)). **E3: ARMED by GBAL, not fired** — this direction
is on the §(K-bare-ext) path, not (a′); reported, not acted on.
