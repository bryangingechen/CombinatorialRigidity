## §(K-chart) — the pencil chart is irreducible, written down once: the tower of affine-linear fibres, the constant-fibre-dimension clause identified as `IsNondegPencilRealization`'s **conjunct 3**, and a nonemptiness clause that FRES's stated hypotheses do **not** supply

Answering `notes/pencil/fanout.md` §"Seventh fan-out" → direction **CIRR**
(twenty-fourth kernel-(K) direction, 2026-08-19), landed as a **HIT**. Read
against §(K-out) *Steps O13–O18* ((OC-19)), §(K-slide) *Step 1(e)* ((S1)),
§(K-dom) *Step D4* ((D4)), §(K-ann) *Steps A10/A14–A17* ((ANH-9)) and
§(K-frame) *Step FR13* ((FR-16)) — its four consumers, plus the section that
found the same gap independently the same day. Driver:
`notes/scripts/w4/cirr.py` (three modes, `--empty`/`--guard`/`--fibre`, run
together by `--all`).

**Why this section exists.** The fact "the pencil chart of `G′` is irreducible"
is consumed by §(K-out) **(OC-19)** input (b), §(K-slide) **(S1)(e)**, §(K-dom)
**(D4)** and §(K-ann) **(ANH-9)(ii)** — four sections, at least two independent
routes — and until this pass it was **stated nowhere as a theorem**: (S1)(e)
carries it in a parenthesis, (ANH-9)(ii) as a phrase, (D4) and (OC-19) by
citation. §(K-out)'s *What would change this* item 2 calls it *"the arc's
most-consumed un-driver-tested fact"*; §(K-frame) *Step FR13* (direction FRES,
same day) found (ANH-9)(ii)'s phrase *"irreducible rational parametrization"*
literally true only on `place_pencil_general`'s **constant-fibre-dimension
locus**. This section states it once, proves it, identifies that locus with a
hypothesis the pin **already carries**, and audits all four consumers.

**Three things came out other than the expected bookkeeping.**

1. **The constant-fibre-dimension clause is not an extra hypothesis at all.**
   It is **conjunct 3** of `IsNondegPencilRealization`
   (`LinearIndepOn K normal (G.closedHubNbhd v)`, `Motive.lean:110`) — at hubs
   it forces the tower's stage-1 locus `U_H`, at non-hubs its stage-3 locus
   `N°`. `hK`'s own hypothesis `HasGenericPencilRealization K 3 G′` carries it
   **about `G′`**, and the harness gate `repin.star_generic` implies it too. So
   FRES's restriction costs the consumers nothing, and not for the reason one
   would guess (see item 2) — **(CH-6)**.
2. **The restriction costs nothing for the *closure* either, and that is what
   (S1)(e) needs.** The whole incidence locus `𝒜(Γ)` — including its
   fibre-jump strata — is the **closure** of the constant-fibre-dimension part,
   because the jump is codimension **2** in the base while the fibre gains only
   **1**. So a witness off the locus is still on the irreducible variety, which
   is exactly what (S1)(e)'s contradiction step needs of `data₀` — **(CH-4)**.
3. **Nonemptiness is NOT free at FRES's stated hypotheses, and this is the one
   correction.** *Step FR13*'s tower is stated for `Γ` loopless with `hcard`,
   min degree 2 and **girth ≥ 3**. At girth 3 the stage-3 locus `N°` can be
   **empty**: a Λ-**triangle** `h₁h₂x` (whose three hub-degrees are forced to
   `2` by `hcard`) carrying a non-hub `s` with hub neighbours `h₁, h₂` makes
   `Π(h₁) = Π(h₂)` **identically**, so `place_pencil_general` returns `None` at
   every seed — **0/200**, with the reason asserted, `cirr.py --empty`. Girth
   `≥ 4` suffices; at `G′` girth is `≥ 6`, and the class predicate
   `gridcol.class_shape`'s *no two-hub triangle* filter excludes it a second,
   independent way, as does — strongest of the three, and **compiler-checked** —
   the landed `not_pencilNondegFeasible_of_triangle_two_hubs`. **No consumer is
   disturbed** — every one lives at `G′` — but the hypothesis list in
   *Step FR13* should gain the clause — **(CH-5)**.

---

### Step CH1 — the ambient, named: which variety, over which field, of which `(shape, split)`

Notation is §(K-frame) *Steps FR12–FR15* *Standing notation*, reused verbatim:
for a loopless multigraph `Γ`, `H(Γ)` its hubs (degree `≥ 3` — `PencilHub`,
`Motive.lean:73`), `Λ(Γ)` its hub-hub subgraph, `d_h = |N_Λ(h)|`, `e_s` the
number of hub neighbours of a non-hub `s`; `hcard` (= (R4)) says `d_h ≤ 2`, and
`e_s ≤ 2` is automatic since a non-hub has degree `≤ 2`.
`closedHubNbhd_Γ(u) = {w : deg_Γ w ≥ 3 and (w = u or w ∼ u)}` (`Motive.lean:82`,
the **definition body**) — at a hub, `{h} ∪ N_Λ(h)`, `1 + d_h` members; at a
non-hub, its `e_s` hub neighbours. `closedNbhd_Γ(u) = {u} ∪ N_Γ(u)`.

**Whose chart.** The chart every consumer means is **`G′`'s, not `G`'s**:
`outer.chart_point` (`outer.py:242`), `dominance.base_seed`
(`dominance.py:547`, via `repin.seed_probe`, `repin.py:225`) each call
`place_pencil_general(Gp, …)` with `Gp = splitOff(edges, v, a, b) = G − v + ab`.
`G′` misses tightness by one (`f(V(G′)) = f(V(G)) + 1`, §(K-frame) (FR-15)), so
no statement below mentions a rank target.

**Two ambients, and they are not interchangeable.** Fix a field `K` of
characteristic `0` (the consumers run at `K = ℚ` and `K = ℚ(i)`; class
uniformity over every infinite characteristic-`0` field is (AC-7)'s, not this
section's).

- **Upstairs** — `𝔸(Γ) := (𝔸³_K)^{V(Γ)} × (𝔸³_K)^{H(Γ)}`, coordinates
  `(q, n) = (`body points`, `hub panel normals`)`. This is
  `place_pencil_general`'s **full** return `(placed, nrm)` and the space
  §(K-slide) (S1)'s "chart coordinates" and §(K-dom) (D4)'s frozen
  `Π(b), Π(c)` live in.
- **Downstairs** — `(𝔸³_K)^{V(Γ)}`, the placement alone. This is where
  §(K-out) (OC-17)'s `Z` (rank conditions on `R(G′)`, `R(G − v)`), (OC-19)'s
  `{H/X` inf. rigid`}` and §(K-ann) (ANH-9)'s hinge-line matroid live.

> **Definition (the pencil incidence locus).** `𝒜(Γ) ⊆ 𝔸(Γ)` is the locally
> closed subset cut out by
>
> (i) `n_h ≠ 0` for every hub `h`;
> (ii) `⟨n_h, q_u − q_h⟩ = 0` for every hub `h` and every `u ∈ closedNbhd(h)`;
> (iii) `q_u ≠ q_w` for every edge `uw` of `Γ`,
>
> where `⟨·,·⟩` is the standard form on `K³`. `Φ : 𝒜(Γ) → (𝔸³)^{V(Γ)}` forgets
> the normals, and **`Chart(Γ) := \overline{Φ(𝒜(Γ))}`** (Zariski closure).

(i)–(iii) are **exactly** `place_pencil_general`'s two closing check loops
(`widened.py:206–212`: the `# pencil condition` loop over every hub and every
neighbour, hub or not, and the `# nonzero hinge extensors` loop over every
edge) plus its `if all(x == 0 for x in nrm[h])` guard — read off the source, not
a docstring. So a returned `(placed, nrm)` **is** a `K`-point of `𝒜(Γ)`, and
`𝒜(Γ)` is the honest geometric object the arc samples. In the projective model
(`point, normal : α → Fin 4 → K`) the same locus is cut by
`HasPencilPanelRealization`'s own-panel conjunct plus the landed cross-incidence
theorem `dotProduct_point_eq_zero_of_mem_closedNbhd` (`Motive.lean:363`), and
conjunct 2's link-point independence in place of (iii).

---

### Step CH2 — (CH-1): the statement

> **(CH-1)** *(proven-informally; every clause's proof is below, and the three
> clauses that could have been false are driver-tested — see *Verification*)*
> Let `Γ` be a loopless multigraph with **`hcard`**, **min degree 2** and
> **girth ≥ 4**, and let `K` have characteristic `0`. Write
> `𝒫(Γ) ⊆ 𝒜(Γ)` for the **constant-fibre-dimension locus** of *Step CH3*'s
> tower. Then:
>
> **(a) Irreducible and rational.** `𝒜(Γ)` is a **nonempty, irreducible**
> variety, **rational over the prime field** `ℚ ⊆ K`; and so is
> `Chart(Γ)`.
> **(b) The restriction is inessential.** `𝒫(Γ)` is a **dense open** subset of
> `𝒜(Γ)`, and `𝒜(Γ) = \overline{𝒫(Γ)}` — so a point of `𝒜(Γ)` off the
> constant-fibre-dimension locus is still a point of the same irreducible
> variety.
> **(c) The image contains a dense open.** `Φ(𝒜(Γ))` — hence
> `Φ(𝒫(Γ))` — contains a dense open subset of `Chart(Γ)`, so any nonempty
> open subset of `Chart(Γ)` contains an **honest pencil placement**, not merely
> a point of a closure.
> **(d) Dimensions.**
> `dim 𝒜(Γ) = 3|H| + Σ_{h ∈ H}(3 − d_h) + Σ_{s ∉ H}(3 − e_s)` and
> `dim Chart(Γ) = dim 𝒜(Γ) − |H|`.
> **(e) ℚ-points are dense** in `𝒜(Γ)` and in `Chart(Γ)`.
>
> **The hypotheses, and where each is used.** `hcard` is what makes the tower's
> normal stage nonzero (**(CH-3)**); min degree 2 and girth `≥ 3` (= simple: no
> loop, no parallel pair) are what make the harness's set-valued adjacency
> agree with the multigraph degrees (FRES's rider, *Step FR13*); **girth ≥ 4**
> is what makes `𝒜(Γ)` **nonempty** (**(CH-5)**) — and it is the clause
> *Step FR13* does not carry.
>
> **At the consumers' object it is unconditional.** All three hold at
> `Γ = G′ = G − v + ab` for `G` a class shape and `v` an eligible split:
> `hcard` two independent ways ((FR-15)'s first table row — it is `hK`'s own
> hypothesis about `G′`, and separately combinatorial from `hcard` at `G` via
> (I2)); min degree 2 from (R1) + (I2); **girth(G′) ≥ 6** from (R3) +
> `hnoRigid` via (I2) ((FR-15)'s last table row).

Clause (a) is what all four consumers cite. Clause (b) is what §(K-slide)
(S1)(e) needs and nobody had. Clause (c) is what §(K-out) (OC-19) needs and
nobody had. Clause (e) is what §(K-ann) (ANH-9)(iii) needs — **more than
irreducibility**, and supplied.

---

### Step CH3 — (CH-2)/(CH-3): the proof — the tower, and `hcard`'s exact job

The tower is *Step FR13*'s, restated against `widened.place_pencil_general`'s
source (`widened.py:160`, read this pass) so that each stage names the code that
realizes it.

| stage | what is free | the fibre | its dimension | in `place_pencil_general` |
|---|---|---|---|---|
| **1** | hub points `(q_h)_{h ∈ H}` | — | `3\|H\|` | `pt = {h: rvec3(rng) for h in hubs}` |
| **2** | hub normals `(n_h)` | `ker A_h(q) ∖ 0`, `A_h(q)` the `d_h × 3` matrix of `q_u − q_h`, `u ∈ N_Λ(h)` | `3 − d_h` | `cons = [...for u in nb[h] if u in hubset]`; `basis = nullspace(cons)`; `nrm[h] = Σ co_i b_i` |
| **3** | — | (open condition, no coordinates) | — | `if all(x == 0 for x in d): return None` |
| **4** | non-hub points `(q_s)` | `⋂_{h ∼ s, h ∈ H} Π(q_h, n_h)`, affine of dim `3 − e_s` | `3 − e_s` | `meet_line` (`e_s = 2`), `in_plane_point` (`e_s = 1`), `rvec3` (`e_s = 0`) |

Two open loci make the fibre dimensions **constant**:

- **`U_H`** (stage 1→2): at every hub, `rank A_h(q) = d_h` — equivalently the
  `1 + d_h` points `{q_h} ∪ {q_u : u ∈ N_Λ(h)}` are **affinely independent**.
  Off `U_H` the kernel is **larger** and the stage-2 fibre **jumps**.
- **`N°`** (stage 3): at every non-hub `s` with `e_s = 2` and hub neighbours
  `h₁, h₂`, the affine normals `n_{h₁}, n_{h₂}` are **independent**, so the two
  panels meet in an affine line. This is `localtest.meet_line`'s
  zero-direction test, whose own body shows the three pivot minors **are**
  `±(n₁ × n₂)`'s components, so "no pivot" and "`d = 0`" are the same condition
  (`localtest.py:57–87`).

`𝒫(Γ) := 𝒜(Γ) ∩ U_H ∩ N°`.

> **(CH-2)** *(proven-informally)* `𝒫(Γ)` is a **Zariski-locally-trivial tower
> of fibrations** over the nonempty open `U_H ⊆ (𝔸³)^H`, with irreducible
> fibres of **constant** dimension at every stage. Hence `𝒫(Γ)` is
> **irreducible** and **rational over ℚ**, of the dimension in (CH-1)(d), and
> its ℚ-points are dense.

*Proof.* `U_H` is a nonempty open subset of the affine space `(𝔸³)^H` (nonempty
by (CH-5)(i) below), hence irreducible and ℚ-rational. Stage 2: on `U_H` the
matrix `A_h` has constant rank `d_h`, so `ker A_h` is a **locally free
subsheaf of constant rank `3 − d_h`** of the trivial rank-3 bundle — Zariski-
locally trivial, since a constant-rank kernel is locally cut by the same
nonvanishing `d_h × d_h` minor. Removing the zero section leaves fibres
`𝔸^{3−d_h} ∖ 0`, which are irreducible for `3 − d_h ≥ 1` — **this is where and
only where `hcard` enters, see (CH-3)** — and a Zariski-locally-trivial
fibration with irreducible base and irreducible fibres has irreducible total
space (each trivializing piece `U_i × F` is irreducible, and over an irreducible
base any two nonempty opens meet, so the pieces glue irreducibly). Stage 3
removes a closed subset, leaving an open (nonempty by (CH-5)(ii)). Stage 4 is
again a locally trivial affine bundle: `meet_line`'s base point is given by a
fixed `2 × 2` cofactor formula on each of the three pivot opens and its
direction is `n_{h₁} × n_{h₂}`, so the fibre `⋂ Π` is an affine subspace of
constant dimension `3 − e_s` varying algebraically; `in_plane_point`'s plane
likewise. Each stage is therefore birational over ℚ to base × affine space, so
`𝒫(Γ)` is ℚ-rational, its dimension is the sum of the column, and its ℚ-points
are dense. ∎

*(The parameter count is a cross-check with no proof content: the sampler draws
`3` rationals per hub point, `3 − d_h` coefficients per normal, and `3 − e_s`
per non-hub — exactly (CH-1)(d)'s first sum, and each coefficient-to-vector map
is a linear isomorphism onto its fibre, so the count **is** the dimension.)*

> **(CH-3)** *(proven; arithmetic of the tower, and asserted per sample)*
> `hcard` is **exactly** the hypothesis that makes stage 2's fibre nonzero:
> `d_h ≤ 2` gives `rank A_h ≤ 2`, so `dim ker A_h ≥ 1` at **every** point of
> `(𝔸³)^H` — on `U_H` or not. Consequently
> `place_pencil_general`'s `return None` on `if not basis:` — its
> *"3 independent hub neighbours"* branch — is **unreachable** under `hcard`.
> The companion cap `e_s ≤ 2` needs no hypothesis (a non-hub has degree `≤ 2`),
> so stage 4's `len(hn) >= 2` branch is always `e_s = 2` exactly and its
> `hn[0], hn[1]` slicing discards nothing.

*Proof.* `nullspace(cons)` returns `[]` only when `rref(cons)` has a pivot in
every column, i.e. `rank cons = 3` (`exactcore.py:68–83`, read this pass);
`cons` has `d_h ≤ 2` rows. ∎

---

### Step CH4 — (CH-4): the fibre jumps do **not** add a component — the restriction is free even for the closure

This is the clause that turns FRES's *"literally true only on the
constant-fibre-dimension locus"* from a caveat about a phrase into **no loss at
all**, and it is the clause §(K-slide) (S1)(e) needs.

> **(CH-4)** *(proven-informally)* `𝒫(Γ) ⊆ 𝒜(Γ)` is **dense open**, and
> `𝒜(Γ) = \overline{𝒫(Γ)}`. Hence `𝒜(Γ)` is irreducible, `Chart(Γ)` is
> irreducible, and **no point of `𝒜(Γ)` lies off the irreducible variety
> whose generic point defines `M_pen^gen`** — in particular a legal pencil
> realization that fails the constant-fibre-dimension condition is *still* a
> point of the same chart, and semicontinuity from it is still valid.

*Proof.* Open: `U_H` and `N°` are defined by non-vanishing of minors and of a
cross product, both polynomial in the coordinates. Dense: it suffices that
every point of `𝒜(Γ)` is a limit of points of `𝒫(Γ)`, which we exhibit.

**There are two jump strata, not one** — this is worth saying because `𝒜(Γ)` is
defined by **equations**, so it contains configurations the *sampler* rejects:
stage 2's (`rank A_h < d_h`, the normal space too big) and stage 4's (the two
panels at an `e_s = 2` non-hub **coincide**, so the "meet line" is a plane and
`meet_line` returns a zero direction). Both are handled.

*(a) The jump is codimension 2 while the fibre gains only 1.* Under `hcard`,
`rank A_h < d_h` is possible only at `d_h = 2` with `rank A_h = 1` (at
`d_h = 1` a rank drop means `q_u = q_h`, excluded by (iii) on the hub-hub edge
`hu`; `d_h = 0` is vacuous). `rank A_h = 1` says `q_h, q_{u₁}, q_{u₂}` are
**collinear**, which is **codimension 2** in the `q`-coordinates, while the
stage-2 fibre grows from `1` to `2` — dimension `−2 + 1 = −1`. So every jump
stratum has dimension **strictly less** than `dim 𝒫`, and no jump stratum can
be a top-dimensional component. *(This is not yet the claim: a lower-
dimensional extra component would still destroy irreducibility. (b) rules it
out.)*

*(b) Every jump-stratum point is a limit of `𝒫`-points.* Let
`(q⁰, n⁰) ∈ 𝒜(Γ)` with `rank A_{h}(q⁰) = 1` at the hubs of some set `S`, so
`n⁰_h ∈ ker A_h(q⁰)`, a 2-plane. Fix `h ∈ S`, write `e` for the common
direction of `q⁰_{u₁} − q⁰_h` and `q⁰_{u₂} − q⁰_h`, so
`ker A_h(q⁰) = e^⊥`. Perturb one hub point: `q_{u₂}(t) = q⁰_{u₂} + t·w`. Then
`A_h(q(t))` has rows `e`-parallel and `(q⁰_{u₂} − q⁰_h) + t w`, so for `t ≠ 0`
its kernel is the **line** `⟨e × w⟩`, **independent of `t`**; and as `w` ranges
over `K³` the line `⟨e × w⟩` ranges over **every** line of `e^⊥`. Choose `w`
with `⟨e × w⟩ = ⟨n⁰_h⟩` and rescale the stage-2 coefficient so that
`n_h(t) ≡ n⁰_h`; do this independently at each `h ∈ S` (the perturbed points
are distinct hubs' coordinates, so the choices do not interact — and if two hubs
of `S` share a neighbour, perturb along a curve in the shared coordinate, which
the same computation allows since only the *direction* `e × w` matters). At the
non-hubs, `q_s(t) := p̄_s(q(t), n(t)) + Σ λ_i d_i(q(t), n(t))` with `p̄, d`
the cofactor base point and direction of stage 4 and `λ` the coordinates of
`q⁰_s` in that frame at `t = 0`; these are rational in `t`, defined at `t = 0`,
and reduce to `q⁰_s` there. All of (i)–(iii), `U_H` and `N°` are open
conditions holding at `t = 0` for the *limit* data or by construction for
`t ≠ 0`, so the curve lies in `𝒫(Γ)` for all but finitely many `t` and tends to
the given point.

*(c) The stage-4 jump stratum is also in the closure.* Suppose instead that at
some non-hub `s` with `e_s = 2` the two panels **coincide** (on `𝒜(Γ)` they
cannot be parallel-and-distinct — equation (ii) puts `q_s` on both), so `q_s^0`
is an arbitrary point of the common plane while `𝒫`'s fibre there is a line.
Codimension: `n_{h₁} ∥ n_{h₂}` is **2** conditions and equality of the two
offsets a **third**, against a fibre gain of `1` — again a strict dimension
drop. Membership in the closure: perturb so that plane 2 becomes
`⟨n + tm, x⟩ = c + ts`; the meet with plane 1 is then
`{⟨n, x⟩ = c, ⟨m, x⟩ = s}`, a line **inside** plane 1 that is independent of
`t` and that sweeps **every** line of plane 1 as `(m, s)` varies. Choose
`(m, s)` so the line passes through `q_s^0` and take `q_s(t) ≡ q_s^0`. The
perturbation is realizable inside the tower for the same reason as in (b): if
`d_{h_i} ≤ 1` the normal has free directions; if both are `2` the two normals
are pinned by two **different** hub-point triples (girth `≥ 4` via (CH-5)(iii)
rules out equal triples), so moving a hub point exclusive to one triple tilts
that panel alone. Hence `𝒜(Γ) ⊆ \overline{𝒫(Γ)}`. ∎

*(d) `Chart(Γ)` and clause (c) of (CH-1).* `Φ` is a morphism, so
`Φ(𝒜) ⊆ \overline{Φ(𝒫)}` and the two closures agree; `Chart(Γ)` is the closure
of the image of an irreducible variety, hence irreducible, and by Chevalley
`Φ(𝒫)` is constructible and dense in it, hence contains a dense open. For
rationality of `Chart(Γ)`: on the open subset where each hub's **closed star**
spans its panel, `n_h` is determined by `q` up to scale (*Step CH6*), so fixing
the first nonvanishing coordinate of each `n_h` to `1` gives a ℚ-rational
section of `Φ` over a dense open; `Φ` restricted to that slice is generically
injective, hence birational onto `Chart(Γ)`, which is therefore ℚ-rational, and
`Φ(𝒫(ℚ))` is dense in `Chart(Γ)`. The generic `Φ`-fibre is then
`(K^*)^{|H|}`, giving (CH-1)(d)'s second formula. ∎

---

### Step CH5 — (CH-5): nonemptiness, the twin-plane obstruction, and the clause *Step FR13* does not carry

Irreducibility of an **empty** variety is worthless, and every consumer needs
`Chart(G′)` to carry points. `U_H` is always fine; `N°` is not.

> **(CH-5)** *(proven-informally; the negative half is **driver-exhibited**,
> `cirr.py --empty`)*
> **(i) `U_H ≠ ∅` always**, for any `Γ` with `hcard`: choose hub points with no
> three collinear (a nonempty open condition on `(𝔸³)^H` over an infinite
> field); since `d_h ≤ 2`, `U_H`'s condition at `h` is exactly that
> `q_h, q_{u₁}, q_{u₂}` are not collinear.
> **(ii) `N° ≠ ∅` iff there is no *twin-plane pair*.** A **twin-plane pair** is
> a non-hub `s` with two hub neighbours `h₁ ≠ h₂` such that
> `d_{h₁} = d_{h₂} = 2` and `{h₁} ∪ N_Λ(h₁) = {h₂} ∪ N_Λ(h₂)`. At a twin-plane
> pair the two panels **coincide identically on `U_H`**, so `N° = ∅` and
> `place_pencil_general` returns `None` at every draw.
> **(iii) A twin-plane pair forces a 3-cycle.** `{h₁} ∪ N_Λ(h₁) =
> {h₂} ∪ N_Λ(h₂)` with `h₁ ≠ h₂` forces `h₁ ∼ h₂`, hence with `h₁ ∼ s ∼ h₂` a
> triangle `h₁ s h₂` of `Γ` (and a Λ-triangle `h₁h₂x` on the common third
> hub). **So `girth(Γ) ≥ 4` ⟹ `N° ≠ ∅` ⟹ `𝒜(Γ) ≠ ∅`.**
> **(iv) `girth ≥ 3` is NOT enough**, so *Step FR13*'s standing hypothesis list
> is one clause short — see the witness below.
> **(v) At `G′` it is free, three times over** — the third leg is landed Lean
> and is strictly the strongest: **`not_pencilNondegFeasible_of_triangle_two_
> hubs`** (`Motive.lean:563`, see (CH-8)) says a triangle with two adjacent hubs
> makes `PencilNondegFeasible` **false**, and by (iii) every twin-plane pair
> carries one (take the triangle `s – h₁ – h₂`, with `h₁, h₂` the adjacent
> hubs). So **no graph the pin talks about has a twin-plane pair**, with no
> girth hypothesis and no appeal to the generators. The two combinatorial legs
> stand as they were: `girth(G′) ≥ 6` ((FR-15)'s last
> table row) kills (iii)'s 3-cycle; independently, the landed class predicate
> `gridcol.class_shape` **rejects any shape with a two-hub triangle**
> (`gridcol.py:181`, the body: `if any(len(t & hubs) >= 2 for t in
> triangles(edges)): return None`) — and a Λ-triangle is a triangle with
> **three** hubs, so a fortiori one with `≥ 2`. Since (I2) gives
> `Λ(G′) = Λ(G)`, the Λ-triangle (iii) needs cannot exist at `G′` either.

*Proof.* (i) as stated. (ii) ⇐: if some `h_i` has `d_{h_i} ≤ 1` its normal
fibre has dimension `≥ 2`, so `n_{h₁} ∦ n_{h₂}` is a nonempty open condition on
that fibre; if both have `d = 2` the normals are determined up to scale as the
normals of `aff({q_{h_i}} ∪ {q_u : u ∈ N_Λ(h_i)})`, two planes determined by two **triples**
of free hub points. If the triples differ, pick `x` in one and not the other:
`q_x` is a free coordinate and tilting it moves that plane's direction through a
2-parameter family, so non-parallelism holds on a nonempty open. Finitely many
nonempty opens on the irreducible `U_H` meet. ⇒: if the triples are equal the
two planes are literally the same plane, at every point of `U_H`. (iii) `h₁` is
in the left set and `h₁ ≠ h₂`, so `h₁ ∈ N_Λ(h₂)`; the three-element sets then
share a third hub `x`. ∎

**The witness for (iv)** (`cirr.py --empty`, exact ℚ, seeds `0..199`). `Γ_bad`
on 6 bodies: hubs `h₁, h₂, x` forming a Λ-triangle, a non-hub `s` adjacent to
`h₁` and `h₂`, and `t, t′` padding `x` to degree 3. It is **loopless, simple
(girth 3), min degree 2, and satisfies `hcard`** — every standing hypothesis of
(FR-16) — and `place_pencil_general` places it **0/200**. The **reason**, not
the symptom, is asserted at all 200 draws by a deliberate stage mirror of the
sampler's stages 1–2: `rank(n_{h₁}, n_{h₂}, n_x) = 1`, i.e. all three panels
coincide. **Two controls separate the two halves of the obstruction**, and this
is the part that makes the characterization sharp rather than a guess:

| graph | Λ-triangle | a non-hub on two triangle hubs | placeable |
|---|---|---|---|
| `Γ_bad` | yes | yes (`s` on `h₁, h₂`) | **0 / 200** |
| control (a) — subdivide the Λ-edge `h₁h₂` | **no** | — | 187 / 200 |
| control (b) — subdivide `h₁s` instead | **yes** | **no** | 174 / 200 |

Control (b) is the informative one: **a Λ-triangle alone is harmless to the
tower.** Its panels still coincide identically — nothing asks for their meet.
(What it is *not* harmless to is `IsNondegPencilRealization`: see (CH-8).)

---

### Step CH6 — (CH-6): the constant-fibre-dimension clause **is** `IsNondegPencilRealization`'s conjunct 3

The dispatch asked for the constant-fibre-dimension hypothesis to be made
explicit. It is explicit — and it turns out to be a hypothesis the pin already
carries, at which point it stops being a hypothesis of this section at all.

Read off the definition body (`Motive.lean:110`, not its docstring):

```
IsNondegPencilRealization G F normal point :=
  HasPencilPanelRealization G F normal point ∧
  (∀ e u v, G.IsLink e u v → LinearIndependent K ![point u, point v]) ∧   -- 2
  (∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v)) ∧              -- 3
  (∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v))  -- 4
```

> **(CH-6)** *(proven; the hub half is driver-exhibited two-sidedly,
> `cirr.py --guard`)* At a pencil realization of `Γ`:
> **(i)** conjunct 3 at a **hub** `h` implies `U_H`'s condition at `h`;
> **(ii)** conjunct 3 at a **non-hub** `s` with `e_s = 2` is exactly `N°`'s
> **projective** form (the two panels are distinct hyperplanes), and the affine
> form follows whenever no body is at infinity — (FR-16)'s step (f), verbatim;
> **(iii)** hence conjunct 3 **cuts out the tower's constant-fibre-dimension
> locus**, and `hK`'s hypothesis `HasGenericPencilRealization K 3 G′` — which
> unfolds to `IsNondegPencilRealization G′ …` — supplies it **about `G′`
> itself**, exactly as (FR-15)'s first table row supplies `hcard`;
> **(iv)** harness-side, `repin.star_generic`'s second clause (`no two hinge
> lines at a body coincide`) implies `U_H` as well, and
> `place_pencil_general` enforces `N°` itself — so every seed accepted by
> `outer.chart_point` or `dominance.base_seed` (both of which apply
> `star_generic`) is on `𝒫(Γ)`. **Stated precisely, because one entry point
> differs:** bare `repin.seed_probe` applies **no** `star_generic` (read this
> pass, `repin.py:225–348`; the gate is applied by its callers), so a raw
> `seed_probe` seed is `N°`-clean but **not** `U_H`-certified — which costs
> nothing, by (CH-4).

*Proof.* (i) Suppose `U_H` fails at `h`, necessarily with `d_h = 2` and
`point h, point u₁, point u₂` spanning only a **2-dimensional** subspace `L` of
`K⁴`. The landed theorem
`dotProduct_point_eq_zero_of_mem_closedNbhd` (`Motive.lean:363`, statement read
this pass: from `IsNondegPencilRealization`, `w ∈ G.closedNbhd v` gives
`point v ⬝ᵥ normal w = 0`) gives `normal h ⊥ point h, point u₁, point u₂`, so
`normal h ∈ L^⊥`; and `normal u_i ⊥ point u_i` (own panel) and
`⊥ point h` (cross-incidence, `h ∈ closedNbhd u_i`), and
`span(point h, point u_i) = L` because conjunct 2 makes the two linked points
independent and `L` is only 2-dimensional — so `normal u_i ∈ L^⊥` too.
`dim L^⊥ = 2`, so the three normals of `closedHubNbhd(h) = {h, u₁, u₂}` are
**dependent**: conjunct 3 fails at `h`. At `d_h = 1`, `U_H`'s condition is
`point u ≠ point h`, which is conjunct 2 on the hub-hub edge; at `d_h = 0` it
is vacuous. (ii) `closedHubNbhd(s)` of a non-hub is its hub neighbours, so
conjunct 3 at `s` says `normal h₁, normal h₂` independent, i.e. the panels are
distinct hyperplanes; two distinct hyperplanes of `P³` meet in a line, and in
the affine model the meet is an affine line exactly when the affine normals are
independent — which holds because `q_s` lies on the meet and is an affine point
((FR-16) step (f)). (iii)/(iv) are (i)+(ii) plus a source read: `star_generic`
is `all star ranks == 3 and not coincident_hinges` (`repin.py:214`), and
`coincident_hinges` is empty iff no vertex has two neighbours collinear with it
(`repin.py:179–211`, the body: `rank([C(h,x), C(h,u)]) == 1`), which at
`x, u ∈ N_Λ(h)` is exactly `¬U_H` at `h`. ∎

**The witness that (i) is not vacuous, and the pinned counter-fact**
(`cirr.py --guard`, constructed not sampled, so it does not depend on a seed).
On control (b)'s 7-body graph, place the three Λ-triangle hubs **collinear**
at `(0,0,0), (1,0,0), (2,0,0)` with panels `z = 0`, `y = 0`, `y + z = 0` and the
four non-hubs on the appropriate panels. Then:

- `kbare_common.verify_pencil_witness` is **green** — it is a bona fide pencil
  realization (conjunct 1);
- `repin.star_span_ranks` is **3 at every body** — the **fourth** conjunct
  holds, so the fourth conjunct alone does **not** see the defect (the
  (OC-7)-shaped counter-fact, here in its hub-hub form, which
  `repin.hinge()`'s single-hub-interior slide does not cover);
- and yet `rank A_h = 1 < d_h = 2` at **all three** hubs: the stage-2 fibre is
  **2**-dimensional, so the witness is **off `U_H`** — a legal pencil
  realization in `𝒜(Γ) ∖ 𝒫(Γ)`, which is what makes (CH-4) load-bearing rather
  than decorative;
- `flanks.nondeg_conjuncts` rejects it at **`conjunct 3 (closedHubNbhd normals
  LI)`, witness `('h1', ['h1','h2','x'])`** — (CH-6)(i) exhibited;
- `repin.star_generic` rejects it too (three coincident hinge pairs);
- negative control on a Λ-triangle-**free** graph: a sampled point is on `U_H`
  with conjunct 3 and `star_generic` both green.

---

### Step CH7 — (CH-7): the consumer audit — the exact sentence each of the four needs, and whether (CH-1) supplies it

> **(CH-7)** *(audit; each row's "needs" is the consumer's own wording, and
> each verdict is against (CH-1) as proven above)* **All four consumers are
> clean.** Two of them need **strictly more than irreducibility**, and both
> extras are supplied.

**1. §(K-ann) (ANH-9)(ii)/(iii) — needs irreducibility *and rationality*.**
Its sentence: *"The pencil chart is the image of an irreducible rational
parametrization (hub points, panel normals, panel-constrained interiors …), so
`M_pen^gen` is well-defined, and it is the weak-map-maximal one among the
`M_pen(p)`"*; and (iii) adds *"some **rational** chart point does (ℚ-density of
a nonempty open in the parameter affine space)"*.
**Supplied.** (CH-1)(a) gives irreducibility, so the generic point exists and
the common matroid on the dense open where all finitely many subset-ranks are
simultaneously maximal is well-defined; (CH-1)(e) gives the ℚ-density (CH-2)'s
ℚ-rational tower is the source of. **Flag — this consumer needs more than
irreducibility** (rationality), and it is the reason (CH-2) is stated with
*"rational over ℚ"* rather than just *"irreducible"*. **Refinement of
(ANH-9)(ii)'s phrase**: (FR-16)'s reading (*"literally true of
`place_pencil_general` restricted to its constant-fibre-dimension locus"*) is
correct as a statement about the **parametrization**, and (CH-4) now shows the
restriction changes **no closure**, so the phrase is also true unrestricted as a
statement about the **variety**. Both readings survive; neither is disturbed.

**2. §(K-slide) (S1)(e) — needs irreducibility of the *ambient the witness sits
in*.** Its sentence: *"The chart is irreducible (a tower of affine-linear
fibers: free hub points, normals in hub-dependent linear subspaces, interiors in
panels / meet lines / free space), so `U` is irreducible"* — where
`U ⊆ chart × 𝔸¹` is the maximal-rank locus and the contradiction step needs
`(data₀, 0) ∈ U`.
**Supplied, and this is the consumer for which (CH-4) is not optional.** `U` is
open in `𝒜(G′) × 𝔸¹`, and (CH-4) makes `𝒜(G′)` — not merely `𝒫(G′)` —
irreducible; so `U` is irreducible **and contains `(data₀, 0)`** whether or not
`data₀` is on the constant-fibre-dimension locus. Read the restriction as a
restriction of the *variety*, (S1)(e) would have needed a
constant-fibre-dimension assert on `data₀` that `kslide.py` never made. **Flag:
this consumer needs the closure clause (CH-4), not just (CH-2).** Note (S1)
lives **upstairs** — `slide_ε` moves a chart coordinate and the limit lines read
the panels — so the variety it needs irreducible is `𝒜`, which is what (CH-4)
delivers.

**3. §(K-dom) (D4) — needs irreducibility of a *different variety*.** Its
sentence: *"The chart with `pt(a), pt(b), pt(c), Π(b), Π(c)` frozen is an
irreducible tower of affine-linear fibres (§(K-slide) *Step 1(e)*, with the
first stages frozen)"*.
**Supplied, by a corollary that has to be stated separately — irreducibility of
`𝒜(G′)` does not give it.** A fibre of a projection need not be irreducible.
The corollary: freezing `q_b, q_c` (stage-1 coordinates), `n_b, n_c` (stage-2)
and `q_a` (stage-4) leaves the *same* tower on the remaining coordinates —
remaining hub points free in an affine subspace, remaining normals in
constant-rank kernels of matrices that may now involve frozen points, remaining
non-hubs in constant-dimension affine fibres — so *Step CH3*'s argument runs
verbatim over the sliced base, **provided the slice's own `U_H ∩ N°` is
nonempty**. That is where (D4)'s hypothesis pays for itself: its frozen data
comes from a `dominance.base_seed` seed, and `base_seed` applies
`repin.star_generic` (`dominance.py:569`) which by (CH-6)(iv) puts the seed on
`U_H`, while `place_pencil_general` enforces `N°`. So the sliced locus is
nonempty at the frozen data and the slice is irreducible. **Flag — this
consumer needs a different variety, and its irreducibility rests on the guard
its own seed passes.** Dating rider, recorded not repaired: the composite
`star_generic` was **adopted at `base_seed` on 2026-08-06** (README *Harness
debt* item 4, slice S2); before that the gate was `star_span_ranks` alone,
which the (CH-6) witness shows does **not** imply `U_H`. This pass did **not**
re-run (D4)'s battery; the claim above is about the guard as landed today.

**4. §(K-out) (OC-19) input (b) — needs irreducibility *plus* that the meeting
point is an honest placement.** Its sentence: *"`X` is irreducible … By (OC-17)
and (a), `Z` is a nonempty open of `X`; by (OC-18) and (c),
`{H/X inf. rigid}` is a nonempty open of `X`. By (b) both are dense, so they
meet; at a common point (OC-18) gives `L_b ⊄ R₁` and membership of `Z` gives
the stratum."*
**Supplied.** `Z` and `{H/X` inf. rigid`}` are restrictions to `Chart(G′)` of
maximal-rank opens of the ambient placement space (both are **downstairs**
conditions — a rank of `R(G′)`, `R(G − v)`, `R(H/X)` at a placement), and
(CH-1)(a) makes `Chart(G′)` irreducible, so two nonempty opens meet. **Flag —
the step needs (CH-1)(c) as well, and (OC-19) does not say so:** `Chart(G′)` is
a **closure**, so a point of `Z ∩ {rigid}` need not *a priori* be a genuine
pencil placement, and (OC-8)'s conclusion is about a point *of `Z`*. (CH-1)(c)
supplies it — intersect the two opens with the dense open contained in
`Φ(𝒫(G′))`, three nonempty opens of an irreducible variety, and the common
point is an honest placement. Also: inputs (a) and (c) are unaffected by
anything here; they remain (OC-19)'s named inputs, and **(a) `Z ≠ ∅` is exactly
the nonemptiness this section does *not* supply** — (CH-5) gives `𝒜(G′) ≠ ∅`,
never `Z ≠ ∅`.

**Nobody needs a fifth thing.** In particular no consumer needs *density* of
the constant-fibre-dimension locus **in a stronger sense** than (CH-4)'s
closure statement, no consumer needs irreducibility of `Z` itself ((OC-17)
derives that from the chart's), and no consumer evaluates `repin.star_generic`
inside its argument — (FR-16)'s guard rider applies verbatim, and (AC-9) stays
irrelevant here for the same reason.

---

### Step CH8 — (CH-8) corrected to a POINTER, the duplicate check across (CH-1)–(CH-7), and the scope line

**This entry was written as a new incidental and is corrected to a pointer**
(coordinator verification, 2026-08-19). The fact it stated is landed:

> **`not_pencilNondegFeasible_of_triangle_two_hubs`**
> (`CombinatorialRigidity/Molecular/Molecule/Pencil/Motive.lean:563`; call sites
> at `Witness.lean:303`, `:307`, `:730`, `:734`). Signature read this pass:
> given `x ≠ y`, `y ≠ z`, `x ≠ z`, links `e₁ : x–y`, `e₂ : y–z`, `e₃ : z–x`, and
> `hy : G.PencilHub y`, `hz : G.PencilHub z` — **two** hubs, `x`'s hub status
> irrelevant, and **no `hcard` hypothesis at all** — it concludes
> `¬ PencilNondegFeasible K G`.

> **(CH-8)** *(**cited, not proven here**)* The infeasibility of a `Γ` carrying
> a triangle with two adjacent hubs is `not_pencilNondegFeasible_of_triangle_
> two_hubs`, above. **The landed form is strictly stronger than what this pass
> derived** — two hubs instead of three, and no `hcard` — and its proof runs
> the same mechanism this section uses elsewhere: conjunct 3 at `y` to get
> `normal y, normal z` independent, then
> `dotProduct_point_eq_zero_of_mem_closedNbhd` to force all three triangle
> points into the `2`-dimensional common perp (`finrank_toDualPerp_pair_eq`),
> then conjunct 4 (or conjunct 3 at `x` plus `finrank_toDualPerp_triple_eq`) for
> the contradiction. A Λ-triangle is a triangle with three hubs, hence a
> fortiori one with two adjacent hubs, so **every graph this pass's version
> covered was already covered**.
>
> **What this pass adds is the chart-side contrast, and only that.** At such a
> `Γ` the pin's nondegenerate stratum is empty, but the **harness chart is
> not**: `place_pencil_general` places control (b) at **174/200** seeds, and
> conjunct 3 fails at **every one of the 174** (`cirr.py --guard`, asserted on
> `verify_pencil_witness`'s derived normals). So `𝒜(Γ) ≠ ∅` and
> `PencilNondegFeasible K Γ` **come apart**, and they come apart exactly here.
> That contrast is what (CH-5) needs and what the landed theorem does not say.

**Scope line.** The landed theorem is a **negative** feasibility criterion, not
a step of the *(`≤3`-closedHubNbhd) line* (which is about *propagating*
feasibility); §(K-frame) *Step FR15*'s paragraph on that line applies verbatim
and is untouched. `gridcol.class_shape`'s *no two-hub triangle* filter is named
*two-hub* **because** the landed theorem needs only two — the reason was already
a theorem, and this section does not supply it.

**The duplicate check across (CH-1)–(CH-7).** (CH-8) reached the coordinator as
a new incidental because nobody grepped the Lean tree for a landed statement of
it. So: one line per claim, against actual **declaration signatures** read this
pass — and note that two citations below were first taken from a docstring
(`Motive.lean:513`'s and `:133`'s) and then **re-verified against the decls**,
which moved one of them to a different file.

The tree-level fact that settles most rows at once: **there is no algebraic
geometry in this project's Lean.** `grep -rlE
"Irreducible|IrreducibleSpace|ZariskiTopology|AlgebraicGeometry"
CombinatorialRigidity/` returns **zero files**. Nothing in the Lean tree states,
or could state without new imports, an irreducibility, closure, or
variety-dimension fact.

| claim | landed Lean declaration? | which, and how it relates |
|---|---|---|
| **(CH-1)** the chart is irreducible, ℚ-rational, `Φ(𝒜)` dense, dims | **none, and none possible** | no AG content in the tree. The nearest landed relatives are its **hypothesis discharges**, not the statement: `ncard_closedHubNbhd_splitOff_le_three_of_safe` (`Habitat.lean:90`) is `hcard` at `G` ⟹ `hcard` at `G′` (with an extra `hsafe : ¬PencilHub a ∨ ¬PencilHub b`, satisfied in the habitat because `a` is a degree-2 body) — the **compiler-checked** form of (FR-15)'s first table row route (ii), which this draft previously cited only as workbook prose |
| **(CH-2)** the tower is an irreducible ℚ-rational bundle | **none** | same reason. `linearIndepOn_pencilChartNormal_closedHubNbhd` (`Chart.lean:613`) is the closest object and runs the **other way**: from the seed's three hub-slot normals being independent it *produces* conjunct 3 for the chart's normals. It is a chart-**map** fact ((GR-5)'s direction), not a chart-**variety** fact |
| **(CH-3)** `hcard` makes stage 2 nonzero / the `None` branch unreachable | **none for the sentence; the projective arithmetic IS landed** | `finrank_toDualPerp_single_eq` (`Molecule/Pencil/Statement.lean:410`, dim 3), `finrank_toDualPerp_pair_eq` (`Molecular/Meet.lean:1562`, dim 2 — stated at general `Fin (m+2)`, not just `Fin 4`) and `finrank_toDualPerp_triple_eq` (`Motive.lean:513`, dim 1) are the landed perp-dimension counts whose affine analogue (CH-3) uses. The **converse** direction is landed and strictly stronger in its own direction: `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` (`Motive.lean:409`) *derives* `hcard` from nondegeneracy, where (CH-3) *consumes* `d_h ≤ 2`. (CH-3)'s own content — that a **Python** branch is unreachable — is not a Lean-statable sentence |
| **(CH-4)** `𝒜 = closure(𝒫)` | **none** | a closure statement; no AG in the tree |
| **(CH-5)** nonemptiness ⟺ no twin-plane pair | **none for the chart** — see (v)'s new third leg | `PencilNondegFeasible` is a **different object** (see (CH-8)); the one landed positive-existence witness, `exists_isNondegPencilRealization_parallel_pair` (`Pair.lean:113`), is about that object **and** at one specific graph — its hypotheses are `V(G) = {x, y}`, `E(G) = {e, f}`, a 2-body parallel pair with no hub at all — so it says nothing about `𝒜(Γ)` at a habitat shape |
| **(CH-6)(i)** conjunct 3 at a hub ⟹ `U_H` there | **no declaration; the mechanism is landed inline, for the triangle case only** | `not_pencilNondegFeasible_of_triangle_two_hubs`'s proof (`Motive.lean:563–690`) runs exactly (CH-6)(i)'s perp count, but at a **triangle**. (CH-6)(i) is the **Λ-path** case `u₁ – h – u₂` with `u₁ ≁ u₂`, which no landed declaration covers — and `hcard` permits `d_h = 2` with no triangle, so the path case is the one the habitat actually presents. **Honest calibration: (CH-6)(i) is a re-use of a landed mechanism at a new configuration, not a new mechanism** — the same three lines of perp counting. It earns its place as a *statement* only because the configuration is different and is the one the tower needs |
| **(CH-6)(ii)–(iv)** conjunct 3 at a non-hub is `N°`; the guards | **none** | (ii) is (FR-16) step (f) restated; (iii)/(iv) are source reads of `Escape.lean`'s `hK` slot and of `repin.py` / `outer.py` / `dominance.py` |
| **(CH-7)** the consumer audit | **none, and none applicable** | an audit of four workbook sentences against (CH-1); nothing in Lean states a workbook consumer's needs |

**Consequence for (CH-6)'s standing.** The **triangle** witness of *Step CH6*
lies inside `not_pencilNondegFeasible_of_triangle_two_hubs`'s scope, so on its
own it exhibits only what the landed theorem already predicts. `cirr.py
--guard` therefore also carries a **path-case witness** on control (a) — a
legal pencil realization (`verify_pencil_witness` green) with
`h₁ – x – h₂` a Λ-**path**, `h₁ ≁ h₂`, and **no two-hub triangle in the graph at
all** (asserted, so the non-duplication is itself driver-tested): `U_H` fails at
`x` (`rank = 1 < d_x = 2`) and conjunct 3 at `x` fails (`rank 2 < 3`), and it is
the only conjunct-3 failure. Two riders, stated because they narrow the witness:
the assertions are on the **hand-chosen** normals, not
`verify_pencil_witness`'s derived ones (at this witness `h₁`'s star is
collinear, so the derived normal is not unique — the derivation picks the same
vector at `h₁` and `h₂`); and the **fourth conjunct also fails** here (star
ranks `2`), so the *"the fourth conjunct alone does not see it"* counter-fact is
carried by the **triangle** witness alone.

**No third duplicate turned up.** Rows (CH-1), (CH-2), (CH-4), (CH-7) are
settled by the absence of AG in the tree; (CH-3) and (CH-6) are calibrated
above; (CH-5) is settled by the object mismatch and gains a citation rather than
losing a claim.

**The scope line — four things this section does not say**, so no later reader
has to reconstruct them.

- **No gap-map status moves.** Writing down a consumed fact is insurance, not a
  status move. (OC-8), (ANH-R1), (GR-15), `hK`'s class uniformity, the balance
  layer and route-ledger entry 5 are **exactly** where they were. Two *content*
  cells change wording — §(K-out)'s (OC-19) row may drop *"conditional on
  (b)"* for *"(b) proven, §(K-chart) (CH-1)"*, and §(K-frame)'s (FR-16) rider
  may gain (CH-5)'s girth clause — and the coordinator decides both.
- **§(K-frame) (FR-7) stays struck.** This section does **not** re-open
  §(K-frame) *What would change this* item (iii): (OC-17) struck the (FR-7)
  irreducibility foothold as unnecessary by showing `Z`'s irreducibility is the
  **chart's**, and (CH-1) is precisely the chart's — the opposite of entering
  the foothold. Nothing below (CH-1) is a foothold for the hard-stratum
  target-rank locus.
- **It says nothing about `Z ≠ ∅`, and nothing about rank.** Every rank
  statement in the arc is a condition **on** the chart; this section is about
  the chart. (OC-19)'s inputs (a) and (c) are untouched.
- **The section placement is the coordinator's call.** The material would sit
  equally well as a §(K-out) sub-block (its heaviest consumer) or as its own
  section (four consumers, none of them owners). It is minted under `CH-`
  either way, so no rename is needed.

---

### Confidence verdict — per claim

| claim | verdict | weakest link |
|---|---|---|
| **(CH-1)** the statement | **proven-informally, no named gap** | the composite of (CH-2)/(CH-4)/(CH-5); ordinary informal-tier algebraic geometry (locally trivial fibrations, Chevalley), none Lean-checked |
| **(CH-2)** the tower is an irreducible ℚ-rational bundle | **proven-informally** | "constant-rank kernel ⟹ Zariski-locally-trivial subbundle" is standard and stated without proof |
| **(CH-3)** `hcard` makes the `None` branch unreachable | **proven** | arithmetic (`rank ≤ 2` rows), plus a per-sample assert |
| **(CH-4)** `𝒜 = \overline{𝒫}` | **proven-informally** | the explicit deformation at several jump hubs simultaneously is written for independent coordinates and waved at the shared-neighbour case in one clause |
| **(CH-5)** nonemptiness ⟺ no twin-plane pair | **proven-informally**, negative half **driver-exhibited** | the ⇐ direction's "tilting a free hub point moves the plane through a 2-parameter family" is a genericity argument, not a computation |
| **(CH-6)** conjunct 3 cuts out the locus | **proven** (hub half from the landed `Motive.lean:363` theorem; non-hub half is (FR-16) step (f)) | the affine/projective seam, which needs "no body at infinity" exactly as (FR-16) does |
| **(CH-6)(i)** at the Λ-**path** configuration | **proven**, and driver-exhibited **outside** the landed theorem's reach | a re-use of the landed triangle theorem's perp count at a new configuration, not a new mechanism |
| **(CH-7)** the consumer audit | **audit, clean at all four** | rows 3 and 4 rest on source reads of guards (`dominance.py:569`, `outer.py:242`) and on **no** re-run of those batteries |
| **(CH-8)** triangle-with-two-hubs ⟹ infeasible | **CITED, not proven here** — landed and **compiler-checked** as `not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563`), in a **strictly stronger** form (two hubs, no `hcard`) | none: the only thing this pass adds is the chart-side contrast (`𝒜(Γ) ≠ ∅` while the graph is infeasible), which is measured |

**Headline: a HIT.** The statement is proven-informally with no named gap and
all four consumers audit clean — with the one correction that *Step FR13*'s
stated hypotheses need `girth ≥ 4` (or an explicit nonemptiness clause), which
disturbs no consumer because every one lives at `G′`.

**One self-correction, recorded rather than quietly dropped** (coordinator
verification, 2026-08-19). (CH-8) was drafted as a new incidental and is
**already landed, compiler-checked, and strictly stronger** as
`not_pencilNondegFeasible_of_triangle_two_hubs` (`Motive.lean:563` — the decl
lives in `Motive.lean`; `Witness.lean:303` is a *call site*). It is now a
pointer, and *Step CH8* carries the duplicate check across (CH-1)–(CH-7) that
would have caught it. Nothing else in this section duplicates a landed
declaration, and the only claim whose standing changed as a result is
(CH-6)(i)'s witness coverage — see *Step CH8*'s closing paragraph.

---

### What would change this

1. **A `Γ` in the class habitat with a twin-plane pair** would empty its chart
   outright — no seed, no witness, every §(K-out)/§(K-dom)/§(K-slide) battery
   silently skipping the shape. (CH-5)(v) says there is none, **three** independent
   ways: the girth bound, a filter the generators already apply, and the landed
   `not_pencilNondegFeasible_of_triangle_two_hubs` — which makes the question
   moot for any graph the pin talks about, since such a `Γ` is not
   `PencilNondegFeasible` at all. The
   cheap probe if anyone doubts it: run `gridcol.class_shape`'s triangle filter
   and (CH-5)(ii)'s twin-plane test over the pooled shape sweeps and report
   0 hits per pool.
2. **A consumer that reads the chart as `Φ(𝒫)` rather than `\overline{Φ(𝒫)}`,
   or vice versa**, in a step where the difference bites. (CH-1)(c) is the
   clause that makes the two interchangeable for *"a point of a nonempty
   open"*, and (CH-7) rows 2 and 4 are the two places the arc already relied on
   it without saying so. A future step that needs a point of a **closed**
   condition on the chart cannot use (CH-1)(c) and must say so.
3. **A `d_h = 2` hub whose two hub neighbours are forced collinear by some
   *other* class condition.** (CH-5)(i)'s nonemptiness of `U_H` uses only that
   hub points are free; a future pass that *freezes* hub points (as (D4) does)
   inherits a nonemptiness obligation on the **slice**, and (CH-7) row 3
   discharges it only through the guard `base_seed` applies. A frozen-scoping
   battery that drops `star_generic` re-opens it.
4. **A characteristic-`p` reading.** Everything here is stated in
   characteristic `0` (the cofactor formulas and the cross product are
   characteristic-free, but "generic point / dense open / ℚ-density" is used in
   the arc's characteristic-0 sense). §(K-clos)'s split of `hK` into
   characteristic 0 and characteristic `p` is the place that question belongs;
   this section does not answer it.
5. **A Lean formalization of (CH-1).** Nothing here is Lean-checked and the
   standing 2026-08-05 Lean hold is not touched. If it ever is, (CH-6) is the
   useful half — it says the constant-fibre-dimension clause needs **no new
   hypothesis**, only `IsNondegPencilRealization`'s conjunct 3, which the pin
   already carries.

---

### Verification

**A driver WAS written, contrary to the dispatch's expectation, and the reason
is F11.** FRES's precedent (a pass may return no driver when every hypothesis
it consumes is already asserted by a landed driver and everything above them is
proof) covers (CH-1)/(CH-2)/(CH-4)/(CH-7): those are proof and source-reading.
It does **not** cover (CH-5), whose content is that a **landed statement's
hypothesis list is one clause short** — a sentence about the *sampler's
behaviour at a specific graph*, which is exactly what a driver tests and what
no amount of prose settles. (CH-6)'s hub half is likewise a *must-reject
witness* claim in the sense of `repin.hinge()`. So `cirr.py` exists, with one
mode per driver-testable sentence.

**Nothing existing was modified** (`git diff --name-only` empty before this
commit; the only addition is `notes/scripts/w4/cirr.py`), so the
figure-invariance gate discharges on that check alone.

**Invocation rows landed in `notes/scripts/README.md` §3, `w4/` subsection**
(runtimes measured on the dispatch machine, `PYTHONHASHSEED=0`, seeds
`0..199`):

```
python3 notes/scripts/w4/cirr.py --empty   # <1 s  (CH-5): Gamma_bad 0/200 placeable with the twin-plane REASON asserted at all 200 draws; controls (a) 187/200, (b) 174/200
python3 notes/scripts/w4/cirr.py --guard   # <1 s  (CH-6): TWO constructed off-`U_H` legal realizations -- the TRIANGLE case (conjunct 1 green, fourth conjunct green, conjunct 3 REJECTS) and the PATH case on a graph asserted to have NO two-hub triangle, which is the part `not_pencilNondegFeasible_of_triangle_two_hubs` does not cover; two-sided collinearity/extensor identity; and (CH-8)'s chart-side contrast, 174/174
python3 notes/scripts/w4/cirr.py --fibre   # <1 s  (CH-3): hcard keeps the `None` branch unreachable; `U_H` at 188/188 and 189/189; the pi_q-fibre = 1 <=> star_span_rank = 3 equivalence at 1508 (hub, sample) pairs, both sides witnessed
python3 notes/scripts/w4/cirr.py --all     #  1 s  all three
```

**Which mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (CH-1)(a),(c),(e) | — | **proof-level**: irreducibility, Chevalley, ℚ-density on a rational variety. No finite check can assert membership in, or the irreducibility of, a parametrized image |
| (CH-1)(d) dimensions | `--fibre` (partially) | the only non-arithmetic input is "the generic `Φ`-fibre is `\|H\|`-dimensional", i.e. `dim ker(closed-star differences) = 1` per hub, asserted at **every hub of every sample** (1508 pairs) |
| (CH-2) | — | **proof-level** (bundle argument). Its *hypothesis* `U_H` is asserted per sample by `--fibre` (188/188, 189/189) |
| (CH-3) | `--fibre` + `--empty` | `not cons or len(nullspace(cons)) >= 1` at every hub of every sample; and the stage mirror in `--empty` carries a hard `assert basis` labelled *"(CH-3) VIOLATED"* that has never fired |
| (CH-4) | — | **proof-level**: a limit argument. Not driver-testable. Its *premise* — that legal points off `𝒫` exist at all — **is** exhibited, by `--guard`'s constructed witness |
| (CH-5)(ii)–(iv) | `--empty` | `Γ_bad`: 0/200 placeable **and** `rank(n_{h₁}, n_{h₂}, n_x) = 1` asserted at all 200 draws (the reason, not the symptom); **two controls** isolate each half of the obstruction (187/200 with the triangle broken, 174/200 with the triangle kept and `s` demoted) |
| (CH-5)(i),(v) | — | **proof-level** (i); **source read** (v): `gridcol.class_shape`'s body and (FR-15)'s girth row |
| (CH-6)(i) | `--guard` | the constructed must-reject witness: `nondeg_conjuncts` returns `('conjunct 3 (closedHubNbhd normals LI)', ('h1', ['h1','h2','x']))` while `verify_pencil_witness` is green and `star_span_ranks` is 3 at every body — **the counter-fact is asserted, not narrated**; plus the two-sided collinearity ⟺ extensor-rank-1 identity |
| (CH-6)(i), the Λ-**path** case | `--guard` | the second constructed witness, on control (a): `verify_pencil_witness` green, `rank(hub-nbr diffs at x) = 1 < d_x = 2`, conjunct 3 at `x` of rank `2 < 3` and no other conjunct-3 failure — **plus an assertion that the graph has no two-hub triangle**, so the non-duplication with `not_pencilNondegFeasible_of_triangle_two_hubs` is itself driver-tested. Riders: asserted on the **hand** normals (the derived ones are non-unique here), and the fourth conjunct **also** fails, so the counter-fact is the triangle witness's alone |
| (CH-6)(ii)–(iv) | — | **proof-level** / **source read** (`repin.py:214`, `:179`; `outer.py:242`; `dominance.py:569`) |
| (CH-7) | — | **audit**: proof-level against (CH-1) plus source reads of the four consumers' own sentences. **No battery was re-run**, and the audit says so where it matters (row 3's dating rider) |
| (CH-8) | **not this pass's claim** — `Motive.lean:563` is compiler-checked | what `--guard` measures is only the **chart-side contrast**: control (b) is placeable at 174/200 while conjunct 3 fails at **all 174**, asserted on the **derived** normals (`verify_pencil_witness`'s own) so the test reads conjunct 3 itself and is not pre-empted by the star-rank precondition. The infeasibility itself is cited, not measured and not proven here |

**Source facts read off the landed definitions and driver source, not their
docstrings** (the CLAUDE.md clause; every row opened this pass).

| fact | where | what was read |
|---|---|---|
| `closedHubNbhd u = {w \| PencilHub w ∧ (w = u ∨ ∃ e, IsLink e u w)}` | `Molecule/Pencil/Motive.lean:82` | the **definition body** — hub ⟹ `{h} ∪ N_Λ(h)`, non-hub ⟹ its hub neighbours. Confirms (FR-16)'s reading |
| `PencilHub v = v ∈ V(G) ∧ 3 ≤ G.degree v` | `Motive.lean:73` | hubs are degree-`≥ 3` in the **multigraph** degree |
| the **four conjuncts** of `IsNondegPencilRealization`, conjunct 3 in particular | `Motive.lean:110` | `(∀ v ∈ V(G), LinearIndepOn K normal (G.closedHubNbhd v))` — the whole of (CH-6) |
| the cross-incidence is a **theorem**, not a docstring claim | `Motive.lean:363` `dotProduct_point_eq_zero_of_mem_closedNbhd` | statement + proof body: from `IsNondegPencilRealization`, `w ∈ closedNbhd v ⟹ point v ⬝ᵥ normal w = 0`. (CH-6)(i) uses exactly this |
| `HasPencilPanelRealization`'s conjuncts (own-panel incidence, nonzero point, through-point) | `Molecule/Pencil/Statement.lean:88` | conjunct 1's content — the cross-incidence is **derived**, not a conjunct |
| the chart map is **normals-first** | `Chart.lean:393` (`pencilChartPoint`), `:412` (`pencilChartNormal`) + `Engine.lean:89` (`PencilSeed.ofCoord`, `fillNbr := fillHub`) | `pencilChartNormal` returns the seed's `hubNormal` at a hub — (GR-5)'s direction, the **opposite** of the tower's; `fillNbr` coupling vacuous when `nbrSel` fills all slots |
| the (ANH-9)(ii) parametrization is **points-first**, and its exact stages | `notes/scripts/w4/widened.py:160` `place_pencil_general` | hub points `rvec3`; `nrm[h]` from `nullspace` of the **hub**-neighbour differences; `return None` on `if not basis` (3 independent hub neighbours); non-hubs via `meet_line` / `in_plane_point` / `rvec3`; the two closing check loops that **are** `𝒜(Γ)`'s equations |
| the chart is `G′`'s, not `G`'s | `outer.py:242` (`chart_point`), `dominance.py:547` (`base_seed`), `repin.py:225` (`seed_probe`) | all three call `place_pencil_general(Gp, …)` with `Gp = splitOff(edges, v, a, b) = G − v + ab` |
| `nullspace` returns `[]` exactly at full column rank | `exactcore.py:68` | the `if not basis: return None` branch is `rank cons = 3` — (CH-3) |
| `meet_line` signals "no affine meet" by a zero direction, and the three pivot minors **are** `±(n₁ × n₂)` | `escape/localtest.py:57` | `N°`'s exact algebraic form; the base point is a `2 × 2` cofactor solve — the rationality (CH-2) needs |
| `star_generic = all star ranks 3 ∧ no coincident hinges`; `coincident_hinges` is a collinearity test | `repin.py:214`, `:179` | `rank([C(h,x), C(h,u)]) == 1` — (CH-6)(iv)'s implication |
| `base_seed` applies `star_generic` (since slice S2) | `dominance.py:569` | (CH-7) row 3's discharge, and its dating rider |
| a triangle with **two adjacent hubs** makes `PencilNondegFeasible` **false** — landed, compiler-checked, and **strictly stronger than this pass's (CH-8)** | `Molecule/Pencil/Motive.lean:563` `not_pencilNondegFeasible_of_triangle_two_hubs` (call sites `Witness.lean:303,307,730,734`) | the **signature**: `(hxy) (hyz) (hxz) (h₁ : IsLink e₁ x y) (h₂ : IsLink e₂ y z) (h₃ : IsLink e₃ z x) (hy : PencilHub y) (hz : PencilHub z) : ¬ PencilNondegFeasible K G` — two hubs, `x` arbitrary, **no `hcard`**; and the proof body's first step, which is (CH-6)(i)'s perp count at a triangle |
| `hcard` at `G` ⟹ `hcard` at `G′`, in **Lean** | `Molecule/Pencil/Habitat.lean:90` `ncard_closedHubNbhd_splitOff_le_three_of_safe` | the signature: adds `hsafe : ¬ G.PencilHub a ∨ ¬ G.PencilHub b` to `hcard`, and concludes `∀ w, ((G.splitOff v a b e₀).closedHubNbhd w).ncard ≤ 3`. The compiler-checked form of (FR-15)'s first-row route (ii); `hsafe` holds in the habitat because `a` is a degree-2 body |
| the chart **produces** conjunct 3 (the opposite direction to (CH-6)) | `Molecule/Pencil/Chart.lean:613` `linearIndepOn_pencilChartNormal_closedHubNbhd` | hypothesis is LI of the **seed's** three hub-slot normals; conclusion is `LinearIndepOn K (pencilChartNormal …) (G.closedHubNbhd v)`. A chart-**map** fact, (GR-5)'s direction |
| there is **no algebraic geometry** in the project's Lean | `grep -rlE "Irreducible\|IrreducibleSpace\|ZariskiTopology\|AlgebraicGeometry" CombinatorialRigidity/` | **zero files** — which is what settles the (CH-1)/(CH-2)/(CH-4)/(CH-7) rows of the duplicate check |
| the class predicate rejects two-hub triangles | `w4/gridcol.py:181` `class_shape` | `if any(len(t & hubs) >= 2 for t in triangles(edges)): return None` — (CH-5)(v)'s second route |
| `hcard_ok` is `closedHubNbhd ≤ 3` ⟺ `d_h ≤ 2` | `w4/nogood_subdiv.py:170` | the harness form of (R4) |
| the adjacency is **set**-valued, so a parallel pair counts once | `exactcore.py:132` `neighbors`, and `deg = {v: len(nb[v])}` in `place_pencil_general` | why the statement carries girth `≥ 3` (= simple), FRES's rider made concrete |
| `in_plane_point` routes through the **degenerate** `localtest.plane_basis` | `escape/localtest.py:31`, `:52` | a *sampler-coverage* rider, **not** a defect in `𝒜(Γ)`: at `n₃ = 0` the two in-plane directions are parallel and the `e_s = 1` fibre is sampled on a **line**, not the plane (README §4 convention 1, ≈9 % of POOL-G frames, (OC-7)). Consequence, stated so nobody over-reads it: a landed *positive* witness is unaffected (the point still satisfies every incidence, so it is still a point of `𝒜(Γ)` and semicontinuity from it is valid); what is weakened is any **negative** reading ("no escaping seed found") from a raw sampled battery. `--fibre` sees this artifact directly: it is the mechanism behind the 8 fibre-jump `(hub, sample)` pairs, all at the `d_h = 0` hub, all rejected by `star_generic` |

**Pools.** No pool is minted or aggregated. `--fibre`'s two targets are a
**single** `gridcol.class_shape` shape (`G° = K4`, branch lengths
`(1,1,3,5,3,5)` — chosen because it is the smallest landed class shape carrying
a `d_h = 2` hub, so that `U_H` is not vacuous) and one of its `G′`s. Nothing
here is quotable as a class-level rate, and nothing here is aggregated with
POOL-G / POOL-OC / POOL-W or any other section's pool.
