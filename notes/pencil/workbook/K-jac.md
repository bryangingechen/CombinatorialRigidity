## §(K-jac) — the Jacobian / singular-locus route is **DEAD**, and the reason is that the zero-section Jacobian **computes `rank R(y)` and nothing else**: the identification is exact, classical and free, but its own hypothesis — *the cone has the expected dimension* — is, at its weakest instance, the phase target; and the one structure it advertised as leverage, the pure-condition quadric, is exactly the fibre-degree-2 part the criterion is identically blind to

Direction **ZJACOB** (`notes/Pencil-fanout.md` §"ZJACOB"), the second
direction `notes/Pencil-strategy.md` §9's external-technique shelf has
produced and the head of §9.3's order after ZSHEAR struck (ZH-1). It settles
candidate **(ZH-4)** of that shelf (§9.2). Read against §(K-tight) *Steps 2,
5* (the boundary-load calculus, its escape criterion, and the two-line failure
conic), §(K-pitch) *Step 0* (the pitch polynomial `P = Q(r̃)`), §(K-pure)
*Steps P0, P5, P6* (the pure condition is a **rank** certificate; WW87
Thm 2.18 does not descend to a constrained subfamily), §(K-chart) (the pencil
chart is irreducible), §(K-bare-ext) *Step BE12/BE13* (the universal partition
rank cap, and the cone rank law), §(K-shear) *Step SH5* ((SH-6)'s dichotomy and
the `PGL(4)`-invariance residue), and `notes/Pencil-strategy.md` §2.4 / §2.5 /
§4.6 (the wall and the two filters). Driver
`notes/scripts/w4/zjacob.py`; all exact ℚ, the `--sym` mode fully **symbolic**
(identities in `ℚ[…]`, no sampling).

**One naming collision, cleared before anything else.** §(K-bare-ext)
**(BE-11)**/**(BE-13)**'s *"cone"* is a **degenerate realization stratum** (every
normal in a common 3-space, every point at `q = N^⊥`). This section's *"cone"*
is the **universal infinitesimal-motion cone**, a cone in the *motion* variable
over a base of realizations. They are different objects with the same word; the
one place they meet is *Step JC3*'s second exhibition, which uses (BE-13)'s
stratum as a base and says so.

**Provenance, and it is a hard bar, not a formality.** The idea source is an
**unrefereed preprint** whose own acknowledgment credits an AI assistant with
the refinement of proof details, the Lean formalization and its verification,
and which **this project has not independently checked**. Per top-level
`CLAUDE.md` *Referencing prior work* and `DESIGN.md` *Formalize everything the
argument uses*, it is an **idea source, never a citation**: **no theorem of it
is imported, assumed, or leaned on anywhere in this section — its Theorem 4.2
included.** Everything below stands on (a) classical facts, cited where used —
the Jacobian criterion; Krull's height theorem; and the classical height bounds
for ideals of minors (Eagon–Northcott; Bruns; Eisenbud–Huneke–Ulrich, full
references in *Step JC3*) — and (b) this project's own drivers and definition
bodies. Nothing here needs the source's Theorem 4.2, Lemma 3.4 or
Proposition 3.3, and nothing here is evidence for or against them. *Step JC5*
records the one place where that bar is **not** what kills the route: even if
the source's Theorem 4.2 were granted in full, its analogue for our carrier
would **be** the phase target rather than an input to it, so the death survives
lifting the bar.

**Status, stated before the mathematics.**

- **(ZH-4) is REFUTED, and the refutation is an equivalence plus two
  identities.** The identification the candidate asks for is real, classical
  and free: along the zero section of the motion cone the Jacobian of the
  defining equations is `[ 0 | A(y) ]`, so its rank is **`rank A(y)`** — the
  framework's own rank. *"The cone is generically smooth along its zero
  section"* therefore unfolds, with no computation in between, to *"`rank R(y)`
  attains target generically"*. The promised replacement of a witness hunt by a
  Jacobian-rank computation is the **identity map on the problem**.
  **(JC-1)**.
- **The leverage the candidate advertised — the local-complete-intersection /
  Cohen–Macaulay package — has its own hypothesis equal to the conclusion.**
  Stratifying the cone by corank gives
  `dim 𝒞 = max_{k ≥ 0}(dim B_k + 6 + k)`, so *"`𝒞` is an LCI of the expected
  codimension"* ⟺ `B_0 ≠ ∅` and `codim B_k ≥ k` for every `k ≥ 1`, whose
  **weakest clause is exactly properness** — and on the tight class properness of this
  locus **is** the phase's own target statement. The package is downstream of
  the conclusion, not upstream. **(JC-2)**. This also shows **(ZH-4) and
  (ZH-3) are the same hypothesis in different clothes**, so ZSHEAR's *circular
  as posed* verdict on (ZH-3) transfers verbatim.
- **Every classical theorem in the package points the wrong way, and the one
  number it produces about our locus is the constant `7`.** Eagon–Northcott,
  Bruns and Eisenbud–Huneke–Ulrich all bound the height of an ideal of minors
  from **above**, and all take the generic rank `r` as an **input**. On our
  shapes the sharpest of them reads `height(I_t) ≤ 6|V| − 6(|V|−1) + 1 = 7`,
  **the same 7 at every class habitat measured** — so it does not see the graph
  at all, and dies on `notes/Pencil-strategy.md` §4.6's growing-ground-set
  filter as well. Exhibited twice, at a tight carrier and at a constructed one.
  **(JC-3)**.
- **And the criterion is identically blind to the half of §(K-pure) that
  (ZH-4) named as its leverage.** Every partial derivative of an equation of
  **fibre-degree ≥ 2** vanishes identically on the zero section — shown for a
  general fibre-quadratic with free coefficients and for the arc's own pitch
  quadric `Q(t) = ⟨t, ★t⟩`. So a cone carrying the pitch condition is singular
  along its **whole** zero section at every `y`, and the zero-section Jacobian
  criterion is **vacuous** on it. By (PC-Z)/(PC5) the arc's obstruction (W4) is
  exactly such a quadric condition. **(JC-4)**.
- **The re-encoding is faithful, which is why it is useless.** `𝒞_G` sits
  inside `𝒞_{G−v} × K⁶` cut by the **10** new hinge rows on **6** new columns,
  and *"do they cut the expected 4?"* is §(K-tight) *Step 2.1*'s corank identity
  verbatim; and over an escaping seed the zero-section singular locus is
  *Step 2.4*'s **degenerate conic `line(ab) ∪ P′`**, both factors exhibited at
  four named carriers. The scheme language re-derives the arc's own criterion
  and stops in the same place. **(JC-5)**.
- **The general form is a conservation law for the technique.** The
  determinantal / scheme-theoretic package converts *expected codimension* into
  structure (regularity, Cohen–Macaulayness, equidimensionality, resolutions);
  it contains no theorem that **produces** expected codimension over a
  non-generic base. Properness is the weakest instance of expected codimension.
  Hence **no repackaging of the arc's rank question in this language can supply
  properness.** Fifth instance of §4.6 (R1)'s relocation pattern, the **second
  one backwards** after ZSHEAR, and the **first that relocates onto the
  conclusion itself** rather than onto another open step. **(JC-6)**.
- **Gap-map effect: NONE.** No *State of (K)* row moves and no status keyword
  changes. What moves is `notes/Pencil-strategy.md` §9's shelf: **(ZH-4) is
  struck**, **(ZH-3)'s circularity is confirmed and explained** (it is (ZH-4)'s
  hypothesis), and §9.3's order is left with **one** dispatchable candidate —
  **(ZH-2)** in its stratified reading only, since (ZH-5) is a design note and
  (ZH-6) is write-up material.

### Standing notation

`G`, the split chain `b–v–a–c`, `G′ = G^{ab}_v`, `s₀`, `U`, `R_a`, `r`,
`r̃ = ★r`, `C(M)` and the meet line `M` are §(K-tight) *Step 2*'s, unchanged;
`P := Q(r̃) = ⟨r̃, r̃⟩` is §(K-pitch) *Step 0*'s pitch polynomial and
`Q(x) = ⟨x, ★x⟩` its quadric; `V_bc`, `T`, `z`, `α(a)`, `Λ²π̂` are
§(K-pitch)/§(K-pure)'s. `target(G) = 6(|V|−1) − def(G)`, and on the tight class
`def(G) = 0` and `5|E| = 6(|V|−1) = target(G)`. New here:

- `Y` — the pencil chart of the **seed** graph `G′` (irreducible, §(K-chart));
  `Y⁰ ⊆ Y` its target-rank open locus, which is the kernel's own antecedent.
- `X_y` — route A's placement sweep for `pt(v)` at the seed `y`, the panel
  `Π̂(b)` at a hub `b` (2-dimensional, and it **moves with `y`**). `B` — the
  total space of that sweep over `Y⁰`, a rank-2 affine bundle with
  `dim B = dim Y⁰ + 2`; this is the base variety on which §(K-tight)'s
  criterion lives, and *not* a product. §(K-tight) *Step 1*'s **joint sweep**
  only enlarges the fibre, which can only help properness, so nothing below is
  an artifact of taking it small. `{y} × X` below abbreviates the fibre over
  `y`.
- `𝒞(G) ⊆ B × (Λ²K⁴)^{V(G)}` — the **universal infinitesimal-motion cone**
  `{(y, x, m) : m(u) − m(w) ∈ ⟨C_{uw}⟩ for every uw ∈ E(G)}`, a cone in `m`.
- `Z := B × {0} ⊆ 𝒞(G)` — its **zero section**. `Z ≅ B`, irreducible.
- `B_k := {(y,x) ∈ B : dim ker R(G; y, x) = 6 + k}` — the corank strata of the
  base, `k ≥ 0`; `D_1 := ⋃_{k ≥ 1} B_k = {rank R(G) < target(G)}`, the **first
  degeneracy locus**, closed in `B`.

### Step JC1 — the object, which of its two presentations the criterion applies to, and the Jacobian identity

The candidate's mechanism is the Jacobian criterion applied along `Z`. Before
applying it one has to know what the equations of `𝒞(G)` *are*, and the harness
has two presentations that are **not** interchangeable for this purpose.

> **(JC-1)** *(proven; symbolic identities in `ℚ[pts, m, ω]`, plus 218
> exhibited zero-section points; `--sym`, `--tan`)* Three parts.
>
> **(a) The harness's 5-rows-per-hinge model is not polynomial in the chart
> coordinates.** `repin.rank_at_V` and `battain.rows_from_W` build five rows
> per hinge as a **basis** of `C_e^{⊥_E}` via `exactcore.perp_basis`, which is
> an `rref` — so the row entries are non-canonical rational functions of the
> chart coordinates, and a "Jacobian" of them is basis-dependent. The
> **polynomial** presentation of the same cone is the augmented system
>
> > `F_{e,k}(y, m, ω) := m(u)_k − m(w)_k − ω_e · C_e(y)_k = 0`,
> > `e = uw ∈ E(G)`, `k = 0..5`,
>
> i.e. `dominance.motion_system` — `6|E|` equations, **polynomial** in `y` and
> **exactly linear** in the fibre variables `(m, ω)`, verified as such
> equation-by-equation. Since `C_e ≠ 0` (asserted at every probe), `ω` is
> determined by `m` and the two models have the **same fibre dimension**:
> asserted, not assumed, at **218/218** probed points.
>
> **(b) Along the zero section the Jacobian is `[ 0 | A(y) ]`.** At `(y, 0, 0)`
> every `∂F/∂y` carries a factor `ω_e` and therefore vanishes: **108/108**
> entries identically zero in `ℚ[pts]` on the carrier probed, and the fibre
> block equals `motion_system`'s own matrix `A(y)` **entry-for-entry**
> (240/240), the two sides built independently — one by differentiating the
> equations, one by constructing the system. Hence
>
> > **`rank Jac F(y, 0, 0) = rank A(y)`.**
>
> **(c) What the criterion therefore gives, and what it does not.** Because
> `#equations = 6|E| = 6|V| + |E| − 6 = ` the expected codimension exactly on
> the tight class (*Step JC3*), the Jacobian criterion yields, at a
> zero-section point `p = (y,x,0)`:
>
> > `p ∉ D_1  ⟹  p` is a smooth point of `𝒞(G)`, which is there a complete
> > intersection of the expected codimension — **unconditionally**, so
> > `Sing 𝒞(G) ∩ Z ⊆ D_1` always;
> >
> > `p ∈ D_1  ⟹  dim T_p 𝒞(G) = dim T_{(y,x)} B + (6 + k) > dim B + 6`, so `p`
> > is singular **provided** `𝒞(G)` has the expected dimension at `p`.
>
> The reverse inclusion `D_1 ∩ Z ⊆ Sing 𝒞(G) ∩ Z` — the half the route needs —
> is therefore **conditional on the expected-dimension hypothesis**, which
> *Step JC2* identifies.

*Measured, at the cap disclosed in the driver docstring (`--tan`).* At `P21`
(§(K-flank) *Step F5(d)*'s bed, re-derived and asserted against that step's
recorded `(30, 5, 5)` over seeds 101..140 before use) and at three named tight
**class** habitats from `dominance.HABITATS` — θ(3,3,6), NT21c3, θ(3,4,5) —
**218** zero-section points: **112 smooth** (fibre dimension `6`, the expected
value) and **106 singular** (excess `≥ 1`), with `dim T_yY` constant at every
seed of a carrier (`58` at `P21` and NT21c3, `30` at both thetas). Every probe
asserts `smooth ⟺ rank = target` and asserts the two models' agreement, so a
single exception fails the run. **The five forced-failure `P21` seeds are
singular at every probed placement**, as §(K-tight) *Step 2.3* proves they must
be. The `plane_basis` precedent is reported, never assumed: `repin.star_generic`
rejects **5/5** forced-failure seeds and accepts **26/30** escaping ones —
independently reproducing §(K-shear) **(SH-3)**'s figures — and because the gate
is **not** used for acceptance here, the 112/106 split is a tally of
**exhibited** points and **not a rate**.

**One asymmetry worth recording, because it is the count again.** On the tight
class the `G`-side equation count matches the expected codimension exactly
(`5|E| = 6(|V|−1)` in the 5-row model, `6|E| = 6|V| + |E| − 6` in the augmented
one; both asserted at eight shapes, *Step JC3*). The **seed** graph's does not:
`|E′| = |E| − 1` and `|V′| = |V| − 1` give
`5|E′| = 6(|V′| − 1) + 1`, one row too many — which is `index(G′) = 1`, i.e.
exactly the **one-dimensional self-stress space** a target-rank `G′` seed
carries (`repin.seed_probe`'s `corank Gp`, measured `1` at every bed seed), and
it is that stress whose `ab`-load image is §(K-tight) *Step 2*'s `R_a`. So
`𝒞(G′)` is cut by
`codim + 1` equations and is **never** a complete intersection of the expected
codimension, whatever else is true; the tight class is exactly and only where
the phrase *"local complete intersection of the expected codimension"* is
arithmetically available at all.

### Step JC2 — properness, restated exactly; and the equivalence that kills the route

> **(JC-2)** *(proven-informally; a stratification dimension count, and the
> load-bearing step of this section)* Fix a class habitat `G` and a split.
>
> **(a) The candidate's target sentence, made precise.** *"Escape fails only
> on a proper closed subset"* is a statement about `Y⁰`, namely about
> `Fail := {y ∈ Y⁰ : {y} × X ⊆ D_1}`. Its **closed** half is free: `D_1` is
> closed, and the affine-bundle projection `B → Y⁰` is flat of finite type over
> a Noetherian base, hence an **open** map, so `Y⁰ ∖ Fail` is the image of the
> open `B ∖ D_1` and `Fail` is closed. (Nothing below leans on this; the
> equivalence in the next display is set-theoretic.) Its **proper** half is
>
> > `Fail ≠ Y⁰  ⟺  D_1 ≠ B  ⟺  B_0 ≠ ∅  ⟺  some (y,x) attains target(G)`,
>
> and with `Y` irreducible (§(K-chart)) this is equivalent to `B_0` **dense**.
> So (ZH-4)'s slogan bundles a free half with the entire difficulty, and the
> difficulty is unchanged by the bundling.
>
> **(b) The stratification identity.** Over `B_k` the fibre of `𝒞(G)` is a
> vector space of dimension `6 + k`, so `𝒞(G)|_{B_k}` has dimension
> `dim B_k + 6 + k`, and since the `B_k` partition `B`,
>
> > **`dim 𝒞(G) = max_{k ≥ 0} ( dim B_k + 6 + k )`** (empty strata omitted).
>
> `B` is irreducible — `Y` is (§(K-chart)), `Y⁰` is open in it, and `B` is an
> affine bundle over `Y⁰` — so exactly one stratum is dense. Therefore
>
> > `𝒞(G)` has the **expected** dimension `dim B + 6` ⟺ `B_0 ≠ ∅` **and**
> > `codim_B B_k ≥ k` for every `k ≥ 1`.
>
> (The `B_0 ≠ ∅` clause is not redundant: if `B_0 = ∅` then some `B_k`,
> `k ≥ 1`, is dense, and that stratum alone already gives
> `dim 𝒞(G) = dim B + 6 + k > dim B + 6`.) Since on the tight class
> `#equations = ` that expected codimension (*Step JC1*), this is also exactly
> *"`𝒞(G)` is a local complete intersection of the expected codimension"*, hence
> also exactly the hypothesis under which Eagon–Northcott perfection /
> Hochster–Eagon Cohen–Macaulayness would apply.
>
> **(c) The circularity.** The **weakest clause** of that condition is the
> first one, `B_0 ≠ ∅` — which by (a) **is** properness, and which the `k = 1`
> clause `codim_B B_1 ≥ 1` also forces given irreducibility. So
>
> > **the route's hypothesis contains its conclusion as the weakest of its
> > instances.** "LCI of the expected codimension ⟹ the degeneracy locus is
> > proper" is a true implication and a **tautology with extra steps**: no
> > Jacobian rank is computed on the way, and nothing has been reduced.
>
> **(d) Consequence for the shelf.** The condition as a whole — `B_0 ≠ ∅` and
> `codim_B B_k ≥ k` for all `k ≥ 1` — is, in words, *"a stratum of codimension `c` has generic self-stress dimension
> `≤ c`"* — which **is** (ZH-3). So **(ZH-4)'s hypothesis is (ZH-3)**, and
> ZSHEAR's *"circular as posed"* verdict on (ZH-3) applies to (ZH-4) unchanged.
> The shelf's two "concrete" candidates were one candidate.

**Why the induction hypothesis does not rescue (c).** The kernel's antecedent
is target-rank genericity for **`G′`**, i.e. `Y⁰` dense in `Y`. That is the
`B_0 ≠ ∅` clause of the same condition for the cone of `G′` — a **different**
graph. Nothing in the scheme-theoretic package propagates an LCI statement
across the vertex insertion: *Step JC5*(a) shows the insertion is cut by 10
equations on 6 new columns and that whether they cut the expected amount is
§(K-tight) *Step 2*'s corank identity, i.e. the escape itself. So the IH gives
the hypothesis for the wrong cone and the machinery gives no transport.

### Step JC3 — what the classical package actually supplies, and which way its inequalities point

The route needs a **lower** bound on the codimension of a degeneracy locus
(`height(I_t) ≥ 1`). The classical literature on heights of ideals of minors is
a literature of **upper** bounds, and says so in as many words.

**References, verified this pass against primary/publisher metadata (no section
pointer is asserted).**

- J. A. Eagon and D. G. Northcott, *Ideals defined by matrices and a certain
  complex associated with them*, Proc. Roy. Soc. London Ser. A **269** (1962),
  no. 1337, 188–204, DOI `10.1098/rspa.1962.0170`.
- W. Bruns, *The Eisenbud–Evans Principal Ideal Theorem and determinantal
  ideals*, Proc. Amer. Math. Soc. **83** (1981), 19–24.
- D. Eisenbud, C. Huneke and B. Ulrich, *Heights of ideals of minors*, Amer. J.
  Math. **126** (2004), 417–438 (preprint arXiv:math/0209184) — whose
  introduction states the direction explicitly: *"A well-known theorem of Eagon
  and Northcott [EN] gives an **upper bound** for the codimension of the locus
  where `ϕ` has rank `≤ s`"*, and whose own Theorems A/B/C are upper bounds too.
- M. Hochster and J. A. Eagon, *Cohen–Macaulay rings, invariant theory, and the
  generic perfection of determinantal loci*, Amer. J. Math. **93** (1971),
  1020–1058 — the Cohen–Macaulayness half, whose hypothesis is **genericity of
  the entries**.

> **(JC-3)** *(proven-informally, with the numbers measured; `--codim`)*
> Write `ϕ = R(G)` over the coordinate ring of `B`, of size `p × q = 5|E| ×
> 6|V|`, with generic rank `r` and `t = target(G)`; the locus of interest is
> `D_1 = V(I_t)`. Three statements.
>
> **(a) Direction.** Instantiated at `i = t` and `r = t`, Eagon–Northcott gives
> `height(I_t) ≤ (r − i + 1)(max(p,q) − i + 1)` and Bruns gives
> `height(I_t) ≤ (r − i + 1)(p + q − r − i + 1)`; **both evaluate to
> `q − t + 1 = 6|V| − 6(|V|−1) + 1 = 7`** on the tight class, and the
> Eisenbud–Huneke–Ulrich sharpening is weaker here (`7 + t − 1`). Krull's
> height theorem likewise bounds `codim 𝒞(G) ≤ #equations`, i.e.
> `dim 𝒞(G) ≥ dim B + 6` — again the free direction. **Every available
> inequality bounds the locus from above and the cone from below; properness
> needs the opposite of both.**
>
> **(b) Input.** Each of those bounds takes the **generic rank `r`** as a
> hypothesis. To invoke them at `i = t` at all one must already know `r = t` —
> which is properness. So the classical package cannot even be *stated* at our
> locus without the conclusion.
>
> **(c) The number is a constant, so §4.6's filter fires too.** Measured at
> all seven `dominance.HABITATS` plus `P21`: `(E–N, Bruns) = (7, 7)` at
> **8/8** shapes, with `5|E| = 6(|V|−1) = target` and
> `6|E| = 6|V| + |E| − 6` asserted at each. The bound is `6 + 1` — the number
> of trivial motions plus one — **independent of the graph**. By
> `notes/Pencil-strategy.md` §4.6's growing-ground-set filter a
> fixed-dimensional quantity cannot see the graph, so this one cannot
> distinguish one class member from another, let alone certify one.

**Exhibition 1 — inside the arc's own tight bed.** At `P21`, over the
forced-failure seed `101` the best route-A rank over 4 probed placements is
`119 = target − 1`, and §(K-tight) *Step 2.3*'s calculus **proves** failure at
every placement there (`dim R_a = 0`), so the generic rank on the sub-locus
`{101} × X` is `119`; over the escaping seed `102` a probed placement attains
`120 = target`. On the first sub-locus `I_t = 0` identically, `height(I_t) = 0`,
**properness fails**, and the Eagon–Northcott bound reads `(r − i + 1)(…) = 0`
and is **satisfied**. On the whole of `B`, *if* `r = t`, it reads `7` and is
also satisfied. Same graph, same matrix shape; the only thing that changed is
`r`, the bound's own input.

**Exhibition 2 — the same, with the two strata global.** The necklace `Nk₄` of
§(K-bare-ext) *Step BE13* (`|V| = 16`, `|E| = 24`, `def₃ = 0`, `def₂ = 1`,
`target = 90`). It is **over-braced** (`5|E| = 120 > 6(|V|−1) = 90`) and
therefore **not** a class shape; it is used only because it is the arc's one
carrier with two *legal* pencil strata of different generic rank. On the
global-cone stratum the exact rank is **`89 = 6(|V|−1) − def₂`** — (BE-13)'s
law, independently recomputed here — and on the local-cone stratum
`rank_modp = 90 = target`; since `rank_modp` is a **lower** bound for the
rational rank and the partition bound of §(K-bare-ext) *Step BE12* is a
universal **upper** bound of `target`, the generic rank there is exactly `90`.
Eagon–Northcott reads `0` on the first and `31` on the second (here
`max(p,q) = 5|E| = 120`) and is satisfied in both. **The classical package
cannot see the difference.**

### Step JC4 — the blind spot: fibre-degree ≥ 2, which is the pure-condition half

(ZH-4)'s pitch was that this is *"a scheme-theoretic upgrade of exactly the
White–Whiteley pure-condition material §(K-pure) works by hand"*. The upgrade
cannot reach that material, and the reason is one line of calculus.

> **(JC-4)** *(proven; an identity in `ℚ[y, t]`, no sampling; `--sym`)* Let a
> cone be cut by equations that include one of degree `≥ 2` in the **fibre**
> variables, with arbitrary polynomial dependence on the base. Then **every**
> partial derivative of that equation — with respect to a fibre variable or a
> base variable — vanishes identically on the zero section. Verified as an
> identity for
>
> - a **general** fibre-quadratic `Σ_{i,j} y_{ij} t_i t_j` with `36` free
>   base-dependent coefficients, and
> - the arc's **own** pitch quadric `Q(t) = ⟨t, ★t⟩` (§(K-pitch) *Step 0*, in
>   the harness's `repin.hodge_star` convention),
>
> **84/84** partials, all identically zero. Consequently such a cone is
> **singular along its entire zero section, at every base point**, and the
> zero-section Jacobian criterion is **vacuous** on it: it assigns the same
> data — nothing — to a pitched and an unpitched configuration alike.

**Why that is fatal to the advertised leverage, and not merely a technicality.**
§(K-pure) *Step P5* **(PC5)** already records the invariant mismatch at the
level of the polynomial: the pure condition is a **rank** certificate (WW87
Cor. 2.7) and the arc's obstruction at the flanks is **(W4)**, which by (PC-Z)
asks whether a distinguished kernel vector lies **off a quadric** — *"the Klein
quadric is invisible to the matroid"*. (JC-4) is that same mismatch one level
up: the zero-section Jacobian sees exactly the **fibre-linear** part of the
equations, i.e. exactly a rank condition, and is identically blind to the
fibre-quadratic part, i.e. exactly the quadric. So the scheme-theoretic
repackaging is **tautologous where it applies** (*Step JC2*) and **vacuous
where the arc needs help** (here). There is no third region.

**The residue that would have to be reached instead, named for completeness and
not pursued.** The first-order datum that actually governs whether `D_1` is
smooth of the expected codimension at a corank-jump point `(y,x)` is not the
zero-section Jacobian but the classical determinantal obstruction map
`Ψ : T_{(y,x)}B → Hom(ker R, coker R)`, `δ ↦ [m ↦ (∂_δ R) m]`, whose
surjectivity is transversality. The arc has already computed an object of
exactly this shape: §(K-dom) measures the differential of `y ↦ V_bc(y)` into
`T_{V}Gr(3,6) = Hom(V_bc, K⁶/V_bc)` — the same `Hom(kernel, cokernel)` shape,
taken against the bad locus that actually matters — and its recorded verdict is
*"rank 9 at every class habitat probed"* together with *"class uniformity is
untouched: 'rank 9 at every class shape' is one determinantal condition per
(shape, split), the same per-shape object §(K-pure) P5 identified as the
wall"*, plus the sharp cap `rank dV ≤ min(9, 6k − 14)` that gives `4` at
`k = 3`. **So the arc has already cashed the "Jacobian-rank computation instead
of a witness hunt" promise once, in the form best adapted to its own bad locus,
and what it bought was a per-shape condition.** (ZH-4) offers the same trade in
a worse coordinate system.

### Step JC5 — the verdict, the faithfulness of the re-encoding, and the general form

> **(JC-5)** *(proven-informally; an argument plus the exhibited conic)* The
> cone formulation is a **faithful** re-encoding of §(K-tight), which is
> exactly why it adds nothing.
>
> **(a) The inductive step, in cone language.** Inserting the degree-2 body `v`
> presents `𝒞(G)` inside `𝒞(G−v) × K⁶` cut by the **10** rows of the two new
> hinges `va`, `vb` on the **6** new columns `m(v)`; solvability for `m(v)`
> given `m(a), m(b)` asks that `m(a) − m(b) ∈ ⟨C_{va}⟩ + ⟨C_{vb}⟩`, i.e. **4**
> conditions on the relative twist. That is §(K-tight) *Step 2.1* verbatim —
> "attainment ⟺ the two functionals `u ↦ ⟨u, C(va)⟩`, `u ↦ ⟨u, C(vb)⟩` are
> linearly independent on `U`", with `dim U = dim R_a + 1` — and the
> "expected drop" question is the escape question. The translation is exact and
> the difficulty is conserved.
>
> **(b) The zero-section singular locus is an object the arc already owns in
> closed form.** Over an **escaping** seed, `Sing 𝒞(G) ∩ Z` restricted to the
> fibre `{y} × X` is §(K-tight) *Step 2.4*'s **degenerate conic
> `det = ℓ_{line(ab)} · ℓ_{P′}`** — the deleted hinge's own line union the
> second failure line. Both factors are exhibited: the `line(ab)` placement and
> `repin.second_line_check`'s `P′` point both give fibre dimension `7` (excess
> `1`, `rank = target − 1`) at every seed probed, at `P21` and at three named
> class habitats. Note the `line(ab)` factor is **chart-illegal** for `G`
> — read off the **definition body**, not a docstring: `Motive.lean:110`'s
> fourth conjunct is
> `∀ v ∈ V(G), ¬ G.PencilHub v → LinearIndepOn K point (G.closedNbhd v)`, and at
> a degree-2 non-hub `v` with neighbours `a, b` the closed neighbourhood is the
> 3-set `{v, a, b}`, so linear independence of `point` on it is exactly
> "`pt v, pt a, pt b` not collinear" — so the carrier's own nondegeneracy
> conjunct
> excises one component of the singular locus and `P′` is what genuinely
> survives — which is *Step 2.4*'s point, recovered here under a new name.

> **(JC-6)** *(proven-informally; the general form, and the one to attack)* A
> conservation law for the technique, and then its two corollaries.
>
> **(a) The law.** The determinantal / scheme-theoretic package —
> Eagon–Northcott's complex and perfection, Hochster–Eagon's
> Cohen–Macaulayness, equidimensionality, the Jacobian criterion, local
> complete intersections — is a machine for converting the hypothesis *"the
> locus has its expected codimension"* into structural conclusions. **It
> contains no theorem producing that hypothesis over a non-generic base**: its
> unconditional statements are codimension **upper** bounds (*Step JC3*), and
> its structural statements assume either genericity of the entries or the
> expected codimension itself. On the tight class, *properness of the escape
> failure locus is the weakest instance of the expected-codimension
> hypothesis* (*Step JC2*). Therefore **no repackaging of the arc's rank
> question in this language can supply properness.**
>
> **(b) The strongest repair, and why it fails for a reason the arc has already
> exhibited.** The one place where expected codimension IS available for free is
> the **ambient** body–hinge realization space `Ω` (no pencil condition): Tay's
> theorem gives generic rank `= 6(|V|−1) − def(G)`, so at `def(G) = 0` the
> ambient cone `𝒞_amb` genuinely **is** an LCI of the expected codimension and
> `Sing 𝒞_amb ∩ Z_amb = D_1^{amb}` is a proper closed subset of `Ω`. The repair
> is then: restrict to the pencil sub-base `B ⊂ Ω`. It supplies nothing, because
> intersecting a proper closed `D_1^{amb} ⊊ Ω` with a subvariety `B` says
> **nothing** about whether `B ⊆ D_1^{amb}` — and that is not a worry but an
> exhibited phenomenon: §(K-pure) *Step P6* **(PC6)** shows at `P21` that a
> constrained subfamily can be **dependent at every point** while the ambient
> system with the same multiplicities is independent (rank `15/15`) and the (C6)
> packing holds. It is also `notes/Pencil-strategy.md` §2.4's wall in one line:
> *"`V_bc` is not a generic point … and we have no description of that image."*
> So the repair is the descent problem, which is the arc's open problem.
>
> **(c) Why "no theorem transfers" was right but not the binding objection.**
> §9.2 already warned that the source's carrier is bar–joint `(2,2)`-sparse and
> ours is body–hinge at multiplicity 5. That warning holds, and §(K-pure)
> *Step P6* **(PC6)** independently exhibits, at `P21`, the *mechanism* by which
> an ambient-generic non-vanishing theorem fails to descend to a constrained
> subfamily. But (a) is stronger and prior: an analogue **for our carrier**
> would not be an input to the phase target, it would **be** it. So the death
> survives granting the source's Theorem 4.2 in full — the provenance bar is
> not what kills this route.
>
> **(d) Relocation, again, and worse.** §4.6 (R1)'s pattern — a candidate
> relocates the crux rather than crossing it — fires for the fifth time (C1 to
> `rank dV = 9`; `∀λ` to "`λ ≠ p⁺` is realizable"; §(K-out) (OC-8) to
> chart-to-frame dominance; (ZH-1) backwards onto avoidance). This is the
> second **backwards** relocation after ZSHEAR and the first onto the
> **conclusion itself**: (ZH-1) relocated onto a step the arc already had,
> (ZH-4) relocates onto the step the arc is trying to prove.

**The (SH-6) dichotomy check, run early as the spec required, and reported
either way.** §(K-shear) **(SH-6)**(a) is a statement about a **group** `Γ`
under which the criterion is equivariant. The Jacobian route posits no group,
and smoothness is not a symmetry claim, so **(ZH-4) is not an instance of
(SH-6)(a)** — confirmed rather than assumed. It **is** an instance of
**(SH-6)(b)**, the relocation reading, in its most degenerate form: (SH-6)(b)
observes that *"avoid finitely many proper subvarieties over an infinite field"*
is free once `P ≢ 0` is known and that the arc's gap is **properness**; (ZH-4)
attacks properness and lands on properness. (JC-6)(d) records it.

**The `PGL(4)`-invariance residue binds, and it decides the symbolic-leaf
question.** §(K-shear)'s residue is that `Q(r̃) ≠ 0` is `PGL(4)`-invariant, so
**no gauge-fixing or frame normalization can ever supply it**. The only
symbolic slice `notes/Pencil-strategy.md` §5.3 measures as *feasible* is the
**gauge-fixed local frame** (`m2/lambda1.m2` block (M4); the ungauged
28-coordinate degree-52 expansion is killed at 600 s). So a Macaulay2 leaf
aimed at the pitch-side variant of this route is barred **twice over** — by
§5.3's measured boundary if it is ungauged, and by the residue if it is
gauged, since the gauged computation is provably incapable of producing the
non-vanishing. **No `m2/zjacob.m2` is opened, and the reason is not budget.**

**Two coordinator-predicted deaths, both refuted as diagnoses.** The dispatch
named the two likeliest deaths to check first: *(i)* the cone may **not** be an
LCI of the expected codimension in our carrier, and *(ii)* the identification
may need a hypothesis the pencil stratum **violates**. Neither is what
happened. For *(i)*: whether the cone is such an LCI is not a fact to be
checked — being one **is** the phase target (*Step JC2*), so the prediction
mis-locates a conclusion as a hypothesis. For *(ii)*: the identification needs
the expected-dimension hypothesis, which the pencil stratum does **not**
violate — it simply *is* the conclusion. The actual death is an **equivalence**,
not an obstruction, which is a different and stronger shape than either
prediction.

### Confidence verdict, per claim

| claim | verdict | instrument |
|---|---|---|
| **(JC-1)**(a) the 5-row model is non-polynomial; the augmented system is the polynomial presentation, and the two agree on fibre dimension | **proven** (read off `exactcore.perp_basis`) / agreement **measured, asserted** 218/218 | `--sym`, `--tan` |
| **(JC-1)**(b) `rank Jac(y,0,0) = rank A(y)` along the zero section | **proven** — identities in `ℚ[pts, m, ω]`, 108/108 vanishing `y`-entries and 240/240 fibre-block entries against an independent construction | `--sym` |
| **(JC-1)**(c) `Sing 𝒞 ∩ Z ⊆ D_1` unconditional; equality conditional on expected dimension | **proven-informally** (the Jacobian criterion, both directions written out) | — |
| **(JC-2)** the stratification identity, and LCI-of-expected-codimension ⟺ `codim B_k ≥ k`, whose `k=1` instance IS properness | **proven-informally** — a dimension count; the load-bearing step, and the one to attack | — |
| **(JC-2)**(d) (ZH-4)'s hypothesis is (ZH-3) | **proven-informally** (a restatement, once (b) is granted) | — |
| **(JC-3)**(a)/(b) every classical bound is an upper bound and takes `r` as input | **classical**, cited and verified against the Eisenbud–Huneke–Ulrich introduction | — |
| **(JC-3)**(c) the bound is the constant `7` across the class | **measured, asserted** at 8/8 shapes, with the two count coincidences | `--codim` |
| **(JC-3)** exhibitions 1 and 2 | **exhibited** — two sub-loci of one chart at `P21` (leaning on *Step 2.3* for the failing one, stated as such), and two global strata at `Nk₄` | `--codim` |
| **(JC-4)** the criterion is identically blind to fibre-degree ≥ 2 | **proven** — 84/84 partials identically zero in `ℚ[y,t]`, general quadratic **and** the arc's own `Q` | `--sym` |
| **(JC-5)**(a) the insertion in cone language is *Step 2.1* verbatim | **proven-informally** (an argument) | — |
| **(JC-5)**(b) the zero-section singular locus over an escaping seed is *Step 2.4*'s conic | **exhibited** at 4 carriers, both factors, every probe asserted | `--tan` |
| **(JC-6)** the conservation law, the ambient-Tay repair and its (PC6) answer, the "no theorem transfers" correction, and relocation #5 | **proven-informally** — arguments, and the ones a successor should attack | — |
| **(ZH-4) as a route to properness** | **REFUTED**, with the exact reason | `--sym` + `--codim` (+ `--tan` for the exhibitions) |

### What would change this

- **(JC-1)**(b) would fall only to an error in the harness's own model, which
  `--sym` pins by comparing two independent constructions of `A(y)` on the same
  symbolic points; a divergence between `dominance.motion_system` and the Lean
  `BodyHingeFramework.rigidityRows` would move the **dictionary** (§(K-tight)'s
  already-recorded model-to-Lean item), not the mathematics.
- **(JC-2)** would fall if some component of `𝒞(G)` were **not** a vector
  bundle over a corank stratum — i.e. if the fibre over a base point were not
  the kernel of `R` at that point. It is, by construction. The other way to
  attack it is to deny (a)'s reduction of *"escape fails only on a proper closed
  subset"* to `B_0 ≠ ∅`: that would need an escape route not of the form
  *"some placement attains target rank"*, which §(K-tight) *Step 1* forecloses
  for A and B, and *Step 1*'s joint sweep only enlarges `X`.
- **(JC-3)** would change if a codimension **lower** bound for degeneracy loci
  of a *specific* non-generic matrix of forms existed in the classical
  literature. The Eisenbud–Huneke–Ulrich introduction is explicit that the
  subject is upper bounds; a genuine lower-bound theorem, with hypotheses our
  carrier satisfies, would reopen the route — and would be a much stronger
  thing to have than the escape.
- **(JC-4)** would change if the escape criterion could be re-presented with
  the pitch as a **fibre-linear** condition on some auxiliary bundle. That is
  what (PC-Z) already does for `V_bc` (the two Schubert `σ₁` conditions), and
  `notes/Pencil-strategy.md` §2.4 records the result: the bad locus becomes a
  hypersurface in `Gr(3,6)` and the whole difficulty moves to describing the
  image of `φ_G`. So the re-presentation exists and the difficulty is
  conserved — which is (JC-6)(a) again.
- **(JC-5)**(b) would change if the two-line failure conic were not the whole
  zero-section singular locus in a fibre; the driver exhibits both factors but
  does not prove completeness — §(K-tight) *Step 2.4* does, and this section
  does not re-derive it.
- **(JC-6)** would be evaded only by a theorem producing expected codimension
  from a **combinatorial** hypothesis on the *constrained* pencil chart.
  Tay's theorem is exactly such a theorem for the **ambient** body–hinge
  realization space, and §(K-pure) *Step P6* exhibits at `P21` why an
  ambient-generic theorem does not descend. A pencil-chart analogue is the
  phase target.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/zjacob.py --sym        #   0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zjacob.py --tan        # 233.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zjacob.py --codim      #  43.4 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/zjacob.py --validate   # 236.7 s
#   validate legs: --sym 0.0 / --tan 234.3 / --codim 2.4
```

(Wall-clock seconds are the driver's own self-timing prints — the one
documented exception to byte-identical output, `notes/scripts/README.md`. The
`--codim` leg is 43.4 s standalone and 2.3 s inside `--validate` because the
`P21` bed is built once per process and reused.)

`--validate` **fits a 600 s foreground budget** (measured 236.7 s). Every
headline figure above is an `assert` inside the mode named in the table, so the
verification bar is: **the modes exit 0.** `--sym` is free of sampling
altogether (identities in polynomial rings, two independent constructions
compared); `--tan` and `--codim` are equalities asserted at every probed point
of a disclosed, seeded, fully-enumerated bed, and the one composite genericity
gate is **reported rather than used** (so the 112/106 smooth/singular split is a
tally of exhibited points, never a rate — README §4 convention 1). Determinism
checked: `--tan`, `--codim` and `--validate` each re-run byte-identical modulo
their own timing lines.

**F11 mapping** (each headline sentence to the mode that tests *that*
sentence). *"The zero-section Jacobian computes `rank A(y)` and nothing else"* →
`--sym`(i)–(iii), an identity in `ℚ[pts, m, ω]` with the fibre block compared
against `dominance.motion_system` built independently. *"The cone is a local
complete intersection of the expected codimension"* is a **structural** claim
and is **derived**, not measured: *Step JC2*(b)'s stratification identity turns
it into `codim B_k ≥ k`, and the driver's role is only to assert the two count
coincidences that make the phrase available at all (`5|E| = 6(|V|−1)` and
`6|E| = 6|V| + |E| − 6`, 8/8 shapes, `--codim`) — **it is nowhere claimed to
hold**. *"The singular locus along the zero section is exactly the first
degeneracy locus"* is the other structural claim: `--sym` proves the Jacobian
identity behind it, `--tan` exhibits both inclusions pointwise at 218 points,
and *Step JC1*(c) states explicitly that the reverse inclusion is
**conditional** — the claim is never stated more strongly than that. *"The
classical bound is the constant 7 and takes `r` as its input"* → `--codim`,
computed from the shapes and asserted at 8/8, with the input-dependence
exhibited twice. *"The criterion is blind to the fibre-quadratic part"* → an
identity, `--sym`, for a general quadratic and for `Q`. *"The zero-section
singular locus over an escaping seed is *Step 2.4*'s conic"* → `--tan`, both
factors at four carriers.

---

## Riders

**Cap disclosure.** `--tan`: the `P21` bed is seeds 101..140 (the range
§(K-flank) *Step F5(d)* used), all 35 valid seeds, both strata, none skipped, 3
route-A placements plus `line(ab)` plus `P′` where available; the three class
habitats get 4 seeds each (seeds 400+, first four valid) with 2 route-A
placements plus the two named points. `--codim`: closed-form integers at 8
shapes; one exact-ℚ rank and up to 8 stratum draws at `Nk₄`. `--sym`: no
sampling. Single randomness literal `RNG_SEED = 20260826`; every RNG seeded.
All exact ℚ; no floating point.

**F25 — verification bar, read off the shipped driver.** Three modes, all run
in the foreground with explicit timeouts, `--validate` inside the 600 s budget,
exact ℚ throughout, the structural mode fully symbolic, the adversarial bed
re-derived and asserted against *Step F5(d)*'s recorded `(30, 5, 5)` before use,
and the `plane_basis` composite gate reported rather than assumed (5/5
forced-failure seeds rejected, 26/30 escaping accepted — independently
reproducing §(K-shear) **(SH-3)**). No scratchpad probe backs any claim in this
section. The driver is untracked at `notes/scripts/w4/zjacob.py` for the
coordinator to gate and commit; **no tracked driver was modified**, so
`git diff --name-only -- '*.py' '*.m2'` is empty and the figures-do-not-move
gate discharges by that check alone (README §"Hard rule — figures do not
move", first bullet).

**Label remainder to return to the tail.** Reserved **(JC-1)–(JC-6)** and
*Steps JC1–JC5*; **all consumed**, none unused. Tag `JC-` was verified 0-hit at
reservation and this section is its only consumer.

## Shelf effect — `notes/Pencil-strategy.md` §9

Proposed edits for the coordinator's landing commit (this dispatch touches no
shared file):

- **§9.2 (ZH-4)** — mark **STRUCK 2026-08-26, direction ZJACOB: REFUTED, and
  the reason is that "LCI of the expected codimension" IS the phase target at
  its weakest instance**, canonical home §(K-jac) *Steps JC1–JC5*, with the
  original pitch preserved as the shelf's own text (the (ZH-1) precedent).
- **§9.2 (ZH-3)** — its *circular as posed* label gains a mechanism: it is
  **(ZH-4)'s hypothesis**, so the two candidates were one.
- **§9.3** — the head advances past (ZH-4). What is left is **(ZH-5)** as a
  design note feeding a fan-out's *selection* (never a result) and **(ZH-2)**
  *in its stratified reading only*; **(ZH-6)** is write-up material. So the
  shelf now carries **exactly one dispatchable candidate**, and it is
  two-for-two: two directions spent, two candidates struck (plus one
  re-explained). The shelf stays **off §8's board**.
- **§7** — three new verified classical references enter the in-use list
  (Eagon–Northcott 1962; Bruns 1981; Eisenbud–Huneke–Ulrich 2004), plus
  Hochster–Eagon 1971 for the Cohen–Macaulay half; **no section pointer is
  asserted for any of them**, per the project's rule.

## TERMINATION check (E1/E2/E3) — reported, never fired

**E1, E2, E3: all NO.**

- **(E1)** no g-flank. This direction touches no colouring, orientation, chunk
  or §(K-grid) ladder object; there is no `D = 0` shape and no binding chunk
  here, so E1 has no subject matter.
- **(E2)** not applicable and not triggered: the orientation theorem is
  untouched and the §(K-grid) ledger is unchanged, with (a′)/(b′)/(d′) and
  (GR-15) exactly as they were. This direction's own target — is (ZH-4)
  alive? — is **settled negative**, and the shelf still names a dispatchable
  successor ((ZH-2), stratified reading), so no no-attack-left condition
  arises. (JC-4)'s residue paragraph additionally points at a *live* object
  (§(K-dom)'s `Hom(kernel, cokernel)` differential) rather than a dead end.
- **(E3)** the phase target is **not** proven. **E3 stays ARMED by GBAL and is
  neither fired nor disarmed.**
