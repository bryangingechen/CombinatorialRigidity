## §(K-bare-ext) — continuation (direction BPROPER): **(PENCIL-SATURATES-CHART)'s PROPERNESS HALF holds at EVERY side, PATH OR NOT — and the argument is SIDE-TOPOLOGY-FREE** — because at a terminal of side-degree `1` the pendant edge carries a **free multiplier**, so `ρ̄_i = ⟨p_x ∧ p_c⟩ + A` with `A = ρ̄(side_i − x; c, y)` a function of the **core points alone**; `Σ_x ⊆ ρ̄_i` at `ρ_i ≤ 5` is then *exactly* `dim(A ∩ Σ_x) = 2` or `Σ_x ⊆ A`, two conditions on **`p_x` against a fixed subspace**, and both cut out a **proper** subvariety of the plane `π_c` that the pencil condition confines `p_x` to — the first because three α-planes over a plane span `Λ²K⁴`, the second by an incidence count on the Klein quadric whose **one** exceptional case `Λ²π_c ⊆ A` is **neutralized by `p_c ∈ π_c` itself**. No `dim⟨L_j⟩` case analysis, no `assert_generic_star`, no path hypothesis — and the **same inclusion survives at `deg_i(x) ≥ 2`**, giving properness whenever `dim A ≤ 4`, measured **91/91**, which is (BE-113)'s price (d), unmeasured until now. **The scope is stated before anything else and never widened below: what is settled is the PROPERNESS half. (PENCIL-SATURATES-CHART) is NOT yet a theorem and half (B)'s item 1 is NOT closed** — the passage from *proper* to *generic* cites (BE-69) rather than re-deriving it for this locus, and (BE-116)'s `p_x`-sweep input is **measured, not proved**. *(Both **DISCHARGED 2026-09-02, direction BOPEN**: (BE-69) is the wrong citation and is not needed ((BE-122)/(BE-123)), the sweep is **proved** from the tower ((BE-124)), and the clause is a **THEOREM** at every side-degree-`1` terminal ((BE-127)).)* **And the direction's adversarial control refutes two landed hunt verdicts**: BSIGMA's planted sampler missed 11 of its own 16 bucket-A topologies for a **sampler** reason — it gave a hub inside the planted plane a *random* flag, forcing that hub's neighbours onto one line and failing a gate — and with the one line repaired the stratum draws at **16/16**, fires at **11** (eight of them **not paths**), and on a full constructed peel in the **generic flag regime** fires at **`ρ₁ = 4`**, which (BE-110)(iv) had recorded as *none found* over 668 rows. The price is **paid down, not up**: `margin ≤ 0` at `Π_x`, `Π_y` and `⟨M⟩` at every exhibited row, so `notes/Phase39.md` item 0(c)'s shortfall is **untouched and still open**; what the non-path rows do break is `U = Λ²K⁴`, because planting off a path costs `a_i ≥ 1` — they are the **first exhibited inhabitants** of (BE-101)(iii)'s live non-attaining block, and the F13 control draws the same graphs freely at `a = (0,0)`, `dim(ρ̄₁ ∩ Σ_x) = 1`, **attaining**

### Standing notation (on top of *Steps BE108–BE112*)

`x, y` the peel's terminal pair; `side_i` one side; `deg_i(v)` the degree of
`v` **inside** `side_i`. Throughout *Steps BE113–BE118*, `x` has
`deg_i(x) = 1` with unique side-`i` neighbour `c`, and

> **`core := side_i − x`** (the side with the pendant terminal **deleted**),
> **`A := ρ̄(core; c, y)`**, **`ℓ := p_x ∧ p_c`**.

`π_v` is `v`'s flag plane — the plane through `closedNbhd(v)`, which the
pencil condition forces to exist at **every** vertex
(`kbare_common.verify_pencil_witness`, read at source this pass: it demands a
common normal for the **closed** star, so `π_c` carries `p_c` *and* every
neighbour of `c`). In particular **`p_x ∈ π_c` and `p_c ∈ π_c` always**, and
that pair of memberships is the whole reason (BE-116) closes. `Σ_p = p ∧ K⁴`
is the α-plane of lines through `p` (`bsatur.sigma_at`; asserted equal to
`bimage.alpha_plane` this pass), `Q` the Klein quadric, `Λ²π` the β-plane of
lines inside `π`. *Bucket A* / *bucket B* are (BE-110)(iv)'s: `deg_i(y) = 1`
and `deg_i(y) ≥ 2`.

### Step BE113 — (BE-114): the pendant reduction, and the exact dichotomy

> **(BE-114)(i)** *(**PROVED**; the reduction, and it is one line of motion
> bookkeeping)* Let `deg_i(x) = 1`. A motion of `side_i` restricts to a
> motion of `core`; conversely every motion `m` of `core` extends, because
> the **only** constraint involving `x` is the single hinge `xc` — read at
> source, `kbare_common.build_rigidity` emits `perp_basis(C_e)` as `+wv` at
> `u` and `−wv` at `w`, i.e. exactly `m(u) − m(w) ∈ ⟨C_e⟩` — so
> `m(x) := m(c) − ω ℓ` is legal for **every** `ω ∈ K`. Writing
> `m(y) − m(x) = (m(y) − m(c)) + ω ℓ`,
>
> **`ρ̄_i = ⟨ℓ⟩ + A`, and `A` is a function of the core points alone — it
> does not involve `p_x`.**
>
> Asserted as an identity of **subspaces** at **327** legal side draws over
> **29** topologies of both buckets, blind (coordinate ranges `{3,5,9}`) and
> planted; and `A` is asserted **unchanged** under **164** legal moves of
> `p_x` inside `π_c` with the core held fixed (`bproper.py reduce`).

> **(BE-114)(ii)** *(**PROVED**; the dichotomy, which is what makes the
> question a question about `p_x`)* `ℓ ∈ Σ_x`, so for any `A`
>
> **`Σ_x ∩ (⟨ℓ⟩ + A) = ⟨ℓ⟩ + (Σ_x ∩ A)`**
>
> — if `s = tℓ + a ∈ Σ_x` with `a ∈ A` then `a = s − tℓ ∈ Σ_x`. Hence
>
> **`dim(ρ̄_i ∩ Σ_x) = dim(A ∩ Σ_x) + [ℓ ∉ A]`,  `ρ_i = dim A + [ℓ ∉ A]`,**
>
> and therefore `Σ_x ⊆ ρ̄_i` **with `ρ_i ≤ 5`** is *exactly*
>
> - **`ℓ ∉ A`:** `dim A ≤ 4` **and** `dim(A ∩ Σ_x) = 2`;
> - **`ℓ ∈ A`:** `dim A ≤ 5` **and** `Σ_x ⊆ A`.
>
> Both identities and the classification are asserted at all 327 rows; every
> row's BAD/GOOD verdict is asserted to agree with the one computed from
> **core data plus `p_x` alone**.

> **(BE-114)(iii)** *(the reading — why this is the right move, stated
> against the predecessor)* (BE-110)(i)'s corank identity
> `dim(ρ̄ ∩ Σ_x) = ρ − dim(ρ̄ ∧ p_x)` is structure-free but **`ρ̄ ∧ p_x`
> still contains `p_x`**, which is why (BE-110)(ii) had to reason about the
> projected pair lines `L_j` and hence about the side's star structure. The
> reduction removes `p_x` from the *subspace* instead of from the *map*: `A`
> is `p_x`-free, so the bad condition becomes a condition on a **point
> against a fixed subspace**, and the side's topology has already been spent.
> **This is why (BE-110)(ii) is a path theorem and (BE-116) is not.**

> **(BE-114)(iv)** *(**PROVED**; the same inclusion at `deg_i(x) ≥ 2`, which
> is (BE-113)'s price (d))* Let `deg_i(x) = k ≥ 2` with side neighbours
> `c₁, …, c_k`. Deleting the edges `xc₂, …, xc_k` only **removes**
> constraints, so `ρ̄_i ⊆ ρ̄_{side_i − {xc₂…xc_k}} = ⟨p_x ∧ p_{c₁}⟩ + A`,
> **with the same core `side_i − x` and the same `p_x`-free `A`**. By (ii)'s
> identity applied to the larger space,
>
> **`Σ_x ⊆ ρ̄_i  ⟹  dim(A ∩ Σ_x) ≥ 2`,**
>
> with **no** hypothesis on `deg_i(x)`. Asserted at **91** rows over **16**
> `deg_i(x) ≥ 2` topologies (`bproper.py degx`). This is strictly weaker
> than (ii) — it loses the `ρ_i ≤ 5` bookkeeping — and (BE-119) says exactly
> what it still buys.

### Step BE114 — (BE-115): the α-plane incidence lemma

> **(BE-115)(i)** *(**PROVED**; clause (a) — `Σ_p ⊆ A` is proper on any
> plane)* Let `π ⊂ P³` be a plane and `p₁, p₂, p₃ ∈ π` independent. In a
> basis `p₁, p₂, p₃, e` of `K⁴`, the three α-planes contain
> `p₁p₂, p₁p₃, p₂p₃, p₁e, p₂e, p₃e`, i.e.
>
> **`Σ_{p₁} + Σ_{p₂} + Σ_{p₃} = Λ²K⁴`.**
>
> So if `Σ_p ⊆ A` for every `p` in a Zariski-dense subset of `π`, then
> `A = Λ²K⁴`. Hence for **every** `A` with `dim A ≤ 5`,
> `{p ∈ π : Σ_p ⊆ A}` is a **proper** subset of `π`; it is closed, being
> `{rank(q̂_p|_A) ≤ dim A − 3}` with `q̂_p(ω) = ω ∧ p` linear in `p`. Asserted
> at 48 independent triples and at every `dim A ≤ 5` draw of
> `bproper.py alpha`.

> **(BE-115)(ii)** *(**PROVED**; clause (b) — the incidence count, with its
> one exception)* Let `dim A ≤ 4` and suppose `dim(A ∩ Σ_p) ≥ 2` for every
> `p` in a dense subset of `π`. Write `S := P(A) ∩ Q`, the variety of
> **lines of `P³` lying in `A`**, and
> `I_π := {(p, ℓ) : p ∈ π ∩ ℓ, ℓ ∈ S}`.
>
> - Fibres of `I_π → π` are `P(A ∩ Σ_p)` (every element of `Σ_p` is
>   decomposable, so `P(A ∩ Σ_p) ⊆ S`), of projective dimension `≥ 1` on a
>   dense set, so `dim I_π ≥ 2 + 1 = 3`.
> - Fibres of `I_π → S` are `ℓ ∩ π`: a **point** when `ℓ ⊄ π`, the line `ℓ`
>   when `ℓ ⊂ π`. So
>   `dim I_π ≤ max(dim S, dim(S ∩ P(Λ²π)) + 1) = max(dim S, dim(A ∩ Λ²π))`.
> - If `Q|_A ≢ 0` then `S` is a hypersurface in `P(A)`, so
>   `dim S = dim A − 2 ≤ 2`.
>
> Then `3 ≤ max(dim A − 2, dim(A ∩ Λ²π))` forces `dim(A ∩ Λ²π) ≥ 3`, i.e.
> **`Λ²π ⊆ A`**. If instead `Q|_A ≡ 0` — possible only at `dim A ≤ 3`, the
> maximal totally singular subspaces of `Q` being the α- and β-planes — then
> `A ⊆ Σ_q` gives `dim(A ∩ Σ_p) ≤ dim(Σ_q ∩ Σ_p) = 1` for `p ≠ q`, and
> `A ⊆ Λ²π′` gives `2` only for `p ∈ π′`, so the locus is proper unless
> `π′ = π` and `A = Λ²π`. **In every case: proper, unless `Λ²π ⊆ A`.** ∎
>
> Asserted at every `dim A ≤ 4` draw off the exception (6 dimensions × 40
> random subspaces × 12 points per plane); the exception is **measure zero**,
> so no random draw lands in it, and it is therefore **built on purpose** in
> (iii) rather than assumed away. `dim(Σ_q ∩ Σ_p) = 1` asserted at 288 pairs.

> **(BE-115)(iii)** *(**PROVED**; the exception is real, and it is
> neutralized by a membership the chart already gives)* `Λ²π ⊆ A` genuinely
> makes **every** `p ∈ π` satisfy `dim(A ∩ Σ_p) ≥ 2` — exhibited at 24
> constructed `A = Λ²π ⊕ ⟨ω⟩`. But **`p, p_c ∈ π ⟹ p ∧ p_c ∈ Λ²π ⊆ A`**, so
> at such an `A` the row falls in (BE-114)(ii)'s **`ℓ ∈ A` branch**, whose
> condition is `Σ_p ⊆ A` — and clause (a) makes *that* proper. Asserted at
> every constructed exception. **This is the exact point at which
> `p_c ∈ π_c` is load-bearing**, and it is the only place any chart fact
> enters (BE-115) at all.

### Step BE115 — (BE-116): properness at every side — PROVEN INSIDE THE FIBRE, one input MEASURED

> **(BE-116)(i)** *(**PROVEN-INFORMALLY inside the `p_x`-fibre; the theorem,
> with its one input named in the same breath**)* Let `H` be a peel with
> terminal pair `x, y`, let `side_i` have `deg_i(x) = 1` with side
> neighbour `c`, and fix any point of `Chart(H)`. Hold `side_i − x` fixed —
> hence `A`, `p_c` and `π_c` — and let `p_x` range over its chart freedom.
> Then
>
> **the bad locus `{Σ_x ⊆ ρ̄_i} ∩ {ρ_i ≤ 5}` meets that fibre in a proper
> closed subvariety.**
>
> *Proof.* By (BE-114)(ii) the bad set is
> `{p_x : dim(A ∩ Σ_{p_x}) = 2, ℓ ∉ A}` ∪ `{p_x : Σ_{p_x} ⊆ A}` with
> `dim A ≤ 5` in the second case, and `A` is fixed. Two cases on the freedom:
>
> - **`deg_i(c) ≥ 3`.** Then `c` has `≥ 2` core neighbours, whose points
>   together with `p_c` already span `π_c` (`assert_generic_star` at `c`
>   forbids collinearity), so `π_c` is core-determined and the pencil
>   condition at `c` confines `p_x` to **`π_c`**. Apply (BE-115) with
>   `π = π_c`. The second set is proper by clause (a). For the first, clause
>   (b) leaves only `Λ²π_c ⊆ A`; but `p_x, p_c ∈ π_c`, so `ℓ ∈ Λ²π_c ⊆ A`
>   and the row is not in the first set at all — it is in the second, which
>   is proper. ∎
> - **`deg_i(c) = 2`.** Then `π_c` is *not* core-determined — it follows
>   `p_x` — and `p_x` ranges over `P³`. Both sets are proper in `P³`: clause
>   (a) as before, and for clause (b) the exceptional `A ⊇ Λ²π′` makes
>   `{dim(A ∩ Σ_p) ≥ 2}` exactly `π′`, itself proper in `P³`. ∎
>
> **The one input, named rather than assumed: the `p_x`-sweep, and it is
> MEASURED.** The proof shows the bad set is proper **inside the fibre**;
> that the fibre is genuinely swept — that `p_x` reaches a Zariski-dense
> subset of `π_c` (resp. of `P³`) **inside `Chart(H)`**, with the core fixed
> — is **not proved here**. It requires re-placing side `2` around the moved
> `p_x`, which is `bsatur.reflag`'s move one variable further along.
> Measured: at **96** planted bad rows over **16** topologies, a 16-point
> sweep of `p_x` over its own freedom contains a good point at **every** row,
> and in fact **0 of ~1 500** swept points are bad (`bproper.py proper`).
> Both the planted `p_x` (asserted to lie in its own fibre and to be bad)
> and the swept ones are legal configurations.

> **(BE-116)(ii)** *(what it delivers, exactly — and it is not the clause)*
> Combined with (BE-14) being **existential** ((BE-16)) and the good locus
> being Zariski-open on the irreducible `Chart(H)` ((BE-69)), (BE-116)(i)
> says the arc's `Π_x`/`Π_y` licence survives at **every** side, path or
> not, wherever (BE-69)'s openness does — so the live-block count stays
> **12** at a generic chart point. ***CORRECTED 2026-09-02 by (BE-122):
> (BE-69)'s openness is about the ATTAINMENT locus and does not transport
> here — and is not needed, (BE-123) replacing it with constructibility on
> an irreducible chart.*** What (BE-112)(iii) could only say at a
> *path* side, it can now say everywhere. **What it does NOT say is that
> (PENCIL-SATURATES-CHART) is a theorem**: that needs the *genericity* half
> as well, and this direction cites (BE-69) for it rather than re-deriving
> it. Half (B)'s **item 1 is NOT closed**.

> **(BE-116)(iii)** *(what it does **not** deliver — stated before the
> board, because the gap is the successor's whole target)* Three things.
> **(a)** The `p_x`-sweep input above is **measured, not proved**. **(b)**
> (BE-69) is **cited, not re-derived** for **this** locus: the passage from
> *proper* to *generic* needs the good locus to be **open**, and `ρ_i` and
> `dim ρ̄_i` are only guaranteed locally constant on the top-rank stratum of
> the chart — the argument runs there and is inherited by density, which is
> exactly the step (BE-69) owns and this direction does not re-open. **(c)**
> `a_i = 0` at a generic configuration — which (BE-120) shows is what
> separates the planted rows from the free ones — is **measured**, not
> proved; it is the max-rank half of the body-hinge count, i.e. a Tay-type
> statement, and this arc does not have it as a theorem.
>
> > **ALL THREE DISCHARGED 2026-09-02, direction BOPEN — and (b)'s premise
> > was wrong.** **(a)** the `p_x`-sweep is **PROVED** from §(K-chart)'s
> > tower: the only equation tying `q_x` to a fixed core is
> > `n_c · (q_x − q_c) = 0` ((BE-124)). **(b)** the passage does **not** need
> > the good locus to be **open** — constructibility on an irreducible chart
> > suffices ((BE-123)) — and (BE-69) is in any case about the **attainment**
> > locus ((BE-122)). **(c)** `a_i = 0` generically **is** (BE-69)(i)'s own
> > open `A_i`, `{a_i = 0} = {rank R_i maximal}` by (BE-22)(ii)'s partition
> > cap, so it is **PROVED** on the induction's own (BE-14) for the side and
> > is **not** a Tay-type obligation ((BE-126)).
>
> > **AND A FOURTH THING, NOT LISTED HERE AND FOUND 2026-09-02 ((BE-125)):
> > THIS STEP PROVES PROPERNESS OF THE WRONG LOCUS — a strictly SMALLER one
> > than the clause is about.** (PENCIL-SATURATES-CHART) is stated at
> > `Π_x = p_x ∧ π_x` (2-dimensional), so its bad locus is
> > `{Π_x ⊆ ρ̄_i, ρ_i ≤ 5}`; what (BE-116)(i) proves proper is
> > `{Σ_x ⊆ ρ̄_i, ρ_i ≤ 5}`, with `Σ_x` **3**-dimensional. The two are
> > **not** equal, and the gap is real: at a **fixed** flag an exhibited `A`
> > makes the `Π_x`-bad set the complement of ONE LINE of the `p_x`-plane —
> > dense — while `Σ_x ⊆ ρ̄_i` holds at a **single point** ((BE-125)(iii)).
> > What closes it is a **second** fibration, not a bigger sweep: rotating
> > `π_x` through the line `p_x ∨ p_c` leaves `ρ̄_i` **constant** and sweeps
> > `Σ_x`, so a bad chart point lying in any **open** set is bad at **every**
> > flag — i.e. lies in this step's locus — **pointwise** ((BE-125)(ii)).
> > **This step is true as stated and is used verbatim**; what was missing is
> > the bridge from its locus to the clause's.

### Step BE116 — (BE-117): the cap was a sampler artefact, and it is repaired

> **(BE-117)(i)** *(**the defect, located at one line of one function**)*
> (BE-109)(iv) disclosed that BSIGMA's planted stratum drew at only **5 of
> 16** bucket-A topologies — all five paths — and concluded that off paths
> the shape was *unmeasured, not excluded*. Read at source, the cause is not
> geometric. `bsigma.sample_side_config(..., plane=, off=)` gives a hub `z`
> a flag `Bp[z] = span([homs[z]] + 2 random)` — a **random** plane through
> `p_z` — and then places `z`'s neighbours in `isect(plane, Bp[z])`. When
> `p_z ∈ plane` that intersection is a **line through `p_z`**, so `z` and
> **all** its neighbours are collinear and `assert_generic_star` rejects the
> draw. Every hub-carrying side therefore failed, by construction of the
> sampler.
>
> **The repair is one line:** give a hub *inside* the planted plane **that
> plane** as its flag (`Bp[z] = plane`). Its neighbours are then free inside
> `π`, non-collinear, and the closed star is coplanar. Everything else —
> including the shape guard and the treatment of the off-plane vertex `off`,
> whose in-plane neighbours **must** lie on the line `π ∩ π_off` (forced by
> the pencil condition at a body off the plane, and *not* a defect) — is
> BSIGMA's, verbatim (`bproper.plant_side`).

> **(BE-117)(ii)** *(**the census**, and the shape is a hub-carrying
> phenomenon)* With that one line changed, over **8** planted draws per
> topology:
>
> | bucket | topologies | drawable | fires | of which non-path |
> |---|---|---|---|---|
> | A (`deg_i(y) = 1`) | 16 | **16** (BSIGMA: 5) | **11** | **8** |
> | B (`deg_i(y) ≥ 2`) | 13 | 10 | 5 | 5 |
>
> The eight non-path bucket-A hits, by name: `2 pendants + cycle(8) at
> distance 4` / `at distance 3`, `2 pendants + cycle(10) at distance 5`,
> `2 pendants + theta(3,4,4)` / `(4,4,4)` / `(3,4,5)`, `2 pendants + K4
> subdivided ×3` / `×4`. **So (BE-109)(iv)'s *"unmeasured, not excluded"* is
> now MEASURED and REALIZED**, and its generality claim is not merely
> restored but widened: the tail stratum is not a series-end phenomenon.
> The three bucket-B topologies still not drawable are listed by name in the
> driver's own output — disclosed, not smoothed.

> **(BE-117)(iii)** *(and the mechanism off paths is **simpler**, not
> harder)* At a non-path core the planted configuration collapses `A` onto
> `Λ²π` exactly: the census returns `(ρ_i, dim(ρ̄_i ∩ Σ_x), dim A) = (4,3,3)`
> at every non-path hit, against `(5,3,4)` at the path hits. That is
> (BE-114)(ii)'s `ℓ ∉ A` branch with `A = Λ²π` — `ρ̄_i = ⟨ℓ⟩ ⊕ Λ²π`,
> `ρ̄_i ∩ Σ_x = ⟨ℓ⟩ + p_x ∧ π = p_x ∧ (⟨p_c⟩ + π) = Σ_x`. **(BE-109)(ii)'s
> two-line dimension count is the `dim A = 4` case of the same computation**,
> with the path's first core edge supplying the extra dimension.

### Step BE117 — (BE-118): the `ρ_i = 4` witness, in the generic flag regime

> **(BE-118)(i)** *(**the peel**, constructed and disclosed as such)* Glue a
> non-path bucket-A side to a subdivided 3-connected skeleton at two
> **non-adjacent** hubs `x, y`. Non-adjacency is required and is the one
> structural constraint: with `x ~ y` in the skeleton, `side_2 + (x,y)`
> carries a parallel pair after degree-2 suppression, a **P-node**, and
> `bpeel.rnode_shaped` rejects it. `K₃₃` and the prism have non-adjacent hub
> pairs; `K₄` has none, which is why the witness is not on BSIGMA's
> skeleton. Asserted at every row: `rnode_shaped(side_2, x, y)` **true**,
> `rnode_shaped(side_1, x, y)` **false** (a side with both terminals of side
> degree `1` never is), `{x,y}` a 2-cut, both gates pass. One exhibited
> graph, for the record: `K33(3,3,3,3,3,3,3,3,3)` + `2 pendants + cycle(8)
> at distance 4`, `|V| = 32`, `|E| = 37`, `def₃ = 1`.

> **(BE-118)(ii)** *(**THE WITNESS**, and it refutes (BE-110)(iv)'s hunt
> verdict)* Over **7** constructed composites × **3** seeds, **21** rows,
> **every one** carries, all asserted:
>
> - `Σ_x ⊆ ρ̄₁` as spaces at **`ρ₁ = 4`** — and `c₁(Π_x) = 2` at the
>   closed-star plane **and at 24 further random planes through `p_x`**;
> - `deg₁(x) = deg₁(y) = 1`, i.e. **bucket A**;
> - `flag_frame` **non-`None`** — the **generic flag regime**, `π_x ≠ π_y`,
>   `p_x ∉ π_y`, `p_y ∉ π_x`;
> - `assert_generic_star` **and** `verify_pencil_witness`, via
>   `bdecor.assemble`.
>
> **(BE-110)(iv)'s verdict** — *"in the bucket a peel in the generic flag
> regime can present (`deg_i(y) = 1`), **none found** at a cap of 668 rows
> over 16 topologies"* — is therefore **REFUTED BY WITNESS**, and it is one
> of the four items (BE-113)'s *What would change this* named (*"a `ρ_i = 4`
> shape with `deg_i(y) = 1` would break the floor inside the
> regime-compatible bucket"*). **(BE-110)(ii) is a PATH theorem and is
> untouched** — its proof consumes the path in both steps; what falls is the
> extrapolation of its conclusion off paths, which (BE-110)(iv) had recorded
> as a *hunt*, not as a theorem.

> **(BE-118)(iii)** *(why the regime survives here and did not at
> (BE-110)(iv)'s `ρ = 4` rows)* (BE-110)(iv)'s `ρ_i = 4` rows were bucket
> **B**: `deg_i(y) ≥ 2` forces `π_y` from side `i` alone, the plant puts
> `p_x ∈ π = π_y`, and `flag_frame` rejects. Here `deg₁(y) = 1`, so side 1
> leaves `π_y` to side 2 ((BE-70)(ii)) and side 2 pulls it off `π`. **The
> regime gate is exactly `deg_i(y)`, as (BE-110)(iv) said — the landed
> reading of the gate is correct and it is the *verdict* attached to it that
> was cap-bound.**

### Step BE118 — (BE-119): the `deg_i(x) ≥ 2` half — (BE-113)'s price (d)

> **(BE-119)(i)** *(**PROVED**, from (BE-114)(iv) + (BE-115))* At
> `deg_i(x) ≥ 2`, `Σ_x ⊆ ρ̄_i` forces `dim(A ∩ Σ_x) ≥ 2` with `A` the same
> `p_x`-free core space. **Whenever `dim A ≤ 4`, (BE-115)(ii)–(iii) make
> that locus proper in `p_x`**, by the same argument and the same
> neutralization — under the same `p_x`-sweep input (BE-116)(i) names. So
> properness at `deg_i(x) ≥ 2` holds on the `dim A ≤ 4` stratum, with
> **`dim A ∈ {5,6}` the named residual** — there `dim(A ∩ Σ_p) ≥ 2` is
> automatic and the weak inclusion says nothing.

> **(BE-119)(ii)** *(**MEASURED**; price (d), which was unmeasured anywhere)*
> Over **16** `deg_i(x) ≥ 2` topologies (cycles at three distances, five
> thetas, two subdivided `K₄`s) × (8 blind + 6 planted) = **91** rows: the
> weak inclusion asserted at **91/91**; `dim A ∈ {1,2,3}` at every row, so
> **`dim A ≥ 5` occurs 0 times** — *not found under that cap*, never
> *"cannot happen"*; and `Σ_x ⊆ ρ̄_i` with `ρ_i ≤ 5` occurs **0 times** —
> again *none found under that cap*. Observed `(ρ_i, dim(ρ̄_i ∩ Σ_x))`:
> `(1,0), (2,0), (2,1), (3,1), (4,1)` only. **The structural reason,
> reported as a reading and not as a theorem:** at `deg_i(x) ≥ 2` the
> terminal sits on a cycle, the core is correspondingly rigid, and `A` stays
> small — which is the opposite of the regime (BE-113)(iii)'s positive half
> pointed at.

### Step BE119 — (BE-120): the price, and where it actually lands

> **(BE-120)(i)** *(**MEASURED**; the shortfall control, and item 0(c) is
> untouched)* At all **21** full-peel rows, **asserted**: `margin ≤ 0` at
> `Π_x`, at `Π_y` and at `⟨M⟩`. Margin histogram at `Π_x`: `{−1: 6, 0: 15}`;
> `(c₁, c₂)` at `Π_x`: `(2,0): 21`. **0 shortfalls at the three 2-blocks.**
> `notes/Phase39.md` *Hand-off* item 0 sub-item (c) — a bad row with
> `margin > 0` at `Π_x` — is **not** exhibited here and **stays open**.
> Job 2's `⟨M⟩` shape is likewise still empty: `(c₁, c₂)` at `⟨M⟩` is
> `(1,0)` at all 21, so the both-sides shape (BE-97)(iv) names is **0 of 21**,
> taking (BE-108)'s denominator from 72 to **93**.

> **(BE-120)(ii)** *(**MEASURED**; the second price of planting off a path,
> and it is the finding of independent value)* At a **path** side the plant
> costs nothing: a path is a tree, its hinge rows are independent at *every*
> configuration, so `dim M = |E| + 6` and `a_i = dim M − 6 − def₃ = 0`
> identically — asserted at every path hit. **Off a path it costs `a_i ≥ 1`**
> — asserted at every non-path hit; measured values `1, 2, 3, 6` across the
> library. Consequently, at all 21 peel rows
> `a₁ + a₂ > max(0, 6 − δ₁ − δ₂)`, so `min(δ₁+δ₂,6) + a₁ + a₂ > 6 ≥ reach`
> and the peel **cannot attain at that configuration** — arithmetically, not
> geometrically. At **15** of the 21 this is an outright violation of the
> block inequality at `U = Λ²K⁴` (`margin = +1`). **These are the first
> exhibited inhabitants of (BE-101)(iii)'s live non-attaining block, and of
> the shape BDOUBLE's own *What would change this* named** (*"a peel with
> `a₁ + a₂ > max(0, 6 − δ₁ − δ₂)`; that breaks `U = Λ²K⁴` directly"*).

> **(BE-120)(iii)** *(**and it is priced DOWN**, with the control that
> settles it)* **F13 negative control:** the **same seven graphs** drawn
> **freely** — `bproper.free_peel`, no plant anywhere — give at every one
> `dim(ρ̄₁ ∩ Σ_x) = 1`, `a = (0,0)`, and `reach = min(δ₁+δ₂,6) + a₁ + a₂`,
> i.e. **the peel ATTAINS**. So nothing in (ii) is a fact about the graph;
> it is a fact about a deliberately non-generic stratum, and **(BE-14) is
> existential**. Half (B) is **not** refuted, `hbareSplit` is untouched, and
> the correct summary is that the planted non-path rows are **doubly**
> non-generic — `Σ_x ⊆ ρ̄_i` *and* `a_i ≥ 1` — which is a *second*,
> independent reason they cannot bear on the block law, on top of (BE-116)'s
> properness.

> **(BE-120)(iv)** *(a landed measured identity, annotated — not refuted)*
> (BE-86)'s `ρ_i = δ_i + a_i` holds at its own 392 certificates and is
> **not** universal: it needs the **welded** side at generic rank too, since
> `ρ_i = dim M_i − 6 − g_i` while `δ_i + a_i = dim M_i − 6 − g_i` only when
> the welded side attains its count. At the planted rows here
> `δ_i + a_i − ρ_i ∈ {0, 1, 4}`. Recorded so a successor does not quote the
> identity as unconditional.

### Step BE120 — (BE-121): the residual, the board, the reading, the E-rider

> **(BE-121)(i)** *(**the residual**, in (BE-113)(i)'s own four-item shape
> and not one word stronger)* **Half (B) is NOT discharged, and item 1 is
> NOT closed.**
>
> 1. **(PENCIL-SATURATES-CHART): its PROPERNESS half is settled —
>    positively, at every side; its GENERICITY half is not.** What is left
>    of item 1 is no longer a properness question; it is the passage from
>    *proper* to *generic*, i.e. **(BE-69)'s openness for this specific
>    locus**, plus (BE-116)(iii)'s two measured inputs (the `p_x`-sweep;
>    `a_i = 0` generically). That is the successor's target, it is a *chart*
>    question rather than a *configuration* hunt, and it is **narrower**
>    than (BE-113)(i)'s was.
>    ***ANSWERED 2026-09-02 by (BE-122)–(BE-127), direction BOPEN: item 1
>    CLOSES at every side-degree-`1` terminal.*** (BE-69) is the **wrong
>    citation** and is **not needed** ((BE-122)/(BE-123)); both measured
>    inputs are **PROVED** ((BE-124)/(BE-126)); and the `Π_x`-vs-`Σ_x` gap
>    (BE-116)(iii) did not list is closed pointwise by a flag rotation
>    ((BE-125)). What is left is the side-degree-`≥ 2` instances, where the
>    clause reduces to a condition `(∗)` on ONE fixed line — certified
>    exactly 91/91 and **not proved** ((BE-127)(ii)/(iii)).
> 2. **The other 12 live blocks**: `⟨M⟩` measured empty at **93** rows
>    (72 + 21); the remaining 11 still unwitnessed rather than excluded.
>    **Unchanged in kind.**
> 3. **The non-attaining case — MOVED from *unchanged* to *inhabited*.**
>    (BE-101)(ii) is an `a₁ = a₂ = 0` statement and off it `U = Λ²K⁴` is
>    live ((BE-101)(iii)); (BE-120)(ii) exhibits 15 rows there. The
>    inhabitants are non-generic configurations of graphs that attain when
>    drawn freely, so the item is **inhabited, not activated**.
> 4. **The ear case's (β) side at the window**, modulo §(K-bare-ext)'s own
>    two window conditions, and **cross-pair welding** ((BE-28)(i)) —
>    unchanged.

> **(BE-121)(ii)** *(**the board**)* **What moved.** The **properness half**
> of the twice-repaired clause holds at **every** side, by a reduction and
> an incidence count that use no side topology; the `deg_i(x) ≥ 2` price (d)
> is **measured for the first time** and proper on its whole measured
> stratum; (BE-109)(iv)'s cap is **repaired** and the tail stratum shown to
> be a hub-carrying phenomenon; (BE-110)(iv)'s hunt verdict is **refuted by
> witness in the generic flag regime**; (BE-101)(iii)'s non-attaining block
> is **inhabited**; and (BE-86)'s measured identity is **annotated with its
> missing hypothesis**. **What did not move.** `PencilPair K 3 G`,
> `hbareSplit`, `hK`, (GR-15), (BE-14), the 2-cut step, half (B), class
> uniformity — **all untouched**; **(PENCIL-SATURATES-CHART) is still not a
> theorem** and item 1 is still open; **no shortfall at `Π_x`/`Π_y`/`⟨M⟩` is
> exhibited**; the 11 unmeasured blocks are still unmeasured; (BE-69) is
> cited, not re-derived; and **(BE-110)(ii) stands as the path theorem it
> was stated as**. ***The (BE-69) clause is SUPERSEDED 2026-09-02: it is not
> re-derived because it is the wrong citation and is not needed
> ((BE-122)/(BE-123)).***

> **(BE-121)(iii)** *(**the coordinator's reading**, classified)* The
> reading was: *"the corank identity is structure-free; what the path-side
> proof consumes is the case analysis on `dim⟨L_j⟩ ∈ {0,1}`, which is where
> `assert_generic_star` does its work — so properness off paths needs **no
> new identity**, only a replacement for `assert_generic_star`'s role at a
> vertex of degree `≥ 2`, where `⟨L_j⟩` has more room and the `ρ ≤ 3` cap
> should weaken rather than vanish."* It is a **SPLIT**, the arc's second.
>
> - **First half CONFIRMED and load-bearing.** The diagnosis of *what the
>   path proof consumes* is exactly right, and it is (BE-114)(iii)'s content:
>   the identity transports, the proof does not, and the reason is the `L_j`
>   analysis.
> - **Second half MOOT** (`RESEARCH-ARC.md` §7's fourth kind). No
>   replacement for `assert_generic_star` was needed and **no `⟨L_j⟩`
>   analysis was run at all**: the pendant reduction moves the question out
>   of the projected plane and into the ambient, where an incidence count
>   settles it for every side at once. The `ρ ≤ 3` cap plays no role.
>   This is the shape §7 flags as most likely to go moot — the hypothesis
>   proposed *repairing* a step rather than *removing* it.
> - **Escape-clause item 1 REFUTED** (the locus is proper everywhere;
>   `Π_x`/`Π_y` do **not** return to the 14). **Item 2 VINDICATED and
>   promoted to the residual** — *"I have not checked whether `Chart(H)`'s
>   irreducibility is available at a non-path side; this may be
>   load-bearing"* is exactly (BE-116)(iii)(b) and (BE-121)(i) item 1.
>   **Item 3 CONFIRMED but relocated**: `deg_i(y) = 1` is doing more work
>   than the properness argument needs — none — and all of it in the
>   **regime gate**, which is what makes (BE-118)'s witness count.
> - **Tally: thirteen instances, seven kinds** — *corrected from "twelve" by
>   the coordinator's round reconciliation, 2026-09-02; the landing read a
>   baseline of eleven that direction GLIST had already consumed the same
>   day*. This is the **second** SPLIT and, like the first, it is recorded
>   as a half-instance of CONFIRMED rather than an eighth kind.

> **(BE-121)(iv)** *(classification, mandatory and explicit)* **What is
> proved**: (BE-114), (BE-115), (BE-119)(i), and (BE-116) **inside the
> `p_x`-fibre**. **What is measured, not proved**: (BE-116)'s `p_x`-sweep
> input; `a_i = 0` at a generic configuration — ***both PROVED 2026-09-02,
> (BE-124)/(BE-126)***. **What is cited, not re-derived**: (BE-69)'s
> openness for this locus — ***and it is the WRONG citation and NOT NEEDED,
> (BE-122)/(BE-123)***. **What is refuted**: two
> *hunt verdicts* — (BE-109)(iv)'s *"unmeasured, not excluded off paths"*
> and (BE-110)(iv)'s *"none found at `ρ_i ≤ 4` in the regime-compatible
> bucket"* — and **no theorem**. **What is NOT refuted**:
> `PencilPair K 3 G`; `hbareSplit`; (BE-14); half (B); (BE-110)(ii) as a
> path theorem; (BE-101); (BE-86) at its own certificates; **any** landed
> measurement. **One question is CLOSED** (properness off paths) **and one
> route is narrowed** (item 1 becomes a chart question). **Not a PENCIL
> event.**

### Verdict, classification, and the price

- **HIT shape 1 — the target's PROPERNESS half settled.** It holds at
  **every** side with `deg_i(x) = 1`, path or not, with **no side-topology
  hypothesis** ((BE-114)+(BE-115)+(BE-116)) — a *class* statement, exactly
  as (BE-113)(i) asked. **PROVEN-INFORMALLY MODULO A MEASURED SWEEP INPUT**,
  never "proved" unqualified.
- **HIT shape 2 — price (d) MEASURED and half-settled** ((BE-119)): 91 rows,
  `dim A ≤ 3` throughout, properness on the whole measured stratum, residual
  `dim A ≥ 5`.
- **HIT shape 3 — the adversarial control refutes TWO landed hunt verdicts**
  ((BE-117), (BE-118)), one of them by a witness in the generic flag regime
  that (BE-113)'s own *What would change this* had named.
- **HIT shape 4 — the forced support audit**, answered for six populations,
  with the predecessor's defect **located at one line of one function**.
- **The coordinator's reading: SPLIT** ((BE-121)(iii)) — first half
  confirmed, second half **moot**, escape-clause item 2 vindicated and now
  the residual.
- **NOT HIT** — **(PENCIL-SATURATES-CHART) is NOT a theorem** and half (B)'s
  item 1 is **NOT closed**: its properness half is settled, its genericity
  half cites (BE-69) and rests on two measured inputs ((BE-116)(iii)).
- **The price, stated as a price.** **(a)** (BE-116)'s `p_x`-sweep input is
  **measured** (96 rows, ~1 500 sweep points), not proved — ***PROVED
  2026-09-02, (BE-124)***. **(b)** (BE-69)'s openness is **cited** for this
  locus, not re-derived; `a_i = 0` generically is **measured** — ***the
  citation is WRONG and unnecessary ((BE-122)/(BE-123)) and `a_i = 0` is
  PROVED ((BE-126)), 2026-09-02***. **(c)** `dim A ≥ 5` at `deg_i(x) ≥ 2` is *not found under
  a cap of 91 rows over 16 topologies*, never *"cannot happen"* — and there
  (BE-119) gives nothing. **(d)** The peel population is **constructed**
  (7 composites × 3 seeds, one branch profile), not a census; *"0 shortfalls
  at the 2-blocks"* is a statement about those 21 rows. **(e)** The whole
  side library inherits `bearcase.sample_piece_config`'s shape guard
  (degree-`≥3` vertices an independent set); sides violating it are outside
  every sweep here. **(f)** `rnode_shaped` is BPEEL's disclosed stand-in.
  **(g)** Exact ℚ only: (BE-115)'s proof is characteristic-free, its
  numerical support is not.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py alpha      #    2.7 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py reduce     #  189.3 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py proper     #   57.9 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py plant      #  116.5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py peel       #   85.4 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py degx       #   40.6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py support    #    0.2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bproper.py validate   #  243.2 s (reduced, all seven)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single
seed is `20260902`, printed by every mode. Every headline is an `assert`,
not a report: the reduction as an identity of **spaces** at 327 draws plus
`A`'s invariance under 164 moves of `p_x`; the dichotomy and its BAD/GOOD
classification at every one; the incidence lemma's two clauses at every
random-subspace draw and its exception at 24 constructed ones; a **good**
`p_x` in every sweep of every one of 96 planted bad rows, with the planted
`p_x` asserted to be in the fibre and bad; the census's `16/16` drawability
and the `a_i = 0` / `a_i ≥ 1` path split at every hit; the 21 peel rows'
regime, both gates, R-node shape, `c₁(Π_x) = 2` at 24 random planes, and
`margin ≤ 0` at `Π_x`/`Π_y`/`⟨M⟩`; the F13 free control's `a = (0,0)`,
`dim(ρ̄₁ ∩ Σ_x) = 1` and attainment; and the weak inclusion at all 91
`deg_i(x) ≥ 2` rows.

### Caps, disclosed rather than smoothed — with the denominator named

1. **(BE-114) and (BE-115) need no cap.** Both are proofs; the draws can
   only falsify them. (BE-115)'s support is exact ℚ, disclosed.
2. **(BE-116) is PROVED inside the fibre and MEASURED across it.** The
   `p_x`-sweep input rests on **96** planted bad rows over **16**
   topologies, 16 sweep points each; **0** of the ~1 500 swept points is
   bad, and a good point exists at **96/96**.
3. **The planted census is 8 draws per topology.** *"16 of 16 drawable"* and
   *"fires at 11"* are statements about those draws; the three bucket-B
   topologies with no draw are named in the output.
4. **The peel population is constructed and small**: 7 composites × 3 seeds
   = **21** rows, one branch profile (all 3s), two skeletons. Every row is a
   hit row by construction. It is not evidence about BSIGMA's 78, BSATUR's
   260 or BUNIF's 92.
5. **price (d)**: **91** rows over **16** topologies; `dim A ≥ 5` and
   `Σ_x ⊆ ρ̄_i` at `ρ_i ≤ 5` are both **not found under that cap**, never
   *"does not exist"*. Only **one** choice of the retained pendant edge
   `c₁` (the lexicographic first) is exercised, though the inclusion holds
   for every choice.
6. **The side library is shape-guarded**, inheriting
   `sample_piece_config`'s restriction verbatim, and `rnode_shaped` is
   BPEEL's disclosed stand-in — both unchanged from BSIGMA.
7. **`a_i = 0` at a generic configuration is MEASURED** (every blind draw of
   the library), not proved; it is the max-rank half of the body-hinge
   count.

### Harness note — the `kbare/` sibling-import set gains its TWENTY-FOURTH consumer, and `bsigma.wedge3` gains its FIRST second consumer

`w4/bproper.py` imports `bsigma`, `bsatur`, `bunif`, `bdecor`, `bpeel`,
`bimage`, `binduc`, `kbare_common` and `exactcore` read-only and
reimplements none of them: no deficiency oracle, no `ρ̄`, no peel scan, no
block decomposition, no row measurement and no margin arithmetic —
`peel_of`, `row_of`, `margin_at`, `sigma_at`, `side_library`,
`sample_side_config`, `flag_assignment`, `draw_branch` and `assemble` are
taken straight from their canonical homes. It is the **twenty-fourth**
`kbare/` consumer and takes the chain **twenty-two** deep
(`… → bsatur → bsigma → bproper`). **A NEW, UNPAID debt item is created and
disclosed**: `bsigma.wedge3` (the map `ω ↦ ω ∧ p_x`) now has a **second**
consumer, which by `notes/scripts/README.md` §2 rule 2 is the signal to move
it down to `exactcore` — **no move made**, and the item is recorded in that
file's *Harness debt*.

**One deliberate DIVERGENCE, and it is (BE-117)'s content:**
`bproper.plant_side` is `bsigma.sample_side_config(..., plane=, off=)` with
**one line changed** — a hub inside the planted plane gets that plane as its
flag. It is a *different sampler*, not a refactor of the old one, and
BSIGMA's recorded figures are untouched; both must stay, and the README's
*Divergences* carries the entry.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-114)(i) the pendant reduction | **PROVED**; asserted as spaces at 327 draws + 164 `p_x` moves |
| (BE-114)(ii) the dichotomy | **PROVED**; asserted, with BAD/GOOD classification, at every row |
| (BE-114)(iv) the weak inclusion at `deg_i(x) ≥ 2` | **PROVED**; asserted at 91/91 |
| (BE-115)(i) clause (a) | **PROVED** (three α-planes span); asserted at 48 triples |
| (BE-115)(ii) clause (b) + the exception | **PROVED** (incidence count); asserted at every draw off the exception |
| (BE-115)(iii) the exception is real and neutralized | **PROVED**; the exception **exhibited by construction**, 24 draws |
| (BE-116)(i) properness at every side | **PROVEN-INFORMALLY INSIDE THE `p_x`-FIBRE**; the sweep input **MEASURED**, 96 rows — *not* "proved" unqualified |
| (BE-116)(ii) what it delivers | **SCOPED**: (PENCIL-SATURATES-CHART) is **not** a theorem; item 1 **not** closed |
| (BE-116)(iii) what it does not deliver | **STATED**, with all three inputs named — **all three DISCHARGED 2026-09-02** ((BE-122)–(BE-126)), and a **fourth** it did not list (the `Π_x`-vs-`Σ_x` locus mismatch) found and closed ((BE-125)) |
| (BE-117)(i) the cap is a sampler artefact | **VERIFIED AT SOURCE** — the offending line read, not inferred |
| (BE-117)(ii) 16/16 drawable, 11 fire, 8 non-path | **MEASURED**, 8 draws per topology, no-draw list disclosed |
| (BE-118)(ii) the `ρ₁ = 4` witness in the regime | **EXHIBITED BY WITNESS**, 21 rows, both gates, `flag_frame` non-`None` |
| (BE-119)(i) properness at `dim A ≤ 4` | **PROVED**, under (BE-116)(i)'s same measured sweep input |
| (BE-119)(ii) price (d) | **MEASURED**, 91 rows; both *"none found"* verdicts capped |
| (BE-120)(i) no shortfall at the 2-blocks | **MEASURED + ASSERTED**, 21 rows; item 0(c) stays OPEN |
| (BE-120)(ii) the plant costs `a_i ≥ 1` off paths | **ASSERTED** at every hit of the census |
| (BE-120)(iii) the F13 free control | **MEASURED**, 7/7 graphs, `a = (0,0)` and attaining |
| (BE-120)(iv) (BE-86)'s identity needs the welded side | **MEASURED**, 21 rows |
| (BE-121)(iii) the reading | **SPLIT** — first half confirmed, second half MOOT |

### What would change this

- **A proof, or a refutation, of (BE-116)'s `p_x`-sweep input.** That is the
  one place the argument still leans on a measurement, and it is a statement
  about side 2's chart, i.e. `bsatur.reflag` one variable further along.
  ***PROVED 2026-09-02 from the tower, (BE-124) — and it needed no re-flag at
  all.***
- **(BE-69)'s openness re-derived for the locus `{Σ_x ⊆ ρ̄_i, ρ_i ≤ 5}`** —
  the passage from *proper* to *generic*, and now item 1's whole residue.
  ***RETIRED 2026-09-02: (BE-69) is about the ATTAINMENT locus and does not
  transport, and the passage needs only constructibility on an irreducible
  chart ((BE-122)/(BE-123)). The residue is `(∗)` at side-degree `≥ 2`
  ((BE-127)).***
- **A `deg_i(x) ≥ 2` side with `dim A ≥ 5`.** (BE-119) gives nothing there,
  and none was found at 91 rows.
- **A `margin > 0` row at `Π_x`, `Π_y` or `⟨M⟩`** — still the arc's first
  genuine shortfall if it exists, and still unexhibited.
- **A peel whose GENERIC configuration has `a_i > 0`.** Every free draw here
  gave `a = (0,0)`; a counterexample would **activate** (BE-101)(iii)'s block
  rather than merely inhabiting it, and would matter far more than
  (BE-120)(ii) does.

### TERMINATION riders

**E1 / E2 / E3 — reported, never fired; E3 remains ARMED (by GBAL).** Read
against their actual definitions in `notes/Pencil-fanout-archive.md`
(`:1686–1712` and `:2078–2106`), not by analogy and not from a later
landing's paraphrase, with the 2026-09-02 correction (`61e046a6`) in force:
**"the target" in E1–E3 is the ARC's target, `PencilPair K 3 G`**, never a
direction's local obligation. The corpus carries **two** E3 texts; **this
reading is `:1700`'s two-conjunct form**, with `:2098`'s one-conjunct
deviation noted and **not** used — as BBASE, BUNIF, BDOUBLE, BSATUR and
BSIGMA all read it.

- **E1** — a g-flank, a `D = 0` shape whose every admissible colouring is
  binding. **Does not fire**: no colourings, no `D`, no g-flank, and
  §(K-grid) is untouched by this direction.
- **E2** — the arc's target refuted or unprovable-as-posed **and** no ledger
  entry left open-with-a-named-dispatchable-attack. **Does not fire on
  either conjunct.** What is refuted here is **two hunt verdicts** —
  (BE-109)(iv)'s cap and (BE-110)(iv)'s *none found* — both local to a
  direction, **not** `PencilPair K 3 G`; and this landing names dispatchable
  attacks ((BE-121)(i) items 1–4, item 1 now a chart question with two named
  inputs).
- **E3** — the arc's target proven **and** every remaining entry
  adjudication-gated. **Does not fire on either conjunct**; under `:2098`'s
  one-conjunct text it still does not fire, the first conjunct being the one
  that fails.

**F11 — one driver per headline sentence, and the two claim classes named.**
The *proved* claims — (BE-114), (BE-115), (BE-116) inside the fibre,
(BE-119)(i) — are proofs whose drivers can only falsify them. The
*existential* claims — the 16/16 drawability, the eight non-path hits, the
`ρ₁ = 4` regime witness — fall to one construction each and needed no sweep
exhausted. The claims that **are** sweeps carry their denominators in
*Caps*: 96 rows for the sweep input, 8 draws per topology for the census, 21
rows for the peel, 91 rows for price (d). Every *"none found"* here —
`dim A ≥ 5`, `Σ_x ⊆ ρ̄_i` at `deg_i(x) ≥ 2`, a `Π_x` shortfall — reads
**none found under those caps**, never *"does not exist"*.

**F12 paid at source in this commit.** Eight hunks, at the statements rather
than only here: **(BE-109)(iv)** (the *5-of-16* cap, REPAIRED),
**(BE-110)(iv)** (the `ρ_i ≤ 4` verdict, REFUTED), **(BE-112)(iii)** (the
bad locus is proper everywhere, not only at path sides), **(BE-113)(i)
items 1 and 3**, **(BE-113)'s price (d)**, BSIGMA's *Caps* items 3 and 8,
and a one-clause annotation on **(BE-86)** per (BE-120)(iv).

**F21**: the `(K-bare)` gap-map row is recomputed — **integrated, not
appended** — to an explicit target of **≤ 1 500 status+close-it words**
(≥ 100 words of headroom against the 1 600 combined cap, up from 62),
landing at **1 499**: a whole landing absorbed at a **net −39 words**, by
folding **mechanism superseded as headline** and never history. Label
preservation verified by `notes/scripts/gapdiff.py`: **143 in, 155 out, ZERO
dropped, 12 added**. **No `SPECIAL_CAPS` entry proposed and none needed** —
*no overflow, no bump*.

**Two mechanics findings, both new to `RESEARCH-ARC.md` §2, recorded here
because §2 currently covers only tracked-file contention.**
**(1) A draft-only dispatch must diff against `HEAD`, never against the
working tree.** This direction did that correctly for the gap map
(`gapdiff.py K-bare HEAD`) and *incorrectly* for the phase note, reading
`notes/Phase39.md`'s line and status-word counts off a **sibling's
uncommitted edits** and reporting them as landed state. The gap-map work was
sound for exactly that reason; the phase-note figures had to be re-measured
after the sibling committed. **(2) The session scratchpad is SHARED between
concurrent dispatches.** Two of this direction's working files were written
under generic names (`closeit.txt`, and a sibling's `status.txt` appeared in
the same directory); a sibling overwrote one of them mid-round. Nothing was
corrupted here **only because** the row-assembly chain re-derives everything
from a single file that was re-verified byte-identical to HEAD before use.
The rule both findings share: **prefix every scratch file with the direction
code**, and **re-verify any scratch input against `HEAD` immediately before
consuming it**.

**Reservation, and what is returned.** Labels **(BE-114)–(BE-121)** and
***Steps BE113–BE120*** were reserved, 0-hit verified, and are **consumed in
full**; nothing is returned. The driver `w4/bproper.py` lands at the reserved
path. **Nothing is minted** — not for the core space `A`, the pendant
reduction, the incidence lemma, or the `p_x`-sweep input, all of which stay
plain descriptive prose, exactly as *the tail stratum* and *the projected
pair lines* did for BSIGMA. The section has now gone **eight** directions
without minting a configuration-level token.
