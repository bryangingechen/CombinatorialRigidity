## §(K-bare-ext), continued — direction BLINE: `(∗)` DECIDED (*Steps BE128–BE134*)

### Standing notation (on top of *Steps BE121–BE127*)

BOPEN's, unchanged, plus four objects this direction needs. `x, y` the
peel's terminals, `deg_i(x) = k ≥ 2` with side neighbours `c₁, …, c_k`,
`core := side_i − x`, `A := ρ̄(core; c₁, y)` the `p_x`-free core space of
(BE-114)(iv), `Σ_p = p ∧ K⁴`, `L_c := p_{c₁} ∨ p_{c₂}`. New here:

> **`z := p_{c₁} ∧ p_{c₂} ∈ Λ²K⁴`**, the Plücker point of `L_c`;
> **`W := z^⊥ = {ω : ω ∧ z = 0}`**, the lines *meeting* `L_c`, a
> **hyperplane** (`dim W = 5`) containing every `Σ_t` with `t ∈ L_c` (if
> `t ∈ L_c` then `t ∧ p_{c₁} ∧ p_{c₂} = 0`, so `(t ∧ v) ∧ z = 0`), and
> containing `z` itself; **`B := A ∩ W`**; and **`b := dim(B + ⟨z⟩) − 1`**,
> the dimension of `B`'s image in `V := W/⟨z⟩`.

The one identification the whole section runs on: **`V ≅ L_c ⊗ (K⁴/L_c)`**
— a space of `2 × 2` matrices, whose rank-one locus is the Segre quadric —
under which `Σ_t/⟨z⟩` is the **column-space-`⟨t⟩` ruling** `t ⊗ (K⁴/L_c)`.
Concretely with `L_c = ⟨e₁, e₂⟩`: `W = ⟨e₁e₂, e₁e₃, e₁e₄, e₂e₃, e₂e₄⟩`,
`z = e₁e₂`, and `Σ_{αe₁+βe₂} = ⟨e₁e₂, αe₁e₃ + βe₂e₃, αe₁e₄ + βe₂e₄⟩`.

**The condition under discussion, quoted from (BE-127)(ii) with its
hypotheses and not paraphrased:** *`Σ_t ⊄ A` for every `t ∈ L_c`, **and**
`{t ∈ L_c : dim(A ∩ Σ_t) ≥ 2}` is FINITE.* Per BOPEN's convention **`(∗)`
is a marker, not a label** — nothing is minted for it here either.

### Step BE128 — (BE-129): the classification — `(∗)` is three incidences and nothing else

> **(BE-129)(i)** *(**PROVED**; the fibre dimension, restated in `V`)* For
> `t ∈ L_c ∖ 0`, `Σ_t = ⟨z⟩ ⊕ σ_t` with `σ_t` a complement mapping
> isomorphically onto `t ⊗ (K⁴/L_c) ⊆ V`. Since any `z`-component is free
> inside `Σ_t`, an element of `A` lies in `Σ_t` **iff** its image in `V`
> lies in `t ⊗ (K⁴/L_c)`. Hence
>
> **`dim(A ∩ Σ_t) = dim(B̄ ∩ (t ⊗ K⁴/L_c)) + [z ∈ A]`,**
>
> with `B̄ ⊆ V` the image of `B`, `dim B̄ = b` when `z ∈ A` and
> `dim B̄ = dim B` otherwise. ∎

> **(BE-129)(ii)** *(**PROVED**; the case analysis)* Read `B̄` as a space of
> `2 × 2` matrices; `B̄ ∩ (t ⊗ M) ≠ 0` says `B̄` contains a **rank-one**
> matrix of column space `⟨t⟩`. So `{t : dim(B̄ ∩ t⊗M) ≥ 1}` is the image of
> `P(B̄) ∩ {det = 0}` under `b ↦ image(b)`, and:
>
> - `dim B̄ ≥ 3`: `3 + 2 > 4`, so **every** `t` qualifies;
> - `dim B̄ = 2`: `P(B̄)` is a line of `P(V) = P³` and `{det = 0}` is the
>   Segre quadric, so `P(B̄) ∩ {det=0}` is a degree-2 divisor on `P(B̄)` —
>   **finite (≤ 2 points), unless `P(B̄)` is a RULING of the quadric**. The
>   two rulings are `t₀ ⊗ M` (constant column space: only `t₀` qualifies)
>   and `L_c ⊗ m₀` (constant row space: **every** `t` qualifies);
> - `dim B̄ ≤ 1`: at most one `t`.
>
> Lifting: `⟨z⟩ ⊕ (t₀ ⊗ M) = Σ_{t₀}` and `⟨z⟩ ⊕ (L_c ⊗ m₀) = Λ²π'` with
> `π' := L_c ∨ m₀`. Therefore
>
> **`(∗)` FAILS ⟺ [`z ∈ A` and (`b ≥ 3`, or `b = 2` with `B/⟨z⟩` a
> ruling)] or [`z ∉ A` and `dim B = 4`].** ∎

> **(BE-129)(iii)** *(**PROVED**; the COMPACT form, and it is the one to
> quote)* Every clause of (ii) is one of three incidences, so the case split
> is removable:
>
> > **`(∗)` HOLDS ⟺ `dim(A ∩ C_{L_c}^⊥) ≤ 3`, AND no `Σ_{t₀}` with
> > `t₀ ∈ L_c` lies in `A`, AND no `Λ²π'` with `L_c ⊆ π'` lies in `A`.**
>
> *Proof.* (⇐, contrapositive of each clause) `dim B ≥ 4` gives `b ≥ 3` when
> `z ∈ A` and `B̄ = V` when `z ∉ A`, both failures by (ii);
> `Σ_{t₀} ⊆ A` is half one's own failure; `Λ²π' ⊆ A` with `L_c ⊆ π'` gives
> `dim(A ∩ Σ_t) ≥ dim(Λ²π' ∩ Σ_t) = 2` at **every** `t ∈ L_c ⊆ π'` (the
> pencil of lines of `π'` through `t`), so half two fails. (⇒) Each of
> (ii)'s four clauses implies one of the three: `b ≥ 3` with `z ∈ A` gives
> `dim B ≥ 4`; `z ∉ A` with `dim B = 4` is the same clause; and the two
> `b = 2` rulings are exactly `Σ_{t₀} ⊆ A` and `Λ²π' ⊆ A`. ∎
>
> The two forms are asserted **against each other and against the
> brute-force reading of `(∗)`** at 140 random `(A, L_c)` spread over
> `dim A = 0..6`, plus 48 constructed degeneracies (`bline.py classify`).

### Step BE129 — (BE-130): `dim A ≥ 5` REFUTES `(∗)` — and takes the reduction with it

> **(BE-130)(i)** *(**PROVED**; the refutation, and it is one line from
> (BE-129)(iii))* `W` is a **hyperplane**, so
> `dim(A ∩ W) ≥ dim A − 1`. Hence
>
> **`dim A ≥ 5 ⟹ dim(A ∩ C_{L_c}^⊥) ≥ 4 ⟹ `(∗)` FAILS`,**
>
> at **every** configuration, for **every** line `L_c`, with no genericity
> and no incidence hypothesis anywhere. Equivalently, and this is the form
> the consumers need: **`(∗)` ⟹ `dim A ≤ 4`.** ∎ Asserted at 60/60 random
> `(A, L_c)` with `dim A ∈ {5, 6}` — `(∗)` never once held — and the
> contrapositive re-asserted at 40 further draws (`bline.py five`).

> **(BE-130)(ii)** *(**PROVED**; and the failure is not a lost certificate
> but a dead route)* At `dim A ≥ 5` the reduction (BE-127)(ii) rests on is
> **VACUOUS**. For any `p ∉ L_c`, `p ∧ L_c` is a **2-dimensional** subspace
> of `W`; `dim(A ∩ W) ≥ 4`; and inside the 5-dimensional `W`,
> `2 + 4 − 5 = 1 > 0`. So
>
> **for every `p_x` off `L_c` there is a `t ∈ L_c` with `p_x ∧ t ∈ A`** —
>
> i.e. the necessary condition (BE-127)(ii) derives from `Π_x ⊆ ρ̄_i` holds
> at **every point of `P³`** and excludes nothing. Asserted at 2 400/2 400
> sampled `p_x` over 60 rows (`bline.py five`).

> **(BE-130)(iii)** *(**the reading**, stated against (BE-127)(ii)'s own
> comparison sentence)* (BE-127)(ii) closes with *"this is **stronger** than
> (BE-119)(i), which needed `dim A ≤ 4` and reached only `B_str`"*. That
> sentence is **half right, and the half that is wrong is the `dim A` half**:
>
> - **The locus half is CORRECT and is the direction's real gain.**
>   (BE-119)(i) proves properness of the `Σ_x ⊆ ρ̄_i` locus; (BE-127)(ii)
>   proves it for the strictly larger `Π_x ⊆ ρ̄_i` locus, and (BE-125)(iii)
>   exhibits a configuration where the two differ by a dense set. Nothing
>   here touches that.
> - **The hypothesis half is INVERTED.** `(∗)` does not *replace*
>   `dim A ≤ 4`; by (BE-130)(i) it **entails** it, and by (BE-129)(iii) it is
>   `dim A ≤ 4`-shaped plus two further exclusions. So `(∗)` is a
>   **strictly smaller** regime than (BE-119)(i)'s, not a larger one.
>
> **Consequence for the two surfaces that disagree.** The `(K-bare)`
> gap-map row lists *"the side-degree-`≥ 2` instances … and (BE-119)'s
> `dim A ≥ 5`"* as **two** left items; `notes/Phase39.md` *Hand-off* item
> 0(a) says the first **subsumes** the second. **The gap-map row is right
> about the count and the hand-off's "subsumes" is FALSE** — `(∗)` cannot
> hold anywhere on the subsumed stratum. The accurate statement is stronger
> than either: **they are the SAME obstruction**, `dim A ≥ 5`, reached by
> two routes that both die on it, and the honest merge is *one* item.

### Step BE130 — (BE-131): below `dim A = 5` — a theorem at `≤ 2`, two named degeneracies at `3`, one incidence at `4`

> **(BE-131)(i)** *(**PROVED**; `dim A ≤ 2 ⟹ (∗)`)* Half one needs
> `dim A ≥ 3`, so it holds. For half two, `dim(A ∩ Σ_t) ≥ 2` with
> `dim A ≤ 2` forces `A ⊆ Σ_t`; and for `t₁ ≠ t₂` on `L_c`,
> `Σ_{t₁} ∩ Σ_{t₂} = ⟨z⟩` is 1-dimensional (the only line through two
> distinct points is `L_c`), so **at most one** `t` qualifies. ∎ Asserted at
> 200/200 random draws, with the `|{t : dim ≥ 2}| ≤ 1` mechanism asserted
> at each rather than inferred from the outcome (`bline.py low`).

> **(BE-131)(ii)** *(**PROVED**; `dim A = 3`)* By (BE-129)(iii), `¬(∗)`
> needs `A ⊆ W` (as `dim(A ∩ W) ≥ 4` is impossible) together with a ruling,
> and at `dim A = 3` each of the two lifted rulings **is** `A`:
>
> **`(∗)` fails at `dim A = 3` ⟺ `A = Σ_{t₀}` for some `t₀ ∈ L_c`, or
> `A = Λ²π'` for some plane `π' ⊇ L_c`.**
>
> Both are **totally singular** 3-spaces of the Klein quadric, specially
> placed against `L_c`; both are **proper closed** in the Grassmannian, so
> **no blind draw of `A` can land on either** — which is exactly why they
> are **constructed** rather than sampled (48 of them, all failing;
> 0/200 random dim-3 draws fail). ∎

> **(BE-131)(iii)** *(**PROVED**; `dim A = 4`)* Here `dim(A ∩ W) ∈ {3, 4}`,
> so `¬(∗)` ⟺ **`A ⊆ C_{L_c}^⊥`**, or (`dim(A ∩ W) = 3` and `A` contains a
> `Σ_{t₀}` or a `Λ²π'` as above). The first clause alone is a **single
> linear incidence** — `ω ∧ z = 0` for every `ω ∈ A`, i.e. every reachable
> line meets `L_c` — and 16 constructed such `A` all fail; 0/200 random
> dim-4 draws fail, every one at `dim(A ∩ W) = 3` (`bline.py low`).

> **(BE-131)(iv)** *(the reading — what `(∗)` actually is)* Taken together,
> (BE-129)(iii) + (BE-130)(i) + this step say that `(∗)` is **not a
> quantifier over the line at all**. It is
>
> **one dimension count (`dim(A ∩ C_{L_c}^⊥) ≤ 3`) and two incidence
> exclusions**, decided by rank arithmetic on `A` and `L_c` alone. That is
> what makes it *decidable*; it is also what makes it **false on a whole
> stratum**, since a dimension count cannot be argued away.

### Step BE131 — (BE-132): what (BE-127)(iii)'s 91/91 certifies — a COROLLARY, not evidence

> **(BE-132)(i)** *(**MEASURED**; the population reproduced exactly)*
> (BE-127)(iii)'s rows are re-derived here from BPROPER's own
> `degx_library` at BPROPER's own seeds — 16 topologies, blind + planted:
> **91 rows**, `dim A ∈ {1: 16, 2: 34, 3: 41}`, `x` with **0** hub side-
> neighbours, `(∗)` holding at **91/91**. Every figure of (BE-127)(iii) is
> reproduced **exactly**, independently of `bopen.py` (`bline.py pop`).

> **(BE-132)(ii)** *(**PROVED**; and this is the finding)* Every one of
> those 91 rows has `dim A ≤ 3`. By (BE-131)(i) the **50** rows at
> `dim A ≤ 2` satisfy `(∗)` **by a theorem**; by (BE-131)(ii) the **41** at
> `dim A = 3` satisfy it unless `A` is one of two proper-closed
> degeneracies, which a blind draw cannot hit. Asserted row by row: **the
> clause of (BE-131) that decides the row is a theorem at 91/91** — 50 by
> (i), 41 by (ii).
>
> **So the 91/91 certification is a corollary of (BE-131), not evidence for
> `(∗)`.** It is not merely, as one might guess, evidence gathered where
> `(∗)` was not needed; it is evidence for a **statement already proved**,
> and it says nothing whatever about the only regime — `dim A ≥ 4` — in
> which `(∗)` was ever in doubt. (BE-127)(iii) had already disclosed (F13)
> that its **reduction assert never fired**; this step supplies the reason
> the *certification* half is blind too, which was not disclosed because it
> was not known.

> **(BE-132)(iii)** *(**the sampler's support**, `RESEARCH-ARC.md` §4's
> sharpening applied to this population)* `bproper.degx_library` is 16 small
> shapes — cycles of length 6/8/10 with `x, y` at distance 2/3/4, five
> thetas, two subdivided `K₄`s. In every one, the core `side_i − x` is
> **short**, so `dim A` cannot exceed 3. The sampler varies the
> **configuration** and never the **core length**, which is the one variable
> `(∗)` is actually a function of. This is F11's shape once more, at the
> variable `dim A` rather than at a flag.

### Step BE132 — (BE-133): the refuted stratum is INHABITED, and generically

> **(BE-133)(i)** *(**MEASURED**; 27 new chart-legal topologies)* Sides with
> the **same** `deg_i(x) = 2` shape at `x` and a **longer** core: `x` on a
> cycle of length 4/5/6, with a path of length `m = 1..6` from a cycle
> vertex to `y`. Two families — the tail hung far from `x`, and hung on
> `a₀ ∼ x` so that `c₁` is a **hub** — 27 topologies, drawn by
> `bsigma.sample_side_config`, the sampler (BE-127)(iii) itself used, 10
> draws each at coordinate ranges `{3, 5, 9}`: **270 rows**.
>
> **(CH-1) is asserted on the COMPOSITE first**, before any number is
> quoted: each side is glued to a subdivided `K₃,₃` (all branches 3) at two
> **non-adjacent** hubs, and `hcard`, min degree `2`, `girth ≥ 4`, both
> terminals hubs of `H` and side 2 `rnode_shaped` are asserted at
> **27/27**. So every row below sits on an irreducible `Chart(H)`
> ((BE-123)(iii)).

> **(BE-133)(ii)** *(**MEASURED**; `dim A` reaches 6, and `(∗)` dies)*
> `dim A` census over the 270 rows: `{1: 30, 2: 10, 3: 60, 4: 30, 5: 60,
> 6: 80}`. **`(∗)` FAILS at 142 of 270** — 60 at `dim A = 5`, 80 at
> `dim A = 6` (both **forced** by (BE-130)(i)), plus **one** row at
> `dim A = 3` and **one** at `dim A = 4`, each by the **β-ruling**
> `Λ²π' ⊆ A` on `cycle(5) at x + tail(1 resp. 2)`. At **every** `dim A ≥ 5`
> row the reduction is asserted **vacuous** in (BE-130)(ii)'s sense.

> **(BE-133)(iii)** *(**PROVED**, and it is what makes (ii) a genericity
> statement rather than a draw)* In every topology here the core is a
> **TREE**, so its hinge rows are independent at **every** configuration
> ((BE-120)(ii)) — asserted as `rank R_core = 5|E(core)|` at all 270 rows.
> With `rank R` constant, `dim A = rank[R; Q] − rank R` is a difference in
> which only the first term moves, and that term is **lower
> semicontinuous**. Hence
>
> **one draw with `dim A = d` certifies `dim A ≥ d` at a GENERIC point of
> that `Chart(H)`.**
>
> Per-topology maxima give `dim A ≥ 5` generically at **14 of the 27**
> topologies. **At those, `(∗)` fails at a generic chart point** — not at a
> degenerate one, not under a cap. ∎

> **(BE-133)(iv)** *(**MEASURED**; the clause is NOT vacuous where `(∗)`
> dies — the fairness check)* One might hope `dim A ≥ 5` forces `ρ_i = 6`,
> making the clause free exactly where the route dies. It does not. The
> `(dim A, ρ_i)` census is `(5,3): 20, (5,4): 10, (5,5): 30, (6,4): 20,
> (6,5): 29, (6,6): 31` — **109 of the 140 `dim A ≥ 5` rows have
> `ρ_i ≤ 5`**, so the clause has content there and the route says nothing
> about it. The mechanism is visible in that census: `ρ̄_i ⊆ ⟨ℓ₁⟩ + A` is a
> **relaxation**, and at `k ≥ 2` it is a lossy one — deleting `xc₂, …, xc_k`
> deletes exactly the constraints that make `x`'s cycle rigid, so `ρ_i` runs
> 1 to 3 **below** `dim A`.

> **(BE-133)(v)** `[MEASURED]` *(**the cap, disclosed with its denominator**)* The
> **clause itself** — `Π_x ⊆ ρ̄_i` with `ρ_i ≤ 5`, evaluated exactly as
> `bopen.py degx` evaluates it — is **0 of 270**: *not found under this
> cap*, never *"cannot happen"*. **What is refuted here is the ROUTE, not
> the clause.** `(∗)` is a **sufficient** condition, so its failure leaves
> (PENCIL-SATURATES-CHART) at side-degree `≥ 2` exactly as open as it was;
> no shortfall is exhibited and `notes/Phase39.md` item 0(b)/(c) is
> untouched.

### Step BE133 — (BE-134): two further gaps, and neither of them is `(∗)`

> **(BE-134)(i)** *(**read at source**; there is no `p_x`-sweep at
> `deg_i(x) ≥ 2`)* (BE-127)(i)'s assembly needs three inputs:
> constructibility ((BE-123)(i), general), the pointwise collapse
> ((BE-125)(ii)), and the **rational `p_x`-sweep** ((BE-124)(ii)). The third
> is proved **only at `deg_i(x) = 1`**: (BE-124)(i) says so in its own
> derivation — *"Since `deg_i(x) = 1`, `c` is `x`'s only side-`i`
> neighbour"* — and the completion it builds re-solves `n_x` from a
> **pencil** of planes through `q_x ∨ q_c`, which exists precisely because
> `π_x` is not yet determined. At `k ≥ 2`, `π_x = ⟨p_x, p_{c₁}, p_{c₂}⟩` is
> **determined by `p_x`** ((BE-105)(iv)), so moving `p_x` moves `π_x` and
> every side-2 neighbour of `x` must be re-placed into the new plane.
> **No lemma in the section covers that**, and (BE-127)(ii) does not claim
> one: it says only *"the bad locus is proper in `p_x`"*. So even a proof of
> `(∗)` would leave item 1 at side-degree `≥ 2` **two** steps short, not
> one. (The collapse (BE-125)(ii) is **not** among the missing steps — it is
> not needed at `k ≥ 2`, because (BE-127)(ii) attacks the `Π_x` locus
> directly.)

> **(BE-134)(ii)** *(**CONSTRUCTED**; and `proper in `P³`` is not `proper in
> the fibre`)* `(∗)` bounds the bad locus in `P³`. The `p_x`-fibre is
> `𝔸³` only when **no** side-`i` neighbour of `x` is a hub; it is the
> **plane** `π_{c_j}` when one is, and a **line** when two are
> ((BE-124)(i)'s two families, at `k ≥ 2`). And `(∗)` explicitly permits
> **finitely many** `t` with `dim(A ∩ Σ_t) = 2` — each of which contributes
> a whole **plane** `{p : p ∧ t ∈ A}` to the bad locus, since
> `q_t^{-1}(A ∩ Σ_t)` is then 3-dimensional. Twelve such `(A, L_c)` are
> **constructed** with `(∗)` **holding** and the bad plane asserted bad
> pointwise (`bline.py fibre`). So a fibre confined to that plane is
> entirely bad while `(∗)` holds. Whether a chart can place `π_{c₁}` on it
> is **not claimed**; what is shown is that `(∗)` as stated does not exclude
> it, so the fibre-relative statement is a **separate obligation**.

> **(BE-134)(iii)** *(**MEASURED**; the confined-fibre case is REACHABLE,
> which (BE-127)(iii) could not see)* (BE-127)(iii) reports `x` with **0**
> hub side-neighbours at all 91 of its rows, so its `p_x` fibre is `𝔸³`
> everywhere and (BE-134)(ii)'s hazard is invisible there. Nine of this
> direction's 27 topologies hang the tail on `a₀ ∼ x`, making `c₁` a hub:
> **90 hub side-neighbour incidences over 90 rows**, all on composites at
> which (CH-1) is asserted. The case is legal and reachable; it was simply
> never drawn.

### Step BE134 — (BE-135): the price, the board, the reading, the E-rider

> **(BE-135)(i)** *(**the board**)* **What moved.** `(∗)` is **decided**:
> an exact classification ((BE-129)), a **refutation** on `dim A ≥ 5` that
> takes the reduction with it ((BE-130)), a **theorem** on `dim A ≤ 2` and
> an exact criterion at `3` and `4` ((BE-131)); the 91/91 certification is
> shown to be a **corollary** ((BE-132)); the refuted stratum is exhibited
> **generically** at 14 chart-legal topologies ((BE-133)); and two
> obligations that are not `(∗)` are named ((BE-134)). The
> `(K-bare)`-row-vs-*Hand-off* disagreement is **settled** in the row's
> favour, with a correction to both ((BE-130)(iii)). **What did not move.**
> `PencilPair K 3 G`, `hbareSplit`, `hK`, (GR-15), (BE-14), the 2-cut step,
> half (B) as a whole, class uniformity, cross-pair welding — untouched.
> **(BE-127)(i) is untouched**: the theorem at side-degree `1` stands
> exactly as landed, and nothing here bears on it. **No shortfall is
> exhibited**; **no landed measurement is refuted** — (BE-127)(iii)'s
> figures are reproduced exactly.

> **(BE-135)(ii)** *(**the coordinator's reading**, classified)* The
> `route` block predicted: *the population that certifies `(∗)` lies
> entirely inside the regime where the older, weaker (BE-119)(i) already
> gave properness, so it is evidence for `(∗)` only where `(∗)` was not
> needed; and the hand-off's "subsumes" would be a subsumption asserted on
> a population containing none of the subsumed cases. Test this; the
> support gap is at `dim A ≥ 4`/`≥ 5` and at rows where `x` has hub side-
> neighbours.*
>
> - **Its premise is CONFIRMED at source.** The population is exactly
>   `dim A ∈ {1: 16, 2: 34, 3: 41}` with 0 hub side-neighbours; reproduced
>   independently ((BE-132)(i)).
> - **Its middle inference is REFUTED.** "(BE-119)(i) already gave
>   properness there" is false as stated: (BE-119)(i)'s locus is `Σ_x`,
>   (BE-127)(ii)'s is the strictly larger `Π_x`, and (BE-125)(iii) exhibits
>   the difference. At `dim A ≤ 3` (BE-127)(ii) does prove something
>   (BE-119)(i) does not.
> - **Its conclusion is CONFIRMED, for a stronger reason than it gave.**
>   The 91/91 certifies nothing not merely because the regime was already
>   covered, but because `(∗)` there is a **theorem** ((BE-132)(ii)).
> - **Its "subsumes" call is CONFIRMED as a defect, and sharpened.** Not
>   *"a subsumption on a population containing none of the subsumed cases"*
>   but **false outright**: `(∗)` cannot hold on the subsumed stratum
>   ((BE-130)(i)). And the corrected statement is neither "two items" nor
>   "subsumes": **one item** ((BE-130)(iii)).
> - **Its located support gap is CONFIRMED at both coordinates** — `dim A ≥ 4`
>   ((BE-133)) and hub side-neighbours ((BE-134)(iii)).
> - **Tally**: `RESEARCH-ARC.md` §7 stands at **sixteen instances, seven
>   kinds**; this landing **cites it and does not increment it**, per the
>   2026-09-02 finding that a shared monotone counter cannot be
>   concurrently incremented. Offered for the coordinator's reconciliation:
>   a **SPLIT** whose parts point the same way, and a candidate **eighth
>   kind — UNDERSHOT**: a prediction right in direction and *weaker than
>   the truth*, so that inheriting it rather than testing it would have
>   understated the finding. Whether that is a kind or a shade of SPLIT is
>   the coordinator's call, not this direction's.

> **(BE-135)(iii)** *(classification, mandatory and explicit)* **What is
> proved**: (BE-129) in full, (BE-130)(i)/(ii), (BE-131)(i)/(ii)/(iii),
> (BE-132)(ii), (BE-133)(iii). **What is measured, not proved**:
> (BE-132)(i), (BE-133)(i)/(ii)/(iv)/(v), (BE-134)(iii) — populations and
> censuses. **What is constructed**: (BE-131)'s degeneracies and
> (BE-134)(ii)'s bad planes. **What is cited**: (BE-105)(iv), (BE-114)(iv),
> (BE-115), (BE-119)(i), (BE-120)(ii), (BE-123)(iii), (BE-124)(i)/(ii),
> (BE-125)(iii), (BE-127)(i)/(ii)/(iii), (CH-1) — all landed. **What is
> refuted**: `(∗)` **as a condition available at `dim A ≥ 5`**; and the
> `dim A` half of (BE-127)(ii)'s comparison sentence, plus
> `notes/Phase39.md` *Hand-off* item 0(a)'s **"subsumes"**. **What is NOT
> refuted**: `PencilPair K 3 G`; `hbareSplit`; (BE-14); half (B);
> (BE-127)(i); (BE-116); (BE-119)(i); (PENCIL-SATURATES-CHART) itself at
> side-degree `≥ 2`, which stays **OPEN**; **any** landed measurement.
> **Not a PENCIL event.**

### Verdict, classification, and the price

- **HIT shape 1 — `(∗)` is DECIDED, in closed form.** `(∗)` ⟺ one dimension
  count and two incidence exclusions ((BE-129)(iii)); no quantifier over
  the line survives.
- **HIT shape 2 — a REFUTATION with a stratum, not a witness.** `(∗)` is
  **false at every configuration with `dim A ≥ 5`** ((BE-130)(i)), and
  there the reduction it certifies is **vacuous** ((BE-130)(ii)).
- **HIT shape 3 — the stratum is INHABITED GENERICALLY.** 14 of 27
  chart-legal `deg_i(x) = 2` topologies have generic `dim A ≥ 5`
  ((BE-133)(iii)), and 109 of the 140 such rows have `ρ_i ≤ 5`, so the
  clause is not vacuous there ((BE-133)(iv)).
- **HIT shape 4 — the arc's own certificate is re-classified.** 91/91 is a
  **corollary of a theorem**, not evidence ((BE-132)(ii)); the blindness is
  total, and it is a *second* blindness on top of the F13-disclosed one.
- **HIT shape 5 — a surface disagreement SETTLED, both surfaces corrected.**
  The gap-map row's two items are **one** item; the *Hand-off*'s "subsumes"
  is **false** ((BE-130)(iii)).
- **A partial result, not a full one — say so.** `(∗)` is **proved** on
  `dim A ≤ 2` ((BE-131)(i)) and holds off two proper-closed degeneracies at
  `dim A = 3`; the direction therefore *proves* the condition on the
  stratum the arc has actually sampled, and *refutes* it on the stratum it
  has not.
- **NOT HIT** — **(PENCIL-SATURATES-CHART) at side-degree `≥ 2` is still
  OPEN.** `(∗)` is sufficient, not necessary; its failure kills the route,
  not the clause, and **0 of 270** rows violate the clause.
- **The price, stated as a price.** **(a)** The refutation is of a
  **sufficient condition**; a successor must still decide the clause.
  **(b)** The whole of `reach` is `deg_i(x) = 2` — `k ≥ 3` is
  **unsampled**. **(c)** Every core in `reach` is a **TREE**; a core
  carrying a cycle is unsampled, and (BE-133)(iii)'s semicontinuity
  argument is stated only for trees. **(d)** The composites are
  constructed — one skeleton (`K₃,₃`), one branch profile (all 3s), 27
  sides — and every "N/N" is a statement about them under seed `20260902`.
  **(e)** (BE-134)(ii)'s bad-plane witnesses are **abstract**: no chart
  point is exhibited that puts `π_{c₁}` on one, and none is claimed.
  **(f)** Everything downstream of (CH-1)/(CH-2) inherits their
  **proven-informally** status. **(g)** Exact ℚ only; the proofs are
  characteristic-free (they use only rank arithmetic and the Segre/Klein
  incidence geometry), the numerics are not.

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py classify   #    0.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py five       #    1.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py low        #    2.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py pop        #   30.8 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py reach      #   24.6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py fibre      #    0.0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bline.py validate   #   59.1 s (all six)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single
seed is `20260902` (`bunif.SEED`), printed by every mode; `validate` fits
the 600 s foreground budget comfortably. **Every headline is an `assert`,
and each headline's own driver is named:** the classification as an **iff**
against the brute-force reading of `(∗)`, in **both** its forms, at 140
random pairs and 48 constructed degeneracies (`classify`); `(∗)` failing at
60/60 draws with `dim A ≥ 5` and the reduction asserted vacuous at
2 400/2 400 sampled `p_x` (`five`); `(∗)` holding at 200/200 draws with
`dim A ≤ 2` **with its mechanism asserted**, and 16 constructed dim-4
failures (`low`); (BE-127)(iii)'s 91 rows reproduced and **each row's
deciding clause asserted to be a theorem** (`pop`); (CH-1) asserted at
27/27 composites, `rank R_core = 5|E|` asserted at every row, (BE-114)(iv)
re-asserted on the new topologies, and `(∗)` failing at 142/270 (`reach`);
12 constructed `(∗)`-holding bad planes asserted bad pointwise (`fibre`).

**Where each headline's own sampler can and cannot see** (`RESEARCH-ARC.md`
§4's sharpening, applied to this direction's own drivers):

1. **`classify` / `five` / `low` draw `A` uniformly from integer
   coordinates in `[−9, 9]`.** That support **misses every degeneracy**,
   all of which are proper closed — which is why the failing side of the
   classification is carried by **constructed** objects (48 + 16) and not
   by draws. A random draw failing would be the surprise; a random draw
   holding certifies nothing about the closed strata.
2. **`pop` reuses (BE-127)(iii)'s support verbatim, on purpose** — same
   library, same seeds, same sampler — because the claim is *about* that
   population. Its blind spot is (BE-132)(iii)'s: it varies the
   configuration, never the core length.
3. **`reach` varies exactly the axis `pop` holds fixed** — core length —
   and holds fixed what `pop` varied. It samples `deg_i(x) = 2` only,
   cycles of length 4/5/6, tails of length 1..6, two attachment positions,
   tree cores only, `K₃,₃`-with-3s as side 2.
4. **`fibre` samples nothing that matters**: it is a construction, and the
   only claim it supports is an existence claim about `(A, L_c, π)`.

### Caps, disclosed rather than smoothed — with the denominator named

1. **(BE-129), (BE-130), (BE-131)(i)/(ii)/(iii) and (BE-133)(iii) need no
   cap** — they are proofs; the driver can only falsify them.
2. **`dim A ≥ 5` is FOUND, not "not found"** — 140 of 270 rows, generic at
   14 of 27 topologies. This is the one place in the section where the cap
   language runs the *other* way, and the claim is correspondingly strong.
3. **The clause's own violation is NOT FOUND under this cap** — 0 of 270
   rows have `Π_x ⊆ ρ̄_i` with `ρ_i ≤ 5`. Never *"cannot happen"*.
4. **`k ≥ 3` is unsampled**; every `reach` row has `deg_i(x) = 2` exactly.
5. **Non-tree cores are unsampled**, and (BE-133)(iii) is stated for trees.
6. **Only the lexicographically first retained pendant edge `c₁` is
   exercised**, inherited from (BE-127)(iii) unchanged; `L_c` is always
   `p_{c₁} ∨ p_{c₂}` for the first two neighbours in sort order.
7. **Everything inherits `bearcase.sample_piece_config`'s shape guard** and
   `bpeel.rnode_shaped`'s disclosed stand-in, unchanged from BSIGMA,
   BPROPER and BOPEN.

### Harness note — `w4/bline.py`, and a `bimage` truncation trap worth recording

`w4/bline.py` imports `bopen`, `bproper`, `bsigma`, `bsatur`, `bunif`,
`bdecor`, `bpeel`, `bimage` and `exactcore` read-only and reimplements none
of them: no `ρ̄`, no sampler, no planter, no peel constructor, no
`sat_locus`. It **adds one consumer** to `bproper.composite`,
`bproper.core_of` and `bproper.degx_library` (their third) and the **first**
to `bopen.sat_locus`; no move-down is made, for BOPEN's own recorded reason.

**A trap, recorded because it is silent.** `bimage.pt_in` is a `K⁴` helper —
its comprehension is `for k in range(4)` — so calling it on a subspace of
`Λ²K⁴` **silently truncates every row to its first four coordinates** and
returns a vector in the wrong space, with no assert firing anywhere. It bit
twice while this driver was written (two constructed-witness modes returned
0 witnesses rather than failing). `bline.sub_pt` is the widened version and
carries the warning in its docstring; a `Λ²`-side draw must not go through
`pt_in`. This is a **new, unpaid** harness-debt item: the right fix is a
width parameter on `pt_in` itself, which would touch every consumer and
re-baseline their figures, so **no move made**.

**No divergence is created.** `bline.classify`, `bline.beta_locus`,
`bline.half_one`/`half_two` and `bline.longcore_library` are new devices,
not variants of existing ones; `half_one` **calls** `bopen.sat_locus`
rather than reimplementing it.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-129)(i) the fibre dimension in `V` | **PROVED** (the `z`-component is free in `Σ_t`) |
| (BE-129)(ii) the ruling case analysis | **PROVED** (Segre quadric; degree-2 divisor on a line) |
| (BE-129)(iii) the compact form | **PROVED**; asserted equivalent to (ii) and to `(∗)` at 140 + 48 |
| (BE-130)(i) `dim A ≥ 5 ⟹ ¬(∗)` | **PROVED** (hyperplane count), 60/60 |
| (BE-130)(ii) the reduction is vacuous there | **PROVED**, 2 400/2 400 |
| (BE-130)(iii) the two surfaces reconciled | **PROVED** from (i); a documentation correction, no measurement moves |
| (BE-131)(i) `dim A ≤ 2 ⟹ (∗)` | **PROVED**, mechanism asserted 200/200 |
| (BE-131)(ii) `dim A = 3`, two degeneracies | **PROVED**; both **CONSTRUCTED**, 48/48 failing |
| (BE-131)(iii) `dim A = 4`, one incidence | **PROVED**; 16 constructed failures |
| (BE-132)(i) the population reproduced | **MEASURED**, 91 rows, figures exact |
| (BE-132)(ii) 91/91 is a corollary | **PROVED**; asserted row by row |
| (BE-132)(iii) the support diagnosis | **READING**, grounded in the library's own shapes |
| (BE-133)(i) 27 chart-legal topologies | **MEASURED**; (CH-1) asserted 27/27 |
| (BE-133)(ii) `(∗)` fails at 142/270 | **MEASURED** |
| (BE-133)(iii) failure is GENERIC at 14/27 | **PROVED** (tree core ⟹ lower semicontinuity), rank asserted 270/270 |
| (BE-133)(iv) the clause is not vacuous there | **MEASURED**, 109 of 140 |
| (BE-133)(v) no clause violation found | **MEASURED**, 0/270 — *not found under this cap* |
| (BE-134)(i) no sweep lemma at `k ≥ 2` | **READ AT SOURCE**; (BE-124)(i)'s own hypothesis |
| (BE-134)(ii) `(∗)` permits a bad plane | **CONSTRUCTED**, 12, asserted pointwise |
| (BE-134)(iii) the confined fibre is reachable | **MEASURED**, 90 rows on (CH-1)-legal composites |
| (BE-135)(ii) the reading | **SPLIT** — premise and conclusion CONFIRMED, middle inference REFUTED |

### What would change this

- **A proof that `dim A ≤ 4` at every `deg_i(x) ≥ 2` terminal of an
  internal R-node peel.** That would resurrect `(∗)` as a live condition —
  and (BE-133) says it would have to contradict 14 chart-legal topologies,
  so it would have to be a statement about which peels the *induction*
  actually presents, not about sides in general.
- **A sharper reduction at `k ≥ 2` that does not discard `xc₂, …, xc_k`.**
  (BE-133)(iv)'s `(dim A, ρ_i)` census says the discarded edges are worth
  1 to 3 dimensions, which is exactly the gap between the dead route and a
  live one. **This is the named successor.**
- **A `p_x`-sweep lemma at `deg_i(x) ≥ 2`** ((BE-134)(i)), with the
  fibre's dimension tracked (`𝔸³` / plane / line) and the fibre-relative
  properness statement ((BE-134)(ii)).
- **A chart point putting `π_{c₁}` on one of (BE-134)(ii)'s bad planes** —
  that would upgrade the second gap from *not excluded* to *realized*.
- **A row with `Π_x ⊆ ρ̄_i` and `ρ_i ≤ 5`** — still unexhibited, now after
  270 further rows, and it would be a far bigger event than anything here.
- **A defect in (CH-1) or (CH-2)**, on which everything here stands.

## TERMINATION check (E1/E2/E3) — read at source, decided explicitly

Read at `notes/pencil/fanout-archive.md` (the ledger's own statement, not by
analogy), each decided:

- **(E1)** — *a g-flank: a `D = 0` shape whose every admissible colouring is
  binding, refuting per-shape (GR-15)*. **DOES NOT FIRE.** This direction is
  on the `(K-bare)` line and exhibits no colouring object at all; (GR-15) is
  untouched.
- **(E2)** — *the target is refuted or unprovable-as-posed **and** no ledger
  entry is left open-with-a-named-dispatchable-attack*. **DOES NOT FIRE**,
  on the second conjunct: what is refuted is a **route**, not the target,
  and the residue — the exact reduction at `k ≥ 2` ((BE-133)(iv)) and the
  sweep lemma ((BE-134)(i)) — is a named, dispatchable attack.
- **(E3)** — *the target is **proven** and every remaining ledger entry is
  adjudication-gated rather than dispatchable*. **DOES NOT FIRE**: nothing
  is proven that was open, (BE-14), `hbareSplit` and `hK` are untouched,
  and dispatchable entries remain.

**Per the "otherwise" clause the natural next step is a further direction**;
this landing does not prep one. See `notes/Phase39.md` *Hand-off*.
