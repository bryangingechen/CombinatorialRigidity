## §(K-bare-ext) — continuation (direction BSIGFOUR, ordinal 118, 2026-09-13)

**The question.** *Is a forced coincident-flag peel at `Σδ ≥ 4` inhabited?*
(BE-311)(ii) (owning section BCOFLAG) states it as the arm's kill condition
and records that it was **not tested**, because BONEONE's generator is
`δ = (1,1)` by construction. The entry arrived with its derivation attached
and needed only a population.

**Verdict in one line.** The region **IS inhabited** — `486` forced peels at
`Σδ ≥ 4` under this direction's cap, where the corpus had `0` — but the
**confinement fails at every one of them**, so the kill condition is **not
found under cap**, not met and not refuted. On the way, the landed
`[PROVED]` clause the spec's own predicted mechanism rested on,
**(BE-77)(ii) (owning section BSPREAD), is REFUTED** by an exhibited
`n = 12` witness with an all-hinge-pair derivation.

Baseline `HEAD` for every figure: `5a67660b`. Driver:
`notes/scripts/w4/bsigfour.py` (new; modes `fence`, `widen`, `theory`,
`blame`, `rand`, `w9alt`).

---

### *Step BE323* — **(BE-324): (BE-77)(ii) is REFUTED, and the defect is one dropped membership**

> **(BE-324)(i)** `[REFUTED]` *(witness exhibited and re-derived with the
> LANDED oracles; this is the clause the round's predicted mechanism rests
> on)* (BE-77)(ii) (owning section BSPREAD, `[PROVED]`) reads: *"Suppose
> `π_u = π_v` is forced at such a peel and **both sides are flexible**,
> `δ₁, δ₂ ≥ 1`. Then **`δ₁ = δ₂ = 1`**."* **That conclusion is false.**
> **The witness.** Side 1 is `boneone.rside((1,1,1,6,1))` — `WIT11`'s own
> `K₄`-skeleton R-node side, 9 vertices, `(f,g,δ) = (1,0,1)`. Side 2 is the
> 5-vertex side
> `{b₀b₁, b₀b₂, b₀u, b₁v, b₂u}`, `(f,g,δ) = (2,0,2)`. Their glue has
> **`n = 12`, `m = 15`, `u ≁ v`, `deg u = 4`, `deg v = 3`**, side 1
> **R-node-shaped**, and **`bpeel.pair_forced(G, u, v)` is `True`** — the
> landed predicate, not a re-implementation. `btwocut.deltas_at(G, u, v,
> check=True)` returns `f₁ = 1, g₁ = 0, f₂ = 2, g₂ = 0`, i.e.
> **`(δ₁, δ₂) = (1, 2)`**, both sides flexible. `Σδ = 3 ≠ 2`.
> **It is not a `pair_forced` over-claim.** `bgenuine.forced_seed` returns
> seed `C` with the **all-hinge-pair** derivation
> `admit D on {C,D,u} · admit u on {C,D,u} · admit b₀ on {b₀,b₂,u} ·
> admit v on {C,b₁,v}` — every step passes `bgenuine.hinge_pair`, which is
> (BE-84)(i)'s genuineness hypothesis. **And it is not a single accident:**
> over the widened generator the `(1,2)` forced rows number **96** and
> **96 / 96** carry an all-hinge-pair derivation; the `(2,1)` rows number
> **276**. Driver `bsigfour.py widen` (control line) and `blame`.

> **(BE-324)(ii)** `[PROVED]` *(**where** it breaks — one sentence of
> (BE-77)(i)(c), and it is a set-membership, not a rank or a draw)*
> (BE-77)(i)(c) says *"`A ∩ V(H₂)` evolves **exactly** as the `H₂`-run
> seeded at `u`"* and (ii)'s Step 1 uses *"`A₂` starts at exactly
> `N_{H₂}[u]`"*. **Both drop the terminals' own membership in `A`.** `A` is
> a union of **closed stars** of admitted hubs, and `u, v ∈ V(H₁) ∩ V(H₂)`,
> so `A_i := A ∩ V(H_i)` acquires a terminal as soon as **any** admitted hub
> **on either side** is adjacent to it — with no admission, and with no step
> crossing the cut. Three consequences, in order of damage:
> — **(a)** (BE-74)(ii)'s per-side induction is no longer available: a side-`i`
> vertex `w ∉ B_i` can be admitted on two witnesses from `B_i ∪ N(B_i)`
> ((BE-74)(i)'s cap) **plus the imported terminal** — exactly three.
> — **(b)** Step 2's `c_i := |N_{H_i}[v] ∩ A_i| ≤ 2` is read off (BE-74)(i),
> which bounds the count on `B_i ∪ N(B_i)`, **not** on `A_i`; the equality
> case `{v, b_i}` can therefore be realized with `b_i ∈ N(B_i) ∖ B_i`.
> — **(c)** Step 3 then has **no `[v]`–`B_i` edge to merge along**, and
> `δ_i ≤ 1` does not follow.
> **Verified mechanically at the witness** (`bsigfour.py blame`): side 2 has
> a **unique** optimal partition `{b₁} · {u,b₀,b₂} · {v}` of value `2 = f₂`,
> so `B₂ = {u,b₀,b₂}`; `B₂ ∪ N(B₂) = {u,b₀,b₁,b₂}` **does not contain `v`**;
> `v` has **no** neighbour in `B₂` (its only side-2 neighbour is `b₁`); and
> yet `A₂ = {u,v,b₀,b₁,b₂}` and `c₂ = |{v,b₁} ∩ A₂| = 2`. The `v` is
> imported from side 1 at the seed itself — `C ∼ v` in `H₁`, so `v ∈ N[C] ⊆
> A` before any terminal is admitted.
> The brute-force partition enumerator is asserted against
> `kbare_common.exact_deficiency` at every side it scores.

> **(BE-324)(iii)** `[PROVED]` *(**what is NOT touched** — priced with
> `--cited-by`, because a refutation that over-reaches is worse than none)*
> First, **(BE-74)(i) and (ii) are untouched and remain theorems.** (BE-74)(ii) is
> a statement about the closure of **one** graph against an optimal
> partition of **that** graph; applied to the glued `H` it still gives
> `fam(h) ⊆ [h]` and `δ_{uv}(H) = 0`, hence `Σδ ≤ 6` at every forced peel.
> What (BE-77) does is **apply it to a side**, where the run is not the
> side's own run. Likewise **(BE-77)(i)(a) and (i)(b) stand** (the first
> terminal's certificate is one-sided — asserted at `39 736 / 39 736` and
> untouched here); only **(i)(c)'s "exactly"** and **(ii)'s conclusion**
> fall. `python3 notes/ledger.py --cited-by '(BE-77)(ii)'` lists **8**
> claims; the two that actually consume the refuted conclusion are
> both **(BE-77)(iii)** and **(BE-73)(iii)'s first CORRECTION** — see
> (BE-330).

---

### *Step BE324* — **(BE-325): what survives, and the repair is CONDITIONAL**

> **(BE-325)(i)** `[PROVED]` *(the certificate shape survives, in the
> OPEN-neighbourhood form — and it needs a hypothesis (BE-77)(ii) thought it
> had proved)* Write `c_i′ := |N_{H_i}(v) ∩ A_i|`, the **open**
> neighbourhood count at the second terminal. **If** `A_i ⊆ B_i ∪ N(B_i) ∪
> {u, v}` on both sides — Step 1's containment, *plus* the cross-cut import
> — **then** `c_i′ ≤ 1` on every side with `δ_i ≥ 1`: by (BE-74)(i), if `v`
> has a neighbour `b ∈ B_i` then `N[v] ∩ (B_i ∪ N(B_i)) = {v,b}` and the
> only open element is `b`; if `v` has no neighbour in `B_i` then
> `|N[v] ∩ (B_i ∪ N(B_i))| ≤ 1` and `v` is not itself in that set, so the
> one element is again open. Since the two sides overlap only in `v`
> (`u ≁ v`), the admission threshold `3 ≤ [v ∈ A] + c₁′ + c₂′ ≤ 3` forces
> **`v ∈ A` and `c₁′ = c₂′ = 1`** — the `{v, b₁, b₂}` shape (BE-77)(ii)
> claims, **with no claim that `b_i ∈ B_i`**, which is precisely the step
> that carried the `δ_i ≤ 1`. ∎

> **(BE-325)(ii)** `[MEASURED]` *(the hypothesis of (i) is **not** free, and
> the driver says how often — `bsigfour.py blame`)* Exhaustive over the cell
> `n₁ = 9`, `n₂ ∈ {4,5}` of the widened generator (brute-force optimal
> partitions need `n ≤ 9`), one forced seed per peel, **3 470** flexible
> side-instances: | reading | count | |---|---| | Step-1 containment
> `A_i ⊆ B_i ∪ N(B_i)` holds for some optimal partition | **2 784** | | it
> fails, and the **only** excess is the imported terminal | **628** | | it
> fails **deeper** than the imported terminal | **58** | and the `{v,b₁,b₂}`
> certificate of (i) **holds at 314 and fails at 46** of the both-flexible
> peels, the 46 being rows with `c_i′ = 2` (28) and `c_i′ = 3` (18) at
> `δ_i = 1`. **So (i) is a conditional theorem and its hypothesis is
> violated in this population** — `c_i′ = 3` at `δ_i ≥ 1` is impossible
> under (i)'s hypothesis, so those 18 rows are a direct witness that the
> containment fails. **Reported as a refutation of my own first repair**,
> which asserted `c_i′ ≤ 1` unconditionally before this mode was run.

> **(BE-325)(iv)** `[REFUTED]` *(witness: `bsigfour.py theory`'s census —
> **and the refuted claim is THIS DIRECTION'S OWN**, which is why it is
> stated before the board)* Two claims, both tested over the widened
> generator's forced peels, both **false**: **Claim A**, which is
> (BE-77)(ii) *Step 2* read literally — *"`δ_i ≥ 1 ⟹ c_i ≤ 2`"* with `c_i`
> the **closed** count on `A_i` — has **984** counterexamples, e.g. the
> `(δ₁,δ₂,c₁,c₂)` rows `(1,1,3,2): 376` and `(1,0,3,3): 48`. **Claim B**,
> this direction's own first sharpening — *"`δ_i ≥ 2` at a forced peel
> forces `δ_{3−i} = 0`"*, derived by reading Steps 1–3 one side at a time
> before any measurement — has **1 404** counterexamples, every `(1,2)` and
> `(2,1)` row. **I derived Claim B from (BE-77)(ii)'s proof, believed it,
> and it died to the same defect the parent clause died to**: any reading
> that inherits Step 1's containment inherits its falsity. *(Disclosed cap:
> `theory` reads the second terminal off the recorded trace, so peels whose
> **seed is itself a terminal** contribute no row — the trace records only
> admissions.)*

> **(BE-325)(iii)** `[OPEN]` *(what an unconditional successor would have to
> do, stated so the next direction does not re-derive it)* A successor to
> (BE-77)(ii) must carry the **import cascade**: the imported terminal
> raises every side-`i` vertex's witness count by one, which can admit a
> vertex outside `B_i`, which enlarges `A_i`, which can import more. The
> question *"does forcing bound `Σδ`?"* is therefore **open below `6`** —
> `Σδ ≤ 6` is all that survives, from (BE-74)(ii) at the **whole** graph,
> and it is consistent with the `(4,0)` and `(0,4)` rows measured in
> (BE-326). **This is the honest replacement for the spec's predicted
> mechanism.**

---

### *Step BE325* — **(BE-326): the region IS inhabited — the widened generator**

> **(BE-326)(i)** `[MEASURED]` *(the instrument (BE-311)(ii) itself names,
> built: `bsigfour.py widen`)* (BE-311)(ii) reads *"A `(δ₁, δ₂)`-widened
> generator is the cheapest next instrument"*. `boneone.k4_rsides` and
> `boneone.free_sides` each end in `if side_delta(E)[2] == 1`; this
> direction re-runs the **same** enumeration with that filter as a
> parameter, importing `boneone.rside`, `boneone.side_delta`,
> `boneone._comps` rather than copying them. **Mode `fence` is the
> figure-invariance test:** at `δ = 1` the widened pools reproduce
> `k4_rsides(9) = 12`, `k4_rsides(10) = 40`, `free_sides(4) = 4`,
> `free_sides(5) = 60` **element for element, 4 / 4 pools identical**. So
> every figure below differs from BONEONE's by the `δ` filter and nothing
> else. **And the factorization itself is re-asserted outside its own
> `δ`:** (BE-79)(i) is asserted in BONEONE at `400 / 400` glued pairs
> **every one of which is at `δ = 1`**, and the whole widened hunt depends
> on `δ_i` and `rnode_shaped` staying per-side at `δ ≠ 1`. Re-run here at
> **`600 / 600`** seeded glues spanning **21** `(δ₁,δ₂)` cells including
> `(0,4)`, `(1,4)`, `(2,4)`, `(3,4)`, `(4,0)`, `(4,1)` and `(3,3)`:
> `btwocut.deltas_at(G, u, v, check=True)` agrees side-for-side with each
> side's own `side_delta`, **0 disagreements**. *(This was a soundness gap
> in this direction's own instrument, found by asking what `deltas_at` was
> still doing in the imports after a refactor removed its only call.)* *(The permanent fix is a `delta=1` keyword on both landed functions;
> it is not made here because this direction commits nothing to shared
> files.)*

> **(BE-326)(ii)** `[MEASURED]` *(**the answer to the question**: the region
> is inhabited, and the corpus's silence was its generator)* Pools: **1 287**
> `K₄` R-node sides, exhaustive over every branch profile at
> `n₁ = 4…12`; **172** free sides, exhaustive at `n₂ = 4, 5`. Glued both
> ways round, R-node shape required on at least one side — **221 364** legal
> peels. | | | |---|---| | at `Σδ ≥ 4` | **15 162** | | forced
> (`bpeel.pair_forced`) | **114 234** | | **FORCED at `Σδ ≥ 4`** |
> **486** | | forced **and** confined on both sides at `Σδ ≥ 4` | **0** |
> The `(δ₁,δ₂)` profile of the forced: `{(0,0): 46500, (0,1): 10372,
> (0,2): 276, (0,3): 12, (0,4): 36, (1,0): 38468, (1,1): 6036, (1,2): 96,
> (2,0): 9012, (2,1): 276, (3,0): 2700, (4,0): 450}`. **So (BE-311)(ii)'s
> "not found under cap `Σδ = 2`" is now "found": `486` forced peels at
> `Σδ = 4`.** The first `Σδ ≥ 4` forced peel appears at `n = 13`
> (`n₁ = 12`, `n₂ = 4`) on the `(4,0)` row and at `n = 12` (`n₁ = 9`,
> `n₂ = 5`) on the `(0,4)` row.

> **(BE-326)(iv)** `[MEASURED]` *(the smallest one, printed in full — and
> it is SEVEN vertices; `bsigfour.py widen`)* Side 1 is `rside((1,1,1,1,1))`
> = **`K₄` minus `uv`** on `{u, v, C, D}` (edges `CD, Cu, Cv, Du, Dv`),
> `(f,g,δ) = (0,0,0)`, **R-node-shaped**. Side 2 is the **path**
> `u – b₂ – b₀ – b₁ – v`, `(f,g,δ) = (4,0,4)`, `dist = 4`. The glue has
> **`n = 7`, `m = 9`**, `u ≁ v`, `deg u = deg v = 3`, and is **forced** with
> seed `C` on an **all-hinge-pair** derivation, `A = {C, D, b₁, b₂, u, v}`.
> `Σδ = 4`. **The confinement holds on side 1 (the path `u–C–v`, length 2)
> and fails on side 2**: `b₀`, the middle of the geodesic, has degree `2`
> and sits at distance `2` from both terminals, so no admitted hub's closed
> star contains it. **This one graph is the whole finding in miniature** —
> the region is inhabited, trivially so, and the confinement is what is
> scarce.

> **(BE-326)(v)** `[MEASURED]` *(**F34: the corpus already held the answer,
> filed under a different question**; `bsigfour.py widen` + (BE-73)(iii)'s
> own numbers)* `n = 7` is **inside BPEEL census 1's range** (`n ≤ 8`,
> exhaustive at `n = 5, 6`). (BE-73)(iii) reports that census as *"5 704
> with `π_u = π_v` forced … 3 352 R-node-shaped"* and totals **"3 497 forced
> R-node-shaped peels, every one with `min(δ₁, δ₂) = 0`"**. **That
> population is exactly this region**, and its `Σδ` was never tabulated —
> the census asked *"are both `δ` positive?"*, a question about `min`, and
> `Σδ ≥ 4` lives entirely inside the `min = 0` complement it discarded. So
> the honest reading of *"the corpus has never drawn a forced peel at
> `Σδ ≥ 4`"* is **not** that the corpus looked and found none: **every
> census that could have found one reported the wrong statistic**. The
> `(1,1)`-only generator of (BE-79)(i) is the *second* fence, not the first.

> **(BE-326)(iii)** `[MEASURED]` *(`bsigfour.py widen`; the **other** half of the
> dispatch's "equally decisive in the other direction", settled
> **negatively**)*
> (BE-311)(ii)'s alternative was *"prove that forcing at a peel with
> `Σδ ≥ 4` is impossible, and rung 3 is the whole of the coincident-flag
> arm"*. **That route is now CLOSED BY COUNTEREXAMPLE**, not merely
> unproved: 486 of them. The spec's hypothesis that (BE-77) would supply
> such a proof is refuted twice over — by (BE-324) at the level of the
> clause, and here at the level of the population.

---

### *Step BE326* — **(BE-327): `δ_i ≤ dist_i`, unconditionally and combinatorially**

> **(BE-327)(i)** `[PROVED]` *(removes (BE-30)(iv)'s attainment proviso on
> the `δ` half, and it is the lemma the confinement question turns on)*
> For any side `(H_i, u, v)`, **`δ_i ≤ dist_{H_i}(u, v)`**, with no
> genericity, no configuration and no attainment hypothesis. *Proof.* The
> functional `kbare_common.exact_deficiency` maximizes is
> `value(P) = 6(|P|−1) − 5 d(P)` over partitions `P` of `V(H_i)`, `d(P)` the
> number of cross edges; `f_i` is its maximum and `g_i` its maximum over
> partitions with `u, v` together. Fix an optimal `P` and a shortest `u–v`
> path `Q` of length `k = dist_i`. Merge, one at a time, the distinct blocks
> `Q` meets, in path order. Each merge joins two blocks connected by at
> least one edge of `Q`, so it changes `value` by `−6 + 5e ≥ −1` where
> `e ≥ 1` is the number of edges between them. `Q` meets at most `k + 1`
> distinct blocks, so at most `k` merges are made and
> `g_i ≥ value(P) − k = f_i − k`. ∎ **Compare (BE-30)(iv)** (owning section
> BIMAGE), which gives `ρ_{uv} ≤ dist` unconditionally but `δ_{uv} ≤ dist`
> only *"at a configuration where `H` and `H/uv` attain"*; the proviso is
> unnecessary for the `δ` half. **Checked at `228 468` side-readings of the
> widened generator's forced peels — two per forced peel, `114 234` of
> them: `0` violations** (`bsigfour.py widen`,
> the `(δ_i, dist_i, path)` table — every row has `δ_i ≤ dist_i`).

> **(BE-327)(ii)** `[MEASURED]` *(`bsigfour.py fence` + `widen`; the consequence
> that makes the hunt hard, and it is a **structural tension**, not a cap)* `δ_i ≥ 4` forces
> `dist_i(u,v) ≥ 4`, so the confining `u–v` path has `≥ 3` interior
> vertices; but every vertex of a confining path must lie in the **closed
> star of an admitted hub**, and admitted vertices have degree `≥ 3`. In the
> widened generator the two demands are incompatible at `δ_i ≥ 4` for a
> structural reason the driver prints: **every** `K₄` R-node side at
> `δ = 4` (`n₁ = 12`, 6 profiles) has degree sequence `[2¹⁰, 3, 3]` and
> `dist ∈ {5, 6}` — only the two skeleton hubs have degree `≥ 3`, and a
> path of length `5` cannot be covered by `4` closed stars; and **every**
> free side at `δ ≥ 4` in the exhaustive `n₂ ≤ 6` enumeration is a **bare
> path** (`δ = 4` at `n = 5`: 6 sides, `0` interior hubs; `δ = 5` at
> `n = 6`: 24 sides, `0` interior hubs; there is **no** `n₂ = 6` side at
> `δ = 4` at all), whose interior vertices at distance `≥ 2` from both
> terminals can never enter `A`.

---

### *Step BE327* — **(BE-328): the kill condition — NOT FOUND under cap, with the cliff located**

> **(BE-328)(i)** `[MEASURED]` *(the headline, with F11's discipline: this
> is a **none-found**, and the denominator is **not** vacuous)* Of the
> **486** forced peels at `Σδ ≥ 4`, **`0`** carry a `u–v` path of **each**
> side inside the forced set `A` — (BE-310)(i)'s confinement hypothesis,
> tested with `bcoflag._path_in`, the same function `bcoflag.py conf` uses
> for the 392. **The 486 are exactly the objects (BE-311)(ii) asks about,
> they exist, and each was tested**, which is what the two vacuous zeros of
> (BE-80)(iii)/(iv) were not. **It reads "not found under cap
> `n₁ ≤ 12`, `n₂ ≤ 5`, `K₄`-skeleton R-node sides", never "does not
> occur".**

> **(BE-328)(ii)** `[MEASURED]` *(`bsigfour.py widen`; **which** side fails, and
> the failure is one-sided every time)* `((δ₁,δ₂), side 1 confined, side 2 confined)`:
> `((0,4), True, False): 36` and `((4,0), False, True): 450`. **In every one
> of the 486 the high-`δ` side is the one that fails** — never the `δ = 0`
> partner, and never both. So the obstruction is attached to the
> deficiency, not to the glue.

> **(BE-328)(iii)** `[MEASURED]` *(`bsigfour.py widen`; the cliff, per side, and
> it lands exactly where (BE-311)(i) does)* Over every forced row of the widened generator,
> per side, `(δ_i, dist_i, confining-path length or None)`: a confining path
> exists at `δ_i = 0, 1, 2, 3` and its length is **always exactly
> `dist_i`** — `(0,2,2), (0,3,3), (0,4,4), (1,2,2), (1,3,3), (1,4,4),
> (2,3,3), (2,4,4), (3,3,3), (3,4,4)` — and at `δ_i = 4` it is **`None` at
> `486 / 486`** (`(4,4,None): 36`, `(4,5,None): 300`, `(4,6,None): 150`).
> **Max `δ_i` with a confining path: `3`.** That is the same number
> (BE-311)(i) derives from the confinement (`H` attains `⟹ Σδ ≤ 3`), which
> is a coincidence worth naming rather than assuming: (BE-311)(i) bounds
> `Σδ`, this bounds `δ_i` **per side**, and the two would separate at a
> `(3,3)` peel. **`(3,3)` is tested `72` times in this generator and forced
> `0` times** — so the separating cell is **not found under cap** either.

> **(BE-328)(v)** `[MEASURED]` *(a **second, targeted** tier aimed at the
> exact structure (BE-327)(ii) says is missing — and a self-caught false
> positive; `bsigfour.py cover`)* `coverable(H_i)` is a **necessary**
> condition for the confinement that is a function of the **side alone**: at
> a forced peel `A` is a union of closed stars of admitted vertices, only
> hubs are admitted, and an interior vertex has the same degree in the side
> as in the glue — so `A ∩ V(H_i) ⊆ ⋃_{w ∈ K_i} N_{H_i}[w]` with
> `K_i = {u,v} ∪ {interior w : deg ≥ 3}`. Swept: **`0`** of the exhaustive
> free sides at `n ≤ 6` and **`0`** of the exhaustive `K₄` R-node sides at
> `n ≤ 12` are both `δ ≥ 4` and coverable — but a seeded random tier
> (`2 038` sides drawn at `n ∈ [7,10]`) produces **3**, at `n = 7` and
> `n = 8`, `δ = 4`, `dist ∈ {5,6}`. **Glued to all `634` partners** (every
> `K₄` R-node side at `n₁ ≤ 10`, every free side at `n₂ ≤ 5`, all `δ`):
> `1 500` legal peels at `Σδ ≥ 4`, **`132` forced**, **`0` forced and
> confined**. *Diagnosis, printed:* the covering interior hubs are **never
> admitted** — at the `n = 7` side, `A ∩ V(H₂) = N[u] ∪ N[v] = {C₁,C₂,u,v}`
> at every forced glue, and the two degree-`3` vertices `C₀, C₃` each need
> `3` of their closed star in `A` and have only `1`.
> **SELF-CAUGHT, and it would have been the headline:** the first run of
> this tier reported **`51` kill-condition hits**. The three sampled sides
> carry `boneone.free_sides`' own `'B'` vertex tag, so gluing them to a
> **free-side** partner silently **identified interior vertices of the two
> sides** — the "peel" was not a peel. Re-tagged and re-run with
> `set(V(H₁)) ∩ set(V(H₂)) == {u,v}` and
> `btwocut.deltas_at(..., check=True)` asserted at **every** glue: the count
> is **`0`**. The committed driver carries both assertions.

> **(BE-328)(iv)** `[MEASURED]` *(`bsigfour.py widen`; the F27 reading, stated
> because this is a failure claim)* Nothing in (i)–(iii) is a draw: `δ_i`, `pair_forced`, `A`
> and `_path_in` are **combinatorial** and the whole run is draw-free and
> deterministic, so F27's multi-draw obligation does not bind on these
> figures. **Where it would bind** is the step after a hit: `dim(ρ̄₁+ρ̄₂)`
> is **lower** semicontinuous ((BE-69)(i)), so a single draw is a **lower
> bound** — which is why (BE-311)(i)'s route is a *proof* (an **upper**
> bound `≤ 3` from the confinement) and not a measurement, and why a hit
> would need **no** repeated draws while a miss would prove nothing.

---

### *Step BE328* — **(BE-329): the blind axes, opened rather than quoted**

> **(BE-329)(i)** `[MEASURED]` *(`boneone.W9_ALT` — declared, read nowhere,
> and the reason turns out to be benign; `bsigfour.py w9alt`)*
> `blindaxes.py --imports notes/scripts/w4/boneone.py` reports `SEED =
> 20260901` (read at 3 sites), `WIT11_LENGTHS = (1,1,1,6,1)` (4 sites) and
> **`W9_ALT = (1,1,4,3,1)` — UNREAD**. Opened: `W9_ALT` is a second
> `n = 9` `K₄` R-node side at `def₃ = 1, g = 0, δ = 1`, R-node-shaped, and
> it carries **the same triangle** `{u, C, D}` as `WIT11_LENGTHS` (both have
> `ℓ_{uC} = ℓ_{uD} = ℓ_{CD} = 1`). So consuming it in place of
> `WIT11_LENGTHS` would **not** have moved (BE-85)(iii)'s girth histogram
> `{3: 392}` or its `0 / 392` (CH-1) row — and (BE-85)(iii) already proves
> the `n₁ = 9` column triangle-free at `0 / 12` over **all twelve**
> profiles, of which `W9_ALT` is one. **The axis is unread because it is
> redundant, not because it was suppressed.**

> **(BE-329)(ii)** `[MEASURED]` *(the axis that was NOT benign — and it is
> the one the spec pointed at)* The load-bearing fence is not a `SEED` or a
> `vmax`: it is `side_delta(...)[2] == 1` inside `k4_rsides` and
> `free_sides`, which `blindaxes.py` does **not** report because it is a
> comparison in a filter body, not a module constant or a keyword default.
> **The generator-shaped blind axis is invisible to the generator-shaped
> lister.** Recorded as a limitation of the instrument, not of the direction
> that used it: `(BE-311)(ii)` names the fence in prose, and that prose was
> the only surface carrying it.

---

### *Step BE329* — **(BE-330): the blast radius, priced**

> **(BE-330)(i)** `[REFUTED]` *(a **vacuity correction is itself void** —
> F11 running backwards, and it is the second time this clause family has
> taken one)* (BE-77)(iii) reads BPEEL's census 3 — *"24 874 R-node-shaped
> peels with both `δ` positive, 180 forced, 0 in the intersection"* — and
> concludes *"By (ii) the only shape a hit can take is `δ₁ = δ₂ = 1`, and of
> those 24 874 the number at `(1,1)` is 0. So the hunt had **0** chances"*.
> **With (BE-324), (ii) no longer licenses that denominator.** A hit can
> take the shape `(1,2)`, `(2,1)` or any `(δ₁,δ₂)` with `Σδ ≤ 6`, so the
> both-flexible R-node population is a live denominator again and census 3's
> zero is **a genuine none-found over 24 874, not a vacuous one**. The same
> correction voids the identical sentence inside **(BE-73)(iii)**'s first
> CORRECTION block. *Note the direction of the repair: it makes BPEEL's
> original non-vacuity check RIGHT again.* (BE-80)(iv)'s **second**
> correction — census 3 is structurally vacuous because every 2-cut of a
> subdivision has a path side whose `δ = min(L,6)` is never `1` — **also
> loosens**: `δ = min(L,6)` reaches `2,…,6` freely, so a path side is no
> longer disqualified once `(1,1)` stops being the only admissible shape.
> **What that tier's zero is worth is now an open measurement, not a
> vacuity.**

> **(BE-330)(ii)** `[PROVED]` *(what does **not** move — checked clause by
> clause with `--cited-by`, and the list is deliberately long)*
> First, **(BE-310) and (BE-311)(i) are untouched**: neither cites (BE-77), and
> (BE-310)(i)'s proof uses only (BE-30)(iv), (BE-16)(iii) and (BE-85)(i)/(ii)
> — **it does not mention `δ_i` anywhere**, so the spec's bar-*(q)* worry
> that *"(BE-310)'s confinement proof silently assumes `δ_i = 1`"* is
> **checked and false**: the proof is `δ`-free and applies verbatim at any
> `Σδ`. **(BE-86)(i)** is likewise unconditional in `δ`. **(BE-79)(i)** (the
> factorization) is untouched and is what makes the widened generator legal.
> Next, **(BE-84)(i)/(iv)** cite (BE-77) only for the certificate *shape*, which
> (BE-325)(i) preserves. **(BE-81)(ii)** reads `WIT11`'s derivation against
> (BE-77)(ii) *Step 2/3* — the Step-2 shape survives, the *Step 3* reading
> *"`b₁ = C` is `v`'s unique neighbour in side 1's `u`-block"* is now an
> observation about that instance rather than a consequence of a theorem.
> And **(BE-77)(i)(a)/(b)** stand.

---

### *Step BE330* — **(BE-331): the independent tier, and what the caps are**

> **(BE-331)(i)** `[MEASURED]` *(tier B — seeded random 2-connected graphs,
> because the factorized generator could itself be the fence;
> `bsigfour.py rand`)* Seeded (`SEED = 20260913`) random 2-connected graphs,
> `n ∈ [9,14]`, edge probability swept over `(0.22, 0.3, 0.4)`, **no
> max-degree filter** — BPEEL's census 1 carried one, which (BE-77)(iv)
> records as the reason its R-node peels were rigid on one side. Every 2-cut
> `{u,v}` with `u ≁ v` and both sides carrying an interior vertex; same
> three tests. **NOT exhaustive**, and its zero (if zero) is *"not found
> under cap `nrand`, `n ≤ 14`"*. **THIS MODE DID NOT COMPLETE under this
> direction's budget** — two runs were killed at the `560 s` / `590 s`
> harness ceiling with no output, because `rand` re-runs the deficiency
> oracle on sides of up to `12` vertices at every 2-cut. **No figure from it
> is quoted, provisionally or otherwise.** The committed driver has the
> redundant `deltas_at` call removed, `_peel_row` fed the per-side values it
> already has, and the defaults trimmed to `nrand = 400`, `n ≤ 12`, so the
> coordinator can run it in one foreground call. **Its absence is a real
> gap**: the exhaustive tier and the targeted tier are both built on the
> per-side factorization, and `rand` is the only tier that samples peels
> that were never glued from a pool.

> **(BE-331)(ii)** `[MEASURED]` *(every cap, in one place, because the
> deliverable is a none-found)* **(1)** R-node pool: `K₄` **skeleton only**
> — the prism and `K_{3,3}` skeletons `bpeel.SKELETONS` carries are **not**
> run; exhaustive over branch profiles at `n₁ ≤ 12`. A `K₄` side first
> reaches `δ = 4` at `n₁ = 12`. **(2)** Free pool: exhaustive at
> `n₂ ≤ 5` (`n₂ = 6` was enumerated for the `δ`-profile of (BE-327)(ii) but
> **not** glued). **(3)** `bpeel.pair_forced` over-claims (its own cap (2)),
> so a `True` is a candidate — which **strengthens** a none-found and
> weakens nothing here, and the `(1,2)` refutation is independently checked
> all-hinge-pair. **(4)** One forced seed per peel in `blame`; **all** seeds
> in `widen`'s confinement test, since different seeds give different `A`.
> — **(5)** `Σδ ≥ 4` is reached in this generator **only** as `(0,4)` and
> `(4,0)`; `(1,3)`, `(3,1)`, `(2,2)`, `(0,5)`, `(0,6)` and every `Σδ ≥ 5`
> shape is **tested and unforced**, `(3,3)` is tested `72` times — so the
> none-found covers `Σδ = 4` well and `Σδ ≥ 5` **barely**.

---

### *Step BE331* — **(BE-332): the board, and what would change this**

> **(BE-332)(i)** `[OPEN]` *(the kill condition, restated with what is now
> known)* **Exhibit a forced coincident-flag internal R-node peel with
> `Σδ ≥ 4` at which some `u–v` path of **each** side lies inside `A`.** The
> `Σδ ≥ 4` half is **done** (486 witnesses). The whole difficulty is now the
> **confinement**, and (BE-327) says where it sits: `δ_i ≥ 4 ⟹ dist_i ≥ 4`,
> while a confining path needs every one of its `dist_i − 1` interior
> vertices inside the closed star of an admitted degree-`≥ 3` vertex.
> **The next instrument is therefore a side generator that maximizes hubs
> along a long `u–v` geodesic at high `δ` — not a wider `(δ₁,δ₂)` sweep of
> the same two families**, which is what this direction ran and what the
> `[2¹⁰,3,3]` degree sequence shows is exhausted.

> **(BE-332)(ii)** `[PROVED]` *(the cheaper question this direction
> surfaced — **and it closed**; the answer is (BE-333))* *"Is `confined on
> side i ⟹ δ_i ≤ 3` a theorem?"* was raised here from the measured cliff at
> `δ_i = 3`. It is, and the proof is (BE-333)(ii). **The route that does
> NOT work is worth recording:** with `A_i ⊆ B_i ∪ N(B_i)` alone, merging
> `B_i` with every block the confining path meets costs `−6t + 5e` with
> `e ≥ 2t−1`, a **gain** for `t ≥ 2`, which would give `δ_i ≤ 1` —
> contradicting the measured `δ_i = 2, 3` confined rows. That argument
> over-counts because the containment it assumes is exactly the one
> (BE-324)(ii) refutes. (BE-333)(ii) goes through `R(H_i)` and the two
> blocks `[u]`, `[v]` instead, and never needs the containment.

> **(BE-332)(iii)** `[OPEN]` *(what would change this verdict — three
> things, in cost order)* **(a)** One side with `δ ≥ 4`, `dist = 4`, and an
> interior vertex of degree `≥ 3` on every `u–v` geodesic; the exhaustive
> `n₂ ≤ 6` free enumeration says none exists at `n ≤ 6`, and `n = 7` is
> `2²⁰` masks — a **seeded** `n = 7, 8` sweep is the cheapest next run.
> — **(b)** A non-`K₄` skeleton (prism, `K_{3,3}`) R-node side at `δ ≥ 4`:
> more hubs per vertex than `K₄`, which is exactly the axis (BE-327)(ii)
> says is starved. **(c)** A proof of (ii), which would close the
> coincident-flag arm at `Σδ ≤ 3` **without** a hit and make (BE-311)(i)'s
> bound tight from below.

> **(BE-332)(iv)** `[OPEN]` *(and the consumer question this direction does
> NOT answer)* Even a hit yields a shortfall that must **reach (BE-14)**.
> The spec routes that through (BE-69)(ii), and (BE-85)(iii) measures
> that **(CH-1)(a) is unavailable at `0 / 392`** of BONEONE's family — *"taking
> (BE-69)(ii)'s dense-or-empty dichotomy with it"*. Every member of the
> widened generator inherits the same triangle (the `K₄` R-node sides at
> `δ ≥ 1` all carry `{u,C,D}`), so **the (BE-69)(ii) route is unavailable at
> every witness this direction can build**, and a hit would land as a
> **pointwise** shortfall at an exhibited configuration, not as a statement
> about `Chart(H)`. **This is the same gap BSMARK (rank 1) is dispatched on,
> and it is not closed by anything here.**

---

---

### *Step BE332* — **(BE-333): the confinement caps `δ_i` at 3, per side and glue-independently**

> **(BE-333)(i)** `[PROVED]` *(the per-side upper bound on `A_i`, which no
> partner can beat — and it is what makes the rest a theorem rather than a
> sweep)* At a forced peel both terminals are admitted, so `u, v ∈ A`; an
> **interior** vertex `w` of side `i` has `N_H[w] = N_{H_i}[w]`, so it is
> admitted iff `|N_{H_i}[w] ∩ A_i| ≥ 3`; and `A_i := A ∩ V(H_i)` grows only
> by closed stars of admitted side-`i` vertices together with `u` and `v`
> themselves. Hence, for **every** partner, every seed and every admission
> order,
> `A_i ⊆ R(H_i) :=` the closure of `N_{H_i}[u] ∪ N_{H_i}[v]` under
> *"admit an interior `w` on `3` of its closed star"*, taken **inside
> `H_i`**. ∎ So (BE-310)(i)'s confinement hypothesis on side `i` implies a
> `u–v` path inside `R(H_i)` — a condition on the **side alone**.
> Driver: `bsigfour.side_reach`.

> **(BE-333)(ii)** `[PROVED]` *(**the bound**, from (BE-74)(i) alone)* If
> `δ_i ≥ 1` and `R(H_i)` contains a `u–v` path, then **`δ_i ≤ 3`.**
> *Proof.* Fix an optimal partition of `H_i`; `δ_i ≥ 1` puts `u, v` in
> different blocks `B := [u]`, `C := [v]`. Write `N(X)` for the
> `H_i`-neighbourhood. Throughout, merging a chain of `r + 1` blocks joined
> by `r` edges changes the partition value `6(|P|−1) − 5 d(P)` by
> `−6r + 5r = −r`, so a chain of length `r` from `B` to `C` gives
> `g_i ≥ f_i − r`, i.e. `δ_i ≤ r`.
> **Case 1: some admitted interior vertex lies outside `B ∪ C`.** Take the
> first such, `w`. Every earlier admitted interior vertex is in `B ∪ C`, so
> the set `R'` it was admitted against satisfies
> `R' ⊆ (B ∪ N(B)) ∪ (C ∪ N(C))`. Since `w ∉ B`, (BE-74)(i) gives
> `|N[w] ∩ (B ∪ N(B))| ≤ 2`, and likewise `≤ 2` on the `C` side; their sum
> is `≥ |N[w] ∩ R'| ≥ 3`, so **at least one side contributes `2`** — say the
> `B` side, whose equality case in (BE-74)(i) forces a neighbour `b ∈ B`, so
> `[w]` is adjacent to `B`. The other side contributes some
> `x ∈ N[w] ∩ (C ∪ N(C))`. If `x = w` or `x ∈ C`, then `[w]` is adjacent to
> `C` too and `B — [w] — C` is a chain of length `2`: `δ_i ≤ 2`. Otherwise
> `x ∈ N(w) ∩ (N(C) ∖ C)` and `B — [w] — [x] — C` is a chain of length `3`:
> `δ_i ≤ 3`.
> **Case 2: every admitted interior vertex lies in `B ∪ C`.** Then
> `R(H_i) ⊆ (B ∪ N(B)) ∪ (C ∪ N(C))`, since `N[u] ⊆ B ∪ N(B)`,
> `N[v] ⊆ C ∪ N(C)` and each admitted `w` contributes `N[w]` inside its own
> block's absorption. A `u–v` path inside `R(H_i)` runs from `u ∈ B` to
> `v ∈ C`; let `q` be its **first** vertex in `C ∪ N(C)`. If `q = u` then
> `u ∈ N(C)`, so `B` and `C` are joined by an edge and `δ_i ≤ 1`. Otherwise
> `q` has a predecessor `p` on the path, `p ∈ B ∪ N(B)` by the covering and
> `p ∉ C ∪ N(C)` by firstness; `[p]` is `B` or adjacent to `B`, `[q]` is `C`
> or adjacent to `C`, and `p ∼ q`, so `B —[p]— [q]— C` (dropping coincident
> blocks) is a chain of length at most `3`. `δ_i ≤ 3`. ∎
> *(Both cases lean only on (BE-74)(i), owning section BSPREAD, `[PROVED]`,
> whose own measurement is `176 344` (block, outside vertex) pairs with `0`
> violations.)*

> **(BE-333)(iii)** `[MEASURED]` *(the bound checked where it is
> checkable — `bsigfour.py reach`)* Over **every** free side at `n ≤ 6`
> (exhaustive, `7 204` sides) and **every** `K₄` R-node side at `n ≤ 12`
> (exhaustive in branch profiles, `1 287` sides): **`0`** sides are both
> `δ ≥ 4` and `side_reach`. The largest `δ` with `side_reach` is **`3`** in
> both tiers (`50` free sides, `8` `K₄` sides), which is (ii)'s bound
> **attained**. The `δ ≥ 4` sides are `6 + 24` free and `6` `K₄`, all
> `side_reach = False`. **Two independent adversarial checks.** *(a)* A
> seeded random tier, `762` sides drawn at `n ∈ [7,9]` (`2 500` attempts,
> seed `20260913`): one `δ = 4` side, `side_reach = False`; largest `δ`
> with `side_reach` is `3`. **Exact invocation, because the mode's own
> defaults do not finish in one foreground call:**
> `run_reach(nsamp=2500, nlo=7, nhi=9, rcap=4, fcap=4)` — the
> `nsamp = 6000`, `n ∈ [7,11]` default run was killed at the harness
> ceiling and **no figure is quoted from it**. The two exhaustive tiers
> above are from the default `reach` run, which completes them before the
> random tier starts. *(b)* The **three `δ = 4` sides that pass the
> weaker `coverable` test** ((BE-328)(v), found at `n = 7, 8` by a random
> sweep and the only `δ ≥ 4` coverable sides this direction has) are
> **`side_reach = False` at 3 / 3** — the sharpest falsification available
> for (ii), aimed at it deliberately, and it holds.

> **(BE-333)(iv)** `[OPEN]` *(**what the arm is now worth**, and it is a
> small finite target)* (BE-333)(ii) plus (BE-311)(i) squeeze
> (BE-311)(ii)'s kill condition into **six** `(δ₁,δ₂)` cells:
> `(1,3), (3,1), (2,2), (2,3), (3,2), (3,3)` — both sides `≤ 3` by
> (BE-333)(ii), and `Σδ ≥ 4` by hypothesis. **This direction tests all six
> and forces none:** `1 020 + 2 304 + 2 160 + 240 + 648 + 72 = 6 444` peels
> in those cells, **`0` forced**. `(BE-77)(ii)` would have ruled the six out
> a priori; since it is refuted ((BE-324)), they are **live** and they are
> the *entire* remaining search space. **The next instrument is a forcing
> hunt confined to those six cells, not a wider `δ` sweep** — and the target
> shape is now sharp enough that a proof of *"forcing at `(δ₁,δ₂)` with both
> `≥ 1` needs `(1,1)`"* — the true statement (BE-77)(ii) was reaching for —
> would close the coincident-flag arm outright.

---

**Confidence.** (BE-324) — **high**: an exhibited witness re-derived with
the landed oracles, 96 + 276 instances, all-hinge-pair at 96/96, and the
defect localized to a unique optimal partition. (BE-326) — **high**, same
kind of evidence. (BE-327)(i) — **high**, a short proof plus 228 468
side-readings with 0 violations. (BE-328) — **a none-found**, and its cap is
its whole content. (BE-325)(i) — **conditional**, and its hypothesis is
measured false in this population.

**What would change this** — (BE-332)(iii).
