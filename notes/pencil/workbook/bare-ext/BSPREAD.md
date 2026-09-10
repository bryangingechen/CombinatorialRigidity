## §(K-bare-ext) — continuation (direction BSPREAD): **(BE-32)(+) IS A THEOREM** — the spread step closes not by a better cycle certificate but by spending (BE-39)(i) on the **closure's own admission rule** instead of on cycles of `G`, where it never runs out; a block of an optimal partition absorbs **at most two** points of any outside vertex's closed star and the closure admits on **three**, so the star-2 / spread **split is retired**, not its second half closed. **(BE-41)(ii) is CONFIRMED REFUTED** as stated (job 0) and annotated at five surfaces. And job 2's cross-cut-only forcing is **confined to `δ₁ = δ₂ = 1`**, which exposes BPEEL's census-3 zero as **vacuous at the only shape the theorem allows**

Direction **BSPREAD** (`notes/pencil/fanout.md` §"BSPREAD", ordinal 55), the
arc's sixty-third, at **(BE-32)(+) at the SPREAD steps** — *forced `π_u = π_v`
⇒ `δ_{uv} = 0`* where (BE-41)(i)'s star-2 certificate does not apply, **55** of
401 544 forcing steps, **7 680** of 203 723 pairs. BPEEL's successor (1), taken
after the coordinator re-ran the F26 consumer trace, which this time
**corrected the target**. Read against *Step BE40* (BEARFULL, (BE-41)),
*Steps BE38–BE39* (BEARFULL, (BE-39)/(BE-40)), *Steps BE19–BE23* (BINDUC,
(BE-22)/(BE-23)(ii)) and *Step BE72* (BPEEL, (BE-73)), whose figures are
**cited, never re-run** except where a mode re-derives one on purpose and says
so. Driver `notes/scripts/w4/bspread.py` (`lemma|chain|peel|validate`),
importing `bearfull` / `bpeel` / `btwocut` / `bimage` / `bzavoid` **read-only**
and through them the rest of the chain; every rng seeded from the printed
literal `20260901`, exact integer arithmetic throughout, every cap disclosed.

**WHICH DELIVERABLE THIS IS — said at the top, as the spec demands.**
**HIT shape 1**, and it is the first time the arc has had one on this item:
**(BE-32)(+) is PROVED OUTRIGHT for the aggressive operator** — not for a
restriction of it, and in fact for **three widenings** of it as well, so the
scope change the coordinator's route hypothesis would have had to pay is
**never incurred**. Also **HIT shape 5** (job 0's correction landed, and the
coordinator's reading of it confirmed), **HIT shape 2** for job 2 (cross-cut-only
forcing reduced to a named, purely combinatorial checkable condition), and
**NOT HIT shape 3** — no genuinely-forced pair with `δ ≠ 0` exists, because
there are none at all.

**Status, stated before the mathematics.**

- **(BE-74), THE BLOCK-ABSORPTION LEMMA — PROVED, and it is the whole
  direction.** Let `P` be an **optimal** partition, `B` one of its blocks, and
  `A := ⋃_{w ∈ B} N[w]`. Then for **every** vertex `v ∉ B`: if `v` has a
  neighbour `b ∈ B` (necessarily unique) then `N[v] ∩ A = {v, b}` **exactly**;
  otherwise `|N[v] ∩ A| ≤ 1`. So **`|N[v] ∩ A| ≤ 2` always** — and the closure
  admits on **three** points. Hence **(BE-32)(+)**, by induction, for **every**
  forcing step, star-2 and spread alike, **with no cycle anywhere in the
  proof**.
- **THE TOOL IS (BE-39)(i), SPENT SOMEWHERE ELSE.** BEARFULL extracted the
  quotient sparsity law and spent it on **cycles of `G`** ((BE-40)), where it
  runs out at `6` because a `7`-cycle of `Q` has slack `−1`. Spent on the
  **closure's own admission rule** it does not run out at all: a vertex outside
  `B` reaches `B` in `Q` by an **edge** or by a **2-path**; an edge and a path
  make a triangle of `Q`, two paths make a `4`-cycle, and two edges coincide.
  Three witnesses need three routes and `Q` has room for two. **(BE-74)(i)**.
- **THE PROOF IS SHARP, AND THE DRIVER SHOWS WHERE.** The equality case
  `N[v] ∩ A = {v, b}` is attained at **59 144** of 176 344 enumerated
  (block, outside vertex) pairs, and the same closure run at threshold **two**
  separates **363** (pair, optimal partition) instances — so the bound `≤ 2` is
  met, threshold `3` is exactly one more than it, and nothing here proves too
  much. That degenerate pair `{v, b}` is precisely the carve-out
  `bearfull.step_shape` made **by hand** and could not explain. **(BE-74)(iii)**.
- **THE STAR-2 / SPREAD SPLIT IS RETIRED, NOT HALF-CLOSED.** (BE-41)(i) proved
  401 489 steps by a `≤4`-cycle at the admitted hub and left 55; (BE-74) proves
  all 401 544 by one argument, and **(BE-32)(ii)/(iii) fall out as the
  `|B| = 1` case**. The conclusion delivered is **stronger** than `δ = 0`: *no
  optimal partition separates a forced pair*, which by (BE-39)(ii) implies the
  `P_max` form. **(BE-75)**.
- **THE COORDINATOR'S ROUTE HYPOTHESIS IS MOOT, AND SAYING SO IS THE RESULT.**
  It proposed **restricting** the closure — dropping spread steps as
  non-genuine, on the ground that the aggressive rule counts vertices and not
  independent points. (BE-74) proves the statement for the **unrestricted**
  operator, and for the operator with the hub restriction dropped on admission,
  on the seed, and on both; so the retreat is **unnecessary** and its item-(c)
  scope change across (BE-23)(ii), (BE-15) and every citing surface is **never
  paid**. Its item-(b) objection — *blocking one derivation does not unforce a
  pair* — was **sound**, and is exactly why proving the statement for the
  over-claiming operator is the better object. **(BE-75)(iv)**.
- **JOB 0 — THE COORDINATOR IS CONFIRMED, off the driver.** **(BE-41)(ii)** —
  *every aggressively-forced pair lies in one `≤6`-cycle class* — is **FALSE as
  a universal statement**: **4 of 8** members of (BE-41)(iii)'s own boundary
  family carry an aggressively-forced pair `(v, t₀)` whose shortest cycle
  through `v` is `7` or `8`, every admitting step **asserted** a genuine spread
  step, and `δ = 0` at **all 8**. Five surfaces annotated (F12). And (BE-74)
  **retires** the clause rather than repairing it. **(BE-76)**.
- **JOB 2 — CROSS-CUT-ONLY FORCING IS CONFINED TO `δ₁ = δ₂ = 1`, and BPEEL's
  zero was VACUOUS.** At a 2-cut `{u,v}` with `u ≁ v`: the closure **factorizes
  at the peel** (the run does not cross the cut before a terminal is admitted,
  and the first terminal is admitted **one-sidedly** — asserted at **39 736**
  runs, `0` violations), so forced-with-both-sides-flexible forces
  **`δ₁ = δ₂ = 1`** — which BPEEL's own **408** instances satisfy **408 / 408**,
  a population BPEEL reported as a bare count. And of BPEEL's **24 874**
  R-node-shaped both-flexible peels, **`0`** sit at `(1,1)`: its *"the hunt had
  that many chances"* had **`0`** chances at the only shape the theorem allows.
  Re-aimed: **43 763** R-node-shaped peels and **932** `(1,1)` peels over two
  independent tiers, **intersection empty**. **(BE-77)**.
- **Verdict: HIT shapes 1, 2, 5.** `PencilPair K 3 G`, `hbareSplit`, (BE-14),
  the 2-cut composition lemma, S-mark, (BE-39)/(BE-40), (BE-42)(i), (BE-43),
  (BE-59)/(BE-60), (BE-64), (BE-70), (BE-72) and BWIN's window theorem are
  **untouched**; **not a PENCIL event**; the phase-boundary consequence is
  **reported, not acted on**.
- **Reservation FULLY CONSUMED.** Labels **(BE-74)–(BE-78)** and *Steps
  BE73–BE77*; nothing returned.

### Standing notation

Inherited from *Steps BE9–BE72* verbatim (`f := def₃`, `g_{uv}`,
`δ_{uv} := f − g_{uv}`, the partition value `6(|P|−1) − 5 d(P)`, the quotient
multigraph `Q(P)` and `e_Q(S)`, tight sets, `P_max`, the `≤L`-cycle class, the
**aggressive plane-class closure**, hub, the **peel** at a 2-cut and its `δ_i`,
**R-node-shaped**, one-sided vs **cross-cut-only** forcing). Added here:

- for a vertex `z`, `[z]` denotes its block of the ambient optimal partition
  `P`; a block `B` **absorbs** the set `A := ⋃_{w ∈ B} N[w] = B ∪ N(B)`;
- for `v ∉ B` and `p ∈ N[v] ∩ A`, the **route** of `p`: the `Q`-edge or
  `Q`-path of length `2` from `[v]` to `B` that `p` supplies (constructed in
  *Step BE73*). A route is an **edge route** or a **path route**, and an edge
  route has a **`[v]`-end**, the endpoint of the underlying `G`-edge lying in
  `[v]`;
- the **witness split** of an admission at a peel: the pair
  `(|N[v] ∩ A ∩ V(H₁)|, |N[v] ∩ A ∩ V(H₂)|)`.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read. The closure rule is read off **`bimage.forced_same_plane`'s
body** and `binduc.flat_forcing_closure`'s (`|N[v] ∩ A| ≥ 3`, a count of
**vertices**), not off either docstring — the docstring's *"assumes every 3
forced points are independent"* is the reason the operator **over-claims**, and
over-claiming is the direction that makes a theorem proved for it **stronger**
than the consumers need, which is what makes the docstring's caveat harmless
here rather than a gap to be closed. The partition value and `f`/`g` are read
off `bearfull.partition_value` / `optimal_partitions` and `btwocut.g_exact`,
each cross-checked inside the driver against `kbare_common.exact_deficiency`.
**No `.lean` was opened; the standing 2026-08-05 Lean hold binds.**

### Step BE73 — (BE-74): the block-absorption lemma, and (BE-32)(+) as a theorem

> **(BE-74)(i)** *(proven; **THE BLOCK-ABSORPTION LEMMA**)* Let `P` be an
> **optimal** partition of `G`, `B ∈ P` a block, and
> `A := ⋃_{w ∈ B} N[w] = B ∪ N(B)`. Let `v ∉ B`. Then:
>
> - if `v` has a neighbour in `B`, that neighbour `b` is **unique** and
>   **`N[v] ∩ A = {v, b}`** exactly;
> - if `v` has no neighbour in `B`, then **`|N[v] ∩ A| ≤ 1`**.
>
> In particular **`|N[v] ∩ A| ≤ 2`** for every `v ∉ B`.
>
> *Proof.* Everything is (BE-39)(i), `5 e_Q(S) ≤ 6(|S|−1)`, read at three
> sizes: `|S| = 2` gives `e_Q ≤ 1`, so **two blocks are joined by at most one
> edge of `G`** (in particular the `b` above is unique); `|S| = 3` and `|S| = 4`
> give `e_Q ≤ 2, 3`, so `Q` has **no triangle and no `4`-cycle**.
>
> Give each `p ∈ N[v] ∩ A` a **route** from `[v]` to `B` in `Q`. Since
> `p ∈ A`, either `p ∈ B` or `p ∈ N[w]` for some `w ∈ B` with `p ∉ B`, whence
> `p ≠ w` and `pw ∈ E(G)`.
>
> - `p ∈ B`: then `p ≠ v` and `p ∈ N(v)`, so `vp` is a `G`-edge joining `[v]`
>   to `B` — an **edge route** with `[v]`-end `v`.
> - `p ∉ B` and `p = v`: `vw` joins `[v]` to `B` — an **edge route** with
>   `[v]`-end `v`.
> - `p ∉ B`, `p ≠ v`, `[p] = [v]`: `pw` joins `[v]` to `B` — an **edge route**
>   with `[v]`-end `p`.
> - `p ∉ B`, `p ≠ v`, `[p] = C ∉ {B, [v]}`: `vp` joins `[v]` to `C` and `pw`
>   joins `C` to `B` — a **path route** with middle `C`.
>
> Now three exclusions. **(1)** An edge route together with a path route with
> middle `C` gives a **triangle** of `Q` on the three distinct blocks `[v]`,
> `C`, `B`: forbidden. **(2)** Two path routes with **distinct** middles
> `C ≠ C′` give the **`4`-cycle** `[v] — C — B — C′ — [v]` on four distinct
> blocks: forbidden; and two path routes with the **same** middle `C` come from
> distinct `p ≠ p′` with `vp, vp′` two `G`-edges between `[v]` and `C`:
> forbidden. **(3)** All edge routes are the **same** `G`-edge `e*` — there is
> at most one between `[v]` and `B` — so they all have the same `[v]`-end.
>
> Consequently, if `v` has a neighbour `b ∈ B` then `v ∈ N[b] ⊆ A`, so both `v`
> and `b` are in `N[v] ∩ A` and both carry edge routes with `[v]`-end `v`,
> forcing `e* = vb`; then by (1) there is no path route, and by (3) no edge
> route with `[v]`-end `≠ v`, and an edge route with `[v]`-end `v` comes only
> from `p = v` or `p = b`. So `N[v] ∩ A = {v, b}`. If instead `v` has no
> neighbour in `B`, then `v ∉ A` and no route has `[v]`-end `v`, so by (1)–(3)
> there is **at most one** route in all. ∎
>
> Measured (`bspread.py lemma`), and the measurement is a **check of a proved
> statement, not its evidence**: **176 344** enumerated (block, outside vertex)
> pairs over **27 990** optimal partitions of **27 930** graphs — exhaustive
> over every connected labelled graph on `n = 3…6`, `250` seeded masks at each
> of `n = 7, 8` — **`0` violations**, with the equality case `{v, b}` attained
> at **59 144** of them.

> **(BE-74)(ii)** *(proven; **(BE-32)(+)**, and the conclusion is stronger than
> the statement)* Let `P` be **any** optimal partition, `h` a seed, and
> `B := [h]`. The aggressive closure's family `fam(h)` satisfies
> **`fam(h) ⊆ B`**.
>
> *Proof.* Induction on the admission order. `h ∈ B`. Suppose the admitted set
> `F` so far lies in `B`; then `A_F := ⋃_{w ∈ F} N[w] ⊆ A` by monotonicity. A
> vertex `v` is admitted on `|N[v] ∩ A_F| ≥ 3`; if `v ∉ B` then
> `|N[v] ∩ A_F| ≤ |N[v] ∩ A| ≤ 2` by (i), a contradiction. So `v ∈ B`. ∎
>
> Hence **no optimal partition separates two aggressively-forced vertices**,
> and in particular, by (BE-39)(ii), **`δ_{uv} = 0`** at every forced pair.
> **(BE-32)(+) is a theorem.** The stronger form is the one (BE-32)(ii)/(iii)
> also had and (BE-41) did not; it is what makes the statement compose without
> appealing to the join lemma at all.
>
> Measured: **`0`** separations at **138 394** (pair, optimal partition)
> instances of the landed operator over the same tier, with the driver's
> parametrized closure **asserted equal** to `bimage.forced_same_plane` at
> **27 930 / 27 930** graphs.

> **(BE-74)(iii)** *(proven; **the bound is sharp, and threshold `3` is exactly
> one more than it**)* The proof never uses `|N[v] ∩ A| ≥ 3` beyond exceeding
> `2`, so it fails at threshold `2` — and it must, because the equality case is
> attained: at any `v ∼ b` with `b` admitted, `N[v] ∩ A ⊇ {v, b}` already.
> Measured: the same closure at threshold `2` **separates 363** (pair, optimal
> partition) instances at `n = 3…6` alone, the first at
> `{01, 04, 05, 12, 13}` — a **tree** with two adjacent degree-`3` vertices,
> where `δ ≠ 0` between them.
>
> **This explains a carve-out the arc made by hand.** `bearfull.step_shape`
> excludes *"the degenerate pair `{v, w}`"* from the star-2 shape with no
> reason beyond *the cycle it would produce is not a cycle*. It is the same
> pair, and (BE-74)(i)'s equality case is what it is: the **unique** two-point
> configuration a block can absorb.

### Step BE74 — (BE-75): what the theorem retires, what it upgrades, and the coordinator's hypothesis

> **(BE-75)(i)** *(the split is **retired**)* (BE-41)(i) proved the **star-2**
> steps — two of the three admitting points in one closed star — by exhibiting
> a `3`- or `4`-cycle through `v` and the witness hub, and left the **spread**
> steps, where no such cycle exists. (BE-74) proves **all** steps by one
> argument that never mentions a cycle of `G`. So the residue is not closed by
> a second certificate; the **classification into two shapes has no work left
> to do**, and `step_shape` becomes a diagnostic rather than a proof device.
> Concretely: **401 544 of 401 544** forcing steps and **203 723 of 203 723**
> pairs, against (BE-41)(i)'s 401 489 and 196 043.

> **(BE-75)(ii)** *(containment — (BE-32)(ii)/(iii) are the `|B| = 1` case)*
> Take `B = {w}` a **singleton** block, so `A = N[w]`. (BE-74)(i) says: if
> `v ∼ w` then `N[v] ∩ N[w] = {v, w}`, i.e. **`v` and `w` have no common
> neighbour**; and if `v ≁ w` then `|N[v] ∩ N[w]| ≤ 1`, i.e. **at most one
> common neighbour**. Contrapositively, a **common triangle** ((BE-32)(ii)) or
> **two common neighbours** ((BE-32)(iii), weakened as (BE-40)(iv) already
> found) puts `u, v` in one block of **every** optimal partition. So the two
> landed merge theorems are the degenerate case of the lemma, exactly as
> (BE-40) contained them — but now the containment reaches the closure's steps
> too, which (BE-40)'s could not.

> **(BE-75)(iii)** *(the consumers, and this is the routing payload)* Two
> surfaces consumed (BE-32)(+) at the **pair** level and inherited its 3.8 %
> residue verbatim. Both are now unconditional:
>
> - **(BE-73)(ii)(b)** — *one-sided forcing at a 2-cut gives `δ_i = 0`, and by
>   (BE-22)(vi) a rigid side removes the general-position half outright* — was
>   *"PROVED given (BE-32)(+), which is itself 96.2 % proved"*. It is now
>   **PROVED**, and half (B)'s located enemy is discharged wherever it is
>   forced one-sidedly, with **no residue at all**.
> - **BRULE's job 2**, the `π_u = π_v` corner of (β)'s ledger ((BE-58)(iv),
>   forced branch) — the same upgrade, on the ear side.
>
> **What it does NOT do.** It does not touch (BE-67)(iii)'s class quantifier,
> `reach`, the flag base, cross-pair welding, (S1)/(S2), or the whole-piece
> reading of (BE-32)(+) at a 2-cut, which (BE-73)(ii)(a) already showed is
> near-vacuous. The residue it leaves is job 2's, and that is *Step BE76*.

> **(BE-75)(iv)** *(**the coordinator's route hypothesis, disposed of** —
> `RESEARCH-ARC.md` §7, and it was labelled *to be tested, not inherited*)*
> The hypothesis was a **restriction** of the closure: at a spread step make
> the three witnesses **collinear** in some legal pencil configuration, so the
> step is not a genuine forcing certificate, leaving the star-2-only closure
> for which (BE-41)(i) already proves (BE-32)(+). **The verdict is MOOT, not
> confirmed and not refuted** — and moot is the strongest of the three here,
> because a moot restriction costs nothing while a confirmed one costs its
> scope change.
>
> **Why.** (BE-74) proves the statement for the **unrestricted aggressive
> operator**, and the driver additionally checks it for **three widenings** the
> proof covers — admission by any vertex rather than a hub, seeding at any
> vertex, and both — at **274 168** (pair, optimal partition) instances with
> `0` separations. So there is no need to argue that any step is non-genuine,
> and the hypothesis's own item **(c)** — that the retreat changes the object
> (BE-32)(+) quantifies over, touching (BE-23)(ii), (BE-15) and every citing
> surface — is a price **never incurred**. Its item **(b)** — *blocking one
> derivation does not show a pair unforced, so the honest object is one
> existential per pair* — was **correct**, and is precisely the reason a
> theorem about the **over-claiming** operator is the right thing to have: it
> holds a fortiori for genuine forcing without any realizability question being
> asked. Its item **(a)** — realizability of collinearity inside the pencil
> stratum — is not tested here and does not need to be.

### Step BE75 — (BE-76): job 0, the correction confirmed off the driver and annotated at source

> **(BE-76)(i)** *(**a correction at source** — F12; **(BE-41)(ii) is refuted
> as stated**, and the refutation is its own sibling's)* (BE-41)(ii) reads:
> *"What is left of (BE-32)(+) is **every aggressively-forced pair lies in one
> `≤6`-cycle class**"*, measured **203 723** pairs, **`0`** outside. But
> (BE-41)(iii), the **same** direction, constructs a family in which one is
> not: with `t₀ … t_k` a path, `x_i` completing the triangle `(t_i, t_{i+1})`,
> and `v` joined to `t₀`, to `x_{k−1}` and to a pendant, the pair `(v, t₀)` is
> aggressively forced and the shortest cycle through `v` has length `k + 2`.
> So (BE-41)(ii) is **FALSE as a universal statement**.
>
> **Re-derived here off the SHIPPED driver, not off the write-up**
> (`bspread.py chain`, importing `bearfull.tri_chain`,
> `forcing_derivation`, `step_shape`, `cycle_classes`, `short_cycles`,
> `def3_fast` and `btwocut.g_exact`): `k = 3…6 ×` 1 or 2 pendants, **8**
> members at `n = 9…16`; the admitting step is **asserted** a genuine spread
> step at every one (no witness triple makes it star-2); the escape set is
> **asserted non-empty** and has **4** members, with shortest cycle `7` (`k=5`)
> and `8` (`k=6`); and `δ = 0` at **all 8** — asserted, since a `δ ≠ 0` here
> would be HIT shape 4. **The coordinator's reading is confirmed in full.**
>
> **(BE-32)(+) itself was never in danger**, and is now a theorem by (BE-74).
> What was dead is the `≤6`-cycle **route**; what (BE-74) shows is that the
> route was never the load-bearing one, so **the clause is retired rather than
> repaired**. Its corrected form is: *the `≤6`-cycle class is a **sufficient**
> certificate for `δ = 0` ((BE-40)) that the aggressive closure can **escape**
> ((BE-41)(iii)); (BE-32)(+) does not depend on it ((BE-74))*.

> **(BE-76)(ii)** *(where the defect sat, and the five hunks)* BEARFULL wrote
> **both** halves; the damage was in surfaces that restated (ii) without
> (iii)'s carve-out, and in the consumers that inherited the wrong form as the
> thing to prove. Annotated at source in this landing's own commit:
>
> 1. **BEARFULL's confidence table** — *"(BE-41)(ii) forced ⟹ `≤6`-cycle
>    class | MEASURED at 203 723 + 27 414 pairs, 0 escapes"*: those are the two
>    **random/enumerated** tiers; the **constructed** tier escapes **by design**
>    and is tabulated on the next row as if it were a different claim.
> 2. **BEARFULL's cap 3** — *"It reads 'no aggressively-forced pair outside a
>    `≤6`-cycle class was found under this cap', never 'none exists'"* — which
>    is **weaker than the truth**: one is known to exist, by construction. A cap
>    disclosure that **under**-reports a known refutation is the F11 hazard
>    running backwards, and it is the reason this direction takes cap
>    disclosure literally rather than formulaically.
> 3. **(BE-41)(ii)'s own measurement line**, `0` escapes with no pointer to
>    (iii).
> 4. **BPEEL's (BE-73)(iv)** and its *What would change this* entry, both of
>    which name *"the SPREAD step ((BE-41)(ii))"* as the proof obligation — a
>    statement with a counterexample.
> 5. **`notes/Phase39.md`'s hand-off candidate 1**, corrected in the BSPREAD
>    prep's own commit.
>
> The `(K-bare)` gap-map row was **checked and is clean** — it names the label
> family, not the refuted clause — and is **not** "fixed" into the refuted form.

### Step BE76 — (BE-77): job 2, cross-cut-only forcing confined, and a vacuity correction to BPEEL's census

> **(BE-77)(i)** *(proven; **THE PEEL FACTORIZATION OF THE CLOSURE**)* Let
> `{u,v}` be a 2-cut of `H` with `u ≁ v` and `H = H₁ ∪ H₂`,
> `H₁ ∩ H₂ = {u,v}`, both sides carrying an interior vertex. Run the closure
> from a seed `h ∈ V(H₁) ∖ {u,v}`. Then:
>
> **(a)** until `u` or `v` is admitted, `A ⊆ V(H₁)` and every admitted vertex
> lies in `V(H₁)`. *(An interior vertex `w` of `H₂` has `N[w] ⊆ V(H₂)`, so
> `N[w] ∩ A ⊆ V(H₁) ∩ V(H₂) = {u,v}`, at most `2 < 3`.)*
>
> **(b)** hence the **first** terminal admitted has **all** its witnesses in
> `V(H₁)`, i.e. it is admitted by the run **on `H₁` alone** — the certificate
> for the first terminal is **one-sided**, always.
>
> *(If the seed is itself a terminal, (a) and (b) are vacuous and (c) below
> applies to both sides at once, seeded at that terminal.)*
>
> **(c)** after that terminal `u` is admitted, `A ∩ V(H₂)` evolves **exactly**
> as the `H₂`-run seeded at `u`, because `A ∩ V(H₂)` grows only through
> `N[w] ∩ V(H₂)` for `w ∈ V(H₂)`; and symmetrically `A ∩ V(H₁)` continues as
> the `H₁`-run. **So the only step that can cross the cut is the admission of
> the second terminal.** ∎
>
> Asserted (`bspread.py peel`): **39 736** closure runs admitting both
> terminals, **`0`** violations of (a) and (b), and **18 080** of them admit
> the second terminal on a witness set genuinely **split** by the cut.

> **(BE-77)(ii)** *(proven; **cross-cut-only forcing is confined to
> `δ₁ = δ₂ = 1`**)* Suppose `π_u = π_v` is forced at such a peel and **both
> sides are flexible**, `δ₁, δ₂ ≥ 1`. Then **`δ₁ = δ₂ = 1`**, and the second
> terminal's witness set is **exactly** `{v, b₁, b₂}` with `b_i` the unique
> neighbour of `v` in the block of `u` on side `i`.
>
> *Proof.* **Relabel so that `v` is the second terminal admitted** (if the seed
> is itself a terminal, take `v` to be the other one; the conclusion is
> symmetric in `u, v`). Write `a := |N_{H₁}[v] ∩ A₁|` and
> `b := |N_{H₂}[v] ∩ A₂|` for its witness split, `A_i := A ∩ V(H_i)`.
>
> **Step 1: each side's admitted set lies in one block of every optimal
> partition of that side.** `δ_i ≥ 1` means **every** optimal partition of
> `H_i` separates `u` from `v`; fix one and let `B_i` be the block of `u`, so
> `v ∉ B_i`. On side 1, `u` is admitted with witnesses in `V(H₁)` by (i)(b) and
> every later admission `w ∈ V(H₁) ∖ {v}` has `N_H[w] = N_{H₁}[w]`, so the
> induction of (BE-74)(ii) runs verbatim inside `H₁` and puts all of them in
> `B₁`; hence `A₁ = ⋃_{w ∈ F₁} N_{H₁}[w]` with `F₁ ⊆ B₁`. On side 2, (i)(c)
> makes `A₂` the `H₂`-run seeded at `u` — `A₂` starts at exactly `N_{H₂}[u]` —
> and the same induction puts `F₂ ⊆ B₂`.
>
> **Step 2: `a, b ≤ 2`, in the shape `{v, b_i}`.** By Step 1, (BE-74)(i)
> applies on each side, so `a ≤ 2` with equality **only** when `v` has a
> neighbour `b₁ ∈ B₁` and `N_{H₁}[v] ∩ A₁ = {v, b₁}`, and likewise `b`. (This
> also disposes of `a ≥ 3`, which by (BE-74)(i) would put `v ∈ B₁` and force
> `δ₁ = 0` against the hypothesis; likewise `b ≥ 3`.) The
> two sides overlap only in `v` itself (`u ≁ v`), so the total is
> `a + b − [v ∈ A] ≥ 3` forces **`a = b = 2`** — the two-point shape needs
> `v ∈ A`, and `(2,1)`, `(1,2)`, `(1,1)` all total `≤ 2`.
>
> **Step 3: the merge.** So `v` has a neighbour `b_i ∈ B_i` on **each** side. In `H_i`, the blocks
> `[v]` and `B_i` are joined by exactly **one** edge — (BE-39)(i) at `|S| = 2`,
> and `v b_i` is it — so **merging them** changes the partition value by
> `−6 + 5·1 = −1` and produces a partition of `H_i` with `u, v` **together**.
> Hence `g_i ≥ f_i − 1`, i.e. **`δ_i ≤ 1`**; with `δ_i ≥ 1`, `δ_i = 1`. ∎
>
> Checked against **BPEEL's own census 1**, re-run here: **13 004** peels,
> **408** forced with both sides flexible, and the `(δ₁, δ₂)` distribution is
> `{(1,1): 408}` — **408 / 408**, `0` violations. BPEEL recorded that
> population as a bare count and read its zero at the R-node shape; the theorem
> says what the population **is**.

> **(BE-77)(iii)** *(**a vacuity correction** — F11, and it is BPEEL's own
> discipline applied with the denominator the theorem supplies)* BPEEL's
> census 3 reported *"**24 874** R-node-shaped peels with both `δ` positive,
> **180** forced, **`0`** in the intersection"* under the non-vacuity check
> *"the hunt had that many chances"*. By (ii) the only shape a hit can take is
> `δ₁ = δ₂ = 1`, and of those **24 874**, the number at `(1,1)` is **`0`**. So
> the hunt had **`0`** chances, not 24 874, and its zero is **vacuous at the
> only shape the theorem allows**. **Recorded, not smoothed** — the check was
> the right instrument pointed at the wrong denominator, and nothing else in
> (BE-73)(iii) moves: its 3 497 forced R-node peels with `min(δ₁,δ₂) = 0` and
> its 408 off-R-node positives stand, and (ii) now **explains** the 408.

> **(BE-77)(iv)** *(**the re-aimed hunt**, and what job 2 has become)* Aimed at
> `(1,1)` rather than at both-flexible, over two independent tiers: random
> 2-connected graphs at `n = 6…10` with **no** max-degree filter (BPEEL's
> census 1 carried one, which is why its R-node peels were rigid on one side)
> — **16 800** peels, **5 005** R-node-shaped, **932** at `(1,1)`; and BPEEL's
> constructed subdivided-skeleton tier — **38 758** R-node-shaped peels,
> **`0`** at `(1,1)`. **Across 43 763 R-node-shaped peels and 932 `(1,1)`
> peels the intersection is EMPTY.** Under F11 that is *"none found under cap
> (1)"*, **never** *"none exists"*.
>
> **So job 2 is now one named, purely combinatorial, checkable condition:**
>
> **can an R-node-shaped 2-cut peel have `δ₁ = δ₂ = 1`?**
>
> No closure, no configuration, no genericity, no constructor — a statement
> about two deficiencies and one 3-connectivity test. If **no**, cross-cut-only
> forcing at an R-node peel with both sides flexible is **impossible** and
> half (B)'s last general-position enemy is gone. If **yes**, the witness is
> immediately testable for forcing by (ii)'s exact certificate shape. That is
> the reduction, and it is what (BE-73)(iv) was short of.
>
> > **ANSWERED, 2026-09-01 (direction BONEONE, *Steps BE78–BE80* /
> > (BE-79)/(BE-80)) — the answer is YES, and BOTH TIERS ABOVE HAD ZERO
> > CHANCES.** `δ_i` and `rnode_shaped` are both **per-side**, and any two
> > sides glue, so the question is whether **one** side can be R-node-shaped at
> > `δ = 1`: a 9-vertex `K₄`-skeleton side is, and glued to a 4-vertex side at
> > `δ = 1` it gives an R-node-shaped `(1,1)` peel on **11** vertices
> > (`WIT11`); two copies of it make **both** sides R-node-shaped (`WIT16`).
> > **Tier A** runs at `n ≤ 10` and the minimum is `11`, so its
> > 5 005-vs-932 *"empty intersection"* is `0` of `0`; **tier B** is
> > `bpeel.constructed_tier`, every peel of which has a **path side**, whose
> > `δ = min(L,6)` is never `1`, so it had 0 chances at any cap. The
> > *"43 763 and 932, intersection empty"* headline is therefore **vacuous on
> > both tiers**. (i) and (ii) themselves are **untouched and CONFIRMED on
> > `WIT11`** — it is their hypothesis that turns out satisfiable — and the
> > forcing test (iv) prescribes comes back **positive** ((BE-81)).

### Step BE77 — (BE-78): the board, reported and not acted on

> **(BE-78)(i)** *(what moved)* **(BE-32)(+) is a theorem.** The `(K-bare)`
> row's *"PROVED at 196 043 of 203 723 forced pairs, residue the geometry-free
> SPREAD step"* becomes *"PROVED, at all of them, for the aggressive operator
> and three widenings of it"*. **(BE-73)(ii)(b)** and **BRULE's (BE-58)(iv)
> `π_u = π_v` corner** lose their inherited 3.8 % and become unconditional.
> **(BE-41)(ii)** is refuted as stated and **retired**, not repaired, with its
> five surfaces annotated. **(BE-73)(iv)'s residue** is reduced from a hunt to
> a combinatorial question, and **(BE-73)(iii)'s census-3 zero** is corrected
> from *"0 of 24 874 chances"* to *"0 of 0 chances"*.

> **(BE-78)(ii)** *(what did **not** move, said plainly)* **(BE-14) is
> untouched.** The 2-cut composition lemma (S-mark) is untouched; (BE-67)(iii)'s
> class quantifier — the uniformity of `reach` over the class — is untouched;
> the **flag base** off the no-adjacent-hubs class ((BE-65)(i)) is untouched;
> **cross-pair welding** ((BE-28)(i)) is untouched; **(S1)/(S2)** are untouched;
> `hbareSplit`, `hK`, **(GR-15)** and class uniformity of the escape are
> untouched. **Not a PENCIL event.** The phase-boundary consequence of a
> HIT shape 1 is **reported, not acted on**: whether it changes the phase's
> shape is the USER's call under the standing 2026-07-24 adjudication and the
> phase note's *On a future HIT* block, and the 2026-08-05 Lean hold binds
> regardless.

> **(BE-78)(iii)** *(the price, stated as a price)* **(BE-74) is a theorem
> about the AGGRESSIVE operator**, which over-claims forcing; that is the
> direction that makes it **stronger** than the consumers need, but it is a
> statement about a **combinatorial** relation, not about which coincidences a
> real pencil configuration actually exhibits. **(BE-74) rests entirely on
> (BE-39)(i)**, which is proven-informally from optimality of `P` in one line
> and enumerated at 130 331 subsets — if that law were wrong every clause here
> falls, and nothing else would. **(BE-77)(ii)'s hypotheses are real**: `u ≁ v`,
> both sides with an interior vertex, and *flexible* meaning `δ_i ≥ 1`; at
> `u ∼ v` (BE-32)(i) already bounds `δ ≤ 1` and the peel is a different object.
> **(BE-77)(iv) is a capped search** and its zero is *"none found"*. And the
> reduction of job 2 is a **reduction**, not a discharge: the named condition
> is open.

### Verification

Every claim above is reproduced by
`python3 notes/scripts/w4/bspread.py {lemma|chain|peel|validate}`, run from the
repo root; `validate` runs all three modes at a reduced tier in **≈ 54 s**
(inside the 600 s foreground budget, one invocation); the full tiers are
`lemma` **≈ 67 s**, `chain` **≈ 3 s**, `peel` **≈ 33 s** — wall clock, which
varies run to run; the counts above are the invariants. The load-bearing
asserts (a failure stops the run):

1. **The block-absorption lemma is asserted, not reported** — a single
   violation at any (optimal partition, block, outside vertex) triple stops
   `lemma`, and would refute (BE-74)(i) rather than bound its scope.
2. **The parametrized closure is asserted equal to the landed one**
   (`bimage.forced_same_plane`) at every graph of the tier, 27 930 / 27 930.
3. **The SHARPNESS control is asserted to FAIL**: `lemma` stops if threshold
   `2` produces **no** separation, because a proof that also proved the false
   threshold-`2` statement would be proving too much.
4. **`chain` asserts the escape set NON-EMPTY**, asserts every member's
   admitting step a genuine spread step, and asserts `δ = 0` at every member.
5. **The peel factorization is asserted**, not measured: a run that crosses the
   cut before a terminal is admitted, or a first terminal with an off-side
   witness, stops `peel`.
6. **(BE-77)(ii) is asserted** at every forced both-flexible peel — an instance
   off `(1,1)` stops the run.
7. **Exact integer arithmetic throughout**, every rng seeded from the printed
   literal `20260901`, zero floating point. The partition oracle is
   cross-checked against `kbare_common.exact_deficiency` at every call
   (inherited from `bearfull.optimal_partitions`).

### Caps, disclosed rather than smoothed

1. **`lemma`'s enumeration is exhaustive at `n = 3…6` and SAMPLED at
   `n = 7, 8`** (250 seeded masks each). The lemma is **proved**, so the tier
   bounds the *check*, not the statement — the opposite of the usual reading,
   and it is stated that way in the driver's own output.
2. **The theorem is about the AGGRESSIVE operator** and its three widenings.
   *Forced* there is a **candidate** and *not forced* is **sound**; a theorem
   proved for it holds a fortiori for genuine forcing. Cap 2 of BEARFULL's list,
   unchanged and still the right reading.
3. **`chain`'s family is a CONSTRUCTION**: it proves the escape set non-empty,
   never that it is large. The blind `n = 9…13` re-finding is **BEARFULL's**
   ((BE-41)(iii)) and is **cited, not re-run**.
4. **`peel`'s hunt is capped**: tier A is exhaustive at `n = 6` and 4 000
   seeded masks at each of `n = 7…10` with `|E| ≤ 2n`; tier B is BPEEL's
   constructed generator at its own cap (`K₄` all profiles at lengths `1…4`,
   prism and `K_{3,3}` seeded). *"No R-node-shaped peel at `(1,1)` was found
   under this cap"* is **never** *"none exists"* (F11).
5. **`rnode_shaped` is BPEEL's stand-in, not an SPQR implementation**, and is
   quoted as one here exactly as there.
6. **F27 on the negative:** the `(1,1)`-and-R-node intersection is empty in
   **two independent tiers** built by different generators (random masks; a
   skeleton-plus-profile constructor), which is the multiple-draw requirement,
   not one sampler run twice.

### Harness note — the `kbare/` sibling-import set gains its SIXTEENTH consumer

`bspread.py` imports `bearfull` (`optimal_partitions`, `cycle_classes`,
`short_cycles`, `step_shape`, `forcing_derivation`, `tri_chain`, `def3_fast`),
`bpeel` (`peel_scan`, `rnode_shaped`, `pair_forced`, `constructed_tier`),
`btwocut` (`deltas_at`, `g_exact`, `vertex_connectivity_at_least`), `bimage`
(`forced_same_plane`), `bzavoid` (`adj_of`, `connected_spanning`,
`edges_of_mask`), plus `exactcore` and `kbare_common`, all **read-only**, and
through them the rest of the chain — so the recorded **unpaid** sibling-import
debt (`notes/scripts/README.md` *Harness debt*) gains its **sixteenth** `w4/`
consumer and the chain is now **fourteen** deep: `battain → bzavoid → binduc →
btwocut → bimage → bearcase → bearfull → bsharp → brule → bwin → brnode →
bdecor → bpeel → bspread`. **`bpeel` gains its FIRST external consumer**, and
`bearfull.optimal_partitions` its first consumer outside bearfull itself.
**NO MOVE MADE**; the consumer lists are extended in the README, exactly as the
previous fifteen did. The new primitives (`closure_trace`, `closure_pairs`,
`block_of`, `lemma_violations`, `strong_separations`, `peel_invariants`) are
local to this driver.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-74)(i) the block-absorption lemma | **PROVED** from (BE-39)(i) at `|S| = 2, 3, 4`; enumerated 176 344 / 0 violations |
| (BE-74)(ii) (BE-32)(+), in the *no optimal partition separates* form | **PROVED**; 138 394 instances / 0 separations, landed-closure cross-check 27 930/27 930 |
| (BE-74)(iii) the bound is sharp; threshold 2 fails | **PROVED** (equality case exhibited); the control **fails as required**, 363 separations |
| (BE-75)(i) the star-2 / spread split is retired | **PROVED** — a corollary of (BE-74)(ii), which never reads the shape |
| (BE-75)(ii) (BE-32)(ii)/(iii) are the `\|B\| = 1` case | **PROVED** |
| (BE-75)(iii) (BE-73)(ii)(b) and BRULE's corner become unconditional | **PROVED given the consumers' own statements**, which carried (BE-32)(+) as the only proviso |
| (BE-75)(iv) the coordinator's route hypothesis is MOOT | **ARGUED** — the restriction is unnecessary, not shown impossible; its (a) is untested and need not be tested |
| (BE-76)(i) (BE-41)(ii) is refuted as stated | **PROVED by construction**, re-derived off the shipped driver; escape set asserted non-empty |
| (BE-76)(ii) the five annotated surfaces | **LANDED** in this commit (F12) |
| (BE-77)(i) the peel factorization | **PROVED**; asserted 39 736 runs / 0 violations |
| (BE-77)(ii) forced + both flexible ⇒ `δ₁ = δ₂ = 1` | **PROVED** from (BE-74) + (BE-39)(i); 408/408 against BPEEL's own census |
| (BE-77)(iii) BPEEL's census-3 zero is vacuous at `(1,1)` | **MEASURED**, `0` of 24 874 — a correction to a landed non-vacuity claim |
| (BE-77)(iv) no R-node peel at `(1,1)` found | **MEASURED**, capped, two independent tiers; **not** an impossibility claim |
| (BE-78) the board | **REPORTED**, not acted on |

### What would change this

- **A counterexample to (BE-39)(i)** would take everything here with it, and
  nothing else would be needed to. It is one line from optimality, and it is
  enumerated at 130 331 subsets ((BE-39)(i)); this direction adds 176 344
  further instances of its `|S| = 2` clause as a by-product.
- **An R-node-shaped 2-cut peel with `δ₁ = δ₂ = 1`** is now the entire content
  of job 2. It is combinatorial, cheap to test, and the driver would find it as
  a `peel` hit; its absence under cap is **not** a proof.
- **A genuinely-forced pair with `δ ≠ 0`** is now impossible for the aggressive
  operator, hence for genuine forcing. HIT shape 4 is **closed**, and any
  future claim of one is a claim against (BE-39)(i).
- **A consumer that needs the `≤6`-cycle class itself** — rather than `δ = 0`
  — would still face (BE-41)(iii)'s escape. None is known; (BE-40) is used
  everywhere through its `δ` conclusion.
- **A widening of the closure past threshold 3** breaks the theorem
  immediately and correctly ((BE-74)(iii)), so any future *"the rule really
  admits on two points"* reading is refuted in advance.

### TERMINATION riders

**E1: NO** — this direction is one combinatorial lemma, its two corollaries and
a capped census; no `g`-flank is involved and none is produced. **E2: NO** —
nothing landed is refuted **except two stated things**: **(BE-41)(ii)** as a
universal statement, which its own sibling already refuted and which this
direction annotates rather than discovers, and **(BE-73)(iii)'s non-vacuity
denominator**, corrected here; every landed *measurement* is intact, and
(BE-39)/(BE-40), (BE-41)(i)/(iii), (BE-64)–(BE-73) are untouched. **E3: ARMED
by GBAL, not fired** — this direction is on the §(K-bare-ext) path, not (a′);
reported, not acted on.
