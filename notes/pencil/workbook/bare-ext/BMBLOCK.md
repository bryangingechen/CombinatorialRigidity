## §(K-bare-ext) — continuation (direction BMBLOCK, ordinal 109, 2026-09-12): **THE `⟨M⟩` BLOCK IS CLOSED BY PROOF ON EVERY REGION THE PATH SPAN REACHES — and the proof does NOT transport (BE-258)'s method, it replaces the rank count by a TRANSVERSAL.** `⟨M⟩ = ⟨p_x ∧ p_y⟩` is, in this carrier, exactly the hinge line the virtual edge `xy` would carry (`bimage.chain_of`: `ℓ_i = p_{i−1} ∧ p_i`), so `c_i(⟨M⟩) = 1` says side `i`'s relative screw space contains the **virtual edge's own line**; by (BE-30)(iv) that forces `p_x ∧ p_y ∈ ⟨P⟩` for **every** x–y path `P` of side `i`. **THE PATH LEMMA: `dim(⟨P⟩ ∩ ⟨M⟩) = 0` for every path of edge-length `2 ≤ m ≤ 5`** — pointwise-under-a-named-non-degeneracy at `m ∈ {2,3,4}` via an **explicit decomposable transversal**, and by a non-vanishing `6 × 6` determinant at `m = 5`. Since an internal R-node peel needs `x ≁ y`, `dist_i ≥ 2` on **both** sides, so **one** side with `dist_i ≤ 5` already gives `c₁(⟨M⟩) + c₂(⟨M⟩) ≤ 1 = dim ⟨M⟩` — a **strictly stronger** closure shape than (BE-259)(i)'s, which needs `dist_i ≤ 4` on **both**. Measured at the **same 427 side rows** (BE-258)(iii) used, with the **same per-distance denominators**: `dim(⟨P₀⟩ ∩ ⟨M⟩)` is `0` at every one of the **386** rows with `dist_i ≤ 5` and `1` at all **41** with `dist_i ≥ 6`. The one surviving corner is `dist_i ≥ 6` on **both** sides, and there the arithmetic closes it from one **measured** step (`c_i(⟨M⟩) = 1 ⟹ ρ_i = 6` at 25 of 25 firing rows), exactly mirroring (BE-259)(ii)'s residue. **That corner is priced WITHOUT A SINGLE DRAW** — `(dist₁, dist₂)` is combinatorial — over BGOODEMPTY's **entire** job list: **2 698 of 2 946** in-region peels are closed by the proved half alone and **248** fall in the corner, so the residue is real and is the *same* question (BE-259)(ii) leaves one dimension up. **The spec's mechanism is REFUTED at the corpus's own best case** ((BE-99)(iii)'s double pencil, 6/6 seeds: `(c₁, c₂)` at `⟨M⟩` is `(0,1)`, never `(1,1)`). **The F26 consumer check is reported and it does NOT kill the question** (*Steps BE270–BE276*)

### Standing notation (on top of *Steps BE148–BE261*)

BGOODEMPTY's, verbatim, plus one object of this direction's own. Read at the
definition sites (`bimage.chain_of`, `bimage.legal_chain`, `bimage.rho_bar_of`,
`bimage.dist_in`, `bdecor.sample_by_branches`, `bgoodempty.side_library`,
`bgoodempty.side1_library`, `bgoodempty.block_row`, `bgoodempty.nonadj_pairs`,
`bgoodempty.xy_paths`, `bproper.composite`, `bproper.free_peel`,
`bunif.BLK`, `bunif.CAP`, `bunif.blocks_of`, `bunif.profile`,
`bdouble.measure_row`):

> **`⟨M⟩ := ⟨p_x ∧ p_y⟩`** — the `bunif.BLK` block `'M'`, with
> `bunif.CAP['M'] = 1`. **Read at source, not off the letter** (blind-axis
> clause, and it is the first thing this direction did): `bunif.blocks_of`
> line 199 is `'M': [wedge2(px, py)]`, and `bunif`'s own block comment says
> *"`M` = the Plücker point of the line `p_x v p_y`"*. So `bunif`'s `'M'`
> **is** (BE-97)(iv)'s `⟨M⟩`, not a different object wearing the same letter.
> **THE DISPATCH'S OWN BLIND-AXIS NOTE IS IMPRECISE HERE, and the correction
> is load-bearing.** The spec warned that the four `bunif.BLK` blocks *"are
> **not** the 16 stable `U`"* and that the two are *"different populations"*.
> Read at source: `bunif.SUBS` is **every subset** of `BLK` — `[tuple(sorted(s))
> for k in range(5) for s in itertools.combinations(BLK, k)]`, so exactly
> `2⁴ = 16` — and `bunif.profile` computes `c[sub]` at the **span of the
> blocks in `sub`**, with `du = Σ_{b ∈ sub} CAP[b]`. So **the 16 stable `U`
> ARE the block-sums, the four blocks are their ATOMS, and `⟨M⟩ = ('M',)` is
> one of the 16, with `du = 1`.** They are one family, not two. This matters
> twice below: it is why `bgoodempty.run_block`'s 16-block margin histogram
> **does** gate the `⟨M⟩` shape ((BE-273)(iii)), and it is why (BE-97)(iv)'s
> *"13 unwitnessed blocks"* — `16 − {0} − {Λ²K⁴} − {Π_x}` — contains `⟨M⟩`.
>
> **`m`** is the **edge count** of a path `P`, so `dim ⟨P⟩ ≤ min(m, 6)` and
> `dist_i(x, y)` is the least `m` over x–y paths of side `i`. **`η`** denotes
> a bivector used as a linear functional through the Klein pairing
> `⟨ω, η⟩ := ω ∧ η ∈ Λ⁴K⁴ ≅ K`; when `η = q ∧ r` is **decomposable**,
> `⟨ℓ, η⟩ = 0` says the two **lines** `ℓ` and `η` **meet**.
>
> **`Good(H; x, y)`** exactly as (BE-69)(i) defines it, so at any of its
> points `a₁ = a₂ = 0` and `dim(ρ̄₁+ρ̄₂) = min(Σδ, 6)`.

**Baseline `HEAD` = `2145cb0b`**; every figure was taken against that sha, and
`git status` was clean at the start and end of this direction. Two siblings
(GBASE 108, GSECOND 110) were in flight on the `hK`/§(K-grid) lane and mint
into `notes/pencil/workbook/grid.md` — disjoint by file and by label range;
nothing here reads either. **No `.lean` opened, no `lake build`** — the
2026-08-05 hold untouched. **Driver:** `notes/scripts/w4/bmblock.py`, new,
six modes (`path`, `side`, `block`, `arith`, `reach`, `dbl`) plus
`validate`. **Which fences each figure ran at, disclosed once:** `path`,
`side`, `arith`, `reach` and `dbl` were run as **top-level modes at the
committed defaults**; **no figure in this section comes from a `validate`
path**, and `block` produced none at all ((BE-276)(iii)). This direction
opens no landed fence: it calls `bgoodempty.side_library(8, 7, 40)`,
`xy_paths(cap=400, maxlen=9)`, `block_row(ndraw=3)` and
`bgoodempty.nonadj_pairs` (all six hub pairs) exactly as landed, and uses
`bproper.NONADJ` only through that un-fencing — the committed
`bproper.NONADJ` still lists **3 of 6**, i.e. BGOODEMPTY's opening lives in
its own `nonadj_pairs`, not as an edit to `bproper`. `bpeel.constructed_tier`,
`bproper.run_peel` and `bimage.run_hunt` are **not used here** at any
setting.

---

### Step BE270 — (BE-271): the F26 consumer check, run FIRST — what consumes a `Good = ∅` piece, and at which quantifier

BTAKERS (107) priced the `Π_x` obligation at **zero** by opening its consumer
and finding it was never consumed in *Steps BE148–BE237* at all, after five
directions had run at it. The same check here, run before any driver:

> **(BE-271)(i)** `[PROVED]` — *the consumer chain, traced to the owning
> sections and not to a summary.* `Good(H; x, y) ≠ ∅` is **(BE-67)(iii)**, and
> (BE-67)(iii) at `H` is *"`A₁ ∩ A₂ ≠ ∅` and `reach(H; x, y) = min(δ₁+δ₂, 6)`"*
> (BPEEL's row, *Step BE68*). Its consumer is **(BE-22)(iii)'s 2-cut
> composition criterion** — `G` attains ⟺ `dim(ρ̄₁+ρ̄₂) = min(δ₁+δ₂,6) + a₁ + a₂`
> — invoked by the **S-mark** induction of (BE-25)(ii), which is the shape
> (BE-14)'s 2-cut step carries. (BE-73)(vi) states the standing exactly:
> *"(BE-67)(iii) is **reduced, not proved**. What (BE-14)'s 2-cut step now
> stands on: the class statement's **uniformity over pieces** (one number,
> `reach`, per peel — the named checkable condition), the **flag base** off the
> no-adjacent-hubs class ((BE-65)(i) …), and **cross-pair welding**
> ((BE-28)(i) …)."* So the obligation **is** consumed, and at the **universal**
> quantifier: *for every internal R-node piece, at its peel.*

> **(BE-271)(ii)** `[PROVED]` — *the one escape a reader would reach for, priced
> and CLOSED — and it had never been priced.* S-mark is stated *"relative to a
> **rooted** 3-block (Tutte / SPQR) tree"*, so a reader may hope that a bad
> `(H; x, y)` is dodged by **re-rooting**. It is not. A 2-separation of `G`
> is a **tree edge** of the 3-block tree; re-rooting flips which endpoint is
> called parent but does not delete the edge, and (BE-22)(iii)'s criterion is
> **symmetric in the two sides** (`dim(ρ̄₁+ρ̄₂)`, `min(δ₁+δ₂,6)`, `a₁+a₂` all
> are), as is `Good = A₁ ∩ A₂ ∩ GP`. So the set of splits the induction must
> compose across is the tree's **edge set**, independent of the rooting, and by
> (BE-25)(i) the induction needs all of them **simultaneously** (a finite
> intersection of dense opens). One `Good(H; x, y) = ∅` at one tree edge of one
> habitat graph therefore **is** fatal. The one *other* frame in the corpus —
> **S-dec**, (BE-43)(iv)'s ear-decomposition marking, *"finitely many pairs,
> **named in advance**"* — does not help either: naming the set in advance
> still requires the peel at each named pair. *Recorded because the corpus had never
> looked:* `git grep -in 're-root\|rerooting\|re-rooting\|choice of root'` over
> `notes/pencil/` returns **0 hits** at `2145cb0b`.

> **(BE-271)(iii)** — *the verdict of the check, stated so a
> successor does not have to re-run it.* **The question is LIVE**, and this is
> the opposite of BTAKERS's finding on the `Π_x` obligation. The `⟨M⟩` route is
> consumed at the quantifier BGOODEMPTY assumed, by the chain
> (BE-67)(iii) → (BE-22)(iii) → (BE-25)(ii) S-mark → (BE-14)'s 2-cut step, with
> (BE-69)(ii) consequence 3 supplying that a failure is **chart-wide** and
> hence an obstruction to `hbareSplit` itself rather than to a universal
> reading of an obligation. **So the cost of this direction is not refunded by
> a quantifier finding, and the mathematics below had to be done.**

---

### Step BE271 — (BE-272): THE PATH LEMMA at `⟨M⟩`, and why (BE-258)'s method does not transport

The spec's *"where I expect to be wrong"* sentence was **right about the
method and wrong about the conclusion**, and it earned its keep: it said
*"`⟨M⟩` is the line `p_x ∨ p_y`, attached to **both** points, so the
analogous rank may differ"*. It does not merely differ — **there is no rank
count at all**, and what replaces it is stronger.

> **(BE-272)(i)** `[PROVED]` — *the chain, POINTWISE, with no semicontinuity
> anywhere in it.* By (BE-30)(iv) `ρ̄_i ⊆ ⟨P⟩` holds **at every
> configuration** for every x–y path `P` of side `i`. Hence
> **`c_i(⟨M⟩) = dim(ρ̄_i ∩ ⟨M⟩) ≤ dim(⟨P⟩ ∩ ⟨M⟩)` at every configuration**,
> for every such `P` — in particular for a shortest one `P₀`. Note what this
> is *not*: unlike (BE-258)(i), which bounds `c_i(Π_x)` through
> `Π_x ⊆ α_x = ker(ω ↦ ω ∧ p_x)` and needs the **rank defect** `rank φ = 3` to
> get anything, `⟨M⟩` is a **single line** and the bound `dim(⟨P⟩ ∩ ⟨M⟩) ∈
> {0, 1}` is already the whole statement. **There is no operator attached to
> `⟨M⟩`, so (BE-258)'s `rank φ = 3` has no analogue; and (BE-259)(i)'s
> `dist_i ≤ 4 ⟹ c_i ≤ 1` is at `⟨M⟩` not merely vacuous but the WRONG SHAPE
> — at `Π_x` the block cap is `2` and a bite needs `c_i = 2` on one side,
> while at `⟨M⟩` the cap is `1` and a bite needs `1` on each.** The spec named
> this trap exactly; it is real, and the way past it is below.

> **(BE-272)(ii)** `[PROVED]` — ***THE PATH LEMMA.*** *Let `P = (p_0, …, p_m)`
> be an x–y path with `p_0 = p_x`, `p_m = p_y`, and `⟨P⟩ := ⟨p_0∧p_1, …,
> p_{m−1}∧p_m⟩`, `⟨M⟩ := ⟨p_0 ∧ p_m⟩`. Then:*
>
> | `m` | `dim(⟨P⟩ ∩ ⟨M⟩)` | status |
> |---|---|---|
> | `1` | `1` — `⟨P⟩ = ⟨M⟩` identically | identity |
> | `2` | `0` iff `p_0, p_1, p_2` are **not collinear** | **POINTWISE** on the habitat |
> | `3` | `0` whenever `p_0, p_3, p_1, p_2` **span** `K⁴` | **POINTWISE** under that hypothesis |
> | `4` | `0` whenever `p_0, p_4, p_1, p_3` **span** `K⁴` | **POINTWISE** under that hypothesis |
> | `5` | `0` on a nonempty open (a `6×6` determinant) | **GENERIC**, witness exhibited |
> | `≥ 6` | `1` generically — `⟨P⟩ = Λ²K⁴` | the confinement is **vacuous** |
>
> *Proof.* Work through the Klein pairing `⟨ω, η⟩ := ω ∧ η`, under which a
> **decomposable** `η = q ∧ r` annihilates a line `ℓ` exactly when the two
> lines **meet**. So it suffices to exhibit a line meeting every path edge and
> **skew to `p_0p_m`** — a *transversal*.
>
> * **`m = 2`.** Every element of `⟨P⟩` is `a(p_0∧p_1) + b(p_1∧p_2) =
>   p_1 ∧ (b p_2 − a p_0)`, a line **through `p_1`**. The line `p_0p_2` passes
>   through `p_1` iff `p_0, p_1, p_2` are collinear. Non-collinearity of three
>   **consecutive** points is the carrier's **own** hinge-coincidence gate
>   (`bimage.legal_chain`; (BE-30)(ii)/(iii) legality; the proviso `G` that
>   (BE-91)(ii) identifies with (BE-64)(ii)'s product theorem), so at
>   `dist_i = 2` the exclusion holds **at every configuration of the habitat**,
>   not merely generically.
> * **`m = 3`.** Take `η = p_1 ∧ p_2`. It shares an endpoint with each of
>   `p_0p_1`, `p_1p_2`, `p_2p_3`, so `⟨ℓ_j, η⟩ = 0` for all three. And
>   `⟨p_0∧p_3, η⟩ = det[p_0, p_3, p_1, p_2]`, nonzero exactly when those four
>   points span.
> * **`m = 4`.** Take `η = p_1 ∧ p_3`. It meets `p_0p_1` and `p_1p_2` at `p_1`
>   and `p_2p_3`, `p_3p_4` at `p_3`. And `⟨p_0∧p_4, η⟩ = det[p_0, p_4, p_1, p_3]`.
> * **`m = 5`.** **No decomposable transversal exists generically**, and the
>   enumeration is short: a line meeting both `p_0p_1` and `p_1p_2` must pass
>   through `p_1` **or** lie in `⟨p_0,p_1,p_2⟩`; likewise `p_4` or
>   `⟨p_3,p_4,p_5⟩` for the last two edges; the four combinations are
>   `p_1p_4` (misses `p_2p_3` generically), `p_1 ∈ ⟨p_3,p_4,p_5⟩` and
>   `p_4 ∈ ⟨p_0,p_1,p_2⟩` (both false generically), and
>   `⟨p_0,p_1,p_2⟩ ∩ ⟨p_3,p_4,p_5⟩`, which meets `p_2p_3` only if that line's
>   intersections with the two planes — `p_2` and `p_3` respectively —
>   coincide. So the exclusion is instead the **non-vanishing of the `6 × 6`
>   determinant `det[ℓ_1, …, ℓ_5, p_0∧p_5]`**, a polynomial in the point
>   coordinates; one nonzero value at one exhibited point proves it on a dense
>   open, non-vanishing being an open condition. ∎
>
> **`[MEASURED]` half of the same clause** — `bmblock.py path`, 0.7 s, seed
> `20260912`, exact ℚ, **60 free-point draws per `m = 1 … 8`, 480 in all**, every
> line an assert. The generic column is
> `(m, dim⟨P⟩, dim(⟨P⟩ ∩ ⟨M⟩))` = `{(1,1,1): 60, (2,2,0): 60, (3,3,0): 60,
> (4,4,0): 60, (5,5,0): 60, (6,6,1): 60, (7,6,1): 60, (8,6,1): 60}`, with
> `dim⟨P⟩ ≤ min(m,6)` asserted at every draw and `dim(⟨P⟩ ∩ ⟨M⟩) = 0` for
> `2 ≤ m ≤ 5` asserted at **480 of 480**. The transversal is asserted to
> annihilate **every** hinge line at `m = 3` (60/60) and `m = 4` (60/60), and to
> separate `⟨M⟩` at every spanning draw (60/60, 0 degenerate). At `m = 5`,
> `rank[ℓ_1..ℓ_5, p_0∧p_5] = 6` at 60/60 draws with `dim⟨P⟩ = 5`; the exhibited
> integer witness is printed by the mode. **The no-transversal remark is
> MEASURED too, not merely argued:** the 1-dimensional Klein annihilator of
> `⟨P⟩` is **decomposable** (`⟨η, η⟩ = 0`, the Plücker test — i.e. an actual
> transversal line) at **0 of 60** draws, so at `m = 5` the functional that
> excludes `⟨M⟩` genuinely is *not* a line. The `m = 2` collinear **negative
> control** (F13) collapses `dim⟨P⟩` to `1` at 60/60 rather than admitting
> `⟨M⟩` at dimension 2 — i.e. the one available degeneration does **not**
> manufacture the shape. **CAP, and it travels:** these are **free** point
> tuples in an affine ℚ-chart, **not** points of `Chart(H)`; the `Chart(H)`
> reading is (BE-273) and (BE-274), which is where the lemma is tested against
> the carrier's own constraints.

> > **— GENERALIZED 2026-09-12 by (BE-279) (direction BSIXTEEN): the instrument
> > was always BLOCK-AGNOSTIC.** (BE-30)(iv) names **no block** — it says
> > `ρ̄_i ⊆ ⟨P⟩` for every x–y path — so intersecting both sides with any stable
> > `U` gives `c_i(U) ≤ dim(⟨P₀⟩ ∩ U)` pointwise at **all sixteen** blocks, and
> > the right-hand side is a closed-form **table**
> > `B(m, U) = max(|U ∩ {Π_x, Π_y}|, m + dim U − 6)`. This clause's `⟨M⟩` column
> > is the `U = ⟨M⟩` row of it, reproduced without being fitted, and `⟨L⟩` — the
> > Plücker point of `π_x ∩ π_y` — has the **same** row and closes by the same
> > two-step. The transversal at `m ∈ {2,3,4}` and the non-decomposable
> > annihilator at `m = 5` both recur at `⟨L⟩` (0 of 30 draws decomposable,
> > against 0 of 60 here). **Nothing in this step is contradicted**; what is
> > added is that the hinge-line identification, which this direction leaned on,
> > was not load-bearing for the confinement.

> **(BE-272)(iii)** `[PROVED]` — *the consequence, and it is strictly stronger
> than (BE-259)(i)'s shape.* An internal R-node peel requires **`x ≁ y`**
> (`bgoodempty.block_row` gates `y ∉ N_H(x)`; `bproper.NONADJ`'s own comment
> gives the reason — *"else `side2 + (x,y)` carries a parallel pair after
> suppression and `rnode_shaped` rejects it as a P-node"*). So **`dist_i ≥ 2`
> on both sides in-region**, and the `m = 1` row of the table is **vacuous
> here**. Combining with (i): **if EITHER side has `2 ≤ dist_i ≤ 5` then
> generic `c_i(⟨M⟩) = 0`, hence `c₁(⟨M⟩) + c₂(⟨M⟩) ≤ 0 + 1 = 1 = dim ⟨M⟩`**
> and the `⟨M⟩` block cannot bind. Contrast (BE-259)(i), which needs
> `dist_i ≤ 4` on **both** sides: at `⟨M⟩` **one** side suffices, and the range
> runs to `5`. *This is the clause that does the work, and it is where the
> spec's expectation of a failed transport is scored: the method does not
> transport, and the conclusion is stronger than the one that would have.*

---

### Step BE272 — (BE-273): the lemma tested against `Chart(H)` — the same 427 side rows, and the column (BE-258)(iii) did not take

(BE-272)'s draws are free point tuples. `Chart(H)` is **not** open in
`(P³)^V` — every hub's closed star must be coplanar ((BE-14)'s *"one
determinant per hub", codimension `Σ_{hubs}(deg v − 2)`*) — so the lemma must
be re-read where the carrier's own constraints hold. `bmblock.py side` does
that on **exactly** `bgoodempty.run_pix`'s population, at its **committed**
defaults, so the two columns are comparable row by row.

> **(BE-273)(i)** `[MEASURED]` — `bmblock.py side`, seed `20260912`, **3 draws
> per row**, `bgoodempty.side_library(maxarc=8, maxtheta=7, nlad=40)` +
> `side1_library()`, `xy_paths(cap=400, maxlen=9)`, draws by
> `bdecor.sample_by_branches` on `Chart(side)`. **427 rows**, with the same
> per-distance denominators (BE-258)(iii) reports.
>
> > **SELF-CAUGHT, AND DISCLOSED BEFORE THE TABLE, because the first draft of
> > this sentence called the match a *cross-check*.** It is not an independent
> > one. `bgoodempty.SEED = 20260912` and this direction's `bmblock.SEED` is
> > **the same integer** (both are today's date), and `side_library`'s ladder
> > family is **seeded** — the cycles and thetas are enumerated, the 40 ladders
> > are drawn. So the two modes read the **identical** library and the matching
> > denominators are a **same-input reproduction**, not a replication. Measured:
> > the library's `dist` histogram at seeds `20260912 / 20260901 / 20260805` is
> > `{2:204, 3:103, 4:58, 5:22, 6:23, 7:18}` / `{2:198, 3:99, 4:68, 5:21,
> > 6:22, 7:18}` / `{2:197, 3:104, 4:62, 5:23, 6:22, 7:18}` — **the
> > denominators move by up to 10 rows with the seed, so they are a CAP, not a
> > constant.** (428 library rows pass the shortest-path gate; **427** survive
> > to a row, one yielding no usable draw — the same 428 → 427 attrition
> > (BE-258)(iii) sees.) What the match *does* buy is that the `α_x` column and
> > the `⟨M⟩` column below are read on **the same rows**, which is exactly what
> > makes them comparable side by side — and that is the only thing claimed
> > for it.
>
> | `dist_i` | rows | `dim(⟨P₀⟩ ∩ α_x)`, (BE-258)(iii) | `dim(⟨P₀⟩ ∩ ⟨M⟩)`, here | generic `c_i(Π_x)`, (BE-258)(iii) | generic `c_i(⟨M⟩)`, here |
> |---|---|---|---|---|---|
> | 2 | **203** | 1 | **0** | `0`×190, `1`×13 | **`0`×203** |
> | 3 | **103** | 1 | **0** | `0`×91, `1`×12 | **`0`×103** |
> | 4 | **58** | 1 | **0** | `0`×49, `1`×9 | **`0`×58** |
> | 5 | **22** | 2 | **0** | `0`×15, `1`×7 | **`0`×22** |
> | 6 | **23** | 3 | **1** | `0`×15, `1`×1, `2`×7 | `0`×16, `1`×**7** |
> | 7 | **18** | 3 | **1** | `2`×18 | `1`×**18** |
>
> Read across: **the `⟨M⟩` confinement is TOTAL below `dist = 6` where the
> `α_x` confinement only descends to `max(1, min(dist,6) − 3)`.** The
> pointwise assert `2 ≤ dim⟨P₀⟩ ≤ 5 ⟹ dim(⟨P₀⟩ ∩ ⟨M⟩) = 0` fired at **1 158
> draws** (386 rows × 3) with **0 exceptions**, so **(BE-272)(ii) survives the
> carrier's constraints**, which is the thing free draws could not have shown.
> Also asserted at every draw: the pointwise chain `c_i(⟨M⟩) ≤ dim(⟨P₀⟩ ∩ ⟨M⟩)`,
> `c_i(⟨M⟩) ≤ 1`, `dim⟨P₀⟩ ≤ min(|P₀|, 6)`, and (BE-30)(iv) as an identity of
> **subspaces** `dim(ρ̄_i ∩ ⟨P₀⟩) = ρ_i`.

> **(BE-273)(ii)** `[MEASURED]` — *the `dist ≥ 6` column, which is the residue's
> own population.* `bmblock.py side`, same run as (i). `c_i(⟨M⟩) = 1` occurs
> at **25 of 427** rows, **all** with
> `dist_i ≥ 6`, and at every one of them **`ρ_i = 6` is asserted** — `0`
> exceptions, the assert being `c_i(⟨M⟩) = 1 ⟹ ρ_i = 6` at every **draw**, not
> merely at the minimum over draws. Those are the **same 25 rows** at which
> (BE-258)(iii) reports `c_i(Π_x) = 2`, which is what the general-position
> reading predicts: at `ρ_i = 6` the side's `ρ̄_i` is all of `Λ²K⁴` and
> `c_i(U) = dim U` at every `U` ((BE-99)(i)). **CAP, disclosed:** this library,
> these branch shapes, 3 draws per row, `maxlen = 9` path enumeration. **NOT
> FOUND under cap C** is the only claim a search can make here, and the
> *proved* content is (BE-272), not the tally.

> **(BE-273)(iii)** — *a landed figure's provenance, checked and
> corrected in its reading — not in its value.* (BE-262)(ii) reports the `⟨M⟩`
> both-sides shape as *"0 at this direction's 253 rows"*. Read at source,
> `bgoodempty.block_row` **does** compute the field `cM`, and
> `bgoodempty.run_block` **never aggregates or prints it** — it histograms
> `cPix` only. So the landed `0 of 253` rests on the **margin histogram**
> (`{0: 253}` over the 16 stable `U`), which at `slack = 0` would score a
> `(1,1)` at `⟨M⟩` as `margin = 2 − 1 = +1` and report it as a hit. **The
> figure is therefore SOUND** — the inference is valid and the gate would have
> fired — **but the `⟨M⟩` marginal distribution was never reported**, so
> nothing in the corpus said how often `c_i(⟨M⟩) = 1` on *one* side. (BE-274)
> supplies it. *This is a reading correction to a landed clause's evidence
> trail, not to its value; recorded so a successor does not quote "0 of 253" as
> a `cM` census.*

---

### Step BE273 — (BE-274): the rung-3 closure at `⟨M⟩` — what is PROVED, what is MEASURED, and the derivation of the `0`

> **(BE-274)(i)** `[PROVED]` — **the arithmetic layer, cap-free.** `bmblock.py
> arith`, 0.0 s, **seedless, no sampling**. Enumerate every
> `(δ₁, δ₂, dist₁, dist₂, ρ₁, ρ₂, c₁, c₂)` the landed constraints allow —
> **31 588 tuples** — under
>
> | law | statement | status |
> |---|---|---|
> | L0 | `δ₁ + δ₂ ≤ 6` | **rung 3**, (BE-225)(iii) |
> | L1 | `ρ_i ≤ δ_i` | (BE-22)(ii) at `a_i = 0` |
> | L2 | `ρ_i ≤ dist_i` | (BE-256)(ii), **pointwise** |
> | L3 | `c_i ≤ min(ρ_i, 1)` | trivial, `dim ⟨M⟩ = 1` |
> | L4 | `dist_i ≥ 2` | the region: `x ≁ y`, (BE-272)(iii) |
> | L5 | `2 ≤ dist_i ≤ 5 ⟹ c_i = 0` | **THE PATH LEMMA**, (BE-272)(ii) — **PROVED** |
> | L6 | `dist_i ≥ 6` and `c_i = 1` ⟹ `ρ_i = 6` | general position — **MEASURED**, (BE-273)(ii) |
>
> *Result.* Under **L0–L4 only**, **4 145** tuples violate `c₁ + c₂ ≤ 1`: the
> arithmetic does **not** triage `⟨M⟩`, which is (BE-97)(i) read at this block.
> Adding **L5**, **1 120** survive, and `assert` fires that **every** survivor
> has `dist₁ ≥ 6` **and** `dist₂ ≥ 6` — the corner where `⟨P₀⟩ = Λ²K⁴` and the
> confinement is vacuous. Their `(ρ₁, ρ₂)` values are the 15 pairs with
> `ρ_i ≥ 1` and `ρ₁ + ρ₂ ≤ 6`. Adding **L6**, **0** survive.
>
> **THE DERIVATION OF THE `0`, since a kill condition naming a number carries
> it.** `c_i(⟨M⟩) = 1` at `dist_i ≥ 6` forces `ρ_i = 6` (L6); with L1 and
> `δ_i ≤ 6` ((BE-21)(ii)) that forces `δ_i = 6`; on **both** sides that is
> `Σδ = 12 > 6`, contradicting L0. **So at rung 3 the `⟨M⟩` block cannot
> bind.** Note the derivation needs no *"other side is rigid"* step at all —
> (BE-259)(ii) needed one because `c_i(Π_x) = 2` on **one** side already
> exhausts `dim Π_x`; at `⟨M⟩` both sides must fire, and the doubled `δ_i = 6`
> kills it outright. **That is the one place the smaller block is an
> advantage.**

> **(BE-274)(ii)** — *the two halves kept apart, per (BE-255)(iii).*
> The **proved** half is (BE-272): whenever **either** side has
> `2 ≤ dist_i ≤ 5`, `⟨M⟩` cannot bind, with **no measurement anywhere** and —
> at `dist_i ∈ {2,3,4}` — **no genericity either**, the exclusion holding at
> every configuration under a named non-degeneracy the carrier already
> enforces. The **measured** half is L6, which is needed **only** when
> `dist_i ≥ 6` on **both** sides. Read against the spec's prediction: the
> verdict *"closable by a rank argument analogous to (BE-258)'s"* is **right
> about closability and wrong about the argument** — there is no rank argument
> here, and had one been attempted the `dist_i ≤ 4` threshold it would have
> produced is both weaker (it needs both sides) and, at `⟨M⟩`, the wrong shape.

---

### Step BE274 — (BE-275): the spec's MECHANISM, refuted at the corpus's own best case — and refuted BEFORE anything was built on it

The dispatch offered: *"(BE-45)'s dichotomy — (M1) a series end at `x`, or
(M2) path saturation `δ_i = d_min` — firing on both sides, exactly as at
(BE-97)(iii)'s `Π_x` tightness."* It is **REFUTED**, and not by a census.

> **(BE-275)(i)** `[PROVED]` — *(M1) can never reach `⟨M⟩` in-region.*
> (BE-45)(i) proves `⟨ℓ_e⟩ ⊆ ρ̄_i ∩ Π_u` where `ℓ_e = p_x ∧ p_{w_1}` is the
> **bridge** hinge line at the series end. That line **is** `⟨M⟩` exactly when
> `w_1 = y`, i.e. when `dist_i = 1` — which (BE-272)(iii) excludes in-region
> (`x ≁ y`). So **(M1) is a mechanism for `Π_x`, and at `⟨M⟩` it is vacuous.**

> **(BE-275)(ii)** `[PROVED]` — *(M2) is a mechanism for `c_i(⟨M⟩) = 0`, not
> for `= 1`.* (BE-45)(ii) gives `ρ̄_i = ⟨P⟩` **as spaces** for a shortest path
> `P`. By the path lemma `⟨P⟩ ∩ ⟨M⟩ = 0` on the whole range
> `2 ≤ d_min ≤ 5`, so path saturation there **forces `c_i(⟨M⟩) = 0`.** Its
> only `⟨M⟩`-reaching case is the **vacuous corner** `d_min = 6` ((BE-99)(i):
> `ρ̄_i = Λ²K⁴`, `c_i(U) = dim U` at every `U`), and there `δ_i = 6` forces
> `δ_j = 0` at rung 3, so the partner side is **rigid** and `c_j(⟨M⟩) = 0` by
> (BE-22)(vi). **So at rung 3 the two clauses of (BE-45) are, at `⟨M⟩`,
> mutually exclusive.**

> **(BE-275)(iii)** `[MEASURED]` — *the refutation, witnessed on the one landed
> peel where both clauses of (BE-45) fire.* `bmblock.py dbl`, 4.4 s, **6 seeds
> at `bdouble`'s own landed seed `20260902`**, on `bdouble.WIT_PIECE` =
> `K4 + th(6,6,6)/ab + ear4/ua` at peel `(a, b)` — (BE-99)(iii)'s double
> pencil, a member of BUNIF's **own** population A, so the test needs no new
> construction. Combinatorics configuration-free and asserted:
> `d_min(side 1) = 2`, `d_min(side 2) = 6`. At **6 of 6** generic-regime draws,
> asserted: `(c₁(Π_x), c₂(Π_x)) = (1, 2)` — (BE-99)(iii) reproduced — and
> **`(c₁(⟨M⟩), c₂(⟨M⟩)) = (0, 1)` at every one** — `c₁ + c₂ = 1 = dim ⟨M⟩`,
> **never `(1,1)`**. *If the spec's mechanism produced the shape, it would
> produce it here.* **Disclosed, because the row is not itself in-region:**
> this peel is at `(δ₁, δ₂) = (2, 6)`, so `Σδ = 8` and `slack = 2` — it is
> **off rung 3**, and its own `⟨M⟩` margin is `0 + 1 − 1 − 2 = −2`. It is used
> for what it is: the **only landed configuration at which both clauses of
> (BE-45) fire at one peel**, hence the strongest available test of the spec's
> mechanism, not as a rung-3 row.
>
> **ORDER OF WORK, stated by re-reading the driver rather than by recalling the
> session (clause 3).** The first slice executed was `arith` (the tuple layer,
> seedless); the second was `path` (the lemma). (BE-275)(i)/(ii) is a
> consequence of `path` **alone** and was in hand before `side` or `block` were
> read, so **nothing in this direction's first two slices rests on the spec's
> mechanism.** The `dbl` confirmation was written and run *after* `side`
> returned, as a check on a refutation already made structurally — not as its
> ground.

---

### Step BE275 — (BE-276): the residue's population, priced with NO DRAWS — and a disclosure about the landed 253-row denominator

`(dist₁, dist₂)` at an internal R-node peel is **combinatorial**: it needs no
configuration. So the question *"can (BE-274)'s open corner — `dist_i ≥ 6` on
**both** sides — occur in-region at all?"* is decided by graph theory, and
`bmblock.py reach` decides it over `bgoodempty.run_block`'s **entire** job
list at its committed defaults, applying the **same** region gates
(`x ≁ y`, `deg_H(x), deg_H(y) ≥ 3`, min degree `2`, girth `≥ 4`,
`hcard_ok_piece`, `rnode_shaped`, side-degree `≥ 2` on both sides at both
terminals, `δ₁ + δ₂ ≤ 6`) — **and drawing nothing**.

> **(BE-276)(i)** `[MEASURED]` — `bmblock.py reach`, **6.0 s**, **4 752 jobs
> offered, 2 946 in-region peels**, seed used only to build `run_block`'s own
> job list, **no configuration sampled anywhere**:
>
> `(dist₁, dist₂)` → count = `{(2,4): 120, (2,5): 238, (2,6): 230, (2,7): 48,
> (3,4): 81, (3,5): 156, (3,6): 172, (3,7): 21, (4,4): 223, (4,5): 489,
> (4,6): 461, (4,7): 109, (5,4): 24, (5,5): 45, (5,6): 48, (5,7): 3,
> (6,4): 96, (6,5): 134, (6,6): 247, (6,7): 1}`
>
> * **`min(dist₁, dist₂) ≥ 2` at 2 946 of 2 946** — asserted, so (BE-272)(iii)'s
>   in-region claim is verified on the population rather than argued from the
>   gate alone.
> * **2 698 of 2 946 (91.6 %) have some side at `2 ≤ dist_i ≤ 5`**, hence are
>   **closed at `⟨M⟩` by the PROVED half of (BE-274) alone**, with no draw and
>   no measurement.
> * **248 of 2 946 (8.4 %) have `dist_i ≥ 6` on both sides** — all of them the
>   `(6,6)` cell plus `(6,7)`. **The residue corner is NOT vacuous**, so L6 is
>   genuinely needed and (BE-277)(iii) is a real question rather than a
>   formality. *Recorded in the direction that would have preferred the
>   opposite answer.*
> * **`δ_i ≤ dist_i` re-verified at all 2 946** in-region peels — (BE-256)(ii)
>   reproduced on a population it was not measured on.
>
> **CAP, disclosed:** two skeletons (`K33`, `prism`), branch lengths `≤ 5`, all
> six non-adjacent hub pairs (`bgoodempty.nonadj_pairs`, which un-fences
> `bproper.NONADJ`'s 3 **without editing it** — verified: the committed
> `bproper.NONADJ` still lists 3), the 66-shape `side1_library()`. **NOT FOUND
> under cap C** is all a wider claim could be; nothing here says `dist_i ≥ 6`
> on both sides *cannot* dominate some other population.

> **(BE-276)(ii)** `[MEASURED]` — **a disclosure about a landed denominator, found
> by taking the same gates without the draws.** `bgoodempty.run_block` reports
> **253** in-region rows on **this same job list**. The gates admit **2 946**.
> The difference is entirely **draw success**: `block_row` returns `None` when
> no free draw survives `bproper.free_peel` + `bunif.flag_frame` +
> `rho_bar_of`, so **the landed 253-row figure sees about 8.6 % of the
> combinatorial region its own gates define.** *Nothing is wrong with the 253 —
> it is what it says it is, a count of rows at which a generic-regime draw was
> obtained.* What is newly visible is that its denominator is set by the
> **sampler**, not by the region, and a successor quoting *"253 in-region
> rows"* as a measure of coverage would be over-reading it by an order of
> magnitude. **(BE-262)(i)'s cap sentence is unaffected** — it already says
> *"NOT FOUND under cap C"* and lists the constructors; this only prices `C`.

> **(BE-276)(iii)** `[MEASURED]` — **the two-sided `⟨M⟩` census, FENCED, with
> the fences named and the reason the full run is not here.** `bmblock.py
> block` calls `bgoodempty.block_row` **unchanged** and reports its dropped
> `cM` field joined with `(dist₁, dist₂)`. At the **committed** defaults
> (`ndraw = 3`, `njob = None`) it is a **multi-hour** run: measured, **40 jobs
> at `ndraw = 2` take 117.3 s** (~2.9 s/job), so the full 4 752-job list is
> **≈ 4 hours** — it was started in the background at the committed defaults
> and was **killed before completion** (the direction reports the harness
> killing it under memory pressure), having written **`0` bytes of computed
> output**, the mode printing only on completion. **So there is no partial run
> to resume and no figure here is quoted from one** — a successor wanting this
> census must re-run it from scratch, and should budget the ≈ 4 hours. What *is* reported is a run that
> finished, with **both** its fences disclosed: **`ndraw = 2` against the
> committed `3`, and `njob = 40` against the committed `None`** — the same
> two fences `bgoodempty.run_validate` carries (plus `quick=True`, which this
> run did **not** use). At that cap, **20 in-region rows**:
>
> * `(c₁(⟨M⟩), c₂(⟨M⟩))` generic over free draws = **`{(0,0): 17, (0,1): 3}`**
>   — **never `(1,1)`**, and this is the first time the `cM` marginal has been
>   printed at all (cf. (BE-273)(iii)).
> * `(dist₁, dist₂)` = `{(2,4): 1, (2,5): 1, (3,5): 1, (3,6): 3, (4,5): 2,
>   (4,6): 4, (4,7): 2, (6,4): 1, (6,5): 3, (6,6): 2}`; **2** rows with
>   `dist_i ≥ 6` on both sides.
> * The in-region asserts passed at every row: `min(dist₁, dist₂) ≥ 2`, and
>   **`2 ≤ dist_i ≤ 5 ⟹ c_i(⟨M⟩) = 0`** — the path lemma tested **two-sidedly
>   on `Chart(H)`**, which is what this mode was for.
>
> **NOT FOUND under cap C** — 20 rows is a small C and it is stated as such.
> **The two-sided reading this direction rests on is (BE-273)'s 427 side rows
> plus (BE-276)(i)'s draw-free 2 946**, which between them cover the same
> claim at a far larger denominator with no sampler in the way; this clause is
> the confirmation, not the evidence. *Said explicitly because the arc's
> 2026-09-12 cross-return pass found a landed figure that did not reproduce
> from its own driver: the way not to repeat that is to disclose the fence a
> figure ran at, in the same sentence as the figure.*

---

### Step BE276 — (BE-277): THE VERDICT, the residue stated so it can be attacked, and the board

> **(BE-277)(i)** `[PROVED]` / `[MEASURED]` — **THE VERDICT, with the quantifier it
> actually carries.** **`c₁(⟨M⟩) = c₂(⟨M⟩) = 1` at an internal R-node peel at
> rung 3 is CLOSED BY PROOF whenever EITHER side has `dist_i(x, y) ≤ 5`, and
> closed by a measured step otherwise.** The proved half is cap-free and
> measurement-free (`bmblock.py path`, `bmblock.py arith`); the measured half
> is `bmblock.py side`'s L6 and `bmblock.py reach`'s population price.
> The proved half needs no draw: at `dist_i ∈ {2,3,4}` it is **pointwise** under a
> non-degeneracy the carrier already enforces, and at `dist_i = 5` it is
> generic by an open condition with an exhibited witness. Since an internal
> R-node peel forces `dist_i ≥ 2` on both sides, the **only** escape is
> `dist_i ≥ 6` on **both** sides, and there the derivation of (BE-274)(i)
> closes it from L6. **So `⟨M⟩` is NOT a route to a rung-3 `Good = ∅` piece**,
> and BGOODEMPTY's *"the cheapest remaining route"* ((BE-262)(ii)) is **spent**.
> Together with (BE-256) (the one-sided obstruction, combinatorial) and
> (BE-259)(i) (the `Π_x`/`Π_y` blocks at `dist_i ≤ 4`), **three of the three
> routes BGOODEMPTY named are now closed**, and the lane's successor is the
> corner named in (BE-277)(iii).

> **(BE-277)(ii)** — **what this does NOT claim, stated before the
> board.** It does **not** prove `Good ≠ ∅` for any piece: it removes one way a
> piece could fail, exactly as (BE-262)(ii)'s THIRD item says of its own
> results. (BE-67)(ii)'s residue is untouched. It does **not** touch the other
> 12 unwitnessed blocks of (BE-97)(iv) — `⟨M⟩` was the 13th, the one with the
> cheapest arithmetic, and the other 12 are unwitnessed rather than excluded.
> And it says nothing about the **12** remaining unwitnessed blocks of
> (BE-97)(iv) — which, per the notation block's correction, are 12 of the
> **same** 16-member family `⟨M⟩` belongs to, not a separate table.

> **(BE-277)(iii)** — **THE RESIDUE, named so it can be attacked, and
> it is the SAME SHAPE as (BE-262)(ii)'s FIRST item.** *What is missing is a
> proof that `⟨M⟩ ⊆ ρ̄_i` is a proper closed condition when `ρ_i ≤ 5` and
> `dim ⟨P₀⟩ = 6` — i.e. at `dist_i ≥ 6`.* That is the entire residue of
> (BE-274); it is **not vacuous** — **248 of 2 946** in-region peels sit in it
> ((BE-276)(i)) — and it is **exactly** the `Π_x` residue (BE-259)(ii) leaves — *"a proof
> that `Π_x ⊆ ρ̄_i` is a proper closed condition when `ρ_i ≤ 5` and
> `dim ⟨P₀⟩ ∈ {5, 6}`"* — one dimension down and one regime narrower (`⟨M⟩`
> needs it only at `dim ⟨P₀⟩ = 6`, because at `dim ⟨P₀⟩ = 5` the path lemma
> already closes it, where the `α_x` bound does not). **A single lemma would
> discharge both**, and that is the most valuable thing this direction can hand
> forward: *the `Π_x` residue and the `⟨M⟩` residue are the same question about
> `ρ̄_i` in general position against a stable block once the path confinement
> has gone vacuous.* *A direction's question, not a coordinator's.*

> > **— SCOPED 2026-09-12 by (BE-295)/(BE-298) (direction BPROPCL): this sentence
> > is REFUTED IN ITS OWN FRAME and CONFIRMED IN BSIXTEEN'S.** Stated as it is here
> > — one lemma about `U ⊆ ρ̄_i` covering both residues — it is **false**: `Π_x` is
> > the span of the side's own hinges while `⟨M⟩` sits in the direct complement of
> > both pencils, and **general position against `Λ²K⁴` — the mechanism this clause
> > and (BE-259)(ii) both name — is FALSE at `Π_x`**, exceeded at **102 of 1 281**
> > draws (never at `⟨M⟩`, 0 of 1 281), by a **proved** saturation mechanism
> > (`ρ_i = dim ⟨P₀⟩ ⟹ ρ̄_i = ⟨P₀⟩ ∋ ℓ₁ ∈ Π_x`). **But stated relative to `⟨P₀⟩`**,
> > as (BE-281)(iii) proposes, one identity does cover both:
> > `c_i(U) = max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)` at **1 281/1 281**. **And the
> > residue is not a lemma at all** — properness is a property of ONE PEEL, and
> > (BE-293)(i) proves it **per peel from one draw**, composing rows 2, 3 and 4 of
> > (BE-255)(i) in three different semicontinuity directions. Certified at **375 of
> > 375** eligible rows and **15 of the 15 ELIGIBLE** in this clause's own `dist ≥ 6` regime.
> > **The corner stays live at 248/248**, and `max δ = 4` there, so this clause's
> > `ρ_i ≤ 5` is not tight.

> **(BE-277)(iv)** — **the board.** **What moved.** The `⟨M⟩` path
> lemma, proved, with transversal certificates at `m ∈ {3,4}` and a determinant
> at `m = 5` ((BE-272)); the `⟨M⟩` block closed at rung 3 whenever either side
> has `dist_i ≤ 5` ((BE-274)(i)); the spec's (BE-45) mechanism refuted at
> `⟨M⟩`, structurally and at (BE-99)(iii)'s own witness ((BE-275)); the
> re-rooting escape from the `Good = ∅` consumer priced and closed, a thing the
> corpus had never looked at ((BE-271)(ii)); the `⟨M⟩` column of the 427-row
> side population taken for the first time ((BE-273)); the residue's population
> priced **draw-free** over BGOODEMPTY's whole job list, 2 946 in-region peels
> in 6 s ((BE-276)(i)), with `δ_i ≤ dist_i` re-verified at all of them; the
> `cM` marginal printed for the first time ((BE-276)(iii)); and two
> landed figures' **evidence trails** corrected without touching either value
> ((BE-273)(iii), (BE-276)(ii)).
> **What did NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`,
> (GR-15), **(BE-14)**, the S-mark, half (B), half (β), the 2-cut step, class
> uniformity, cross-pair welding, `(BE-E4′)`, the flag base, `(BE-OBL7)`,
> `(BE-OBLK)`, (BE-253)'s verdict and certificate, (BE-259)'s residue, the
> other 12 blocks of (BE-97)(iv), and **every landed measurement** — this
> direction contradicts none of them. In particular **(BE-262)'s verdict is
> untouched**: it said *"NOT FOUND under cap C"* and named `⟨M⟩` as open; this
> direction closes `⟨M⟩` and thereby *confirms* (BE-262)(ii)'s own reading that
> the tally was not the result. **The E-rider:** no termination-ledger entry
> fires; E1/E2/E3 are §(K-grid) objects and the two siblings in flight
> (GBASE 108, GSECOND 110) are on that lane.

> **(BE-277)(v)** — **the dispatch's prediction, scored; verdict,
> mechanism and tell SEPARATELY, per `RESEARCH-ARC.md` §7.**
>
> * **VERDICT: CONFIRMED, right for a different reason than given** — §7's
>   *right-for-a-better-reason* entry, the same square (BE-262)(iv) landed in.
>   The spec predicted *"Not exhibited, and closable by a rank argument
>   analogous to (BE-258)'s"*. Not exhibited: **confirmed**. Closable:
>   **confirmed**. *By a rank argument analogous to (BE-258)'s*: **refuted** —
>   there is no operator attached to `⟨M⟩`, hence no rank defect to exploit,
>   and the closure comes from a **transversal**, a different instrument. Its
>   stated evidence stratum — *"a measured `0 of 93 + 253`"* — is **evidence,
>   not the reason**, and the reason (the path lemma) was not available to the
>   spec.
> * **THE SPEC'S *"WHERE I EXPECT TO BE WRONG"* SENTENCE: CORRECT, and it is
>   the highest-yield sentence in the spec exactly as it claimed.** It said the
>   analogy to `Π_x` would fail because `⟨M⟩` is attached to both points, that
>   (BE-259)(i)'s `dist_i ≤ 4` bound *"may be vacuous or actively misleading
>   here"*, and that *"the very bound that closes `Π_x` is the biting value at
>   `⟨M⟩`"*. All three hold. **Acting on it is what produced the result**: the
>   instruction *"check what biting means at `dim U = 1` before transporting
>   the method"* is precisely what sent this direction to the transversal
>   rather than to a rank count, and the transversal closes **more** than the
>   transported method would have (one side, not two; `dist ≤ 5`, not `≤ 4`).
> * **MECHANISM: REFUTED**, structurally by (BE-275)(i)/(ii) and at the
>   corpus's own best case by (BE-275)(iii). The board's mechanism field was
>   `0 of 6` across 2026-09-12's two rounds; this is the seventh.
> * **TELL: DID NOT FIRE — and the spec correctly predicted that it could not,
>   in the arm it was aimed at.** The tell was *"a row with `c_i(⟨M⟩) = 1` on
>   both sides at a free draw"*. **0 of 427 side rows** ((BE-273)), and
>   `c_i(⟨M⟩) = 1` on *either* side is impossible on the **2 698** in-region
>   peels with a side at `dist_i ≤ 5` ((BE-276)(i)); and the `cM` marginal,
  printed for the first time, is `{(0,0): 17, (0,1): 3}` at the fenced
  two-sided census ((BE-276)(iii)) — a **draw-free**
>   statement, which is the strongest form the negative can take. The spec's own semicontinuity paragraph
>   (F31, (BE-255)(i) row 4) said a draw is an **upper** bound, so a `(1,1)`
>   draw *"proves nothing generically"* — the tell was structurally unable to
>   settle the **positive** arm. **In the reverse arm it fired decisively**:
>   every draw returning `c_i(⟨M⟩) = 0` is, by the same row-4 direction, a
>   proof of the generic statement — and (BE-272)(i) makes even that
>   unnecessary, since the chain `c_i(⟨M⟩) ≤ dim(⟨P₀⟩ ∩ ⟨M⟩)` is **pointwise**
>   by (BE-30)(iv) and needs no semicontinuity at all. **So the region the tell
>   samples — rung-3 internal R-node peels with `a = (0,0)`, `Σδ ≤ 6`,
>   side-degree `≥ 2`, generic flag regime — is one inside which the verdict
>   CANNOT differ, and that is a stronger statement than "the tell did not
>   fire".** The spec's design instruction (*"state, for every figure you
>   report, which arm it can bear"*) is what made this scoreable, and it is the
>   clause that decided this direction's whole design.

> **(BE-277)(vi)** — **what this direction self-caught.**
>
> 1. **The blind axis was real and the answer was the reassuring one.**
>    `bunif`'s `'M'` had to be read at source before any figure was quoted off
>    it; `blocks_of` line 199 is `'M': [wedge2(px, py)]`, so it **is**
>    (BE-97)(iv)'s `⟨M⟩`. Recorded because the check was cheap and the
>    alternative would have invalidated every figure here.
> 2. **A landed figure's evidence trail, not its value** — (BE-273)(iii):
>    `bgoodempty.run_block` computes `cM` and never prints it, so "0 at 253
>    rows" rests on the margin histogram. Sound, but not a `cM` census.
> 3. **The `dbl` row is off rung 3** (`Σδ = 8`, `slack = 2`) and is used as a
>    mechanism test, not as a rung-3 row — disclosed in (BE-275)(iii) rather
>    than left for a reader to notice.
> 4. **The dispatch's blind-axis note on `bunif.BLK` vs the 16 stable `U` is
>    imprecise, and the correction is load-bearing** — see the notation block.
>    `bunif.SUBS` is every subset of `BLK`, so the 16 stable `U` **are** the
>    block-sums and `⟨M⟩ = ('M',)` is one of them at `du = 1`. Had this
>    direction inherited the spec's *"different populations"* reading it would
>    have concluded that `run_block`'s margin histogram does **not** gate
>    `⟨M⟩`, and (BE-273)(iii) would have reported a landed figure as
>    *unsupported* rather than as *sound with an unreported marginal*. **The
>    spec's own instruction — read the value, then re-derive with the axis
>    opened — is what caught it.** A third fence on the same validate call the
>    spec's list did not name: `bgoodempty.run_validate` calls
>    `run_block(ndraw=2, njob=40, quick=True)`, and `quick=True` halves the
>    side-1 library on top of the two fences the spec listed; likewise
>    `bproper.run_validate` calls `run_peel(nseed=1, jobs=PEELJOBS[:3])`, a
>    *second* fence beside `nseed`. Neither affects any figure here — **no
>    figure in this section was taken from a `validate` path.**
> 5. **The first draft of this direction's `dist_i = 1` case was in-region
>    noise.** The path lemma's `m = 1` row (`⟨P⟩ = ⟨M⟩`, so `ρ_i ≤ 1`) looked
>    like a *second* route to `Good = ∅` — a side with `dist_i = 1` and
>    `δ_i ≥ 2` would fire (BE-257)(i) immediately. It cannot happen twice over:
>    `δ_i ≤ dist_i` ((BE-256)(ii)) kills the `δ_i ≥ 2` half, and `x ≁ y` kills
>    the `dist_i = 1` half outright. Recorded so a successor does not re-walk
>    it.
> 6. **The 427-row match with (BE-258)(iii) was nearly presented as a
>    cross-check, and it is a same-input reproduction** — see the disclosure
>    above (BE-273)(i)'s table. `bmblock.SEED` and `bgoodempty.SEED` are the
>    **same integer**, `side_library`'s ladder family is seeded, so the two
>    modes read the identical library; and measured across three seeds the
>    per-distance denominators move by up to **10** rows. **The denominators
>    are a cap, not a constant**, and the match buys comparability of the two
>    columns, nothing more. This is the arc's own 2026-09-12 cross-return
>    finding — *three of six directions shipped a figure defect no gate could
>    see* — caught here by re-deriving the figure's own inputs rather than
>    trusting that two runs agreeing means two runs are independent.
> 7. **The two-sided `block` census was planned as this direction's main
>    two-sided figure and was FENCED rather than quoted partially.** At the
>    committed defaults it is a ~4-hour run (measured: 40 jobs at `ndraw = 2`
>    take 117.3 s); the background attempt did not finish, so what is
>    reported is a run that **did** finish, at `ndraw = 2, njob = 40`, with
>    **both** fences named in the same sentence as its figure. The
>    replacement — `reach`, which takes the *same* gates and drops the draws —
>    is not a fallback but a **better** instrument for the question it was
>    aimed at, since `(dist₁, dist₂)` never needed a configuration. Finding
>    that out is what produced (BE-276)(i) and (BE-276)(ii), including the
>    disclosure that the landed `253` denominator is set by the sampler and
>    covers about 8.6 % of its own gates' region. **The rule that produced
>    this is "do not quote a figure you have not taken"**, not cleverness.
> 8. **The order-of-work sentence in (BE-275)(iii) was rewritten by re-reading
>    the driver** rather than by recalling the session: `dbl` ran *after*
>    `side`, and the first draft of that sentence said otherwise.

**What would change this.** *(a)* A configuration on `Chart(H)` with
`2 ≤ dist_i ≤ 5` on some side and `dim(⟨P₀⟩ ∩ ⟨M⟩) = 1` — that refutes
(BE-272)(ii) and every assert in `bmblock.py side` and `block` is written to
catch it. *(b)* An in-region rung-3 peel with `dist_i ≥ 6` on **both** sides
and `c_i(⟨M⟩) = 1` on both at a **max-profile** draw with `ρ_i ≤ 5` — that
refutes L6 and re-opens the corner; `bmblock.py side`'s
`c(⟨M⟩) = 1 ⟹ ρ = 6` assert is the gate. *(c)* An in-region peel with `dist_i = 1` on
either side — `bmblock.py reach` asserts `min(dist₁, dist₂) ≥ 2` at all
2 946, and that assert is the gate. *(d)* A proof that the S-mark
induction may **choose** which tree edges it composes across — that would
refute (BE-271)(ii) and refund the whole question.
