## §(K-bare-ext) — continuation (direction BGOODEMPTY, ordinal 105, 2026-09-12): **NO `Good = ∅` PIECE FOUND — and the informative part is not the tally: TWO of the three routes to one are now CLOSED, one by a four-line COMBINATORIAL proof and one at the only block ever measured to bite on both sides.** `δ_{xy} ≤ dist(x,y)` is a theorem of the partition formula, so the one-sided obstruction `ρ_i < δ_i` is combinatorially **unreachable** (31 338 / 31 338 as a check). `rank(ω ↦ ω ∧ p_x) = 3` on `Λ²K⁴` bounds `dim(⟨P₀⟩ ∩ α_x)` by `max(1, dist_i − 3)`, so **`dist_i ≤ 4` forces generic `c_i(Π_x) ≤ 1`** — which applies to BWHOLEH's own side 1 (the `(4,4)` cycle, `dist₁ = 4`) and turns (BE-250)(iii)'s 6-of-6 free-draw control from a measurement into a **theorem**. Over **427** side rows `c_i(Π_x) = 2` occurs **only** at `ρ_i = 6`, which at rung 3 forces the other side RIGID, so the `Π_x` margin is `0` and never positive; over **253** in-region whole-`H` rows — every non-adjacent hub pair, branch lengths past the landed fence, a 66-shape side-1 library — the margin over all 16 stable blocks is `{0: 253}`. A new one-draw decision procedure for `Good = ∅` is proved and hunted: **0 certificates at 257 rows**. The spec's TELL **did not fire** and could not have settled the question — it samples the one quantity a draw cannot settle. **NOT FOUND under cap C**, never *does not exist* (*Steps BE254–BE261*)

### Standing notation (on top of *Steps BE148–BE253*)

BWHOLEH's, verbatim, plus three objects of this direction's own. Read at the
definition sites (`bimage.rho_bar_of`, `bimage.plane_at`,
`binduc.rel_screw_space`, `bdecor.d3`, `bdecor.weld_d3`,
`bdecor.sample_by_branches`, `bdecor.hcard_ok_piece`, `bpeel.SKELETONS`,
`bpeel.subdivided`, `bpeel.rnode_shaped`, `bproper.composite`,
`bproper.free_peel`, `bproper.NONADJ`, `bunif.flag_frame`, `bunif.blocks_of`,
`bunif.profile`, `bunif.blockcap`, `bunif.blockdeg`, `bunif.generic_c`):

> **`slack := max(0, δ₁ + δ₂ − 6)`**; **RUNG 3** is the locus `Σδ ≤ 6`, where
> `slack = 0` and the `Π_x` obligation is `c₁ + c₂ ≤ 2` ((BE-225)(iii)).
> **`⟨P⟩`** is the span of the hinge lines of a path `P`; **`d_min_i`** is the
> length of a shortest x–y path inside side `i`, written **`dist_i(x, y)`**
> throughout this section. **(M1)** is (BE-45)(i)'s series end, **(M2)** is
> (BE-45)(ii)'s path saturation `δ_i = d_min_i`.
>
> **NEW HERE, three objects.** **`α_x := p_x ∧ K⁴`** — the 3-dimensional
> subspace of `Λ²K⁴` whose nonzero decomposable members are the lines through
> `p_x`. It is the **kernel** of `φ: ω ↦ ω ∧ p_x`, and `Π_x = α_x ∩ Λ²π_x`, so
> `Π_x ⊆ α_x`. **`m_i := dim ⋂_P ⟨P⟩`** — the intersection over **all** x–y
> paths `P` of side `i`. **`P₀`** — a shortest x–y path of side `i`.
>
> **`Good(H; x, y)`** is used exactly as (BE-69)(i) defines it: `A₁ ∩ A₂ ∩ GP`,
> so at any of its points `a₁ = a₂ = 0` and `dim(ρ̄₁+ρ̄₂) = min(Σδ, 6)`.

**Baseline `HEAD` = `29a60d1a`**; every figure was taken against that sha.
**`HEAD` advanced to `6372ec45` while this direction ran** (BTAKERS (107) and
GCOLTRANS (106) landed): no figure here was re-taken against it, and the
coordinator re-takes the doc-cap figures at landing (item 8 below). Nothing in
either landing is read or cited by this section. **No `.lean` opened, no `lake
build`** — the 2026-08-05 hold untouched.

---

### Step BE254 — (BE-255): the semicontinuity ledger, and why it is this direction's main tool

The spec's centrepiece is (BE-69)(ii) consequence 2 — *"a draw outside `Good`
settles nothing (F27), and the asymmetry is not a convention: it is the
semicontinuity direction of clause (i)."* That is right, and it is a statement
about **one** quantity. The move this direction makes is to ask which *other*
measured quantities run the other way.

> **(BE-255)(i)** `[PROVED]` *(the ledger; every row is the semicontinuity of a
> rank, and rows 4–5 are the ones this direction spends)* On an irreducible
> `Chart(H)` a **lower** semicontinuous integer has generic value = its
> **MAXIMUM**; an **upper** semicontinuous one has generic value = its
> **MINIMUM**. So one draw is an honest bound in exactly one direction per
> quantity, and which direction decides whether a measurement can ever become a
> theorem. **Row 1** — `dim(ρ̄₁+ρ̄₂)`: lower, so a draw is a lower bound;
> *attainment* at a draw is a theorem and a *shortfall* is not. **Row 2** —
> `ρ_i = dim ρ̄_i`: lower; `ρ_i = δ_i` at a draw is a theorem, `ρ_i < δ_i` is
> not. **Row 3** — `a_i = dim M_i − 6 − f_i`: upper, because `dim M_i` is, so
> `a_i = 0` at a draw **proves** `a_i = 0` generically — the mechanism
> (BE-69)(iii) already uses. **Row 4** — `c_i(U) = dim(ρ̄_i ∩ U)`: upper on the
> locus where `ρ_i` is constant, so a draw is an **upper** bound:
> `c_i(U) ≤ k` is provable from a draw, `c_i(U) ≥ k` is not. **Row 5** —
> `m_i = dim ⋂_P ⟨P⟩` on the locus where the profile `(dim ⟨P⟩)_P` is
> constant: upper ((BE-65)(iii), which is also why (BE-66)'s tables quote the
> **minimum** over draws — its driver cap (2)).

> **(BE-255)(ii)** `[PROVED]` *(**the density lever** — (BE-69)(ii)'s dichotomy
> run in the direction the corpus has not used it)* `Chart(H)` is irreducible
> ((BE-65)(ii), citing §(K-chart) (CH-1)(a) under `hcard`, min degree `2`,
> girth `≥ 4`, characteristic `0`). Let `Ω ⊆ Chart(H)` be **any** nonempty
> open — hence dense. If `Good ≠ ∅` then `Good` is dense ((BE-69)(ii)), and two
> dense opens of an irreducible variety **meet**. So **every inequality that
> holds on a nonempty open holds at some point of `Good`, whenever `Good` is
> nonempty**, and contradicting one of `Good`'s own defining equalities there
> therefore **proves `Good = ∅`**. Consequence 2 says a draw cannot *exhibit* a
> generic shortfall; consequence 3 says a real failure is chart-wide. **The
> lever says a draw CAN exclude one** — and that, not a pile of failed draws,
> is what makes a one-draw argument decisive here.

> **(BE-255)(iii)** *(the honest limit, stated before anything is built on it)*
> The lever never converts a measured `c_i(U) ≥ 1`, a measured `ρ_i < δ_i`, or
> a measured shortfall into a theorem. Those stay **evidence**. Every clause
> below is tagged `[PROVED]` or `[MEASURED]` accordingly, and where a clause has
> a proved half and a measured half the two are separated **inside** the clause
> rather than averaged into one word.

---

### Step BE255 — (BE-256): route 1 — the one-sided obstruction is combinatorially unreachable

`Good ≠ ∅` at rung 3 needs, at one point, `a = (0,0)` and
`dim(ρ̄₁+ρ̄₂) = min(Σδ, 6) = Σδ`. With `ρ_i ≤ δ_i + a_i` ((BE-22)(ii)) and
`dim(ρ̄₁+ρ̄₂) ≤ ρ₁+ρ₂`, that forces **`ρ_i = δ_i` on BOTH sides**. So any
structural upper bound on `ρ_i` strictly below `δ_i` kills `Good` outright, and
the cheapest candidate is (BE-30)(iv)'s unconditional `ρ_i ≤ dist_i(x, y)`.

> **(BE-256)(i)** `[PROVED]` *(four lines from the partition formula the
> (6,6)-count oracle computes — and it kills the cheapest route to a
> `Good = ∅` piece outright)* The elementary partition cap is
> `def₃(G) = max over partitions 𝒫 of V(G) of [6(|𝒫| − 1) − 5·d(𝒫)]`, with
> `d(𝒫)` the number of edges joining distinct blocks; `bdecor.d3` computes it,
> and `bdecor.weld_d3` is the **same** maximum restricted to partitions with
> `x` and `y` in **one** block (welding identifies them, and `x ≁ y` so no edge
> changes status). So `f = max over all partitions` and `g = max over the
> x∼y-together ones`. *Proof.* Let `𝒫*` be optimal for `f`, let
> `P₀ = x v₁ … y` be a shortest x–y path with `k = dist(x, y)` edges, and merge
> the `t` blocks of `𝒫*` that `P₀` meets into one. The result puts `x` and `y`
> together; it has `|𝒫*| − t + 1` blocks, so the first term drops by `6(t−1)`;
> at least `t−1` edges of `P₀` crossed between those blocks and are now
> internal, so `d` drops by at least `t−1` and the second term rises by at
> least `5(t−1)`. Net loss `≤ t−1`, and `P₀` meets at most `k+1` blocks so
> `t−1 ≤ k`. Hence `g ≥ f − k`, i.e. **`δ = f − g ≤ dist(x, y)`**. ∎

> **(BE-256)(ii)** `[PROVED]` *(the consequence, and why (i) is worth proving
> rather than measuring — it also corrects a hypothesis on a landed clause)*
> `ρ_i ≤ dist_i(x, y)` holds at **every** configuration ((BE-30)(iv), by
> telescoping along a path — degenerate configurations included, since a
> degenerate one only makes `dim ⟨P⟩` *smaller*). So `δ_i > dist_i` would give
> `ρ_i < δ_i` identically on `Chart(H)` and hence `Good = ∅` with no genericity
> anywhere. By (i) **it cannot happen.** This also upgrades (BE-30)(iv)'s own
> `δ ≤ dist` clause, which it states under the hypothesis *"at a configuration
> where `H` **and** `H/uv` attain"*: the inequality is **combinatorial** and
> carries no configuration hypothesis at all, and (BE-30)(iv)'s *"tight for
> `m ≤ 5`"* observation on the ear is the `dist − δ = 0` cell of the histogram
> in (iii).

> **(BE-256)(iii)** `[MEASURED]` *(`bgoodempty.py dist`, 4.2 s — the check on
> the proof, not the ground of the claim)* **31 338 rows**, each asserting the
> side connected, `0 ≤ δ ≤ 6` ((BE-21)(ii)) and `δ ≤ dist`: cycles with arcs to
> `(8,9)`; generalized thetas on 3–5 internally disjoint paths; **ladders**
> (x–y paths that are *not* internally disjoint — a shape no cycle or theta
> supplies); the **whole** branch-profile product of subdivided `K₄` at lengths
> `1…4` plus 200 sampled profiles each of the prism and `K₃,₃`, at **every**
> vertex pair and not only the non-adjacent ones; and 400 random 2-connected
> subdivisions. `dist − δ` histogram
> `{0: 1193, 1: 7893, 2: 9815, 3: 8277, 4: 3848, 5: 278, 6: 32, 7: 2}`;
> `max(δ − dist) = 0`; **0 exceptions**. The `0` cell is the path-saturated
> (M2) locus, at 1 193 of 31 338.

---

### Step BE256 — (BE-257): route 2 — a confinement criterion that IS a theorem

> **(BE-257)(i)** `[PROVED]` *(the criterion — one max-profile exact-ℚ draw
> settles `Good = ∅` affirmatively, which is exactly the shape (BE-69)(ii)
> consequence 3 asks for)* Two facts. `ρ̄_i ⊆ ⟨P⟩` holds **pointwise** for
> every x–y path `P` of side `i` ((BE-30)(iv), the telescoping identity — no
> genericity); and `m_i = dim ⋂_P ⟨P⟩` is **upper** semicontinuous on the locus
> where the profile `(dim ⟨P⟩)_P` is constant ((BE-65)(iii)), a nonempty open.
> **Claim.** If at one draw whose profile is the coordinatewise maximum we
> measure `δ_i > m_i`, then `Good(H; x, y) = ∅`. *Proof.*
> `{profile maximal} ∩ {dim ⋂_P ⟨P⟩ ≤ m_i}` is nonempty open, hence dense. If
> `Good ≠ ∅` it is dense too, and the two meet ((BE-255)(ii)); at a common point
> `a = (0,0)` and `dim(ρ̄₁+ρ̄₂) = Σδ`, forcing `ρ_i = δ_i` — but there
> `ρ_i ≤ dim ⋂_P ⟨P⟩ ≤ m_i < δ_i`. ∎

> **(BE-257)(ii)** `[MEASURED]` *(`bgoodempty.py conf`, 226.1 s, **4
> independent draws per side**, 257 rows — the criterion hunted, 0
> certificates)* `δ − m` histogram
> `{−5: 1, −4: 2, −3: 2, −2: 8, −1: 10, 0: 234}`: the confinement is **tight**
> (`δ = m`) at **234 of 257**, and where it is loose it is loose in the
> harmless direction (`m > δ`). At **every draw of every row** the driver
> asserts `dim(ρ̄_i ∩ ⋂_P ⟨P⟩) = ρ_i` — (BE-30)(iv) re-verified as an identity
> of **subspaces**, not of dimensions — and `ρ_i ≤ m_i`. **0 certificates.**

> **(BE-257)(iii)** *(the cap, disclosed, plus one reading of the driver a
> successor must re-check)* Cycles with arcs to `(7,8)`, generalized thetas on
> 3–5 paths of length `≤ 6`, 20 ladders. Path enumeration is capped at 400
> paths of length `≤ 9` and was **truncated at 5 of the 257 rows** — a
> truncated enumeration intersects **fewer** `⟨P⟩`, so it can only make `m`
> **larger**, i.e. it can never manufacture a false certificate. The reported
> `m` is the minimum over the draws whose path-dim profile equals the
> coordinatewise maximum **over those draws**; if no single draw attains every
> maximum at once the code **falls back** to the minimum over all draws, and
> that fallback is *not* theorem-grade. No certificate was found under either
> reading, so the fallback carries no figure — but a successor exhibiting one
> **must** re-check that its draw is genuinely max-profile.

---

### Step BE257 — (BE-258): the `Π_x` lemma — `rank(ω ↦ ω ∧ p_x) = 3`, and the threshold it puts at `dist_i ≤ 4`

At rung 3 with `slack = 0` the two-sided obstruction is `ρ̄₁ ∩ ρ̄₂ ≠ 0` on a
dense open. By (BE-95)(i)'s modular law — which holds **pointwise**, at every
configuration — a violation `c₁(U) + c₂(U) > dim U` at **any** subspace `U` is
such an intersection. (BE-97)(iii) records that the **only** `U` at which both
sides have ever been measured to exceed the generic profile is `Π_x`, and
BWHOLEH's certificate is a `Π_x` violation, `c₁ + c₂ = 3 > 2`, at a **steered**
point.

> **(BE-258)(i)** `[PROVED]` *(the rank computation, and the combinatorial
> threshold it yields)* `Π_x = α_x ∩ Λ²π_x ⊆ α_x`, and `ρ̄_i ⊆ ⟨P₀⟩` pointwise
> ((BE-30)(iv)), so **`c_i(Π_x) ≤ dim(ρ̄_i ∩ α_x) ≤ dim(⟨P₀⟩ ∩ α_x)`**. Now
> `α_x` is the **kernel** of `φ: Λ²K⁴ → Λ³K⁴`, `ω ↦ ω ∧ p_x`, whose image is
> `p_x ∧ Λ²K⁴ ≅ Λ²(K⁴/⟨p_x⟩)`: **`rank φ = 3` exactly.** Hence with
> `d := dim ⟨P₀⟩ ≤ dist_i(x, y)`,
> `dim(⟨P₀⟩ ∩ α_x) = d − rank(φ|⟨P₀⟩) ≥ d − 3`, while `ℓ₁ = p_x ∧ p_1 ∈ ker φ`
> always forces `rank(φ|⟨P₀⟩) ≤ d − 1`. The generic rank is `min(3, d−1)`, so
> the **generic** value of `dim(⟨P₀⟩ ∩ α_x)` is **`max(1, d − 3)`**. Therefore
> **`dist_i(x, y) ≤ 4` ⟹ generic `c_i(Π_x) ≤ 1`** — a purely combinatorial
> hypothesis on the side, with no measurement anywhere.

> **(BE-258)(ii)** *(**FIRST-RUN CORRECTION**, self-caught, and it moved the
> threshold by one — the driver's own assert is what produced it)* This
> direction first wrote *"the `d−1` vectors `p_{j−1} ∧ p_j ∧ p_x` are
> generically independent for `d ≤ 5`, so the kernel is `⟨ℓ₁⟩` and
> `c_i(Π_x) ≤ 1` whenever `dist_i ≤ 5"`*. **False.** All those vectors lie in
> the **3-dimensional** `p_x ∧ Λ²K⁴`, so the rank saturates at 3 and the bound
> is `max(1, d−3)`, not `1`. The first `pix` run reported
> `(dist, dim(⟨P₀⟩ ∩ α_x)) = (5, 2)` at 22 rows and `(6, 3)` / `(7, 3)` at 41 —
> `max(1, d−3)`, not `1`. Clause (i) states the corrected threshold and the
> driver now asserts the `d − 3` floor at every draw. The lesson is the arc's
> own: **a dimension count stated without naming the ambient space of the image
> is not a dimension count.**

> **(BE-258)(iii)** `[MEASURED]` *(`bgoodempty.py pix`, 326 s, **427 side
> rows**, 3 draws each, every line an assert)*
> ***RE-TAKEN BY THE COORDINATOR AT LANDING, and two things changed.*** The
> draft reported **527** rows with a proportionally larger histogram; the
> committed driver at its committed defaults gives **427**, deterministically
> across two runs, and every claim below holds at **427 of 427**. *(Unlike the
> `dist` figure, whose 31 338 was recovered exactly by restoring a default that
> had drifted, no parameter setting reproduced 527, so the reproducing figure
> is the one recorded.)* **And the display formula was wrong at its own largest
> bucket:** `(dist_i, generic dim(⟨P₀⟩ ∩ α_x))` is
> `{(2,1): 203, (3,1): 103, (4,1): 58, (5,2): 22, (6,3): 23, (7,3): 18}` —
> which is **`max(1, min(dist_i, 6) − 3)`, not `max(1, dist_i − 3)`**: at
> `dist = 7` the latter predicts `4` and the measurement is `3`. The
> **saturation is this direction's own point** — the image `Λ²(K⁴/p_x)` is
> 3-dimensional, so `dim⟨P₀⟩ ≤ 6` caps the bound — and it is the same
> saturation behind the self-caught *"false by one"* lemma at (BE-258)(i); the
> lemma was fixed and the display form was not. **The driver was right
> throughout**: its assert reads `calpha >= max(1, dim(P0) - 3)`, in terms of
> `dim⟨P₀⟩` rather than `dist`. So the generic rank is attained at every row,
> which is what this clause needs. `(dist_i, generic c_i(Π_x))` is
> `{(2,0): 190, (2,1): 13, (3,0): 91, (3,1): 12, (4,0): 49, (4,1): 9,
> (5,0): 15, (5,1): 7, (6,0): 15, (6,1): 1, (6,2): 7, (7,2): 18}` —
> **`c_i(Π_x) = 2` occurs only at `dist_i ≥ 6`** (25 rows) and at **0 rows**
> with `dist_i ≤ 5`, the 27 rows at `dist_i = 5` included, where the α-bound
> would allow `2` (there the second kernel vector must additionally lie in
> `Λ²π_x`, one further condition). **`c_i(Π_x) = 2 ⟹ ρ_i = 6` is asserted at
> every DRAW**, not merely at the minimum over draws, with **0 exceptions**.

> **(BE-258)(iv)** `[MEASURED]` *(the mechanism, stated as a mechanism — and
> there is no shape in between)* At `dist_i ≥ 6`, where `dim ⟨P₀⟩ = 6` makes
> the confinement **vacuous**, `c_i(Π_x)` equals the **general-position** value
> `bunif.generic_c(ρ_i, 2) = max(0, ρ_i − 4)` at every row: `ρ = 3 → 0`,
> `ρ = 4 → 0`, `ρ = 5 → 1`, `ρ = 6 → 2`. So **while `⟨P₀⟩` is a proper subspace
> the rank-3 bound holds `c_i(Π_x)` down; once every x–y path is long enough
> that `⟨P₀⟩` is the whole screw space, `ρ̄_i` sits in general position against
> `Π_x` and nothing is forced.** `c_i(Π_x) = 2` needs `ρ_i = 6` under both
> regimes, for opposite reasons.

---

### Step BE258 — (BE-259): the consequence — `Π_x` cannot be the binding block of a rung-3 `Good = ∅` piece

> **(BE-259)(i)** `[PROVED]` *(the arithmetic, and the half that needs no
> measurement at all)* At rung 3, `slack = 0` and `dim Π_x = 2`, so a `Π_x`
> obstruction needs generic `c₁(Π_x) + c₂(Π_x) ≥ 3`, hence `c_i(Π_x) = 2` on
> some side. If **both** sides have `dist_i(x, y) ≤ 4`, (BE-258)(i) gives
> generic `c_i(Π_x) ≤ 1` on each, so `c₁ + c₂ ≤ 2 = dim Π_x`, and by the
> density lever (BE-255)(ii) **`Π_x` cannot bind.** No draw is used. The same
> at `Π_y`, every ingredient being x/y symmetric.

> **(BE-259)(ii)** `[MEASURED]` *(`bgoodempty.py pix`; the half that is a
> 427-row assert — and the residue it leaves is named rather than smoothed)*
> Outside that hypothesis:
> `c_i(Π_x) = 2` forces `ρ_i = 6` at 427 of 427 rows ((BE-258)(iii)), hence
> `δ_i = 6` (as `ρ_i ≤ δ_i ≤ 6`), hence `δ_j = 0` by `Σδ ≤ 6` — and at
> `a_j = 0`, (BE-22)(ii)'s `ρ_j ≤ δ_j + a_j` gives `ρ_j = 0`, the collapse
> (BE-22)(vi) names, so `c_j(Π_x) = 0`. Therefore **generic
> `c₁(Π_x) + c₂(Π_x) ≤ 2`: the margin at `Π_x` is `0` and never positive at
> rung 3.** ***What is missing is a proof that `Π_x ⊆ ρ̄_i` is a proper closed
> condition when `ρ_i ≤ 5` and `dim ⟨P₀⟩ ∈ {5, 6}`. That is the entire residue
> of this clause, and it is stated here so it can be attacked.***

> **(BE-259)(iii)** *(what this does to two landed clauses — an upgrade, not a
> contradiction)* BWHOLEH's side 1 is the **`(4,4)` cycle**, so
> `dist₁(x, y) = 4`, and **(BE-259)(i)'s PROVED half applies to that very
> certificate**: generic `c₁(Π_x) ≤ 1` there, hence no generic `Π_x` violation,
> hence — `Good` being dense-or-empty — the killing point is **provably**
> non-generic. (BE-250)(iii) reported exactly this as a 6-of-6 free-draw
> control (`c₁ = 0` at 6 of 6); **that control is now the consequence of a
> theorem rather than the evidence for a reading**, and (BE-253)(ii)'s *"the
> killing configuration is steered, hence non-generic"* is **forced** by
> `dist₁ = 4` and `rank φ = 3` rather than measured. BWHOLEH itself flagged
> this as its fragile part — *"(BE-253)(ii)'s scope … rests on 6 free draws of
> one `H`, and a free draw that failed to attain would make this a `Good = ∅`
> claim instead"* — and that fragility is now removed. **Nothing in (BE-253) is
> contradicted:** its verdict (the obligation REFUTED as a universal over an
> open stratum) and its exact-ℚ certificate stand untouched, one exhibited
> configuration being a proof that needs no genericity.

---

### Step BE259 — (BE-260): the two-sided hunt, run wide at the whole-`H` layer

> **(BE-260)(i)** `[MEASURED]` *(`bgoodempty.py block`, 1 782.8 s, **253
> in-region rows** of 420 jobs, **3 independent FREE draws each**, seed
> `20260912`)* Per draw: `bunif.flag_frame` on the **whole `H`** (so every row
> is in the generic flag regime by construction), `bunif.blocks_of`, and
> `bimage.rho_bar_of` per side; the **generic** `c_i(U)` is estimated as the
> **minimum** over draws (ledger row 4), `ρ_i` and `reach` as the **maximum**
> (rows 1–2), `a_i` as the minimum (row 3). Results: the margin
> `max over the 16 S(ϕ)-stable U of [c₁(U) + c₂(U) − dim U − slack]` has
> histogram **`{0: 253}`** — never positive, never negative; **0 rows** with a
> generic shortfall `reach < min(Σδ,6) + a₁ + a₂`; `(c₁, c₂)` at `Π_x`,
> generic, is `{(0,0): 145, (0,1): 69, (0,2): 15, (1,0): 23, (1,1): 1}`; **23**
> distinct `(δ, a, ρ, c(Π_x))` tuples. The bracket
> **`blockdeg ≤ reach ≤ blockcap`** ((BE-96)(i) and (BE-95)(i)) is **asserted at
> every row** and fired 0 times, its left half doubling as the (BE-69)(iii)
> genericity check on the draws.

> **(BE-260)(ii)** `[MEASURED]` *(`bgoodempty.py block`, the same 253 rows; two
> readings worth keeping, and the second is a new instance of a landed rarity)* **(a)** The 15 rows with
> `(c₁, c₂) = (0, 2)` are **exactly** the 15 rows with `δ = (0, 6)` — side 1
> rigid, `ρ₂ = 6`. That is (BE-259)(ii)'s only route to `c_i(Π_x) = 2`,
> appearing in the population and contributing margin `0` because the rigid
> side contributes `c = 0`: the theorem's own mechanism, observed. SECOND, the
> single `(1, 1)` row is a **both-sides-bite at `Π_x`** with margin exactly
> `0` — one more instance of (BE-97)(iii)'s *"the one place it is tight"*, and
> it is **tight, not violated**.

> **(BE-260)(iii)** *(the population, disclosed at the generator — three fences
> opened, per dispatch-log F28's* a listed fence is not an acted-on fence*)*
> First, every skeleton-**non-adjacent** hub pair of `K₃,₃` and of the prism
> (6 per skeleton) where `bproper.NONADJ` hardcodes **3** of 6 —
> (BE-248)(iii)'s un-fencing, carried here. Second, branch lengths to **5**,
> where `bpeel.constructed_tier` defaults to `maxlen = 4` and `bunif.tier_rows`
> uses `3` — the branch-length axis (BE-251) re-identified as the one that
> mattered last round. Third, a **66-shape side-1 library** with
> `deg₁(x), deg₁(y) ∈ {2,…,5}`: 11 cycles, 14 generalized thetas on 3 and 4
> paths, 5 ladders (non-internally-disjoint x–y paths), and **36 subdivided
> 3-connected skeletons used as side 1** at every non-adjacent hub pair, with
> `dist₁(x, y)` running to **8** — where `bline.longcore_library()` is the
> generator-level fence (BE-248)(ii) found (`deg₁(y) = 1` at 27/27) and
> BWHOLEH's own side-1 generator is the `(4,4)` cycle alone.

> **(BE-260)(iv)** *(the cap, quoted in the direction it can bear)* 420 jobs,
> 253 in region, 3 draws each, two skeletons, `Σδ ≤ 6` enforced
> **combinatorially before any draw**. The generic `c_i(U)` is estimated from
> **3 draws**, so a `margin = 0` row is *evidence* that the generic margin is
> `0`, never a proof: a minimum over 3 draws is an **upper** bound on the true
> generic value, so the estimate can only be **too large** — the safe direction
> for a *"no violation found"* report and the unsafe one for reporting a
> violation. No violation was found, so the bias runs the right way. A shorter
> re-run (`njob = 80`, same seed, 53 rows) reproduces `{0: 53}`; it is a
> **prefix of the same shuffled job list**, so it is a reproduction and **not**
> independent evidence, and is reported that way.

---

### Step BE260 — (BE-261): the spec's TELL, run — and why it could not have settled the question

> **(BE-261)(i)** `[MEASURED]` *(`bgoodempty.py sweep`, 285.0 s — **31
> in-region pieces**, **5 independent FREE draws each**)* `reach` attains
> `min(Σδ, 6) + a₁ + a₂` at **31 of 31**. **The tell did not fire:** no piece
> showed a shortfall at even one free draw, let alone at all five.

> **(BE-261)(ii)** *(and it was structurally unable to settle the question even
> if it had — `RESEARCH-ARC.md` §7(b), answered)* The tell is *"shortfall `> 0`
> at every one of several independent FREE draws"*, i.e. it samples
> `dim(ρ̄₁+ρ̄₂)` — **row 1** of the ledger (BE-255)(i): **lower**
> semicontinuous, so a draw is a lower bound and a measured shortfall is never
> a generic one. The spec says as much (*"a POINTER, not a proof"*) and is
> right. The addition here is that **the ledger names the tells that WOULD have
> been decisive** — a max-profile draw of `m_i` ((BE-257)(i)), or an upper
> bound on `c_i(U)` ((BE-258)(i)) — and those are the two this direction
> actually spent. The tell is **live** in the sense the spec checked (the region
> is non-empty at 253 rows; the verdict could differ inside it) and **dead** in
> the sense that firing would not have settled it.

---

### Step BE261 — (BE-262): THE VERDICT, the residue, and the prediction scored

> **(BE-262)(i)** `[MEASURED]` *(`bgoodempty.py` modes `dist`, `conf`, `pix`,
> `block`, `sweep` together; **the verdict**, with the quantifier it actually
> carries)* **NOT FOUND under cap C** — C being 253 in-region
> composite rows × 3 free draws, 257 side rows × 4 draws, 427 side rows × 3
> draws, 31 pieces × 5 free draws, two skeletons, branch lengths `≤ 5`, all six
> non-adjacent hub pairs per skeleton, a 66-shape side-1 library. **Never
> *"does not exist"* — and here that rule has teeth beyond the usual, because
> `Good = ∅` is precisely a claim a search cannot make.** So the tally is not
> the result. The result is what is **closed**: **(1)** the one-sided
> obstruction, by the combinatorial proof (BE-256)(i)–(ii); **(2)** the `Π_x`
> and `Π_y` blocks at rung 3 — outright when both sides have `dist_i ≤ 4`
> ((BE-259)(i)), by a 427-row assert otherwise ((BE-259)(ii)) — which is the
> block BWHOLEH's certificate used and the only one at which both sides have
> ever been measured to bite ((BE-97)(iii)); and **(3)** a new decision
> procedure, (BE-257)(i), which settles `Good = ∅` affirmatively from **one**
> max-profile exact-ℚ draw when it fires. It did not fire at 257 rows, with the
> confinement tight at 234.

> **(BE-262)(ii)** *(**what remains open**, stated so it can be attacked, and
> who decides each)* FIRST, the `dist_i ∈ {5, 6}` corner of (BE-259)(ii): a
> proof that `Π_x ⊆ ρ̄_i` is a proper closed condition at `ρ_i ≤ 5` would make
> (BE-259) unconditional. *A direction's question, not a coordinator's.*
> SECOND, the **13 unwitnessed blocks**. (BE-97)(iv) is untouched — *"`Π_x`
> only"* remains a statement about constructed populations. In particular the
> `U = ⟨M⟩` shape — `c_i(⟨M⟩) = 1` on **both** sides, which at `dim U = 1` is a
> violation by `2 > 1`, the cheapest the arithmetic allows — is still
> unwitnessed (0 of the landed 93 ((BE-120)(i)), and 0 at this direction's 253
> rows; the two denominators are left **un-summed** deliberately). **`⟨M⟩` is
> now the cheapest remaining route to a rung-3 `Good = ∅` piece and this
> direction did not close it.**
>
> > **— SPENT 2026-09-12 by (BE-274)/(BE-277) (direction BMBLOCK), and the
> > evidence trail of the `0 of 253` is corrected without its value moving.**
> > `⟨M⟩` is **closed by proof** whenever either side has `dist_i ≤ 5`, by the
> > path lemma (BE-272)(ii) — `⟨M⟩` is the virtual edge's own hinge line, so
> > (BE-30)(iv) confines it to `⟨P⟩` and an explicit decomposable transversal
> > kills the intersection at `m ∈ {3,4}` (pointwise) and a `6 × 6`
> > determinant at `m = 5` — and closed by the measured step `c_i(⟨M⟩) = 1 ⟹
> > ρ_i = 6` on the remaining `dist_i ≥ 6` corner. So this clause's *"the
> > cheapest remaining route"* is **spent**, and three of the three routes this
> > direction named are closed. **On the figure itself:** `bgoodempty.block_row`
> > **does** compute the field `cM` and `run_block` never aggregates or prints
> > it, so the `0 of 253` rests on the **margin histogram** — which at
> > `slack = 0` would score a `(1,1)` at `⟨M⟩` as `margin = +1` and fire. The
> > inference is **valid and the figure stands**; what was never reported is the
> > `⟨M⟩` **marginal**, which (BE-273) supplies. Do not quote *"0 of 253"* as a
> > `cM` census. **The residue this leaves is (BE-262)(ii)'s FIRST item one
> > dimension down and is the same question ((BE-277)(iii)).**
>
> THIRD, the class statement: (BE-67)(ii)'s
> residue is not touched — nothing here proves `Good ≠ ∅` for a piece it did
> not measure; what it removes is two of the three ways a piece could fail.
> FOURTH, both skeletons used are 3-regular on 6 vertices; a side 2 from a
> **larger or non-regular** 3-connected skeleton is **not** reached, and per
> (BE-251) the branch-length axis is opened to 5 here, not removed.

> **(BE-262)(iii)** *(**the board** — what moved and what did not)* **What
> moved.** `δ_{xy} ≤ dist(x, y)` proved **combinatorially**, and (BE-30)(iv)'s
> configuration hypothesis on that clause shown unnecessary ((BE-256));
> `rank(ω ↦ ω ∧ p_x) = 3` and the resulting `max(1, min(dist, 6) − 3)` bound, attained
> at 427/427 ((BE-258)); the `Π_x`/`Π_y` blocks closed at rung 3, proved at
> `dist_i ≤ 4` ((BE-259)(i)); (BE-250)(iii)'s 6-of-6 control and (BE-253)(ii)'s
> scope sentence **upgraded from measurement to theorem** ((BE-259)(iii)); a
> new one-draw decision procedure for `Good = ∅` ((BE-257)(i)); a second
> both-sides-bite instance at `Π_x`, tight ((BE-260)(ii)); three
> generator-level fences opened ((BE-260)(iii)). **What did NOT move.**
> `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`, (GR-15), **(BE-14)**,
> the S-mark, half (B), half (β), the 2-cut step, class uniformity, cross-pair
> welding, `(BE-E4′)`, the flag base, `(BE-OBL7)`, `(BE-OBLK)`, (BE-253)'s
> verdict and certificate, (BE-97)(iv)'s 13 blocks, and **every landed
> measurement** — this direction contradicts none of them. **The E-rider:** no
> termination-ledger entry fires; E1/E2/E3 are §(K-grid) objects.

> **(BE-262)(iv)** *(the dispatch's prediction, scored — verdict, mechanism and
> tell **separately**, per `RESEARCH-ARC.md` §7)* **VERDICT: the spec predicted
> NEGATIVE (*"no `Good = ∅` piece gets exhibited in this dispatch"*) and is
> CONFIRMED.** Its stated reason — *"every landed measurement of the shortfall
> at a free draw is 0"* — is **evidence, not the reason**; the reason the
> verdict holds (two of three routes closed structurally) was not available to
> the spec, so the §7 taxonomy entry is *right, for a better reason than
> given*. **MECHANISM: REFUTED, first, before anything was built on it.** The
> spec offered *"`Good ≠ ∅` is forced at rung 3 by (BE-22)(ii)'s partition
> cap"*. The cap is `dim M_i ≥ 6 + f_i` at every configuration, i.e. a
> universal **upper** bound on rank; attainment is the **maximal**-rank locus,
> which the cap makes **open** — (BE-69)(i) uses it for exactly that — and says
> nothing whatever about it being **nonempty**, which is what `Good = ∅`
> denies. Three landed rows witness the gap: `a_i = 1` at 100 of 392
> ((BE-86)(ii)); `a_i ∈ {1,2,3,6}` off a path side ((BE-120)(ii)); an
> `a = (0,0)` in-regime chart point with `dim M(H) = 7 > 6 = 6 + def₃(H)`
> ((BE-250)(i)). `bgoodempty.py mech`, which runs no computation and says so.
> The first slice actually run was `dist`, not the mechanism. **TELL: DID NOT
> FIRE**, and was structurally unable to settle the question ((BE-261)(ii)).
> **The spec's *"where I expect to be wrong"* sentence — scored.** It said the
> negative might be *"a statement about constructors, not about the class —
> look for the piece the constructors cannot present"*. This direction
> **acted** on that at the generator ((BE-260)(iii)): a side-1 library no
> landed builder carries, `bproper.NONADJ` opened 3→6, branch lengths past
> `constructed_tier`'s default. The widened population produced **new** tuples
> (23 distinct) and new `c(Π_x)` profiles including a `(1,1)` both-sides-bite —
> **and still margin `0` at 253 of 253.** So on *this* question the constructor
> fence was **real but not load-bearing**: opening it changed what was seen and
> did not change the verdict. That is the opposite of the previous round's
> result and is worth logging as such.

---

### What each driver actually asserts — read off the code, not recalled

*Written by re-reading `bgoodempty.py` after the runs, per the F-clause on*
"we checked it N ways".

- **`run_dist`** — per row, three asserts: the side is connected, `0 ≤ δ ≤ 6`,
  and `δ ≤ dist`. No draw; seeded only for the 400-member random family.
  `dist` is a BFS on the side, `δ` is `bdecor.d3 − bdecor.weld_d3` — neither
  oracle is re-implemented here.
- **`conf_row`** — per **draw**: `dim(ρ̄_i ∩ ⋂_P ⟨P⟩) = ρ_i` (the (BE-30)(iv)
  containment **as a subspace**) and `ρ_i ≤ m_i`. The reported `m` and its
  max-profile caveat are (BE-257)(iii).
- **`run_pix`** — per **draw**: `dim α_x = 3`; `Π_x ⊆ α_x`;
  `c_i(Π_x) ≤ dim(⟨P₀⟩ ∩ α_x)`; the rank-3 floor
  `dim(⟨P₀⟩ ∩ α_x) ≥ max(1, dim ⟨P₀⟩ − 3)`; `c_i(Π_x) ≤ 2`;
  `dim(ρ̄_i ∩ ⟨P₀⟩) = ρ_i`; and the headline **`c_i(Π_x) = 2 ⟹ ρ_i = 6`**. The
  row-level `ρ` printed is the **minimum** over draws, which *under*-estimates
  the generic `ρ` (lower semicontinuity), so the row-level flag
  `c = 2 ∧ ρ < 6` is biased towards **false positives** — the safe direction
  for a "none found" report. The per-draw assert is what carries the claim.
- **`block_row`** — every region gate is checked **before** any draw: simple,
  `x ≁ y`, `deg_H(x), deg_H(y) ≥ 3`, min degree `≥ 2`, girth `≥ 4`,
  `bdecor.hcard_ok_piece`, `bpeel.rnode_shaped` on side 2,
  `deg_i(x), deg_i(y) ≥ 2` on **both** sides, `δ₁ + δ₂ ≤ 6`. The generic flag
  regime is enforced per draw by `bunif.flag_frame` returning non-`None`. The
  one row-level assert is the `blockdeg ≤ reach ≤ blockcap` bracket.
- **`run_sweep`** calls the same `block_row`, so its gates are identical; only
  the draw count and the reported statistic differ.
- **`run_mech`** runs no computation at all, and labels itself as an argument
  plus three citations.

### Caps and blind axes

| axis | value used here | landed default | status |
|---|---|---|---|
| `bproper.NONADJ` hub pairs | **all 6** per skeleton | 3 hardcoded | **opened** |
| branch length | **≤ 5** | `constructed_tier(maxlen=4)`, `bunif.tier_rows(maxlen=3)` | **opened** |
| side-1 generator | **66 shapes**, `deg₁(x), deg₁(y) ∈ {2,…,5}`, `dist₁ ≤ 8` | the `(4,4)` cycle (BWHOLEH); `deg₁(y) = 1` at 27/27 (`bline.longcore_library`) | **opened** |
| skeletons | `K₃,₃`, prism — both 3-regular on 6 hubs | same | **NOT opened** — blind axis (BE-262)(ii) FOURTH |
| free draws per row | 3 (`block`), 4 (`conf`), 3 (`pix`), 5 (`sweep`) | `bpeel.run_open(ndraw=5)`, `bpeel.run_indep(ndraw=3)` | comparable; not exhaustive |
| path enumeration | ≤ 400 paths of length ≤ 9 | — | truncated at 5 of 257 `conf` rows, in the **safe** direction |
| `δ ≤ dist` enumeration | 31 338 rows; `K₄` profiles exhaustive at lengths 1–4 | — | a **proof**; the enumeration is the check |
| field | exact ℚ | ℚ | unchanged |

**The class `blindaxes.py` cannot list — the provenance of a POPULATION — was
checked at the generator** for every one of them: `bgoodempty.side1_library`,
`side_library`, `skeleton_pairs` and the composite job list are written in this
direction's own file and disclosed as **CONSTRUCTED**, not censused.

### What would change this

- **A side with `ρ_i ≤ 5`, `dist_i(x, y) ∈ {5, 6}` and generic
  `c_i(Π_x) = 2`.** One such side, paired with any path-saturated side 2 with
  `δ₂ = 6 − δ₁`, gives `c₁ + c₂ = 3 > 2` **generically** at `slack = 0`, hence
  `Good = ∅`. (BE-258)(iii) says every one of 427 rows has `ρ_i = 6` there;
  **one counterexample closes this lane the other way.**
- **A peel with `c_i(⟨M⟩) = 1` on both sides** — the (BE-97)(iv) shape, at
  `dim U = 1`.
- **A side with `δ_i > m_i` at a max-profile draw** — (BE-257)(i) then
  **proves** `Good = ∅` with no further work.
- A larger or non-regular 3-connected skeleton for side 2.

### Driver

`notes/scripts/w4/bgoodempty.py` — modes **`mech`** (the dispatch mechanism
eliminated; no computation, ~0 s), **`dist`** (the combinatorial theorem's
enumeration, 31 338 rows, 4.2 s), **`conf`** (the confinement criterion, 257
rows × 4 draws, 226.1 s), **`pix`** (the `Π_x` lemma, 427 rows × 3 draws,
448.5 s), **`block`** (the two-sided hunt, 253 in-region rows × 3 free draws,
1 782.8 s), **`sweep`** (the spec's tell, 31 pieces × 5 free draws, 285.0 s),
and **`validate`** (`mech` + reduced `dist`/`conf`/`pix`/`block`, run **green
end-to-end** at `29a60d1a`). Seed `20260912`; exact ℚ throughout; `bimage`,
`bdecor`, `bpeel`, `bproper` and `bunif` primitives are **imported**, never
copied. **This section merges into §(K-bare-ext) as a new continuation file**
`notes/pencil/workbook/bare-ext/BGOODEMPTY.md`, matching BWHOLEH's shape.

---
