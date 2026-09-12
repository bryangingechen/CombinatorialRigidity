## §(K-bare-ext) — continuation (direction BPROPCL, ordinal 113, 2026-09-12): **THE "PROPER CLOSED CONDITION" IS NOT A LEMMA — IT IS A ONE-DRAW CERTIFICATE THE CORPUS'S OWN SEMICONTINUITY LEDGER ALREADY ISSUES; AND THE TWO RESIDUES ARE ONE QUESTION ONLY IN A FRAME NEITHER CLAUSE STATES IT IN.** (BE-259)(ii) and (BE-277)(iii) each ask for *"a proof that `U ⊆ ρ̄_i` is a proper closed condition when `ρ_i ≤ 5`"*, and (BE-277)(iii) asserts that **a single lemma would discharge both**. Three things are wrong with that framing and one of them is load-bearing. **FIRST — the object.** "Proper closed" is not a lemma one proves once: `{c_i(U) ≥ dim U}` is closed only on the locus where `ρ_i` is constant ((BE-255)(i) row 4), so properness is a statement **per peel**, and the corpus's own ledger already converts one draw into it: `ρ_i ≤ δ_i` pointwise with `δ_i` **combinatorial**, and `ρ_i` **lower** semicontinuous, make `{ρ_i = δ_i}` **open**; attained at one draw it is **dense**; and on it `c_i(U)` is **upper** semicontinuous, so **one draw with `ρ_i = δ_i ≤ 5` and `c_i(U) < dim U` PROVES properness at that peel** — a witness, cap-free. **SECOND — the mechanism.** Both clauses (and the dispatch) name *"`ρ̄_i` in general position against a stable block"*. Tested per draw for the first time — `run_pix` and `bmblock.run_side` compute `ρ` and `c(U)` at every draw and print only the `(dist, c)` marginal, so the joint `(dist, ρ, c)` has **never been reported** — general position is **EXCEEDED at 102 of 1 281 draws at `Π_x`** and at **0 of 1 281 at `⟨M⟩`**. **THIRD — the divergence, and it is the answer to the dispatch's question.** The excess at `Π_x` has a **named pointwise mechanism**: `π_x` is the plane of the **closed star** of `x` (`bimage.plane_at`), so **every** hinge line of side `i` at `x` lies in `Π_x`; when the path confinement **saturates** (`ρ_i = dim ⟨P₀⟩`, i.e. `ρ̄_i = ⟨P₀⟩` by (BE-30)(iv)) the path's first hinge `ℓ₁ = p_x ∧ p_1` is in `ρ̄_i ∩ Π_x` and `c_i(Π_x) ≥ 1` **pointwise**. At `⟨M⟩` the same saturation gives **nothing**, because `dim(⟨P₀⟩ ∩ ⟨M⟩) = 0` is exactly (BE-272)(ii). **So no single lemma of the form both residue clauses state — general position against `Λ²K⁴` — can discharge both: it is FALSE at `Π_x`.** **BUT THE REPAIR LANDED FROM THE OTHER LANE MID-RUN.** BSIXTEEN (111, `0bd802e7`) proposes in (BE-281)(iii) that the unified lemma be stated **relative to `⟨P₀⟩`**, and that is right: with `gpP(U) := max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)` — which equals `bunif.generic_c(ρ_i, dim U)` **exactly when `dim ⟨P₀⟩ = 6`** — **`c_i(U) = gpP(U)` at every draw at BOTH blocks, asserted, 0 exceptions.** **So (BE-277)(iii)'s *"a single lemma would discharge both"* is CONFIRMED in BSIXTEEN's frame and REFUTED in its own**, and the two directions converge on one lemma from opposite ends of the `dim ⟨P₀⟩` axis. **FOURTH — the corner, priced draw-free.** `bmblock.run_reach` **computes** `((δ₁,δ₂),(dist₁,dist₂))` and prints only the `dist` marginal — the same dropped-field shape (BE-273)(iii) found at `cM`. Printed here: at the **248** residue-corner peels the profile is `{(2,2): 6, (2,3): 13, (2,4): 1, (3,2): 72, (3,3): 156}`, so **`δ_i ≤ 4` on both sides at every one of them** and hence **`ρ_i ≤ 4`** — the hypothesis `ρ_i ≤ 5` both clauses state is **never tight on the population they cite**, and the dangerous case `ρ_i = 5` does not occur there at all. **AND THE CERTIFICATE IS NOT HYPOTHETICAL: over the same 427-row library, `a_i = 0` at 1 281 of 1 281 draws, a draw with `a_i = 0` and `ρ_i = δ_i` exists at 400 of 400 distinct sides, and properness is therefore CERTIFIED — proved, not measured — at 375 of the 375 ELIGIBLE rows (`ρ_i = δ_i ≤ 5`) for BOTH blocks, and at 15 of 15 in the residue regime `dist_i ≥ 6`. The 25 rows that do not certify are exactly the `ρ_i = δ_i = 6` rows, where `U ⊆ ρ̄_i` genuinely HOLDS and the ARITHMETIC closes the peel.** **THE F26 CONSUMER CHECK, RUN FIRST AND REPORTED EVEN THOUGH IT WEAKENS THE QUESTION: every consumer of (BE-259) and (BE-274) is inside this lane, and the two verdict clauses that terminate it — (BE-262)(ii)/(iii), (BE-277)(ii)/(iv) — state in their own words that they do NOT prove `Good ≠ ∅`, do NOT touch (BE-67)(ii)'s residue and do NOT move (BE-14). No downstream consumer requires either clause to be `[PROVED]` rather than `[MEASURED]`.** (*Steps BE290–BE297*)

### Standing notation (on top of *Steps BE148–BE276*)

BGOODEMPTY's and BMBLOCK's, verbatim. Two objects are named here because
this direction quantifies over them and they have not carried a symbol
before. Read at the definition sites (`bimage.plane_at`,
`bimage.pencil_space`, `bimage.rho_bar_of`, `bunif.generic_c`,
`bunif.blocks_of`, `bgoodempty.delta_of`, `bgoodempty.dist_of`,
`bmblock._jobs`, `bmblock.run_reach`):

> **`U ⊆ ρ̄_i` means `c_i(U) = dim U`**, and *"a proper closed condition"*
> means: the locus where it holds is a **proper** closed subset, i.e. the
> **generic** point of `Chart(H)` is not in it. Both residue clauses use the
> phrase without saying **in what** the locus is closed; it matters, and
> §(BE-293) below is where it is pinned down.
>
> **`gp(U) := bunif.generic_c(ρ_i, dim U) = max(0, ρ_i + dim U − 6)`** — the
> **general-position** value, the mechanism both residue clauses name. `U` is
> **in general position against `ρ̄_i`** at a configuration iff
> `c_i(U) = gp(U)` there. This is a *per-configuration* predicate; it is what
> (BE-258)(iv) asserts at `dist_i ≥ 6` and what this direction tests at every
> draw.
>
> **SATURATION.** Side `i` is **saturated** at a configuration iff
> `ρ_i = dim ⟨P₀⟩`, i.e. the (BE-30)(iv) containment `ρ̄_i ⊆ ⟨P₀⟩` is an
> **equality**. Saturation is a *pointwise* property, not a generic one.
>
> **`Π_x` read at source, and this is a definition-body reading, not a
> docstring one.** `bunif.blocks_of` builds `Π_x` as
> `bimage.pencil_space(p_x, plane_at(H, pt, x))`, and `plane_at`'s body takes
> `star = [p_x] + [p_w : w ∈ N(x)]` and **requires `rank(star) = 3`**. So
> `π_x` is the plane of the **closed star of `x`**, every `p_w` with
> `w ∈ N(x)` lies in it, and therefore **every hinge line `p_x ∧ p_w` at `x`
> lies in `Π_x = p_x ∧ π_x`.** Two non-coincident ones span it (`dim Π_x = 2`).
> *This is the whole of §(BE-294) and it is read off the body of two
> functions, not off any prose.*

---

### Step BE290 — (BE-291): the F26 consumer check, run FIRST, and it weakens the question rather than killing it

> **(BE-291)(i)** `[PROVED]` — *the citation closure, taken from the ledger and
> not from a summary.* `notes/ledger.py --cited-by '(BE-259)'` returns **11**
> claims and `--cited-by '(BE-274)'` returns **7**; the union is
> **(BE-260)(ii), (BE-262)(i)/(ii)/(iii), (BE-272)(i)/(ii)/(iii),
> (BE-273)(iii), (BE-274)(i)/(ii), (BE-276)(i), (BE-277)(i)/(iii)/(iv)/(v)**.
> **Every one of them is in `workbook/bare-ext/`, in this lane, and written by
> BGOODEMPTY or BMBLOCK.** `--cited-by '(BE-277)'` returns **2**, both also in
> the lane. The citation graph of the two residues **terminates inside the
> lane**: nothing in §(K-grid), nothing at (GR-15), nothing at `hbareSplit`,
> nothing at (BE-14) cites either.
>
> **(BE-291)(ii)** `[PROVED]` — *and the terminal clauses disclaim the payoff in
> their own words.* (BE-277)(ii): *"It does **not** prove `Good ≠ ∅` for any
> piece: it removes one way a piece could fail … (BE-67)(ii)'s residue is
> untouched."* (BE-262)(ii)'s THIRD item: *"the class statement: (BE-67)(ii)'s
> residue is not touched — nothing here proves `Good ≠ ∅` for a piece it did
> not measure."* (BE-262)(iii) and (BE-277)(iv) both list **(BE-14)** under
> *"what did NOT move"*. **So the positive outcome this direction was
> dispatched for — "two landed clauses lose a hypothesis" — is a change of
> STATUS TAG on two clauses whose own consumers are two verdict paragraphs
> that already say the lane does not reach the class statement.** The
> hypothesis is real (the clauses are honestly tagged `[MEASURED]`), but it is
> **not load-bearing at any consumer**: no landed claim is conditional on
> either clause being upgraded.
>
> **(BE-291)(iii)** — *what the check does NOT say, because
> BTAKERS (107) found the other pattern and the difference matters.* This is
> **not** the (BE-276)(iii)-shaped finding *"the residual is never consumed"*.
> It is consumed — (BE-274)(i)'s L6 is a **law in a cap-free enumeration**
> whose removal takes the survivor count from `0` back to **1 120**, and
> (BE-259)(ii)'s measured step is what carries the `Π_x` closure outside
> (BE-259)(i)'s hypothesis. What the check establishes is narrower and is
> stated narrowly: **the two clauses are load-bearing INSIDE the lane and the
> lane's own verdicts are not conditional on their tag.** A successor
> deciding whether to spend a direction on the uniform lemma should price it
> against that, not against *"it would unblock (BE-14)"*, which it would not.

---

### Step BE291 — (BE-292): the residue corner priced DRAW-FREE, and the field `run_reach` computes and drops

> **(BE-292)(i)** `[MEASURED]` — `bpropcl.py pop`, **4.1 s**, **4 752 jobs
> offered, 2 946 in-region peels**, seed used only to build `bmblock._jobs`'s
> own job list, **no configuration sampled anywhere**. `bmblock.run_reach`
> builds `dd_delta[((d1,d2),(t1,t2))]` and prints only the `(t1,t2)`
> marginal — the same **dropped field** shape (BE-273)(iii) found at `cM`, and
> found the same way, by reading the function body rather than its output.
> `δ_i` is combinatorial (`bgoodempty.delta_of = d3 − weld_d3`), so the joint
> costs no draw either. At the **248** residue-corner peels (`dist_i ≥ 6` on
> both sides):
>
> > **`(δ₁, δ₂)` → count = `{(2,2): 6, (2,3): 13, (2,4): 1, (3,2): 72,
> > (3,3): 156}`.**
>
> * `min(δ₁, δ₂) ≥ 2` at **248 of 248**, so **neither residue is closed by a
>   rigid other side**: the `δ_j = 0` collapse (BE-259)(ii)'s derivation ends
>   in is **unavailable at every peel of the corner**.
> * `max(δ₁, δ₂) ≤ 4` at **248 of 248**, hence **`ρ_i ≤ δ_i ≤ 4` at every
>   residue-corner peel**. (BE-259)(ii) and (BE-277)(iii) both state the
>   residue at `ρ_i ≤ 5`; on the population (BE-276)(i) prices it over, `ρ_i`
>   never reaches `5`. The statements are not wrong — `≤ 5` is implied — but
>   the hypothesis is **not tight**, and §(BE-295) is where that changes what
>   has to be proved.
> * Both arithmetic gates pass at **248 of 248**: the `Π_x` bite needs
>   `min(δ₁,2) + min(δ₂,2) ≥ 3` (since `c_i ≤ min(ρ_i, 2) ≤ min(δ_i, 2)`) and
>   the `⟨M⟩` bite needs `δ_i ≥ 1` on both sides. **So the residue is LIVE at
>   248 of 248 and is not closed by arithmetic** — (BE-276)(i)'s *"the residue
>   corner is NOT vacuous"* is **confirmed at a second, independent gate**,
>   and *recorded in the direction that would have preferred the opposite
>   answer*: a `min(δ) = 0` profile would have closed both residues outright.
>
> **CAP, disclosed:** `bmblock._jobs(seed, maxlen=5)` = `bgoodempty.run_block`'s
> committed job list, every job, **no `njob` truncation and no `quick`** — two
> skeletons, branch lengths `≤ 5`, all six non-adjacent hub pairs, the
> 66-shape `side1_library()`. **NOT FOUND under cap C** is all a wider claim
> could be; nothing here says the `(δ₁,δ₂)` profile cannot reach `(0, ·)` or
> `(5, ·)` on some other population. The `2 946` and the `248` reproduce
> (BE-276)(i) exactly, which is a **same-input reproduction and not an
> independent check** — same job list, same seed, same gates, by construction.
>
> **(BE-292)(ii)** `[PROVED]` — *the consequence for (BE-259)(ii)'s own
> derivation, and it is not the one the clause expects.* (BE-259)(ii) closes
> `Π_x` by: `c_i(Π_x) = 2 ⟹ ρ_i = 6 ⟹ δ_i = 6 ⟹ δ_j = 0 ⟹ ρ_j = 0 ⟹
> c_j(Π_x) = 0`. At every peel of the residue corner `δ_i ≤ 4`, so `ρ_i = 6`
> is **impossible**; the contrapositive of the measured step gives
> `c_i(Π_x) ≤ 1` on **both** sides directly and `c₁ + c₂ ≤ 2 = dim Π_x`
> follows with **no** rigid-side step. So on the corner the clause's *chain*
> never runs: **all of the work is done by the measured implication itself,
> and none by the δ-arithmetic.** That is worth saying because the clause's
> prose presents the δ-collapse as the mechanism, and on the only population
> where the clause is not already proved, the δ-collapse cannot fire.

---

### Step BE292 — (BE-293): **THE RESIDUE IS NOT A LEMMA — it is a ONE-DRAW CERTIFICATE, and the corpus's own ledger already issues it**

> **(BE-293)(i)** `[PROVED]` — ***the certificate.*** *Fix a peel `(H; x, y)`,
> a side `i` and a stable block `U`. Let `q ∈ Chart(H)` be a configuration at
> which*
>
> > *(a) `a_i(q) = 0`;  (b) `ρ_i(q) = δ_i ≤ 5`;  (c) `c_i(U)(q) < dim U`.*
>
> *Then `{U ⊆ ρ̄_i}` is a **proper** closed condition: the generic point of
> `Chart(H)` is not in it, i.e. **generically `U ⊄ ρ̄_i`**.*
>
> *Proof.* `Chart(H)` is irreducible ((BE-65)(ii), citing §(K-chart) (CH-1)(a)
> under `hcard`, min degree `2`, girth `≥ 4`, characteristic `0`), so every
> nonempty open subset of it is dense and two of them meet — the (BE-255)(ii)
> lever. Three semicontinuities, **in three different directions**, and the
> proof is that they compose:
> * `a_i = dim M_i − 6 − f_i` is **upper** semicontinuous ((BE-255)(i) row 3,
>   *"so `a_i = 0` at a draw **proves** `a_i = 0` generically"*), so
>   `Ω₃ := {a_i = 0}` is **open**, and (a) makes it nonempty, hence **dense**.
> * On `Ω₃`, (BE-22)(ii)'s `ρ_i ≤ dim M_i − 6 − g_i = δ_i + a_i` reads
>   `ρ_i ≤ δ_i` — a **pointwise cap by a combinatorial constant**, now holding
>   on a *neighbourhood* rather than at a point, which is the whole reason (a)
>   is in the hypothesis. `ρ_i` is **lower** semicontinuous (row 2), so
>   `Ω₂ := Ω₃ ∩ {ρ_i ≥ δ_i} = Ω₃ ∩ {ρ_i = δ_i}` is **open**, and (b) makes it
>   nonempty, hence **dense**.
> * On `Ω₂` the value of `ρ_i` is **constant** (`= δ_i`), which is exactly the
>   hypothesis of row 4: `c_i(U) = dim(ρ̄_i ∩ U)` is **upper** semicontinuous
>   there, so its **generic** value on `Ω₂` is its **minimum**, and by (c)
>   that minimum is `≤ c_i(U)(q) < dim U`.
>
> `Ω₂` is dense open, so the generic point of `Chart(H)` lies in it and has
> `c_i(U) < dim U`. Hence `{c_i(U) = dim U}` contains no nonempty open, i.e.
> it is contained in a proper closed subset. ∎
>
> **Three things this proof is, said plainly.** It is **not new
> mathematics** — every ingredient is a landed row of (BE-255)(i) plus
> (BE-22)(ii). It is **the first time rows 2, 3 and 4 are used together**: the
> corpus uses row 3 alone at (BE-69)(iii), row 4 alone at (BE-258)/(BE-273),
> and row 2 alone when it says *"`ρ_i = δ_i` at a draw is a theorem"*. And it
> is a **witness**, not a search — **no cap attaches to a row that
> certifies**; the cap attaches only to the *denominator*, i.e. to how many
> peels one has exhibited a certifying draw for.
>
> **(BE-293)(ii)** — *what this does to the two residue clauses,
> and it is a reframing rather than a discharge.* Neither (BE-259)(ii) nor
> (BE-277)(iii) is asking for a *universal* statement in the sense a lemma
> would give — read at the owning sections, both ask for *"a proof that
> `U ⊆ ρ̄_i` is a proper closed condition"*, and **properness is a property of
> one peel**, not of the class. (BE-293)(i) supplies that proof, **per peel,
> from one draw**. What it does **not** supply is a statement quantified over
> **all** internal R-node peels at rung 3, which is what would let the two
> clauses drop the words *"at 427 of 427 rows"* from their evidence line. So
> the honest score is: **the residue as literally stated is discharged
> peel-by-peel by a landed-ingredient proof — and, measured, discharged at
> EVERY eligible row of the population the two clauses cite ((BE-293)(iv));
> the residue as the clauses INTEND it — a class statement over all internal
> R-node peels — is not, and is not the same object.** The
> distinction is the direction's main deliverable and it is stated before any
> figure, because a figure cannot make it.
>
> **(BE-293)(iii)** — *the hypothesis that is doing real work,
> and where a successor should attack.* Clause (b) needs `ρ_i(q) = δ_i` —
> **the side must ATTAIN**. That is precisely (BE-22)(iii)(a), the 2-cut
> composition's own first requirement, and it is *not* automatic. **A
> warning, because this direction nearly got it wrong:** (BE-262)(i)'s
> *"the confinement tight at 234"* is **NOT** this condition. Read at its
> owning clause (BE-257)(ii), *"tight"* means **`δ_i = m_i`** with
> `m_i = dim ⋂_P ⟨P⟩` — the **path** confinement — and the histogram is of
> `δ − m`. It says nothing about `ρ_i = δ_i`. The attainment rate this
> certificate needs is measured here, separately, in (BE-293)(iv). At a
> non-attaining row the certificate is **unavailable**, not false: `ρ_i(q) < δ_i` leaves open that
> the generic `ρ_i` is larger and the draw sits on a proper closed subset, and
> then row 4 propagates the `c_i` bound only across that subset. **A
> successor's cheapest move is therefore NOT the uniform lemma but a driver
> that, at each of the 248 residue-corner peels, hunts for one `a_i = 0`,
> `ρ_i = δ_i` draw** — each success is a theorem at that peel and the run is a
> *witness hunt*, whose failures cost nothing but a cap sentence.
>
> **(BE-293)(iv)** `[MEASURED]` — *the certificate census, and the denominator
> is the only thing capped.* `bpropcl.py gp`, **517 s**, seed `20260912`,
> exact ℚ, **427 library rows × 3 draws = 1 281 draws** over **400 distinct
> sides** (see (BE-298)(iii) for why those two numbers differ).
>
> * **`a_i = 0` at 1 281 of 1 281 draws** — clause (a) everywhere.
> * **A draw with `a_i = 0` AND `ρ_i = δ_i` exists at 400 of 400 distinct
>   sides** — clause (b)'s attainment half holds at **every** row of this
>   library. **This is the first time `ρ_i = δ_i` has been counted on this
>   population.** It is *not* (BE-262)(i)'s *"confinement tight at 234 of
>   257"*, which is `δ_i = m_i` on the **path** confinement ((BE-257)(ii)'s
>   `δ − m` histogram) and a different statistic entirely.
> * **25 of the 400 rows have `ρ_i = δ_i = 6`**, so clause (b)'s `≤ 5` fails
>   and the certificate does not apply. **Those are not failures**: at
>   `ρ_i = 6`, `ρ̄_i = Λ²K⁴` and `U ⊆ ρ̄_i` **genuinely holds** for every `U`
>   ((BE-99)(i)) — they are exactly the case the *arithmetic* handles, by
>   `δ_i = 6 ⟹ δ_j = 0` ((BE-259)(ii)) and by `Σδ ≤ 6` ((BE-274)(i)).
> * **Of the 375 ELIGIBLE rows (`ρ_i = δ_i ≤ 5`), properness is CERTIFIED at
>   375 — every one — for BOTH `Π_x` and `⟨M⟩`.** **THE DERIVATION OF THE
>   `375`, since the driver prints the certified count and not the eligible
>   one:** all 400 rows carry an `a_i = 0`, `ρ_i = δ_i` draw; a row is
>   ineligible exactly when that draw has `ρ_i = 6` (and then `δ_i = 6` too,
>   `ρ_i ≤ δ_i ≤ 6`); the joint shows `ρ_i = 6` at `21 + 54 = 75` draws, i.e.
>   `25` rows; `400 − 25 = 375`, which is the certified count.
> * **In the residue regime** (`dist_i ≥ 6`, where the confinement is
>   vacuous): **40** distinct rows, of which **25** have `ρ_i = 6` and **15**
>   have `ρ_i ≤ 5`; **all 15 certify, for both blocks — 15 of 15.** (Same
>   derivation: the `ρ_i = 6` rows are the whole of the `25`, since every
>   `ρ_i = 6` draw in the joint sits at `dist ∈ {6, 7}`.)
>
> **So on this library the residue is not open at a single row: at every row
> where the question is asked, the answer is PROVED.** What is capped is the
> **denominator** — this library, these shapes — and a wider population could
> contain a row where no `a_i = 0`, `ρ_i = δ_i ≤ 5` draw exists. **A
> certifying row carries NO cap**: it is a witness. **NOT FOUND under cap C**
> applies only to the claim *"no non-certifying row exists"*, which this
> direction does not make.

---

### Step BE293 — (BE-294): **GENERAL POSITION IS FALSE AT `Π_x`** — the mechanism both residue clauses name, tested per draw and refuted, with its cause named

> **(BE-294)(i)** `[PROVED]` — ***the hinge-line identity, read off two function
> bodies.*** *At any configuration at which `Π_x` is defined,
> `Π_x = ⟨ p_x ∧ p_w : w ∈ N_H(x) ⟩`; in particular **every** hinge line of
> **either** side at `x` lies in `Π_x`, and any two non-coincident ones
> **span** it.*
>
> *Proof.* `bunif.blocks_of` sets `Π_x = bimage.pencil_space(p_x, plane_at(H,
> pt, x))`. `plane_at`'s body is `star = [p̂_x] + [p̂_w : w ∈ N(x)]` followed by
> `if rank_exact(star) != 3: return None`, and it returns a basis of the
> 3-space `π_x` spanned by `star`. So `p_w ∈ π_x` for every `w ∈ N(x)` and
> `p_x ∈ π_x`, whence `p_x ∧ p_w ∈ p_x ∧ π_x = Π_x`. `pencil_space` asserts
> `dim Π_x = 2`, and `Π_x = p_x ∧ (π_x/⟨p_x⟩)` is spanned by the images of any
> two `p_w` independent modulo `p_x` — i.e. by two hinge lines at `x` that do
> not coincide, which is exactly the carrier's own hinge-coincidence gate
> (`bimage.legal_chain`'s *"no three consecutive points collinear"*,
> (BE-30)(ii)/(iii)). ∎
>
> **PRIORITY, stated because `HEAD` moved under this direction.** The
> pointwise fact `ℓ₁ ∈ Π_x` is **BSIXTEEN's**, landed at `0bd802e7` in
> (BE-280)(iii) — *"`ℓ₁ ∈ Π_x` **pointwise**, so the path instrument can
> never exclude an end block"* — while this direction was running. It was
> derived here independently from `plane_at`'s body; it is **not** claimed as
> new, and the clause is kept because what *is* new is the use made of it in
> (ii) and (iii). **This is a definition-body reading, not a docstring one** —
> the project's standing caution — and it is the whole asymmetry with `⟨M⟩`. **`Π_x` is the
> span of the hinge lines AT `x`. `⟨M⟩ = ⟨p_x ∧ p_y⟩` is the hinge line of an
> edge that is ABSENT from both sides** (`x ≁ y` is the in-region gate,
> (BE-272)(iii)) **and lies in the DIRECT COMPLEMENT of both pencils** —
> `bunif.blocks_of`'s own assert is `dim(Π_x + Π_y + ⟨M⟩ + ⟨L⟩) = 6`, a direct
> sum of `2+2+1+1`, so `⟨M⟩ ∩ Π_x = ⟨M⟩ ∩ Π_y = 0`.
>
> **(BE-294)(ii)** `[PROVED]` — ***the saturation mechanism***, and it is why
> general position cannot be a lemma at `Π_x`. *Let `P₀` be a shortest x–y
> path of side `i` and suppose side `i` is **saturated** at the configuration,
> `ρ_i = dim ⟨P₀⟩`. Then `c_i(Π_x) ≥ 1` **pointwise** — with no genericity
> anywhere — and in particular general position **fails** whenever
> `ρ_i ≤ 4`.*
>
> *Proof.* `ρ̄_i ⊆ ⟨P₀⟩` at **every** configuration ((BE-30)(iv)); with
> `dim ρ̄_i = ρ_i = dim ⟨P₀⟩` the containment is an **equality**, so
> `ρ̄_i = ⟨P₀⟩ ∋ ℓ₁ = p_x ∧ p_1`, the path's first hinge line. `p_1` is a
> side-`i` neighbour of `x`, so `ℓ₁ ∈ Π_x` by (i). Hence
> `0 ≠ ⟨ℓ₁⟩ ⊆ ρ̄_i ∩ Π_x` and `c_i(Π_x) ≥ 1`. The general-position value is
> `max(0, ρ_i − 4)`, which is `0` for `ρ_i ≤ 4`. ∎
>
> ***And the same hypothesis gives NOTHING at `⟨M⟩`, for exactly the reason
> (BE-272)(ii) is a theorem:*** saturation gives `ρ̄_i = ⟨P₀⟩`, and
> `dim(⟨P₀⟩ ∩ ⟨M⟩) = 0` for every path of edge-length `2 ≤ m ≤ 5` — the path
> lemma — so `c_i(⟨M⟩) = 0` there. **The path lemma is precisely the statement
> that the `Π_x` mechanism has no analogue at `⟨M⟩`.** That is the divergence
> the dispatch's *"where I expect to be wrong"* sentence predicted, located.
>
> **(BE-294)(iii)** `[MEASURED]` — `bpropcl.py gp`, **517 s**, seed `20260912`,
> exact ℚ, **427 side rows × 3 draws = 1 281 draws**, every line an assert.
> **The library, the seed ladder and the path cap are `run_pix`'s own**
> (`side_library(maxarc=8, maxtheta=7, nlad=40)` + `side1_library()`,
> `xy_paths(cap=400, maxlen=9)`, `rng = Random(seed + 733·s + len(E))`), so
> the rows **are** (BE-258)(iii)'s and (BE-273)(i)'s rows. **SAID BEFORE THE
> TABLE, because (BE-273)(i) had to say it too: this is a SAME-INPUT
> REPRODUCTION, not an independent check.** Same library, same integer seed,
> same ladder — the denominators cannot disagree, and what the match buys is
> that the **new `ρ` axis** is read on the **same** rows as the two landed
> columns, nothing more.
>
> **What reproduces.** (BE-258)(iii)'s `(dist, c(Π_x))` histogram, bucket for
> bucket: `{(2,0): 190, (2,1): 13, (3,0): 91, (3,1): 12, (4,0): 49, (4,1): 9,
> (5,0): 15, (5,1): 7, (6,0): 15, (6,1): 1, (6,2): 7, (7,2): 18}`. And
> (BE-273)(i)'s `⟨M⟩` column: `0` at every row with `dist ≤ 5`, `0`×16 / `1`×7
> at `dist = 6`, `1`×18 at `dist = 7`.
>
> **What is new — the `ρ` axis both landed drivers compute and neither
> prints.** `(dist, ρ, c(Π_x))` → count =
> `{(2,0,0): 546, (2,1,0): 24, (2,2,1): 39, (3,0,0): 213, (3,1,0): 36,
> (3,2,0): 24, (3,3,1): 36, (4,0,0): 81, (4,1,0): 15, (4,2,0): 30,
> (4,3,0): 21, (4,4,1): 27, (5,0,0): 3, (5,1,0): 6, (5,2,0): 3, (5,3,0): 18,
> (5,4,0): 15, (5,5,1): 21, (6,2,0): 6, (6,3,0): 36, (6,4,0): 3, (6,5,1): 3,
> (6,6,2): 21, (7,6,2): 54}`, and `(dist, ρ, c(⟨M⟩))` is the same table with
> the `c` coordinate `0` everywhere except `(6,6,1): 21` and `(7,6,1): 54`.
>
> * **GENERAL POSITION IS EXCEEDED AT `Π_x` AT 102 OF 1 281 DRAWS** and
>   **NEVER SHORT**. At `⟨M⟩` it is exceeded at **0 of 1 281** and never
>   short: `c_i(⟨M⟩) = max(0, ρ_i − 5)` **exactly**, at every draw.
> * **THE EXCESS IS SATURATION, AND NOTHING ELSE.** `ρ_i = dim ⟨P₀⟩` at
>   **198** draws, and at **198 of 198** the asserts `ℓ₁ ∈ ρ̄_i`,
>   `ℓ₁ ∈ Π_x` and `c_i(Π_x) ≥ 1` all hold — (BE-294)(ii) tested rather than
>   argued. The **exact law**
>
>   > **`c_i(Π_x) = max(0, ρ_i − 4) + [side i saturated and ρ_i ≤ 4]`** and
>   > **`c_i(⟨M⟩) = max(0, ρ_i − 5)`**
>
>   is **asserted in the driver and fires at 0 of 1 281 draws.** **The
>   assert's own provenance, stated rather than implied** (the direction
>   core's *"write your verification sentence by re-reading the driver"*):
>   the law was first read off the printed joint, the assert was written
>   afterwards, and the driver was then **re-run from scratch at
>   `ndraw = 3`** — 491.3 s, exit 0, the same `400 / 375 / 40 / 15` row
>   counts — so the sentence above is a statement about an executed assert,
>   not about an inspection. The `≥` half of the first law is PROVED
>   ((BE-294)(ii)); the *equality* — that saturation is the **only** excess —
>   is MEASURED, and is what this clause claims.
> * **AND THE INTERSECTION LINE IS A HINGE.** At the **102** excess draws the
>   line `ρ̄_i ∩ Π_x` **is** a side-`i` hinge line at `x` at **102 of 102**.
>   At the **24** non-excess draws with `c_i(Π_x) = 1` it is a hinge at
>   **21** (the `dist = ρ = 5` rows, saturated) and **not** a hinge at **3** —
>   and those `3` are exactly the `(dist = 6, ρ = 5)` draws, where general
>   position is attained. **The two populations separate cleanly on the hinge
>   test**, which is what makes *saturation* a mechanism and not a coincidence.
> * **THE RESIDUE REGIME.** At `dist ≥ 6` and `ρ_i ≤ 5` — the corner both
>   clauses leave open — `(ρ_i, c_i(Π_x))` = `{(2,0): 6, (3,0): 36, (4,0): 3,
>   (5,1): 3}` and `(ρ_i, c_i(⟨M⟩))` = `{(2,0): 6, (3,0): 36, (4,0): 3,
>   (5,0): 3}`. **`Π_x ⊄ ρ̄_i` and `⟨M⟩ ⊄ ρ̄_i` at 48 of 48 draws — 16 library
>   rows, 15 distinct sides.** That is the dispatch's TELL, and it fires. It
>   also **reproduces, at draw resolution, the 16 rows (BE-258)(iii) and
>   (BE-273)(i) already report at `dist = 6`** — `c_i(Π_x)` `0`×15 + `1`×1 and
>   `c_i(⟨M⟩)` `0`×16 — which the spec recorded as *"not reported anywhere"*.
>   **It is reported; it was never read as a containment statement.**
> * **`a_i = 0` at 1 281 of 1 281 draws** (`a_i = dim M_i − 6 − d3(side)`, the
>   arithmetic `bproper.run_proper` uses), so clause (a) of the certificate
>   holds everywhere on this library.
>
> **CAP, and it travels:** this library, these branch shapes, 3 draws per row,
> `maxlen = 9` path enumeration, and — the axis (BE-273)(i) measured — **the
> per-distance denominators move by up to 10 rows with the seed, so they are a
> cap, not a constant.** Every counting figure above is **NOT FOUND under cap
> C** in the search direction; the *saturation* asserts and the *certificate*
> are witnesses and carry no cap.
>
> **(BE-294)(iv)** `[MEASURED]` — ***BSIXTEEN's (BE-281)(iii) REFRAMING,
> TESTED — and it is the lemma.*** `bpropcl.py gp`, same run, same rows. With
>
> > **`gpP(U) := max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)`**
>
> — general position **inside the path span** rather than inside `Λ²K⁴`, and
> equal to `bunif.generic_c(ρ_i, dim U)` **exactly when `dim ⟨P₀⟩ = 6`** —
> the driver asserts `c_i(Π_x) = gpP(Π_x)` and `c_i(⟨M⟩) = gpP(⟨M⟩)` at
> **every draw**, and **fires at 0 of 1 281** (`bpropcl.py gp`, 480.2 s,
> exit 0, every other figure reproducing exactly: `102 / 198 / 102-of-102 /
> 21-and-3 / 375 / 15`).
>
> The joint `(dim ⟨P₀⟩, dim(⟨P₀⟩ ∩ Π_x), ρ_i, c_i(Π_x))` → count, at
> `ndraw = 1` (`427` draws) =
> `{(2,1,0,0): 182, (2,1,1,0): 8, (2,1,2,1): 13, (3,1,0,0): 71, (3,1,1,0): 12,
> (3,1,2,0): 8, (3,1,3,1): 12, (4,1,0,0): 27, (4,1,1,0): 5, (4,1,2,0): 10,
> (4,1,3,0): 7, (4,1,4,1): 9, (5,1,0,0): 1, (5,1,1,0): 2, (5,1,2,0): 1,
> (5,1,3,0): 6, (5,1,4,0): 5, (5,1,5,1): 7, (6,2,2,0): 2, (6,2,3,0): 12,
> (6,2,4,0): 1, (6,2,5,1): 1, (6,2,6,2): 25}`.
>
> **Read across it:** `dim(⟨P₀⟩ ∩ Π_x) = 1` at every draw with
> `dim ⟨P₀⟩ ≤ 5` and `= 2` at `dim ⟨P₀⟩ = 6` — which is (BE-258)(i)'s
> `max(1, min(d,6) − 3)` α-column **restricted to `Λ²π_x`**, measured
> directly here rather than inferred from the α-bound. That single column is
> the whole of the `Λ²K⁴` frame's failure: `gp` uses `dim U = 2`, `gpP` uses
> the **actual** `dim(⟨P₀⟩ ∩ U)`, and below `dim ⟨P₀⟩ = 6` those differ by
> exactly `1` at `Π_x` and by exactly `1` at `⟨M⟩` (`dim(⟨P₀⟩ ∩ ⟨M⟩) = 0`
> against `dim ⟨M⟩ = 1`, which is (BE-272)(ii)).
>
> **WHAT THIS SETTLES AND WHAT IT DOES NOT.** It settles that **one lemma
> covers both residues** — BSIXTEEN's, not the one the residue clauses
> state — and that this direction's `dim ⟨P₀⟩ = 6` corner is its **top
> instance**, where `gpP` degenerates to `gp` and the two frames agree. It
> does **not** prove `gpP`: `gpP` is `[MEASURED]` here at 1 281 of 1 281
> exactly as the `Λ²K⁴` form was, and the residue is now *"prove `gpP`"*
> rather than *"prove general position"*. **The gain is that the target is
> one statement instead of two, and that it is stated in a frame where it is
> not already false.**

---

### Step BE294 — (BE-295): **THE VERDICT — the two residues are NOT one question, and the sharpened statement each one actually needs**

> **(BE-295)(i)** `[PROVED]` / `[MEASURED]` — **THE VERDICT, with the quantifier
> it carries.** (BE-277)(iii) states: *"the `Π_x` residue and the `⟨M⟩` residue
> are the same question about `ρ̄_i` in general position against a stable block
> once the path confinement has gone vacuous"*, and *"a single lemma would
> discharge both"*. **REFUTED as stated, and the refutation is a proof, not a
> tally.** The single lemma that would discharge both is *"`ρ̄_i` is in general
> position against every stable block at `dim ⟨P₀⟩ = 6`"*, and:
> * at `⟨M⟩` that lemma is **exactly** what is needed and is **unviolated** on
>   the landed population (general position exceeded at **0 of 1 281** draws);
> * at `Π_x` the *same* lemma is **FALSE** — not merely unproved. (BE-294)(ii)
>   gives a **pointwise** mechanism producing `c_i(Π_x) ≥ 1` against a
>   general-position prediction of `0`, and it **fires on the landed
>   population**: general position exceeded at **102 of 1 281** draws.
>
> **AND THE REPAIR ARRIVED FROM THE OTHER LANE WHILE THIS DIRECTION RAN.**
> BSIXTEEN (111) landed at `0bd802e7` mid-run and its (BE-281)(iii) proposes
> exactly the right fix: *"a single lemma stated relative to `⟨P₀⟩` rather
> than to `Λ²K⁴` would discharge both"*. **Tested here and it holds.** Define
> the `⟨P₀⟩`-relative general-position value
>
> > **`gpP(U) := max(0, ρ_i + dim(⟨P₀⟩ ∩ U) − dim ⟨P₀⟩)`**,
>
> which coincides with `bunif.generic_c(ρ_i, dim U)` **exactly when
> `dim ⟨P₀⟩ = 6`**. Then **`c_i(U) = gpP(U)` at every draw, at BOTH blocks**
> — asserted, `0` exceptions ((BE-294)(iv)). **So (BE-277)(iii)'s *"a single
> lemma would discharge both"* is CONFIRMED, in BSIXTEEN's frame and not in
> the frame the residue clauses state it in**, and the two directions
> converge on the same lemma from opposite ends of the `dim ⟨P₀⟩` axis:
> BSIXTEEN needs the `dim ⟨P₀⟩ ∈ {4, 5}` instances ((BE-280)(iv)), this
> direction the `dim ⟨P₀⟩ = 6` instance. **The refutation above is not
> withdrawn — it is what forces the reframing:** the `Λ²K⁴` form is false at
> `Π_x`, and `gpP` is false-free precisely because at saturation
> (`ρ_i = dim ⟨P₀⟩`) it *predicts* `c_i(Π_x) = dim(⟨P₀⟩ ∩ Π_x) ≥ 1` instead
> of `0`.
>
> **What survives of "two questions".** They *agree* on their conclusion
> **inside the corner**, and that is why the two clauses could be mistaken for
> one: at `dist_i ≥ 6` the shortest-path span is the whole screw space at
> every draw taken ((BE-273)(i)'s `dim(⟨P₀⟩ ∩ ⟨M⟩) = 1` column at
> `dist ∈ {6,7}`, and (BE-272)(ii)'s `m ≥ 6` row), so **saturation there
> would force `ρ_i = dim ⟨P₀⟩ = 6`** and cannot happen at `ρ_i ≤ 5`. **But
> they do not agree on the statement that would PROVE it**, and a lemma true
> at `⟨M⟩` and false at `Π_x` is not one lemma. The corner is where the two
> *answers* coincide; the residue clauses read that coincidence as an identity
> of *questions*, and it is not one.
>
> **(BE-295)(ii)** `[PROVED]` — *the sharpened statements, one per block, and
> the `Π_x` one is strictly harder.* On the population (BE-276)(i) prices,
> (BE-292)(i) gives `δ_i ≤ 4` on both sides at all **248** residue-corner
> peels, so `ρ_i ≤ 4` there. **THE DERIVATION OF THE `4`, since a bound
> naming a number carries it:** `min(δ₁, δ₂) ≥ 2` is **measured** at 248 of
> 248 ((BE-292)(i)) and `δ₁ + δ₂ ≤ 6` is rung 3 ((BE-225)(iii)), so
> `max(δ₁, δ₂) ≤ 4`; with `ρ_i ≤ δ_i` ((BE-22)(ii) at `a_i = 0`) that gives
> `ρ_i ≤ 4`. **The `ρ_i = 5` case is not impossible in general** — the side
> library carries rows with `dist = 6` and `ρ = 5` ((BE-294)(iii)'s `(6,5,1)`
> draws) — it is excluded from the COMPOSITE corner by `Σδ ≤ 6` together with
> the measured `min(δ) ≥ 2`, and that second ingredient is a measurement with
> a cap. The two residues then read:
>
> | block | what the corner actually needs | why it is not the same statement |
> |---|---|---|
> | `⟨M⟩`, `du = 1` | `ρ_i ≤ 4 ⟹ p_x ∧ p_y ∉ ρ̄_i` | `⟨M⟩ ∩ Π_x = ⟨M⟩ ∩ Π_y = 0`: no hinge of either side lies in it, so no saturation mechanism can put it in `ρ̄_i` |
> | `Π_x`, `du = 2` | `ρ_i ≤ 4 ⟹ Π_x ⊄ ρ̄_i`, i.e. **both** hinge directions at `x` are not simultaneously realized as (x,y)-relative screws | `Π_x` **is** the span of side `i`'s own hinges at `x`, and one of them is already in `ρ̄_i` at every saturated configuration |
>
> **The `Π_x` residue is a statement about the side's own hinges and the
> `⟨M⟩` residue is a statement about a line that is not a hinge at all.** A
> successor attacking them should expect two proofs, and should expect the
> `⟨M⟩` one first: it is the one whose mechanism survives contact with the
> population.
>
> **(BE-295)(iii)** — *a correction to both clauses' hypothesis,
> and it is a sharpening rather than a defect.* Both write the residue at
> `ρ_i ≤ 5`. At **248 of 248** residue-corner peels `δ_i ≤ 4`, hence
> `ρ_i ≤ 4`; the case `ρ_i = 5` — which is the *dangerous* one at `Π_x`,
> since `c_i(Π_x) = 2` at `ρ_i = 5` on one side together with `c_j(Π_x) = 1`
> at `ρ_j = 1` on the other is a **margin `+1`** and a `Good = ∅` route —
> **does not occur in the corner of the population the clauses cite**. This
> does not make either statement wrong (`≤ 5` is implied by `≤ 4`); it means
> the hypothesis is **not tight**, and that a successor proving the `ρ_i ≤ 4`
> case has discharged the residue **on this population** without touching
> `ρ_i = 5`. **CAP:** this is a statement about `bgoodempty.run_block`'s
> committed job list, not about all pieces; a wider population may reach
> `δ_i = 5` with `dist_i ≥ 6` on both sides. **NOT FOUND under cap C.**

---

### Step BE295 — (BE-296): what this direction does NOT claim, stated before the board

> **(BE-296)(i)** — **it does not prove the uniform lemma, at
> either block.** (BE-293)(i) proves properness **per peel from a
> certificate**; it quantifies over nothing. Nothing here shows that every
> internal R-node peel at rung 3 admits a certifying draw, and the rows that
> do not certify are **not** counterexamples — they are rows at which no
> `a_i = 0`, `ρ_i = δ_i` draw was obtained under this cap.
>
> **(BE-296)(ii)** — **it does not exhibit a `Good = ∅` piece and
> does not open a route to one.** The refutation in (BE-295)(i) is of a
> *proof strategy*, not of either landed closure: (BE-259)(ii)'s and
> (BE-274)(i)'s measured steps are **not contradicted anywhere** — every draw
> taken here satisfies them, `c_i(Π_x) = 2` occurring only at `ρ_i = 6` and
> `c_i(⟨M⟩) = 1` only at `ρ_i = 6`. **The general-position excesses at `Π_x`
> are all `c_i(Π_x) = 1`, never `2`**, so none of them is a bite and none of
> them is a `Good = ∅` shape.
>
> **(BE-296)(iii)** — **it does not touch a block.** The eleven
> remaining stable blocks of (BE-97)(iv) are **BSIXTEEN's** (ordinal 111);
> nothing here closes or opens one. `Π_y` is the x/y mirror of `Π_x` and every
> statement above transposes, but the measurements are taken at `x` only and
> are reported as such.
>
> **(BE-296)(iv)** — **the Chart(side) / Chart(H) gap, disclosed
> because it is the widest axis here.** Every measured figure in (BE-294) and
> (BE-293)'s certificate census is taken on `Chart(side)` by
> `bdecor.sample_by_branches`, exactly as (BE-258)(iii) and (BE-273)(i) are;
> the certificate of (BE-293)(i) is stated on `Chart(H)`. They agree **iff**
> the restriction `Chart(H) → Chart(side_i)` is dominant, which this direction
> **did not verify and does not assume**. The one thing checked is the piece
> of it that would break `Π_x`: `π_x` is the closed-star plane of `x` in
> whichever graph it is computed in, and side `i`'s own two hinges at `x` span
> it at **every** draw (BE-294)(i)'s assert — so `Π_x` computed on the side
> equals `Π_x` computed on `H` whenever `deg_i(x) ≥ 2`, which the in-region
> gate enforces. **The dominance question itself is open and is a
> coordinator's to route**, since it conditions every side-row figure the lane
> has taken, not only this direction's.

---

### Step BE296 — (BE-297): the board, and the dispatch's prediction scored — verdict, mechanism and tell SEPARATELY

> **(BE-297)(i)** — **the board. What moved.** The F26 consumer
> check, run first and reported against this direction's own interest
> ((BE-291)); the residue corner's `(δ₁, δ₂)` profile, a field
> `bmblock.run_reach` **computes and drops**, printed draw-free over the same
> committed job list — `δ_i ≤ 4` on **both** sides at **248 of 248**, hence
> `ρ_i ≤ 4`, hence both clauses' `ρ_i ≤ 5` hypothesis is **not tight**
> ((BE-292)); the observation that at every corner peel (BE-259)(ii)'s own
> `δ_j = 0` collapse **cannot fire**, so the measured step carries the whole
> closure there ((BE-292)(ii)); **the one-draw properness certificate**,
> which composes rows 2, 3 and 4 of (BE-255)(i) — three semicontinuities in
> three directions — into a cap-free per-peel proof, an assembly the corpus
> has not made ((BE-293)); the hinge-line identity `Π_x = ⟨p_x ∧ p_w :
> w ∈ N_H(x)⟩` read off `plane_at`'s body ((BE-294)(i)); **the saturation
> mechanism**, which makes general position **pointwise false** at `Π_x` and
> gives nothing at `⟨M⟩` for exactly the reason (BE-272)(ii) is a theorem
> ((BE-294)(ii)); and the joint `(dist, ρ, c(U))` distribution that `run_pix`
> and `bmblock.run_side` both compute and neither prints; the certificate
> census — **375 of 375 eligible rows certify, 15 of 15 in the residue
> regime** ((BE-293)(iv)); and a disclosure about a landed denominator — the
> 427-row side library is **400 distinct sides**, `side_library` and
> `side1_library` overlapping in exactly **27** shapes ((BE-298)(iii)). **And
> the cross-return item: BSIXTEEN's (BE-281)(iii) `⟨P₀⟩`-relative reframing,
> landed at `0bd802e7` during this run, TESTED AND CONFIRMED at both blocks —
> `c_i(U) = gpP(U)` with 0 exceptions — which reverses this direction's own
> first headline ((BE-294)(iv), (BE-298)(vii)).**
>
> **What did NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`,
> (GR-15), **(BE-14)**, the S-mark, half (B), half (β), the 2-cut step, class
> uniformity, cross-pair welding, `(BE-E4′)`, the flag base, `(BE-OBL7)`,
> `(BE-OBLK)`, (BE-253)'s verdict and certificate, (BE-262)'s verdict,
> (BE-277)(i)'s verdict, the eleven blocks BSIXTEEN holds, and **every landed
> measurement** — this direction contradicts none of them. In particular
> **(BE-259)(ii) and (BE-274)(i) are not contradicted**: every draw here
> satisfies both measured steps. What is refuted is a *sentence about them* —
> (BE-277)(iii)'s *"a single lemma would discharge both"*. **The E-rider:** no
> termination-ledger entry fires; E1/E2/E3 are §(K-grid) objects and the
> sibling on that lane is GODDRUNG (112).
>
> **(BE-297)(ii)** — **the dispatch's prediction, scored; verdict,
> mechanism and tell separately, per `RESEARCH-ARC.md` §7.**
> * **VERDICT: SPLIT, and one half reversed itself in the last hour.** The spec predicted *"It is proper — the containment
>   cuts out a genuine closed subvariety, not the whole chart — so both
>   closures go unconditional."* **Properness: CONFIRMED**, and better than
>   predicted — it is not merely true, it is **provable from landed
>   ingredients at any peel where one certifying draw exists** ((BE-293)(i)),
>   and no draw anywhere in this direction's 1 281 contradicts it. **"So both
>   closures go unconditional": REFUTED as stated** — properness per peel is
>   not a class statement, and the two closures quantify over the class. **And
>   the framing the spec inherited from the board — that this is ONE lemma —
>   **is refuted in the frame it is stated in and CONFIRMED in BSIXTEEN's**
   ((BE-295)(i), (BE-294)(iv)) — see (BE-298)(vii).
> * **THE SPEC'S *"WHERE I EXPECT TO BE WRONG"* SENTENCE: CORRECT, and again
>   the highest-yield sentence in the spec.** It said *"I expect to be wrong
>   that the two residues are **one** question"*, named the two differences
>   (regime, and `Π_x`'s operator against `⟨M⟩`'s absence of one), and
>   instructed: *"if a single lemma does not cover both, finding the precise
>   point where they diverge is a better return than half-proving the
>   union"*. **Acting on that instruction is what produced (BE-294).** The
>   divergence is *not* the operator `α_x` the spec guessed at — `α_x` is
>   vacuous in the corner, which is what makes the corner a residue at all —
>   it is that **`Π_x` is the span of the side's own hinges at `x` and `⟨M⟩`
>   is in the direct complement of both pencils**.
> * **MECHANISM: REFUTED, and refuted FIRST, before anything was built on
>   it.** The spec offered: *"`Chart(H)` is irreducible, so any proper closed
>   condition is nowhere dense, and the containment is cut out by the
>   vanishing of a minor that is not identically zero — exhibit one
>   non-vanishing point and properness follows."* The irreducibility half is
>   right and is used ((BE-293)(i)). **The "exhibit one point" half is wrong
>   as stated**: `{c_i(U) ≥ dim U}` is **not** closed on `Chart(H)` — it is
>   closed only on the locus where `ρ_i` is constant ((BE-255)(i) row 4) — so
>   a point with `c_i(U) < dim U` at *some* `ρ_i` proves nothing about the
>   generic `ρ_i`. That is why (BE-293)(i) needs clauses (a) and (b) at all,
>   and it is the difference between a certificate and a draw. **The spec's
>   own instruction to refute it cheaply first is what exposed this**; the
>   first slice run was `pop`, which uses no mechanism at all. The board's
>   mechanism field was `0 of 9` across three rounds before this one.
> * **TELL: FIRED, and it was ALREADY SATISFIED in the landed corpus — which
>   the spec said it was not.** The tell was *"one chart point in that region
>   at which `U ⊄ ρ̄_i`"*, and the spec recorded *"Already satisfied? Not
>   reported anywhere."* **Read at the owning clauses, it is reported, twice,
>   and neither clause read it as a containment statement.** (BE-258)(iii)'s
>   `dist = 6` column is `c_i(Π_x)` = `0`×15, `1`×1, `2`×7 — **16 rows with
>   `c_i(Π_x) ≤ 1`, i.e. `Π_x ⊄ ρ̄_i`** — and (BE-273)(i)'s `dist = 6` row is
>   `c_i(⟨M⟩)` = `0`×16, `1`×7 — **the same 16 rows with `⟨M⟩ ⊄ ρ̄_i`**.
>   Reproduced here at draw resolution. **The tell runs the right way**, as
>   the spec said: row 4 makes `c_i(U) < dim U` at a draw a bound in the
>   direction properness needs. **Could it have come out otherwise inside its
>   region?** Yes — the region is the `dist_i ≥ 6` rows, `c_i(U) = dim U` is
>   representable there (it occurs, at `ρ_i = 6`), and a row with
>   `c_i(U) = dim U` at `ρ_i ≤ 5` would have been a live `Good = ∅` route.
>   The tell was not structurally dead.

---

### Step BE297 — (BE-298): what this direction self-caught

> **(BE-298)(i)** — **the certificate's first statement was FALSE,
> and the missing clause is the one the corpus writes INTO the hypothesis.**
> The first draft of (BE-293)(i) had only clauses (b) and (c): *"one draw with
> `ρ_i = δ_i ≤ 5` and `c_i(U) < dim U` proves properness"*. That is **not a
> proof**: `ρ_i ≤ δ_i` is (BE-22)(ii) **at `a_i = 0`**, and without `a_i = 0`
> on a *neighbourhood* the set `{ρ_i = δ_i}` need not be open, so the density
> step — the one the whole argument turns on — does not run. Caught by reading
> (BE-22)(ii) at its owning section instead of trusting the gloss; the gloss
> is fine, and **(BE-274)(i)'s own law table writes L1 as `ρ_i ≤ δ_i` —
> (BE-22)(ii) at `a_i = 0`, hypothesis in the cell**, which is exactly the
> proviso the first draft dropped. Clause (a) is then free by row 3: `a_i` is
> **upper** semicontinuous, so one draw with `a_i = 0` proves it generically.
> **Measured: `a_i = 0` at 1 281 of 1 281 draws** (`bpropcl.py gp`, where
> `a_i = dim M_i − 6 − d3(side)`, the same arithmetic `bproper.run_proper`
> uses). So the clause is satisfied everywhere on this
> library — **and it is still a hypothesis, not a freebie**.
>
> **(BE-298)(ii)** — **a mis-scoped counter in this mode's first
> run, and it was hiding this direction's best figure.** The first `gp` run
> printed *"of the 102 excesses at `c(Π_x) = 1`, the intersection line IS a
> side hinge line at x at 123, is NOT at 3"*. `123 + 3 = 126 ≠ 102`: the
> counter ranged over **every** `c(Π_x) = 1` draw, not over the excesses.
> Caught by the arithmetic failing to close, not by a gate. The fix is to
> split the counter, and the split is the result: **the excesses are `102` of
> `102` hinge lines**, and the `3` non-hinge cases are exactly the
> `(dist = 6, ρ = 5)` draws — the ones where general position is **attained**.
> The defect had made the two populations look like one.
>
> **(BE-298)(iii)** — **a suspected defect of this direction's own
> that turned out to be a disclosure about a LANDED DENOMINATOR.** The first
> `ndraw = 1` run reported **427 draws over 400 rows** with **one draw per
> row**, which is impossible, and the first diagnosis was a key collision:
> `(tag, x, y)` is not a key, since `bgoodempty.side_library` and
> `side1_library` both emit `cyc(a,b)` / `gtheta(...)` / `ladder(...)` shapes.
> Re-keyed on the **edge set** — and the count did **not** move: still 400.
> So the two library halves do not merely share **names**, they share
> **graphs**. Measured directly: **the combined library is 428 entries and
> 401 distinct `(tag, x, y, edge-set)` sides; `side_library(8,7,40)` has 362
> distinct shapes, `side1_library()` has 66, and the overlap is exactly 27.**
> **So the landed "427 side rows" of (BE-258)(iii) and (BE-273)(i) is 400
> DISTINCT sides with 27 counted twice.** *Nothing is wrong with the 427 — it
> is what it says it is, a count of library rows that yielded a draw* — but a
> successor reading it as a count of distinct side shapes is over-reading it
> by 27. (`428` entries, `401` distinct, and the `428 → 427` attrition
> (BE-273)(i) records leaves `400` distinct sides with a usable draw.) **The
> duplication is not spread evenly over the `dist` axis:** the 27 are the
> `cyc`/`gtheta`/`ladder` shapes `side1_library()` shares with
> `side_library`, and **26 of them sit at `dist ≤ 5`, exactly 1 at
> `dist ≥ 6`** — derived: 41 library rows have `dist ≥ 6` ((BE-258)(iii)'s
> `23 + 18`) and 40 of them are distinct. The same genre as (BE-276)(ii), found the same way: **take the
> generator's own inputs rather than trusting that a printed denominator
> counts what its name says.** Every row-level figure of this direction is at
> the **distinct-side** resolution (400), every draw-level figure at the
> library-entry resolution (1 281 = 427 × 3); both are labelled.
>
> **(BE-298)(iv)** — **a summary phrase nearly imported without
> its owning definition, which is this corpus's documented pathology.** The
> first draft of (BE-293)(iii) read *"(BE-262)(i) reports the confinement
> tight at 234 of 257 rows, i.e. a fourteenth of the rows do not attain"* —
> using it as evidence about `ρ_i = δ_i`, the certificate's own hypothesis.
> **False.** Read at the owning clause (BE-257)(ii), *"tight"* means
> **`δ_i = m_i`** with `m_i = dim ⋂_P ⟨P⟩`, and the histogram is of `δ − m`;
> `ρ` does not appear in it. Caught by opening (BE-257) instead of quoting
> (BE-262)(i)'s one-line summary of it — **clause L1 of the direction core,
> and it fired on this direction's own draft.** The corrected statement is
> that the attainment rate the certificate needs had **never been counted**,
> which is why (BE-293)(iv) counts it.
>
> **(BE-298)(v)** — **a landed driver's variable is named for the
> wrong semicontinuity direction; no figure is affected and it is recorded so
> a successor does not misread it.** `bgoodempty.run_pix` and
> `bmblock.run_side` both carry `cmin_rho = min(cmin_rho, rho)` over the
> draws of a row. `ρ_i` is **lower** semicontinuous ((BE-255)(i) row 2), so
> its generic value is the **maximum** over draws; `cmin_rho` is a **lower
> bound** on the generic `ρ`, not the generic `ρ`. Read at source, it is used
> **only** in `if cmin_pix == 2 and cmin_rho < 6: big.append(...)` — an alarm
> list — where taking the minimum makes the alarm **more** likely to fire, so
> the usage is **conservative and both landed figures stand**. The
> load-bearing statement in each driver is the **per-draw** assert
> (`if cpix == 2: assert rho == 6`), which has no semicontinuity direction to
> get wrong. *Recorded because `cmin_pix` (correctly a minimum, `c` being
> upper) and `cmin_rho` sit on adjacent lines and read as the same idiom.*
>
> **(BE-298)(vi)** — **the answer this direction wanted was the
> other one, and it is reported against interest twice.** The first slice was
> the draw-free `pop` census, run precisely because a `min(δ₁, δ₂) = 0`
> profile on the corner would have closed **both** residues outright with no
> lemma and no draw. It came back `min(δ) ≥ 2` at **248 of 248** — the residue
> is live — and (BE-292)(i) says so in the clause that would have preferred
> the opposite. The F26 consumer check ((BE-291)) runs the same way: it makes
> this direction's own question **cheaper to skip**, and it is the first step
> of the section.
>
> **(BE-298)(vii)** — **THIS DIRECTION'S OWN HEADLINE WAS
> REVERSED IN ITS LAST HOUR, BY READING A SIBLING'S LANDING RATHER THAN ITS
> OWN DATA AGAIN.** The draft's title through six of its eight steps was
> *"the two residues are NOT one question"*, resting on (BE-294)(ii)'s
> refutation of general position at `Π_x` — which stands. **`HEAD` then moved
> to `0bd802e7`** (BSIXTEEN, 111), and its (BE-281)(iii) says *"a single
> lemma stated relative to `⟨P₀⟩` rather than to `Λ²K⁴` would discharge
> both"*. Tested at once rather than argued against: `c_i(U) = gpP(U)` at
> **1 281 of 1 281** draws, both blocks, asserted ((BE-294)(iv)). **So the
> "single lemma" claim is right and this direction's headline was wrong about
> the conclusion while being right about the statement it tested.** Recorded
> in full because the arc's own rule is that a direction's corrections are
> the most valuable line in its return, and because the reversal is the
> cross-return finding of the round: **two directions, dispatched on
> complementary regimes and told not to attempt each other's lemma, converged
> on ONE lemma that neither residue clause states** — BSIXTEEN from
> `dim ⟨P₀⟩ ≤ 5`, this direction from `dim ⟨P₀⟩ = 6`. **The diff against
> `HEAD` rather than the working tree is what surfaced it**; a direction that
> had diffed at dispatch time would have shipped the wrong headline.
>
> **(BE-298)(viii)** — **a mechanism this direction derived, checked
> and discarded, recorded so a successor does not re-walk it.** Before
> saturation, the candidate mechanism for `c_i(Π_x) ≥ 1` was **leafhood**: if
> `deg_i(x) = 1` with neighbour `z`, then `S_x = t·(p_x ∧ p_z)` with every
> other body fixed is a motion of side `i`, so `p_x ∧ p_z ∈ ρ̄_i ∩ Π_x`
> pointwise. **True, and OFF-REGION**: an internal R-node peel gates
> `deg_i(x) ≥ 2` on **both** sides (`bgoodempty.block_row`,
> `bmblock.run_reach`), and measured, the side-degree at `x` over the library
> is `{2: 261, 3: 306, 4: 336, 5: 378}` — **no degree-1 row exists**. The
> mechanism that *does* fire is saturation, which needs no leaf.

---

### Draft disposition — confidence, what would change it, and where it merges

**This file merges as a new section file `workbook/bare-ext/BPROPCL.md`**, in
the one-file-per-section shape the 2026-09-09 split fixed, sibling to
`BGOODEMPTY.md` and `BMBLOCK.md` under `§(K-bare-ext) — continuation`. Labels
**(BE-291)–(BE-298)**, ***Steps BE290–BE297***, driver
`notes/scripts/w4/bpropcl.py` (modes `pop`, `gp`, `validate`).
**Baseline `16881765`; `HEAD` advanced twice under this direction — to
`0bd802e7` (BSIXTEEN, 111) and `d073ddb4` (GODDRUNG, 112). Every figure was
taken against drivers that neither landing touched** (`git status` shows no
modification to `bgoodempty.py`, `bmblock.py`, `bproper.py`, `bunif.py` or
`bimage.py` at any point), **and the `0bd802e7` landing is read INTO the
argument rather than around it** ((BE-294)(iv), (BE-298)(vii)). Reservation
re-verified at `d073ddb4`: **0 hits on every label, step and code token**
outside this direction's own two files.

**Confidence, clause by clause.**

| clause | confidence | why |
|---|---|---|
| (BE-291) F26 consumer check | **high** | a ledger closure plus four verbatim quotations from the terminal clauses; mechanical |
| (BE-292) corner `(δ₁,δ₂)` profile | **high** for the figure, **capped** for its reach | draw-free, reproduces (BE-276)(i)'s `2 946`/`248` exactly as a same-input replay; says nothing about other populations |
| (BE-293)(i) the certificate | **high** — it is a proof | three landed semicontinuity rows plus (BE-22)(ii); the one place to attack it is whether row 4's *"on the locus where `ρ_i` is constant"* means what is used here |
| (BE-293)(iv) certificate census | **high** for the 375/375 and 15/15, **capped** for the denominator | each certifying row is a witness; the claim *"no non-certifying eligible row exists"* is NOT made |
| (BE-294)(i) hinge-line identity | **high** — read off two function bodies, and asserted at every draw | |
| (BE-294)(ii) saturation | **high** — it is a proof, and its conclusion is asserted at every saturated draw | |
| (BE-295)(i) the two residues diverge **in the stated frame** | **high** on the refutation, **capped** on the population | the refutation is (BE-294)(ii), a proof; the *"0 of 1 281 at `⟨M⟩`"* half is a cap |
| (BE-294)(iv) `gpP` unifies them | **high** that it holds on this population, **`[MEASURED]`** as a statement | an assert with 0 exceptions; it is not proved, and the residue is now *"prove `gpP`"* |
| (BE-295)(iii) `ρ_i ≤ 4` sharpening | **capped** | a statement about this job list only |

**WHAT WOULD CHANGE THIS.**

1. **A single residue-corner peel with `δ_i = 5` or `δ_i = 6` on one side**
   would restore the `ρ_i = 5` case (BE-295)(iii) reports absent, and with it
   the `Π_x` margin-`+1` route. The cheapest test is `bpropcl.py pop` on a
   **wider** job list — a third skeleton, or branch lengths past `5`.
2. **One draw with `c_i(Π_x) = 2` or `c_i(⟨M⟩) = 1` at `ρ_i ≤ 5`** refutes the
   properness reading outright and is a live `Good = ∅` route. **Not found at
   1 281 draws here, nor at the 427 rows of (BE-258)(iii)/(BE-273)(ii)**, and
   at the 375 eligible rows it is excluded by a **proof**, not a search
   ((BE-293)(iv)).
5. **An eligible peel at which NO `a_i = 0`, `ρ_i = δ_i ≤ 5` draw exists**
   would be the first row where the certificate is unavailable and the
   residue is genuinely open. `bpropcl.py gp` found none at 400 of 400 sides;
   the honest form of that figure is *"not found under cap C"*.
3. **A proof that `Chart(H) → Chart(side_i)` is NOT dominant** would sever
   every side-row figure in this lane, this direction's included, from the
   peels they are quoted about ((BE-296)(iv)).
4. **A counterexample to (BE-294)(ii)'s saturation step** — a configuration
   with `ρ_i = dim ⟨P₀⟩` and `c_i(Π_x) = 0` — would refute the divergence
   argument and restore *"one lemma"*. Asserted false at every saturated draw
   below; it is an assert, so it would have fired.
