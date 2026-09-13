## §(K-bare-ext) — continuation (direction BCOFLAG, ordinal 115, 2026-09-13)

**Question.** At the internal R-node peels where the flags coincide, is
`Good ≠ ∅` a CLASS theorem — and what is the right object there, given that
the four blocks do not decompose the screw space at all?

**Baseline.** `HEAD` = `2d31b36c` at dispatch and at draft time (re-checked;
it did not advance during the run). Driver: `notes/scripts/w4/bcoflag.py`
(new, untracked at draft time), seed `20260913`, exact ℚ throughout.
No `.lean` opened (the standing 2026-08-05 Lean hold).

---

### The verdict in one paragraph

The question is **not well posed as asked**, and the reason is sharper than
"`Good` degenerates". `Good ≠ ∅` is the right proxy for the consumer only
because (BE-69)(i)/(ii) make it *dense or empty* on an irreducible
`Chart(H)` — and at these peels **`Chart(H)` is not known irreducible at a
single witness**, because (CH-1)(a)'s hypotheses fail there (girth `3` at
**928 / 928** of BONEONE's family, recomputed here, not cited; `hcard` at
**8 / 392**). (BE-85)(iii), inside the very direction that produced the
certificates, already says this — *"taking (BE-69)(ii)'s dense-or-empty
dichotomy … with it"*. So the arm's class question is **not** "is the generic
configuration good"; it is a bare existential, one piece at a time.

Read as a bare existential it is **PROVED at 292 of the 392 by exhibition**
and **OPEN at the other 100** — where the exhibited draw has `a_i = 1`, lies
outside `Good`, and by (BE-69)(ii)'s consequence 2 settles nothing. That
refutes (BE-284)(ii)'s *"settled per-piece by the 392 certificates"* by a
count of 100, and voids its citation of (BE-69)(ii)'s consequence 1 at all
392.

And the right object is **not** a stable-subspace family of any size. At a
coincident-flag peel **both `ρ̄₁` and `ρ̄₂` are confined to `Λ²π`, a single
maximal totally singular 3-space** — a theorem here, not a measurement — so
the 14-inequality criterion collapses to **ONE** inequality, `ρ₁ + ρ₂ ≤ 3`,
which at rung 3 reads *at most one side may lose attainment*. That
inequality is where the whole arm now lives, and it carries a **kill
condition with a derivation** ((BE-311)(ii)).

---

### *Step BE308* — **(BE-309): the stable-subspace lattice at a coincident flag pair**

> **(BE-309)(i)** `[PROVED]` *(draw-free, exhaustive; the generic regime is
> the method's control and it reproduces the landed 16)* Let `ϕ` be a flag
> pair with `π_x = π_y = π` and `p_x ≠ p_y` (both automatic at a guarded
> draw: `draw_flat` asserts all points distinct, and the coincidence is
> (BE-81)'s forcing). Then the `S(ϕ)`-stable subspaces of the screw space
> `Λ²K⁴` number exactly **ELEVEN**, with dimension histogram
> `{0:1, 1:1, 2:2, 3:3, 4:2, 5:1, 6:1}`, and they are, named:
>
> | dim | subspace |
> |---|---|
> | 0 | `0` |
> | 1 | `⟨M⟩ = ⟨p_x ∧ p_y⟩` |
> | 2 | `Π_x = p_x ∧ π` · `Π_y = p_y ∧ π` |
> | 3 | `Λ²π` · `α_x = p_x ∧ K⁴` · `α_y = p_y ∧ K⁴` |
> | 4 | `Λ²π + ⟨p_x ∧ f⟩` · `Λ²π + ⟨p_y ∧ f⟩` |
> | 5 | `α_x + α_y = ⟨p_x, p_y⟩ ∧ K⁴` |
> | 6 | `Λ²K⁴` |
>
> *Why the enumeration is complete.* `S(ϕ)` contains the maximal torus of the
> frame `(p_x, p_y, e, f)` (with `π = ⟨p_x, p_y, e⟩`), which acts on `Λ²K⁴`
> with the six weights `t_i t_j` — **pairwise distinct**, so every `S(ϕ)`-stable
> subspace is a sum of weight lines and the `2⁶ = 64` subsets are an
> exhaustive candidate list. **Exhaustiveness is its own claim class and has
> its own driver** (`bcoflag.py blocks`, `0.1 s`, draw-free): the same
> algorithm run in the **generic** regime — frame `(p_x, e₁, e₂, p_y)`,
> `S(ϕ) = GL₁ × GL₂ × GL₁`, exactly `bunif.stab_elt`'s group — returns **16**,
> `asserted == 16`, which is (BE-96)(iv)'s family reproduced rather than
> assumed. The naming above is asserted as a **bijection** onto the
> enumeration (both directions), not as a sample.
>
> **The structural reading, and it is stronger than "a smaller family."**
> Exactly one stable subspace is 1-dimensional, so the socle is **simple**
> and `Λ²K⁴` is an **INDECOMPOSABLE** `S(ϕ)`-module at a coincident flag
> pair. In the generic regime the lattice is the Boolean lattice `2⁴` on four
> blocks; here it is an 11-element lattice with a unique atom. There is no
> direct-sum block decomposition at all — **coarse or fine**.

> **(BE-309)(ii)** `[REFUTED]` *(witness: `bcoflag.py blocks`, by name and
> draw-free)* The dispatch's proposed mechanism — *"the screw space decomposes
> under a **coarser** pairing whose totally-singular blocks are `Π_x = Π_y` and
> `Λ²π_x`, giving a family of **4**"* — is **false on both counts**, and the
> way it fails is the informative part.
>
> - `Π_x ≠ Π_y`: `Π_x = Π_y` would need `p_x = p_y`, which no guarded draw
>   permits. Measured: `dim(Π_x ∩ Π_y) = 1` and that intersection **is**
>   `⟨M⟩` (asserted as spaces).
> - The family is **11**, not 4.
> - The failure is not that the pairing is coarser. It is that the blocks
>   **overlap** (`Π_x ∩ Π_y = ⟨M⟩ ≠ 0`) and **miss half the screw space**:
>   `Π_x + Π_y + ⟨M⟩ = Λ²π`, of dimension **3**, asserted.
> - `⟨L⟩` does not exist at all: `π_x ∩ π_y` is `π` itself, 3-dimensional, so
>   `bimage.plane_meet` returns a 3-element basis and `bunif.flag_frame`
>   returns `None` at the `len(Lb) != 2` test — which is (BE-284)(ii)'s
>   sentence, verified against the code rather than the prose.
>
> **What survives of the mechanism** is only its direction — *"a different,
> smaller family"* — and even that is misleading, because the right object is
> not a family (see (BE-310)).

---

### *Step BE309* — **(BE-310): the confinement, and the criterion collapses to ONE inequality**

> **(BE-310)(i)** `[PROVED]` *(the load-bearing new fact; a proof with one
> combinatorial hypothesis, and the hypothesis is checked draw-free at
> 392/392)* At a forced coincident-flag peel of BONEONE's family, **both
> `ρ̄₁` and `ρ̄₂` lie in `Λ²π`** — the 3-dimensional space of lines lying
> inside the common pencil plane, which is a **maximal totally singular**
> subspace of the Klein quadric (a β-plane; the Klein form is asserted to
> vanish identically on it).
>
> *Proof.* (BE-30)(iv) (`[PROVED]`, owning section BIMAGE) gives
> `ρ̄_{uv}(H_i) ⊆ ⟨ℓ_e : e ∈ P⟩` for **every** `u–v` path `P` of side `i`,
> **pointwise at every configuration**. At a guarded configuration the hinge
> of an edge is the **join of its two concurrency points** ((BE-16)(iii),
> owning section BZAVOID). (BE-85)(i)/(ii) put the whole forced set `A` in
> one plane `π` (confinement controls `3 580 / 3 580`), and `π_u = π_v = π`
> is asserted as spaces at `392 / 392` ((BE-85)(ii)). So if some `u–v` path
> of side `i` has **all** its vertices in `A`, each of its hinges is a join of
> two points of `π`, hence lies in `Λ²π`; and therefore so does `ρ̄_i`. ∎
>
> **The hypothesis, checked exhaustively and draw-free** (`bcoflag.py conf`,
> `0.1 s` — the closure set `A` is combinatorial, so no draw is involved):
> over the **392** forced witnesses, a `u–v` path inside `A` exists on **BOTH**
> sides at **392 / 392**, on exactly one side at `0`, on neither at `0`. Edge-
> length histogram `{(2,2): 256, (2,3): 36, (3,2): 88, (3,3): 12}`.
>
> **Independently confirmed geometrically** (`bcoflag.py prof`, stride
> subsample of **60** of the 392, every 6th in generator order — chosen for
> cost, **not random and not exhaustive**): `ρ̄₁ ⊆ Λ²π` at **60 / 60**, and
> `c_i(Λ²π) = ρ_i` in every row of the profile table. The proof is the
> statement; the measurement is its signature.

> **(BE-310)(ii)** `[PROVED]` *(the right object, and it is ONE inequality at
> ONE stable subspace)* With (i)'s confinement, (BE-95)(i)'s cap at
> `U = Λ²π` reads `dim(ρ̄₁ + ρ̄₂) ≤ dim Λ²π = 3`, and (BE-86)(i)'s
> unconditional criterion needs that dimension to be
> `min(δ₁+δ₂, 6) + a₁ + a₂`. Hence at a coincident-flag peel with the
> confinement,
>
> **`H` attains ⟹ `min(δ₁+δ₂, 6) + a₁ + a₂ ≤ 3`.**
>
> At **rung 3** (`δ₁ = δ₂ = 1`, so `Σδ = 2`) that is exactly
>
> **`a₁ + a₂ ≤ 1` — AT MOST ONE SIDE MAY LOSE ATTAINMENT,**
>
> equivalently `ρ₁ + ρ₂ ≤ 3`, since `ρ_i = δ_i + a_i` is (BE-22)(ii) tight at
> `392 / 392` ((BE-86)(ii)). **So the 14-inequality criterion of (BE-96)(iv)
> is replaced here by ONE inequality at ONE stable subspace**, and the
> measured census is exactly its boundary: `(a₁, a₂) ∈ {(0,0), (0,1), (1,0)}`
> at `292 / 60 / 40`, and **never `(1,1)`**.
>
> **This is why "the four blocks are not the right object" understates the
> case.** It is not that the blocks are the wrong *family*; it is that at a
> coincident flag the whole relative-screw action collapses into a single
> maximal totally singular 3-space, and the instrument there is a dimension
> count inside that 3-space, not a block-by-block sweep.

### *Step BE310* — **(BE-311): the rung bound the one inequality yields**

> **(BE-311)(i)** `[PROVED]` *(the rung bound, free from (BE-310)(ii))* At a
> coincident-flag peel with the confinement, **`H` attains ⟹ `Σδ ≤ 3`.**
> *Derivation:* `min(Σδ,6) ≤ min(Σδ,6) + a₁ + a₂ = dim(ρ̄₁+ρ̄₂) ≤ 3`, and
> `min(Σδ,6) ≤ 3` gives `Σδ ≤ 3` for `Σδ ≤ 6`; for `Σδ > 6` the left side is
> `6 > 3`. ∎ Compare (BE-284)(iii), which reads `Σδ ≤ d_S + 5` from the
> *block* arithmetic and concludes `⟨M⟩`/`⟨L⟩` bind only at rung 3: this is a
> **different and much tighter** bound, and it comes from the confinement
> rather than from the block dimensions.

> **(BE-311)(ii)** `[OPEN]` *(THE KILL CONDITION, with its derivation — this
> is what the arm is now worth dispatching for)* **Exhibit a forced
> coincident-flag internal R-node peel with `Σδ ≥ 4` at which some `u–v` path
> of each side lies inside the forced set `A`.** At such a peel `H` **cannot**
> attain, by (BE-311)(i); the shortfall then holds at the exhibited
> configuration, and by (BE-69)(ii)'s route a shortfall at a coincident-flag
> peel reaches **(BE-14)**, exactly as the dispatch's negative arm says.
> Equivalently and equally decisive in the other direction: **prove that
> forcing at a peel with `Σδ ≥ 4` is impossible**, and rung 3 is the whole of
> the coincident-flag arm, closed by (BE-310)(ii).
>
> **NOT TESTED HERE, and the reason is a cap, not an opinion.** BONEONE's
> generator is `(1,1)` only — every one of its 928 members has `δ₁ = δ₂ = 1`
> by construction (`k4_rsides` / `free_sides` both filter `side_delta(...) ==
> 1`). So this direction's population **cannot** reach `Σδ ≥ 4` and the
> condition is **not found under cap `Σδ = 2`**, never "does not occur". A
> `(δ₁, δ₂)`-widened generator is the cheapest next instrument.

---

### *Step BE311* — **(BE-312): what the 392 certificates do and do not settle**

> **(BE-312)(i)** `[REFUTED]` *(witness: the census itself, re-derived;
> (BE-284)(ii) over-reads its own source by 100)* (BE-284)(ii) says the
> coincident-flag peels *"are settled **per-piece**, by (BE-86)(ii)'s 392
> exact-ℚ certificates with shortfall `0` at 392/392 — which by (BE-69)(ii)'s
> consequence 1 is a **theorem per piece**"*. **Two defects.**
>
> — DEFECT (a), **the count is 292, not 392.** `Good = A₁ ∩ A₂ ∩ GP` with
> `A_i = {rank R_i ≥ 6|V_i| − 6 − f_i} = {a_i = 0}` — (BE-69)(i)'s own
> definition, read at BPEEL rather than off a summary. At **100** of the 392
> the exhibited draw has `a_i = 1` ((BE-86)(ii)'s rows `(0,1,1,2,3) → 60` and
> `(1,0,2,1,3) → 40`), so that draw is **outside `Good`**, and by (BE-69)(ii)'s
> **consequence 2** — *"a draw outside `Good` settles nothing"* — it settles
> nothing about `Good ≠ ∅` at those pieces. The certificates settle a
> **different** statement at 392/392, namely `dim M(H) = 6 + def₃(H)`, i.e.
> (BE-14) **at `H`**; that is (BE-86)(i)'s unconditional criterion and is
> insensitive to `a_i`. `H` attaining is not `Good ≠ ∅`.
>
> — DEFECT (b), **the citation of consequence 1 is void at ALL 392.** Consequence 1
> ("one exact-ℚ draw in `Good` settles the piece", i.e. upgrades a point to
> the generic point) runs through the dense-or-empty dichotomy, which runs
> through `Chart(H)` **irreducible**, which is (CH-1)(a) under `hcard`,
> min degree `2` and **girth ≥ 4**. **Recomputed here rather than cited**
> (`bcoflag.py`-adjacent probe, `bdecor.girth` and the canonical
> `bdecor.hcard_ok_piece`, exhaustive over the whole generator):
>
> | clause | over all 928 members | over the 392 forced |
> |---|---|---|
> | girth `≥ 4` | **0 / 928** | **0 / 392** |
> | `hcard` | 104 / 928 | **8 / 392** |
> | min degree `≥ 2` | 928 / 928 | 392 / 392 |
> | **all three** | **0 / 928** | **0 / 392** |
>
> (BE-85)(iii) records the forced column and draws the right conclusion —
> *"(CH-1)(a) is unavailable at every member of the family, taking (BE-69)(ii)'s
> dense-or-empty dichotomy and (BE-72)(iii) with it"*. **This is the tell's
> "answer under another name": it was already in the corpus, in the very step
> (BE-284)(ii) cites for the certificates, and (BE-284)(ii) cites past it.**
>
> **What survives, and it is enough for the positive half.** (BE-67)(iii) is
> an **existential** — *"some point of `Chart(H)` makes both peel sides attain
> and puts `ρ̄₁, ρ̄₂` in general position"* (the target as stated in
> `fanout.md`'s BPEEL entry) — so an **exhibited** point of `Good` proves it
> outright, with no irreducibility anywhere. At the **292** rows the draw has
> `a₁ = a₂ = 0` and `dim(ρ̄₁+ρ̄₂) = 2 = min(Σδ,6)`, so it **is** a point of
> `Good`: `Good ≠ ∅` is a per-piece **theorem** there, by exhibition and not
> by the dichotomy. The corpus's own framing under-sells these 292 by
> routing them through a consequence it does not have.

> **(BE-312)(ii)** `[MEASURED]` *(measured, the fence removed by a factor of
> 75; `bcoflag.py losers`, 171.3 s, seed 20260913, exact ℚ)* **The blind axis
> and what removing it does.** `blindaxes.py --imports notes/scripts/w4/
> bgenuine.py` puts `run_bite(nwit=4)` on the DEFAULTS list, and inside that
> loop the redraw count is a **hardcoded `range(4)`**, not a parameter — so
> (BE-86)(iii)'s F27 rider rests on **4 rows × 4 draws = 16 draws**, sitting
> exactly on the one FAILURE claim of that step. Un-fenced here by
> parameterizing **this** driver's loop around the imported `draw_flat` /
> `measure` (no landed driver edited):
>
> **EVERY** losing row (100 of 392, reproduced from a first pass, not cited),
> `6` independent draws each, at **two** coordinate-box sizes `s ∈ {20, 60}`
> — **1 200 draws**:
>
> | box | `(a₁, a₂, dim(ρ̄₁+ρ̄₂))` → count | rows with a `Good` point |
> |---|---|---|
> | `|coord| ≤ 20` | `{(0,1,3): 360, (1,0,3): 240}` | **0 / 100** |
> | `|coord| ≤ 60` | `{(0,1,3): 360, (1,0,3): 240}` | **0 / 100** |
>
> The value is **constant per row** across all twelve draws and both boxes.
> **NOT FOUND UNDER CAP: 1 200 draws.** And note the asymmetry, which is the
> whole of F27 here: a draw with `a_i = 0` would have been a **proof**
> (`dim M_i` is upper semicontinuous, so a draw is an upper bound on the
> generic `a_i` — `bgoodempty.py`'s U-1 mechanism, read at its own docstring),
> whereas a miss proves nothing. And `Good = ∅` **cannot be certified by
> draws at all here**, because the certificate for that direction is the
> dense-or-empty dichotomy, which (i)(b) has just removed. So these 100
> pieces are **OPEN**, and open in a way this population cannot close.

> **(BE-312)(iii)** `[REFUTED]` *(witness: `bcoflag.py side`, 46.5 s;
> (BE-69)(iii)'s discharge of `A_i ≠ ∅` does not hold at a forced peel)*
> (BE-69)(iii) discharges the first conjunct of its own criterion with
> *"`A_i ≠ ∅` is **(BE-14) for the side** — the 2-cut induction's own
> hypothesis, not a new obligation"*. **That is a non-sequitur at a forced
> peel, and the corpus has the witness.**
>
> *The argument.* `A_i` is a subset of `Chart(H)`, the **composite's** chart
> ((BE-69)(i): *"Fix a piece `H` … `Good(H;x,y)` is Zariski-open in
> `Chart(H)`"*). (BE-14) for the side is a statement about `Chart(H_i)`. At a
> forced peel the restriction `Chart(H) → Chart(H_i)` lands inside the
> coincidence locus `{π_u = π_v}`, which is **proper and closed** in
> `Chart(H_i)` — the side alone does not force it, which is exactly
> (BE-282)(iv)'s sentence (*"`π_x` and `π_y` are drawn independently and
> nothing can force them equal"*, `bunif.flag_frame` rejecting `0 of 854`
> one-sided rows). The preimage of a dense open under a non-dominant map can
> be empty, so the discharge does not follow.
>
> *The witness.* At a stride subsample of **40** of the 100 losing sides
> (every 2nd, chosen for cost — not random, not exhaustive), `4` draws each of
> the **side's own chart** via `bdecor.sample_by_branches` ((BE-64)'s
> parametrization), `160` draws:
>
> | | |
> |---|---|
> | `a_i = 0` over every usable own-chart draw | **160 / 160** |
> | draws at which the side alone determines both flags | 40 |
> | of those, `π_u ≠ π_v` | **40 / 40** |
> | of those, `a_i = 0` | **40 / 40** |
> | draws at which the side alone leaves `π_u` or `π_v` undetermined | 120 |
> | sides with `a_i = 0` found on their own chart | **40 / 40** |
>
> Each hit is a **theorem** (upper semicontinuity again). So every one of
> these 40 sides **attains on its own chart**, at configurations where
> `π_u ≠ π_v`, while having `a_i = 1` at **every one of the 1 200 composite
> draws** of (ii). The two statements are about two different charts and the
> implication between them fails exactly here.
>
> **A third fact worth recording, and it is not a defect.** At `120` of the
> `160` draws the side alone does not determine `π_u` or `π_v` at all — the
> terminal is not a hub of that side, so its closed star spans less than a
> plane. **The flag at a terminal is a property of the composite**, which is
> why (BE-282)(iv)'s *"the forced coincidence is a property of the composite
> two-sided peel"* is literally true and not merely a sampling remark.

---

### *Step BE312* — **(BE-313): F26, the consumer, run before anything was built**

> **(BE-313)(i)** `[OPEN]` *(what the consumer actually takes, and the answer
> is not what the dispatch assumed)* The chain (BE-284)(i) names was opened at
> each owning section: (BE-69)(ii) (*"(BE-67)(iii) at `H` is exactly
> `Good ≠ ∅`"*) → (BE-67)(iii) → the general-position half of (BE-22)(iii)(b)
> → the **S-mark** induction of (BE-25)(ii) → check **(a)**.
>
> **Check (a) is not the problem.** (BE-25)(ii)'s check (a) for S-mark is
> *"**yes** — at the root, `H = G` and there is no marked pair"*, i.e. the
> top-level consumable is **(BE-14) at `G`**, an existential (`G` attains at
> *some* configuration), and (BE-86)(ii)'s 392 certificates deliver exactly
> that shape of statement at `392 / 392`.
>
> **The 2-cut STEP is the problem, and it is where these peels land.**
> S-mark's inductive hypothesis at a child node `C` with parent pair `{u,v}`
> is, verbatim: *"the union `H_B` of `B`'s subtree … has an irreducible
> component of `Y°(H_B)`, **with the flags at `u,v` prescribed**, at whose
> generic point `H_B` attains and `H_B/uv` attains"*. At a forced
> coincident-flag peel the parent has **no choice** of prescription — `π_u =
> π_v` holds in every legal configuration of the composite — and (BE-312)(ii)
> measures the child failing to attain at that prescription at **1 200 / 1 200**
> draws. So **S-mark's hypothesis is asked for at exactly the prescription
> where its conclusion is not available**, and the induction as stated does
> not close at these peels. It is not routed elsewhere: (BE-22)(vi)'s escape
> (*"if one side is rigid the general-position half disappears"*) needs
> `δ₂ = 0`, and (BE-81)'s forcing is stated **with both sides flexible**
> (`δ₁ = δ₂ = 1`); (BE-20)'s 3-connected rigidity puts the R-node itself out
> of scope but not the subtree union `H_B`.
>
> **What the repair looks like, named so it is a deliverable and not a
> phrase.** S-mark's attainment clause must be replaced by its
> `a`-carrying form — *"`a_{H_B} = 0` **or** the composite's
> `min(Σδ,6) + a₁ + a₂` identity is met"* — i.e. the induction must carry
> (BE-86)(i) rather than (BE-22)(iii). That is a **motive-level change** of
> the same kind (BE-25)(v) already priced for the rooted tree, and it is a
> deliverable (a restated inductive statement with its three checks re-run),
> **not** coordinator wiring.

> **(BE-313)(ii)** `[OPEN]` *(the class question, restated so it can be
> attacked)* With `Good ≠ ∅` demoted and the confinement in hand, the
> coincident-flag arm has exactly **two** live questions, both bounded:
>
> 1. **Can both sides lose attainment at a coincident-flag rung-3 peel?**
>    Measured `(a₁, a₂) ≠ (1,1)` at `392 / 392` plus `1 200` redraws; by
>    (BE-310)(ii) a `(1,1)` row is a **shortfall**, and by (BE-69)(ii) it
>    reaches (BE-14). A proof that `a₁ a₂ = 0` closes the arm at rung 3
>    class-wide.
> 2. **(BE-311)(ii)**, the `Σδ ≥ 4` kill condition.
>
> Neither is answered by closing sixteen blocks, eleven blocks, or any
> number of blocks: both are statements about one 3-dimensional totally
> singular subspace.

---

### Verification

| claim | driver / source | figure |
|---|---|---|
| (BE-309)(i) 11 stable subspaces; generic control 16 | `python3 notes/scripts/w4/bcoflag.py blocks` | 0.1 s, draw-free, exhaustive over 64 candidates, `assert len == 16` on the control, naming asserted bijective |
| (BE-309)(ii) mechanism refuted | same | `Π_x ≠ Π_y` asserted; `dim(Π_x+Π_y+⟨M⟩) = 3` asserted |
| (BE-310)(i) confinement hypothesis | `python3 notes/scripts/w4/bcoflag.py conf` | 0.1 s, draw-free, **392 / 392** both sides |
| (BE-310)(i) geometric signature | `python3 notes/scripts/w4/bcoflag.py prof` | 5.3 s, stride 60 of 392, `ρ̄₁ ⊆ Λ²π` at 60/60 |
| (BE-312)(ii) un-fenced redraw | `python3 notes/scripts/w4/bcoflag.py losers` | 171.3 s, 1 200 draws, 2 box sizes, **0 / 100** |
| (BE-312)(iii) side attains on its own chart | `python3 notes/scripts/w4/bcoflag.py side` | 46.5 s, 160 draws, `a_i = 0` at 160/160 |
| (BE-312)(i)(b) (CH-1) census | `bdecor.girth` + `bdecor.hcard_ok_piece` over `bgenuine.family()` | girth `3` at 928/928; `hcard` 104/928, 8/392 — **recorded as measured, probe not retained as a mode** |

**Caps and blind axes, disclosed.**

- `bcoflag.py` runs at seed `20260913`; `run_losers(ndraw=6, boxes=(20,60))`,
  `run_prof(cap=60)`, `run_side(cap=40, ndraw=4)` are this driver's own
  fences and are named in its signatures, not buried.
- Every population here is **BONEONE's generator**: rows `(9,4)`, `(9,5)`,
  `(10,4)`, `δ₁ = δ₂ = 1` by construction, `n ≤ 12`. Nothing here reaches
  `Σδ ≥ 3`, the `(10,5)` row of (BE-85)(iv), or any non-`K₄`-skeleton R-node
  side. `WIT11_LENGTHS = (1,1,1,6,1)` and the **unread** `W9_ALT = (1,1,4,3,1)`
  of `w4/boneone.py` are not consumed by any mode here.
- `bgenuine.draw_flat(s=20, tries=120)` is the sampler under everything; the
  `s` axis was opened here (20 vs 60, no movement) and `tries` was not.
- (BE-310)(i)'s proof cites (BE-30)(iv) and (BE-16)(iii) as `[PROVED]` at
  their owning sections; it does **not** re-verify their proofs.
- The `(CH-1)` census probe was run inline and **not retained as a driver
  mode** — recorded here explicitly per the harness rule.

**What would change this.** (a) A forced coincident-flag peel with `Σδ ≥ 4`
and the confinement — (BE-311)(i) then refutes (BE-14). (b) A `(1,1)` row
at rung 3 — same consequence by (BE-310)(ii). (c) A draw with `a₁ = a₂ = 0`
at any of the 100 open rows — moves that piece to PROVED. (d) A forced
coincident-flag peel satisfying all three (CH-1) clauses — restores the
dichotomy and puts `Good ≠ ∅` back as the right question there;
(BE-85)(iv)'s `0 of 648` is the only non-degenerate control that exists, and
it is a none-found, not a theorem.

**Merges into** a new section file `notes/pencil/workbook/bare-ext/BCOFLAG.md`
(one file per section is the workbook's shape).
