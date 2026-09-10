## §(K-bare-ext) — continuation (direction BFOUR): **§(K-bare-ext) (E4) IS FALSE** — an exact-ℚ peel has `c_i(Π_x) = 2` with `e₁ + e₂ = 3`, in the **attaining** case and through every gate; the hunt (BE-154)(iv) named **could not have found it**, because every (E4) falsifier is a *clause* counterexample (535/535) and that population holds side 2 at a **single point** of its own parameter space; and the refutation is **confined to (BE-22)(vi)'s rigid-side collapse**, so the repair **(BE-E4′)** keeps 14 → 12 on the both-flexible zone at a **measured** price of 158 escapes, every one of them discharged by a proved theorem — **UNPROVED, and TIGHT at `δ₂ = 1`** (*Steps BE155–BE161*)

**It opens at exactly the tail BARCH declared** (*"The next tail is (BE-156) /
Step BE155"*), and **not** at (BE-157). Its step numbers therefore sit *below*
the BSERIES continuation above it: this file is ordered by **landing**, not by
step index, and BSERIES consumed *Steps BE163–BE170* in the commit before this
one.

**(BE-154)(iii) named the falsifier's shape correctly and the place to look for
it wrongly.** It asked for a peel with `c_i(Π_x) = 2` and `e₁ + e₂ ≤ 3`, noted
that this needs `ρ_i ≤ 5` and, at BSATUR's own `ρ_i = 5` witness, `ρ̄_j ⊆ Π_x`
with `ρ_j ≤ 2` — and it sent the hunt to `bdegtwo.sweep_points`. **The witness
exists and has exactly those numbers.** `K4(5,2,2,2,2,2)` peeled at `('A','B')`
with side 1 the 5-branch, reflagged onto (BE-105)'s bad plane, gives
`(δ₁,δ₂ | a₁,a₂ | ρ₁,ρ₂ | c₁,c₂)(Π_x) = (5,0 | 0,0 | 5,0 | 2,0)`, hence
`e = (3,0)` and **`e₁ + e₂ = 3 < 4`** — with `verify_pencil_witness` TRUE,
girth 6, `hcard` TRUE, `rnode_shaped(side₂)` TRUE, `x`/`y` hubs, `y ∉ N(x)`,
`deg₁(x) = 1`, the F13 negative control clean, `a₁ = a₂ = 0` (the **attaining**
case), and all three margins `≤ 0` so it is **not** a shortfall. **The
population (BE-154)(iv) named could not have produced it**, and that is a
theorem plus a measurement rather than bad luck: `c_i(Π_x) = 2` *is*
`Π_x ⊆ ρ̄_i`, so `e_i = ρ_i − 2` and `e₁ + e₂ ≤ 3` forces `ρ_i ≤ 5` — **every
(E4) falsifier is a (PENCIL-SATURATES-CHART) counterexample, 535 of 535** — and
at all **411** composite chart points side 2's signature is the single value
`(δ₂, a₂, ρ₂, c₂(Π_x)) = (3, 0, 3, 0)`, so `e₂ ≡ 3`, the two-sided clause
degenerates to a one-sided one, and only **3 of the 535** falsifying tuples are
reachable — each demanding `ρ̄₁ = Π_x` at `ρ₁ = 2`, strictly inside what
(BE-140) swept at **0/772**. The refutation sits **one hardcoded generator
parameter along** (side-2 branch length `3 → 2`); of `sweep_points`' three
side-2 axes the two that are *parameters* are inert and the one that is
*hardcoded* is the whole question. **The damage is contained**: every falsifier
has `δ₂ = 0`, which is (BE-22)(vi)'s **proven** collapse — one rigid side
reduces the 2-cut criterion to `ρ₁ = δ₁` with *no general-position content*, so
the 14 inequalities (E4) exists to thin are vacuous exactly there. **The repair
(BE-E4′)** — (E4) restricted to `δ₁, δ₂ ≥ 1` — leaves **158** escapes of 6 400
and **all 158** sit at `min(δ₁,δ₂) = 0`, i.e. every one is carried by
(BE-22)(vi) instead of by a clause, so **14 → 12 survives on the both-flexible
zone**; but it is **UNPROVED** and **TIGHT** at `δ₂ = 1`. **And the loss is
now shared by both halves of S-mark**: BSERIES's one-end reduction of (b2) to
(b1) is itself **conditional on (PENCIL-SATURATES) at side-degree `≥ 2`**
((BE-168)/(BE-170)), which is the very item (E4) was the successor to.
**Nothing landed is refuted** beyond (E4) itself: (BE-149)–(BE-152) are
reproduced or extended, (BE-153)(i)/(ii)/(iv)'s arithmetic all stands, and
(BE-153)(iii) is **upgraded from asserted-at-its-own-numbers to MEASURED**.

### Standing notation (on top of *Steps BE148–BE154*)

BARCH's, verbatim — `V := Λ²K⁴`, `M°`, `s`, `r`, `Γ`, `Γ_Π(p)`, `R`, `R₀`,
`e_i := ρ_i − c_i(Π_x)`, and the *BAD* / *relaxed bad* / *graph-bad* reading
convention. Three additions:

> **`(BE-E4′)`** is (E4) **restricted to `δ₁, δ₂ ≥ 1`** — the both-flexible
> zone, i.e. off (BE-22)(vi)'s collapse; it is (BE-29)(i)'s *"genuinely open
> zone"*. The `BE-` prefix is clause (L1)'s remedy for a `(X<digit>)`-shaped
> token, and the prime follows the `(GR-4′)` convention; the collision on the
> **un-prefixed** `(E4)` is recorded in `notes/Pencil-labels.md`'s collision
> table, and every citation of it here is (L3)-qualified.
>
> **The `pr` axis.** `bdegtwo.peel_of` and `bdegtwo.sweep_points` both
> **hardcode** `pr = [3] * len(SKELETONS[skname])` for side 2's branch
> profile. `bproper.composite`/`free_peel` and `bsatur.peel_of` all take that
> profile as a **parameter**; the sweep does not. *"The `pr` axis"* always
> means this one number vector.
>
> **The `δ₂` ladder.** `bsatur.peel_of(sk, [5, m, …, m], 0)` for `m = 2, 3` and
> the mixed profiles between, at `sk ∈ {K4, prism, K33}`. Side 1 is always the
> peeled 5-branch, so `δ₁ = 5` and `deg₁(x) = 1`; the ladder moves `δ₂` alone.

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read and **no `.lean` was opened** (the standing 2026-08-05
hold). `bdegtwo.sweep_points`' **docstring is stale** — it advertises nine
yield fields where the body yields fourteen — and the consumption below is
written against the **body**, per CLAUDE.md's *docstrings are not evidence*
rule; the defect is recorded as a *Recorded observation* in
`notes/scripts/README.md` rather than fixed, since editing a landed driver's
comment would cost the figure-invariance gate its one-line discharge.
(BE-22)(vi) was re-read at its **proof site**, not its summary: the collapse is
derived from (BE-22)(ii)'s `δ₂ = 0 ⇒ ρ₂ = 0` together with
`min(δ₁+δ₂, 6) = δ₁`, and its own text says the criterion then has *"no
general-position content whatsoever"*.

### Step BE155 — (BE-156): the CONTAINMENT THEOREM — the hunt is a STRICT SUB-HUNT of one already run

> **(BE-156)(i)** *(**PROVED**; one line, and it re-prices (BE-154)(iii))*
> `dim Π_x = 2` (`assert_generic_star` at `x`), so the hypothesis
> `c_i(Π_x) = 2` is exactly `Π_x ⊆ ρ̄_i`, and there `e_i = ρ_i − 2`. Since
> `e_j ≥ 0` always (`c_j ≤ ρ_j`),
>
> > **`c_i(Π_x) = 2` and `e₁ + e₂ ≤ 3` ⟹ `ρ_i ≤ 5`** — i.e. **every (E4)
> > falsifier is a (PENCIL-SATURATES-CHART) counterexample.** ∎
>
> Asserted by exhaustion over `barch.all_tuples()`: of the **535**
> (E4)-violating tuples, **535** are clause-violating. `bfour.py --arith`.
>
> **Why this earns a label rather than a remark.** (BE-154)(iii) prices the
> falsification as *"the cheapest decisive next move"* — right about
> *decisiveness*, wrong about cost per unit of evidence: the falsifier space is
> **contained** in the clause-violation space, which (BE-135)/(BE-140) swept at
> **0/772**, (BE-128) at 54 rows and (BE-108) at 93. A hunt cannot be cheaper
> than a hunt it is a sub-hunt of. The reusable form: **price the population
> against the claim's own quantifiers before spending the compute.**

> **(BE-156)(ii)** *(**MEASURED by exhaustion**; 72% of the falsifier space
> would be a larger event than an (E4) refutation)* Over the same 535, the
> margin `c₁(Π_x) + c₂(Π_x) − 2 − slack` histograms as
> `{0: 150, 1: 234, 2: 151}`. So **385 of 535** have `margin > 0` and would
> exhibit **item 0(b) [MARGIN]** — *the arc's first shortfall*, unexhibited at
> 54 rows ((BE-128)(i)) with none new at BLINE or BDEGTWO
> ((BE-135)(i)/(BE-140)(iv)) — leaving **150** clean falsifiers. **50** of the
> 535 are attaining (`a₁ = a₂ = 0`), the case S-mark's pin carries.

> **(BE-156)(iii)** *(**PROVED by exhaustion**; what the named population can
> reach, computed *before* it is run)* Given (BE-157)(ii)'s measurement that
> side 2's signature is the constant `(3, 0, 3, 0)`, exactly **3** of the 535
> falsifying tuples carry it — `(δ₁,δ₂ | a₁,a₂ | ρ₁,ρ₂ | c₁,c₂)` equal to
> `(0,3 | 2,0 | 2,3 | 2,0)`, `(1,3 | 1,0 | 2,3 | 2,0)` and
> `(2,3 | 0,0 | 2,3 | 2,0)`, each with `e = (0,3)`. **All three force
> `ρ₁ = c₁(Π_x) = 2`, i.e. `ρ̄₁ = Π_x` exactly** — asserted. That is a clause
> violation at `ρ₁ = 2`, *strictly* inside the condition
> `Π_x ⊆ ρ̄₁ ∧ ρ₁ ≤ 5` the same sweep returned **0/772** on. So on its own
> population the commissioned hunt is the **hardest 3 tuples** of the clause
> hunt.

> **(BE-156)(iv)** *(the divergence guard)* BARCH's four arithmetic figures are
> **reproduced** in the same mode, each an `assert`: 970 separating tuples
> ((BE-153)(ii)), `escapes((E4)) = 0` ((BE-153)(i)),
> `escapes((PENCIL-SATURATES)) = 0` ((BE-101)(i)), `escapes(pair-patch) = 287`
> ((BE-153)(iv)).

### Step BE156 — (BE-157): the COMMISSIONED SWEEP — both sides at 411 chart points, and side 2 never moves

> **(BE-157)(i)** *(**MEASURED**; (BE-154)(iv) run as specified)*
> `bdegtwo.sweep_points` over `bdegtwo.all_jobs()` at `nseed = 2`,
> `ntarget = 6`, in two halves (`--charta` 204 points / 34 peels, `--chartb`
> 207 / 36): **411 composite chart points over 70 peels**, reproducing
> (BE-136)'s own `411/411`, with all **four** fibre shapes — `𝔸³` 36, plane
> `π_{c₁}` 18, plane `π_x` (`k ≥ 3`) 10, the line `π_{c₁} ∩ π_{c₂}` 6, by peel.
> At each point **both** sides are measured; `barch.run_cert` measures one side
> of a bare side configuration and `bdegtwo.run_direct` side 1 of the
> composite, so neither had ever measured side 2. The per-side arithmetic is
> composed from `bimage.rho_bar_of` + `bdecor.d3`/`weld_d3` rather than from
> `bsatur.row_of`'s 16-block `profile` (seconds a row), and is
> **cross-asserted against `row_of` itself** — `ρ`, `δ`, `a`, `c(Π_x)`,
> `c(Π_y)`, `slack` — at the first point of **every** peel, **70/70**, together
> with the three margin controls at `Π_x`, `Π_y`, `⟨M⟩`, all `≤ 0`.

> **(BE-157)(ii)** *(**MEASURED**; the finding, and it is about the population
> rather than the clause)*
>
> > **Side 2's signature is the single value
> > `(δ₂, a₂, ρ₂, c₂(Π_x)) = (3, 0, 3, 0)` at 411 of 411 points** — asserted.
>
> Hence `e₂ = 3` **identically**, and on this population the two-sided (E4)
> degenerates to the **one-sided** `c₁(Π_x) = 2 ⟹ ρ₁ ≥ 3`. A falsifier
> therefore needs `e₁ = 0`, i.e. `ρ̄₁ = Π_x` at `ρ₁ = 2` — (BE-156)(iii)'s three
> tuples. Censuses: `(e₁, e₂)`
> `{(0,3): 96, (1,3): 69, (2,3): 36, (3,3): 69, (4,3): 141}`; `(c₁, c₂)` at
> `Π_x` `{(0,0): 306, (1,0): 69, (2,0): 36}`; at `Π_y`
> `{(0,0): 96, (1,0): 279, (2,0): 36}`.

> **(BE-157)(iii)** *(**MEASURED**; the hunt itself, cap disclosed)* (E4)'s
> **hypothesis** is met at **72** block-instances (36 at `Π_x`, 36 at `Π_y`),
> so the sweep is **not** vacuous — asserted. **(E4) is falsified at 0 of
> them.** Stated as `RESEARCH-ARC.md` §5 requires: **not found under this
> cap**, never *"cannot happen"* — and here the cap is the whole content,
> because (BE-157)(ii) shows the population is a **single point** in the
> side-2 factor of a clause quantified over the **pair**. So **(BE-154)(iv)'s
> population cannot decide (E4)**, which is a statement about the *spec*, not
> about the clause. `bfour.py --charta --chartb`.

### Step BE157 — (BE-158): what each population reaches — and `Γ_Π` is an (E4) PROVER, not a falsifier

> **(BE-158)(i)** *(**PROVED**, then **MEASURED** at 411/411; a bound at every
> `k`)* At `k ≥ 3` the true motion space satisfies `N_full ⊆ r^{-1}(Π_x)` for
> the first two side-neighbours, because the `j ≥ 3` constraints only cut
> further. Hence `ρ̄₁ ∩ Π_x ⊆ φ_p(Γ_Π(p))` and
>
> > **`c₁(Π_x) ≤ dim Γ_Π(p)`, at every side-degree `k ≥ 2`.**
>
> Asserted at **411/411**. **Consequence, and it inverts (BE-151)'s reading:**
> `dim Γ_Π(p) ≤ 1` forces `c₁(Π_x) ≤ 1`, so **wherever the graph certificate
> fires it PROVES (E4) at that point** — (E4)'s hypothesis cannot hold at side
> 1 there. It fires at **375 of 411**; the `dim Γ_Π` census
> `{0: 306, 1: 69, 2: 36}` **coincides** with the `c₁(Π_x)` census, so the
> bound is attained at every point of this population.

> **(BE-158)(ii)** *(**MEASURED**; (BE-149)(i) extended to the population it
> had not reached)* At the **351** `k = 2` chart points the identity
> `ρ̄₁(p) ∩ Π_x(p) = φ_p(Γ_Π(p))` is asserted as an identity of **subspaces**,
> **351/351**. (BE-149)(i)'s 99 rows were **bare side configurations**; these
> are **composite chart points** on an irreducible `Chart(H)`, core byte-fixed
> and side 2 re-drawn by (CH-2)'s tower. `Γ` is `p_x`-free by construction, so
> this extends the identity's domain rather than re-running it. **Scope,
> disclosed:** the `Γ` of (BE-149) is built from `(c₁, c₂)` alone, so at
> `k ≥ 3` it is the *relaxed* object and (i)'s inequality — not (ii)'s
> identity — is what holds; the exact identity is asserted only at `k = 2`.

> **(BE-158)(iii)** *(the reach comparison, as three sets)*
> - **What the chart population reaches and (BE-151)'s 54 relaxation-blind
>   fibres do not:** composite chart points on an irreducible `Chart(H)` with
>   **(CH-1)** asserted on the whole graph; all **four** fibre shapes including
>   the `k ≥ 3` one where `π_x` is *constant* along the fibre; **both** sides;
>   and the `Π_y` and `⟨M⟩` blocks alongside `Π_x`. (BE-151)'s population is
>   bare side configurations, one side, `k = 2` only.
> - **What (BE-151)'s fibres reach and the chart population does not:** the
>   `dim A ∈ {5, 6}` stratum where the relaxation is vacuous (21 of its 39
>   firings at `dim A = 6`), and per-*fibre* statements — 783 swept points over
>   99 configurations, a denser sweep of one side's fibre than 6 targets per
>   peel gives.
> - **What NEITHER reaches, and it is the same blind spot:** any peel whose
>   side 2 differs from the all-3-profile subdivided skeleton. Both hold
>   `pr = [3]*n`. That is (BE-159), and it is where the refutation lives.

### Step BE158 — (BE-159): the GENERATOR AUDIT — three side-2 axes, two inert parameters and one hardcoded number

> **(BE-159)(i)** *(**MEASURED**; the two exposed axes are inert)*
> `sweep_points(job, nseed, ntarget, skname, xy)` exposes `skname` and `xy`,
> and every landed consumer takes the defaults `'K33'`, `('A','B')`. Swept over
> all three skeletons and **every** hub pair yielding a legal peel — 12
> realized combinations, at `K33` and `prism` (**disclosed**: `K4` realizes
> *none* for this side-1 job, `peel_of` returning `None` because the `k ≥ 2`
> side does not glue at two non-adjacent hubs there, so the axis is exercised
> at two skeletons rather than three) — side 2's signature is the **single**
> value `(3, 0, 3, 0)`, asserted. **Moving these two axes changes nothing.**

> **(BE-159)(ii)** *(**MEASURED**; the hardcoded axis is the whole question)*
> `pr = [3] * len(SKELETONS[skname])` is hardcoded in **both** `peel_of` and
> `sweep_points`. Reached through `bproper.free_peel(skname, prof, xy, side1,
> rng)` — the same canonical generator `sweep_points` itself calls, with `prof`
> moved, and **disclosed** as drawing the sampler's own `p_x` rather than
> sweeping the fibre: `pr = [1]*9` and `[2]*9` give
> `(δ₂, a₂, ρ₂, c₂) = (0,0,0,0)` hence **`e₂ = 0`**; `[3]*9` gives
> `(3,0,3,0)`, `e₂ = 3`; `[4]*9`–`[6]*9` give `(6,0,6,2)`, `e₂ = 4`. **`e₂`
> takes three distinct values on this axis alone, including `0`** — and
> `e₂ = 0` is precisely what (BE-154)(iii)'s falsifier criterion needs.
> `bfour.py --gen`.

> **(BE-159)(iii)** *(the audit's point, and it is `RESEARCH-ARC.md` §4's own)*
> `bdegtwo.run_direct` **asserts** the clause unviolated at 0/772;
> `barch.run_cert` **asserts** both certificates sound at 663 firings. Both are
> true statements about every draw those runs made; both hold side 2 at a
> single point of its parameter space; and (E4) is quantified over the **pair**.
> The refutation sits **one step along the axis nobody moved** — `pr` from 3 to
> 2 — which is the **RPOOL sharpening**'s signature shape, recorded here a
> **second** time in this section.

### Step BE159 — (BE-160): **(E4) IS FALSE** — the witness, and every gate it passes

> **(BE-160)(i)** *(**MEASURED**, upgrading (BE-153)(iii) from
> ASSERTED-at-its-own-numbers)* BSATUR's own refuting peel `K4(5,3,3,3,3,3)` at
> skeleton edge `('A','B')`, side 1 the 5-branch, reflagged onto (BE-105)'s bad
> plane by `bsatur.bad_plane`/`reflag`, measured geometrically at **5/5** draws:
>
> > `(δ₁,δ₂ | a₁,a₂ | ρ₁,ρ₂ | c₁,c₂)(Π_x) = (5,3 | 0,0 | 5,3 | 2,0)`,
> > `e = (3, 3)`, `e₁ + e₂ = 6 ≥ 4` — **(E4) HOLDS**, asserted.
>
> Gates: `|V| = 18`, `|E| = 20`, girth 9, min degree 2,
> `deg(x) = deg(y) = 3`, `y ∉ N(x)`, `hcard` true, `{x,y}` a 2-cut,
> `rnode_shaped(side₂)` true, `deg₁(x) = 1`. F13 negative control: `c = 1 < 2`
> at the sampler's own plane, and the bad plane is not the drawn one. The
> reflag moves **no** side-1 vertex, asserted. **(BE-153)(iii)'s numbers are
> exactly reproduced** — and the *reason* (E4) holds there is now visible:
> **`ρ₂ = 3`**, a fact about **side 2**, which no per-side refutation and no
> landed sweep ever moved.

> **(BE-160)(ii)** *(**CONSTRUCTED and MEASURED**; the refutation)* The **same
> generator, one parameter along** — side-2 branch length `3 → 2`:
>
> > **`K4(5,2,2,2,2,2)`, peeled at `('A','B')`, side 1 the 5-branch, reflagged
> > onto the bad plane:**
> >
> > `(δ₁,δ₂ | a₁,a₂ | ρ₁,ρ₂ | c₁,c₂)(Π_x) = (5,0 | 0,0 | 5,0 | 2,0)`,
> > **`e = (3, 0)`, `e₁ + e₂ = 3 < 4`.**
> >
> > **§(K-bare-ext) (E4) IS FALSE.**
>
> Reproduced at **7/7** draws, exact ℚ; 15 further rows at `δ₂ = 0` over three
> skeletons in (BE-161)(i). Every gate asserted individually: `|V| = 13`,
> `|E| = 15`, **girth 6 ≥ 4**, min degree 2, `deg(x) = deg(y) = 3` (both hubs
> of `H`), **`y ∉ N(x)`**, **`hcard_ok_piece` true**, `{x,y}` a 2-cut with
> `delta_pair = (0, 5)`, **`rnode_shaped(side₂)` true** — so this is an
> *internal R-node peel*, (E4)'s own habitat — `deg₁(x) = 1` (a series end,
> BSATUR's own shape), **`verify_pencil_witness` TRUE** (a legal pencil
> realization), `Π_x ⊆ ρ̄₁` asserted directly, and the reflag moves no side-1
> vertex, so `ρ̄₁` is genuinely the drawn one. **F13 negative control clean**:
> `c = 1 < 2` at the sampler's own plane, so the row is evidence rather than an
> artefact of a degenerate draw. `bfour.py --wit`.

> **(BE-160)(iii)** *(**MEASURED**; not a shortfall, and the attaining case)*
> Margins `c₁(U) + c₂(U) − dim U − slack`: **`Π_x` 0, `Π_y` −1, `⟨M⟩` −1** —
> all `≤ 0`, asserted. So **item 0(b) [MARGIN] stays unexhibited**: this
> refutes a *clause*, it does not exhibit a *shortfall*. And `a₁ = a₂ = 0`, so
> the witness sits in the **attaining** case — the one (BE-101)(ii)'s corollary
> and S-mark's pin ((BE-22)(iii)/(BE-86)(i)) live in.

> **(BE-160)(iv)** *(**MEASURED**; (E4)'s *other* reading fails too)*
> (BE-153)(i) states (E4) with an *"equivalently"*: *the two sides' relative
> screw spaces together fill the 4-dimensional quotient `Λ²K⁴/Π_x`*. At the
> witness `dim(ρ̄₁ + ρ̄₂) = 5` and `dim((ρ̄₁ + ρ̄₂ + Π_x)/Π_x) = 3 < 4`,
> asserted. **Both** formulations fail at the same point, so the refutation is
> not an artefact of reading `e₁ + e₂` as an arithmetic surrogate.

> **(BE-160)(v)** *((BE-154)(iii)'s criterion, met verbatim)* That step
> predicted the shape: *"needs `ρ_i ≤ 5` **and** `ρ_j ≤ c_j(Π_x) + (5 − ρ_i)`,
> so on BSATUR's own `ρ_i = 5` witness it needs `ρ̄_j ⊆ Π_x` outright, i.e.
> `ρ_j ≤ 2`."* The witness has `ρ₁ = 5` and `ρ₂ = 0 ≤ 2` with `ρ̄₂ = 0 ⊆ Π_x`.
> **The prediction was exactly right about what to look for and exactly wrong
> about where to look**: it sent the hunt to a population whose `ρ₂` is pinned
> at 3.

> **(BE-160)(vi)** *(**the §8 bar, and it REVERSES — for (E4) ONLY**)*
> (BE-154)(iii) lifted `notes/Pencil-strategy.md` §8's bar for **(E4)** as *"a
> new object and … the cheaper of the two: (BE-152)/(BE-153) are already
> exhaustive on the arithmetic, so what remains is the geometry of a single
> lower bound on `e₁ + e₂`."* That geometry is now settled **negatively**: no
> such lower bound exists. So — and §8 records this on its own rule that a lift
> or a lowering is written down there with its reason:
>
> - **THE LIFT FOR (E4) REVERSES; the bar comes back down over it.** (E4) is
>   not a repair of (PENCIL-SATURATES-CHART) but a refuted clause, and §8's
>   recurring-wall rule now counts it as the **fifth** attempt in the family
>   (after `-GEN`, the `ρ_i ≥ 5` weakening, the per-side floor family, and the
>   corner patch).
> - **THE LIFT FOR `Γ`-PROPERNESS IS *NOT* REVERSED, AND IS STRENGTHENED.**
>   (BE-149)(v)'s lemma — properness of
>   `{p ∈ F : dim(Γ ∩ (Π_x(p) ⊕ Π_x(p))) ≥ 2}` — is untouched by this
>   refutation, and (BE-158)(i)/(ii) *add* to its standing: the certificate is
>   sound as an upper bound at **every** `k`, its identity now holds on
>   composite chart points, and where it fires it **proves** (E4) pointwise.
>   **A reader must not come away thinking the whole clause family is barred
>   again.**
> - **`A_sharp` PROPERNESS STAYS BARRED**, unchanged here.
> - **(BE-E4′) is a NEW object**, priced at (BE-162); whether §8 opens a lift
>   for it is not this direction's call.

### Step BE160 — (BE-161): the refutation is CONFINED to (BE-22)(vi)'s collapse — the `δ₂` ladder

> **(BE-161)(i)** *(**MEASURED**; the ladder, three skeletons, 57 rows over 12
> profiles)* Walking `δ₂` with `δ₁ = 5` and the flag adversarial at every rung:
>
> | `δ₂` | `ρ₂` | `c₂(Π_x)` | `e₂` | `e₁ + e₂` | (E4) | skeletons |
> |---|---|---|---|---|---|---|
> | **0** | 0 | 0 | **0** | **3** | **FAILS** | K4, prism, K33 |
> | 1 | 1 | 0 | 1 | **4** | holds, **TIGHT** | K4, prism, K33 |
> | 2 | 2 | 0 | 2 | 5 | holds | K4, prism, K33 |
> | 3 | 3 | 0 | 3 | 6 | holds | K4, K33 |
> | 6 | 6 | 2 | 4 | 7 | holds | prism |
>
> Asserted: (E4) fails at **every** `δ₂ = 0` rung (15 rows) and holds at
> **every** `δ₂ ≥ 1` rung drawn (42 rows). `bfour.py --repair`.

> **(BE-161)(ii)** *(the reading, resting on a PROVED theorem)* `δ₂ = 0` is
> exactly **(BE-22)(vi)**'s regime — *"if one side is rigid the general-position
> half disappears"*: `δ₂ = 0` gives `ρ₂ = 0` by (BE-22)(ii),
> `dim(ρ̄₁ + ρ̄₂) = ρ₁` and `min(δ₁+δ₂, 6) = δ₁`, so the 2-cut criterion
> collapses to the **single condition `ρ₁ = δ₁`** with *no general-position
> content whatsoever*. The witness has `ρ₁ = δ₁ = 5`, so **it attains**, and
> the **14 per-side inequalities (E4) exists to thin ((BE-97)/(BE-101)) are
> vacuous at it**. So the refutation is real *as a refutation of the sentence
> (E4)* and lands in the one regime where the sentence has no work to do.
> **This is why the verdict is a SPLIT and not a bar-lowering over the whole
> clause family**: (BE-154)(iii) wrote *"the bar should come back down for the
> whole clause family"* on the assumption that a falsifier would be a live
> counterexample, and a falsifier inside (BE-22)(vi)'s collapse is weaker news
> than that.

> **(BE-161)(iii)** *(**MEASURED**; the boundary is TIGHT, which is the bad
> news)* At `δ₂ = 1` the sum is **exactly 4** at 3 of 3 skeletons. So a
> repaired clause has **zero margin** at its own boundary: one further
> mechanism — `ρ̄₂ ⊆ Π_x` at `δ₂ = 1`, where `ρ̄₂` is a **single line** and
> `Π_x` is already pinned to (BE-105)'s bad plane — would refute it. Every
> draw here leaves `c₂(Π_x)` to the sampler rather than steering it; **no draw
> in this direction targets that coincidence**, and that is the named residue.

### Step BE161 — (BE-162): the REPAIR **(BE-E4′)**, its exact price, and what it does not buy

> **(BE-162)(i)** *(the clause)*
>
> > **(BE-E4′).** At an internal R-node peel with **`δ₁ ≥ 1` and `δ₂ ≥ 1`**, if
> > `c_i(Π_x) = 2` for some side `i`, then `e₁ + e₂ ≥ 4`. Same at `Π_y`.
>
> The added hypothesis is exactly (BE-22)(vi)'s complement — (BE-29)(i)'s
> *"genuinely open zone — both sides non-rigid with `δᵢ > 0`"*, which is the
> zone the arc's own tiers already sweep.

> **(BE-162)(ii)** *(**PROVED by exhaustion**; the price, paid by a theorem
> rather than by the clause)* Over the 6 400 tuples, (BE-E4′) admits **158**
> escapes where (E4) admitted 0. **All 158 have `min(δ₁, δ₂) = 0`** — asserted
> at 158/158, with `(δ₁,δ₂)` over `(0,0)…(0,5)` and `(1,0)…(5,0)`. So every
> escape it lets through sits in the regime **(BE-22)(vi) discharges by a
> proved theorem**, where the 14 inequalities are not part of the criterion at
> all. Hence
>
> > **14 → 12 survives on the both-flexible zone under (BE-E4′)**, with the
> > rigid-side remainder carried by (BE-22)(vi) instead of by a clause.
>
> Further: **1160** separating tuples (strictly weaker than
> (PENCIL-SATURATES), and weaker than (E4)'s 970), and **0** `Π_x` violations
> at `a₁ = a₂ = 0` — so **(BE-101)(ii)'s corollary survives**, asserted.

> **(BE-162)(iii)** *(**UNPROVED**, and refutable — the honest status, and the
> successor)* **245** tuples in the space still violate (BE-E4′), with `δ₂`
> down to **1**. Nothing here proves it: (BE-161)(i) measures it holding at
> every `δ₂ ≥ 1` rung of one ladder, at one `δ₁`, with `c₂(Π_x)` unsteered —
> **not found under that cap**. Given (BE-161)(iii)'s tightness the successor
> is the cheapest test this section has had in five steps:
>
> > **Steer `c₂(Π_x)` at `δ₂ = 1`.** Side 2's `ρ̄₂` is one line; `Π_x` is the
> > bad plane's pencil, already constructed. Ask whether the line can be put
> > inside it while side 1 stays bad. **YES kills (BE-E4′)** and finishes the
> > two-sided route as a family; **NO** is the geometric obstruction (BE-E4′)
> > needs.

> **(BE-162)(iv)** *(what does NOT follow, recorded because the temptation is
> real)* (BE-156)(i) shows every (E4) falsifier is a clause counterexample; the
> converse fails — (BE-104)'s witness is a clause counterexample where (E4)
> **holds** ((BE-160)(i)) — so this direction does **not** refute
> (PENCIL-SATURATES-CHART) again and exhibits **no** new clause counterexample
> beyond the (BE-104) family BSATUR already landed. It does **not** touch
> (BE-149)–(BE-152): every figure of theirs is reproduced or extended, and
> `Γ`-properness is where BARCH left it plus one bound and one identity in its
> favour. **What it does change is the shared exposure**: BSERIES's one-end
> reduction of (b2) to (b1) is **conditional on (PENCIL-SATURATES) at
> side-degree `≥ 2`** ((BE-168)/(BE-170)), i.e. on half (B)'s item 0(a) — the
> item (E4) was the successor to — so **both halves of S-mark now depend on the
> clause whose cheapest replacement just died.**

> **(BE-162)(v)** *(**the board**)* **What moved.** (E4) **REFUTED**
> ((BE-160)); §8's (E4) lift **REVERSED**, `Γ`-properness's **strengthened**
> ((BE-160)(vi)); (BE-153)(iii) **MEASURED**; (BE-149)(i) extended to composite
> chart points; a new bound `c₁(Π_x) ≤ dim Γ_Π` at every `k`; (BE-E4′) minted
> and priced. **What did NOT move.** `PencilPair K 3 G`, `hbareSplit`, `hK`,
> `hcontract`, (GR-15), (BE-14) and **S-mark**, class uniformity, the 12
> unwitnessed-not-excluded blocks ((BE-97)(iv), `⟨M⟩` empty at 93 rows),
> cross-pair welding, item 0(b) **[MARGIN]** (still unexhibited),
> (BE-101)(iii) (inhabited, not activated). No `.lean` opened; the 2026-08-05
> hold untouched. **Not a PENCIL event**, and the arc's standing result is
> unchanged: **`hK` is not closer**. **The E-rider.** No termination-ledger
> entry fires: **E1** no g-flank and no rank computed here; **E2** untouched;
> **E3 ARMED, does not fire** — this direction exhibits a refutation, not a
> class-uniform positive.

### Verification

New driver `notes/scripts/w4/bfour.py`, seven modes, exact ℚ, every headline an
`assert`, seed printed by every mode; run from the repo root, each in the
**foreground** with an explicit 600 s timeout:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --arith      #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --charta     # 505 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --chartb     # 504 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --gen        #  38 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --wit        #   3 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --repair     #  31 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --support    #   0 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bfour.py --validate   # 268 s, rc 0
```

`--chart` is the whole 411-target population in one process and measures
**~1 010 s**, which does not fit a 600 s foreground budget; its halves each do,
so it is carried as **two** foreground invocations — the YLOC / GGLOB
precedent recorded in `notes/scripts/README.md` §0, **not** a waiver.
`--validate` runs `chart` at a 70-point sample and **says so in its own
output**; every 411-point figure above comes from the two halves.
**Attestation:** the coordinator's verification tier re-ran `--wit` and
`--repair` and reproduced both exactly; the two chart halves were **not**
re-run at landing, so their figures are **measured-with-cap by this direction
and attested rather than independently reproduced.**

**Figure-invariance gate.** This landing only **adds** a driver:
`git diff --name-only -- '*.py' '*.m2'` is empty, `--cached` likewise, and
`git status --porcelain notes/scripts/` shows only the **addition** of
`w4/bfour.py` — so *No tracked driver modified* discharges the gate and §3 is
not baselined. Reproducibility spot-check: `--arith --gen --wit --repair` run
twice at `PYTHONHASHSEED=0` is **byte-identical** modulo the drivers' own
timing lines.

**Harness hazards navigated** (`notes/scripts/README.md` *Harness debt*).
`bimage.pt_in` is **not called** — the only calls in the import closure are
`sweep_points`' own, on the width-4 `p_x` fibre, which is what it is for, so
**no `Λ²`-side draw goes through it**. **No width-12 object goes through
`span`/`dim`/`isect`**: the one 12-wide measurement is inside
`barch.gamma_cut`, which routes it through `exactcore.rank` and works in
motion-space coordinates; every `K⁴`-side subspace here is built by
`nullspace`/`plane_at`, so `bdegtwo.k4span`/`k4meet` are left alone. `bwin` is
**not imported**, so `dehom`'s list-vs-tuple guard defeat is unreachable rather
than merely avoided.
