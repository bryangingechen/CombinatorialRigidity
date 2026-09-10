## §(K-bare-ext) — continuation (direction BOBLIG): **THE OBLIGATION IS NEITHER PROVED NOR REFUTED — IT IS *DECOMPOSED*, EXACTLY, AND ITS TOP RUNG IS FREE.** `c₁(Π_x) + c₂(Π_x) ≤ 2 + slack` is a **three-rung ladder in the single combinatorial number `δ₁+δ₂`**, constant on the chart: **`≥ 8` ⟹ TRUE with no hypothesis at all**, `= 7` ⟹ *not both sides fire*, `≤ 6` ⟹ **IS (NO-DOUBLE-PENCIL)** — so the residue is **exactly `δ₁+δ₂ ≤ 7`** and, at `a = 0`, exactly **30 tuples**, every one with `max(ρ₁,ρ₂) ≤ 5`. The cheapest route to it — (BE-95)(i)'s modular law — is **CIRCULAR by an identity**. The successor is **item 0(a)'s own clause with one added hypothesis**, and the **un-fenced `deg₁(x) = 2` population reaches the dispatch's whole quantifier for the first time** (`a = 0`, generic flag regime) with **0 violations at 135/135** — but **cannot present the discriminating shape** (*Steps BE224–BE229*)

**It opens at exactly the tail BNONUNI declared** (*"THE LIVE TAIL IS NOW
(BE-225) / Step BE224"*), enumerated rather than sampled per clause (L7) as
this direction's first action; the collision record and the (L6) disclosure
are `notes/Pencil-labels.md`'s. **One correction to the dispatch spec, and it
is the kind clause (L7) exists for:** the spec called the range *"verified
0-hit"*, and `(BE-225)` / *Step BE224* is **2 hits / 2 files** — BNONUNI's
tail-declaration sentence in the registry and in its untracked draft. Both are
**declarations, never consumptions**, which is the same non-zero-by-design
opening BGTWOA and BNONUNI each disclosed; the other thirteen tokens are 0/0.

### Standing notation (on top of *Steps BE148–BE223*)

BNONUNI's, verbatim, and **read at the definition sites rather than from a
docstring** (`barch.slack_of`, `barch.violates`, `barch.all_tuples`,
`barch.ps_full`, `barch.ps_floor`, `bfour.e_row`, `bfour.side_nums`,
`bproper.plant_peel`, `bproper.free_peel`, `bline.legal_peel`,
`bline.longcore_library`, `bunif.flag_frame`):

> **`slack := max(0, δ₁ + δ₂ − 6)`** and the **`Π_x` OBLIGATION**
> `c₁(Π_x) + c₂(Π_x) ≤ 2 + slack` — the `U = Π_x` member of (BE-97)/(BE-101)'s
> fourteen per-side inequalities, and (BE-100)(i)'s inequality. Write
> **`Σδ := δ₁ + δ₂`** and **`Σρ := ρ₁ + ρ₂`**.
>
> **`a_i := dim M_i − 6 − f_i`**, and `ρ_i = δ_i + a_i` **iff the welded side
> attains** ((BE-22)(ii)/(BE-86)); at `a = 0`, `ρ_i = δ_i` and `Σρ = Σδ`.
>
> **The Grassmann floor**, hypothesis-free: `dim(ρ̄_i ∩ Π_x) ≥ ρ_i + 2 − 6`, so
> **`c_i ≥ max(0, ρ_i − 4)`** and in particular **`ρ_i = 6 ⟹ c_i = 2`**. This
> is (BE-211)/(BE-213)(i)'s conjunct, and it is load-bearing three times below.

**Carrier check, off the landed bodies.** No new Lean object is read and **no
`.lean` was opened** (the 2026-08-05 hold). **No tracked script was
modified**: the driver `w4/boblig.py` is new and every configuration comes
from a predecessor's own builder, so the figure-invariance obligation is
discharged by the diff itself (`git diff --name-only -- '*.py'` names only the
new file, so no landed figure can move).

### Step BE224 — (BE-225): THE LADDER — three rungs in `Σδ`, and the top one is a theorem with no hypothesis

> **(BE-225)(i)** *(**PROVED**, hypothesis-free, then asserted by exhaustion)*
> `c_i(Π_x) ≤ dim Π_x = 2` gives `c₁ + c₂ ≤ 4` at **every** configuration. So
> `slack ≥ 2` — i.e. **`Σδ ≥ 8`** — makes the obligation **TRUE outright**:
> no genericity, no draw, no chart point. ∎ Asserted at all **630** such
> tuples of `barch.all_tuples()`, **0** failures.
>
> **Hence the obligation's residue is EXACTLY `Σδ ≤ 7`** — the **same** zone
> (BE-216)(i) left for `(BE-E4′)`, reached by a **different** identity
> (`c₁+c₂ ≤ 4` here, `e_i = ρ_i − 2` there). Asserted: all **1 655**
> violating tuples carry `Σδ ≤ 7`, which reproduces (BE-100)(iii)'s own
> figure for the same set.

> **(BE-225)(ii)** *(**PROVED by exhaustion**; the middle rung)* At `Σδ = 7`,
> `slack = 1`, so the obligation **is** `c₁ + c₂ ≤ 3` — i.e. **`Π_x` is not
> contained in BOTH relative screw spaces**. Asserted tuple by tuple.

> **(BE-225)(iii)** *(**PROVED by exhaustion**; the bottom rung, and it is a
> landed clause)* At `Σδ ≤ 6`, `slack = 0`, so the obligation **is
> `c₁ + c₂ ≤ 2`**, which by (BE-100)(i) **is (NO-DOUBLE-PENCIL)** verbatim.
> Asserted tuple by tuple. So the whole of the obligation is: *(NO-DOUBLE-
> PENCIL) below 6, "not both fire" at 7, free above.*

> **(BE-225)(iv)** *(**the hypothesis a relay drops**, and the dispatch spec
> asked for exactly this check)* `slack` is `max(0, δ₁+δ₂−6)` **read at
> `barch.slack_of`'s definition site**: it is a **function of the `δ`s**, so
> *"`slack = 0`"* is the **locus `Σδ ≤ 6`** and not a settable parameter. The
> sentence *"the obligation IS (NO-DOUBLE-PENCIL) at `slack = 0`"* is
> therefore **true and carries the hypothesis `Σδ ≤ 6`**. Measured: over the
> 6 400 tuples the two conditions **agree at 6 080 and differ at 320** — and
> **every** disagreement carries `Σδ ≥ 7` with the obligation the **weaker**,
> asserted. (The 320 is (BE-100)(iii)'s own gap figure, independently
> reproduced.) **That is why (BE-99)'s refutation of (NO-DOUBLE-PENCIL) does
> not reach the obligation:** its witness sits at `Σδ = 8`, margin `−1`
> ((BE-100)(ii)) — outside rung 1, in the zone where the obligation is
> strictly weaker. **The relayed sentence was sound; its hypothesis was
> missing, and the hypothesis is the whole content of the rung.**

### Step BE225 — (BE-226): THE STRENGTH AUDIT — the two relayed numbers re-derived, and "strictly weaker" is a statement about tuple SETS

> **(BE-226)(i)** *(**PROVED**, and both relayed figures REPRODUCE)* At
> `a = 0` there are **324** tuples; **(PENCIL-SATURATES) implies the
> obligation at all 324, 0 counterexamples**, and the **converse fails at
> 98** — asserted, and both figures are (BE-223)(ii)'s. **And the implication
> is a two-line proof, not 324 passes:** if side `i` fires then
> (PENCIL-SATURATES) gives `ρ_i = 6`, so at `a = 0` `Σδ = 6 + δ_j` and
> `slack = δ_j = ρ_j ≥ c_j`, whence `c₁+c₂ = 2 + c_j ≤ 2 + slack`; if neither
> fires, `c₁+c₂ ≤ 2` outright. ∎ The proof's one step is asserted at every
> (PENCIL-SATURATES) tuple.

> **(BE-226)(ii)** *(**PROVED by exhaustion**; and it re-prices the dispatch)*
> For the per-side floor family `(PS-f)` (`barch.ps_floor`:
> `c_i(Π_x) = 2 ⟹ ρ_i ≥ f`), the counterexample counts to *"(PS-f) implies
> the obligation at `a = 0`"* are
>
> > **`f = 0,1,2 : 30`; `f = 3 : 15`; `f = 4 : 6`; `f = 5 : 2`; `f = 6 : 0`.**
>
> So the obligation is implied by `(PS-6)` = (PENCIL-SATURATES) and by **no
> weaker member of that family** — asserted. The mechanism is the `c = (2,1)`
> corner: there `ρ_j` is bounded below only by `c_j = 1`, so the sum
> `Σρ ≥ 7` the obligation needs forces `f ≥ 6` on the firing side alone.
> **Hence "the obligation is STRICTLY WEAKER than item 0(a)'s clause" is a
> true statement about TUPLE SETS and NOT about proof difficulty inside the
> per-side floor family** — the distinction BNONUNI's own generalizable lesson
> asks for, applied to its own successor.

> **(BE-226)(iii)** *(**MEASURED**, then **REFUTED at a landed row**; the
> two-piece frontier, the (BE-205)(iii) shape)* Pairs `(f, g)` with
> `c_i(Π_x) = 2 ⟹ ρ_i ≥ f` **and** `c_j(Π_x) ≥ 1 ⟹ ρ_j ≥ g` sufficient at
> `a = 0`: **28** pairs, **minimal members `(0,4)`, `(4,3)`, `(5,2)`,
> `(6,0)`**. And the two cheapest are **dead**:
>
> > **`(0,4)` and `(4,3)` are REFUTED at a fully-gated in-regime `a = (0,0)`
> > peel** — `K33 (A,B)`, uniform profile `[4]*9`, side 1
> > `2 pendants + theta(3,3,3)`, with **`ρ = (2,6)`, `c(Π_x) = (1,2)`,
> > `δ = (2,6)`, `a = (0,0)`**, 8 such rows. Both members demand
> > `c_j ≥ 1 ⟹ ρ_j ≥ 3`, and there `c₁ = 1` with `ρ₁ = 2`.
>
> This is **BGTWOA's own kill mechanism arriving one rung down**: the row is
> its (BE-214) witness, and what supplies `c₁(Π_x) = 1` at a series end is
> **(BE-175)(i) itself** on the non-firing side. **Surviving: `(5,2)` and
> `(6,0)`** — and only `(5,2)` is weaker than item 0(a). Its `g = 2` half is
> exactly *"`ρ̄_j` is not a line inside `Π_x`"*, which **(BE-175)(i) makes
> FALSE at a series end at `x` with `ρ_j = 1`** — so `(5,2)`'s first check is
> whether that shape is reachable in-regime at `a = 0`, and it is named rather
> than assumed.

### Step BE226 — (BE-227): THE MODULAR-LAW ROUTE IS CIRCULAR — a proof about routes, not about the obligation

> **(BE-227)(i)** *(**PROVED**; the identity, then asserted)* (BE-95)(i) is
> `dim(ρ̄₁ ∩ ρ̄₂) ≥ c₁(U) + c₂(U) − dim U` for **every** `U`. At `U = Π_x` the
> obligation is therefore **equivalent to `dim(ρ̄₁ ∩ ρ̄₂) ≤ slack`**, i.e. to
> `dim(ρ̄₁ + ρ̄₂) ≥ Σρ − slack`. At `a = 0` that right-hand side **is
> `min(Σδ, 6)`** — asserted at all 324 `a = 0` tuples — which is the `≥` half
> of **(BE-22)(iii)**, the attainment statement the obligation is a
> **necessary condition for**. ∎
>
> **So the cheapest-looking route derives the obligation from its own
> conclusion.** What the induction hypothesis `a_i = 0` (per-side attainment)
> actually supplies is `ρ_i = δ_i` and **nothing about the relative position
> of the two subspaces** — which is the entire content of the obligation. This
> is recorded because the modular law is the first thing a reader reaches
> for, it *looks* like a one-line proof, and it is one-line **in the wrong
> direction**.

> **(BE-227)(ii)** *(**PROVED by exhaustion**; the residue, exactly)* Of the
> 324 `a = 0` tuples, **30** violate the obligation; **all 30** are
> Grassmann-floor-legal ((BE-213)(i)) and **all 30** are
> attainment-compatible (`min(Σδ,6) + a₁ + a₂ ≤ 6`, (BE-22)(iii)/(BE-86)(i)),
> splitting **10** in the `c = (2,2)` corner and **20** in the `c = (2,1)`
> corner and **nothing else**. And
>
> > **every one has `max(ρ₁, ρ₂) ≤ 5`** — asserted.
>
> The reason is the Grassmann floor: `ρ_i = 6 ⟹ c_i = 2` **and** `δ_i = 6` at
> `a = 0`, so `slack = δ_j = ρ_j ≥ c_j` and the obligation closes for free.
> **Hence the obligation's whole content sits exactly where firing is NOT
> Grassmann-forced**, which is item 0(a)'s own bad locus — the 30 tuples
> include `ρ = (3,3)`, `c = (2,2)`, which is the shape of the two landed
> pointwise-refutation families ((BE-229)(iii)).

### Step BE227 — (BE-228): THE SUCCESSOR — item 0(a)'s clause with ONE added hypothesis, and neither half can be relaxed

> **(BE-228)(i)** *(**PROVED**, then asserted by exhaustion)* The clause
>
> > **§(K-bare-ext) (BE-OBL).** At an internal R-node peel in the generic
> > flag regime, `c_i(Π_x) = 2` **and** `c_j(Π_x) ≥ 1` ⟹ `ρ_i = 6`.
>
> **implies the `Π_x` obligation at `a = 0`** — asserted, 0 counterexamples
> over the 324 tuples. *Proof.* If no side fires, `c₁+c₂ ≤ 2`. If side `i`
> fires and `c_j = 0`, `c₁+c₂ = 2`. Otherwise `ρ_i = 6`, so `Σδ = 6 + δ_j`
> and `slack = ρ_j ≥ c_j`. ∎ It is **item 0(a)'s own clause
> (PENCIL-SATURATES) with the single added hypothesis `c_j(Π_x) ≥ 1`**, and it
> is **strictly weaker**: it holds at **56** `a = 0` tuples where
> (PENCIL-SATURATES) fails.

> **(BE-228)(ii)** *(**two NEGATIVE CONTROLS, both asserted**; neither half
> can be relaxed)* **The conclusion cannot drop to `ρ_i ≥ 5`** — 2
> counterexamples, e.g. `c = (2,1)`, `ρ = (5,1)`, `Σρ = 6 < 7`. **The
> hypothesis cannot strengthen to `c_j(Π_x) = 2`** — 20 counterexamples, the
> whole `c = (2,1)` corner. So the honest successor is **not a weaker
> inequality but item 0(a) RESTRICTED TO THE TWO-SIDED SUB-LOCUS**, and that
> is the exact content of *"one rung weaker"*.

> **(BE-228)(iii)** *(**the scope, from (BE-175)(i)**; where the restriction
> is free and where it buys something)* At a **series end at `x`**
> (`deg_j(x) = 1`), (BE-175)(i) makes `c_j(Π_x) ≥ 1` **automatic**, so on such
> a peel (BE-OBL)'s added hypothesis is **vacuous** and the obligation is
> item 0(a) **verbatim**. The restriction therefore has content **exactly when
> neither side is a series end at `x`** — i.e. at side-degree `≥ 2` on both
> sides, which is where this dispatch's quantifier puts it, and which
> `rnode_shaped` already forces on side 2 ((BE-175)(ii)). **This is the
> statement (BE-223)(ii)'s *"strictly weaker"* was pointing at, localized.**

### Step BE228 — (BE-229): THE POPULATIONS — the fence, the UN-FENCING, and the sharpest test

> **(BE-229)(i)** *(**MEASURED**; the in-regime `plant_peel` population is
> fenced twice, and it delivers the strictness witness instead)* BNONUNI's
> machinery unchanged — `bproper.plant_peel` over `bproper.PEELJOBS` with the
> non-uniform `δ₂` axis (BE-218) **plus** BGTWOA's uniform-`plen` jobs — with
> the **obligation** read off each row instead of `(BE-E4′)`'s margin:
>
> > **64** fully-gated rows, **64** in the generic flag regime, firing at
> > **64**, the content corner `c₁+c₂ ≥ 3` reached at **8**, and the
> > **obligation FAILS at 0**. `a = (0,0)` at **8** of 64 (`a₁ ∈ {0,1,2,3,6}`,
> > `a₂ = 0`); `deg₁(x) = 1` at **64/64**; residue reached at **0**.
>
> **Both fences are measured, not argued:** `plant_peel` returns `None` unless
> side 1's neighbour count at `x` is 1, and `a = 0` is a minority of its rows.
> What it *does* deliver is the **first geometric witness of (BE-226)(i)'s
> 98-tuple strictness**: at **56** of the 64 rows item 0(a)'s clause **FAILS**
> (a planted side firing at `ρ₁ = 4 < 6`) while the **obligation HOLDS** at
> margin `0` — so the strictness gap is inhabited by configurations through
> every habitat gate, not merely by tuples. *(These rows are **planted**, so
> they do not refute item 0(a), which is generic; they exhibit the gap.)*

> **(BE-229)(ii)** *(**THE UN-FENCING, and it is the positive**;
> `deg₁(x) = 2` in the regime at `a = 0`)* The blind axis BNONUNI disclosed —
> `deg₁(x) ≥ 2` on the firing side — is opened at the cost of **a different
> landed call and no harness edit at all**: `bproper.free_peel`, the F13
> negative control of the same peel, carries **no degree gate**, and
> `bline.longcore_library()` puts `x` on a short cycle. Then:
>
> > **135** fully-gated rows; **`deg₁(x) = 2` at 135/135**; **`a = (0,0)` at
> > 135/135**; **generic flag regime at 135/135** — all three asserted. `δ₁`
> > spans `1…6`, `δ₂ ∈ {0,1,2,3,6}`, `Σδ` spans `1…12`. Firing at **39**, the
> > content corner at **9**, and the **OBLIGATION FAILS at 0**.
>
> **This is the first population in the whole (BE-14) thread that reaches the
> obligation's own quantifier** — every predecessor was fenced out by `a ≠ 0`,
> by the flag regime, or by `deg₁(x) = 1` — and the obligation is unviolated
> on it. **CAP, and it is the finding's other half:** the **residue**
> ((BE-227)(ii)) is reached at **0** rows. All 9 content-corner rows sit at
> `c = (1,2)`, `ρ = (5,6)` or `c = (2,2)`, `ρ = (6,6)`, margin `−4` — every
> firing this population produces is at `ρ_i = 6`, where Grassmann forces
> `c_i = 2` and the obligation is free. So the reading is **"not found under
> this cap"**, never *"does not exist"*: **the population cannot present the
> discriminating case**, which is the shape (BE-186)(i) recorded one rung up,
> and the discriminating case **is item 0(a)'s bad locus**. Cap disclosed:
> 27 library shapes × 5 profiles × **1** seed, one seed traded for the `δ₂`
> coverage.

> **(BE-229)(iii)** *(**MEASURED**; the sharpest test the obligation has, and
> it is disqualified STRUCTURALLY)* BRANKV's (BE-192) arc-3 and BLONGARC's
> (BE-200)(iv) arc-4 families, re-read against the **obligation** rather than
> against `(BE-E4′)`:
>
> > **48** gated chart points, `ρ = (3,3)`, `c(Π_x) = (2,2)`, `a = (3,12)`,
> > `slack ∈ {0,1}` — the **obligation FAILS at 48 of 48**, and `flag_frame`
> > is **None at 48/48** with **`a = (0,0)` at 0/48**. Both asserted.
>
> So the only landed population that violates the obligation is outside its
> quantifier on **both** counts, and the first is **structural rather than
> incidental**: (BE-191) and (BE-200) *force* `q_y ∈ π_x` / `q_z ∈ π_x`, which
> is exactly one of the three exclusions `bunif.flag_frame`'s rank-4 test
> applies. **This population provably cannot refute the obligation.** It is
> also the exact `c = (2,2)`, `ρ = (3,3)` tuple of (BE-227)(ii)'s residue —
> so the residue is *inhabited off the quantifier* and *unreached inside it*,
> which is the honest state.

### Step BE229 — (BE-230): the verdict, the board, §8, and the bars

> **(BE-230)(i)** *(**the verdict**)* The naked `Π_x` obligation at a generic
> chart point with `a₁ = a₂ = 0` and side-degree `≥ 2` is **NEITHER PROVED NOR
> REFUTED, and is now DECOMPOSED**: rungs `Σδ ≥ 8` and (arithmetically)
> `Σδ = 7`/`Σδ ≤ 6` ((BE-225)), residue **exactly 30 tuples** all at
> `max ρ ≤ 5` ((BE-227)(ii)), successor **(BE-OBL)** = item 0(a) ∧
> `c_j(Π_x) ≥ 1` with neither half relaxable ((BE-228)), and **0 violations at
> 135/135 rows inside its own quantifier** ((BE-229)(ii)). It stays **OPEN**;
> **no gap-map status word moves**, and this is **not** a PENCIL event.

> **(BE-230)(ii)** *(**what this does to §8**)* The obligation entered the
> board as a rank-1 candidate on the sufficiency test. It **survives** that
> test and gains what it did not have: a **named smallest first slice** —
> **(BE-OBL)**, one added hypothesis on a landed clause, with `(5,2)` as the
> per-side alternative and its own first check named. Two routes are now
> **closed** rather than open: the modular law ((BE-227)(i)) and every
> per-side floor below `f = 6` ((BE-226)(ii)).

> **(BE-230)(iii)** *(**the bars this adds**, as §8's rule requires)*
> *(a)* **No further per-side-floor attempt on the obligation at `a = 0`** —
> `(PS-f)` for `f ≤ 5` is refuted as *sufficient* by exhaustion, and the
> two-piece frontier's two cheapest members are refuted at a landed in-regime
> `a = 0` row. *(b)* **No modular-law / (BE-95)(i) derivation of the
> obligation** — circular by an identity, (BE-227)(i). *(c)* **No reading of
> the arc-3/arc-4 families as a refutation of the obligation** — they fail it
> 48/48 and are off its quantifier on two independent, one of them
> structural, counts. BLONGARC's four, BEFOURP's three, BGTWOA's three and
> BNONUNI's three stand unchanged.

> **(BE-230)(iv)** *(**the generalizable lesson**, one level above the
> instance)* BNONUNI's lesson was *compare a proposed reduction's strength to
> its target's on the same tuple space*. This landing's is its sequel and it
> bites in the opposite direction: **"strictly weaker as a set of tuples" does
> not mean "weaker as a proof obligation"** — the obligation is strictly
> weaker than item 0(a) at 98 tuples and yet **no weaker member of item 0(a)'s
> own clause family implies it**, because the weakening lives in a *corner*
> (`c = (2,1)`) rather than along the *conclusion*. So when a target is
> demoted to a weaker successor, **locate the weakening**: if it is a corner
> of the hypothesis space rather than a slackening of the conclusion, the
> successor's proof is the predecessor's proof plus a hypothesis, and the
> honest first slice is the *restricted* clause, not a smaller number.

### Verification (Steps BE224–BE229)

Driver `notes/scripts/w4/boblig.py`, four modes plus `validate`; exact ℚ
throughout, `PYTHONHASHSEED=0`, seed `20260902` (printed; unused by `arith`).

| claim | status |
|---|---|
| (BE-225)(i)–(iii) the three rungs; residue exactly `Σδ ≤ 7` | **proven** (hypothesis-free) + asserted over all 6 400 tuples |
| (BE-225)(iv) the `slack = 0` locus; 6 080 / 320 split, all disagreements weaker | **proven** + asserted; reproduces (BE-100)(iii)'s 320 |
| (BE-226)(i) 324 / 0 / 98, and the two-line proof | **proven** + asserted at every (PENCIL-SATURATES) tuple |
| (BE-226)(ii) the `(PS-f)` counterexample ladder `30/30/30/15/6/2/0` | **proven** (exhaustive) |
| (BE-226)(iii) 28 sufficient pairs, minimal `(0,4)/(4,3)/(5,2)/(6,0)`; two REFUTED | **proven** (enumeration) + **measured** at 8 gated in-regime `a = 0` rows |
| (BE-227)(i) the modular-law circularity identity | **proven** + asserted at all 324 `a = 0` tuples |
| (BE-227)(ii) residue = 30, all floor-legal, all attainment-compatible, `max ρ ≤ 5` | **proven** (exhaustive) |
| (BE-228)(i)/(ii) (BE-OBL) sufficient; both negative controls fire | **proven** + asserted, 0 counterexamples |
| (BE-228)(iii) the series-end scope | **stated** from (BE-175)(i)/(ii); no new measurement claimed |
| (BE-229)(i) 64 rows, 0 failures, `a = 0` at 8, 56 strictness rows | **MEASURED**, every habitat gate asserted through `bline.legal_peel` |
| (BE-229)(ii) 135 rows, `deg₁(x) = 2` / `a = 0` / regime at 135/135, 0 failures, residue 0 | **MEASURED**, all three asserted; cap disclosed |
| (BE-229)(iii) 48 rows, obligation fails 48/48, off-regime 48/48, `a ≠ 0` 48/48 | **MEASURED**, asserted |

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/boblig.py arith     # (BE-225)-(BE-228), 0.0s
PYTHONHASHSEED=0 python3 notes/scripts/w4/boblig.py regime    # (BE-229)(i),   ~140s
PYTHONHASHSEED=0 python3 notes/scripts/w4/boblig.py degtwo     # (BE-229)(ii),  ~255s
PYTHONHASHSEED=0 python3 notes/scripts/w4/boblig.py gated      # (BE-229)(iii),  ~12s
PYTHONHASHSEED=0 python3 notes/scripts/w4/boblig.py validate   # all four,      ~405s
```

**THE AXES THIS GENERATOR CANNOT VARY** (`RESEARCH-ARC.md` §4's newest clause,
run forward rather than as a post-mortem — the blind-axis list is a candidate
list of cheap decisive moves, and this landing spent one of BNONUNI's):

1. **PAID, and it was the round's positive.** `deg₁(x) ≥ 2` on the firing
   side, `plant_peel`'s hard gate — reached through `free_peel` at the cost of
   **one different landed call and zero tracked edits**, and it delivered the
   first in-quantifier population ((BE-229)(ii)).
2. **OPEN: side 2's topology.** Every row here has side 2 a **subdivided
   `K33` or `prism`**, so `deg₂(x) = 3` at **all 199** measured rows. A peel
   with `deg₂(x) = 2` is `rnode_shaped`-legal in principle and unreachable
   from `SKELETONS`, which has exactly two members.
3. **OPEN: the side-1 library.** `bline.longcore_library()` hardcodes cycle
   lengths `(4,5,6)` and tails `1…6`; `bproper.side_library()`'s bucket-A
   pieces are a fixed list. Neither is a parameterized family, so
   *"δ₁ spans 1…6"* is a statement about those two lists.
4. **OPEN, and it is where a refutation would have to come from:** nothing in
   the harness produces a **generic** chart point with `c_i(Π_x) = 2` at
   `ρ_i ≤ 5`. `plant_peel` produces it by **planting** (hence `a ≠ 0`);
   `flat_config` produces it **off the flag regime**. That the two available
   constructions each land outside the obligation's quantifier is measured
   ((BE-229)(i)/(iii)) and is **exactly item 0(a) being unrefuted** — so the
   axis is not a harness gap that a keyword argument opens, it is the open
   mathematics.

### Confidence verdict (Steps BE224–BE229)

**The obligation: OPEN — DECOMPOSED, with a free top rung, an exact 30-tuple
residue and a named first slice.** The decomposition, the circularity and both
strength audits are **proven** (hypothesis-free arithmetic plus exhaustive
assertion over a cap-free tuple space). The geometric side is **measured**:
0 violations at 135/135 rows inside the quantifier, and the residue **unreached
there** — *not found under this cap*, never *does not exist*.

### What would change this (Steps BE224–BE229)

- **A proof of (BE-OBL)** ((BE-228)(i)) closes the obligation, hence — with
  (BE-101)(ii) and (BE-22)(iii) — the `U = Π_x` member of the fourteen.
- **A generic in-regime `a = 0` chart point with `c_i(Π_x) = 2` at
  `ρ_i ≤ 5` and `c_j(Π_x) ≥ 1`** refutes it. By (BE-227)(ii) that is the
  **only** shape that can, and by blind-axis item 4 no landed construction
  produces it.
- **A reachable series end at `x` with `ρ_j = 1` and `c_j = 1` alongside a
  firing side, in-regime at `a = 0`** kills the surviving frontier member
  `(5,2)` and leaves `(6,0)` = item 0(a) as the only per-side route.
