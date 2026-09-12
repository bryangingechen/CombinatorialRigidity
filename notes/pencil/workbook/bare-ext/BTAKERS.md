## §(K-bare-ext) — continuation (direction BTAKERS, ordinal 107, 2026-09-12): **(BE-239)(ii)'s *"how every consumer in Steps BE148–BE237 uses it"* IS REFUTED — FOUR landed sentences in its own range quantify the obligation at a GENERIC CHART POINT, one of them is BOBLIG's own refutation criterion, and the certificate misses it by the single word *generic*.** The classification is **not** the spec's dichotomy: the 44 obligation-naming clauses of the range sort into **five** quantifier classes, and the two that decide the damage are **neither** pole — the **tuple space** (configuration-free) and the **existential**. Net price of the round's headline: **0 consumers of the obligation lose a hypothesis**; **3 successor status words** (`(BE-OBL7)`, `(BE-OBLK)`, `(BE-E4′)`) need the qualifier *"as a universal"*; and **one long-open existential item is DISCHARGED** — **item 0(b) [MARGIN] is EXHIBITED**, margin `+1` at `Π_x`, where steering is not a weakness but sufficient (*Steps BE262–BE269*)

**DRAFT — untracked, uncommitted.** Merges into a new file
`notes/pencil/workbook/bare-ext/BTAKERS.md` at landing. Baseline `HEAD` =
`29a60d1a`; every figure below is read against that sha, never the working
tree. Reserved namespace verified CLEAN at the baseline
(`ledger.py --reserve-range 'BE-263..BE-270' --steps BE262..BE269 --also
BTAKERS btakers --ref 29a60d1a` → 18 tokens, 0 hits, 0 files).

**NO DRIVER IS SHIPPED, and that is the correct outcome for this entry.**
This is a prose re-read. Everything below is either a verbatim quotation from
a landed clause or arithmetic on a landed, already-asserted tuple. The one
mechanical step — the consumer enumeration — was done with two shell
commands and `notes/ledger.py`, both recorded verbatim in *Step BE262* so the
enumeration is reproducible without a new script. **No `.lean` opened, no
`lake build`**; the 2026-08-05 hold untouched.

### Standing notation (on top of *Steps BE148–BE253*)

BSIXRUNG's and BWHOLEH's, verbatim:

> **`slack := max(0, δ₁ + δ₂ − 6)`** and the **`Π_x` OBLIGATION**
> `c₁(Π_x) + c₂(Π_x) ≤ 2 + slack` — the `U = Π_x` member of
> (BE-97)/(BE-101)'s fourteen per-side inequalities (BOBLIG's *Standing
> notation*). **RUNG 3** is the locus `Σδ ≤ 6`, where `slack = 0` and the
> obligation **is** `c₁ + c₂ ≤ 2` ((BE-225)(iii)).
>
> **THE CERTIFICATE** is BWHOLEH's ((BE-249)(ii)/(iii)): the whole-`H` peel
> at `t = (δ₁,δ₂,a₁,a₂,ρ₁,ρ₂,c₁,c₂) = (2,4,0,0,2,4,2,1)`, `Σδ = 6`,
> `slack = 0`, in the generic flag regime, side-degree `≥ 2` on both sides
> (`deg₁(x) = 2`, `deg₂(x) = 3`), 72/72 against a 36/36 control.
>
> **Three quantifiers, kept apart in every sentence below.**
> **(Q-univ)** *for every configuration of the chart's generic-flag stratum*;
> **(Q-gen)** *at a generic chart point* — i.e. on a dense open of
> `Chart(H)`, equivalently off a proper closed subset;
> **(Q-ex)** *at some configuration* — the form an "unexhibited" item carries.
> `(Q-univ) ⟹ (Q-gen) ⟹ (Q-ex)` and none of the converses. A **steered**
> witness refutes (Q-univ), is **inert** against (Q-gen), and **discharges**
> (Q-ex).

**Two bars inherited and obeyed.** BWHOLEH's scope sentence ((BE-253)(ii),
(BE-247)(i)–(iii)) is **settled and not re-litigated here**: the certificate
does not reach (BE-14), half (B) or `hbareSplit`. (BE-245)(iii)(a) — no
mechanism-completeness claim carried across a rung without being re-taken —
is why *Step BE262* states its own generator and its own escape routes rather
than inheriting (BE-239)(ii)'s population sentence. **No consumer's prose is
repaired here**; every repair is handed to the coordinator in the closing
block.

---

### Step BE262 — (BE-263): THE ENUMERATION — how the consumer set was generated, and the three ways something can still escape it

> **(BE-263)(i)** `[MEASURED]` *(the generator, stated because "every
> consumer" is its own claim class — `RESEARCH-ARC.md` §4)* *Steps
> BE148–BE237* are held by **exactly ten** files of
> `notes/pencil/workbook/bare-ext/`: `BARCH` (BE148–BE154), `BFOUR`
> (BE155–BE161), `BSERIES` (BE163–BE170), `BSTEER` (BE171–BE176), `BGPROP`
> (BE179–BE186), `BRANKV` (BE187–BE194), `BLONGARC` (BE195–BE202), `BEFOURP`
> (BE203–BE216), `BNONUNI` (BE217–BE223), `BOBLIG` (BE224–BE237). *Steps
> BE162* and *BE178* are the registry's two returned strays
> (`labels.md`; `gapmap.md`'s (K-bare-ext) row names both), so the range has
> **no hole a file could hide in**. Enumerated per-file by
> `grep -o '^### Step BE[0-9]*'` and cross-checked against the gap-map row.
>
> The consumer set was then generated **three ways, and the union taken**:
>
> 1. **`ledger.py --cited-by`** on `(BE-OBL)` (3 clauses), `(BE-OBL7)` (0),
>    `(BE-OBLK)` (0), `(BE-225)` (6), `(BE-97)` (22), `(BE-100)` (8),
>    `(BE-101)` (45), `(NO-DOUBLE-PENCIL)` (0).
> 2. A **clause-block scan** over the ten files: each `> **(BE-n)(c)**`
>    blockquote block is read whole and kept if its body names the object in
>    the corpus's own words — `obligation`, `NO-DOUBLE-PENCIL`, `BE-OBL`.
>    **44 label-clauses.** A second pass on the **symbolic** forms
>    (`c₁ + c₂`, `margin`) with the word-matches removed adds **14**
>    candidates; a third on `item 0(b)` adds **5**.
> 3. A **manual pass over the un-indexed verdict blocks** — `### Confidence
>    verdict` / `### What would change this` — which `--cited-by` **cannot**
>    reach because they are not `> **(LABEL)**` blockquotes
>    (`notes/pencil/CLAUDE.md`, *"Not everything is indexed"*). In this range
>    there is **exactly one such pair**, BOBLIG's at `BOBLIG.md:387` and
>    `:396`, and **it contains the single most load-bearing sentence in this
>    direction** ((BE-264)(iv)).

> **(BE-263)(ii)** `[PROVED]` *(why `--cited-by` alone is **not** a
> sufficient generator here, and this is a finding about the tool, not a
> complaint)* The `Π_x` obligation **has no label of its own.** It is
> introduced in BOBLIG's *Standing notation* as *"the `U = Π_x` member of
> (BE-97)/(BE-101)'s fourteen per-side inequalities"*, and `(BE-97)`/
> `(BE-101)` are the **whole fourteen**, not the member. So `--cited-by
> '(BE-97)'` returns 22 clauses and `--cited-by '(BE-101)'` returns 45, of
> which most are about other blocks entirely, while the obligation's own
> consumers inside BOBLIG cite `(BE-225)` or nothing at all. **The mechanical
> generator over-returns and under-returns at the same time**, and only the
> clause-block scan separates them. Recorded because the dispatch spec named
> `--cited-by` as *"the right generator"* and a grep as *"not"*: on this
> object the honest answer is **both, plus a hand pass over the un-indexed
> blocks**.

> **(BE-263)(iii)** *(**13 false positives**, named so the count is auditable)*
> The scan's `item 0(a)` arm returns **13** clauses that name **half (B)'s
> item 0(a)** — which is `(PENCIL-SATURATES)` at side-degree `≥ 2`, a
> **different object**: (BE-162)(iv), (BE-169)(ii), (BE-171)(ii), (BE-175)(i),
> (BE-177)(iii), (BE-186)(iii), (BE-194)(i), (BE-203)(ii), (BE-203)(vi),
> (BE-206)(v), (BE-209)(vii), (BE-217)(vi), (BE-228)(ii). They are **excluded
> from the consumer count** and re-enter only through the item-0(b) arm
> ((BE-209)(vii), (BE-217)(vi) — see (BE-267)). The conflation is easy to
> make and this direction made it for two probes: item 0(a) is a **per-side
> implication**, the obligation is a **two-sided inequality**, and
> (BE-223)(ii) measures the first **strictly stronger** than the second at 98
> of 324 `a = 0` tuples.

> **(BE-263)(iv)** *(**what can still escape**, three routes, disclosed
> rather than smoothed)* *(a)* **A fourth alias.** The scan covers
> `obligation` / `NO-DOUBLE-PENCIL` / `BE-OBL` / `c₁ + c₂` / `margin` /
> `item 0(b)`. A clause that consumed the obligation only as *"the `U = Π_x`
> block"* or *"the fourteen"* or through `bunif.never_bites` would be missed;
> an aliases grep for those three phrases over the ten files returns **4**
> lines, all inside clauses the scan already holds (`BOBLIG.md:22`, `:131`,
> `:399`, `:574`). *(b)* **A verdict block in another shape.** The
> `### Confidence verdict` / `### What would change this` headings exist in
> **exactly one** of the ten files; a direction that wrote its verdict under a
> different heading, or inside `fanout.md`'s write-up rather than the
> workbook, is outside this scan. `fanout.md` and `strategy.md` §8 are
> **deliberately outside** the range (BE-239)(ii) names, and both carry live
> status text — they are in the closing block as coordinator actions, not as
> consumers. *(c)* **A consumer one step outside the range.** The range is
> (BE-239)(ii)'s, not this direction's: the arc's actual block-list consumer
> is **(BE-101)(ii)** at *Step BE100*, which is **out of range by one
> step-block**, and its own quantifier is *"read at a **generic flag** this
> stands verbatim"* — i.e. it lands in the same class as every in-range
> verdict ((BE-265) class **G**). Including it would strengthen this
> direction's verdict; it is excluded to keep the population the one the
> sentence under test names.

---

### Step BE263 — (BE-264): (BE-239)(ii) IS REFUTED — four landed sentences in its own range carry (Q-gen), and the fourth is BOBLIG's own refutation criterion

> **(BE-264)(i)** `[REFUTED]` *(**the verdict**, stated with the sentence it
> kills)* (BE-239)(ii) reads *"What it would refute is the obligation **as a
> universally-quantified statement over the chart's generic-flag stratum**,
> which is how **every** consumer in *Steps BE148–BE237* uses it."* **The
> *every* is FALSE.** Four landed sentences inside that range state the
> obligation **at a generic chart point** — (Q-gen), not (Q-univ) — and three
> of them are the range's own **verdict** clauses, i.e. the most load-bearing
> consumers it has. Quoted, not paraphrased:
>
> - **(BE-223)(iii)** *(BNONUNI, Step BE222)*: *"the (BE-14) thread's open
>   content is exactly: **the `Π_x` obligation at a generic chart point with
>   `a = 0`, at side-degree `≥ 2`.**"*
> - **(BE-230)(i)** *(BOBLIG, Step BE229)*: *"The naked `Π_x` obligation **at
>   a generic chart point** with `a₁ = a₂ = 0` and side-degree `≥ 2` is
>   **NEITHER PROVED NOR REFUTED, and is now DECOMPOSED**…"*
> - **(BE-238)(i)** *(BCORNER, Step BE237)*: *"**The `Π_x` obligation at a
>   generic chart point with `a = 0` and side-degree `≥ 2` remains exactly
>   where BOBLIG left it: OPEN**"*.
> - **BOBLIG's *What would change this (Steps BE224–BE229)*, bullet 2**
>   (`BOBLIG.md:399`–`402`, an **un-indexed** block): *"**A generic in-regime
>   `a = 0` chart point with `c_i(Π_x) = 2` at `ρ_i ≤ 5` and `c_j(Π_x) ≥ 1`**
>   refutes it. By (BE-227)(ii) that is the **only** shape that can."*
>
> ∎ **Not one of the four is reached by BWHOLEH's certificate.**

> **(BE-264)(ii)** `[PROVED]` *(**the certificate sits at a provably
> non-generic point**, and this is a proof off landed clauses, not an
> absence of evidence)* Let `H` be the named certificate's piece
> ((BE-249)(iii)). *(1)* By **(BE-239)(ii)**, a rung-3 violation forces
> `dim(ρ̄₁ + ρ̄₂) ≤ Σρ − 1 < min(Σδ,6) + a₁ + a₂`, hence by (BE-86)(i) the
> peel does **not** attain; so the obligation's failure locus on `Chart(H)` is
> contained in `Chart(H) \ Good(H; x, y)`. *(2)* By **(BE-253)(ii)** the same
> `H` at a **free** draw (`bproper.free_peel`, 6 of 6, in-regime) gives
> `t = (2,4,0,0,2,4,0,1)` and `H` **attains**, so `Good(H; x, y) ≠ ∅`.
> *(3)* By **(BE-69)(i)/(ii)** `Good` is open in `Chart(H)` and `Chart(H)` is
> irreducible, so a nonempty `Good` is **dense open**. Hence the obligation's
> failure locus on this `H` is contained in the complement of a dense open:
> it is **nowhere dense**. ∎ **So the obligation holds at a generic chart
> point of the very `H` that refutes it as a universal**, and every consumer
> in class **G** is untouched **by a proof**, not by a gap in the evidence.

> **(BE-264)(iii)** `[PROVED]` *(**the near-miss, measured conjunct by
> conjunct** — the certificate meets BOBLIG's refutation criterion on every
> clause except one word)* BOBLIG's criterion asks for a chart point that is
> **(a)** generic, **(b)** in-regime, **(c)** `a = 0`, **(d)** `c_i(Π_x) = 2`,
> **(e)** `ρ_i ≤ 5`, **(f)** `c_j(Π_x) ≥ 1`. The certificate
> ((BE-249)(ii)/(iii)) delivers **(b)** `bunif.flag_frame` non-`None` 72/72,
> **(c)** `a = (0,0)` 72/72, **(d)** `c₁ = 2`, **(e)** `ρ₁ = 2 ≤ 5`,
> **(f)** `c₂ = 1 ≥ 1` — **five of six**, at the tightest possible value of
> (e). It fails **(a)** alone, and (a) is the word the owning direction put
> first. **This is the single sharpest statement this re-read produces:** the
> round's headline result is one word away from the criterion its own target's
> owning direction wrote down, and the word is exactly the one (BE-239)(ii)
> asserted no consumer carried.

> **(BE-264)(iv)** *(**the process finding**, and it is the same shape as
> (BE-231)(ii))* BOBLIG's refutation criterion has been in the tree since
> 2026-09-09 and is **invisible to `ledger.py`**: it lives in a
> `### What would change this` bullet, not a `> **(LABEL)**` blockquote, so
> `--cited-by`, `--label` and `--brief` all return nothing for it, and
> `--selftest`'s 20-mention threshold does not reach a one-line criterion.
> BSIXRUNG's (BE-239)(ii) was written from the clause layer and stated a
> population claim about a range whose **decisive sentence is off the clause
> layer**. (BE-231)(ii)'s lesson was *"a clause was minted whose refutation
> was already in a committed driver's output"*; this is its documentary twin
> — **a population claim was made about a range whose own refutation
> criterion was already written in that range, one heading away from the
> index.** The cost of the check was one `sed` of 28 lines.

---

### Step BE264 — (BE-265): THE SPEC'S DICHOTOMY IS THE DEFECT — five quantifier classes, and the two that decide the damage are neither pole

> **(BE-265)(i)** `[REFUTED]` *(the framing, refuted first and cheaply, as
> §7's amendment (a) requires)* The dispatch's candidate mechanism was that
> *"universal vs generic"* might not be a clean dichotomy per consumer, and
> asked for a **three-way** classification if a consumer needed the obligation
> on a characterized subfamily. **It is worse than three-way and the extra
> classes are not subfamilies at all.** Of the 44 obligation-naming clauses
> in the range, the **large majority carry a quantifier that is not over
> configurations in any form.** Five classes, mutually exclusive, each named
> by the quantifier the clause's **own** statement carries:
>
> | class | quantifier the clause carries | reached by the certificate? |
> |---|---|---|
> | **T — tuple space** | *"asserted at all **N** tuples of `barch.all_tuples()`"* — configuration-free | **NO** (the certificate realizes a tuple these clauses already count as violating) |
> | **C — configuration-universal THEOREM** | *"at **every** configuration … no genericity, no draw, no chart point"* | **NO** (proved; the certificate satisfies them) |
> | **P — named population, cap disclosed** | *"at **N of N** rows of `<builder>`", "not found under this cap"* | **NO** (different builder; the free-draw control agrees) |
> | **G — the target, at a GENERIC CHART POINT** | *"at a generic chart point with `a = 0`, side-degree `≥ 2`"* | **NO** — by (BE-264)(ii), by a proof |
> | **U — a status word that is a (Q-univ)** | *"UNREFUTED"*, *"remains UNPROVED"*, *"unrefuted"* | **YES** — 3 statements, all successors, none a consumer |
> | **E — EXISTENTIAL** | *"a row with `margin > 0` … **if it exists**, unexhibited"* | **YES, and it is DISCHARGED** — 1 item |
>
> **Neither pole of the spec's binary contains class E, and class E is where
> the round's result actually lands a change.**

> **(BE-265)(ii)** `[MEASURED]` *(class **T**, the bulk, with the count)*
> **18** of the 44 are tuple-space assertions over `barch.all_tuples()` or a
> slice of it — (BE-152)(i), (BE-153)(i), (BE-219)(ii)/(iii), (BE-220)(i)/(ii),
> (BE-223)(ii), (BE-225)(ii)/(iii)/(iv), (BE-226)(i)/(ii), (BE-227)(ii),
> (BE-228)(i), (BE-235)(i)/(ii), (BE-236), (BE-237)(iii) — the count taken
> **after** removing (BE-225)(i), which is class **C** by its own proof
> (*"at every configuration … no chart point"*) and only incidentally asserted
> over 630 tuples, and (BE-228)(ii), which is one of (BE-263)(iii)'s 13. A tuple-space
> statement is a statement about the finite index set
> `(δ₁,δ₂,a₁,a₂,ρ₁,ρ₂,c₁,c₂)`; a configuration certificate can only reach one
> by **realizing a tuple the statement calls impossible**, and none of these
> does. The reverse holds and is worth recording: the certificate's tuple
> `(2,4,0,0,2,4,2,1)` **confirms** three of them — it is one of
> (BE-227)(ii)'s 30 (`max(ρ₁,ρ₂) = 4 ≤ 5` ✓), one of (BE-239)(i)'s 26 in the
> `c = (2,1)` corner ((BE-250)(ii)(e) recomputes the 26 independently), and by
> (BE-235)(i) it is simultaneously a `(BE-OBL)` counterexample, which is the
> identity that clause asserts at all 141 rung-3 tuples.

> **(BE-265)(iii)** `[MEASURED]` *(classes **C** and **P**, and why a
> *"0 violations"* figure is not a (Q-univ))* Class **C** — (BE-225)(i)
> (*"`c₁ + c₂ ≤ 4` at **every** configuration … no genericity, no draw, no
> chart point"*), (BE-234) (*"at every configuration with no genericity, no
> degree condition and no draw"*), (BE-227)(i)'s (BE-95)(i) (*"for **every**
> `U`"*) — quantifies over **more** than the generic-flag stratum and is
> untouched because it is **proved and true at the certificate**: `c₁+c₂ = 3
> ≤ 4` ✓, `c₁ = 2 ≥ max(0, ρ₁−4) = 0` and `c₂ = 1 ≥ max(0, ρ₂−4) = 0` ✓.
> Class **P** — (BE-229)(i) (64 `plant_peel` rows), (BE-229)(ii) (135
> `free_peel` rows), (BE-229)(iii) (48 arc rows), (BE-231)(i), (BE-232)(i)/
> (ii)/(iii), (BE-233)(ii) — each states *"at N of N rows"* and **(BE-229)(ii)
> writes its own cap into the clause**: *"the reading is **"not found under
> this cap"**, never *"does not exist"*"*. A population measurement with a
> disclosed cap is **not** a (Q-univ) and cannot be refuted by a row outside
> its population. **The 135/135 is doubly safe**: `bproper.free_peel` draws
> **freely**, and BWHOLEH's own free-draw control on the same `H` gives the
> obligation **holding** ((BE-250)(iii), 6 of 6) — so the certificate
> **agrees** with the 135/135 rather than straining it.

---

### Step BE265 — (BE-266): THE DAMAGE, PRICED — three status words, all on SUCCESSORS, and not one consumer of the obligation loses a hypothesis

> **(BE-266)(i)** `[REFUTED]` *(class **U**, member 1 — and it is §8's own
> live slice)* **(BE-237)(i)** names `(BE-OBL7)` := `(BE-OBL) ∧ Σδ ≤ 7` and
> closes *"**UNREFUTED, and unproved**"*. `(BE-OBL)` is *"at an internal
> R-node peel in the generic flag regime, `c_i(Π_x) = 2` **and**
> `c_j(Π_x) ≥ 1` ⟹ `ρ_i = 6`"* ((BE-228)(i), quoted with its hypotheses).
> At the certificate: `c₁ = 2` ✓, `c₂ = 1 ≥ 1` ✓, internal R-node peel and
> generic flag regime gated ✓, `Σδ = 6 ≤ 7` ✓ — and `ρ₁ = 2 ≠ 6`. **So
> `(BE-OBL7)` is FALSE at the certificate**, i.e. **refuted as a (Q-univ)**.
> Arithmetic on a landed, already-asserted tuple; no new measurement.

> **(BE-266)(ii)** `[REFUTED]` *(class **U**, member 2)* **(BE-237)(ii)**
> names `(BE-OBLK)` := `(BE-OBL)` restricted to **side-degree `≥ 2` on both
> sides** and closes *"(BE-231)(i)'s witness does not reach it ((BE-232)(iii)),
> so it is **unrefuted**"*. The certificate's gate line reads
> `deg1x: 2, deg2x: 3` ((BE-249)(iii)), so side-degree `≥ 2` holds on **both**
> sides. **`(BE-OBLK)` is FALSE at the certificate**, and so is
> `(BE-OBL7) ∧ (BE-OBLK)` — **which (BE-237)(ii) calls *"the honest
> successor"* and which §8 carries as the live slice.** `(BE-232)(iii)`'s
> sentence stays true of **its own** witness (`deg₁(x) = 1` at 78/78); what
> changes is that a **second** witness now exists and does meet the habitat.

> **(BE-266)(iii)** `[REFUTED]` *(class **U**, member 3 — already retired, so
> the damage is bookkeeping)* **(BE-E4′)** is *"at an internal R-node peel
> with `δ₁ ≥ 1` and `δ₂ ≥ 1`, if `c_i(Π_x) = 2` for some side `i`, then
> `e₁ + e₂ ≥ 4`"* ((BE-162)(i)), carried as **UNPROVED** by (BE-162)(iii) and
> as *"SURVIVES its own tight boundary"* by (BE-177)(ii). At the certificate
> `δ₁ = 2 ≥ 1`, `δ₂ = 4 ≥ 1`, `c₁ = 2`, and `e_i = ρ_i − c_i(Π_x)` gives
> `e₁ = 0`, `e₂ = 3`, `e₁ + e₂ = 3 < 4`: **FALSE**. This is **predicted by
> (BE-219)(ii)** — *"at `a = 0` and `δ₁+δ₂ ≥ 6`, `(BE-E4′)` and the `Π_x`
> OBLIGATION are the SAME CONDITION"*, and `Σδ = 6` is exactly the boundary of
> that zone — so (BE-219)(ii) is **confirmed** by the certificate while
> (BE-162)(iii)/(BE-177)(ii)'s status word falls with it. The family was
> already **barred as a family** by (BE-224)(iii)(a), so nothing live is lost;
> the row is recorded because (BE-247)(iii) and (BE-253)(iii) both list
> `(BE-E4′)` as **untouched**.

> **(BE-266)(iv)** `[PROVED]` *(**the headline count, both directions**)*
> **Consumers of the `Π_x` obligation in *Steps BE148–BE237* that needed it
> as a (Q-univ) over the generic-flag stratum: ZERO.** Not one clause in the
> range assumes the obligation and derives anything from it — a
> case-insensitive scan of the ten files for *"under / assuming / by the
> obligation"*, *"the obligation holds/gives/implies/forces"* returns **three**
> lines, of which two are about a **successor's** strength and one is
> (BE-229)(i) reporting a **measured** hold. The obligation is, throughout
> this range, a **target** ((BE-230)(i), (BE-238)(i)), a **measured
> statistic** ((BE-229)), or the **consequent** of a sufficiency implication
> ((BE-226)(i), (BE-228)(i)) — never a hypothesis.
> **Statements in the range whose own status word is a (Q-univ) and which the
> certificate therefore reaches: THREE** — (BE-237)(i), (BE-237)(ii),
> (BE-162)(iii)/(BE-177)(ii) — **all three successors, none a consumer, and
> all three survive intact under (Q-gen).**
> **Consumers that needed only (Q-gen): FOUR**, all untouched ((BE-264)(i)).
> **So the round's headline refutation costs the (BE-14) arc nothing at the
> consumer layer**, and costs §8 exactly one thing: its live slice
> `(BE-OBL7) ∧ (BE-OBLK)` must now be **read at (Q-gen)** or it is refuted
> before it is attempted.

---

### Step BE266 — (BE-267): THE GAIN nobody counted — item 0(b) [MARGIN] is EXHIBITED, and steering is not a defect there but sufficient

> **(BE-267)(i)** `[CONSTRUCTED]` *(the certificate is BWHOLEH's and the driver
> is its — `notes/scripts/w4/bwholeh.py cross`, which prints and asserts both
> the tuple `(2,4,0,0,2,4,2,1)` and the `H`-layer reading `dim M(H) = 7`
> against `6 + def₃(H) = 6`; the margin below is **arithmetic on that asserted
> tuple**, not a fresh `bsatur.row_of` read, and that read is the confirmation
> this direction commissions rather than performs)* (the item, quoted with its
> own quantifier)
> `notes/Phase39.md` item 0 reads: *"**(b) [MARGIN]** a row with `margin > 0`
> at `Π_x`, `Π_y` or `⟨M⟩` — the arc's first **shortfall** if it exists,
> unexhibited at 54 rows ((BE-128)(i)), none new at BLINE or BDEGTWO"*. The
> margin is (BE-97)(ii)'s: `c₁(U) + c₂(U) − dim U − max(0, δ₁+δ₂−6)`. At the
> certificate, `U = Π_x`: `2 + 1 − 2 − max(0, 6−6) = **+1 > 0**`. **Item 0(b)
> [MARGIN] is EXHIBITED.** Independently and at the `H` layer rather than
> inferred through the tuple: **(BE-250)(i)** measures `dim M(H) = 7` against
> `6 + def₃(H) = 6`, *"`H` does **NOT** attain, with an excess of 1 motion"*,
> at 3 of 3 draws with every line an assert — and (BE-249)(ii) reports
> `H` attains **no, 72/72**.

> **(BE-267)(ii)** `[PROVED]` *(**why steering is irrelevant here**, and this
> is the class the dispatch's binary has no room for)* Item 0(b) is a
> **(Q-ex)**: *"a row … if it exists"*. A (Q-ex) is **discharged by any
> witness**, and a steered witness is a witness. The asymmetry is the same one
> (BE-69)(ii)'s consequence 2 states in the other direction — *"a draw
> outside `Good` settles nothing"* — read for an **existential about the bad
> locus** rather than for a claim about the good one. The corpus already
> uses exactly this asymmetry: (BE-160)(iii) *"item 0(b) [MARGIN] stays
> unexhibited: this refutes a **clause**, it does not exhibit a
> **shortfall**"* — a clause refutation and a shortfall exhibition are
> **different events with different quantifiers on the same row**, and
> BWHOLEH's row is the first in the thread that is **both**.

> **(BE-267)(iii)** *(**the five surfaces carrying the stale status**, split
> into dated and live)* *(a)* **DATED, and not to be rewritten** — five
> board rows that say *"item 0(b) [MARGIN] (still unexhibited)"* **as of
> their own landing**: (BE-160)(iii), (BE-162)(v), (BE-177)(iv),
> (BE-209)(vii), (BE-217)(vi). A *"what did not move"* row is a statement
> about its own commit and repointing it would falsify history; the right
> repair is a forward pointer, and that is the coordinator's call.
> *(b)* **LIVE, and stale now** — `notes/Phase39.md` item 0(b) (*"the arc's
> first shortfall **if it exists**, unexhibited at 54 rows"*) and
> `notes/pencil/strategy.md` §8's below-the-top-four list (*"the 12
> unwitnessed-not-excluded blocks and **item 0(b) [MARGIN]**, still
> unexhibited after this round"*). **Both are user-facing status surfaces and
> both are now wrong.** Naming them is this direction's deliverable; editing
> them is not ((BE-269)(iii)).

> **(BE-267)(iv)** *(the honest scope of (i), stated before anyone reads it
> as more than it is)* The margin figure is **arithmetic on a landed,
> already-asserted tuple**, not a fresh `bsatur.row_of` call — this direction
> shipped no driver and ran no measurement. `row_of` is *"undefined off the
> regime"* ((BE-208)(iv)) and the certificate's rows are **in**-regime at
> 72/72, so a `row_of` read is available and is the obvious confirmation to
> commission; until it is run, the claim rests on (BE-97)(ii)'s definition
> applied to (BE-249)(ii)'s tuple plus (BE-250)(i)'s independent `H`-layer
> shortfall. **Neither leg is a new measurement and both are landed.** What
> item 0(b) does **not** become is a refutation of anything: (BE-250)(i)'s own
> sentence — *"its scope is (BE-247)(i)–(ii)'s and no wider"* — stands, and a
> shortfall at one chart point of a piece with a dense `Good` reaches neither
> (BE-14) nor `hbareSplit` ((BE-247)(i)).

---

### Step BE267 — (BE-268): THE LANDED PRECEDENT — the corpus has run this exact experiment three times before and recorded the answer

> **(BE-268)(i)** `[PROVED]` *(**(BE-192)(ii) already states this direction's
> verdict as a general lesson**, one step inside the range and 46 steps before
> (BE-239)(ii) contradicted it)* **(BE-192)(ii)**, verbatim: *"**This is the
> third time on this thread that a degenerate-configuration witness has
> refuted a clause's universal form without touching its generic one** —
> (BE-104)/(BE-105) at *"a plane no sampler draws"*, (BE-107)(iii)/(BE-109) at
> the `-GEN` residual, and here — and the lesson is the one the `-CHART`
> repair already encodes: **the word *generic* in that clause is
> load-bearing**."* **BWHOLEH's steered certificate is the FOURTH**, and it is
> the first on the **two-sided** object rather than on the per-side clause.
> (BE-192)(iii) adds the qualifier that matters for the next dispatch: its own
> witness was *"**maximally degenerate**, which is exactly why it does not
> reach the generic clause — and a **less** degenerate witness is not
> excluded"*. BWHOLEH's is **less** degenerate (only side 1's `p_y` is
> steered; side 2 is `bproper.free_peel`'s own path-saturated draw), which is
> progress **toward** the generic question and not an answer to it.

> **(BE-268)(ii)** `[PROVED]` *(**the sibling half of the precedent** —
> a planted refutation of the pointwise form coexisting with a PROOF of the
> generic one, on the same strata, in the same direction)* (BE-192)(i) refutes
> `c_i(Π_x) = 2 ⟹ ρ_i = 6` at **24 of 24 fully gated** planted chart points;
> **(BE-193)(ii)** then **proves** the same implication *"holds on a DENSE
> OPEN subset of `Chart(H)`"* at arc length `≤ 3`, by confining the bad locus
> to `{q_y ∈ π_x}` — *"proper and inhabited"* ((BE-193)(i)) — and citing
> (BE-123). **Refuted pointwise and proved generically, one step apart.** So
> the corpus's own answer to *"does a gated planted/steered witness settle the
> object?"* is a landed **no**, with a worked positive on the other side; and
> (BE-229)(i)'s parenthesis says it in one line for the obligation's own
> population: *"(These rows are **planted**, so they do not refute item 0(a),
> **which is generic**; they exhibit the gap.)"*

> **(BE-268)(iii)** *(**the generalizable lesson**, one level above the
> instance)* (BE-245)(iv) said *"when a region is entered by removing a
> hypothesis, re-run the mechanism census asking which mechanisms never needed
> that hypothesis"*. The sequel here is about **quantifiers rather than
> mechanisms**, and it bites on the surface a corpus indexes rather than on
> its mathematics: **a claim about how a POPULATION OF CLAUSES is quantified
> must be taken at the population, and the population includes the surfaces
> the index cannot see.** (BE-239)(ii) was written from the clause layer,
> where every neighbouring row is an exhaustion over tuples and the
> (Q-univ) reading is the natural one; the range's four (Q-gen) sentences sit
> in **verdict** clauses and in one **un-indexed heading block**, which is
> precisely where a direction working from `--brief` does not look. The
> operational form: **before asserting how "every consumer" uses an object,
> list the consumers with the tool AND read the range's own verdict and
> "what would change this" blocks — the quantifier a range actually commits
> to lives in its verdicts, not in its lemmas.**

---

### Step BE268 — (BE-269): the verdict, the board, the bars, the E-rider

> **(BE-269)(i)** `[REFUTED]` *(**the verdict**)* **(BE-239)(ii)'s
> *"which is how every consumer in *Steps BE148–BE237* uses it"* is REFUTED**,
> by four landed sentences inside its own range ((BE-264)(i)), one of which is
> the obligation's owning direction's own refutation criterion and which the
> certificate misses by the single conjunct *generic* ((BE-264)(iii)). The
> damage from BWHOLEH's headline result, priced in both directions:
> **ZERO consumers of the obligation lose a hypothesis** — none ever assumed
> it ((BE-266)(iv)); **THREE successor status words** fall as (Q-univ) and
> survive as (Q-gen) — `(BE-OBL7)`, `(BE-OBLK)`, `(BE-E4′)` ((BE-266)(i)–
> (iii)); and **ONE existential item is DISCHARGED** — item 0(b) **[MARGIN]**
> ((BE-267)). **The target itself — (BE-230)(i)/(BE-238)(i)'s naked `Π_x`
> obligation at a generic chart point with `a = 0` and side-degree `≥ 2` —
> stays exactly where BCORNER left it: OPEN**, and (BE-264)(ii) proves it is
> untouched rather than merely unrefuted. **No gap-map status word moves for
> the obligation. `hK` is not closer.**

> **(BE-269)(ii)** *(**the board**)* **What moved.** (BE-239)(ii)'s
> population sentence **REFUTED** ((BE-264)(i)); the obligation's failure
> locus at BWHOLEH's own `H` **PROVED nowhere dense** ((BE-264)(ii));
> `(BE-OBL7)` and `(BE-OBLK)` **REFUTED as universals**, and with them
> (BE-237)(ii)'s *"honest successor"* `(BE-OBL7) ∧ (BE-OBLK)` — §8's live
> slice ((BE-266)(i)/(ii)); `(BE-E4′)`'s *"UNPROVED"* **resolved to REFUTED as
> a universal**, confirming (BE-219)(ii) ((BE-266)(iii)); **item 0(b)
> [MARGIN] EXHIBITED** for the first time in the thread ((BE-267)); the
> quantifier taxonomy of the range **measured at five classes**, refuting the
> dispatch's binary ((BE-265)); (BE-192)(ii)'s *"third time"* count
> **advanced to a fourth** ((BE-268)(i)). **What did NOT move.**
> `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`, (GR-15), (BE-14), the
> S-mark, half (B), half (β), the 2-cut step, class uniformity, cross-pair
> welding, the flag base, (BE-101)(iii), the 12 unwitnessed-not-excluded
> blocks, (BE-230)(i)/(BE-238)(i)'s OPEN verdict on the obligation, and
> **every landed measurement** — including (BE-229)(ii)'s 135/135,
> (BE-229)(iii)'s 48/48, (BE-231)(i)'s 62 of 78 and (BE-249)(ii)'s 72/72,
> every one of which this direction **reproduces the reading of or leaves
> intact** rather than contradicts. **No `.lean` opened, no `lake build`, no
> driver shipped, no tracked file edited**; the 2026-08-05 hold untouched.
> **The E-rider:** no termination-ledger entry fires; E1/E2/E3 are §(K-grid)
> objects and are untouched. **Not a PENCIL event.**

> **(BE-269)(iii)** *(**the bars this adds**, as §8's rule requires)*
> *(a)* **No status word of the form *"UNREFUTED" / "unrefuted" / "remains
> UNPROVED"* may be written for a clause over a chart stratum without saying
> **at which quantifier**** — (Q-univ), (Q-gen) or (Q-ex). Three such words
> in this range fell to one certificate, and all three would have survived
> verbatim had they carried *"generically"*. *(b)* **No claim about how a
> RANGE of clauses is quantified may be taken from the clause layer alone** —
> the range's `### Confidence verdict` and `### What would change this` blocks
> are not indexed by `ledger.py` and carried the decisive sentence here
> ((BE-264)(iv)); read them, or say the claim was taken from the index only.
> *(c)* **No steered or planted witness may be read as settling an object
> stated at (Q-gen)**, and conversely **no (Q-ex) item may be left standing
> as unexhibited once such a witness exists** — the asymmetry is (BE-69)(ii)'s
> consequence 2 read in both directions, and this round produced one instance
> of each on the **same row** ((BE-267)(ii)). BSIXRUNG's three
> ((BE-245)(iii)(a)/(b)/(c)), BOBLIG's three, BCORNER's three, BNONUNI's
> three, BGTWOA's three, BEFOURP's three and BLONGARC's four stand unchanged;
> (BE-230)(iii)(a)/(b)/(c) and (BE-238)(iii)(a)/(b)/(c) stand.

---

### Step BE269 — (BE-270): the dispatch's prediction, scored — verdict and mechanism separately, per §7

> **(BE-270)(i)** *(**VERDICT: CONFIRMED, and for a reason the spec did not
> have**)* The spec predicted *"MOST consumers needed only the GENERIC form,
> so the refutation's cost to the arc is small"* from the thinnest possible
> stratum — (BE-69)(ii)'s upgrade mechanism, with no consumer re-read. **The
> verdict is CONFIRMED and is stronger than predicted: not "most" but
> ALL** — zero consumers needed (Q-univ) ((BE-266)(iv)), because zero
> consumers **consume** the obligation at all in this range.

> **(BE-270)(ii)** *(**MECHANISM: REFUTED**, and this is where the
> mathematics was)* The spec's stated reason was *"the arc's dominant proof
> pattern is per-piece generic, and (BE-69)(ii)(1) is exactly the device that
> licenses one draw to stand for the generic configuration — so consumers are
> more likely phrased that way."* **That is not why the verdict holds.**
> (BE-69)(ii) is a statement about `Good`, i.e. about **attainment**, and no
> consumer in the range invokes it for the obligation; the range's own
> quantifier discipline comes from a **different** landed lesson —
> (BE-192)(ii)'s *"the word *generic* in that clause is load-bearing"*, itself
> inherited from the `(PENCIL-SATURATES-CHART)` repair ((BE-113)/(BE-127)) —
> and the operative fact is not that consumers are *"phrased"* generically but
> that **the obligation is never consumed at all**: it is a target, a measured
> statistic, or a consequent. The mechanism is eliminated, per §7's amendment
> (a), and was not allowed to carry the first slice: (BE-264)(i)'s four
> quotations were taken before (BE-69)(ii) was used anywhere, and (BE-69)(ii)
> enters only at (BE-264)(ii), as one leg of a proof about a **single** `H`.

> **(BE-270)(iii)** *(**TELL: it FIRED, and it COULD have** — §7's amendment
> (b) asks both)* The spec's tell was *"one consumer whose statement
> quantifies over the STRATUM rather than over a chart point"*, region *"the
> consumer clauses themselves in Steps BE148–BE237"*. **It fired three
> times** — (BE-237)(i), (BE-237)(ii), (BE-162)(iii)/(BE-177)(ii) — and the
> region **could** have produced a different verdict: had any of the four
> class-**G** sentences read *"over the generic-flag stratum"* instead of
> *"at a generic chart point"*, the damage would have been real and the
> target closed. The tell was **live**, **not already satisfied** (nobody had
> classified a single consumer), and **satisfiable** (the set is finite and
> landed). **But the tell under-samples its own region in one direction the
> spec could not have known:** all three firings are **successors**, not
> consumers, so the tell as worded would have scored *"damage found"* on a
> population the question was not about. The correction is (BE-266)(iv)'s
> split of the count into *consumers* and *status words*.

> **(BE-270)(iv)** *(**the spec's own "where I expect to be wrong", scored** —
> it named the right sentence and drew the right conclusion from it)* The
> spec wrote: *"A landed sentence says the opposite of my prediction.
> (BE-239)(ii) records the universal reading as *"how every consumer in Steps
> BE148–BE237 uses it"*. If that sentence is right, I am wrong at **every**
> consumer. So your first job is to test that sentence."* **That instruction
> was correct and is the whole of this direction's value.** The sentence is a
> **population claim, in prose, with no driver** — the class the spec named
> and the class this round has now refuted **four** times. The spec's own
> hedge *"do not assume it is wrong either"* was also right: (BE-239)(ii) is
> **true of the tuple-space and population clauses it was written next to**,
> and false only as a statement about *every* consumer. **What the spec got
> wrong is the shape of the answer, not its direction**: it asked for a
> binary or at worst a three-way subfamily split, and the honest object is a
> five-class taxonomy in which the decisive class — the **existential** item
> 0(b) — is not a weakening of either pole but a **gain**, and was not on the
> board at all.

> **(BE-270)(v)** *(**what this direction self-caught**)* *(1)* The first
> pass conflated **half (B)'s item 0(a)** — `(PENCIL-SATURATES)` at
> side-degree `≥ 2` — with the **`Π_x` obligation**, because 13 of the
> keyword scan's hits name the first and the two are one implication apart;
> (BE-223)(ii)'s *"strictly weaker … at 98"* is what caught it, and
> (BE-263)(iii) now lists the 13 explicitly. *(2)* The first enumeration used
> `--cited-by` alone, as the dispatch spec directed, and **missed BOBLIG's
> refutation criterion entirely** — the single most decisive sentence in the
> range — because it is not a `> **(LABEL)**` blockquote; (BE-263)(ii)
> records that the named generator is insufficient on **this** object and
> why. *(3)* `(BE-OBL7)`/`(BE-OBLK)`/`(BE-E4′)` were initially going to be
> reported as *"contradictions in (BE-253)(iii)'s board"*; they are not —
> BWHOLEH's board is consistent **provided** those three are read at (Q-gen),
> which is exactly the reading this direction argues for, so the honest
> report is a missing qualifier and not an error. *(4)* Item 0(b) was found
> **last**, from a stale *"still unexhibited"* phrase in an out-of-scope
> false-positive clause ((BE-209)(vii)), i.e. from the debris of correction
> (1) — the conflation that cost two probes is what produced the one result
> that moves a live status surface.

---

### Confidence verdict (Steps BE262–BE269)

**(BE-239)(ii)'s population sentence: REFUTED — HIGH confidence.** Four
verbatim quotations from landed clauses inside the named range, three of them
verdict clauses, one of them the owning direction's refutation criterion. The
quotations are the evidence and they are reproducible in one `sed` each.
**The damage count: HIGH confidence on the *zero consumers* half** (a
case-insensitive scan of the ten files for every "assume/under/by the
obligation" phrasing returns three lines, none of them a consumption) and
**HIGH on the three status words** (arithmetic on a landed asserted tuple
against three verbatim clause statements). **Item 0(b) [MARGIN] EXHIBITED:
MEDIUM-HIGH** — the margin is arithmetic on (BE-249)(ii)'s tuple rather than a
fresh `bsatur.row_of` read, and (BE-250)(i) independently measures the
shortfall at the `H` layer; the residual risk is that item 0(b)'s intent was
a shortfall at a **generic** point, which its own wording does not say.
**The five-class taxonomy: MEDIUM** — the class boundaries are this
direction's, not the corpus's, and a coordinator may prefer four or six.

### What would change this (Steps BE262–BE269)

- **A consumer in *Steps BE148–BE237* that assumes the obligation and derives
  something from it**, phrased over the generic-flag stratum, found under one
  of (BE-263)(iv)'s three escape routes. That would move the *zero* to a
  positive number and is the only finding that makes the round's headline
  cost the arc anything.
- **A `bsatur.row_of` read at the certificate** returning a margin `≤ 0` at
  every one of the 16 stable blocks would refute (BE-267)(i) and leave item
  0(b) unexhibited. (BE-250)(i)'s `H`-layer shortfall makes that unlikely but
  it is the check that closes the question.
- **A statement of item 0(b) that carries a genericity hypothesis** — none is
  in `notes/Phase39.md`, `strategy.md` §8 or the five board rows — would move
  it from class **E** to class **G** and withdraw (BE-267).
- **A ruling that `(BE-OBL7)`/`(BE-OBLK)` were always meant at (Q-univ)**
  would make (BE-266)(i)/(ii) a genuine kill of §8's live slice rather than a
  missing qualifier, and §8 would lose its named first slice a second time.

---
