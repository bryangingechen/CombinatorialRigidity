## §(K-bare-ext) — continuation (direction BSIGMA): **BSATUR's OWN NAMED RESIDUAL IS REALIZED, SO (PENCIL-SATURATES-GEN) IS FALSE TOO — AND ITS FLOOR IS A THEOREM** — the shape (BE-107)(iii) named and measured absent, `Σ_x ⊆ ρ̄_i` at `ρ_i = 5`, is exhibited on **BSATUR's own pinned peel** `K4(5,3,3,3,3,3)`: place the peeled 5-branch so that `p_x` and every one of its points *except the neighbour of `x`* lie in one plane `π`, and then `ρ̄₁ = ⟨ℓ₁, ℓ₂⟩ ⊕ Λ²π` contains `p_x ∧ π` **and** `ℓ₁ = p_x ∧ p_{b₀}`, whose span is `p_x ∧ (π + ⟨p_{b₀}⟩) = Σ_x` — so **every** plane through `p_x` is bad, legal or not, and no genericity in the **flag** saves the repair. The peel is R-node-shaped, passes both gates, and sits in the **generic flag regime** — which it does for a structural reason worth naming: **both** terminals of the peeled branch are series ends, so side 1 never forces `π_y`. **The price is SLACK, not a shortfall, for the third time running** — `margin ≤ 0` at four blocks and `reach = min(δ₁+δ₂,6)+a₁+a₂` asserted at **78** exhibited rows over **39** constructed profiles, **0** shortfalls — so half (B) is **not** refuted, exactly as BDOUBLE's and BSATUR's refutations were not. **And the failure locus is pinned again, this time by a proved identity**: projection from `p_x` is the linear map `ω ↦ ω ∧ p_x` whose kernel is exactly `Σ_x`, so `dim(ρ̄ ∩ Σ_x) = ρ − dim(ρ̄ ∧ p_x)`; at a **path** side the image is the span of the projected consecutive-pair lines, `dim ≤ 1` forces every point into one plane with `p_x` and caps `ρ` at `3`, and hence **`Σ_x ⊆ ρ̄_i ⟹ ρ_i ≥ 5` is PROVED, not measured**. Below `ρ_i = 5` the shape is reached only at sides with `deg_i(y) ≥ 2`, and there — at **8 of 8** exhibited `ρ_i = 4` rows — `p_x` lies in the plane the side *itself* forces on `y`, i.e. `p_x ∈ π_y`: **off the generic flag regime**, which is BSATUR's own structural warning firing on a hit rather than on a construction. **The forced support audit answers sharply**: (BE-105)(ii)'s battery has **exactly five** `deg = 1` terminals and they are the **five path pieces**, one configuration each, every one **generic** — so `ρ = 5 ↦ 2, never 3` was a statement about *generic configurations of a path*, and the quantifier this direction rides is the **configuration stratum**, not the flag. That identity is true where it was measured — its `≤` half is upgraded here from MEASURED to **PROVED** at a generic path configuration — and false one stratum away. **The repair repaired is (PENCIL-SATURATES-CHART)**, the clause at a generic **point of `Chart(H)`** rather than at a generic flag of an arbitrary configuration, and it is free by the **same** (BE-16) + (BE-69) argument BSATUR used — with one thing BSATUR did not have: the bad locus is now **proved** proper, not measured proper *(the (BE-69) half of that argument is **CORRECTED 2026-09-02**: it is the wrong citation and is not needed — (BE-122)/(BE-123) — and the clause is a **THEOREM** at every side-degree-`1` terminal, (BE-127))*

### Standing notation

BSATUR's, unchanged (*Steps BE103–BE107*): `H` an internal R-node piece peeled
at `{x, y}`, sides `H₁, H₂`, `ρ̄_i`, `ρ_i`, `δ_i`, `a_i`, blocks
`Π_x, ⟨M⟩, ⟨L⟩, Π_y`, `c_i(U) = dim(ρ̄_i ∩ U)`, `Σ_z = p_z ∧ K⁴`, and *the bad
plane at `x`* as prose. Two further pieces of vocabulary are used, both
descriptive and neither minted as a token:

- **the tail stratum** — prose for the configurations of a `deg_i(x) = 1`
  terminal in which `p_x` and every point of the side *except* the neighbour
  `c₁` of `x` lie in one plane `π`. It is a stratum of the piece's
  configuration space, not an object.
- **the projected pair lines `L_j`** — prose for the images of the chain's
  hinge lines under `ω ↦ ω ∧ p_x`, i.e. the lines of consecutive points seen
  from `p_x`.

One name is minted, and like BSATUR's it is a **condition**, not an object:
**(PENCIL-SATURATES-CHART)**, the twice-repaired clause.

### Step BE108 — (BE-109): the residual is REALIZED, and the witness is BSATUR's own peel

> **(BE-109)(i)** *(**THE HIT**, exhibited at the peel BSATUR pinned)* Take the
> subdivided `K₄` skeleton with profile `(5,3,3,3,3,3)`, peeled at the skeleton
> edge `{A,B}` carrying the 5-branch — **`K4(5,3,3,3,3,3)`, (BE-104)(i)'s own
> witness peel, unchanged**. Side 1 is that branch,
> `x = A, b₀, b₁, b₂, b₃, y = B`, so `deg₁(x) = deg₁(y) = 1`. What is new is
> the **configuration**: draw a plane `π`, place
>
> **`p_x, p_{b₁}, p_{b₂}, p_{b₃}, p_y ∈ π` and `p_{b₀} ∉ π`,**
>
> and draw everything else (the other two hubs, the five other branches, the
> hub flags) freely. Then, all **asserted**, not reported:
>
> - the configuration passes `assert_generic_star` **and**
>   `kbare_common.verify_pencil_witness` (`bdecor.assemble`'s two gates);
> - the flag pair is in the **generic regime** (`bunif.flag_frame` non-`None`);
> - `ρ₁ = 5`, `δ = (5,3)`, `a = (0,0)`;
> - **`Σ_x ⊆ ρ̄₁` as SPACES**, i.e. `dim(ρ̄₁ ∩ Σ_x) = 3`;
> - hence `c₁(Π_x) = 2` at the closed-star plane `plane_at(H, x)` **and at 24
>   further planes through `p_x` drawn at random** — every plane through `p_x`
>   is bad, legal or not;
> - the peel **ATTAINS**: `reach = min(δ₁+δ₂,6) + a₁ + a₂ = 6`.
>
> Measured at **6 of 6** independent seeds. **(PENCIL-SATURATES-GEN) is
> FALSE.** **F13 negative control**: the *same* peel drawn by
> `bsatur.draw_peel` gives `dim(ρ̄₁ ∩ Σ_x) = max(1, ρ₁ − 3)` at every draw and
> **0** hits — which is the whole explanation of (BE-105)(ii)'s measurement.

> **(BE-109)(ii)** *(the arithmetic, which is one line and needs no draw)*
> Since `p_{b₁}, p_{b₂}, p_{b₃}, p_y ∈ π`, the three hinge lines
> `ℓ₃, ℓ₄, ℓ₅` lie in `π` and span `Λ²π` unless they are concurrent, which
> `p_{b₂} ≠ p_{b₃}` forbids. Since `p_{b₀} ∉ π`, both `ℓ₁ = p_x ∧ p_{b₀}` and
> `ℓ₂ = p_{b₀} ∧ p_{b₁}` are of the form `p_{b₀} ∧ w`, and
> `⟨ℓ₁, ℓ₂⟩ ∩ Λ²π = 0`. So `ρ̄₁ = ⟨ℓ₁, ℓ₂⟩ ⊕ Λ²π` and `ρ₁ = 5` exactly.
> Finally `p_x ∈ π` gives `Λ²π ∩ Σ_x = p_x ∧ π` (dimension 2), and
>
> **`(p_x ∧ π) + ⟨p_x ∧ p_{b₀}⟩ = p_x ∧ (π + ⟨p_{b₀}⟩) = p_x ∧ K⁴ = Σ_x`. ∎**
>
> No genericity, no draw; the seeds supply only the **realizability** of a peel
> meeting the hypotheses.

> **(BE-109)(iii)** *(what is refuted, and what is NOT — said before anything
> else, as (BE-104)(ii) did)* **Not** `PencilPair K 3 G`; **not** half (B) —
> the witness peel **attains** ((BE-112)(i)); **not** (BE-101)(i) as an
> implication, whose content is *"given the clause"*; **not one landed
> measurement** — BSATUR's 260 bad-flag rows, the 24-piece threshold, the
> `⟨M⟩` census, every `92/92` and `300/300` in *Steps BE93–BE108* stand,
> because each was taken at a **drawn configuration** and the hit lives at a
> configuration no sampler draws. What falls is **(PENCIL-SATURATES-GEN) as a
> statement about every legal configuration**, and with it (BE-107)(i)'s
> licence read pointwise in the configuration. This is the **third** landing in
> a row whose refutation is a quantifier the previous landing's sampler never
> ranged over ((BE-45)(iii) at configurations, (BE-104) at flags, here at
> configuration **strata**) — and the first where the previous landing *named
> the shape in advance*.

> **(BE-109)(iv)** *(the shape is a FAMILY, not an instance — and the one
> thing it is NOT measured to be)* The same placement works at every peeled
> branch of length `L ≥ 5`, because `ρ̄₁ = ⟨ℓ₁, ℓ₂⟩ ⊕ Λ²π` is independent of
> `L` once `L ≥ 5`: **the tail stratum caps `ρ₁` at `5` and never reaches
> `6`**, asserted at every coplanar-tail draw of *mech* (`L = 3..7`, **30**
> draws), and it fires at `L = 5, 6, 7` (**24** planted rows in *floor*). So
> the hit is not a corner of one profile; it is a codimension-1 stratum present
> at every series end long enough to carry it, and the peel it sits in is a
> general internal R-node peel whose *other* side is arbitrary. **What is NOT
> shown: that the stratum exists at a non-path side.** The planted sampler
> draws at **5 of 16** bucket-A topologies — every hub-carrying side rejects
> it, disclosed row by row in *floor*'s output — so at a side that is not a
> path the shape is **unmeasured, not excluded**. That does not weaken the
> refutation (side 1 of an internal R-node peel *is* a branch here, the same
> series-end class BSATUR's refutation lives in); it bounds the generality
> claim, and it is the cap a successor would attack first.
> ***REPAIRED 2026-09-02 by (BE-117): the obstruction was ONE LINE of
> `sample_side_config` — a hub inside the planted plane received a random
> flag, collapsing its neighbours onto a line — and with that line repaired
> the stratum draws at 16 of 16 bucket-A topologies and fires at 11, EIGHT of
> them NOT paths ((BE-118) then realizes it at `ρ_i = 4` in the generic flag
> regime). The cap was a property of the sampler, not of the geometry.***

### Step BE109 — (BE-110): the mechanism, the corank identity, and the FLOOR — which is a theorem

> **(BE-110)(i)** *(proven; **THE CORANK IDENTITY**, and it holds at any side)*
> The map `q̂ : Λ²K⁴ → Λ³K⁴`, `ω ↦ ω ∧ p_x`, is linear with **kernel exactly
> `Σ_x`** (a 2-vector annihilates `p_x` iff it is `p_x ∧ (·)`). Hence for any
> subspace `ρ̄`,
>
> **`dim(ρ̄ ∩ Σ_x) = ρ − dim(ρ̄ ∧ p_x)`,**
>
> so `Σ_x ⊆ ρ̄` ⟺ `dim(ρ̄ ∧ p_x) = ρ − 3`. Asserted at every draw of *mech*
> and *floor*. `q̂` is the projection of `P³` **from the point `p_x`**: it sends
> the hinge line `p_a ∧ p_b` to the line of `\bar p_a, \bar p_b` in the
> quotient plane, so the whole question is *what the side looks like seen from
> `p_x`*.

> **(BE-110)(ii)** *(**THE FLOOR**, proved for a path side — `ρ_i ≥ 5`)* Let
> `x` be a `deg_i(x) = 1` terminal whose side is the path
> `x = v₀, v₁, …, v_L = y`. Then `ρ̄_i = ⟨ℓ₁, …, ℓ_L⟩` (a path is a tree, so
> the multipliers are free — (BE-30)), and `ℓ_j ∧ p_x = L_j`, the projected
> pair line, with `L₁ = 0`. Suppose `Σ_x ⊆ ρ̄_i`; by (i), `dim⟨L_j⟩ = ρ_i − 3`.
>
> - `dim⟨L_j⟩ = 0` is impossible: it forces `\bar p₁ = \bar p₂`, i.e.
>   `p_x, p₁, p₂` collinear, which `assert_generic_star` forbids at `v₁`.
> - `dim⟨L_j⟩ = 1`: every nonzero `L_j` is one line `λ` of the quotient plane
>   and every vanishing one identifies its two endpoints, so by connectivity of
>   the index chain **every** `\bar p_j` lies on `λ` — i.e. every point of the
>   path lies in the plane `π = ⟨p_x, λ⟩`, `p_x` included. Then
>   `ρ̄_i ⊆ Λ²π` and `ρ_i ≤ 3`, so `dim(ρ̄_i ∩ Σ_x) = ρ_i − 1 ≤ 2 < 3`.
>   Contradiction.
>
> Hence `dim⟨L_j⟩ ≥ 2` and `ρ_i ≥ 5`. ∎ Both steps are **asserted** in *mech*
> (at **30** deliberately flat draws for the second), and the conclusion at
> every one of **90** path draws. **The residual therefore sits at exactly one
> value of `ρ_i` at a path side, `5`, precisely as (BE-105)(ii) put the
> original failure at exactly one** — and (BE-107)(iii)'s *"impossible below
> `ρ_i = 3`"* is improved from `3` to `5` on that class.

> **(BE-110)(iii)** *(the same identity **proves** (BE-105)(ii)'s measured half
> at a generic path configuration)* At a path side with `L ≥ 4` and the
> projected points `\bar p₁, …, \bar p_L` in general position, `L₂, L₃, L₄` are
> three lines with `L₂ ∩ L₃ = \bar p₂` and `\bar p₂ ∉ L₄`, hence
> non-concurrent, hence `dim⟨L_j⟩ = 3` and `dim(ρ̄ ∩ Σ_x) = ρ − 3`; at `L = 3`
> the two lines give `dim⟨L_j⟩ = 2` and `dim = 1`. That is exactly
> `max(1, ρ − 3)`. **So (BE-105)(ii)'s `≤` half, listed there as MEASURED, is
> PROVED on the class its battery actually ranged over** — which is (BE-111)'s
> point, and is why the landed number was right and the sentence around it was
> not.

> **(BE-110)(iv)** *(**below `ρ_i = 5`, and the REGIME GATE** — a hit that
> proves nothing, exhibited on purpose)* At a side with `deg_i(y) ≥ 2` the
> floor **fails**: on `pendant + cycle(8)` (a pendant `x–c` with `c, y`
> antipodal on an 8-cycle), planting the tail stratum gives `ρ_i = 4` with
> `dim(ρ̄_i ∩ Σ_x) = 3`, at **8 of 8** draws. **It proves nothing about the
> repair, and the reason is the one BSATUR named**: the stratum puts `p_y` and
> *both* of `y`'s side-`i` neighbours in `π`, they are non-collinear
> (`assert_generic_star` at `y`), so the **side alone forces `π_y = π`** — and
> `p_x ∈ π`. Hence `p_x ∈ π_y` and `bunif.flag_frame` returns `None`: the
> configuration is **off the generic flag regime**, where the whole block law
> lives ((BE-98)). Asserted at **8 of 8** such rows. **The witness escapes this
> exactly because `deg₁(y) = 1` too** — two points do not span a plane, so side
> 1 leaves `π_y` to side 2 ((BE-70)(ii)), asserted at every witness seed. The
> honest reading: *`deg_i(y)` is the gate on whether a tail-stratum hit is a
> hit at all*, and it is the same "check the ambient before the statement"
> discipline (`RESEARCH-ARC.md` §7's seventh kind), applied to one's own
> positive result.
>
> **Verdict on `ρ_i ≤ 4` (F11):** in the bucket a peel in the generic flag
> regime can present (`deg_i(y) = 1`), **none found** at a cap of **668** rows
> over **16** topologies — never *"does not exist"* — and at a path side
> **impossible** by (ii).
> ***REFUTED 2026-09-02 by (BE-118): a witness at `ρ₁ = 4` with
> `deg₁(x) = deg₁(y) = 1` and `flag_frame` non-`None`, on a constructed peel
> whose side 2 is R-node-shaped — 21 rows. The 668-row cap was honest and the
> sampler behind it could not reach the shape ((BE-117)). This item's
> STRUCTURAL reading — that `deg_i(y)` is the regime gate — is CONFIRMED by
> that witness, which lives in bucket A precisely because side 1 leaves `π_y`
> free; and (ii) is a PATH theorem, untouched.***

### Step BE110 — (BE-111): the support audit — what (BE-105)(ii)'s battery actually ranges over

> **(BE-111)(i)** *(**the audit**, read off the driver body, not its
> docstring)* `bearcase.piece_battery()` returns **24** pieces;
> `bsatur.run_mech` branches on `deg(u)` and asserts the threshold identity at
> the `deg = 1` ones. Enumerated: `deg(u) = 1` at **exactly 5** of the 24, and
> they are
>
> > *path of 3 edges*, *path of 4 edges*, *path of 5 edges*, *path of 6 edges*,
> > *path of 7 edges*
>
> — **one topological family**, in which the side *is* the path and both
> terminals are series ends. The other 19 are thetas, cycles at antipodes and
> subdivided `K₄`/prism/`K_{3,3}`, all with `deg(u) ≥ 2`. Inside each of the
> five, `run_mech` keeps **one** configuration: the arg-max of `ρ` over at most
> six draws of `bearcase.sample_piece_config`, whose coordinates are
> `rq(rng, s)` — **uniform on a box** — so every kept configuration is
> **generic**. Asserted here by re-running it: `ρ → dim` comes back
> `3↦1, 4↦1, 5↦2, 6↦3`, **(BE-105)(ii) reproduced verbatim**.

> **(BE-111)(ii)** *(**which of the claim's own variables the support varies**
> — the `RESEARCH-ARC.md` §4 rider, answered)* The claim
> `dim(ρ̄_i ∩ Σ_x) = max(1, ρ_i − 3)` has three variables: the **piece**, the
> **configuration**, and the **flag**. The battery varies the piece *within one
> family*; it varies the configuration only in the sense of taking a generic
> one; and it does not vary the flag **because the flag is not a variable of
> this claim at all** — `Σ_x = p_x ∧ K⁴` depends on `p_x` alone, and `ρ̄_i` on
> the points alone. **That is the audit's sharp answer, and it is the opposite
> of BSATUR's case**: BSATUR found an assert whose sampler never moved the
> flag, and the counterexample sat at a flag; here the flag is irrelevant and
> the missing quantifier is the **configuration stratum**. Both are the same
> failure — *an in-driver assertion is only as strong as the distribution it
> runs under* — reached through different variables, and the hunt started
> exactly where the slice ended: at a **non-generic configuration of a path**.

> **(BE-111)(iii)** *(the identity's honest status after the audit)* `ρ = 5 ↦
> 2, never 3` is **true and now proved** at a generic configuration of a path
> side ((BE-110)(iii)) and **false** on the tail stratum, asserted at **6**
> draws where `ρ = 5` and `dim = 3`. So the landed number was never wrong; the
> sentence *"asserted at every `deg = 1` terminal of the battery"* over-read a
> **generic-configuration** statement as one about all legal configurations.
> That is (BE-105)(iii)'s own diagnosis of (BE-38)(iii), one variable further
> along — and the arc has now made this mistake at **four** consecutive levels
> ((BE-36), (BE-45)(iii), (BE-104), here). **The pattern is worth stating as a
> standing caution rather than a fourth incident**: in this workbook a summary
> sentence that quantifies *"at every X of the battery"* means *"at the one
> generic draw the battery kept for each X"*, and only a driver that plants a
> stratum on purpose says otherwise.

### Step BE111 — (BE-112): the price, and (PENCIL-SATURATES-CHART)

> **(BE-112)(i)** *(measured; **the hit is on the SLACK side**, as BDOUBLE's
> and BSATUR's were)* Over **39** constructed profiles — subdivided `K₄` with
> the peeled branch at `5` and the other five in `{3,4,5}`, plus prism and
> `K_{3,3}` with one branch at `5` — **2** draws each, **78** drawn rows,
> **every one** a hit row (`Σ_x ⊆ ρ̄₁` at `ρ₁ = 5`, asserted). At every one,
> **asserted**: `margin ≤ 0` at `Π_x`, `Π_y`, `⟨M⟩` and `Λ²K⁴`, and
> `reach = min(δ₁+δ₂,6) + a₁ + a₂`, so the peel **ATTAINS**. Margin histogram
> at `Π_x`: `{−3: 66, −2: 12}`; `(c₁, c₂)` at `Π_x`:
> `(2,0): 16, (2,1): 8, (2,2): 54`. **0 shortfalls**, and `Π_x` is **never**
> tight in this population. So half (B) is **not** refuted, and the
> coordinator's pre-priced reading — *"it would not refute half (B); say so
> explicitly"* — is **confirmed**, for the third direction running.

> **(BE-112)(ii)** *(**what it does cost**, and it is not a new number)*
> (BE-106)(ii)'s enumeration is **unchanged** and needs no re-run: with the
> clause replaced by its measured floor `c_i(Π) = 2 ⟹ ρ_i ≥ 5`, **24** `Π_x`
> violations escape `U = Λ²K⁴`, against **0** under the landed clause and
> **313** under none. What BSIGMA moves is **which row of that table applies at
> a generic flag**. Before: the top row, because (BE-107)(i) licensed the
> clause there. After: the **middle** row, for any statement quantified over
> configurations — because the bad configurations are not avoided by choosing a
> generic *flag*. Under (PENCIL-SATURATES-CHART) it is the top row again. The
> live-block count therefore reads three ways, and (BE-106)(iii) should be read
> with the third line added: **14** pointwise in the flag; **14** pointwise in
> the configuration at a generic flag *(new)*; **12** at a generic point of the
> chart.

> **(BE-112)(iii)** *(**(PENCIL-SATURATES-CHART)**, and why the arc may still
> have it for nothing)* Name the twice-repaired clause
>
> > **(PENCIL-SATURATES-CHART).** At a **generic point of `Chart(H)`** — a
> > generic configuration together with its flag — of an internal R-node peel
> > in the generic flag regime, `c_i(Π) = 2 ⟹ ρ_i = 6`, at `Π = Π_x` and at
> > `Π = Π_y`.
>
> It is free **for exactly the argument (BE-107)(i) already gave, and with one
> thing that argument did not have**: (BE-14) is **EXISTENTIAL** ((BE-16)), the
> good locus is Zariski-open on the irreducible `Chart(H)` and hence dense or
> empty ((BE-69)), and `dim(ρ̄₁+ρ̄₂)` is lower-semicontinuous — so the arc only
> ever needs a generic point of the chart. The new ingredient is that the bad
> locus is **proved** proper rather than measured proper: by (BE-110)(iii) a
> generic path configuration has `dim(ρ̄ ∩ Σ_x) = max(1, ρ−3) < 3`, so the tail
> stratum is a **proper closed** subset of the chart, not merely one that no
> sampler happened to draw. ***Extended 2026-09-02 by (BE-116): the
> properness holds at EVERY side with `deg_i(x) = 1`, path or not, and with
> no side-topology hypothesis — so this licence no longer depends on the
> side being a path. What it still depends on is (BE-69)'s openness for
> this locus and (BE-116)(iii)'s two measured inputs.*** **(BE-101)(i) and
> (ii) hold verbatim under
> (PENCIL-SATURATES-CHART)** and the `14 → 12` drop stands.
>
> > **WARRANT CORRECTED and the clause PROVED, 2026-09-02, direction BOPEN
> > ((BE-122)–(BE-127)).** Two corrections, both in this direction's favour.
> > **(1)** The *"Zariski-open … ((BE-69))"* clause cites (BE-69) for a locus
> > it is not about — its subject is the **attainment** locus, proved open by
> > rank **lower** bounds ((BE-122)) — and it is **not needed**:
> > constructibility of the bad locus plus **(CH-1)(a)**'s irreducibility
> > already give a **dense open** good locus ((BE-123)). **(2)** The two
> > remaining inputs are no longer measured: the `p_x`-sweep falls out of
> > §(K-chart)'s tower ((BE-124)) and `a_i = 0` generically **is**
> > (BE-69)(i)'s own open locus `A_i` ((BE-126)). So
> > **(PENCIL-SATURATES-CHART) is a THEOREM at every side-degree-`1`
> > terminal** ((BE-127)(i)) — this step's *"the arc may still have it for
> > nothing"* is settled positively there — while at side-degree `≥ 2` it
> > rests on the condition `(∗)`, certified 91/91 and **not proved**.

> **(BE-112)(iv)** *(what the repair is STILL not free for — (BE-107)(ii)
> restated with its scope widened)* It is free **only** because the target is
> existential. Any later step that needs the block inequalities at **every**
> legal *flag* — (BE-107)(ii)'s warning — or now at every legal
> **configuration** — a uniform statement over the chart, a closure argument,
> a degeneration argument that lands *on* a stratum, or anything that
> quantifies the class statement before choosing a point of the chart — does
> **not** get it, and there `Π_x`/`Π_y` are live and (BE-106)(ii)'s 24
> escapees are the price. Nothing in the arc as it stands does that. **The
> widening matters more than the original warning did**: a degeneration
> argument is a natural tool for a *lower* bound on `reach`, and the tail
> stratum is exactly the kind of locus such an argument walks onto.

### Step BE112 — (BE-113): job 3's residual, the board, the reading, and the E-rider

> **(BE-113)(i)** *(**the residual**, in (BE-97)(iv)/(BE-108)(ii)'s terms and
> not one word stronger)* **Half (B) is NOT discharged.** Against
> (BE-108)(ii)'s four items:
>
> 1. **(PENCIL-SATURATES-GEN) is settled — negatively**, and **replaced** by
>    (PENCIL-SATURATES-CHART). Item 1 is closed as posed for the second time in
>    two directions. Its own residual is **narrower than (BE-107)(iii)'s was**:
>    what would kill (PENCIL-SATURATES-CHART) is a piece at which the tail
>    stratum (or another `Σ_x ⊆ ρ̄_i` shape) is **not proper** — i.e. holds at
>    a *generic* configuration of `Chart(H)`. (BE-110)(iii) excludes that at a
>    path side outright; at a non-path side with `deg_i(y) = 1` it is
>    **unwitnessed rather than excluded**, over the **668**-row cap of
>    (BE-110)(iv) — and the planted stratum is not even *drawable* there under
>    this sampler ((BE-109)(iv)). That is the successor's target, and it is a
>    *class* statement, not a hunt.
> ***ANSWERED 2026-09-02 — positively, and only in HALF — by (BE-116): the
>    locus is PROPER at every side, path or not, proven inside the `p_x`-fibre
>    with one MEASURED sweep input. Both clauses above are also repaired: the
>    stratum IS drawable off paths ((BE-117)) and IS realized there at
>    `ρ_i = 4` ((BE-118)). Item 1 is NOT closed — what is left is the passage
>    from proper to GENERIC, i.e. (BE-69) for this locus plus (BE-116)(iii)'s
>    two measured inputs, a chart question rather than a hunt.***
> 2. **The other 12 live blocks**: `⟨M⟩` measured empty at 72 rows ((BE-108));
>    the remaining 11 still unwitnessed rather than excluded. **Unchanged.**
> 3. **The non-attaining case** — unchanged; (BE-101)(ii) is an `a₁ = a₂ = 0`
>    statement and off it `U = Λ²K⁴` is live ((BE-101)(iii)).
>    ***INHABITED 2026-09-02 by (BE-120)(ii): 15 of 21 exhibited rows carry
>    `a₁ + a₂ > max(0, 6 − δ₁ − δ₂)` and break `U = Λ²K⁴` outright — the shape
>    BDOUBLE's own* What would change this *named. They are non-generic
>    configurations of graphs that ATTAIN when drawn freely (F13 control), so
>    the item is INHABITED, not ACTIVATED.***
> 4. **The ear case's (β) side at the window**, modulo §(K-bare-ext)'s own two
>    window conditions, and **cross-pair welding** ((BE-28)(i)) — unchanged.

> **(BE-113)(ii)** *(**the board**)* **What moved.** BSATUR's named residual is
> realized, so the repair is refuted and re-repaired; the failure locus is
> pinned by a **proved** floor rather than a measured one; (BE-105)(ii)'s
> measured half is upgraded to proved on its own class; the support audit
> names what the arc's most-cited battery ranges over; and the regime gate
> `deg_i(y)` is identified as what separates a hit from an artefact. **What did
> not move.** No class statement is proved; **no shortfall is exhibited** — 78
> hit rows all attain; `hbareSplit`, `hK`, (GR-15), (BE-14) and class
> uniformity are untouched; the coincident regime ((BE-98)(i)) still keeps only
> the cap; the 11 unmeasured blocks are still unmeasured.

> **(BE-113)(iii)** *(**the coordinator's reading**, classified)* The reading
> was: *"the hunt is not at those terminals as sampled; at `deg_i(x) ≥ 2` there
> is no flag freedom at all, and that is where the coordinator would look
> first."* It is **CONFIRMED IN ITS NEGATIVE HALF AND WRONG IN ITS POSITIVE
> ONE.** The negative half is exactly right and is (BE-111)'s content: the
> battery's terminals *as sampled* do not carry the shape. The positive half —
> *look at `deg_i(x) ≥ 2` first* — points away from the hit: at `deg_i(x) ≥ 2`
> the flag carries no freedom, but `Σ_x ⊆ ρ̄_i` is not a statement about the
> flag at all ((BE-111)(ii)), so that regime is neither easier nor harder for
> it; the hit is at `deg_i(x) = 1`, the same regime BSATUR's refutation lived
> in, at a different **configuration**. The prep's other steer — *"check the
> regime before reporting a hit"* — is **load-bearing and fired**, on the
> `ρ_i = 4` rows ((BE-110)(iv)); without it this landing would have reported a
> sub-floor hit that `flag_frame` rejects. **Tally**: eleven instances, seven
> kinds; this is the first **SPLIT** verdict, and it is recorded as a
> half-instance of CONFIRMED rather than an eighth kind.

> **(BE-113)(iv)** *(classification, mandatory and explicit)* **What is
> refuted**: one named condition, **(PENCIL-SATURATES-GEN)**, as a statement
> about every legal configuration — and with it (BE-107)(i)'s licence read
> pointwise in the configuration, and (BE-107)(iii)'s *"named and measured
> absent"* status. **What is NOT refuted**: `PencilPair K 3 G`; `hbareSplit`;
> (BE-14)-for-all-`G`; the 2-cut step; half (B); (BE-101)(i) as an implication;
> (BE-104)/(BE-105)/(BE-106); **any** landed measurement. **No route is closed.
> One route is narrowed** — the clause the redundancy theorem rests on is now a
> *generic-chart-point* statement whose bad locus is proved proper. **Not a
> PENCIL event.**

### Verdict, classification, and the price

- **HIT shape 2 — REFUTED**, with a witness at BSATUR's own internal R-node
  peel, in the generic flag regime, through both gates ((BE-109)). And
  **priced exactly as the prep asked**: it removes the repaired clause's
  universal-over-configurations reading, **not** half (B) — the witness peel
  attains ((BE-112)(i)).
- **HIT shape 3 — REDUCED**, twice: the floor `Σ_x ⊆ ρ̄_i ⟹ ρ_i ≥ 5` is
  **PROVED** at a path side ((BE-110)(ii)), improving (BE-107)(iii)'s
  modular-law bound from `3` to `5`; and (BE-105)(ii)'s measured `≤` half is
  **PROVED** at a generic path configuration ((BE-110)(iii)).
- **HIT shape 4 — the forced support audit**, answered with the battery's own
  enumeration and the variable named ((BE-111)).
- **HIT shape 5 — the residual and the E-rider** ((BE-113)(i), *TERMINATION
  riders*).
- **The coordinator's reading: SPLIT** ((BE-113)(iii)) — its negative half
  confirmed and its positive half pointing away from the hit, with its
  regime warning load-bearing and fired.
- **NOT HIT shape 1** — (PENCIL-SATURATES-GEN) is **not** salvaged as stated;
  it is **false**. What is delivered instead is (PENCIL-SATURATES-CHART),
  free **only** because the target is existential ((BE-112)(iv)).
- **The price, stated as a price.** (a) (PENCIL-SATURATES-CHART) is **still not
  a theorem**: what is proved is that its bad locus is proper at a *path*
  side; at a non-path side with `deg_i(y) = 1` properness is
  **measured-only**, at 668 rows. (b) The `ρ_i ≤ 4` verdict is *none found
  under that cap* in the regime-compatible bucket, never *"does not exist"*.
  (c) The scan's population is **constructed** subdivided skeletons, a **new**
  one, not a census, and `Π_x` is never tight in it — so it says nothing about
  tightness. (d) The hit is exhibited at `deg_i(x) = 1` terminals only; whether
  a `deg_i(x) ≥ 2` shape can carry `Σ_x ⊆ ρ̄_i` below `ρ = 6` is **not
  measured here at all** — (BE-105)(iv)'s 19-piece measurement is about
  `c_i(Π_x) = 2`, which is weaker.
  ***MEASURED 2026-09-02 by (BE-119): 91 rows over 16 `deg_i(x) ≥ 2`
  topologies, `dim A ≤ 3` at every one, `Σ_x ⊆ ρ̄_i` with `ρ_i ≤ 5` NOT FOUND
  under that cap — and properness settled wherever `dim A ≤ 4`, so the
  residual there is `dim A ≥ 5`, itself not found under the same cap.***

### Verification

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsigma.py witness    #    2.2 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsigma.py mech       #    1.5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsigma.py support    #    0.5 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsigma.py floor      #  237.6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsigma.py price      #   77.6 s
PYTHONHASHSEED=0 python3 notes/scripts/w4/bsigma.py validate   #  113 s (reduced, all five)
```

Exact ℚ throughout (`fractions.Fraction`, no floating point); the single seed
is `20260902`, printed by every mode. Every headline is an `assert`, not a
report: the witness's identities at every seed including the 24 random planes
through `p_x` and the F13 control; the corank identity at every path draw; the
flat cap and the coplanar-tail dimensions at the 30 + 30 deliberately-planted
draws; the battery's five `deg = 1` terminals and the reproduction of
`3↦1, 4↦1, 5↦2, 6↦3`; the modular lower bound at every row of the 1 212-row
floor sweep, with the sub-floor rows' regime probe; and `margin ≤ 0` at four
blocks plus `reach = min(δ₁+δ₂,6)+a₁+a₂` at all 78 scan rows.

### Caps, disclosed rather than smoothed — with the denominator named

1. **The hit needs no cap.** (BE-109)(ii) is a two-line dimension count with no
   genericity in it; the seeds supply only the realizability of a peel meeting
   its hypotheses, asserted at 6 of 6.
2. **The floor is PROVED at a path side and MEASURED elsewhere.**
   (BE-110)(ii) is a proof. Off paths, *"no `dim = 3` at `ρ ≤ 4` where the
   regime survives"* rests on **668** rows over **16** `deg_i(y) = 1`
   topologies (628 blind at coordinate ranges `{3,5,9}`, 40 planted). The
   `deg_i(y) ≥ 2` bucket adds **544** rows over **13** topologies, where the
   shape **is** reached at `ρ = 4` and every such row is off-regime.
3. **The planted stratum is drawable at only 5 of the 16 bucket-A
   topologies** — the five paths — and at **3 of 13** in bucket B; every
   hub-carrying side rejects it under `sample_side_config`, because planting
   the plane forces a hub's neighbours onto one line and the draw then fails a
   gate. The 11 + 10 topologies are **listed by name in the driver's own
   output**. So the *blind* sweep covers hub-carrying sides and the *planted*
   one does not: what the tail stratum does at a non-path side is
   **unmeasured**, and (BE-109)(iv) says so.
   ***REPAIRED by (BE-117) — the non-drawability was one line of the planter,
   not a property of hub-carrying sides: 16 of 16, firing at 11.***
4. **The support audit is an enumeration, not a sample.** *"Exactly 5 of 24,
   and they are the paths"* is read off `piece_battery()` in full; the generic
   reproduction and the stratum failure are 5 and 6 draws respectively.
5. **The scan is a constructed population**, and a **new** one: 39 profiles,
   2 draws each, **78** rows, all of them hit rows by construction. *"0
   shortfalls"* is a statement about those 78. It is not evidence about
   BSATUR's 260 or BUNIF's 92.
6. **The side library is shape-guarded**, inheriting `sample_piece_config`'s
   restriction (degree-`≥3` vertices an independent set) verbatim; sides
   violating it are outside every sweep here.
7. **`rnode_shaped` is BPEEL's disclosed stand-in**, unchanged.
8. **Nothing here measures `deg_i(x) ≥ 2`.** The hit, the floor and the sweeps
   are all at `deg_i(x) = 1`.
   ***MEASURED by (BE-119), 91 rows over 16 topologies.***

### Harness note — the `kbare/` sibling-import set gains its TWENTY-THIRD consumer

`w4/bsigma.py` imports `bsatur`, `bunif`, `bdecor`, `bpeel`, `bearcase`,
`bimage`, `binduc` and `exactcore` read-only and reimplements none of them: no
deficiency oracle, no `ρ̄`, no peel scan, no block decomposition, no R-node
stand-in, no row measurement and no margin arithmetic is rewritten — `peel_of`,
`row_of`, `margin_at`, `sigma_at` and `draw_peel` are taken straight from
`bsatur`. It is the **twenty-third** `kbare/` consumer and takes the chain
**twenty-one** deep (`… → bunif → bdouble → bsatur → bsigma`). The recorded
**unpaid** sibling-import debt (`notes/scripts/README.md` *Harness debt*) is
unchanged; **no move made**. The one piece of new linear algebra is `wedge3`
(the map `ω ↦ ω ∧ p_x`), which is not in the shared layer and is guarded by the
corank identity's own assert at every call site.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-109)(i) the residual is realized | **EXHIBITED BY WITNESS** — 6 seeds, both gates, generic regime, R-node-shaped, `Σ_x ⊆ ρ̄₁` asserted as spaces |
| (BE-109)(ii) the arithmetic behind it | **PROVED** — one dimension count, no draw |
| (BE-109)(iii) nothing landed is refuted with it | **ARGUED**, and the F13 control is the evidence |
| (BE-109)(iv) the stratum caps `ρ₁` at 5, so it is a family | **ASSERTED** at every coplanar-tail draw (30) + 24 planted; its reach at NON-path sides **UNMEASURED**, disclosed |
| (BE-110)(i) the corank identity | **PROVED** (kernel of `ω ↦ ω ∧ p_x`), asserted at every row |
| (BE-110)(ii) the floor `ρ_i ≥ 5` at a path side | **PROVED**; both steps asserted, the second at 30 planted flat draws |
| (BE-110)(iii) `max(1, ρ−3)` at a generic path configuration | **PROVED** — upgrades (BE-105)(ii)'s measured half |
| (BE-110)(iv) the `ρ = 4` shapes are off-regime | **MEASURED**, 8 of 8, with the structural reason proved (`deg_i(y) ≥ 2 ⟹ π_y` forced) |
| (BE-111)(i)/(ii) the support audit | **VERIFIED AT SOURCE** — the battery enumerated and `run_mech`'s loop read, not inferred |
| (BE-111)(iii) the identity's status | **PROVED** true generically, **ASSERTED** false on the stratum (6 draws) |
| (BE-112)(i) slack, not a shortfall | **MEASURED**, 78 rows, margins and attainment asserted |
| (BE-112)(ii) the cost | **CITED** — (BE-106)(ii)'s enumeration, unchanged; only the applicable row moves |
| (BE-112)(iii) the repair is free | **ARGUED** from (BE-16) + (BE-69) + semicontinuity, now with a **proved** proper bad locus at path sides; **not** a new theorem |
| (BE-113)(iii) the reading | **SPLIT** — negative half CONFIRMED, positive half misdirected |

### What would change this

- **A piece where `Σ_x ⊆ ρ̄_i` holds at a GENERIC configuration** — i.e. the
  bad locus is not proper — would refute (PENCIL-SATURATES-CHART) and leave
  the clause with no repair. (BE-110)(iii) excludes it at path sides; that is
  the successor's target.
- **A `deg_i(x) ≥ 2` shape with `Σ_x ⊆ ρ̄_i` and `ρ_i < 6`** would show the
  mechanism is not confined to series ends.
- **A tail-stratum row with `margin > 0`** — `δ₂ ≤ 2` with `c₂(Π_x) ≥ slack+1`
  is the arithmetic shape — would be the arc's **first exhibited shortfall**
  and would matter far more than this landing does.
- **A `ρ_i = 4` shape with `deg_i(y) = 1`** would break the floor inside the
  regime-compatible bucket.
- **A step that needs the block inequalities at every point of the chart**
  would remove (BE-112)(iii)'s licence for good.

### TERMINATION riders

**E1 / E2 / E3 — reported, never fired; E3 remains ARMED (by GBAL).** Read
against their actual definitions in `notes/pencil/fanout-archive.md`, with the
2026-09-02 correction (`61e046a6`) in force: **"the target" in E1–E3 is the
ARC's target, `PencilPair K 3 G`**, never a direction's local obligation. The
corpus carries **two** E3 texts; **this reading is `:1700`'s two-conjunct
form**, with `:2098`'s one-conjunct deviation noted and **not** used — as
BBASE, BUNIF, BDOUBLE and BSATUR all read it.

- **E1** — a g-flank, a `D = 0` shape whose every admissible colouring is
  binding. **Does not fire**: no colourings, no `D`, no g-flank here.
- **E2** — the arc's target refuted or unprovable-as-posed **and** no ledger
  entry left open-with-a-named-dispatchable-attack. **Does not fire on either
  conjunct.** What is refuted is **(PENCIL-SATURATES-GEN)**, a condition a
  landed theorem is conditional on — a direction's local obligation — **not**
  `PencilPair K 3 G`; and this landing names dispatchable attacks
  ((BE-113)(i) items 1–4, item 1 now a *class* statement with a named class).
- **E3** — the arc's target proven **and** every remaining entry
  adjudication-gated. **Does not fire on either conjunct.** Under `:2098`'s
  one-conjunct text it still does not fire, the first conjunct being the one
  that fails.

**F11 — the central rider, and the target was a `∃`, not a `∀`.** *"Is there a
shape forcing `dim(ρ̄_i ∩ Σ_x) = 3` at `ρ_i = 5`?"* is an existential, and an
existential falls to one construction; no sweep had to be exhausted for the
headline. The figures that **are** sweeps are disclosed with their denominators
in *Caps*: **668** rows over 16 `deg_i(y) = 1` topologies and **544** over 13
`deg_i(y) ≥ 2` ones for the `ρ ≤ 4` hunt; **78** rows over 39 constructed
profiles for the price; **24** pieces enumerated (not sampled) for the audit.
Every *"none found"* — the `ρ ≤ 4` verdict in the regime-compatible bucket, the
scan's 0 shortfalls — reads **none found under those caps**, never *"does not
exist"*. The claims that are **not** sweeps are (BE-109)(ii), (BE-110)(i),
(BE-110)(ii), (BE-110)(iii) and (BE-111)(i). **And the asserted-in-driver /
proved distinction is paid a third time**: (BE-105)(ii) **was** asserted in its
driver at every `deg = 1` terminal — verified at source, and true there — and
that was still not enough, because the assert ran only on the configurations
the sampler drew.

**F12 to be paid at source.** Six hunks, at the statements rather than only
here — drafted below under *F12 hunks*: **(BE-105)(ii)** (the threshold, marked
generic-configuration-only with its `≤` half upgraded to proved),
**(BE-106)(iii)** (the live-block count, third reading added), **(BE-107)(i)**
((PENCIL-SATURATES-GEN) refuted as stated, repointed), **(BE-107)(ii)** (scope
widened from flags to chart points), **(BE-107)(iii)** (the residual, marked
REALIZED), and **(BE-108)(ii) item 1** (the residue sentence).

**F21**: the `(K-bare)` gap-map row needs recomputing with this direction
folded in; a drafted, **integrated** (not appended) edit is below under
*Gap-map row*, sized to stay under the generic cap with the row's existing
headroom. **No `SPECIAL_CAPS` entry is proposed and none is needed** — *no
overflow, no bump*. Label preservation to be verified by
`notes/scripts/gapdiff.py`; the seven codes added are **(BE-109)**–**(BE-113)**,
**(BE-110)(ii)** and **(PENCIL-SATURATES-CHART)**.

**Reservation, and what is returned.** Labels **(BE-109)–(BE-113)** and
***Steps BE108–BE112*** were reserved and are **consumed in full**; nothing is
returned. The driver `w4/bsigma.py` lands at the reserved path. **One** new
name is minted, and it is a **condition**, not an object:
**(PENCIL-SATURATES-CHART)**. Nothing is minted for `Σ_x`, `Π_x`, `ρ̄_i`,
`c_i(U)` or the flag regime, per the reservation's constraint — *the tail
stratum* and *the projected pair lines* are plain descriptive prose, as *the
bad plane* was for BSATUR. The section has now gone **seven** directions
without minting a configuration-level token.
