## §(K-bare-ext) — continuation (direction BSIXRUNG, ordinal 101, 2026-09-11): **THE BOTTOM RUNG IS NOT PROVED, NOT REFUTED — AND THE FIRING HALF OF A REFUTATION IS NOW EXHIBITED.** A cycle side with both arcs of length `≥ 4` reaches `c_i(Π_x) = 2` at **`ρ_i = δ_i = 2`**, `a_i = 0`, `deg_i(x) = 2`, in the generic flag regime — `δ_i`/`a_i` read off `bfour.side_nums`, `ρ̄_i` cross-asserted against `binduc.rel_screw_space` — which is exactly the half (BE-232)(iii) records as *reached at 0 rows*. Two exclusions are **proved**: an x–y path of length `≤ 3` can never carry the pencil in-regime, and by (BE-30)(iv) that is a statement about **every** x–y path of a firing side, so `d_min_i ≥ 4`. What is **not** exhibited is the non-firing side's `c_j(Π_x) ≥ 1` at the same flag — and (BE-234)'s *"together they are the whole of it"* is **REFUTED**: (BE-45)(ii) path saturation is a **third** free mechanism, degree-free, and the **only** one that survives this dispatch's quantifier. A rung-3 certificate would be a **SHORTFALL** — asserted at 26/26. And the cheapest route to the non-firing half is **closed on the landed family**: **0 of 236 196** R-node-shaped sides are path-saturated (*Steps BE238–BE244*)

### Standing notation (on top of *Steps BE148–BE237*)

BOBLIG's and BCORNER's, verbatim, **read at the definition sites**
(`barch.slack_of`, `barch.violates`, `barch.all_tuples`, `bfour.e_row`,
`bfour.side_nums`, `bimage.rho_bar_of`, `bimage.dist_in`,
`binduc.rel_screw_space`, `bline.legal_peel`, `bline.longcore_library`,
`bproper.free_peel`, `bpeel.rnode_shaped`, `bunif.flag_frame`):

> **`slack := max(0, δ₁ + δ₂ − 6)`** and the **`Π_x` OBLIGATION**
> `c₁(Π_x) + c₂(Π_x) ≤ 2 + slack`. **RUNG 3** is the locus `Σδ ≤ 6`, where
> `slack = 0` and the obligation **is** `c₁ + c₂ ≤ 2` ((BE-225)(iii)), which
> by (BE-100)(i) **is (NO-DOUBLE-PENCIL)**. `slack` is a **function of the
> `δ`s** ((BE-225)(iv)), so rung 3 is a **locus**, never a settable
> parameter — carried in every sentence below.
>
> **`⟨P⟩`** is the span of the hinge lines of a path `P`; **`d_min_i`** is
> the length of a shortest x–y path *inside side `i`*. **(M1)** is
> (BE-45)(i)'s series end, **(M2)** is (BE-45)(ii)'s path saturation
> `δ_i = d_min_i`. **The Grassmann floor**, hypothesis-free:
> `c_i ≥ max(0, ρ_i − 4)` ((BE-234)).
>
> **THE REGION** this direction is quantified over, from the dispatch:
> `a₁ = a₂ = 0`, `Σδ ≤ 6`, side-degree `≥ 2` on **both** sides, an internal
> R-node peel, the generic flag regime (`bunif.flag_frame` non-`None`:
> `π_x ≠ π_y`, `p_x ∉ π_y`, `p_y ∉ π_x`).

**Carrier check, off the landed bodies.** No new Lean object is read and
**no `.lean` was opened** (the 2026-08-05 hold). **No tracked script was
modified**: the driver `notes/scripts/w4/bsixrung.py` is new, and every
configuration is either drawn by this driver at exact ℚ or produced by a
predecessor's own builder (`bproper.free_peel` through
`bline.legal_peel`), so no landed figure can move.

---

### Step BE238 — (BE-239): the bottom rung, PRICED — both coincidences are strictly above the floor, and a certificate is a SHORTFALL

> **(BE-239)(i)** `[PROVED]` *(exhaustion; the price of the rung, and half
> of it is new)* At `a = 0`, rung 3 carries **141** tuples of
> `barch.all_tuples()` and the obligation fails at **26**, splitting
> `{(1,2): 10, (2,1): 10, (2,2): 6}` — (BE-227)(ii)'s corners restricted to
> the rung, and (BE-235)(ii)'s 26 reproduced independently. At **26 of 26**,
> asserted tuple by tuple: the **firing** side has `ρ_i ≤ 5` **and** the
> **non-firing** side has `ρ_j ≤ 4`, so `c_i = 2` **and** `c_j ≥ 1` are
> **both strictly above the Grassmann floor** `max(0, ρ_i − 4)`. *Proof.*
> `c_i = 2` needs `ρ_i ≥ 2` and `c_j ≥ 1` needs `ρ_j ≥ 1`, so
> `ρ_i ≤ Σδ − 1 ≤ 5`; and `ρ_j ≤ Σδ − 2 ≤ 4`. ∎ **(BE-237)(i) records the
> firing half** (*"`ρ_j ≥ 5` with `c_i = 2` forces `ρ_i ≤ 2`"*, at `Σδ ≤ 7`);
> the **non-firing** half is new, and it is the one that matters, because
> `c_j ≥ 1` is the clause (BE-234) made free. `bsixrung.py arith`.

> **(BE-239)(ii)** `[PROVED]` *(exhaustion; **what a rung-3 certificate
> costs**, and it is not what (BE-232)(i) costs)* At **26 of 26**, asserted:
> a rung-3 violation forces `dim(ρ̄₁ ∩ ρ̄₂) ≥ c₁ + c₂ − 2 ≥ 1` by (BE-95)(i),
> hence `dim(ρ̄₁ + ρ̄₂) ≤ Σρ − 1 < min(Σδ, 6) + a₁ + a₂`, hence by (BE-86)(i)
> **the peel does not attain**. So a rung-3 certificate is a **SHORTFALL at
> an `a = 0` chart point in the generic flag regime** — the event
> (BE-232)(i) calls *"far larger"* and (BE-232)(ii) shows (BE-231)(i)'s kill
> avoided by sitting at `Σδ ∈ {10,11}`. **SCOPE, stated before anyone
> reads it as more than it is:** this does **not** refute (BE-14), which is
> **existential** ((BE-16)) with a **dense** good locus ((BE-69)) — a
> shortfall at one chart point of an open stratum leaves half (B) standing.
> What it would refute is the obligation **as a universally-quantified
> statement over the chart's generic-flag stratum**, which is how every
> consumer in *Steps BE148–BE237* uses it. `bsixrung.py arith`.

> **(BE-239)(iii)** *(**the re-aiming, and the coordinator is right**)* The
> dispatch was re-aimed off §8's stated item — `(BE-OBL7) ∧ (BE-OBLK)` —
> onto the bottom rung itself. **This direction agrees, and the reason is
> the consumer's own words:** (BE-235)(ii) reads *"on `Σδ ≤ 6`, which
> carries the other 26, it is the target restated. A successor that equals
> its target on 87 % of the residue is not a reduction"*, and (BE-237)(ii)
> reads *"it is **not** the honest successor … whether that is worth a
> direction is §8's call"*. The board's own framing therefore **points at
> the rung**, and §8's entry lags its own consumer by one landing. **No
> correction to the dispatch is owed.**

---

### Step BE239 — (BE-240): (BE-234)'s closing clause is REFUTED — there is a THIRD free mechanism, and it is the ONLY one that survives the quantifier

> **(BE-240)(i)** `[REFUTED]` *(a landed clause's enumeration, refuted by a
> landed PROVED clause the same corpus already cites in this exact role)*
> (BE-234) closes *"**This is the second free mechanism**; (BE-228)(iii)
> names only the series-end one, **and together they are the whole of
> it**."* **The enumeration is incomplete.** §(K-bare-ext) (BE-45)(ii) is
> `[PROVED]`: at path saturation `δ_i = d_min_i`, `ρ̄_i = ⟨P⟩` for a
> shortest path `P` and hence *"`ρ̄₁ ∩ Π_u = ⟨P⟩ ∩ Π_u ⊇ ⟨ℓ_{P,1}⟩ ≠ 0`,
> **at both ends**"* — so `c_i(Π_x) ≥ 1`, with **no genericity, no draw and
> no degree hypothesis**. The corpus states the trio itself one direction
> earlier: (BE-99)(ii) reads *"by (BE-45)(i) a **series end** … and by
> (BE-45)(ii) so does **path saturation** `δ_j = d_min` at any `d_min`.
> **Both are unconditional identities.**"* So the refutation of (BE-234)'s
> closing clause was already inside the corpus, one `--brief` away —
> **(BE-231)(ii)'s process finding, a second time, on the clause that
> corrected the first.**

> **(BE-240)(ii)** `[PROVED]` *(why the omission is load-bearing **here** and
> was not at (BE-234))* In **this** region the three mechanisms separate:
> **(a)** the Grassmann floor is unavailable — (BE-239)(i) puts the
> non-firing side at `ρ_j ≤ 4` at all 26; **(b)** the series end needs
> `deg_j(x) = 1`, which the dispatch's quantifier excludes on side 1 and
> `rnode_shaped` excludes on side 2 ((BE-175)(ii)) — **with the scope note
> below**; **(c)** path saturation
> needs only `δ_j = d_min_j` — **no degree condition at all** — so it is the
> **unique landed free mechanism that reaches the region**. (BE-234) was
> written for `(BE-OBL)`'s over-strength locus, where `ρ_j ≥ 5` and (a)
> does all the work, so the omission cost nothing there and costs the whole
> question here. **This is (BE-238)(iv)'s lesson turned on the mechanism
> list: a mechanism census must be re-taken at the rung, not inherited.**
>
> **SCOPE NOTE, self-caught, on (b).** *"Side-degree `≥ 2`"* is **not
> literally** *"(M1) does not fire"*. (BE-45)(i)'s hypothesis is *"every
> `u–v` path leaves `u` by the same edge"* — a **bridge** condition — and
> (BE-175)(i)'s `deg_i(x) = 1` is *sufficient* for it, not necessary: a
> side with `deg_i(x) ≥ 2` still satisfies it if `x` is a cut vertex
> separating the other branch from `y`. The two coincide exactly when
> `side_i + xy` is **2-connected** (then `x` is not a cut vertex of the
> side), which is true of a genuine SPQR split component but is **not
> asserted by the harness**: `boblig._assert_gates` requires `rnode_far`
> and records `rnode_near` without checking it. So (b) is a *mathematical*
> exclusion under the split-component hypothesis, not a machine-checked
> one, and a future population built off a non-2-connected near side
> would need it re-argued. This is the third member of the
> (BE-228)(iii)/(BE-233)(i) family of scope slips — caught before it was
> written into a conclusion rather than after.

> **(BE-240)(iii)** `[MEASURED]` *(and it is absent in practice)* On the
> landed population of (BE-229)(ii), re-read at rung 3 ((BE-243)), path
> saturation fires at **0 of 108** rows on side 1 and **0 of 108** on side
> 2 — `δ_i < d_min_i` strictly at every row, on both sides. So the only
> free mechanism that reaches the region is **available in principle and
> unrealized in every landed configuration**, which is precisely the gap a
> refutation has to cross — and (BE-244) then shows it is unrealizable on
> the landed skeleton family at all. `bsixrung.py census`.

---

### Step BE240 — (BE-241): what a PATH SPAN can do to the pencil, exactly, and where the generic flag regime forbids it

> **(BE-241)(i)** `[PROVED]` *(the reduction, off an unconditional landed
> clause)* (BE-30)(iv) is `[PROVED]` and hypothesis-free: *"for **every**
> `u–v` path `P` of a piece `H`, `ρ̄_{uv}(H) ⊆ ⟨ℓ_e : e ∈ P⟩`"*. Hence
> **`c_i(Π_x) = 2` ⟹ `Π_x ⊆ ⟨P⟩` for EVERY x–y path `P` of side `i`** —
> the question *"can a side fire?"* becomes *"can a path span swallow the
> pencil?"*, one path at a time, with no genericity assumption anywhere.
> ∎ (This is (BE-44)(i)'s reduction used in the `c = 2` direction rather
> than the `c = 0` one.)

> **(BE-241)(ii)** `[PROVED]` *(the structure, uniformly in the path length
> `m`; the path does not merely permit a firing flag, it **names** one)*
> Write `S := ⟨P⟩ ∩ (p_x ∧ K⁴)`. Since `Π_x ⊆ p_x ∧ K⁴`, firing needs
> `dim S ≥ 2`; and where `dim S = 2` there is a **unique** plane `U` with
> `S = p_x ∧ U`, so the **only** flag at which `P` can fire is `π_x = U`.
> Counting: `dim S = m − dim(p_x ∧ ⟨P⟩)` and `p_x ∧ ⟨P⟩` is spanned by the
> `m − 1` vectors `p_x ∧ p_{k−1} ∧ p_k` (`k = 2 … m`) inside the
> **3-dimensional** `p_x ∧ Λ²K⁴`, so `dim S ≥ m − 3` — the Grassmann floor,
> re-derived — with equality generically. Measured over 60 exact-ℚ draws at
> each `m = 1 … 7`: `dim S = max(1, m − 3)` at **420 / 420**, and wherever
> `dim S = 2` it is **asserted** that `U` is a plane, that `U ∋ p_1` (the
> first neighbour, so the flag is legal), and that `Π_x = p_x ∧ U ⊆ ⟨P⟩`.
> At `m = 5` this happens at **60 / 60 generic draws with no condition
> imposed** — firing at `ρ_i = 5` costs only that the chart's own flag *be*
> that plane, which is exactly (BE-104)(i)'s mechanism, now with the plane
> named rather than searched for. `bsixrung.py path`.

> **(BE-241)(iii)** `[PROVED]` *(**the exclusion**, and it is the direction's
> one genuine obstruction)* In the generic flag regime, an x–y path of
> length `m ≤ 3` **cannot** carry `Π_x`:
> - `m = 1` — `dim⟨P⟩ = 1 < 2 = dim Π_x`. (Also `x`, `y` adjacent puts
>   `p_y ∈ π_x` by (CH-1), which `flag_frame` excludes outright, so
>   `d_min ≥ 2` on every in-regime side.)
> - `m = 2` — `⟨P⟩ = p_{v₁} ∧ ⟨p_x, p_{v₂}⟩` is the pencil at `p_{v₁}`, and
>   `Π_x` is the pencil at `p_x`; two pencils coincide only at a common
>   centre, so `⟨P⟩ = Π_x` needs `p_{v₁} = p_x`. The only available
>   degeneration, `p_x, p_{v₁}, p_{v₂}` collinear, drops `dim⟨P⟩` to 1
>   instead — asserted at 60/60 draws of that stratum. So `c = 2` is
>   unreachable at `m = 2` at **every** configuration.
> - `m = 3` — writing `q_k := p_k mod p_x`, a second kernel vector needs
>   `λ₂ q₁∧q₂ + λ₃ q₂∧q₃ = 0`, i.e. `p_x, p₁, p₂, p₃` **coplanar**; the
>   surviving vectors then all lie in `⟨q₁, q₂⟩` (the `q₁` terms cancel
>   identically), so `c = 2` forces `q₂ ∈ π̄_x` and hence
>   `q₃ ∈ π̄_x`. On an x–y path `p₃ = p_y`, so this is **`p_y ∈ π_x`** —
>   one of `bunif.flag_frame`'s three exclusions. Asserted at 55/55 draws of
>   the coplanar stratum with `π_x` the common plane (`dim⟨P⟩ = 3`, `c = 2`,
>   `p_y ∈ π_x`), with the **F13 negative control** at 58/58: the same
>   coplanar stratum with `π_x` *not* the common plane gives `c = 1`. So the
>   firing is the plane coincidence, not the coplanarity, and the
>   coincidence is exactly the excluded flag. ∎
>
> With (i): **a firing side has no x–y path of length `≤ 3`, so
> `d_min_i ≥ 4`.** This is the same *shape* as (BE-229)(iii)'s
> *"disqualified STRUCTURALLY"* — both say a short arc forces a flag
> `flag_frame` rejects — but **the identification is not made here**:
> (BE-229)(iii) reports (BE-191)/(BE-200) forcing `q_y ∈ π_x` /
> `q_z ∈ π_x` at named auxiliary vertices, and whether that is *this*
> mechanism was not checked. Read the two as consistent, not as one.
> `bsixrung.py path`.

> **(BE-241)(iv)** `[REFUTED]` *(a landed clause's *"equivalent"*, pinned by
> a certificate; its own body already says so)* (BE-44)(ii) reads
> *"`⟨P⟩ ∩ Π_u = ⟨ℓ_{P,1}⟩` is **equivalent to `dim⟨P⟩ ≤ 5`**"*. The
> equivalence is **generic, not universal**. Exhibited at exact ℚ:
> `p₀ = (35, 52, 8)`, `p₁ = (−86, −49, 35)`, `p₂ = (61, −60, −55)`,
> `p₃ = (691, 580, −348)`, `p₄ = (−2537, −2284, 1306)` with
> **`π_x = ⟨p₀, p₁, p₃⟩`** — the flag is reconstructible from the five
> points and is asserted to be, with `p₂` and `p₄` both **outside** it.
> Then `dim⟨P⟩ = 4` and `⟨P⟩ ∩ Π_u = Π_u`, re-verified by containment. The
> locus is `q₄ ∈ ⟨q₂, q₃⟩` (i.e. `p₄ ∈ ⟨p₀, p₂, p₃⟩`) together with
> `p₃ ∈ π_x` — which by (ii) is not an extra hypothesis but the *forced*
> plane `U` — and it is reached at **356 of 400** draws of that stratum
> with `p₄ ∉ π_x`.
> **The clause's own body is right** — *"below the boundary the condition is
> a genuine **open** condition"* — and its measured row is one guarded draw
> per piece; what is corrected is the summary word *"equivalent"*, the
> corpus's documented pathology in its exact form. **(BE-44)(ii)'s
> `dim⟨P⟩ = 6 ⟹ ⟨P⟩ ∩ Π_u = Π_u` half is untouched**, and so is (BE-44)(i),
> which uses only the `⊆` direction. `bsixrung.py path`.

---

### Step BE241 — (BE-242): THE FIRING SIDE, EXHIBITED at side-degree 2 — the half (BE-232)(iii) records as reached at 0 rows

> **(BE-242)(i)** `[PROVED]` *(the mechanism, and it is the **opposite** of
> (BE-104)(i)'s)* Let side `i` be a **cycle** through `x` and `y`, arcs `P`
> and `Q`, so `deg_i(x) = 2`. Then the closed star of `x` **inside the
> side** is `{p_x, p_{P,1}, p_{Q,1}}`, so (CH-1) **forces**
> `π_x = ⟨p_x, p_{P,1}, p_{Q,1}⟩` and `Π_x = ⟨ℓ_P, ℓ_Q⟩`: **there is no
> plane left to steer.** By (BE-30)(i) each arc is an ear with
> `⟨arc⟩` its own span, and their interior multipliers are independent, so
> `ρ̄_i = ⟨P⟩ ∩ ⟨Q⟩` — **argued from (BE-30)(i), and then verified against
> `binduc.rel_screw_space` at every certificate in (ii) rather than
> assumed.** Hence
> **`c_i(Π_x) = 2` ⟺ `ℓ_Q ∈ ⟨P⟩` and `ℓ_P ∈ ⟨Q⟩`** — and each is a system
> of `6 − m` linear conditions on `p_y` alone, because `p_y` sits in
> exactly one hinge line of each arc. The pair is solved in ℚ by
> `nullspace`, **on top of** (BE-241)(ii)'s forced-plane pre-condition for
> an arc of length exactly 4 (its third interior vertex must be drawn in
> `π_x`, or that arc's own span degenerates — measured at 40/40 of an
> earlier run of this mode that omitted it). Solvability is therefore
> **measured per arc shape in (ii)**, not predicted from
> `(6 − m₁) + (6 − m₂) ≤ 3` alone: `(4,4)` has four conditions and still
> solves, at 33 of 40. ∎ **This inverts
> (BE-104)(i)'s habitat**: there the side was a path, `deg₁(x) = 1`, the
> flag was free and one plane of the legal pencil was bad; here the flag is
> pinned and the *configuration* moves.

> **(BE-242)(ii)** `[CONSTRUCTED]` *(the certificates, read at the **side**
> layer off the landed primitives)* Exact ℚ, seed `20260911`,
> `bsixrung.py cycle`. Each certificate's cycle is handed as an edge list
> plus affine points to **`bfour.side_nums`** (which calls
> `bimage.rho_bar_of`, `bdecor.d3`, `bdecor.weld_d3`) and to
> **`binduc.rel_screw_space`**; the model `ρ̄_i = ⟨P⟩ ∩ ⟨Q⟩` is
> **cross-asserted** against both, as a *space*, not as a dimension.
>
> | arcs | draws | firing & in-regime | `ρ_i` | `δ_i` | `a_i` | `c_i(Π_x)` | `|E|` |
> |---|---|---|---|---|---|---|---|
> | (4,4) | 40 | **33** | **2** | **2** | **0** | 2 | 8 |
> | (5,4) | 40 | **40** | 3 | 3 | 0 | 2 | 9 |
> | (5,5) | 40 | **40** | 4 | 4 | 0 | 2 | 10 |
> | (6,4) | 40 | **38** | 4 | 4 | 0 | 2 | 10 |
> | (6,5) | 40 | **40** | 5 | 5 | 0 | 2 | 11 |
> | (4,3) | 40 | **0** | — | — | — | — | 7 |
>
> The `ρ_i` column is the **minimum over the shape's firing draws**, which
> is the named certificate's; `(4,4)` splits `{ρ_i = 2: 32, ρ_i = 3: 1}`
> and `(6,4)` is `{ρ_i = 4: 38}`, the remaining draws of each losing an arc
> span rather than failing to fire. *"In-regime"* is `flag_frame`'s three
> exclusions checked at the local layer: `p_y ∉ π_x`, `p_x ∉ π_y`, `π_x ≠ π_y`. The `(4,3)` row is
> **0 of 40 by (BE-241)(iii)**, not by cap — an arc of length 3 forces the
> excluded flag — and is carried as this step's negative control. At
> `(4,4)` the certificate has **`ρ̄_i = Π_x` exactly as spaces**, the
> `ρ_i = 2` corner (BE-239)(i) puts 13 of the 26 residue tuples in. Named
> `(4,4)` certificate: `p_x = (−60, −35, 86)`, P interior
> `(−28, 6, −30), (−29, 19, −62), (−3, 29/5, −101/5)`, Q interior
> `(97, 5, 19), (−2, 31, 97), (75, 160/7, −313/7)`,
> `p_y = (1848335745/69840386, 3217045/6349126, −1/4)`.

> **(BE-242)(iii)** `[MEASURED]` *(**the scope**, said plainly and not
> elided — this is a SIDE, not a PEEL)* What (ii) exhibits is **one side**
> of a peel with its own `δ_i`, `a_i`, `ρ̄_i` and `c_i(Π_x)`. It does **not**
> exhibit a peel: there is **no side 2**, so no `bline.legal_peel` gate
> (H's (CH-1), min degree `≥ 2`, girth `≥ 4`, `deg_H(x) ≥ 3`,
> `rnode_shaped` on the far side, `sized`), no
> `kbare_common.verify_pencil_witness` on a whole `H`, no `bfour.e_row`,
> no `c_j(Π_x)` and no `Σδ`. **Nothing here refutes (PENCIL-SATURATES)** —
> that clause is quantified at an internal R-node peel and was refuted at
> (BE-104) anyway. What is new is the **habitat**: `c_i(Π_x) = 2` at
> `ρ_i = 2 … 5`, `a_i = 0` and **side-degree 2**, which (BE-232)(iii)
> records as *"refuting rows with the **firing** side at side-degree `≥ 2`
> number **0** on this population"* and which §8 priced as needing a new
> builder. **The builder is now priced instead of guessed**: the steering is
> two linear systems in **one vertex**, `p_y`.

---

### Step BE242 — (BE-243): the landed `deg₁(x) = 2` population, re-read AT RUNG 3, and the cap is not what it looked like

> **(BE-243)(i)** `[MEASURED]` *(the region is NON-EMPTY, and no new builder
> was needed to show it)* (BE-229)(ii)'s population — `bproper.free_peel`
> over `bline.longcore_library()` through `bline.legal_peel`'s own gates,
> boblig's job list with the one `prism`/`[4]*9` job dropped as
> `δ₂ = 6`, hence off rung 3 — gives **108** fully-gated rows, with
> `a = (0,0)`, the generic flag regime and side-degree `≥ 2` on **both**
> sides **asserted at every row**. **Rung 3 (`Σδ ≤ 6`) at 84 of 108**, and
> the **obligation fails at 0**. So the dispatch's region is inhabited by a
> **landed** builder at 84 rows, and §8's *"needs a new builder"* pricing is
> wrong about *reaching the region* — it is right only about **steering
> inside** it. Cap, disclosed: 27 library shapes × 4 profiles × **1** seed.
> `bsixrung.py census`.

> **(BE-243)(ii)** `[MEASURED]` *(**the discriminating statistic**, and it
> sharpens (BE-229)(ii)'s own reading)* At **108 of 108** rows and on
> **both** sides — 216 side-instances, 0 exceptions — `c_i(Π_x)` **equals**
> the Grassmann floor `max(0, ρ_i − 4)`. So the population does not merely
> *fail to fire below `ρ_i = 6`* ((BE-229)(ii)'s reading); it produces **no
> incidental intersection at any `ρ`**. And the cap is **not** the length
> exclusion: `d_min₁ ≥ 4`, (BE-241)(iii)'s necessary condition for side 1 to
> fire, is reached at **88 of 108** rows. The population is in the right
> length regime and still never fires, because `free_peel` **does not
> steer** — which is (BE-229)(ii)'s *"cannot present the discriminating
> case"* with the discriminating case now named: *floor-exceeding
> intersection*, and its price is (BE-242)(i)'s two linear systems.
> `bsixrung.py census`.

> **(BE-243)(iii)** *(a landed clause's conclusion must be read WITH the
> floor)* (BE-45)(iv) reads *"where neither mechanism fires, the sharpening
> holds"* — conclusion `dim(ρ̄_i ∩ Π_u) = 0` — `[PROVED]` at 8 of 11 pieces
> and `[MEASURED]` at 3. In this region **(M1) cannot fire** (`deg_i(x) ≥ 2`
> on both sides) and **(M2) fires at 0 of 108 on either side**, so all
> **216** side-instances are *"neither"* instances; **36** of them have
> `c_i > 0` — and every one is at `ρ_i ≥ 5`, which is not a second
> measurement but a consequence of the asserted `c_i = max(0, ρ_i − 4)`,
> where (BE-234)'s floor **forbids** `c = 0`. So (BE-45)(iv)'s conclusion is correct only below `ρ_i = 5` and
> its honest form is **`c_i = max(0, ρ_i − 4)`** — measured here at
> 216/216, in the *peel* habitat, which (BE-45)(iv)'s 49-piece census was
> not taken in. This is a **scope correction, not a refutation of any
> measurement**: (BE-45)(iv)'s own 49 pieces are untouched.
> `bsixrung.py census`.

---

### Step BE243 — (BE-244): the named cheapest route to the NON-FIRING half is CLOSED on the landed skeleton family

> **(BE-244)(i)** `[MEASURED]` *(exhaustive over the enumerated family;
> **0 of 236 196**)* (BE-240) leaves exactly one landed free mechanism
> reaching the region — path saturation `δ_j = d_min_j` — and side 2 of an
> internal R-node peel must pass `bpeel.rnode_shaped`. Enumerated: every
> skeleton of `bpeel.SKELETONS`, every branch profile in
> `{1,2,3}^{|E(skeleton)|}` (3⁹ = 19 683 each for `K33` and `prism`), every
> hub pair **non-adjacent in the skeleton**. `K4` contributes **0
> candidate peels** — every hub pair is skeleton-adjacent, and such a pair
> can never pass `rnode_shaped`, because its branch suppresses onto the
> virtual edge and the parallel test rejects (**read at
> `bpeel.rnode_shaped`'s body**: `suppress_deg2(E_side + [(u,v)],
> keep={u,v})` then `len(set(map(frozenset, E))) != len(E) → False`, not
> from its docstring). Result: **236 196 R-node-shaped sides, PATH-SATURATED
> at 0.** The `(δ_j, d_min_j)` census is the same on both skeletons in
> shape — `δ_j = 0` at `d_min_j ∈ {2…6}`, `δ_j = 1` only at
> `d_min_j ≥ 4`, `δ_j = 2` only at `d_min_j ≥ 5`, `δ_j = 3` only at
> `d_min_j = 6` — and the **smallest gap `d_min_j − δ_j` over the whole
> family is 2**. (BE-30)(iv) proves only `δ_j ≤ d_min_j`; the family shows
> the inequality is never tight here. `bsixrung.py sat`.

> **(BE-244)(ii)** *(**what this closes and what it does not**)* It closes
> the route this direction itself named as the cheapest next step: pairing
> (BE-242)(ii)'s firing cycle with a **path-saturated** side 2 to get
> `c_j(Π_x) ≥ 1` for free. On the landed family that side does not exist,
> so a rung-3 certificate needs `c_j(Π_x) ≥ 1` **incidentally** — a second
> steered coincidence on top of the firing side's, of codimension
> `6 − δ_j` in the worst reading. **CAP, and it is the whole of the
> reading:** the family is **three skeletons** with branch lengths in
> `{1,2,3}`. *"Not found under that family"*, never *"does not exist"* — a
> larger 3-connected core is exactly what is not enumerated, and
> `bpeel.SKELETONS` is the harness's own list, not a classification.

---

### Step BE244 — (BE-245): the verdict, the board, the bars, the lesson

> **(BE-245)(i)** *(**the verdict**)* The `Π_x` obligation at `a = 0`,
> `Σδ ≤ 6`, side-degree `≥ 2` on both sides, at an internal R-node peel in
> the generic flag regime — **26 of the 30 residue tuples** — is **NEITHER
> PROVED NOR REFUTED**, and the state is now asymmetric in a way it was
> not: the **firing** half of a certificate is **exhibited at the side
> layer** ((BE-242)(ii)) at `ρ_i = δ_i = 2`, `a_i = 0`, side-degree 2,
> in-regime; the **non-firing** half is not, and (BE-240) shows the only
> free mechanism that reaches the region is path saturation, which
> (BE-244) then finds **unreachable on the landed skeleton family — 0 of
> 236 196 R-node-shaped sides**. Two exclusions are **proved**
> ((BE-241)(iii)): no x–y path of length `≤ 3` on a firing side, hence
> `d_min_i ≥ 4`. **The residue's TUPLE count does not move** — it stands at
> 26, and the tempting inference that (BE-241)(iii) reduces it is **false**,
> because (BE-30)(iv) bounds `ρ_i ≤ d_min_i`, which is the wrong direction
> to bound `δ_i` from below ((BE-239), *arith*'s closing block). What
> collapses is the **configuration** space. **No gap-map status word
> moves. Not a PENCIL event. `hK` is not closer.**

> **(BE-245)(ii)** *(**the board**)* **What moved.** (BE-234)'s closing
> enumeration REFUTED ((BE-240)(i)); (BE-44)(ii)'s *"equivalent"* REFUTED
> with a certificate, its `dim⟨P⟩ = 6` half untouched ((BE-241)(iv));
> (BE-45)(iv)'s conclusion scoped to `ρ_i ≤ 4` ((BE-243)(iii)); the
> non-firing side's floor-strictness at rung 3 PROVED ((BE-239)(i)); a
> rung-3 certificate priced as a SHORTFALL ((BE-239)(ii)); the length
> exclusion `d_min_i ≥ 4` PROVED ((BE-241)(iii)); the firing side at
> side-degree 2 CONSTRUCTED ((BE-242)(ii)); the path-saturated R-node side
> MEASURED ABSENT over 236 196 enumerated sides ((BE-244)(i)). **What did NOT move.**
> `PencilPair K 3 G`, `hbareSplit`, `hK`, `hcontract`, (GR-15), (BE-14),
> S-mark, half (B), half (β), the 2-cut step, class uniformity, cross-pair
> welding, (BE-E4′), the flag base, `(BE-OBL7)`, `(BE-OBLK)`, and **every
> landed measurement** — including (BE-229)(ii)'s 135/135 and
> (BE-229)(iii)'s 48/48, both of which this direction *explains* rather
> than contradicts. **No `.lean` opened**; the 2026-08-05 hold untouched.
> **The E-rider:** no termination-ledger entry fires; E1/E2/E3 are
> §(K-grid) objects and are untouched.

> **(BE-245)(iii)** *(**the bars this adds**, as §8's rule requires)*
> *(a)* **No claim that a mechanism list is complete may be carried across a
> rung without re-taking it at that rung** — (BE-240): (BE-234)'s *"together
> they are the whole of it"* was true where it was written (`ρ_j ≥ 5`) and
> false one rung down, and the missing member is the *only* one that
> survives the quantifier. *(b)* **No further attempt to refute the rung-3
> obligation may spend effort on the FIRING side** — it is exhibited at
> `ρ_i = 2 … 5` with side-degree 2 ((BE-242)(ii)); the open half is
> `c_j(Π_x) ≥ 1` at the same flag, and the named cheapest route is a
> path-saturated side 2 (`δ₂ = d_min₂`), which (BE-244)(i) now finds
> **absent at 236 196 of 236 196** on the landed skeleton family — so that
> route is closed unless the family is enlarged. *(c)* **No firing side may be proposed with an
> x–y path of length `≤ 3`** — (BE-241)(iii) kills it before it is drawn,
> and this is why (BE-229)(iii)'s arc-3/arc-4 families are off the
> quantifier. BOBLIG's three, BCORNER's three, BNONUNI's three, BGTWOA's
> three, BEFOURP's three and BLONGARC's four stand unchanged;
> (BE-230)(iii)(a)/(b)/(c) and (BE-238)(iii)(a)/(b)/(c) stand.

> **(BE-245)(iv)** *(**the generalizable lesson**, one level above the
> instance)* (BE-238)(iv) said *"when a target has already been decomposed
> into rungs, split any proposed successor by those same rungs before
> adopting it"*. The sequel is about **mechanisms rather than successors**,
> and it is sharper because a mechanism list looks like a fact rather than
> a claim: **an "and that is all of them" is a headline claim with its own
> driver obligation, and it inherits the quantifier it was written under.**
> (BE-234)'s enumeration was taken on `{ρ_j ≥ 5}`, where the series end and
> the Grassmann floor genuinely exhaust the free mechanisms; carried to
> `Σδ ≤ 6` it dropped the one member that has **no** hypothesis to lose.
> The operational form: **when a region is entered by *removing* a
> hypothesis (here `deg_j(x) = 1`), re-run the mechanism census asking which
> mechanisms *never needed* that hypothesis** — those are the ones an
> inherited list is systematically blind to, because they were invisible
> where the list was taken.
