## §(K-bare-ext) — continuation (direction BWHOLEH, ordinal 102, 2026-09-12): **THE RUNG-3 `Π_x` OBLIGATION IS REFUTED AS A UNIVERSAL OVER ITS STRATUM — a whole-`H` peel with `c₁ + c₂ = 3` is EXHIBITED.** Side 1 is (BE-242)(ii)'s firing cycle glued into a composite; side 2 is a subdivided 3-connected skeleton that is **PATH-SATURATED**, so (BE-45)(ii) supplies `c₂(Π_x) ≥ 1` with no genericity. The tuple is `(δ₁,δ₂,a₁,a₂,ρ₁,ρ₂,c₁,c₂) = (2,4,0,0,2,4,2,1)` — `Σδ = 6`, `slack = 0`, `c₁+c₂ = 3 > 2` — at `a = (0,0)`, side-degree `≥ 2` on **both** sides, side 2 `rnode_shaped`, `verify_pencil_witness` green on the whole `H`, in the generic flag regime, over **both** skeletons and **all six** non-adjacent hub pairs of each. **(BE-244)(i)'s *"0 of 236 196"* is reproduced exactly and its cap is then MOVED: the fence is the BRANCH LENGTH `{1,2,3}`, not the skeleton list** — (BE-244)(ii) named the wrong missing axis. **THE SCOPE TRAVELS WITH THE FIGURE:** the killing point is STEERED, the same `H` ATTAINS at a free draw, so `Good` is DENSE ((BE-69)(ii)) and neither (BE-14) nor half (B) nor — by the F26 consumer check, run first — `hbareSplit` as `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` takes it is reached (*Steps BE246–BE253*)

### Standing notation (on top of *Steps BE148–BE245*)

BSIXRUNG's, verbatim, **read at the definition sites** (`barch.slack_of`,
`barch.violates`, `barch.all_tuples`, `bfour.e_row`, `bfour.side_nums`,
`bfour.gates_of`, `bimage.rho_bar_of`, `bimage.plane_at`,
`binduc.rel_screw_space`, `bline.legal_peel`, `bline.longcore_library`,
`bproper.composite`, `bproper.free_peel`, `bproper.NONADJ`,
`bpeel.rnode_shaped`, `bpeel.SKELETONS`, `bpeel.subdivided`,
`bpeel.delta_pair`, `bdecor.flag_assignment`, `bdecor.draw_branch`,
`bdecor.assemble`, `bunif.flag_frame`):

> **`slack := max(0, δ₁ + δ₂ − 6)`** and the **`Π_x` OBLIGATION**
> `c₁(Π_x) + c₂(Π_x) ≤ 2 + slack`. **RUNG 3** is the locus `Σδ ≤ 6`, where
> `slack = 0` and the obligation **is** `c₁ + c₂ ≤ 2` ((BE-225)(iii)).
> `slack` is a **function of the `δ`s** ((BE-225)(iv)), so rung 3 is a
> **locus**, never a settable parameter.
>
> **`⟨P⟩`** is the span of the hinge lines of a path `P`; **`d_min_i`** is
> the length of a shortest x–y path *inside side `i`*. **(M1)** is
> (BE-45)(i)'s series end, **(M2)** is (BE-45)(ii)'s path saturation
> `δ_i = d_min_i`, **the Grassmann floor** is `c_i ≥ max(0, ρ_i − 4)`
> ((BE-234)).
>
> **THE REGION**, from the dispatch: `a₁ = a₂ = 0`, `Σδ ≤ 6`, side-degree
> `≥ 2` on **both** sides, an internal R-node peel, the generic flag regime
> (`bunif.flag_frame` non-`None`).

**Carrier check, off the landed bodies.** **No `.lean` was opened for
editing and no `lake build` was run** (the 2026-08-05 hold); the one Lean
file *read* is `Molecular/Molecule/Pencil/Escape.lean`, for the F26 consumer
check of *Step BE246*, and its `hbareSplit` binder is quoted below from the
source rather than from a docstring. **No tracked script was modified**: the
driver `notes/scripts/w4/bwholeh.py` is new, it **imports** the landed layer
(including `bsixrung._linear_pyk` rather than a copy of it), and every
configuration is either drawn by it at exact ℚ or produced by a predecessor's
own builder (`bproper.free_peel`). Baseline `HEAD` = `fde0317f`.

---

### Step BE246 — (BE-247): THE CONSUMER, OPENED FIRST (dispatch-log F26) — what a rung-3 refutation reaches, and what it does not

> **(BE-247)(i)** `[PROVED]` *(read at the binder, not at a docstring; the
> dispatch's own first instruction)* The consumer
> `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
> (`CombinatorialRigidity/Molecular/Molecule/Pencil/Escape.lean`) takes
> `hbareSplit` as a **∀-quantified implication whose conclusion is
> `HasPencilRealization K 3 G`** — read at the binder: given `G.Simple`,
> `5 ≤ V(G).ncard`, `G.TwoEdgeConnected`,
> `(∀ H, ¬ H.IsProperRigidSubgraph G 3)`, `G.degree v = 2`, `eₐ ≠ e_b`, the
> two `IsLink`s, `(¬ G.PencilHub a ∨ ¬ G.PencilHub b)`, `e₀ ∉ E(G)`,
> **`¬ PencilNondegFeasible K G`** and
> `HasPencilRealization K 3 (G.splitOff v a b e₀)`, conclude
> `HasPencilRealization K 3 G`. **Its conclusion is EXISTENTIAL.**
> (BE-16)(iii)(a) is the corpus's own statement of why that matters: *"the
> statement is **existential**: `rank ≤ target` holds universally (Step
> BE12), so **one witness per graph settles `G`** and no genericity argument
> is required"*. **Therefore a shortfall at one chart point does not reach
> `hbareSplit`,** and by (BE-69)(ii) it cannot even reach the *piece*: `Good`
> is **dense or empty**, and *"a draw outside `Good` settles nothing"* is
> that clause's own consequence 2. The certificate below is a **steered**,
> i.e. non-generic, chart point.

> **(BE-247)(ii)** *(what a rung-3 certificate DOES reach — quoted from the
> landed clause that priced it, with its hypotheses)* (BE-239)(ii) reads:
> *"a rung-3 certificate is a **SHORTFALL at an `a = 0` chart point in the
> generic flag regime** … **SCOPE, stated before anyone reads it as more
> than it is:** this does **not** refute (BE-14), which is **existential**
> ((BE-16)) with a **dense** good locus ((BE-69)) — a shortfall at one chart
> point of an open stratum leaves half (B) standing. What it would refute is
> the obligation **as a universally-quantified statement over the chart's
> generic-flag stratum**, which is how every consumer in *Steps BE148–BE237*
> uses it."* **That is exactly the object this direction refutes, and no
> larger one.** The prize named in the dispatch — *"the `Π_x` obligation is
> refuted at its own bottom rung"* — is delivered; the gloss *"the carried
> item of `hbareSplit`"* is the **lane**, not the theorem, and the theorem is
> untouched.

> **(BE-247)(iii)** *(the honest register, and it is smaller than a
> `PencilPair` event)* The refuted object is the **universally-quantified**
> `Π_x` obligation over `{a = 0, Σδ ≤ 6, side-degree ≥ 2 both sides,
> internal R-node peel, generic flag regime}` — (BE-235)(ii)'s **26 of 30**
> residue tuples, reproduced independently here at **26** by
> `bwholeh.py cross`. Every consumer that quantified the obligation over
> that stratum (*Steps BE148–BE237*) loses its hypothesis there. `PencilPair
> K 3 G`, `hbareSplit`, `hK`, `hcontract`, (GR-15), (BE-14), the S-mark,
> half (B), half (β), the 2-cut step, class uniformity, cross-pair welding,
> `(BE-E4′)`, the flag base, `(BE-OBL7)` and `(BE-OBLK)` are **untouched**
> **— QUALIFIED 2026-09-12 by (BE-266) (direction BTAKERS): untouched AT A
> GENERIC CHART POINT, which is the quantifier every verdict clause in this
> range carries, and REFUTED as universals at this direction's own
> certificate. Without the qualifier this list contradicts the verdict clause
> above it.**
> **No termination-ledger entry fires**: E1/E2/E3 are §(K-grid) objects.

### Step BE247 — (BE-248): THE FENCE `blindaxes.py` CANNOT LIST — `bline.longcore_library()`'s side-1 shapes, checked at the GENERATOR

> **(BE-248)(i)** `[MEASURED]` *(GLAMPROP bar (ii): a population's provenance
> is checked at the generator, not at a keyword)* `bline.longcore_library()`
> returns **27** side-1 shapes, and **every one of them is a cycle AT `x`
> with `y` hung off a TAIL** — read at the body: the two families are
> `cycle(cyc) at x + tail(m) from <hub>` (`cyc ∈ {4,5,6}`, `m ∈ {1..6}`, 18
> shapes) and `… from a0 (c_1 a HUB)` (`cyc ∈ {4,5,6}`, `m ∈ {1,3,5}`, 9
> shapes), both built by the module-local `_arc(E, hub, 'y', m, tag)`.
> Measured over the library: **`deg₁(x) = 2` at 27/27** — which is the axis
> (BE-229)(ii) opened and reports — **and `deg₁(y) = 1` at 27/27**, which
> nothing in the (BE-14) thread records. `bwholeh.py` (helper `dmin_in`,
> `bline.longcore_library`).

> **(BE-248)(ii)** `[PROVED]` *(why that shape can never carry the
> certificate, and it is structural rather than statistical)* `deg₁(y) = 1`
> means **every x–y path of side 1 leaves `y` by the same edge**, which is
> (BE-45)(i)'s hypothesis at `y` — side 1 is a **series end at `y`** at every
> row of the landed population. That is harmless for `c_i(Π_x)` (it is a
> statement at `Π_y`), and it is not why the population fails. What *is*
> structural: (BE-242)(i)'s firing mechanism needs the closed star of `x`
> **inside the side** to be `{p_x, p_{P,1}, p_{Q,1}}` **with `P`, `Q` two
> internally-disjoint x–y arcs**, so that steering `p_y` moves **both** arc
> spans. In a `longcore_library()` shape the two paths out of `x` **re-merge
> at the cycle's far hub and then share the whole tail**, so `p_y` sits on
> the shared tail and its two systems are not independent. **So every
> `longcore_library()` shape is OUTSIDE (BE-242)(i)'s hypothesis, and
> (BE-242)(ii)'s steering is unavailable on it** — not because of a keyword
> default, but because of what its generator builds. *Scope, self-caught
> before it was written as a conclusion: this says the landed **mechanism**
> cannot be run there, NOT that no such side can ever fire by some other
> route; the evidence that they in fact do not fire below `ρ_i = 6` is
> (BE-243)(ii)'s measurement, which is a population statement.* This is the
> class of fence `blindaxes.py` cannot list, and the coordinator's own
> `aglu._pool8()` miss one commit earlier is the same class.

> **(BE-248)(iii)** *(the un-fencing, and it costs one new generator and no
> harness edit)* `bwholeh.cycle_side(m₁, m₂)` returns the cycle through
> **both** `x` and `y` — (BE-242)(ii)'s own firing shape — and is handed to
> the **landed** `bline.legal_peel(side1, skname, xy, prof)` and
> `bproper.composite`, which already take `side1` as a parameter. So the
> composite peel is built by the landed layer; only the side-1 *generator* is
> new. **`bproper.NONADJ` is also un-fenced**: it lists **3** of K33's **6**
> skeleton-non-adjacent hub pairs and **3** of the prism's **6**, and under a
> **non-uniform** profile the omitted three are not automorphic images of the
> listed three. `bwholeh._nonadj_pairs` enumerates all six of each, and every
> figure below runs over all twelve.

### Step BE248 — (BE-249): THE CERTIFICATE — a whole-`H` peel at rung 3 with `c₁ + c₂ = 3`, so the `Π_x` obligation is REFUTED there

> **(BE-249)(i)** `[PROVED]` *(the construction, and both halves are landed
> clauses — nothing here is a new mechanism)* Take side 1 to be a **cycle
> through `x` and `y` with arcs (4,4)**: by (BE-242)(i) the closed star of
> `x` inside the side is `{p_x, p_{P,1}, p_{Q,1}}`, so (CH-1) **forces**
> `π_x = ⟨p_x, p_{P,1}, p_{Q,1}⟩` and `Π_x = ⟨ℓ_P, ℓ_Q⟩`, and `c₁(Π_x) = 2`
> is the pair of linear systems in `p_y` that (BE-242)(ii) solves —
> `δ₁ = ρ₁ = 2`, `a₁ = 0`. Take side 2 to be a **subdivided 3-connected
> skeleton that is PATH-SATURATED**, `δ₂ = d_min₂ = 4`: by (BE-45)(ii),
> which is `[PROVED]` and carries **no genericity, no draw and no degree
> hypothesis**, `ρ̄₂ = ⟨P⟩` for a shortest x–y path `P` of side 2 and hence
> `ρ̄₂ ∩ Π_x ⊇ ⟨ℓ_{P,1}⟩ ≠ 0`, i.e. **`c₂(Π_x) ≥ 1`**. Then
> `Σδ = 2 + 4 = 6` — **rung 3**, `slack = 0` — and `c₁ + c₂ = 3 > 2`. ∎
> **The whole content of the construction is that the two halves can be
> carried by ONE `H` at ONE flag**, which is what (BE-245)(i) left open and
> what (BE-242)(iii) priced.

> **(BE-249)(ii)** `[CONSTRUCTED]` *(exact ℚ, seed base `20260912`,
> `bwholeh.py peel`; the numbers are the whole claim)* **108** fully-gated
> whole-`H` rows over **2 skeletons × all 6 skeleton-non-adjacent hub pairs
> of each × 2 path-saturated profiles + 1 non-saturated control profile ×
> 3 independent seeds**. Result, with **no other tuple occurring**:
>
> | side 2 | rows | `t = (δ₁,δ₂,a₁,a₂,ρ₁,ρ₂,c₁,c₂)` | in-regime | obligation | `H` attains |
> |---|---|---|---|---|---|
> | **PATH-SATURATED** | **72** | **`(2,4,0,0,2,4,2,1)`** | **72/72** | **VIOLATED 72/72** | **no, 72/72** |
> | not saturated (same `δ₂ = 4`) | 36 | `(2,4,0,0,2,4,2,0)` | 36/36 | holds 36/36 | yes, 36/36 |
>
> Every row passes `boblig._assert_gates`' own battery, asserted row by row:
> (CH-1) `hcard` on `H`, min degree `≥ 2`, girth `≥ 4`, `deg_H(x) ≥ 3` and
> `deg_H(y) ≥ 3`, `x ≁ y`, **`bpeel.rnode_shaped` on side 2**, the two sides
> covering `H` with **distinct** edge counts (so the side identification is
> not ambiguous — (BE-208)(ii)'s scope check), and
> `bdecor.verify_pencil_witness` on the whole `H` (it is inside
> `bdecor.assemble`, so a non-witness is never returned). Added here:
> `bunif.flag_frame` non-`None` (**the generic flag regime, on `H`**) and
> `deg_i(x) ≥ 2` on **both** sides. The control row differs from the killing
> row **only in whether side 2 is path-saturated** — same skeletons, same
> hub pairs, same `δ₂ = 4`, same steered side 1 — so the `c₂ = 1` is the
> saturation and not an artefact of the builder.

> **(BE-249)(iii)** `[CONSTRUCTED]` *(the named certificate, exact over ℚ —
> this is a **proof** and needs no cap)* `K33` at hub pair `(A, B)`, branch
> profile `(2,2,2,2,4,4,2,5,5)` on
> `bpeel.SKELETONS['K33'] = [(A,D),(A,E),(A,F),(B,D),(B,E),(B,F),(C,D),(C,E),(C,F)]`;
> side 1 the (4,4) cycle `x–u₁–u₂–u₃–y`, `x–v₁–v₂–v₃–y` (renamed `s1u*`,
> `s1v*` by `bproper.composite`). `|V(H)| = 31`, `|E(H)| = 36`,
> `|E(side 1)| = 8`, `|E(side 2)| = 28`; gates
> `{hcard: True, mindeg: 2, girth: 8, degx: 5, degy: 5, adj: False,
> rnode_far: True, deg1x: 2, deg2x: 3, deg1y: 2, deg2y: 3}`. Note
> **`deg₁(y) = 2`**: the certificate is off (BE-45)(i)'s series-end
> hypothesis at `y` as well as at `x`, which the landed population is not
> ((BE-248)(i)).
>
> ```
> E   = [('A', 's0_0'), ('A', 's1_0'), ('A', 's1u1'), ('A', 's1v1'), ('A', 's2_0'), ('B', 's3_0'), ('B', 's4_0'), ('B', 's5_0'), ('C', 's6_0'), ('C', 's7_0'), ('C', 's8_0'), ('s0_0', 'D'), ('s1_0', 'E'), ('s1u1', 's1u2'), ('s1u2', 's1u3'), ('s1u3', 'B'), ('s1v1', 's1v2'), ('s1v2', 's1v3'), ('s1v3', 'B'), ('s2_0', 'F'), ('s3_0', 'D'), ('s4_0', 's4_1'), ('s4_1', 's4_2'), ('s4_2', 'E'), ('s5_0', 's5_1'), ('s5_1', 's5_2'), ('s5_2', 'F'), ('s6_0', 'D'), ('s7_0', 's7_1'), ('s7_1', 's7_2'), ('s7_2', 's7_3'), ('s7_3', 'E'), ('s8_0', 's8_1'), ('s8_1', 's8_2'), ('s8_2', 's8_3'), ('s8_3', 'F')]
> s1  = [('A', 's1u1'), ('A', 's1v1'), ('s1u1', 's1u2'), ('s1u2', 's1u3'), ('s1u3', 'B'), ('s1v1', 's1v2'), ('s1v2', 's1v3'), ('s1v3', 'B')]
> aff = {'A': ['15', '-16', '23'], 'B': ['652518137/2865447', '-608425933/2865447', '0'], 'C': ['-11/19', '2/19', '-15/19'], 'D': ['14/9', '8/9', '2/3'], 'E': ['4/7', '13/7', '-19/7'], 'F': ['-14/11', '-6/11', '0'], 's0_0': ['78260819/5292750', '-41221457/10585500', '7/5'], 's1_0': ['19831107/1354318', '-37233211/6771590', '-3/2'], 's1u1': ['21', '94', '93'], 's1u2': ['-61', '14', '-58'], 's1u3': ['-1', '-164', '-337'], 's1v1': ['14', '2', '-32'], 's1v2': ['-88', '-34', '-35'], 's1v3': ['7', '-488/3', '-211/3'], 's2_0': ['38050352/2759195', '-89401212/2759195', '2'], 's3_0': ['230050668872105809/252714342235200', '-186257750641370077/505428684470400', '-11/20'], 's4_0': ['-221088447202497/315305987029', '2/11', '-15/11'], 's4_1': ['6/7', '-2/7', '3/14'], 's4_2': ['-27886/3509', '9/11', '-8/11'], 's5_0': ['-20416957844033/28664180639', '19/7', '-13/7'], 's5_1': ['-8/3', '10/3', '-3/2'], 's5_2': ['-2069/898', '-9/2', '15/4'], 's6_0': ['30220353/17904775', '-20855192/17904775', '-13/7'], 's7_0': ['-16994/21249', '5/3', '-7/9'], 's7_1': ['-7/4', '-15/4', '-5/4'], 's7_2': ['5/7', '19/7', '-6/7'], 's7_3': ['-25215/5104', '-9/16', '-9/16'], 's8_0': ['78343/2361', '-14', '-17'], 's8_1': ['9/10', '9/20', '3/5'], 's8_2': ['-5/16', '1/8', '9/16'], 's8_3': ['-367/2694', '-7/2', '1/2']}
> ```

### Step BE249 — (BE-250): THE SHORTFALL, read directly at the `H` layer — and the two controls that make the certificate evidence rather than a coincidence

> **(BE-250)(i)** `[MEASURED]` *(the event (BE-239)(ii) predicted, measured
> at the `H` layer and NOT inferred through (BE-86)(i))* At the certificate,
> `bimage.rho_bar_of` on the **whole** `H` gives **`dim M(H) = 7`** while
> `6 + def₃(H) = 6 + 0 = 6`: **`H` does NOT attain**, with an excess of
> **1** motion. `dim M(H) ≥ 6 + def₃(H)` is the universal partition cap and
> equality is attainment ((BE-86)(i)), so a shortfall is an **excess** of
> motions — *this direction first wrote the assertion the other way round
> and the assertion is what caught it.* Cross-checked against the side layer
> by (BE-22)(i) in the form (BE-86)(i) proves it —
> `dim M(H) = 6 + f₁ + f₂ + a₁ + a₂ − dim(ρ̄₁+ρ̄₂)` — asserted, with
> `dim(ρ̄₁+ρ̄₂) = 5` against the target `min(Σδ,6) + a₁ + a₂ = 6`. So the
> certificate is a **SHORTFALL at an `a = 0` chart point in the generic flag
> regime**, exactly the event (BE-232)(i) calls *"far larger"*. **Its scope
> is (BE-247)(i)–(ii)'s and no wider.** `bwholeh.py cross`, 3 of 3
> independent draws, every line an `assert`.

> **(BE-250)(ii)** `[MEASURED]` *(what is asserted, re-read off the driver
> rather than recalled — the F-clause on *"we checked it N ways"*)* At each
> of 3 independent draws `bwholeh.py cross` asserts, and all pass: (a)
> `ρ̄_i` agrees **as a SPACE** between `bfour.side_nums` (i.e.
> `bimage.rho_bar_of`) and `binduc.rel_screw_space`, on **both** sides;
> (b) `Π_x` computed from `bimage.plane_at` on the **whole `H`** (not on
> side 1) is the same 2-dimensional space `bfour.e_row` uses; **(c)**
> `c₁ = 2` is **containment** `Π_x ⊆ ρ̄₁`, not a dimension coincidence;
> (d) (BE-45)(ii)'s witness vector is **named** — a first hinge line
> `p_x ∧ p_w` of side 2 at a neighbour `w` of `x` lies in `ρ̄₂ ∩ Π_x` (at
> the named certificate, `w = s0_0`, the first vertex of the `(A,D)` branch,
> which is the shortest x–y path's first edge); (e) the tuple is one of
> the **26** rung-3 residue tuples, the residue being recomputed here from
> `barch.all_tuples()` with (BE-213)(i)'s Grassmann-floor legality imposed
> and reproducing (BE-239)(i)'s **26** independently; (f) `d_min₁ ≥ 4`,
> so the firing side obeys (BE-241)(iii); (g) `ρ_i = δ_i + a_i` on both
> sides, so the `a = (0,0)` reading is measured and not assumed.

> **(BE-250)(iii)** `[MEASURED]` *(**the F13 control that locates the gap**,
> and it is the most informative row in the direction)* `bproper.free_peel`
> — the **landed** builder, side 1 **not** steered — run on the **same**
> composite `K33 (A,B) (2,2,2,2,4,4,2,5,5)` gives, at **6 of 6** draws,
> `t = (2,4,0,0,2,4,**0**,1)`: in-regime, `a = (0,0)`, `Σδ = 6`, obligation
> **HOLDS** — and **`c₂ = 1`**. So the landed builder **already reaches the
> non-firing half** on a path-saturated side 2, at the first draw, with no
> steering at all. Combined with the second control of (BE-249)(ii) —
> non-saturated side 2 with the steered side 1, `c = (2,0)` at 36/36 — the
> two halves are **separately free** and the whole cost of the certificate
> was **pairing them in one `H`**. This is why (BE-245)(i) could report the
> firing half exhibited and the non-firing half absent: the landed
> population's side 2 is never path-saturated ((BE-251)), and its side 1 is
> outside the only landed firing mechanism ((BE-248)(ii)).

### Step BE250 — (BE-251): (BE-244)(i)'s *"0 of 236 196"* is REPRODUCED and its cap is MOVED — the fence is the BRANCH LENGTH, not the skeleton list

> **(BE-251)(i)** `[MEASURED]` *(the reproduction first, because a moved cap
> is only readable against the fenced figure)* `bwholeh.py sat` at branch
> lengths `{1,2,3}`, all three of `bpeel.SKELETONS` and **every** hub pair
> non-adjacent in the skeleton (K4 contributes 0, K33 six pairs, prism six
> pairs): **236 196 sides enumerated, PATH-SATURATED at 0.** This
> reproduces (BE-244)(i)'s headline figure **exactly**, independently, in a
> new driver. Seedless and exhaustive over that family.

> **(BE-251)(ii)** `[REFUTED]` *(a landed clause's **disclosed** cap,
> refuted by moving it one step — and the clause named the wrong axis)*
> (BE-244)(ii) reads: *"**CAP, and it is the whole of the reading:** the
> family is **three skeletons** with branch lengths in `{1,2,3}`. *"Not
> found under that family"*, never *"does not exist"* — **a larger
> 3-connected core is exactly what is not enumerated**, and
> `bpeel.SKELETONS` is the harness's own list, not a classification."* The
> disclosure is correct and the **diagnosis is wrong**: the core is not the
> missing axis. At branch lengths `{1,2,3,4}`, **the same three skeletons
> and the same hub pairs**, `bwholeh.py sat` gives **3 145 728 sides
> enumerated, PATH-SATURATED at 100 656** — of those **48 444** at
> `δ₂ ≤ 4`, and **7 440** with every branch `≥ 2`, which is the subfamily
> this direction can draw ((BE-251)(iv)). Per (skeleton, hub pair): **9 951**
> at each of K33's six, **6 825** at each of the prism's six. **So the
> phenomenon (BE-244)(i) reports absent appears at branch length 4 — one
> step past the fence — and the enumeration that found 0 was blind to it by
> a constant, not by a classification.**

> **(BE-251)(iii)** `[CONSTRUCTED]` *(and the one-step reading is not a
> technicality: a certificate lives inside the moved cap)* `bwholeh.py`
> builds the rung-3 killing row at `K33 (A,B)` with profile
> `(2,2,2,2,4,4,4,4,4)` — **every branch length in `{2,4} ⊂ {1,2,3,4}`** —
> giving `t = (2,4,0,0,2,4,2,1)`, in-regime, `H` not attaining, at 2 of 2
> independent draws. So the certificate does **not** need the length-5
> branches of (BE-249)(iii)'s named profile; those are incidental.

> **(BE-251)(iv)** *(a fence of THIS direction's own, disclosed rather than
> buried)* Every profile drawn here has **all branch lengths `≥ 2`**. This is
> **not** mathematics: `bdecor.flag_assignment` places a hub point **before**
> it checks the plane constraint, so it cannot honour a **fixed** flag at `x`
> when a skeleton edge at `x` has branch length 1 (the hub neighbour must
> then lie in `π_x`, and the sampler draws it free). The flag at `x` must be
> fixed here because side 1 pins it. **A length-1 branch away from `x` and
> `y` is not excluded by anything and is simply not swept** — 100 656 minus
> 7 440 is mostly that, and it is a lower bound on the reachable family, not
> an upper one. Fixing `flag_assignment`'s placement order would open it; no
> tracked script was modified here.

> **(BE-251)(v)** `[PROVED]` *(a cheap structural fact the enumeration
> needs, asserted rather than assumed)* `bpeel.rnode_shaped(side2, x, y)` is
> **independent of the branch profile**: suppressing every degree-2 vertex of
> `side2 + (x,y)` returns the **skeleton plus the virtual edge** whatever the
> lengths are, so the test depends only on (skeleton, hub pair). Asserted in
> `bwholeh.py sat` at four extreme profiles per (skeleton, hub pair) rather
> than called per profile — which is also what makes the 3 145 728-side
> enumeration affordable.

### Step BE251 — (BE-252): the Grassmann-floor EQUALITY is a property of the sampled LIBRARY, not a law of the region — the dispatch's stated mechanism, eliminated

> **(BE-252)(i)** `[REFUTED]` *(the dispatch's own mechanism, refuted
> cheaply and first, as §7's 2026-09-10 amendment requires)* The dispatch
> offered as mechanism: *"I could not rule out that (BE-243)(ii)'s
> Grassmann-floor equality is **forced** at `a = 0` rather than a property of
> the sampled population … one row anywhere with `c_i > max(0, ρ_i − 4)` at
> `a = 0` kills it."* **Killed, twice over, in the same row.** At the
> certificate `a = (0,0)` and **both** sides exceed the floor:
> `c₁ = 2 > max(0, ρ₁ − 4) = max(0, 2−4) = 0` and
> `c₂ = 1 > max(0, ρ₂ − 4) = max(0, 4−4) = 0`. Asserted in
> `bwholeh.py cross`. So the equality is **not forced by `a = 0`**, and the
> dispatch's *reason* for its (wrong) negative verdict falls independently of
> the verdict.

> **(BE-252)(ii)** *(the SCOPE, so the landed measurement is not read as
> refuted when it is not)* (BE-243)(ii) — *"At 108 of 108 rows and on both
> sides — 216 side-instances, 0 exceptions — `c_i(Π_x)` equals the Grassmann
> floor"* — is a **measurement of one population** (`bproper.free_peel` over
> `bline.longcore_library()`), and **that measurement is untouched**: no row
> of it is contradicted here, and this direction's sides are outside it by
> construction ((BE-248)). What is refuted is any reading of it as a **law**
> of the region, and (BE-243)(iii) is the clause that comes closest to such a
> reading — *"so (BE-45)(iv)'s conclusion is correct only below `ρ_i = 5` and
> its honest form is `c_i = max(0, ρ_i − 4)` — measured here at 216/216, in
> the peel habitat"*. **In the peel habitat, at `a = 0`, in-regime, at an
> internal R-node peel, `c_i > max(0, ρ_i − 4)` occurs** — on the FIRING
> side at all **108** rows of (BE-249)(ii) (`c₁ = 2`, `ρ₁ = 2`, floor `0`),
> and on the NON-FIRING side at the **72** killing rows plus the **6** free
> draws of (BE-250)(iii) (`c₂ = 1`, `ρ₂ = 4`, floor `0`). The
> honest form of (BE-243)(iii) is therefore `c_i ≥ max(0, ρ_i − 4)`, the
> floor itself ((BE-234)), with equality a property of the library.

> **(BE-252)(iii)** *(and the attributed CAUSE is corrected too, which is
> the part that would have misdirected the next direction)* (BE-243)(ii)
> attributes the floor-equality to the builder: *"the population is in the
> right length regime and still never fires, because `free_peel` **does not
> steer**"*. The F13 control of (BE-250)(iii) runs **`bproper.free_peel`
> itself**, unsteered, and gets `c₂ = 1` strictly above the floor at 6 of 6
> draws. **So not steering is not the cause.** The cause is that
> `bline.longcore_library()`'s side 1 is outside the landed firing
> mechanism ((BE-248)(ii)) **and**
> boblig's job-list profiles put side 2 inside (BE-244)(i)'s `{1,2,3}` family,
> where path saturation is absent ((BE-251)(i)). Two independent library
> facts, neither of them a property of `free_peel`.

### Step BE252 — (BE-253): THE VERDICT, its exact scope, and the board

> **(BE-253)(i)** `[REFUTED]` *(**the verdict**, stated with the quantifier
> it actually kills)* The `Π_x` obligation at `a = 0`, `Σδ ≤ 6`, side-degree
> `≥ 2` on both sides, at an internal R-node peel in the generic flag regime
> — **(BE-235)(ii)'s 26 of the 30 residue tuples, the region (BE-245)(i) left
> NEITHER PROVED NOR REFUTED** — is **REFUTED as a universally-quantified
> statement over that stratum**, by an exhibited exact-ℚ whole-`H`
> certificate with `c₁ + c₂ = 3` at `Σδ = 6`, `slack = 0`, `a = (0,0)`
> ((BE-249)). One certificate is a proof and carries **no cap**; it was
> reproduced at **72 of 72** rows over 2 skeletons × 6 hub pairs each × 2
> profiles × 3 seeds, with a matched **36 of 36** negative control, and it
> is **invariant in the coordinate box** (`bdecor` `s ∈ {7, 20, 50}`, same
> tuple at 6 of 6). **(BE-245)(iii)(b) is discharged**: the open half —
> `c_j(Π_x) ≥ 1` at the same flag — is supplied by (BE-45)(ii) path
> saturation, and no effort was spent on the firing side, which was taken
> from (BE-242)(ii) unchanged.

> **(BE-253)(ii)** *(**THE SCOPE**, and it is the sentence that must travel
> with the verdict everywhere it is quoted)* The killing configuration is
> **steered, hence non-generic**. The **same** `H` at a **free** draw
> (`bproper.free_peel`, 6 of 6, in-regime) gives `t = (2,4,0,0,2,4,0,1)` and
> **`H` ATTAINS**. So `Good(H; x, y) ≠ ∅`, and by (BE-69)(ii) it is
> **DENSE** — the shortfall of (BE-250)(i) is a phenomenon **at a special
> point** of a piece whose good locus is dense, which is precisely the case
> (BE-69)(ii)'s consequence 3 distinguishes from `Good = ∅`. Consequently:
> (BE-14) is **NOT refuted**, half (B) is NOT refuted, and **nothing here
> reaches `hbareSplit`** ((BE-247)(i)). What is refuted is the obligation
> **as a universal statement over an open stratum**, which (BE-239)(ii)
> records as *"how every consumer in Steps BE148–BE237 uses it"*. A
> consumer that only ever needed the obligation **at a generic chart point**
> is untouched and should say so explicitly rather than inherit this row.

> **(BE-253)(iii)** *(**the board**)* **What moved.** The rung-3 `Π_x`
> obligation **REFUTED** as a universal over its stratum ((BE-249));
> (BE-244)(i)'s *"0 of 236 196"* **reproduced** and its disclosed cap
> **moved**, with the missing axis re-identified as the **branch length**
> rather than (BE-244)(ii)'s *"a larger 3-connected core"* ((BE-251));
> `bline.longcore_library()`'s side-1 shape identified as a **generator-level
> fence** that no keyword scan can list, with `deg₁(y) = 1` at 27/27 recorded
> for the first time ((BE-248)); (BE-243)(ii)'s Grassmann-floor **equality**
> scoped to the sampled library and its attributed cause (*"`free_peel` does
> not steer"*) corrected ((BE-252)); `bproper.NONADJ`'s 3-of-6 hub-pair list
> un-fenced to all 6 per skeleton ((BE-248)(iii)); `bpeel.rnode_shaped`
> proved profile-independent ((BE-251)(v)); a **SHORTFALL** at an `a = 0`
> in-regime chart point exhibited and read directly off `dim M(H)`
> ((BE-250)(i)). **What did NOT move.** `PencilPair K 3 G`, `hbareSplit`,
> `hK`, `hcontract`, (GR-15), (BE-14), the S-mark, half (B), half (β), the
> 2-cut step, class uniformity, cross-pair welding, `(BE-E4′)`, the flag
> base, `(BE-OBL7)`, `(BE-OBLK)` *(these three **at (Q-gen)**; as universals
> they fall at this certificate — (BE-266))*, and **every landed measurement** —
> including (BE-243)(ii)'s 216/216 and (BE-244)(i)'s 236 196, both of which
> this direction *reproduces or leaves intact* rather than contradicts.
> **No `.lean` opened for editing, no `lake build`**; the 2026-08-05 hold
> untouched. **The E-rider:** no termination-ledger entry fires; E1/E2/E3
> are §(K-grid) objects.

> **(BE-253)(iv)** *(the dispatch's prediction, scored — verdict and
> mechanism separately, per §7)* **VERDICT: the spec predicted NEGATIVE
> ("no such peel gets exhibited inside this dispatch") and is REFUTED.**
> **MECHANISM: separately REFUTED** ((BE-252)(i)) — the Grassmann-floor
> equality is not forced at `a = 0`, and both sides of the certificate
> exceed the floor. **TELL: FIRED**, and it was live in all three senses the
> spec checked: a whole-`H` peel at `Σδ ≤ 6` with `c₁ + c₂ = 3` is exactly
> the refutation, it was not already satisfied (0 of the landed 84), and the
> region was non-empty. **And the spec's own *"where I expect to be wrong"*
> sentence was RIGHT about the class and WRONG about the instance**: it
> predicted *the fence, not the theorem*, and named
> `bline.legal_peel(xy=('A','B'))` and `bproper.run_peel(nseed=1)`. The
> fence was real but neither of those was it — `xy` is un-fenced here and
> **changes nothing** (all twelve pairs kill), and the seed count changes
> nothing (72 of 72). The two fences that mattered were **the side-1
> generator** ((BE-248)) and **(BE-244)(i)'s branch-length family**
> ((BE-251)), and the second is a cap the corpus had already *disclosed* and
> mis-diagnosed. Both are of the class the spec's own last bullet names as
> unlistable by `blindaxes.py`.

### Step BE253 — (BE-254): the bars this adds, what remains open, and the generalizable lesson

> **(BE-254)(i)** *(**the bars**, as §8's rule requires)* *(a)* **No further
> effort may be spent trying to PROVE the rung-3 `Π_x` obligation as a
> universal over its stratum** — it is refuted by an exhibited certificate
> ((BE-249)), and a proof attempt is now an attempt to prove a false
> statement. The live successor is the **generic-chart-point** form, which
> this direction does **not** touch ((BE-253)(ii)). *(b)* **A *"not found
> under cap C"* whose cap is an ENUMERATED FAMILY must name the axis that
> would break it, and that naming is a headline claim with its own driver
> obligation** — (BE-244)(ii) named *"a larger 3-connected core"*; the axis
> was the **branch length**, one step past the fence, on the same three
> skeletons ((BE-251)(ii)). *(c)* **A side LIBRARY is a quantifier, not a
> convenience.** `bline.longcore_library()` fixes `deg₁(y) = 1` at 27/27 —
> a hypothesis nothing in the (BE-14) thread records, because the thread only
> ever audited the degree at `x` ((BE-248)(i)). Audit a population's side
> shapes at **both** terminals. *(d)* **`bdecor.flag_assignment` cannot
> honour a fixed flag at a terminal with a length-1 branch at that
> terminal** — it places the hub point before checking the plane. Any
> direction that needs length-1 branches at `x`/`y` must **fix the placement
> order**, not route around it ((BE-251)(iv)). BSIXRUNG's three
> ((BE-245)(iii)(a)/(b)/(c)) stand: (a) unchanged; (b) is **discharged**, not
> withdrawn — the open half it named is now closed by (BE-45)(ii); (c)
> unchanged and **respected** (`d_min₁ = 4` at the certificate, asserted).
> BOBLIG's three, BCORNER's three, BNONUNI's three, BGTWOA's three,
> BEFOURP's three and BLONGARC's four stand unchanged.

> **(BE-254)(ii)** *(**what remains open, and who decides it**)* (1) Is
> there an `H` in the region with `Good(H; x, y) = ∅`, i.e. a shortfall that
> holds **identically** on the chart? Not settled here — the certificate's own
> `H` attains at a free draw ((BE-253)(ii)), so this direction exhibits the
> obligation failing at a special point and **not** a bad piece. That is the
> statement that would begin to reach (BE-14), and it is a different search.
> (2) Which consumers in *Steps BE148–BE237* actually needed the
> **universal** obligation and which only needed it at a **generic** chart
> point? Each such consumer must be re-read; **this is the board's call, not
> a measurement**, and it is the work this refutation creates. (3) Does
> the obligation hold at **generic** chart points of the same stratum? The
> **6** genuinely free draws of (BE-250)(iii) say yes, as do the **36**
> steered-but-non-saturated control rows of (BE-249)(ii) — but that is a
> population and not a theorem.

> **(BE-254)(iii)** *(**the generalizable lesson**, one level above the
> instance)* (BE-245)(iv) said *"an 'and that is all of them' is a headline
> claim with its own driver obligation, and it inherits the quantifier it was
> written under."* The sequel is about **caps rather than mechanism lists**,
> and it is sharper because a cap is already written down as a disclosure —
> so it reads as handled. **A disclosed cap carries a second, usually
> unstated claim: which axis, if moved, would change the answer. That second
> claim is not disclosed by disclosing the first, and it is exactly as
> falsifiable.** (BE-244)(ii) disclosed its family honestly and in the same
> breath guessed the missing axis; the guess was wrong by one integer, and
> five landed clauses were written on the strength of the 0. The operational
> form: **when a cap is disclosed, move each of its axes by ONE step before
> building on the figure** — not to the limit, one step. Here `{1,2,3}` →
> `{1,2,3,4}` took the count from **0** to **100 656**.

---

**Confidence, and what would change this.** The certificate is
**exhibited** at exact ℚ with every gate asserted, so the refutation of
(BE-253)(i)'s universal statement is a **proof** and would be changed only
by an error in the landed primitives it calls (`bfour.side_nums` /
`bimage.rho_bar_of`, cross-checked here against `binduc.rel_screw_space` as
spaces; `bpeel.delta_pair`, cross-checked against `bfour.e_row`'s `δ`;
`bdecor.verify_pencil_witness`, inside `bdecor.assemble`) — a single shared
error in two independent readings of `ρ̄_i` would be needed. **(BE-251)(ii)'s
counts are exhaustive over the stated family and seedless**; they would move
only if `bpeel.rnode_shaped`'s profile-independence ((BE-251)(v)) were
false, which is asserted. **(BE-253)(ii)'s scope is the fragile part**: it
rests on 6 free draws of one `H`, and a free draw that failed to attain would
make this a `Good = ∅` claim instead — a *larger* event, so the reading here
is the conservative one. **This section merges into §(K-bare-ext) as a new
continuation file** `notes/pencil/workbook/bare-ext/BWHOLEH.md`, matching
BSIXRUNG's shape.

**Driver.** `notes/scripts/w4/bwholeh.py` — modes `sigma` (the combinatorial
region, seedless, ~8 s; its `maxlen` defaults to **2** for cost, the
branch-length axis being covered exhaustively by `sat` instead), `peel` (the
certificate sweep, ~261 s at the defaults), `sat` ((BE-244)(i)'s enumeration
with the cap moved; ~35 s at `{1,2,3}`, ~509 s at `{1,2,3,4}`), `cross` (the
`H`-layer hardening + the F13 control, ~42 s), and `validate`
(`sat{1,2,3}` + a reduced `peel` + `cross`, ~180 s, run green end-to-end at
`fde0317f`). Seed base `20260912`; exact ℚ throughout;
`bsixrung._linear_pyk`, `_in_span` and `_rand_pt` are **imported**, not
copied. **Self-caught while writing this paragraph:** `sigma`'s original
default `maxlen = 4` is ~12.6 M composite builds and does not finish — a
mode that cannot be run is not a driver.
