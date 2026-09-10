## §(K-out) — (OUT)'s hypothesis, measured: the bad locus is **nonempty on every class shape's chart**, so no counting argument can ever deliver it ((OC-3)); availability is confirmed **pointwise** over two disjoint pools, the **combinatorial half does not deliver it**, and the pass surfaced a **harness defect** ((OC-7))

Answering §(K-Λ) *What would change this* item (viii) and §(K-Λ) *Step 5a*'s
*"(OUT)'s hypothesis has never been evaluated anywhere in the arc … That is a
**new driver mode**, not run by this pass."* Read against §(K-Λ), whose
notation this section inherits verbatim: (OUT), (Λ0a)–(Λ0i), (Λ0f′), (Λ1),
(Λ2), (Λ3) are all §(K-Λ)'s, and their qualified form is used here per
`notes/Pencil-labels.md` clause L3.

**Headline, negative first, because the negative is the load-bearing result.**

- **(OC-3) — no counting argument can ever deliver (OUT)'s hypothesis.** On the
  pencil chart `C₁ = C(b, x₁)` is confined to the 2-dimensional pencil `L_b` of
  lines through `pt(b)` inside the panel `Π(b)`, while the far relative twist
  space `R₁` does not see `pt(x₁)` at all; `dim R₁ = 5` then forces
  `dim(R₁ ∩ L_b) ≥ 5 + 2 − 6 = 1`. So **`{λ₁ = 0}` is nonempty at every class
  shape in the enumerated scope** — exactly one marked direction of `x₁`'s
  pencil — and no count, no matroid statement, and no argument that does not
  see the placement can ever conclude `λ₁ ≠ 0`. Verified on-chart at every
  frame it was computed: `dim R = 5` and `dim(R ∩ L) = 1`, never 2.
- **The combinatorial half does not deliver availability, and this must not be
  quoted as though it did.** **(OC-2)**'s clean 4296-pair result — uniform
  `χ = 0`, `def(H/X) = def(H/Y) = 0`, `(μ, dim R, A) = (1, 5, 0)` on both sides
  — collapses to **one** measured fact (rigidity of `H/X`; the rest is
  arithmetic), and `deficiency` is the ***ambient*-generic** count, which cannot
  see the chart confinement (OC-3) is about. It does **not** discharge (OUT).
- **The positives are real, and they are pointwise.** **(OC-5)** POOL-G (4
  habitats × seeds 200–299, 357 frames): distribution `322/17/17/1`; (OUT)'s
  hypothesis — the disjunction — holds at **356/357**, its *conclusion*
  separately verified at **356/356**, and (Λ0d) fails at **0/357** so the
  conditionality guard never fires in this pool. **(OC-6)** POOL-S (41 shapes /
  90 splits / 270 frames, **disjoint** from POOL-G): **270/270**, and **zero**
  (split, companion) pairs are silent at every probed seed. **(OC-1)** *Step
  5a*'s hinge-rate reading is exact and now driver-asserted:
  `λ₁ = 0 ⟺ C₁ ∈ V_bc ⟺ dim{m(b) − m(X)} = 1 ⟺ C₁ ∈ R₁`, at 46 frames.
  **(OC-4)** `--build` constructs `λ₁ = λ₄ = 0` at all four habitats keeping
  every (Λ0) clause, the target rank, `dim R_a = 1` and all four
  `IsNondegPencilRealization` conjuncts — at 3 of the 4 with **no** coincident
  hinge line — and `deg_t Q(z(t)) = 4` there, so **the escape holds exactly
  where (OUT) is blind**. (OUT) is therefore *never automatic*, and it is not
  contradicted.
- **(OC-7) is a harness defect and an escalation.**
  `widened.place_pencil_general`'s single-hub-interior sampler degenerates via
  `localtest.plane_basis` at **32 of 357** POOL-G frames (≈ 9 %), and that
  degeneracy **implies `λᵢ = 0`** (15/15 on the `b` side, 18/18 on the `c`
  side). **`flanks.star_span_ranks` — documented in its own docstring
  (`flanks.py:201`) as the genericity guard against exactly the `plane_basis`
  artifact, and invoked as that guard at `dominance.base_seed` (`dominance.py:554`)
  — does not catch it, and no `IsNondegPencilRealization` conjunct excludes
  it.**
  Restricted to the **318 coincidence-free** frames the distribution is uniform
  (`318/318`).
- **(OC-8), the residual, is OPEN.** Class uniformity of (OUT) ⟺ at every class
  shape the whole-graph chart carries a hard-stratum point with `L_b ⊄ R₁` or
  `L_c ⊄ R₄` — a rank **lower** bound at a pencil placement, i.e.
  `notes/Pencil-strategy.md` §2.3's wall **relocated** onto the smaller
  `H/{e₂,e₃,e₄}` and **weakened, not crossed** — and (OC-3) says the relocation
  cannot be discharged combinatorially.

> **Standing rule for the whole arc, not a note on one table.** **No
> `place_pencil_general`-sampled battery may be quoted as a *rate*, or as
> evidence about a *generic* chart point.** Pool figures from this section are
> quoted over the **318 coincidence-free** frames, never the raw 357, and the
> same applies to every other habitat battery in the harness that draws through
> that sampler. What such a battery still supports unharmed is a *negative*
> (`0 hits`) or a *positive existence witness*: a degenerate draw can create
> neither a false hit nor a false witness. It is the **rate** reading, and only
> that reading, the defect destroys. Harness-side record:
> `notes/scripts/README.md` *Harness debt* item 4 and §4 convention 1.

**Verdict, stated at the strength the measurement supports: this is
availability, MEASURED, not proven.** What the section mainly establishes is
the negative (OC-3) plus a per-shape existence result; do not write it warmer
than that.

### Standing notation (on top of §(K-Λ))

`H := G − v − a`; the length-4 companion `P = b–x₁–x₂–x₃–c` with lines `C_i`,
`S = ⟨C₁,…,C₄⟩`, `V_bc ⊆ S` of dimension 3, and `λ ∈ S*` its annihilator, so
`λ_i = λ(C_i)` and `λ_i = 0 ⟺ C_i ∈ V_bc`. Write

- `X := {x₁, x₂, x₃, c}` and `Y := {b, x₁, x₂, x₃}` — the two **welds**;
- `μ₁` := the number of `H`-edges between `b` and `X` (`μ₄` symmetrically);
- `W₁` := `{m(b) − m(X)}` in `H` with `X` welded — the relative twist space
  §(K-Λ) *Step 5a* names;
- `R₁` := the same in `H − e₁` with `X` welded — the **far** relative twist
  space, which the placement of `x₁` does not enter;
- `L_b := α_{pt(b)} ∩ β_{Π(b)}` — the **2-dimensional pencil** of lines through
  `pt(b)` inside the panel `Π(b)`. Every nonzero element is a genuine line of
  that pencil (`b ∧ u` is decomposable), so every one of them is realizable as
  `C(b, x₁)` for a legal placement of `x₁`.

Welding is imposed as explicit equality rows on the rigidity matrix, never by
contracting the graph: a contracted edge would lose its hinge *line*, and the
hinge lines are the entire content here.

### Step O1 — (OC-1): the hinge-rate reading, made exact

§(K-Λ) *Step 5a* asserts the reading in one line and leaves it untested. It is
exact, needs no genericity beyond §(K-Λ) (Λ0a), and now has a driver.

> **(OC-1)** At any placement with `C₁,…,C₄` independent ((Λ0a)):
> `λ₁ = 0` ⟺ `C₁ ∈ V_bc` ⟺ `dim W₁ = 1` ⟺ (when `μ₁ = 1`) `C₁ ∈ R₁`.
> Symmetrically on the `c` side with `Y`, `W₄`, `R₄`, `e₄`.

*Proof.* `λ₁ = λ(C₁)` and `V_bc = ker λ ∩ S` give the first equivalence for
free. For the second: a relative twist has *unique* companion coordinates by
(Λ0a), so `m(b) − m(c) = C₁` forces `ω = (1,0,0,0)`, i.e.
`m(x₁) = m(x₂) = m(x₃) = m(c)` — `X` is welded — and conversely any motion of
`H` with `X` welded has `m(b) − m(c) = m(b) − m(X) ∈ W₁`. For the third: with
`μ₁ = 1` the only `b`–`X` hinge is `e₁`, so `W₁ = R₁ ∩ ⟨C₁⟩`, which is nonzero
iff `C₁ ∈ R₁`. ∎ (With `μ₁ ≥ 2` the intersection of two distinct hinge lines is
`0`, so `λ₁ ≠ 0` — §(K-Λ) *Step 5a*'s "further `b`–`X` edges only make `b` more
attached", now with its reason.)

*Exact, per frame:* `--pool` asserts the whole chain at **46** POOL-G frames —
every frame with `λ₁ = 0` or `λ₄ = 0` plus three controls per habitat — with
`(μ₁, dim W₁, dim R₁, dim(R₁ ∩ L_b) | μ₄, dim W₄, dim R₄, dim(R₄ ∩ L_c))`
taking only the four values `(1, ε₁, 5, 1 | 1, ε₄, 5, 1)`, `ε ∈ {0,1}`, and
`dim W = 1` occurring exactly when the corresponding `λᵢ` vanishes.

### Step O2 — (OC-2): the combinatorial availability map, and what it does *not* say

`nogood_subdiv.deficiency` gives the **ambient-generic** value of every
dimension above, via `dim Mot(G) = 6 + def(G)` and the fact that welding two
bodies is vertex identification: the generic dimension of `{m(u) − m(w)}` is
`def(G) − def(G/uw)`. Write `A₁ := def(H/X) − def(H/(X ∪ {b}))`, the
ambient-generic value of `dim W₁`.

> **(OC-2)** Over the enumerated class scope — the four certified
> length-4-companion habitats, the 19-shape named inventory, and the whole
> systematic sweep `outer.sweep_shapes()` (1357 class shapes), **4296
> (split, companion) pairs in all** — the map is *uniform*:
> `χ = 0` (the companion has no chord), `def(H/X) = def(H/Y) = 0`, and
> `(μ₁, dim R₁, A₁, μ₄, dim R₄, A₄) = (1, 5, 0, 1, 5, 0)` at every pair.

**The map collapses to one measured statement.** With `χ = 0` the arithmetic is
forced: `H` has trivial-partition count `6(|V(H)|−1) − 5|E(H)| = 3`, and welding
`X` removes 3 vertices and 3 edges, so `H/X` is **tight** (count `5χ = 0`;
asserted per pair). Then rigidity of `H/X` gives `A = 0` (a contraction of a
rigid graph is rigid) *and* `dim R = 5` (deleting one independent edge of a
tight rigid graph costs exactly 5). Tightness is arithmetic; rigidity of
`H/X` **is since 2026-08-06 a theorem** — *Step O9*'s (OC-10) proves it at
every class shape (direction O); the 4296 `deficiency` calls remain as a
check of the proof's conclusion.

**What this does not say, stated because a one-line quotation will get it
wrong.** `deficiency` is the **unconstrained** generic count. The pencil chart
is a proper subvariety of the placement space, so `A₁ = 0` is *not* evidence
that `λ₁ ≠ 0` at a pencil-generic placement — it is the ambient-generic
statement, and the gap between the two is precisely
`notes/Pencil-strategy.md` §2.3's asymmetry. **The combinatorial half therefore
does not deliver availability.** Step O3 is where the pencil constraint enters,
and it changes the answer qualitatively.

### Step O3 — (OC-3): on the pencil chart the bad locus is **always nonempty** (the load-bearing negative)

`C₁` is not a free line of `P³`. `x₁ ∈ N_{G′}(b)`, so `pt(x₁) ∈ Π(b)` and
`C₁ = C(b, x₁)` is confined to the 2-dimensional pencil `L_b`. Since `R₁` does
not involve `pt(x₁)`, and `μ₁ = 1`:

> **(OC-3)** `λ₁ = 0 ⟺ C₁ ∈ R₁ ∩ L_b`, and
> `dim(R₁ ∩ L_b) ≥ dim R₁ + dim L_b − 6 = 5 + 2 − 6 = 1`.
> So with everything but `pt(x₁)` held fixed there is **always at least one
> direction of `x₁`'s pencil that kills `λ₁`** — the bad locus of (OUT)'s first
> disjunct is nonempty on the chart of every class shape with `dim R₁ = 5`,
> which by (OC-2) is every shape in the enumerated scope. Measured
> `dim(R₁ ∩ L_b) = dim(R₄ ∩ L_c) = 1` **exactly** — never 2 — at all 46
> POOL-G frames of *Step O1*, so the locus is also **proper**: `λ₁ ≢ 0` along
> the `x₁`-slide at every measured chart point.

This is the (OUT) analogue of §(K-Λ) (Λ0g)/(Λ0i) for `g₁₄`, with the signs
reversed: (Λ0i) shows the `g₁₄` clause is *implied by* (Λ0d) wherever a
companion end is free, whereas (OC-3) shows the `λ₁` clause is **never** implied
by anything combinatorial. **That is the load-bearing negative of this
section:** a class-uniform proof of (OUT)'s hypothesis cannot be a count, a
matroid statement, or any argument that does not see the placement — because
the bad set is nonempty at every shape, and is exactly one point of a `P¹`.

`dim R₁ = 5` is itself the ambient-generic value; it was *measured* to hold at
the pencil placement at 46/46 frames, and that is the only sense in which the
pencil chart has been checked not to inflate it.

### Step O4 — (OC-5): the measurement (POOL-G)

POOL-G is the four `lambda.habitat_specs` habitats × placement seeds
**200–299** — deliberately the same integer pool `lambda.py --adv` uses for its
habitat leg. A frame is kept when the placement is target rank with
`dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4` and `star_span_ranks` green;
**(Λ0d) failures are kept and reported rather than dropped**, because that is
precisely where (OUT) stops applying. 400 seeds give **357 frames** (16 with no
placement, 27 rejected by the star-span guard); on a fixed 20-frame subsample
`λ` is asserted identical up to scale to `lambda.habitat_frame`'s.

| `(λ₁ = 0, λ₄ = 0)` | reading | count |
|---|---|---|
| `(0, 0)` | both outer coordinates nonzero — (OUT) applies | **322** |
| `(1, 0)` | `λ₁ = 0` only — (OUT) still applies, via `C₄` | 17 |
| `(0, 1)` | `λ₄ = 0` only — (OUT) still applies, via `C₁` | 17 |
| `(1, 1)` | **both vanish — (OUT) SILENT** | **1** |

Per habitat: θ(3,4,5) 98/99, NT21 89/89, NT24 91/91, NT30 78/78.

- **(OUT)'s hypothesis holds at 356 of 357.**
- **(OUT)'s conclusion is verified, separately, at 356 of 356** frames where the
  hypothesis holds and (Λ0)+(Λ0f′) are green: `λ ∦ p⁺`, `λ ∦ q`, and
  `Q(z(t)) ≢ 0` along the `a`-line. This is the sentence (OUT) actually
  asserts, and it is now driver-tested rather than inherited from (Λ2).
- `λ ∝ p⁺`: **0**. `λ ∝ q`: **0**. `(Λ0d)` fails at **0 of 357**, so the
  conditionality warning never fires in this pool.
- Codimension-1 calibration over the *same* pool: `g₁₃`, `g₁₄`, `g₂₄`, `p⁺₂`,
  `p⁺₃`, `q₂`, `q₃` and (Λ0d) vanish at **0/357** each; `λ₁` and `λ₄` at
  **18/357** each. *Step O5* explains the whole of that gap — **and forbids
  reading either as a rate.**

**The single silent frame, in full.** θ(3,4,5) **seed 233**: (Λ0a)–(Λ0f′) all
green, `λ ∦ p⁺`, `λ ∦ q`, `deg_t Q(z(t)) = 4` — so the escape holds there by the
pitch certificate and (OUT) simply cannot see it. It is also doubly
sampler-degenerate (*Step O5*), which is why *Step O6* exists.

### Step O5 — (OC-7): every failure is a coincident hinge line, most are manufactured, and the documented guard does not fire

> **(OC-7)** At **all 35** POOL-G frames with `λ₁ = 0` or `λ₄ = 0`, the
> vanishing outer line **coincides projectively with another hinge line at its
> hub**: `C(b, x₁) = C(b, u)` for some `u ∈ N_{G′}(b) \ {x₁}`, i.e.
> `pt(b), pt(x₁), pt(u)` collinear. Moreover — **asserted per frame, and the
> driver prints all 36 rows** (36 side-events over 35 frames; seed 233 carries
> both) — the coincidence list *exhausts* the hub's other `H`-neighbours at
> every one: the hub's whole hinge pencil has collapsed to a single line, so the
> hub is a **free rotor** about it and `ω C₁ ∈ V_bc` for trivial reasons. The
> converse fails (2 frames per side carry a coincidence with `λᵢ ≠ 0`), so the
> coincidence is not sufficient — and its **necessity beyond this pool is
> REFUTED by construction** (*Step O11* (OC-14), 2026-08-06, direction O: 38
> constructed fully-nondegenerate target-rank chart points, 34 guard-accepted,
> with `λᵢ = 0` and **no** coincident hinge; the correct general statement is
> (OC-12)'s dichotomy, and this pool's rates and the 318 / 299 denominators
> are **unaffected** — a codimension-1 locus is invisible to rational
> sampling, which is *why* 35/35 was measured). Restricted to the **318**
> coincidence-free frames the distribution is `(0,0) : 318` — a clean
> `318/318`.

> **(OC-9)** *(new 2026-08-06, slice S2 — the FIELD half of the coincident-hinge
> guard's adversarial test; driver leg `--pool`)* The composite guard
> `repin.star_generic` **rejects 58 of the 357** POOL-G frames, and its
> rejection set **strictly contains** the two-end diagnostic's 39 (asserted
> frame by frame, 0 violations): **19 further frames** are coincidence-free at
> `b` and `c` and carry a coincidence somewhere else in the configuration, and
> the driver prints all 19 with their coincidence lists. So the plan's
> expectation that the guard's output *equals* the hand-restriction is
> **refuted, in the safe direction**: the guard is the wider test.
> Consequences, both recorded because they point opposite ways. (i) The 318
> restriction is **not wrong** — every `λᵢ = 0` frame carries a coincidence at
> the hub its coordinate belongs to (the assertion above), so all 19 extra
> frames have both outer coordinates nonzero and the `318/318` reading is
> unaffected. (ii) But the **strictest** sub-pool this harness can certify is
> the guard's own **299 of 357**, whose distribution the driver now also prints
> (`(0,0) : 299`), and a rate quoted over 299 is the one that needs no
> hand-restriction argument at all.

**Where the coincidences come from.** `widened.place_pencil_general` places
every *single-hub interior* through `localtest.in_plane_point`, whose
`plane_basis` is the **degenerate** member of the README's *Divergences* table:
for some normals it returns two **parallel** in-plane directions, and then every
single-hub interior of that hub lands on **one line** through `pt(h)`. Measured
implication, per side:

| | sampler degenerate at the hub | `λᵢ = 0` | count |
|---|---|---|---|
| `b` | no | no | 339 |
| `b` | no | **yes** | 3 |
| `b` | **yes** | **yes** | **15** |
| `c` | no | no | 339 |
| `c` | **yes** | **yes** | **18** |

So the degeneracy **implies** `λᵢ = 0` (15/15 and 18/18, no exceptions), and 33
of the 36 coordinate-vanishing events in POOL-G are manufactured by it. The
remaining 3 (θ(3,4,5) seeds 205, 225, 280, all `λ₁ = 0`) are ordinary rng
coincidences of the same geometric type. The driver prints the union directly:
**32 of the 357 frames have a degenerate in-plane sampler at `b` or at `c`**
(both at 1, θ(3,4,5) seed 233 — which is exactly the silent frame).

**Three things this costs the harness, stated precisely.**

1. **`flanks.star_span_ranks` is not the guard its docstring says it is.** Its
   docstring (`flanks.py:201`) says rank 3 at every vertex is *"simultaneously
   the genericity guard against the `plane_basis` artifact and
   `IsNondegPencilRealization`'s fourth conjunct"*, and every consumer invokes
   it under exactly that reading (`dominance.py:554`, `annih.py:67`,
   `outer.py`, `sigma.py`). It passes at all 33 manufactured frames, because a
   hub's star still spans its panel through a *third* neighbour (here `pt(a)`, which
   sits on the meet line `M` and is placed by a different branch). Nor does any
   of the four conjuncts of `IsNondegPencilRealization`, as
   `flanks.nondeg_conjuncts` implements them, exclude two coincident hinge lines
   at a hub. The cheap correct guard is the one this driver uses: **no two hinge
   lines at a hub coincide.** This is the **second** recorded `plane_basis`
   contamination (the first, 2026-08-02, is the `(K-tight)` re-pin's sampler
   artifact — `notes/dispatch-log.md`) and the **first where the documented
   guard failed**; it is `notes/scripts/README.md` *Harness debt* **item 4**.
   **REPAIRED 2026-08-06** by the re-baselining round: slice S1 defined the
   composite guard `repin.star_generic` with a constructed adversarial witness
   (`repin.py --hinge`), slice S2 adopted it at every acceptance site in
   `w4/` — this driver's two modes deliberately excepted, because they are the
   measurement — repaired all four falsified docstrings, and added the FIELD
   half of the adversarial test here, (OC-9). The finding stands as measured;
   what changed is that the harness now rejects the configuration everywhere it
   is not being measured.
2. **No recorded figure moves, and the reason is one-directional.** Every
   `place_pencil_general`-sampled figure in the arc that this could touch is
   either a *negative* (`0 hits for λ ∝ p⁺`, `0 hits for Q(z) = 0`) or a
   *positive existence witness* (`g₁₄ ≠ 0` at a chart point, refuting forcing);
   a degenerate draw can create neither a false hit nor a false witness. What it
   does damage is any reading of those batteries as **rates** or as evidence
   about a *generic* chart point — hence the standing rule in this section's
   headline block: **32 of 357 (≈ 9 %)** of the habitat frames here are drawn
   from a strictly non-generic sub-family.
3. **§(K-ann) was flagged for a CHECK, not accused of an error — and the check
   was DONE on 2026-08-06 (slice S2) and came back CLEAN** (§(K-ann)
   *Verification*, the re-read blockquote). `annih.py:67`
   took its genericity guard from the same `star_span_ranks`, through
   `dominance.base_seed`, so it inherited the same exposure. The asymmetry that
   decides which figure classes are exposed, recorded so a successor does not
   have to re-derive it: **§(K-ann)'s claims are identities and structural facts
   verified at every tested frame** (`def(H/P) = 0`, stress dimension `= k − 3`,
   the reciprocity identity, full support), so including degenerate frames makes
   them **harder** to satisfy, not easier — the defect is *conservative* there —
   **whereas this section's are rates**, which the defect distorts. The claim
   that would need re-running under the new guard is any §(K-ann) statement read
   as *generic* rather than *pointwise*. **Done, clean** — see item 3's
   opening sentence.

### Step O6 — (OC-4): (OUT) silent at a **nondegenerate** chart point

(OC-3)'s marked direction is *constructible*. In the §(K-Λ) (Λ0i) free-end
pattern `pt(x₁)`'s only chart constraint is `pt(x₁) ∈ Π(b)`, so aiming it along
`R₁ ∩ L_b` is legal; and the two ends are **independent**, because welding
`Y = {b,x₁,x₂,x₃}` for the `c`-side computation absorbs `e₁` and `e₂`, so
`pt(x₁)` does not enter `R₄` (and symmetrically). `--build` slides both at
once.

> **(OC-4)** At all four certified habitats, at placement seed 200 and slide
> parameters `(t₁, t₃) = (1, 1)`, the result is an exact chart point with
> `λ₁ = λ₄ = 0` — **(OUT) SILENT** — at which
> `C₁, C₄ ∈ V_bc`; (Λ0a)–(Λ0e) all hold; both middle brackets of `p⁺` and of
> `q` survive ((Λ0f)); `g₁₃, g₁₄, g₂₄ ≠ 0` ((Λ0f′)); the placement is still
> target rank (54 / 114 / 114 / 144) with `dim R_a = 1`, `dim V_bc = 3`,
> `dim Mot(H) = 9`; **all four `IsNondegPencilRealization` conjuncts hold**;
> and `λ ∦ p⁺`, `λ ∦ q`, `deg_t Q(z(t)) = 4`.

**And at 3 of the 4 the point carries no coincident hinge line at `b` or `c`**
(NT21, NT24, NT30), so the locus is reached without collapsing any hub's hinge
pencil: the phenomenon is real, not only the artifact of *Step O5*. At θ(3,4,5)
it *is* the artifact — `b` has only two `H`-neighbours there, so `R₁ ∩ L_b`
is forced to be `⟨C(b, y₁)⟩` and the marked direction aims straight at the far
neighbour (driver prints `aims at [[17], [20]]`) — an observation *Step O10*'s
(OC-12) has since promoted from a θ(3,4,5)-specific remark to the general
degree-3-hub theorem. That is also why θ(3,4,5)
alone contributes non-manufactured sampled hits: at a degree-2 `b` the bad
direction is a *first*-neighbour coincidence, which small rational sampling
occasionally meets.

Read together with *Step O4*: **(OUT) is strictly weaker than §(K-Λ) (Λ2)**, and
now with a witness. §(K-Λ) *Step 5a*'s own "sufficient, never necessary … silent
on the whole line" is confirmed at an exhibited nondegenerate point, not merely
argued.

### Step O7 — (OC-6): shape-level availability, which is what the route needs

(OUT) is a per-*seed* sufficient condition and the escape needs *some*
target-rank seed, so the question that matters is per shape.

> **(OC-6)** POOL-S — the 19-shape named inventory plus the first 4 shapes of
> each `outer.sweep_shapes()` family (41 class shapes), every eligible split,
> placement seeds 1–39, ≤ 3 hard-stratum frames per split, every length-4
> companion — gives **270 frames over 90 (split, companion-bearing) splits**.
> Distribution `(0,0) : 254`, `(1,0) : 8`, `(0,1) : 8`, `(1,1) : 0`. **(OUT)'s
> hypothesis holds at 270 of 270**, and **0** (split, companion) pairs have no
> available frame. 16 of the 270 carry a coincident hinge line, and every
> `λᵢ = 0` frame is one of them (asserted).

POOL-S is **disjoint from POOL-G** and its figures are never summed with
POOL-G's.

### Step O8 — a denominator correction to §(K-Λ) *Step 5a*

§(K-Λ) *Step 5a* recorded *"`--adv` reports `λ ∝ p⁺` and `λ ∝ q` at **0 of 1497**
frames"* (and its *Verification* table carried the same denominator). By code
reading of `lambda.py --adv`, those tests run **only inside the habitat loop**,
whose pool is seeds 200–299 at 4 habitats — at most **400** frames. The
remaining count comes from the local-strata loop, where `sample_local_frame`
deliberately leaves the far covector **free**: those frames carry no `λ` at all.
The strata leg's maximum is exactly `38 strata × 30 seeds = 1140`, and
`357 + 1140 = 1497`, consistent with POOL-G's 357 and with zero strata
rejections. So the `λ`-bearing denominator behind the recorded `0 of 1497` is
**`≤ 400`**, not 1497. Nothing about the *result* changes — 0 hits is 0 hits —
but the figure is quoted with the smaller denominator, here and at the two other
sites that carried it (§(K-Λ) *Verification*, `notes/scripts/w4/README.md`).

*One extension of the correction, from the same code read and flagged as this
pass's own:* `Q(z) = 0` is computed in the habitat loop too, so its `0` carries
the same `≤ 400` denominator. `C(M) ∈ S` and the `(span ω⁺, span ω⁻)` histogram
**do** run over all 1497 frames, and §(K-Λ) *What would change this* item (iii)'s
"6 of 1497" is therefore correct as written.

### Verdict

**Availability: CONFIRMED at the probed scope; class uniformity OPEN, and now
demonstrably out of reach of any counting argument.** Component by component:

| | claim | standing |
|---|---|---|
| **(OC-1)** | the hinge-rate reading, as an exact equivalence chain | **proven-informally** (two lines, no genericity beyond (Λ0a)); driver-tested at 46 frames |
| **(OC-2)** | `χ = 0`, `H/X` tight and rigid, hence `(μ, dim R, A) = (1,5,0)` on both sides | tightness **proven** (arithmetic); rigidity **measured** at 4296 pairs over an enumerated, non-exhaustive scope. **Ambient-generic — it does not discharge (OUT)** |
| **(OC-3)** | `{λ₁ = 0}` nonempty on every chart, exactly one direction per pencil | **proven-informally** given `dim R = 5` (pure linear algebra); `dim R = 5` and `dim(R ∩ L) = 1` measured on the pencil chart at 46 frames. **The section's headline** |
| **(OC-4)** | an (OUT)-silent nondegenerate chart point | **exhibited**, 4 habitats, 3 of them coincidence-free |
| **(OC-5)/(OC-6)** | the distributions | **measured**, pointwise, over two disjoint pinned pools; POOL-G's rates only over the 318 coincidence-free frames |
| **(OC-7)** | every failure is a coincident hinge; 33/36 manufactured; the documented guard misses it | **measured**, with the implication asserted per frame; **a harness defect, escalated — and CLEARED 2026-08-06 by the re-baselining round's slices S1/S2** |
| **(OC-9)** | the composite guard rejects **58/357** and its rejection set strictly contains the two-end diagnostic's 39 (19 extra, printed) | **measured**, asserted per frame — the FIELD half of the guard's adversarial test |
| **(OC-8)** | the residual (below) | **OPEN** |

> **(OC-8) what (OUT) now reduces to, exactly.** Class uniformity of (OUT) at
> length-4-companion splits is *equivalent* to: at every class shape, the
> whole-graph pencil chart carries a hard-stratum target-rank point with
> `L_b ⊄ R₁` or `L_c ⊄ R₄`. That is a rank **lower** bound at a pencil
> placement — the class of statement `notes/Pencil-strategy.md` §2.3 identifies
> as the arc's wall — relocated onto the *smaller* graph `H/{e₂,e₃,e₄}` and
> *weakened* (it asks for one constraint between `b` and `X`, not the full
> escape), but **not crossed**. (OC-3) shows the relocation cannot be discharged
> combinatorially: the bad set is nonempty at every shape, so any proof must be
> a genericity argument on the **whole-graph** chart, and that needs the
> chart's irreducibility (or at least that its hard-stratum component is not
> contained in `{λ₁ = 0} ∩ {λ₄ = 0}`) — which the arc has never established,
> because `λ` is a far datum and §(K-Λ)'s class-uniformity bridge is about the
> *local* frame only.

**This measurement is informative, not decisive, and the reason is sharper than
"it is pointwise."** It measures a hypothesis never measured, so it is not a
re-run of a saturated question (`notes/Pencil-strategy.md` §5.2). But what it
can establish is *availability* — that (OUT) is not vacuous and not dead —
whereas what (OUT) as a route needs is *uniform* availability, and (OC-3) shows
that the natural cheap route to uniformity (a count on the contracted graph) is
structurally unavailable. A clean `n/n` here must not be read as more than: at
every shape we could place exactly, (OUT) applies at a generic hard-stratum
seed.

### What would change this

1. *(and 2.)* **STRUCK as unrealizable** (2026-08-06, direction O — *Step O9*
   (OC-10)): the hunted shapes — `dim R = 6`, or `dim R ≤ 4` / `μ ≥ 2` — do
   not exist at **any** class shape; the availability map is forced, so the
   widened 5226-pair sweep's 0-rates are theorems, not measurements. These
   items were never hunts.
2. *(struck with item 1 — see (OC-10).)*
3. **`L_b ⊆ R₁` at a chart point** — **HIT, by construction** (2026-08-06,
   direction O — *Step O11* (OC-14)): the hub slide onto `C₀` lands 38/38
   exact fully-nondegenerate target-rank points with `L_h ⊆ R`, sharpening
   (OC-8) past "sometimes forced" to *Step O11*'s restated containment
   question. The 46-frame `dim(R₁ ∩ L_b) = 1` figure stands as a statement
   about sampled frames only.
4. **Pushing the constructed point from the bad *line* to the bad *point*
   `p⁺`.** (OC-4) lands `λ` on `{λ₁ = λ₄ = 0}` with both slide parameters
   spent; the residual chart freedom (`pt(x₂)`, the far graph) is untouched. A
   `λ ∝ p⁺` hit at a nondegenerate hard-stratum point is §(K-Λ) *Step 4*'s
   genuine (T3) escape failure — **not** a disproof of the pencil conjecture,
   since a constructed point is not a generic realization, and it should not be
   reported as one. Deliberately not attempted here.
5. **Re-running any `place_pencil_general`-sampled battery under the
   coincident-hinge guard.** (OC-7) says ≈ 9 % of habitat frames are non-generic
   in a way no existing guard catches. The right fix is the coordinator's
   deliberate re-baselining commit (`notes/scripts/README.md` *Harness debt*,
   which now carries this as item 4), not a research dispatch's side errand.
6. **Symbolic (Macaulay2) treatment of `R₁ ∩ L_b` on the local frame** —
   **ANSWERED on the `ℓ_min = 5` stratum, structurally BLOCKED off it**
   (2026-08-06, direction O — *Step O12*): (OC-16) proves `Δ ≢ 0` at the
   generic point of the length-5-chain local frame with the bad line `C₀` in
   closed form, and (OC-15) shows the path-span (bracket) form carries no
   information for `ℓ_min ≥ 6` (the stratum is 8 of 5226 pairs). The residue
   is the chart-to-frame dominance plus the block decomposition of *What
   would change this (Steps O9–O12)* item 3.

### Verification

`notes/scripts/w4/outerline.py` (tracked, new this pass; exact ℚ; a `w4/` leaf
beside `flanks`/`pure`/`lambda`/`dominance`/`outer`/`sigma`, importing only
catalogued §1 primitives and **modifying nothing**). Run from the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --comb     # (OC-2)
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --pool     # (OC-1),(OC-5),(OC-7)
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --shapes   # (OC-6)
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerline.py --build    # (OC-3),(OC-4)
```

Times as landed: `--comb` 14 s, `--build` 10 s, `--pool` 358 s, `--shapes`
322 s. All four re-run **byte-identical** under two different `PYTHONHASHSEED`
values. `--pool` and `--shapes` do **not** fit together in one 600 s
foreground budget; run them separately.

**Pools, pinned; every figure above is quoted over exactly one of them and none
is aggregated across two.**

- **POOL-C** (`--comb`) — deterministic, no rng: the 4 `lambda.habitat_specs`
  habitats, `outer.named_inventory()`, and every family of
  `outer.sweep_shapes()`. 4296 (split, companion) pairs.
- **POOL-G** (`--pool`) — the 4 habitats × placement seeds **200–299**;
  357 frames, of which the **318** coincidence-free-at-the-companion-ends ones
  are a legitimate denominator for a rate (the standing rule above) and the
  **299** the composite guard accepts are the strictest one ((OC-9),
  2026-08-06). The frame set itself is deliberately **not** guard-restricted:
  the coincidence is what (OC-7) measures, so `--pool` reports it instead of
  rejecting it — slice S2's per-site adoption judgement.
- **POOL-S** (`--shapes`) — 41 class shapes × every eligible split × seeds
  **1–39**, ≤ 3 frames per split; 270 frames.
- **POOL-B** (`--build`) — the 4 habitats × seeds **200–259**; slides from the
  fixed list `1, 2, −1, 3, 1/2, 5, −3, 7`; all four constructions land at seed
  200, slides `(1,1)`.

The only rng is `random.Random(seed)` inside `widened.place_pencil_general`.
The aux point `w` is fixed at `(1, −2, 5)`; the pencil `L_h` and every marked
direction come from `repin.robust_plane_basis` and are **deterministic**.

*Figures-do-not-move gate* (`notes/scripts/README.md`): the pass that opened
this section **added** a driver and modified none, so the gate discharged by
the check itself. **Re-baselined 2026-08-06 (slice S2)**, which did modify
`outerline.py`: `--comb` and `--shapes` came back **byte-identical**; `--pool`
gained the (OC-9) block and `--build` one reported line per construction (the
composite guard's verdict, `False` at exactly the one non-coincidence-free
construction, `True` at the other three — so (OC-4)'s `3 of 4` is now the
guard's own count and not a hand-count). The transient duplicate
`outerline.hinge_coincidences` was retired in the same commit and this file's
copy is now `repin`'s.

Per mode, what is asserted:

- `--comb`: per pair, the `5χ` count identity for `H/X`; `def(H/X)`,
  `def(H/Y)`; `μ`, `dim R`, `A` on both sides; the uniformity of the histogram;
  and that no pair kills both disjuncts.
- `--pool`: per frame, `λᵢ = 0 ⟺ C_i ∈ V_bc`; the full (Λ0a)–(Λ0f′) clause
  battery; (OUT)'s **conclusion** (`λ ∦ p⁺`, `λ ∦ q`, `Q(z(t)) ≢ 0`) wherever
  its hypothesis holds and the clauses are green; the codimension-1 rates of
  every (Λ0) bracket over the same pool; the (OC-1) chain at 46 frames; the
  (OC-7) implications *degenerate sampler ⟹ `λᵢ = 0`* and *`λᵢ = 0` ⟹
  coincident hinge*, both as per-frame asserts; the **free-rotor exhaustion**
  (the coincidence list contains every other `H`-neighbour of the hub) as a
  per-frame assert at all 36 rows, each printed; and `λ` agreement with
  `lambda.habitat_frame` at 20 frames.
- `--shapes`: the same `λ` measurement per shape, plus that no (split,
  companion) pair is silent at every probed seed.
- `--build`: the construction, every (Λ0) clause at the constructed point, the
  target rank and `dim R_a = 1`, all four `IsNondegPencilRealization`
  conjuncts, `λ` off both bad points, `deg_t Q(z(t)) ≥ 0`, and that ≥ 3 of the
  4 constructions carry no coincident hinge line.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean
(`DESIGN.md` *Formalize everything the argument uses*). Nothing in `lambda.py`
or `outer.py` was modified; both are read.

### Steps O9–O12 (2026-08-06, fan-out direction O) — the negative half got stronger, and the residue got smaller and sharper

Drivers `notes/scripts/w4/outerwide.py` (imports `outerline.py` read-only) and
`notes/scripts/m2/outerwide.m2`, both new this pass; labels **(OC-10)–(OC-16)**.
Everything cited that this pass did not mint is qualified: **(OUT)**,
**(Λ0a)–(Λ0i)**, **(Λ0f′)** are §(K-Λ)'s; **(K-wit)** is owned jointly by
§(K-pitch) *Step 3* and §(K-Λ) *Steps 3–6*; POOL-C / POOL-G / POOL-S / POOL-B are
this section's earlier pools and **nothing below is aggregated with them**.


Four things, in the order they change the reading of (OUT).

- **(OC-10) — the combinatorial availability map is FORCED, not measured, and
  §(K-out) *What would change this* items 1 and 2 are UNREALIZABLE.** At every
  **class** shape — tight, `def(G) = 0`, both chain ends **hubs**, and
  **`hnoRigid`**; all four hypotheses are needed and each is shown
  load-bearing — every eligible split and every length-4 companion has
  `χ = 0`, `μ₁ = μ₄ = 1`, `H/X` and `H/Y` **isostatic**, `A₁ = A₄ = 0`,
  `dim R₁ = dim R₄ = 5`. So the hunt items 1–2 commission (a shape with
  `dim R = 6`, or with `dim R ≤ 4` / `μ ≥ 2`) cannot succeed at any class shape
  whatsoever: the widening is not merely a no-hit, it is a **theorem that no
  widening can hit**. §(K-out) (OC-2)'s "rigidity of `H/X` is the one measured
  fact" is superseded — that fact is now proven. **A process note the
  coordinator should keep:** the first draft of this proof discharged the
  boundary case by a pigeonhole argument that is valid only when the violating
  subgraph has no interior-to-interior edge; the F11 minimality driver
  (`--adv`, rows 7–8) refuted it, and row 8 is a graph satisfying *every* other
  hypothesis with `dim R₁ = 6`, whose only broken hypothesis is `hnoRigid`.
  The repaired proof is below and is the one to land.
- **(OC-11)/(OC-12) — (OC-3)'s marked direction acquires a FORMULA, and at a
  degree-3 hub it *is* the other hinge line.** `dim R₁ = 5` being a theorem
  makes `R₁` a **hyperplane**; inside the panel, `dim(R₁ ∩ β_b) ≥ 2` always
  (`β_b` := the 3-dimensional, totally `B`-isotropic space of lines of `Π(b)`),
  and where the meet is exactly 2 it is the **pencil of a single point `p` of
  `Π(b)`**. Then `λ₁ = 0 ⟺ p, pt(b), pt(x₁)` collinear, and
  `L_b ⊆ R₁ ⟺ p = pt(b)`. At a **degree-3 hub** (`deg_G(b) = 3`, so
  `deg_H(b) = 2` with other `H`-neighbour `u`) one has `C(b,u) ∈ R₁`
  unconditionally, hence `p ∈ C(b,u)` and the marked direction **is** `C(b,u)`:
  `λ₁ = 0 ⟺ C(b,x₁) = C(b,u)`, a **coincident hinge line at `b`** — so
  **§(K-out) (OC-7)'s measured implication is a THEOREM at a degree-3 hub**
  (`repin.star_generic` accepting the frame *implies* `λ₁ ≠ 0` there), and
  *Step O6*'s remark that θ(3,4,5) is special because "`b` has only two
  `H`-neighbours there" is not a special case but the general degree-3 statement.
  Census: `deg_G(b) = 3` at **3081 of 5226** POOL-CW pairs, and at least one
  companion end has degree 3 at **3702 of 5226**.
- **(OC-13)/(OC-14) — the exceptional locus is a LINE of the panel, it is
  REACHABLE, and reaching it REFUTES (OC-7)'s necessity claim.** With
  `T_u := {m(u) − m(v*)}` in `(H/X) − b` (4-dimensional and **independent of
  `pt(b)`, `pt(x₁)` and `pt(a)`**), `R₁ = ⟨C(b,u)⟩ ⊕ T_u` and
  `R₁ ∩ β_b = ⟨C(b,u)⟩ ⊕ (T_u ∩ β_b)`, so `L_b ⊆ R₁` ⟺ `dim(T_u ∩ β_b) = 2`
  or `pt(b) ∈ C₀`, where `C₀` is the line of `Π(b)` spanning `T_u ∩ β_b`.
  Because `T_u` and `β_b` do not see `pt(b)`, **sliding `pt(b)` inside its own
  panel** is a legal chart move whenever `b` has no hub `G′`-neighbour, and
  `C₀` is *fixed* along it. Run exactly: the slide **onto** `C₀` lands **38 of
  38** attempts at θ(3,4,5), each an exact chart point that is target rank with
  `dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4`, **all four**
  `IsNondegPencilRealization` conjuncts, **(Λ0a)–(Λ0f′) all green**, `λ ∦ p⁺`,
  `λ ∦ q`, `deg_t Q(z(t)) = 4` — and with `λᵢ = 0` **identically in `pt(xᵢ)`**
  and **no coincident hinge line at the hub** (34 of the 38 are accepted by the
  whole-configuration guard `repin.star_generic`). So: **(OC-7)'s "the
  coincidence is necessary" is REFUTED as a general statement** (it survives as
  a statement about POOL-G's *sampled* frames, and the pool restriction to 318 /
  299 is unaffected — see the correction list), and **(OC-8)'s bad case is
  inhabited at a real class habitat by an explicit construction**, not merely
  possible. Four of the 38 are (OUT)-**silent** (both outer coordinates vanish),
  strengthening (OC-4): the escape still holds there by the pitch certificate.
- **(OC-15)/(OC-16) — §(K-out) *What would change this* item 6 is ANSWERED on
  one stratum and structurally BLOCKED off it.** `R₁` is contained in the
  hinge-line span of **every** `b`-to-`v*` path of `K = (H/X) − e₁` (each edge
  contributes `m(u) − m(w) ∈ ⟨C(u,w)⟩`), and `dim R₁ = 5` therefore forces every
  such path to have `≥ 5` edges. Where some path has **exactly** 5 the
  containment is an equality, `R₁` is a **bracket** object, and the whole (OC-8)
  clause becomes one `6×6` Plücker determinant in seven points —
  `m2/outerwide.m2` then proves, at the **generic point** of the gauge-sliced
  local frame, that `Δ ≢ 0` (so `L_b ⊄ R₁` generically), that `Δ` factors into
  **exactly two** simple irreducible factors, and that the non-degenerate factor
  is **linear in `pt(b)`** — i.e. **`C₀` in closed form**, its coefficients
  brackets of the far chain points only. Off that stratum the route is blocked
  and the blockage is measured: for `ℓ_min ≥ 6` the path spans are already all of
  `K⁶` and their intersection carries no information (`(2, 6, False) : 38`,
  `(3, 6, False) : 70`), and the census says `ℓ_min = 5` holds at only **8 of
  5226** POOL-CW pairs. **This is the honest boundary of the symbolic route**,
  and it is a boundary of the *bracket* form, not of (OC-11)–(OC-13), which need
  only `deg_H(b) = 2`.

**Verdict, stated at the strength the work supports.** The *combinatorial*
half of §(K-out) is now **proven** rather than measured, and two of its six
*What would change this* items are struck as unrealizable. (OC-8) is **still
open**, but it is no longer "a rank lower bound on the whole-graph chart": at a
degree-3 hub it is the single sentence *the hard-stratum target-rank locus is not
contained in the hypersurface `{pt(b) ∈ C₀}`*, with `C₀` an explicit line of the
panel — in closed bracket form on the `ℓ_min = 5` stratum. **Class uniformity of
(OUT) is not established and no gap-map status moves.**

---

### Step O9 — (OC-10): the availability map is forced

Notation is §(K-out)'s *Standing notation* verbatim: `H = G − v − a` at the
split `v` with `b–v–a–c` the length-3 split branch (`deg v = deg a = 2`, `b` and
`c` hubs), `P = b–x₁–x₂–x₃–c` a length-4 companion, `X = {x₁,x₂,x₃,c}`,
`Y = {b,x₁,x₂,x₃}`, `μᵢ`, `Rᵢ`, `Aᵢ`, `χ` as *Step O2* defines them. Write
`cnt(W) := 6(|W| − 1) − 5|E_G(W)|` for `W ⊆ V(G)`.

> **(OC-10)** Let `G` be **tight** (`5|E| = 6(|V| − 1)`) with `def(G) = 0` —
> i.e. **isostatic** in the count matroid `nogood_subdiv.deficiency` computes —
> and satisfying **`hnoRigid`**: no *proper* branch-union of `G` is rigid
> (`kslide.no_rigid_branch_union`, the class predicate's own certificate). Let
> `v` be an **eligible** split, so both chain ends `b`, `c` are **hubs**
> (`outer.split_data`'s filter). Then at every length-4 companion:
> `χ = 0`; `μ₁ = μ₄ = 1`; `H/X` and `H/Y` are **tight and isostatic**
> (`def = 0`); `A₁ = A₄ = 0`; and `dim R₁ = dim R₄ = 5`.
> **Corollary.** Every `b`-to-`v*` path of `K = (H/X) − e₁` has `≥ 5` edges,
> and symmetrically at the `c` end.
>
> **All four hypotheses are used, and each is load-bearing** (`--adv`): drop
> tightness of `H`'s count, or `def(G) = 0`, or girth (a consequence of the
> first two), or `χ = 0`, or *`b`, `c` hubs*, or **`hnoRigid`**, and a witness
> with `dim R₁ = 6` or `μ ≥ 2` appears at once. In particular `hnoRigid` is
> **not** decoration: `--adv` row 8 is tight, isostatic, girth 8, `χ = 0`, has
> both chain ends hubs and no vertex with two weld-neighbours — and still has
> `def(H/X) = 1` and `dim R₁ = 6`.

*Proof.*

**(a) Isostatic ⟹ 5/6-sparse.** `def(G) = 0` means
`rank_{(6,6)}(5G) = 6(|V| − 1)`, which tightness makes `= 5|E| = |5G|`: the
multiset `5G` is **independent**. A sub-multiset supported on `W ⊆ V` is largest
when it takes all five copies of every `G`-edge inside `W`, so independence is
*equivalent* to `cnt(W) ≥ 0` for every `W`. (Only necessity is used until step
(e); sufficiency is used there. `kslidecomb.shape_ok`'s own docstring already
records this equivalence — "tight (def = 0, which with the count
`5|E| = 6(|V|−1)` forces 5/6-sparsity of every subgraph)" — so nothing here is
a new convention.)

**(b) Girth ≥ 6.** A cycle on `L` vertices has `cnt = 6(L − 1) − 5L = L − 6`,
so `L ≥ 6`. In particular `G` is triangle-free and has no 4- or 5-cycle —
*independently* of the class predicate's own `triangles(E)` test.

**(c) `χ = 0`.** The six candidate chords of `P` close cycles of `G` of lengths
3 (`bx₂`, `x₁x₃`, `x₂c`), 4 (`bx₃`, `x₁c`) and 5 (`bc`, via the companion). All
`< 6`. (`bc` is doubly excluded: with the split branch it also closes a
4-cycle.)

**(d) `μ₁ = 1`.** A second `b`–`X` edge is one of `bx₂`, `bx₃`, `bc`, excluded
by (c). Symmetrically `μ₄ = 1`.

**(e) `H/X` is isostatic.** `cnt_H := 6(|V(H)| − 1) − 5|E(H)| = 3` (removing
`v, a` drops 2 vertices and 3 edges from a graph of count 0), and with `χ = 0`,
welding `X` drops 3 vertices and 3 edges, so `H/X` has count `0` — **tight**
(this is *Step O2*'s `5χ` identity at `χ = 0`, and the driver asserts it per
pair). For independence, suppose `W′ ⊆ V(H/X)` is a **minimal** violating set:
`5|E_{H/X}(W′)| > 6|W′| − 6`, every vertex of `W′` incident to an edge inside
(minimality — deleting an isolated vertex only strengthens a violation). If
`v* ∉ W′` then `W′ ⊆ V(H)` and `E_{H/X}(W′) = E_H(W′)`, contradicting (a). So
`v* ∈ W′`; put `W := W′ ∖ {v*}`, `s := |W|`, and let `K` be the corresponding
`H`-edge set — edges with both ends in `W ∪ X`, at least one end in `X`, none of
them the three `X`-internal path edges. The violation reads **`5|K| > 6s`**.

- *If `b ∈ W`:* apply (a) at `U := W ∪ X ∪ {v, a}`, `|U| = s + 6`. `E_G(U)`
  contains `K`, the three internal edges `x₁x₂, x₂x₃, x₃c`, the three split-path
  edges `bv, va, ac`, and `bx₁` — at least `|K| + 6` distinct edges (`bx₁` may
  already lie in `K`). So `5(|K| + 6) ≤ 6(s + 5)`, i.e. `5|K| ≤ 6s`.
  **Contradiction.**
- *If `b ∉ W`:* apply (a) at `U := W ∪ X ∪ {b, v, a}`, `|U| = s + 7`. Now `bx₁`
  cannot be in `K` (its end `b` is outside `W ∪ X`), so `E_G(U)` contains
  `|K| + 7` distinct edges and `5(|K| + 7) ≤ 6(s + 6)`, i.e.
  **`5|K| ≤ 6s + 1`**. Together with the violation `5|K| > 6s` this forces
  `5|K| = 6s + 1` **exactly** — and then `cnt(U) = 0` with `E_G(U)` **equal**
  to the listed `|K| + 7` edges (one more `G`-edge inside `U` would give
  `5|K| ≤ 6s − 4`). So `U` is a **tight** subgraph of `G`; being a subgraph of
  an independent set it is independent; so **`U` is isostatic, hence rigid**.
  Three observations finish it.
  - *`U` has minimum degree `≥ 2`.* A vertex `y` of degree `≤ 1` in `U` gives
    `cnt(U − y) = cnt(U) − 6 + (5 or 0) < 0`, contradicting independence.
  - *`U` is a union of COMPLETE branches of `G`.* If a `G`-degree-2 vertex lies
    in `U` then both of its edges do (min degree `≥ 2`), so its neighbours lie
    in `U`; induction along the branch puts the whole branch, both hub ends
    included, in `U`. Hubs of `U` need no such closure. Hence `V(U)` is exactly
    the vertex union of a set of branches and `E_G(U)` their induced edge set —
    which is precisely the object `kslide.no_rigid_branch_union` enumerates.
  - *`U` is PROPER.* Here is where `b` being a **hub** is used: `deg_G(b) ≥ 3`
    while `b`'s `U`-edges are only `bv` and `bx₁`, so `b` has a third `G`-edge
    `bz`; if `z ∈ U` then `bz ∈ E_G(U)` beyond the list, contradicting the
    equality above. So `z ∉ U` and `U ⊊ G`.

  So `U` is a **rigid proper branch-union**, contradicting `hnoRigid`.

So no violating set exists; `H/X` is independent, and being tight it is
isostatic. Symmetrically for `H/Y`, with `U := W ∪ Y ∪ {c, v, a}` (resp.
`W ∪ Y ∪ {v, a}` when `c ∈ W`), the internal edges `bx₁, x₁x₂, x₂x₃`, the extra
edge `x₃c`, the same split path, and `c` the hub supplying properness.

*Remark (what the first draft got wrong, kept because it is the useful special
case).* If every `K`-edge joins `W` to `X` — no interior-to-interior edge —
then `5|K| = 6s + 1` forces `|K| > s`, every vertex of `W` carries a `K`-edge,
and pigeonhole gives some `u ∈ W` with **two** `X`-neighbours; each such pair
closes a cycle of length `≤ 5` through the `X`-path (`x₁,x₂`: 3; `x₁,x₃`: 4;
`x₁,c`: 5; `x₂,x₃`: 3; `x₂,c`: 4; `x₃,c`: 3), contradicting (b) with **no**
appeal to `hnoRigid`. That sub-case is what the driver asserts per pair (and it
holds at 5226/5226). It is *not* the general case: with `W`-`W` edges allowed
the violating configuration exists as a graph (`--adv` rows 7–8) and only
`hnoRigid` excludes it.

**(f) `A = 0` and `dim R = 5`.** `A₁ = def(H/X) − def(H/(X ∪ {b}))`; welding two
bodies of a rigid body-hinge framework is satisfied by its trivial motions, so a
contraction of a rigid graph is rigid and both terms vanish. For `dim R₁`: with
`μ₁ = 1`, `K = (H/X) − e₁` is independent of count 5, so `def(K) = 5`; and
`(K)/(b,v*) = (H/X)/e₁` is a contraction of a rigid graph, so its deficiency is
0. Hence `dim R₁ = 5 − 0 = 5`. ∎

**Corollary (the path bound).** `e₁` together with any `b`-to-`v*` path of `K`
of length `ℓ` closes a cycle of `H/X` of length `ℓ + 1`, and (b) applies to
`H/X` too (it is isostatic by (e)), so `ℓ ≥ 5`.

**Why items 1–2 are dead, stated as the consequence.** §(K-out) *What would
change this* item 1 asks for `dim R₁ = dim R₄ = 6` and item 2 for
`dim R₁ ≤ 4` or `μ₁ ≥ 2`; (OC-10) forbids all three at every class shape, so the
`0 of 4296` of (OC-2) and the `0 of 5226` of *Step O10*'s widened pool are not
rates at all. Both items should be **struck** from §(K-out) *What would change
this* and replaced by a pointer here.

**A remark that explains the sweep's zeros, and is worth recording because it
shrinks the class.** For a *theta* shape (2 hubs, `m` branches) tightness gives
`Σl = 6(m − 1)`, and a `k`-subset `S` of branches spans a subgraph of count
`Σ_S − 6(k − 1)`, so independence needs `Σ_S ≥ 6(k − 1)` and `hnoRigid`
(`kslidecomb.no_rigid_branch_union`) needs **strict** inequality for proper
subsets. With the split branch pinned at 3 and a companion branch at 4, the
`(m−1)`-subsets give `l_i ≤ 6` for every `i`, so the other `m − 2` branches sum
to `6(m−2) − 1` with each `≤ 6`: exactly one of them is 5 and the rest are 6.
But then `{3, 4, 5}` is a proper branch-union of count exactly 0 — **rigid** —
which `hnoRigid` forbids. Hence **no theta shape with `m ≥ 4` branches is a
class shape**, and θ(3,4,5) is the unique theta member. Driver-checked
exhaustively: `theta4` (`lmax = 13`, 364 tuples) and `theta5` (`lmax = 18`,
5700 tuples) both yield **0** class shapes.

---

### Step O10 — the widened sweep (POOL-CW), and (OC-11)/(OC-12): the hyperplane form

**POOL-CW.** `outer.named_inventory()` plus a widened family list: `theta3`
(exhaustive), `theta4` and `theta5` (exhaustive, both empty — see the remark
above), **two new 3-hub multigraphs** `M3a` (5 branches, exhaustive; 20 shapes)
and `M3b` (6 branches, exhaustive; 60 shapes), `K4` and `K4+par` at raised
bounds (540 / 740 shapes, unchanged from `outer.sweep_shapes()`, so those
`lmax` values were already effectively exhaustive), **`K4 +` two parallel edges**
(8 branches, capped; 60 shapes), the `|V°| = 5` families at `lmax = 6` capped at
60 each (180 shapes, versus 75 at the old cap 25 / `lmax` 5), and **`|V°| = 6`**
at `|E°| ≤ 10`, `lmax = 6`, cap 12 each (72 shapes over 6 hub graphs) — a family
`outer.sweep_shapes()` does not reach at all. Total **5226 (split, companion)
pairs over 1693 class shapes** (POOL-C: 4296 / 1376). **Disjoint in intent from
POOL-C but overlapping in content — POOL-CW figures are never summed with
POOL-C's, and POOL-CW supersedes rather than extends them.**

- `(μ₁, dim R₁, A₁, μ₄, dim R₄, A₄) = (1,5,0,1,5,0)` at **5226 of 5226**;
  `(χ, def(H/X), def(H/Y)) = (0,0,0)` at **5226 of 5226**. Hits for items 1 and
  2: **0 and 0** — and by (OC-10) that is forced, not measured.
- Per pair the driver asserts the proof's own steps: the `5χ` count identity,
  `χ = 0`, `μ = 1`, `def(H/X) = def(H/Y) = 0`, no vertex outside a weld with two
  weld-neighbours (the pigeonhole configuration), and `ℓ_min ≥ 5` at both ends;
  girth `≥ 6` is asserted on the first 250 pairs' shapes (the proof itself uses
  only the two *local* consequences, which are asserted at all 5226).
- **Coverage boundary, stated as a boundary.** `|V°| = 6` is reached only at
  `|E°| ≤ 10`: one `|E°| = 11` hub graph costs **137 s** at cap 8 — a measured
  cost, not a claim about those shapes. The `|V°| = 5,6` and `K4+2par` families
  are **capped**, so their shape lists are not exhaustive.

**The census, which is what the widening actually buys.** Two of these rows are
inputs to (OC-12)/(OC-13) and had never been measured:

| datum | histogram over the 5226 pairs |
|---|---|
| `(deg_G b, deg_G c)` | `(3,3) 2460`, `(3,4) 606`, `(4,3) 606`, `(4,4) 1522`, `(3,5) 15`, `(5,3) 15`, `(4,5) 1`, `(5,4) 1` |
| `(ℓ_min at b, at c)` | `(6,6) 1616`, `(7,7) 1478`, `(6,7)/(7,6) 317` each, `(8,8) 500`, `(6,8)/(8,6) 203` each, `(7,8)/(8,7) 246` each, `(8,9)/(9,8) 40` each, `(5,5) **8**`, `(6,9)/(9,6) 4`, `(7,9)/(9,7) 2` |
| `b` has no hub `G′`-neighbour / `c` has none | `(T,T) 1478`, `(T,F)/(F,T) 1749` each, `(F,F) 250` |
| companion hub pattern `(x₁,x₂,x₃)` | `(0,0,0) 1172`, `(0,0,1)/(1,0,0) 1634` each, `(0,1,0) 758`, `(1,0,1) 24`, `(0,1,1)/(1,1,0) 2` each |

So **(OC-12) applies at the `b` end at 3081 of 5226 pairs** and at **at least
one end at 3702 of 5226**; **(OC-13)'s hub slide is additionally legal at the
`b` end at 1715 of 5226**; and the bracket/M2 form of *Step O12* applies at
**8 of 5226**.

**Now the geometry.** `β_h` := the space of lines of the panel `Π(h)`. It is
`Λ²` of a 3-dimensional subspace of `K⁴`, hence **3-dimensional, every nonzero
element decomposable** (so every element is a genuine line of `Π(h)`) and
**totally `B`-isotropic** (four vectors in a 3-space have determinant 0) — all
three asserted per end. `L_h = α_{pt(h)} ∩ β_{Π(h)} ⊆ β_h` is a 2-dimensional
subspace, and *every* 2-dimensional subspace of `β_h` is the pencil of exactly
one point of `Π(h)` (a line of the dual plane).

> **(OC-11)** At any chart point with `dim Rᵢ = 5` (so, by (OC-10), at every
> one): `dim(Rᵢ ∩ β_h) ≥ 5 + 3 − 6 = 2`, and where the meet is exactly 2 it is
> the pencil `L_p` of a single point `p ∈ Π(h)`. Then
>
> - `λᵢ = 0 ⟺ Cᵢ ∈ Rᵢ ∩ β_h ⟺ p, pt(h), pt(xᵢ)` **collinear** — so §(K-out)
>   (OC-3)'s "exactly one marked direction of `x₁`'s pencil" is the direction
>   `pt(b) → p`, a formula rather than an existence statement;
> - `L_h ⊆ Rᵢ ⟺ p = pt(h)` — a **single point coincidence in the panel plane**.
>
> *Proof.* Both `Cᵢ` and every element of `L_h` lie in `β_h`, so the first
> equivalence is §(K-out) (OC-1) intersected with `β_h`; a line through `pt(h)`
> lies in the pencil `L_p` iff it passes through `p`; and `L_h = L_p` iff their
> centres agree. ∎

> **(OC-12)** Suppose `deg_G(b) = 3`, i.e. `deg_H(b) = 2` with `b`'s
> `H`-neighbours `x₁` and one other `u`. Then `C(b,u) ∈ R₁`
> **unconditionally**, hence `p ∈ C(b,u)`, hence — as long as `p ≠ pt(b)` —
> the marked direction of (OC-3) is exactly `C(b,u)` and
>
> `λ₁ = 0 ⟺ C(b,x₁) = C(b,u)`, i.e. `pt(b), pt(x₁), pt(u)` collinear.
>
> *Proof.* In `K = (H/X) − e₁` the body `b` carries the single hinge `b–u`, so
> the twist rotating `b` about `C(b,u)` and fixing everything else is a motion
> of `K`, and it realizes `m(b) − m(v*) ∝ C(b,u)`. `pt(u) ∈ Π(b)` (the closed
> star spans the panel), so `C(b,u) ∈ L_b ⊆ β_b`; thus
> `C(b,u) ∈ R₁ ∩ β_b = L_p` and `p ∈ C(b,u)`. If `p ≠ pt(b)` then
> `pt(b) ∨ p = C(b,u)` and (OC-11)'s first equivalence reads
> `pt(x₁) ∈ C(b,u)`. ∎
>
> **Two consequences.** (i) §(K-out) **(OC-7)'s implication is a theorem at a
> degree-3 hub**, together with its free-rotor reading: the coincidence
> exhausts `b`'s other `H`-neighbours because at degree 3 there is only one.
> (ii) **`repin.star_generic` implies `λ₁ ≠ 0`** at a degree-3 hub off the
> exceptional locus `{p = pt(b)}` — the guard the 2026-08-06 re-baselining
> round adopted is, at these ends, not merely a genericity hygiene measure but
> *the hypothesis of (OUT)*.

*Measured (POOL-W, `--wrench`).* The 4 `lambda.habitat_specs` habitats × seeds
**200–219**, accepted exactly as `outerline.frame_at` accepts them, with
`repin.star_generic` **reported** rather than applied (it is what (OC-12) is a
statement about): **73 frames, 146 companion ends**. `dim R = 5` at 146/146
(the theorem, re-checked); `dim(R ∩ β_h) = 2` at 146/146 (never 3);
`L_h ⊆ R` **false** at 146/146. Degree-3 ends: **38** (all θ(3,4,5)), at every
one of which `C(b,u) ∈ R` and `p ∈ C(b,u)` are asserted, `dim(T_u ∩ β_h) = 1`,
and `λᵢ = 0 ⟺` the coincidence is asserted. The guard sentence, tested as
itself: over the degree-3 ends, `(star_generic accepts, λᵢ = 0)` is
`(accepted, False) 30`, `(rejected, False) 4`, `(rejected, True) 4` — **0
violations of the implication, asserted per end**, not observed as a rate.

---

### Step O11 — (OC-13)/(OC-14): the bad locus is a line of the panel, and the hub slide reaches it

> **(OC-13)** At a degree-3 hub `b`, let `T_u := {m(u) − m(v*)}` in
> `(H/X) − b`. Then `dim T_u = 4`, `C(b,u) ∉ T_u`, `R₁ = ⟨C(b,u)⟩ ⊕ T_u`, and
> — because `C(b,u) ∈ β_b` —
> `R₁ ∩ β_b = ⟨C(b,u)⟩ ⊕ (T_u ∩ β_b)` with `dim(T_u ∩ β_b) ∈ {1, 2}`. Hence
>
> `L_b ⊆ R₁ ⟺ dim(T_u ∩ β_b) = 2, or pt(b) ∈ C₀`,
>
> where `C₀` is the line of `Π(b)` spanning `T_u ∩ β_b` in the 1-dimensional
> case. `T_u` involves **no** panel datum and **not** `pt(b)`, `pt(x₁)` or
> `pt(a)` (the body `b` is deleted from the system and `a ∉ V(H)`), and `β_b`
> depends only on the *plane* `Π(b)`. Therefore, whenever `b` has **no hub
> `G′`-neighbour**, sliding `pt(b)` inside `Π(b)` with the panel and every other
> point held fixed is a **legal chart move** along which `C₀` is constant, and
> the bad locus of `pt(b)` is exactly the line `C₀`.
>
> *Proof of the dimension count.* `(H/X) − b` has count `0 − 6 + 5·2 = 4` and is
> independent, so `def = 4` and `dim T_u ≤ 4`; `dim R₁ = 5` ((OC-10)) with
> `R₁ ⊆ ⟨C(b,u)⟩ + T_u` (split `m(b) − m(v*)` across the single hinge `b–u`)
> forces `dim T_u = 4` and `C(b,u) ∉ T_u`. `dim(T_u ∩ β_b) ≥ 4 + 3 − 6 = 1`; it
> cannot be 3, since that would put `C(b,u) ∈ β_b ⊆ T_u`. Legality of the slide:
> `Π(b)` unchanged keeps every `G′`-neighbour of `b` inside it and keeps every
> meet line through it (so `pt(a)` stays on `M = Π(b) ∩ Π(c)`), and `pt(b)`
> stays in the panels of its hub neighbours vacuously when there are none. ∎

> **(OC-14)** *(the experiment, `--slide`)* At θ(3,4,5), at every one of the
> **38** degree-3, hub-neighbour-free ends of POOL-SL (the 4 habitats × seeds
> 200–219; only θ(3,4,5) qualifies), the slide of `pt(b)` **onto** `C₀` lands —
> `38 of 38`, **zero** rejections — at an exact chart point which is
>
> - **target rank** with `dim R_a = 1`, `dim V_bc = 3`, `rank{C_i} = 4`,
>   `pt(a)` still on `M`, no coincident adjacent points, closed-star ranks 3;
> - **all four `IsNondegPencilRealization` conjuncts** green (38/38);
> - **(Λ0a)–(Λ0f′) all green**, with `λ ∦ p⁺`, `λ ∦ q` and
>   `deg_t Q(z(t)) = 4` (38/38) — so **the escape still holds there**, by the
>   pitch certificate, exactly as at §(K-out) (OC-4);
> - carrying `λᵢ = 0` **and** `L_h ⊆ R` (both asserted), i.e. `λᵢ` vanishes
>   *identically in the placement of `xᵢ`*;
> - with **no coincident hinge line at the hub** (38/38), and accepted by the
>   whole-configuration guard `repin.star_generic` at **34 of 38**.
>
> Conversely the slide **off** `C₀` lands at 38 chart points, at every one of
> which `λᵢ ≠ 0` and `L_h ⊄ R` — asserted, which is (OC-13)'s positive half.
> Four of the 38 on-`C₀` points have **both** outer coordinates zero, i.e.
> (OUT) **silent** at a point where one disjunct has died identically.

**What (OC-14) costs and what it buys, stated separately.**

*It costs §(K-out) (OC-7) its necessity claim.* (OC-7) records "the converse
fails …, so the coincidence is **necessary**, not sufficient". Necessity is
**refuted**: a guard-accepted, fully nondegenerate, target-rank hard-stratum
chart point of a real class habitat has `λ₁ = 0` with no coincident hinge at
`b`. The correct statement is (OC-12)'s **dichotomy** — at a degree-3 hub,
`λ₁ = 0` implies *either* the coincidence *or* `p = pt(b)`. Nothing else in
(OC-7) moves: the 33/36 manufactured-by-`plane_basis` finding, the standing rule
that no `place_pencil_general` battery may be quoted as a **rate**, and the
restriction of POOL-G rates to the **318** coincidence-free (or the **299**
guard-accepted) frames are all untouched, because the exceptional locus
`{pt(b) ∈ C₀}` has codimension 1 and random rational sampling never meets it.
That is also *why* (OC-7) measured 35/35: the second branch of the dichotomy is
invisible to sampling and visible only to a construction.

*It buys the sharpest available form of (OC-8).* Combining (OC-12) and (OC-13):
at a degree-3 hub, `(OUT)`'s first disjunct holds at **every** chart point
outside the union of two explicit hypersurfaces — `{C(b,x₁) = C(b,u)}` (which
`repin.star_generic` already rejects everywhere in the harness) and
`{pt(b) ∈ C₀}`. So

> **(OC-8), restated at a degree-3 hub.** (OUT)'s first disjunct is available at
> some hard-stratum target-rank chart point **iff** that locus is not contained
> in `{pt(b) ∈ C₀}`. One explicit line of one panel plane; no rank condition
> left in the statement.

This is §(K-out) (OC-8)'s "relocated and weakened, not crossed" made concrete:
the wall is now a containment question about the target-rank locus, and the
object it must avoid is written down.

---

### Step O12 — (OC-15)/(OC-16): the path-span form, its exact reach, and the M2 computation

> **(OC-15)** `R₁ ⊆ span{C_e : e ∈ π}` for **every** `b`-to-`v*` path `π` of
> `K = (H/X) − e₁`, since `m(u) − m(w) ∈ ⟨C(u,w)⟩` at every hinge and
> `m(b) − m(v*)` telescopes along `π`. With `dim R₁ = 5` this re-proves the
> corollary of (OC-10) (`|π| ≥ 5`) and gives, when some `|π| = 5`, the
> **equality** `R₁ = span{C_e : e ∈ π}` — `R₁` is then a **bracket** object,
> computed from five hinge lines with no rigidity matrix.
> **The converse is REFUTED for `ℓ_min ≥ 6`:** the intersection over all paths
> is then already all of `K⁶` and carries no information. Measured per end over
> POOL-W, `(#paths, dim of the intersection, the intersection equals `R`)`:
> `(1, 5, True) : 38`, `(2, 6, False) : 38`, `(3, 6, False) : 70`. The
> containment itself is asserted per path at all 146 ends.

So the bracket form is exactly the **`ℓ_min = 5` stratum**, and *Step O10*'s
census prices it: **8 of 5226** POOL-CW pairs. That is the honest reach of the
symbolic route, and it is a limit on the *bracket* form only — (OC-11)–(OC-13)
need nothing but `deg_H(b) = 2`.

**The variety, and the computation.** On the `ℓ_min = 5` stratum, with the
chain `b–u–w₂–w₃–w₄–x` (`x ∈ X`) and `pt(a) ∈ M ⊆ Π(b)` giving a second
generator `C(b,a)` of `L_b`,

`L_b ⊆ R₁ ⟺ Δ := det₆[C(b,u), C(u,w₂), C(w₂,w₃), C(w₃,w₄), C(w₄,x), C(b,a)] = 0`

— **one `6×6` Plücker determinant in seven points**, and `R₁`'s far-ness has
dissolved: this is a statement about the **local frame**, inside
`notes/Pencil-strategy.md` §5.3's boundary, which is what item 6 asked for and
what the arc has never had on the `λ` side. `m2/outerwide.m2` computes it on the
gauge slice `Π(b) = {x₄ = 0}`, `Π(c) = {x₃ = 0}`, `pt(c) = e₄`, `pt(a) = e₁`
(legitimate: `PGL(4)` is transitive on (ordered distinct planes, a point of the
second off the meet, a point of the meet), and `Δ`'s vanishing is
`PGL(4)`-invariant), leaving `pt(b)` **free** in `Π(b)` because the locus of
`pt(b)` is the point of the exercise:

> **(OC-16)** *(`M2 --script notes/scripts/m2/outerwide.m2`, M2 1.26.06,
> deterministic)* On that local frame: the five chain hinge lines are
> independent at the generic point; `Δ ≠ 0` **as a polynomial** (degree 10, 148
> terms), so `L_b ⊄ R₁` at the generic point — an identity over the function
> field rather than 38 rational witnesses; and `Δ` factors into **exactly two**
> simple irreducible factors,
>
> `Δ = [a, u, b] · C₀(pt b)`,
>
> the first being the in-panel collinearity bracket (the degenerate case where
> `C(b,u)` and `C(b,a)` fail to span `L_b` at all — a coincident hinge at `b`,
> which `repin.star_generic` rejects) and the second **linear in `pt(b)`**, with
> coefficients involving only `pt(u), pt(w₂), pt(w₃), pt(w₄)`. That second
> factor **is (OC-13)'s `C₀`, in closed form**; the two lines are distinct
> (asserted), and `C₀` passes through neither `pt(u)` nor `pt(a)`. The
> `pt(b)`-freeness of the coefficients is (OC-13)'s "`T_u` and `β_b` do not see
> `pt(b)`" read symbolically — the symbolic certificate of the hub slide's
> legality.

**What (OC-16) does not establish, named as the residue.** It is a statement at
the generic point of the **local frame**. Carrying it to a class shape needs the
**chart-to-frame map to be dominant** — the same step `m2/lambda0.m2` had for
free because (Λ0) is a local-frame statement with the far graph absent, and the
same step §(K-out) (OC-8) says the arc has never established because `λ` is a
far datum. Here the far datum has been compressed to four chain points, so the
dominance question is *smaller* than (OC-8) as recorded, but it is not
discharged: at a shape whose chain interiors are constrained by other hubs'
panels, the frame's parameters are not free. **That is the residue this pass
leaves**, and it is a finite check per chain hub pattern (the census's
`(x₁,x₂,x₃)` histogram is the companion-side analogue).

---

### Confidence verdict (Steps O9–O12)

| | claim | standing |
|---|---|---|
| **(OC-10)** | `χ = 0`, `μ = 1`, `H/X`, `H/Y` isostatic, `A = 0`, `dim R = 5` at every class shape (tight + isostatic + chain ends hubs + `hnoRigid`); hence *What would change this* items 1–2 are unrealizable | **proven-informally** (Step O9: the count-matroid sparsity equivalence that `kslidecomb.shape_ok`'s docstring already records, girth-6, and one boundary case discharged by `hnoRigid` via a rigid-proper-branch-union). Conclusion corroborated at **5226/5226** POOL-CW pairs with the proof's steps asserted per pair; **all four hypotheses shown load-bearing** by eight adversarial non-class graphs (`--adv`), 6 realizing item 1 and 5 item 2, one of them isolating **`hnoRigid`** as the single broken hypothesis. **The first draft of the proof was wrong and this driver refuted it** — treat the hypothesis list as part of the claim |
| **theta remark** | no theta shape with `m ≥ 4` branches is a class shape; θ(3,4,5) is the unique theta member | **proven-informally** (arithmetic + `hnoRigid`); exhaustively driver-checked at `m = 4, 5` (0 shapes over 364 + 5700 tuples) |
| **(OC-11)** | `dim(Rᵢ ∩ β_h) ≥ 2` always; where `= 2` it is a pencil `L_p`; `λᵢ = 0 ⟺ p` on `C(h,xᵢ)`; `L_h ⊆ Rᵢ ⟺ p = pt(h)` | **proven-informally** (two lines of projective geometry on top of (OC-10)); both equivalences asserted per end at **146/146** POOL-W ends |
| **(OC-12)** | at `deg_G(b) = 3`: `C(b,u) ∈ R₁`, `p ∈ C(b,u)`, and off `{p = pt(b)}` `λ₁ = 0` **is** the coincident-hinge condition; so `star_generic ⟹ λ₁ ≠ 0` there | **proven-informally**; asserted per end at all **38** degree-3 ends of POOL-W, **0 violations** of the guard implication. Applies at **3081 of 5226** POOL-CW pairs at the `b` end, **3702** at some end |
| **(OC-13)** | `R₁ = ⟨C(b,u)⟩ ⊕ T_u`, `R₁ ∩ β_b = ⟨C(b,u)⟩ ⊕ (T_u ∩ β_b)`, the bad `pt(b)`-locus is the line `C₀`, and the hub slide is legal when `b` has no hub `G′`-neighbour | **proven-informally**; `dim T_u = 4`, `C(b,u) ∉ T_u`, `R₁ = ⟨C(b,u)⟩ ⊕ T_u`, `dim(R₁∩β) = 1 + dim(T_u∩β)` and `pt(b) ∈ C₀ ⟺ p = pt(b)` all asserted at 38/38 degree-3 ends; legality at **1715 of 5226** pairs at the `b` end |
| **(OC-14)** | `L_h ⊆ R` is **reachable** at θ(3,4,5) — 38 exact, fully nondegenerate, guard-accepted (34/38) chart points with `λᵢ = 0` and **no** coincident hinge at the hub, the escape still holding; hence (OC-7)'s **necessity** claim is refuted | **exhibited by construction** (38 points, deterministic slide targets, zero rejections); the refutation of (OC-7)'s necessity is therefore **settled**, and the corrective dichotomy is (OC-12) |
| **(OC-15)** | `R₁ ⊆` every path's hinge-line span (hence `ℓ_min ≥ 5`), with equality iff some path has length 5; the intersection form is **useless** for `ℓ_min ≥ 6` | containment **proven-informally** and asserted per path at 146/146 ends; the equality's failure **measured** (`(2,6,False) 38`, `(3,6,False) 70`); reach priced at **8 of 5226** pairs |
| **(OC-16)** | `Δ ≢ 0` at the generic point of the length-5-chain local frame; `Δ` has exactly two simple irreducible factors; the non-degenerate one is linear in `pt(b)` and **is** `C₀` | **proven at the generic point of the local frame** (M2 1.26.06, exact, deterministic) — **not** a class statement: the chart-to-frame dominance is not computed |
| **(OC-8)** | the residue, restated: at a degree-3 hub, availability ⟺ the hard-stratum target-rank locus `⊄ {pt(b) ∈ C₀}` | **OPEN**, and now a containment question about the target-rank locus rather than a rank lower bound |

**No gap-map status moves, and class uniformity is untouched.** What moves is
the *content* of two rows: §(K-out)'s (which gains (OC-10)–(OC-16), loses items
1–2 of its *What would change this*, and must record the (OC-7) correction) and
the **(K-wit)** row's *what would close it* cell, whose (OUT) caveat should now
read: *never automatic ((OC-3)), but at a degree-3 hub the bad locus is exactly
the coincident-hinge locus together with one explicit line `C₀` of the panel
((OC-12)/(OC-13)), the first of which every harness gate already rejects and the
second of which is reachable by construction ((OC-14))*.

### What would change this (Steps O9–O12)

1. **A degree-3 hub with `dim(T_u ∩ β_b) = 2`** would make `L_b ⊆ R₁` for
   *every* `pt(b)` of the panel — the shape-level bad case, a codimension-2
   Schubert condition on `T_u ∈ Gr(4,6)` against the fixed 3-plane `β_b`. Not
   seen: `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends. The cheap next
   probe is the same `--wrench` leg over a **shape** pool (POOL-S-style, many
   shapes × few seeds) rather than four habitats × many seeds. **Promoted
   from a hunt to the exact residue (2026-08-19, direction OCON):** at the
   1715 slide-legal `b` ends this condition (in its perp form
   `T_u^{⊥_B} ∩ β_b ≠ 0`) is exactly the failure of availability, an **iff**
   by §(K-out) (OC-21).
2. **A `deg_H(b) ≥ 3` analogue of (OC-12).** At degree `≥ 3` no hinge rotation
   survives in `K`, so `C(b,u) ∈ R₁` fails and the marked direction is not a
   neighbour direction; `dim(R₁ ∩ β_b) = 2` and `p ≠ pt(b)` were nevertheless
   measured at all 108 non-degree-3 POOL-W ends. Whatever replaces `C(b,u)`
   there would extend (OC-12) from 3702 to all 5226 pairs. **Answered in a
   different shape (2026-08-19, direction OCON):** §(K-out) (OC-18) makes a
   `deg_H(b) ≥ 3` analogue of (OC-12) unnecessary for (OC-8) — its
   degree-free sufficient condition covers both ends of every class pair —
   though the marked-direction *formula* this item originally asked for is
   still open.
3. **`R₁` as an iterated span/intersection of hinge lines along `K`'s block
   structure.** (OC-15) kills the naive path-intersection at `ℓ_min ≥ 6`, but
   the two structural cases seen so far both decompose: a serial prefix
   contributes its span, and a branch vertex where two paths diverge should
   contribute the **intersection of the two branch spans** (dimension
   `4 + 4 − 6 = 2` in the one worked example). If that decomposition is a
   theorem, `R₁` is a bracket object at **every** end and (OC-16)'s M2 object
   generalizes off the 8-pair stratum. This is the single highest-value next
   step of this section, and it is a pure screw-system statement about a
   subdivision of a small multigraph — no pencil pin needed.
4. **The chart-to-frame dominance for (OC-16).** Per chain hub pattern, does a
   class shape's pencil chart dominate the local frame? Finitely many patterns;
   `hcard_ok` caps hub-hub adjacency at 2, which bounds the zoo. A negative at
   some pattern would be a class shape with `Δ ≡ 0` — i.e. (OUT)'s first
   disjunct dead on the whole chart, the strongest possible negative and a
   genuine kill for that shape.
5. **Sliding both ends onto their bad lines simultaneously.** `C₀` at the `b`
   end depends on `pt(c)` and vice versa, so the two slides are **coupled** and
   a sequential slide breaks the first condition. A joint solve (two equations,
   four panel parameters) would decide whether **both** disjuncts can die
   identically at one chart point — which is the first thing that would make
   (OUT) *dead*, not merely silent, at a class habitat. Four of the 38
   constructed points already have both outer coordinates zero, but only one
   disjunct dies *identically* there.
6. **Deliberately not attempted, again:** §(K-out) *What would change this* item
   4 (pushing a constructed point to the bad point `p⁺`). The 38 constructed
   points of (OC-14) are a natural launch pad for it — they keep every (Λ0)
   clause and spend only the `pt(b)` freedom — which is a reason to record the
   restraint explicitly rather than let a successor assume it was tried.

### Verification (Steps O9–O12)

`notes/scripts/w4/outerwide.py` (new, untracked; exact ℚ; a `w4/` leaf **above**
`outerline`, which it imports read-only for the welded relative-twist model —
`weld_motions`, `rel_span`, `line_pencil`, `comb_data`, `frame_at`, `clauses` —
so nothing is re-derived) and `notes/scripts/m2/outerwide.m2` (new, untracked;
M2 1.26.06 printed as the second output line; `randomness: none`; an (M0)
convention pin against `exactcore.wedge2`'s `PL` order and `pitch.klein` on a
fixed rational instance, per `notes/scripts/m2/README.md` convention 3).
Nothing existing is modified. From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wide     # (OC-10), POOL-CW + the census
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --adv      # (OC-10)'s minimality, POOL-A
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --wrench   # (OC-11),(OC-12),(OC-13),(OC-15), POOL-W
PYTHONHASHSEED=0 python3 notes/scripts/w4/outerwide.py --slide    # (OC-14), POOL-SL
M2 --script notes/scripts/m2/outerwide.m2                         # (OC-16)
```

Times as run: `--wide` **122 s**, `--adv` **0.2 s**, `--wrench` **87 s**,
`--slide` **75 s**, the M2 driver **0.5 s**. Each fits a single 600 s foreground
budget comfortably; all four Python modes and the M2 driver re-run
**byte-identical** under two different `PYTHONHASHSEED` values (`0` and
`12345`), the *figures-do-not-move* gate (`notes/scripts/README.md`) — which
this pass discharges by the check itself, having **added** two drivers and
modified none.

**Pools, pinned; every figure above is quoted over exactly one of them, and
none is aggregated with POOL-C / POOL-G / POOL-S / POOL-B.**

- **POOL-CW** (`--wide`) — deterministic, no rng: `outer.named_inventory()`
  plus `wide_shapes()`. **5226 (split, companion) pairs over 1693 class
  shapes.** Per-family coverage boundary printed (`EXHAUSTIVE` when the `lmax`
  provably cannot bind, else `BOUNDED`/`CAPPED` with the arithmetic bound).
- **POOL-A** (`--adv`) — **eight** hand-built **non-class** graphs, no rng. Not
  class figures, and labelled as such in the output. Rows 7 and 8 are the ones
  that refuted Step O9's first draft; row 8 isolates `hnoRigid`.
- **POOL-W** (`--wrench`) — the 4 habitats × seeds **200–219**; **73 frames,
  146 companion ends**; `star_generic` reported, not applied.
- **POOL-SL** (`--slide`) — the same habitats × seeds, restricted to degree-3,
  hub-neighbour-free ends (only θ(3,4,5) qualifies); **38 ends**, deterministic
  slide targets from a fixed coefficient ladder.

Per mode, what is asserted:

- `--wide`: per pair, the `5χ` count identity for `H/X`; `χ = 0`; `μ = 1`;
  `def(H/X) = def(H/Y) = 0`; no vertex outside a weld with two weld-neighbours;
  `ℓ_min ≥ 5` at both ends; `G` tight and `def(G) = 0`; the histogram's
  uniformity; girth `≥ 6` on the first 250 pairs' shapes.
- `--adv`: per graph, which of (OC-10)'s **eight** named hypotheses it breaks —
  computed, not asserted by hand: `count(H) = 3`, `G` tight, `def(G) = 0`,
  `b, c` hubs, `hnoRigid` (by brute-force enumeration of rigid proper subgraphs
  with min degree `≥ 2`, which in a subdivision are exactly the branch-unions),
  girth `≥ 6`, `χ = 0`, no 2-into-weld vertex — and that **every** graph
  exhibiting a hit breaks at least one. That assertion is the one that fired on
  Step O9's first draft.
- `--wrench`: per end, `dim R = 5`; `β_h` 3-dimensional and totally
  `B`-isotropic; `dim(R ∩ β_h) ≥ 2`; the pencil centre `p` on both meet lines;
  (OC-11)'s two equivalences; at degree-3 ends `C(b,u) ∈ R`, `p ∈ C(b,u)`,
  `R = ⟨C(b,u)⟩ ⊕ T_u`, `dim T_u = 4`,
  `dim(R ∩ β) = 1 + dim(T_u ∩ β)`, `pt(b) ∈ C₀ ⟺ p = pt(b)`, and
  `λᵢ = 0 ⟺` the coincidence; (OC-15)'s containment per path; the chain
  equality at `ℓ_min = 5`; and the guard implication `star_generic ⟹ λᵢ ≠ 0`
  at every degree-3 end.
- `--slide`: at every slid point the whole acceptance battery re-run from
  scratch on the modified placement (panels, adjacent-point distinctness,
  closed-star ranks, target rank, `dim R_a = 1`, panels non-parallel,
  `dim V_bc = 3`, `rank{C_i} = 4`, `λ` a point of `P(S*)`, `pt(a)` on `M`, all
  four nondeg conjuncts, the (Λ0a)–(Λ0f′) battery); that every on-`C₀` point
  has `λᵢ = 0` **and** `L_h ⊆ R`; that every off-`C₀` point has neither; and
  that `λ` is proportional to **neither** `p⁺` **nor** `q` and
  `Q(z(t)) ≢ 0` at every constructed point (the sentence that would be the
  headline if it failed).
- `outerwide.m2`: (M0) the convention pin; the chain's independence at the
  generic point; `Δ ≠ 0`; exactly two simple irreducible factors; the
  collinearity bracket divides `Δ`; the complementary factor is linear in
  `pt(b)` and not a multiple of the collinearity line.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics and the M2 layer — **never** a substitute for
Lean (`DESIGN.md` *Formalize everything the argument uses*). Nothing in
`outerline.py`, `outer.py`, `lambda.py` or `repin.py` was modified; all are
read.

### Steps O13–O18 (2026-08-19, sixth fan-out, direction OCON) — (OC-8)'s **hard-stratum target-rank qualifier is FREE**: the stratum is an *open* subvariety of the chart ((OC-17)), so §(K-frame) (FR-7)'s un-owned irreducibility object is **struck**, one chart point *anywhere* suffices, and the sufficient condition that point has to satisfy is **`H/X` infinitesimally rigid** ((OC-18)) — degree-free, at **both ends of every class pair** — which lands (OC-8)'s residue in the **same object class as §(K-ann) (ANH-R1)**; (OC-8) stays **OPEN**, no gap-map status moves

Driver `notes/scripts/w4/ocon.py` (new this pass; imports `outerline` and
`outerwide` read-only, modifies nothing); labels **(OC-17)–(OC-22)**. Everything
cited that this pass did not mint is qualified: **(OUT)**, **(Λ0a)–(Λ0i)** are
§(K-Λ)'s; **(FR-1)**/**(FR-3)**/**(FR-4)**/**(FR-6)**/**(FR-7)** are §(K-frame)'s;
**(ANH-9)**/**(ANH-R1)** are §(K-ann)'s; **(S1)** is §(K-slide)'s; **(D4)** is
§(K-dom)'s; **(K-tight)** *Step 2*'s items are §(K-tight)'s. POOL-C / POOL-G /
POOL-S / POOL-B / POOL-CW / POOL-A / POOL-W / POOL-SL are this section's earlier
pools and **nothing below is aggregated with them**.

Write `Z` for the **hard-stratum target-rank locus** of the pencil chart of
`G′ = G − v + ab` at an eligible split — the set (OC-8) quantifies inside.

Five things, in the order they change the reading of (OC-8).

- **(OC-17) — `Z` is an OPEN subvariety of the chart, not a stratum.** At
  **every** legal chart point, with no genericity anywhere,
  `dim R_a = corank(G′) − s₀`: the stress space of `G′` maps *onto* `R_a`, and
  its kernel is exactly the stress space of `G′ − ab = G − v`, whose dimension
  is `s₀`. With `index(G) = 0` (tight) and `def(G′) = 0` (§(K-tight) *Step 2*'s
  declared scope) that reads `dim R_a = 1 − s₀`, so
  `Z = {rank R(G′) = 6(|V(G)| − 2) − def(G′)} ∩ {rank R(G − v) = 5|E(G − v)|}`
  — an intersection of **two maximal-rank conditions**, hence Zariski open.
  Consequence, and the reason this matters: **an open subset of an irreducible
  variety is irreducible and dense.** §(K-frame) **(FR-7)**'s named residual
  ingredient — *"the smallest object is the hard-stratum target-rank locus of
  the (shape, split) chart … whose irreducibility nobody owns"* — is therefore
  **owned as soon as the chart is**, and §(K-ann) **(ANH-9)(ii)** /
  §(K-slide) *Step 1(e)* / §(K-dom) **(D4)** already own that. The one thing
  (OC-17) does *not* supply is `Z ≠ ∅`, which is a separate input — see (OC-19).
- **(OC-18) — a degree-free sufficient condition, at both ends of every pair:
  `H/X` infinitesimally rigid.** `W₁ = {m(b) − m(v*)}` in the welded framework
  `H/X` (with `e₁` **present**) is exactly (OC-1)'s space, and (OC-1) gives
  `λ₁ = 0 ⟺ dim W₁ = 1`. If `H/X` is infinitesimally rigid at the chart point
  then every motion is trivial, so `W₁ = 0`, so **`λ₁ ≠ 0`, hence `C₁ ∉ R₁`,
  hence `L_b ⊄ R₁`** — a witness of (OC-8)'s first disjunct at that point.
  `{H/X infinitesimally rigid}` is `{rank = 6|V(H)| − 6}`, a **maximal-rank
  hence open** condition, and (OC-10)(e) proves `def(H/X) = 0`, so it is
  non-empty in the **ambient** placement space. **No degree hypothesis is
  used** — only (Λ0a) and `μ = 1`, which (OC-10) proves at every class pair —
  so it applies at **both ends of every class pair**, where (OC-12)
  additionally needs `deg_G(b) = 3` and (OC-13)'s slide additionally needs no
  hub `G′`-neighbour. For comparison, over POOL-CW's **labelled** pairs
  (harness README §4 convention 7 — labelled instances, never a class-level
  ratio): **5226 of 5226** against (OC-12)'s 3081 (`b` end) / 3702 (some end)
  and (OC-13)'s slide-legal 1715. §(K-out) *What would change this (Steps
  O9–O12)* **item 2 is answered, though not in the shape it asked for**: it
  wanted the replacement for
  `C(b,u)` at `deg_H(b) ≥ 3` — the *marked direction*'s formula — and (OC-18)
  instead makes the marked direction unnecessary for (OC-8)'s purpose.
- **(OC-19) — the reduction: (OC-8) factors into three inputs, one of which is
  not (OUT)'s to pay.** At a class (shape, split, length-4 companion), (OC-8)'s
  `b`-end disjunct **follows from**: **(a)** `Z ≠ ∅`; **(b)** the pencil chart
  of `G′` is irreducible; **(c)** *one* chart point — **anywhere on the chart,
  with no rank-stratum condition on it** — at which `H/X` is infinitesimally
  rigid. Proof: (b) makes the open sets of (a) and (c) dense, and two dense
  opens of an irreducible variety meet. **Input (a) is a prerequisite of the
  whole (K-tight) criterion, not of (OUT)**: §(K-tight) *Step 2* item 3 records
  that `dim R_a = 0` forces uniform failure of routes A **and** B at every
  placement, so a shape with `Z = ∅` loses the KT-route escape entirely,
  independently of (OUT). What is genuinely (OUT)'s is (c), and it is
  **one-point decidable per (shape, split)** by one exact rank computation at
  one rational chart point — the `λ`-side analogue of §(K-ann) **(ANH-9)(iii)**.
- **(OC-20)/(OC-21) — the bad case, in its perp form, with `x₁` deleted from
  the statement.** `β_h` is a **maximal** totally `B`-isotropic 3-space, so
  `β_h^{⊥_B} = β_h` and for any subspace `T`,
  `dim(T ∩ β_h) = dim T + 3 − 6 + dim(T^{⊥_B} ∩ β_h)`. At `dim T_u = 4` that is
  `dim(T_u ∩ β_h) = 1 + dim(T_u^{⊥_B} ∩ β_h)`, so **(OC-13)'s shape-level bad
  case `dim(T_u ∩ β_b) = 2` is exactly `T_u^{⊥_B} ∩ β_b ≠ 0`** — one 2-space of
  wrenches meeting one 3-space of panel lines, a Schubert condition written
  down. Separately, `R₁^{⊥_B} = ⟨ρ⟩` is one wrench and (OC-11)'s marked point
  `p` is the point of `Π(h)` cut out by `B(ρ, ·)|_{β_h}` — **and `ρ` is
  measured NOT `B`-isotropic at 4/4 degree-3 POOL-OC ends**, so the tempting
  reading *"`p = ρ ∩ Π(h)`"* is valid only in the non-generic decomposable
  case and is recorded here as the trap it is. And (OC-21): at a degree-3 hub
  with `pt(b), pt(u), pt(a)` non-collinear, `L_b = ⟨C(b,u), C(b,a)⟩` with
  `C(b,u) ∈ R₁` free, so **`L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁`** — the condition is about
  the **split-edge** hinge line and `x₁` has left the statement altogether.
- **(OC-22) — where the residue lands: the same object class as (ANH-R1).**
  After (OC-19), (OC-8)'s own content is *"the welded far framework `H/X` is
  infinitesimally rigid at one pencil chart point"*. §(K-ann) **(ANH-R1)** is
  *"`H/P − β` is infinitesimally rigid at the pencil placement"*, and
  `H/P = (H/X)/(b ∼ v*)`, so the two objects sit on one contraction tower. The
  arc had recorded three independent arrivals at the *same missing technology*
  ((ANH-9)(iii)'s class-uniform independent-point recipe: §(K-grid)'s residual,
  §(K-ann)'s, §(K-out) (OC-16)'s); this is the first arrival at the **same kind
  of object**, which is what makes §(K-frame)'s (FR-1)+(FR-4) machinery apply
  to (OC-8) verbatim rather than by analogy.

**Verdict, stated at the strength the work supports.** **(OC-8) stays OPEN and
no gap-map status moves.** What moves is its *shape*: the hard-stratum
target-rank qualifier — the thing §(K-frame) (FR-7) named as the un-owned
ingredient and §(K-frame) (FR-6) spent 4 of its 8 colourings satisfying — is
**free**, and the residue is a pencil-rigidity statement about a welded far
framework, degree-free and one-point decidable. **Class uniformity is untouched**,
and the honest boundary is (OC-19)'s input (c) at *every* class shape, which no
argument here supplies.

---

### Step O13 — (OC-17): the hard stratum at target rank is an **open** subvariety of the chart

Notation is §(K-out)'s *Standing notation* plus: `G′ = G − v + ab`
(`outer.split_data`'s `Gp`), `s₀` = the **row corank** of the shared rows
(the edges of `G − v = G′ − ab`; `repin.py:252`, `s0 = 5·|E| − rank`), `R_a` the
boundary-load space of §(K-tight) *Step 2* item 2 (`outer.stratum_at`),
`index(G) := 5|E(G)| − 6(|V(G)| − 1)` (§(K-ind) *Standing notation*), `corank(G′)`
the dimension of `G′`'s stress space at the placement.

> **(OC-17)** *(proven-informally)* At **every** chart point with
> `pt(a) ≠ pt(b)` — no genericity, no target-rank hypothesis:
>
> `dim R_a = corank(G′) − s₀`.  (†)
>
> At a target-rank point `corank(G′) = index(G) + 1 + def(G′)`, so for a class
> shape (`index(G) = 0`) inside §(K-tight) *Step 2*'s scope (`def(G′) = 0`),
> `dim R_a = 1 − s₀` and
>
> `Z := {target rank} ∩ {dim R_a = 1}`
> ` = {rank R(G′) = 6(|V(G)| − 2) − def(G′)} ∩ {rank R(G − v) = 5|E(G − v)|}`,
>
> an intersection of **two maximal-rank conditions** — hence a **Zariski-open**
> subset of the pencil chart.
>
> **Corollary (the one that matters).** If the chart is irreducible and
> `Z ≠ ∅`, then `Z` is **dense open and irreducible**. So §(K-frame) **(FR-7)**'s
> *"the smallest object is the hard-stratum target-rank locus … whose
> irreducibility nobody owns"* is **struck**: its irreducibility is the
> chart's, which §(K-ann) **(ANH-9)(ii)**, §(K-slide) *Step 1(e)* and §(K-dom)
> **(D4)** already own and consume.

*Proof of (†).* `R_a` is by definition the image of the map
`σ : {stresses of G′} → K⁶`, `λ ↦ Σ_{r ∈ ab-rows} λ_r · r|_{a-block}`
(`outer.stratum_at`, `repin.seed_probe`). The five `ab` rows restricted to the
`a` block are the five rows of that hinge and span `C(ab)^⊥`, of dimension 5,
whenever `C(ab) ≠ 0` — i.e. whenever `pt(a) ≠ pt(b)`, which
`IsNondegPencilRealization` conjunct 2 supplies. So the composite
`λ ↦ λ|_{ab} ↦ σ(λ)` is injective on the `ab`-coordinates, and
`ker σ = {λ : λ|_{ab} = 0}` = the stress space of `G′ − ab = G − v`, of dimension
`s₀`. Rank–nullity gives (†). ∎

*Proof of the two displayed forms.* At target rank,
`corank(G′) = 5|E(G′)| − [6(|V(G′)| − 1) − def(G′)] = index(G′) + def(G′)`, and
`index(G′) = index(G) + 1` (§(K-ind) *Step I2*), which is
`notes/Pencil-W4-informal.md`'s recorded count identity
`corank(G′) = index(G) + 1 + def(G′)`. With `index(G) = 0`, `def(G′) = 0`:
`dim R_a = 1 − s₀`, so on the target-rank locus `dim R_a = 1 ⟺ s₀ = 0`. And
`s₀ = 0` is `rank R(G − v) = 5|E(G − v)|`, the maximum a matrix with that many
rows can have; `rank R(G′) = 6(|V(G)| − 2) − def(G′)` is likewise the maximum
(rank is bounded above by the generic rank). Both are non-vanishing of a
maximal minor, hence open. ∎

*Two remarks, each recorded because a one-line quotation will get it wrong.*

*(i)* **§(K-tight) *Step 2* item 3 is not corrected, it is completed.** That
item states `dim R_a = index(G) + 1 − s₀` "at a target-rank seed"; (†) carries
the extra `+ def(G′)`, which vanishes inside *Step 2*'s own declared scope
(`def(G) = def(G′) = 0`). Outside that scope the `def(G′)` term is live, and
(†) itself needs neither scope clause nor target rank.

*(ii)* **`Z` open does not make `Z` big, and it does not make (OC-8) true.**
`Z` is cut out by two *non-vanishing* conditions on the chart, so it is open —
but a nonempty open of an irreducible variety is dense, and that is the whole
force of the corollary. `Z ≠ ∅` is a genuinely separate input; it is **measured
`≠ ∅`** at every probed (split, companion) pair (POOL-S: 270 frames over 90
splits, *Step O7*) and at all four habitats, and the arc's only recorded
`dim R_a = 0` chart points are §(K-flank) *F5(d)*'s five `P21` seeds — at a
shape carrying **no** length-4 `bc`-companion, so not a counterexample to
(OC-8), which is vacuous there.

---

### Step O14 — (OC-18): `H/X` infinitesimally rigid at a chart point ⟹ (OUT)'s first disjunct, at **every** class pair

> **(OC-18)** *(proven-informally; asserted per end)* Let a class (shape,
> split, length-4 companion) be given, and let a chart point be one at which
> the **welded** framework `H/X` — `X = {x₁,x₂,x₃,c}` welded into one body
> `v*` by explicit equality rows, with `e₁ = bx₁` **present** — is
> **infinitesimally rigid** (`dim Mot(H/X) = 6`). Then at that point
>
> `λ₁ ≠ 0`, hence `C₁ ∉ R₁`, hence `L_b ⊄ R₁`.
>
> `{H/X infinitesimally rigid}` = `{rank = 6|V(H)| − 6}` is a **maximal-rank,
> hence Zariski-open** subset of the chart; and (OC-10)(e) proves
> `def(H/X) = 0`, so it is **nonempty in the ambient placement space**.
> Symmetrically at the `c` end with `H/Y`.
>
> **Coverage.** The statement uses **no degree hypothesis** — only (Λ0a) and
> (OC-1). By (OC-10) `μ₁ = μ₄ = 1` at **every class pair**, so (OC-18) applies
> at **both ends of every class (split, companion) pair**, with no census
> needed. For comparison against the two degree-gated predecessors, over
> POOL-CW's **labelled** pairs (harness README §4 convention 7 — labelled
> instances, never a class-level ratio): (OC-18) **5226 of 5226**, (OC-12)
> **3081** (`b` end) / **3702** (some end), (OC-13)'s slide legal at **1715**
> (`b` end).

*Proof.* `H/X` infinitesimally rigid means every infinitesimal motion is a
global (trivial) twist, which assigns the same screw to every body; so
`m(b) − m(v*) = 0` for every motion, i.e. `W₁ = {m(b) − m(X)} = 0`. (OC-1)'s
chain reads `λ₁ = 0 ⟺ C₁ ∈ V_bc ⟺ dim W₁ = 1`, so `λ₁ ≠ 0`. With `μ₁ = 1`,
(OC-1) also gives `λ₁ = 0 ⟺ C₁ ∈ R₁`, so `C₁ ∉ R₁`; and `C₁ = C(b, x₁) ∈ L_b`
(the pencil of lines through `pt(b)` in `Π(b)`, since `pt(x₁) ∈ Π(b)`), so
`L_b ⊄ R₁`. The rank statement: `dim Mot ≥ 6` always, so `dim Mot = 6` is
`rank = 6|V(H)| − 6`, maximal. ∎

**What this is and is not.** It is **not** a proof of (OUT)'s hypothesis: the
pencil chart is a proper subvariety of the placement space, and (OC-2)'s
warning — *"the combinatorial half does not deliver availability"* — applies
verbatim to `def(H/X) = 0`. (OC-3) stands unchanged: the bad locus is nonempty
on every class shape's chart, so no count can discharge (OUT). What (OC-18)
supplies is a **transfer-shaped** criterion in place of a chart-geometric one:
the ambient-generic fact is `def(H/X) = 0`, the chart-side question is whether
its *open* consequence survives to one chart point, and the object doing the
work is a rigidity statement rather than a containment.

*Measured, POOL-OC (`--check`).* At all **12** companion ends of the 6 frames:
`(dim Mot(H/X), H/X rigid, dim W_i, λ_i = 0)` takes exactly two values —
`(6, True, 0, False) : 11` and `(7, False, 1, True) : 1`. Both
`λ_i = 0 ⟺ dim W_i = 1` (a re-check of (OC-1)) and the implication
`H/X rigid ⟹ λ_i ≠ 0` are **asserted per end**, not observed as rates; the one
`(7, False, 1, True)` end is a naturally-occurring instance that the condition
must and does reject, and `--control` adds three **constructed** ones.

---

### Step O15 — (OC-19): the reduction, and the input that is not (OUT)'s to pay

> **(OC-19)** *(proven-informally, conditional on the two named inputs)* Fix a
> class (shape, split, length-4 companion) and write `X` for the pencil chart
> of `G′`. Suppose
>
> **(a)** `Z ≠ ∅` — the chart carries some hard-stratum target-rank point;
> **(b)** `X` is irreducible (§(K-ann) (ANH-9)(ii); §(K-slide) *Step 1(e)*'s
>   *"a tower of affine-linear fibers: free hub points, normals in
>   hub-dependent linear subspaces, interiors in panels / meet lines / free
>   space"*, already consumed by §(K-dom) (D4));
> **(c)** **some** chart point — anywhere on `X`, with **no** rank-stratum
>   condition attached to it — has `H/X` infinitesimally rigid (or `H/Y`, for
>   the `c` end).
>
> Then **(OC-8) holds at that (shape, split)**: `Z` contains a point with
> `L_b ⊄ R₁` (resp. `L_c ⊄ R₄`).
>
> *Proof.* By (OC-17) and (a), `Z` is a nonempty open of `X`; by (OC-18) and
> (c), `{H/X inf. rigid}` is a nonempty open of `X`. By (b) both are dense, so
> they meet; at a common point (OC-18) gives `L_b ⊄ R₁` and membership of `Z`
> gives the stratum. ∎
>
> **Corollary (one-point decidability).** (c) is decided by **one exact rank
> computation at one rational chart point** — the `λ`-side analogue of §(K-ann)
> **(ANH-9)(iii)**, and of §(K-grid) (GR-7)'s remark (i) on the `τ` side.

**The re-attribution, which is the strategically useful half.** Input (a) is
**not (OUT)'s**. §(K-tight) *Step 2* item 3 records that `dim R_a = 0` means
*"failure at every placement"* on routes A and B alike, so a (shape, split)
with `Z = ∅` has already lost the KT-route escape before (OUT) is consulted;
(a) is a hypothesis of the **whole (K-tight) criterion**, shared by every route
on the (K-wit) row. Input (b) is a standing, thrice-consumed fact of the arc.
So the *incremental* content of (OC-8) at a (shape, split) is exactly (c) —
and (c) has no `λ`, no `V_bc`, no `L_b`, no `C₀`, no `x₁`-pencil and no
stratum in it.

**Two things this immediately buys, both about existing landed work.**

*(i)* **§(K-frame) (FR-6)'s stratum filter is unnecessary for (OC-8).** (FR-6)
reports *"4 of 8 colourings land on `(rank, dim R_a) = (54, 1)` — target rank,
hard stratum"* and treats exactly those four as (OC-8) witnesses. Under
(OC-19) **any** of the 8 that carries the open condition is a witness, because
the point need not lie in `Z`. (Unchanged, and still riding: a grid point is a
chart point of `G′` only modulo §(K-frame) **(FR-4)**'s named gap, the (GR-5)
restatement at `G′`. (OC-19) removes the *stratum* requirement from a grid
witness; it does not touch that gap.) Whether the other four in fact carry it is not
measured here — the (FR-6) follow-on battery is out of this pass's scope — but
the *requirement* is gone, and with it the (FR-7) foothold of §(K-frame) *What
would change this* item (iii) (*"certify generic `dim R_a = 1` along that
irreducible family — the first named irreducible subvariety inside the
hard-stratum locus"*), which (OC-17) makes **unnecessary rather than open**.

*(ii)* **The pointwise pools keep exactly the standing they had.** POOL-G's 46
frames and POOL-S's 270 frames were already *in* `Z` with `λ₁ ≠ 0`, so they
were already per-shape witnesses of (OC-8) at their (shape, split); nothing
about their reading changes, and §(K-out)'s *Verdict* sentence — *"what (OUT)
as a route needs is uniform availability"* — stands verbatim. (OC-19) widens
what a **recipe** may use, not what the samples proved.

**The adversarial control, and why the argument cannot be shortened.** `Z ≠ ∅`
alone does **not** give (OC-8): `--control` rebuilds (OC-14)'s hub slide onto
`C₀` at θ(3,4,5) and lands, at seeds 200/201/202, three exact chart points that
are **in `Z`** (`(rank, dim R_a) = (54, 1)`), `star_generic`-accepted, carrying
**no** coincident hinge at `b`, and with `L_b ⊆ R₁` — at which `H/X` is
**flexible** (`dim Mot = 7`), so (OC-18)'s open condition correctly rejects
them. `Z` genuinely meets the bad divisor; the reduction must run through
openness **plus** irreducibility **plus** a witness, and no two of the three
suffice.

---

### Step O16 — (OC-20)/(OC-21): the perp form of the shape-level bad case, and the disappearance of `x₁`

> **(OC-20)** *(proven-informally; asserted per end and at 200 synthetic
> spans)* `β_h = Λ²Π̂(h)` is a **maximal** totally `B`-isotropic 3-space of
> `Λ²K⁴`, so `β_h^{⊥_B} = β_h`, and therefore for **any** subspace `T`
>
> `dim(T ∩ β_h) = dim T + 3 − 6 + dim(T^{⊥_B} ∩ β_h)`.
>
> At `dim T_u = 4` ((OC-13)) this is `dim(T_u ∩ β_h) = 1 + dim(T_u^{⊥_B} ∩ β_h)`,
> so **(OC-13)'s shape-level bad case is exactly**
>
> `L_b ⊆ R₁ for every pt(b) of Π(b)` ⟺ `T_u^{⊥_B} ∩ β_b ≠ 0`,
>
> a 2-dimensional space of wrenches meeting a 3-dimensional space of panel
> lines. Separately, `dim R₁ = 5` makes `R₁^{⊥_B} = ⟨ρ⟩` one wrench; then
> `dim(R₁ ∩ β_h) = 3 ⟺ ρ ∈ β_h`, and where the meet is 2-dimensional
> (OC-11)'s marked point `p` is the point of `Π(h)` **cut out by the
> functional `B(ρ, ·)|_{β_h}`**.
>
> **Trap, recorded because the pass walked into it.** `ρ` is *not* in general
> decomposable: `B(ρ, ρ) ≠ 0` at **4 of 4** degree-3 POOL-OC ends. So the
> tempting reading *"`p = ρ ∩ Π(h)`, the point where the annihilator line
> pierces the panel"* holds **only** on the non-generic locus `{B(ρ,ρ) = 0}`;
> the functional form above is the correct one everywhere.
>
> *Proof.* `dim(A ∩ B) = dim A + dim B − dim(A + B)` and
> `dim(A + B) = 6 − dim(A^{⊥_B} ∩ B^{⊥_B})` for the nondegenerate `B`; put
> `B := β_h` and use `β_h^{⊥_B} = β_h` (a maximal totally isotropic subspace of
> a nondegenerate 6-dimensional form is self-perpendicular; `β_h` is
> 3-dimensional and totally isotropic — both asserted per end by
> `outerwide.panel_line_space`). For `ρ`: `R₁` is a hyperplane, so `R₁^{⊥_B}`
> is a line; `R₁ ∩ β_h = β_h ∩ ρ^{⊥_B}` is the kernel of the functional
> `B(ρ, ·)` restricted to `β_h`, of dimension 2 unless that functional is zero,
> i.e. unless `ρ ∈ β_h^{⊥_B} = β_h`. A 2-dimensional subspace of `β_h` is the
> pencil of exactly one point of `Π(h)` ((OC-11)). ∎
>
> *A reading, marked as one (the algebra above is what the driver tests).* A
> wrench pairs to zero with a relative twist exactly when the corresponding
> single bar is redundant, so `T_u^{⊥_B}` is the **2-dimensional space of
> wrenches `(H/X) − b` transmits from `u` to `v*`**, and the shape-level bad
> case says one of them is a **pure force along a line of `b`'s own panel**.

> **(OC-21)** *(proven-informally; asserted per degree-3 end)* At a degree-3
> hub `b` (so `deg_H(b) = 2` with other `H`-neighbour `u`) at which
> `pt(b), pt(u), pt(a)` are **not collinear** — the bracket `[a,u,b] ≠ 0`,
> (OC-16)'s first factor, a coincident hinge pair at `b` that
> `repin.star_generic` rejects:
>
> `L_b = ⟨C(b,u), C(b,a)⟩` and `C(b,u) ∈ R₁` ((OC-12)), hence
> **`L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁`**.
>
> The condition is about the **split-edge** hinge line `C(b,a)` alone: `x₁`,
> whose pencil direction was the whole subject of (OC-3), has **left the
> statement**. (This is what (OC-16)'s `Δ = det₆[…, C(b,a)]` was already
> computing on the `ℓ_min = 5` stratum; (OC-21) is the same fact with no
> stratum hypothesis.)
>
> **The slide dichotomy, sharpened.** `T_u`, `β_b` and hence `C₀` do not see
> `pt(b)` ((OC-13)), so along any chart move of `pt(b)` inside `Π(b)`, `C₀` is
> fixed. Therefore, with (OC-19):
>
> - **`b` has no hub `G′`-neighbour** (`pt(b)` free in `Π(b)`, 2 dimensions;
>   **1715 of 5226** POOL-CW pairs at the `b` end): (OC-8)'s `b`-end disjunct
>   holds **iff** `T_u^{⊥_B} ∩ β_b = 0` at some chart point — a line cannot
>   contain a plane, so `pt(b) ∈ C₀` cannot hold identically.
> - **`b` has exactly one hub `G′`-neighbour `h`** (`pt(b)` confined to the
>   line `N = Π(b) ∩ Π(h)`, 1 dimension): the same, with the extra clause
>   `N ≠ C₀`. *(Proven-informally on the same chart-legality reading (OC-13)
>   uses for its own slide; **not driver-tested here**, and its census share is
>   **not measured** — the recorded numbers give only `deg_G(b) = 3` at 3081
>   and hub-neighbour-free-at-`b` at 3227, whose overlap is the 1715 above.)*
> - **`b` has two hub `G′`-neighbours** (`hcard` caps it there): `pt(b)` is
>   pinned and the slide is unavailable; (OC-19) still applies, via any other
>   chart move or via (OC-18).

---

### Step O17 — (OC-22): the residue's object class, and the exact reach of the grid form

> **(OC-22)** *(assessment; no driver)* After (OC-19), the incremental content
> of (OC-8) at a (shape, split) is
>
> *the welded far framework `H/X` is infinitesimally rigid at **one** pencil
> chart point*,
>
> which is the **same kind of statement** as §(K-ann) **(ANH-R1)** (*`H/P − β`
> is infinitesimally rigid at the pencil placement*), on the same contraction
> tower: `H/P = (H/X)/(b ∼ v*)`, so `H/X` rigid at a point implies `H/P` rigid
> there (welding two bodies of a rigid framework preserves rigidity). Both are
> **rank lower bounds on a smaller welded far graph at a pencil placement**;
> both are one-point decidable ((ANH-9)(iii) and (OC-19)); both are consumed by
> §(K-frame) **(FR-1)** with the chart's own irreducibility. The arc had
> recorded three arrivals at the *same missing technology*; this is the first
> arrival at the **same kind of object**, so §(K-frame)'s (FR-4) transport
> recipe applies to the (OC-8) side **verbatim** rather than by analogy.

**The grid form, and exactly how far it reaches — a derivation, deliberately
not a battery.** At a σ-fixed grid point of `G′` — a chart point modulo
§(K-frame) **(FR-4)**'s named (GR-5)-at-`G′` gap, untouched here — §(K-frame)
(FR-3)(iii) makes span-membership in a set of hinge lines combinatorial, and (OC-15) gives
`R₁ ⊆ span{C_e : e ∈ π}` **pointwise** for every `b`-to-`v*` path `π` of
`K = (H/X) − e₁`. Hence a purely combinatorial **sufficient** criterion:

> `C(b,a) ∉ span{C_e : e ∈ π}` for some path `π` ⟹ `C(b,a) ∉ R₁` ⟹
> `L_b ⊄ R₁`, and at a grid point that is: `π` contributes **≤ 2 distinct
> colouring components** in `C(b,a)`'s family, and `C(b,a)`'s component is not
> one of them.

**Its reach is bounded by alternation, and that is the combinatorial
explanation of the `ℓ_min = 5` boundary.** `closure.alternation_classes` (the
admissibility constraint §(K-clos) (AC-2) and §(K-frame) (FR-4) use) forces the
two edges at a **`G′`-degree-2 body** into opposite families. A path all of
whose interior bodies have `G′`-degree 2 therefore alternates strictly, giving
`⌈ℓ/2⌉` and `⌊ℓ/2⌋` maximal same-family runs; unless two runs of one family
land in the *same* colouring component, the span has dimension
`min(3, ⌈ℓ/2⌉) + min(3, ⌊ℓ/2⌋)` — which is **5 at `ℓ = 5`** (matching (FR-6)'s
measured *"the alternating chain always splits 3–2 with distinct lines"*) and
**6, i.e. vacuous, from `ℓ = 6` on** (matching (OC-15)'s measured
`(2, 6, False) : 38`, `(3, 6, False) : 70`). So the bracket route's `8 of 5226`
reach is not an accident of the `ℓ_min = 5` stratum: it is what strict
alternation forces. **What a general-`ℓ` grid certificate must supply, named
exactly:** a path carrying **interior hubs with two same-family consecutive
edges** (an immediate component merge, and by §(K-clos) (AC-9) a σ-fixed hub of
degree ≥ 3 always has such a pair somewhere), or a global colouring in which
two runs of one family share a component. This is *What would change this
(Steps O9–O12)* item 3 (the block decomposition of `R₁`) restated on the grid
side; it is **not** attempted here, and it is **not** §(K-frame) *What would
change this* item (ii)'s battery, which this pass leaves alone.

---

### Step O18 — where this leaves (OC-8) (hand-off)

**Status, unchanged: (OC-8) is OPEN, class uniformity is untouched, and no
gap-map status moves.** The (K-wit) row's (OUT) caveat gains one clause and
loses none.

What a successor should pick up, in descending value:

1. **Input (c) of (OC-19), class-uniformly** — *`H/X` infinitesimally rigid at
   one pencil chart point, at every class (shape, split, length-4 companion)*.
   This is the whole residue. It is **one-point decidable per triple**, so a
   census is a set of per-triple proofs, and the missing piece is a **recipe**.
   The two recipes the arc owns are §(K-frame) (FR-4)'s pattern colouring
   (which transports a *combinatorial* criterion to an exact chart point) and
   §(K-ann) (ANH-9)(iii)'s one-point discharge. Because (OC-22) puts input (c)
   in (ANH-R1)'s object class, **(FR-4) applies to it verbatim** — the open
   question is whether a pattern colouring exists making `H/X` rigid at the
   grid point, which is a **rank** condition and therefore *not* as cheap as
   (FR-R1) was. Say so plainly: this is (GR-15)-flavoured, not (FR-R1)-flavoured.
2. **Input (a), `Z ≠ ∅`, as a statement in its own right.** It is a
   prerequisite of the *whole* (K-tight) criterion and it is currently carried
   implicitly by every route on the (K-wit) row. It is measured at 90/90
   POOL-S splits, and the only recorded `dim R_a = 0` chart points anywhere in
   the arc are §(K-flank) *F5(d)*'s five `P21` seeds. Making it explicit —
   *at every class (shape, split), the chart carries a target-rank point with
   `s₀ = 0`* — is cheap to state and would clean up several rows at once.
3. **`T_u^{⊥_B} ∩ β_b = 0`** ((OC-20)) at the **1715** slide-legal `b` ends,
   where (OC-21) makes it an **iff**. This is *What would change this (Steps
   O9–O12)* item 1 promoted from a hunt to the exact residue at those ends;
   still measured `dim(T_u ∩ β_b) = 1` at 38/38 POOL-W degree-3 ends and 4/4
   POOL-OC ones, i.e. `T_u^{⊥_B} ∩ β_b = 0` at 4/4.
4. **The one-hub-neighbour extension of the slide** ((OC-21)'s second bullet)
   and its census share — a cheap `--wide`-style leg, not run here.
5. **Deliberately not attempted, again**, and recorded so a successor does not
   assume otherwise: §(K-out) *What would change this* item 4 (pushing a
   constructed point to `p⁺`), item 5's coupled two-end slide, and every
   §(K-frame) *What would change this* item (ii)–(iv).

---

### Verification (Steps O13–O18)

`notes/scripts/w4/ocon.py` (new, untracked at draft time; exact ℚ, stdlib only;
a `w4/` leaf **above** `outerwide`, which it imports read-only — `panel_line_space`,
`far_twist_space`, `hub_free_end`, `collinear`, `klein_point_on`,
`pencil_centre`, `slide_targets`, `slide_placement`, `check_slid`, `wrench_row`
— together with `outerline` (`frame_at`, `weld_motions`, `rel_span`,
`line_pencil`); everything else is a catalogued §1 primitive. **Nothing existing
is modified**: `outerline.py`, `outerwide.py`, `outer.py`, `repin.py`,
`pitch.py`, `lambda.py`, `widened.py` are all read.) From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --validate   # (OC-20)'s algebra, POOL-OV
PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --check      # (OC-17),(OC-18),(OC-20),(OC-21), POOL-OC
PYTHONHASHSEED=0 python3 notes/scripts/w4/ocon.py --control    # (OC-17)/(OC-19)'s controls, POOL-OZ
```

Times as run: `--validate` **0.3 s**, `--check` **17 s**, `--control` **4 s** —
21 s in total, a derivation pass's budget. All three re-run **byte-identical**
under two different `PYTHONHASHSEED` values (`0` and `12345`), the
*figures-do-not-move* gate (`notes/scripts/README.md`), which this pass
discharges by the check itself: it **added** one driver and modified none
(`git status --porcelain notes/scripts/` shows exactly the one new file).

**Pools, pinned; every figure above is quoted over exactly one of them, and
none is aggregated with POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A /
POOL-W / POOL-SL.**

- **POOL-OV** (`--validate`) — synthetic exact-ℚ subspaces of `K⁶` from
  `random.Random(20260819)` (seed printed), plus **two constructed witnesses**.
  No graph, no placement.
- **POOL-OC** (`--check`) — the 4 `lambda.habitat_specs` habitats × placement
  seeds **200–201**, accepted exactly as `outerline.frame_at` accepts them.
  **6 frames, 12 companion ends, 4 of them degree-3.** Deliberately tiny: this
  is a derivation pass and every sentence under test is an **identity**, so the
  pool is a witness set, not a sample — **no figure here is a rate**.
- **POOL-OZ** (`--control`) — θ(3,4,5) × placement seeds **200–214**,
  **unfiltered** (15 placements), plus **3 constructed** chart points from the
  (OC-14) hub slide onto `C₀` rebuilt here.

Per mode, what is asserted:

- `--validate`: `β = Λ²` of a 3-space is 3-dimensional, totally `B`-isotropic
  and `β^{⊥_B} = β`; the (OC-20) identity
  `dim(A ∩ β) = dim A + 3 − 6 + dim(A^{⊥_B} ∩ β)` at **200** random spans of
  every dimension 1–5, with the `(dim A, dim(A ∩ β))` histogram printed; the
  **constructed** bad case (a 4-space `T ⊆ C^{⊥_B}` for a panel line `C ∈ β`)
  has `T^{⊥_B} ∩ β ≠ 0` and `dim(T ∩ β) = 2`; and the **negative control** —
  60 random 4-spaces with `T^{⊥_B} ∩ β = 0`, every one with `dim(T ∩ β) = 1`
  (README §4 convention 6).
- `--check`: per frame, `index(G) = 0`, `def(G′) = 0`, `def(G − v) = 4`,
  `corank(G′) = index(G) + 1 + def(G′) = 1`, **(†) `dim R_a = corank(G′) − s₀`**
  against `outer.stratum_at`'s independently-computed `dim R_a`, and both
  maximal-rank readings (`rank R(G′) = tgt`, `rank R(G − v) = 5|E(G − v)|`);
  ledger `(index, def(G′), corank(G′), s₀, dim R_a) = (0,0,1,0,1)` at **6 of 6**.
  Per companion end (12 of 12): (OC-1)'s `λ_i = 0 ⟺ dim W_i = 1`, and
  **(OC-18)**'s `H/X` rigid ⟹ `λ_i ≠ 0`, both as per-end asserts; histogram
  `(6, True, 0, False) : 11`, `(7, False, 1, True) : 1`. Per degree-3 end (4 of
  4): `dim T_u = 4`, `dim T_u^{⊥_B} = 2`, **(OC-20)**'s
  `dim(T_u ∩ β) = 1 + dim(T_u^{⊥_B} ∩ β)`, (OC-13)'s
  `dim(R₁ ∩ β) = 1 + dim(T_u ∩ β)`, `dim R₁^{⊥_B} = 1`,
  `dim(R₁ ∩ β) = 3 ⟺ ρ ∈ β`, the marked point `p` agreeing with `ρ`'s panel
  trace (and with `outerwide.pencil_centre`), `p = pt(h) ⟺ L_h ⊆ R₁`, and
  **(OC-21)**'s `L_h ⊆ R₁ ⟺ C(h,a) ∈ R₁` with `[a,u,h] ≠ 0` asserted.
  Histogram `(dim(R∩β), dim(T∩β), dim(T^{⊥_B}∩β), L_h ⊆ R, non-collinear,
  ρ B-isotropic, hub-free) = (2, 1, 0, False, True, **False**, True) : 4` — the
  `False` in the sixth slot is the (OC-20) trap, measured.
- `--control`: at all 15 unfiltered placements, (†) is asserted wherever the
  placement reaches target rank, together with `dim R_a = 1 ⟺ s₀ = 0` there;
  the histogram is printed and the boundary is stated as one (**no sampled
  placement of this window falls off `Z`** — which is what a dense open `Z`
  predicts, and which means the *off-`Z`* side of the control is **not**
  exercised by sampling). The **constructed** half is the one that bites: the
  (OC-14) slide onto `C₀` lands at seeds 200/201/202 at points that
  `outerwide.check_slid` accepts — so target rank, `dim R_a = 1`,
  `dim V_bc = 3`, `rank{C_i} = 4`, `pt(a)` on `M`, star-span green — with
  `L_b ⊆ R₁` and **no** coincident hinge at `b`, `star_generic` accepting, and
  `dim Mot(H/X) = 7` (**not** rigid), all asserted. That is (OC-18)'s
  adversarial witness and (OC-19)'s "`Z ≠ ∅` is not enough" control in one
  object.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean
(`DESIGN.md` *Formalize everything the argument uses*).

---

### Confidence verdict (Steps O13–O18)

| | claim | standing |
|---|---|---|
| **(OC-17)** | `dim R_a = corank(G′) − s₀` at every legal chart point; hence, at `index(G) = 0`, `def(G′) = 0`, `Z` is an intersection of two maximal-rank loci and so **Zariski open**; its irreducibility is the chart's | **proven-informally** (rank–nullity on the stress space, plus the landed count identity `corank(G′) = index(G) + 1 + def(G′)`); the identity and both maximal-rank readings **asserted per frame** at 6/6 POOL-OC frames and at every target-rank POOL-OZ placement |
| **(OC-18)** | `H/X` infinitesimally rigid at a chart point ⟹ `λ₁ ≠ 0` ⟹ `L_b ⊄ R₁`; the condition is maximal-rank hence open, ambient-nonempty by (OC-10)(e); **no degree hypothesis** — both ends of 5226/5226 pairs | **proven-informally** (two lines on top of (OC-1)); the implication **asserted per end** at 12/12 POOL-OC ends, with one naturally-occurring rejecting instance and **three constructed** ones (`--control`) |
| **(OC-19)** | (OC-8) at a (shape, split) follows from (a) `Z ≠ ∅` + (b) chart irreducibility + (c) one chart point with `H/X` rigid; one-point decidable; (a) is the **whole (K-tight) criterion's** input, not (OUT)'s | **proven-informally — (b) proven, §(K-chart) (CH-1)** (2026-08-19, direction CIRR: the chart is irreducible, ℚ-rational, and the constant-fibre-dimension restriction (ANH-9)(ii)/(S1)(e)/(D4) each relied on costs nothing, per (CH-4)/(CH-6)/(CH-7)). **(a) and (c) are inputs, not results**: neither is established class-uniformly here |
| **(OC-20)** | `β_h^{⊥_B} = β_h` gives `dim(T ∩ β_h) = dim T − 3 + dim(T^{⊥_B} ∩ β_h)`; so (OC-13)'s shape-level bad case is `T_u^{⊥_B} ∩ β_b ≠ 0`; `R₁^{⊥_B} = ⟨ρ⟩` and `p` is `ρ`'s panel trace **as a functional** | **proven-informally**; asserted at 200 synthetic spans + a constructed bad case + 60 negative controls, and per degree-3 end at 4/4. **`ρ` is measured non-decomposable at 4/4** — the "`p = ρ ∩ Π(h)`" reading is refuted as a general one |
| **(OC-21)** | `L_b ⊆ R₁ ⟺ C(b,a) ∈ R₁` at a degree-3 hub off `{[a,u,b] = 0}` — `x₁` leaves the statement; and the slide dichotomy makes availability **iff** `T_u^{⊥_B} ∩ β_b = 0` at the 1715 slide-legal `b` ends | equivalence **proven-informally**, asserted per degree-3 end at 4/4; the hub-free dichotomy **proven-informally** on (OC-13)'s own legality reading; the **one-hub-neighbour extension is proven-informally and NOT driver-tested**, its census share **not measured** |
| **(OC-22)** | (OC-8)'s residue is in §(K-ann) (ANH-R1)'s object class (same contraction tower, both one-point decidable), so (FR-4)'s transport applies verbatim; and strict alternation is why the grid/bracket form stops at `ℓ_min = 5` | **assessment** (argument, no driver). The alternation half is a derivation from `closure.alternation_classes`'s landed constraint and reproduces (FR-6)'s and (OC-15)'s measured 3–2 / `(·, 6, False)` figures |
| **(OC-8)** | the residue | **OPEN** — reshaped, not closed; class uniformity untouched |

**No gap-map status moves. Class uniformity of (OUT), and of `hK`, is exactly
where it was.** What moves is the *content* of two rows: §(K-out)'s (which gains
(OC-17)–(OC-22)) and **(K-wit)**'s (OUT) caveat, which gains the sentence that
the genericity argument (OC-3) demands needs **no hard-stratum qualifier**.

### What would change this (Steps O13–O18)

1. **A class shape with `Z = ∅` at a length-4-companion-bearing split** would
   make (OC-8) **false** there — and would simultaneously kill routes A and B
   at that split by §(K-tight) *Step 2* item 3, so it is a (K-tight) event, not
   an (OUT) event. Nothing in the arc exhibits one; §(K-flank) *F5(d)*'s `P21`
   seeds are the only recorded `dim R_a = 0` chart points and `P21` carries no
   length-4 companion. **The cheap probe:** extend `--control`'s unfiltered leg
   to a POOL-S-style shape pool and report the `s₀` histogram per (shape,
   split) rather than per seed.
2. **A failure of chart irreducibility** ((OC-19) input (b)) would break this
   pass, §(K-slide) (S1)(e), §(K-dom) (D4) and §(K-ann) (ANH-9)(ii) at once. It
   is the arc's most-consumed un-driver-tested fact; a pass that *writes it
   down* — the tower of affine-linear fibres, with the constant-fibre-dimension
   clause made explicit — would be cheap insurance for four sections.
   **Cross-direction convergence (2026-08-19, sixth fan-out):** FRES landed
   the *other* half of this same fact independently, the same day, without
   either direction seeing the other's — its (ANH-9)(ii) correction records
   that "irreducible rational parametrization" is literally true only on
   `place_pencil_general`'s **constant-fibre-dimension locus**, not
   unconditionally. Consumers (this pass included) are undisturbed because
   every one needs only irreducibility, which the constant-fibre-dimension
   restriction still supplies — but the fact itself is now **load-bearing for
   at least two independent routes and owned by nobody**: written down once,
   not four times.
3. **A class (shape, split) at which `H/X` is infinitesimally rigid at NO chart
   point.** By (OC-19) that is exactly the failure of (OUT)'s first disjunct
   there, and by (OC-10)(e) it would be a chart-vs-ambient separation at a
   *rigidity* statement — the sharpest possible negative on this side, and a
   genuine kill for that shape's first disjunct (the `c` end would still have
   to be checked). Not seen: `H/X` rigid at 11 of 12 POOL-OC ends, the twelfth
   being a `λ = 0` end.
4. **A `deg_H(b) ≥ 3` formula for the marked direction** — §(K-out) *What would
   change this (Steps O9–O12)* item 2 in its original shape. (OC-18) makes it
   unnecessary for (OC-8), but (OC-11)–(OC-13)'s *geometry* (which point `p`,
   which line `C₀`) is still confined to degree-3 ends, and the (OC-21)
   dichotomy with it.
5. **The (OC-22) grid criterion, run** — a pattern-colouring existence question
   for `H/X` rigidity at a σ-fixed grid point. **This one carries a rank
   condition** and is therefore (GR-15)-flavoured rather than (FR-R1)-flavoured;
   it is named here as the successor, not commissioned, and it overlaps
   §(K-frame) *What would change this* item (ii), which this pass leaves alone.
6. **The `X°` refinement of (OC-19), if a converse is ever wanted.** (OC-19)'s
   direction is sufficient only. On the dense open `X° ⊆ X` where
   `rank M_K` and `rank[M_K; P]` are both maximal, `{L_b ⊆ R₁}` is *closed*, so
   (OC-8) there is **iff** one point of `X°` has `L_b ⊄ R₁`; nothing in this
   pass needs the converse and it is stated only so a successor does not
   re-derive it.

### Steps O19–O24 (2026-08-19, seventh fan-out, direction ZNEQ) — (OC-19) input **(a)** written down as a statement in its own right, and it **factors**: `s₀ = 0` is *independence of the far framework `H`* alone ((OC-23)), which is a **necessary condition for `hK` at the shape** ((OC-24)) and is **dominated by §(K-grid) (GR-10)** — one grid point per shape covering **every** split at once ((OC-28)); the target-rank half is the (K-tight) criterion **one split down** ((OC-25)), whose failure is a **codimension-2 Schubert jump** of the far framework's relative twist space ((OC-26), whose first closed form this pass **refutes by construction** and replaces); measured with an exact-ℚ **witness at 138/138** (shape, split) pairs ((OC-27)). **Input (a) is OPEN as a class-uniform statement and is NOT an independent gap; no gap-map status moves.** (Written before §(K-chart) landed; CIRR's **(CH-1)**/**(CH-2)** then *proved* this pass's one structural input and its ℚ-descent step — see *Step O24*'s convergence note.)

Driver `notes/scripts/w4/zneq.py` (new this pass; imports `ocon`, `outerline`,
`outer`, `flanks`, `kslidecomb`, `widened`, `repin` **read-only** and modifies
nothing); labels **(OC-23)–(OC-28)**, Steps **O19–O24**. Everything cited that
this pass did not mint is qualified per `notes/Pencil-labels.md` clause L3:
**(OUT)**, **(Λ0a)–(Λ0i)** are §(K-Λ)'s; **(FR-4)**/**(FR-6)**/**(FR-7)** are
§(K-frame)'s; **(ANH-9)**/**(ANH-R1)** are §(K-ann)'s; **(S1)** is §(K-slide)'s;
**(D4)** is §(K-dom)'s; **(CH-1)**/**(CH-2)**/**(CH-5)** are §(K-chart)'s
(direction CIRR, landed **the same day and after this pass's mathematics was
written** — see the convergence note in *Step O24*); **(GR-5)**/**(GR-9)**/**(GR-10)** are §(K-grid)'s;
**(AC-3)**/**(AC-7)** are §(K-clos)'s; **(PC-OBS)** is §(K-pure)'s; *F5(d)* is
§(K-flank)'s; **(K-tight)** *Step 2*'s items are §(K-tight)'s. POOL-C / POOL-G /
POOL-S / POOL-B / POOL-CW / POOL-A / POOL-W / POOL-SL / POOL-OV / POOL-OC /
POOL-OZ are earlier pools of this section and **nothing below is aggregated with
them**; POOL-G and POOL-S are pinned and are neither re-sampled nor extended.

Standing notation is §(K-out)'s, plus: `orient`'s split frame is the chain
`b — v — a — c` with `v`, `a` interior (degree 2) and `b`, `c` hubs
(`widened.orient`); `G′ = G − v + ab`; `H = G − v − a` (§(K-out)'s `H`);
`σ := corank R(H)` at a chart point; `Z` = the hard-stratum target-rank locus of
the pencil chart of `G′`; `M = Π(b) ∩ Π(c)` the panels' meet line, with `M̂ ⊆ K⁴`
its 2-dimensional cone and `t` an affine parameter on it;
`D := {m(b) − m(c) : m ∈ Mot(H)}` the relative twist space of `H`;
`U_H := D^⊥ = {u : ⟨u, m(b) − m(c)⟩ = 0 ∀ m ∈ Mot(H)}` — §(K-tight) *Step 2*'s
obstruction space `U` at the substituted instance `(G′, a)`.

Six things, in the order they change the reading of input (a).

- **(OC-23) — the pendant-edge reduction: `s₀ = corank R(H)` at *every* chart
  point.** `E(G − v) = E(H) ∪ {ac}` and `a` has degree **one** in `G − v`, so the
  five `ac` rows, restricted to the `a` block, span `C(ac)^⊥` (5-dimensional
  whenever `pt(a) ≠ pt(c)`, which `IsNondegPencilRealization` conjunct 2
  supplies) and every `G − v` stress vanishes on them. Hence the `s₀` half of
  input (a) contains **no `v`, no `a`, no split edge, no `λ`, no `V_bc`, no
  stratum**: it is *independence of the far framework `H`*, the same object
  §(K-out) has been about since *Step O1*. This is (OC-17)'s own one-line
  argument, run on a pendant edge instead of on the `ab` rows.
- **(OC-24) — the dichotomy, and the sharp corollary the dispatch did not
  anticipate.** With the chart irreducible — **§(K-chart) (CH-1)(a)**, landed by
  CIRR the same day, and unconditional at `Γ = G′` — `Z ≠ ∅`
  ⟺ `{target rank} ≠ ∅` **and** `{σ = 0} ≠ ∅` on the chart, each open, each
  one-point decidable. And **`{σ = 0} = ∅` on the chart implies `hK` is FALSE at
  that shape**: `H ⊆ G`, so a self-stress of `H` at every chart point is a
  self-stress of `G` at every pencil realization, and `G` is tight with
  `def(G) = 0`, so `G` never attains `6(|V| − 1) = 5|E(G)|`. **So the `s₀` half
  of input (a) is a *necessary condition* for the phase's own target** — it
  cannot fail at a class shape without disproving the pencil conjecture there.
  That **refines the dispatch's decisive-negative wording**: a `Z = ∅` shape via
  the `s₀` half is a **PENCIL event** (a disproof at that shape, §(K-flank)
  direction-A pivot class), strictly stronger than the (K-tight) event; a
  `Z = ∅` shape via the target-rank half is the **(K-tight) event** the dispatch
  named, and only that branch.
- **(OC-25) — input (a) is an instance of the (K-tight) criterion, one split
  down the chain.** §(K-tight) *Step 2* item 1 at the substituted instance
  `(G, v, a, b) ↦ (G′, a, b, c)` gives, at every chart point with
  `pt(a) ∉ {pt(b), pt(c)}`,

  > `corank R(G′) = σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)`,  `dim D = 3 + σ`,
  > `dim U_H = 3 − σ`,

  so a chart point lies in `Z` **iff** `σ = 0` **and** the two placement
  functionals `⟨·, C(ab)⟩`, `⟨·, C(ac)⟩` are linearly independent on the
  3-space `U_H` — *Step 2* item 1's own attainment criterion. The prerequisite of
  the criterion **is** the criterion, one split down; and the regress
  **terminates in exactly one step**, because `orient`'s chain has exactly two
  interior vertices and `G′ − a = H`. Consequence: every §(K-tight) tool applies
  to input (a) verbatim — and the P21 `s₀`-jump seeds are its `dim U = 1`
  analogue one level up (measured: `dim U_H = 2`, `dim D = 4` there).
- **(OC-26) — the `pt(a)`-fibre over `M`, and the closed form of failure.**
  `pt(a)` is confined to `M` (its two `G′`-neighbours are the hubs `b`, `c`), and
  `C(ab)`, `C(ac)` are **affine-linear in `t`** along `M`. At `σ = 0` the
  functional matrix is `2 × 3`, so its **three** `2 × 2` minors are quadratics in
  `t` and the bad set is their **common** zero locus — three conditions on one
  parameter, hence **generically empty**, and when empty the *whole* `pt(a)`-fibre
  over that `H`-part lies in `Z`. Bad at **every** `t` has an exact closed form —
  and it is a **disjunction**, not the single containment the first derivation
  gave (that reading is **refuted by construction** below, POOL-ZQ Case C):

  > bad at every `t` ⟺ `dim(D ∩ (M̂ ∧ W)) ≥ 3` **or** `M̂ ∧ w ⊆ D` for some
  > `w ∈ W`,  where `W = ⟨pt(b)^, pt(c)^⟩`.

  Both disjuncts force `dim(D ∩ (M̂ ∧ W)) ≥ 2` — a **codimension-2** Schubert
  jump in `Gr(3, 6)` off the generic value 1. Measured (POOL-ZF): `ℚ[t]`-GCD of
  the three minors of degree **0 at 32 of 32** `σ = 0` frames (*no* bad `t` in
  **any** extension of ℚ, so the entire meet line is good), with
  `dim(D ∩ (M̂ ∧ W)) = 1` and no pencil inside `D` at all 32 — and the closed
  form asserted **against** the GCD test per frame.
- **(OC-27) — the measurement the dispatch asked for, run.** POOL-ZN, the
  unfiltered leg extended to a POOL-S-*style* shape pool: **138 (shape, split)
  pairs — 90 carrying a length-4 companion plus 48 others — every one of them
  carrying an exact-ℚ *certified* chart point of `Z`**, and the first
  guard-accepted draw sufficed at every one. `Z ≠ ∅` is therefore **proven
  individually** at each of the 138: one point suffices, so neither openness nor
  irreducibility is consumed. **No miss, hence no candidate (K-tight) event and
  no candidate PENCIL event in scope.**
- **(OC-28) — the `s₀` half is *dominated* by §(K-grid) (GR-10), one grid point
  per shape covering every split.** `H` omits **both** `v` and `a`, and the
  `G`-chart and the `G′`-chart impose *identical* constraints on the `H`-data
  (hub points free, hub normals constrained only by their `H`-neighbours,
  `H`-interiors in their hub-neighbours' panels), so their `H`-projections have
  the same image and an `H`-part extends to a `G′`-chart point by re-placing
  `pt(a)` anywhere on `M` off a proper closed subset. That extension is
  **performed as a construction**, guards and all: at **30 of 30** (shape,
  split) pairs a target-rank chart point of the whole graph `G` transfers to a
  guard-accepted `G′`-chart point which is **in `Z`** (POOL-ZT). **No rank claim
  crosses, so §(K-frame) (FR-4)'s gap is *not* invoked**. At a configuration
  where `G`
  attains the Tay target, `corank R(G) = 0`, hence `σ = 0` — and that is exactly
  what §(K-grid) **(GR-9)** *proves* wherever its both-block tree-triple
  colouring exists, which **(GR-10)** measures at **907/907** shapes of
  §(K-grid)'s pool. So: **(GR-10) ⟹ the `s₀` half of input (a) at every tight
  class shape and every eligible split**, from *one* grid point per shape. The
  converse boundary is exhibited, not assumed: at `P21` — a (K-res) shape that
  **fails `hnoRigid`** — the arc's five recorded `dim R_a = 0` seeds have
  `s₀ = σ = 1`, so `{σ = 0}` is a **proper** open — and its complement there is
  the **sampler's coincidence locus**, not a thick subset of the variety
  ((OC-38)(iv); the earlier "not thin in the sampler's rational range" reading
  is refuted, the *proper-open* claim itself unaffected). The class predicate's
  `hnoRigid` conjunct remains the arc's tool against it, and **(OC-37)** now
  proves no such stress is combinatorially forced in the habitat.

**Verdict, stated at the strength the work supports.** **Input (a) stays OPEN as
a class-uniform statement, and no gap-map status moves.** What changes is that it
is **no longer an unowned prerequisite**: it factors into a half that is a
*necessary condition* for the phase's own target and is dominated by §(K-grid)'s
own residual, and a half that is the (K-tight) criterion one split down whose
failure has a closed form. **Class uniformity is untouched**, and the honest
boundary is that neither half is *proven* class-uniformly here: the `s₀` half
waits on (GR-10) (or on any class-uniform independence statement for `H` at
pencil placements — the hard direction of `Pencil-strategy.md` §2.3), and the
target-rank half waits on a class-uniform non-containment `M̂ ∧ w ⊄ D`.

---

### Step O19 — (OC-23): `s₀` is `corank R(H)`, at every chart point

> **(OC-23)** *(proven-informally; asserted per frame)* At **every** legal chart
> point of `G′` with `pt(a) ≠ pt(c)` — no genericity, no target-rank hypothesis —
>
> `s₀ = corank R(G − v) = corank R(H)`,  `H = G − v − a`.
>
> Hence, with (OC-17), `dim R_a = corank(G′) − corank R(H)`, and inside
> §(K-tight) *Step 2*'s scope (`index(G) = 0`, `def(G′) = 0`) the second defining
> condition of `Z` is exactly **`H` has independent rows**.

*Proof.* `orient` gives `deg_G v = 2` with neighbours `a`, `b`, `deg_G a = 2`
with neighbours `v`, `c`. So `E(G − v) = E(G) ∖ {va, vb} = E(H) ∪ {ac}` and `a`
is incident, in `G − v`, to the single edge `ac`. Let `λ` be a row dependency of
`R(G − v)`. Its `a`-block reads `Σ_{i} λ_{(ac)i} · r_i(C(ac))|_a = 0`, and the
five rows of a hinge restricted to one endpoint block span `C(ac)^⊥`, which is
5-dimensional and their images independent whenever `C(ac) ≠ 0`, i.e.
`pt(a) ≠ pt(c)`. So `λ_{(ac)i} = 0` for all `i`, and `λ` restricted to `E(H)` is
a dependency of `R(H)` — bijectively, since any `R(H)` dependency extends by
zero. ∎

*Two remarks.* *(i)* This is the **same** lemma (OC-17) proves for the `ab` rows
(*Step O13*): "five hinge rows on one block span a 5-space, so a stress cannot
touch a degree-1 body". (OC-17) uses it to peel `ab`; (OC-23) uses it to peel the
pendant `ac`. Together they say the whole `dim R_a` ledger of a class split is
carried by `H`. *(ii)* The reduction is **exact and unconditional**, so it applies
at off-`Z` points too, which is what makes *Step O24*'s P21 leg a test of it
rather than of its scope: at the five `s₀`-jump seeds `corank R(H) = 1` as well.

*Exact, per frame:* asserted at **32/32** POOL-ZF frames, at **138/138**
POOL-ZN witnesses, and at **all 35** valid POOL-ZR (P21) seeds — including the
five that reject.

---

### Step O20 — (OC-24): the dichotomy, and why the `s₀` half cannot fail without disproving `hK`

> **(OC-24)** *(proven-informally; the first clause conditional on chart
> irreducibility)* Fix a class (shape, split) and let `X` be the pencil chart of
> `G′`.
>
> **(i)** `{target rank}` and `{σ = 0}` are Zariski-open in `X` ((OC-17),
> (OC-23)), and `X` **is** irreducible (§(K-chart) **(CH-1)(a)**, unconditional
> at `Γ = G′` for a class shape and an eligible split), so
>
> `Z ≠ ∅ ⟺ {target rank} ≠ ∅ and {σ = 0} ≠ ∅`,
>
> and each is **witnessed** by **one** exact rank computation at **one** rational
> chart point — the *positive* answer is one-point certifiable, the negative is
> not (it quantifies over the chart). A single point satisfying **both** needs no
> irreducibility at all.
>
> **(ii)** *(unconditional in `X`; needs the shared-sub-tower clause of (OC-28)
> only to move between the two charts)* If `{σ = 0} = ∅` — `H` dependent at every
> chart point — then **`hK` is false at that shape**. Consequently the `s₀` half
> of input (a) is a **necessary condition** for `hK` at the shape.

*Proof.* (i) is (OC-17) plus (OC-23) plus "two dense opens of an irreducible
variety meet", exactly (OC-19)'s argument — with the irreducibility now
**proven** rather than cited (§(K-chart) (CH-1)(a)), so (OC-19)'s input (b) has
stopped being a hypothesis of this reduction as well. For (ii): `E(H) ⊆ E(G)`, so a
self-stress of `H` at a placement is a self-stress of `G` at that placement. `G`
is tight (`index(G) = 0`) with `def(G) = 0`, so its Tay target is
`6(|V(G)| − 1) = 5|E(G)|` — **full row rank**, i.e. `hK`'s conclusion at `G` is
`corank R(G) = 0`. If `H` is dependent at every point of the `H`-image of the
chart, and (OC-28)'s shared-sub-tower clause identifies that image with the
`H`-image of `G`'s own chart, then `corank R(G) ≥ 1` at every pencil realization
of `G` and the Tay target is never attained. ∎

**Why this matters more than the reduction does.** The dispatch's framing —
correct as far as it goes — is that a `Z = ∅` class shape at a
length-4-companion-bearing split is *"a (K-tight) event, not an (OUT) event"*,
because §(K-tight) *Step 2* item 3 makes `dim R_a = 0` a uniform failure of routes
A and B. (OC-24)(ii) splits that event in two, and the two halves have very
different consequences:

| branch of `Z = ∅` | mechanism | consequence |
|---|---|---|
| **`{σ = 0} = ∅`** — `H` dependent at every chart point | a self-stress of the far framework, i.e. §(K-pure) (PC-OBS)'s *combinatorially certifiable* direction | **`hK` FALSE at that shape.** A **PENCIL event** — the phase's target theorem is false, §(K-flank) direction-A pivot class. Strictly stronger than a (K-tight) event |
| **`{target rank} = ∅`** with `{σ = 0} ≠ ∅` — identical badness on `M` ((OC-26)) | the Schubert containment `M̂ ∧ w ⊆ D` | **(K-tight) event**, exactly as the dispatch names it: (OC-8) false there, routes A and B dead **at that split**; `hK` at the shape untouched (another split, or §(K-grid)'s route, may still carry it) |

Nothing in the arc exhibits either branch at a class shape. **Surface the first
branch to the coordinator in those words**: the `s₀` half of input (a) is a
necessary condition for the theorem, so the only way it bites is by being false,
and then the phase pivots rather than re-routes.

**And the converse reading, which is the strategically useful one.** Because the
`s₀` half is *implied by* `hK` at the shape, it can never be the *binding*
obstruction: any proof of `hK` at a shape — the grid route included — hands it
over for free. That is what *Step O24* makes quantitative.

---

### Step O21 — (OC-25): input (a) is §(K-tight) *Step 2* item 1, one split down

> **(OC-25)** *(proven-informally — a substitution instance of §(K-tight) *Step 2*
> item 1, itself proven-informally; asserted per frame, and this is the first
> time that item has been driver-tested at a substituted instance)* At every
> chart point of `G′` with `pt(a) ∉ {pt(b), pt(c)}`:
>
> **(a)** `corank R(G′) = σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)`;
> **(b)** `dim D = 3 + σ` and `dim U_H = 3 − σ`;
> **(c)** hence, inside §(K-tight) *Step 2*'s scope,
>
> > the chart point lies in `Z` ⟺ `σ = 0` **and** the two functionals
> > `u ↦ ⟨u, C(ab)⟩`, `u ↦ ⟨u, C(ac)⟩` are linearly **independent** on the
> > 3-space `U_H`,
>
> which is *Step 2* item 1's attainment criterion with `(G, v, a, b)` replaced by
> `(G′, a, b, c)`.

*Proof.* §(K-tight) *Step 2* item 1 reads: at the split of a degree-2 vertex `x`
with neighbours `y`, `z`, `corank R(Γ) = corank R(Γ − x) + dim(U ∩ C(xy)^⊥ ∩
C(xz)^⊥)` with `U = {u : ⟨u, m(y) − m(z)⟩ = 0 ∀ m ∈ Mot(Γ − x)}`, valid at any
placement with `pt(x) ∉ {pt(y), pt(z)}`. Apply it with `Γ = G′`, `x = a`,
`{y, z} = {b, c}`: `a` has degree 2 in `G′` (its `G`-neighbour `v` is replaced by
`b`), `G′ − a = H`, and `U = U_H`. That is (a). For (b): *Step 2* item 3's count,
at the same substitution, gives `dim{m(y) − m(z)} = 4 + corank − index(Γ)` with
`index(G′) = index(G) + 1 = 1` (§(K-ind) *Step I2*), i.e. `dim D = 3 + σ`, and
`U_H = D^⊥` gives `dim U_H = 3 − σ`. For (c): at target rank
`corank R(G′) = index(G′) + def(G′) = 1`, so with `σ = 0` and `dim U_H = 3`, (a)
forces `dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥) = 1`, i.e. the two functionals cut `U_H`
down by 2, i.e. they are independent on it; conversely independence gives
`corank R(G′) = 1`, which *is* target rank since `5|E(G′)| − 1 = 6(|V(G)| − 2)`.
And `σ = 0` is `s₀ = 0` by (OC-23). ∎

**The regress terminates in one step, and that is a fact about the frame, not
luck.** `orient` requires `deg a = 2` and `deg c ≥ 3`, so the chain carrying the
split is `b — v — a — c` with exactly **two** interior vertices; peeling `v`
gives `G′`, peeling `a` gives `H`, and `H` has no further degree-2 vertex on that
chain to peel. A longer chain would iterate — which is worth recording, because a
naive reading of "the criterion's prerequisite is the criterion" suggests an
infinite regress and there is none here.

**Relation to KT's route B, so the two are not confused.** KT's `p₃` (pp.
684–691, §(K-tight) *Step 1*) uses the isomorphism `ρ : G^{vc}_a ≅ G^{ab}_v`
between two splits of the **same** `G`; (OC-25) is a different move — the split
of the **already-split** `G′` at `a` — and it produces the `H`-level obstruction
space, not a second route. They are compatible: both are the observation that
`v` and `a` are an adjacent degree-2 pair.

*Exact, per frame:* (a), (b), (c) asserted at **32/32** POOL-ZF frames, at the
first POOL-ZN witness of each family, and — the informative case — at the
**five** POOL-ZR (P21) `σ = 1` seeds, where `(dim U_H, dim D, rank of the two
functionals, dim W) = (2, 4, 2, 0)`: `corank R(G′) = 1 + 0 = 1`, target rank
with `dim R_a = 0`. The ledger holds off `Z` as well as on it.

---

### Step O22 — (OC-26): the `pt(a)`-fibre over the meet line, and the closed form of failure

> **(OC-26)** *(proven-informally; asserted per frame, with all three
> configurations CONSTRUCTED and 60 negative controls)* Fix a chart point with
> `σ = 0`, let `t` parametrize `M = Π(b) ∩ Π(c)` (the locus of `pt(a)`), write
> `W = ⟨pt(b)^, pt(c)^⟩` for the hub line's 2-space and
> `Φ : M̂ ∧ W → U_H^*`, `x ↦ ⟨·, x⟩|_{U_H}`, so that `ker Φ = D ∩ (M̂ ∧ W)`. Then
>
> **(i)** `C(ab)` and `C(ac)` are **affine-linear in `t`**, so the functional
> matrix of (OC-25)(c) is a `2 × 3` matrix of affine functions and its three
> `2 × 2` minors are quadratics in `t`. The **bad set** — the `pt(a)` for which
> the point leaves `Z` — is their **common** zero locus: three conditions on one
> parameter, hence **generically empty**. When it is empty the *whole*
> `pt(a)`-fibre over that `H`-part lies in `Z`.
>
> **(ii)** *(an equivalence, and a disjunction)* the bad set is **all** of `M`
> ⟺ `rank Φ ≤ 1` (i.e. `dim(D ∩ (M̂ ∧ W)) ≥ 3`) **or** `M̂ ∧ w ⊆ D` for some
> `w ∈ W`. Both disjuncts force `dim(D ∩ (M̂ ∧ W)) ≥ 2`, a **codimension-2**
> Schubert condition in `Gr(3, 6)` (generic value 1).
>
> **(iii)** the weaker degeneracy `D ∩ (M̂ ∧ pt(b)^) ≠ 0` (the `b`-side
> functional pair dependent on `U_H`) makes **exactly one** point of `M` bad, not
> the whole line.

*Proof.* (i) `pt(a) = P₀ + t·P_d` with `{P₀, P_d}` a basis of `M̂`, so
`C(ab) = pt(a)^ ∧ pt(b)^ = P₀ ∧ pt(b)^ + t · P_d ∧ pt(b)^` and likewise for
`C(ac)`; the pairing is linear, so each matrix entry is affine in `t` and each
`2 × 2` minor is a quadratic. By (OC-25)(c) the point is in `Z` iff the matrix
has rank 2, i.e. iff some minor is nonzero.

(ii) `{P₀ ∧ pt(b)^, P_d ∧ pt(b)^, P₀ ∧ pt(c)^, P_d ∧ pt(c)^}` is a basis of the
4-space `M̂ ∧ W` (using `M̂ ∩ W = 0`, i.e. `pt(b), pt(c) ∉ M`, which (Λ0d)
supplies), and `Φ` sends it to `(f₀, f₁, g₀, g₁)` where
`f_t = ⟨·, C(ab)⟩|_{U_H} = f₀ + t f₁` and `g_t = ⟨·, C(ac)⟩|_{U_H} = g₀ + t g₁`.
*(⟸)* If `rank Φ ≤ 1` all four lie in one line of `U_H^*`, so
`f_t ∧ g_t = 0` for every `t`. If `M̂ ∧ w ⊆ D = U_H^⊥` with
`w = pt(c)^ − c·pt(b)^` then `g_t = c f_t` for every `t`, likewise bad.
*(⟹)* Bad at every `t` says `f_t ∧ g_t = 0` in `Λ²U_H^*` identically, i.e.
`f₀ ∧ g₀ = 0`, `f₁ ∧ g₁ = 0`, `f₀ ∧ g₁ + f₁ ∧ g₀ = 0`. If `f₀ ∧ f₁ ≠ 0`, the
first two give `g₀ = c₀ f₀`, `g₁ = c₁ f₁` and the third `(c₀ − c₁) f₀ ∧ f₁ = 0`,
so `c₀ = c₁ =: c` and `Φ(q ∧ (pt(c)^ − c·pt(b)^)) = 0` for every `q ∈ M̂`, i.e.
`M̂ ∧ w ⊆ D`. If `f₀ ∧ f₁ = 0`, all `f_t` lie in one line `⟨φ⟩` (or vanish);
`g_t ∈ ⟨f_t⟩` for all but at most one `t`, and an affine map into a line agreeing
with it at ≥ 2 points has both coefficients in it, so `g₀, g₁ ∈ ⟨φ⟩` and
`rank Φ ≤ 1`. Finally `rank Φ = 4 − dim ker Φ = 4 − dim(D ∩ (M̂ ∧ W))`, and
`M̂ ∧ w ⊆ D` gives `dim ker Φ ≥ 2`; so either disjunct forces
`dim(D ∩ (M̂ ∧ W)) ≥ 2`, whose generic value in `Gr(3, 6)` against a fixed
4-space is `3 + 4 − 6 = 1` and whose jump locus has codimension 2 (choose the
2-plane inside the 4-space, 4 parameters, then extend to a 3-space of `K⁶`, 3
more: `7 < 9 = dim Gr(3, 6)`). ∎

**The first closed form this pass derived was WRONG, and the correction is a
constructed refutation, not a hedge.** The `f₀ ∧ f₁ = 0` branch above was first
read as also forcing `M̂ ∧ w ⊆ D` — "a ≥3-dimensional subspace of a 4-space
contains a pencil". It does not: identifying `M̂ ∧ W ≅ M̂ ⊗ W ≅ K^{2×2}`, a
hyperplane is `{X : tr(AᵗX) = 0}` and it contains the column space
`{q ⊗ w : q ∈ M̂}` iff `Aw = 0`, i.e. iff `A` is **singular**. POOL-ZQ **Case C**
constructs a nonsingular one: `D` = a nonsingular hyperplane of `M̂ ∧ W`, giving
`rank Φ = 1` (whole line bad) with **no** pencil inside `D` — asserted. So the
single-containment reading is **refuted by construction**, and (ii)'s
disjunction is the exact form. (iii) is the same computation stopped one step earlier: a nonzero element
of `D ∩ (M̂ ∧ pt(b)^)` is a relation `λ f₀ + μ f₁ = 0` on `U_H`, which makes the
`b`-row of the matrix proportional to a fixed functional and leaves a single
root; the constructed witness has GCD degree exactly 1. ∎

**Reading (i) correctly, because it is stronger than a codimension count.** With
`dim U_H = 3` there are **three** minors, so badness is *three* equations in one
unknown — not one, as the `2 × 2` case would give. That is why the generic fibre
is bad **nowhere** rather than at ≤ 2 points, and it is what makes the measured
figure below a statement about the whole line rather than about the sampled
`pt(a)`.

*Exact, per frame (POOL-ZF).* At **32 of 32** `σ = 0` frames: the three minors
have **ℚ[t]-GCD of degree 0** — no common root in **any** extension of ℚ — so
*every* legal `pt(a) ∈ M` gives a target-rank point and the entire `pt(a)`-fibre
lies in `Z`; `dim(D ∩ (M̂ ∧ W)) = 1` (the generic value) and no pencil lies
inside `D`; no minor vanishes identically; and **(ii)'s closed form is asserted
against the GCD test at every frame** — the disjunction and the GCD agree 32/32.

*The must-reject witnesses (POOL-ZQ, synthetic, `random.Random(20260819)`;
README §4 convention 6 — a criterion observed only passing is untested).*
**Case A**, the first disjunct: `M̂ ∧ w ⊆ D` for `w = pt(c)^ − 2 pt(b)^`
constructed by hand — all three minors vanish **identically in `t`**
(`dim(D ∩ M̂ ∧ W) = 2`, pencil present), so the whole meet line is bad and
`σ = 0` alone does **not** put a chart point in `Z`.
**Case B**, the *weaker* degeneracy `D ∩ (M̂ ∧ pt(b)^) ≠ 0` — the `b`-side pair
is rank 1 at every `t` and the bad-`t` GCD has degree **1**: exactly one bad
point, so meeting one pencil is strictly weaker than identical badness.
**Case C**, the **refutation**: `D` a nonsingular hyperplane of `M̂ ∧ W` —
`dim(D ∩ M̂ ∧ W) = 3`, **no** pencil inside `D`, and yet all three minors vanish
identically. **Negative control:** 60 random 3-spaces `D`, all with
`dim(D ∩ M̂ ∧ W) = 1`, no pencil, and bad-`t` GCD degree **0** — the generic
behaviour the three constructions must be read against.

---

### Step O23 — (OC-27): the probe *Step O18* asked for, run — POOL-ZN

> **(OC-27)** *(measurement; witnesses, never a rate)* Over POOL-ZN — 19 named
> class shapes plus the first 4 shapes of each `outer.sweep_shapes()` family
> (POOL-S's **shape** construction) at seed window **400–405** with **no stratum
> filter** — **138 (shape, split) pairs** were probed: the **90** eligible splits
> carrying a length-4 companion, plus **48** further eligible splits (every 4th
> of the remaining 190). At **138 of 138** the first guard-accepted chart point
> is an **exact-ℚ certified point of `Z`**: `rank R(G′) = 6(|V(G)| − 2) −
> def(G′)` and `corank R(G − v) = 0`, with (OC-23)'s `s₀ = corank R(H)` asserted
> at each. **No miss.**

**What this is.** Each row is a **witness**: one exact-ℚ chart point in `Z`
*proves* `Z ≠ ∅` at that (shape, split), with no appeal to openness,
irreducibility or genericity. So this measurement is exactly the kind the (OC-7)
standing rule leaves unharmed — *"a positive existence witness: a degenerate draw
can create neither a false hit nor a false witness"* — and the pass takes **no**
rate reading from it. (For the record: the acceptance gate here is
`outer.chart_point`, i.e. the composite `repin.star_generic` plus
`verify_pencil_witness`, which per `notes/scripts/README.md` §4 convention 1 is
the condition under which a `place_pencil_general` battery *may* be quoted as a
rate. The pass does not lean on that permission, and no figure above is a rate.)

**What this is not.** It is not class uniformity, and no seed pool can make it
so — §(K-out)'s standing caveat, repeated verbatim. Nor is it a claim about the
shapes and splits outside the disclosed bounds: the **caps are disclosed**
(README §4 convention 8) — per-family shape cap **4**, seed window **6** seeds,
stride **4** on the non-companion splits, so **142 of the 190** non-companion
eligible splits of the same pool, and every shape beyond each family's first
four, are **not covered**, and nothing here reports on them. Counts are
**labelled instances** (README §4 convention 7), never isomorphism classes:
`outer.sweep_shapes()` carries measured ~31× duplication (§(K-frame) (FR-14)).

**The two things the probe was for, answered.** *(1) Does any (shape, split) fail?*
No candidate in scope — hence no candidate (K-tight) event and, by (OC-24)(ii),
no candidate PENCIL event either. *(2) Is `s₀ = 0` per-seed luck or per-shape
structure?* Structure: with (OC-23) it is a property of the `H`-part alone, and
with (OC-26) the whole `pt(a)`-fibre over a good `H`-part is in `Z` at 32/32
POOL-ZF frames. The **per-(shape, split)** granularity the dispatch asked for is
therefore the right one, and the per-seed histogram it replaces would have been
measuring the `H`-part twice.

---

### Step O24 — (OC-28): the transfer from `G`, the grid domination, and the proper-open boundary

> **(OC-28)** *(proven-informally, conditional on the shared-sub-tower clause;
> the domination is a conditional, the boundary is exhibited)*
>
> **(i) Shared sub-tower.** Read against §(K-chart) **(CH-2)**'s stage table,
> the towers of `G` and of `G′` **coincide stage by stage over `V(H)`**:
> `H(G) = H(G′)` (the two chain interiors `v`, `a` have degree 2 and are not
> hubs), so **stage 1** — the free hub points — is literally the same space;
> **stage 2**'s matrix `A_h(q)` is built from `h`'s **hub** neighbours `N_Λ(h)`
> only, and `N_Λ(w)` is unchanged for every `w ∈ V(H)` (at `b`, the neighbour
> that changes, `v` and `a` are *both* non-hubs and so enter no `A_b`), so the
> hub-normal stage is the same too; **stage 4**'s fibre over an `H`-non-hub `s`
> is `⋂_{h ∼ s, h ∈ H} Π(q_h, n_h)`, again unchanged. The two towers differ
> **only** in the fibres over the chain interiors — `{v, a}` for `G` (both at
> `e = 1`, an in-panel point) versus `{a}` for `G′` (at `e = 2`, the meet line
> `M`) — and in **stage 3**'s open condition, which `G′` imposes at `a`
> (`n_b, n_c` independent, i.e. `Π(b) ≠ Π(c)`) and `G` does not. Hence the
> `H`-projection of `G′`'s chart is the `H`-projection of `G`'s chart intersected
> with that **dense open**, and an `H`-part of a `G`-chart point extends to a
> `G′`-chart point by re-placing `pt(a)` on `M`. **No rank claim crosses**, so
> §(K-frame) **(FR-4)**'s named gap — the (GR-5) restatement at `G′` — is
> **not** invoked. **Constructed** (POOL-ZT): at **30 of 30** (shape, split)
> pairs, a `G`-chart point at the Tay target, with its `H`-part copied verbatim
> and `pt(a)` slid to a pinned rational point of `M`, is accepted by the
> harness's own `G′` chart-point guards (`repin.star_generic` +
> `verify_pencil_witness`) with `corank R(H)` **unchanged** and the landed point
> **in `Z`**.
>
> **(ii) Transfer.** If `G` attains its Tay target at a pencil configuration then
> `corank R(G) = 0` (tight, `def(G) = 0`), hence `corank R(H) = 0` there, hence by
> (i) and (OC-23) `{σ = 0} ≠ ∅` on the chart of `G′` — **at every eligible split
> simultaneously**, since one `corank R(G) = 0` point kills every subgraph's
> stresses at once. Asserted per transfer at **30/30** POOL-ZT points
> (`corank R(G) = 0 ⟹ corank R(H) = 0`), and the transferred point landed in `Z`
> at all 30 — so at those pairs `hK`-at-a-chart-point yields a point of `Z` by an
> **explicit** construction rather than by the density argument.
>
> **(iii) Domination.** §(K-grid) **(GR-9)** *proves* that a legal alternating
> colouring with both-block tree-triple certificates reaches the Tay target
> `6(|V| − 1)` at a σ-fixed grid configuration, and **(GR-5)** puts that
> configuration in the chart's image. So **(GR-10) ⟹ the `s₀` half of input (a)
> at every tight class shape and every eligible split**; and it is *already*
> free at every shape where the certificate has been exhibited — **907/907** of
> §(K-grid)'s census pool ((GR-10)'s evidence, `--treetriple`).
>
> **(iv) Boundary — `{σ = 0}` is a *proper* open.** At `P21` (§(K-flank) *F5(d)*;
> a **(K-res)** shape that **fails `hnoRigid`**, §(K-pure) P4/P7) the five
> recorded `dim R_a = 0` seeds have `s₀ = σ = 1` — measured here, with (OC-23) and
> (OC-25) asserted at each — while **30** of the same window's valid seeds have
> `σ = 0`. The pinned counter-fact is that the **count** predicts
> `dim R_a = 5 + def(G′) − def(G − v) = 1`, i.e. `s₀ = 0`, at every placement.
> **This clause's *quantitative* reading — "so the complement of `{σ = 0}` is
> not thin in the sampler's rational range" — is REFUTED** (direction SIGZ,
> **(OC-38)**(iv)): **the five σ-jump seeds are EXACTLY the five at which `localtest.plane_basis` degenerates at hub `c`** (§(K-out) **(OC-38)**(iii), a set equality; under the composite gate `repin.star_generic`, `σ = 0` at all 360 gate-accepted seeds, cap 500), so at `P21` the complement **is** that
> coincidence locus, a proper closed subset. **The *proper-open* claim itself
> stands** — the five seeds are legal chart points (`flanks.nondeg_conjuncts`
> green at all five), which is all (iv) needs.

*Proof of (i).* Both `G` and `G′` satisfy §(K-chart) (CH-1)'s hypotheses — a
class shape has `hcard`, min degree 2 and girth ≥ 6, and (CH-1)'s own last
paragraph discharges all three at `G′` — so the tower description applies to
each. §(K-chart) **(CH-2)**'s four stages are indexed by bodies, and
each body's fibre condition reads only that body's **hub** neighbourhood: stage 1
frees the hub points, stage 2 puts `n_h ∈ ker A_h(q) ∖ 0` with `A_h` the matrix
of `q_u − q_h` over `u ∈ N_Λ(h)` (hub neighbours only — `widened.py:160`'s
`cons = [… for u in nb[h] if u in hubset]`), stage 4 puts a non-hub `s` in
`⋂_{h ∼ s, h ∈ H} Π(q_h, n_h)`. Now `deg v = deg a = 2`, so neither is a hub and
`H(G) = H(G′)`; and for every `w ∈ V(H)`, `N_Λ^{G′}(w) = N_Λ^{G}(w)` — the only
neighbourhood that changes at all is `b`'s, where the non-hub `v` is replaced by
the non-hub `a`, and non-hubs enter no `A_h`. So stages 1, 2 agree identically and
stage 4 agrees over every body of `H`. The towers therefore differ only over the
chain interiors and in stage 3's condition, which `G′` imposes at `a` (`e_a = 2`:
`n_b, n_c` independent) and `G` does not (`e_v = e_a = 1` there). Extension:
`a`'s `G′`-fibre is `M`, an affine line whenever `Π(b) ≠ Π(c)`; the acceptance
guards remove a proper closed subset of it. ∎

**Cross-direction convergence, recorded because it is the fan-out's own
mechanism.** This pass's mathematics was written **before** §(K-chart) landed,
with (i) flagged as "this pass's one structural input, tower-level, owned by
CIRR". CIRR then landed **(CH-2)** the same day — the tower written down stage by
stage against `place_pencil_general`'s source — and its stage table is exactly
what turns (i) from a flagged input into the proof above: the *hub*-only
dependence of stage 2 is the clause that does the work, and no prose description
of the tower before (CH-2) said it. Same shape as the sixth fan-out's
OCON/FRES convergence: two directions, same day, neither seeing the other, and
the pair is worth more than the sum.

*Proof of (ii)/(iii).* `G` tight with `def(G) = 0` makes its Tay target
`6(|V(G)| − 1) = 5|E(G)|`, i.e. full row rank, i.e. `corank R(G) = 0`; row-subset
monotonicity gives `corank R(H) = 0`; (i) transports the `H`-part; (OC-23)
converts it to `s₀ = 0`. For (iii), (GR-9) is quoted, not re-derived: its
conclusion is the Tay target at a grid configuration, and (AC-3) supplies the
nondegeneracy (GR-5) needs. The grid points are over `ℚ(i)`; a maximal minor of
`R(H)` nonvanishing there is nonvanishing at the generic point of the ℚ-chart,
hence at a ℚ-point, because §(K-chart) **(CH-1)(a)/(e)** makes the chart
ℚ-rational **with dense ℚ-points** — the step this pass would otherwise have had
to flag, supplied outright, on the same descent shape as §(K-clos) **(AC-7)**. ∎

**Two honest limits on (iii), stated because a one-line quotation will drop
them.** *(a)* §(K-grid)'s census pool (877 exhaustive `K4`-stratum shapes + 6 + 21
sweep shapes + 3 tight thetas) and §(K-out)'s class-shape population are **keyed
differently** and are labelled-instance pools (README §4 convention 7); "907/907"
is §(K-grid)'s pool, **not** "every class shape", and this pass does **not**
re-key either. *(b)* (GR-10) discharging would close `hK` on the whole tight
stratum outright ((GR-9) + (GR-5) + (AC-7)), which makes the domination a
*strategic* fact rather than a shortcut: it says the `s₀` half **cannot become the
binding obstruction before the grid route does**, not that either is closed.
Symmetrically — and this is the useful direction — any *partial* progress on the
grid route hands the `s₀` half over at the shapes it covers, because
independence of a proper subgraph is strictly weaker than rigidity of `G`.

**The mechanism of a failure, named.** (iv)'s `σ = 1` is not arithmetic noise: at
every one of the five seeds §(K-flank) *F5(d)* measured the `G − v` self-stress to
be supported on the theta sub-multigraph `{12, 13, 23a, 23b}` — 12 edges, line
rank 6 — the same support §(K-slide) *Step 5* exhibits for `P21`'s limit stress.
By (OC-23) that stress lives in `H`. So **the only known mechanism for the `s₀`
half to fail is a self-stress of a *subframework* of `H` forced by the pencil
pin** — §(K-pure) **(PC-OBS)**'s dependence side, which is exactly the
*combinatorially certifiable* direction of `Pencil-strategy.md` §2.3. Two
consequences: a future proof of the `s₀` half should look for a counting /
`hnoRigid`-driven exclusion of such subframework circuits rather than for a
genericity argument; and a search for a *counterexample* should look at class
shapes whose `H` contains a short theta sub-multigraph, which is where
`hnoRigid` is closest to failing.

---

### Where this leaves input (a) (hand-off)

**Status: OPEN as a class-uniform statement; not an independent gap; no gap-map
status moves.** *Step O18* item 2 asked for input (a) *"as a statement in its own
right"*; here it is, in the form the factorization leaves:

> **(a₂)** at every class (shape, split), `H = G − v − a` has **independent rows**
> at some pencil chart point — equivalently, at the generic one; and
> **(a₁)** at some such point, `D = {m(b) − m(c) : m ∈ Mot(H)}` contains **no**
> pencil `M̂ ∧ w` with `w` on the line `pt(b) pt(c)`.

What a successor should pick up, in descending value:

1. **(a₂) class-uniformly, via the grid route.** By (OC-28)(iii) this is
   *implied* by §(K-grid) (GR-10) and free at 907/907 of its pool, so the
   cheapest genuine progress is **not** a new argument here but a re-keying:
   check that every §(K-out) class shape carrying a length-4 companion is in
   §(K-grid)'s certified set (the two pools are keyed differently, (OC-28)(a)),
   which is a **combinatorial** cross-pool job with no new mathematics — and the
   transfer itself is already **machinery**, not an argument: `zneq --transfer`
   turns any target-rank chart point of `G` into a guard-accepted point of `Z` on
   every eligible split's `G′`-chart (30/30). Failing that, the honest target is a
   counting/`hnoRigid` exclusion of the subframework circuits *Step O24* names.
2. **(a₁) class-uniformly.** The Schubert non-jump `dim(D ∩ (M̂ ∧ W)) ≤ 1` —
   one condition, `x₁`-free, `λ`-free, stratum-free, and in the same object class
   as §(K-out) (OC-20)'s perp form (a subspace-meets-subspace count in `Λ²K⁴`).
   It is measured to fail nowhere (GCD degree 0 and `dim(D ∩ M̂ ∧ W) = 1` at
   32/32 POOL-ZF frames) and it is **one-point decidable**; a *recipe* is what is
   missing, exactly as for (OC-19) input (c). Worth trying first: `D` is the
   relative twist space of `H` with **no** hinge deleted and **no** weld, so
   §(K-out) (OC-18)'s `H/X`-rigidity criterion and `D` are near neighbours —
   `H/X` rigid forces `W₁ = 0`, and `D` is the un-welded analogue. Second: `D`
   depends only on the `H`-part, so (OC-28)(i) makes this too a statement about
   `G`'s own chart.
3. **A `σ > 0`-everywhere hunt at class shapes whose `H` carries a short theta
   sub-multigraph** — the only known failure mechanism (*Step O24*). A hit is a
   **PENCIL event** (disproof at that shape), so this is the highest-variance
   item on the list and should be run with the direction-A pivot rule in force.
4. **Deliberately not attempted**, recorded so a successor does not assume
   otherwise: (OC-19) input (c) (`H/X` rigid class-uniformly — OCON's verdict
   stands: (GR-15)-flavoured, not (FR-R1)-flavoured); chart irreducibility
   itself (§(K-chart), landed this wave — **cited**, not re-derived); pushing a constructed
   point to `p⁺` (§(K-out) *What would change this* item 4); the coupled two-end
   slide (item 5); every §(K-frame) *What would change this* item (ii)–(iv); and
   any counting / matroid route to (OUT)'s hypothesis ((OC-3) refutes the whole
   class).

---

### Verification (Steps O19–O24)

`notes/scripts/w4/zneq.py` (new, untracked at draft time; exact ℚ, stdlib only;
a `w4/` leaf **above** `ocon`, which it imports read-only — `stratum_numbers`,
`perp_B`, `meet` — together with `outerline` (`weld_motions`, `rel_span`),
`outer` (`split_data`, `eligible_splits`, `named_inventory`, `sweep_shapes`,
`companions4`, `chart_point`, `stratum_at`, `panel_frame`), `flanks`
(`P21_SPECS`), `kslidecomb` (`shape_data`), `widened` (`orient`,
`split_report`), `repin` (`rank_at_V`, `span_basis`, `star_generic`,
`seed_probe`), `kbare_common` (`rank_modp`, `verify_pencil_witness`,
`verts_of`), `pencil_escape` (`build_rigidity`), `nogood_subdiv`
(`deficiency`) and catalogued §1 primitives. **Nothing existing is modified**: `outer.py`,
`outerline.py`, `outerwide.py`, `ocon.py`, `repin.py`, `flanks.py`,
`kslidecomb.py`, `widened.py` are all read.) From the repo root:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --factor   # (OC-23),(OC-25),(OC-26); POOL-ZF, POOL-ZQ
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --sweep    # (OC-27); POOL-ZN
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --reject   # (OC-28)(iv); POOL-ZR
PYTHONHASHSEED=0 python3 notes/scripts/w4/zneq.py --transfer # (OC-28)(i)/(ii) CONSTRUCTED; POOL-ZT
```

Times as run: `--factor` **97 s**, `--sweep` **242 s**, `--reject` **76 s**,
`--transfer` **106 s** — 521 s in total. All four re-run **byte-identical** under
two different `PYTHONHASHSEED` values (`0` and `12345`), the
*figures-do-not-move* gate
(`notes/scripts/README.md`) — `--sweep` modulo the elapsed-second progress marks
it prints per family, which are wall-clock, not figures. The pass **added** one
driver and modified none (`git status --porcelain notes/scripts/` shows exactly
the one new file).

**Harness debt recorded, not paid.** `ocon.meet` — the dimension-asserting
wrapper of `lambda.span_meet` — now has **two** consumers, which is
`notes/scripts/README.md` §2 rule 2's own trigger to move it one layer down
beside `span_meet`. This pass may not modify a landed file, so the move is
**recorded for a successor**, not made; `zneq` imports it read-only meanwhile.

**Pools, pinned; every figure above is quoted over exactly one of them, and none
is aggregated with POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A /
POOL-W / POOL-SL / POOL-OV / POOL-OC / POOL-OZ.**

- **POOL-ZF** (`--factor`) — the 4 `lambda.habitat_specs` habitats × **every**
  eligible split × placement seeds **300–303**, **unfiltered** (no target-rank,
  no stratum filter) but guard-accepted through `outer.chart_point`
  (`repin.star_generic` + `verify_pencil_witness`): **30 splits probed, 32 chart
  points accepted, 88 draws rejected by the guards.** A derivation pool: every
  sentence under test is an identity, so it is a witness set, and **no figure
  from it is a rate**.
- **POOL-ZQ** (`--factor`) — synthetic exact-ℚ subspaces of `Λ²K⁴` from
  `random.Random(20260819)` (seed printed), plus **three constructed**
  configurations (Cases A, B, C — C being the refutation of this pass's own first
  closed form) and **60 negative controls**. No graph, no placement.
- **POOL-ZN** (`--sweep`) — `outer.named_inventory()` (19 named class shapes)
  plus the **first 4** shapes of each `outer.sweep_shapes()` family — POOL-S's
  *shape* construction — at seed window **400–405** with **no stratum filter**;
  population = every eligible split carrying a length-4 companion (**90**) plus
  **every 4th** of the remaining 190 (**48**). **138 (shape, split) pairs, 138
  chart points drawn.** *Caps disclosed* (README §4 convention 8): shape cap 4
  per family, seed window 6, stride 4; the other 142 non-companion splits and
  every shape past each family's fourth are **not covered**.
- **POOL-ZT** (`--transfer`) — the 4 habitats × **every** eligible split ×
  placement seeds **500–507** of the **whole graph `G`** (not of `G′`),
  guard-accepted for `G` by `repin.star_generic` + `verify_pencil_witness`, then
  `pt(a)` slid onto `M` at the first of **8 pinned rational parameters**
  (`1, −1, 2, ½, −3, 3, 5, −⅓`) the `G′` guards accept. **30 transfers
  constructed, 30 accepted, 0 failures.** The slide-parameter list is a
  disclosed bound: a (shape, split) where none of the eight is accepted would be
  reported, and none was.
- **POOL-ZR** (`--reject`) — `P21` (`flanks.P21_SPECS`), split `v = 100`
  (`a = 101`, `b = 0`, `c = 1`), seeds **101–140**: the same window §(K-flank)
  *F5(d)* used, re-read in `s₀` / `corank R(H)` coordinates. `P21` **fails
  `hnoRigid`** and is a **(K-res)** shape, not a tight class member — it is here
  as the arc's only recorded `σ = 1` witness.

Per mode, what is asserted:

- `--factor`: per frame — (OC-23)'s `s₀ = corank R(H)`; (OC-25)(a) against
  independently computed coranks; (OC-25)(b)'s `dim D = 3 + σ`,
  `dim U_H = 3 − σ`; (OC-25)(c)'s `Z`-membership equivalence; (OC-17) against
  the catalogued `outer.stratum_at` (`dim R_a = 1 − s₀` at target rank, and
  `stratum_at is None` off it); `pt(a)` **on** the meet line `M`, exactly; the
  affine-linearity of `C(ab)`, `C(ac)` along `M` spot-checked at `t = 2`; the
  three minors' ℚ[t]-GCD, with an assert that **no** minor vanishes identically;
  **(OC-26)(ii)'s disjunction asserted against that GCD**; and the sampled `t`'s
  goodness against `Z`-membership. Histograms:
  `(target rank?, s₀, σ, dim U_H, dim W, in Z) = (True, 0, 0, 3, 1, True) : 32`;
  `(minors, identically-zero minors, deg GCD, dim(D ∩ M̂ ∧ W), pencil?) =
  (3, 0, 0, 1, False) : 32`.
  POOL-ZQ: Case A — three minors identically zero, `dimK = 2`, pencil present;
  Case B — `b`-row rank 1, bad-`t` GCD degree exactly 1; **Case C** — `dimK = 3`,
  **no** pencil, three minors identically zero (the refutation); 60 random
  controls at `dimK = 1`, no pencil, GCD degree 0.
- `--sweep`: per (shape, split) — a GF(p) screen (`rank_modp`, a **certified
  lower bound**, README §4 convention 2) selects a candidate seed, and the
  accepted witness is **rechecked in exact ℚ**: `rank R(G′) = 6(|V(G)| − 2) −
  def(G′)`, `corank R(G − v) = 0`, plus (OC-23). An assert catches any screen
  mis-prediction (none fired). The (OC-25) leg runs at the first witness of each
  family (disclosed). Outcome: `('WITNESS in Z', has length-4 companion) =
  (True) : 90`, `(False) : 48`; first-witness seed histogram
  `{400: 62, 401: 47, 402: 25, 403: 4}`.
- `--transfer`: per (shape, split) — the `G`-side guards (`star_generic`,
  `verify_pencil_witness`) on the **whole-graph** placement; `corank R(H) ≤
  corank R(G)`; at every target-rank `G`-point `corank R(G) = 0` **and**
  `corank R(H) = 0`; after the slide, the `H`-part asserted **equal
  point-by-point** to the `G`-point's, `corank R(H)` asserted **unchanged**, the
  `G′` guards asserted to accept, and the full (OC-23)/(OC-25) ledger at the
  landed point. Histogram `(G at target rank?, corank R(H), G′ at target rank,
  in Z) = (True, 0, True, True) : 30`.
- `--reject`: per valid seed — `s₀` cross-checked against `repin.seed_probe`'s
  own `s₀`, (OC-23) asserted, and at each `dim R_a = 0` seed the full (OC-25)
  ledger `(s₀, σ, dim U_H, dim D, rank of the two functionals, dim W) =
  (1, 1, 2, 4, 2, 0)` with `rank R(G′) = tgt` asserted. Tally: **30** seeds with
  `σ = 0`, **5** with `σ = 1`, 5 invalid.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean (`DESIGN.md`
*Formalize everything the argument uses*).

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (OC-23) `s₀ = corank R(H)` | `--factor`, `--sweep`, `--reject` | both coranks computed **independently** in exact ℚ and asserted equal, per frame — 32/32 POOL-ZF, 138/138 POOL-ZN witnesses, 35/35 valid POOL-ZR seeds **including the 5 that reject** |
| (OC-24)(i) openness / one-point witnessing | — | **proof-level** ((OC-17) + (OC-23) + §(K-chart) (CH-1)(a), **proven** not cited). Its *operational* content — one point certifies — is what `--sweep` exercises 138 times |
| (OC-24)(ii) `{σ = 0} = ∅ ⟹ hK` false | `--transfer` for its ingredient | **proof-level** (row-subset monotonicity + tightness), resting on (OC-28)(i). **Not driver-testable as stated**: no driver can quantify over a whole chart. What *is* tested is the implication it contraposes — `corank R(G) = 0 ⟹ corank R(H) = 0`, asserted at every target-rank `G`-chart point (30/30, POOL-ZT) — plus `corank R(H) = 0` wherever `Z` is reached (138/138, POOL-ZN) |
| (OC-25)(a) the corank identity | `--factor` (per frame), `--sweep` (first witness per family), `--reject` (per jump seed) | `corank R(G′)` from an exact rank vs `σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)` from the motion space — the two sides computed by disjoint routes |
| (OC-25)(b) the two dimension counts | same | `dim D = 3 + σ` and `dim U_H = 3 − σ` asserted inside `u_space`, at `σ = 0` (POOL-ZF, 32) **and** `σ = 1` (POOL-ZR, 5) |
| (OC-25)(c) the `Z`-membership equivalence | same | `(rank = tgt ∧ s₀ = 0) == (σ = 0 ∧ the functional pair independent)` asserted per frame — an **iff**, so both directions are exercised (the 5 POOL-ZR seeds exercise the false side) |
| (OC-26)(i) affine-linearity + the 3-minor count | `--factor` | the matrix is rebuilt from its `t = 0` / `t = 1` values and **spot-checked against a direct evaluation at `t = 2`**; the minor count is `C(dim U_H, 2) = 3`, printed |
| (OC-26)(i) "generically empty" | `--factor` | the exact ℚ[t] **GCD** per frame: degree 0 at 32/32, i.e. no bad `t` in any extension of ℚ. This is the sentence a rational-root search would have *under*-tested |
| (OC-26)(ii) the disjunction | `--factor` (per frame) | `(GCD identically zero) == (dim(D ∩ M̂ ∧ W) ≥ 3 or a pencil M̂ ∧ w ⊆ D)` asserted at **every** frame, the two sides computed by disjoint routes (a ℚ[t] GCD vs two exact rank computations); the pencil test is exact — `∃w` iff a `(2·dim U_H) × 2` matrix has rank ≤ 1, no `P¹` parametrization |
| (OC-26)(ii) ⟸, both disjuncts | `--factor` POOL-ZQ | **constructed** Case A (`M̂ ∧ w ⊆ D`, `dimK = 2`) and **constructed** Case C (`dimK = 3`, **no** pencil) each asserted to make all three minors vanish identically |
| (OC-26)(ii) the *first* closed form, REFUTED | `--factor` POOL-ZQ Case C | Case C is asserted to have `dimK = 3` **and** no pencil **and** identical badness — a constructed counterexample to "identically bad ⟺ a pencil inside `D`", which is what this pass first derived |
| (OC-26)(iii) one bad point, not the line | `--factor` POOL-ZQ | the **constructed** Case B asserted to have `b`-row rank 1 **and** GCD degree exactly 1 |
| (OC-26) as a criterion (F13) | `--factor` POOL-ZQ | **three** constructed must-**reject** objects plus **60** negative controls, each asserted at `dimK = 1`, no pencil, GCD degree 0 — the guard is not observed only passing |
| (OC-27) the witness census | `--sweep` | per (shape, split), an exact-ℚ certified point of `Z` or an explicit miss row; a screen mis-prediction assert; caps printed in the mode's own header |
| (OC-28)(i) shared sub-tower | `--transfer` | **constructed**: a `G`-chart point's `H`-part, copied point-by-point, plus `pt(a)` on `M`, is asserted to pass the harness's own `G′` chart-point guards, with `corank R(H)` asserted unchanged — 30/30. The *general* statement is **proven** against §(K-chart) (CH-2)'s stage table (hub-only stage 2), not merely sampled |
| (OC-28)(ii) transfer | `--transfer` | `corank R(G) = 0 ⟹ corank R(H) = 0` asserted at every target-rank `G`-point (30/30), and the landed `G′` point asserted through the full `Z` ledger — in `Z` at 30/30 |
| (OC-28)(iii) domination | — | **quotation**: (GR-9) proven, (GR-10) measured 907/907 in §(K-grid)'s own driver. Nothing re-derived here, and the pools are **not** re-keyed |
| (OC-28)(iv) the proper-open boundary | `--reject` | 5 `σ = 1` seeds against 30 `σ = 0` at the same window, with the **count-theoretic counter-fact** (`widened.split_report` = 1) printed beside them |
| `Z ≠ ∅` class-uniformly | — | **not tested and not claimed.** 138 labelled (shape, split) witnesses under disclosed caps, never a class-level statement |

---

### Confidence verdict (Steps O19–O24)

| | claim | standing |
|---|---|---|
| **(OC-23)** | `s₀ = corank R(H)` at every legal chart point with `pt(a) ≠ pt(c)`; so input (a)'s `s₀` half is independence of `H` alone | **proven-informally** (the pendant-edge case of (OC-17)'s own lemma); asserted per frame at 32/32 POOL-ZF, 138/138 POOL-ZN witnesses and 35/35 valid POOL-ZR seeds |
| **(OC-24)(i)** | `Z ≠ ∅ ⟺` both halves nonempty; each one-point witnessable; one point satisfying both needs no irreducibility | **proven-informally** — and its irreducibility hypothesis is now **PROVEN**, not cited: §(K-chart) **(CH-1)(a)**, unconditional at `Γ = G′`, with (CH-1)(b) making FRES's constant-fibre-dimension restriction inessential |
| **(OC-24)(ii)** | `{σ = 0} = ∅` at a class shape ⟹ **`hK` FALSE** there; so the `s₀` half is a **necessary condition** for the phase's target, and that branch of a `Z = ∅` negative is a **PENCIL event**, not a (K-tight) event | **proven-informally**, conditional on (OC-28)(i)'s shared-sub-tower clause. Not driver-testable (a whole-chart quantifier). **This is the pass's sharpest finding and the one to surface** |
| **(OC-25)** | `corank R(G′) = σ + dim(U_H ∩ C(ab)^⊥ ∩ C(ac)^⊥)`, `dim D = 3 + σ`, `dim U_H = 3 − σ`; hence membership of `Z` **is** §(K-tight) *Step 2* item 1's attainment criterion at `(G′, a)`, and the regress terminates in one step | **proven-informally** (a substitution instance of a proven-informally item); asserted per frame at 32/32 POOL-ZF, at 5/5 POOL-ZR jump seeds and at the first POOL-ZN witness per family. **First driver test of that item at a substituted instance** |
| **(OC-26)** | along `M` the bad set is the common zero locus of **three** quadratics, generically empty; bad-at-every-`t` ⟺ `dim(D ∩ M̂ ∧ W) ≥ 3` **or** `M̂ ∧ w ⊆ D` — both forcing a codimension-2 Schubert jump; the weaker `D ∩ (M̂ ∧ b^) ≠ 0` gives exactly one bad point | **proven-informally**, equivalence in both directions, and the closed form **asserted against the GCD at every frame** (32/32). ℚ[t]-GCD degree **0**, `dim(D ∩ M̂ ∧ W) = 1`, no pencil, at 32/32; three configurations **constructed** + 60 controls (F13). **This pass's own first closed form was REFUTED by its Case C** — record it as the correction it is |
| **(OC-27)** | 138/138 labelled (shape, split) pairs of POOL-ZN carry an exact-ℚ certified point of `Z` — 90 companion-bearing, 48 others | **measurement; witnesses, not a rate.** Caps disclosed; no class-level reading; no candidate (K-tight) or PENCIL event in scope |
| **(OC-28)** | the two charts share their `H`-sub-tower, so `corank R(H) = 0` transfers from a target-rank configuration of `G`; hence **(GR-10) ⟹ the `s₀` half at every tight class shape and split**, free at 907/907 of §(K-grid)'s pool; and `{σ = 0}` is a **proper** open, witnessed at `P21` | **(i) proven-informally** against §(K-chart) (CH-2)'s stage table (hub set unchanged; stage 2 depends on **hub** neighbours only, and both chain interiors are non-hubs) **and constructed** at 30/30 POOL-ZT pairs — it was flagged as this pass's one structural input and CIRR's same-day landing discharged it; **(ii) proven-informally, asserted 30/30**, with the transferred point landing **in `Z`** at all 30; **(iii) a conditional plus a quotation** — (GR-9) proven, (GR-10) measured, the ℚ-descent supplied by (CH-1)(e), pools **not** re-keyed; **(iv) measured**, 5 vs 30 at a **non-class** shape |
| **input (a)** | `Z ≠ ∅` at every class (shape, split) | **OPEN as a class-uniform statement — and NOT an independent gap.** Reduced to (a₂) + (a₁) above; neither proven class-uniformly here |

**No gap-map status moves. Class uniformity of (OUT), of (OC-8) and of `hK` is
exactly where it was.** What moves is the *content* of §(K-out)'s row (which
gains (OC-23)–(OC-28)) and the reading of (OC-19)'s input (a): from an unowned
prerequisite to a two-half statement, one half necessary for `hK` and dominated
by (GR-10), the other the (K-tight) criterion one split down.

### What would change this (Steps O19–O24)

1. **A class shape whose `H` is dependent at every chart point** — `{σ = 0} = ∅`.
   By (OC-24)(ii) that **disproves `hK` at that shape**: a **PENCIL event**, not
   a (K-tight) event, and the phase pivots rather than re-routes. The hunt with
   the best prior is class shapes whose `H` contains a short theta
   sub-multigraph, the *only* known mechanism (§(K-flank) *F5(d)*'s support, via
   (OC-23)); it would simultaneously refute §(K-grid) (GR-10) at that shape.
2. **A class (shape, split) at which the (OC-26)(ii) disjunction holds** at
   every `σ = 0` chart point — the (K-tight) event the dispatch named. Measured
   nowhere: GCD degree 0, `dim(D ∩ M̂ ∧ W) = 1` and no pencil, at 32/32 POOL-ZF
   frames. **Constructed** instances of *both* disjuncts exist synthetically
   (Cases A and C), so the configuration is not impossible in `Λ²K⁴` — the open
   question is whether a class chart can realize it. Note the two disjuncts are
   genuinely different loci: Case C carries no pencil at all, which is why the
   single-containment reading had to be replaced.
3. **A failure of the shared-sub-tower clause** ((OC-28)(i)) would break
   (OC-24)(ii) and (OC-28)(ii)–(iii) at once, leaving (OC-23), (OC-25), (OC-26)
   and (OC-27) intact. It is **no longer an input**: §(K-chart) (CH-2)'s stage
   table proves it (stage 2 reads **hub** neighbours only, and both chain
   interiors are non-hubs), and 30/30 POOL-ZT transfers are guard-accepted. What
   *would* break it is a change to `place_pencil_general`'s stage 2 that let a
   **non-hub** neighbour constrain a hub normal — worth naming because that is
   precisely the difference between the two charts. It remains **cheaper than
   §(K-frame) (FR-4)**, which it deliberately does not invoke: nothing about rank
   crosses between the two charts.
4. **A failure of chart irreducibility** ((OC-24)(i)) would break the *two-point*
   form of the reduction but **not** the one-point form, so it would not touch
   (OC-27)'s 138 witnesses. Since §(K-chart) **(CH-1)** it is **proven**, so this
   item is now a pointer to (CH-1)'s own hypotheses (`hcard`, min degree 2,
   girth ≥ 4 — all unconditional at `G′`) rather than an open risk.
5. **Re-keying §(K-grid)'s 907 against §(K-out)'s class-shape population.** The
   cheapest genuine progress on (a₂) and the one thing this pass deliberately did
   **not** do: the two pools are labelled-instance pools with different keys
   (README §4 convention 7), so "907/907" cannot be read as "every §(K-out) class
   shape". A combinatorial cross-pool check, no new mathematics.
6. **A longer split chain.** (OC-25)'s regress terminates in one step because
   `orient`'s chain has exactly two interior vertices. If a future frame admits a
   split whose chain interior is longer, input (a) at that frame iterates the
   substitution and the peeling bottoms out further down — worth recording so a
   successor does not assume the one-step form is structural.
7. **A `σ = 1` chart point at a *class* shape** (as opposed to `P21`, which fails
   `hnoRigid`). None is recorded anywhere in the arc; exhibiting one would be item
   1 in progress, and its absence is currently the whole empirical content of
   (a₂).

---

### Steps O31–O36 (2026-08-19, eighth fan-out, direction SIGZ) — the `σ > 0`-everywhere hunt: **NO HIT, and the counting route to a disproof of `hK` is DEAD.** The pencil self-stress space of any subgraph is a **Kirchhoff flow on its topological branches** valued in the chain-span perps ((OC-35)), which turns `corank R(F)` into a three-term ledger ((OC-36)); at a class shape §(K-Λ) **(Λ4)(iii)** makes the ledger's combinatorial term **`slack(F) ≥ 0`, with equality iff `F` is a cycle or a bouquet of cycles** ((OC-37)) — so **no `H`-supported self-stress is combinatorially forced anywhere in the habitat**, thetas included, and the *only* recorded instance of the mechanism, at `P21` (**`hnoRigid`-FALSE**), is **exactly one unit short** of what the class requires ((OC-38)) *and* is located precisely: its five σ-jump seeds are **exactly** the five where `localtest.plane_basis` degenerates at hub `c` ((OC-38), set equality). `{σ = 0} ≠ ∅` carries an exact-ℚ **full-row-rank certificate at 3368/3368** class (shape, split) pairs over the **exhaustive `K4` stratum** ((OC-39)). **No gap-map status moves; `hK`, (OC-8), (GR-15), `{σ = 0}`'s row and class uniformity are exactly where they were.**

> **Read this first.** This direction was authorized as the arc's first
> **disproof** direction, with the direction-A pivot rule in force. **It did
> not hit.** Everything below is the negative and the machinery that produced
> it; nothing here is a licence to re-plan the arc, and the two adjudications
> the pass surfaces — the (OC-28)(iv) *reading* correction and the harness
> finding — are the coordinator's and the user's, not this pass's.

#### Standing notation (on top of §(K-out) *Steps O19–O24*)

`H := G − v − a` at a class split; `σ := corank R(H)` ((OC-23)). For a
subgraph `F ⊆ G` with **minimum degree ≥ 2**, write `F°` for its
**topological reduction**: nodes are the vertices of `F`-degree ≥ 3, paths
are the maximal `F`-paths between nodes, and a component with no
degree-≥ 3 vertex contributes one **loop** at an arbitrary chosen vertex of
it. Write `n(F)` for the number of nodes, `ℓ_Q` for the length (edge count)
of path `Q`, and

- `S_Q := ⟨C_e : e ∈ Q⟩ ⊆ Λ²K⁴` — the path's **chain span** (§(K-pure)'s
  `S_P` for a single branch, read at the *unslid* placement rather than at
  the `ε = 0` limit; **that is the whole difference**);
- `δ_Q := min(ℓ_Q, 6) − dim S_Q ≥ 0` — its **chain-span deficiency**;
- `ρ_F := 6(n(F) − 1) − rank K_F ≥ 0` — the **Kirchhoff-rank deficiency**
  of the flow system of *(OC-35)*;
- `slack(F) := Σ_Q min(ℓ_Q, 6) − 6·c(F) = 6(n(F) − 1) − Σ_Q (6 − ℓ_Q)^+`.

`f(V(F)) = 5|E(F)| − 6(|V(F)| − 1) = 6c(F) − |E(F)|` is the *Shared
dictionary*'s sparsity functional (the second equality is (I1)'s
substitution). Everything below is at an arbitrary legal pencil chart point
unless a genericity clause is stated; no target-rank hypothesis is used
anywhere in *Steps O31–O33*.

---

#### Step O31 — (OC-35): the pencil self-stress space is a Kirchhoff flow on the topological branches

> **(OC-35)** *(proven; unconditional, no genericity, asserted per frame)*
> Let `F` be a subgraph with min degree ≥ 2 at any pencil placement. Then the
> self-stress space of `F` is **canonically isomorphic** to
>
> `{ (ψ_Q)_{Q ∈ E(F°)} ∈ ⊕_Q S_Q^⊥ : Σ_{Q ∋ h} ±ψ_Q = 0 at every node h of F° }`,
>
> the sign being `+` at the path's start node and `−` at its end node (so a
> loop contributes nothing at its node). Hence
>
> `corank R(F) = Σ_Q (6 − dim S_Q) − rank K_F`.
>
> Two riders. *(i)* A vertex of `F`-degree 1 forces its stress coefficient to
> **0**, so every minimal support has min degree ≥ 2 — this is the *same*
> five-hinge-rows-on-one-block lemma (OC-17) and (OC-23) use. *(ii)* Every
> path of a minimal support carries `ψ_Q ≠ 0`, so `dim S_Q ≤ 5` there; in
> particular a topological path with **full** span `dim S_Q = 6` carries no
> stress at all.

*Proof.* A self-stress assigns to each oriented edge `e` a covector
`φ_e` annihilating `C_e` — a 5-space — with `Σ_{e ∋ u} ±φ_e = 0` at every
body `u`. At a body `x` of `F`-degree 2 with edges `e, e′` that condition
**is** `φ_e = ±φ_{e′}`, so normalizing signs forward along the path the
covector is *constant* along it, and it lies in
`⋂_{e ∈ Q} C_e^⊥ = S_Q^⊥`, of dimension `6 − dim S_Q`. What survives at the
nodes is Kirchhoff's law. For *(i)*, at a degree-1 body the single edge's
condition is `φ_e = 0`. For *(ii)*, `S_Q^⊥ = 0` when `dim S_Q = 6`. ∎

**Why this is not §(K-pure)'s statement, and why the difference is the
point.** §(K-pure) *Step P0* already writes the limit carrier's stresses in
exactly this shape — `R_P := S_P^{⊥_B}`, "the available bars", with a
vertex-sum condition at every hub. That statement is about the **`ε = 0`
slide limit** on `G°`, where `S_P` is the *limit* chain span and where (S1)
supplies the carrier. (OC-35) says the same bookkeeping is valid **on the
pencil chart itself, with no slide, no limit and no decoration**, for any
subgraph and any placement — because the only input is *"a degree-2 body has
two hinge lines and they span at most its own 2-dimensional pencil"*. That is
what lets §(K-Λ) **(Λ4)**'s combinatorics be spent directly on `σ`.

**One convention note, stated because a reader will trip on it.** The
harness's `pencil_escape.build_rigidity` builds each edge's rows from the
**Euclidean** perp `perp_basis(C_e)`; §(K-pure) uses the **Klein** perp
`S_P^{⊥_B}`. The two differ by one Hodge star, which is an isomorphism of
`Λ²K⁴` commuting with the Kirchhoff map, so every dimension and rank in
*Steps O31–O36* is the same in either convention. The driver uses the
Euclidean one and says so.

*Exact, per frame:* the isomorphism's numerical content — `corank R(F)`
computed from the full `5|E(F)| × 6|V(F)|` rigidity matrix versus computed
from the flow system — agrees at **400/400** (shape, seed, support)
instances, including **10** with `corank ≥ 1` (`sigz.py --reduce`).

---

#### Step O32 — (OC-36): the degeneracy-budget identity

> **(OC-36)** *(proven; an identity, unconditional, asserted per frame)* At
> every pencil placement, for every min-degree-≥ 2 subgraph `F`,
>
> `corank R(F) = Σ_Q δ_Q + ρ_F − slack(F)`,
>
> equivalently `corank R(F) = f(V(F)) + Σ_Q (ℓ_Q − dim S_Q) + ρ_F`. All of
> `δ_Q`, `ρ_F` are `≥ 0`, so
>
> **a self-stress of `F` exists ⟺ `Σ_Q δ_Q + ρ_F ≥ slack(F) + 1`.**
>
> The two summands are the pass's two **geometric** currencies: `δ_Q` is a
> *chain-span* degeneracy (the path's `ℓ_Q` hinge lines fail to span
> `min(ℓ_Q, 6)` dimensions), `ρ_F` a *Kirchhoff* degeneracy (the perp spaces
> fail to be in general position at the nodes). `slack(F)` is the purely
> combinatorial term and is the only one that sees the class predicate.

*Proof.* From (OC-35), `corank = Σ_Q(6 − dim S_Q) − rank K_F`. Substitute
`dim S_Q = min(ℓ_Q,6) − δ_Q` and `rank K_F = 6(n − 1) − ρ_F`:
`corank = 6m − Σ_Q min(ℓ_Q,6) + Σδ_Q − 6(n−1) + ρ_F` with `m = |E(F°)|`, and
`6m − 6(n−1) = 6c(F)` because `c(F) = m − n + 1` (the loop convention makes
this hold for `n = 1` too). Non-negativity of `ρ_F` is `rank K_F ≤ 6(n−1)`:
the image of `K_F` lies in the sum-zero subspace of `(K⁶)^{nodes}`, since
each path enters two node blocks with opposite signs. The `f`-form follows
from `f(V(F)) = 6c(F) − Σ_Q ℓ_Q`. ∎

**Two special cases, worth naming because they are the arc's own objects.**
For a single cycle `Z` (so `n = 1`, one loop, `ρ = 0`) the identity is
`corank R(Z) = 6 − dim S_Z` — **exactly §(K-slide) *(S5)*'s serial-chain
count `#stresses = 6 − rank{lines}`**, now derived rather than telescoped,
and valid off the limit. For a **theta** (`n = 2`, three paths) it is
`corank = 12 − Σ_i dim S_i + dim(S_1 ∩ S_2 ∩ S_3)`, i.e. `ρ` **is** the
triple-intersection dimension there.

*Exact, per frame:* the identity is asserted at all **400** instances of
*Step O31*; the theta form's `ρ = Σ_i min(ℓ_i,6) − 12` (the generic
triple-intersection value) holds at **all 978** measured `c(F°) ≤ 2`
supports (`sigz.py --theta`).

---

#### Step O33 — (OC-37): the class-shape stress floor — `slack ≥ 0`, with equality only at cycles and bouquets

> **(OC-37)** *(proven; the class input is §(K-Λ) **(Λ4)(iii)**, cited, plus
> girth ≥ 7, which is (Λ4)'s own first consequence)* Let `G` be a class shape
> (tight, `def(G) = 0`, `hnoRigid`, `hcard`) and `F ⊊ G` a **proper**
> subgraph with min degree ≥ 2. Then
>
> **(i)** `slack(F) ≥ 0`;
> **(ii)** `slack(F) = 0` **iff** `n(F) = 1` — iff `F` is a cycle, or a
> bouquet of cycles meeting in a single body (and then every one of those
> cycles has length ≥ 7);
> **(iii)** hence, by (OC-36), a self-stress of `F` at a pencil placement
> requires `Σ_Q δ_Q + ρ_F ≥ slack(F) + 1`, which is **≥ 1** for a
> cycle/bouquet and **≥ 2 for every other topology, thetas included**.
>
> **Consequently no `H`-supported self-stress at a class shape is
> combinatorially forced**, and `{σ = 0} = ∅` **cannot** be certified by any
> count: the counting route to a disproof of `hK` at a class shape is dead.

*Proof.* `F` has min degree ≥ 2, so every degree-2 vertex of `G` inside `F`
brings both its neighbours: `F` is a union of whole branches, i.e. a
**branch subset** of `E(G°)`, and it is proper. `slack` and `f` are additive
over components, so assume `F` connected. Write `s_Q := (6 − ℓ_Q)^+`; then
`slack(F) = 6(n − 1) − Σ_Q s_Q`, so (i) is `Σ_Q s_Q ≤ 6(n − 1)`.

Let `F_S` be the union of the **short** paths (`ℓ_Q ≤ 5`, i.e. `s_Q ≥ 1`).
Girth ≥ 7 ((Λ4)'s first consequence) says every cycle of `G` has length ≥ 7,
so **no loop of `F°` is short**: `F°_S` is loopless. Let its components be
`K_1, …, K_r`, with `n_i` nodes, `m_i` paths and `c_i = m_i − n_i + 1`.

- If `c_i ≥ 1`: `K_i` is itself a proper branch subset with cycle rank `c_i`
  (cycle rank is invariant under the topological reduction — merging a
  degree-2 node deletes one node and one path), so **(Λ4)(iii)** gives
  `Σ_{Q ∈ K_i} ℓ_Q ≥ 6c_i + 1`, whence
  `Σ_{K_i} s_Q = 6m_i − Σℓ_Q ≤ 6(m_i − c_i) − 1 = 6(n_i − 1) − 1`.
- If `c_i = 0`: `K_i` is a tree, `m_i = n_i − 1`, and `s_Q ≤ 5` gives
  `Σ_{K_i} s_Q ≤ 5(n_i − 1) ≤ 6(n_i − 1) − 1` (a tree component with a path
  has `n_i ≥ 2`).

Summing, `Σ_Q s_Q ≤ 6(Σ_i n_i − r) − r ≤ 6(n − 1) − 1` whenever `r ≥ 1`
(the `K_i` node sets are disjoint subsets of `F°`'s nodes, and `r ≥ 1`
contributes the `−6 − 1`). If `r = 0` there are no short paths at all,
`Σ_Q s_Q = 0` and `slack = 6(n − 1)`. That proves (i), and (ii): `slack = 0`
forces `r = 0` **and** `n = 1`, i.e. all paths are loops of length ≥ 6, and
girth upgrades ≥ 6 to ≥ 7. Conversely a cycle/bouquet has `slack = 0` by the
same computation. (iii) is (OC-36). ∎

**What this is, in one line: the general form of the `ℓ₁ + ℓ₂ ≥ 7` bound the
gap map's `P21` row already carries.** That bound is (OC-37)'s inequality at
the single sub-multigraph `F_S` = a parallel pair — the `c_i = 1`, `n_i = 2`
case — and §(K-dom) **(D3)**'s `k ≥ 4` is the same instance at the split
chain plus a companion. (OC-37) says the *whole* family of such exclusions is
one inequality and it never fails: **there is no sub-multigraph anywhere in
`hK`'s habitat whose count forces a pencil self-stress.** The theta case the
dispatch named is the sub-case `n = 2, m = 3`, where (OC-37) reads
`Σ_i min(ℓ_i, 6) ≥ 13` — and the driver's measured minimum over the pool is
exactly **13**, so the bound is tight, not slack.

**Which theta lengths remain uncovered: none, at the level of the count.**
The honest form of the dispatch's question. The *combinatorial* exclusion is
uniform in the length data — every admissible triple satisfies
`Σ min(ℓ_i,6) ≥ 13 > 12`, whatever it is — so no length triple is
"uncovered" by (OC-37). What is *not* closed is not indexed by lengths at
all: it is the single geometric input of *Step O36*, and it is the same
one-point-decidable object as (OC-8)'s residue.

*Exact, and this mode ENUMERATES rather than samples:* over **2614** class
shapes — the exhaustive `G° = K4` class stratum (877), `outer.sweep_shapes`'s
exhaustive `theta3` / `K4` / `K4+par` rows, three `|V°| = 5` rows capped at
**150 shapes each (cap disclosed)**, and the five named habitats — at every
eligible split, **every** branch-subset support of `H` with min degree ≥ 2
was enumerated with **no cap on the supports and no rng**: **215 906**
instances. `slack < 0`: **0**. `slack = 0`: **83 634**, and **every single
one has `n(F°) = 1`** — 0 counterexamples to (ii). Distribution of `slack`:
`0:83634, 1:19804, 2:15376, 3:28164, 4:30336, 5:22254, 6:9144, 7:3980,
8:2118, 9:822, 10:228, 11:44, 12:2` (`sigz.py --slack`). The (Λ4)(iii)
half is separately asserted directly: over the 882-shape pool,
**22 169** proper cyclic branch subsets, `max f(V(F)) = −1` (attained), and
`f(V(H)) = −3` at **every** eligible split of **every** shape
(`sigz.py --budget`).

---

#### Step O34 — (OC-38): `P21`'s mechanism is one unit short of the habitat — and it is a `plane_basis` artifact

> **(OC-38)** *(the ledger clause proven-informally and asserted per seed; the
> location clause is a **set equality measured on the landed window**)*
> `P21` **fails `hnoRigid`** — it is a **(K-res) residual, not a tight class
> member** (§(K-pure) *P4*/*P7*, gap map `P21` row). Every figure in this step
> carries that qualifier. Then:
>
> **(i) The ledger.** §(K-flank) *F5(d)*'s recorded theta support
> `{12, 13, 23a, 23b}` (12 edges) has `n = 2` nodes and topological path
> lengths `(3, 3, 6)`, hence `f(V(F)) = 0` and **`slack = 0` at `n = 2`** —
> which (OC-37)(ii) forbids at a class shape. Its `σ = 1` decomposes as
> `(slack, Σδ, ρ) = (0, 1, 0)`: **one** unit of chain-span deficiency, on the
> length-6 topological path `2 — 1 — 3`, whose span is **5** instead of 6.
> On the whole of `H` the same seed reads `(f, Σ(ℓ_Q − dim S_Q), ρ) =
> (−3, 4, 0)` with path data `(ℓ, dim S) = (3,3), (3,3), (9,6), (6,5)` — the
> length-9 path's three units being *structural* (`dim S ≤ 6`).
>
> **(ii) Why it cannot cross.** The single inequality that fails at `P21` is
> `(Λ4)(iii)` at the short-path pair `{23a, 23b}`: `3 + 3 = 6 < 7`. That pair
> is a rigid `C₆`, which is exactly `hnoRigid` failing. Inside the class the
> same support has `slack ≥ 1`, so it needs **`Σδ + ρ ≥ 2`**. The recorded
> mechanism supplies **1**. It is **quantitatively one unit short**, and the
> missing unit is precisely the one `hnoRigid` buys.
>
> **(iii) Where the one unit comes from, located.** On the landed window —
> `G′`-chart seeds 101…140 of `widened.place_pencil_general`, target rank of
> `G′` required, the sampler and window §(K-flank) *F5(d)* used — there are
> **35** valid seeds and **5** with `σ = 1` (reproducing the recorded
> 30/5/5), and those five are **EXACTLY** the five seeds at which
> `localtest.plane_basis` degenerates at hub `c` (`nrm[c][2] = 0`): a **set
> equality**, not a containment. At each, `repin.coincident_hinges` reports
> exactly one coincident pair, `(c, 113, 115)` — the hub-`c` ends of branches
> `12` and `13` — which is precisely what drops the length-6 path's span from
> 6 to 5. So the arc's **only** exhibited instance of the `{σ = 0}`-failure
> mechanism is produced by the degenerate in-plane sampler basis that
> `notes/scripts/README.md` §4 convention 1 / *Harness debt* item 4 /
> §(K-out) **(OC-7)** name.
>
> **(iv) What survives and what does not.** The five points are **legal**
> chart points: `flanks.nondeg_conjuncts` is green at all five (a coincident
> hinge pair is not excluded by `IsNondegPencilRealization` — (OC-7)'s own
> finding). So **(OC-28)(iv)'s claim that `{σ = 0}` is a *proper* open stands
> — the complement is nonempty and contains legal chart points.** What does
> **not** survive is its *quantitative reading*, "so the complement of
> `{σ = 0}` is not thin in the sampler's rational range": at `P21` the
> complement **is** the coincidence locus, a proper closed subset, and the
> ≈ 14 % hit rate is a property of `plane_basis`, not of the variety. Under
> the composite gate `repin.star_generic`, **360** gate-accepted seeds
> (cap **500**, disclosed) give `σ = 0` at **every one**; the first 60 of them
> are all at target rank of `G′`, so the gate is not selecting away the
> stratum.

*Proof of (i)/(ii).* (i) is (OC-36) read at the measured spans, plus the
`(3,3,6)` reading of the recorded support (branches `12` and `13` meet at hub
`1`, which has `F`-degree 2 and is therefore absorbed into one length-6
topological path — hub `1`'s third branch, `14`, is outside the support).
For (ii): `Σ_F ℓ = 12 = 6c(F)`, so `f(V(F)) = 0`, which (Λ4)(iii) excludes at
a class shape; the *only* violated instance is the `{23a, 23b}` pair, whose
`Σℓ = 6 < 7`. ∎ (iii) and (iv) are measurements; see *Verification*.

**This is a harness finding, not only a mathematical one, and it is stated
here because the dispatch's premise rested on it.** §(K-flank) *F5(d)*'s
`dim R_a = 0` stratum is the arc's first and only exhibited "target-rank seed
that fails at every placement". Its *mathematical* content is untouched — the
five seeds are legal, `dim U = 1`, and (K-tight) *Step 2.3*'s prediction
holds at them, exactly as recorded. What changes is the reading of its
**genericity**: it is a codimension-≥ 1 phenomenon that a known-degenerate
sampler reaches often, and any future quotation of "5 of 35" must say so.
*Recorded for the coordinator to adjudicate, not acted on here* — this pass
edits nothing.

*Exact, per seed:* `sigz.py --p21`; the ledger `(0,1,0)` / `(−3,4,0)` is
asserted against the direct rigidity-matrix corank at each of the five, and
the reduction (OC-35) is re-asserted there (the `corank ≥ 1` direction of
*Step O31*'s 400 instances is exactly this leg).

---

#### Step O35 — (OC-39): the hunt, run — `{σ = 0} ≠ ∅` is **certified**, not sampled, at 3368/3368 class pairs

> **(OC-39)** *(a per-pair proof, not a rate; the pool's coverage boundary is
> stated inside the claim)*
>
> **(i) The boundary, first.** `{σ = 0}` is Zariski-**open** in the chart
> ((OC-23) + (OC-17)) and the chart is **irreducible** (§(K-chart)
> **(CH-1)(a)**), so `{σ = 0} = ∅` is a **closed** condition, equivalent to
> `corank R(H) ≥ 1` at the *generic* point. Therefore: **a finite sample can
> REFUTE it but can never establish it.** One rational chart point with
> `corank R(H) = 0` is a *complete* certificate that the shape is not a
> counterexample ((OC-24)(i)); a shape at which every sampled seed has
> `σ > 0` is **"not found under cap C"** and is **not** a hit. A hit needs an
> argument or an exhaustive, uncapped chart-level certificate.
>
> **(ii) No hit.** Over **882** class shapes — the **exhaustive** `G° = K4`
> class stratum (877, `kslidecomb.shape_ok`, no cap) plus the five named
> habitats — and **every** eligible split, **3368 of 3368** (shape, split)
> pairs carry an exact-ℚ **full-row-rank** certificate for `R(H)`
> (`rank = 5|E(H)|`, asserted, not inferred) at a `repin.star_generic`-gated
> chart point of `G`'s own chart; by **(OC-28)(i)** that point's `H`-part is
> an `H`-part of every eligible split's `G′`-chart, and the first **40**
> pairs were additionally cross-checked against a gated placement of `G′`'s
> **own** chart, agreeing at 40/40. So `{σ = 0} ≠ ∅` at every pair, and by
> (i) each of those is a **per-pair proof** that the disproof does not occur
> there — a stronger statement than a tally.
>
> **(iii) And no forced stress anywhere wider.** (OC-37)'s enumeration
> (*Step O33*) covers **2614** class shapes and **215 906** supports with no
> cap on the supports and finds `slack < 0` **zero** times. Since
> `slack(F) < 0` would give `corank R(F) ≥ −slack(F) > 0` at **every** pencil
> placement — a genuine, argument-level, sample-free disproof of `hK` at that
> shape ((OC-24)(ii)) — this is the search for a hit conducted in the one
> currency that could have produced one, and it came back empty **by a
> theorem**, (OC-37), not by exhaustion.

*Exact:* `sigz.py --hunt` (3368/3368, 40/40 cross-checks, 0 unresolved),
`sigz.py --slack` (215 906 instances, 0 negative). Both figures are witness
counts with their pools stated; neither is a rate.

---

#### Step O36 — (OC-40): what a hit would now have to look like, and the one input that is measured rather than proved

> **(OC-40)** *(scope statement; the classification clause is proven, the
> genericity clause is **measured per shape** and is the named residue)*
>
> **(i) The `c(F°) ≤ 2` classification is complete.** A support with
> `c(F°) = 2` is a theta, a dumbbell or a figure-eight. In a dumbbell,
> Kirchhoff at either node forces the connecting path's `ψ` to **0** (its two
> loops enter with cancelling signs), and in a figure-eight the node
> condition is vacuous; in both cases the system **decouples** and
> `corank R(F) = Σ_{loops} (6 − dim S_{loop})`, the `c = 1` answer twice.
> So every `c ≤ 2` mechanism is one of exactly two things: a **cycle** of
> length ≥ 7 whose pencil lines span ≤ 5 (one geometric unit, `slack = 0`),
> or a **theta** needing two (`slack ≥ 1`).
>
> **(ii) The one remaining input, named.** After (OC-37) a hit needs
> `Σ_Q δ_Q + ρ_F ≥ slack(F) + 1` to hold **identically on the chart** for
> some single support `F` (identically, because `{σ > 0}` is closed and the
> chart irreducible). Both currencies are **codimension-≥ 1 conditions on the
> chart** — a `δ_Q ≥ 1` is a determinantal vanishing among a path's hinge
> lines, and `ρ_F ≥ 1` is one among the perp spaces at the nodes. Whether
> either is *forced* at some class shape is the residue, and it is exactly the
> nonemptiness of an open condition on an irreducible chart: **one-point
> decidable per shape**, hence in the **same object class as (OC-8)'s
> residue** ((OC-22)) and §(K-ann) **(ANH-R1)**. It is **measured free** at
> every shape probed: `dim S_Q = min(ℓ_Q, 6)` at **444/444** topological
> paths, lengths 1–15, over 17 shapes; `corank = 0` at **978/978** measured
> `c ≤ 2` supports; and the 3368/3368 certificates of (OC-39)(ii).
>
> **(iii) So the honest shape of the negative.** *Proven:* the counting route
> is dead, uniformly, at every class shape and every support ((OC-37)); the
> theta mechanism in particular needs two geometric units where the only
> recorded instance supplies one ((OC-38)). *Not proven:* that the geometric
> conditions are never forced — i.e. **(a₂) is NOT free unconditionally**.
> The dispatch's second outcome is delivered **for the counting half in
> full and for the geometric half only per shape**, so (OC-28)(iii)'s
> conditional reduction of the `s₀` half to §(K-grid) **(GR-10)** remains the
> best *uniform* statement, unchanged in status.

*Proof of (i).* Orient each path from start to end node. In a dumbbell with
nodes `u`, `w`, loops `L_u`, `L_w` and connector `P`, Kirchhoff at `u` reads
`ψ_{L_u} − ψ_{L_u} + ψ_P = 0`, i.e. `ψ_P = 0`; likewise at `w`. So the
system is `ψ_P = 0` together with two unconstrained loop variables, giving
`corank = (6 − dim S_{L_u}) + (6 − dim S_{L_w})` and
`ρ_F = 6 − dim S_P^⊥ = dim S_P`, consistent with (OC-36). In a figure-eight
`n = 1` and both loops cancel at the single node, so `rank K_F = 0`,
`ρ_F = 0` and the same formula holds. ∎

---

#### Verification (Steps O31–O36)

`notes/scripts/w4/sigz.py` (new, untracked at draft time; exact ℚ, stdlib
only; a `w4/` leaf **beside** the existing kernel-(K) leaves, importing
downward only and reimplementing nothing): `exactcore`'s `rank` /
`nullspace` / `wedge2` / `hat` / `neighbors`; `kbare_common.verts_of`;
`pencil_escape.build_rigidity`; `nogood_subdiv`'s `deficiency` /
`branch_decomposition`; `dominance.branch_pmap`; `widened`'s
`place_pencil_general` / `orient` / `removeV` / `splitOff`; `repin`'s
`star_generic` / `span_basis` / `coincident_hinges`; `pitch.paths_graph`;
`kslide.no_rigid_branch_union`; `kslidecomb`'s `shape_data` / `shape_ok`;
`flanks.P21_SPECS`; `ltwo.branch_subsets`; `outer`'s `split_data` /
`eligible_splits` / `sweep_shapes`.

**One new local primitive, flagged as a `Divergences` candidate.**
`sigz.topo_reduce` is **not** `nogood_subdiv.branch_decomposition` and must
not be merged with it: `branch_decomposition` reduces `G` at *`G`-hubs*
(degree ≥ 3 **in `G`**), whereas every statement here needs the reduction of
a **subgraph** `F` at *`F`-degree-≥ 3* vertices — a `G`-hub of `F`-degree 2
must be absorbed into a longer topological path, and that absorption is
exactly where `P21`'s length-6 path (and its span drop) lives. Same-name-
different-semantics, so a different name.

| mode | ~time | asserts |
|---|---|---|
| `--reduce` | 72 s | (OC-35)/(OC-36): direct corank == flow corank == `f + Σδ + ρ` at 400 (shape, seed, support) instances, 10 of them with corank ≥ 1 (the `P21` leg) |
| `--spans` | 1 s | `dim S_Q = min(ℓ_Q, 6)` at 444/444 topological paths, `ℓ = 1..15`, 17 shapes; 0 drops |
| `--budget` | 2 s | (Λ4)(iii) on the 882-shape pool: 22 169 proper cyclic branch subsets, `max f = −1`; `f(V(H)) = −3` at every eligible split |
| `--slack` | 46 s | **(OC-37), enumerated:** 2614 shapes, 215 906 supports, `slack < 0` **0 times**, `slack = 0` **only** at `n(F°) = 1` (83 634/83 634) |
| `--theta` | 2 s | (OC-37) at `c ≤ 2`: 978 supports with their budgets tabulated by topology and theta length triple; `ρ = Σ min(ℓ_i,6) − 12` at every theta; min `Σ min(ℓ_i,6) = 13`; 0 with corank > 0 |
| `--p21` | 148 s | **(OC-38):** 35 valid window seeds, 5 with `σ = 1`, ledger `(0,1,0)` at each, **set equality** with `nrm[c][2] = 0`; 360 `star_generic`-gated seeds (cap 500) all `σ = 0` |
| `--hunt` | 455 s | **(OC-39):** 3368/3368 pairs with a full-row-rank certificate; 40/40 `G′`-chart cross-checks; 0 unresolved |

**`--validate` does not fit a 600 s foreground budget** (measured 693 s and
747 s on two runs),
so it runs as the **two-invocation split** below — the
`flanks --limit` / `yloc --coll` precedent, recorded in
`notes/scripts/README.md` so a successor plans around it:

```
python3 notes/scripts/w4/sigz.py --reduce --spans --budget --slack \
    --theta --p21                                   # measured 239 s / 292 s
python3 notes/scripts/w4/sigz.py --hunt             # measured 454 s / 455 s
```

**Caps, disclosed in one place.** `--reduce` samples 2 seeds × 6 `K4`-stratum
shapes + 5 named + the five pinned `P21` seeds; `--spans` 12 `K4` shapes + 5
named, 1 gated placement each; `--theta` 40 `K4` shapes + 5 named, 1 gated
placement each; `--slack` **no cap on supports**, and its `|V°| = 5` rows are
capped at 150 shapes each (the `theta3`/`K4`/`K4+par` rows and the 877-shape
`K4` stratum are exhaustive); `--p21` window 101…140 (the landed one) plus a
500-seed gated cap; `--hunt` up to 4 gated placements per shape, pool
exhaustive over the `K4` stratum. Every rng is `random.Random` from the
printed literal `20260819`; every sampled placement is gated by
`repin.star_generic` (not `star_span_ranks`) except `--p21` leg (a), whose
whole subject is the coincidence and which reports it.

---

#### Confidence verdict (Steps O31–O36)

- **(OC-35)** the branch-flow reduction — **proven** (elementary, no
  genericity), and driver-checked against the full rigidity matrix at
  400/400 instances including 10 with a stress.
- **(OC-36)** the degeneracy-budget identity — **proven** (algebra on
  (OC-35)); asserted at the same 400.
- **(OC-37)** the class-shape stress floor `slack ≥ 0`, equality iff
  `n = 1` — **proven-informally**, its only class input being §(K-Λ)
  (Λ4)(iii) (itself proven-informally) and girth ≥ 7; the headline sentence
  is separately **enumerated** at 215 906 supports over 2614 shapes with 0
  counterexamples to either clause. **The consequence — no `H`-supported
  self-stress at a class shape is combinatorially forced, so the counting
  route to a disproof is dead — is PROVEN at the same confidence as
  (Λ4)(iii).**
- **(OC-38)(i)/(ii)** `P21`'s ledger and the one-unit gap —
  **proven-informally**, asserted per seed. **(OC-38)(iii)** the location as
  a `plane_basis` artifact — a **measured set equality** on the landed
  40-seed window (5 = 5), plus 360 gated seeds with no jump under a
  disclosed cap of 500: strong, and **not** a proof that
  `{σ > 0} ⊆ {coincident hinge at c}` as varieties. **(OC-38)(iv)**
  (OC-28)(iv)'s *proper-open* claim **stands**; its *thinness* reading is
  **refuted**.
- **(OC-39)** no hit — **the negative is as strong as it can be made**: each
  of the 3368 pairs is a per-pair *proof* (one-point certifiable, (OC-24)(i)
  + (CH-1)(a)), not a sample; and the pool is exhaustive over the `K4`
  stratum. It is **not** a class-uniform proof of (a₂), and this pass does
  not claim one.
- **(OC-40)** the `c ≤ 2` classification — **proven**; the genericity input
  — **open, measured free at every shape probed**, one-point decidable per
  shape.
- **The hunt's own verdict: NOT A HIT.** No class shape with `{σ = 0} = ∅`
  was found, and the only mechanism the arc records is proven unable to force
  one. **No gap-map status moves** — `{σ = 0}`'s row, (OC-8), (GR-15), class
  uniformity and `hK` all stay exactly where they were.

#### What would change this (Steps O31–O36)

1. **For (OC-35)/(OC-36):** an error in the constancy step (a degree-2 body
   whose two hinge lines are equal — then `S_Q` is smaller but the argument
   is unchanged, and the driver's 400/400 includes such frames at `P21`), or
   in the `rank K_F ≤ 6(n−1)` bound (it is the sum-zero image; a disconnected
   `F°` would need the per-component form, which `topo_reduce` supplies).
2. **For (OC-37):** an error in the (Λ4)(iii) application — the load-bearing
   step is that a **component of the short-path sub-multigraph** is itself a
   proper branch subset, which needs `F ⊊ G` (used) and cycle-rank invariance
   under topological reduction (used, and re-derived in the proof). A class
   shape with a support at `slack < 0` would refute it outright and would be
   a **PENCIL event**; `--slack` is the enumerating search for exactly that,
   and it is the cheapest thing on the board to widen (pure combinatorics, no
   placements — a `|V°| = 6` sweep is the obvious next cut, and the
   `|V°| = 5` rows are the only capped ones).
3. **For (OC-38)(iii):** a `star_generic`-accepted `P21` placement with
   `σ > 0`. 360 gated seeds (cap 500) produce none; a wider cap, or a
   *constructed* coincidence-free placement with a dependent length-6 chain
   span, would move it from "measured" to "refuted".
4. **For (OC-39):** a class shape at which every gated placement has
   `σ > 0` — which would still be only "not found under cap", per (i), and
   would need an argument to become a hit. The pool's real boundary is
   `|V°| ≥ 5` with lengths beyond the capped rows.
5. **For (OC-40)(ii):** a class shape and a cycle of length ≥ 7 whose pencil
   lines are *forced* dependent, or a forced excess triple intersection at a
   theta. Either is a hit. Neither is exhibited, and both are
   codimension-≥ 1 conditions witnessed nonempty-complement at every shape
   probed.
6. **Deliberately not attempted**, so a successor does not assume otherwise:
   the target-rank half of input (a) — **(a₁) is OSCHU's this wave**;
   (OC-19) input (c); chart irreducibility (§(K-chart) (CH-1)(a), **cited**);
   the `p⁺` push, the coupled two-end slide, every §(K-frame) *What would
   change this* item (ii)–(iv); any counting/matroid route to (OUT)'s
   hypothesis ((OC-3)); and re-running `flanks.py --rzero` (its 30/5/5 figure
   is **cited**; `--p21` re-derives the window only to attach the new
   ledger to it, and says so).

#### `(a₁)`-relevant by-products, reported and NOT developed (OSCHU's target this wave)

Two, both falling out of (OC-35) and neither pursued: *(a)* the same
branch-flow bookkeeping applies verbatim to the **welded** systems §(K-out)
uses for `W₁`/`R₁` — welding is an equality row, so it merges two nodes of
`F°` and the flow statement survives — which would give (OC-18)'s
`H/X`-rigidity criterion a `G°`-level form; *(b)* `D = {m(b) − m(c)}` is the
*dual* object to the flow (`dim D = 3 + σ` by (OC-25)(b)), so a `ρ_F`-style
Kirchhoff deficiency at the nodes of `H°` is what an (a₁) recipe would have
to control. Both are **findings, not results**, and are not developed here.

#### TERMINATION check (E1/E2/E3) — this direction's reading; firing is the coordinator's

**E1, E2, E3: all NO.**

- **(E1)** does not fire: no g-flank is exhibited, and nothing in this pass
  is on the `D = 0` / admissible-colouring line at all — §(K-grid) is
  untouched.
- **(E2)** does not fire: the direction's *target* was a disproof, and a MISS
  on a disproof direction is not "the target refuted or unprovable-as-posed
  with no successor left" — it is the **expected** outcome, and the input-(a)
  ledger leaves (a₁) (OSCHU's, this wave) and (a₂)-via-(GR-10) both
  open-with-a-named-dispatchable-attack. **The dispatch's own second outcome
  landed in its counting half**, which is a positive, not a refutation.
- **(E3)** does not fire, and **stays ARMED by GBAL's entry-5 HIT, neither
  fired nor disarmed** — its target is §(K-grid) ledger entry 1, (a′), which
  this pass does not touch.
- **The direction-A pivot rule did not trigger.** It fires on a HIT; there is
  none. Had `--slack` returned a single negative-slack support the rule would
  have fired, which is worth recording as the one place in this pass where it
  could have.

---

---

### Steps O25–O30 (2026-08-19, eighth fan-out, direction OSCHU) — input (a)'s target-rank half **(a₁)** given a **recipe for one of its two disjuncts and a one-determinant residue for the other**: the ambient 4-space of the Schubert condition is **§(K-out)'s own two hub pencils**, `M̂ ∧ W = L_b ⊕ L_c` ((OC-29)), whose Klein perp is the pencil `⟨C(M), C(bc)⟩` — so the bad set on the meet line is *exactly* the set of transversals of `M` and `bc` lying inside `D` ((OC-30)); at **every** target-rank chart point of the **whole graph `G`** the two hinge lines `C(vb) ∈ L_b`, `C(ac) ∈ L_c` come for free and force **`dim(D ∩ M̂ ∧ W) ≤ 2`** ((OC-31)), killing (OC-26)(ii)'s first disjunct outright, while a **third** such generator is **structurally unavailable** ((OC-32)); the surviving disjunct forces the **pitch form on `D` to be degenerate**, so `rank(Q|_D) = 3` at one target-rank `G`-point **implies input (a)** ((OC-33)). The **(a₂) re-keying is DONE** ((OC-34)): §(K-grid)'s 907 labelled shapes are **75** isomorphism classes and cover only **19** of §(K-out)'s **174**, but the remaining **155 are certified directly, 155/155**, so the `s₀` half is free at **all 174 — and *without* (GR-10)**; a re-keyed per-class census carries a **174/174** one-point witness of input (a). **Input (a) stays OPEN as a class-uniform statement; no gap-map status moves.**

Driver `notes/scripts/w4/oschu.py` (new this pass; imports `zneq`, `ocon`,
`outerline`, `outer`, `grid`, `gridwit`, `closure`, `dominance`, `kslide`,
`widened`, `repin`, `pitch` **read-only** and modifies nothing); labels
**(OC-29)–(OC-34)**, Steps **O25–O30**. Everything cited that this pass did not
mint is qualified per `notes/Pencil-labels.md` clause L3: **(OUT)**,
**(Λ0d)** are §(K-Λ)'s; **(OC-1)**, **(OC-3)**, **(OC-8)**, **(OC-17)**–**(OC-28)**
are this section's own earlier items; **(K-tight)** *Step 2*'s items are
§(K-tight)'s; **(CH-1)**/**(CH-2)** are §(K-chart)'s; **(GR-5)**/**(GR-9)**/**(GR-10)**/**(GR-15)**
are §(K-grid)'s; **(AC-2)**/**(AC-4)**/**(AC-7)** are §(K-clos)'s; **(FR-2)**/**(FR-3)**/**(FR-4)**
are §(K-frame)'s; **(I4)** is §(K-ind)'s; **(ANH-R1)** is §(K-ann)'s;
*F5(d)* is §(K-flank)'s. POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A /
POOL-W / POOL-SL / POOL-OV / POOL-OC / POOL-OZ / POOL-ZF / POOL-ZQ / POOL-ZN /
POOL-ZT / POOL-ZR are earlier pools of this section and **nothing below is
aggregated with them**; POOL-G and POOL-S are pinned and are neither re-sampled
nor extended.

Standing notation is §(K-out)'s plus *Steps O19–O24*'s (`orient`'s chain
`b — v — a — c`; `G′ = G − v + ab`; `H = G − v − a`; `σ := corank R(H)`;
`Z` the hard-stratum target-rank locus of `G′`'s chart; `M = Π(b) ∩ Π(c)` with
2-dimensional cone `M̂`; `D := {m(b) − m(c) : m ∈ Mot(H)}`; `U_H = D^⊥`), plus:

- `W := ⟨pt(b)^, pt(c)^⟩` — the hub line's 2-space; `C(bc) := pt(b)^ ∧ pt(c)^`.
- `T := D^{⊥_B} = {u : B(u, d) = 0 ∀ d ∈ D}` — **the wrenches `H` transmits
  between `b` and `c`**; `dim T = 3 − σ`.
- `Π := ⟨C(M), C(bc)⟩` — the 2-space spanned by the meet line and the hub line.
- `K := D ∩ (M̂ ∧ W)`, and `dimK := dim K`; `L_h` is (OC-3)'s pencil of lines
  through `pt(h)` inside `Π(h)` (`outerline.line_pencil`); `β_h = Λ²Π̂(h)` is
  (OC-20)'s panel line space.

Six things, in the order they change the reading of (a₁).

- **(OC-29) — the ruling dictionary: the Schubert 4-space is `L_b ⊕ L_c`, and
  its Klein perp is `⟨C(M), C(bc)⟩`.** `M̂ ∧ W` is not a new object. Its two
  "row" rulings are §(K-out)'s **own** hub pencils — `L_b = M̂ ∧ pt(b)^`,
  `L_c = M̂ ∧ pt(c)^` — and `M̂ ∧ W = L_b ⊕ L_c`; `(M̂ ∧ W)^{⊥_B} = Π`, so
  `dimK = 1 + dim(T ∩ Π)` and **`dimK ≥ 1` always** (`3 + 4 − 6`). Two
  corollaries land the dictionary on landed objects: `β_h = ⟨C(M)⟩ ⊕ L_h`,
  hence `β_b + β_c = ⟨C(M)⟩ ⊕ (M̂ ∧ W)` is §(K-tight) *Step 2* item 5's
  5-space with `(β_b + β_c)^{⊥_B} = ⟨C(M)⟩` — that item's own `★r ∥ C(M)`
  criterion, re-derived; and `Q` restricted to `M̂ ∧ W` is the **determinant**
  of the `2 × 2` picture `M̂ ⊗ W`, so the **decomposables of `M̂ ∧ W` are exactly
  the transversals of `M` and `bc`**.
- **(OC-30) — the bad set on `M`, exactly, and (OC-26)(ii) by a second route.**
  With `pt(a) ∈ M`, `⟨C(ab), C(ac)⟩ = pt(a)^ ∧ W` is a ruling of the *other*
  kind, and (OC-25)(c) says the point is in `Z` iff `C(ab)`, `C(ac)` are
  independent **mod `D`**. Hence
  > `pt(a)` is bad ⟺ `K` contains a nonzero **decomposable** whose `M̂`-column
  > is `⟨pt(a)^⟩` ⟺ **`D` contains a line joining `pt(a)` to a point of the hub
  > line `bc`**,

  so the bad set is the image of `K`'s decomposables under `x ↦ x ∩ M`. The
  classification is complete: `dimK = 1` gives **no** bad point (generator
  nonsingular) or **one** (generator a line); `dimK = 2` gives **all** of `M`
  iff `K` is a ruling `M̂ ∧ w`, else **at most two** points; `dimK ≥ 3` gives
  **all**. That reproduces (OC-26)(ii) from a disjoint route *and* sharpens it:
  **off the all-bad case the bad set has ≤ 2 points**. All five cases are
  **constructed** (POOL-OQ) with 60 negative controls.
- **(OC-31) — `dimK ≤ 2` at *every* target-rank chart point of `G`, and the
  two distinguished rulings excluded.** In `G`'s **own** chart `v`'s only hub
  neighbour is `b` and `a`'s only hub neighbour is `c` (§(K-chart) (CH-2)
  stage 4), so `pt(v) ∈ Π(b)` and `pt(a) ∈ Π(c)` — and two distinct lines of the
  projective plane `Π(b)` always meet, so `C(vb)` is a transversal of `M` and
  `bc` **automatically**: `C(vb) ∈ L_b`, and symmetrically `C(ac) ∈ L_c`. With
  §(K-tight) *Step 2* item 1 at `Γ = G`, `x = v` and `corank R(G) = 0`,
  `D ⊕ ⟨C(ac), C(va), C(vb)⟩ = K⁶`; hence `dim(D + M̂ ∧ W) ≥ 5`, i.e.
  **`1 ≤ dimK ≤ 2`**, and `L_b ∩ D = L_c ∩ D = 0`. So **`hK` at one chart point
  of `G` kills (OC-26)(ii)'s `dimK ≥ 3` disjunct at every eligible split of that
  shape at once**, and the surviving bad case needs `K = M̂ ∧ w` with `w` on the
  hub line **distinct from both `pt(b)` and `pt(c)`**.
- **(OC-32) — and the bound is exactly what the method yields: a third
  generator does not exist.** `C(va)` is a transversal of `M` and `bc` at **no**
  legal `G`-chart placement carrying target rank: off the two hub points the
  transversal forces `pt(v) = pt(a)`, and at `pt(b)` (resp. `pt(c)`) it forces
  `C(va) = C(vb)` (resp. `C(va) = C(ac)`), collapsing (OC-31)'s triple. Both
  collapses are **CONSTRUCTED**, with the constructed placements' panel legality
  asserted, at 60 sites. So `dimK ≤ 2` is not a missing-argument artifact.
- **(OC-33) — the residue, in the arc's own object class: the pitch form on
  `D`.** A ruling inside `D` is a 2-dimensional totally Klein-isotropic
  subspace of the 3-space `D`, so it forces `rank(Q|_D) ≤ 2`, i.e.
  `D ∩ T ≠ 0`. Hence at a target-rank `G`-chart point
  > `rank(Q|_D) = 3` ⟹ **input (a) holds at that (shape, split)**,

  a single `3 × 3` determinant — `x₁`-free, `λ`-free, stratum-free, one-point
  decidable, and decidable *at a point the grid route already constructs*.
  Sufficiency is **not** necessity, twice, both **constructed**: `dimK = 3` with
  `rank(Q|_D) = 3` is all-bad (so (OC-31) is genuinely needed), and
  `rank(Q|_D) ≤ 2` with a one-point bad set exists.
- **(OC-34) — the (a₂) re-keying, DONE, and it changes the reading of
  "907/907".** Keyed by isomorphism class of the length-labelled hub multigraph:
  §(K-grid)'s census pool is **907 labelled shapes = 75 classes**; §(K-out)'s
  class-shape population is **1376 labelled shapes**, **1364** carrying a
  length-4 companion, in **174 classes**; and **only 19 of the 174** lie in
  §(K-grid)'s pool. (OC-28)(a)'s warning is therefore not a formality — it was
  a factor of nine. The gap is then closed **by construction, not by the
  transfer**: the 155 classes outside were run through §(K-grid)'s own
  certificate hunt and **155 of 155** carry a both-block tree-triple
  certificate (0 misses, no node-cap hit, class predicate asserted per shape).
  So the `s₀` half is free at **all 174 classes** — and, at a shape where the
  certificate is *exhibited*, **(GR-10) is not consumed at all**; only the
  *class-uniform* statement still needs it.

**Verdict, stated at the strength the work supports.** **Input (a) stays OPEN as
a class-uniform statement, and no gap-map status moves.** What changes is that
(a₁) is no longer a bare Schubert non-jump with no recipe: one of its two
disjuncts is **killed by a proof** wherever `hK` holds at a single chart point of
`G`, and the other is **implied by one determinant vanishing**. The honest
boundary: `rank(Q|_D) = 3` is measured at **570 of 570** chart points across
three pools and **174 of 174** isomorphism classes, and is **not proven** class-
uniformly; the cheapest route to it is the `⋆`-invariance argument of *Step O29*,
which stops on a **field** obstruction (§(K-clos) (AC-2)'s grids are `ℚ(i)`-only)
rather than on a missing idea.

---

### Step O25 — (OC-29): the ruling dictionary — `M̂ ∧ W = L_b ⊕ L_c`, and its Klein perp

> **(OC-29)** *(proven; asserted per frame)* At every chart point of `G′`
> satisfying (Λ0d) (`pt(c) ∉ Π(b)` and `pt(b) ∉ Π(c)`):
>
> **(i)** `L_b = M̂ ∧ pt(b)^`, `L_c = M̂ ∧ pt(c)^`, and
> `M̂ ∧ W = L_b ⊕ L_c`; moreover `Λ²K⁴ = ⟨C(M)⟩ ⊕ (M̂ ∧ W) ⊕ ⟨C(bc)⟩`.
>
> **(ii)** `(M̂ ∧ W)^{⊥_B} = Π = ⟨C(M), C(bc)⟩`, hence
>
> > `dimK = dim D − 2 + dim(T ∩ Π)`,  in particular `dimK = 1 + dim(T ∩ Π)` at
> > `σ = 0`, and **`dimK ≥ 1` always**.
>
> **(iii)** `β_h = ⟨C(M)⟩ ⊕ L_h` for `h ∈ {b, c}`; hence
> `β_b + β_c = ⟨C(M)⟩ ⊕ (M̂ ∧ W)` is 5-dimensional — §(K-tight) *Step 2*
> item 5's 5-space — and `(β_b + β_c)^{⊥_B} = ⟨C(M)⟩`, i.e. its Euclidean perp
> is `⟨★C(M)⟩`: that item's own `★r ∥ C(M)` criterion.
>
> **(iv)** identifying `M̂ ∧ W ≅ M̂ ⊗ W ≅ K^{2×2}` by
> `Σ x_{ij} P_i ∧ w_j ↦ (x_{ij})`, `Q|_{M̂ ∧ W} = λ · det` for a nonzero scalar
> `λ`. So the **decomposable** elements of `M̂ ∧ W` are exactly the rank-1
> pictures, i.e. the **transversals of `M` and `bc`**, and the totally isotropic
> 2-subspaces of `M̂ ∧ W` are exactly the two ruling families `q ∧ W` and
> `M̂ ∧ w`.
>
> **(v)** with `pt(a) ∈ M`, `⟨C(ab), C(ac)⟩ = pt(a)^ ∧ W` — a ruling of the
> `q ∧ W` family — and (OC-25)(c) reads: at `σ = 0` the point lies in `Z`
> **iff** `C(ab)`, `C(ac)` are linearly independent **modulo `D`**.

*Proof.* (i) `M ⊆ Π(b)` by definition of the meet line, and `pt(b) ∉ M` (else
`pt(b) ∈ Π(c)`, against (Λ0d)), so `M̂ ∧ pt(b)^` is 2-dimensional and every
nonzero element is a line through `pt(b)` lying in `Π(b)`. `L_b` is the *whole*
pencil of such lines, itself 2-dimensional, so the two coincide. `M̂ ∧ W` is
spanned by `M̂ ∧ pt(b)^` and `M̂ ∧ pt(c)^`; in the `M̂ ⊗ W` picture these are the
sets of matrices with row space inside `⟨pt(b)^⟩` resp. `⟨pt(c)^⟩`, which meet in
`0`, so the sum is direct and 4-dimensional. (Λ0d) gives `M̂ ∩ W = 0`, so
`M̂ ⊕ W = K⁴` and `Λ²K⁴ = Λ²M̂ ⊕ (M̂ ∧ W) ⊕ Λ²W` with `Λ²M̂ = ⟨C(M)⟩`,
`Λ²W = ⟨C(bc)⟩`.

(ii) `B(u ∧ u′, x ∧ y) = [u, u′, x, y]` up to the fixed scale, and a bracket
with three vectors from the 2-space `M̂` vanishes, so `B(C(M), M̂ ∧ W) = 0`;
likewise `B(C(bc), M̂ ∧ W) = 0`. As `dim(M̂ ∧ W)^{⊥_B} = 2` and `Π` is
2-dimensional (`B(C(M), C(bc)) = [M₀, M₁, pt(b)^, pt(c)^] ≠ 0` by (Λ0d)), the
perp **is** `Π`. So `K = D ∩ C(M)^{⊥_B} ∩ C(bc)^{⊥_B}`, whose dimension is
`dim D` minus the rank of the two functionals `B(C(M), ·)`, `B(C(bc), ·)` on
`D`, and that rank is `2 − dim(T ∩ Π)`. Finally `dim D + dim(M̂ ∧ W) = 7 > 6`,
so `K ≠ 0`.

(iii) `C(M) ∈ β_b` (`M ⊆ Π(b)`) and `L_b ⊆ β_b`, and `C(M) ∉ L_b` because `M`
misses `pt(b)`; dimensions `1 + 2 = 3 = dim β_b` give the decomposition.
`β_h^{⊥_B} = β_h` ((OC-20)), so
`(β_b + β_c)^{⊥_B} = β_b ∩ β_c = ⟨C(M)⟩` — the lines lying in both panels — and
`⟨·,·⟩ = B(·, ★·)` turns that into `⟨★C(M)⟩`.

(iv) On the basis `P_i ∧ w_j`, `B(P_0 ∧ w_1, P_1 ∧ w_2) = [P_0, w_1, P_1, w_2] =
−[P_0, P_1, w_1, w_2] ≠ 0`, `B(P_i ∧ w_j, P_i ∧ w_k) = 0` (repeated `P_i`), and
`B(P_i ∧ w_j, P_k ∧ w_j) = 0` (repeated `w_j`): the Gram matrix of `Q` is the
Gram matrix of `det` scaled by `−2[P_0, P_1, w_1, w_2]`. A 2-space of `K^{2×2}`
inside `{det = 0}` is a linear subspace of the Segre quadric, hence one of its
two rulings.

(v) `pt(a) ∈ M` gives `C(ab) = pt(a)^ ∧ pt(b)^` and `C(ac) = pt(a)^ ∧ pt(c)^`,
which span `pt(a)^ ∧ W`. (OC-25)(c) says the point is in `Z` iff the two
functionals `⟨·, C(ab)⟩`, `⟨·, C(ac)⟩` are independent on `U_H = D^⊥`;
`α C(ab) + β C(ac) ⊥ U_H` says exactly `α C(ab) + β C(ac) ∈ D`. ∎

**Why this is worth a label rather than a remark.** (a₁) was dispatched as a
Schubert condition on an *ad hoc* 4-space of `Λ²K⁴`. (i) identifies that 4-space
as the direct sum of the two objects this section has been about since
*Step O1* — the hub pencils `L_b`, `L_c` of (OC-1)/(OC-3), whose non-containment
in `R₁`, `R₄` **is** (OC-8) — and (ii)/(iii) put the obstruction in the same
2-space `⟨C(M), C(bc)⟩` whose first generator carries §(K-tight) *Step 2* item
5's combined-failure criterion. Everything below is a computation inside this
dictionary.

*Exact, per frame:* (i)–(v) asserted at **104/104** POOL-OS frames, and (i),
(ii), (iv) again at **292/292** POOL-OG and **174/174** POOL-OC2 points; (iv)
also on the synthetic frame of POOL-OQ (`λ = −2` there).

---

### Step O26 — (OC-30): the bad set on `M` is the set of transversals inside `D`

> **(OC-30)** *(proven; asserted per frame against ZNEQ's independent
> `ℚ[t]`-GCD route, and CONSTRUCTED at every attainable `dimK`)* Fix a chart
> point with `σ = 0` and let `B ⊆ M` be the set of `pt(a)` for which the point
> leaves `Z`. Then
>
> **(i)** `pt(a) ∈ B ⟺ K ∩ (pt(a)^ ∧ W) ≠ 0 ⟺` **`D` contains a line joining
> `pt(a)` to a point of the hub line `bc`**. Equivalently, `B` is the image of
> the nonzero **decomposable** elements of `K` under `x ↦ x ∩ M`.
>
> **(ii)** the complete classification, over the chart's own field:
>
> | `dimK` | shape of `K` | `B` |
> |---|---|---|
> | 1 | generator nonsingular (`Q ≠ 0` on it) | **∅** |
> | 1 | generator decomposable | **1 point** |
> | 2 | a ruling `M̂ ∧ w` | **all of `M`** |
> | 2 | otherwise | **≤ 2 points**, and `∅` exactly when `det\|_K` is anisotropic over the field |
> | ≥ 3 | — | **all of `M`** |
>
> **(iii)** hence `B = M ⟺ dimK ≥ 3` **or** `M̂ ∧ w ⊆ D` for some `w ∈ W`
> ((OC-26)(ii), by a disjoint route), and — the new half — **off that case
> `|B| ≤ 2`**, with `B = ∅` exactly when `K` carries no decomposable.

*Proof.* (i) is (OC-29)(v) plus the observation that `pt(a)^ ∧ W ⊆ M̂ ∧ W`, so
the failure of independence mod `D` happens inside `K`; and every nonzero
element of `pt(a)^ ∧ W` is rank-1 in the `M̂ ⊗ W` picture, hence decomposable by
(OC-29)(iv) — a **line** through a point of `bc` meeting `M` at `pt(a)`.

(ii) In the picture, `pt(a)^ ∧ W = \{q v^{\mathsf T}\}` for `q` the coordinate
vector of `pt(a)^`, i.e. the matrices with column space `⟨q⟩`. `dimK = 1`: the
generator lies in some `q v^{\mathsf T}` iff it is rank 1, and then `q` is its
column space — one point. `dimK = 2`: `det|_K` is a binary quadratic form; if it
vanishes identically then `K` is a ruling, and a ruling `M̂ ∧ w` (fixed *row*
space) contains a matrix of column space `⟨q⟩` for **every** `q`, whereas a
ruling `q₀ ∧ W` contains one only for `q = q₀`; if `det|_K ≠ 0` its projective
zeros are ≤ 2 points, each contributing one column space. `dimK = 3`: `K` is a
hyperplane `{tr(A^{\mathsf T}X) = 0}` and for each `q` the 2-space
`\{q v^{\mathsf T}\}` meets it, so every `q` is bad — **whether or not `A` is
singular**, which is why the single-containment reading (OC-26) first derived is
false and why (iii)'s first disjunct is needed. `dimK = 4` is trivial.

(iii) is (ii) read off, plus `dimK ≥ 1` from (OC-29)(ii). ∎

**Read against ZNEQ, which this both confirms and sharpens.** (OC-26)(ii) is the
`B = M` row of the table, and this pass re-derives it without a `ℚ[t]` GCD — the
two routes are asserted equal at every frame. What is new: the *whole* bad set,
not just the all-bad case. In particular (OC-26)(iii)'s "`D ∩ (M̂ ∧ pt(b)^) ≠ 0`
gives exactly one bad point" is the `dimK = 1` decomposable row with
`q ∧ W`-column on `L_b`, and the previously unnamed case
`dimK = 2, det|_K` anisotropic — **`B = ∅` over `ℚ`, two points over `ℚ(i)`** —
is a genuine field dependence: the bad set is not a field-neutral object, though
`B = M` is (both disjuncts of (iii) are).

*Exact, per frame (POOL-OS).* At **104 of 104** guard-accepted chart points
(all with `σ = 0`): `dimK = 1`, `B = ∅`, `rank(Q|_D) = 3`, no ruling in `D`, and
ZNEQ's three-minor `ℚ[t]` GCD of degree **0** — the two routes agreeing at every
frame, and each frame's predicted goodness of the *sampled* `pt(a)` asserted
against its actual `Z`-membership.

*The must-reject constructions (POOL-OQ, `random.Random(20260820)`; README §4
convention 6).* All **six** attainable configurations built by hand and each
asserted to produce exactly the table's row: `dimK = 1` nonsingular → `B = ∅`;
`dimK = 1` rank-1 → 1 point; `dimK = 2` ruling → all of `M`, with
`rank(Q|_D) = 2`; `dimK = 2` anisotropic over `ℚ` → `B = ∅` over `ℚ`;
`dimK = 3` with **no** ruling → all of `M` with `rank(Q|_D) = 3` (ZNEQ's Case C
recovered from the classification instead of assumed); and `rank(Q|_D) ≤ 2` with
**no** ruling → 1 point (the (OC-33) separation). **`dimK = 0` is not a case**:
`dim D + dim(M̂ ∧ W) = 7`. **Negative control:** 60 random 3-spaces, every one at
`(dimK, B, ruling, rank(Q|_D)) = (1, ∅, no, 3)`.

---

### Step O27 — (OC-31): `dimK ≤ 2` at every target-rank chart point of `G`

> **(OC-31)** *(proven-informally, citing §(K-tight) *Step 2* item 1 and
> §(K-chart) (CH-2); every conclusion asserted per point)* Let a class (shape,
> split) be given and let `p` be a pencil chart point of the **whole graph `G`**
> at which `G` attains its Tay target (`rank R(G) = 6(|V(G)| − 1)`, i.e.
> `corank R(G) = 0`). Then, at the `H`-part of `p` — which by (OC-28)(i) is the
> `H`-part of a `G′`-chart point, so `D`, `M`, `W`, `K` are the same objects —
>
> **(i)** `σ = 0` ((OC-28)(ii));
> **(ii)** `pt(v) ∈ Π(b)` and `pt(a) ∈ Π(c)`, hence `C(vb) ∈ L_b` and
>   `C(ac) ∈ L_c` — both **transversals of `M` and `bc`**, with no hypothesis;
> **(iii)** `D ⊕ ⟨C(ac), C(va), C(vb)⟩ = K⁶`;
> **(iv)** therefore `dim(D + M̂ ∧ W) ≥ 5`, i.e. **`1 ≤ dimK ≤ 2`**, and
>   `L_b ∩ D = L_c ∩ D = 0`.
>
> **Consequences.** (a) (OC-26)(ii)'s **first disjunct is killed**: `dimK ≥ 3`
> is impossible at a target-rank `G`-chart point, at **every** eligible split of
> that shape simultaneously. (b) The surviving bad case is `K = M̂ ∧ w` for a `w`
> on the hub line with `w ∉ \{pt(b)^, pt(c)^\}`. (c) By (OC-30)(iii), at such a
> point **either some point of `M` is good — and then input (a) holds at that
> (shape, split) — or `D` contains a ruling**.

*Proof.* (i) is (OC-28)(ii) (row-subset monotonicity: `E(H) ⊆ E(G)`).

(ii) is the tower, read at `G` rather than `G′`. §(K-chart) (CH-2)'s stage 4
places a non-hub `s` in `⋂_{h ∼ s, h hub} Π(q_h, n_h)`. In `G`, `v` has
neighbours `a` (degree 2, non-hub) and `b` (hub), and `a` has neighbours `v`
(non-hub) and `c` (hub) — `widened.orient`'s frame — so `v`'s hub neighbourhood
is `{b}` and `a`'s is `{c}`: `pt(v) ∈ Π(b)`, `pt(a) ∈ Π(c)`. Now `pt(v)` and
`pt(b)` both lie in the plane `Π(b)`, and so does `M`; two distinct lines of a
projective plane meet, so the line `pt(v) pt(b)` meets `M`, and it meets `bc` at
`pt(b)`. It is therefore a transversal, and being a line through `pt(b)` inside
`Π(b)` it lies in `L_b` by (OC-29)(i). (The two degenerate readings are
excluded: `pt(v) = pt(b)` is not a placement, and the line equalling `M` would
put `pt(b) ∈ M ⊆ Π(c)`, against (Λ0d).) Symmetrically at the other end,
`C(ac) ∈ L_c`.

(iii) §(K-tight) *Step 2* item 1, at `Γ = G`, `x = v`, `{y, z} = {a, b}` — the
instance the item is *stated* at — reads
`corank R(G) = s₀ + dim(U ∩ C(va)^⊥ ∩ C(vb)^⊥)` with `s₀ = corank R(G − v)` and
`U = {u : ⟨u, m(a) − m(b)⟩ = 0 ∀ m ∈ Mot(G − v)}`, valid at any placement with
`pt(v) ∉ \{pt(a), pt(b)\}`. With `corank R(G) = 0` both summands vanish. Now
`G − v = H + ac` with `a` **pendant** on `c` ((OC-23)'s frame), so
`m(a) = m(c) + ω C(ac)` with `ω` free and
`\{m(a) − m(b)\} = D + ⟨C(ac)⟩` (using `−D = D`); item 3's count gives it
dimension `4 + s₀ − index(G) = 4`, so `C(ac) ∉ D`. Hence `U = (D + ⟨C(ac)⟩)^⊥`
and `U ∩ C(va)^⊥ ∩ C(vb)^⊥ = (D + ⟨C(ac), C(va), C(vb)⟩)^⊥ = 0`, which is (iii).

*One scope clause, checked rather than assumed.* §(K-tight) *Step 2*'s scope
line reads `def(G) = def(G′) = 0`, `deg_G v = 2` **and** *"a target-rank
`G′`-seed"* — and the last clause is **not** available here, since a target-rank
`G′`-point is what (a₁) is trying to produce. It is also **not consumed**: item
1's identity relates `corank R(G)` to `corank R(G − v)` and `U` only, and its own
parenthetical derivation ("a `G`-row dependency's `v`-block forces antisymmetric
fiber loads `±u`") uses nothing but `deg_G v = 2` and `pt(v) ∉ {pt(a), pt(b)}`;
the target-rank-`G′` clause is what items 2–5 need, because they are the ones
that bring in `C(ab)` and `R_a`. Belt and braces: the driver asserts the
**conclusion** (iii) directly at every point, from the motion space, by a route
that does not pass through the identity at all — so (iv) stands on a measured
rank at 466 points even if this scope reading is contested.

(iv) `C(ac), C(vb) ∈ M̂ ∧ W` by (ii), and by (iii) they are independent mod `D`,
so `dim(D + M̂ ∧ W) ≥ dim(D + ⟨C(ac), C(vb)⟩) = 3 + 2 = 5`; with
`dimK = dim D + 4 − dim(D + M̂ ∧ W) = 7 − dim(D + M̂ ∧ W)` this is `dimK ≤ 2`.
`C(vb) ∉ D` gives `L_b ⊄ D`, and since `L_b` is a ruling and any nonzero
`K ∩ L_b` would already make `L_b ∩ D` a line, the driver asserts the sharper
`rank(D ∪ L_b) = 5`, i.e. `L_b ∩ D = 0`; symmetrically for `L_c`. Consequence
(b): if `K = M̂ ∧ w` with `w ∝ pt(b)^` then `L_b = M̂ ∧ pt(b)^ = K ⊆ D`,
contradicting (iv). Consequence (c) is (OC-30)(iii) with the first disjunct
removed. ∎

**What (OC-31) is, and is not.** It is **not** a proof of (a₁): it consumes
`hK` at one chart point of `G` — exactly the object (GR-9)+(GR-5) construct at a
certified shape, and exactly what `hK` asserts — and returns half of (a₁).
Strategically it is the (a₁) analogue of (OC-24)(ii)'s "the `s₀` half cannot be
the binding obstruction": the `dimK ≥ 3` half of the *target-rank* half cannot be
either. What remains is not implied by `hK`-at-a-point by this argument, and
*Step O28* shows why that is structural rather than an accident of the argument.

*Exact, per point:* (i)–(iv) asserted at **292/292** POOL-OG target-rank
`G`-chart points (4 habitats × 30 eligible splits × seeds 700–711; **0**
guard-accepted `G`-points were off target rank, and **0** were rejected by
(Λ0d)/the meet line) and at **174/174** POOL-OC2 per-class witnesses. Measured
value at every one of the 466: `(dimK, B, rank(Q|_D), ruling) = (1, ∅, 3, no)`.

---

### Step O28 — (OC-32): the third generator is structurally unavailable

> **(OC-32)** *(proven; both collapses CONSTRUCTED)* There is **no** legal
> pencil chart placement of `G` at which `C(va)` is a transversal of `M` and
> `bc` **and** `G` attains its Tay target. Precisely, for a transversal
> `ℓ = q ∨ w` with `q ∈ M`, `w` on the line `bc`:
>
> **(i)** if `w ∉ \{pt(b), pt(c)\}` then `ℓ ∩ Π(b) = ℓ ∩ Π(c) = \{q\}`, so
> `pt(v) = pt(a) = q` and `C(va) = 0` — not a placement;
> **(ii)** if `w = pt(b)` then `ℓ ⊆ Π(b)`, `pt(a) ∈ ℓ ∩ Π(c) ⊆ M` forces
> `pt(a) = q`, and then `C(va) = C(vb)`; symmetrically `w = pt(c)` forces
> `C(va) = C(ac)`. Either way (OC-31)(iii)'s triple spans ≤ 2 dimensions mod
> `D`, so `corank R(G) > 0`.
>
> Hence **`dimK ≤ 2` is the exact reach of (OC-31)'s method**: a third element
> of `M̂ ∧ W` independent mod `D` is not merely unfound, it does not exist among
> the split's own hinge lines.

*Proof.* (i) By (Λ0d), `bc ∩ Π(b) = \{pt(b)\}` and `bc ∩ Π(c) = \{pt(c)\}`. If
`w ∉ \{pt(b), pt(c)\}` then `w ∉ Π(b) ∪ Π(c)`, and `ℓ` meets each panel in
exactly one point; that point is `q` in both cases, since `q ∈ M ⊆ Π(b) ∩ Π(c)`
and `ℓ ⊄ Π(b)`. But `pt(v) ∈ Π(b)` and `pt(a) ∈ Π(c)` must both lie on `ℓ`
((OC-31)(ii)), so both equal `q`.
(ii) If `w = pt(b)` then `ℓ` joins two points of `Π(b)` hence lies in `Π(b)`;
then `ℓ ∩ Π(c) ⊆ Π(b) ∩ Π(c) = M`, and `ℓ ∩ M = \{q\}`, so `pt(a) = q`; and
`pt(v) ∈ ℓ` makes the line `pt(v) pt(b)` equal to `ℓ = pt(v) pt(a)`, i.e.
`C(vb) = C(va)` as Plücker points. Then `rank(D + ⟨C(ac), C(va), C(vb)⟩) ≤ 5`,
so (OC-31)(iii) fails and `corank R(G) > 0`. ∎

**Both readings of (ii) matter, and both are CONSTRUCTED** (60 sites = 30
(shape, split) pairs × 2 ends): the placement built at each end is asserted
**panel-legal** (`pt(a) ∈ Π(c)`, `pt(v) ∈ Π(b)`), `C(va)` is asserted to be a
genuine transversal (`C(va) ∈ M̂ ∧ W`), the collapse `C(va) = C(vb)` (resp.
`= C(ac)`) is asserted as a rank-1 pair, and the loss of target rank is asserted
as `rank(D + ⟨C(ac), C(va), C(vb)⟩) ≤ 5`. So this is a **must-reject witness for
(OC-31)'s own method**, not a hedge: the placements exist, they are legal, and
they are exactly the ones where the third generator would have come from.

---

### Step O29 — (OC-33): the residue is nondegeneracy of the pitch form on `D`

> **(OC-33)** *(proven-informally; the sufficiency asserted per point, the
> separation CONSTRUCTED in both directions)*
>
> **(i)** If `M̂ ∧ w ⊆ D` for some `w ∈ W`, then `D` contains a 2-dimensional
> totally Klein-isotropic subspace, so **`rank(Q|_D) ≤ 2`** — equivalently
> `D ∩ T ≠ 0`, i.e. `D` lies in the tangent hyperplane of the Klein quadric at
> one of its own points.
>
> **(ii)** Hence, at a target-rank chart point of `G` ((OC-31)),
>
> > `rank(Q|_D) = 3` ⟹ some point of `M` is good ⟹ **input (a) holds at that
> > (shape, split)**,
>
> a single `3 × 3` determinant: `x₁`-free, `λ`-free, stratum-free, one-point
> decidable, and evaluable at the very point the grid route constructs.
>
> **(iii)** Neither implication reverses, and both failures are **constructed**:
> `dimK = 3` with `rank(Q|_D) = 3` is all-bad (so (ii) genuinely needs
> (OC-31)'s `dimK ≤ 2`), and `rank(Q|_D) ≤ 2` with a **one-point** bad set
> exists (so (ii) is sufficient, never necessary).

*Proof.* (i) `M̂ ∧ w` is 2-dimensional and every element is decomposable
((OC-29)(iv)), so `Q` vanishes on it; a quadratic form of rank `r` on a 3-space
has maximal totally isotropic subspaces of dimension `3 − r + ⌊r/2⌋`, which is
`1` at `r = 3`. So `r ≤ 2`. `rad(Q|_D) = D ∩ D^{⊥_B} = D ∩ T`, and a nonzero
element `d` of it has `Q(d) = 0`, i.e. is a **line**, with `D ⊆ d^{⊥_B}`.
(ii) By (OC-31)(iv) `dimK ≤ 2`, so by (OC-30)(iii) `B = M` requires
`M̂ ∧ w ⊆ D`, which (i) excludes; hence `B ≠ M` and any `pt(a) ∈ M ∖ B` — a
nonempty complement of ≤ 2 points on a line over an infinite field, minus the
proper closed subset the chart guards remove — gives a point of `Z`, which is
input (a) at that (shape, split). ∎

**The `⋆`-invariance route, and the field obstruction it stops on. This is a
route, not a result: no driver of this pass tests it, and the reason is stated.**
Suppose `D` is `⋆`-invariant. Then `D = D_+ ⊕ D_−` with `D_±` inside the `±1`
eigenspaces of `⋆` (§(K-frame) (FR-2)(iii)'s `W_A`, `W_B`), and since
`B(x, y) = ⟨x, ★y⟩`, `B` restricted to `D` is `⟨·,·⟩|_{D_+} ⊕ (−⟨·,·⟩|_{D_−})`
with the two blocks `B`-orthogonal. Over a **real** field the Euclidean form is
definite on every subspace, so `rank(Q|_D) = 3` **outright** and (ii) fires. And
`D` **is** `⋆`-invariant at a σ-fixed grid configuration: §(K-clos) (AC-2) puts
each hinge screw in `Λ²₊` or `Λ²₋`, so each hinge constraint
`m(x) − m(y) = ω C_e` splits into its `+` and `−` halves and the whole motion
system decouples — §(K-clos) (AC-4)'s decoupling, applied to `Mot(H)` and hence
to `D`. **The obstruction is exactly the field:** (AC-2) needs a field *with
isotropic vectors*, so the grids live over `ℚ(i)`, where `⟨·,·⟩` is
nondegenerate but **not** definite; and no σ-fixed configuration exists over
`ℝ`. Over `ℚ(i)` the residue splits into two independent nondegeneracy
conditions, one per `⋆`-eigen block, and whether *those* are combinatorial at a
grid point in (FR-3)'s sense is **not settled here** — `D` is a motion-derived
space, not a span of hinge lines, so (FR-3) does not apply as stated. **A
successor with a `ℚ(i)` motion-space leg can settle (a₁) at every certified
shape or exhibit the first `rank(Q|_D) ≤ 2` configuration.** This pass's harness
is `ℚ`-only, which is why the paragraph carries no driver.

*Exact, per point:* `rank(Q|_D) = 3` measured at **104/104** POOL-OS,
**292/292** POOL-OG and **174/174** POOL-OC2 points — **570 of 570**, and at
**174 of 174** isomorphism classes. The implication (ii)'s hypothesis-to-
conclusion step (`rank(Q|_D) = 3 ⟹` no ruling in `D`) is asserted at every one
of the 570, and its two non-reversals are constructed in POOL-OQ. **These are
witnesses, never a rate** — and no figure here is evidence about a *generic*
chart point ((OC-7)).

---

### Step O30 — (OC-34): the (a₂) cross-pool re-keying, done — and the per-class census

> **(OC-34)** *(a combinatorial computation plus a construction; every count a
> **labelled-instance** or **isomorphism-class** count as marked, README §4
> convention 7, caps disclosed)*
>
> **(i) The two pools, re-keyed.** Keying a class shape by the isomorphism class
> of its **length-labelled hub multigraph** (a subdivision whose hubs are its
> degree-`≥ 3` vertices is determined up to isomorphism by that datum):
> §(K-grid)'s census pool is **907 labelled shapes = 75 isomorphism classes**;
> §(K-out)'s class-shape population (`outer.named_inventory()` plus **every**
> shape of `outer.sweep_shapes()`) is **1376 labelled shapes**, of which
> **1364** carry a length-4 companion at some eligible split, in **174
> isomorphism classes**. **Only 19 of the 174** lie in §(K-grid)'s pool.
>
> **(ii) And the other 155 are certified directly.** Each of the 155 classes
> outside was run through §(K-grid)'s **own** (GR-9)/(GR-10) certificate hunt
> (admissible colourings, the combinatorial filter, `closure.build_fixed_config`,
> both-block tree-triples, and the Tay target re-verified at seeded rational
> draws): **155 of 155 certified**, **0 misses**, **0** node-cap hits, with the
> class predicate (tight, `def = 0`, `hnoRigid`) **asserted** per shape. So a
> both-block tree-triple certificate is **exhibited at all 174**.
>
> **(iii) What that buys, exactly.** At a shape where the certificate is
> *exhibited*, the `s₀` half of input (a) follows from §(K-grid) **(GR-9)** +
> **(GR-5)** + §(K-clos) **(AC-7)** + §(K-chart) **(CH-1)(e)** + (OC-23) +
> (OC-28)(i) — **(GR-10) is not consumed at all**, since its content is the
> *existence* of such a colouring. So the `s₀` half is free at **174 of 174**
> classes unconditionally on (GR-10); only the **class-uniform** statement still
> needs (GR-10) (or an uncapped re-keying).
>
> **(iv) The re-keyed witness census.** One representative per class, at the
> first eligible split carrying a length-4 companion, at the first
> guard-accepted target-rank `G`-chart point in seeds 800–802:
> **174 of 174** carry a witness, every one at
> `(dimK, B, rank(Q|_D), ruling) = (1, ∅, 3, no)`. Each row is an individual
> **proof** that input (a) holds at that (shape, split) — and more than
> (OC-27)'s rows gave, because `B = ∅` puts the **whole `pt(a)`-fibre** over
> that `H`-part inside `Z`.

**A deliberate refinement of the dispatch's own wording, recorded as one.** The
dispatch instructed that the (a₂) leg's result "stays **CONDITIONAL** on
(GR-10), which is itself **OPEN**". At the *class-uniform* level that is exactly
right and is stated as such above. At the 174 certified classes it is **not**
the right conditionality: (OC-28)(iii)'s own text says the `s₀` half "is
*already* free at every shape where the certificate has been exhibited", and
exhibiting it is what (ii) does. The conditionality that remains at those 174 is
on **(GR-9)**, **(GR-5)**, **(AC-7)**, **(CH-1)(e)** and **(OC-28)(i)** — all
proven-informally, none open — plus the caps in (i).

**Two honest limits, stated because a one-line quotation will drop them.**
*(a)* **174 classes is not the class.** `outer.sweep_shapes()` carries its own
bounds (exhaustive over lengths 1..9 for `theta3`/`theta4`, 1..5 for `K4`, 1..6
for `K4+par`, **capped at 25** per `|V°| = 5` family) and the class is infinite
in the `G°` direction (§(K-ind) **(I4)**), so this is a coverage jump, not
uniformity — README §4 convention 8's rule applies verbatim: an exhausted cap is
not a proof of nonexistence. *(b)* The certificate hunt itself is **capped at 48
filter-passing colourings per shape**; with 0 misses no cap-boundary reading
arises, but a future miss would need an uncapped re-run before being called
structural.

**The counting correction worth carrying.** "907/907" has been quoted for the
`s₀` half since (OC-28). Re-keyed it is **75 isomorphism classes**, and it
covered **19** of §(K-out)'s 174 — a factor of nine between the pool's labelled
count and its class-level reach, and the exact shape of README §4 convention 7's
warning. Nothing in §(K-grid) is wrong; the *transfer* reading was over-broad,
and (ii) is what repairs it.

---

### Where this leaves input (a) (hand-off)

**Status: OPEN as a class-uniform statement; not an independent gap; no gap-map
status moves.** After this pass input (a) reads:

> **(a₂)** free at **174 of 174** isomorphism classes of §(K-out)'s
> length-4-companion population, by an **exhibited** grid certificate, with
> **(GR-10) not consumed** at those shapes; class-uniform only modulo (GR-10) or
> an uncapped re-keying.
> **(a₁)** at a target-rank chart point of `G`: `dimK ≤ 2` is **proven**
> ((OC-31)), the third generator is **provably unavailable** ((OC-32)), and the
> whole residue is **`rank(Q|_D) = 3`** — the pitch form on the far framework's
> relative twist space is nondegenerate ((OC-33)). Measured at 570/570 points
> and 174/174 classes; **not proven** class-uniformly.

What a successor should pick up, in descending value:

1. **`rank(Q|_D) = 3` class-uniformly, via `⋆`-invariance over `ℚ(i)`** (*Step
   O29*). The real-field version is a two-line proof; the grid is `ℚ(i)`-only
   (§(K-clos) (AC-2)), and over `ℚ(i)` the residue splits into two independent
   eigen-block nondegeneracy conditions. The concrete first step is a **`ℚ(i)`
   motion-space leg** for the harness (`closure`'s `Gauss` class is the only
   exact `ℚ(i)` arithmetic in tree, and it is private to `closure` — moving it
   down is a real harness decision, not a side errand). A hit closes (a₁) at
   every certified shape; a `rank(Q|_D) ≤ 2` configuration is the first
   candidate **(K-tight) event** the arc has ever had a recipe to look for.
   **[RUN at *Steps O37–O41* (2026-08-25, direction OQRANK; the `Gauss`
   move-down had landed 2026-08-20): a graded HIT — the mechanism is
   completed ((OC-40)/(OC-41)), the naive single-colouring form is REFUTED
   as a class statement (27/174, incl. the (OC-42) WALL), the hunted form
   delivers input (a) at 174/174 classes per-class/per-colouring-generic
   ((OC-43)/(OC-44)); rank-2 grid points exist but carry no ruling, so the
   (K-tight)-event branch never fires — see the scope line at *Step O41*.]**
2. **The uncapped re-keying**, to turn (OC-34)'s 174 into a class statement, or
   the counting/`hnoRigid` exclusion (OC-28) names.
3. **§(K-out) hand-off item 4** — the one-hub-neighbour extension of the
   (OC-21) slide. **NOT attempted here** (budget went to the two legs above);
   it remains "a cheap `--wide`-style leg, too small to be a direction".
4. **Deliberately not attempted**, recorded so a successor does not assume
   otherwise: (OC-19) input (c) (`H/X` rigid class-uniformly — OCON's verdict
   stands); chart irreducibility (§(K-chart), cited); the `σ > 0` hunt (SIGZ's
   target this wave); pushing a constructed point to `p⁺`; the coupled two-end
   slide; every §(K-frame) *What would change this* item (ii)–(iv); any
   counting/matroid route to (OUT)'s hypothesis ((OC-3) refutes the class).

**The event classification, restated because it is load-bearing and was
corrected once already.** A shape where the non-jump fails at every `σ = 0`
chart point is a **(K-tight) event at that split** — (OC-8) false there, routes
A and B dead **at that split**, `hK` at the shape **untouched** (another split,
or §(K-grid)'s route, may still carry it). It is **not** a PENCIL event. Only
the *other* half — `{σ = 0} = ∅` at a class shape, (OC-24)(ii) — is a PENCIL
event. This pass **sharpens** the (K-tight) side: by (OC-31), at any shape where
`hK` holds at even one chart point the `dimK ≥ 3` route to a (K-tight) event is
**closed**, so the only surviving mechanism is `rank(Q|_D) ≤ 2`. Nothing in this
pass exhibits either event.

**One by-product, reported and not developed** (the `σ > 0` hunt was SIGZ's
target this wave, landed **NO HIT**): at **292** POOL-OG and **174** POOL-OC2 guard-accepted
`G`-chart points, `corank R(G) = 0 ⟹ σ = 0` was asserted and held, and at
POOL-OG **0** guard-accepted `G`-points were off target rank at all.

---

### Verification (Steps O25–O30)

`notes/scripts/w4/oschu.py` (new, untracked at draft time; exact ℚ, stdlib only;
a `w4/` leaf **above** `zneq`, which it imports read-only — `u_space` (via
`ledger`), `corank_at`, `ledger`, `schubert_data`, `bad_t_polys`, `poly_gcd`,
`meet_param_of` — together with `ocon` (`meet`, `perp_B`), `outerline`
(`line_pencil`, `weld_motions`, `rel_span`), `outer` (`split_data`,
`eligible_splits`, `named_inventory`, `sweep_shapes`, `companions4`,
`chart_point`, `panel_frame`, `lam0d`), `grid` (`census_shapes`, `block_data`,
`colourings`, `combinatorial_filter`, `cycle_rank`, `rank_at_params`,
`TRIES_SEED`), `gridwit` (`tree_triple`), `closure` (`build_fixed_config`),
`dominance` (`branch_pmap`), `kslide` (`no_rigid_branch_union`), `pitch`
(`klein`, `Q`), `repin` (`in_span`, `span_basis`, `star_generic`), `widened`
(`place_pencil_general`), `nogood_subdiv` (`deficiency`,
`branch_decomposition`), `kbare_common` (`verify_pencil_witness`, `verts_of`)
and catalogued §1 primitives. **Nothing existing is modified**:
`git status --porcelain notes/scripts/` shows exactly the one new file.)

From the repo root, **one mode per invocation, foreground**:

```
PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --restate   # (OC-29),(OC-30); POOL-OS, POOL-OQ
PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --gtarget   # (OC-31),(OC-32) CONSTRUCTED; POOL-OG
PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --rekey     # (OC-34)(i)-(iii); POOL-OR
PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --census1   # (OC-34)(iv), classes 1,3,5,...; POOL-OC2
PYTHONHASHSEED=0 python3 notes/scripts/w4/oschu.py --census2   # (OC-34)(iv), classes 2,4,6,...; POOL-OC2
```

Times as run: `--restate` **197 s**, `--gtarget` **466 s**, `--rekey` **55 s**,
`--census1` **139 s**, `--census2` **122 s** — 979 s in total. **The census is
split into two invocations deliberately**: `--gtarget` alone runs 466–515 s, so
a combined mode would exceed the 600 s foreground budget; the split is by class
parity in a pinned `(|V|, label)` order, so the two halves are disjoint and
together exhaust the 174. All five modes re-run **byte-identical** under two
different `PYTHONHASHSEED` values (`0` and `12345`), the *figures-do-not-move*
gate (`notes/scripts/README.md`), modulo the elapsed-second marks, which are
wall-clock and not figures.

**Harness debt recorded, not paid** (this pass may not modify a landed file).
*(a)* `ocon.meet` now has a **third** consumer (OCON, ZNEQ, this pass) —
`notes/scripts/README.md` §2 rule 2's move-down trigger, recorded by ZNEQ
2026-08-19; **RE-DATED here, still UNPAID.** *(b)* `zneq`'s `corank_at`,
`ledger`, `schubert_data`, `bad_t_polys`, `poly_gcd`, `meet_param_of` each gain
a **second** consumer — the same trigger, a **new** unpaid item. *(c)*
`gridwit.tree_triple` gains a **second** consumer — same trigger, new unpaid
item. *(d)* the `⋆`-invariance route of *Step O29* needs `closure`'s private
`Gauss` (`ℚ(i)`) arithmetic one layer down; that is a **design decision**, not a
mechanical move-down, and is recorded as such. **All four PAID 2026-08-20** by
the harness move-down round: `meet` → `lambda`, the six `zneq` devices →
`ocon`, `tree_triple` → `grid`, and (adjudicated) `Gauss` → `exactcore`, each
re-exported from its old home, so every figure above stands unchanged and
*Step O29*'s route may now use exact `ℚ(i)` directly.

**Pools, pinned; every figure above is quoted over exactly one of them, and none
is aggregated with POOL-C / POOL-G / POOL-S / POOL-B / POOL-CW / POOL-A /
POOL-W / POOL-SL / POOL-OV / POOL-OC / POOL-OZ / POOL-ZF / POOL-ZQ / POOL-ZN /
POOL-ZT / POOL-ZR.**

- **POOL-OS** (`--restate`) — the 4 `lambda.habitat_specs` habitats × **every**
  eligible split × placement seeds **600–603** of `G′`, **unfiltered** (no
  target-rank, no stratum filter) but guard-accepted through
  `outer.chart_point` (`repin.star_generic` + `verify_pencil_witness`):
  **30 splits probed, 104 chart points accepted, 16 draws rejected by the
  guards**, every accepted point at `σ = 0`. A derivation pool: every sentence
  under test is an identity, so it is a witness set and **no figure from it is a
  rate**.
- **POOL-OQ** (`--restate`) — synthetic exact-ℚ subspaces of `Λ²K⁴` from
  `random.Random(20260820)` (seed printed), plus **six constructed**
  configurations (one per attainable `dimK` row of (OC-30)(ii), plus the
  (OC-33) separation) and **60 negative controls**. No graph, no placement.
- **POOL-OG** (`--gtarget`) — the 4 habitats × **every** eligible split ×
  placement seeds **700–711** of the **whole graph `G`** (not of `G′`),
  guard-accepted for `G` by `repin.star_generic` + `verify_pencil_witness`:
  **292 target-rank `G`-chart points**, **0** off-target guard-accepted points,
  **0** (Λ0d)/meet-line rejections, plus **60** constructed (OC-32) placements
  (30 (shape, split) pairs × 2 ends).
- **POOL-OR** (`--rekey`) — §(K-out)'s class-shape population
  (`outer.named_inventory()` + every `outer.sweep_shapes()` shape, **1376**
  labelled shapes) keyed against §(K-grid)'s `grid.census_shapes()` (**907**
  labelled shapes). Purely combinatorial except the 155 certificate hunts.
  *Caps disclosed*: `sweep_shapes`' own bounds (above), and probe cap **48**
  filter-passing colourings per certificate hunt.
- **POOL-OC2** (`--census1`/`--census2`) — one representative per isomorphism
  class of the length-4-companion population (**174** classes), at the **first**
  eligible split carrying a length-4 companion, at the **first** guard-accepted
  target-rank `G`-chart point among seeds **800–802**: **174 witnesses, 0
  classes without one**. *Caps disclosed*: one split per class, 3 seeds, and
  POOL-OR's shape caps inherited.

Per mode, what is asserted:

- `--restate`: per frame — (OC-29)(i) elementwise (`L_b`, `L_c` **are** the two
  rulings; `M̂ ∧ W = L_b ⊕ L_c`), (ii) (`(M̂ ∧ W)^{⊥_B} = ⟨C(M), C(bc)⟩`,
  `Q(C(M)) = Q(C(bc)) = 0`, `B(C(M), C(bc)) ≠ 0`, and
  `dimK = 1 + dim(T ∩ Π)`), (iii) (`β_h = ⟨C(M)⟩ ⊕ L_h`, `dim(β_b + β_c) = 5`,
  `(β_b + β_c)^{⊥_B} = ⟨C(M)⟩`), (iv) (`Q = λ · det` on ten test vectors, `λ`
  asserted nonzero and constant), (v) in its **literal** form
  (`⟨C(ab), C(ac)⟩ = pt(a)^ ∧ W`, and `Z`-membership `==` "`C(ab)`, `C(ac)`
  independent mod `D`"); then (OC-30)'s bad set computed **from `K`** and
  asserted against **ZNEQ's independent `ℚ[t]`-GCD route** *and* against the
  sampled `pt(a)`'s `Z`-membership; plus `rank(Q|_D) = 3 ⟹` no ruling.
  Histogram: `(dimK, bad set, #bad pts, rank(Q|_D), ruling?, deg GCD) =
  (1, none, 0, 3, False, 0) : 104`.
  POOL-OQ prints the six constructed rows and the 60-control histogram
  `(1, none, False, 3) : 60`.
- `--gtarget`: per guard-accepted `G`-point — `pt(v) ∈ Π(b)` and
  `pt(a) ∈ Π(c)` (the (CH-2) stage-4 input, **asserted, not assumed**);
  `C(vb) ∈ L_b`, `C(ac) ∈ L_c`; then at target rank: `corank R(G) = 0`,
  `σ = 0`, `dim D = 3`, `D ⊕ ⟨C(ac), C(va), C(vb)⟩ = K⁶` (rank computed
  **independently** of the (K-tight) identity), `C(ac), C(vb)` independent mod
  `D`, `dimK ≤ 2`, `L_b ∩ D = L_c ∩ D = 0`, and `rank(Q|_D) = 3 ⟹` no ruling.
  Histogram `(dimK, bad set, rank(Q|_D), ruling?) = (1, none, 3, False) : 292`.
  Then the (OC-32) construction at both ends of each (shape, split).
- `--rekey`: the two key sets and their intersection; per certificate hunt, the
  **class predicate** asserted (tight, `def = 0`, `hnoRigid` via
  `kslide.no_rigid_branch_union`), each tree-triple pair-union asserted to be a
  spanning tree, and the Tay target re-verified at up to 3 seeded rational
  draws (an assert fires if a certified colouring misses it — (GR-9) would be
  false or the code wrong; none fired). Output: `907 → 75`, `1376 → 1364 → 174`,
  `19` inside, `155` outside, `155/155` certified, `0` misses, `0` capped.
- `--census{1,2}`: per class — the same ledger as `--gtarget` at one split, with
  the miss list printed. Histogram `(1, none, 3, False) : 87` in each half.

*Standing of this output.* Evidence for this workbook, at the same standing as
the rest of the exact-ℚ numerics — **never** a substitute for Lean (`DESIGN.md`
*Formalize everything the argument uses*).

**Which driver mode tests which sentence (F11).**

| claim | mode | what asserts *that sentence* |
|---|---|---|
| (OC-29)(i) `L_b`, `L_c` are the two rulings and `M̂ ∧ W = L_b ⊕ L_c` | `--restate` | each basis vector of `outerline.line_pencil` asserted **in** `M̂ ∧ pt(h)^` (span membership, elementwise) and the two spans asserted to sum to `M̂ ∧ W` with rank 4 — 104/104; the sum identity again at 292 + 174 points |
| (OC-29)(ii) the Klein perp, and `dimK = 1 + dim(T ∩ Π)` | `--restate` | `ocon.perp_B(M̂ ∧ W)` asserted rank-equal to `⟨C(M), C(bc)⟩`; `dimK` computed by **two disjoint routes** (Grassmann count via `zneq.schubert_data`, and `1 + dim(T ∩ Π)` via `ocon.meet`) and asserted equal — 104/104 |
| (OC-29)(ii) `dimK ≥ 1` always | `--restate` (POOL-OQ) | structural, and **exercised**: the synthetic builder asserts `n ≤ 2` extra directions fit, i.e. `dimK = 0` is not constructible |
| (OC-29)(iii) the two panel identities + (K-tight) item 5's 5-space | `--restate` | `β_h` built from `Λ²Π̂(h)`, asserted `= ⟨C(M)⟩ ⊕ L_h`; `dim(β_b + β_c) = 5`; `perp_B` of it asserted `= ⟨C(M)⟩` — 104/104 |
| (OC-29)(iv) `Q\|_{M̂ ∧ W} = λ · det` | `--restate` | one `λ` extracted from the basis and asserted **constant and nonzero** across ten test vectors (4 basis + 6 pairwise sums), per frame — 104/104, plus the synthetic frame (`λ = −2`) |
| (OC-29)(v) `Z`-membership is independence mod `D` | `--restate` | `⟨C(ab), C(ac)⟩` asserted `= pt(a)^ ∧ W`, and `(rank(D ∪ \{C(ab), C(ac)\}) == 5) == inZ` asserted per frame — an **iff**, both sides exercised |
| (OC-30)(i)/(ii) the bad set | `--restate` | computed **from `K`'s decomposables** and asserted against ZNEQ's `ℚ[t]`-GCD of the three `2 × 2` minors (a disjoint route), plus against the sampled `pt(a)`'s actual `Z`-membership — 104/104 |
| (OC-30)(ii) every row of the table | `--restate` POOL-OQ | **six constructed** objects, one per attainable row, each asserted to produce exactly that row's bad set and ruling verdict; the `dimK = 3, no ruling` row is ZNEQ's Case C **recovered**, not assumed |
| (OC-30)(iii) `\|B\| ≤ 2` off the all-bad case | `--restate` | the badness determinant asserted **quadratic** in `t` (degree checked at a fourth point), so its root set is ≤ 2 — per frame; the `≤ 2` bound realized at 1 in POOL-OQ |
| (OC-31)(ii) `pt(v) ∈ Π(b)`, `pt(a) ∈ Π(c)`, and the two hinge lines are transversals | `--gtarget`, `--census{1,2}` | the panel memberships asserted as **exact** scalar products at every guard-accepted `G`-point (292 + 174), and `C(vb) ∈ L_b`, `C(ac) ∈ L_c` by span membership |
| (OC-31)(iii) the (K-tight) item-1 consequence | `--gtarget`, `--census{1,2}` | `rank(D ∪ \{C(ac), C(va), C(vb)\}) = 6` asserted at every target-rank point — computed from the motion space, **independently** of the corank identity it is derived from — 292 + 174 |
| (OC-31)(iv) `dimK ≤ 2`, `L_b ∩ D = L_c ∩ D = 0` | `--gtarget`, `--census{1,2}` | asserted per point, 292 + 174; measured value `dimK = 1` at every one |
| (OC-32) the third generator | `--gtarget` | **CONSTRUCTED** at both ends of 30 (shape, split) pairs: the placement's panel legality, `C(va) ∈ M̂ ∧ W`, the rank-1 collapse onto `C(vb)`/`C(ac)`, and `rank(D ∪ \{…\}) ≤ 5` all asserted — a must-reject witness for (OC-31)'s own method |
| (OC-33)(i) a ruling forces `rank(Q\|_D) ≤ 2` | `--restate` POOL-OQ | the constructed ruling case asserted at `rank(Q\|_D) = 2`; and `rank(Q\|_D) = 3 ⟹` no ruling asserted at **570** graph points |
| (OC-33)(ii) sufficiency | `--gtarget`, `--census{1,2}` | the two hypotheses (`dimK ≤ 2` and `rank(Q\|_D) = 3`) and the conclusion (`B ≠ M`) asserted together per point — 292 + 174 |
| (OC-33)(iii) neither reversal | `--restate` POOL-OQ | **two constructed** separations: `dimK = 3` with `rank(Q\|_D) = 3` all-bad, and `rank(Q\|_D) ≤ 2` with a one-point bad set |
| (OC-33) `⋆`-invariance route | — | **no driver, and the draft says so**: the harness is ℚ-only and (AC-2)'s grids are ℚ(i). Recorded as a route with a named field obstruction, never as a result |
| (OC-34)(i) the re-keying | `--rekey` | both key sets computed by the same `shape_key` and printed with their intersection: `907 → 75`, `1364 → 174`, `19` inside |
| (OC-34)(ii) 155/155 certified | `--rekey` | §(K-grid)'s **own** hunt re-run per shape, with each pair-union asserted a spanning tree and the Tay target re-verified; class predicate asserted per shape; misses and cap hits printed (both 0) |
| (OC-34)(iii) what it buys | — | **quotation**: (GR-9)/(GR-5)/(AC-7)/(CH-1)(e) proven elsewhere, (OC-23)/(OC-28)(i) this section's. Nothing re-derived; the pools are **not** aggregated |
| (OC-34)(iv) the per-class census | `--census1`, `--census2` | 174 individual exact-ℚ witnesses, each with the full (OC-31)/(OC-33) ledger asserted; disjoint halves by pinned order |
| (a₁) class-uniformly | — | **not tested and not claimed.** 570 labelled points and 174 isomorphism classes under disclosed caps, never a class-level statement |
| `rank(Q\|_D) ≤ 2` anywhere on a class chart | — | **hunted only incidentally**: 570 points, 0 hits. Not a search; the named successor item |

---

### Confidence verdict (Steps O25–O30)

| | claim | standing |
|---|---|---|
| **(OC-29)** | `M̂ ∧ W = L_b ⊕ L_c`; `(M̂ ∧ W)^{⊥_B} = ⟨C(M), C(bc)⟩` so `dimK = 1 + dim(T ∩ Π)` and `dimK ≥ 1` always; `β_h = ⟨C(M)⟩ ⊕ L_h` with `β_b + β_c` the (K-tight) *Step 2* item-5 5-space and Klein perp `⟨C(M)⟩`; `Q\|_{M̂ ∧ W} = λ · det`; `Z`-membership `⟺` `C(ab), C(ac)` independent mod `D` | **proven** (linear algebra over the chart's field, given (Λ0d)); every clause asserted per frame at 104/104 POOL-OS, and (i)/(ii)/(iv) again at 292 POOL-OG + 174 POOL-OC2 |
| **(OC-30)** | the bad set on `M` is the image of `K`'s decomposables; the five-row classification; `B = M ⟺ dimK ≥ 3` or a ruling ((OC-26)(ii) by a disjoint route); **off that case `\|B\| ≤ 2`** | **proven**; asserted per frame against ZNEQ's independent GCD route and against the sampled point's `Z`-membership (104/104), with **six constructed** rows + 60 controls. The `dimK = 2` anisotropic row is **field-dependent** and flagged |
| **(OC-31)** | at every target-rank `G`-chart point: `σ = 0`, `C(vb) ∈ L_b`, `C(ac) ∈ L_c`, `D ⊕ ⟨C(ac), C(va), C(vb)⟩ = K⁶`, hence **`1 ≤ dimK ≤ 2`** and `L_b ∩ D = L_c ∩ D = 0`; so (OC-26)(ii)'s `dimK ≥ 3` disjunct is **killed by `hK`-at-a-point**, at every eligible split at once | **proven-informally**, citing §(K-tight) *Step 2* item 1 (itself proven-informally) and §(K-chart) (CH-2) stage 4; the (CH-2) input and the item-1 **conclusion** each asserted per point, the latter computed by a disjoint route — 292/292 + 174/174. **This is the pass's sharpest positive** |
| **(OC-32)** | `C(va)` is a transversal of `M` and `bc` at no legal `G`-chart placement with target rank; so `dimK ≤ 2` is the exact reach of (OC-31)'s method | **proven**, and **CONSTRUCTED** at 60 sites with the constructed placements' panel legality asserted. A must-reject witness for the pass's own method (F13) |
| **(OC-33)** | a ruling in `D` forces `rank(Q\|_D) ≤ 2`; hence at a target-rank `G`-chart point `rank(Q\|_D) = 3 ⟹` **input (a) at that (shape, split)**; sufficiency is not necessity, in both directions | **(i)/(ii) proven-informally** (Witt index of a rank-3 form; (OC-30)(iii) + (OC-31)); **(iii) constructed twice**. `rank(Q\|_D) = 3` measured at **570/570** points and **174/174** classes — **witnesses, never a rate**, and never evidence about a generic chart point ((OC-7)). The `⋆`-invariance route is **a route with a named field obstruction, carrying no driver, and is labelled as such** |
| **(OC-34)** | §(K-grid)'s 907 labelled shapes are **75** classes and cover **19** of §(K-out)'s **174**; the other **155 are certified directly, 155/155, 0 misses**; so the `s₀` half is free at all 174 **without (GR-10)**; and a re-keyed census carries **174/174** one-point witnesses of input (a) | **(i)/(ii) a computation and a construction**, class predicate asserted per shape, caps disclosed; **(iii) a quotation** ((GR-9)/(GR-5)/(AC-7)/(CH-1)(e) + (OC-23)/(OC-28)(i)), pools **not** aggregated; **(iv) measurement — witnesses, never a rate**. **Not class uniformity**: `sweep_shapes`' caps stand and the class is infinite in the `G°` direction ((I4)) |
| **input (a)** | `Z ≠ ∅` at every class (shape, split) | **OPEN as a class-uniform statement — and NOT an independent gap.** (a₂) free at 174/174 classes by an exhibited certificate; (a₁) reduced to one determinant at a point the grid route constructs |

**No gap-map status moves. Class uniformity of (OUT), of (OC-8) and of `hK` is
exactly where it was.** What moves is the *content* of §(K-out)'s row (which
gains (OC-29)–(OC-34)) and the reading of input (a): its `s₀` half is now free
at a nine-times-larger, **isomorphism-class-keyed** population than "907/907"
covered, and its target-rank half has lost one of its two failure disjuncts to a
proof and the other to a single determinant.

### What would change this (Steps O25–O30)

1. **A class chart point with `rank(Q|_D) ≤ 2`** — `D` tangent to the Klein
   quadric at one of its own lines. Measured nowhere (570 points, 174 classes).
   If it also carries the ruling `M̂ ∧ w` with `w` off `{pt(b), pt(c)}`, and at
   **every** `σ = 0` chart point of that shape, it is the arc's first
   **(K-tight) event** — routes A and B dead **at that split**, `hK` at the
   shape **untouched**, **not** a PENCIL event.
2. **The `ℚ(i)` eigen-block leg** (*Step O29*). Over a real field
   `⋆`-invariance of `D` settles `rank(Q|_D) = 3` in two lines; the grid is
   `ℚ(i)`-only (§(K-clos) (AC-2)) and no σ-fixed real configuration exists. A
   `ℚ(i)` motion-space leg either closes (a₁) at all 174 certified classes or
   produces item 1. **This is the single cheapest open step this pass leaves.**
3. **A failure of (OC-31)(ii)'s tower input** — a chart in which a chain
   interior with one hub neighbour is *not* confined to that hub's panel — would
   break (OC-31) and (OC-32) together while leaving (OC-29), (OC-30) and
   (OC-34) intact. It is **not** an input in the ZNEQ sense: §(K-chart) (CH-2)'s
   stage table proves it, and it is asserted at 466 points. What would break it
   is a change to `place_pencil_general`'s stage 4.
4. **A `sweep_shapes`-external class shape carrying a length-4 companion whose
   grid certificate fails.** (OC-34)(ii) is exhaustive over the pooled 174 and
   silent beyond; a miss there would refute (GR-10) at that shape *and* remove
   the `s₀` half's freeness there, and by (OC-24)(ii) make `hK` false at it — a
   **PENCIL event**. The hunt with the best prior is still §(K-flank) *F5(d)*'s
   short-theta mechanism (SIGZ's target this wave).
5. **A longer split chain.** (OC-31)'s proof uses `orient`'s chain having
   exactly the two interior vertices `v`, `a`, so that `pt(v) ∈ Π(b)` and
   `pt(a) ∈ Π(c)` are single-panel conditions. A frame with a longer chain
   interior would put the middle vertices in *free* space and the two automatic
   transversals would be lost — worth recording so a successor does not assume
   the argument is chain-length-free.
6. **The `dimK = 2` anisotropic row becoming reachable.** (OC-30)(ii)'s only
   field-dependent row: at such a point the bad set is empty over ℚ and two
   points over ℚ(i). Nothing exhibits it on a class chart; it matters because a
   ℚ(i)-based argument (item 2) would see bad points a ℚ-based one does not.

**TERMINATION check (E1/E2/E3).** *(E1)* **No `g`-flank.** This direction *does*
examine admissible colourings — 155 certificate hunts — and every one of the 155
shapes carries a filter-passing colouring with both-block tree-triple
certificates, so no shape had *every* admissible colouring fail; the probe cap
(48 filter-passing colourings/shape) is disclosed and, with 0 misses, no
cap-boundary reading arises. **E1 does not fire, on a real detector.**
*(E2)* The target is neither refuted nor unprovable-as-posed — it is **reduced**:
(a₂) discharged at 174/174 classes, (a₁) reduced to a single named determinant
with a named dispatchable attack (the ℚ(i) eigen-block leg). **E2 does not
fire.** *(E3)* The target is **not proven** class-uniformly, and §(K-grid) route
ledger entry 1's (a′) is untouched by this direction; **E3 stays ARMED by
GBAL's entry-5 HIT and is neither fired nor disarmed.** Firing is a coordinator
action.

---

### Steps O37–O41 (2026-08-25, direction OQRANK) — (a₁)'s residue at σ-fixed grid points: the ⋆-eigen-block route of *Step O29* COMPLETED as a mechanism, its naive single-colouring form REFUTED as a class statement (27 of 174), the hunted form GREEN at 174/174 — and a combinatorial WALL found

(a₁)'s one-determinant residue ((OC-33)) attacked at **σ-fixed grid
points** by the ℚ(i) ⋆-eigen-block leg *Step O29* named and could not run.
The route paragraph's open piece is **settled in both directions**: the
decomposition is real and the per-block conditions are *partially*
combinatorial — with an exact combinatorial **wall**. At a σ-fixed
target-rank grid chart point of `G` the split forces `D = D_X ⊕ D_Y` with
`dim D_X = 1`, `dim D_Y = 2`, the `X`-family being `col(vb) = col(ac)`
((OC-40)); the residue factors as the exact criterion
`rank(Q|_D) = [Q(g) ≠ 0] + rank⟨·,·⟩|_{D_Y}` on the block Grams
((OC-41)); the `X`-condition hits a **combinatorial wall**: a `b`–`c`
path of `H` through a *single* `X`-class confines the block generator to
that class's ruling line and forces `rank(Q|_D) = 2` at **every**
parameter draw of that colouring ((OC-42)) — so *the naive route
(first certificate colouring) is FALSE as a class statement*, refuted at
**27 of 174** classes by persistent first-point failures (7 by the
proven wall, 20 by a second, not-yet-characterized confinement with the
same signature). The rescue is a colouring hunt: at **174 of 174**
classes a certificate colouring within the disclosed caps carries an
exact ℚ(i) target-rank grid chart point with `rank(Q|_D) = 3` — every
one in the parameter-free secant/secant configuration — ((OC-43)), and
one witness per (class, colouring) lifts to **every sufficiently generic
draw of that colouring** by openness ((OC-44)) — with (OC-33)(ii),
**input (a) holds at every certified class at an exhibited σ-fixed grid
point, by the eigen-block mechanism**. Input (a) stays OPEN as a
class-uniform statement; the new named residuals are the wall-avoiding
colouring existence and the second confinement's mechanism
((OC-44)(iii)). **No gap-map status moves.**

*(Everything cited that this pass did not mint, per
`notes/Pencil-labels.md` clause L3: (OC-1), (OC-3), (OC-7)–(OC-8),
(OC-17)–(OC-34) are §(K-out)'s own earlier items; (AC-2)/(AC-4)/(AC-7)/
(AC-9) are §(K-clos)'s; (FR-2)/(FR-3) are §(K-frame)'s; (GR-5)/(GR-9)/
(GR-10) are §(K-grid)'s; (CH-1)/(CH-2) are §(K-chart)'s; (Λ0d) is
§(K-Λ)'s; §(K-tight) *Step 2* items are §(K-tight)'s. POOL-OS / POOL-OG /
POOL-OQ / POOL-OR / POOL-OC2 are OSCHU's pinned pools — cited, never
re-run or extended; the new pool is **POOL-OQ2**.)*

Standing notation: §(K-out)'s plus *Steps O19–O30*'s (`b — v — a — c`;
`G′ = G − v + ab`; `H = G − v − a`; `σ = corank R(H)`;
`D = {m(b) − m(c) : m ∈ Mot(H)}`; `K = D ∩ (M̂ ∧ W)`), plus the grid
dictionary of §(K-clos)/(K-frame): `W_A ⊕ W_B = Λ²K⁴` the `±1`
⋆-eigenspaces ((FR-2)(iii)), `A(s)`/`B(u)` the ruling Plücker points
(each family a Veronese conic in its 3-space), `B(x,y) = ⟨x, ⋆y⟩` the
Klein form, `Q(x) = B(x,x)` the pitch form. A **colouring** is admissible
(legal, alternating); a **certificate colouring** carries both-block
tree-triples ((GR-9)/(GR-10)); `col(e)` is an edge's ruling family. For a
family `F ∈ {A, B}` and the split chain, `X := col(vb)` and
`Y := col(va)` (well-defined by (OC-40)(iii) below).

---

### Step O37 — (OC-40): the ⋆-eigen split of `D`, and the forced `(1,2)` profile at target rank

> **(OC-40)** *(proven; every clause asserted per POOL-OQ2 point)* Let
> `pt` be a σ-fixed grid configuration of a class shape `G` at an
> admissible colouring, and fix a split `b — v — a — c`. Then:
>
> **(i)** `Mot(H)` decouples: `Mot(H) = Mot_A(H) ⊕ Mot_B(H)`, hence
> `D = D_A ⊕ D_B` with `D_F := {m_F(b) − m_F(c)} ⊆ W_F` — `D` is
> ⋆-invariant.
>
> **(ii)** `B|_D = ⟨·,·⟩|_{D_A} ⊕ (−⟨·,·⟩|_{D_B})`, the two blocks
> `B`-orthogonal *and* `⟨·,·⟩`-orthogonal.
>
> **(iii)** alternation at the degree-2 interiors `v`, `a` forces
> `col(vb) = col(ac) = X ≠ col(va) = Y`, and the three hinge lines are
> ruling lines: `C(vb) = A(s_b)`, `C(ac) = A(s_c)` (the lines of `b`'s
> and `c`'s `X`-classes), `C(va) = B(u₀)` (the line of the singleton
> `Y`-class `{v, a}`, which `H` deletes whole). *(Family labels: if
> `X = B` swap `A ↔ B` throughout; the driver keeps the honest sign.)*
>
> **(iv)** if moreover `pt` carries the **Tay target on `G`**
> (`corank R(G) = 0`), then (OC-31)(iii)'s direct sum
> `D ⊕ ⟨C(ac), C(va), C(vb)⟩ = K⁶` splits per family into
>
> > `D_X ⊕ ⟨A(s_b), A(s_c)⟩ = W_X`  and  `D_Y ⊕ ⟨B(u₀)⟩ = W_Y`,
>
> forcing **`dim D_X = 1`, `dim D_Y = 2`**, `s_b ≠ s_c`, `u_b ≠ u_c`, and
> `b ≁ c` in both the `X`- and the `Y`-forest of `H`. In particular
> **(Λ0d) holds automatically at every target-rank grid point**, so the
> whole (OC-29) dictionary is available there with no side condition.

*Proof.* (i) By (AC-2) every hinge screw of the configuration lies in
`W_A` or `W_B` — this is per-edge and survives restriction to the
subgraph `H`, which is σ-fixed body-by-body. For an edge `e = xy` with
`C_e ∈ W_A`, the constraint `m(x) − m(y) ∈ ⟨C_e⟩` reads, in
eigen-components, `m_A(x) − m_A(y) ∈ ⟨C_e⟩` *and* `m_B(x) = m_B(y)`
(the `W_B`-component of a multiple of `C_e` is `0`); symmetrically for
`C_e ∈ W_B`. So the constraint set is the direct sum of a `W_A`-system
and a `W_B`-system on the same body set — (AC-4)'s decoupling, applied
verbatim to `Mot(H)` — and evaluation `m ↦ m(b) − m(c)` respects it.

(ii) `B(x, y) = ⟨x, ⋆y⟩ = ±⟨x, y⟩` on the eigenspaces; for the cross
terms, ⋆ is `⟨·,·⟩`-self-adjoint (the identity `⟨x, ⋆y⟩ = ⟨⋆x, y⟩`,
§(K-clos) *Step Z2*'s proof), so eigenvectors to distinct eigenvalues are
`⟨·,·⟩`-orthogonal, and then `B(x_A, y_B) = −⟨x_A, y_B⟩ = 0` as well.

(iii) Alternation is (AC-4)'s last clause (conjunct 4 at a degree-2
body): `col(vb) ≠ col(va)` at `v` and `col(va) ≠ col(ac)` at `a`, so
`col(vb) = col(ac)`. At a grid point every hinge line is a ruling line
whose identity is its edge's colouring-component ((FR-3)(i)): `vb` lies
in the `X`-tree containing both `v` and `b`, so `C(vb)` *is* that class's
line `A(s_b)`; likewise `C(ac) = A(s_c)`. The `Y`-class of `va` is the
`Y`-component `{v, a}` — `v` and `a` have degree 2 in `G` and one
`Y`-edge each, namely `va` — a singleton class whose two bodies `H`
deletes, so `H`'s `Y`-classes are exactly `G`'s minus `{v, a}` and
`H`'s `X`-classes are `G`'s with the leaves `v`, `a` removed (a leaf
removal never splits a tree, and never changes the class parameter).

(iv) `D` is ⋆-invariant by (i); `S := ⟨A(s_b), A(s_c), B(u₀)⟩` is
⋆-invariant because each generator is an eigenvector. A ⋆-invariant
subspace `V` splits as `(V ∩ W_A) ⊕ (V ∩ W_B)` (char ≠ 2: apply the
projections `(1 ± ⋆)/2`). Intersecting `K⁶ = D ⊕ S` with each family and
counting — `dim(D_F) + dim(S_F) ≤ 3` per family, summing to `6` — gives
equality per family, i.e. the two displayed sums. The `X`-sum needs
`dim⟨A(s_b), A(s_c)⟩ = 2`, i.e. `s_b ≠ s_c` (distinct classes); then
`dim D_X = 1`. The `Y`-sum gives `dim D_Y = 2`; if `b` and `c` lay in one
`Y`-component of `H` then `m_Y(b) = m_Y(c)` for every motion and
`D_Y = 0` — excluded; likewise a common `X`-component would put
`s_b = s_c` — excluded. `Y`-components of `H` and of `G` containing `b`
or `c` coincide ((iii): only `{v,a}` is deleted), so `u_b ≠ u_c` by
injectivity of parameters across components, and by (AC-2)'s conjugacy
formula `pt(b) ⬝ pt(c) = 2(s_b − s_c)(u_b − u_c) ≠ 0` up to the fixed
parameterization scale — which is exactly (Λ0d) at a σ-fixed point
(`Π(h) = pt(h)^⊥`). ∎

**Two remarks.** *(1)* The profile `(1, 2)` is forced with the 1-dim
block always in the family of the two *outer* hinge lines `C(vb)`,
`C(ac)` — the easy cases `(3,0)`/`(0,3)` (where a 3-dim block fills its
family and nondegeneracy is free) **never occur** at a target-rank grid
point. *(2)* At a grid point the (OC-3) pencil becomes split too:
`L_h = ⟨A(s_h), B(u_h)⟩`, the two ruling lines through `pt(h)` — so
(OC-31)(iv)'s `L_b ∩ D = 0` reads: *neither of `b`'s ruling lines is an
achievable relative motion* — and the (OC-40)(iv) sums re-prove it per
family.

*Exact, per point:* (i)–(iv) asserted at every standing target-rank
point the POOL-OQ2 hunt met — the 174 hit points plus every rank-2
point on the way ((OC-43)): star-invariance as `rank(D ∪ ⋆D) = 3`, the
dims, the family match against `star_sign(C(vb))`, cross-block
`B`-orthogonality elementwise, both per-family sums at full rank,
`pt(b) ⬝ pt(c) ≠ 0`, and (OC-31)(iii) itself.

---

### Step O38 — (OC-41): the per-block criterion, and the Veronese dictionary that reads it

> **(OC-41)** *(proven; asserted per point, with must-reject controls)*
> At a point as in (OC-40)(iv), write `D_X = ⟨g⟩`. Then
>
> > **`rank(Q|_D) = [Q(g) ≠ 0] + rank(⟨·,·⟩|_{D_Y})`** ,
>
> so `rank(Q|_D) = 3 ⟺ Q(g) ≠ 0` **and** `Gram⟨·,·⟩(D_Y)` nonsingular.
> The two conditions read geometrically:
>
> **(i)** *(the `X`-condition)* `Q(g) = 0 ⟺ g` lies on the `X`-family
> conic `⟺ g` **is a ruling line**: the 1-dimensional relative
> `X`-motion of `b` against `c` is itself a line of the fixed quadric.
>
> **(ii)** *(the `Y`-condition, apolarity form)* for same-family ruling
> lines `B(A(s), A(s′)) = κ (s − s′)²` with `κ ≠ 0` fixed — the Veronese
> Gram — so `⟨q, A(u)⟩ ∝ q̃(u)` where `q = Σ λ_i A(s_i)` has *symbol*
> `q̃(u) = Σ λ_i (s_i − u)²`; a 2-space `U ⊆ W_Y` is degenerate `⟺` it is
> a **tangent plane** of the `Y`-conic `⟺` all its symbols share a root.
>
> **(iii)** *(secant rigidity — the parameter-free positives)* a 1-space
> `⟨g⟩ ⊆ ⟨A(s₁), A(s₂)⟩` (`s₁ ≠ s₂`) with `g` on neither line has
> `Q(g) ≠ 0` **for every parameter value**; a 2-space
> `U = ⟨A(u₁), A(u₂)⟩` spanned by two distinct ruling lines is
> nondegenerate **for every parameter value** (its Gram is
> anti-diagonal with entry `κ(u₁ − u₂)² ≠ 0`).

*Proof.* The displayed rank identity is (OC-40)(ii): the `B`-Gram of `D`
in a block basis is block-diagonal, and rank is additive over blocks
(the sign on the `Y`-block does not change its rank). (i) The isotropic
vectors of `(W_F, ⟨·,·⟩)` are exactly the family's conic of decomposables
(§(K-clos) *Step Z2*: the lines on the fixed quadric are the ⋆-fixed
points of the Klein quadric, and on each eigenspace the form restricts to
a smooth conic). (ii) `f(s, s′) := B(A(s), A(s′))` is a symmetric
polynomial of bidegree `(2, 2)` (each `A` is quadratic in its affine
parameter) vanishing iff the two lines meet, i.e. exactly on `s = s′`;
for fixed `s`, `f(s, ·)` is a degree-≤2 polynomial with `s′ = s` its only
root, so `f(s, s′) = c(s)(s − s′)²`, and bidegree forces `c(s) = κ`
constant, nonzero since distinct same-family lines are disjoint. (At
infinity use the homogeneous form `κ(st′ − ts′)²`; the census draws are
affine.) Then for `q = Σ λ_i A(s_i)` and a conic point `A(u)`:
`⟨q, A(u)⟩ = B(q, A(u)) = κ Σ λ_i (s_i − u)² = κ q̃(u)` — pairing against
conic points evaluates the symbol. A 2-dim `U` in a 3-dim nondegenerate
quadratic space is degenerate iff its 1-dim perp `⟨n⟩` lies in
`U = n^⊥`, i.e. iff `⟨n, n⟩ = 0`: `U` is the perp of a conic point,
which by the evaluation formula is `{q : q̃(u(n)) = 0}` — the tangent
plane at `n`, the quadratics vanishing at `n`'s parameter. (iii) Direct
Gram computation: `Q(αA(s₁) + βA(s₂)) = 2αβκ(s₁ − s₂)²` and
`Gram(A(u₁), A(u₂)) = [[0, κ(u₁−u₂)²], [κ(u₁−u₂)², 0]]`. ∎

**Reading.** *This is Step O29's "two independent per-eigen-block
nondegeneracy conditions", made exact.* The one 3×3 determinant of
(OC-33) factors at a grid point into a 1×1 and a 2×2 block determinant,
and the blocks live on the two *block direction networks* of *Step O39*
below. Both failure modes exist and are detected by the same identity —
driver leg `--controls` plants each (a ruling-line generator; a genuine
tangent plane, built with the exact derivative `B′(u) = (B(u+1) −
B(u−1))/2`, exact because `B(·)` is quadratic; a clean secant/secant
pass; and a `(2,1)`-shaped space with a planted isotropic `Y`-line, off
the census's split shape) and each is caught, 4/4.

---

### Step O39 — (OC-42): the block networks, the WALL, and what is combinatorial in (FR-3)'s sense

> **(OC-42)** *(proven (i)–(iii); (iv) is the honest scope statement)*
> At a σ-fixed grid point of `H` (notation as above):
>
> **(i)** *(the block network)* `Mot_X(H)` factors through the
> `Y`-quotient `H̄_X` — nodes the `Y`-components of `H`, one `K³`-variable
> per node — where an `X`-edge of class `i` constrains the node
> difference to the line `⟨A(s_i)⟩`, all edges of one class carrying the
> **same** conic point; `D_X = {m(b̄) − m(c̄)}`, and for any fixed
> `b̄`–`c̄` path `P`, every achievable value equals
> `Σ_{e ∈ P} ± λ_e A(s_{cls(e)})`. Moreover `H̄_X = Ḡ_X − n_{va}`: `G`'s
> own `X`-block network minus the single degree-2 node `{v, a}`, whose
> two edges (classes `s_b`, `s_c`) land exactly on the probe nodes
> `b̄`, `c̄`; and `H̄_Y = Ḡ_Y − e₀`, `G`'s `Y`-network minus the one edge
> `va` — again joining exactly the probe nodes. At a certificate
> colouring both parent networks are generically isostatic ((GR-9)), and
> extension-to-`G` re-proves (OC-40)(iv)'s sums from isostaticity alone.
>
> **(ii)** *(the WALL — a colouring-level obstruction)* if `b` and `c`
> are joined in `H` by a path using only `Y`-edges and `X`-edges of a
> **single class** `i` — equivalently, `b̄` and `c̄` are joined in `H̄_X`
> through class `i` alone — then every achievable `X`-value lies in
> `⟨A(s_i)⟩`, so at a target-rank grid point `D_X = ⟨A(s_i)⟩` and
> `Q(g) = 0`:
>
> > **`rank(Q|_D) = 2` at EVERY parameter draw of that colouring.**
>
> The wall is a connectivity read of the coloured shape — O(1) in
> (FR-3)'s sense — and the wall class is automatically a *third* class
> (`i ∉ {cls(b), cls(c)}`), since `D_X ⊕ ⟨A(s_b), A(s_c)⟩` is direct.
>
> **(iii)** *(Y-side vacuity)* a single-class `b`–`c` path on the `Y`-side
> forces `dim D_Y ≤ 1`, so at a target-rank point the `Y`-wall is
> **vacuous** (asserted per point).
>
> **(iv)** *(scope — Step O29's question answered)* the per-block
> conditions are **not** an O(1) colouring read in general: off the wall
> and off the secant cases they are non-vanishing of block Grams,
> polynomial in the class parameters, decided per (class, colouring) by
> one exact witness plus openness ((OC-44)(i)). What *is* combinatorial:
> the wall forces failure identically ((ii)), and the secant supports
> force success identically ((OC-41)(iii)). The census below measures
> where the 174 classes actually sit.

*Proof.* (i) A `Y`-edge forces equal `X`-components at its endpoints, so
`m_X` descends to `Y`-components; an `X`-edge of class `i` has hinge
`A(s_i)` — (FR-3)(i): the family parameter is constant on components —
which is the stated node constraint. The path formula is a telescoping
sum. For the identification: `H = G − v − a` deletes the bodies `v`, `a`
(one `Y`-component, `{v,a}`, hence one node of `Ḡ_X`) and the three
edges `vb`, `va`, `ac`; `vb`, `ac` are the deleted node's only `X`-edges
(degree-2 bodies), with classes `s_b`, `s_c` and far endpoints in `b̄`,
`c̄`; `va` is the one `Y`-edge between the `X`-trees of `b` and of `c`,
i.e. the edge `e₀ = (N_{X_b}, N_{X_c})` of `Ḡ_Y` — and `b̄, c̄` (resp.
`N_{X_b}, N_{X_c}`) are unchanged in `H` since only leaves left their
trees. Extension: a motion `m ∈ Mot_X(H)` extends to `Ḡ_X` iff a value
at `n_{va}` exists with both edge constraints, iff
`m(b̄) − m(c̄) ∈ ⟨A(s_b)⟩ + ⟨A(s_c)⟩`; at a generic draw of a certificate
colouring the extended network's motions are constants ((GR-9)), forcing
`m(b̄) = m(c̄)` — i.e. `D_X ∩ ⟨A(s_b), A(s_c)⟩ = 0`, and with the
dimension count this is (OC-40)(iv)'s `X`-sum; the `Y`-sum likewise with
`e₀`. (ii) Take `P` the single-class path: every achievable value is
`(Σ ± λ_e) A(s_i) ∈ ⟨A(s_i)⟩`; `dim D_X = 1` makes it equality. The
wall class is third: `A(s_i) ∈ ⟨A(s_b), A(s_c)⟩` with all three distinct
conic points is impossible (three distinct Veronese points are
independent, (FR-2)(ii)), and `i ∈ {cls(b), cls(c)}` would break the
direct sum. (iii) Same confinement on the `Y`-side gives
`dim D_Y ≤ 1 < 2`. ∎

**The wall is sufficient, not the whole story.** The census found the
`Q(g) = 0` signature at 27 first points; the (OC-42)(ii) predicate holds
at only **7** of them. At the other **20** the generator lies on a
component ruling line with **no** single-class path, persistently — at
**every** standing draw of that colouring (4/4 each, seeded
independently) — so a *second* structural confinement mechanism exists
(value-level cancellation through ≥ 4-class cycle relations is the
natural suspect: three distinct Veronese points are independent, so no
shorter relation can cancel); characterizing it is left open
(*what-would-change* item 4). Measured signature difference: the 7 wall
points all carry `dimK = 2` (never a ruling `M̂ ∧ w`), the 20 unexplained
ones all `dimK = 1`.

**Why the wall is invisible from ℚ-generic chart points.** At
`repin.star_generic` ℚ-points (OSCHU's pools) `rank(Q|_D) = 3` was
measured at 570/570 and 174/174 — the wall lives **only on the σ-fixed
locus**, where hinge lines collapse onto ≤ 2 ruling lines per body
((AC-9)'s world): it is a new instance of the (AC-9) lesson that σ-fixed
witnesses are structurally special. It does **not** contradict any landed
figure — and it does not even cost input (a) at the walled points
themselves: every rank-2 point of the census has `dimK ≤ 2` with **no**
ruling `M̂ ∧ w ⊆ D`, so by (OC-30)(ii)/(iii) its bad set is **≤ 2
points** of `M` and some `pt(a)` is good — (OC-31) consequence (c) —
i.e. **every standing point of the census, walled ones included,
individually witnesses input (a) at its (shape, split)**. The wall
kills only the rank-3 *criterion* ((OC-33)(ii) is sufficient, never
necessary — its (iii) separation, met here in the wild).

---

### Step O40 — (OC-43): the census — the naive route refuted at 27, the hunted route green at 174/174

> **(OC-43)** *(measured, POOL-OQ2; every count a class count; caps
> disclosed; each hit an individual exact witness, never a rate)*
> Population: `oschu.out_classes()` — the (OC-34) key, one representative
> per isomorphism class (174), at the **same pinned (shape, split)** as
> POOL-OC2. Hunt: the first ≤ 6 filter-passing colourings carrying
> both-block tree-triples (probe cap 48, colouring cap 2¹⁶) × ≤ 4 seeded
> parameter draws each (seed 20260825, per-class rng `20260825·100+ci`);
> a draw *stands* when it passes bodies-distinct, the (GR-5)
> closed-hub-neighbourhood LI clause, and **full exact-ℚ(i) Tay target on
> `G`**; every standing point runs every (OC-40)/(OC-41)/(OC-42)
> assertion.
>
> **(i)** *(the naive route is FALSE as a class statement)* at the FIRST
> standing point of the hunt, per class —
> `(rank(Q|_D), Q(g)≠0, rank Gram(D_Y), dimK, ruling M̂∧w ⊆ D, wallX, suppX, suppY)`:
>
> > `(3, T, 2, 1, F, F, secant, secant)` : **147**
> > `(2, F, 2, 2, F, T, line, secant)` : **7**  — the proven (OC-42) wall
> > `(2, F, 2, 1, F, F, line, secant)` : **20** — the second confinement
>
> — so "grid + first certificate colouring ⟹ `rank(Q|_D) = 3`" is
> **refuted at 27 of 174 classes** by exhibited persistent witnesses
> (each rank-2 colouring re-drawn: every standing draw, 4/4 seeded, gave
> the same `(2, F, 2)` row; the 7 wall colourings were left after one
> standing draw, their persistence being the (OC-42)(ii) *theorem*).
> On the whole pool: `rank(Q|_D) = 2 ⟺ Q(g) = 0 ⟺ g` on a component
> ruling line; `wallX ⟹ Q(g) = 0` held with no exception (asserted);
> the converse fails at the 20; and **the `Y`-block never degenerated
> anywhere** — `rank Gram(D_Y) = 2` at all 297 standing points (174 hits + 123 rank-2 points across the re-drawn colourings); the
> tangent-plane failure mode was never observed.
>
> **(ii)** *(the hunted route)* allowing the ≤ 6 colourings × ≤ 4 draws
> hunt: **174 of 174 classes carry an exact ℚ(i) σ-fixed target-rank
> grid chart point of `G` with `rank(Q|_D) = 3`** — 0 misses; every hit
> at draw 0 of its colouring, at colouring index ≤ 3 (caps 6 × 4 never
> approached). Hit rows: `(3, T, 2, 1, F, secant, secant)` : **174**.
> 43 classes hit past their first colouring: the 27 rank-2 cases above
> plus **16** whose earlier certificate colourings produced **no chart
> point at all** — every draw rejected by the (GR-5) closed-hub-
> neighbourhood LI clause (a 3-member `closedHubNbhd` mono-component in
> one family: (FR-4)'s placement-free legality, which the tree-triple
> filter does not test; concentrated on the `V5e8` stratum).
>
> **(iii)** *(support profile — how combinatorial the positives are)*
> at **all 174** hit points both supports are **secant**: `D_X` lies in
> the span of two component ruling lines of `H`'s `X`-forest with `g`
> on neither, and `D_Y` *equals* the span of two component ruling lines
> of the `Y`-forest — so at every winning point both block verdicts are
> of (OC-41)(iii)'s **parameter-free** kind: given those supports, the
> Grams are nonzero identically in the parameters, not merely at the
> exhibited draw.

Verification: `notes/scripts/w4/oqrank.py` (new, this pass); modes
`--controls` (the (OC-41) must-rejects, ~1 s), `--range A B` (the
census, run as **nine foreground chunks** of the single global
(|V|, label) class order — `0 30 / 30 60 / 60 90 / 90 115 / 115 140 /
140 150 / 150 160 / 160 167 / 167 174`, each within a 600 s budget,
202 / 187 / 210 / 194 / 252 / 151 / 473 / 153 / 557 s; per-class seeds
are keyed by the GLOBAL class index, so chunk boundaries move no
figure — the SIGZ multi-invocation precedent), `--census1`/`--census2`
(the same 174 split by parity — same figures, for a single-machine
re-run), `--validate` (controls + 3 + 3 classes). Asserted per
standing point: isotropy/conjugacy; `hcard` + the (GR-5) LI clause; full
ℚ(i) target rank; `σ = 0`; `dim D = 3`; `⋆D = D`; the `(1,2)` split with
the 1-dim block in family `col(vb)`; (Λ0d); (OC-31)(iii) + both
per-family sums; cross-block `B`-orthogonality; the (OC-41) identity;
`dimK ≤ 2`; `Q(g) = 0` whenever `g` lies on a component line; the wall
predicate ⟹ `Q(g) = 0`; and `Y`-wall vacuity.

---

### Step O41 — (OC-44): the theorem delivered, its exact quantifier, and the residue

> **(OC-44)** *(the landing statement)*
>
> **(i)** *(openness — one witness per (class, colouring) decides the
> generic verdict)* Fix a class, its pinned split, and a certificate
> colouring, and let `N` be its number of ruling classes. Inside the
> affine draw space `𝔸^N` of class parameters, the locus
>
> > `U = {draws : bodies distinct ∧ (GR-5) LI ∧ corank R(G) = 0 ∧ rank(Q|_D) = 3}`
>
> is **Zariski-open**: each clause is the non-vanishing of finitely many
> polynomials/minors in the draw (on the target-rank locus `Mot(H)` has
> locally constant dimension, so `D` has a locally rational basis and
> the Gram minors are rational). `𝔸^N` is irreducible, so one exact
> witness in `U` makes `U` **dense**: the POOL-OQ2 hit at that
> (class, colouring) proves `rank(Q|_D) = 3` — hence, with (OC-33)(ii),
> **input (a)** — at *every sufficiently generic draw of that
> colouring*, not just at the exhibited point.
>
> **(ii)** *(what is proven, exactly)* **At every one of the 174
> certified classes, at POOL-OC2's pinned (shape, split):
> input (a) holds at an exhibited exact ℚ(i) σ-fixed grid chart point,
> and at every sufficiently generic parameter draw of the exhibited
> certificate colouring — by the ⋆-eigen-block mechanism
> ((OC-40)–(OC-42)), the route Step O29 asked for.** The quantifier is
> per-class/per-colouring-generic; it is NOT the class-uniform input (a)
> ((GR-15)-adjacent, out of scope by the dispatch bar), and it is NOT
> "every certificate colouring" — (OC-43)(i) refutes that stronger form.
>
> **(iii)** *(the new named residual — the wall-avoiding colouring
> existence)* the statement "every certified class (every tight class
> shape) admits a certificate colouring with no single-class `b`–`c`
> `X`-path and with generic-draw `rank(Q|_D) = 3`" is **open** — the
> (GR-10)-shaped combinatorial-existence question this direction leaves,
> measured 174/174 within caps (never past the fourth certificate
> colouring). A min-max for it would upgrade
> (ii) to "at every certified class, uniformly-stated"; a tight class
> shape where **every** admissible certificate colouring is walled would
> be the route's genuine dead end (and still NOT a (K-tight) event —
> see the scope line below).

**Scope line — what a walled point is and is not.** A `rank(Q|_D) = 2`
grid point is **not** the spec's (K-tight) event: that event needs the
ruling `M̂ ∧ w` (`w` off the hub points) at **every** `σ = 0` chart point
of the shape, and OSCHU's POOL-OC2 already exhibits `rank(Q|_D) = 3`
ℚ-chart points at all 174 classes — so no class can be tight-evented by
grid evidence. Nor is a walled point even a failure of input (a) *at
that point*: `rank = 3` is sufficient, never necessary ((OC-33)(iii)),
and every rank-2 census point has `dimK ≤ 2` with no ruling `M̂ ∧ w`, so
its bad set is ≤ 2 points and the point itself witnesses input (a)
((OC-30)(ii)/(iii) + (OC-31)(c)). What the wall kills is only the
*naive recipe*; what survives is the hunted recipe with a per-class
certificate.

**Confidence verdict.** **(OC-40), (OC-41), (OC-42)(i)–(iii):
proven-informally** (derivations above from landed inputs, every clause
machine-asserted at every standing POOL-OQ2 point, must-reject controls
4/4). **(OC-43): measured** (exact ℚ(i), seeded, caps disclosed).
**(OC-44)(i)–(ii): proven-informally** (openness argument + the exact
witnesses; the disposition of the F11 rider for (i) is: *derivational,
consuming only this pass's own exhibited witnesses — no separate driver
tests the openness sentence itself*). **(OC-44)(iii): open**, with
174/174 evidence. Input (a) as a class-uniform statement: **OPEN,
unchanged**; (OC-8): **OPEN, unchanged**; no gap-map status moves.

**What would change this.** *(1)* A tight class shape whose **every**
admissible certificate colouring carries the (OC-42) wall — kills the
grid route to (a₁) at that class (the hunt cannot rescue it) and makes
(OC-44)(iii) FALSE; the route then needs off-grid points, i.e. leaves
the recipe class. *(2)* A proof of (OC-44)(iii) (most plausibly: a
colouring-exchange argument on the tree-triple structure, since the wall
is a single-class connectivity event the exchange can break) — upgrades
(OC-44)(ii) to the uniform per-class statement with no caps. *(3)* A
walled point that IS all-bad (`K = M̂ ∧ w` a genuine ruling, `B = M`)
at a class where some `σ = 0` stratum degenerates — would reopen the
(K-tight)-event reading; the census saw **zero** rulings at 297/297
standing points. *(4)* A *complete* combinatorial characterization of
`Q(g) = 0` — the (OC-42) wall covers 7 of the census's 27 rank-2
first points; the other 20 (`dimK = 1`, no single-class path, persistent
4/4 draws) need a second mechanism, most plausibly a value-level
cancellation through a ≥ 4-class cycle relation; characterizing it would
make the whole `X`-condition an O(1) read and (OC-44)(iii) decidable by
enumeration.

---

### Termination check (Steps O37–O41) — this direction's reading (the coordinator re-ran it)

- **E1: NO.** No `g`-flank — this direction never touches colouring
  goodness / `D = 0` shapes; nothing here is a CSP kill.
- **E2: NO.** The target is neither refuted nor unprovable-as-posed: it
  is **delivered at 174/174 under disclosed caps** with a named
  dispatchable successor ((OC-44)(iii), and the wall-characterization
  attack (4) above).
- **E3: NO — stays ARMED by GBAL, not fired.** The target is proven only
  per-class-generic, not class-uniformly; dispatchable attacks remain
  ((OC-44)(iii); (GR-15); (OC-8)). Firing is a coordinator action; this
  is a report.

Cap disclosure: every "not found" above is *not found under the stated
caps* (6 colourings × 4 draws × probe 48), never nonexistence.

---
