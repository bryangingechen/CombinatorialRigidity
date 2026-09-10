## §(K-bare-ext) — continuation (direction BZAVOID): the forced-degeneration T2 criterion is **UNSATISFIABLE for every graph** (BATTAIN's triangle-free premise is unnecessary — the trap is empty), the pencil stratum is identified as the **planar-atom molecular** stratum, and the two routes that identification suggests are both **closed** — the landed `G²` molecule apparatus by a measured dictionary gap, the transversality count by a structural impossibility

Direction **BZAVOID** (`notes/pencil/fanout.md` §"BZAVOID", ordinal 40), the
arc's forty-eighth and the **first pick made by user option selection between
slice shapes of a landed direction's own offer** — BATTAIN's `def₂ = def₃`
proof-of-concept declined in favour of **(BE-14) at the full statement**. Read
against *Steps BE9–BE13* (direction BATTAIN, whose figures are **cited, never
re-run**). Driver `notes/scripts/w4/bzavoid.py`
(`tri|crit|cap|pn|flat|sq|glue|validate`); all exact ℚ, every rng seeded.

**Status, stated before the mathematics.**

- **HIT shape 2, and it fired NEGATIVELY — reported first, as the spec requires.**
  The spec commissioned a hunt for a **triangle-carrying `G` whose `Y` is forced
  to the cone with `def₂ > def₃`**, off the habitat where triangles are legal.
  **That hunt is provably empty.** The two halves of BATTAIN's decidable T2
  criterion are **logically incompatible**: forcing needs the triangle-edge
  subgraph spanning and connected, and *that* forces `def₂ = 0`, hence
  `def₃ = 0 = def₂`. **(BE-15)**, exact, cap-free, quantified over **every**
  graph. So BATTAIN's habitat/triangle-free premise is **not why the arm was
  empty** — it was never inhabited, on or off the habitat.
- **The criterion GENERALIZES first, and dies in the general form.** The cone is
  the `k = 1` case of a whole family of universal caps, one per forced class
  partition. The general cap's deficiency is exactly
  `partitionDef₃(π(G)) = max(0, 6(k−1) − 5c)` — *a value `def₃(G)`'s own maximand
  already takes*. **The mechanism can only ever reproduce a bound the target
  already accounts for.** That is the structural reason the hunt was hopeless,
  and it replaces a triangle-freeness accident with an identity.
- **The pencil stratum is the PLANAR-ATOM MOLECULAR stratum.** The rank depends
  only on the hinge lines (read off `rigidityRows` / `hingeRowBlock`); on the
  pencil stratum the hinge of `uv` is the **join `p_u ∨ p_v`** of the two
  concurrency points, so the framework **is** Katoh–Tanigawa's hinge-concurrent
  (molecular) framework at atom positions `p`; and the pencil condition is
  exactly *every closed star of points is COPLANAR* — every atom is
  **trigonal-planar**. **(BE-16)**. `Y° ⊄ Z(G)` is thereby restated as a
  statement about a *point* configuration, and — this is the part that changes
  how to work on it — as an **existential**, not a genericity claim: `rank ≤ target`
  is universal, so **one** witness per graph settles `G`.
- **The transversality/dimension count offered for testing is structurally
  incapable of settling it, and this is a proof, not a difficulty report.**
  Containment `Y° ⊆ Z` needs only `dim Y° ≤ dim Z`, and `Z(G)` is known only to
  be a *proper* closed subset; at DZ, `dim Y° = 54 ≤ 59`. Whenever `G` has a
  hub the inequality is satisfiable, so **no codimension count can ever
  obstruct containment**. The spec's other half — "deform off the canonical
  point" — survives as the right *shape*, and (BE-15) now prices the deformation
  exactly: the cone undershoots by `def₂ − def₃ ≥ 0`, and `def₂ ≥ def₃` holds at
  **every** connected graph, so the cone is never better than the pencil generic.
- **The route the identification most obviously suggests is DEAD, with a
  witness.** The project has the molecular apparatus formalized (Phases 24–26):
  `molecularOfCentres`, the dictionary `molecular_finrank_motions_eq_square_ker`,
  `molecule_rank_formula`. **Its general-position gate is the literal negation of
  the pencil condition** — `IsGeneralPositionPlacement` demands every `≤ 4`-subset
  affinely independent, and the pencil condition at a degree-3 hub says the
  closed star's four points are dependent. And it is not a mere hypothesis
  mismatch: the dictionary's *sufficient condition for (BE-14)* is measured
  **FALSE** at DZ and two further habitat-shaped gadgets (gap `5`, `4`, `1`) while
  the molecular rank **attains** at all three. **(BE-17)**.
- **One structural reduction banked.** `def₃` is additive over a 1-vertex cut and
  the panel-hinge rank is `GL₄`-invariant, so pencil attainment **composes over
  1-cuts** and (BE-14) reduces to **2-connected** graphs. **(BE-18)**.
- **Verdict: (BE-14) remains OPEN; this is an HONEST PARTIAL, and it does not
  even reach the declined `def₂ = def₃` slice** (what (BE-15) proves in that
  direction is a *subclass* of it). **Classification: nothing here refutes
  `PencilPair K 3 G`, `hbareSplit`, or (BE-14)-for-all-`G`. Three ROUTE findings
  and one reduction. Not a PENCIL event.** **(BE-19)**. `hbareSplit` unchanged,
  carried as pinned; **no gap-map status moves except the
  (K-bare)/(K-bare-ext) row's development column**.

### Standing notation

Inherited from *Steps BE9–BE13* verbatim (`n := normal`, `p := point`, `W_e`,
`closedNbhd`, hub, `target(G) = 6(|V|−1) − def₃(G)`, `def₂ := max_P 3(|P|−1) − 2d(P)`,
`Y(G)`, `Z(G)`). Added here: **`T(G) ⊆ E(G)`** the set of edges lying in a
triangle; **`π(G)`** the partition of `V` into the vertex classes of the spanning
subgraph `T(G)` (a vertex in no triangle is its own singleton class); **`k := |π(G)|`**;
**`c`** the number of edges of `G` joining distinct classes.

### Step BE14 — the forced-degeneration criterion, generalized and then killed

BATTAIN's T2 criterion reads: *if `G`'s pencil conditions FORCE the cone, then
`HasPencilRealization K 3 G` fails exactly when `def₂(G) > def₃(G)`*. Its forcing
half runs on one mechanism, and it is worth writing out because the mechanism is
what generalizes. Put `S_v := span{n_w : w ∈ closedNbhd(v)}`, of dimension `≤ 3`
on `Y` by (BE-12). At adjacent `v, w` the shared bodies are
`closedNbhd(v) ∩ closedNbhd(w) = {v, w} ∪ (N(v) ∩ N(w))`, so three *independent*
shared normals require a common neighbour — a **triangle** — and then
`S_v = S_w` (two `3`-spaces sharing a `3`-space). So plane-class equality
propagates exactly along `T(G)`, and:

> **(BE-15)(i)** *(proven; the generalized cap)* On `Y(G)`, propagation confines
> each class `V_i ∈ π(G)` to a **local cone**: all its normals lie in one
> `3`-space `S_i`, i.e. all its panels pass through one point `q_i`, so every
> hinge internal to `V_i` passes through `q_i`. Running BATTAIN's (BE-13)
> splitting argument **per class** — quotient by `S̃_i := q_i ∧ K⁴`, and the
> `S̃_i`-part is the planar panel-and-pin system of `G[V_i]` — gives
> `dim{m|_{V_i}} = 3 + (3 + def₂(G[V_i])) = 6 + def₂(G[V_i])`. The `c` crossing
> edges impose at most `5` conditions each on `⊕_i` those spaces, so
>
> **`rank ≤ 6(|V| − 1) − max(0, 6(k−1) − 5c + Σ_i def₂(G[V_i]))`,**
>
> a universal cap for every forced class partition, specializing at `k = 1`
> (`c = 0`) to BATTAIN's `rank(cone) = 6(|V|−1) − def₂(G)`.

> **(BE-15)(ii)** *(proven; exact, cap-free, ALL graphs — the falsification arm,
> closed negatively)* **`Σ_i def₂(G[V_i]) = 0` always**, so the cap's deficiency
> is exactly `max(0, 6(k−1) − 5c) = max(0, partitionDef₃(π(G)))`, which is
> `≤ def₃(G)` **by definition** — `def₃` is the maximum of `partitionDef₃` over
> *all* partitions, and `π(G)` is one of them. **Therefore no graph whatsoever
> is refutable by the forced-degeneration mechanism**, and in particular the
> spec's hunt for a triangle-carrying `G` with a forced cone and `def₂ > def₃`
> is **empty by an argument, not by exhaustion**.
>
> > **SCOPE CORRECTION, 2026-08-26 (direction BINDUC, *Step BE22* / (BE-23)(ii))
> > — read this before quoting the sentence above.** The propagation rule this
> > step derives is **adjacent-pair** forcing, and *that* is what needs a
> > triangle. The **general** rule is weaker-hypothesised and fires without one:
> > `π_v` is forced to `π` as soon as `closedNbhd(v)` holds **three independent
> > points already in `π`**, which can accumulate from three *non-adjacent*
> > neighbours — `K_{3,3}` is **forced flat and triangle-free**. So the forced
> > class partition can be **strictly coarser** than `π(G)`'s `T(G)`-components,
> > and on those coarser classes the *"each class is triangle-covered, hence
> > `def₂ = 0`"* step of the proof above **does not apply**. What (BE-15)(ii)
> > therefore establishes, exactly: **the TRIANGLE-forced mechanism is closed at
> > every graph, cap-free and by an argument** — unchanged, and the proof above
> > is sound for it. The **general** forced-degeneration mechanism is closed only
> > as **MEASURED** ((BE-23)(ii): 25 270 forced-flat instances under an
> > *aggressive* closure, zero with `def₂ > def₃`; the measured statement is the
> > stronger *forced flat ⇒ `def₂ = def₃`*), with a structural sketch and **no
> > proof**. The unqualified phrase *"no graph whatsoever"* above therefore
> > over-reaches beyond the triangle rule; a proof of (BE-23)(ii) is the named
> > target that would restore it in full, and is recorded as the disproof side's
> > highest-value single search.
>
> *Proof of `Σ_i def₂(G[V_i]) = 0`.* Fix a class `V_i` with `|V_i| ≥ 2`. Its
> `T`-component `T_i` is connected and spanning on `V_i`, and every edge of `T_i`
> lies in a triangle of `G`; the triangle's other two edges also lie in a
> triangle, hence in `T`, hence (sharing a vertex with `T_i`) in `T_i` — so the
> triangle is *inside* `V_i` and `T_i`'s edges are **covered by triangles of
> `T_i`**. In the planar (`D = 3`) body-pin matroid a triangle is an isostatic
> **rigid** unit (`3·3 − 2·3 = 3`, the trivial count), and two rigid units
> sharing a **body** — which is what sharing a *vertex* means when vertices are
> bodies — are rigid together. `T_i` connected makes the triangle-intersection
> graph connected, so all of `V_i` is one rigid body: `def₂(T_i) = 0`, and
> `def₂` is monotone decreasing in edges, so `def₂(G[V_i]) = 0`. Singleton
> classes have `def₂ = 0` trivially. ∎
>
> Two corollaries fall out. **(a)** `def₂ = 0 ⇒ def₃ = 0`
> (`2d ≥ 3(q−1) ⇒ 5d ≥ 7.5(q−1) ≥ 6(q−1)`), so at a genuinely forced cone
> (`k = 1`) the cone **attains** in closed form; hence **(BE-14) holds, with a
> closed-form witness and no genericity argument at all, for every graph whose
> triangle-edge subgraph is spanning and connected** — every `K_n`, every
> triangular cactus, every graph in which every edge lies in a triangle. This is
> a *subclass* of BATTAIN's declined `def₂ = def₃` slice (it forces
> `def₂ = def₃ = 0`), so it is **not** the declined partial and not the
> deliverable; it is a free corollary, recorded because it is the arc's first
> **combinatorially checkable** proved attainment class.
> **(b)** On a connected `G`, **`def₂ ≥ def₃`**: at a `q`-part partition of a
> connected graph `d ≥ q − 1`, so `3(q−1) − 2d ≥ 6(q−1) − 5d`. The cone
> therefore *never* beats the pencil generic, and the exact deficit the
> deformation must recover is `def₂ − def₃`.

**Machine validation.** `bzavoid.py tri` (102 s): **EXHAUSTIVE over all edge sets
on `n ≤ 7` vertices — 375 719 connected spanning triangle-covered graphs, ZERO
with `def₂ > 0`** (`n = 7` alone contributes 370 437 of `2²¹` edge sets), plus
1 200 sampled connected unions of triangles on 8–10 vertices, all `def₂ = 0`.
`crit` (10 s): **EXHAUSTIVE over all 27 474 connected graphs on `n ≤ 6`** — `0`
fire, `16 894` **tight** (`cap = def₃` exactly), `Σ_i def₂(G[V_i]) = 0` and
`def₂ ≥ def₃` at every one; plus 1 336 sparse random connected graphs on
`n = 7…12`, `0` fire. `cap` (2 s): `K4` at `k = 1` reproduces BATTAIN's law
(cap deficiency `= def₂`); **DZ** is triangle-free so `π` is the *finest*
partition (`k = 20`, `c = 23`) and the cap deficiency is
`max(0, 114 − 115) = 0` — no cap at all; the necklaces `Nk_k`, `k = 3…7`, have
**one class per blob** exactly as predicted (`k` classes, `k` crossing edges) with
cap deficiency `max(0, k − 6)`, **equal to `def₃`** at `k = 7` and `0` below —
which is precisely why BATTAIN's `localcone` found attainment there.

**What this does to BATTAIN's reading, and it is a strengthening not a
correction.** *Step BE13* explained the empty arm structurally — "forcing needs a
triangle, and the habitat is triangle-free by `hnoRigid`" — with a Lean-level
citation (`Escape.lean:411–418`). That explanation is **sound but not needed**:
the arm is empty **on and off the habitat**, and the reason is not a property of
the habitat but an identity between the forcing mechanism's cap and `def₃`'s own
maximand. The `hnoRigid` citation stops being the load-bearing step and becomes
a special case.

### Step BE15 — the pencil stratum IS the planar-atom molecular stratum

**Read off the Lean bodies, not a docstring.** `rigidityRows F` is
`{hingeRow u v r | F.graph.IsLink e u v, r ∈ F.hingeRowBlock e}`
(`RigidityMatrix/Basic.lean:654`) and `hingeRowBlock F e` is
`(span {F.supportExtensor e}).dualAnnihilator` (`ibid.:435`). So:

> **(BE-16)(i)** *(proven; exact, from the definitions)* `finrank span F.rigidityRows`
> is a function of the graph and the assignment `e ↦ span{F.supportExtensor e}`
> **alone** — the panels `normal` and the points `point` enter only by
> constraining which line assignments are legal. In particular the pencil
> stratum's rank is a function of the **hinge lines**.

> **(BE-16)(ii)** *(proven; the dual of (BE-12), via the landed self-duality)*
> Eliminating `n` rather than `p` from (BE-10): the conditions involving `n_u`
> are `n_u ⬝ᵥ p_v = 0` for every `v ∈ closedNbhd(u)` (the closed-neighbourhood
> relation is symmetric), so a legal `n_u` exists iff
> `dim span{p_v : v ∈ closedNbhd(u)} ≤ 3`. Hence
>
> **`∃ n : the pencil conditions hold at p ⟺ for every u, the points of
> closedNbhd(u) are COPLANAR in P³`.**
>
> This is (BE-12) with `(p, n)` swapped, matching
> `hasPencilPanelRealization_mapExtensor_screwComplementIso` on the nose.

> **(BE-16)(iii)** *(proven; the identification)* Where adjacent concurrency
> points are projectively distinct, `p_u, p_v ∈ W_e` with `dim W_e = 2` forces
> `W_e = span(p_u, p_v)`: **the hinge of `uv` is the JOIN of the two concurrency
> points.** Combining with (i): on that locus the pencil framework's rigidity
> matrix **is** the molecular (hinge-concurrent) body-hinge matrix at atom
> positions `p` — the object the project already carries as
> `molecularOfCentres` (`Molecule/Dictionary.lean:54`, whose own docstring pins
> Katoh–Tanigawa's hinge-concurrency at KT 2011 p. 671). So (BE-14) reads:
>
> > *For every graph `G` there is a point configuration `p : V → P³` with every
> > closed star coplanar at which the molecular body-hinge framework attains
> > `6(|V|−1) − def₃(G)`.*
>
> Every atom's bonds are coplanar — the configuration is **all-trigonal-planar**.
> Two consequences for how to work on it. **(a)** The statement is
> **existential**: `rank ≤ target` holds universally (*Step BE12*), so one
> witness per graph settles `G` and **no genericity argument is required** —
> `Y° ⊄ Z(G)` is an equivalent but strictly less constructive phrasing of the
> same thing. **(b)** The object to be built is a *point* configuration subject
> to one determinant per hub, not a panel configuration; the harness has in fact
> always worked in this form (`kbare_common.build_rigidity` is literally the
> molecular matrix built from `pt`, and `verify_pencil_witness` checks closed-star
> coplanarity), which the workbook had not stated.

> **(BE-16)(iv)** *(proven; a structural impossibility, no measurement)* **The
> transversality/dimension count cannot settle `Y° ⊄ Z(G)`, ever.** Containment
> requires only `dim Y° ≤ dim Z(G)`; `Z(G)` is known only to be a proper closed
> subset of the panel configuration space, so `dim Z(G) ≤ 3|V| − 1` is all that
> is available, while `dim Y° = 3|V| − Σ_{hubs}(deg v − 2) ≤ 3|V| − 1` as soon as
> `G` has a hub. The two are compatible at **every** graph with a hub, so no
> codimension comparison can produce a contradiction. At DZ: ambient `60`,
> `codim Y° = 6`, `dim Y° = 54`, against `dim Z ≤ 59`.

**Machine validation** (`bzavoid.py pn`, 3 s). At DZ, on a `Y`-generic exact-ℚ
sample: all **20** closed stars have point-span `≤ 3` (`0` degenerate below `3`);
`kbare_common.verify_pencil_witness` recovers a legal normal at every body **from
the points alone**; the `(p, n, W)` carrier and the molecular carrier at the same
points return the **same exact rank 114 = target**; and every `W_e` is verified
to be `span(p_u, p_v)` with `p_u ≁ p_v` at all 23 edges. The dimension arithmetic
of (iv) is printed in the same mode.

### Step BE16 — the landed molecule apparatus is unavailable, and its route is dead with a witness

The identification of *Step BE15* points straight at Phases 24–26: the project
has `molecularOfCentres`, the dictionary
`molecular_finrank_motions_eq_square_ker` (`Molecule/Dictionary.lean:321`), and
`molecule_rank_formula` — `r(G²) = 3|V| − 6 − def(G̃)`
(`Molecule/Application.lean:185`; the formula is due to Jackson–Jordán 2008 and
made unconditional by Katoh–Tanigawa's Theorem 5.6, per the decl's own
docstring). It looks like a ready-made route. **It is not.**

> **(BE-17)(i)** *(proven; the gate is the negation of the hypothesis)* The
> dictionary's hypothesis `IsGeneralPositionPlacement c`
> (`GeneralPositionPlacement.lean:59`) is *"every `s : Finset V` with
> `s.card ≤ 4` has `AffineIndependent ℝ (fun i : s => p i)`"* — **no four points
> coplanar**. The pencil condition at a degree-3 hub `v` says precisely that the
> four points of `closedNbhd(v)` **are** affinely dependent. So the pencil
> stratum lies entirely inside the gate's complement, at *every* hub: the landed
> dictionary is unavailable at every point of `Y` that has a hub at all.

> **(BE-17)(ii)** *(proven; the mechanism)* The failure is real, not a
> convenience of the hypothesis. `G²` is the union of the closed-star cliques,
> and a **coplanar** `K₄` has bar-joint rank `5`, not `6` — for a coplanar
> configuration the bar equations `(p_i − p_j) ⬝ (x_i − x_j) = 0` never see the
> out-of-plane velocity component, so the flat tetrahedron carries one extra
> flex. The dictionary's surjectivity is exactly the claim that a `G²`-flex
> restricted to a closed star comes from a screw, and at a flat star it need
> not.

> **(BE-17)(iii)** *(measured; the route is dead, cap disclosed)* The
> dictionary's **injective** half survives without the gate, giving
> `dim Z_mol ≤ dim ker R(G², p)`; so a **sufficient** condition for (BE-14) at
> `G` is *"`rank R(G², p) = 3|V| − 6 − def₃(G)` at some coplanar-star `p`"*. That
> condition is **FALSE** at every shape probed, while the molecular rank
> attains:
>
> | shape | \|V\| | def₃ | generic `rank R(G²)` | best pencil `rank R(G²)` | deficit | `dim ker R(G²)` vs `dim Z_mol` | molecular rank / target |
> |---|---|---|---|---|---|---|---|
> | **DZ** | 20 | 0 | 54 | **49** | 5 | 11 vs 6 (gap 5) | **114 / 114** ✓ |
> | `spider(5,5,5)+centre` | 16 | 0 | 42 | **38** | 4 | 10 vs 6 (gap 4) | **90 / 90** ✓ |
> | `theta(4,4,4)+centre` | 13 | 0 | 33 | **32** | 1 | 7 vs 6 (gap 1) | **72 / 72** ✓ |
>
> Each pencil figure is the **maximum over 6 seeded draws** of the `Y` sampler —
> rank is lower semicontinuous, so a single draw would only be a lower bound
> (BATTAIN's own recorded trap, *Step BE12*'s methodological correction). A
> generic (non-pencil) control attains `3|V| − 6 − def₃` at all three, which
> validates the matrix. **So the `G²` route's condition is strictly stronger than
> (BE-14) and fails at the arc's flagship gadget: the route cannot be
> class-uniform.** Cap: 3 shapes with a reachable `Y` sample, 6 draws each; the
> necklace `Nk_3` had **no** usable `Y` sample at any seed (every vertex is a
> hub, so the private-variable tower has no private variable) and is disclosed
> as skipped.

**What this costs and what it buys.** It costs the most attractive-looking route
on the board: the arc cannot borrow Phases 24–26 wholesale. It buys a sharp
statement of what a `G²`-side attack would have to do — **re-prove the dictionary
(or just its surjectivity) under a hypothesis compatible with flat stars**, which
is a genuinely new lemma about flat-star molecular frameworks, and *then* still
prove a degenerate-placement bar-joint rank statement. Both halves are new
mathematics; nothing is reusable as-is.

### Step BE17 — pencil attainment composes over a 1-vertex cut

> **(BE-18)** *(proven; `def₃` half enumerated, rank half elementary)* Let
> `G = G₁ ∪ G₂` with `V(G₁) ∩ V(G₂) = {v}`. Then
> **`def₃(G) = def₃(G₁) + def₃(G₂)`**, and if each `G_i` attains on its pencil
> stratum then so does `G`. Hence **(BE-14) reduces to 2-connected graphs.**
>
> *`def₃` additivity.* `≥`: merge the parts containing `v`; the two maximands add
> (`|P| = |P₁| + |P₂| − 1`, `d(P) = d₁ + d₂`). `≤`: restrict a partition `P` of
> `V` to `V₁, V₂`; with `a, b` the numbers of parts meeting `V₁, V₂` and `m ≥ 1`
> the number meeting both (the part containing `v` does),
> `6(|P|−1) − 5d(P) = [6(a−1) − 5d₁] + [6(b−1) − 5d₂] − 6(m−1) ≤ def₃(G₁) + def₃(G₂)`.
> *Alignment.* `Λ²A` for `A ∈ GL₄` carries `M(C)` isomorphically to
> `M(Λ²A·C)`, so the panel-hinge rank is `GL₄`-invariant — elementary, no appeal
> to projective-invariance theory needed — and `PGL₄` is transitive on
> (plane, point-on-that-plane) flags. Transport `G₂`'s realization so its
> `v`-panel and `v`-point coincide with `G₁`'s; then `closedNbhd_G(v)`'s points
> all lie in the **one** shared plane, so the pencil condition holds at `v`, and
> at every other vertex the closed star is unchanged.
> *Rank.* `M(G)` is the fibre product of `M(G₁), M(G₂)` over the shared body's
> screw, so `dim M = dim M₁ + dim M₂ − 6` and `rank(G) = rank(G₁) + rank(G₂)`.

**Machine validation** (`bzavoid.py glue`, 0.4 s). **907** random 1-cut gluings
on `≤ 11` vertices: `def₃(G) = def₃(G₁) + def₃(G₂)` at every one. A genuine
glued pencil pair (two triangles sharing a body, all closed stars coplanar):
`rank 24 = 12 + 12`, targets `24 = 12 + 12`, all three attaining.

**Honest weight of this.** Combined with `def₂ ≥ def₃` and the equality-case
slice, the reduction adds nothing *new* on the `def₂ = def₃` class (`def₂` is
1-cut-additive too, so the class is block-local already). Its value is as a
composition rule for a *future* attainment theorem, and as a statement that the
open problem is genuinely about 2-connected graphs.

### Step BE18 — the verdict, the classification, and the price

**Which HIT shape this is: shape 2 fired NEGATIVELY, shape 1 reached only an
honest partial, shape 3 re-priced.**

**Shape 2 (reported first, as required).** *Is there a triangle-carrying `G`
whose `Y` is forced to the cone with `def₂ > def₃`?* **No — and not "none found
under cap": none exists.** (BE-15). The **classification the direction-A pivot
rule demands** is therefore short: **nothing is refuted.** Not `PencilPair K 3 G`,
not `hbareSplit`, not (BE-14)-for-all-`G`. What is refuted is a **route** — three
of them:

1. the forced-degeneration T2 criterion, as a live refutation route for **any**
   graph (cap-free, exact);
2. the `G²` / landed-molecule-apparatus route to (BE-14) (measured, 3 shapes ×
   6 draws, gap `5/4/1`);
3. the transversality/dimension-count reading (structurally, by an inequality).

None is a PENCIL event; all three are route findings, and the first *strengthens*
BATTAIN's own reading rather than correcting it.

**Shape 1.** *(BE-14) proven, or reduced with the residual named and quantified.*
**Not proven. Reduced only to 2-connected graphs (BE-18), with the statement
restated in its constructive existential form (BE-16).** Stated with the exact
quantifier: what remains open is

> `∀ G` 2-connected, `∃ p : V(G) → P³` with `{p_w : w ∈ closedNbhd(v)}` coplanar
> for every `v` and `p_u ≁ p_v` on edges, such that the molecular body-hinge
> rigidity matrix at `p` has rank `6(|V|−1) − def₃(G)`.

**This return does NOT reach the declined `def₂ = def₃` partial.** (BE-15)(a)
proves (BE-14) on the *forced-triangle* class, which is a **subclass** of
`def₂ = def₃` (it forces both to `0`), so it is strictly less than what the user
declined. Saying so plainly: **this is an honest partial**, and the remaining
distance to the phase target is the whole of the residual above.

**Shape 3.** *The price, re-quoted against BATTAIN's.*

- **The `∃`-seed + deformation-repair alternative is unchanged.** Nothing here
  lowers §(K-tight) *Step 5*'s chartless wall; this direction did not touch it.
- **Direct attainment got cheaper in exactly one way and dearer in one other.**
  Cheaper: the object to be built is now a *point* configuration with one
  determinant per hub, the statement is **existential** with no genericity
  argument required, and 2-connectivity may be assumed. Dearer: the one route
  that would have imported a landed 700-line apparatus is closed, so the
  construction has to be built from scratch. Net, the honest reading is that the
  problem is **the same size as it was after BATTAIN**, with two dead ends
  removed and its shape stated correctly.
- **What a successor should attack, in the order this pass would rank it.**
  (1) An **inductive construction** on the point side: build coplanar-star
  configurations along a graph decomposition (1-cuts are done; 2-cuts look
  routine by the same `GL₄` alignment, with `def₃(G) = def₃(G₁) + def₃(G₂) − 6`
  to be checked). **DONE and CORRECTED 2026-08-26 (BINDUC, *Steps BE19–BE23*):
  the construction was carried out, the base turned out FREE (3-connected ⇒
  `def₂ = 0`), and both halves of this bullet's "routine" were wrong — the `− 6`
  is REFUTED and the rank half needs a strengthened statement. Read *Step BE20*
  onward, not this bullet.** (2) The **`def₂ = def₃` closed-form slice** as the base case —
  still unclaimed and still the smallest genuinely new attainment theorem.
  (3) A **flat-star dictionary**: re-prove
  `molecular_finrank_motions_eq_square_ker`'s surjectivity under a hypothesis
  that admits coplanar closed stars; that is a self-contained lemma, and if it
  came with a corrected `G²` rank statement it would revive route 2.

### Verification

`python3 notes/scripts/w4/bzavoid.py tri` (102 s — the exhaustive `n ≤ 7` sweep,
375 719 graphs, plus the 8–10-vertex sample); `crit` (10 s — 27 474 connected
graphs exhaustive at `n ≤ 6`, 1 336 sparse random at `n = 7…12`, with the two
deficiency oracles cross-checked at every exhaustive entry); `cap` (2 s — `K4`,
DZ, the necklaces `k = 3…7`); `pn` (3 s — DZ, exact rank `114` by both carriers,
20/20 coplanar closed stars, the dimension arithmetic); `flat` (3 s — the
coplanar-`K₄` rank `5` vs `6`, and 6/6 DZ hubs violating
`IsGeneralPositionPlacement`); `sq` (6 s — the three shapes above at 6 draws each,
with a generic control); `glue` (0.4 s — 907 gluings, the glued pencil pair).
`validate` runs all of them **except** `tri`'s `n = 7` tier (it runs `n ≤ 6`
there) in **16 s**; run `tri` separately for the full sweep.

### Caps, disclosed rather than smoothed

1. **The exhaustive `tri` sweep stops at `n = 7`.** `2²¹` edge sets is where the
   Python loop cost turns; `n = 8, 9, 10` are covered only by 1 200 *sampled*
   connected unions of triangles. The claim `def₂ = 0` at larger `n` rests on the
   **proof**, not the enumeration.
2. **`crit`'s exhaustive tier stops at `n = 6`;** `n = 7…12` is a 1 336-member
   sparse random sample, not an enumeration. Again the general claim is proved,
   not exhausted.
3. **Deficiency oracles.** `def₂` is the exact `2^{|V|}` partition oracle
   throughout (so the `Nk_k` rows for `k ≥ 5` report `def₂ = None`, and their
   `def₂ = k − 3` is BATTAIN's derived closed form, cited). `def₃` is the exact
   oracle to `|V| ≤ 8` and the `(6,6)`-count pebble oracle above; the two are
   **cross-checked against each other at all 27 474 exhaustive `crit` entries**
   and agree.
4. **(BE-15)(i)'s cap formula inherits (BE-13)'s status** — *proven-informally*,
   because the per-class splitting imports the planar (`d = 2`) body-pin rank
   formula. **(BE-15)(ii)'s conclusion does not**: it needs only
   `def₂(G[V_i]) = 0` and the definitional inequality, both proved and
   enumerated here, so the **falsification arm's closure does not rest on
   (BE-13)**.
5. **The propagation and the cap both assume pairwise-distinct panels inside a
   class.** If `n_u = n_v` at an internal edge, `n_u^⊥ ∩ n_v^⊥` is 3-dimensional
   and `W_e` need not pass through `q_i`; likewise three shared closed-star
   normals may be *dependent*, in which case propagation does not fire. Both
   make forcing **harder**, so neither weakens (BE-15)(ii); both are inherited
   from BATTAIN's own `sample_cone` (which enforces pairwise independence).
6. **(BE-16)(iii) is stated on the locus where adjacent points are distinct.** On
   the complement the hinge keeps the `W_e` freedom of (BE-10) and the framework
   is *not* molecular — the extreme case being BATTAIN's cone, where all points
   coincide. That locus is proper and closed, and the affine class is dense in
   `Y°` by (BE-12)(iii); the identification is therefore dense-generic, not
   everywhere.
7. **`sq`'s three shapes are `def₃ = 0` and degree-3-hubbed**, drawn through the
   same `solve_schedule` tower BATTAIN's cap 1/cap 2 disclose. A `def₃ > 0` shape
   and a degree-`≥ 4` hub are **unprobed** for the `G²` gap. The gap being
   nonzero is a *measured* claim: 6 draws per shape, best taken. **All `G²`
   ranks are exact ℚ, deliberately** — a GF(p) rank is only a *lower* bound on
   the rational one, which is the wrong direction for a shortfall claim; the
   molecular ranks stay GF(p) because there `rank ≤ target` is universal, so a
   mod-`p` reading *equal* to the target sandwiches the exact rank.
8. **(BE-18)'s 2-cut extension is asserted as "looks routine", not proved or
   measured.** Only the 1-cut case is established. **SUPERSEDED 2026-08-26
   (BINDUC, *Step BE20*): the asserted `def₃(G) = def₃(G₁) + def₃(G₂) − 6` is
   REFUTED** — it goes negative (impossible, since `def₃ ≥ 0`) at 87 % of 10 804
   enumerated gluings — and is replaced by the exact law
   `def₃(G) = max(g₁+g₂, f₁+f₂−6)`, both directions proved. The word "routine"
   was wrong in both halves: the rank half needs a **strengthened** inductive
   statement plus a general-position input the residual gauge group cannot
   supply. This cap is the reason it was written as a cap.
9. **No `.lean`** — the standing 2026-08-05 Lean hold. Every Lean citation here
   is a *read* of a landed body (`rigidityRows`, `hingeRowBlock`,
   `HasPencilPanelRealization`, `partitionDef`, `IsGeneralPositionPlacement`,
   `molecularOfCentres`, `molecular_finrank_motions_eq_square_ker`,
   `molecule_rank_formula`), never an edit.

### Harness note — the `kbare/` sibling-import set gains its SECOND `w4/` consumer

`notes/scripts/README.md` *Harness debt* → *the `kbare/` sibling imports;
**UNPAID***. BATTAIN was the first `w4/` consumer; `bzavoid.py` is the **second**,
and it also becomes the first consumer of `battain` itself. **No move made** (a
dispatch may not edit a landed driver another direction may be importing in
flight). Recorded consumer list, extended:

| name | current home | consumers |
|---|---|---|
| `dz_gadget` | `danger` | `optc`, `breakhunt`, `w4/battain`, **`w4/bzavoid`** (4) |
| `spider`, `exact_deficiency`, `build_rigidity`, `verify_pencil_witness`, `rank_modp`, `rint`, `verts_of` | `kbare_common` | …, `w4/battain`, **`w4/bzavoid`** |
| `def2_exact`, `sample_Y`, `solve_schedule`, `closed_star`, `span_dim`, `necklace`, `target_of`, `rows_from_W` | `w4/battain` | **`w4/bzavoid`** (1 — first external consumer of any `battain` device) |
| `deficiency` (pebble) | `w4/nogood_subdiv` | …, `w4/battain`, **`w4/bzavoid`** |

If the eventual move-down happens, `bzavoid.py` joins the acceptance test
alongside `battain.py`.

### TERMINATION check (E1/E2/E3) — this direction's reading; the coordinator re-runs it

- **(E1) NO.** No `g`-flank. This direction is on **(K-bare)**, not the §(K-grid)
  ledger; it computes deficiencies and ranks of the *pencil / molecular* rigidity
  matrix on and off `hbareSplit`'s habitat, and touches no colouring, matching,
  or `d_adm` object. Clauses (i)–(v) have nothing to fire on.
- **(E2) NO.** No ledger entry is refuted or shown unprovable-as-posed. The
  landed claim this pass **strengthens** is BATTAIN's *Step BE13* reading of why
  T2 is unreachable, and it strengthens it **with a successor in hand**
  ((BE-15)); `hbareSplit` is unchanged and (BE-14) is unchanged in status.
- **(E3) ARMED by GBAL, DOES NOT FIRE, and this direction does not fire it.** E3
  fires only on a HIT completing **entry 1 / (a′)**; this pass is on (K-bare)
  and does not touch (a′).

### Confidence verdict

- **(BE-15)(ii) — the falsification arm's closure: PROVEN.** Exact, cap-free,
  quantified over every graph, and independent of (BE-13)'s informal ingredient.
  Enumerated at 375 719 + 27 474 graphs with zero exceptions.
- **(BE-15)(i) — the generalized cap formula: PROVEN-INFORMALLY**, inheriting
  (BE-13)'s imported planar rank formula. Its arithmetic is verified at `K4`, DZ
  and `Nk_{3…7}`.
- **(BE-15) corollaries (a) forced-triangle attainment and (b) `def₂ ≥ def₃` on
  connected graphs: PROVEN** ((a) modulo (BE-13) for the cone law; (b) exact and
  enumerated).
- **(BE-16)(i), (ii), (iv): PROVEN** — read off the Lean bodies and, for (iv),
  a one-line dimension inequality. **(BE-16)(iii): PROVEN on the
  distinct-adjacent-points locus** (cap 6).
- **(BE-17)(i), (ii): PROVEN** (the gate is literally the negation; the flat-`K₄`
  rank deficit is exact). **(BE-17)(iii): MEASURED** — 3 shapes, 6 draws each,
  gap `5/4/1`, generic control matching; a cap report on the *nonzero-ness* of
  the gap, decisive as a route verdict.
- **(BE-18): PROVEN** — `def₃` additivity both directions plus elementary
  `GL₄`-invariance; enumerated at 907 gluings. The 2-cut extension is **OPEN**.
- **(BE-14): OPEN**, unchanged in status, now reduced to 2-connected graphs and
  restated existentially. **`hbareSplit`: OPEN and unchanged, carried as
  pinned.** **Not a PENCIL event.**

**What would change this.** For **(BE-15)(ii)**, a connected spanning
triangle-covered graph with `def₂ > 0` — i.e. a failure of the body-pin gluing
lemma "two rigid clusters sharing a *body* are rigid", which is where the whole
argument lives; 375 719 exhaustive checks say no. For **(BE-16)(iii)**, an error
in reading `hingeRowBlock` as depending only on `span{supportExtensor e}` (it
does, by definition) or a pencil realization whose adjacent points coincide
*everywhere* off the cone. For **(BE-17)(iii)**, a coplanar-star placement at
which `rank R(G², p)` **does** reach `3|V| − 6 − def₃` — which would revive the
`G²` route and is exactly what a 7th draw or a `def₃ > 0` shape could produce, so
this is the one measured claim a successor should re-run first. For **(BE-14)**,
either a construction of one coplanar-star point configuration per 2-connected
graph attaining the target — the theorem — or a graph at which none exists, which
by (BE-15) **cannot** be certified by any forced-degeneration cap and would need
a genuinely new universal-cap mechanism.
