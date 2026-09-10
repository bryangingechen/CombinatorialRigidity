## §(K-bare-ext) — continuation (direction BDECOR): the ACHIEVABLE DECORATIONS ARE A PRODUCT OF EAR CHAINS — at a fixed flag assignment on the hub set the legal configurations of ANY piece are a *product*, one factor per topological branch, modulo the cross-branch proviso `G`, so the per-child sets (BE-62)(iii) left open **are never needed past ears**; the coordinator's job-2 hypothesis is CONFIRMED and STRENGTHENED beyond the P-layer, the theta child's law falls out as a corollary with an exact generic dimension `max(0, Σ min(a_j,6) − 12)` and welded attainment FREE; the residual coupling is the **flag base**, which is the arc's own §(K-chart) object, so (CH-1) already supplies irreducibility, rationality and dense ℚ-points; and the small-`m` correction (BE-30)(iii) does **not** stay inside its branch — at `π_x = π_y` two length-3 branches have EQUAL spans and `ρ̄` **exceeds** general position by up to 3, at configurations that are exactly the NON-ATTAINING ones (BE-22)(iii)'s hypothesis excludes

Direction **BDECOR** (`notes/pencil/fanout.md` §"BDECOR", ordinal 53), the arc's
sixty-first, at **(BE-62)(iii)'s named residue** — *which decoration tuples
`{ρ̄_e}` are simultaneously achievable by pencil configurations of an internal
R-node piece* — BRNODE's successor (1), taken only after the coordinator
re-ran the F26 consumer trace. Read against *Steps BE58–BE62* (BRNODE, the
decorated-skeleton law), *Steps BE29–BE33* (BIMAGE, the ear's image and
(BE-30)(ii)/(iii)), *Steps BE19–BE23* (BINDUC, (BE-22)) and **§(K-chart)
*Steps CH2–CH3*** (CIRR, the chart tower), whose figures are **cited, never
re-run**. Driver `notes/scripts/w4/bdecor.py`
(`prod|theta|small|chart|attain|validate`), importing `brnode` / `bsharp` /
`bimage` / `binduc` / `bwin` / `widened` / `nogood_subdiv` **read-only**, and
through them the rest of the chain; all exact ℚ, every rng seeded from the
printed literal `20260901`, every drawn configuration through
`assert_generic_star` **and** `kbare_common.verify_pencil_witness`.

**WHICH DELIVERABLE THIS IS — said at the top, as the spec demands.**
**HIT shapes 1 and 2, together and in a stronger form than either was
stated.** Job 1 asked for the per-child achievable set past ears; the answer
is that **there is no "past ears"**: recursing (BE-62)(iii)'s own fibration
down to the **topological skeleton** — hubs joined by one edge per maximal
degree-2 branch — makes every child an ear, and at a fixed legal flag
assignment the configurations are the **product** of the per-branch
ear sets, **intersected with the cross-branch proviso `G`** ((BE-64)) — `G` is
disclosed at every statement of the theorem and is **never shown nonempty in
general**, which is this direction's own named gap. Job 2's hypothesis (*the P-node layer may be free*) is
therefore **CONFIRMED and STRENGTHENED**: every layer is free at fixed flags,
and the theta child's set is a corollary ((BE-66)) — which is exactly the
relocation the spec predicted, *"the direction's real content is half (B)"*.
Its **weak link (b)**, the degree-3 terminal, is **CHECKED and CLEARED**, with
the reason; its **weak link (a)**, the small-`m` correction, is **CONFIRMED as
real and sharper than predicted** — it propagates *through* the P-node and
moves `ρ̄` off general position by up to 3. The residual coupling is located
in the **flag base** ((BE-65)), which is the arc's own §(K-chart) object.

**Status, stated before the mathematics.**

- **(BE-64), THE BRANCH-PRODUCT THEOREM — PROVED, both directions.** The
  pencil condition is *every closed star coplanar* ((BE-16)); at a
  degree-2 vertex it is vacuous, and at a hub `z` it is a **conjunction over
  the incident branches**, one conjunct per branch and each conjunct reading
  only that branch's own first interior vertex. So at a **fixed** flag
  assignment on the hub set `W` there is **no cross-branch term at all**, and
  `Config(H; flags) = (∏_b Ear(b; flags)) ∩ G` for `G` the harness gate's
  finite set of proper closed cross-branch conditions. Measured both ways:
  **495 branch restrictions legal, 0 not**, at joint draws from **three
  independent samplers** (the branch sampler, `bsharp.sample_piece_config_adj`
  and `widened.place_pencil_general`) over 8 pieces including a **nested
  two-level R-node**; and the **MIX test** — chains drawn in **independent
  runs** and glued — produces a gate-passing configuration at **8/8** theta
  shapes, every one of whose terminals has degree 3 into the child.
- **NOTHING PAST EARS IS EVER NEEDED.** (BE-62)(iii)'s *"known exactly for
  leaves and ears, open in general"* is **closed by the reduction, not by new
  geometry**: for any child, its achievable set at fixed terminal flags is the
  decorated-skeleton image of a product of ear sets, unioned over the flag
  assignments at its own interior hubs. The decorated-skeleton law holds on
  the topological skeleton as well as the SPQR tree — asserted as spaces at
  **69 draws, 0 mismatches** — and the topological skeleton is the **coarsest**
  decomposition whose children are all ears. **(BE-64)(iii)/(iv)**.
- **THE THETA CHILD, DONE.** `ρ̄ = ⟨C₁⟩ ∩ ⟨C₂⟩ ∩ ⟨C₃⟩` over independent legal
  chains; at `π_x ≠ π_y` the three spans are in **general position subject only
  to their dimensions**, `dim ρ̄ = max(0, Σ_j min(a_j,6) − 12)` at **30/30**
  measured triples (`a_j` to 10); and the welded-attainment obligation
  (BE-22)(iii)(a) is **FREE**: `ρ = δ` at **30/30**. **(BE-66)(i)/(ii)**.
- **THE SMALL-BRANCH CORRECTION IS REAL AND DOES NOT STAY IN ITS BRANCH.** At
  `π_x = π_y` a length-3 branch has span **exactly `Λ²π`** ((BE-30)(iii)(b)),
  so two of them have **equal** spans and the P-node intersection does not
  drop. The law becomes `max(ambient, confined)`, the confined term computed
  inside the 3-space `Λ²π` — **30/30** rows, **7** of them **exceeding**
  general position (by 1, 2 and 3), and **7 of 7** of those at a
  configuration that does **not attain**. So the extra members of the
  achievable set are exactly what **(BE-22)(iii)'s own hypothesis excludes**,
  and (BE-62)(iii)'s quantifier is corrected accordingly. **(BE-66)(iii)/(iv)**.
- **THE FLAG BASE IS THE ARC'S OWN CHART, AND (CH-1) ALREADY PAYS FOR IT.**
  The achievable-decoration space is `Chart(H)`, and (BE-64)'s parametrization
  **is** (CH-1)'s tower (`widened.place_pencil_general`) reorganized by branch.
  So under (CH-1)'s hypotheses — `hcard`, min degree 2, girth `≥ 4`,
  characteristic 0, all three checked at every battery piece — irreducibility,
  rationality over ℚ and **dense ℚ-points** are **already proved** and this
  direction cites them. The base is **free** (a product of irreducible
  rational bundles) exactly when **no two hubs are adjacent**; otherwise it is
  a pencil-realization problem for the hub subgraph — the phase's own problem
  one level down, on a much smaller graph. **(BE-65)**.
- **HALF (B): the drawn criterion is a PER-PIECE THEOREM, not a constructor
  artifact — and it now reaches THETA children.** At **28 measured peels**
  over 7 pieces (**14 of them with a theta child**, which BRNODE's 24/24 did
  not have) the (BE-22)(i) identity is **asserted** at every one; welded
  attainment `ρ_i = δ_i` holds at every side, and the general-position
  shortfall is **0 at 28/28**. Each such row is a theorem *for that piece*:
  every quantity is an exact-ℚ fact about an exhibited configuration and
  `rank ≤ target` is universal. What stays open is the **class** statement.
  **(BE-67)**.
- **Verdict: HIT shapes 1 and 2. Nothing landed is refuted**; one landed
  prose surface is **annotated at source** (F12): (BE-62)(iii)'s *"open in
  general"* and its *"achievable by pencil configurations"* quantifier.
  `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the 2-cut step,
  S-mark and (BE-32)(+) are untouched; **not a PENCIL event**; the
  phase-boundary consequence is **reported, not acted on**.
- **Reservation FULLY CONSUMED.** Labels **(BE-64)–(BE-68)** and *Steps
  BE63–BE67*; nothing returned.

### Standing notation

Inherited from *Steps BE9–BE62* verbatim (`f := def₃`, `g_{uv}`,
`δ_{uv} := f − g_{uv}`, `ρ̄_{uv}`, `ρ_{uv}`, hub, `Π_v := p_v ∧ π_v`, `M(F)`,
attainment, `Z`, `E = Π_u + Π_v`, `Λ²π`, the decorated skeleton `(B₀; {ρ̄_e})`
of (BE-59)(ii), the flag `(p_z, π_z)`). Added here:

- the **hub set** `W := {u, v} ∪ {z : deg_H(z) ≥ 3}` — the marked pair is in
  `W` whatever its degree, so that the branches ending at it are named. Note
  this is **coarser** than §(K-chart)'s hub set (degree `≥ 3` only); the two
  differ exactly when `u` or `v` has degree 2, which is the normal case at a
  marked pair, and **(CH-1)'s `hcard` is read on §(K-chart)'s set**;
- a **topological branch** `b`: a maximal path of `H` whose *interior*
  vertices all have degree 2, with both ends in `W`. Its **length** is its
  edge count `a_b`; a length-1 branch is a **real edge between two hubs**;
- the **topological skeleton** `T(H)`: the multigraph on `W` with one edge per
  branch. It is the **coarsest** decomposition of `H` into children glued
  along a shared vertex set with disjoint interiors whose children are **all
  ears**, and it is what (BE-59)(ii) is applied to below;
- `Ear(a; ϕ_z, ϕ_{z'})`: the achievable chain set of a length-`a` ear at the
  two fixed flags — **(BE-30)(ii)** for `a ≥ 4` and **(BE-30)(iii)** at
  `a ≤ 3` and in the `π_z = π_{z'}` regime;
- the **genericity proviso** `G`: the cross-branch part of the harness gate —
  points pairwise distinct across branches, and no two hinge lines coincident
  at a hub. Each is a proper closed condition on the product; **`G` is what
  the product theorem is stated modulo**, and every statement of the theorem in
  this file and on the status surfaces carries it (repaired 2026-09-01 at
  verification: six summary sites had dropped it — `notes/dispatch-log.md`).

**Carrier check, done off the landed bodies rather than the prose.** No new
Lean object is read; the pencil condition used throughout is *every closed
star coplanar*, read off `kbare_common.verify_pencil_witness` (a nonzero
common normal for `{p_z} ∪ {p_w : w ∈ N(z)}` at every `z`) and the
hinge-coincidence half off `binduc.assert_generic_star`, exactly as in *Steps
BE29–BE62*. **No `.lean` was opened; the standing 2026-08-05 Lean hold binds.**

### Step BE63 — (BE-64): the branch-product theorem, and why nothing past ears is needed

> **(BE-64)(i)** *(proven; the **per-vertex conjunction lemma** — two lines,
> and it is the whole content)* A configuration of `H` is a pencil
> configuration iff every closed star is coplanar ((BE-16)). Decompose that
> condition by vertex:
>
> - a vertex **interior to a branch** has degree 2, and three points are
>   always coplanar, so it imposes **nothing** — the *"free vertex in
>   btwocut's sense"* of (BE-30)(ii)'s proof;
> - a **hub** `z` imposes `N_H(z) ⊆ π_z`, and `N_H(z)` is the disjoint union,
>   over the branches incident to `z`, of that branch's own **first interior
>   vertex** (or, for a length-1 branch, the other hub). So the condition at
>   `z` is a **conjunction with one conjunct per incident branch**, and each
>   conjunct constrains **only that branch's own moduli**.
>
> Hence at a **fixed** flag assignment on `W` the legality of a configuration
> has **no cross-branch term**. ∎
>
> **This is the theorem the arc's samplers have been assuming since
> BEARCASE** — `bearcase.sample_piece_config`'s own docstring states it
> almost verbatim (*"choose a point AND a plane at each vertex of degree
> `≥ 3` (and at `u` and `v`), then place each remaining vertex freely — a
> degree-2 vertex imposes no condition of its own"*), and
> `bsharp.sample_piece_config_adj` and `widened.place_pencil_general` do the
> same. Their **caps** are (BE-65)(i) read backwards: bearcase's is exactly
> *"the branch set is an INDEPENDENT set"* — the **free-base class** — and
> the two successors relax it to `hcard`. It was never written down as a
> theorem;
> (BE-62)(iii) states its consequence (children coupled only through the flag)
> for SPQR children and leaves the per-child sets open. Nothing landed is
> wrong; what changes is that the coupling statement is now a **product**.

> **(BE-64)(ii)** *(proven; the **branch-product theorem**)* Fix a legal flag
> assignment `ϕ = {(p_z, π_z)}_{z ∈ W}` (legal: `p_z ∈ π_z`, and
> `p_{z'} ∈ π_z ∧ p_z ∈ π_{z'}` for every length-1 branch `zz'`). Then
> restriction to the branches is a **bijection**
>
> **`Config(H; ϕ) ≅ (∏_b Ear(a_b; ϕ_z, ϕ_{z'})) ∩ G`.**
>
> *Proof.* Forward: a branch's interior vertices have degree 2 **in `H`**
> (the interiors are disjoint from everything else), its first interior point
> lies in `π_z` and its last in `π_{z'}`, so the restriction is a legal ear
> configuration at those flags; the gate conditions restrict too. Converse:
> given a legal chain per branch, glue. Every interior vertex's star is
> coplanar (degree 2); every hub's star is `{p_z}` together with one point
> per incident branch, each already in `π_z` by that branch's own legality, so
> the union lies in `π_z`. The two directions are inverse. ∎
>
> Measured, **both directions, and the converse from three independent
> samplers**: `bdecor.py prod` restricts every branch of every joint draw and
> tests (BE-30)(ii)-legality at the configuration's **own closed-star flags**
> — **495 / 495 legal, 0 failures**, over 8 pieces × 3 samplers × 3 draws.
> The **MIX test** is the converse in its sharpest form: draw the chains in
> **independent runs** at one fixed flag assignment, take branch `j`'s chain
> from run `j`, glue — **8/8** theta shapes produce a configuration passing
> `assert_generic_star` **and** `verify_pencil_witness`, with
> `ρ̄` equal to the intersection of the three spans.

> **(BE-64)(iii)** *(proven; the **branch-decorated form** — (BE-59)(ii) at
> the topological skeleton)* (BE-59)(ii) is stated for children glued along a
> shared vertex set with disjoint interiors; the branches are such a family.
> Hence, at **every** configuration and with no genericity,
>
> **`ρ̄_{u,v}(H) = ρ̄_{u,v}(T(H); {⟨C_b⟩})`**,
>
> where `⟨C_b⟩ = ⟨ℓ^b_1, …, ℓ^b_{a_b}⟩` is the branch's chain span
> ((BE-30)(i)). Asserted as an identity of **spaces** at **69 draws** across
> the 8 battery pieces and all three samplers, **0 mismatches**.

> **(BE-64)(iv)** *(proven; the corollary that CLOSES (BE-62)(iii)'s open
> half — **F12**, annotated at source)* For **any** piece `H` — theta child,
> nested R-node child, anything — its achievable decoration set at fixed
> terminal flags is
>
> **`{ ρ̄_{u,v}(T(H); {⟨C_b⟩}) : ϕ a legal flag assignment extending the
> terminal flags, `(C_b)_b ∈ (∏_b Ear(a_b; ϕ)) ∩ G` }`.**
>
> Every geometric input is (BE-30)(ii)/(iii) at an **ear**; the only other
> ingredient is the **union over flag assignments at the interior hubs**,
> which is (BE-65)'s object. So (BE-62)(iii)'s *"known exactly for leaves and
> ears, open in general"* is closed **by the reduction, not by new geometry**,
> and the coordinator's job-2 hypothesis holds at **every** layer, not only
> the P-node one. Exercised at a **nested two-level R-node piece** (an
> `K₄`-skeleton child inside a `K₄`-skeleton piece) in `prod`, which
> `bsharp.sample_piece_config_adj` refuses outright and the branch sampler
> draws.

### Step BE64 — (BE-65): the flag base, which is the arc's own §(K-chart) object

> **(BE-65)(i)** *(proven; the base, identified)* The legal flag assignments
> on `W` are exactly the pencil configurations of the **hub subgraph**
> `B_real` — the graph whose edges are the **length-1** branches — with a
> plane chosen through each hub point carrying its `B_real`-neighbours. In
> particular the base is a **product of irreducible rational bundles**, one
> `{(p, π) : p ∈ π}` per hub, **iff `E(B_real) = ∅`**, i.e. **no two hubs of
> `H` are adjacent**, i.e. every topological branch has length `≥ 2`. Off
> that class the base is a pencil-realization problem for `B_real` — the
> phase's own problem one level down, on a graph with `|W|` vertices.
>
> *Proof.* The only conditions on `ϕ` are `p_z ∈ π_z` and, per length-1
> branch `zz'`, `p_{z'} ∈ π_z` and `p_z ∈ π_{z'}` — which is precisely the
> closed-star coplanarity of `B_real` restricted to `B_real`-neighbours. ∎
>
> **CORRECTED at the BBASE landing (2026-09-02, F12).** The last sentence —
> *"off that class the base is a pencil-realization problem for `B_real` — the
> phase's own problem one level down"* — **overstates it**, and the overstatement
> is the whole of (BE-68)(ii) item 1. The base is the **flag** variety of
> `B_real`, with a flag at *every* vertex, so it is §(K-chart)'s tower's
> **stages 1–2 only**; the stages carrying min degree `2` and girth `≥ 4` do not
> exist here, and **(CH-1) does not apply to `B_real`** ((BE-89)(iii)/(iv)). It
> is **free** on every `B_real` component of cyclomatic number `≤ 1`
> ((BE-90)(ii), (BE-91)(iii)) and nonempty always. See *Steps BE88–BE92*.

> **(BE-65)(ii)** *(a re-use, not a new proof — the load-bearing observation
> of this step)* (BE-64)(ii)'s parametrization — hub flags, then per-branch
> chains — **is** §(K-chart) *Step CH3*'s tower, stage for stage: hub points
> free, hub normals in `ker A_h(q)`, non-hub points in the intersection of
> their hub neighbours' planes. That tower is the source of
> `widened.place_pencil_general`, and **(CH-1)(a)/(e) is proved against it**:
> for `Γ` with **`hcard`**, **min degree 2**, **girth `≥ 4`** over a
> characteristic-0 field, `Chart(Γ)` is **nonempty, irreducible, rational
> over ℚ**, with **dense ℚ-points**. So the achievable-decoration space of a
> piece satisfying those three hypotheses inherits all of it, **already
> proved**, and this direction cites §(K-chart) rather than re-deriving it.
> Checked at every battery piece by `bdecor.py chart` (`hcard` **True**, min
> degree **2**, girth **4–8** at 7/7), together with **cross-sampler
> agreement on the generic `ρ̄`** between the branch sampler and
> `place_pencil_general` at **7/7** pieces.
>
> **What `hcard` is, seen from here.** It is the condition that every hub have
> at most two hub neighbours — exactly the cap
> `bsharp.sample_piece_config_adj` and `place_pencil_general` both carry and
> both disclose. (BE-65)(i) says why: it is the condition under which the
> **base** is still a tower of positive-dimensional fibres. So the arc's
> standing sampler cap is not an artifact; it is (CH-1)'s hypothesis.

> **(BE-65)(iii)** *(what the irreducibility buys, stated exactly, and what it
> does not)* On an irreducible parameter space a function that is
> semicontinuous in the right direction attains its extreme value on a **dense
> open** subset, so **one exact-ℚ draw settles the generic value** — the
> (BE-32)/(BE-46)/(BE-52) mechanism, now available for the **whole piece**
> rather than only the ear's own moduli. The branch-span profile
> `(dim⟨C_b⟩)_b` is a tuple of matrix ranks and is **lower** semicontinuous;
> `dim ⋂_b ⟨C_b⟩` is **upper** semicontinuous on the locus where that profile
> is constant, so its **minimum** is the generic value — which is why
> (BE-66)'s tables quote the **minimum over draws** (driver cap (2)).
> **It does not** make a *failure* at one configuration mean anything: that
> stays "not attained by this constructor" (F27).

### Step BE65 — (BE-66): the theta child, and the small-branch correction that does not stay in its branch

> **(BE-66)(i)** *(proven; job 1's theta case, as a corollary — the
> coordinator's job-2 hypothesis CONFIRMED)* A theta child `C` between
> terminals `x, y` with paths of `a₁, a₂, a₃` edges is its own topological
> skeleton: `W(C) = {x, y}`, three branches, **no interior hub**. So
> (BE-64)(ii) applies with the terminal flags already fixed by the fibration,
> and with (BE-60)(i)'s `P`-node law,
>
> **`Achieve(C; ϕ_x, ϕ_y) = { ⟨C₁⟩ ∩ ⟨C₂⟩ ∩ ⟨C₃⟩ : (C₁,C₂,C₃) ∈
> ∏_j Ear(a_j; ϕ_x, ϕ_y), generic }`** —
>
> the three chains **independent**, exactly as the coordinator's hypothesis
> predicted, and *computed* from (BE-30)(ii)/(iii) rather than newly
> characterized. **Weak link (b) — the degree-3 terminal — is CLEARED, and
> the reason is (BE-64)(i):** the pencil condition at `x` is a *conjunction*
> over the incident branches, so three first-lines in the pencil `Π_x` is
> three copies of the ear condition, not a new one; the only thing degree 3
> adds is more pairs for the hinge-coincidence gate, which is part of `G`.
> Measured by the MIX test at **8/8** theta shapes (*Step BE63*).

> **(BE-66)(ii)** *(measured, 30/30; the generic law and the free obligation)*
> At `π_x ≠ π_y` the three chain spans behave as subspaces **in general
> position subject only to their dimensions** `dim⟨C_j⟩ = min(a_j, 6)`:
>
> **`dim ρ̄_{x,y}(θ(a₁,a₂,a₃)) = max(0, Σ_j min(a_j, 6) − 12)`**,
>
> at **30 / 30** measured triples with `a_j` up to **10** (`bdecor.py theta`;
> the `P`-node law asserted as **spaces** at every draw). Moreover the
> **welded-attainment obligation (BE-22)(iii)(a) is FREE at a theta child**:
> `ρ = δ` at **30 / 30**, with `f = max(0, Σ_j a_j − 12)` and `g = f − δ`
> absorbing the excess when some `a_j > 6`. The tables print `f`, `g`, `δ`,
> `dim M` and attainment per row; every row attains.

> **(BE-66)(iii)** *(measured, 30/30; **the spec's weak link (a), CONFIRMED
> and sharper than predicted**)* (BE-30)(iii) is a correction *inside* an ear,
> and the natural reading is that it travels per branch and nothing more. It
> does **more than that.** At `π_x = π_y = π`:
>
> - a length-2 branch has `⟨C⟩ ⊆ Λ²π` of dimension **2**, and a **length-3**
>   branch has `⟨C⟩ = Λ²π` **exactly** ((BE-30)(iii)(b)) — so **two length-3
>   branches have EQUAL spans**, and the `P`-node intersection does not drop
>   at all;
> - a longer branch still meets `Λ²π` in at least `⟨ℓ_1, ℓ_{a}⟩` (both ends
>   lie in `Π_x, Π_y ⊆ Λ²π`), the **(Z) confinement** of (BE-33)(ii) read at a
>   P-node.
>
> Writing `c(a) := dim(⟨C_a⟩ ∩ Λ²π)`, the measured law is
>
> **`dim ρ̄ = max( ambient, confined )`, `ambient = max(0, Σ_j dim⟨C_j⟩ − 12)`,
> `confined = max(0, Σ_j c(a_j) − 6)`,**
>
> at **30 / 30** rows over both flag regimes. **Seven** rows **exceed**
> general position — `θ(3,3,3)`, `θ(3,3,6)` by **3**; `θ(2,3,3)`, `θ(3,3,4)`,
> `θ(3,3,5)` by **2**; `θ(2,2,3)`, `θ(3,4,4)` by **1** — the theta being
> *flexible* where the ambient count says rigid.

> **(BE-66)(iv)** *(the consequence for the consumer, and the correction to
> (BE-62)(iii)'s own quantifier — **F12**)* Every one of those seven rows is
> at a configuration that **does not attain** (`dim M > 6 + f`), measured
> **7 of 7**. That is the point, not a footnote: **(BE-62)(iii) asks for the
> tuples achievable by pencil configurations, and (BE-22)(iii)'s hypothesis is
> that both pieces ATTAIN.** The achievable set is strictly larger than the
> attaining-achievable set, and its extra members are exactly the
> flag-coincidence ones. **The consumer's question is the attaining one**, and
> the statement is corrected at source.
>
> **And the coincidence cannot be FORCED where the consumer needs it.** The
> only landed mechanism forcing `π_x = π_y` is BZAVOID's triangle propagation
> ((BE-15)), which needs `x ∼ y`. At an internal R-node peel the child's
> terminals are the ends of a **virtual** edge of a simple 3-connected
> skeleton `B`, so `xy ∉ E(H)` and there is no triangle on `{x, y}` to
> propagate. So **no landed mechanism forces the confinement at an R-node
> child's terminals** — stated as *no landed mechanism*, not as *never*.
>
> > **CORRECTION, 2026-09-01 (direction BPEEL, *Step BE72* / (BE-73)(i)) — read
> > this before quoting the paragraph above.** The clause *"the only landed
> > mechanism ... needs `x ∼ y`"* is **FALSE as stated**. It misses
> > **(BE-15)(ii)'s own inline scope correction**, which records the
> > **general** propagation rule — *`π_v` is forced to `π` as soon as
> > `closedNbhd(v)` holds three independent points already in `π`* — as landed,
> > **triangle-free and adjacency-free** (`K_{3,3}` is forced flat and has no
> > triangle), implemented as `binduc.flat_forcing_closure` and quantified over
> > by (BE-23)(ii) and (BE-32)(+). **`K_{2,3}` forces `π_u = π_v` at a
> > NON-adjacent pair** (asserted, `bpeel.py force`), so the mechanism reaches
> > a virtual edge's terminals.
> >
> > **The CONCLUSION stands, by a different and stronger argument**
> > ((BE-73)(ii)): where the forcing certificate lives inside **one side** of
> > the peel, **(BE-32)(+)** gives `δ_i = 0` and **(BE-22)(vi)** then removes
> > the general-position half **outright** — so the enemy is self-defeating
> > wherever it is one-sidedly forced, whatever the mechanism. Enumerated:
> > **3 497** forced R-node-shaped peels, **every one** with
> > `min(δ₁, δ₂) = 0`; **24 874** both-flexible R-node peels, **none** forced;
> > and off the R-node shape, forced-with-both-flexible is **common (408)**, so
> > the R-node hypothesis is **load-bearing**. The residue is **cross-cut-only**
> > forcing, and its proof obligation is the **SPREAD step** ((BE-41)(ii)).
> >
> > **SECOND CORRECTION, 2026-09-01 (direction BONEONE, *Step BE80* /
> > (BE-81)) — the CONCLUSION FALLS TOO.** The re-derivation above covers the
> > **one-sided** case only; the cross-cut-only case was *"none found under
> > cap"*. It is now **found**. An R-node-shaped peel **can** sit at
> > `δ₁ = δ₂ = 1` ((BE-79)), and of the **48** such peels on 11 vertices —
> > exhaustive over that class — **24** force `π_u = π_v`, on exactly
> > (BE-77)(ii)'s `{v, b₁, b₂}` certificate split `(2,2)` by the cut; 392 of
> > 928 across three exhaustive rows. **So *"the coincidence cannot be forced
> > where the consumer needs it"* is FALSE for the aggressive operator.** What
> > survives is the one-sided half, which is a theorem and is untouched. **And
> > *load-bearing* needs correcting with it:** both halves of that comparison
> > were measured at `n ≤ 8`, where by (BE-80)(ii) the R-node half **cannot**
> > occur — the hypothesis raises the size floor from 4 vertices to 11, it does
> > not discharge anything. The enemy is a **candidate**, not a proven
> > counterexample, because the operator over-claims ((BE-82)(ii)).

### Step BE66 — (BE-67): half (B), and job 3's question answered

> **(BE-67)(i)** *(measured, 28/28; the criterion at peels with THETA
> children)* At **28 peels** over 7 constructed R-node pieces — **14 of them
> peeling a theta child**, which BRNODE's 24/24 did not contain — every
> configuration through both gates: the (BE-22)(i) fibre-product identity
> **asserted** at every peel; both sides **attained**; welded attainment
> `ρ_i = δ_i` at **every side**; and the general-position shortfall
> `min(δ₁+δ₂,6) − dim(ρ̄₁+ρ̄₂)` **= 0 at 28/28**. The pieces reach
> `θ(6,6,6)` children and `|V| = 28`.

> **(BE-67)(ii)** `[PROVED]` *(job 3's question, answered: **theorem, per piece**;
> **artifact only as to the class**)* BRNODE asked whether the criterion
> holding outright at 24/24 was *"a theorem or a constructor artifact"*. It is
> a **theorem for each piece measured**, and the reason needs no
> irreducibility: every quantity in a row is an **exact-ℚ fact about an
> exhibited configuration**, `rank ≤ target` is universal, and (BE-22)(iii) is
> a **biconditional at a given configuration**, so a row reaching the
> criterion *proves* that the piece composes at that configuration — the
> (BE-37)(i)(3) mechanism. What is **not** settled is the **class** statement
> — *every* internal R-node piece — and that is where the residue sits.

> **(BE-67)(iii)** *(what the class statement now needs, stated so it can be
> attacked)* By (BE-64) the quantifier is now over an **explicit** parameter
> space: a flag assignment on `W`, then an independent (BE-30)(ii)/(iii)-legal
> chain per branch. By (BE-65)(ii) that space is irreducible and rational with
> dense ℚ-points under (CH-1)'s three hypotheses. So the class statement is
> *"for every internal R-node piece, some point of `Chart(H)` makes both peel
> sides attain and puts `ρ̄₁, ρ̄₂` in general position"* — a **single**
> statement about one irreducible variety per piece, with **two** identified
> ways to fail: the welded half (BE-22)(iii)(a), **free at theta children**
> by (BE-66)(ii), and the general-position half, whose only located enemy is
> the flag coincidence of (BE-66)(iii), **unforceable at an R-node peel** by
> (BE-66)(iv). That is the shape BWIN's opaque-subspace theorem had, one level
> up.
>
> **CORRECTED at the BUNIF prep (2026-09-02, F12) — the last clause cites a
> REFUTED lemma.** *"Unforceable at an R-node peel by (BE-66)(iv)"* no longer
> holds: **(BE-66)(iv) is refuted outright** ((BE-81), direction BONEONE) —
> `π_u = π_v` **is** forced at an internal R-node peel with both sides flexible,
> at **392 of 928**. The **conclusion still stands, by a different route**: the
> certificate is a **hinge pair**, so the forcing is genuine *pointwise*, and the
> shortfall is **0 at 392/392** ((BE-84)–(BE-86), direction BGENUINE). So the
> coincidence is a **checked hypothesis**, not an unforceable one, and the
> general-position half's enemy is *located and measured-harmless* rather than
> *excluded*. Three landings made the correction at (BE-66)(iv) itself and not
> here, at the statement that cites it. The rest of (BE-67)(iii) is unaffected —
> and its `Chart(H)` irreducibility citation is **not** touched by (BE-89)'s
> correction to (BE-65), which is about `𝒜(B_real)`, a different object.
>
> **REDUCED at the BUNIF landing (2026-09-02) — F12.** The *"two identified
> ways to fail"* framing above is superseded: by (BE-96)(iv) the welded half is
> **not a separate half**, it is the `U = Λ²K⁴` term of one inequality family
> indexed by the **16 `S(ϕ)`-stable subspaces** of the screw space, and
> (BE-67)(iii) at a generic-regime peel is exactly *14 numerical inequalities
> `c₁(U) + c₂(U) ≤ dim U + max(0, δ₁+δ₂−6)` with each side's
> `c_i(U) = dim(ρ̄_i ∩ U)` computed on its own*. Measured, the only block at
> which both sides bite is `Π_x`, and the residue is **(NO-DOUBLE-PENCIL)**
> ((BE-97)(iii)). See *Steps BE93–BE97*.

### Step BE67 — (BE-68): the routing verdict, and the residue in its honest minimal form

> **(BE-68)(i)** *(the verdict on the spec's own prediction — F26, tested as
> required)* The spec's job 2 predicted *"if that holds, job 1's theta case is
> a corollary and the direction's real content is half (B)"*. **CONFIRMED, and
> the corollary is wider than predicted**: not only the theta case but every
> child, because the fibration bottoms out at ears at the topological skeleton
> rather than at the SPQR tree. **One clause is reframed**: the spec located
> the freedom *"at the P-node layer"*; the right statement has nothing to do
> with node type — freedom at fixed flags is a property of the **pencil
> condition being a per-vertex conjunction**, and the SPQR tree was simply the
> wrong decomposition to ask it on.
>
> The spec's two named weak links came out **opposite ways**, which is the
> direction's most useful single sentence: **(b)**, the degree-3 terminal —
> the one the spec said to *"check first"* — is **harmless, and provably so**;
> **(a)**, the small-`m` correction, is **real, and stronger than the spec's
> reading**, because it does not stay inside its branch.

> **(BE-68)(ii)** *(the residue, in its honest minimal form — the successor
> this direction names)* After (BE-64)–(BE-67), (BE-62)(iii) leaves exactly
> **two** things, and neither is about children:
>
> 1. **The flag base off the no-adjacent-hubs class** ((BE-65)(i)): when the
>    skeleton has real hub-hub edges the base is a pencil-realization problem
>    for `B_real`. It is a *small* instance of the phase's own problem — but
>    it is the phase's own problem, and saying otherwise would be the
>    overclaim the spec's bars single out.
>
>    **DISCHARGED at the BBASE landing (2026-09-02, F12) — this item is no
>    longer residue.** It is **not** the phase's own problem: it is the *flag*
>    variety of `B_real`, §(K-chart)'s stages 1–2 with no stage 3 or 4, free on
>    every component of cyclomatic number `≤ 1` and nonempty always
>    ((BE-89)–(BE-91)). The only failure mode is **reducibility** at a
>    `B_real`-triangle or 4-cycle, both excluded on the class by girth `≥ 6` and
>    both off the locus the proviso `G` already imposes ((BE-92)). **Half (B)'s
>    residue is therefore item 2 alone.** See *Steps BE88–BE92*.
> 2. **The class quantifier of half (B)** ((BE-67)(iii)): one statement per
>    piece about one irreducible variety, with the two failure modes named and
>    both currently unwitnessed.
>
>    **REDUCED at the BUNIF landing (2026-09-02, F12) — still the residue, but
>    a different statement.** The item is now the **per-side** condition
>    **(NO-DOUBLE-PENCIL)** ((BE-97)(iii)): *no internal R-node peel has one
>    side with `dim(ρ̄_i ∩ Π_x) = 2` and the other with `dim(ρ̄_j ∩ Π_x) ≥ 1`*
>    (and the same at `Π_y`), whose two clauses are priced by (BE-44)(ii) and
>    (BE-45) respectively. The *"two failure modes"* are one inequality family
>    ((BE-96)(iv)). See *Steps BE93–BE97*.
>
> **What is NOT left:** per-child achievable sets past ears; a
> (BE-30)(ii)-analogue for thetas; and any coupling between children at fixed
> flags. Those were the direction's stated targets and they are closed.

### Verdict, classification, and the price

- **HIT shape 1**: the per-child achievable set is characterized **past
  ears** — by showing the question never arises past ears ((BE-64)(iv)), with
  the theta case written out explicitly ((BE-66)).
- **HIT shape 2**: the P-node layer is **free**, in the stronger form *every
  layer is free at fixed flags* ((BE-64)), relocating the content to half (B)
  exactly as job 2 predicted.
- **NOT HIT shape 3**: half (B) is settled **per piece**, at 28 peels, not for
  a named class — the honest reading of (BE-67)(ii).
- **NOT HIT shape 4**: no obstruction. The one mechanism that moves `ρ̄` off
  general position ((BE-66)(iii)) is **located** and shown to sit at
  non-attaining configurations and to be unforceable at an R-node peel by any
  landed mechanism — a **candidate examined and set aside**, never a
  refutation.
- **The price, stated as a price.** The product theorem is stated **modulo
  the genericity proviso `G`**, whose emptiness is never checked in general
  (it is nonempty at every drawn instance, and a *forced-empty* `G` would be a
  cross-branch obstruction the theorem does not see); the dimension laws of
  (BE-66)(ii)/(iii) are **measured**, not proved, on batteries capped at
  `a_j ≤ 10` and one constructor; (BE-65)(ii) is a **citation** of a
  proven-informally result of §(K-chart), with its three hypotheses, not a
  new proof; and half (B)'s class quantifier is untouched.
- **Untouched.** `PencilPair K 3 G`, `hbareSplit`, (BE-14)-for-all-`G`, the
  2-cut composition lemma, S-mark, (BE-32)(+), the short-cycle law, BWIN's
  window theorem, (GR-15), class uniformity. **Not a PENCIL event.**

### Verification

Every claim above is reproduced by
`python3 notes/scripts/w4/bdecor.py {prod|theta|small|chart|attain|validate}`,
run from the repo root; `validate` runs all five modes at a reduced tier in
**≈ 182 s** (inside the 600 s foreground budget, one invocation); the full tiers
are `prod` **≈ 33 s**, `theta` **≈ 22 s**, `small` **≈ 20 s**, `chart`
**≈ 166 s**, `attain` **≈ 15 s** — wall clock, which varies run to run; the
counts below are the invariants. The load-bearing asserts (a failure stops the run):

1. **Every configuration is a pencil configuration** — `assert_generic_star`
   **and** `verify_pencil_witness` on every draw from **all three** samplers,
   including every glued MIX configuration. This is the composite guard
   `notes/scripts/README.md` §3 requires before a
   `place_pencil_general`-sampled battery may be quoted as a rate.
2. **Every space claim is an identity of SPACES** (`same_space`, never
   dimensions): the branch-decorated law against the direct `ρ̄` per draw, the
   `P`-node law at every theta draw, the MIX configurations' `ρ̄`.
3. **(BE-22)(i) is asserted, not reported**, at every one of the 28 peels.
4. **The deficiency oracle is cross-checked**: the welded multigraph's `g` is
   computed by `nogood_subdiv.deficiency` (the (6,6)-count-matroid oracle,
   the only one that runs on a multigraph at `|V| > 8`) and agrees with
   `binduc.def_by_partitions(together=…)` at **15/15** small instances.
5. **Exact ℚ throughout**, every rng seeded from the printed literal
   `20260901`, zero floating point.

### Caps, disclosed rather than smoothed

1. **The branch sampler's placement is a greedy order.** It places hub points
   in order of hub-degree inside the intersection of the planes its complete
   constraints force, and **verifies every constraint** before returning — so
   it draws a hub with three `W`-neighbours, which
   `bsharp.sample_piece_config_adj` refuses outright, and that is what lets
   the nested two-level R-node piece be drawn (`place_pencil_general` draws
   that piece too: its own hub set is degree-`≥ 3` only, so the piece is
   inside *its* cap). A dense hub subgraph (an all-leaf `K₄` skeleton, whose
   only pencil configurations are flat) still defeats the greedy order.
2. **(BE-66)'s tables quote the MINIMUM over the seeded draws**, since
   `dim ⋂` is upper semicontinuous; a larger value at a special configuration
   is not a counterexample to a generic law, and `small` exhibits exactly such
   configurations on purpose.
3. **`attain`'s battery is one constructor** — `K₄`-skeleton pieces with theta
   and ear children. A shortfall elsewhere would be *"not attained by this
   constructor"*, never *"does not attain"* (F27). None was seen.
4. **`prod`'s FORWARD figure counts branch restrictions, not pieces**: 495 =
   8 pieces × 3 samplers × 3 draws × their branch counts, minus the one
   (piece, sampler) pair that produced no draw (`bsharp-adj` on the nested
   piece, which it refuses).
5. **The genericity proviso `G` is never shown nonempty in general.** Every
   drawn instance satisfies it; a *forced-empty* `G` would be a cross-branch
   obstruction (BE-64)(ii) does not rule out. Recorded as a named gap, not
   smoothed.

### Harness note — the `kbare/` sibling-import set gains its FOURTEENTH consumer

`bdecor.py` imports `brnode` (`build_piece`, `K4_named`, `PRISM_named`),
`bsharp` (`guarded_draw`, `sample_piece_config_adj`), `bimage` (the space
helpers, `sample_flags`, `legal_chain`, `chain_of`, `rho_bar_of`, `pt_in`,
`v4`), `binduc` (`assert_generic_star`, `def_by_partitions`, `theta`), `bwin`
(`dehom`), plus the §1-catalogued `widened.place_pencil_general` and
`nogood_subdiv.deficiency`, all **read-only**, and through them the rest of
the chain — so the recorded **unpaid** sibling-import debt
(`notes/scripts/README.md` *Harness debt*) gains its **fourteenth** `w4/`
consumer and the chain is now **twelve** deep: `battain → bzavoid → binduc →
btwocut → bimage → bearcase → bearfull → bsharp → brule → bwin → brnode →
bdecor`. **`bwin.dehom` gains its SECOND consumer, which trips the §2 rule-2
threshold**, and `brnode` gains its **first** external consumer. **NO MOVE
MADE**; the consumer lists are extended in the README, exactly as the previous
thirteen did. The new primitives (`hubs_and_branches`, `flag_assignment`,
`draw_branch`, `sample_by_branches`, `branch_decorated_rho`, `weld_d3`) are
local to this driver.

### Confidence verdicts, per claim

| claim | status |
|---|---|
| (BE-64)(i) the per-vertex conjunction lemma | **PROVED** (two lines, from (BE-16)); it is what the arc's samplers already assumed |
| (BE-64)(ii) the branch-product theorem, modulo `G` | **PROVED**, both directions; measured 495/495 forward and 8/8 by the MIX converse |
| (BE-64)(iii) the branch-decorated form of `ρ̄` | **PROVED** (from (BE-59)(ii)); asserted as spaces at 69 draws |
| (BE-64)(iv) nothing past ears is needed | **PROVED** (a corollary of (i)–(iii)); exercised at a nested two-level R-node piece |
| (BE-65)(i) the flag base is the hub subgraph's pencil problem; free iff no two hubs adjacent | **PROVED** (the conditions are exactly `B_real`'s closed-star coplanarity) |
| (BE-65)(ii) the base IS §(K-chart)'s tower; (CH-1) supplies irreducibility, rationality, dense ℚ-points | **CITED** — (CH-1) is *proven-informally* in §(K-chart), with three hypotheses, all three checked at 7/7 battery pieces here |
| (BE-65)(iii) one draw settles a generic value | **PROVED given (CH-1)**; one-directional (a failure settles nothing) |
| (BE-66)(i) the theta's achievable set; weak link (b) cleared | **PROVED** (a corollary of (BE-64)(ii) + the `P` law); MIX-measured 8/8 |
| (BE-66)(ii) the generic dimension law; `ρ = δ` free | **MEASURED 30/30** (cap 2), `a_j ≤ 10` |
| (BE-66)(iii) the `max(ambient, confined)` law; 7 rows off general position | **MEASURED 30/30**; the two confinement mechanisms are (BE-30)(iii)(b) and (BE-33)(ii)(Z), both proved |
| (BE-66)(iv) the extra members are non-attaining; the coincidence is unforceable at an R-node peel | **MEASURED 7/7** for the first half; the second half **PROVED for the landed mechanism only** ((BE-15) needs `x ∼ y`) |
| (BE-67)(i) the criterion at 28 peels, 14 with a theta child | **MEASURED**, constructor-capped (cap 3) |
| (BE-67)(ii) each such row is a per-piece theorem | **PROVED** (exact-ℚ facts about an exhibited configuration; `rank ≤ target` universal) |
| (BE-67)(iii) what the class statement needs | **LOCATED**, not proved |
| (BE-68) the routing verdict and the two-item residue | **STATED**, a routing judgement |

### What would change this

- **A cross-branch obstruction** — a piece and a flag assignment at which the
  genericity proviso `G` is **forced empty**, so that a tuple of individually
  legal chains never glues — would qualify (BE-64)(ii) and is the first thing
  to hunt. None was seen; the driver would find one as a piece with legal
  per-branch draws and no gate-passing assembly.
- **A theta triple violating `max(ambient, confined)`** at `π_x ≠ π_y` would
  refute (BE-66)(ii)'s general-position reading and would mean the chain spans
  carry a structure the (P)/(Z)/(R) classification of (BE-33)(ii) does not
  list.
- **A second, graph-level mechanism forcing `π_x = π_y`** at the ends of a
  virtual edge would reopen (BE-66)(iv) and put the confinement back on the
  consumer's path — this is the sharpest single question this landing leaves,
  and it is combinatorial.
- **A peel with a persistent criterion shortfall** (surviving resampling and
  constructor escalation per (GR-83)/(GR-113)) would be the R-node case's
  first (α)/(β)-shaped obstruction. None was seen at 28 peels here or at
  BRNODE's 24.
- **The class quantifier of half (B)** ((BE-67)(iii)) and **the flag base off
  the no-adjacent-hubs class** ((BE-65)(i)) are the named successors.

### TERMINATION riders

**E1: NO** — this direction is one decomposition lemma, one identification
with a landed chart result, and two measurement passes; no `g`-flank is
involved and none is produced. **E2: NO** — nothing landed is refuted; the two
annotated prose surfaces ((BE-62)(iii)'s *"open in general"* and its
*"achievable by pencil configurations"* quantifier) are **closed** and
**sharpened** respectively, and every landed measurement is intact. **E3:
ARMED by GBAL, not fired** — this direction is on the §(K-bare-ext) path, not
(a′); reported, not acted on.
