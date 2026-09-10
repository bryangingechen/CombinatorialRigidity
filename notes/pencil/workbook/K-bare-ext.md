## §(K-bare-ext) — the arbitrary-seed insertion lemma is **REFUTED as stated** (a legal target-rank seed where route A fails at *every* placement, exact and cap-free), the §(K-tight) boundary-load calculus **transports** to this kernel (192/192), and the dependent stratum is **complete** at `corank(G′) ≤ 3`

Probe **KBARE-FALSIFY** (`notes/pencil/fanout.md` §"Two probes SPECCED and
AUTHORIZED 2026-08-20"), the commissioned falsification hunt for `hbareSplit`.
Read against `notes/Phase39-design.md` §"(K-bare) extension-route recon" (the
statement, the corank stratification, the DZ/cube/Wagner danger gadgets, the
option-C results) and §(K-tight) *Steps 2–4* (the boundary-load calculus this
section transports). Driver `notes/scripts/kbare/breakhunt.py`
(`tiers|calc|arith|rzero|locus|c1b`); all exact ℚ.

**Status, stated before the mathematics.**

- **(K-bare-ext) as written is FALSE, and the witness is exact.** At the
  option-C **C2 cube-skeleton index-2 danger gadget** (24v/28e, `def = 0`,
  infeasible), at its KT-faithful **hub-end** split, there are legal
  target-rank bare pencil realizations of `G′` from which **no** placement of
  `v` attains `target(G)` — verified cap-free (every `2×2` minor of the
  criterion matrix vanishes **identically** on the placement panel) and
  corroborated by the observed exact rank `137 = target − 1` at every legal
  placement drawn. **(BE-1)**.
- **This is a route finding, tier T1 — `hbareSplit` is NOT refuted.** Its
  consequent `HasPencilRealization K 3 G` is an **existential** over
  frameworks (`Statement.lean:103`, re-read this pass), and the gadget
  **attains** its bare target (138/138 here). What is refuted is route A's
  *fixed-seed* strategy: the `∀`-over-seeds shape of the statement.
- **The mechanism is §(K-tight)'s own, at a stratum Step 4 said escapes
  generically.** All eight hit seeds have `rank⟨U, Λ²Π̂(b)⟩ = 1` — *Step
  2.4*'s uniform-failure criterion `r ⊥ Λ²Π̂(b)` — at **`dim R_a = 3`**, where
  the codimension count (`dim U = 4`, rank-≤1 locus of a `2 × 4` form matrix)
  predicts a *generically* empty intersection with the 2-dimensional panel.
  The seeds are legal and non-generic; the count is generic. **(BE-2)**.
- **The calculus transports, and its scope is now measured, not assumed.**
  The corank identity is **scope-free** (192/192 placements over four
  (gadget, split) cases spanning both strata); `U ∩ C(ab)^⊥ = R_a` and
  `R_a ⊆ U` hold everywhere; **`dim U = dim R_a + 1` and
  `dim R_a = index + 1 − s₀` are `def = 0`-only** (0/8 in the
  count-independent case). **(BE-3)**.
- **The dependent stratum is COMPLETE: `index(G) ∈ {1, 2}`, so
  `corank(G′) ≤ 3`** — a theorem by arithmetic, not a search. This
  **corrects** the design doc's "`index ≤ 4` caps it at 5": the two inhabited
  values are the only ones, and both are witnessed. **(BE-4)**.
- **Two recorded claims corrected, and one corroborated.** Option-C C3's "the
  failure set looks exactly like the line" fails **at DZ itself** — an
  off-line failure point *constructed* (not sampled) and verified at exact
  rank `113 = 114 − 1` **(BE-5)**; C1's "the rank antecedent polices the
  degeneracy" is corroborated at a second gadget for three strata and
  **refuted as a general reading** by the stratum that carries the hit
  **(BE-6)**.
- **No T2 candidate exists in the arc's gadget stock, and none could be
  produced by this harness.** T2 needs `HasPencilRealization K 3 G` to fail —
  a universal non-existence over all frameworks — which no sampler can
  certify; every gadget probed attains. **(BE-7)**.
- **Gap-map effect.** The `(K-bare)/(K-bare-ext)` row moves from *open,
  nothing being developed* to *the `∀`-seed form REFUTED; the live statement
  is the `∃`-seed form plus a seed-repair obligation*. `hbareSplit`'s own
  status is **unchanged** — still carried as pinned, on the standing route-(a)
  GO.

### Standing notation

`G` a habitat member of `hbareSplit` (`Escape.lean:351`: simple, `5 ≤ |V|`,
2EC, no proper rigid subgraph at `d = 3`, `deg v = 2` with links to `a`, `b`,
`hsafe` = at least one of `a`, `b` a non-hub, a fresh `e₀`, and
`¬ PencilNondegFeasible K G`); `G′ = G.splitOff v a b e₀`; `index(G) := 5|E| −
6(|V| − 1)`; `c_G := 5|E(G)| − target(G) = index(G) + def(G)`. `s₀`, `U`,
`R_a`, `Λ²Π̂(b)` are §(K-tight) *Step 2*'s, restated in *Step BE2* against
this carrier. Every rank is exact ℚ; GF(p) only as a certified lower bound.

### Step BE1 — the hit criterion, sharpened off the Lean bodies

`HasPencilRealization` (`Statement.lean:103`) and `PencilNondegFeasible`
(`Motive.lean:133`) are **both `∃`-statements** (bodies read this pass), and
`PencilPair` (`Motive.lean:160`) carries `HasPencilRealization K n G` as an
**unconditional** second conjunct. Three consequences fix what a hit can be:

> **(BE-1)** *(bookkeeping, load-bearing)* A candidate breaks into exactly
> three tiers. **T1** — route A's *fixed-seed* insertion fails: this refutes
> **(K-bare-ext)**, not `hbareSplit`, because a prover may also perturb the
> rest of the seed. **T2** — `HasPencilRealization K 3 G` **fails** at a
> habitat member: a universal non-existence over all frameworks and all
> placements. **T3** — the `∀`-form "off-line ⟹ attains", already refuted at
> the (K-tight) control (*Step 2.4*: the failure locus is `line(a,b) ∪ P′`).

**A correction to the tier semantics, recorded because it changes who a T2
decides.** A T2 witness would falsify `PencilPair K 3 G`'s second conjunct,
hence the **conclusion** of `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`
(`Escape.lean:555`) at a spanning `G` — so it is not a "phase-shape event" but
a **PENCIL event**: it would prove the conjunction
`hcontract ∧ hK ∧ hbareSplit` false and kill the program's target as
formalized, with the direction-A pivot rule in force. No T2 candidate was
found (*Step BE7*), so nothing turns on this operationally; it is recorded so
the next dispatch prices a T2 correctly.

### Step BE2 — the boundary-load calculus on this carrier, and what a uniform failure is

Derived from the row structure of the carrier (`kbare_common.build_rigidity`:
five rows per link, `perp_basis(C_e)` in the `u`-block and its negative in the
`v`-block), **not** imported as prose. Write `E(u)` for the column vector that
is `u` in `a`'s block, `−u` in `b`'s block and `0` elsewhere; the orientation
of the two `v`-links cancels, so `E` is sign-canonical.

> **(BE-2)** *(proven-informally; exact, no genericity, no `def` hypothesis)*
> With `U := {u ∈ K⁶ : E(u) ∈ rowspan(shared rows of G − v)} = {u : ⟨u, m(a) −
> m(b)⟩ = 0 for every motion `m` of `G − v`}`, `s₀ :=` corank of the shared
> rows, and `M(x) := [⟨u_i, C(va)⟩ ; ⟨u_i, C(vb)⟩]` the `2 × dim U` matrix at
> placement `pt(v) = x`:
>
> 1. **`corank R(G) = s₀ + dim U − rank M(x)`** at every placement. (A
>    `G`-stress's `v`-block forces antisymmetric fiber loads `±u`, its `a`/`b`
>    blocks say `E(u) ∈ rowspan(shared)`, and the shared part is then free up
>    to `s₀`.)
> 2. Hence **attainment ⟺ `rank M(x) = s₀ + dim U − c_G`**, and since
>    `rank M ≤ min(2, dim U)`, a **required rank above that bound is uniform
>    failure by arithmetic alone**.
> 3. `R_a := {Σ_j ν_j w_j}` over the `ab`-block `ν` of the `G′`-stresses
>    (`w_j` the five `perp_basis(C_ab)` generators) satisfies
>    **`corank(G′) = s₀ + dim R_a`** and `U ∩ C(ab)^⊥ = R_a`, `R_a ⊆ U`.
> 4. In the **count-dependent** stratum (`def(G) = def(G′) = 0`, so
>    `c_G = index`, `corank(G′) = index + 1` at a target-rank seed) items 2–3
>    collapse to §(K-tight)'s form: `dim U = dim R_a + 1`,
>    `dim R_a = index + 1 − s₀`, and **the required rank is exactly 2**.

**Machine validation** (`breakhunt.py calc`, 118 s): four (gadget, split)
cases — DZ non-hub-ends, DZ hub-end, the C2 cube index-2 gadget hub-end, and
`theta(6,6,6)+center` (**count-INDEPENDENT**, `def = 3`) — 8 target-rank seeds
each, **192/192** placements with predicted corank = observed exact corank.
`Ra_subset_U` and `meet_eq_Ra` hold **32/32 seeds**. Item 4's two identities
hold 24/24 in the dependent cases and **0/8** in the independent one, which is
the scope statement: they are `def = 0`-only, and quoting them off that stratum
is an error the old prose invited.

> **(BE-3)** *(measured)* In the count-independent **def-drop** branch
> (`corank(G′) = 0`) the observed `dim U = 0` at 8/8 seeds, so the required
> rank is **0**: attainment is automatic at *every* legal placement. The
> gate's seven-gadget extension result is therefore explained by an
> **identity**, not by its sampling — and the def-equal branch
> (`corank(G′) = 1`, `dim U = 1`) is where the recorded line-avoidance caveat
> lives, its failure locus being the intersection of the **two** hyperplanes
> `⟨u, · ∧ â⟩ = ⟨u, · ∧ b̂⟩ = 0`, i.e. a single line, equal to `line(a,b)`
> exactly when `u ⊥ C_ab`.

**Uniform failure is decidable per seed with no cap.** Every entry of `M(x)`
is affine-linear in the placement parameters (`C(vx) = x̂ ∧ ŵ`), so every
`2×2` minor is a quadratic form with finitely many coefficients: "fails at
every placement of the domain" is an **identical-vanishing** test on those
coefficients, not a sample. The placement domain is the affine chart when both
split ends are non-hubs, and the hub end's panel `Π̂(b)` when one is a hub
(forced: the seed fixes the hub's other neighbours, and `pt(a) ∈ Π̂(b)`
already, `a` being `b`-adjacent in `G′` through the fresh edge). This is
`breakhunt.uniform_failure_exact`; a grid test runs beside it and the two
verdicts are **asserted equal** at every seed of every battery.

### Step BE3 — the hunt, and the T1 hit

Six sampler strata (robust generic; global hub-coplanar; apex-star collinear;
every-hub-star collinear; **local flat**; global flat) × 10 seeds × five
(gadget, split) cases, all through a new **general** BFS pencil sampler
(`sample_pencil_bfs`: hub panels propagated over the hub-hub adjacency graph,
robust plane sampling throughout — no call to the degenerate `plane_basis`
family). `breakhunt.py rzero`, 322 s.

The **local flat** stratum is the one that pays, and it exists because of a
combinatorial fact worth naming on its own:

> **(BE-4)** *(proven-informally; the pencil propagation rule)* If three
> bodies of a hub's closed star lie in a plane `P` and span it, the hub's
> panel **is** `P`, so its whole closed star lies in `P`. Hence forced
> coplanarity spreads by the closure `S ↦ S ∪ closedStar(h)` over hubs `h`
> with `|closedStar(h) ∩ S| ≥ 3`. The pencil stratum therefore has **no
> local degenerations of the bar-joint kind** — but the closure is **proper**:
> at DZ's `G′` a shortest cycle (7 bodies) closes on **11 of 19**.

**The hit.** At the C2 cube-skeleton index-2 gadget's hub-end split, the local
flat stratum yields **8 of 10** seeds that are legal `G′` pencil witnesses **at
target rank 132**, each with `s₀ = 0`, `dim R_a = 3`, `dim U = 4`, required
rank 2, and **all six `2×2` minors of `M` identically zero on the panel** —
route A fails at **every** placement. Independent corroboration per seed:
observed exact rank `137` at every legal placement drawn, `target(G) = 138`.
Mechanism: `rank⟨U, Λ²Π̂(b)⟩ = 1` at **8/8** hit seeds.

> **(BE-5)** *(refutation)* **(K-bare-ext) is false as stated.** There is a
> habitat member `G`, a legal split, and a bare pencil realization of `G′`
> attaining `target(G′)` such that **no** placement of `v` — off
> `line(pt a, pt b)` or on it, inside the hub end's panel (and no placement
> outside it is even a panel realization) — attains `target(G)`.

**Why the seed is in scope, which is the whole point.** (K-bare-ext) may not
add a nondegeneracy antecedent: `hbareSplit`'s own hypothesis is
`¬ PencilNondegFeasible K G`, so **no** nondegenerate realization of `G` (or
of `G′`, infeasibility propagating) exists at all, and every seed the lemma
must handle is degenerate. The hit seeds are exactly that — legal, degenerate,
target-rank. The design doc named this as a *worry* (its item (iii): the
calculus's genericity step "is not automatic at an opaque IH seed"); it is now
a **refutation**.

**What the hunt did NOT find, under cap.** No seed with `dim R_a = 0` — the
§(K-tight) *Step 2.3* mechanism, which here needs `s₀ = index + 1 ∈ {2, 3}`:
every stress-raising stratum that reached `s₀ ≥ 1` fell **below**
`target(G′)` and is excluded by (K-bare-ext)'s own rank antecedent (`s₀ = 1`
at apex/star-collinear seeds, `s₀ ∈ {6, 9, 12}` at global flats). So the
hard stratum `dim R_a ≤ 1` of this kernel is **uninhabited under cap** (6
strata × 10 seeds × 5 cases), and the hit arrives by the *other* mechanism
instead. *Not found under cap* — never "does not exist".

### Step BE4 — the dependent stratum is complete: `index ∈ {1, 2}`

> **(BE-6)** *(proven-informally; arithmetic, no cap)* Let `G` satisfy
> `hbareSplit`'s antecedents with `E(G̃)` count-dependent (`index ≥ 1`) and
> some degree-2 body. Then **`index(G) ≤ 2`**, hence
> **`corank(G′) = index + 1 ≤ 3`** at a target-rank seed.
>
> *Proof.* (i) For a maximal degree-2 path of length `l ≥ 2`, deleting its
> interiors leaves a **proper** vertex subset `W` with
> `f(W) = 5|E(W)| − 6(|W| − 1) = index + l − 6`, so `hnoRigid` forces
> **`l ≤ 5 − index`**. (ii) `index = 4` would force every `l ≤ 1`, i.e. no
> degree-2 body, contradicting `hdeg2`. (iii) `index = 3` forces every
> `l ≤ 2`, so `L ≤ 2E_s`; the index identity gives `L = 6E_s − 6H + 3`, hence
> `4E_s ≤ 6H − 3`, while min-degree-3 of the suppressed skeleton gives
> `2E_s ≥ 3H`, i.e. `4E_s ≥ 6H`. Contradiction. (A bare cycle has no
> skeleton; `|V| ≥ 5` and `index ≥ 1` force `C₅`, `index 1`, which is not
> `¬Feasible`-certifiable.) ∎

**This corrects a recorded figure.** The design doc's option-C C2 bullet reads
"the corank stratification is genuinely inhabited at least up to
`corank(G′) = 3` (`index ≤ 4` caps it at 5)". The cap is **3**, and both
values `{2, 3}` are witnessed (DZ and the cube/Wagner hits) — so the
stratification of the dependent habitat is **complete**, not merely inhabited.

**Enumerated corroboration** (`breakhunt.py arith`, 1 s). Over **every**
connected loopless cubic multigraph skeleton on `≤ 6` hubs
(`gridcol.cubic_iso_classes`), with the apex's three arcs pinned to length 1
(the only known `¬PencilNondegFeasible` certificate: `closedHubNbhd(apex)`
has 4 members) and the skeleton-level habitat check: **216** members at
index 1, **0** at index 2, **0** at indices 3 and 4; longest arc **4**,
exactly clause (i)'s bound. The two smallest are certified exactly
(`|V| = 20`, `|E| = 23`, `def = 0`, `max f(W)` proper `= −1`, 2EC,
`max closedHubNbhd = 4`) — so **DZ is one of a 216-member family**, and the
spec's "larger skeletons are unprobed" is now a census rather than a gap. At
8 and 10 hubs (cube, Wagner, Petersen) the arithmetic candidate count is
`{1: 146808, 2: 360, 3: 0, 4: 0}` resp. `{1: 15015660, 2: 34320, 3: 0, 4: 0}`
— indices 3/4 **empty before any habitat check**. **Cap:** the exhaustive
*class* sweep stops at 6 hubs (`cubic_iso_classes(8)` alone costs ~110 s and
the index-1 census on a 12-edge skeleton is combinatorially large); 8 and 10
hubs are covered by the named skeletons and by (BE-6) itself, which is a
proof.

### Step BE5 — the failure locus, constructed rather than sampled (T3)

Option-C C3 concluded from **179** random off-line placements at DZ that "as
far as sampling shows the failure set is *exactly* the deleted hinge's line".
The locus is a **curve** (`dim U = 3` there: the rank-≤1 locus of a `2 × 3`
form matrix has codimension 2), and random sampling of a 3-dimensional domain
**cannot** meet a curve — so the figure `0/179` was never evidence for the
conclusion it was quoted for.

Solving instead of sampling: on a line through an end, `A(â) = 0` makes the
wedge system `t · (W₁ + t W₂) = 0`, whose non-anchor root solves a **linear**
system exactly. `breakhunt.py locus` (11 s): at DZ's non-hub-ends split, one
constructed line carries a legal solution, and it is **off** `line(a,b)` with
observed exact rank **113 = 114 − 1**.

> **(BE-7)** *(T3, corroboration — not a hit)* The route-A failure locus at
> DZ's corank-2 seeds is **strictly larger** than `line(a,b)`. This is the
> already-settled `∀`-form refutation (§(K-tight) *Step 2.4*'s `line(a,b) ∪
> P′`) reproduced at the (K-bare) stratum; the `∃`-form side condition is
> unaffected. What is new is only that C3's gloss is corrected **at DZ
> itself**, by construction.

### Step BE6 — the second gadget against option-C's C1

C1's structural plus — "at these seeds the target-rank hypothesis itself
polices exactly the local chain degeneracy the insertion calculus needs" —
was flagged as one gadget, one sampler family. `breakhunt.py c1b` (19 s) runs
four degeneration strata at the **cube index-2 gadget** and at DZ as control:

| stratum | Q3 index-2 | DZ (control) |
|---|---|---|
| apex-star collinear | 0/8 at target′ (131) | 0/8 at target′ (107) |
| every-hub-star collinear | 0/8 at target′ (131) | 0/8 at target′ (107) |
| global hub-coplanar | **8/8 AT target′** (132) | **8/8 AT target′** (108) |
| global flat | 0/7 at target′ (120) | 0/8 at target′ (98) |

> **(BE-8)** *(measured)* C1's finding **corroborates at a second gadget** for
> the collinear and global-flat strata, and its *general reading* is
> **refuted**: two strata are target-compatible — the global hub-coplanar one
> (already noted at DZ as C1's D4) and the **local flat**, which is where the
> (BE-5) hit lives. "The rank antecedent polices the degeneracy" is a
> stratum-by-stratum observation, never a principle.

### Step BE7 — no T2 candidate, and why this harness cannot make one

`breakhunt.py tiers` (1 s): DZ attains `114/114` and the cube index-2 gadget
attains `138/138`, each exact-ℚ-confirmed, through a **different sampler**
from the one that first recorded them — so both figures are independently
reproduced and **neither gadget is a T2 candidate**. The gate's seven gadgets
were already known to attain.

> **(BE-9)** *(methodological, and a cap disclosure — **the first sentence's
> pessimism CORRECTED 2026-08-26 by (BE-13), direction BATTAIN**)* T2 is a
> **universal non-existence** over frameworks and no sampler can certify it —
> that half stands. ~~and so a T2 witness is not producible by this
> harness~~ **does NOT follow, and is now known false as stated:** a rank
> upper bound valid for all pencil configurations IS producible **by an
> argument**, and (BE-13) is one — the exact cone law `6(|V|−1) − def₂(G)`,
> which reduces T2 at a forced cone to the *decidable* criterion
> `def₂ > def₃`. What actually blocks T2 is **narrower and structural**:
> forcing the cone needs three shared closed-star normals, hence a common
> neighbour of two adjacent bodies — a **triangle** — and the habitat is
> **triangle-free** by `hnoRigid` (`Escape.lean:411–418`, via
> `Graph.triangle_isProperRigidSubgraph`). **The subclass objection stands
> but is INERT** ((BE-13)): the affine class is Zariski-**dense** in `Y°`, a
> tower of linear fibrations, hence irreducible and rational. (BE-4)'s
> propagation rule still points away from a global collapse.

**Harness disclosure, in the (OC-7) shape.** The recorded (K-bare) DZ figures
are drawn through `danger.sample_dz_pencil`, which places the apex's three
hub neighbours with `kbare_common.point_in_plane3` — the **known-degenerate**
`plane_basis` member (`notes/scripts/README.md` *Divergences*): when the drawn
normal's third coordinate is `0`, the three land on **one line**, i.e.
silently on option-C's own D3 "apex star collinear" stratum. Measured over the
58 seed draws behind the recorded DZ/C1/C2/C3 figures: it fires at **4**
(`8201`, `11002`, `11103`, `13051`). Small, and disclosed rather than
smoothed: one of `danger.py`'s corank-2 hub-end extension seeds and one of the
C2 mini-gate's extension seeds sit on a deeper stratum than their labels say.
No recorded figure is *moved* by this note (no landed driver was edited); this
driver uses the robust sampler throughout, and `repin.star_generic` is
recorded per seed rather than asserted, because in an infeasible habitat a
nondegeneracy guard cannot be a gate.

### Step BE8 — what the statement should now say, and what it costs

The `∀`-seed form is dead, so the live shapes are:

1. **The `∃`-seed form** — *some* target-rank bare realization of `G′` admits
   an attaining insertion — **plus a seed-repair obligation**: from the
   opaque seed `hbareSplit`'s antecedent hands you, produce a good one. This
   is exactly the "arbitrary-seed/seed-repair extension of the calculus" the
   design doc named as the new mathematics, now **forced** rather than
   merely prudent. The repair is a deformation statement inside
   `HasPencilRealization K 3 G′`'s own attainment locus, with **no chart
   available** (the habitat is infeasible), which is the same wall §(K-tight)
   *Step 5* meets one level up.
2. **A seed side condition**, named by the mechanism: `rank⟨U, Λ²Π̂(b)⟩ ≥ 2`
   (sufficient to defeat the exhibited failure, by (BE-2)). Any such
   condition needs its own supply lemma, i.e. it reduces to shape 1.
3. **Bypass the antecedent entirely** — prove `HasPencilRealization K 3 G`
   directly on the habitat. Strictly stronger than `hbareSplit`, but
   **seed-free**, and the hit says the antecedent is a liability rather than
   an asset: it supplies an object route A cannot use.

**Verdict: (K-bare-ext) REFUTED as stated (tier T1); `hbareSplit` OPEN and
unchanged, carried as pinned.** *What would change this:* for the refutation,
an error in the model-to-Lean dictionary (the five-rows-per-hinge carrier vs
`BodyHingeFramework.rigidityRows`) — the same single point of failure
§(K-tight) names, and the hit is stated in that carrier's terms; for
`hbareSplit`, either a discharge along shape 1/3 above, or a T2 witness, which
would be a **PENCIL event** and not this section's to declare.

**Verification.** `python3 notes/scripts/kbare/breakhunt.py tiers` (1 s,
(BE-9) + the two attainment figures); `calc` (118 s, (BE-2)/(BE-3), the
192/192 corank identity); `arith` (1 s, (BE-6) and the 216-member census);
`rzero` (322 s, the (BE-5) hit and the `dim R_a = 0` cap report); `locus`
(11 s, (BE-7)); `c1b` (19 s, (BE-8)).
