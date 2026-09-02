# PENCIL — W4 residual-arc informal mathematics workbook

**Purpose.** The **W4 (`hcontract`) residual arc** of Phase 39 (PENCIL), split
out of `notes/Pencil-informal.md` (2026-08-05) so that a kernel-(K) research
pass reads only live (K) material. Its three sections are closed **as
arguments** — `hnoGood'` vacuity REFUTED, (SAFE-RES) REFUTED with the successor
(SAFE-RES′) open, the routes-1/3 kernel widening PRICED — and all three are
live **as input to the eventual W4 build**: they carry the residual structure
theorem ((C7)/(C8) at a maximal cluster), the statement of (SAFE-RES′), the
statement of the widened kernel **(K-res)**, and the (E)/(E-loc)/(V) gap
inventory the route-3(b) adjudication is pinned on — **(T) left that inventory
2026-09-02**, proved in §(SAFE-RES) *Step TF5*. They are kept at full
detail for exactly that reason.

**W4 is parked.** The standing adjudication (2026-08-02, user) is route **3,
packaging (b)** — the structure-theorem-pinned dispatch invariant, *recorded as
a decision, not built*, while the (K)-family research continues (the route's
kernel and the pinned `hK` share their crux). Nothing here is commissioned;
when the W4 build is, this file is its mathematical input, and
`notes/Phase39.md` *Hand-off* carries the leaf sequence (first commit W4-L4b).

**Discipline** — the same as `notes/Pencil-informal.md`'s, i.e. `notes/CLAUDE.md`'s
workbook rules. Each section reads as the **current state of its argument**,
revised in place (git is the changelog; superseded reasoning does not stay
inline). Each carries an explicit **confidence verdict** — *proven-informally*
/ *true-modulo-named-gap* / *open* / *refuted* — plus a **"what would change
this"** line naming the observation that would move it. Landed Lean facts are
cited by declaration name; every appeal to `PencilNondegFeasible` says whether
it is landed-**sufficient**, landed-**necessary**, or **middle zone**. Dated
recon history lives in `notes/Phase39-design.md` and the one-line decisions in
`notes/Phase39.md` *Decisions made*; this file carries only the mathematics.

**Cross-file reading.** The kernel-(K) arc — §(K-tight), §(K-pitch),
§(K-slide), §(K-slide-cl), §(K-slide-comb), §(K-bare-ext) — and the **Shared
dictionary** every section here depends on (the deficiency/rigidity vocabulary,
the consequences **(R1)**–**(R5)** cited throughout below, and the canonical
definitions of the test shapes `W19` and `S29`) are in **`notes/Pencil-informal.md`**; its
*State of (K)* map is the entry point to that arc. Section references below
name the file whenever they leave this one; a bare `§…` is a section of this
file.

**Labels.** This file's `(C1)`–`(C6)` (§`hnoGood'` vacuity), `(C7)`/`(C8)` and
`(TF-1)`–`(TF-6)` (§(SAFE-RES)) are a **different family** from `notes/Pencil-informal.md`
§(K-slide-cl)/§(K-slide-comb)'s same-numbered labels, and from
`notes/Pencil-strategy.md` §4's C1/C2/C3. The registry that records all three,
and the minting rule that prevents the next such clash, is
**`notes/Pencil-labels.md`** — read it before minting a label, and qualify every
cross-section citation with its owner.

## §`hnoGood'` vacuity — **REFUTED**

**Verdict: refuted.** The W4-L4 recon's conjecture — *every simple, 2EC,
`PencilNondegFeasible` graph with `3 ≤ |V|` and a proper rigid subgraph has
either a co-1 rigid subgraph or a rigid contraction that is
`Simple ∧ PencilNondegFeasible`* — is **false**. An explicit `|V| = 19`
counterexample is below; it is machine-verified end to end, and both of its
feasibility verdicts are **landed-lemma-certified** (not middle-zone), so the
refutation does not depend on any unproven feasibility fact.

**What would change this:** an error in the rigidity computation (two
independent oracles agree — see *Verification*), or a misreading of
`IsProperRigidSubgraph` / `rigidContract` / `closedHubNbhd` (each was read
from the definition body, and each load-bearing consequence is re-derived
below).

The Lean shape of `hnoGood'` is pinned in `notes/Phase39-design.md`
§"W4-L4 identification recon" Verdict 4. Refuting vacuity does **not** refute
`hnoGood'` itself — its conclusion is the pencil conjecture at `G`, expected
true. What dies is the cheap discharge route: **branch 4 of the W4 skeleton
needs real content.** Consequences are in *What this costs W4* below.

### Step 1 — the Ear Lemma (the tool the earlier search was missing)

> **Ear Lemma.** Let `H` be rigid and let `P` be a path with both endpoints in
> `V(H)` and `j` interior vertices disjoint from `V(H)`. Then `H ∪ P` is
> rigid **iff** `j ≤ 5` (given `H` rigid).

*Proof (packing form).* `5(H ∪ P)` must carry 6 edge-disjoint spanning trees.
Restricted to the ear, each tree needs `j` of the `j + 1` new edges (the ear
plus its two attachments closes one cycle through `H`), i.e. each tree omits
exactly one new edge; each new edge has capacity `5`, so each must be omitted
by at least one of the 6 trees, forcing `j + 1 ≤ 6`. Conversely at
`j ≥ 6` the finest-partition count already fails:
`f` changes by `5(j+1) − 6j = 5 − j < 0` while `f(V(H)) ≥ 0` is needed. ∎

Special cases: `j = 1` is "a vertex with two edges into a rigid `H`";
`H` = a single vertex recovers **(R3)**. Numerically re-checked for
`j = 0..7` (`--validate`).

This is what makes the residual habitat **large**: at a *maximal* rigid
subgraph every ear through the complement must have `≥ 6` interior vertices,
so residual instances have long branches and cannot be small. The W4-L4
recon's search capped `|V| ≤ 13` and used gadget paths with `≤ 3` interior
vertices — both caps sit strictly below the threshold, which is why it
returned 0 candidates.

### Step 2 — what a maximal cluster's contraction looks like

Let `H` be a **maximal** induced-saturated proper rigid subgraph,
`S = V(H)`, `T = V(G) ∖ S`, `t = |T|`.

- **(C1) simplicity is free.** No `w ∈ T` has two neighbours in `S` (Ear
  Lemma at `j = 1`: `S ∪ {w}` would be rigid, contradicting maximality unless
  it spans — which is the excluded co-1 case). Hence `G/H` is simple. This is
  the design doc's recorded bridge, re-derived.
- **(C2) outside degrees are preserved.** Each `w ∈ T` has `≤ 1` edge into
  `S`, so `deg_{G/H}(w) = deg_G(w)`; hubs outside stay hubs and non-hubs stay
  non-hubs.
- **(C3) every boundary attachment point is a `G`-hub.** If `w ∈ T` attaches
  to `u ∈ S`, then `deg_G(u) ≥ deg_H(u) + 1 ≥ 3` by **(R1)**.
- **(C4) `hcard` can only fail at `v*`.** By (C2)+(C3) an outside vertex
  trades the hub `u` for the hub `v*` in its closed hub-neighbourhood, no net
  gain; so `G/H` violates `hcard` iff **`v*` is a hub with `≥ 3` hub
  neighbours**, i.e. `≥ 3` boundary vertices of `T` have `deg_G ≥ 3`.
- **(C5) no triangle through `v*`** (new). If `w, w' ∈ T` are adjacent and
  both attach to `S`, then `S ∪ {w, w'}` is rigid (an ear with `j = 2`), so
  by maximality `t = 2`; and then `G/H` is exactly the **spanning `C₃`**,
  which is landed-feasible (L7c-3). So a `v*`-triangle never obstructs.
- **(C6) the boundary-hub budget.** At most 2 boundary hubs attach at one
  `u ∈ S` (else `u` has 3 hub neighbours, contradicting `hcard` in `G`), and
  a `u` already carrying 2 hub neighbours *inside* `S` can carry none. Hence
  a `C₃` core (`≤ 1` hub by **(R5)**) and a `C₄` core with 3 or 4 hubs, or
  with 2 *adjacent* hubs, always give `hcard` at `v*`. The **first** core that
  can break it is a `C₄` whose two hubs are **opposite**.

So for a maximal cluster the *only* obstructions left are (a) `¬hcard` at
`v*` via (C4)/(C6), and (b) a triangle already inside `G[T]` (which lands in
the middle zone rather than in a landed verdict).

### Step 3 — the counterexample `W19`

Mechanism (a) of Step 2, realized with branches long enough for the Ear Lemma
to protect maximality. `W19` — a `C₄` core, three degree-3 poles, three
4-interior paths; `|V| = 19`, `|E| = 22`, hubs `{c0, c2, z0, z1, z2}` — is
defined in `notes/Pencil-informal.md` *Shared dictionary* → *Test shapes `W19`
and `S29`*, its canonical home; vertex names below are that definition's.

- **`G` is simple, 2-edge-connected, `3 ≤ |V|`.** ✓
- **`G` is `PencilNondegFeasible`** — landed-**sufficient**, no middle zone:
  `hcard` holds (`closedHubNbhd(c0) = {c0, z0, z1}`,
  `closedHubNbhd(c2) = {c2, z2}`, `closedHubNbhd(z_i) = {z_i, c·}`, all
  others `≤ 2`) and `G` is triangle-free (girth 4, the core), so L6b
  `pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`
  applies (its `[Infinite K]` is the ambient instance of
  `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`).
- **The only proper rigid subgraph is the core `C₄`.** By **(R1)** a rigid
  `W` is its own 2-core, so every degree-2 vertex of `W` drags its whole
  branch and both branch endpoints in; the candidate `W` are therefore unions
  of branches. The core is rigid by **(R3)**. Every other branch union has
  `f < 0` or fails the packing condition: adding one whole pole path to the
  core is an ear with `j = 6` (`z_i`, four path vertices, `z_j`), refuted by
  the Ear Lemma; the outer 15-cycle has `f = 75 − 84 < 0`; two independent
  cycles need `|W| ≤ 11` by **(R2)** but the two shortest cycles already
  span 12 vertices. Machine-checked exhaustively (below).
- **No co-1:** `|V(H)| + 1 = 5 < 19`. ✓
- **Every contraction fails.** For non-induced `H` the contraction carries a
  loop at `v*` (not simple). For the core, `G / E(C₄)` is simple with
  `deg(v*) = 3` and neighbours `z0, z1, z2` all of degree `3`, so
  `closedHubNbhd(v*) = {v*, z0, z1, z2}` has **4** members and the landed
  **necessary** condition
  `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` refutes
  `PencilNondegFeasible K (G.rigidContract H r)` for every `r`. ✓

Both directions are landed-lemma-certified — the counterexample is *not* a
middle-zone artifact.

**Robustness.** Lengthening the three paths preserves every verdict and
raises the deficiency, so **both deficiency regimes are inhabited**:
`lengths (4,4,4) → def(G) = 0`, `(4,4,6) → def(G) = 2`,
`(5,5,5) → def(G) = 3`. Replacing the core by `C₅`/`C₆` and varying the pole
attachment gives 96 further inhabitants.

**Minimality.** A 21455-instance sweep over cores `C₃…C₆`, 3 or 4 poles at
all attachment multisets, and **independent** path lengths `0..4` puts the
minimum at `|V| = 19`, matching the structural lower bound: `≥ 3` poles are
needed by (C4); each pole needs 2 further edges, so the outside graph on the
poles has min degree 2 and contains a cycle, i.e. `≥ 3` paths; each path must
carry `≥ 4` interior vertices (the ear `core–pole–path–pole–core` has
`2 + L` interior, and the Ear Lemma needs `≥ 6`); and the smallest core that
survives (C6) is `C₄`, giving `4 + 3 + 12 = 19`.

### Verification

`notes/scripts/w4/nogood_subdiv.py` (tracked; exact integer arithmetic).

- Rigidity oracle: `def(H) = 6(|V|−1) − rank_{(6,6)}(5H)` — the matroid-union
  rank identity `r = min_P [5 d(P) + 6(|V|−|P|)]` — computed by the
  Lee–Streinu `(6,6)` pebble game. `--validate` checks it against the
  independent partition/packing oracle `kbare_common.exact_deficiency` used
  by every earlier Phase-39 gate: **400/400 agreement**; `C_k` rigid iff
  `k ≤ 6`; the Ear Lemma threshold at `j = 5/6`.
- Rigid-subset enumeration by branch subsets (justified by **(R1)**), checked
  against a brute-force subset sweep on 120 random 2EC graphs: **0
  mismatches**.
- `--witness` re-derives `W19` from scratch and re-checks *all* `2^19` vertex
  subsets with both oracles agreeing on every survivor of the
  `f ≥ 0` + min-degree-2 prefilter.

Reproduce:
`python3 notes/scripts/w4/nogood_subdiv.py --validate | --witness | --min`.

### What survives (reusable positive content)

The steps above are not wasted by the refutation — they are a *structure
theorem for the contraction branch*, and they say exactly when the good
contraction exists:

> Let `G` be simple, 2EC, feasible, with a proper rigid subgraph and no co-1
> rigid subgraph, and let `H` be a maximal induced rigid proper subgraph.
> Then `G/H` is simple; it satisfies `hcard` unless `≥ 3` boundary vertices
> are `G`-hubs; it has no triangle through `v*`; and if additionally `G[T]`
> is triangle-free, `G/H` is `PencilNondegFeasible` by L6b.

In particular the "two-hub multi-path" and "pendant triangle / bowtie"
families the earlier search kept dissolving are all covered by (C5)/(C6);
the residual is exactly the `≥ 3`-boundary-hub configuration.

### What this costs W4, and the routes out

Branch 4 of the reshaped skeleton (L3′) can no longer be discharged by
vacuity. Three routes, in increasing cost:

1. **Re-dispatch the residual to the split arm** (recommended for
   assessment first). The split arm's inputs at a residual `G`, and the
   `hnoRigid` points the landed chain consumes, are worked out in
   **§(SAFE-RES)** below — the deep-split-vertex conjecture that used to be
   stated here is **refuted**, and its surviving successor (SAFE-RES′) is
   that section's subject. The kernel-widening cost is priced in
   **§"widened kernels (routes 1/3)"**: it is **one** kernel — the
   `noRigid`-free **(K-res)** (`hbareSplit` is unreachable at a residual,
   which is feasible by hypothesis) — carried alongside the byte-identical
   `hK`, plus a residual-habitat sibling of the L7a leaf.
2. **Discharge branch 4 directly**: build a generic realization of `G` from
   the IH's *bare* half at an infeasible contraction. This is the hardest
   kernel shape in the phase (strictly stronger than `hbareContract`, which
   only has to produce the bare conclusion).
3. **Change the dispatch invariant** so the contraction branch is only
   entered when a good contraction exists — i.e. carry the Step-2 structure
   theorem as the branch condition and route the `≥ 3`-boundary-hub
   configuration to the split arm. Same kernel cost as route 1, but the case
   analysis is pinned by Step 2 (now also by §(SAFE-RES)'s (C7)/(C8)) rather
   than by a new conjecture. §(SAFE-RES) Step 1 sharpens what this route
   inherits: at a **triangle-free** residual, case (A) — `≥ 3` boundary
   hubs — is the *only* configuration, so route 3's case analysis is a
   two-way split, not an open-ended one.

**ADJUDICATED (2026-08-02, user): route 3, packaging (b)** — recorded as a decision, not
built; W4 stays parked while the (K)-family research proceeds (the route's kernel and the
pinned `hK` share their crux). Both routes needed the same bundle:

- **(K-res)**, one extra carried kernel — same statement shape and same
  difficulty class as `hK`, on the complementary habitat; supported by
  exact-ℚ numerics at every residual probed (§"widened kernels" Steps 4–5).
  Its *proof route* is strictly harder than `hK`'s: the residual habitat sits
  wholesale in the `dim R_a = 1` stratum where the (K) recon found no
  landed-brick route (Step 2).
- **(T)** and **(V)** of §(SAFE-RES′), unchanged.
- **(E)**, now reduced to a cheap `noRigid`-free Lean leaf plus the new
  combinatorial gap **(E-loc)** (§"widened kernels" Step 3, 255/255).

Neither route needs `hbareSplit` to move.

## §(SAFE-RES) — **REFUTED**; successor (SAFE-RES′) open

**Verdict: refuted.** §`hnoGood'` route 1 pinned

> **(SAFE-RES)** *every residual `G` has a degree-2 vertex strictly interior to
> a branch with `≥ 3` interior vertices (a "deep split vertex")*

on the strength of 93/93 sweep inhabitants. It is **false**. `S29` (*Step 2*)
is a `|V| = 29` residual, certified to the same standard as `W19` — both
feasibility verdicts landed-lemma-backed, no middle zone — in which **every**
branch carries at most `2` interior vertices. What survives is the strictly
weaker **(SAFE-RES′)** of *Step 3*, which is what the landed split arm actually
consumes; it is **open**, holds on 255/255 inhabitants swept, and reduced to two
named gaps — the residual's edge count **(E)** and its triangle-freeness **(T)**.
**(T) IS NOW A THEOREM** (*Steps TF1–TF5*, direction WTRI 2026-09-02): no feasible
residual carries a triangle at all, by two **landed** feasibility transfers this
section's own *Step 4* had not inventoried. So (SAFE-RES′) reduces to **(E)** —
itself reduced further to (E-loc), §"widened kernels (routes 1/3)" *Step 3* — plus
the local choice **(V)**, and route 3's cost list drops from four items to three.

Here *residual* abbreviates `hnoGood'`'s antecedent bundle (`notes/Phase39-design.md`
§"W4-L4 identification recon" Verdict 4): `G.Simple`, `3 ≤ |V(G)|`,
`G.TwoEdgeConnected`, `PencilNondegFeasible K G`, a proper rigid subgraph exists,
**no** co-1 rigid subgraph, and **no** `(H, r)` whose `rigidContract` is
`Simple ∧ PencilNondegFeasible`. Branch / hub vocabulary is **(R4)**: a
**branch** is a maximal path all of whose interior vertices have degree `2`,
with hub endpoints (a 2EC feasible `G` with a hub is a subdivision of its hub
multigraph).

**What would change this.** *For the refutation:* an arithmetic error (three
independent integer-exact oracles agree — *Verification*), or a misreading of
the split arm's `hnoRigid` consumption (all five points were read from the
landed proof bodies, not docstrings). *For the successor:* a proof or
counterexample for **(E)** (equivalently (E-loc)), or a residual every one of whose
`≥ 2`-interior branches is one of (V)'s two `C₄`-carrying shapes. **Not (T)** — that
is settled (*Step TF5*); what would change *it* is an error in the two landed
transfers it composes, or in the four mechanical Lean obligations *Step TF6* lists.

### Step 0 — what the split arm actually consumes (`hnoRigid`, five points)

Read off the landed chain `hasGenericPencilRealization_of_splitOff_of_safe`
(`Molecule/Pencil/Escape.lean:95`) and `pencilPair_of_splitOff_of_habitat`
(`:334`), at a degree-`2` vertex `v` with neighbours `a ≠ b`:

- **(S0)** `simple_of_loopless_of_noRigid` — free at a residual (`G.Simple` is
  a hypothesis).
- **(S1)+(S2)** the safe pair, from
  `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two`
  (`Induction/ReducibleVertex.lean:1383`): `deg v = 2` and `deg a = 2` (so
  `hsafe : ¬G.PencilHub a ∨ ¬G.PencilHub b`, `PencilHub w ↔ w ∈ V(G) ∧ 3 ≤ deg w`).
  **New reading (this recon).** Its `hnoRigid` enters *only* through
  `edgeBound_of_noRigid_of_degree_two` (`:1270`), whose sole output is the
  KT-4.5(i) count. The actual consumer
  `exists_adjacent_degree_two_pair_of_edgeBound` (`:1068`) is already
  rigid-free: it needs `[G.Loopless]`, `3 ≤ |V(G)|`, `G.TwoEdgeConnected`, and
  `(D−1)|E| < D(|V|−1) + (D−1)` — at `D = 6`, `5|E| < 6(|V|−1) + 5`. So in the
  residual habitat (S1)+(S2) reduce to the **pure counting hypothesis**

  > **(E)**  `f(V(G)) := 5|E(G)| − 6(|V(G)| − 1) ≤ 4`.

- **(S3)** `a ≁ b` — all that `splitOff_simple_of_noRigid_of_card`
  (`Induction/Operations.lean:1149`) needs `hnoRigid` for: it kills the
  triangle `{v, a, b}` an `ab`-edge would create, via
  `triangle_isProperRigidSubgraph`.
- **(S4)** `N(a) ∩ N(b) = {v}` — the induced-`C₄` arm of
  `splitOff_triangleFree_of_noRigid` (`Molecule/Pencil/Habitat.lean:300`), via
  `c4_isProperRigidSubgraph`; `deg v = 2` already supplies the second diagonal
  `vc ∉ E(G)`.
- **(S5)** **`G` is triangle-free** — the *other* arm of the same lemma: a
  `G′`-triangle avoiding the fresh edge `e₀` is a `G`-triangle, i.e. a proper
  rigid subgraph.

*Correction to the route-1 text.* The claim that a deep split vertex makes "the
split's simplicity and triangle-freeness re-derive" is three-quarters true: it
buys (S2), (S3) and (S4), **not** (S5), which is a global condition on `G` and
is exactly the gap (T) below.

### Step 1 — new structure at a maximal cluster of a residual

Extends §`hnoGood'` Step 2. Let `H` be the maximal induced-saturated proper
rigid subgraph of `exists_maximal_induced_isProperRigidSubgraph`
(`Molecular/Deficiency.lean:978` — maximal in **vertex cardinality among all**
proper rigid subgraphs, and induced-saturated; `IsProperRigidSubgraph H G n`
is `H.IsRigidSubgraph G n ∧ 2 ≤ |V(H)| ∧ V(H) ⊂ V(G)`, `Deficiency.lean:483`).
Write `S = V(H)`, `T = V(G) ∖ S`, `t = |T| ≥ 2` (`t = 1` is the excluded co-1
case). An **ear** is a path with both ends in `S` and interior in `T`; the
degenerate closed ear (both ends at the same `u ∈ S`) obeys the same Ear-Lemma
count `5(j+1) − 6j = 5 − j` and is numerically re-checked for `j = 0..7`.

> **(C7) Every ear through `T` has `≥ 6` interior vertices.**

*Proof.* Ear Lemma + maximality give the dichotomy: an ear `P` with
`1 ≤ j ≤ 5` interior vertices makes `G[S ∪ int(P)]` rigid with `> |S|`
vertices, so it cannot be *proper* — hence `int(P) = T` and `t = j ≤ 5`.
Suppose that happens; `T` is then the path `w₁ … w_t`. (i) No `w_i` with
`1 < i < t` has an `S`-edge: it would give an ear with `i < t` interior
vertices, which by the dichotomy would have to cover `T`. (ii) `G[T]` has no
chord `w_i w_j` (`j > i+1`): routing the covering ear through it produces a
shorter one, same contradiction. So `G[T]` is exactly that path and every
`T`-vertex has `deg_G = 2`; with (C1) the contraction `G/H` is the **cycle**
`C_{t+1}` on `{v*, w₁, …, w_t}`. For `t = 2` that is the spanning `C₃`,
feasible by the landed-**sufficient** L7c-3 witness; for `t ≥ 3` it is hub-free
and triangle-free, so feasible by the landed-**sufficient** L6b. Either way
`G/H` is `Simple ∧ Feasible` — a good contraction, contradicting the residual. ∎

> **(C8) Dichotomy at a maximal cluster.** `G/H` is simple (C1) and infeasible,
> and `¬`(landed-sufficient) is `¬hcard ∨ ∃ triangle`; a `v*`-triangle is
> excluded by (C5). So exactly one of
> **(A)** `v*` is a hub of `G/H` with `≥ 3` hub neighbours — i.e. `≥ 3`
> boundary vertices of `T` are `G`-hubs — or
> **(B)** `G[T]` carries a triangle, which by **(R5)** is a *pendant* triangle
> of `G` (two adjacent degree-`2` vertices with a common hub), i.e. a petal
> branch with `2` interior vertices.
> In particular **(A) holds at every maximal cluster of every residual** — the
> triangle-free proviso this line originally carried is vacuous since
> *Step TF5*, which rules out case (B) outright.

(C7) + (C8)(A) + (C6) pin the shape: the core is at least a `C₄` with its two
hubs opposite, it carries `≥ 3` boundary hubs spread over `≥ 2` attachment
points, and those boundary hubs are pairwise at `G[T]`-distance `≥ 5`.

### Step 2 — the refutation: `S29`

`S29` — a `C₄` core with three hub-edge poles, a 2-subdivided hub ring on the
poles, and three 2-subdivided spokes to a centre — is defined in
`notes/Pencil-informal.md` *Shared dictionary* → *Test shapes `W19` and `S29`*,
its canonical home; vertex names below are that definition's.

`|V| = 29`, `|E| = 34`, `f(V(G)) = 2`, `def(G) = 0`. Hubs (9):
`A, B, z0, z1, z2, y0, y1, y2, p`; **every one of the 14 branches carries
`0`, `1` or `2` interior vertices** — max `2`, so there is **no deep split
vertex**.

- **Residual, both verdicts landed-certified.** `G` is simple, 2EC, and
  `PencilNondegFeasible` by **L6b** (`hcard`: the hub-induced graph is the path
  `z0 – A – z1` plus the edge `B – z2`, max degree 2; girth 4, so triangle-free).
  The unique proper rigid subgraph is the core `{A, m1, B, m2}` (`C₄`, **(R3)**);
  `|V(H)| + 1 = 5 < 29`, so no co-1; and `G/H` is simple with
  `closedHubNbhd(v*) = {v*, z0, z1, z2}` of size **4**, refuted by the landed
  *necessary* `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`.
- **Why the Ear Lemma cannot see it.** The ear `A – z0 – ⋯ – z1 – A` has 7
  interior vertices — comfortably past the Ear Lemma's threshold, so the core
  stays maximal — but it decomposes as `A–z0` (0 interior) + `z0…y0` (2) +
  `y0…z1` (2) + `z1–A` (0). *All the ear length is carried by hub chains.* The
  Ear Lemma bounds ears; (SAFE-RES) asserted something about branches; the
  witness lives exactly in that gap, which is the failure the coordinator
  flagged.
- **Why it has to be this big — the branch arithmetic.** Let `h` = #hubs,
  `b` = #branches, `I = |V| − h` the total branch interior, `c` the cycle rank.
  Then `|E| = b + I`, `c = b − h + 1`, and

  ```
  f(V(G)) = 5c − (|V| − 1) = 5b − 6h + 6 − I .
  ```

  Min degree `3` at hubs gives `2b ≥ 3h`. If every branch has `≤ κ` interior
  vertices then `I ≤ κb`, so `f(V(G)) ≥ (5 − κ)b − 6h + 6`.
  - `κ ≤ 1`: `f(V(G)) ≥ 4b − 6h + 6 ≥ 6h − 6h + 6 = 6 > 4`, so **(E)'s
    inequality fails for such a graph** — one with at least one hub and every
    branch at `≤ 1` interior vertex violates the KT-4.5(i) edge bound. (The
    hubless case is not residual at all: `G` is then a cycle, whose proper
    subgraphs are forests, so no proper rigid subgraph exists.) (Dually,
    `f(V(G)) ≥ 4` is exactly the range in which a degree-`2` co-1 rigid
    subgraph is arithmetically permitted, since
    `f(V(G − v)) = f(V(G)) − 4`.) **Conditionality.** What this proves outright
    is only that a `κ ≤ 1` graph with a hub violates the KT-4.5(i) count; it
    rules out `κ ≤ 1` *residuals* solely through **(E)**, which is open
    (Step 3). So the short-branch probes' emptiness — 366 instances in
    §`hnoGood'`, 343 here — is *evidence for* (E), not a consequence of the
    arithmetic.
  - `κ = 2`: `f(V(G)) ≥ 6 − 1.5h`, no obstruction from `h ≥ 2` — but equality
    pressure forces the graph to be near-cubic and near-fully-subdivided.
    `S29` is exactly that (`h = 9`, `b = 14`, `I = 20`, `f = 2`).

  Two things to keep apart. **Unconditional:** `κ = 2` residuals exist
  (`S29`), so `κ ≥ 3` — (SAFE-RES) — is false; and a `κ ≤ 1` graph with a hub
  violates the KT-4.5(i) count. **Conditional on (E):** the matching lower
  bound `κ ≥ 2` at a residual, which is then not new work at all — it is the
  landed `exists_adjacent_degree_two_pair_of_edgeBound`. So the picture is
  that (SAFE-RES) was one notch too strong, `S29` attains the true value, and
  the whole branch-length question collapses into (E).

### Step 3 — the successor (SAFE-RES′)

> **(SAFE-RES′)** *A residual `G` is triangle-free and carries a degree-`2`
> vertex `v` whose neighbours `a ≠ b` satisfy `deg a = 2 ∨ deg b = 2`,
> `a ≁ b`, and `N(a) ∩ N(b) = {v}`.* — i.e. exactly (S1)–(S5).

**Verdict: open**, 255/255 on every residual inhabitant swept (both scripts'
families; `saferes.py --prime`). It decomposes into three obligations:

- **(E)** `f(V(G)) ≤ 4` — **open, but no longer the sharpest thing route 1
  needs: it is now reduced to (E-loc)**, §"widened kernels (routes 1/3)"
  *Step 3*. It *is* KT Lemma 4.5(i)'s conclusion, landed only under `hnoRigid`
  (`edgeBound_of_noRigid_of_degree_two`) — but that lemma consumes `hnoRigid`
  at exactly one point, to make the `v`-avoiding edge fiber count-independent,
  and 255/255 residuals carry a degree-`2` vertex at which that independence
  holds outright. Numerics: 255/255 for `f ≤ 4` itself, and `S29`, `W19` both
  sit at `f = 2`. (The natural direct attempt — bound `f(V(G))` by `f(S) + …`
  at a maximal cluster — leaks because `f(S)` of a dense rigid `H` is
  unbounded; the (E-loc) route replaces it.)
- **(T)** `G` triangle-free — **PROVED** (*Steps TF1–TF5*). The recorded
  255/255 was **never** evidence for it (the sweep's feasibility certificate is
  L6b, which *requires* triangle-freeness, so a triangle-carrying residual can
  never appear in a certified sweep) and it is not what settles it: the proof is
  a two-case contraction argument on two **landed** feasibility transfers.
- **(V)** the local choice — **elementary given (E) and (T).** (E) supplies a
  branch `β` with `j ≥ 2` interior vertices `x₁ … x_j` and hub ends `u, u'`.
  Then:
  - `j ≥ 4`, or `j = 3` with `u ≠ u'`: take `v = x₂`; `a = x₁`, `b = x₃` are
    degree `2`, non-adjacent, and share only `x₂`. ✓
  - `j = 2` with `u ≠ u'` and `u ≁ u'`: take `v = x₁`; `a = x₂` (degree 2),
    `b = u`, `N(u) ∩ N(x₂) = {x₁}`. ✓
  - the three residues — `j = 2` with `u = u'` (a pendant triangle, **killed
    outright by the (T) theorem**, *Step TF5*); `j = 3` with `u = u'`; `j = 2`
    with `u ~ u'` — are unusable at every
    vertex of `β`. Each of the last two exhibits a **chordless induced `C₄`**
    (`u, x₁, x₂, u'` resp. `u, x₁, x₂, x₃`), hence a proper rigid subgraph, so
    they are natural material for the contraction arm rather than the split
    arm; a full proof of (V) must show that not *every* `≥ 2`-interior branch
    of a residual is of those two shapes.

### Step 4 — the pendant-triangle anatomy (the input to *Steps TF1–TF5*)

Let `Δ = {x, y, z}` be a triangle of a feasible `G` with `|V(G)| > 3`. By
**(R5)** `x, y` have degree `2` and `z` is a hub, so `Δ` is a *pendant*
triangle, and it is a proper rigid subgraph. Its contraction is simple (`x, y`
have no outside neighbours) and equals `G − x − y` with `z ↦ v*`,
`deg v* = deg z − 2`. The only degree that changes is `z`'s, and it only
*drops*, so no vertex gains hub status; `x, y` were not hubs, so
`closedHubNbhd_{G/Δ}(v*) ⊆ closedHubNbhd_G(z)[z ↦ v*]` and every other closed
hub neighbourhood is contained in its `G`-counterpart. Hence **`hcard(G/Δ)`
always holds**, and the residual's `¬Feasible(G/Δ)` can only be witnessed,
landed-wise, by a *second* triangle in `G − x − y`.

Consequence (ii) survives verbatim and is the reason numerics never decided this:
such a `G` is middle-zone (a 1-hub triangle is neither landed-sufficient-feasible
nor landed-necessary-infeasible), so it is **invisible to a certified search**.
So is the *contraction*: `G/Δ` inherits `hcard` and inherits ≤ 1-hub triangles
(both are downward-monotone in degree), so **neither verdict on `G/Δ` can be
certified either** — the blind spot is two-sided, which is sharper than what this
step originally recorded, and it is why the recorded 255/255 is not a denominator
one may reason from.

**Consequence (i) was WRONG and is retracted** (direction WTRI, 2026-09-02).
*"Two pendant triangles already satisfy every landed test, so (T) is not provable
from the landed set"* took *landed set* to mean the landed feasibility
**criteria** — L6b / L7c-3 on the sufficient side, `hcard` / no-two-hub-triangle
on the necessary side. The landed set also contains two feasibility **transfers**,
neither of which is a criterion and neither of which was inventoried here:
`PencilNondegFeasible.mono` and `pencilNondegFeasible_induce_of_pendant_deg3`
(`Molecule/Pencil/{Motive,Steer}.lean`). They decide `G/Δ` outright.
**(T) is a theorem** — *Steps TF1–TF5* below; the bowtie remark is subsumed (no
residual carries even *one* triangle, at any `|V|`, so a fortiori no bowtie), and
route 1/3's three options are moot: nothing is carried, nothing is relocated.

### Step TF1 — the landed inventory *Step 4* was missing

> **(TF-1) Two landed feasibility TRANSFERS, neither of them a criterion.**
> **(a)** `PencilNondegFeasible.mono` (`Molecule/Pencil/Motive.lean:272`;
> `[G.LocallyFinite]`): `PencilNondegFeasible K G → H ≤ G →
> (∀ v ∈ V(H), G.PencilHub v → H.PencilHub v ∨ H.degree v ≤ 1) →
> PencilNondegFeasible K H`. Feasibility descends to a subgraph as long as no
> `G`-hub lands at `H`-degree exactly `2`; that one case is the recorded
> **cut-arm demotion gap** (2026-07-24), and the `≤ 1` bound is sharp.
> **(b)** `pencilNondegFeasible_induce_of_pendant_deg3` (`Steer.lean:421`;
> `[Finite α] [Finite β] [Infinite K]`): at `G.Simple`, `G.degree u_c = 3`, one
> crossing edge `e_c : u_c–v_c`, `V(G) = V₁ ∪ {v_c}` and `u_c`'s two `V₁`-links to
> `w₁ ≠ w₂`, `PencilNondegFeasible K G → PencilNondegFeasible K (G.induce V₁)`.
> This one **closes the demotion-2 gap in its own configuration**, not by
> restricting the given witness but by re-seeding it into the pencil chart and
> **steering** to a common seed that makes the demoted triple `{u_c, w₁, w₂}`
> independent alongside every standing chart condition
> (`exists_common_seed_linearIndepOn_pencilChartPoint`).

**Neither carries a triangle-freeness hypothesis** — read off the landed
signatures, not the docstrings. That is the whole reason they see past L6b's
blind spot: L6b is a *criterion* and needs triangle-freeness; these are
*transfers* and do not.

### Step TF2 — the residual's pendant triangle, and what 2EC forces at its hub

Let `G` be a residual carrying a triangle `Δ`. Then:

> **(TF-2)** (i) `|V(G)| ≥ 5`; (ii) `Δ = G[{x, y, z}]` with `deg x = deg y = 2`
> and `z` the unique hub; (iii) `Δ` is a **proper rigid subgraph** with
> `z ∈ V(Δ)`; (iv) `G.rigidContract Δ z = G.induce (V(G) ∖ {x, y})`, which is
> **simple**; and (v) **`deg z ≥ 4`**.

*Proof.* `|V(G)| ≥ 4`: at `|V(G)| = 3` a proper rigid subgraph would need
`2 ≤ |V(H)|` and `V(H) ⊊ V(G)`, i.e. two vertices, and no `2`-vertex graph is
rigid (`two_le_degree_of_isKDof_zero`, **(R1)**) — so the residual's `∃`-rigid
clause fails. (ii) is *Step 4* via **(R5)**: `G` is connected with `|V(G)| > 3`,
so some vertex of `Δ` has an outside edge and is a hub, and
`not_pencilNondegFeasible_of_triangle_two_hubs` forbids a second; the other two
are non-hubs, hence of degree exactly `2` (2EC gives `≥ 2`). (iii)
`isKDof_zero_of_triangle`. (iv) `rigidContract G H r =
(G.deleteEdges E(H)).map (collapseTo r V(H))`: the deletion removes exactly the
three `Δ`-edges, `collapseTo z {x,y,z}` fixes every surviving vertex, and `x, y`
have no edges outside `Δ`, so vertex set and link relation are those of the
induced subgraph on `V(G) ∖ {x, y}`; simplicity is inherited. (v) Take
`V' = {x, y, z}`, nonempty and proper by (i). `TwoEdgeConnected`'s own definition
(`Deficiency.lean:1166`) demands `2 ≤ |cutEdges V'|`, and `cutEdges V'` is exactly
`z`'s edges to the outside, of which there are `deg z − 2`. Hence `deg z ≥ 4`, and
`|V(G)| ≥ 5`. ∎

*(At `deg z = 3` the single outside edge is a **bridge** — this is where 2EC does
the work, and it is why the two cases below are the only ones.)*

### Step TF3 — the case `deg z ≥ 5`: the restriction lemma alone

> **(TF-3)** If `deg z ≥ 5` then `G.induce (V(G) ∖ {x, y})` is feasible.

*Proof.* Apply (TF-1)(a) with `H := G.induce (V(G) ∖ {x, y}) ≤ G`. Only vertices
adjacent to `x` or `y` change degree, and `N(x) = {y, z}`, `N(y) = {x, z}`, so `z`
is the only one: `H.degree z = deg z − 2 ≥ 3`, i.e. `z` stays a hub. Every other
`G`-hub of `H` keeps its `G`-degree. The demotion hypothesis is therefore
discharged with no residual at all. ∎

### Step TF4 — the case `deg z = 4`: delete ONE vertex, then steer

Here `H` demotes `z` to degree `2` — precisely the sharp case (TF-1)(a) excludes.
The move is to **split the deletion in two** so that the landed steering lemma
applies to the second half.

> **(TF-4)** If `deg z = 4`, with `N(z) = {x, y, w₁, w₂}`, then
> `G.induce (V(G) ∖ {x, y})` is feasible.

*Proof.* **Step A.** Put `H₁ := G.induce (V(G) ∖ {x})`. Degrees move only at `y`
(`2 → 1`) and `z` (`4 → 3`). `y` is not a `G`-hub, so (TF-1)(a) asks nothing of
it; `z` is still a hub at degree `3`. So `PencilNondegFeasible K H₁`.
**Step B.** Apply (TF-1)(b) to `H₁` with `u_c := z`, `v_c := y`,
`V₁ := V(G) ∖ {x, y}`, and `w₁, w₂` as named. Its five configuration hypotheses
all hold: `H₁.Simple` (induced); `H₁.degree z = 3`; `V(H₁) = V₁ ∪ {y}`;
`(H₁.cutEdges V₁).ncard = 1`, since `y`'s only `H₁`-neighbour is `z` (`x` is
gone); and `w₁ ≠ w₂` by `G.Simple` (`z` has four distinct neighbours). Hence
`PencilNondegFeasible K (H₁.induce V₁) = PencilNondegFeasible K (G.induce V₁)`
(`induce_induce_of_subset`). ∎

**Why the split is not a trick.** (TF-1)(b) is *exactly* the lemma for one hub
demoting from degree `3` to degree `2` across a single pendant edge, and deleting
`x` first is what turns the pendant triangle into that shape. The landed lemma's
`[Infinite K]` rides in free: the successor
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Escape.lean:555`)
already carries `[Infinite K] [Finite α] [Finite β]`, so the residual habitat has
them.

### Step TF5 — **(T) is a THEOREM**, and what falls out

> **(TF-5)** **§(SAFE-RES) (T): a feasible residual `G` is triangle-free.**

*Proof.* Suppose not, and take `Δ = {x, y, z}` as in (TF-2). Then `(Δ, z)` is a
proper rigid subgraph with `z ∈ V(Δ)`, `G.rigidContract Δ z` is simple (TF-2)(iv),
and it is feasible by (TF-3) at `deg z ≥ 5` and by (TF-4) at `deg z = 4` — the only
two cases, by (TF-2)(v). That is a **good contraction**, contradicting the
residual's own no-good-contraction clause. ∎

Consequences, in the order they bite:

- **(SAFE-RES′) loses a gap.** *Step 3*'s three obligations become **(E)**
  (reduced to (E-loc)) and **(V)**; route 3's cost list drops from four items to
  **three** — (E-loc), (V), **(K-res)** — of which only (K-res) is a user call.
- **(C8) collapses to case (A), unconditionally.** *Step 1* recorded *"at a
  triangle-free residual, (A) holds at every maximal cluster"*; by (TF-5) that
  proviso is vacuous, so **every** maximal cluster of **every** residual has `v*`
  a hub with `≥ 3` hub neighbours. The recorded `--structure` figure "case (B)
  0/59" now has a proof rather than an explanation.
- **The two-pendant-triangle question is dissolved, not answered.** *Step 4*
  reduced (T)'s failure to a residual carrying `≥ 2` pendant triangles, and that
  structure was the natural next handle. (TF-5) empties it: no residual carries
  **one**. In particular the bowtie dies at every `|V|`, not only at `|V| = 5`.
- **(V) is unchanged and its dependence on (T) is now discharged, not carried.**
  *Step 3*'s residue *"`j = 2` with `u = u'` (a pendant triangle)"* is killed by a
  theorem; the two `C₄`-carrying residues (`j = 3` with `u = u'`; `j = 2` with
  `u ~ u'`) are untouched and remain (V)'s whole content. Nothing about (V) had to
  be re-proved, and **no obligation was relocated** — the question *"if (T) is
  carried rather than proved, which of (V)'s residues re-opens"* is moot.

### Step TF6 — verification, the Lean obligations, and a by-product certificate

**Compiler-checked spike** (scratch, deleted; the Lean hold forbids landing
`.lean`). The two-case chain of *Steps TF3/TF4* was elaborated against the landed
signatures: the `deg z ≥ 5` branch is **sorry-free** modulo its degree hypothesis,
and the `deg z = 4` branch composes both landed transfers and rewrites through
`induce_induce_of_subset` to the stated conclusion, leaving only the mechanical
residues below. Four Lean obligations remain for the eventual W4 build, **all pure
degree/cut bookkeeping, no geometry**:

- **(O1)** `G.PencilHub v → 3 ≤ (G.induce (V(G) ∖ {x})).degree v` for `v ≠ x`.
- **(O2)** `((G.induce (V(G) ∖ {x})).cutEdges (V(G) ∖ {x, y})).ncard ≤ 1`.
- **(O3)** `(G.induce (V(G) ∖ {x})).degree z = 3`.
- **(O4)** `G.rigidContract (G.induce {x,y,z}) z = G.induce (V(G) ∖ {x, y})`
  (with `isKDof_zero_of_triangle`'s `E(H) = {exy, eyz, exz}` side condition).

**A by-product, recorded because it is reusable and it is new.**

> **(TF-6) One-plane feasibility criterion.** Let `G` be simple with **every
> closed hub-neighbourhood of size `≤ 1`** — equivalently, **the hubs are pairwise
> at distance `≥ 3`** — over a field with `|K| ≥ |V(G)|` (so over any infinite
> field). Then `PencilNondegFeasible K G`, **triangles allowed**.

*Proof.* Fix `n₀ ≠ 0`, set `normal v := n₀` for every body, and place all points on
a moment curve `t ↦ (1, t, t²)` inside the single panel `τ = n₀^⊥` (3-dimensional,
so any three distinct such points are independent by Vandermonde). Give each link
`uv` the support extensor `extensor ![point u, point v]` and every other label a
fixed nonzero extensor of `τ`. Conjuncts 1–2 of `IsNondegPencilRealization` and
`HasCoplanarPanelRealization` are immediate (`span{p_u,p_v} ⊆ τ`); conjunct 4 at a
non-hub is the three-distinct-points-on-a-conic fact; and conjunct 3 is where the
hypothesis is spent — with all normals equal, `LinearIndepOn K normal S` holds
**iff** `|S| ≤ 1`. ∎ This is not implied by L6b (it admits triangles) and does not
imply it (L6b admits adjacent hubs); it is consistent with both landed necessary
conditions by construction, since adjacent hubs are exactly what it forbids. It is
**not used by (TF-5)** and is **not landed**.

**Driver** — `notes/scripts/w4/wtri.py` (tracked; three modes). It deliberately
does **not** hunt for a triangle-carrying residual, because that hunt is
impossible in principle (below).

- **`--validate`** — on **32 466** generated instances / **62 041** triangles:
  pendancy **62 041/62 041**, hub degree `≥ 4` **62 041/62 041**, and the (O4)
  identity `G/Δ = G − x − y` **62 041/62 041**. The one-plane criterion fires on
  **5 549** instances and is consistent with `hcard` *and* no-two-hub-triangle at
  **5 549/5 549**.
- **`--audit`** — the same pool, restricted to the **blind-spot family**: simple,
  2EC, **triangle-carrying**, passing every landed *necessary* test, hence
  undecidable either way by a landed criterion. Contraction simple
  **62 041/62 041**; the `deg z = 4` branch's landed-steering configuration holds
  at **52 466/52 466** and the `deg z ≥ 5` branch's demotion condition at
  **9 575/9 575**. **0** failures; any one would have refuted (TF-5).
- **`--regress`** — the falsification test the new certificate demanded: does
  (TF-6) dissolve anything recorded? Re-deriving `saferes.py --prime`'s pool
  reproduces **255** residual inhabitants exactly; **0** are triangle-carrying (as
  (TF-5) requires), **0** are dissolved by the new certificate, and both named
  witnesses survive — `W19`'s and `S29`'s unique proper rigid subgraph contracts
  to a graph refuted by the landed **necessary** `hcard`, which (TF-6) can never
  override.

**Cap and denominator disclosure — and it is stronger than a cap.** Every figure
above is over a *generated* pool, and the `--audit` denominator (62 041 pendant
triangles) counts configurations, not residuals. But the binding disclosure is not
a cap at all: **no sweep at any size can exhibit a triangle-carrying residual**,
because the sweep's feasibility certificate is L6b, which *requires* triangle-
freeness — and, per *Step 4*'s corrected consequence, the *contraction*'s
infeasibility is equally uncertifiable. The recorded **255/255** for §(SAFE-RES)
(T) was therefore never evidence, in either direction; it is the arc's clearest
example of a figure whose denominator is the wrong one. What settles (T) is
*Steps TF2–TF5*.

Reproduce: `python3 notes/scripts/w4/wtri.py --validate | --audit | --regress`.

### Verification

`notes/scripts/w4/saferes.py` (tracked; exact integer arithmetic), on top of
`nogood_subdiv.py`'s machinery.

- **Third oracle.** `treepack_deficiency` packs 6 edge-disjoint spanning
  forests in `5H` by matroid-union augmenting paths (Nash-Williams/Tutte). It
  is polynomial, so — unlike `kbare_common.exact_deficiency`, a `2^|V|`
  partition enumeration — it runs at `|V| = 29`. `--validate`: all three
  oracles agree on 250 random graphs (0 mismatches), on `C_k` (rigid iff
  `k ≤ 6`), on the Ear-Lemma threshold `j = 5/6`, and on sparse subdivisions up
  to `|V| ≈ 30`.
- **`--witness`** re-derives `S29`, evaluates all 1718 branch-subset candidates
  on both the pebble game and the tree packing (0 disagreements, unique rigid
  set = the core), and excludes co-1 **vertex by vertex** — all 29 `G − v` are
  non-rigid on both oracles (`min def(G − v) = 2`).
- **`--search`**: a 1989-instance structured short-branch sweep (core + poles +
  hub ring) yields 39 short-branch residuals and puts the minimum at
  `|V| = 29`. Two random sweeps over min-degree-3 bases with the branch cap
  *verified on the built graph* (not merely intended): 584 instances at
  `κ ≤ 2` and 343 at `κ ≤ 1` produce **0** residuals — at `κ ≤ 1` every
  instance dies as `not-feasible` (317) or `co-1` (26), exactly the two
  outcomes the (E-κ) count predicts. Random subdivisions of dense bases are a
  poor generator for this habitat; the structured family is what reaches it.
- **`--prime`**: **255** residual inhabitants across both scripts' families —
  216 have a deep split vertex (so **39 refute (SAFE-RES)**), and 255/255 have
  two adjacent degree-2 vertices, satisfy (E), are triangle-free, and carry a
  split-usable vertex. (Figures re-run 2026-08-02 by the widened-kernel recon;
  the "281 / 65" first recorded here was a transcription error — the script is
  unchanged and every other figure in this section reproduces exactly.)
- **`--structure`**: coverage for this section's own steps. (E-κ): 338
  ultra-short instances (`κ ≤ 1`), **0** violations of `f(V(G)) ≥ 5`. On 59
  residual inhabitants: **(C7) 59/59**, **(C8) case (A) 59/59** (case (B) 0/59 —
  since *Step TF5* this has a proof, not merely the certified-sweep explanation
  *Step 4* originally gave it), split-usable vertex 59/59. The (V)
  branch characterization was checked against the direct scan with no
  over-generous branch on any instance in the pool.

Reproduce: `python3 notes/scripts/w4/saferes.py --validate | --witness |
--search | --prime | --structure`. The (T) theorem's own driver is
`notes/scripts/w4/wtri.py` — see *Step TF6*, whose `--regress` mode re-derives
this section's `--prime` pool independently and reproduces its **255** exactly.

## §widened kernels (routes 1/3) — **priced; no counterexample**

**Verdict: true-modulo-named-gaps.** W4 routes 1/3 send *residual* graphs to
the split arm, whose carried kernels take
`hnoRigid : ∀ H, ¬ H.IsProperRigidSubgraph G 3` as an antecedent, so a kernel
must widen. Three findings price that:

1. **It is ONE kernel, not two.** `hbareSplit` is unreachable at a residual
   (Step 0), so its habitat and its whole (K-bare) analysis are untouched.
   The route-1 text's "widens two already-open research kernels" was wrong.
2. **The widened kernel (K-res) is not new mathematics — it is `hK`'s own
   conclusion on a bigger habitat** (Step 4). `hK`'s conclusion mentions only
   `G`; both the pinned and the widened obligation say "this `G` attains the
   pencil rank target in chart form". What the widening costs is the *proof
   route*: the (K) stratification's cheap branch dies (Step 2).
3. **The escape still works at every residual probed** — exact-ℚ, 8/8 escaping
   seeds at `W19` and `S29`, and (as first recorded) 94/96 over a stratified
   pool sample against 11/12 for the *pinned* kernel's own tight control
   (Step 5). **Corrected 2026-08-02 by the (K-tight) re-pin: the non-escaping
   seeds in both figures were placement-sampler artifacts; with the sampler
   fixed, every target-rank seed probed escapes** (`notes/Pencil-informal.md`
   §(K-tight) Step 3). A
   failure here would have killed routes 1/3 outright; none exists.

Net: routes 1/3 cost **one extra carried kernel of the same shape and the same
difficulty class as `hK`**, plus §(SAFE-RES)'s (T) and (V), plus (E) — which
Step 3 reduces to a cheap Lean leaf and one new combinatorial gap (E-loc).

**What would change this.** A residual split at which *no* target-rank `G′`
seed escapes (that would refute (K-res) and kill routes 1/3); a reading error
in `pencilPair_of_splitOff_of_habitat`'s `by_cases hfeas` branching (read from
the body, `Escape.lean:396–428`); or a residual with no degree-`2` vertex
whose `v`-avoiding edge fiber is count-independent (that would undo Step 3).

### Step 0 — which kernels routes 1/3 actually touch

Read from the landed producer `pencilPair_of_splitOff_of_habitat`
(`Molecule/Pencil/Escape.lean:334`) and the residual's own antecedent bundle
(`hnoGood'`, `notes/Phase39-design.md` §"W4-L4 identification recon" Verdict 4).

- The producer branches on `by_cases hfeas : PencilNondegFeasible K G`
  (`:396`). The **feasible** branch chains L7a → `hK` → L7b; the **infeasible**
  branch (`:424–428`) is the *only* consumer of `hbareSplit`.
- A residual is **feasible by hypothesis** — `PencilNondegFeasible K G` is one
  of `hnoGood'`'s antecedents — and branch 4 of the L3′ skeleton sits inside
  the `Simple ∧ Feasible` case, whose only deliverable is
  `HasGenericPencilRealization K 3 G` (the bare half is
  `hasPencilRealization_of_generic` of it).

So at a residual the infeasible branch is discharged by `absurd`, and
**`hbareSplit` is never instantiated**. Its `hnoRigid` and its corank
stratification stand exactly as pinned — the latter now **complete**
(`index ∈ {1, 2}`, `corank(G′) ≤ 3`, `notes/Pencil-informal.md`
§(K-bare-ext) (BE-6)) — while **(K-bare-ext) itself is REFUTED as stated**
(ibid., (BE-5), 2026-08-20; a *route* finding, `hbareSplit` untouched). (For the record,
what *would* break if it were reached: the (K-bare) count dichotomy
"count-dependent ⟹ spanning circuit ⟹ `def(G) = 0`" needs vertex-properness to
force the circuit to span. At a residual the core supplies a non-spanning
circuit, so `def(G) > 0` **and** count-dependent becomes possible — 57 of the
255 pool residuals are exactly that, a combination the pinned dichotomy
excludes.)

The `hnoRigid` consumption points of the surviving chain are §(SAFE-RES)
*Step 0*'s (S0)–(S5) plus **one that section missed**: the wrapper's `hfresh`
discharge `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two`
(`Escape.lean:516`) calls `edgeBound_of_noRigid_of_degree_two` and nothing
else, so it collapses into **(E)** exactly like (S1)/(S2). Also free at a
residual: `5 ≤ |V(G)|`, since a simple rigid subgraph needs `≥ 3` vertices
(`2` vertices give one edge, `def = 1`) and no-co-1 adds two more.

### Step 1 — the trace: where the settled (K) analysis consumes `noRigid`

Four points in `notes/Phase39-design.md` §"(K) route-1 gate" + §"(K)
non-constancy recon", each read from the design text against the landed lemma
it cites:

| # | consumption | producer | fate at a residual |
|---|---|---|---|
| K1 | `index(G) ≤ 4`, so the corank stratification is finite | `edgeBound_of_noRigid_of_degree_two` (`ReducibleVertex.lean:1270`) | = gap **(E)**; **survives modulo (E-loc)**, Step 3 |
| K2 | `s₀ = 0` (no pure shared-row stresses), hence `dim R_a = corank(G′)` | `circuit_induces_isRigidSubgraph` + vertex-properness | **BREAKS**, Step 2 — this is the load-bearing one |
| K3 | a lever-critical habitat has no cut vertex (blocks argument) | same | **proof breaks; conclusion holds** 255/255 |
| K4 | route-1 gate finding 1's *explanation* that the stress is globally supported ("no proper subgraph to localise onto") | prose | verdict unaffected — that gate **refuted** locality; a residual makes the picture more mixed, not more local. Route 1 of the (K) options stays NO-GO |

K2's exact form: a count-matroid circuit inside `G − v` induces a rigid
subgraph on `V(C) ⊆ V(G) ∖ {v}`, vertex-proper, excluded by `hnoRigid`. So the
step really needs only

> **(I)** `E(G − v)` is independent in the `(6,6)` count matroid
> (equivalently `f(W) ≤ 0` for every `W ⊆ V(G) ∖ {v}`),

which is strictly weaker than `hnoRigid` — a rigid subgraph is
count-*dependent* only when `f(V(H)) > 0`, so a residual all of whose rigid
subgraphs are count-tight can still satisfy (I). 160 of the 255 pool residuals
are of that kind. `W19` and `S29` are **not**: their `C₄` cores have
`f = 5·4 − 6·3 = 2 > 0`.

### Step 2 — what breaks: the corank arithmetic at a residual

Write `index(H) = 5|E(H)| − 6(|V(H)| − 1)`. At a target-rank seed
`corank(H) = 5|E(H)| − rank = index(H) + def(H)`. For a split at a degree-`2`
`v` — so `|E(G−v)| = |E| − 2`, `|E(G′)| = |E| − 1`, and both lose one vertex:

```
s₀        = corank(G − v) = index(G) − 4 + def(G − v)
corank(G′) = index(G) + 1 + def(G′)
dim R_a   = corank(G′) − s₀ = 5 + def(G′) − def(G − v)          (†)
```

(†) is **independent of `index(G)`** — checked on all 4192 (residual,
split-usable `v`) pairs of the pool, 0 mismatches, and matched by the
*geometric* `s₀`/`corank` read off the exact-ℚ seeds at `W19`/`S29`.

The (K) recon's cheap branch was: `index(G) ≥ 1` ⟹ `s₀ = 0` ⟹
`dim R_a = corank(G′) = index(G) + 1 ≥ 2` ⟹ **escape automatic**. At a
residual the proper rigid subgraph's own dependency reappears as `s₀` and
**cancels the index gain exactly**. Concretely at `W19` and `S29`
(`index = 2`, `def = 0`): every split-usable `v` has `def(G−v) = 4`,
`def(G′) = 0`, `s₀ = 2`, `corank(G′) = 3`, hence `dim R_a = 1` — the
`(K-tight)`-shaped hard regime, at an index-2 graph.

Pool-wide, over the 102 **rigid** residuals (`def(G) = 0`), the
`(index, dim R_a)` pairs are `(0,1): 1128`, `(1,1): 450`, `(1,2): 40`,
`(2,1): 120` — i.e. `dim R_a = 1` on 1698 of 1738 pairs, and there is no
`index ≥ 1 ⟹ dim R_a ≥ 2` implication left. Deficient residuals (`def > 0`)
mostly give `dim R_a = 0`; those are the `k > 0` habitats the design doc
already routes to KT Case II rather than Case III.

**So: the widened kernel's habitat lands wholesale in (K)'s hard stratum.**
That is the honest cost of routes 1/3 to the (K) *analysis* — not to (K)'s
truth (Step 5) and not to its statement (Step 4).

K3 fares better: the block argument dies, but 255/255 pool residuals (and
`W19`, `S29`) are 2-connected anyway, so the property the lever argument wanted
is still there — it just needs a different proof, presumably from the (C7)/(C8)
structure rather than from circuits.

### Step 3 — (E) is reduced: a cheap leaf plus (E-loc)

`edgeBound_of_noRigid_of_degree_two` (`ReducibleVertex.lean:1270`) uses its
`hnp` at **exactly one point** (verified line-by-line in the body, not from the
docstring): to prove `hindep : (G.matroidMG n).Indep E'`, where `E'` is the
`5`-fold fiber of the edges avoiding `v`. Everything after that is pure
counting: sparsity of `E'` on a vertex set avoiding `v` gives
`5(|E| − 2) + 6 ≤ 6(|V| − 1)`, i.e. `f(V(G)) ≤ 4`. Two consequences.

- A `noRigid`-free sibling taking `(I)` (or "no proper rigid subgraph avoids
  `v`") in place of `hnoRigid` is a **verbatim-prefix extraction**, the same
  L7c-1-grade move as `simple_of_loopless_of_noRigid`. Cheap Lean leaf.
- The conclusion `f(V(G)) ≤ 4` is a statement about `G`, **not about `v`**. So
  (E) follows as soon as *some* degree-`2` vertex satisfies (I) — it need not
  be the vertex the split uses. That is the new gap:

> **(E-loc)** *Every residual `G` has a degree-`2` vertex `v₀` with `E(G − v₀)`
> independent in the `(6,6)` count matroid.*

**Numerics: 255/255** (`widened.py --ebound`). The witness is typically *not*
split-usable: at `W19` it is `c1` or `c3`, at `S29` it is `m1` or `m2` — the
**core's own** degree-`2` vertices, and the split-usable set is disjoint from
them in both cases. (210 of the 255 do have a split-usable witness, which then
buys `s₀ = 0` as well; `W19`/`S29` are among the 45 that do not.)

Structure that should make (E-loc) tractable. `f` is **supermodular** (`|E(·)|`
is supermodular; `−6(|W| − 1)` is modular), so
`f(W₁ ∪ W₂) ≥ f(W₁) + f(W₂) − f(W₁ ∩ W₂)`. When `W₁ ∩ W₂` is a single vertex
`f(W₁ ∩ W₂) = 0`, and when it is count-independent `f(W₁ ∩ W₂) ≤ 0`; either
way two count-dependent sets meeting like that **merge** into a
count-dependent union. So the obstruction to (E-loc) is one of exactly two
shapes: two count-dependent vertex sets meeting in an independent set (in
particular two *disjoint* proper rigid subgraphs with `f > 0`), or a single
dependent "brick" all of whose vertices have `G`-degree `≥ 3`. Neither occurs
anywhere in the pool. Discharging (E-loc) fixes gap **(E)** of §(SAFE-RES)
*Step 3*, and with it the `hfresh` discharge of Step 0.

### Step 4 — the minimal honest widened statements

The kernel routes 1/3 need is `hK` with `hnoRigid` deleted. Since `hK` is only
ever invoked inside `by_cases hfeas`, adding `PencilNondegFeasible K G` is free
at the existing call site and *weakens* the obligation, so the minimal honest
form is:

> **(K-res)** For every `G : Graph α β` with `G.Simple`, `5 ≤ |V(G)|`,
> `G.TwoEdgeConnected`, **`PencilNondegFeasible K G`**, a vertex `v` of degree
> `2` with `eₐ ≠ e_b`, `G.IsLink eₐ v a`, `G.IsLink e_b v b`,
> `¬ G.PencilHub a ∨ ¬ G.PencilHub b`, and `e₀ ∉ E(G)`: if
> `HasGenericPencilRealization K 3 (G.splitOff v a b e₀)`, then there are a
> correct hub selector `hubSel`, a seed `q`, and an edge-indexed
> `s` of size `screwDim 2 * (|V(G)| − 1) − G.deficiency 3` with
> `LinearIndependent K (fun i : s => pencilRow hubSel G.endsOf q i)`.

— i.e. `hK`'s statement verbatim, `hnoRigid` ↦ `PencilNondegFeasible K G`.
`f(V(G)) ≤ 4` and triangle-freeness may be added as further antecedents at no
cost, since the route must establish both anyway ((E)/(T) of §(SAFE-RES)); they
are *not* needed for the conclusion to be stated, so the minimal form omits
them.

**Two packagings, same mathematics.**

- *(a) widen `hK` in place.* One kernel; but it edits the landed
  `pencilPair_of_splitOff_of_habitat` and every caller.
- *(b) carry `(K-res)` as a second hypothesis alongside the byte-identical
  `hK`.* No landed code moves; branch 4 gets its own producer. **Recommended.**

There is no double work either way: `hK`'s habitat (`hnoRigid`) and (K-res)'s
(`∃` proper rigid, via the residual) are **disjoint**, so (a) is exactly
(b) + `hK` merged. And because `hK`'s *conclusion* mentions only `G`, both
obligations assert the same thing — "this `G` attains the pencil rank target in
chart form" — on complementary habitats. The widening adds **no new kind of
mathematics**; it adds a habitat on which the identified proof route (the
escape) is in its hard regime.

Besides the kernel, branch 4 needs a **residual-habitat sibling of L7a**
(`hasGenericPencilRealization_of_splitOff_of_safe`, `Escape.lean:95`): a leaf,
not a kernel, whose three `hnoRigid` calls are exactly (S3)/(S4)/(S5), all
supplied by (T) + (V) of §(SAFE-RES′). That was already priced there.

### Step 5 — numerics: does the widened kernel hold?

Exact-ℚ, `notes/scripts/w4/widened.py`. The comparable statistic is the
**escape rate**: over pencil-generic seeds of `G′` that attain `target(G′)`,
the fraction from which *some* admissible re-insertion of `v` (the model's only
freedom is `pt(v)`, confined to `Π(b)` when `b` is a hub) reaches `target(G)`.
Kernel (K) needs one escaping seed, so a seed-level failure is not a
counterexample; a *split* with no escaping seed would be.

| object | habitat | `s₀` | `corank(G′)` | `dim R_a` | escaping seeds |
|---|---|---|---|---|---|
| θ(4,4,3) split (N9a control) | `noRigid`, index 1 | 0 | 2 | 2 | **8/8** |
| dbl-subdivided `K4` (tight control) | `noRigid`, index 0 | 0 | 1 | 1 | **11/12**† |
| `W19`, 3 split shapes | residual, index 2 | 2 | 3 | 1 | **8/8** each |
| `S29` | residual, index 2 | 2 | 3 | 1 | **8/8** |
| stratified pool sample, 8 strata × 3 pairs | residual | — | — | 0/1/2 | **94/96**† |

† As measured by `widened.py`'s sampler; **all three non-escaping seeds are
sampler artifacts** (degenerate in-plane placements freezing `hinge(vb)`) and
escape with the corrected sampler — `notes/Pencil-informal.md` §(K-tight)
*Step 3* (`notes/scripts/w4/repin.py`).

- The pencil rank target itself is attained at `W19` (108/108) and `S29`
  (168/168) at freely-sampled pencil-generic seeds — so **the rank statement
  (K-res)'s conclusion packages is true at both**, independently of the route
  (the remaining packaging — the hub selector and the `pencilRow` indexing —
  is combinatorial and comes from `hcard`).
- The only non-escaping seeds in the whole sweep sit in the
  `(def(G) = 0, dim R_a = 1)` stratum, at 10/12 — the *same* regime and the
  *same* rate as the pinned kernel's own tight control (11/12). **No split had
  zero escaping seeds.** (Since sharpened: those non-escapes were sampler
  artifacts, see †; the corrected stratum figure is 24/24.)
- `dim R_a ≥ 2` was automatic-escape everywhere it occurred (12/12 at
  `def = 0`), so the (K) recon's *criterion* survives; it is only its
  derivation of `s₀ = 0` that dies.
- On-line placements (`pt(v) ∈ line(pt a, pt b)`) fail 16/16 at `W19` and
  14/14 at `S29`, reproducing (K-bare)'s C3 gloss. **That gloss is corrected
  (2026-08-20, probe KBARE-FALSIFY):** on-line failure is *structural*
  (`C(va) ∥ C(vb)` there), but the failure set is **larger** than the line —
  see `notes/Pencil-informal.md` §(K-bare-ext) *Step BE5*, where an off-line
  failure is constructed at DZ itself. The 16/16 and 14/14 figures are
  unaffected (they are on-line failures, the half that is structural).

**The seed-442 caveat is RESOLVED (2026-08-02).** The re-pin this step's
caveat asked for has been done — `notes/Pencil-informal.md` §(K-tight) — and
it dissolved the caveat in
both directions: (i) seed 442's observed uniform failure was a **sampler
artifact** (degenerate in-plane placements on a line through `pt(b)`,
freezing `hinge(vb)`; the seed escapes on both routes with a correct
sampler), and (ii) the "observed predictor M2 = `R_a ⊄ pencil(b)^⊥`" scored
against those artifact observations and is **refuted as the criterion** —
two control seeds have `r ⊥ pencil(b)` yet escape. The carrier-correct
criterion (proven and validated, `notes/Pencil-informal.md` §(K-tight)
Steps 2–3) is per route the
**full panel span** (`r ̸⊥ Λ²Π̂(b)` for the `pt(v)`-sweep; `r ̸⊥ Λ²Π̂(c)`
for the iso-relabeled `pt(a)`-sweep), with combined failure ⟺ `★r ∥ C(M)`,
the meet line of the two end panels.

### Verification

`notes/scripts/w4/widened.py` (tracked; exact-ℚ). New geometry:
`place_pencil_general`, a pencil-generic placement that handles **hub-hub
adjacency** — `escape/pencil_escape.py`'s sampler gives every hub an
independent plane, which is only valid for the double-subdivision families
(no two hubs adjacent); every residual has hub edges, so hub normals must be
solved against their hub neighbours and shared non-hubs placed on plane
intersections. `--validate` reproduces the N9a record exactly and checks (†)
on all 4192 pool pairs.

Reproduce: `python3 notes/scripts/w4/widened.py --validate | --witness |
--pool | --sample | --ebound`.

### Confidence verdict per widened kernel

- **(K-res)** — **open, no counterexample; same difficulty class as `hK`.**
  Truth: supported by direct rank attainment at `W19`/`S29` and an escape
  rate that is **100% after the sampler correction**
  (`notes/Pencil-informal.md` §(K-tight) Step 3; first recorded as 94/96).
  Provability: strictly *harder to route* than the
  pinned `hK`, because the whole residual habitat sits in the `dim R_a = 1`
  stratum — but that stratum's escape criterion is now settled and identical
  across the pinned and residual habitats (`notes/Pencil-informal.md`
  §(K-tight) Steps 2/5), so the two
  kernels share one uniform gap ((K-move)/(K-pitch)). **Scope note
  (2026-08-28, direction RESGRID): that kinship is the *escape*-side one.**
  On the *grid* side the arc's reduced gap (GR-15) does **not** cover
  (K-res) — the (K-res) grid residual is **(RS-5)** (§(K-res),
  `notes/Pencil-informal-grid.md`): the §(K-grid) geometry transports
  verbatim and (RS-5) is proven per-shape at `W19`/`S29`/`NT21c3`, while
  the deficient fringe is excluded with a mechanism ((RS-6), θ(2,3,7)).
- **`hbareSplit`** — **unchanged.** Not on routes 1/3's path (Step 0); its
  adjudicated carry stands verbatim. **(K-bare-ext)**, its route-A discharge
  statement, is **REFUTED as stated** since 2026-08-20
  (`notes/Pencil-informal.md` §(K-bare-ext)); that does not reach this arm,
  precisely because Step 0 keeps the branch unreachable here.
