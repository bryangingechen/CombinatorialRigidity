# PENCIL — informal mathematics workbook

**Purpose.** Informal proofs under development for the kernels and branch
arms Phase 39 (PENCIL) carries as hypotheses. This is the **staging ground
before blueprint transcription**: nothing here is formalization-committed, no
`\lean{...}` pin points at it, and a section may be rewritten wholesale when
the argument changes. Once a section reaches *proven-informally* and the
coordinator commissions its build, its content moves to
`blueprint/src/chapter/pencil.tex` (with a `notes/BlueprintExposition.md`
entry when it earns a detailed exposition) and the section here shrinks to a
pointer.

**Discipline.**

- Each section reads as the **current state of the argument**, revised in
  place. Git is the changelog; do not keep superseded reasoning inline (the
  `notes/CLAUDE.md` rule for phase notes applies here too).
- Each section carries an explicit **confidence verdict**, one of:
  *proven-informally* / *true-modulo-named-gap* / *open* / *refuted*, plus a
  **"what would change this"** line naming the observation that would move
  the verdict.
- Landed Lean facts are cited by declaration name; claims that are *not*
  landed are flagged as such at the point of use. `PencilNondegFeasible` has
  no combinatorial characterization — whenever an argument needs a
  feasibility fact, say whether it is landed-**sufficient**
  (`hcard ∧ triangle-free`, L6b; the spanning-`C₃` witness, L7c-3),
  landed-**necessary** (`hcard`; no-2-hub-triangle), or **middle zone**
  (undecided by landed lemmas).

**Recon verdict history lives elsewhere.** The dated recon record — what was
asked, what method was used, what was refuted — is
`notes/Phase39-design.md`; the one-line decisions are `notes/Phase39.md`
*Decisions made*. This file carries only the mathematics, in its current
state.

## Shared dictionary (used by every section below)

Body-hinge at `d = 3`: `D = bodyBarDim 3 = 6`, hinge multiplicity `5`.
For a graph `H`,

```
def(H) = max over partitions P of V(H) of [ 6(|P| − 1) − 5·d(P) ]
```

(`Molecular/Deficiency.lean`), `d(P)` = number of edges crossing `P`; `H` is
**rigid** (`H.IsKDof 3 0`) iff `def(H) = 0` iff `5H` packs 6 edge-disjoint
spanning trees (Tay; `thm:body-hinge-tay`). Writing `f(W) = 5|E(W)| −
6(|W| − 1)` for a vertex set `W`, one has `def(H) = 6(|V|−1) − 5|E| +
max { Σ_parts f(part) }`, so `def(H) = 0` forces `f(V(H)) ≥ 0`.

Consequences used throughout (all elementary, all numerically re-checked in
`notes/scripts/w4/nogood_subdiv.py --validate`):

- **(R1) min degree.** A rigid `H` with `2 ≤ |V(H)|` has `deg_H(v) ≥ 2`
  everywhere and is connected (`{v}`-vs-rest gives `6 − 5·deg ≥ 1 > 0`;
  components give `6(p−1) > 0`). Landed as
  `two_le_degree_of_isKDof_zero` (`Deficiency.lean:1306`).
- **(R2) size bound.** A rigid `H` with cycle rank `c = |E| − |V| + 1`
  satisfies `|V(H)| ≤ 5c + 1`, and has at most `2c − 2` vertices of
  `H`-degree `≥ 3`.
- **(R3) short cycles.** `def(C_k) = max(0, k − 6)`: `C_k` is rigid iff
  `k ≤ 6` (the classical 6R-loop count). `C₃` and `C₄` are landed
  (`isKDof_zero_of_triangle`, `c4_isProperRigidSubgraph`).
- **(R4) `hcard` restated.** `PencilNondegFeasible K G` gives `∀ v ∈ V(G),
  (G.closedHubNbhd v).ncard ≤ 3` (`ncard_closedHubNbhd_le_three_of_
  isNondegPencilRealization`). At a **non**-hub the bound is automatic
  (`closedHubNbhd v ⊆ N(v)`, of size `≤ 2`), so `hcard` says exactly:
  **every hub has at most two hub neighbours** — the subgraph induced on
  `{v : deg v ≥ 3}` has maximum degree `≤ 2`. Hence a `2`-edge-connected
  feasible `G` is a **subdivision** of a multigraph `G°` on its hubs (or a
  bare cycle), and hub-hub adjacency is confined to paths/cycles.
- **(R5) feasible triangles are pendant.** `not_pencilNondegFeasible_of_
  triangle_two_hubs` says a triangle of a feasible `G` has `≤ 1` hub, so
  two of its vertices have degree exactly `2`: every triangle is either the
  spanning `C₃` or a two-vertex ear hanging at one vertex.

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
to protect maximality.

```
core       C₄ :  c0 – c1 – c2 – c3 – c0
poles      z0, z1 attached to c0 ;  z2 attached to c2
paths      z0 –w0_0 w0_1 w0_2 w0_3– z1
           z1 –w1_0 w1_1 w1_2 w1_3– z2
           z2 –w2_0 w2_1 w2_2 w2_3– z0
```

`|V| = 19`, `|E| = 22`; degrees `c0 ↦ 4`, `c2 ↦ 3`, `z0,z1,z2 ↦ 3`, all
others `2`. Hubs: `{c0, c2, z0, z1, z2}`.

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
consumes; it is **open**, holds on 255/255 inhabitants swept, and reduces to two
named gaps: the residual's edge count **(E)** and its triangle-freeness **(T)**.
**(E) is since reduced further** — §"widened kernels (routes 1/3)" *Step 3*.

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
counterexample for **(E)** or **(T)**. A residual carrying a triangle would
settle (T) negatively — but *Step 4* shows such a graph is invisible to any
landed-lemma-certified search, so numerics cannot decide (T) in either
direction.

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
> In particular **at a triangle-free residual, (A) holds at every maximal
> cluster.**

(C7) + (C8)(A) + (C6) pin the shape: the core is at least a `C₄` with its two
hubs opposite, it carries `≥ 3` boundary hubs spread over `≥ 2` attachment
points, and those boundary hubs are pairwise at `G[T]`-distance `≥ 5`.

### Step 2 — the refutation: `S29`

```
core    C₄ :  A – m1 – B – m2 – A            (A deg 4, B deg 3)
poles   hub edges  A–z0,  A–z1,  B–z2
ring    z0 – y0 – z1 – y1 – z2 – y2 – z0,  every leg 2-subdivided
spokes  y0–p, y1–p, y2–p,                  every spoke 2-subdivided
```

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
- **(T)** `G` triangle-free — **open, with a landed-invisible failure mode**
  (Step 4). Numerics: 255/255, but that is *not* evidence: the search's own
  feasibility certificate for `G` is L6b, which requires triangle-freeness, so
  a triangle-carrying residual can never appear in a certified sweep.
- **(V)** the local choice — **elementary given (E) and (T).** (E) supplies a
  branch `β` with `j ≥ 2` interior vertices `x₁ … x_j` and hub ends `u, u'`.
  Then:
  - `j ≥ 4`, or `j = 3` with `u ≠ u'`: take `v = x₂`; `a = x₁`, `b = x₃` are
    degree `2`, non-adjacent, and share only `x₂`. ✓
  - `j = 2` with `u ≠ u'` and `u ≁ u'`: take `v = x₁`; `a = x₂` (degree 2),
    `b = u`, `N(u) ∩ N(x₂) = {x₁}`. ✓
  - the three residues — `j = 2` with `u = u'` (a pendant triangle, killed by
    (T)); `j = 3` with `u = u'`; `j = 2` with `u ~ u'` — are unusable at every
    vertex of `β`. Each of the last two exhibits a **chordless induced `C₄`**
    (`u, x₁, x₂, u'` resp. `u, x₁, x₂, x₃`), hence a proper rigid subgraph, so
    they are natural material for the contraction arm rather than the split
    arm; a full proof of (V) must show that not *every* `≥ 2`-interior branch
    of a residual is of those two shapes.

### Step 4 — why (T) is not reachable from the landed lemmas

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

Consequences: (i) `G` must carry `≥ 2` triangles, and two pendant triangles
already satisfy every landed test, so (T) is **not provable** from the landed
set; (ii) such a `G` is itself middle-zone (a 1-hub triangle is neither
landed-sufficient-feasible nor landed-necessary-infeasible), so it is
**invisible to a certified search** — (T) is a genuine research gap, not a
numerics gap. The smallest instance does die: the **bowtie** (two pendant
triangles at one degree-4 hub, `|V| = 5`) contracts either triangle to the
spanning `C₃`, landed-feasible by L7c-3 — a good contraction. Route 1/3 must
either carry (T) as a hypothesis, add triangle-freeness to branch 4's dispatch
condition (routing the triangle case elsewhere), or land a new
feasibility-*necessary* condition that kills pendant triangles.

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
  residual inhabitants: **(C7) 59/59**, **(C8) case (A) 59/59** (case (B) 0/59,
  as Step 4 predicts for a certified sweep), split-usable vertex 59/59. The (V)
  branch characterization was checked against the direct scan with no
  over-generous branch on any instance in the pool.

Reproduce: `python3 notes/scripts/w4/saferes.py --validate | --witness |
--search | --prime | --structure`.

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
   fixed, every target-rank seed probed escapes** (§(K-tight) Step 3). A
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
**`hbareSplit` is never instantiated**. Its `hnoRigid`, its corank
stratification, and (K-bare-ext) all stand exactly as pinned. (For the record,
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
escape with the corrected sampler — §(K-tight) *Step 3*
(`notes/scripts/w4/repin.py`).

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
  14/14 at `S29`, reproducing (K-bare)'s C3 "failure set is exactly the line".

**The seed-442 caveat is RESOLVED (2026-08-02).** The re-pin this step's
caveat asked for has been done — §(K-tight) — and it dissolved the caveat in
both directions: (i) seed 442's observed uniform failure was a **sampler
artifact** (degenerate in-plane placements on a line through `pt(b)`,
freezing `hinge(vb)`; the seed escapes on both routes with a correct
sampler), and (ii) the "observed predictor M2 = `R_a ⊄ pencil(b)^⊥`" scored
against those artifact observations and is **refuted as the criterion** —
two control seeds have `r ⊥ pencil(b)` yet escape. The carrier-correct
criterion (proven and validated, §(K-tight) Steps 2–3) is per route the
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
  rate that is **100% after the sampler correction** (§(K-tight) Step 3;
  first recorded as 94/96). Provability: strictly *harder to route* than the
  pinned `hK`, because the whole residual habitat sits in the `dim R_a = 1`
  stratum — but that stratum's escape criterion is now settled and identical
  across the pinned and residual habitats (§(K-tight) Steps 2/5), so the two
  kernels share one uniform gap ((K-move)/(K-pitch)).
- **`hbareSplit` / (K-bare-ext)** — **unchanged.** Not on routes 1/3's path
  (Step 0); its adjudicated carry stands verbatim.

## §(K-tight) — the carrier escape criterion (KT pp. 684–691 re-pin) and the uniform mechanism

The hard residue of kernel **(K)** after the corank stratification: tight
habitats (`5|E| = 6(|V| − 1)`), both chain ends hubs, 2-connected — plus,
since the W4 route-3(b) adjudication, the whole (K-res) residual habitat,
which sits in the same `dim R_a = 1` shape (§"widened kernels" *Step 2*).

**Verdict (two-part).** The **escape criterion** below is
**proven-informally** — exact linear algebra from KT's pp. 684–691 machinery
re-derived against the carrier, machine-validated per-placement and per-seed
at every probed habitat (`notes/scripts/w4/repin.py`). The **kernel** stays
**open**, narrowed to one uniform gap ((K-move)/(K-pitch), Step 5). A key
factual correction rides along: **no escape failure has ever actually been
observed in the phase's numerics** — the recorded failure figures (11/12 at
the tight control including seed 442; 94/96 pool-wide) were artifacts of a
degenerate placement sampler, not of the mathematics (Step 3).

**What would change this.** *For the criterion:* an error in the
model-to-Lean dictionary (the scripts' 5-rows-per-hinge Euclidean-perp
rigidity model vs `BodyHingeFramework.rigidityRows`) — the derivation is
pairing-agnostic, but the numerics live in the script convention. *For the
kernel:* a target-rank seed with genuine uniform failure (`r̃ ∥ C(M)` below)
would inhabit the bad locus and force the uniform mechanism to engage it; a
White–Whiteley-style evaluation of the pitch polynomial (Step 5(b)) would
close it.

### Step 0 — what KT pp. 684–691 actually prove (transcription)

KT Lemma 6.10, `k = 0` case (all pointers verified against the `.refs` copy
this pass): `v` of degree 2 with neighbours `a, b`; `a` of degree 2 with
neighbours `v, c`; `G′ = G^{ab}_v`, with a generic nonparallel realization
`(G′, q)` at rank `6(|V|−2)` (6.18). **Claim 6.11** (p. 684): some copy
`(ab)_{i*}` of the 5-fold `ab` fiber is redundant — sourced from Lemma
4.3(ii)'s base `B′` with `|B′ ∩ ãb| < 5` (this is where KT consumes
minimality) — giving a row dependency `λ` with `λ_{(ab)i*} = 1`
(6.24)–(6.25). Three candidate realizations of `G`:

- `p₁` (6.12): `hinge(vb) := q(ab)` **pinned**, `hinge(va) := L` swept over
  **all** lines in the panel `Π(a)`;
- `p₂` (6.19): symmetric — `hinge(va) := q(ab)` pinned, `hinge(vb) := L′`
  swept over `Π(b)`;
- `p₃` (6.31)–(6.33): via the isomorphism `ρ : G^{vc}_a ≅ G^{ab}_v` (`v, a`
  an adjacent degree-2 pair), `hinge(va) := q(ac)`, `hinge(vb) := q(ab)`
  pinned, `hinge(ac) := L″` swept over `Π(c)`.

Row/column operations (6.26)–(6.30), (6.35)–(6.41) reduce attainment to a
top-left `6×6` block `M₁/M₂/M₃` (6.42), whose second row is always
`r := Σ_j λ_{(ab)j} r_j(q(ab))` — for `M₃` via the identity **(6.44)**
`r = −Σ_j λ_{(ac)j} r_j(q(ac))`, the stress balance at the degree-2 body `a`
(KT glosses `r` as the force applied to `a`'s panel through the hinge,
p. 681). **Claim 6.12** (pp. 690–691): if all three fail for every choice of
`L, L′, L″`, then `r ⊥` the span (6.45) `= Λ²Π̂(a) + Λ²Π̂(b) + Λ²Π̂(c)`,
which is **6-dimensional** at a generic nonparallel seed (the four-point
Lemma-2.1 argument), forcing `r = 0` — contradiction.

### Step 1 — which KT freedoms survive the carrier pin

Carrier facts, from definition bodies: `HasPencilPanelRealization`
(`Molecule/Pencil/Statement.lean:88`) requires every link's extensor through
**both** endpoint points; `IsNondegPencilRealization` conjunct 2 makes
adjacent points projectively distinct, so **every hinge is pinned**:
`C(uv) ∝ pt(u) ∧ pt(v)`. Conjunct 4 forbids `pt(v) ∈ line(pt a, pt b)` at
the degree-2 body `v`. At a hub `h`, every neighbour's point lies in `Π̂(h)`
(the hinge is in `h`'s panel and through the neighbour's point).

| KT freedom | carrier fate |
|---|---|
| `p₁`/M₁: `hinge(va)` sweeps `Π(a)`, `hinge(vb) := q(ab)` | **DEAD**: `hinge(vb) = pt(v) ∧ pt(b) = q(ab)` forces `pt(v) ∈ line(a,b)` — the nondegeneracy-forbidden locus |
| `p₂`/M₂: `hinge(vb)` sweeps `Π(b)` | survives as **route A**: `pt(v)` sweeps `Π̂(b)` (`b` hub; all of `K⁴` if not) — with **both** new hinges moving, neither pinned |
| `p₃`/M₃: `hinge(ac)` sweeps `Π(c)` | survives as **route B**: `ρ` is carrier-valid (degrees preserved), `pt(v) := old pt(a)`, new `pt(a)` sweeps `Π̂(c)` |
| — | **NEW, not in KT**: the joint sweep `(pt v, pt a) ∈ Π̂(b) × Π̂(c)`, strictly larger than A ∪ B — un-analyzed; can only enlarge the escape |

So the carrier deletes M₁ outright and re-shapes M₂/M₃ from
one-hinge-swept-one-pinned constructions into point sweeps moving both new
hinges at once. Neither the §2 form `S = Λ²Π̂(a) + pencil(b) + pencil(c)`
nor the pencil-restricted M₂ is the right criterion; Step 2 derives what is.

### Step 2 — the boundary-load calculus on the carrier

Scope: `def(G) = def(G′) = 0` (the `k = 0` / Case-III world; `k > 0` routes
to KT Case II per the design doc), `deg_G v = 2`, a target-rank `G′`-seed.
Write `⟨·,·⟩` for the fixed pairing in which each hinge's 5 rows span
`C(e)^⊥` (Euclidean on Plücker coordinates in the scripts; the derivation
never uses more), `s₀` = corank of the **shared** rows (edges of `G − v`),
and

> `U := {u ∈ K⁶ : (u @ a, −u @ b) ∈ rowspan(shared rows)}`
> ` = {u : ⟨u, m(a) − m(b)⟩ = 0 for every motion m of the shared framework}`.

All of the following is exact (no genericity), machine-validated at every
probed seed (Step 3):

1. **Corank identity.** At placement `pt(v) = x` (with `x ∉ {[â],[b̂]}`),
   `corank R(G) = s₀ + dim(U ∩ C(va)^⊥ ∩ C(vb)^⊥)`; attainment of
   `target(G)` ⟺ the two functionals `u ↦ ⟨u, C(va)⟩`, `u ↦ ⟨u, C(vb)⟩`
   are **linearly independent on `U`**. (A `G`-row dependency's `v`-block
   forces antisymmetric fiber loads `±u`; its remaining blocks say exactly
   `(u@a, −u@b) ∈ rowspan(shared)`.)
2. **`U ∩ C(ab)^⊥ = R_a`** — the boundary loads reciprocal to the deleted
   hinge are exactly the stress loads (`u = Σ ν_j r_j(C_ab)` plus the shared
   relation *is* a `G′`-stress with `ab`-part `ν`).
3. **`dim U = dim R_a + 1`, forced**: `≤` because `U` meets the hyperplane
   `C(ab)^⊥` in the `dim R_a`-dim `R_a`; `≥` because the shared framework
   has exactly `4 + s₀ − index(G)` relative motions while
   `dim R_a = index(G) + 1 − s₀` at a target-rank seed. Consequences:
   `dim R_a = 0` (the `s₀`-jump seeds, and most deficient residuals) means
   **failure at every placement**; `dim R_a ≥ 1` is the live case; the old
   (K-shared) seed-quality worry is absorbed here — "some `G′`-stress
   engages the `ab` fiber" is all the quality a seed needs.
4. **The hard stratum `dim R_a = 1`** ((K-tight) and every probed (K-res)
   residual): `U = ⟨r⟩ ⊕ ⟨w⟩` with `⟨w, C_ab⟩ ≠ 0` forced. The route-A
   failure locus in the confinement space is the **degenerate conic**
   `det = ℓ_{line(ab)} · ℓ_{P′}`: the deleted hinge's line **union a second
   line `P′`** — so "the failure set is exactly the line" is refuted (the
   `∃`-form side conditions survive; any `∀`-form "off-line ⟹ attains"
   would be false). Uniform route-A failure ⟺
   `r ⊥ (pencil(pt a; Π(b)) + pencil(pt b; Π(b))) = Λ²Π̂(b)` when `b` is a
   hub (the two pencils span **all** lines in the panel because
   `pt(a) ∈ Π(b)` in the `G′`-seed), resp. ⟺ `r ∥ ★C_ab` when `b` is free.
   Route B is the mirror with load `−r` (KT 6.44): uniform failure ⟺
   `r ⊥ Λ²Π̂(c)`.
5. **(K-tight) combined criterion.** Both chain ends hubs: uniform failure
   of A and B ⟺ `r ⊥ (Λ²Π̂(b) + Λ²Π̂(c))` (5-dim) ⟺
   **`r̃ := ★r ∥ C(M)`**, `M = Π(b) ∩ Π(c)` the panels' **meet line** (which
   passes through `pt(a)`: the `G′`-seed pins `pt(a)` onto `M`). Gloss: the
   wrench the stress transmits through the deleted hinge is a **pure force
   along the meet line**. In particular a **non-null transmitted wrench**
   (`⟨r̃, r̃⟩_Klein ≠ 0`, "the wrench has pitch") certifies escape.
6. **Where KT's six dimensions went.** The carrier keeps 5 of KT's 6 escape
   dimensions — M₁'s panel `Λ²Π̂(a)` is exactly the lost one — so failure
   is one dimension away from KT's impossible. That single dimension is why
   PENCIL is research where KT Claim 6.12 was a page.

### Step 3 — machine validation, and the corrected numerical record

`notes/scripts/w4/repin.py` (tracked; exact-ℚ). Reproduce:
`python3 notes/scripts/w4/repin.py --control | --theta | --witness |
--stratum | --pointwise`.

- **The seed-442 "mispredict" was a sampler artifact.** `localtest.py`'s
  `plane_basis` returns two *parallel* in-plane directions whenever the
  normal's third coordinate is `0`, so `in_plane_point` then samples a
  **line through `pt(b)`**, freezing `hinge(vb)` across all placements. At
  seed 442, `nrm[b] = (1, −5/2, 0)`. With a robust sampler
  (`repin.py::rob_in_plane`) **seed 442 escapes on both routes**; so do the
  pool's two recorded failures (one pair, seeds 5000/5001, both with
  `nrm[b][2] = 0`). Corrected record: **every target-rank seed ever probed
  escapes** — 34/34 tight control, 6/6 θ(4,4,3), 12/12 `W19`, 4/4 `S29`,
  24/24 the `(def 0, dim R_a 1)` pool stratum. (Positive records — on-line
  failures, rank attainments — are unaffected; the artifact only ever
  *suppressed* escapes.)
- **Per-placement biconditional 80/80** (`--pointwise`): attainment ⟺ the
  two `U`-functionals independent, checked placement-by-placement at the
  tight control (`s₀ = 0`) and `W19` (`s₀ = 2`).
- **Structure checks at every seed**: `dim U = dim R_a + 1`,
  `U ∩ C(ab)^⊥ = R_a`, `R_a ⊆ U` — all asserted, no exceptions.
- **`P′` exhibited**: at control seed 440 the calculus *predicts* an
  off-line failure point from `(r, w)`; the placement fails by exactly 1.
- **The pencil-restricted M₂ form is refuted as criterion**: seeds 442 and
  473 have `r ⊥ pencil(pt b; Π(b))` yet escape (the `pencil(pt a; Π(b))`
  half of `Λ²Π̂(b)` is what saves them) — 32/34 for M₂-pencil vs 34/34 for
  the corrected `Λ²Π̂(b)` test. The workbook's earlier "M2 12/12 vs S 11/12"
  observation is superseded: both figures scored predictors against
  artifact-contaminated observations.
- **`★C(M)` identified**: the 1-dim perp of `Λ²Π̂(b) + Λ²Π̂(c)` equals the
  meet line's starred extensor (seed-442 post-mortem; `r` is *not* parallel
  to it there, and `⟨r̃, r̃⟩ ≠ 0`).

### Step 4 — reconciliation with the §2 derivation

What the design doc's §2 boundary-load derivation got **right**: the
antisymmetric-load setup; `R_a` as the stress-load space with
`dim R_a = corank − s₀`; failure as a perp condition of the right
codimension (its `dim S = 5` matches Step 2's 5-dim span — hence 11/12-style
agreement); the qualitative stratification (`dim R_a ≥ 2` generically
escapes — now: `dim U = dim R_a + 1 ≥ 3` makes the rank-≤1 locus of the
`2 × dim U` form matrix codim `≥ 2` in the sweep). Three **panel leaks**:

1. **M₁'s span is carrier-unrealizable** — `Λ²Π̂(a)` (or even `pencil(a)`)
   must not appear: its construction pins `hinge(vb) := q(ab)`, forbidden.
2. **M₂/M₃ under-counted**: restricting to `pencil(b)`/`pencil(c)` treats
   one hinge as swept and one as pinned; on the carrier both new hinges move
   with the point, and the effective span is the **full**
   `Λ²Π̂(b)`/`Λ²Π̂(c)`.
3. **`u` was confined to `R_a`** — correct only under a pinned
   `hinge = q(ab)` (which lands `u` in `C(ab)^⊥`); the carrier's obstruction
   space is `U = R_a ⊕ ⟨w⟩`, whose extra direction produces the second
   failure line `P′`.

Also corrected: the (K) recon item 4's "non-hub chain ends give `dim S = 6`,
`r ≠ 0` suffices" — a free end still leaves a 1-dim bad set (`r ∥ ★C_ab`);
it is the *pair* of routes that generically kills it.

### Step 5 — the uniform mechanism ((K-move)/(K-pitch)): assessment

What the kernel still needs, per habitat graph `G` and split: **some**
target-rank `G′`-chart-seed with `r̃ ∦ C(M)` (the both-ends-hubs form; at a
free end the failure direction is the deleted hinge's own line — `r̃ ∦ C_ab`
suffices, strictly easier). Per-graph this is polynomial non-vanishing on
the chart variety — one exact-ℚ witness decides it (and every probed
habitat has many). The **uniform** statement over the class is the open
mathematics. Named routes, with status:

- **(K-move) — fiber variability** (the route-1 gate's lever, sharpened).
  `C(M)` is *local-block data* (determined by `Π(b), Π(c)`); uniform failure
  at a graph would force `[r]` to be the local-block-determined value
  `[★C(M)]` on **every** local-block fiber. The gate's N8 already witnesses
  `[r]` taking 5 distinct directions on one fiber (and moving under a single
  distance-4 far move), refuting this at both probed habitat families. A
  uniform proof still needs `[r]`-as-rational-function infrastructure.
  **Status: open — the sharpest gap**, unchanged in substance from the (K)
  recon, but the target is now the *proven* failure direction `★C(M)`
  rather than a criterion carried on trust.
- **(K-pitch) — the null-wrench test** (new this pass). Failure requires
  `r̃` to be a *line* extensor (Klein-null, `⟨r̃, r̃⟩ = 0`); so
  `⟨r̃, r̃⟩ ≢ 0` on the seed variety suffices — a **single scalar
  polynomial** per (graph, split). By Cramer cofactors, the corank-1 stress
  coefficients are signed maximal minors of the deleted-row matrices, so
  `⟨r̃, r̃⟩` is an explicit quadratic in such minors — exactly the shape the
  White–Whiteley pure-condition calculus structures (the 1983/1987 papers,
  the literature hunt's verified nearest exemplars). A leading-term /
  degeneration evaluation of this one polynomial is the most attackable
  formal route identified so far. **Status: open, newly named; strictly
  easier as a target than (K-move)** (scalar vs projective direction),
  though not implied by it in either direction.
- **Degeneration / limit arguments**: unchanged **NO-GO** — still blocked on
  stress control at degenerate seeds (route-1 gate).
- **The joint sweep** (Step 1's new freedom): un-analyzed; even a genuinely
  `r̃ ∥ C(M)` seed might escape through it. Only widens the target.

**Adversarial hunt (the mandate).** A counterexample to `hK`/(K-res) at this
stratum must have `r̃ ∥ C(M)` at **every** target-rank chart seed — the
transmitted wrench a pure force along the panel-meet line, identically on
the variety — and additionally kill the joint sweep. Structural constraints
do not forbid it: `r̃` is reciprocal to both hinges at `a` (lines through
`pt(a)`), and `C(M)` passes through `pt(a)`, so the bad direction sits
*inside* the structurally-allowed cone — there is no cheap refutation. But
nothing found points toward it: no genuine failure seed exists anywhere in
the phase's corrected numerics; N8's fiber variability contradicts
block-determined `[r]` at both probed families; and a candidate structural
mechanism (a stress confined to the two panels) is excluded by the route-1
gate's full-support finding. **No counterexample candidate; hunt negative.**

**Verdict for (K-tight) (and (K-res), same stratum): open — true with
strong evidence, narrowed to (K-move)/(K-pitch).** The enabling technology
is unchanged (stress-as-chart-rational-function / pure-condition
infrastructure, option B), with (K-pitch) as the new sharpest entry point:
one scalar polynomial whose non-vanishing per habitat closes the kernel's
hard stratum. **(K-pitch) is developed in §(K-pitch) below (2026-08-04)**:
the pitch transfers off the stress side onto the motion side of
`G − v − a`, and closes in bracket-monomial form at companion-chain
habitats.

## §(K-pitch) — the null-wrench route: motion-side transfer, the placement quartic, a bracket-monomial closed form

The attack on §(K-tight) Step 5's sharpest entry point: escape failure
requires the transmitted wrench `r̃ = ★r` to be a *line* extensor
(`⟨r̃, r̃⟩_Klein = 0`), so `⟨r̃, r̃⟩ ≢ 0` on the seed variety suffices — one
scalar polynomial per (graph, split). Standing notation, on top of
§(K-tight)'s: split chain `b–v–a–c` at a target-rank `G′`-seed in the
`def(G) = def(G′) = 0` world, hard stratum `dim R_a = 1`;
`H := G − v − a = G′ − a` (terminal bodies `b, c`);
`T := ⟨C_ab, C_ac⟩` (the pencil of lines through `pt(a)` in
`plane(a,b,c)`); `B(x,y) := ⟨x, ★y⟩` the Klein form (`B(C(L), C(L′)) = 0`
⟺ the lines meet), `Q(x) := B(x,x)` the pitch quadric (`Q(x) = 0` ⟺ `x`
is a line extensor).

**Verdict (three-part; parts (ii)/(iii) extended 2026-08-04, second
pass).** (i) The reductions (T1)–(T5) below — transferring the pitch off
the stress side onto the **motion side of `H`** — are
**proven-informally**: exact linear algebra plus classical quadratic-form
theory, machine-validated per seed at every probed habitat
(`notes/scripts/w4/pitch.py`). (ii) At habitats whose split chain has a
**parallel length-3 companion chain** — θ(3,3,6) the exemplar, a member of
the **(K-res)** hard stratum (it contains a rigid `C₆`) — the pitch
polynomial collapses to a **bracket monomial** and (K-pitch) **closes**
(Step 5): the first hard-stratum splits discharged by argument (exact
seeds certify only the open side conditions' nonemptiness) rather than by
observation alone. For **longer companions** the far data compresses to a
single annihilator covector and `Q(z)` is an explicit local quadratic in
it (Step 5b, (T5)). (iii) The uniform kernel over the full class stays
**open**, but the naive collinear-collapse route is **refuted** and
replaced by the chart-legal **slide-in degeneration** (Step 6), which
evaluates the pitch at a `G°`-local limit system — developed in the
sibling **§(K-slide)** (2026-08-04 third pass) into a proof device: the
slide-transfer theorem (S1) makes one exact limit witness close a
habitat's split, the `K4`/`W4` control habitats are closed at every
split, and the named gaps are now **(K-Λ)** and **(K-slide-cl)** —
itself reduced (fourth pass, §(K-slide-cl)) to the combinatorial
**(K-slide-comb)** — plus the `P21`-type parallel-edge shapes (with
(K-wit) still the weakest exact form). Adversarial record intact — pitch was **nonzero at every
probed seed** (29/29 first pass: 16 tight-control + 5 residual + 8
pool-stratum; +5/5 second pass at the (T5) driver, θ(3,4,5) and the new
non-theta tight habitat NT21; +23/23 limit witnesses + 12/12 transfer
certificates, third pass, §(K-slide) Step 4).

**What would change this.** *For the reductions:* an error in the two-port
derivation (T1) — each claim is asserted per seed against an independently
computed stress. *For the route:* a habitat with `Q(z) ≡ 0` at every seed
(that kills the pitch route there, while escape may still hold through a
moving line wrench); none found. *For the closed form:* a companion-chain
habitat where one of the five brackets vanishes identically on the pencil
chart — the stated hypotheses exclude the one identified degeneration
(an `x`/`y`–opposite-hub adjacency, which drops `dim V_bc ≤ 2` and leaves
the companion-chain hypothesis unsatisfiable). *For the slide-in route:* a
simple-`G°` habitat whose slide-in limit twist is null or rank-degenerate
(that would puncture (K-slide-cl); none found — §(K-slide) *What would
change this* carries the sharper conditions); a companion habitat whose
local quadratic `Φ_loc` is the zero form (that would blunt (K-Λ) to the
trivial reduction).

### Step 0 — the pitch polynomial, and which specializations are legitimate

By Cramer, the corank-1 stress's coefficients at a target-rank seed are
signed maximal minors of the deleted-row matrices of `R(G′)`, so
`r = Σ_j λ_{(ab)j} r_j(C_ab)` and `P := ⟨r̃, r̃⟩` are honest **polynomials
in the chart coordinates** (not just rational functions on the target-rank
locus). Two consequences frame everything below.

- **One witness seed decides a split.** `P ≢ 0` plus density of the
  target-rank locus (supplied by the kernel's own antecedent,
  `HasGenericPencilRealization` of the split graph) gives a seed that is
  simultaneously target-rank and `P ≠ 0`; §(K-tight) Steps 2/5 then give
  the escape, and `hK`/(K-res)'s conclusion follows (the hub-selector /
  `pencilRow` packaging is combinatorial, from `hcard` — §"widened
  kernels" Step 5).
- **Polynomial specialization ≠ the refuted degeneration route.** The
  route-1 NO-GO (design doc §"(K) route-1 gate") refuted *analytic stress
  control at degenerate seeds*; evaluating the polynomial `P` at a special
  chart point needs no control — the obstruction was only ever that no
  specialization made the global minors *computable*. (T1) supplies
  exactly that computability, by eliminating the stress from `P`
  altogether.

### Step 1 — (T1): the two-port transfer — `r` from motions of `H`, no stress

`H = G′ − a` and `a` carries exactly the two hinges `C_ab, C_ac` in `G′`,
both through `pt(a)` (KT's (6.44) equilibrium body). Let

> `V_bc := { m(b) − m(c) : m a motion of H }` ⊆ `K⁶`

be the **relative twist system** of the terminals — a motion-side object
(motions of a body–hinge framework are screw-center assignments with
`m(x) − m(y) ∈ ⟨C_xy⟩` per hinge; Whiteley 1996 §12.2). Then, exactly:

> **(T1)** `r` is Euclidean-orthogonal to `V_bc` and to `T`; at a seed
> with `dim V_bc = 3` (the generic value; observed at every probed seed)
> `W := V_bc ⊕ T` is 5-dimensional and **`r` spans `W^⊥`**. Moreover
> `V_bc ∩ T = 0` is *forced* at a target-rank seed.

*Proof.* Restrict the stress `λ` to the `H`-rows: equilibrium at every
body off `{a, b, c}` is untouched, at `b` the deleted `ab`-fiber
contributed `−r`, at `c` the `ac`-fiber contributed `−r_ac = +r` (6.44).
So `λ|_H` is an `H`-row combination with net load `(+r @ b, −r @ c, 0)`.
Pairing a row combination's loads against any motion gives `0`, so
`⟨r, m(b) − m(c)⟩ = 0` for every motion `m` — `r ⊥ V_bc`; `r ⊥ T` is the
reciprocity of `r` to both `a`-hinges (§(K-tight)). Conversely a nonzero
`t = ω₁C_ab + ω₂C_ac ∈ V_bc ∩ T` extends the `H`-motion to
`m(a) := m(b) − ω₁C_ab = m(c) + ω₂C_ac`, a nontrivial flex of `G′` —
impossible at a target-rank seed with `def(G′) = 0`. So
`dim W = dim V_bc + 2 = 5` and the 1-dimensional `W^⊥` is `⟨r⟩`. ∎

Two structural facts ride along. **(a) Path-sum containment:** telescoping
`m(x) − m(y) = ω_{xy}C_{xy}` along any `b`–`c` path `P` of `H` gives
`V_bc ⊆ span{C_e : e ∈ P}` — for **every** path, simultaneously. This is
the lever Step 5 uses. **(b)** `V_bc` needs only a kernel computation
(cycle conditions on hinge rotations) — the stress, its cofactors, and
the corank bookkeeping have disappeared from the right-hand side; this is
the computable simplification the refuted routes lacked.

### Step 2 — (T2): the sign law — pitch of `r` = − pitch of the reciprocal twist

`T` is **totally isotropic** for `B` (its two generators meet at `pt(a)`),
and both `★r` and the solution set of `B(·, C_ab) = B(·, C_ac) = 0` live
in `T^⊥` (Klein-perp, 4-dimensional). Let

> `z` span `V_bc ∩ T^{⊥_B}` — the **reciprocal twist**: the unique (up to
> scale, generically) relative twist of `b` vs `c` through `H` that does
> no reciprocal work on either hinge at `a`.

In the quotient `T^{⊥_B}/T` — a **hyperbolic plane** (Witt index drops by
`dim T`) — the classes of `★r` and `z` are `B`-orthogonal (that is (T1):
`B(★r, z) = ⟨r, z⟩ = 0`). In a hyperbolic plane two nonzero orthogonal
vectors are either both isotropic (and parallel) or both anisotropic with
`Q`-values of product `= −(nonzero square)`:

> **(T2)** at a seed where `z ∉ T` and `★r ∉ T`:
> `Q(r) = 0 ⟺ Q(z) = 0`, and when nonzero `Q(r)·Q(z) < 0`.

So the pitch of the transmitted wrench equals (up to a negative square)
the pitch of a **motion** of the smaller framework `H`. Failure geometry:
`Q(z) = 0` means the reciprocal twist is an actual **line** `L`; `z ∈ T^⊥`
then forces `L` through `pt(a)` or `L ⊆ plane(a,b,c)` (a line meets both
`a`-hinges ⟺ one of the two). On the irreducible chart, identical
vanishing of `Q(z)` therefore splits into two sharp identical-membership
statements — *(F-A)* `z` is always a rotation about a line through
`pt(a)`, or *(F-B)* always about a line in `plane(a,b,c)` — each refutable
by one exact seed.

### Step 3 — (T3): the motion form of the full criterion, and (K-wit)

The β-plane `Λ²Π̂(b)` is maximal isotropic, hence its own Klein-perp; so
§(K-tight)'s route-A uniform-failure criterion `r ⊥ Λ²Π̂(b)` reads:
**`★r` is a line lying in the panel `Π(b)`** — and route B dually. Both
routes failing ⟺ `★r ∈ Λ²Π̂(b) ∩ Λ²Π̂(c) = ⟨C(M)⟩`, recovering
§(K-tight) Step 2.5. Transferred by (T1) (and using
`B(C(M), C_ab) = B(C(M), C_ac) = 0`, since `M` passes through `pt(a)`):

> **(T3)** at a `dim W = 5` target-rank seed, both hubs: **escape ⟺ some
> motion `m` of `H` has `B(C(M), m(b) − m(c)) ≠ 0`** — the relative twist
> system is not contained in the linear line complex of the meet line.

Two consequences. **(a)** `Q(r) ≠ 0` certifies **both routes at once**
(any failure mode requires `★r` decomposable) — and this is
**end-stratum-uniform**: at a free chain end the failure directions are
again line extensors (`★C_ab`-type, §(K-tight) Step 4), so pitch ≠ 0
certifies escape in every end configuration with the *same* polynomial.
**(b)** The kernel's remaining content, in its weakest exact form, is now
stress-free and existential:

> **(K-wit)** *(per habitat + split; equivalent to the escape at a good
> seed)* — some pencil-chart target-rank seed of `G′` admits a motion of
> `H` whose relative `b`–`c` twist pairs non-trivially with `C(M)` (both
> hubs; at a free end, with the corresponding 1-dim failure direction).

One linear functional on one kernel — much closer to the phase's
somewhere-witness engine food than stress cofactors, though still open
uniformly (the kernel is seed-dependent).

### Step 4 — (T4): the placement quartic, and an `a`-free leading term

`pt(a)` is a chart coordinate confined to the meet line `M`; `V_bc` does
not involve `a` at all. Fix everything but `pt(a) = p₀ + t·d` (`d` = the
direction of `M`): the two conditions cutting `z` out of `V_bc` are linear
in `t`, so `z(t)` is quadratic and

> **(T4)** `q(t) := Q(z(t))` is a polynomial of degree ≤ 4 whose `t⁴`
> coefficient is `Q(z_∞)`, where `z_∞` is the same construction with the
> two `a`-hinges replaced by the lines joining `M`'s **direction point**
> `(d, 0)` to `pt(b)`, `pt(c)` — an expression in which `a` does not
> appear.

Validated by exact interpolation at four habitats (one seed each,
`--sweep`), with the sign law re-checked against a fully recomputed stress
at moved placements. All five coefficients were nonzero at all four, the
leading one included. This gives a sufficient reduction one level down:

> **(K-pitch-∞)** *(sufficient for (K-pitch) at the split)* — `Q(z_∞) ≢ 0`
> on the `a`-free part of the chart.

### Step 5 — the companion-chain closed form: pitch as a bracket monomial

Suppose the split chain `b–v–a–c` has a **parallel length-3 companion**:
a second path `b–x–y–c` in `H` (so `G` has two length-3 hub paths between
the same hubs). Write `C₁ = C(bx), C₂ = C(xy), C₃ = C(yc)` and
`[p,q,r,s]` for the `4×4` determinant of the four homogenized points.

> **Proposition (companion-chain closed form).** At a target-rank seed
> with `dim V_bc = 3`: path-sum containment (Step 1a) pins
> `V_bc = ⟨C₁, C₂, C₃⟩`, and the reciprocal twist is
> `z = −[y,c,a,b][x,y,a,c]·C₁ + [y,c,a,b][b,x,a,c]·C₂
>      − [x,y,a,b][b,x,a,c]·C₃`, with
>
> `Q(z) = 2·[x,y,a,b]·[b,x,a,c]·[y,c,a,b]·[x,y,a,c]·[b,x,y,c]`.
>
> In particular (T2/T3): if the five brackets are nonzero at one such
> seed, the split escapes.

*Proof.* The Gram of `B` on `(C₁, C₂, C₃)` has only one nonzero entry,
`B(C₁, C₃) = [b,x,y,c]` (consecutive lines meet at `pt(x)`, `pt(y)`) —
the serial-chain signature (`rank Q|_{V_bc} = 2`, observed identically at
θ(3,3,6)). The two cutting conditions have coefficient rows
`(0, [x,y,a,b], [y,c,a,b])` and `([b,x,a,c], [x,y,a,c], 0)` — the zeros
because `C₁` and `C_ab` meet at `pt(b)`, `C₃` and `C_ac` at `pt(c)`. The
cross product gives `z`; expanding `Q` through the Gram leaves the single
`2·z₁z₃·[b,x,y,c]` term. ∎

**Instantiation: θ(3,3,6)** (two length-3 paths + one length-6 path
between two hubs; tight, `def = 0` (machine-checked), 2EC,
landed-**sufficient** feasible — triangle-free with `hcard` from the R4
shape, the L6b criterion — and it contains the rigid `C₆` spanned by the
two short paths, so it is a **(K-res)**-habitat member, not reachable by
the pinned `hK`). On its chart: `x, a ∈ Π(b)`, `y, a ∈ Π(c)`, all else
generic. Each bracket has an obvious witness — `[x,y,a,b]` needs
`y ∉ Π(b)` etc.; `[b,x,y,c]` needs the two short paths non-coplanar — so
each is `≢ 0` on the irreducible chart, hence so is their product; the
remaining open conditions (target rank, `dim V_bc = 3`, the (T2) side
conditions) are nonempty by the validated seeds, so a common good seed
exists and **(K-pitch) holds at θ(3,3,6)'s hard-stratum split:
proven-informally** (machine-confirmed exactly, `--theta336`:
`V_bc = ⟨C₁,C₂,C₃⟩`, the monomial identity, and the sign law against the
independently computed stress, 4/4 seeds).

**Scope.** The proposition applies verbatim to any hard-stratum split
with a parallel length-3 companion (interior `x, y` may even be hubs —
only the five bracket-nonvanishing checks are chart-dependent). The one
identified degeneration: `y` adjacent to `b` (or `x` to `c`) forces the
bracket's four points coplanar *and* creates a shorter `b`–`c` path,
collapsing `dim V_bc ≤ 2` — outside the proposition's hypotheses. This is
the White–Whiteley mechanism in miniature: at special structure the pure
condition **factors into brackets** (cf. the 1987 paper's factorization
of bar-and-body pure conditions along the block lattice), and the pencil
chart is then attacked bracket-by-bracket.

### Step 5b — (T5): longer companions — the Λ-compression

Suppose the companion `b`–`c` path has length `k` with `4 ≤ k ≤ 6` and
independent lines `C₁,…,C_k`. Path-sum containment still pins
`V_bc ⊆ ⟨C₁,…,C_k⟩`, now of codimension `k − 3`; **all far-graph
dependence enters through the annihilator** `Λ` of `V_bc` in the span's
dual (a `(k−3)`-frame of covectors; for `k = 4` a single covector `λ`, up
to scale). For `k = 4`:

> **(T5)** with `m := (⟨C_i, ★C_ab⟩)_i = (0, m₂, m₃, m₄)` and
> `n := (⟨C_i, ★C_ac⟩)_i = (n₁, n₂, n₃, 0)` (the zeros structural, as in
> Step 5), the reciprocal twist's coefficient vector is the Laplace
> cofactor vector `ω` of the `3×4` matrix `[λ; m; n]`, and — since the
> path Gram is banded (consecutive lines meet) —
>
> `Q(z) = 2·(ω₁ω₃·[b,x₁,x₂,x₃] + ω₂ω₄·[x₁,x₂,x₃,c] + ω₁ω₄·[b,x₁,x₃,c])`
>
> — an explicit **quadratic form `Φ_loc(λ)`** whose coefficients are
> 4-point brackets in the local points `{b, x₁, x₂, x₃, c, a}` only.

`k = 3` recovers Step 5 (no far data at all — `Φ_loc` is a constant, the
bracket monomial); at `k ≥ 7` the span is everything and the compression
is vacuous. The reduced gap on such habitats:

> **(K-Λ)** *(sufficient for (K-pitch) at a length-4-companion split)* —
> some target-rank chart seed's far covector `λ` avoids the local quadric
> `{Φ_loc = 0}`.

One projective point against one locally-computable quadric — the entire
far graph enters through `λ` alone. Machine-validated exactly
(`--companion4`): at θ(3,4,5) (where `λ` is independently recomputable as
the far arc's span normal — cross-checked) and at **NT21**, a new
non-theta tight habitat (hub multigraph on 4 hubs with `b`–`c` paths of
lengths 3 and 4 plus five more; `Σℓ = 24 = 6·4`; certified `def = 0` and
no proper rigid branch-union over all `2⁷` branch subsets): `λ` unique,
`z` reproduced from `(λ, m, n)` alone, the `Φ_loc` identity exact, and
`Q ≠ 0` with the (T2) sign law against the independently computed stress,
5/5 seeds.

### Step 6 — uniformity: the naive collapse refuted, and the slide-in degeneration

**(a) The naive collinear collapse is REFUTED as a chart move.** "Each
hub path degenerates toward its own line" cannot happen on the pencil
chart: an interior `x` adjacent to hub `u` lives in `Π(u)`, and the chord
`line(pt u, pt w)` meets `Π(u)` only at `pt(u)` (else the panels are
incident) — so the path can only reach its chord *at the hub point
itself*. And repairing this by making chords panel-resident
(`pt(w) ∈ Π(u)` along every `G°`-edge) forces each closed hub star
coplanar (`n_u ⊥` every neighbour chord — impossible outright when the
chords at `u` span 3-space), which on the probed complete-type `G°`
(e.g. `K4`) is exactly the **all-coplanar locus** — and that locus is
target-rank-**deficient** on tight habitats (R2's criterion
`2|E| < 3|V| − 3` holds identically under `5|E| = 6(|V|−1)`). The
tightness budget `Σ_P ℓ_P = 6·c°(G°)` (elementary:
`index(G) = 6(|E°| − |V°| + 1) − Σℓ_P`) survives as bookkeeping, but the
order-0 "body–hinge on `G°` with one line per path" picture does not.

**(b) The corrected, chart-legal degeneration: the slide-in.** Move each
panel-constrained interior *into its hub point along its own ray*:
`x(ε) = pt(u) + ε·(x₀ − pt(u))` — the segment stays in `Π(u)`, so every
`ε > 0` is an honest chart point. The hinge lines have a clean limit,
per edge: a **hub-incident** hinge `u–x` is *constant* along the slide
(`û ∧ (û + εd) = ε·û∧x̂₀` — same line, dying magnitude); an
**interior–interior** hinge becomes the **chord** `û∧ŵ`; an
interior–fixed hinge becomes the hub-to-point line. So for an
all-length-3 (double-subdivision) habitat the limit system is **body–
hinge on `G°` where each edge carries the serial triple
(pencil line at `u`, chord `u∧w`, pencil line at `w`)** — consecutive
members meeting at the hub points, i.e. per `G°`-edge exactly the banded
serial-chain Gram of Step 5, one level up. The far data compresses to
`G°`-local decorations (hub points, normals, one pencil parameter per
edge-end).

**(c) Why the limit is legitimate: the slide-transfer theorem.** The
analytic route this pass first recorded (constant-rank family ⟹
continuous kernel, with `O(ε)` Plücker convergence as evidence) is
**superseded by §(K-slide) (S1)**: the normalized row family is
polynomial in (chart data, `ε`) including `ε = 0`, the slide is a chart
automorphism for `ε ≠ 0`, and one exact limit witness proves `Q(z) ≢ 0`
on the chart by Zariski closure alone — no convergence, and rank
persistence (the observed `9 → 9`) is an a-posteriori corollary, not a
hypothesis.

**(d) The slide-in evaluation WORKS on simple `G°` — now a proof
device.** At dbl-subdivided `K4` (the (K-tight) control), the limit
system keeps `dim V_bc = 3` and its reciprocal twist is **pitched**
(3/3 exact, `--slide`). The gap this named, (K-slide) — "`Q ≠ 0` at
the limit system for generic decorations" — is **witness-decidable per
member by (S1)** and *discharged at every probed member*; the surviving
uniform statement is **(K-slide-cl)** (§(K-slide) Step 5). The
`G°`-level system — decorated multigraphs, finitely many parameters per
edge, no subdivision interiors — is squarely White–Whiteley-1987
territory and now carries the class program.

**(e) The parallel-edge obstruction — and the division of labor.** On a
theta, all chords coincide with `line(b,c)`, and the (partial) slide-in
limit twist comes out **null** (`Q = 0`, 2/2 exact at θ(3,4,5)): the
order-0 evaluation fails on `G°` with parallel edges — and §(K-slide)
(S5) shows this is structural (a repeated line in a hinge cycle under
the full support; a hub-concentrated circuit under reduced supports).
Parallel `b`–`c` edges are exactly **short companion paths** — Steps
5/5b's monomial / `Φ_loc` territory. The two flanks this pass left
untested — mixed path lengths on simple `G°`, and hub–hub edges — are
now **witnessed inside the slide framework** (§(K-slide) Steps 2/4);
what remains outside both mechanisms is the non-`bc`-parallel shape
(`P21`, §(K-slide) S5).

- **The joint sweep** (§(K-tight) Step 5) still only widens the escape;
  un-analyzed.

**Adversarial hunt (this pass).** A pitch-route counterexample must have
the reciprocal twist `z` decomposable at every seed — by the Step-2
dichotomy, a line through `pt(a)` always, or a line in `plane(a,b,c)`
always — while `V_bc` varies with the far seed (route-1 gate, N8). No
structural mechanism produces that: the only found `Q|_{V_bc}`-degeneracy
(the serial-chain Gram) still yields nonzero pitch as a bracket monomial.
Pitch was nonzero at **29/29** probed seeds: 16 tight-control (dbl-subdiv
`K4` 6, θ(3,4,5) 5, θ(3,3,6) 5), 5 residual (`W19` 3 — free-end shape,
`S29` 2 — both-hubs), 8 pool-stratum (4 splits × 2); the second pass adds
**5/5** at the (T5) driver (θ(3,4,5) 3, NT21 2). The slide-in limit's
*null* twist on thetas is not a counterexample — those splits escape
through Steps 5/5b, and the theta `ε`-family itself stays `Q ≠ 0` at every
sampled `ε` down to `1/64`. **No counterexample candidate; hunt
negative.**

### Verification

`notes/scripts/w4/pitch.py` (tracked; exact-ℚ, on top of `repin.py`, with
its robust in-plane sampler; every sampled object carries rank/dimension
asserts). Reproduce:
`python3 notes/scripts/w4/pitch.py --control | --witness | --stratum |
--sweep | --theta336 | --companion4 | --slide`. Per seed it asserts:
(T1) `r ⊥ V_bc`, `V_bc ∩ T = 0`, `W^⊥ = ⟨r⟩`; (T2) side conditions and
the sign law `Q(r)·Q(z) < 0` (or both zero); (T3) the motion-form
combined criterion against `repin.py`'s validated `critA/critB`, and the
`★r`-in-panel route-A form; (T4) exact interpolation, degree ≤ 4,
`q₄ = Q(z_∞)`, and the sign law against a recomputed stress at two moved
placements; (`--theta336`) the pairing–bracket dictionary
`B(C(uv), C(pq)) = [u,v,p,q]`, `V_bc = ⟨C₁,C₂,C₃⟩`, the closed-form `z`,
and the bracket-monomial identity; (`--companion4`, T5) the containment
`V_bc ⊆ ⟨C₁..C₄⟩`, uniqueness of `λ`, `z` from `(λ, m, n)` alone, the
`Φ_loc` identity, the θ far-arc `ν` cross-check, and NT21's habitat
certificates (`def = 0`, no proper rigid branch-union, `2⁷` subsets);
(`--slide`) the per-edge limit-line rule, motion-rank persistence
(9 → 9), `O(ε)` Plücker convergence of `V_bc(ε)` to the limit plane, and
the limit twist's pitch class (pitched at dbl-K4, null at θ).

**Confidence verdict: (T1)–(T5), the companion-chain closed form, and
the slide-in limit calculus proven-informally; (K-pitch) at
θ(3,3,6)-type splits proven-informally; the naive collinear collapse
refuted; the uniform (K-pitch)/(K-tight)/(K-res) kernel open — narrowed
to (K-Λ) (companion habitats) and, after §(K-slide)'s third pass and
§(K-slide-cl)'s fourth, (K-slide-comb) (the combinatorial residue of
(K-slide-cl) on parallel-free shapes, every probed member discharged)
plus the `P21`-type shapes, with (K-wit)/(K-pitch-∞) as the weakest
exact forms.**

## §(K-slide) — the slide-in transfer theorem: the `G°`-level limit is a proof carrier

Sibling of §(K-pitch), attacking the gap its Step 6 named; standing
notation inherited (split chain `b–v–a–c`, both ends hubs, `G′ = G − v +
ab`, `H = G′ − a`, `V_bc`, `T = ⟨C_ab, C_ac⟩`, the reciprocal twist `z`,
the pitch quadric `Q`). `G°` = the hub multigraph (vertices = hubs, one
edge per hub path, the split path's edge written `e₀ = bc`); a
**decoration** of the limit system = hub points, normals, one pencil
direction per slid path end, one meet-line point per length-2 path, and
free middle points for paths of length ≥ 4 — exactly the chart data the
slide does not destroy.

**Verdict (2026-08-04, third pass).** (i) The **slide-transfer theorem
(S1) is proven-informally**: the slide is an automorphism of the pencil
chart for every `ε ≠ 0`, the (normalized) `H`-row family is polynomial in
(chart data, `ε`) *including* `ε = 0`, and hence **one exact `ε = 0`
witness** — (W1) limit rows independent, (W2) `dim V_bc(limit) = 3`, (W3)
`z(limit)` defined, (W4) `Q(z_limit) ≠ 0` — proves `Q(z) ≢ 0` on the
habitat's chart. Step 6(d)'s rank-persistence proviso is **dissolved**:
nothing analytic is consumed (the `O(ε)` convergence record survives only
as numerics history, and rank constancy along the slide is now an
a-posteriori corollary, not a hypothesis). (ii) The limit carrier
extends to **arbitrary path lengths and arbitrary slide supports** (S2);
Step 6(e)'s two untested flanks — mixed path lengths on simple `G°`, and
hub–hub edges — are *inside* the framework and **witnessed**; the
hub-level serial-chain system equals the subdivision-level limit
(interior elimination, machine-asserted). (iii) **Witnessed members**
(S4): dbl-subdiv `K4` (all splits, by `Aut(K4)`), the wheel `W4` (**all**
splits: rim orbit + both spoke ends), `K5 − {01, 23}` at split `02` (both
ends), prism+diagonal at split `01` (both ends), the mixed-length `K4`
(both ends), the hub–hub-edge `K4` (both ends) — **23/23 hard witnesses
pitched** — so (K-pitch) closes at every one of these splits, and in
particular **the double-subdivision (K-tight) control habitats over `K4`
and `W4` close at every split**, with no side condition left. (iv)
**Parallel `G°`-edges obstruct the device at order 0** (S5): under the
full slide support the coincident chords force a stress on the
parallel-pair cycle (proven — a repeated line in a 6-hinge cycle), and
the probed reduced support does not rescue it (a circuit closes on a
theta sub-multigraph; exhibited). The sharpest uncovered *shape* is
**P21** — a parallel non-`bc` edge with no length-≤4 `bc`-companion —
reachable by neither the slide device nor the companion forms. The
class-uniform residue is **(K-slide-cl)** (Step 5) — attacked in
**§(K-slide-cl)** (fourth pass, 2026-08-04): the geometry is discharged
by the tetrahedral collapse and the residue reduces to the purely
combinatorial **(K-slide-comb)**.

**What would change this.** *For (S1):* an error in the
automorphism/polynomiality argument — refutable by a habitat whose chart
pitch vanishes identically while a (W1)–(W4) witness exists (the theorem
says none can). *For the member closures:* nothing short of that — each
rests on exact certificates plus (S1). *For the residue:* a proof (or refutation) of §(K-slide-cl)'s
combinatorial residue (K-slide-comb), or any local mechanism for
`P21`-type shapes.

### Step 1 — (S1): the slide-transfer theorem

Fix the habitat, the split, and a **slide support** `Σ`: any set of
single-panel interiors of `H` (each `x ∈ Σ` is adjacent to exactly one
hub `h_x`, its only chart constraint `pt(x) ∈ Π(h_x)`). For `ε ∈ K` let
`slide_ε` fix every chart coordinate except `pt(x) ↦ pt(h_x) + ε·(x₀ −
pt(h_x))` for `x ∈ Σ`.

> **Theorem (S1).** Suppose one exact chart point `data₀` satisfies, at
> its `ε = 0` limit line system: **(W1)** the `H`-rows are independent
> (`dim ker = 6|V_H| − 5|E_H|`; `= 9` at every tight member), **(W2)**
> `dim V_bc = 3`, **(W3)** the two `T`-conditions are independent on
> `V_bc`, **(W4)** `Q(z) ≠ 0`. Then `Q(z) ≠ 0` on a dense open subset
> of the pencil chart of `G′`.

*Proof.* (a) For `ε ≠ 0`, `slide_ε` is an **automorphism of the chart**:
it maps each panel `Π(h_x)` to itself bijectively (an affine scaling
about `pt(h_x)` inside the plane) and touches no other coordinate's
constraint. (b) Choose per-edge line representatives polynomial in
`(data, ε)`: for a hub-incident hinge `(h, x)` with `x ∈ Σ`, `x̂(ε) = ĥ +
ε·(x₀ − pt(h), 0)` gives `ĥ ∧ x̂(ε) = ε·(ĥ ∧ x̂₀)` — the hinge line
**never moves along the slide**; take the constant representative `ĥ ∧
x̂₀` (at `ε = 0` it reads as the pencil line at `pt(h)` toward `x₀`).
For every other hinge take `p̂(ε) ∧ q̂(ε)`; at `ε = 0` a slid–slid hinge
becomes the hub **chord**, a slid–fixed hinge the hub-to-point line, all
others their original lines. Off a proper closed set every
representative is nonzero at every `ε`, `0` included. (c) Encode `m(u) −
m(w) ∈ ⟨C_e⟩` by the 15 minor rows `(m(u) − m(w))_i (C_e)_j − (m(u) −
m(w))_j (C_e)_i` (same kernel as the 5-row perp form): the stacked
matrix `R(data, ε)` is **polynomial**, and its kernel depends only on
the projective lines — so for `ε ≠ 0` it is the `H`-motion space at the
chart point `slide_ε(data)`, while `T` is constant (`a, b, c` are never
slid). (d) Let `U ⊆ chart × 𝔸¹` be the locus where `rank R` and
`rank [R; P]` (`P : m ↦ m(b) − m(c)`) attain their absolute bounds
(`5|E_H|` resp. `6|V_H| − 6`; the latter because trivial twists always
lie in `ker [R; P]`, so (W2)'s `dim V_bc = 3` under (W1) says exactly
`ker [R; P]` = the trivial twists) and the `2 × 3` matrix of the
`T`-conditions on `V_bc` has rank 2. These are maximal-rank conditions on polynomial
matrices, so `U` is **open**, and (W1)–(W3) say precisely `(data₀, 0) ∈
U`. On `U`, `dim V_bc ≡ 3`, fixed cofactor formulas give a basis
rational in `(data, ε)`, and `z`, `Q(z)` are rational with `{Q(z) = 0}`
closed. (e) Suppose the chart function `data ↦ Q(z)` vanished
identically wherever defined. The chart is irreducible (a tower of
affine-linear fibers: free hub points, normals in hub-dependent linear
subspaces, interiors in panels / meet lines / free space), so `U` is
irreducible; by (a)+(c), `Q(z) = 0` on `U ∩ {ε ≠ 0}` — dense open in `U`
since `U` is open nonempty, hence not inside `{ε = 0}` — so `Q(z) ≡ 0`
on `U`, contradicting (W4) at `(data₀, 0)`. ∎

Three remarks. **(i) Nothing analytic survives**: no `ε → 0` limits, no
constant-rank family, no convergence — and no target rank, realization
count, or stress at the witness: (W1)–(W4) are linear-algebra
certificates on the limit lines alone. **(ii) Rank persistence is now a
corollary**: (W1) certifies the absolute row-count bound at `ε = 0`, and
rank is subgeneric only on a closed set, so it is constant along the
slide off finitely many `ε` — Step 6(c)'s observed `9 → 9` is proven
a-posteriori and consumed nowhere. **(iii) The support is a free
parameter**: the proof runs verbatim for any `Σ`; smaller supports leave
more surviving chart coordinates in the limit data (less locality, same
validity) — the freedom Step 5 exploits and (S5) tests.

### Step 2 — (S2): the general limit carrier on `G°`

Per hub path `[u, x₁, …, x_{ℓ−1}, w]` (with the ≥3-length ends in `Σ`),
the limit lines are:

    ℓ = 1 : (u∧w)                      — hub-hub hinge (mutual-panel data)
    ℓ = 2 : (u∧x₁, x₁∧w)               — x₁ on the meet line; not slid
    ℓ = 3 : (P_u, u∧w, P_w)            — the serial triple of Step 6(b)
    ℓ = 4 : (P_u, u∧x₂, x₂∧w, P_w)     — x₂ free; not slid
    ℓ = 5 : (P_u, u∧x₂, x₂∧x₃, x₃∧w, P_w)

with `P_u` the (constant) pencil line at `u` toward the slid end. All of
it is `G°`-local decoration data, and the decoration space is an
irreducible linear-fiber tower, so per member "one witness ⟹ generic
decorations" holds for the limit system itself too. **Interior
elimination is exact**: every interior has degree 2, so relative twists
telescope, and the hub-level system — bodies at hubs only, one
constraint `m(u) − m(w) ∈ span(chain lines)` per `G°`-edge — has the
same `V_bc` as the subdivision-level limit (machine-asserted at the `K4`
and mixed members). Step 6(e)'s flanks are therefore *inside* the
framework: mixed lengths contribute longer serial chains with surviving
free points, hub–hub edges contribute their own hinge as a 1-member
chain.

### Step 3 — (S3): what a witness closes

Per split, the battery pairs each `ε = 0` witness with an `ε = 1`
**transfer certificate**: one exact target-rank `dim R_a = 1` seed
passing (T1)–(T3) with the (T2) side conditions and `Q(r) ≠ 0`. The
certificate alone already exhibits an escaping seed (§(K-tight)'s
per-seed criterion, via (T3)) — by Step 0's one-witness logic every
probed split is *individually* closed that way, `P21`'s included. What
(S1) adds is **where the argument lives**: the witness computation runs
on the `G°`-level limit system — pencil lines, chords, banded serial
Grams, the bracket-friendly objects — so a *class-uniform* proof can now
be attempted on the structured limit carrier and transferred to every
chart at once. That is the program (K-slide-cl) names.

### Step 4 — (S4): the battery (all exact, `kslide.py`)

Every member is tight (`def = 0`, asserted), both split-chain ends hubs.
"hnoRigid" = no proper rigid branch-union (NT21-standard `2^paths`
sweep). Witness = hard (W1)–(W4); certificate = (T1)–(T3) + `Q(r) ≠ 0`.

| member (`G°`, lengths) | \|V\| | hnoRigid | splits covered | witnesses |
|---|---|---|---|---|
| dbl-subdiv `K4` (all 3) | 16 | yes | all (Aut-transitive on directed edges) | 3 + (S2) check |
| `W4` wheel, rim (all 3) | 21 | yes | rim orbit, both ends (`0↔1, 3↔2`) | 2 |
| `W4` wheel, spoke (all 3) | 21 | yes | both spoke ends (2 runs) | 2 + 2 |
| `K5 − {01, 23}`, split `02` (all 3) | 21 | yes | both ends (`0↔2, 1↔3` autom.) | 2 |
| prism + diagonal `04`, split `01` (all 3) | 26 | yes | both ends (2 runs) | 2 + 2 |
| `K4` mixed `(3,4,2,3,3,3)` | 16 | yes | both ends (2 runs) | 2 + 2, (S2) check |
| `K4` + hub-hub edge `23`, `(3,1,4,4,3,3)` | 16 | yes | both ends (2 runs) | 2 + 2 |

23/23 witnesses pitched; 12/12 certificates passed ((T1)–(T3) re-validated
at every new habitat). Consequences: **(K-pitch) holds at every listed
split, proven-informally** ((S1) + (S3)); the `K4` and `W4` rows close
their habitats at *every* split (orbit-complete), so the
double-subdivision (K-tight) control class over `K4`/`W4` is **closed
with no residual side condition**.

### Step 5 — (S5): the parallel-edge obstruction, and the residue

**Full support (proven).** For a `k`-hinge body cycle, telescoping gives
`#stresses = 6 − rank{lines}`. Two parallel length-3 chains slide to
serial triples `(P_u, C, P_w)`, `(P_u′, C, P_w′)` **sharing the chord**
`C`: their union is a 6-hinge cycle with ≤ 5 distinct lines — one stress,
always. (Machine: the exhibited stress sits exactly on the parallel
pair, 6 edges, line rank 5.) So (W1) is unattainable at parallel
`G°`-edges under the full support, for *every* decoration.

**Reduced supports (probed, obstructed).** Hub-incident lines never move
along any slide ((S1)(b)), so both parallel chains keep pencil-line ends
at the shared hubs regardless of support, and the limit concentrates
chords through hub points. At **P21** — `G°` = `K4 − 02` plus doubled
`23`, lengths `(3; 3,3; 4,5,3,3)`, 21 vertices, residual-shaped (the
parallel pair is a rigid `C₆`) — leaving one parallel chain fully
unslid still yields exactly one limit stress, now supported on the theta
sub-multigraph `{12, 13, 23a, 23b}` (12 edges, line rank 6; exhibited).
Half-measures are worse: a half-slid chain's middle line passes through
the hub point and rebuilds the short circuit.

**Division of labor, updated from Step 6(e).** `bc`-parallel shapes go
to the companion forms (Steps 5/5b: monomial at `ℓ = 3`, (K-Λ) at
`ℓ = 4`, the (T5) frame at `ℓ = 5, 6`). Non-`bc`-parallel shapes with no
length-≤4 `bc`-companion — exemplar `P21` — are covered by **neither**
mechanism: closable per-split by Step-0 seed logic (P21's certificate
seed escapes), but with no `G°`-local argument. The named residue:

> **(K-slide-cl)** *(class-uniform; supersedes the per-member (K-slide),
> which is now witness-decidable and discharged at every probed
> member)* — for every tight/(K-res) habitat shape `(G°, ℓ, e₀)` without
> parallel `G°`-edges, generic decorations of the slide-in limit system
> satisfy (W1)–(W4).

Every attempted member closed at the first sampled decorations; a class
proof should factor the limit system's pure condition along `G°`'s
structure (the White–Whiteley 1987 mechanism, now aimed at a decorated
bar-and-body-like object with only pencil lines and chords). **That
factoring is now carried out in §(K-slide-cl)** (the tetrahedral
collapse): (K-slide-cl) is true-modulo-**(K-slide-comb)**, a purely
combinatorial assignment problem, solved by search at every probed
member.

### Verification

`notes/scripts/w4/kslide.py` (tracked; exact-ℚ, on top of `repin.py` /
`pitch.py`; every sampled object carries rank/dimension asserts).
Reproduce: `python3 notes/scripts/w4/kslide.py --k4 | --battery [0-3] |
--mixed | --flanks`. Per member it asserts: `def = 0`; the transfer
certificate ((T1)–(T3) via `pitch.transfer_probe`, internal asserts);
per witness (W1) `dim mot = 6|V_H| − 5|E_H|`, (W2) `dim V_bc(limit) =
3`, (W3) `z` defined, (W4) `Q(z_limit) ≠ 0` (hard everywhere except the
flank probes, which report); at `K4`/mixed the (S2) hub-level equality
of `V_bc` spans; at the parallel member the (W1) failure in both
supports with the stress's chain support and line rank printed.

**Confidence verdict: (S1) and the (S2) carrier proven-informally;
(K-pitch) at all 11 probed split-classes (7 members) proven-informally —
the `K4`/`W4` double-subdivision control habitats closed at every
split; the parallel-edge order-0 obstruction proven (full support) /
exhibited (reduced support); the uniform kernel still open — residue
(K-slide-cl), reduced by §(K-slide-cl) to (K-slide-comb), + (K-Λ) +
the `P21`-type shapes, with (K-wit)/(K-pitch-∞) the weakest exact
forms.**

## §(K-slide-cl) — the tetrahedral collapse: the class statement reduced to a combinatorial assignment problem

Sibling of §(K-slide), attacking the class-uniform residue its Step 5
named; standing notation inherited (`G°`, decorations, the split edge
`e₀ = bc` of length 3, witnesses (W1)–(W4), the limit-line dictionary of
(S2)). The route is the one §(K-slide) suggested — factor the limit
system along `G°`'s structure — made concrete by the **specialization
technique of White–Whiteley 1987** (the Theorem-2.18 proof: evaluate the
pure condition at an assignment of *one shared coordinate frame per
spanning tree*, so a single Laplace term survives), now run **inside the
decoration variety**, whose pencil/chord structure does not admit free
`k`-frame rows.

**Verdict (2026-08-04, fourth pass).** (i) The **collapse mechanism
(C1)–(C3) is proven-informally**: at a *tetrahedral collapse* decoration
— hubs placed on the four vertices of a coordinate tetrahedron by a
proper 4-coloring, panels/pencil directions/interior points chosen per
the transversal dictionary (C2) — every limit row becomes a scalar
difference equation in one of six basis-line coordinates, and
(W1)–(W2) become **pure combinatorics**: the six edge classes must be
forests, exactly three spanning trees and three two-component forests
each separating `b` from `c`; then `V_bc` = the span of the three
separating lines' opposite duals, and (W3)/(W4) close by an explicit
bracket monomial in `pt(a)` (C3). (ii) The **length dictionary is
complete** on the class (C0): tightness alone caps every path at length
6 (`def ≥ ℓ − 6`, interiors-as-singletons partition), and under
`hnoRigid` a length-6 path is impossible too (its complement branch
union is tight, hence a proper rigid subgraph; 5848/5848 machine sweep)
— so `ℓ ∈ {1,…,5}`, exactly the range (C2) covers. (iii) The pure
tetrahedral scheme has one genuine obstruction, located exactly: a
**length-2 path forces a tetra point into both end panels**, and at the
mixed-length member this pincers against the neighbouring pencil planes
(every pt-mode assignment dies — proven by the finite case check, C4);
the **meet-plane extension** (C4) repairs it (interior at
`M ∩ π(i,j,m)`, panels freed, one non-basis row absorbed by the exact
witness). (iv) With the extension, **the assignment problem is solved
and the collapse witness verified at all 7 probed members** — the full
§(K-slide) battery (`kslidecl.py`, exact-ℚ; 6 pure, 1 extended). What
remains class-uniform is the purely combinatorial residue
**(K-slide-comb)** (C5): existence of a coloring + assignment with the
forest/separator structure. (K-slide-cl) is therefore
**true-modulo-(K-slide-comb)** — the geometry is discharged; the gap is
a finite matroid-flavoured question per shape, with 4-colorability
*proven* for all-length-3 shapes (3-degeneracy from 5/6-sparsity) and
every probed shape solved by search.

**What would change this.** *For the mechanism:* an error in the
transversal calculus (C2) — machine-asserted per edge per member
(`klein(L, C) = 0` for every assigned basis line against every chain
line), with the V_bc-structure and Gram identities asserted globally.
*For the residue:* a shape where (K-slide-comb) is unsolvable — that
would blunt the tetrahedral basis there, not the route (the basis
configuration can be generalized; the meet-plane extension is the first
instance); a shape whose underlying simple graph is not 4-colorable
would do it structurally (excluded for all-length-3 shapes, open in
general). *For the class verdict:* a proof of (K-slide-comb) upgrades
(K-slide-cl) to proven-informally wholesale; a counterexample to
(K-slide-comb) forces a second-generation basis.

### Step C0 — the hub-level target, and dictionary completeness

By (S2), interior elimination is exact and the limit system is the
hub-level serial-chain system: bodies at the hubs of `G° − e₀`, one
constraint `m(u) − m(w) ∈ S_P := span(chain lines)` per edge `P`, i.e.
`6 − ℓ_P` scalar rows (for independent chain lines). Tightness
(`Σ_P ℓ_P = 6·c°(G°)`) makes the total row count `6|V°| − 9`, so
(W1) says the rows are independent (`dim mot = 9`), (W2) that the
kernel is trivial twists ⊕ a 3-dimensional `V_bc`.

Two elementary lemmas close the length bookkeeping:

- **(ℓ ≥ 7 is not tight.)** Putting a length-`ℓ` path's interiors in
  singleton parts and everything else in one part scores
  `6ℓ − 6 − 5ℓ = ℓ − 6`, so `def(G) ≥ ℓ − 6`: a tight graph has every
  path of length ≤ 6. (Machine: K4 lengths `(3;7,2,2,2,2)` has the
  tight count but `def = 1`.)
- **(ℓ = 6 forces a rigid complement.)** If `G` is tight with a
  length-6 non-split path, the branch union of all *other* paths has
  the tight count (`Σℓ` drops by `6 = 6·Δc°`), and any bad partition of
  it would lift to `G` at zero cost through the six interiors — so the
  complement is a proper **rigid** branch union and `hnoRigid` fails.
  (Machine: 5848/5848 tight W4-wheel shapes with a length-6 path fail
  `hnoRigid`.)

So on the tight-`hnoRigid` subclass `ℓ ∈ {1,…,5}` — the dictionary
below is complete. ((K-res) residual shapes waive `hnoRigid`, so they
may carry length-6 paths; those contribute **no** hub-level rows and
the mechanism is unchanged, but no parallel-free (K-res) member was at
hand to probe.)

### Step C1 — the six scalar systems

Let `E₁…E₄` be the vertices of a coordinate tetrahedron and
`L_ij := C(E_i ∨ E_j)` its six edge lines: a **basis** of `Λ²K⁴` with
`B(L_ij, L_kl) ≠ 0` iff `{i,j}, {k,l}` are **opposite** (disjoint). So
`x_L(v) := B(m(v), L)` are linear coordinates on twists, and a
constraint `m(u) − m(w) ∈ S_P` whose reciprocal space
`R_P := {ω : B(ω, C) = 0 ∀C ∈ S_P}` is *spanned by basis lines*
`A_P ⊆ {L_ij}` reads as the `|A_P|` scalar equations

> `x_L(u) = x_L(w)`, one per `L ∈ A_P`.

If every edge is basis-aligned this way, the whole hub-level system
splits into **six scalar graph systems**: for each basis line `L`, the
class `E_L := {P : L ∈ A_P}` constrains `x_L` to be constant on the
components of `(V°, E_L)`. Hence, exactly:

> **(C1)** rows independent ⟺ every class is a **forest**; then
> `dim ker = Σ_L c_L` (`c_L` = component count), and since
> `Σ_L (c_L − 1) = 3`: **(W1) ∧ (W2)** ⟺ three classes are spanning
> trees and three are two-component forests **each separating `b` from
> `c`**; in that case `V_bc = ⟨ opp-dual(L) : L separating ⟩` (the
> B-dual basis vector of `L_ij` is proportional to its opposite line).

This is the White–Whiteley tree-specialization structure: the surviving
"Laplace term" is the product of the six forest determinants, evaluated
inside the pencil-decoration variety rather than at free `k`-frame
rows.

### Step C2 — the transversal dictionary (which alignments the chart allows)

Color the hubs `φ: V° → {1,…,4}` **properly** (adjacent hubs distinct,
`φ(b) ≠ φ(c)` — `b, c` are non-adjacent in `G° − e₀` by
parallel-freeness, but (C3) needs their points distinct) and place
`pt(u) = E_{φu}`. Per edge `P = uw` of length `ℓ`, colors
`(i, j) = (φu, φw)`, the chain lines can be decorated so that `R_P` is
*exactly* a basis-line span (each claim = one transversal computation;
all machine-asserted per edge):

    ℓ = 1 : chord L_ij; panels of u, w both contain it (mutual-panel
            data).                     A_P = all five basis lines ≠ opp(ij)
    ℓ = 2 : interior at E_k (k ∉ {i,j}), forced into BOTH panels; chain
            (L_ik, L_kj).              A_P = {ij, ik, jk, opp(ij)}
    ℓ = 3 : P_u = Π(u) ∩ π(i,j,s), chord L_ij, P_w = Π(w) ∩ π(i,j,t).
                                       A_P = {ij, it, js}
    ℓ = 4 : middle at E_k, P_u ⊂ π(i,k,l), P_w ⊂ π(j,k,l) ({k,l} =
            complement).               A_P = {ij, opp(ij)} (forced)
    ℓ = 5 : middles at E_k and a generic point of π(i,j,k); pencil ends
            generic in their panels.   A_P = {ij} (forced)

The ℓ = 3 computation is the exemplar: a line through `E_i` meets
`L_js` iff it lies in `π(i,j,s)`, so the class prescription *forces*
`P_u = Π(u) ∩ π(i,j,s)` — the transversal set of the serial triple is
`pencil(E_i, π(i,j,t)) ∪ pencil(E_j, π(i,j,s))`, spanning exactly
`⟨L_ij, L_it, L_js⟩`. (Same-color chords of different edges coincide as
lines; that is harmless — dependencies live inside classes, and classes
are forests.)

### Step C3 — (W3)/(W4) at the collapse: the bracket monomial, and finiteness of the local type

With separators `{L¹, L², L³}` and duals `D_s ∝ opp(L^s)`,
`Q|_{V_bc}`'s Gram is nonzero exactly on opposite dual pairs — so the
separator triple must contain **exactly one opposite pair** (no pair ⟹
`Q|_{V_bc} ≡ 0` ⟹ that witness fails (W4); two pairs don't fit in a
triple). Then `Q|_{V_bc}` has the serial-chain signature (rank 2), and
with `pt(a)` on the meet line `M = Π(b) ∩ Π(c)`, `z` is the cross
product of the rows `(B(D_s, C_ab))_s, (B(D_s, C_ac))_s` — 4-point
brackets. Exemplar (the type found at `K4`, separators
`{L₁₂, L₁₃, L₂₄}`, `φb = 1, φc = 2`; structural zeros from
`E₁ ∈ D₃ = L₁₃`, `E₂ ∈ D₂ = L₂₄`):

> `Q(z) = 2·[3,4,a,1]·[2,4,a,1]·[3,4,a,2]·[1,3,a,2]·[2,4,1,3]`

— a bracket **monomial** again (the Step-5 pattern one level up),
nonzero iff `pt(a)` avoids the four tetrahedron faces: generic on `M`.
Crucially, (W3)/(W4) depend only on the **local type** (separator
triple, `φb`, `φc`, the `b`/`c` panels and `pt(a)`) — *not* on the
shape — so their nonvanishing is a **finite** check over types, not
part of the per-shape combinatorics. (Machine corroboration: members
with the same type produce byte-identical `Q(z_lim)` under the same
panel draws.)

### Step C4 — the length-2 pincer, and the meet-plane extension

The ℓ = 2 alignment is the one dictionary entry that **constrains the
panels**: `E_k` must lie in both end panels. At the mixed-length member
(`K4`, lengths `(3;4,2,3,3,3)`) this is fatal: in either admissible
coloring, the forced panel point's color collides with the color of a
neighbouring ℓ = 3 edge's far end, degenerating that edge's pencil line
onto its chord (`E_j ∈ Π(u)` forces `P_u = Π(u) ∩ π(i,j,s) = L_ij` for
*every* `s`) — both colorings die, all pt-mode assignments fail (a
finite check, confirmed by exhaustive search). The repair keeps the
class structure and frees the panels:

> **(meet-plane mode)** place the ℓ = 2 interior at
> `x₁ = M_uw ∩ π(i,j,m)` (`m ∉ {i,j}`). Both chain lines then lie in
> `π(i,j,m)`, so `A_P ⊇ {ij, im, jm}` — three aligned rows — and the
> fourth row is non-basis ("extra"). The aligned kernel grows to
> `9 + z` (`z` = number of meet-plane edges, budget
> `Σ(c_L − 1) = 3 + z`), and the `z` extra rows must cut it back to 9
> with `dim V_bc = 3` — checked by the **exact witness itself** (which
> is all (S1) consumes; `V_bc ⊆ ⟨opp duals of separating classes⟩`
> remains a theorem and is asserted).

Local compatibility (part of the assignment problem): forced panel
points must avoid the far-end colors of ℓ = 3 edges at the same hub,
and each ℓ = 4 edge needs an admissible middle point
(`{k,l} ⊄ req(u) ∪ req(w)`).

### Step C5 — (K-slide-comb), what is proven, and the battery

> **(K-slide-comb)** *(the class-uniform residue; per shape a finite
> problem)* — for the shape `(G°, ℓ, e₀)`: there exist a proper
> 4-coloring `φ` of the simple graph underlying `G°` **+ e₀** (so
> `φb ≠ φc`) and per-edge choices (C2/C4: `k` or meet-plane `m` at
> ℓ = 2; `s, t` at ℓ = 3) satisfying the local compatibility rules,
> such that the six classes are forests with excess `3 + z`, at least
> three classes separate `b` from `c` (exactly three spanning trees +
> three separating 2-component forests when `z = 0`), the separating
> lines contain an opposite pair, and (for `z > 0`) the extra rows cut
> the aligned kernel exactly.

Proven pieces: **4-colorability holds for every all-length-3 shape** —
5/6-sparsity of the subdivision gives `|E(K)| ≤ 2|W| − 2` for every
subgraph `K` of `G° + e₀` (up to the one extra edge), so min degree ≤ 3
in every subgraph: 3-degenerate, greedily 4-colorable. (General
lengths: the same sparsity gives only weak degeneracy bounds;
4-colorability is open there and is *part of* (K-slide-comb) — as is
the option of replacing the tetrahedron by another basis configuration
if a shape ever needs it.) The battery (`kslidecl.py`, all exact-ℚ;
same members as §(K-slide) Step 4):

| member | mode | separating classes | witness |
|---|---|---|---|
| dbl-subdiv `K4` | pure | {12},{13},{24} | (W1)–(W4) ✓ |
| `W4` rim split | pure | {12},{14},{23} | ✓ |
| `W4` spoke split | pure | {12},{14},{23} | ✓ |
| `K5 − {01,23}`, split 02 | pure | {12},{13},{24} | ✓ |
| prism + diagonal, split 01 | pure | {12},{14},{23} | ✓ |
| `K4` mixed `(3;4,2,3,3,3)` | meet-plane (z = 1) | {12},{13},{24} | ✓ |
| `K4` + hub-hub edge | pure | {12},{14},{23} | ✓ |

Each collapse witness realizes as an honest chart point (interiors
along the chosen pencil rays, `pt(a) ∈ M` — the chart's own
constraints are exactly the dictionary's), so (S1) applies verbatim:
each row of the table *re-closes* that split by a structural witness —
and the class program now stands or falls with (K-slide-comb) alone.

### Verification

`notes/scripts/w4/kslidecl.py` (tracked; exact-ℚ, on top of
`repin.py`/`pitch.py`/`kslide.py`; every sampled object carries
rank/dimension asserts). Reproduce:
`python3 notes/scripts/w4/kslidecl.py --k4 | --battery [0-3] | --mixed |
--hubhub | --scope`. Per member it asserts: `def = 0`; per edge the
chain-span dimension, independence of the assigned basis lines, and the
transversal identities `klein(L, C) = 0`; globally (W1) (subdivision-
level row independence), (W2) with the `V_bc` structure identity
(equality to the separators' opposite-dual span in pure mode,
containment in extended mode) and the Gram-structure identity (pure
mode), (W3), and (W4) `Q(z_lim) ≠ 0`. `--scope` validates both
dictionary-completeness lemmas (the `def = ℓ − 6` exemplar; the
exhaustive length-6 sweep).

**Confidence verdict: the collapse mechanism (C1)–(C4) and the
dictionary-completeness lemmas proven-informally; (K-slide-cl)
true-modulo-(K-slide-comb) — geometry discharged, the residue purely
combinatorial, solved by search at all 7 probed members (6 pure
tetrahedral, 1 meet-plane extended); 4-colorability proven for
all-length-3 shapes; (K-slide-comb) in general, and the (K-res)
length-6 flank, open.**

## §(K-bare-ext) — stub

The minimal open statement isolated by the (K-bare) extension-route recon:
the arbitrary-seed insertion lemma, with the def-equal caveat folded into its
`∃` as a line-avoidance side condition. Statement, the corank stratification
that produced it, the DZ/cube/Wagner danger gadgets and the option-C probe
results are in `notes/Phase39-design.md` §"(K-bare) extension-route recon".

**Scope note (2026-08-02).** W4 routes 1/3 do **not** touch this kernel: a
residual is feasible by hypothesis, so the split producer's `hbareSplit`
branch is unreachable there — §"widened kernels (routes 1/3)" *Step 0*.

**What the (K-tight) re-pin settles for this statement (2026-08-02,
pointer-level).** Its named prerequisite — the KT pp. 684–691 boundary-load
re-pin — is **done** (§(K-tight) Steps 0–2), and the calculus is exact at
*any* target-rank seed, not just chart-generic ones. Consequences for the
eventual statement:

- The right shape is the **determinantal criterion**: at a target-rank bare
  seed, a placement attains ⟺ the two functionals `⟨·, C(va)⟩, ⟨·, C(vb)⟩`
  are independent on the seed's obstruction space `U`, with
  `dim U = dim R_a + 1` forced (`= corank(G′) − s₀ + 1`); higher corank
  makes the failure locus thinner (rank-≤1 of a `2 × dim U` matrix of
  linear forms), matching the C2/C3 corank-stability observations.
- The C3 gloss "the failure set is exactly the line" is **corrected**: on
  the `dim U = 2` stratum the route-A failure locus is
  `line(a,b) ∪ P′` — a second line, exhibited at the control
  (§(K-tight) Step 3). The `∃`-form side condition survives unchanged; a
  `∀`-form "off-line ⟹ attains" would be false.
- The genuinely open core is now sharply two-part: (i) at an adversarial
  IH seed, show `dim R_a ≥ 1` — some `G′`-stress engages the fresh-edge
  fiber; a `dim R_a = 0` seed fails at **every** placement — and (ii) a
  rank-2 point exists in the confinement space (the criterion's
  non-vanishing at that seed), with no chart available to supply
  genericity for either part.

**Verdict: open.** To be filled by the dispatch that attacks it; nothing is
being developed here yet.
