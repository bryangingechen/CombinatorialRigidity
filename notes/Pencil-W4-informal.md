# PENCIL — W4 residual-arc informal mathematics workbook

**Purpose.** The **W4 (`hcontract`) residual arc** of Phase 39 (PENCIL), split
out of `notes/Pencil-informal.md` (2026-08-05) so that a kernel-(K) research
pass reads only live (K) material. Its three sections are closed **as
arguments** — `hnoGood'` vacuity REFUTED, (SAFE-RES) REFUTED with the successor
(SAFE-RES′) open, the routes-1/3 kernel widening PRICED — and all three are
live **as input to the eventual W4 build**: they carry the residual structure
theorem ((C7)/(C8) at a maximal cluster), the statement of (SAFE-RES′), the
statement of the widened kernel **(K-res)**, and the (E)/(E-loc)/(V) gap
inventory the route-3(b) adjudication is pinned on — **that inventory EMPTIED on
2026-09-02**: (T) proved (§(SAFE-RES) *Step TF5*), (E-loc) refuted and shown
unnecessary (§widened kernels *Steps EL4–EL6*), **(E-pair) proved** (*ibid.*
*Steps PR1–PR6* + *GW1–GW6*) and **(V)** with it. What is left for W4 is
**(K-res)** — a user call — and the build. They are kept at full
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
section's own *Step 4* had not inventoried. So (SAFE-RES′) reduces to **(E)** plus
the local choice **(V)**, and route 3's cost list drops from four items to three.
**(E)'s onward reduction to (E-loc) is DEAD** (2026-09-02, direction WELOC —
§"widened kernels (routes 1/3)" *Steps EL1–EL6*): **(E-loc) is REFUTED** by `T32`,
a `|V| = 32` residual with two *disjoint* count-dependent `C₄` cores, so (E) is
back to being the primitive gap — **open, and now known tight** (`f(V(T32)) = 4`).
Its successor target is **(E-pair)**, *two adjacent degree-`2` vertices*, which is
all the split arm consumes ((EL-6)) — and **(E-pair) IS NOW A THEOREM**
(2026-09-02, directions WPAIR + WGROW, ibid. *Steps PR1–PR6* and *GW1–GW6*): it
reduced to the **seed condition (PAIR-5)** ((PAIR-3)), and (PAIR-5) is settled
both ways on the **hub multigraph** — false as stated (`K₂,₃`, (GROW-5)), true
under the residual's own *no co-1 rigid set* clause ((GROW-4)). **(V) is a
THEOREM** with it ((PAIR-6)). So route 3's **non-user-call cost list is EMPTY**;
what is left is **(K-res)**, a user call, and the W4 build itself.

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
landed proof bodies, not docstrings). *For the successor:* **nothing is open
on it any more.** (E-pair) — all (S1)/(S2) consume ((EL-6)) — is a theorem
(*Steps GW1–GW6*), and (V) with it; what would change *that* is an error in
(PAIR-3), in the hub-model translation of *Step GW2*, or in the landed `hcard`
necessary condition (EL-1) it rests on. **(E) itself stays open and tight**
(`f = 4` at `T32`) but is no longer on any W4 path; **(E-loc)** is **refuted**
(§"widened kernels" *Step EL5*). **Not (T)** — that
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

- **(E)** `f(V(G)) ≤ 4` — **open, and the primitive gap again.** It *is* KT
  Lemma 4.5(i)'s conclusion, landed only under `hnoRigid`
  (`edgeBound_of_noRigid_of_degree_two`), which consumes `hnoRigid` at exactly
  one point — to make the `v`-avoiding edge fiber count-independent. **The
  (E-loc) route through that point is REFUTED** (2026-09-02, §"widened kernels"
  *Steps EL1–EL6*): at `T32` no degree-`2` deletion is count-independent, and the
  generalized bound `f ≤ 4 + κ(v)` reaches only `f ≤ 6` there. Numerics for (E)
  itself: 255/255 in the pool (max `f = 2`, `W19`/`S29` at `f = 2`) **and
  `f = 4` at `T32`, so (E) is tight**. Two direct attempts are known to leak:
  bounding `f(V(G))` by `f(S) + …` at a maximal cluster (`f(S)` of a dense rigid
  `H` is unbounded), and the local count above. The live successor is
  **(E-pair)** (*Step EL6*; the token is registered in §widened kernels' own `WK-`
  neighbourhood, **not** as (EL-6), which WELOC RETURNED unconsumed), which is weaker
  and is what (SAFE-RES′)'s (S1)/(S2) actually needs — **and (E-pair) itself is now
  REDUCED** to the seed condition (PAIR-5) (§widened kernels *Steps PR1–PR6*), with
  the `e₀ = 0` stratum PROVED ((PAIR-4)) and the sharpened threshold *"(E-pair)
  follows from `f ≤ 6`"* replacing (E)'s `f ≤ 4` — those are the W4 clauses, not
  §(K-bare-ext)'s window side conditions of the same name (L3).
- **(T)** `G` triangle-free — **PROVED** (*Steps TF1–TF5*). The recorded
  255/255 was **never** evidence for it (the sweep's feasibility certificate is
  L6b, which *requires* triangle-freeness, so a triangle-carrying residual can
  never appear in a certified sweep) and it is not what settles it: the proof is
  a two-case contraction argument on two **landed** feasibility transfers.
- **(V)** the local choice — **a THEOREM given (E-pair) and (T)** ((PAIR-6));
  what follows is the case analysis, whose two open residues WPAIR closed. (E) supplies a
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
    (`u, x₁, x₂, u'` resp. `u, x₁, x₂, x₃`), hence a proper rigid subgraph.
    **Both are now IMPOSSIBLE at a residual** (2026-09-02, direction WPAIR:
    §widened kernels (PAIR-6)) — that `C₄`'s outside boundary meets at most two
    hubs by (EL-1), making it a *seed*, which (PAIR-3) forbids. So **(V) is a
    THEOREM given (E-pair)**: no branch of a residual is of those shapes, and the
    demand this bullet used to make — *show that not every `≥ 2`-interior branch is
    of those two shapes* — is discharged.

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
difficulty class as `hK`**, plus §(SAFE-RES)'s (T) — **now a THEOREM** — and (V),
plus (E). **Step 3's reduction of (E) to (E-loc) is DEAD** (2026-09-02, direction
WELOC): **(E-loc) is REFUTED** by `T32` (*Steps EL1–EL6*), while **(E) itself
stands, open and now known tight**. (E)'s successor target is **(E-pair)** —
*every residual carries two adjacent degree-`2` vertices* — which is all the
split arm consumes ((EL-6)). **(E-pair) is now REDUCED** (2026-09-02, direction
WPAIR, *Steps PR1–PR6*): a residual violating it carries `f(V(G)) ≥ 7`
((PAIR-1)/(PAIR-4)), no residual carries a rigid set attached to `≤ 2` outside
hubs ((PAIR-3)), and what is left is the **seed condition (PAIR-5)**. **(V) is a
THEOREM given (E-pair)** ((PAIR-6)), so W4's non-user-call cost is that ONE
obligation.

**What would change this.** A residual split at which *no* target-rank `G′`
seed escapes (that would refute (K-res) and kill routes 1/3); a reading error
in `pencilPair_of_splitOff_of_habitat`'s `by_cases hfeas` branching (read from
the body, `Escape.lean:396–428`); or — for *Steps EL1–EL6* — an error in `T32`'s
certification (three independent rigidity oracles agree; both feasibility
verdicts are landed-lemma-backed) or in (EL-4)'s two-branch chain, whose every
step is asserted instance-by-instance by `weloc.py --brick`; or — for *Steps
PR1–PR6* — an error in (PAIR-1)'s double count (an exact identity, re-checked on
33 299 instances) or in (PAIR-3)'s monotone invariant, asserted at every step of
22 359 chain runs by `wpair.py --validate`. **Not** a residual
with no count-independent degree-`2` deletion: that is `T32`, and it is what the
last line of this paragraph used to ask for. **Not**, either, a residual with all
branches of interior length `≤ 1` produced by a sweep: (PAIR-5) is where such a
thing would have to live, and `wpair.py --hunt`'s cap is disclosed there.

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
else, so it collapses into **(E)** exactly like (S1)/(S2). **Annotated
2026-09-02 ((EL-6)): that is true of the landed PROOF, not of the OBLIGATION.**
The edge bound is used there only to contradict `E(G′) = univ`, and a residual
is `Simple`, so `|E| ≤ |α|(|α| − 1)/2` discharges it outright at the price of a
larger `β` headroom in the consumer-facing headline. **(E) has ONE real
consumer, (S1)/(S2), not two.** Also free at a
residual: `5 ≤ |V(G)|`, since a simple rigid subgraph needs `≥ 3` vertices
(`2` vertices give one edge, `def = 1`) and no-co-1 adds two more.

### Step 1 — the trace: where the settled (K) analysis consumes `noRigid`

Four points in `notes/Phase39-design.md` §"(K) route-1 gate" + §"(K)
non-constancy recon", each read from the design text against the landed lemma
it cites:

| # | consumption | producer | fate at a residual |
|---|---|---|---|
| K1 | `index(G) ≤ 4`, so the corank stratification is finite | `edgeBound_of_noRigid_of_degree_two` (`ReducibleVertex.lean:1270`) | = gap **(E)**, still open; **its (E-loc) route is REFUTED** (*Step EL5*), successor **(E-pair)** (*Step EL6*) |
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

> **(E-loc) is REFUTED — 2026-09-02, direction WELOC, *Steps EL1–EL6* below.**
> `T32` (`|V| = 32`) is a residual with **two disjoint count-dependent `C₄`
> cores**, so every `E(G − v)` is count-dependent ((EL-5)). The **other**
> obstruction shape is impossible ((EL-4)), so this is the only way it fails.
> **(E) itself is untouched** — `f(V(T32)) = 4` **exactly**, so (E) is also now
> known **tight** — and what dies is this route to it. The paragraphs below are
> the state *before* that landing, kept because their reduction is exact and
> because *Steps EL1–EL6* are read against it; every "255/255" in them is over a
> pool whose honest denominator for this question is **`0`** ((EL-5)'s
> disclosure).

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

*Three corrections this paragraph earned* (WELOC): **merging does not remove
shape 1** — it organizes it, and shape 1 is exactly what `T32` inhabits
((EL-3)); the brick is not merely *"all degree `≥ 3`"* but a hub `C₄`/`C₅`, and
it is **impossible** ((EL-3)/(EL-4)); and *"neither occurs anywhere in the
pool"* is true but empty, since **no** pool instance carries two dependent sets
at all. The `hfresh` half of the last sentence is also over-stated — that
consumer needs no edge bound ((EL-6)).

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

### Step EL1 — the landed inventory (job 2), and the hub-degree law

**The job-2 answer, stated as asked.** There is **no** landed declaration giving
(E-loc), and none giving a `noRigid`-free edge bound: `edgeBound_of_noRigid_of_
degree_two` (`ReducibleVertex.lean:1270`) and `no_rigid_edge_count` (`:330`) are
the tree's only two edge-count bounds and each consumes `hnoRigid` (the second
also minimality). But the sweep of that file's neighbours turned up **two landed
items that decide this direction**, each of which the workbook had been using in
only one of its two roles:

- **`isKDof_zero_of_cycle` (`Deficiency.lean:743`) / `cycle_isProperRigidSubgraph`
  (`Operations.lean:1082`)** — **every cycle of length `3 ≤ m ≤ D = 6` is rigid**,
  and inside a bigger simple graph is a *proper* rigid subgraph as soon as one of
  its vertices has degree `≥ 3`. `c4_isProperRigidSubgraph` (`Habitat.lean:211`)
  and `triangle_isProperRigidSubgraph` are its `m = 4` and `m = 3` cases. So a
  `C₅` core stands on exactly the landed footing the `C₄` cores of `W19`/`S29`
  do — which is why *Step EL5*'s refuting family is two-parameter, not one.
- **the `hcard` necessary condition read as a TRANSFER, not as a sweep test.**
  Every recorded use of `ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`
  (`Motive.lean:409`) in this arc tests a *contraction* for certified
  infeasibility. Composed with the `PencilNondegFeasible` existential
  (`Motive.lean:133`) it is instead a **structure theorem about the residual
  itself**, and that is the only input *Steps EL3/EL4* need:

> **(EL-1) Hub-degree law.** In a `PencilNondegFeasible` graph every hub has at
> most **two** hub neighbours — equivalently `G[hubs]` has maximum degree `≤ 2`.
> Hence a hub all of whose `G`-neighbours but two are outside `G[hubs]` has all of
> them of degree exactly `2` (`≤ 2` as non-hubs, `≥ 2` by 2EC).

*Proof.* `PencilNondegFeasible K G` is `∃ F normal point, IsNondegPencilRealization
…`; the landed necessary condition gives `(G.closedHubNbhd v).ncard ≤ 3` at every
`v ∈ V(G)`; and `closedHubNbhd v = {w | PencilHub w ∧ (w = v ∨ w ~ v)}`
(`Motive.lean:82`) contains `v` itself when `v` is a hub. ∎

This is WTRI's inventory lesson at one remove: the item was landed **and**
inventoried — but in one role only, and the missing role is the load-bearing one.
(A first corollary, free and used below: a feasible 2EC graph on `≥ 2` vertices
**has** a degree-`2` vertex, since min degree `≥ 3` would make every vertex a hub
with `≥ 3` hub neighbours.)

The `noRigid`-free Lean sibling *Step 3* proposes is still a one-commit
verbatim-prefix extraction and is still worth having with **(I)** as its
antecedent; what *Step EL5* removes is the reason to want it — no residual
supplies (I) at a degree-`2` vertex. (Lean hold: not built.)

### Step EL2 — the count identity, and the anatomy of a minimal dependent set

Write `f(W) = 5|E(G[W])| − 6(|W| − 1)` and call `W` **count-dependent** when
`f(W) > 0`. By `matroidMG_indep_iff` (`Deficiency.lean:163`) and `IsSparse`
(`BodyBar/TreePacking.lean:103`, `∀ E' ⊆ E, E'.Nonempty → |E'| + ℓ ≤ k|span E'|`)
that is exactly dependence of the `5`-fold fiber over `E(G[W])` in `M(G̃)`, and
`E(G − v)` is independent iff **no** `W ⊆ V(G) ∖ {v}` is dependent.

> **(EL-2)** (i) `f(W) = 5·c(G[W]) − |W| − 5·k(G[W]) + 6`, with `c` the cycle rank
> and `k` the number of components; for connected `W` this is `f(W) = 5c − |W| + 1`,
> so **`W` is dependent iff `|W| ≤ 5·c(G[W])`**. (ii) `f(V(G)) = corank(G̃) −
> def(G)`. (iii) A `⊆`-minimal dependent `W` is **connected**, has **min degree
> `≥ 2` in `G[W]`**, and is therefore **branch-closed**.

*Proof.* (i) substitute `|E| = |W| − k + c`. (ii) `5|E| = rank + corank` against
`rank = 6(|V|−1) − def` — the identity *Step 2*'s `corank(H) = index(H) + def(H)`
already used at a seed. (iii) if `u ∈ W` has `G[W]`-degree `d ≤ 1` then
`f(W ∖ {u}) = f(W) − 5d + 6 ≥ f(W) + 1 > 0`, contradicting minimality; if `W` were
disconnected, `f(W) = Σᵢ f(Wᵢ) − 6(k−1)` forces some component dependent. Min
degree `2` then drags every degree-`2` vertex's whole branch **and both hub ends**
into `W`, and every hub of `W` lies on `≥ 2` of `W`'s branches. ∎

(iii) is the same closure property `nogood_subdiv.rigid_vertex_sets` exploits for
rigid sets, so a residual's dependent sets are computable by the `2^#branches`
branch sweep rather than a `2^|V|` subset sweep; `weloc.py --validate`
cross-checks the enumeration against brute force (215 subdivisions, 533 minimal
dependent sets, 0 mismatches).

### Step EL3 — the two shapes, named exactly

(E-loc) fails at `G` iff **no degree-`2` vertex lies in every dependent set** —
equivalently in every *minimal* one, since every dependent set contains a minimal
one. So the obstruction is exactly one of

1. **shape 1** — two or more minimal dependent sets whose intersection carries no
   degree-`2` vertex (in particular two **disjoint** ones);
2. **shape 2** — a single dependent set carrying no degree-`2` vertex at all: a
   **brick**, every vertex of which is a hub.

*Step 3*'s supermodularity remark is what makes this list exhaustive, and its role
is worth stating precisely, because it does **not** remove shape 1. Two dependent
sets meeting in a nonempty independent set merge (`f(W₁ ∪ W₂) ≥ f(W₁) + f(W₂) −
f(W₁ ∩ W₂) > 0`), so the union of any intersection-connected family of minimal
dependent sets is dependent; what follows is that **two distinct components of
that family are two disjoint dependent sets**. Merging therefore *organizes*
shape 1 rather than killing it: (E-loc) fails the moment the family has two
components, and it can also fail with a connected family whose common part is
hub-only. Shape 2 in exchange collapses to a finite list:

> **(EL-3)** In a feasible `G` a brick is a **cycle** `C₃`, `C₄` or `C₅` **all of
> whose vertices are `G`-hubs**; in a residual (T) ((TF-5)) removes `C₃`, so it is
> a hub `C₄` or a hub `C₅`. Such a cycle is a whole component of `G[hubs]`, and
> **every neighbour of it outside it has degree exactly `2`**.

*Proof.* A minimal dependent `W` with no degree-`2` vertex has `W ⊆ hubs`, so
`G[W]` has max degree `≤ 2` by (EL-1) and min degree `≥ 2` and is connected by
(EL-2)(iii): a cycle `C_m`, with `f = 5m − 6(m−1) = 6 − m > 0` iff `m ≤ 5`. Each
of its vertices already has two hub neighbours inside, so by (EL-1) none outside;
the rest is (EL-1)'s corollary. ∎

### Step EL4 — **no residual carries a brick**: shape 2 is IMPOSSIBLE

> **(EL-4)** No residual contains a cycle of length `≤ 6` all of whose vertices are
> `G`-hubs. Equivalently, by (EL-3): **every count-dependent vertex set of a
> residual contains a degree-`2` vertex**, so shape 2 never occurs and (E-loc) can
> fail only through shape 1.

Call `S ⊆ V(G)` **shielded** when `G[S]` is rigid and every vertex of `V(G) ∖ S`
with a neighbour in `S` has `G`-degree `2`.

*Proof.* Let `B` be a hub cycle, `3 ≤ |B| = m ≤ 6`.

**(a) `B` is shielded and proper.** `G[B]` is the cycle itself: a chord would give each
of its two endpoints a **third** hub neighbour, contradicting (EL-1) — this is the uniform
reason, and for `m ≤ 5` (T) gives it too, a chord there being a triangle. `G[B]` is rigid by
`isKDof_zero_of_cycle` (`3 ≤ m ≤ 6 = bodyBarDim 3`); its boundary is degree-`2` by (EL-1)
(each `B`-vertex already has its two hub neighbours inside `B`); and `B ≠ V(G)`, since every
vertex of a cycle has degree `2` while `B ⊆ hubs`.

**(b) a shielded `S ≠ V(G)` whose contraction is SIMPLE has `hcard(G/S)`** — which is all
(c) needs, since it dispatches on non-simplicity first. Here `G/S := G.rigidContract
(G.induce S) r`, whose deleted edge set is *all* of `E(G[S])`, so no inner edge
survives as a loop at `v*`. Simplicity says no outside vertex has two
`S`-neighbours, so every outside vertex keeps its `G`-degree and its hub status.
Then: `v*`'s neighbours are exactly `S`'s boundary vertices, all of degree `2`,
hence non-hubs, so `closedHubNbhd(v*) ⊆ {v*}`; a boundary vertex is itself a
non-hub, so its closed hub-neighbourhood sits inside its `≤ 2` neighbours; and
every other vertex keeps its `G`-value, `≤ 3` by (EL-1). **So L6b's `¬hcard`
escape is closed** — which is the one thing a general rigid subgraph does not
give (at `W19`/`S29` it is exactly `¬hcard` that saves the core's contraction).

**(c) the chain.** Take `S` of **maximum cardinality among shielded sets `⊇ B`
with `S ≠ V(G)`** — the family is nonempty by (a). `G[S]` is a proper rigid
subgraph with `2 ≤ |S|`, so the residual's no-good-contraction clause applies at
`(G[S], r)`; by (b) and L6b (`pencilNondegFeasible_of_ncard_closedHubNbhd_le_
three_of_triangleFree`, `Steer.lean:1344`) a simple **and** triangle-free `G/S`
would be feasible. So one of:

- **`G/S` not simple** — some `x ∉ S` has two `S`-neighbours; shieldedness makes
  `deg_G x = 2`, so both its neighbours are in `S` and are distinct (`G.Simple`).
  `S ∪ {x}` is rigid (Ear Lemma, `j = 1`) and still shielded (`x` has no neighbour
  outside it), so maximality forces `S ∪ {x} = V(G)` — and then `G[S]` is a
  **co-1** rigid subgraph, which the residual's no-co-1 clause forbids.
- **`G/S` carries a triangle** — it passes through `v*`, since a triangle off `v*`
  is a `G`-triangle and (T) forbids that. Write it `v* x y`: `x ~ y`, both outside
  `S`, both attached to `S`, hence both of degree `2`, so `N(x) = {y, u}` and
  `N(y) = {x, u'}` with `u, u' ∈ S` and `u ≠ u'` (else `u x y` is a `G`-triangle).
  `S ∪ {x, y}` is rigid (Ear Lemma, `j = 2`) and shielded, so maximality forces
  `S ∪ {x, y} = V(G)`; then `V(G) ∖ S = {x, y}` and `G/S` is exactly the
  **spanning `C₃`** `v* x y`, simple and feasible by the landed-*sufficient*
  L7c-3 witness (`pencilPair_of_habitat_ncard_eq_three`) — a good contraction.

Both branches contradict the residual. ∎

Three remarks.

- **This is (C1)+(C5) freed from maximality.** *Step 2*'s (C1) (*no `T`-vertex has
  two `S`-neighbours*) and (C5) (*no triangle through `v*`*) are these two branches
  at a **maximal cluster**, where maximality supplies what shieldedness supplies
  here. A brick is typically *not* a maximal cluster — but it is shielded, and
  shieldedness is what those two arguments actually consume. No new mathematics.
- **Shieldedness is preserved because every vertex the chain adds has degree `2`
  with both neighbours inside**, so the boundary only shrinks. That is the engine,
  and it is why the chain cannot stall.
- **(T) is spent twice** — no hub `C₃` in (EL-3), and no triangle off `v*` here — so
  (EL-4) is a genuine consumer of WTRI's theorem, landed hours earlier. (The no-chord step
  is (EL-1)'s, not (T)'s; that matters only at `m = 6`, where a main diagonal is not a
  triangle.)

### Step EL5 — **(E-loc) is REFUTED**: the witness `T32`

> **(EL-5)** There is a residual with **no** degree-`2` vertex `v₀` making
> `E(G − v₀)` count-independent. `T32`: `|V| = 32`, `|E| = 38`, `f(V(G)) = 4`,
> `def(G) = 0`, girth `4`.

`T32` (`weloc.py --witness`; `two_core(4, 1, 4)`) is

- two **disjoint** `C₄` cores `c₀c₁c₂c₃` and `d₀d₁d₂d₃`;
- three hub poles per core, two on one core vertex and one on the opposite —
  `z₀, z₁` on `c₀`, `z₂` on `c₂`; `w₀, w₁` on `d₀`, `w₂` on `d₂` — all six of them
  hub **edges**;
- one ring through the six poles in the order `z₀ z₁ z₂ w₀ w₁ w₂`, carrying **4**
  interior vertices on each same-core leg and **1** on each cross leg.

Every clause of `hnoGood'` holds, each certified by the landed lemma the pool's
own classifier uses — the `W19`/`S29` standard, no middle zone:

| clause | verdict at `T32` |
|---|---|
| `Simple`, three or more vertices, `TwoEdgeConnected` | ✓ |
| `PencilNondegFeasible K G` | `hcard` ✓ and girth `4` ⟹ **L6b** (sufficient) |
| `∃` proper rigid subgraph | the two `C₄` cores (`c4_isProperRigidSubgraph`) |
| no co-1 rigid subgraph | the **only** proper rigid vertex sets are those two cores, at `4` vertices each against `30` |
| no good contraction | both contractions are **simple**, with `closedHubNbhd(v*) = {v*, z₀, z₁, z₂}` resp. `{v*, w₀, w₁, w₂}` of size **4** — infeasible by the landed **necessary** `hcard` |

and (E-loc) fails for the simplest available reason: `f = 2` at each core and the
cores are **disjoint**, so each of the 32 vertices misses one of them entirely.
All 22 degree-`2` vertices are additionally checked against the pebble game
directly (`0` count-independent deletions).

**Why the witness is this size** — the three constraints that fix it are also why
the pool never reached it:

- *three hub poles per core.* With two, `closedHubNbhd(v*) = 3` and L6b certifies
  the contraction **feasible**: a good contraction, no residual. This is (C6)'s
  budget — the first core that can break `hcard` at `v*` is a `C₄` whose two hubs
  are **opposite** — applied twice.
- *`≥ 4` interior vertices on a same-core leg.* The ear `c₀ – z₀ – [a] – z₁ – c₀`
  has `a + 2` interior vertices, and the Ear Lemma merges it into the core at
  `a + 2 ≤ 5`.
- *`f(V(G)) ≤ 4`.* In this family `f = 22 − (4a + 2b)`, and **every** instance with
  `f ≥ 6` came back `co-1` or `good-contraction`. `(a, b) = (4, 1)` is the smallest
  residual the family reaches, and it sits at `f = 4` **exactly**.

**Consequences, in the order they bite.**

- **(E) is NOT refuted — and is now known TIGHT.** `f(V(T32)) = 4` is precisely the
  bound (E) asserts, attained. The pool's maximum was `2` (`W19`, `S29`), so (E)
  could not previously be known sharp; it is, and *"`f(V(G)) ≤ 3`"* is false. What
  dies is the **route**, not the statement.
- **The local counting route to (E) is dead, and not by a hair.** Generalize the
  landed argument: for a degree-`2` `v` the `v`-avoiding fiber has `|E'(v)| =
  5(|E| − 2)` and `rank(E'(v)) ≤ 6(|V| − 2)` (its span avoids `v`), so
  **`f(V(G)) ≤ 4 + κ(v)`** with `κ(v)` its corank —
  `edgeBound_of_noRigid_of_degree_two` is the `κ(v) = 0` case, i.e. (E-loc). At
  `T32`, `κ(v) ∈ {2, 4}` and `min_v κ(v) = 2`, so the sharpest conclusion the
  argument can reach is `f ≤ 6` against a true value of `4`. **No care in choosing
  `v` recovers (E) here**, and no sharpening of the counting step does either:
  the argument's only free parameter is the deleted vertex.
- **It is a family, not a point.** `--hunt`'s `(m, a, b)` scan certifies **24** refuting
  residuals (`m ∈ {4, 5}`, `a ≥ 4`, `b ≥ 1`), `T32` the smallest — a `C₅` core works exactly
  as a `C₄` core does (`isKDof_zero_of_cycle`, *Step EL1*), and a `C₄` core and a `C₅`
  core coexist in one residual at `|V| = 33`.
- **(SAFE-RES′) is untouched at the witness.** `T32` is triangle-free (as (T)
  requires), carries 8 deep split vertices and 16 split-usable ones, and satisfies
  (E). Only the (E-loc) route dies.

**Cap and denominator disclosure — and the denominator is `0`, not `255`.** Of the
255 residual inhabitants of `saferes.py --prime` (all 255 certified STRONG, no
middle-zone contraction), **160 carry no count-dependent set at all** — (E-loc)
is then vacuous, every degree-`2` vertex works — and **95 carry exactly one**, in
which case (EL-4) makes (E-loc) automatic. **Zero carry two.** So the pool contains
**no instance of the only configuration that can decide the question**, and the
recorded 255/255 was never evidence about (E-loc): the honest denominator is `0`.
The reason is structural, not a size cap — `family_g` and `family_core_ring` each
build **exactly one** core cycle, and the random sweeps contribute no residual at
all (`--search`: `0` residuals from `584 + 343` random instances). **This is not
(T)'s blind spot and must not be described as one:** count-independence appears in
no feasibility certificate, so a sweep *could* have seen an (E-loc) failure — the
generator simply never built one. The pool's maximum `f(V(G)) = 2` against `T32`'s
`4` is the same gap seen from the arithmetic side.

### Step EL6 — the two consumers, the successor, and (V)

**Consumer 1 — (S1)/(S2) — needs strictly less than (E), and that is the successor
to aim at.** *Step 0* records that (E) reaches the split arm only through
`exists_adjacent_degree_two_pair_of_edgeBound` (`ReducibleVertex.lean:1068`),
whose conclusion is *two adjacent degree-`2` vertices*. So the honest obligation is

> **(E-pair)** *every residual carries two adjacent degree-`2` vertices*,

which is implied by (E) and is what the arm consumes. It holds at **255/255** of
the pool (`--prime`, recorded) and at `T32` — **but that figure is not evidence**
(WPAIR, (PAIR-1)): ¬(E-pair) forces `f ≥ 6` while the pool's maximum is `2`, so the
honest denominator here is **0** too and the 255/255 merely restates `f ≤ 4`.
Unlike (E), it is a statement
about branch lengths, where the Ear Lemma and the no-good-contraction clause are
already the working tools (*Step EL4* is a worked example of exactly that pair of
tools). **This is the pick the direction recommends**: it dominates (E) on cost and
loses nothing on the split arm.

**Consumer 2 — `hfresh` — is NOT really an (E) consumer.** *Step 0* records that
the wrapper's discharge `freshEdgeSupply_of_card_lt_of_noRigid_of_degree_two`
(`Escape.lean:516`) *"calls `edgeBound_of_noRigid_of_degree_two` and nothing else,
so it collapses into (E)"*. True of the **landed proof**; not of the **obligation**.
Read the body: the edge bound is used only to contradict `E(G') = univ` under the
headroom `6(|α| − 1) < |β|`. A residual is `Simple`, so distinct edges have
distinct endpoint pairs and `|E(G)| ≤ |α|(|α| − 1)/2` outright — so the
residual-habitat sibling is discharged by **simplicity plus a larger `β`
headroom**, with no edge bound at all. The cost is a bigger constant in the
consumer-facing headline `pencil_conjecture_of_hcontract_hK_hbareSplit_of_card`,
which is a hypothesis of that headline and freely strengthenable. **So (E) has one
real consumer, not two**, and *Step 0*'s sentence is annotated accordingly.

**(V), i.e. job 3 — the premise is void and the answer is "unchanged".**
**SUPERSEDED 2026-09-02 by (PAIR-6): (V) is a THEOREM given (E-pair)**, its two
`C₄`-carrying residues being *seeds* that (PAIR-3) forbids. What follows is WELOC's
state, kept because its closing sentence — that (V) and (E-pair) share one upstream
target — is exactly what WPAIR then cashed. Job 3
asked what (V) costs *once (E) lands*; (E) did not land, and (E-loc) — the route
it was to land by — is refuted. So (V) stays *"elementary given (E) and (T)"* with
(T) discharged and (E) open, and its two `C₄`-carrying residues (`j = 3` with
`u = u'`; `j = 2` with `u ~ u'`) are exactly as *Step 3* left them. Two things are
worth recording anyway. First, **(V) holds outright at `T32`** by *Step 3*'s
`j ≥ 4` branch (the same-core legs carry 4 interior vertices), so the refutation
costs (V) nothing. Second, **(V)'s dependence on (E) is only through (E-pair)'s
neighbourhood**: *Step 3* uses (E) to produce a branch with `j ≥ 2` interior
vertices (via the (E-κ) arithmetic, `κ ≤ 1 ⟹ f ≥ 6 > 4`), which is again a
branch-length statement — so **(E-pair)-style work serves (V) too**, and the two
remaining non-user-call W4 items now share a single upstream target.

**What did NOT move.** (T) ((TF-1)–(TF-6)) is untouched and is used three times
here. (SAFE-RES) stays refuted, (SAFE-RES′) open with `W19`/`S29` intact; the
`hnoGood'` vacuity refutation stands (`T32` is a third inhabitant, and the first
with two cores). (K-res), *Step 4*'s minimal widened statements, *Step 5*'s
numerics and the route-3/packaging-(b) adjudication are all untouched — (E-loc)
was never an input to them. Nothing on the (BE-14) side is touched.

### Step PR1 — the landed inventory (job 2), and the deficit identity

**The job-2 answer, and this time the find is on the target itself.**
`ReducibleVertex.lean` carries **five** producers of "two adjacent degree-`2`
vertices", of which *Step EL6* had inventoried one:

| producer | what it consumes beyond `Loopless`/2EC/`3 ≤ \|V\|` |
|---|---|
| `exists_adjacent_degree_two_pair` (`:893`) | `IsMinimalKDof n 0` **and** no proper rigid subgraph |
| `exists_adjacent_degree_two_pair_of_edgeBound` (`:1068`) | **only** the edge bound `hedge` — the consumer *Step EL6* found |
| `exists_adjacent_degree_two_pair_of_noRigid_of_deficiency_pos` (`:1206`) | no proper rigid subgraph, `def(G̃) > 0` |
| `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two` (`:1384`) | no proper rigid subgraph, one degree-`2` vertex |
| `edgeBound_of_noRigid_of_degree_two` (`:1270`) / `no_rigid_edge_count` (`:330`) | the two edge bounds themselves, both `hnoRigid`-consuming |

Read `:1068`'s hypothesis in the arithmetic this section uses: `hedge` is
`(D−1)·|E| < D·(|V| − 1) + (D−1)`, i.e. at `D = 6` exactly `f(V(G)) ≤ 4` — **`hedge`
IS (E)** of §(SAFE-RES) *Step 3*, not a weaker relative of it. And read `:893`'s
**body**: its proof of (E-pair) is a double count over `X₂ = {deg = 2}` and
`X₃ = V ∖ X₂` — independence of `X₂` forces `Σ_{X₂} deg ≤ Σ_{X₃} deg` (each edge
has at most as many `X₂` ends as `X₃` ends), hence `Σ deg ≥ 4|X₂|`, which with
`Σ deg ≥ 2|X₂| + 3|X₃|` contradicts the edge bound. So the arc was not missing a
*lemma*: it was missing the observation that **the landed proof of (E-pair) is a
counting argument whose only rigidity input is an edge bound**, and that the count
can be made **exact**.

> **(PAIR-1) Deficit identity.** Let `G` be simple with `2 ≤ deg v` for every
> vertex (e.g. 2EC), and suppose its degree-`2` vertices form an **independent
> set** — the exact negation of (E-pair). Write `W` for the hubs (`deg ≥ 3`; under
> 2EC exactly the non-degree-`2` vertices, and exactly `PencilHub`,
> `Motive.lean:73`), `Λ := G[W]` for the **hub graph**, `e₀ := |E(Λ)|` and
> `σ := Σ_{v ∈ W} (deg v − 3) ≥ 0`. Then `W ≠ ∅` and
>
> `f(V(G)) = 5|E| − 6(|V| − 1) = 6 + e₀ + 2σ`.
>
> Hence **`f(V(G)) ≥ 6 + e₀ ≥ 6`**, with `f = 6` iff `e₀ = σ = 0`, i.e. iff `G` is
> the **full subdivision of a 3-regular multigraph**.

*Proof.* `W = ∅` would make every vertex degree `2` and every edge join two of
them, contradicting independence (with `V ≠ ∅`), so `W ≠ ∅`. Let `n₂ = |V ∖ W|`
and `D = Σ_{v ∈ W} deg v = 3|W| + σ`. Every edge has at least one hub end, so
`|E| = e₀ + (#hub–non-hub edges)`; each degree-`2` vertex contributes exactly `2`
of the latter, so `|E| = e₀ + 2n₂` and `D = 2e₀ + 2n₂`, i.e. `n₂ = D/2 − e₀`.
Substituting into `f` gives
`f = 5(e₀ + 2n₂) − 6(|W| + n₂ − 1) = 4n₂ + 5e₀ − 6|W| + 6`, and then
`= 2D + e₀ − 6|W| + 6 = 2σ + e₀ + 6`. ∎

Three consequences, in the order they bite.

- **(E-pair) follows from `f(V(G)) ≤ 5`** — *strictly weaker than (E)*, which is
  `f ≤ 4`. The landed `:1068` consumes the stronger form, and its own proof does
  not need it: the two inequalities `Σ deg ≥ 4|X₂|` and `Σ deg ≥ 2|X₂| + 3|X₃|`
  already give `f ≥ 6` (put `x₂ ≤ Σdeg/4` and `x₃ ≤ (Σdeg − 2x₂)/3` into
  `f = (5/2)Σdeg − 6(x₂ + x₃) + 6`). So `hedge` could be weakened by one unit —
  a **one-unit slack in a landed statement**, not a gap, recorded because the
  successor leaf will want the weakest antecedent available.
- **The obligation is a branch-length statement about an over-braced graph.**
  ¬(E-pair) says every branch has `≤ 1` interior vertex; (PAIR-1) says such a `G`
  carries `f ≥ 6`, whereas every residual ever exhibited sits at `f ≤ 4` (`T32`,
  §widened kernels *Step EL5*, attains `4`). So a counterexample to (E-pair)
  would also refute **(E)** — which is why the pool decides nothing here
  (*Verification*, `wpair.py --pool`).
- **The regime is the opposite of (E-loc)'s.** (E-loc) failed because a residual
  can carry *two* small dependent cores; (E-pair) can fail only if the residual
  is dependent *everywhere at once* (`f ≥ 6` against `f(V) = corank − def`,
  (EL-2)(ii)).

**The standing job-2 verdict, asked for after three directions.** There **is** a
systematic gap, and it has one shape: *the arc inventories landed CONCLUSIONS and
mis-reads landed HYPOTHESES.* WTRI found two landed feasibility **transfers**
omitted because the inventory had enumerated only *criteria*; WELOC found
`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization` used only as a
contraction **test** and `isKDof_zero_of_cycle` cited only at `m = 4`; this
direction finds a whole **family** of (E-pair) producers behind the one that was
cited, and finds that the cited one's `hedge` is (E) verbatim — a hypothesis the
arc had been describing as "an edge-count hypothesis". The common cause is that
the workbook cites declarations by the *role they played when first needed*, and
that role is recorded in prose rather than re-derived from the signature. The
cheap standing fix, which all three directions did by hand: **before declaring an
obligation unprovable from the landed set, `grep` the owning file for every
declaration whose NAME contains the obligation's conclusion, and read each one's
hypotheses in the arc's own arithmetic** — not its docstring. Two of the three
finds would have been impossible to miss under that rule; the third (the
`hcard` transfer) needs the composition step and is genuinely harder.

### Step PR2 — the contraction criterion at a general rigid set

§`hnoGood'` vacuity *Step 2*'s (C1)–(C6) describe a **maximal** cluster and (EL-4)(b)
a **shielded**
set. Both are instances of one criterion, which is what the rest of this direction
runs on, and which needs no maximality and no branch-length hypothesis.

> **(PAIR-2) Contraction criterion.** Let `G` be simple and feasible, `U ⊆ V(G)`
> with `G[U]` rigid, `3 ≤ |U|`, `U ≠ V(G)`; write `∂U` for the vertices outside
> `U` with a neighbour in `U`, and `∂_hub U ⊆ ∂U` for those that are hubs. Set
> `G/U := G.rigidContract (G.induce U) r` (`ReducibleVertex.lean:1461`; the
> induced subgraph, so every inner edge is deleted and none survives as a loop).
> Then:
>
> (i) **closure.** Every degree-`2` vertex of `U` has **both** neighbours in `U`,
> and every `u ∈ U` with a neighbour outside is a **hub**.
> (ii) **simplicity.** `G/U` is simple iff no `x ∈ ∂U` has two `U`-neighbours.
> (iii) **`hcard`.** If `G/U` is simple then `hcard(G/U)` holds **iff**
> `|∂_hub U| ≤ 2`.
> (iv) **triangles.** If `G/U` is simple then `G/U` is triangle-free iff `G` has
> no triangle avoiding `U` and no two vertices of `∂U` are adjacent.
>
> Consequently, with (T) ((TF-5)) in hand: `G/U` is a **good contraction** as soon
> as no `x ∈ ∂U` has two `U`-neighbours, no two `∂U`-vertices are adjacent, and
> `|∂_hub U| ≤ 2` — the first two by L6b's simplicity/triangle-freeness inputs,
> the third by L6b's `hcard` input
> (`pencilNondegFeasible_of_ncard_closedHubNbhd_le_three_of_triangleFree`,
> `Steer.lean:1344`).

*Proof.* (i) `deg_{G[U]} v ≥ 2` by **(R1)** (`two_le_degree_of_isKDof_zero`,
`Deficiency.lean:1306`), so a degree-`2` vertex of `U` spends both edges inside;
and `u ∈ U` with an outside neighbour has `deg_G u ≥ deg_{G[U]} u + 1 ≥ 3`.
(ii) is `rigidContract`'s definition: the only possible multi-edge is a pair
`x–u`, `x–u'` with `u, u' ∈ U`. (iii) In a simple contraction every outside vertex
keeps its `G`-degree, hence its hub status, and `v*`'s neighbours are exactly
`∂U`; so `closedHubNbhd(v*)` is `∂_hub U`, together with `v*` itself exactly when
`|∂U| ≥ 3`, of size `|∂_hub U| + [|∂U| ≥ 3]` — and `|∂_hub U| = 3` already forces
`|∂U| ≥ 3`. At a
boundary vertex `x` the unique `U`-neighbour `u` — a hub by (i) — is *replaced* by
`v*`, so `|closedHubNbhd(x)|` does not grow; every other vertex keeps its
`G`-value, `≤ 3` by (EL-1). So `hcard(G/U)` can fail only at `v*`, and there
exactly when `|∂_hub U| ≥ 3`. (iv) A triangle of `G/U` either avoids `v*` — then
it is a `G`-triangle avoiding `U` — or passes through `v*`, i.e. is a pair of
adjacent `∂U`-vertices. ∎

(EL-4)(b) is the case `∂_hub U = ∅` (*shielded*: all of `∂U` has degree `2`),
and (C4)/(C6) are (iii) read at a maximal cluster, where `∂_hub U` is the set of
boundary hubs. **The gain is that (iii) leaves TWO of the three `hcard` slots
free**: a rigid set may be attached to two outside hubs and still contract
feasibly.

### Step PR3 — the seed lemma: no residual carries a rigid set with `≤ 2` boundary hubs

> **(PAIR-3) Seed lemma.** Let `G` be a residual. Then **every** rigid
> `U ⊆ V(G)` with `3 ≤ |U|` and `U ≠ V(G)` has `|∂_hub U| ≥ 3`. Equivalently: a
> residual carries no *seed* — no proper rigid set attached to at most two outside
> hubs.

*Proof.* Suppose `U` is a seed. Among rigid `S ⊇ U` with `S ≠ V(G)` and
`|∂_hub S| ≤ 2`, take one of **maximum cardinality**; `|S| ≤ |V(G)| − 2`, since a
co-1 rigid set is forbidden outright. Now `G[S]` is a proper rigid subgraph with
`2 ≤ |S|`, so the no-good-contraction clause applies at `(G[S], r)`, and by
(PAIR-2) one of three things happens.

- **`G/S` not simple.** Some `x ∉ S` has two `S`-neighbours; `S ∪ {x}` is rigid
  (Ear Lemma, `j = 1`) and proper (`|S| ≤ |V(G)| − 2`, so `S ∪ {x} ≠ V(G)`). So
  maximality is contradicted, *provided the hub-boundary did not grow*: by
  (PAIR-2)(i) both of `x`'s `S`-neighbours are **hubs**, so if `x` is a hub it has
  already spent both of its (EL-1) hub slots inside `S` and contributes **no** new
  boundary hub; if `x` has degree `2` both its neighbours are now inside. Either
  way `∂_hub(S ∪ {x}) ⊆ ∂_hub S ∖ {x}`, so the invariant survives.
- **`G/S` carries a triangle.** By (T) it passes through `v*`: adjacent
  `x, y ∈ ∂S`, each with exactly one `S`-neighbour (the previous branch is
  exhausted), and those two neighbours are **distinct** — else `u x y` is a
  `G`-triangle. So `S ∪ {x, y}` is rigid (Ear Lemma, `j = 2`). If
  `S ∪ {x, y} = V(G)` then `∂S = {x, y}` and `G/S` is the **spanning `C₃`**
  `v* x y`, simple and feasible by the landed-*sufficient* L7c-3 witness
  (`pencilPair_of_habitat_ncard_eq_three`, `Base.lean:63`) — a good contraction,
  forbidden. Otherwise maximality is again contradicted, and again the
  hub-boundary does not grow: each of `x, y` that is a hub has its `S`-neighbour
  (a hub) plus possibly the other of the pair among its `≤ 2` hub slots, so it
  contributes at most one new boundary hub while itself leaving `∂_hub`; each of
  `x, y` of degree `2` has both neighbours inside afterwards.
- **`G/S` simple and triangle-free.** Then `hcard(G/S)` holds by (PAIR-2)(iii)
  (`|∂_hub S| ≤ 2`), so L6b makes `G/S` feasible: a good contraction, forbidden. ∎

Three remarks.

- **This is (EL-4) freed from shieldedness**, and it is the third freeing in one
  progression: (C1)+(C5) hold at a **maximal cluster**, (EL-4) replaced maximality
  by **shieldedness**, and (PAIR-3) replaces shieldedness by **two free `hcard`
  slots**. (EL-4) is the corollary at a brick, whose `∂_hub` is empty by (EL-3).
  No new mathematics — the same two ear moves and the same three landed
  feasibility verdicts.
- **The engine is now a monotone invariant, not a shrinking boundary.** What makes
  the chain work is that `|∂_hub ·|` **never increases** along either ear move, and
  that is a consequence of (EL-1) alone — every absorbed hub arrives with a hub
  neighbour already inside `S`. This needs no branch-length hypothesis, so
  (PAIR-3) is available to the whole arc, not only to this direction.
  **Confirmed and BOUNDED** (2026-09-02, direction WGROW, *Step GW6*): the
  non-increase holds at every one of 726 checked `j = 1` absorptions and is
  unconditional — but it is a property of **these two moves**, not of ear
  absorption in general. Absorbing a hub through **two subdivided branches** is
  an ear with `j = 3`, admissible for the Ear Lemma, and it can **strictly
  grow** `|∂_hub|` (241 witnesses, `wgrow.py --validate`). So the invariant
  carries (PAIR-3)'s chain and does **not** carry a general "grow until it is a
  seed" attack.
- **It kills configurations the arc had left open**: any rigid set whose hubs sit
  on a single connected segment of the hub graph `Λ` is a seed (a segment has at
  most two continuing ends), and so is any `C₄`/`C₅`/`C₆` whose hub run is long
  enough. *Step PR6* spends this on (V).

### Step PR4 — **(E-pair) holds when the hubs are independent**

> **(PAIR-4)** No residual `G` with `e₀ = 0` — hubs pairwise non-adjacent, i.e.
> `G` a **full subdivision** — violates (E-pair). Hence a residual violating
> (E-pair) has `e₀ ≥ 1` and, by (PAIR-1), **`f(V(G)) ≥ 7`**; equivalently
> **(E-pair) follows from `f(V(G)) ≤ 6`**, two units weaker than (E).

*Proof.* Let `U` be any rigid set with `3 ≤ |U| < |V(G)|` — one exists, since a
residual carries a proper rigid subgraph `H` (and `V(H)` is rigid too, `G[V(H)]`
having at least `H`'s edges; `|V(H)| ≥ 3` because a simple graph on two vertices
has one edge and `def = 1`). Then `∂_hub U = ∅`: an outside hub `w` adjacent to
`U` attaches at some `u ∈ U`, which is a hub by (PAIR-2)(i) — but `e₀ = 0` makes
hubs pairwise non-adjacent, a contradiction. So `U` is a seed, contradicting
(PAIR-3). ∎

Note what does the work: the closure (PAIR-2)(i) means the boundary of a rigid set
can only be reached through **hub–hub edges**, so `e₀ = 0` removes the obstruction
outright. This is exactly the stratum (PAIR-1) singles out as `f = 6` when the
hubs are additionally 3-regular, and it is the stratum a naive search reaches
first — every full subdivision probed is killed by a co-1 rigid subgraph or a
certified good contraction (`wpair.py --sub`, 220 instances, 173 836 rigid sets,
all with `∂_hub = ∅`).

### Step PR5 — what remains: the seed condition, and why it is finite-per-instance

Putting *Steps PR1–PR4* together, (E-pair) is **reduced**:

> **(PAIR-5) Seed condition.** *Every simple, 2EC, triangle-free graph whose
> closed hub-neighbourhoods have `≤ 3` members, whose degree-`2` vertices form an
> independent set, and which carries a proper rigid subgraph, has a rigid
> `U ⊆ V(G)` with `3 ≤ |U| ≤ |V(G)| − 2` and `|∂_hub U| ≤ 2`.*
>
> **(PAIR-5) ⟹ (E-pair)**, by (PAIR-3). It is a statement about the **hub graph
> `Λ` and the rigid sets of a partial subdivision** — no feasibility geometry, no
> deficiency beyond `def(G[U]) = 0` — and it is decidable per instance.
>
> **SETTLED, BOTH WAYS (2026-09-02, direction WGROW, *Steps GW1–GW6*).** As
> stated it is **FALSE**: `K₂,₃` is in the class, carries a proper rigid
> subgraph (its `C₄`) and has no seed ((GROW-5)) — and it is the **only**
> counterexample. Add either *no co-1 rigid set* or `6 ≤ |V(G)|` and it is a
> **THEOREM** ((GROW-4), the seed dichotomy). A residual supplies the first of
> those outright, so **(E-pair) is a theorem** ((GROW-6)) and so is **(V)**.
> The paragraphs below are the state of the question *before* that landing and
> are kept because the attack they name is what (GROW-4) replaces.

Why it is the right residual, and what is known about it.

- **`Λ`'s shape is pinned.** By (EL-1) `Λ` has max degree `≤ 2`, so its components
  are paths and cycles; by (EL-4) every **cycle** component has length `≥ 7`. And
  `∂_hub U` is exactly the set of outside endpoints of the `Λ`-edges leaving
  `U ∩ W` ((PAIR-2)(i)), so `|∂_hub U|` counts **dangling `Λ`-ends** of `U ∩ W`.
- **A sufficient criterion, free.** If `U ∩ W` is contained in one `Λ`-component
  and is `Λ`-connected (a sub-path), it has at most two dangling ends, so `U` is a
  seed. So a counterexample needs **every** rigid set's hub part to be spread
  across `Λ` with `≥ 3` dangling ends — while by ¬(E-pair) the graph is
  over-braced (`f ≥ 7`), which makes rigid sets *plentiful*. That tension is the
  content of (PAIR-5), and it is why the two conditions pull against each other.
- **Worked instance.** Take `Λ` an 8-cycle `z₁ … z₈` of hubs with the four
  "diameters" `z_i z_{i+4}` present as once-subdivided branches: `|V| = 12`,
  `|E| = 16`, `f = 14 = 6 + 8 + 0`, triangle-free, `hcard` (each `z_i` has exactly
  the two hub neighbours `z_{i±1}`), all branches of interior length `≤ 1`. The
  `C₆` `z₁z₂z₃z₄z₅ m₁₅` is rigid, and its hub part `z₁ … z₅` is a `Λ`-sub-path:
  `∂_hub = {z₆, z₈}`, a **seed**. So (PAIR-3) kills it — here through the co-1
  clause, the chain from that `C₆` reaching `|V| − 1`. Machine-asserted, not
  quoted (`wpair.py --hunt`'s first lines), and every candidate the sweep built
  dies one of the same three ways.
- **Numerics.** `wpair.py --hunt`: over 313 candidates (partial subdivisions of
  min-degree-3 multigraphs, all simple, 2EC, triangle-free, `hcard`, with an
  independent degree-`2` set), the seed condition held **313/313**, and `classify`
  returned `co-1` at 303 and `good-contraction` at 10 — **0 residuals**. **Cap:
  `≤ 16` branches** (`rigid_vertex_sets`' `2^{branches}` enumeration), i.e. `≤ 10`
  hubs at min degree `3`, and the pairing-model generator builds **no `Λ`-cycle of
  length `≥ 7`** — precisely the configuration (EL-4) leaves open. **This sweep
  proves nothing about all residuals** (F11): what proves is (PAIR-3)+(PAIR-4);
  the sweep only reports that the seed condition is not violated anywhere it could
  be tested.
- **What would settle it.** Either (a) a proof that some rigid set's hub part is
  `Λ`-connected — the natural attack is to grow a rigid set *along* a `Λ`-path
  using the Ear Lemma, since the branches hanging off a `Λ`-run have interior
  length `≤ 1` and an ear through `k` consecutive hubs has `≤ 2k − 1` interior
  vertices; or (b) a counterexample: a graph as in the worked instance whose every
  rigid set straddles `≥ 3` `Λ`-ends. **(b) would refute (E) as well** (`f ≥ 7`),
  which is the reason to expect (a). **Correction (2026-09-02, WGROW):** that
  last sentence holds only for a counterexample that is a **residual**. The
  actual counterexample ((GROW-5)) is `K₂,₃`, which is in the class but is not a
  residual and sits at `f = 6`, so it refutes the *statement* and says nothing
  about (E). And the settling route was neither (a) nor (b) but a third one —
  (GROW-4).

> **Both coordinator readings of this paragraph are now TESTED (2026-09-02,
> direction WGROW; `RESEARCH-ARC.md` §7).** **(i) CONFIRMED verbatim:** the
> `≤ 2k − 1` count holds under the convention that the ear **attaches directly
> at `z₁` and `z_k`**; with one attachment running through a subdivided branch
> it is `2k`, with both `2k + 1`. Against the Ear Lemma's `j ≤ 5`
> (§(SAFE-RES) *Step 1*, an **iff**) that caps **one** ear at **three**
> consecutive hubs — two if either attachment is subdivided — so attack (a)
> could only ever have been **iterated** short ears. **(ii) CONFIRMED and then
> some:** only the restriction of (PAIR-5) to residuals is consumed, and the
> restriction is not merely *sufficient* but **necessary** — the unrestricted
> statement is false ((GROW-5)), and the single clause that repairs it is the
> residual's *no co-1 rigid set*. **Both are superseded as an attack:**
> (GROW-4) proves the repaired statement without growing anything, by reading
> `|∂_hub| ≥ 3` off **every part of a minimum-excess partition at once**. Spec:
> `notes/Pencil-fanout.md` §"WGROW".

### Step PR6 — job 3: **(V) is a THEOREM given (E-pair)**, and the consumer state

> **(PAIR-6)** Given (E-pair) and (T), **(V)** — i.e. §(SAFE-RES′)'s (S1)–(S5)
> (its own clauses, **not** §(K-bare-ext)'s window conditions of the same name) —
> holds at every residual. In particular the two `C₄`-carrying residues
> §(SAFE-RES) *Step 3* left open are **impossible at a residual**.

*Proof.* (E-pair) supplies two adjacent degree-`2` vertices, i.e. a branch `β`
with `j ≥ 2` interior vertices `x₁ … x_j` and hub ends `u, u'` — exactly the input
§(SAFE-RES) *Step 3*'s case analysis consumes, and it discharges every case but three.
`j = 2` with `u = u'` is a triangle, killed by (T) ((TF-5)). The other two are
killed by (PAIR-3):

- **`j = 3` with `u = u'`.** `U := {u, x₁, x₂, x₃}` induces the chordless `C₄`
  `u x₁ x₂ x₃` (the `x_i` have degree `2`), rigid by `isKDof_zero_of_cycle`
  (`Deficiency.lean:743`) and proper because `deg u ≥ 3` gives `u` a neighbour
  outside. `∂U ⊆ N(u) ∖ {x₁, x₃}`, so `∂_hub U` is contained in `u`'s hub
  neighbours: **`|∂_hub U| ≤ 2` by (EL-1)**. Seed — contradiction.
- **`j = 2` with `u ~ u'`.** `U := {u, x₁, x₂, u'}` induces the `C₄`
  `u x₁ x₂ u'` (closed by the edge `u u'`), rigid and proper as above. Each of
  `u, u'` has the other among its `≤ 2` hub neighbours, so each contributes at
  most one outside boundary hub: **`|∂_hub U| ≤ 2`**. Seed — contradiction. ∎

So (V) does **not** need its own argument, and §(SAFE-RES) *Step 3*'s closing
sentence — *"a
full proof of (V) must show that not every `≥ 2`-interior branch of a residual is
of those two shapes"* — is discharged: **no** branch of a residual is of those
shapes. WELOC's *"(V) holds outright at `T32`"* is a **witness**; (PAIR-6) is the
**theorem**, and it holds for the same reason (EL-4) does.

**The consumer state after this direction.** (E) has one real consumer,
§(SAFE-RES′)'s (S1)/(S2) ((EL-6)); that consumer needs only (E-pair); (E-pair) is
reduced to (PAIR-5); and (V) — the other non-user-call W4 item — is now a theorem
*given the same (E-pair)*. **Updated 2026-09-02 (direction WGROW):** (PAIR-5) is
settled ((GROW-4)/(GROW-5)), so **(E-pair) is a theorem** ((GROW-6)) and with it
(V); **W4's non-user-call cost list is EMPTY**, and **(K-res)** — a **USER
call** — is the only open item left. (The `hfresh` consumer needs no edge bound
at all, (EL-6).)

### Step GW1 — the landed inventory (job 2): **the partition face of `deficiency`**

The standing verdict WPAIR returned — *the arc inventories landed CONCLUSIONS
and mis-reads landed HYPOTHESES* — was run here against a **new** consumer
surface: producers of rigid subgraphs and of ear/cycle extensions. It fires
again, and the find is larger than the previous three, because this time the
missing object is not a lemma but a **face of the central definition**.

`Graph.deficiency` is **defined** as a maximum over partitions
(`Deficiency.lean:273`): `def(G̃) = ⨆_f partitionDef(G, n, f)` with
`partitionDef = D(|P| − 1) − (D − 1)·d_G(P)` (`ibid.:262`, `numParts`
`ibid.:255`). At `D = 6` that reads

> `def(G̃) = max_P [ 6(|P| − 1) − 5·d_G(P) ]`, so **`G` is rigid iff every
> partition `P` of `V(G)` has `5·d_G(P) ≥ 6(|P| − 1)`**,

and the finest partition is exactly `−f(V(G))`. On top of it sits a whole
**Jackson–Jordán tight-partition layer**, landed in Phase 32 for the Jacobs
chapter and sitting in the same file this arc already cites for (R1) and
`isKDof_zero_of_cycle`:

| landed | what it says |
|---|---|
| `IsTightPartition` (`:1929`), `exists_isTightPartition` (`:1940`) | a partition attaining `def` exists |
| `partitionDef_merge` (`:1978`) | the exact arithmetic of collapsing a subfamily of parts |
| `IsTightPartition.subfamily_le` (`:2038`) | JJ Lemma 3.2(a): `(D−1)·e(Q) ≤ D(|S|−1)` on any subfamily |
| `IsTightPartition.parts` (`:2091`) | JJ Lemma 3.2(b): a part with `≥ 2` members has `≥ 3`, and every vertex of it has `≥ 2` in-part edges |
| `IsTightPartition.crossingEdgesWithin_pair_le_one` (`:2211`), `.eq_of_common_nbr` (`:2324`) | the cross-pair consequences |
| `deficiency_eq_zero_iff_exists_spanningTrees` (`:3083`) | rigidity as the `D`-tree packing |

**This whole file's W4 arc had cited none of it: `partitionDef` occurs 0 times
in `notes/Pencil-W4-informal.md`.** Every deficiency claim from §`hnoGood'`
vacuity onward is made through the *edge-count* face (`f = 5|E| − 6(|V| − 1)`,
the Ear Lemma's packing count, the pebble-game oracle). *Steps GW2–GW4* below
are nothing but the partition face applied to this arc's own class, and they
settle (PAIR-5).

**The standing verdict, sharpened.** WPAIR's diagnosis (*conclusions
inventoried, hypotheses in prose*) is correct but not the whole shape. The
sibling arc **had** read this object: `notes/Pencil-informal.md` cites
`Graph.partitionDef`/`Graph.deficiency` 16 times (direction BINDUC read the
bodies, and §(K-bare-ext) argues with `partitionDef₃` directly). So the gap is
**per-arc**, not per-project: *an object already read and used on one side of
the phase can still be missing from the other side's inventory, because each
section's citations are grown from what that section needed when it was
written.* The cheap fix that follows, and the one this direction ran: **before
declaring an obligation open, grep the SIBLING WORKBOOK for the Lean file you
are about to cite** — if the other arc reads more of that file than you do, the
difference is your inventory gap. Applying it here cost one `grep` and produced
the proof.

*Applied prospectively?* Partly, and honestly: this direction ran the
`grep`-the-owning-file rule **before** planning (it is what turned up the
tight-partition layer), but the sibling-workbook half is new — invented while
running the first half, not inherited. That is the evidence asked for: the
standing rule was absorbed, and it generated its own extension.

### Step GW2 — the hub-multigraph carrier: **(GROW-1)** and **(GROW-2)**

Fix a member `G` of (PAIR-5)'s class: simple, 2EC, triangle-free, `hcard`, and
with an **independent** degree-`2` set. Then every edge of `G` has a hub end
and every degree-`2` vertex has two hub neighbours, so `G` is the **partial
subdivision of a multigraph on the hubs**:

> **The hub model.** `M` is the multigraph on `W` whose edges are the
> `Λ`-edges (hub–hub edges of `G`, un-subdivided) together with one edge `u w`
> per degree-`2` vertex `x` with `N(x) = {u, w}` (*subdivided*). Then
> `deg_M z = deg_G z ≥ 3` for every hub, `Λ ⊆ M` has max degree `≤ 2` ((EL-1),
> which is exactly `hcard` at a hub — `closedHubNbhd v = {v} ∪ (hub
> neighbours)`, `Motive.lean:82`), no `Λ`-edge is parallel to another `M`-edge
> and `Λ` has no `C₃` (both would put a triangle in `G`).
>
> Give an `M`-edge **weight 5** when it is a `Λ`-edge and **4** when it is
> subdivided, and write `N` for `M` so weighted. For `A ⊆ W` put
> `U(A) := A ∪ {degree-2 vertices with both neighbours in A}`, `c(A)` for the
> `M`-edges leaving `A`, `e_Λ(A)` for the `Λ`-edges inside `A`, and
> `σ_A = Σ_{z ∈ A}(deg z − 3)`.

> **(GROW-1) Localized deficit identity.**
> `f(U(A)) = 6 + e_Λ(A) + 2σ_A − 2c(A)` for every `A ⊆ W`. (PAIR-1) is the case
> `A = W`, where `c = 0`.

*Proof.* `U(A)` has `|A| + b` vertices and `e_Λ(A) + 2b` edges, `b` the
subdivided `M`-edges inside `A`; so
`f = 5e_Λ(A) + 4b − 6|A| + 6 = 4m(A) + e_Λ(A) − 6|A| + 6` with
`m(A) = e_Λ(A) + b` the `M`-edges inside `A`. Now
`2m(A) = Σ_{z∈A} deg_M z − c(A) = 3|A| + σ_A − c(A)`; substituting gives the
claim. ∎

> **(GROW-2) The hub-multigraph criterion.** For `A ⊆ W` and a partition
> `Q = {X₁, …, X_k}` of `A`, let `a` / `b` count the `Λ`- / subdivided `M`-edges
> of `M[A]` crossing `Q` and set
>
> `exc(Q) := 5a + 4b − 6(k − 1) = 6 + a + 2·Σ_i (c(X_i) − 3)`,
>
> the second form for `Q` a partition of **all** of `W` (`c` taken in `M`).
> Then **`G[U(A)]` is rigid iff `exc(Q) ≥ 0` for every partition `Q` of `A`**,
> and `exc(finest) = f(U(A))`. Moreover (**hub closure**) every rigid
> `U ⊆ V(G)` satisfies `U ⊆ U(A)` for `A = U ∩ W`, `U(A)` is rigid, and
> `∂_hub U = ∂_hub U(A) = N_Λ(A) ∖ A`. Consequently, for `A ⊊ W`,
> `|U(A)| ≤ |V(G)| − 2` **always**, and `3 ≤ |U(A)|` whenever `U(A)` is rigid
> **and `2 ≤ |A|`**.
>
> **The `2 ≤ |A|` is load-bearing in the statement and free in every use** (coordinator
> repair, 2026-09-02, at the WGROW verification pass — the clause first landed without
> it). At `|A| = 1` it fails: `U({z}) = {z}`, since a mid has two *distinct* hub
> neighbours, and one vertex is rigid — its only partition is the one-part one, where
> `partitionDef = 6·0 − 5·0 = 0`, so `def = 0`, and **(R1)**'s min-degree-`2` conclusion
> does not bite because `two_le_degree_of_isKDof_zero` (`Deficiency.lean:1306`) carries
> the hypothesis `2 ≤ |V(G)|`. **Nothing downstream moves:** (GROW-4) quotes the clause
> only at `|X_i| ≥ 2` (it disposes of singleton parts by `c({z}) = deg_M z ≥ 3` instead),
> *Step GW5* re-derives its own `|U(W ∖ {z})| ≥ 3` from `|W| ≥ 4`, and `wgrow.py
> --validate` ranges `r` from `2`, so no figure or verdict is touched. Recorded rather
> than silently patched because it is the *seventh* summary-outruns-its-caveat instance
> of this arc and the first inside a freshly-landed lemma **statement**.

*Proof.* Take a partition `P` of `V(G[U(A)])` and read
`6(|P| − 1) − 5·d(P)`, the landed `partitionDef` at `D = 6`
(`Deficiency.lean:262`). A degree-`2` vertex `x ∈ U(A)` contributes `+0` when
its part contains both its neighbours, `−4` as a singleton, `−5` with exactly
one, `−10` with neither; so a maximizing `P` puts each such `x` with its two
neighbours when they share a part and alone otherwise, i.e. `P` is the
hub-closed lift of a partition `Q` of `A` with the `b` straddling mids as
singletons. That lift has `|P| = k + b` and `d(P) = a + 2b`, so
`6(|P| − 1) − 5 d(P) = 6(k − 1) − 5a − 4b = −exc(Q)`. Hence
`def = max(0, −min_Q exc(Q))`, which is the criterion; the finest `Q` gives
`−exc = 6(|A| − 1) − 5e_Λ(A) − 4b = −f(U(A))` by (GROW-1). The second form of
`exc` is `Σ_i c(X_i) = 2(a + b)` substituted into `5a + 4b = 4(a+b) + a`.
For the closure: a degree-`2` vertex of a rigid `U` has both neighbours in `U`
by **(R1)** (`two_le_degree_of_isKDof_zero`, `Deficiency.lean:1306`), so
`U ⊆ U(A)`; `G[U]`'s own excess drops only the non-chosen mids from `b`, so
`exc_U ≤ exc_{U(A)}` pointwise and `U(A)` is rigid too. `∂U` can leave `U`
only at a hub (again (R1)), so `∂_hub U` is the set of outside `Λ`-neighbours
of `A`, unchanged by adding mids. Finally `A ⊊ W` leaves a hub `z ∉ U(A)` and
(since `deg_M z ≥ 3 > 2 ≥ λ_z`) at least one mid at `z` outside as well, so
`|U(A)| ≤ |V| − 2`; and a rigid `U(A)` with `|A| = 2` needs weight `≥ 6` across
the two hubs, i.e. `≥ 2` **subdivided** parallel edges (a lone `Λ`-edge weighs
`5`, and a `Λ`-edge parallel to anything is a triangle), so `|U(A)| ≥ 4`. ∎

Two immediate readings. **The seed search is a hub-subset search**: by the
closure it suffices to test `A ⊆ W`, `2^{|W|}` instead of
`rigid_vertex_sets`' `2^{branches}` — which is what lets the driver reach the
`Λ`-cycles of length `≥ 7` that `wpair.py --hunt`'s cap could not build. And
**`|∂_hub U(A)| ≤ 2` is a `Λ`-condition alone**: `A = W ∖ Z` with `|Z| ≤ 2` is
always within budget, so the only question about such an `A` is rigidity.

### Step GW3 — **(GROW-3)**: the parts of a minimum-excess partition are rigid

> **(GROW-3)** Let `Q*` minimize `exc` among the partitions of `W` with `k ≥ 2`
> parts. Then `U(X)` is rigid for every part `X` of `Q*`.

*Proof.* If `N[X]` failed the criterion there would be a partition `R` of `X`
with `w_X(cross R) < 6(|R| − 1)`; refining `Q*` by replacing `X` with `R` gives
a partition with `≥ 2` parts and excess
`exc(Q*) + w_X(cross R) − 6(|R| − 1) < exc(Q*)`. ∎

This is the tight-partition idiom of *Step GW1*'s landed layer, one notch
stronger than the landed `IsTightPartition.parts` (`Deficiency.lean:2091`,
JJ Lemma 3.2(b)): that lemma extracts *`≥ 3` vertices and `≥ 2` in-part edges*
from the same merge/split arithmetic, where (GROW-3) extracts *rigidity of the
part*. The restriction to `k ≥ 2` is what keeps the one-part partition (excess
`0` always) from being the minimizer; when `def(G̃) > 0` the minimizer is a
tight partition in the landed sense.

### Step GW4 — **(GROW-4) THE SEED DICHOTOMY**, and **(GROW-6): (E-pair) is a THEOREM**

> **(GROW-4) Seed dichotomy.** Every member of (PAIR-5)'s class has a **seed**
> (a rigid `U` with `3 ≤ |U| ≤ |V(G)| − 2` and `|∂_hub U| ≤ 2`) **or** a
> **co-1 rigid set** (`V(G) ∖ {x}` rigid). No hypothesis about proper rigid
> subgraphs is needed.

*Proof.* First `|W| ≥ 2`: `W = ∅` would make `G` a cycle (2EC, all degrees `2`),
whose degree-`2` set is not independent, and a single hub cannot carry a
degree-`2` vertex, which needs **two** hub neighbours. So the `k ≥ 2` partitions
of `W` are a nonempty family. Suppose `G` has no seed, and let
`Q* = {X₁, …, X_k}` minimize `exc` over them.

By (GROW-3) each `U(X_i)` is rigid. A **singleton** part `{z}` has
`c({z}) = deg_M z ≥ 3`. A part `X_i` with `|X_i| ≥ 2` gives a rigid `U(X_i)`
with `3 ≤ |U(X_i)| ≤ |V| − 2` ((GROW-2), using `X_i ⊊ W` since `k ≥ 2`), so by
the no-seed assumption `|∂_hub X_i| ≥ 3`: at least three **distinct** outside
hubs are `Λ`-adjacent to `X_i`, hence at least three `Λ`-edges leave it, hence
`c(X_i) ≥ 3` again. So every part has `c(X_i) ≥ 3` and, by (GROW-2)'s second
form, `exc(Q*) = 6 + a + 2Σ_i(c(X_i) − 3) ≥ 6`.

By minimality **every** `k ≥ 2` partition of `W` has `exc ≥ 6`. Now let `e` be
any subdivided `M`-edge — one exists, since `Λ` has max degree `≤ 2` while `M`
has min degree `≥ 3`. Deleting `e` lowers `exc` by `4` at the partitions it
crosses and by `0` at the others, so `N − e` still has `exc ≥ 2 > 0` at every
`k ≥ 2` partition (and `0` at the one-part partition). By (GROW-2) applied to
`M − e`, that says `V(G) ∖ {x_e}` is **rigid**, `x_e` the degree-`2` vertex of
`e` — a co-1 rigid set. ∎

> **(GROW-6) (E-pair) is a THEOREM.** No residual has an independent
> degree-`2` set; equivalently, **every residual carries two adjacent
> degree-`2` vertices**. Hence, by (PAIR-6), so is **(V)**.

*Proof.* Let `G` be a residual whose degree-`2` vertices are independent. `G`
is simple and 2EC by hypothesis, triangle-free by **(T)** ((TF-5)), and
`hcard` by the landed necessary condition
(`ncard_closedHubNbhd_le_three_of_isNondegPencilRealization`, (EL-1)); so `G`
is in (PAIR-5)'s class. A residual has **no** co-1 rigid subgraph, so (GROW-4)
gives a seed — a proper rigid `U` with `|∂_hub U| ≤ 2` — which **(PAIR-3)**
forbids at a residual. ∎

Three remarks on what actually did the work.

- **The co-1 clause is the hypothesis that was doing the work all along, and
  it was in the residual bundle from the start.** (PAIR-4) used it (its `U`
  has to be proper *and* not co-1); *Step PR5* did not carry it into the class
  statement, and *Step GW5* shows that is exactly where (PAIR-5) breaks.
- **The named attack is superseded, not completed.** *Step PR5*(a) proposed
  growing a rigid set **along** a `Λ`-run by iterated ears. (GROW-4) never
  grows anything: it takes the extremal partition and reads the same
  `|∂_hub| ≥ 3` hypothesis off **every part at once**. The ear moves survive
  only inside (PAIR-3), which is where they were already proved.
- **What is *not* used**: no feasibility geometry, no branch-length bound
  beyond the class's own, no bound on `e₀`, and no cap on `|V|`. The proof is
  a two-line count once the carrier of *Step GW2* is in place.

### Step GW5 — **(GROW-5)**: (PAIR-5) *as stated* is REFUTED, by `K₂,₃`

> **(GROW-5)** `K₂,₃` — two hubs joined by three subdivided branches — is in
> (PAIR-5)'s class, **carries a proper rigid subgraph**, and has **no seed**.
> So (PAIR-5) as *Step PR5* states it is **false**. It is repaired by either
> of the two hypotheses that (PAIR-3)'s consumer supplies anyway: *no co-1
> rigid set* ((GROW-4)) or `6 ≤ |V(G)|`.

*Verification.* `|V| = 5`, `|E| = 6`, `f = 6 = 6 + 0 + 2·0`; simple, 2EC,
triangle-free, `hcard` (neither hub has a hub neighbour), degree-`2` set
independent. Its `C₄` (drop one degree-`2` vertex) is a cycle of length `4`,
rigid by `isKDof_zero_of_cycle` (`Deficiency.lean:743`), on `4 ⊊ 5` vertices —
an `IsProperRigidSubgraph` (`ibid.:483`, which asks `2 ≤ |V(H)|` and
`V(H) ⊊ V(G)`). But a seed needs `3 ≤ |U| ≤ |V| − 2 = 3`, and **every** 3-set
carries at most two edges, `f = −2`, `def = 2`: no seed
(`wgrow.py --k23` prints all ten). **`K₂,₃` is not a residual** — the very co-1
rigid set that refutes (PAIR-5) is what a residual forbids — so this refutation
**says nothing about (E)**, and (E) remains open and tight at `f = 4`.

**It is the only one.** Seedlessness forces `exc ≥ 6` everywhere ((GROW-4)'s
first half) while, for a seedless `G`, `V ∖ {x, x'}` must fail to be rigid for
every pair of degree-`2` vertices, which needs a `k ≥ 2` partition with
`exc ≤ 7`; a minimum-excess partition with a non-singleton part has `a ≥ 2`,
hence `exc ≥ 8`, so the finest partition must be the witness and
`f(V(G)) = 6 + e₀ + 2σ ≤ 7`, i.e. `σ = 0` and `e₀ ≤ 1`. With `σ = 0` the hub
multigraph is **cubic** (so `|W|` is even), and at a hub with `λ_z = 0` the
identity `exc_{N[W∖z]}(R) = exc_N(R ∪ {{z}}) − (4 deg z + λ_z) + 6 ≥ 6 − 12 + 6
= 0` makes `U(W ∖ {z})` **rigid** — a seed, since `|∂_hub| ≤ λ_z = 0`, provided
`|U(W ∖ {z})| ≥ 3`, which holds once `|W| ≥ 4`. With `e₀ ≤ 1` at most two hubs
carry a `Λ`-edge, so `|W| ≥ 4` always exposes such a `z`. That leaves `|W| = 2`,
where `e₀ = 0` (a `Λ`-edge between the two hubs would be parallel to a
subdivided one) and cubicity forces the three-parallel-edge hub multigraph, i.e.
`K₂,₃`. The sweep agrees: **1 seedless member in 1 016 class members**, and it
is `K₂,₃` (`wgrow.py --k23`, `--dich`).

### Step GW6 — job 3: the W4 cost list, the readings, the E-rider

**The W4 cost list after this landing.** Non-user-call items: **NONE**.
(E) — never needed by the split arm; its only real consumer, §(SAFE-RES′)'s
(S1)/(S2), needs (E-pair) ((EL-6)), and (E-pair) is now a theorem ((GROW-6)).
(E-loc) — refuted and not needed ((EL-5)). (T) — a theorem ((TF-5)). (V) — a
theorem ((PAIR-6) + (GROW-6)). (PAIR-5) — settled both ways ((GROW-4),
(GROW-5)). The **only** open W4 item is **(K-res)**, which is a **USER call**
(the standing route-3/packaging-(b) adjudication parks the W4 build; (K-res)'s
own mathematics is ranked with the kernel arc, not here). So W4's informal
side is **closed as an argument**, and what remains is a build, not a gap.

**Readings (2) and (3), tested (`RESEARCH-ARC.md` §7).**

- **Reading (2) — CONFIRMED, and SHARPENED.** The `|∂_hub|` invariant is
  indeed unconditional for (PAIR-3)'s **two** moves (726 `j = 1` absorptions
  checked, all non-increasing), and the `j = 1` clause does strictly decrease
  at a boundary hub. The sharpening the prep did not state, and which matters
  the moment one tries to *grow*: the invariant is a property of **those two
  moves**, not of ear absorption in general. Absorbing a hub through **two
  subdivided branches** is an ear with `j = 3` — admissible for the Ear Lemma,
  and it can **strictly grow** `|∂_hub|` (241 witnesses). That is why "grow
  until it is a seed" does not close, and why (GROW-4) does not grow.
- **Reading (3) — CONFIRMED, verbatim.** An ear through `k` consecutive hubs
  has `2k − 1` interior vertices when it attaches directly at both ends, `2k`
  with one subdivided attachment, `2k + 1` with two; against the Ear Lemma's
  `j ≤ 5` that admits `k ≤ 3` (direct) and `k ≤ 2` otherwise. The correction
  is made at *Step PR5* itself (F12), together with the note that the attack
  the paragraph proposes is now **superseded** rather than blocked.

**The E-rider, read and NOT fired.** E1–E3 are the **(BE-14)/(GR-15) arc's**
termination test, stated over that arc's ledger and target; W4 is not a ledger
entry but is named inside GEXIST's E3 as an example of an *adjudication-gated*
one. I read **both** E3 texts: GEXIST's two-conjunct form
(`notes/Pencil-fanout-archive.md:1700` — *target proven* **and** *every
remaining ledger entry adjudication-gated*) and the later deliberate
one-conjunct deviation (`ibid.:2098` — *the target is proven, full stop*).
Under either, **E3 does not fire**: the target is the arc's,
`PencilPair K 3 G`, and proving (E-pair) does not prove it; the (BE-14) thread
also stays dispatchable, so the two-conjunct form fails twice over. **E2 does
not fire**: its second conjunct — no ledger entry left
open-with-a-named-dispatchable-attack — is false. Worth recording, since the
prep's pre-correction and the rider's own wording differ: **E2's literal text
says *"the direction's target"* while E3's says *"the target"***, so the
"never a direction's local obligation" reading is a correction to E2's letter,
not a restatement of it — under E2's letter its first conjunct would arguably
be met here ((PAIR-5) *as stated* is refuted), and only the second conjunct
stops it. **E1** needs a g-flank; none was exhibited. **Nothing is fired; this
is a report.**

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

**The (E-loc) driver is `notes/scripts/w4/weloc.py`** (tracked; integer-exact,
five modes), and it is the evidence behind *Steps EL1–EL6*.

- **`--validate`** — the mechanical identities of (EL-2): `f(W) = 5c − |W| − 5k
  + 6` on **9 567** instances (7 156 connected), `count_indep` against the direct
  `f(W) ≤ 0` sweep on **389** graphs, the minimal-dependent-set branch
  enumeration against a brute-force subset sweep on **215** subdivisions
  (533 sets), the Ear Lemma threshold at `j = 0..7`, and (EL-1) on 533 `hcard`
  graphs. **0 mismatches anywhere.**
- **`--witness`** — `T32`, every `hnoGood'` clause, with rigidity re-checked on
  all three oracles (pebble game / tree packing / partition enumeration) and all
  22 degree-`2` deletions tested; plus six further instances of the family.
- **`--brick`** — the falsification audit for **(EL-4)**. (EL-3) first: **81**
  bricks found across **319** random `hcard` graphs, every one a hub cycle of
  length `≤ 5`. Then **374** instances *carrying* a hub cycle (structured stars,
  chorded stars and random min-degree-3 bases), each run through *Step EL4*'s
  chain with `hcard(G/S)` and shieldedness **asserted at every step**: **157**
  `j = 1` and **128** `j = 2` ear extensions actually taken across 198 of them,
  **0** assertion failures, and **0 residuals** — any one would refute (EL-4).
- **`--pool`** — the denominator disclosure of *Step EL5* (255 → 160 / 95 / **0**).
- **`--hunt`** — the size of the shape-1 family: the `(m, a, b)` scan, the
  smallest refuting instance (`|V| = 32`), and mixed `C₄`/`C₅` cores. A three-core
  construction is **not** run: 24 branches is past `rigid_vertex_sets`' `2^22`
  enumeration cap, so no instance of it could be certified — recorded as a cap,
  not as an absence.

Reproduce: `python3 notes/scripts/w4/weloc.py --validate | --witness | --brick |
--pool | --hunt` (all five: 114 s, `VALIDATE: OK`).

**The (E-pair) driver is `notes/scripts/w4/wpair.py`** (tracked; integer-exact,
five modes), the evidence behind *Steps PR1–PR6*.

- **`--validate`** — the three mechanical claims. **(PAIR-1)**'s identity
  `f = 6 + e₀ + 2σ` on **33 299** random simple min-degree-2 graphs with an
  independent degree-`2` set; **(PAIR-2)** on **48 133** rigid sets over 1 135
  graphs (`hcard(G/U) ↔ |∂_hub U| ≤ 2` at all **14 521** simple contractions,
  plus the (R1) closure and the hub-attachment claim); **(PAIR-3)**'s monotone
  invariant asserted at every step of **22 359** chain runs from seeds in
  triangle-free `hcard` 2EC graphs, outcomes `good-contraction` 18 734 / `co-1`
  1 051 / `spanning-C3` 2 574 and **nothing else**. **0 mismatches anywhere.**
- **`--sub`** — (PAIR-4)'s stratum: **220** full subdivisions of min-degree-3
  multigraphs carrying a proper rigid subgraph, **173 836** rigid sets, **all**
  with `∂_hub = ∅`; every instance classified `co-1` (200) or
  `good-contraction` (20), i.e. **no residual**, and the `f`-spectrum
  `{6, 12, 14, 18, 22, 24, 28}` shows the `f = 6` stratum is exactly the
  3-regular case.
- **`--hunt`** — *Step PR5*'s worked instance asserted (the octagon with four
  subdivided diameters: `f = 14`, the `C₆`'s hub-boundary `{z₅, z₇}`, chain
  verdict `co-1`), then the search for a ¬(E-pair) residual over partial
  subdivisions:
  **313** candidates (simple, 2EC, triangle-free, `hcard`, independent degree-`2`
  set; max `f = 32`, max hubs 10), **0 residuals**, and the **seed condition
  (PAIR-5) held at 313/313**. Cap: `≤ 16` branches (the `2^{branches}` rigid-set
  enumeration), i.e. `≤ 10` hubs, and the pairing-model generator builds no
  `Λ`-cycle of length `≥ 7` — recorded as a cap, not as an absence.
- **`--vee`** — (PAIR-6): **432** explicit carriers of the two (V) residues
  (332 of `j = 3, u = u'`; 100 of `j = 2, u ~ u'`), each with residue
  `|∂_hub| ≤ 2` (tree-packing oracle agreeing on rigidity), none a residual, and
  each chain ending on a residual-forbidden verdict.
- **`--pool`** — the denominator disclosure: over the 255 pool residuals the
  `f`-spectrum is `{−3: 32, −2: 47, −1: 51, 0: 83, 1: 34, 2: 8}` and **0** have an
  independent degree-`2` set (`T32` included, at `f = 4`).

Reproduce: `python3 notes/scripts/w4/wpair.py --validate | --sub | --hunt | --vee
| --pool` (all five: 282 s, `VALIDATE: OK`, byte-identical at pinned
`PYTHONHASHSEED`).

**The (PAIR-5) driver is `notes/scripts/w4/wgrow.py`** (tracked; integer-exact,
four modes), the evidence behind *Steps GW1–GW6*. It works on the **hub model**
of *Step GW2*, so its enumeration is `2^{|W|}` rather than
`rigid_vertex_sets`' `2^{branches}` — which is what lets it build the
`Λ`-**cycles of length `≥ 7`** that `wpair.py --hunt`'s pairing-model generator
could not (the cap that direction disclosed, and the configuration (EL-4)
leaves open).

- **`--validate`** — the four mechanical claims, over **824** class members
  built from **882** hub models (all cubic hub multigraphs on `2`/`4`/`6` hubs
  crossed with **every** valid `Λ`, plus the `Λ`-cycle family and random
  min-degree-3 models). **(GROW-1)** on **196 028** hub subsets; **(GROW-2)** on
  **39 989** hub subsets against **both** landed oracles (pebble game and tree
  packing, which agree everywhere) plus the **co-1 stratum** — `V(G) ∖ {x}` at a
  degree-`2` vertex is the partial subdivision of `M − e_x`, checked on **4 242**
  candidates (**3 998** rigid); the **hub closure** on **46 024** rigid sets
  taken from the independent branch enumeration; **(GROW-3)** on **1 490** parts
  of minimum-excess partitions, with the `exc = 6 + a + 2Σ(c − 3)` rewriting
  asserted. **0 mismatches anywhere.** Then the two readings: **726** `j = 1`
  absorptions all non-increasing, and **241** `j = 3` absorptions that strictly
  grow `|∂_hub|`; and the `2k − 1 / 2k / 2k + 1` ear table against `j ≤ 5`.
- **`--dich`** — **(GROW-4)** checked on **1 016** class members from 1 182 hub
  models: `seed` 5, `co-1` only **1**, both 1 010, **NEITHER 0**. **118** of
  them carry a `Λ`-cycle of length `≥ 7`. Cap, disclosed: `|V| ≤ 27`,
  `≤ 10` hubs (the `2^{|W|}` seed enumeration), `f(V(G)) ≤ 37`. **The sweep is
  a check, not the evidence** — (GROW-4) is proved.
- **`--k23`** — **(GROW-5)**: `K₂,₃`'s class membership, its `C₄`, and the
  deficiency of **all ten** 3-subsets (`def = 2` except the edgeless one at
  `12`), i.e. no seed; plus the uniqueness sweep — **1** seedless member over
  the whole model set, and it is `K₂,₃`.
- **`--pool`** — the denominator disclosure, unchanged from WPAIR's: **0 of
  255** pool residuals have an independent degree-`2` set, so that pool decides
  nothing here either.

Reproduce: `python3 notes/scripts/w4/wgrow.py --validate | --dich | --k23 |
--pool` (all four: **204 s**, byte-identical across two runs at pinned
`PYTHONHASHSEED=0`).

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
- **(E), (E-loc) and (E-pair)** — not kernels, but this section's other open
  item, and the one that keeps moving. **(E-loc): REFUTED** (*Step EL5*, `T32`) —
  and its *other* obstruction shape is **impossible** (*Step EL4*), so the
  refutation is not a gap in the analysis but the whole answer. **(E): open**,
  holding at every instance known and **tight** (`f = 4` attained at `T32`); its
  live successor is **(E-pair)**, which is weaker and is all §(SAFE-RES′)'s
  (S1)/(S2) consumes (*Step EL6*). **(E-pair): a THEOREM** (*Steps PR1–PR6* +
  *GW1–GW6*, 2026-09-02) — ¬(E-pair) forces `f ≥ 6` exactly ((PAIR-1)) and
  `f ≥ 7` once the independent-hub stratum is closed ((PAIR-4)); no residual
  carries a rigid set attached to `≤ 2` outside hubs ((PAIR-3), which subsumes
  (EL-4)); and on the hub multigraph every class member has such a set or a co-1
  rigid set ((GROW-4)), which a residual forbids ((GROW-6)). Its *statement*
  (PAIR-5) needed one repair on the way — `K₂,₃` refutes the unrestricted form
  ((GROW-5)) and is the only graph that does. **(V): a THEOREM** ((PAIR-6) +
  (GROW-6)). **So W4's non-user-call cost list is EMPTY**, and its informal side
  is closed as an argument; **(K-res)**, a USER call, is the only open item.
- **`hbareSplit`** — **unchanged.** Not on routes 1/3's path (Step 0); its
  adjudicated carry stands verbatim. **(K-bare-ext)**, its route-A discharge
  statement, is **REFUTED as stated** since 2026-08-20
  (`notes/Pencil-informal.md` §(K-bare-ext)); that does not reach this arm,
  precisely because Step 0 keeps the branch unreachable here.
