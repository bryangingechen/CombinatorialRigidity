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
   assessment first). At `W19` the split arm's *geometric* inputs are all
   present — the long branches supply a degree-2 vertex `v` strictly inside a
   branch of `≥ 3` interior vertices, whose two neighbours are degree-2,
   non-adjacent and share no other neighbour. **Every one of the 93 sweep
   inhabitants has such a vertex, and a 366-instance probe restricted to
   graphs with every branch `≤ 1` interior vertex found no inhabitant at
   all** — so the conjecture worth proving next is

   > **(SAFE-RES)** *A residual `G` always has a degree-2 vertex strictly
   > interior to a branch with `≥ 3` interior vertices.* — verdict **open**,
   > strong numerical support; the Ear Lemma forces long *ears* but not
   > directly long *branches*, which is the gap.

   The Lean cost is *not* only (SAFE-RES). Reading
   `pencilPair_of_splitOff_of_habitat` (`Escape.lean:334`) and
   `hasGenericPencilRealization_of_splitOff_of_safe` (`:95`), the landed
   chain consumes `hnoRigid` at five points: `simple_of_loopless_of_noRigid`
   (free at a residual `G`, `Simple` is a hypothesis);
   `exists_adjacent_degree_two_pair_of_noRigid_of_degree_two` (= SAFE-RES);
   `splitOff_simple_of_noRigid_of_card` and
   `splitOff_triangleFree_of_noRigid` (both re-derivable from a *deep* split
   vertex, which is why (SAFE-RES) is stated in that sharper form); the
   `htf` derivation feeding L7b (already superseded by W4-B / leaf W4-L2);
   and — the real cost — **`hnoRigid` sits in the antecedents of the carried
   kernels `hK` and `hbareSplit`**, so this route widens two already-open
   research kernels rather than reusing them as pinned.
2. **Discharge branch 4 directly**: build a generic realization of `G` from
   the IH's *bare* half at an infeasible contraction. This is the hardest
   kernel shape in the phase (strictly stronger than `hbareContract`, which
   only has to produce the bare conclusion).
3. **Change the dispatch invariant** so the contraction branch is only
   entered when a good contraction exists — i.e. carry the Step-2 structure
   theorem as the branch condition and route the `≥ 3`-boundary-hub
   configuration to the split arm. Same kernel-widening cost as route 1, but
   the case analysis is pinned by Step 2 rather than by a new conjecture.

Route 1 vs 3 is a coordinator/user adjudication; both need (SAFE-RES) or an
equivalent, and both need the `noRigid`-free kernel restatements.

## §(K-tight) — stub

The hard residue of kernel **(K)** after the corank stratification: tight
habitats (`5|E| = 6(|V| − 1)`), both chain ends hubs, provably 2-connected,
where no landed-brick route closes the escape's non-constancy. Current state,
the `index ≥ 1` trade against (K-shared), and the identified enabling
technology (stress-as-chart-rational-function infrastructure) are in
`notes/Phase39-design.md` §"W5-L7 research recon" → "(K) non-constancy
recon"; the literature verdict (NO HIT, crux novel) is §"(K) literature
hunt".

**Verdict: open.** To be filled by the dispatch that attacks it; nothing is
being developed here yet.

## §(K-bare-ext) — stub

The minimal open statement isolated by the (K-bare) extension-route recon:
the arbitrary-seed insertion lemma, with the def-equal caveat folded into its
`∃` as a line-avoidance side condition. Statement, the corank stratification
that produced it, the DZ/cube/Wagner danger gadgets and the option-C probe
results are in `notes/Phase39-design.md` §"(K-bare) extension-route recon".

**Verdict: open.** To be filled by the dispatch that attacks it; nothing is
being developed here yet.
