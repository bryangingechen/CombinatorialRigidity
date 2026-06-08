# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. Design-reconned in
`notes/Phase22-realization-design.md` §1.33 (A)/(B); this note is the canonical home for
that recon's verdict. KT §6.4.1 (Lemma 6.10) at the `k=0`/`d=3` scope.

## Current state

**Just landed: the abstractly-indexed device-closure feed
`hasFullRankRealization_of_independent_panelRow_index`** (`GenericityDevice.lean`), the `Set`-free
repackaging of `hasFullRankRealization_of_independent_panelRow`. Where the device closure consumes a
*set*-indexed panel-row subfamily `s`, this takes a finite type `ι`, an injective index map
`j : ι → β × ⋀ᵏ-pair × ⋀ᵏ-pair`, the panel-row family `i ↦ panelRow ends (j i)` independent, and the
count `D(|V|−1) ≤ |ι|`, and produces `HasFullRankRealization k G` — reindexing across
`Equiv.ofInjective j` + transferring the count by `Nat.card_range_of_injective`. This is exactly the
final packaging step `case_II_placement_eq612` performs inline (CaseI.lean:2757–2818), lifted out so
the `d=3` `hsplit` producer can feed the device closure the **candidate-completion's `Sum`-indexed
output** (`linearIndependent_sum_augment_candidateRow` yields `(rn ⊕ {w}) ⊕ ro`, a `Sum` type, not a
`Set`) once each summand is identified with a `panelRow ends (j i)`. Fully green, no defeq trap (it
is index-bookkeeping over the already-green closure). The candidate-selection capstone
`case_III_eq629_conditional` (the previous commit, graph-free, `RigidityMatrix.lean`) discharges
`lem:case-III-eq629-conditional`; both this feed and the selection capstone are now green, so the
producer's two end-bricks (selection in, packaging out) are in place — what remains is the
graph-data instantiation between them.

**Next concrete step (smallest forward commit): build the `d=3` `hsplit` producer at real graph
data.** Wire `case_II_placement_eq612` (eq. (6.12), `D(|V|−1)−1`, output over `ofNormals G ends q₀`)
⊕ the candidate row ⊕ the now-green `case_III_eq629_conditional` selection into
`linearIndependent_sum_augment_candidateRow` **at the actual `G.splitOff …` framework** — extract
`rn`/`ro`/`ρ` + supply the three per-candidate `hselᵢ` from the real candidate families, select the
winning candidate, feed the now-green `hasFullRankRealization_of_independent_panelRow_index` (the
abstractly-indexed device-closure feed — it consumes the candidate-completion's `Sum`-indexed family
directly via an injective `j` placing each summand at its `(edge, ⋀ᵏ-pair)`) — yielding
`HasFullRankRealization k (G.splitOff …) ⟹ … k G`, discharging `theorem_55`'s `hsplit` premise at
`k=2`. **`G.splitOff` is NOT `≤ G`** (edge-substitution: deletes `v`'s edges, adds fresh `e₀`); the
transport routes through the common subgraph `G − v` (`removeVertex_le` / `removeVertex_le_splitOff`,
both green) via N7b-2 `exists_independent_panelRow_transport`, exactly as `case_II_placement_eq612`
already does internally. This is the first consumer wiring real graph data, so **the
`ofNormals`/`withGraph` defeq-timeout trap bites** (FRICTION; TACTICS-QUIRKS §38) — budget for it; it
is the main engineering risk, not a math risk. See `notes/Phase22-realization-design.md` §1.33 (A).

After the `hsplit` producer: instantiate `theorem_55 (n:=2) (k:=2)` with it + the green
`hcontract` (`case_I_realization`) and `hbase` (`theorem_55_base`); feed that into
`rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound is already green, discharged in-proof);
do the Thm 5.5→5.6 multigraph push (`lem:motions-mono-of-graph-le`). Milestone: the molecular
conjecture proved at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma 6.13) is
**Phase 23** (reuse map: §1.33 (C)).

**Recon done; build not yet started.** The two open items the recon flagged are resolved below
(*Red-node consistency gate — recon verdict*); the supersession + label-resolution gates ran
clean over the algebraic-induction chapters. No Lean built this commit (docs/blueprint only).

## Red-node consistency gate — recon verdict (2026-06-07, opening commit)

Read the target producer nodes `lem:case-II-realization` / `lem:case-III`
(`algebraic-induction/case-iii.tex`) end-to-end (statement AND proof), traced
`minimal_kdof_reduction` + the `theorem_55`/`theorem_55_generic` dispatch
(`Induction/ForestSurgery.lean`, `AlgebraicInduction/PanelHinge.lean`), and ran the supersession +
label-resolution gates over `algebraic-induction/*.tex`. **Gate clean; both open items resolved.**

- **(B.1) — CONFIRMED: the `d=3` `hsplit`/`theorem_55` path does NOT consume `lem:cycle-realization`
  (KT Lemma 5.4).** `theorem_55` and `theorem_55_generic` are *literally*
  `Graph.minimal_kdof_reduction` applied to three branch hypotheses — `hbase` (`V(G).ncard = 2`),
  `hsplit` (a reducible degree-2 vertex, split off), `hcontract` (a proper rigid subgraph,
  contracted). The reduction's induction (`Nat.strong_induction_on` on `V(G).ncard`) has **no
  cycle branch**: the *only* base case is `V = 2`, reached purely by descent through `hsplit`/
  `hcontract`. Short cycles dissolve into repeated splits — there is no separate short-cycle
  realization input on the Lean path. So `lem:case-III`'s `\uses{lem:cycle-realization}` is a
  **blueprint↔Lean structural divergence**: a KT-*narrative* dependency (KT's Lemma 6.13 opens by
  Lemma 4.6 with $G$ a short cycle, by Lemma 5.4, *or* carrying a length-`d` chain — Lemma 6.10/6.13
  proper is the chain case), **not** a Lean-load-bearing one for the `d=3` assembly.
  - *Reconciled in this commit, not dropped.* `lem:cycle-realization` stays genuinely RED (no
    `\leanok`; its residual gap is the cited Crapo–Whiteley projective input, not the device) and
    stays a real general-`d` input for **Phase 23's** cycle base — and it is *already* load-bearing
    for the `k > 0` `lem:case-II` (green, `\uses`'s it). So the `\uses` edge on `lem:case-III` is
    kept, with a new prose note in the node clarifying the `d=3` Lean path does not consume it.
  - *Stale `case-i.tex:149–151` text fixed.* The `lem:cycle-realization` node said the only
    cited-not-formalized step is "the genericity device, Claim 6.4/6.9, shared with Cases I and II."
    Stale post-22b — `lem:claim-6-4` went green (`\leanok`). Rewritten: the residual cited step is
    the **Crapo–Whiteley** "cycle rigid iff hinge lines independent" projective input
    (`crapoWhiteley1982` Prop 3.4 / `whiteley1999` Prop 3), with an explicit aside that Claim 6.4/6.9
    is now green and is not the gap.
- **(B.2) — DECIDED: add a small `d=3`-instance `theorem_55` node.** A blueprint node is
  green-or-red, and the *general* `thm:theorem-55` (free `n k`) must stay red until Phase 23 supplies
  `hsplit` at all `k`. So the molecule-app chapter (Cor 5.7) consumes a small green `d=3`-instance
  node = `theorem_55 (n:=2) (k:=2)` applied to the three green args (`hbase`/`hsplit`/`hcontract`),
  **not** a standalone `theorem_55_dim3` restating the statement. Rationale: avoids duplicating the
  statement (it's an instantiation, not a re-proof) and keeps the general node honestly
  red-pending-Phase-23 with a note. Mint the node name when the producer lands.
- **Supersession + resolution gates clean.** Superseded labels =
  {`-disjoint-line-meet`, `-e0-recovery`, `-motion-side-assembly`, `-pin-vertex`} (the four 22c
  motion-side dead-ends); no live node's `\uses` reaches any of them. `\uses` ⊆ `\label` (no
  dangling references). `lem:case-II-realization` / `lem:case-III` route through the same argument
  their statements claim (the `d=3` contrapositive is green; the realization assembly is the genuine
  remaining content), no live-route `\uses` reaches a superseded node.

**Verdict: the build is safe to scope.** The one real gap is the `d=3` `hsplit` producer (§1.33 (A));
the `lem:cycle-realization` dependency is not Lean-load-bearing for it (B.1), and the architecture
call is settled (B.2). No deferred Lemma-5.4 sub-phase is a prerequisite for `d=3` (it re-enters at
the Phase-23 cycle base).

## Lemma checklist

- [x] **`lem:case-III-eq629-conditional` candidate-selection capstone** — `case_III_eq629_conditional`
  (`RigidityMatrix.lean`), the graph-free selection routing `case_III_claim612`'s disjunction through
  the three per-candidate full-family implications. Node flipped GREEN. (2026-06-07)
- [x] **Abstractly-indexed device-closure feed** — `hasFullRankRealization_of_independent_panelRow_index`
  (`GenericityDevice.lean`), the `Set`-free repackaging of the device closure consuming a finite
  `ι` + injective `j` (the shape of the candidate-completion's `Sum`-indexed output). The producer's
  packaging-out end-brick. Fully green, no defeq trap; internal infra (no blueprint node). (2026-06-07)
- [ ] **`d=3` `hsplit` producer** — wire `case_II_placement_eq612` ⊕ candidate-row ⊕ the green
  `case_III_eq629_conditional` into `linearIndependent_sum_augment_candidateRow` at real graph data,
  feeding the green `hasFullRankRealization_of_independent_panelRow_index`, giving
  `HasFullRankRealization k (G.splitOff …) ⟹ … k G`. The work; defeq-trap engineering. §1.33 (A).
- [ ] **`d=3`-instance `theorem_55` node** (B.2) — instantiate `theorem_55 (n:=2) (k:=2)` on the
  three green branch args; add the small green blueprint node the molecule-app chapter consumes.
- [ ] **`lem:case-II-realization` / `lem:case-III` flip green** — once the producer + instance land.
- [ ] **Thm 5.5→5.6 push + feed `rigidityMatrix_prop11`'s `hgen`** — unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **The `ofNormals`/`withGraph` defeq-timeout trap** is the standing engineering risk (TACTICS-QUIRKS
  §38; carried from 22a–e *Blockers*). Mitigation known: make the two frameworks syntactically equal
  before `convert`; transfer rigidity via a `mem_infinitesimalMotions` round-trip; extract a generic
  helper to dodge the `whnf`/`isDefEq` timeout. Budget for it; not a math risk.
- **No math blockers.** (B.1)/(B.2) resolved; the `d=3` contrapositive (Claim 6.12 + candidate
  completion + N3b) is fully green; the producer is plumbing-on-green-bricks (the candidate-completion
  was deliberately built graph-free in 22e to isolate exactly this wiring).

## Hand-off / next phase

**Smallest next commit:** build the `d=3` `hsplit` producer (the spine in §1.33 (A)) — wire
`case_II_placement_eq612` + the candidate row + the now-green selection capstone
`case_III_eq629_conditional` into `linearIndependent_sum_augment_candidateRow` at real `G.splitOff`
graph data, feed the now-green `hasFullRankRealization_of_independent_panelRow_index`, and conclude
`HasFullRankRealization k (G.splitOff …) ⟹ … k G`. Both end-bricks (selection in,
`…_index` packaging out) and the abstract candidate-completion are green; the remaining content is
the *graph-data instantiation between them* — extract `rn`/`ro`/`ρ` + the three `hselᵢ` from the real
candidate families, package the selected `Sum.elim` family with an injective `j` for `…_index`, and
transport the old block through the common subgraph `G − v` per N7b-2. Likely **multi-session**: the
`ofNormals`/`withGraph` defeq-trap engineering dominates *and* the three candidate families'
graph-data construction (each `rn`/`ro`/span/pin) is itself non-trivial. A reasonable cut, if the
whole producer walls: land the producer as a green-modulo lemma carrying the three candidate families
+ their `hselᵢ` + the duality/affine-indep as explicit hypotheses (the Phase-21b `h…` idiom), then
discharge those sub-obligations one candidate at a time. If a single instantiation `whnf`-walls,
extract the generic helper per TACTICS-QUIRKS §38 first. Then the `theorem_55` instantiation (B.2
node), the `lem:case-II-realization` / `lem:case-III` flips, and the Thm 5.5→5.6 push.

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d`
(KT Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1 verbatim;
generalize the candidate chain on the graph-free assembly; build the `⋀^{d−1}` duality via the
top-power route per §1.33 (D), reusing 22f's already-landed `map`-range infra; reuse the existing
alg-independence machinery for the points). Open Phase 23 with its own recon (read eqs. 6.46–6.67
against the `d=3` Lean) and add the general-`d` alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **Device-closure feed lifted to an abstract index, decoupling the producer's packaging from
  `case_II_placement_eq612` (2026-06-07).** `hasFullRankRealization_of_independent_panelRow_index`
  repackages the `Set`-indexed device closure to consume a finite `ι` + injective `j` — the shape of
  the candidate-completion's `Sum`-indexed output. Built green by reindexing across
  `Equiv.ofInjective j` + `Nat.card_range_of_injective`, lifting the inline packaging out of
  `case_II_placement_eq612` (CaseI.lean:2757–2818) so the candidate path reuses it. No defeq trap (it
  is the already-green closure under an index bijection). Internal infra — no blueprint node (a
  `Set`-free restatement of an already-blueprinted lemma; churn-prone glue, below the selection bar).
- **Selection capstone built graph-free as the first producer brick (2026-06-07).**
  `case_III_eq629_conditional` discharges `lem:case-III-eq629-conditional` by composing
  `case_III_claim612`'s disjunction with three abstract per-candidate implications
  (`r̂(Cᵢ)≠0 ⟹ LinearIndependent famᵢ`). Stated over abstract families (no `ofNormals`) so the heavy
  concrete-carrier `whnf` (§38) cannot bite — the selection logic is pure `Or`-mapping. The defeq
  trap is thereby confined to the *one* remaining step (the real-graph instantiation), keeping it
  isolatable per the §38 extract-a-helper mitigation. 1-line term proof.
- **(B.1) the `d=3` `hsplit`/`theorem_55` path does NOT consume `lem:cycle-realization`
  (2026-06-07, open).** `theorem_55`/`theorem_55_generic` = `minimal_kdof_reduction` with three
  branches, no cycle branch, base case `V=2` only. Short cycles dissolve into repeated splits.
  `lem:case-III`'s `\uses{lem:cycle-realization}` is a KT-narrative (not Lean-load-bearing)
  dependency — kept with a clarifying prose note; the cited step it bottoms on is Crapo–Whiteley,
  not Claim 6.4/6.9 (which is green). Fixed the stale `case-i.tex:149–151` text. Detail above.
- **(B.2) add a small `d=3`-instance `theorem_55` node, not a standalone `theorem_55_dim3`
  (2026-06-07, open).** It's `theorem_55 (n:=2) (k:=2)` on three green args; the general
  `thm:theorem-55` stays honestly red-pending-Phase-23. Avoids duplicating the statement.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *The `ofNormals`/`withGraph` defeq-timeout trap + its extract-a-generic-helper mitigation*
  → TACTICS-QUIRKS § 38 (carried from 22a–e).
