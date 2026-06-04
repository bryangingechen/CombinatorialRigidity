# Phase 22 — Realization layer (Case I + Case III at `d=3`) (work log)

**Status:** in progress (opened 2026-06-04).

Stratum 5 of the molecular-conjecture program, continued: the Theorem-5.5 *case
producers* that the Phase-21b genericity device feeds. Phase 21b closed the
genericity-free reductions (the accounting iffs, the `V(G)`-relative count
bridges, the device, the reusable row/glue infra) and re-scoped the realization
*producers* here after a math-first feasibility pass. The KT math for both
producers is worked out in `notes/Phase21b.md` *Finding A/B* + *Hand-off to
Phases 22–23* — **Phase 22 formalizes it, it does not re-derive it.**

Forward-mode / **structural-edit** discipline (`blueprint/CLAUDE.md`): Phase 22
does *not* open a new blueprint chapter. Its producers (N4/N5/N6, the Case II/III
producer) **extend the existing `algebraic-induction.tex`** — their nodes are
already stubbed red there. Program plan / reuse map / citations:
`notes/MolecularConjecture.md` *Phase 22*. Lean lands in
`Molecular/{Induction,AlgebraicInduction}.lean`. Cross-cutting rationale:
`DESIGN.md` *Realization motive must be V(G)-relative*, *Constructibility recon
before a producer build*, *Phase Case-naming vs. KT's k-bookkeeping*.

## Current state

Phase opened; no Lean landed yet. **A second constructibility recon
(2026-06-04, below) further sharpened N4: it is not merely a "union does not
commute with contraction" issue — the per-cycle-matroid step `cycleMatroid_contract`
does not even apply** (the graph `rigidContract` is a vertex-relabel `map` with
`E(H)` *deleted*, the matroid side *contracts* `E(H̃)`; there is no vendored
`cycleMatroid`-under-`map` lemma, and the Whitney rank-of-contraction identity is
the real content). The matroid-side fact N4 would transport
(`contraction_isMinimalKDof`, `Induction.lean:1998`) is green; the graph↔matroid
bridge `matroidMG (G.rigidContract H r) = M(G̃)／E(H̃)` is a **several-node
sub-build**, not a single commit. **Neither N4 nor the N5 fallback is a clean
single-session node** (N5's own blueprint note: "the genuinely hard one …
warrants its own decomposition pass before a single-commit build"). The next
concrete commit is the leaf-most brick: see *Hand-off* below.

## Architectural choices made up front

- **Two tracks; Track A first.** Track A (Case I producer, full-rank, KT §6.2) is
  the tractable entry point and independent of Case III. Track B (Case II/III
  reducible-vertex producer at `d=3`, KT §6.3 + §6.4.1) is the crux (Lemma 6.10,
  ~12 pages, the single largest proof in KT). See `notes/MolecularConjecture.md`
  *Phase 22* for the node-by-node plan.
- **The motive is `V(G)`-relative** (`DESIGN.md` *Realization motive must be
  V(G)-relative*; carried from Phase 21b). `HasFullRankRealization` is the
  `V(G)`-relative rank `D(|V(G)|−1)`; the absolute null-space form is
  unsatisfiable for non-spanning inductive subgraphs.

## Lemma checklist

**Track A — Case I producer (full-rank, KT §6.2).**
- [ ] **N4** `lem:rigidContract-isMinimalKDof` — graph↔matroid contraction-
  minimality bridge: `G.IsMinimalKDof n 0 ∧ H proper rigid ⟹ (G.rigidContract H
  r).IsMinimalKDof n 0`. Matroid side (`contraction_isMinimalKDof`) green; the
  content is the `matroidMG`-of-`(map ∘ deleteEdges)` correspondence — a
  **several-node Whitney-style build** (see the refined N4 recon below; the
  per-cycle-matroid `cycleMatroid_contract` does *not* apply). Sub-bricks:
  - [ ] **N4a** rigid subgraph's multiplied graph is connected (`H̃` connected on
    `V(H)`), licensing the `collapseTo r V(H)` vertex-collapse. *Leaf — the
    recommended next commit; see Hand-off.*
  - [ ] **N4b** cycleMatroid under the vertex-collapse `map` (Whitney contraction).
  - [ ] **N4c** union-level independence bridge via `ext_indep` against
    `matroidMG_indep_iff` + `Matroid.Indep.contract_indep_iff` (the `(D,D)`-boundary
    Whitney rank-of-contraction identity).
- [ ] **N5** `lem:case-I-splice-placement` — splice the inductive legs `(H,p₁)`,
  `(G/E',p₂)` along boundary hinges at panel intersections (eq. 6.6); needs a
  *panel-transversality* lemma + block-triangular independence (Lemma 5.1). Three
  KT sub-cases (6.2/6.3/6.5). Research-shaped — decompose math-first.
- [ ] **N6** `lem:case-I-realization` — compose N4 + N5 + the green glue
  (`isInfinitesimallyRigidOn_union_of_inter`) + device ⇒ discharges
  `theorem_55.hcontract`.

**Track B — Case II/III producer at `d=3` (the crux, KT §6.3 + §6.4.1).**
- [ ] eq. (6.12) degenerate placement (`p1(vb)=q(ab)` reproduces the `e₀` row;
  the green N7b-0/1/2/3 + glue feed it) — gives `+(D−1)`, one short.
- [ ] **Lemma 6.10** (`d=3`, 3 candidates): Claim 6.11 (combinatorial↔linear,
  redundant `ab`-row), Claim 6.12 (extensor-span genericity via Lemma 2.1).

**Assembly (may defer to Phase 23 with Thm 5.5's completion).**
- [ ] `prop:rigidity-matrix-prop11` `hub` brick (Phase-19 partition count).
- [ ] `thm:theorem-55` flips green once the producers land.

## Decisions made during this phase

### Phase-local choices and proof techniques
- **N4 constructibility recon (2026-06-04, before any build).** Ran the producer
  recon (`blueprint/CLAUDE.md` *the honesty gate*, second half) on N4. **Finding:
  N4 is the graph↔matroid correspondence Phase 20 deliberately deferred, and the
  underlying matroid fact is non-trivial — not the one-commit "build-shaped" node
  the launch plan implied.** The target equality is
  `matroidMG (G.rigidContract H r) = matroidMG G ／ E(H̃)`. Edge-set check: both
  grounds equal `(E(G) \ E(H)) × Fin D`, so the ground sets *do* match. But:
  - `M(G̃)` is the `D`-fold *union* of cycle matroids restricted to `E(G̃)`
    (`Deficiency.lean:141`). **`Matroid.Union` does not commute with contraction**
    in general (`Union Mᵢ ／ C ≠ Union (Mᵢ ／ C)`), so the per-cycle-matroid fact
    `cycleMatroid_contract` (vendored `Matroid/Graphic.lean:177`,
    `(G/[E(H),φ]).cycleMatroid = G.cycleMatroid ／ E(H)`) does **not** push
    through the union to give the whole-`matroidMG` equality directly.
  - **Refinement (2026-06-04, second recon — sharper than the bullet above).**
    `cycleMatroid_contract` does not even *apply* to the per-cycle-matroid step,
    let alone fail to push through the union. The recon above pictured the matroid
    side as `cycleMatroid ／ E(H̃)` (a genuine matroid contraction by the
    contracted-out fibers) and the graph side as the same contraction. But the
    *graph* `rigidContract` is `(G ＼ E(H)).map (collapseTo r V(H))` — a pure
    **vertex-relabel `map`** with the contracted edges `E(H)` *deleted* (so on the
    cycle-matroid side those fibers are gone, not contracted). On the matroid side,
    `M(G̃) ／ E(H̃)` *contracts* those same fibers. Reconciling a graph that
    *deletes* `E(H)` and *relabels vertices* with a matroid that *contracts* `E(H̃)`
    is the classical Whitney fact "contracting a connected edge set in the cycle
    matroid = collapsing its vertex set in the graph" — and there is **no vendored
    `cycleMatroid`-under-`map`/iso lemma** (checked: `Matroid/Graphic.lean` has
    `cycleMatroid_{restrict,deleteEdges,contract,deleteVerts_isolatedSet}`, no
    `cycleMatroid_map`). `cycleMatroid_contract`'s own hypothesis
    `(G ＼ E(H) ↾ E(H)).connPartition.IsRepFun (collapseTo r V(H))` is *false* here:
    `G ＼ E(H) ↾ E(H)` has empty edge set (discrete connPartition), so collapsing all
    of `V(H)` to `r` is not a rep-fun. So the per-cycle-matroid step is itself a
    from-scratch build (cycleMatroid under vertex-collapse map), and it bottoms out
    on **connectivity of `H̃`** (rigid ⟹ packs `D` spanning trees ⟹ connected on
    `V(H)`, so the collapse is the legitimate connected-contraction).
  - The whole green substrate (`contract_matroidMG_deficiency_eq`,
    `contract_minimality_transport`, `contraction_isMinimalKDof`) reasons
    *directly on the matroid contraction* `M(G̃)／E(H̃)` and explicitly says "No
    graph↔matroid `map` correspondence is needed" — precisely because the
    correspondence is the deferred hard part.
  - The viable route is **independence-level** (`Matroid.ext_indep`), mirroring
    how `matroidMG_restrict_mulTilde` (`Deficiency.lean:212`) handled *restriction*
    via the sparsity characterization `matroidMG_indep_iff` rather than a union
    identity. The graph side is favorable: `rigidContract = (G.deleteEdges
    E(H)).map (collapseTo r V(H))`, and `contract_eq_map_of_disjoint`
    (`Matroid/Graph/GraphLike/Contract.lean:78`) gives `G/[C,φ] = φ ''ᴳ G` when
    `Disjoint E(G) C` — which holds after `deleteEdges E(H)` (already green as
    `rigidContract_eq_contract`). But the `ext_indep` is **not** a `restrict`-style
    one-screen proof: contraction-independence (`Matroid.Indep.contract_indep_iff` /
    the basis form) reads `(M(G̃) ／ E(H̃)).Indep I ↔ I ⊓ E(H̃) = ∅ ∧ M(G̃).Indep (I ∪ J)`
    for an `M(G̃)`-basis `J` of `E(H̃)`, i.e. `(G̃ ↾ (I ∪ J))` is `(D,D)`-sparse;
    the RHS wants `(rigidContract.mulTilde ↾ I)` `(D,D)`-sparse. Equating those two
    sparsities is the **Whitney rank-of-contraction identity** at the `(D,D)`
    boundary regime (the collapse changes `spanningVerts` counts by `|V(H)|−1`),
    *not* a congruence like `isSparse_restrict_mulTilde_congr`. **Budget N4 as a
    several-node sub-build** (connectivity-of-`H̃` brick → cycleMatroid-under-collapse
    → union-level independence bridge), not one commit; or pivot to **Track A's N5 /
    Track B** (N4 gates only N6, the Case-I composer).

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN
- *(none yet — the N4 recon lesson is already captured by `DESIGN.md`
  *Constructibility recon before a producer build*; this is its first
  application post-21b.)*

## Blockers / open questions

- **N4 difficulty (above, refined twice).** The graph↔matroid bridge is a
  several-node Whitney-style build, not the union↔contraction one-liner the launch
  plan implied, and `cycleMatroid_contract` does not apply (the graph side is a
  vertex-relabel `map`, not an edge contraction). Decompose, don't attempt
  whole-hog.
- **N5 is equally research-shaped** (its blueprint proof note already says so), so
  it is not the clean fallback the launch hand-off treated it as. **Track B** (the
  Case II/III producer) is also a multi-node crux. The phase has *no* clean
  single-commit next node among the named producers; the unblocking move is to
  build the leaf bricks first (below).

## Hand-off / next phase

**No named producer (N4/N5/Track B) is a clean single-session commit** — the
launch hand-off's "do N4, fall back to N5" was optimistic on both. Two recons
(this session's is the second) place N4's matroid bridge as a several-node
Whitney-style build; N5/Track B are research-shaped by their own blueprint notes.

**Recommended next concrete commit:** the leaf-most brick that *any* of these need
— **N4a, connectivity of a rigid subgraph's multiplied graph** (`H.IsKDof n 0 ⟹ H̃`
connected on `V(H)`): a self-contained `Graph`-level fact in `Deficiency.lean` (it
owns `IsRigidSubgraph`/`matroidMG`), with no dependency on the matroid bridge. It
is the hypothesis a `cycleMatroid`-under-vertex-collapse argument needs to license
the `collapseTo r V(H)` collapse (a disconnected `H` collapses several components
to one `r`, which is *not* the connected contraction the cycle matroid sees), and
it is reusable by Track A's N5 splice (which orients hinges along a spanning forest
of `H`). **Substrate already in `Deficiency.lean`:** the cut-labeling deficiency
machinery `two_le_crossingEdges_of_isKDof_zero` (`lem:two-edge-conn`, KT 3.1) +
`cutLabeling` / `numParts_cutLabeling` — a disconnected `H` admits a *crossing-free*
cut, whose `cutLabeling` partition witnesses `partitionDef ≥ D > 0` via
`partitionDef_le_deficiency`, contradicting `def(H̃) = 0`. So N4a is "0-dof ⟹
connected", proved by the same cut-partition contradiction, *not* a fresh device.
It does not flip a blueprint node on its own (infrastructure below N4), so **no
`\leanok` flip** that commit. Then build N4b/N4c with it in hand.

*If a producer is preferred over infrastructure:* **N5**
`lem:case-I-splice-placement`, decomposed math-first per its blueprint proof note
(boundary-panel intersection + block-triangular independence each break into
sub-lemmas) — start with the **panel-transversality** lemma (two generic
`(d−1)`-panels meet in a `(d−2)`-hinge), the one genuinely new geometry. The KT
math is in `notes/Phase21b.md` *Finding A* (Case I tractable) and the
`algebraic-induction.tex` `lem:case-I-splice-placement` proof sketch.
