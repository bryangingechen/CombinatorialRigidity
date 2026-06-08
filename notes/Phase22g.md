# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. Design-reconned in
`notes/Phase22-realization-design.md` §1.33 (A)/(B); this note is the canonical home for
that recon's verdict. KT §6.4.1 (Lemma 6.10) at the `k=0`/`d=3` scope.

## Current state

**Just landed: L2, the pinned-block span bridge** (`BodyHingeFramework.span_panelRow_comp_single_of_edge`,
Pinning.lean). Supplies the FULL hinge-block span `hspan : span (range (rn ∘ₗ single v)) =
F.hingeRowBlock e` the candidate producers (`linearIndependent_sum_p2/p3_candidateRow`,
`…_sumElim_candidateRow_iff`) need on top of the pinned independence: for an independent panel-row
subfamily of a transversal edge `e`, all using `e`, of full per-edge size `D−1`, the `v`-pinned span
equals the hinge-row block. Each pinned row IS the bare annihilator `annihRow (C(e)) t₁ t₂ ∈ r(p(e))`
(`single v` reads `v`, the distinct other endpoint `0`); `=` by equal `finrank D−1`
(`linearIndependent_panelRow_comp_single_of_edge` + `finrank_hingeRowBlock`), an
`eq_of_le_of_finrank_eq` leaf mirroring `exists_redundant_panelRow_of_edge_of_finrank_lt`'s `hrspan`.
The `comp Φ` the producers carry is identity at the pin (`columnOp hvb (single v x) = single v x`,
`b ≠ v`), so this feeds them directly. Fully green, sorry-free (axioms = `propext`/`choice`/`Quot.sound`),
warning-clean, lint clean.

**Next concrete step (smallest forward commit): L3 — the §38 defeq leaf, ISOLATED.** Align the
candidate placement's framework with the assembly + reuse L1's `hane`/`hnewne` extensor-nonzero
(`case_III_old_new_blocks`). Route through `…_index` WITHOUT a helper if the families are built directly
as `panelRow (ofNormals G ends q₀)` subfamilies; extract `panelRow_ofNormals_candidate_eq` (§38
`mem_infinitesimalMotions` round-trip) only if a `convert`/`rw` `whnf`-walls. The one engineering-risk
leaf; L0's green-modulo state lets it wall in isolation. See §1.34 / the checklist below for L3–L5
shapes; L4/L5 are green-brick plumbing.

(L0 spine, landed earlier this phase: `PanelHingeFramework.case_III_hsplit_producer` carries the
candidate-selection data + each candidate's `panelRow`-packaging as explicit `h…` and composes
`case_III_eq629_conditional` → `…_index` per disjunct; `case_III_eq629_conditional` generalized to
three index types — one-line signature edit, FRICTION `[resolved]`.)

After all of L1–L5 discharge the carried hypotheses: instantiate `theorem_55 (n:=2) (k:=2)` with it + the green
`hcontract` (`case_I_realization`) and `hbase` (`theorem_55_base`); feed that into
`rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound is already green, discharged in-proof);
do the Thm 5.5→5.6 multigraph push (`lem:motions-mono-of-graph-le`). Milestone: the molecular
conjecture proved at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma 6.13) is
**Phase 23** (reuse map: §1.33 (C)).

**Spine + L1–L2 green; L3–L5 remain.** §1.34 cracked the producer core into L0–L5; L0 (the spine)
is green-modulo, L1 (block extraction) + L2 (span bridge) green. The phase-open red-node +
supersession + label-resolution gates ran clean at open.

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

**Verdict: the build is safe to scope.** The one real gap is the `d=3` `hsplit` producer (now cracked
into L0–L5, §1.34); the `lem:cycle-realization` dependency is not Lean-load-bearing for it (B.1), and
the architecture call is settled (B.2). No deferred Lemma-5.4 sub-phase is a prerequisite for `d=3`
(it re-enters at the Phase-23 cycle base).

## Lemma checklist

- [x] **`lem:case-III-eq629-conditional` candidate-selection capstone** — `case_III_eq629_conditional`
  (`RigidityMatrix.lean`), the graph-free selection routing `case_III_claim612`'s disjunction through
  the three per-candidate full-family implications. Node flipped GREEN. (2026-06-07)
- [x] **Abstractly-indexed device-closure feed** — `hasFullRankRealization_of_independent_panelRow_index`
  (`GenericityDevice.lean`), the `Set`-free repackaging of the device closure consuming a finite
  `ι` + injective `j` (the shape of the candidate-completion's `Sum`-indexed output). The producer's
  packaging-out end-brick. Fully green, no defeq trap; internal infra (no blueprint node). (2026-06-07)
- **`d=3` `hsplit` producer — cracked into L0–L5** (§1.34; each a smallest-buildable commit):
  - [x] **L0 — `hsplit` skeleton green-modulo** (`PanelHingeFramework.case_III_hsplit_producer`,
    CaseI.lean). The spine: the producer carries the candidate families + `hselᵢ` + `hp`/`hduality`/`hr`
    + per-candidate `panelRow`-packaging (`q₀ᵢ`/`ιᵢ`/`jᵢ`/`hfamᵢ`/`hcardᵢ`) as explicit hypotheses; body
    `rcases`'s the Claim-6.12 disjunction (`BodyHingeFramework.case_III_eq629_conditional`) and feeds the
    winner to `…_index` per branch. Green-modulo, sorry-free. (2026-06-07)
  - [x] **L1 — IH → old/new block extraction** (`PanelHingeFramework.case_III_old_new_blocks`,
    CaseI.lean). The front of `case_II_placement_eq612` exposing the OLD block `so`
    (`holdindep`/`hold`/count/`so`-avoids-`e_b`) and NEW block `sn` (`hsn_e`/`hsn_indep`/`hnewpin`)
    separately + `hane`/`hnewne`. Graph-free over `ofNormals`. Green, sorry-free. (2026-06-07)
  - [x] **L2 — pinned-block span bridge** (`BodyHingeFramework.span_panelRow_comp_single_of_edge`,
    Pinning.lean). `rn`-pinned spans `F.hingeRowBlock e` ⟹ the `hspan` the candidate producers need:
    each pinned row IS `annihRow (C(e)) t₁ t₂ ∈ r(p(e))`, `=` by equal `finrank D−1`
    (`linearIndependent_panelRow_comp_single_of_edge` + `finrank_hingeRowBlock`). Small
    `eq_of_le_of_finrank_eq` leaf, mirrors `exists_redundant_panelRow_of_edge_of_finrank_lt`'s `hrspan`.
    Green, sorry-free. (2026-06-07)
  - [ ] **L3 — the §38 defeq leaf, ISOLATED.** Align the candidate placement's framework with the
    assembly + reuse `case_II_placement_eq612`'s `hane`/`hnewne` extensor-nonzero. **Route through `…_index`
    WITHOUT a helper if the families are built directly as `panelRow (ofNormals G ends q₀)` subfamilies;**
    extract `panelRow_ofNormals_candidate_eq` (§38 `mem_infinitesimalMotions` round-trip) only if a
    `convert`/`rw` `whnf`-walls. The one engineering-risk leaf; L0's green-modulo lets it wall in isolation.
  - [ ] **L4 — candidate-row membership.** `e_a` links `v a` in `G` (`hG_ea`) ⟹ `panelRow_mem_rigidityRows`
    for the `+1` summand (the F2 gap; analog of `case_II_placement_eq612`'s membership step for `e_a`).
  - [ ] **L5 — the `j`/`Sum.elim` packaging + injectivity.** `ι = (ιn ⊕ Unit) ⊕ ιo`; `j` places `ιn→e_b`,
    `Unit→e_a` (candidate row IS `panelRow ends (e_a,·)` by F1), `ιo→Gv`-edges. Injectivity is its own
    leaf (analog of `hjinj`, three disjoint edge-supports). Count `D(|V|−1) = ((D−1)+1)+D(|V_v|−1)`.
- [ ] **`d=3`-instance `theorem_55` node** (B.2) — instantiate `theorem_55 (n:=2) (k:=2)` on the
  three green branch args; add the small green blueprint node the molecule-app chapter consumes.
- [ ] **`lem:case-II-realization` / `lem:case-III` flip green** — once the producer + instance land.
- [ ] **Thm 5.5→5.6 push + feed `rigidityMatrix_prop11`'s `hgen`** — unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **The `ofNormals`/`withGraph` defeq-timeout trap** is the standing engineering risk (TACTICS-QUIRKS
  §38; carried from 22a–e *Blockers*) — now **confined to leaf L3** by the §1.34 cut. Mitigation:
  build the candidate families directly as `panelRow (ofNormals G ends q₀)` subfamilies (then the
  framework is one syntactic term and L3 needs no helper); else extract `panelRow_ofNormals_candidate_eq`
  (the `mem_infinitesimalMotions` round-trip). Budget for L3; not a math risk, and isolated.
- **No math blockers.** (B.1)/(B.2) resolved; the `d=3` contrapositive (Claim 6.12 + candidate
  completion + N3b) is fully green; the producer is plumbing-on-green-bricks. Three structural facts
  de-risk the leaves (§1.34): F1 the candidate row IS a `panelRow` (so it places at an edge for `j`),
  F2 `case_II_placement_eq612` already only needs `Gv ≤ G` for ONE membership step (transport is
  graph-free, reused verbatim), F3 the candidate producers need the full hinge-row block span (L2,
  green bricks).

## Hand-off / next phase

**Smallest next commit: build L3 — the §38 defeq leaf, ISOLATED.** L0–L2 are green: L1
(`case_III_old_new_blocks`) gives the OLD/NEW blocks + `hane`/`hnewne`, L2
(`span_panelRow_comp_single_of_edge`) gives the FULL hinge-block span the candidate producers need.
L3 is the one place real graph data meets the `ofNormals`/`withGraph` `whnf`/`isDefEq` trap: align the
candidate placement's framework with the assembly's `Sum.elim` output and reuse `case_II_placement_eq612`'s
`hane`/`hnewne` extensor-nonzero (now exposed by L1). Decide proactively: route through `…_index`
WITHOUT a bespoke helper if the candidate families are built directly as `panelRow (ofNormals G ends q₀)`
subfamilies (then `j` is identity-on-edge-index and the framework is one syntactic term); extract
`panelRow_ofNormals_candidate_eq` (the §38 `mem_infinitesimalMotions` round-trip) only if a single
`convert`/`rw` `whnf`-walls. L0's green-modulo state lets L3 wall in isolation. Then L4 (candidate-row
`rigidityRows` membership) + L5 (the `j`/`Sum.elim` packaging + injectivity), one green-brick-plumbing
leaf per commit. Then the `theorem_55` instantiation (B.2 node), the `lem:case-II-realization` /
`lem:case-III` flips, and the Thm 5.5→5.6 push. Full leaf shapes, the `j` bridge, and the three
structural facts: `notes/Phase22-realization-design.md` §1.34.

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d`
(KT Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1 verbatim;
generalize the candidate chain on the graph-free assembly; build the `⋀^{d−1}` duality via the
top-power route per §1.33 (D), reusing 22f's already-landed `map`-range infra; reuse the existing
alg-independence machinery for the points). Open Phase 23 with its own recon (read eqs. 6.46–6.67
against the `d=3` Lean) and add the general-`d` alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **L2 landed: the pinned-block span bridge, an `hrspan`-mirror leaf (2026-06-07).**
  `BodyHingeFramework.span_panelRow_comp_single_of_edge` (Pinning.lean, next to its independence
  companion `linearIndependent_panelRow_comp_single_of_edge`) gives the candidate producers' `hspan`:
  for an independent `D−1`-size panel-row subfamily of a transversal edge `e`, the `v`-pinned span
  equals `F.hingeRowBlock e`. Proof = `eq_of_le_of_finrank_eq`: `⊆` since each pinned row IS the bare
  `annihRow (C(e)) t₁ t₂ ∈ r(p(e))` (`single v` reads `v`, distinct other endpoint `0`), `=` by equal
  `finrank D−1`. Two design notes: (a) the family lands in the *small* dual `Dual ℝ (ScrewSpace k)`
  (always finite-dim), so `↥s` finiteness comes from `LinearIndependent.finite` — no `[Finite α]`
  needed; (b) the producers' `comp Φ` is identity at the pin (`columnOp hvb (single v x) = single v x`,
  `b ≠ v`), so the plain-`single v` span feeds them. No new FRICTION (the coerced-index projection trap
  hit is the resolved FRICTION line 776 pattern — `rintro ⟨⟨i, hi⟩, rfl⟩`).
- **L1 landed: the IH → old/new block extraction, the front of `case_II_placement_eq612` re-exposed
  (2026-06-07).** `PanelHingeFramework.case_III_old_new_blocks` (CaseI.lean) takes the same setup as
  `case_II_placement_eq612` (IH-rigid `ofNormals Gv ends q`, the eq.-(6.12) shear seed `q₀`) but
  outputs the OLD block `so` and NEW block `sn` *separately* — instead of packaging them into one
  `D(|V|)−1`-size set — so each candidate placement appends its own `+1` row. Output shape matches the
  candidate producers' inputs (`hold`/`holdindep` ← `so`; `hsn_e`/`hsn_indep`/`hnewpin` ← `sn`; the
  `so`-avoids-`e_b` disjointness fact for L5's `j`; `hane`/`hnewne` for L3). The full hinge-block span
  `hspan` the producers also need stays L2. Proof is `case_II_placement_eq612` lines 2649–2756 verbatim
  (no new tactics); chose re-exposure over re-using `case_II_placement_eq612` directly since its packaged
  set hides the two-block split the candidate `+1` augment needs.
- **L0 landed: the `hsplit` producer spine green-modulo; `case_III_eq629_conditional` generalized to
  three index types (2026-06-07).** `PanelHingeFramework.case_III_hsplit_producer` (CaseI.lean) carries
  the candidate-selection data + each candidate's `panelRow`-packaging (`q₀ᵢ`/`ιᵢ`/`jᵢ`/`hfamᵢ`/`hcardᵢ`)
  as explicit hypotheses and composes `case_III_eq629_conditional` → `…_index` per disjunct (6-line proof).
  The selection capstone was minted with one shared index `ιfam`; the three candidates genuinely differ
  (`M₁` is `(rn ⊕ Unit) ⊕ ro`), so it was generalized to `{ιfam₁ ιfam₂ ιfam₃}` — one-line signature edit,
  `.imp` proof unchanged. FRICTION `[resolved]`. Confirms the green-modulo-skeleton route below: the spine
  is now plumbing-on-green-bricks, L1–L5 named, §38 trap confined to L3.
- **`hsplit` producer core cracked: green-modulo-skeleton-first, defeq trap isolated to one leaf
  (2026-06-07).** Decided the green-modulo-skeleton route (state the producer carrying the residual
  graph-data obligations as explicit `h…`, flip the spine first, discharge each as a leaf) over
  all-at-once — it converts the "multi-session blob" into L0–L5 and confines the §38 trap to L3.
  Three structural facts found in the Lean de-risk the leaves: F1 the candidate row IS a `panelRow`
  (placeable at an edge for `j`), F2 `case_II_placement_eq612` only needs `Gv ≤ G` for ONE membership
  step (transport graph-free, reused verbatim), F3 candidate producers need the full hinge-row-block
  span (L2, green bricks). Full cut + `j` bridge + leaf shapes: `notes/Phase22-realization-design.md` §1.34.
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
