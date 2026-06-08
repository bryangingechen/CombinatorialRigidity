# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. Design-reconned in
`notes/Phase22-realization-design.md` §1.33 (A)/(B); this note is the canonical home for
that recon's verdict. KT §6.4.1 (Lemma 6.10) at the `k=0`/`d=3` scope.

## Current state

**Just landed: L5-pack, the candidate-completion `panelRow ∘ j` family identity + count**
(`PanelHingeFramework.candidateCompletion_panelRow_packaging`, CaseI.lean). Ties the candidate
producer's abstract `Sum.elim (Sum.elim rn (Unit→hingeRow u w ρ)) ro` family to the
`fun i => panelRow ends (j i)` shape the L0 spine carries (the device feed
`hasFullRankRealization_of_independent_panelRow_index`'s shape): given `rn`/`ro` already as panelRows
(L1) and the `Unit`-summand realized via L3 as `panelRow ends (e_a,ta,tb)` (with
`ρ = annihRow (C(e_a)) ta tb`, `ends e_a = (u,w)`), the family is *definitionally* `panelRow ends ∘ j`
for the L5-inj index map — `funext`/`rcases`/`rfl`, graph-free (no §38). Plus the eq.-(6.29) count
`D(|V|−1) ≤ |(sn ⊕ Unit) ⊕ so|` from the L1 block counts: `((D−1)+1)+D(m−2) = D(m−1)` for `m ≥ 1`
(same arithmetic as `case_II_placement_eq612`'s inline count). **(F1) resolved as stated** (§1.34): the
producer `ρ` is realized as a single `annihRow` pair, so the `Unit` summand IS one `panelRow` — no
device-feed restatement needed. Fully green, sorry-free (axioms = `propext`/`Classical.choice`/
`Quot.sound`), warning-clean, lint clean.

**Next concrete step (smallest forward commit): L-wire — thread L1–L5 into the L0 spine.** All leaves
are now green (L0 spine + L1 blocks + L2 span + L3 candidate-row-as-panelRow + L4 membership + L5-inj +
L5-pack). The next commit builds the actual `case_III` producer that *invokes* `case_III_hsplit_producer`
by discharging its carried hypotheses: run a candidate producer (`linearIndependent_sum_{p2,p3,augment}_candidateRow`)
on the L1 `so`/`sn` blocks + L2 `hspan` (with `ρ := annihRow (C(e_a)) ta tb`) to supply each `hselᵢ`,
feed `candidateCompletion_panelRow_packaging` for each `hfamᵢ`/`hcardᵢ`, and `candidateCompletion_index_injective`
(needs the new `hso_ne_ea` fact — L1 emits only `hso_ne_eb`; supply it: both `e_a`/`e_b` link the fresh
`v ∉ V(Gᵥ)`, so no `Gᵥ`-edge is either) for each `hjᵢ`. Then supply the Claim-6.12 selection data
(`hr`/`hp`/`hduality`) from `exists_candidate_row_eq612` + N3b. Assess whether L-wire is one commit or
splits per-candidate when it opens.

(L0 spine, landed earlier this phase: `PanelHingeFramework.case_III_hsplit_producer` carries the
candidate-selection data + each candidate's `panelRow`-packaging as explicit `h…` and composes
`case_III_eq629_conditional` → `…_index` per disjunct; `case_III_eq629_conditional` generalized to
three index types — one-line signature edit, FRICTION `[resolved]`.)

After L-wire builds the actual producer: instantiate `theorem_55 (n:=2) (k:=2)` with it + the green
`hcontract` (`case_I_realization`) and `hbase` (`theorem_55_base`); feed that into
`rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound is already green, discharged in-proof);
do the Thm 5.5→5.6 multigraph push (`lem:motions-mono-of-graph-le`). Milestone: the molecular
conjecture proved at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma 6.13) is
**Phase 23** (reuse map: §1.33 (C)).

**All leaves L0–L5 green; L-wire remains.** §1.34 cracked the producer core into L0–L5; L0 (the
spine) is green-modulo, L1 (block extraction) + L2 (span bridge) + L3 (candidate-row-as-panelRow) +
L4 (candidate-row membership) + L5-inj (index-map injectivity) + L5-pack (the `panelRow ∘ j` family
identity + count) all green. L-wire (invoke `case_III_hsplit_producer`, discharging its carried
`hselᵢ`/`hfamᵢ`/`hjᵢ`/`hcardᵢ` from the leaves + the candidate producers) is the next step before the
`theorem_55` instantiation. The phase-open red-node + supersession + label-resolution gates ran clean
at open.

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
  - [x] **L3 — the candidate-row-IS-a-panelRow leaf** (`BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends`,
    Pinning.lean). The `+1` `Unit`-summand candidate row `hingeRow u w ρ` = `panelRow ends (e,t₁,t₂)`
    (where `ρ = annihRow (C(p(e))) t₁ t₂`, `ends e = (u,w)`), so it lands at an `(edge,⋀ᵏ-pair)` index
    of L5's `j`. Proof = `rw [panelRow, hends]`. **§38 trap did NOT bite** — graph-free (`panelRow` reads
    only `ends`/`supportExtensor`), so the general `BodyHingeFramework`-level form is the answer; the
    design's `ofNormals` round-trip helper was not needed. Green, sorry-free. (2026-06-07)
  - [x] **L4 — candidate-row membership** (`BodyHingeFramework.panelRow_mem_rigidityRows_of_link`,
    Pinning.lean). `e_a` links `v a` *directly* in `G` (`hlink`/`hG_ea`) ⟹ `panelRow_mem_rigidityRows`
    (after `rw [hends]`) for the `+1` summand — the direct-link analog of `case_II_placement_eq612`'s
    `hGv`-routed membership step. Closes the F2 gap. One-liner, graph-free (no §38). Green, sorry-free.
    (2026-06-07)
  - [x] **L5-inj — the candidate-completion index-map injectivity**
    (`PanelHingeFramework.candidateCompletion_index_injective`, CaseI.lean). `j` over `(sn ⊕ Unit) ⊕ so`
    placing `sn→e_b`, `Unit→e_a`, `so→Gᵥ`-edges is injective — the candidate analog of
    `case_II_placement_eq612`'s inline `hjinj`, abstract (3 disjointness facts in), graph-free (no §38).
    Green, sorry-free. (2026-06-07)
  - [x] **L5-pack — the `panelRow ∘ j` family identity + count**
    (`PanelHingeFramework.candidateCompletion_panelRow_packaging`, CaseI.lean). Ties the candidate
    producer's abstract `Sum.elim` family to `fun i => panelRow ends (j i)`: `rn`/`ro` are `panelRow`s
    of `sn`/`so`-vals, the `Unit`-summand `hingeRow u w ρ = panelRow ends (e_a,ta,tb)` via L3 once
    `ρ = annihRow (C(e_a)) ta tb` ((F1) resolved as stated — no device-feed restatement). Count
    `D(|V|−1) = ((D−1)+1)+D(m−2)`, `m ≥ 1`. `funext`/`rcases`/`rfl` identity (graph-free, no §38) +
    the `case_II_placement_eq612` count arithmetic. Green, sorry-free. (2026-06-07)
- [ ] **L-wire — invoke the L0 spine to build the actual `case_III` producer.** Run a candidate
  producer per branch on the L1 blocks + L2 span (with `ρ := annihRow (C(e_a)) ta tb`) for `hselᵢ`,
  feed `candidateCompletion_panelRow_packaging` for `hfamᵢ`/`hcardᵢ`, `candidateCompletion_index_injective`
  (needs the new `hso_ne_ea` fact) for `hjᵢ`, and the Claim-6.12 selection data from
  `exists_candidate_row_eq612` + N3b.
- [ ] **`d=3`-instance `theorem_55` node** (B.2) — instantiate `theorem_55 (n:=2) (k:=2)` on the
  three green branch args; add the small green blueprint node the molecule-app chapter consumes.
- [ ] **`lem:case-II-realization` / `lem:case-III` flip green** — once the producer + instance land.
- [ ] **Thm 5.5→5.6 push + feed `rigidityMatrix_prop11`'s `hgen`** — unblocks Cor 5.7 at `d=3`.

## Blockers / open questions

- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38; carried from 22a–e) was
  the standing engineering risk, confined to L3 by the §1.34 cut — **and L3 dodged it entirely**: the
  candidate-row-as-panelRow identity is graph-free (`panelRow` reads only `ends`/`supportExtensor`),
  so the general `BodyHingeFramework`-level `rw [panelRow, hends]` form needs no `ofNormals` framework
  to compute. No `panelRow_ofNormals_candidate_eq` round-trip. The trap is now off the `d=3` path.
- **No math blockers.** (B.1)/(B.2) resolved; the `d=3` contrapositive (Claim 6.12 + candidate
  completion + N3b) is fully green; the producer is plumbing-on-green-bricks. Three structural facts
  de-risk the leaves (§1.34): F1 the candidate row IS a `panelRow` (so it places at an edge for `j`),
  F2 `case_II_placement_eq612` already only needs `Gv ≤ G` for ONE membership step (transport is
  graph-free, reused verbatim), F3 the candidate producers need the full hinge-row block span (L2,
  green bricks).

## Hand-off / next phase

**Smallest next commit: L-wire — invoke `case_III_hsplit_producer` to build the actual `case_III`
producer.** All leaves L0–L5 are green: L1 (`case_III_old_new_blocks`) gives the OLD/NEW blocks +
`hane`/`hnewne`, L2 (`span_panelRow_comp_single_of_edge`) gives the FULL hinge-block span, L3
(`panelRow_eq_hingeRow_annihRow_of_ends`) identifies the `+1` candidate row as a `panelRow`, L4
(`panelRow_mem_rigidityRows_of_link`) gives that row's `rigidityRows` membership, L5-inj
(`candidateCompletion_index_injective`) gives the injective index `j` over `(sn ⊕ Unit) ⊕ so`, and
L5-pack (`candidateCompletion_panelRow_packaging`) gives the `panelRow ∘ j` family identity + count.
L-wire discharges the spine's carried hypotheses: per candidate, run
`linearIndependent_sum_{p2,p3,augment}_candidateRow` (with `ρ := annihRow (C(e_a)) ta tb`) on the L1
blocks + L2 `hspan` for `hselᵢ`, `candidateCompletion_panelRow_packaging` for `hfamᵢ`/`hcardᵢ`,
`candidateCompletion_index_injective` for `hjᵢ` (supply the **new `hso_ne_ea` fact** L1 doesn't emit —
both `e_a`/`e_b` link the fresh `v ∉ V(Gᵥ)`, so no `Gᵥ`-edge equals either), and supply the Claim-6.12
selection data `hr`/`hp`/`hduality` from `exists_candidate_row_eq612` + N3b. Assess whether it is one
commit or splits per-candidate when it opens. Then the `theorem_55` instantiation (B.2 node), the
`lem:case-II-realization` / `lem:case-III` flips, and the Thm 5.5→5.6 push. Full leaf shapes, the `j`
bridge, and the three structural facts: `notes/Phase22-realization-design.md` §1.34.

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d`
(KT Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1 verbatim;
generalize the candidate chain on the graph-free assembly; build the `⋀^{d−1}` duality via the
top-power route per §1.33 (D), reusing 22f's already-landed `map`-range infra; reuse the existing
alg-independence machinery for the points). Open Phase 23 with its own recon (read eqs. 6.46–6.67
against the `d=3` Lean) and add the general-`d` alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **L5-pack landed: the candidate-completion `panelRow ∘ j` family identity + count (2026-06-07).**
  `PanelHingeFramework.candidateCompletion_panelRow_packaging` (CaseI.lean, next to L5-inj): ties the
  candidate producer's abstract `Sum.elim (Sum.elim rn (Unit→hingeRow u w ρ)) ro` family to the
  `fun i => panelRow ends (j i)` shape the L0 spine carries. With `rn`/`ro` as panelRows (L1) and the
  `Unit` summand realized via L3 as `panelRow ends (e_a,ta,tb)` (`ρ = annihRow (C(e_a)) ta tb`), the
  identity is `funext`/`rcases`/`rfl` (graph-free, no §38); the count `D(|V|−1) ≤ |(sn ⊕ Unit) ⊕ so|`
  is the `case_II_placement_eq612` arithmetic over the L1 block counts. **(F1) resolved as stated**
  (§1.34): `ρ` realized as a single `annihRow` pair, so the `Unit` summand IS one `panelRow` — the
  device-feed-restatement alternative was not needed. No new FRICTION (`Nat.card_unique`/`Nat.mul_succ`
  arithmetic + the established `Sum.elim`-`rfl` packaging idiom).
- **Leaves L0–L5-inj landed earlier this phase (2026-06-07; one-line record, full detail in the Lean
  source + git):**
  - L0 `case_III_hsplit_producer` (CaseI.lean) — the green-modulo spine carrying `hselᵢ`/`hfamᵢ`/`hjᵢ`/
    `hcardᵢ`, composing `case_III_eq629_conditional` → `…_index` per disjunct;
    `case_III_eq629_conditional` generalized to three index types (FRICTION `[resolved]`).
  - L1 `case_III_old_new_blocks` (CaseI.lean) — the front of `case_II_placement_eq612` re-exposed to
    output the OLD `so` / NEW `sn` blocks separately (verbatim proof; re-exposed since the packaged set
    hides the two-block split the `+1` augment needs).
  - L2 `span_panelRow_comp_single_of_edge` (Pinning.lean) — the candidate producers' `hspan` (pinned
    `D−1` rows span `hingeRowBlock e`), `eq_of_le_of_finrank_eq`; the `comp Φ` is identity at the pin.
  - L3 `panelRow_eq_hingeRow_annihRow_of_ends` (Pinning.lean) — F1, the candidate row IS a `panelRow`;
    `rw [panelRow, hends]`, graph-free so the §38 trap is off the `d=3` path entirely.
  - L4 `panelRow_mem_rigidityRows_of_link` (Pinning.lean) — the `+1` summand's `rigidityRows`
    membership at `e_a` via its *direct* `G`-link (closes F2); graph-free.
  - L5-inj `candidateCompletion_index_injective` (CaseI.lean) — `j` over `(sn ⊕ Unit) ⊕ so` injective,
    abstract over the three disjointness facts (incl. the new `hso_ne_ea` L1 doesn't emit); graph-free.
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
