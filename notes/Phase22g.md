# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. Design-reconned in
`notes/Phase22-realization-design.md` §1.33 (A)/(B); this note is the canonical home for
that recon's verdict. KT §6.4.1 (Lemma 6.10) at the `k=0`/`d=3` scope.

## Current state

**Just landed: L5-inj, the candidate-completion index-map injectivity leaf**
(`PanelHingeFramework.candidateCompletion_index_injective`, CaseI.lean). The candidate-completion
index `j = Sum.elim (Sum.elim (sn-vals) (const (e_a,ta,tb))) (so-vals)` over `(sn ⊕ Unit) ⊕ so` is
injective — the candidate analog of `case_II_placement_eq612`'s inline `hjinj` (two-block `sn ⊕ so`),
now with the extra `Unit` summand at `e_a`: three pairwise-disjoint edge-supports (`sn`→`e_b`,
`Unit`→`e_a`, `so`→`Gᵥ`-edges ≠ `e_b`,`e_a`; `e_a ≠ e_b`). Abstract (caller supplies the three
disjointness facts as `hsn_e`/`hso_ne_eb`/`hso_ne_ea`), graph-free (reads only edge labels, no §38
trap). Fully green, sorry-free (axioms = `propext`/`Quot.sound`), warning-clean, lint clean.

**Next concrete step (smallest forward commit): L5-pack — the `j`/`Sum.elim` `panelRow ∘ j` packaging.**
With injectivity now its own leaf (`candidateCompletion_index_injective`), L5-pack ties the candidate
producer's abstract `Sum.elim (Sum.elim rn (Unit→hingeRow v a ρ)) ro` family
(`linearIndependent_sum_{p2,augment}_candidateRow` on the L1 blocks + L2 span) to the
`fun i => panelRow ends (j i)` shape the device feed
(`hasFullRankRealization_of_independent_panelRow_index`) needs: `rn i = panelRow ends (sn-val)`,
`ro i = panelRow ends (so-val)`, and the `Unit`-summand `hingeRow v a ρ = panelRow ends (e_a,ta,tb)`
**once `ρ` is realized as `annihRow (C(e_a)) ta tb`** (the subtlety §1.34 (F1) glosses: the producer's
`ρ` is a general block functional in `r(p(e_a)) = (span C)^⊥`, NOT a priori a single `annihRow`; pick
the realizing pair via `span_annihRow_eq_dualAnnihilator` / route the device feed to accept the
`Sum.elim` family directly — assess which is smaller). Then feed `…_index` with this leaf + the
landed injectivity. Target count `D(|V|−1) = ((D−1)+1)+D(|V_v|−1)`. See §1.34 / the checklist below.

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

**Spine + L1–L4 + L5-inj green; L5-pack remains.** §1.34 cracked the producer core into L0–L5; L0
(the spine) is green-modulo, L1 (block extraction) + L2 (span bridge) + L3 (candidate-row-as-panelRow)
+ L4 (candidate-row membership) + L5-inj (the index-map injectivity) green. L5-pack (the
`panelRow ∘ j` family identity + count) is the last leaf before the spine's carried `hfamᵢ`/`hjᵢ`/
`hcardᵢ` discharge. The phase-open red-node + supersession + label-resolution gates ran clean at open.

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
  - [ ] **L5-pack — the `panelRow ∘ j` family identity + count.** Tie the candidate producer's abstract
    `Sum.elim` family to `fun i => panelRow ends (j i)`: `rn`/`ro` are `panelRow`s of `sn`/`so`-vals, the
    `Unit`-summand `hingeRow v a ρ = panelRow ends (e_a,ta,tb)` once `ρ` is realized as `annihRow (C(e_a)) ta tb`
    (the (F1) subtlety: producer `ρ` is a *general* block functional, realize via
    `span_annihRow_eq_dualAnnihilator` OR route the device feed to accept the `Sum.elim` family directly).
    Then feed `…_index` with this + L5-inj. Count `D(|V|−1) = ((D−1)+1)+D(|V_v|−1)`.
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

**Smallest next commit: build L5-pack — the `panelRow ∘ j` family identity + count.** L0–L4 + L5-inj
are green: L1 (`case_III_old_new_blocks`) gives the OLD/NEW blocks + `hane`/`hnewne`, L2
(`span_panelRow_comp_single_of_edge`) gives the FULL hinge-block span, L3
(`panelRow_eq_hingeRow_annihRow_of_ends`) identifies the `+1` candidate row as a `panelRow`, L4
(`panelRow_mem_rigidityRows_of_link`) gives that row's `rigidityRows` membership, and L5-inj
(`candidateCompletion_index_injective`) gives the injective index map over `(sn ⊕ Unit) ⊕ so`.
L5-pack: run a candidate producer (`linearIndependent_sum_p2_candidateRow` on the L1 blocks + L2 span)
and tie its abstract `Sum.elim` family to `fun i => panelRow ends (j i)` (the device feed
`…_index`'s shape), then feed `…_index` with the injectivity. **The one residual subtlety** (§1.34's
(F1) glosses it): the producer's candidate functional `ρ` is a *general* member of the block
`r(p(e_a)) = (span C)^⊥`, not a priori a single `annihRow (C(e_a)) ta tb`, so the `Unit`-summand
isn't literally one `panelRow` — either realize `ρ` as a specific pair via
`span_annihRow_eq_dualAnnihilator` (the block is spanned by the `annihRow` family) and choose the
candidate row from such a pair, or restate the device feed to accept a `Sum.elim` family of `panelRow`s
plus one block functional directly; assess which is the smaller commit when L5-pack opens. Count
`D(|V|−1) = ((D−1)+1)+D(|V_v|−1)`. Then the `theorem_55` instantiation (B.2 node), the
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

- **L5-inj landed: the candidate-completion index-map injectivity leaf (2026-06-07).**
  `PanelHingeFramework.candidateCompletion_index_injective` (CaseI.lean, next to the L0 spine): the index
  `j = Sum.elim (Sum.elim (sn-vals) (const (e_a,ta,tb))) (so-vals)` over `(sn ⊕ Unit) ⊕ so` is injective.
  The candidate analog of `case_II_placement_eq612`'s inline `hjinj` (its two-block `sn ⊕ so`), with the
  extra `Unit` summand for the candidate edge `e_a` — 9-way `rintro` case split, each cross-block clash
  closed by one of the three disjointness facts on the first coordinate (`e_a ≠ e_b`, `so` avoids both).
  Stated **abstractly** (the three facts as hypotheses `hsn_e`/`hso_ne_eb`/`hso_ne_ea`) so it is a clean
  reusable leaf and graph-free (reads only edge labels, no §38 trap). `hso_ne_ea` (so avoids `e_a`) is a
  NEW disjointness fact L1 does not yet output (it gives only `hso_ne_eb`); L5-pack must supply it (both
  `e_a`/`e_b` link the fresh `v ∉ V(Gᵥ)`, so no `Gᵥ`-edge is either). No new FRICTION (the established
  `Sum.elim`-injectivity idiom). Splits L5 into L5-inj (done) + L5-pack (the `panelRow ∘ j` identity).
- **L4 landed: the candidate-row `rigidityRows` membership leaf (2026-06-07).**
  `BodyHingeFramework.panelRow_mem_rigidityRows_of_link` (Pinning.lean, next to L3): given
  `ends e = (u,w)` + a direct `F.graph.IsLink e u w`, the panel row at `(e,t₁,t₂)` is a rigidity row.
  Proof = feed `panelRow_mem_rigidityRows` the link after `rw [hends]`. The candidate `+1` summand uses
  this at `e_a`/`hG_ea` — a *direct* `G`-link, contrasting the OLD block's `hGv`-routed
  `IsSubgraph.isLink_iff` step in `case_II_placement_eq612` (the F2 sole use of `Gv ≤ G`); closes the
  F2 gap. Graph-free (no §38), so the same general `BodyHingeFramework` form L3 took. No new FRICTION.
- **L3 landed (2026-06-07).** `BodyHingeFramework.panelRow_eq_hingeRow_annihRow_of_ends` (Pinning.lean):
  `panelRow ends (e,t₁,t₂) = hingeRow u w (annihRow (C(p(e))) t₁ t₂)` when `ends e = (u,w)` (F1, the
  `+1` candidate row IS a `panelRow`). Proof = `rw [panelRow, hends]`; the §38 `ofNormals` trap dodged
  by taking the graph-free `BodyHingeFramework` form (no `panelRow_ofNormals_candidate_eq` round-trip) —
  see *Blockers*. The trap is now off the `d=3` producer path entirely (L4/L5 graph-free plumbing).
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
  is now plumbing-on-green-bricks, L1–L5 named, §38 trap was confined to L3 (and L3 then dodged it).
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
