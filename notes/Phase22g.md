# Phase 22g — the `d=3` realization assembly: design program + leaf infrastructure (work log)

**Status:** ✓ complete (closed 2026-06-09). Closed as the **design-program + leaf-infrastructure
stratum** of the `d=3` assembly (the 22c→22d precedent: stratum complete, crux split forward). The
banner flips (`lem:case-II-realization` / `lem:case-III`, the `theorem_55` `d=3` instance) move to
**Phase 22h**, scoped to the corrected `d=3` assembly (`notes/Phase22h.md`). Cross-cutting design
history: `notes/Phase22-realization-design.md` §1.33–§1.49.

## What this phase delivered

1. **The `d=3` Case-III crux architecture, PINNED** (design §1.39–§1.40, supersedes §1.37/§1.38's
   B1): `case_III_claim612` restated to the premise-free **existential** conclusion
   `∃ q : six joins, r̂(join q) ≠ 0` — the ~5-line contrapositive through
   `eq_zero_of_annihilates_span_top` / `span_omitTwoExtensor_eq_top`. `hann` was only ever the
   internal `by_contra` negation, and the three-fixed disjunction is undischargeable (three
   2-extensors span ≤ 3 of `⋀²ℝ⁴`'s 6 dims; KT's lines are free). The producer consumes the
   existential because candidate supports are panel-meets (= join form): it builds its candidate at
   the witness join's line `L ⊂ Π(u)`.
2. **~15 axiom-clean leaves** (the checklist below): Leaf 1 (the existential restate), Leaf 2a/2b
   (join↔meet bridge + line-indexed candidate placement), R1 (homogeneous-vector Lemma 2.1 core +
   bare-LI consumer restate), R3 (splitOff simplicity for `|V| ≥ 4`), the graph-free Leaf-3 pieces
   (C2-feed assembly, line-data leaf), and the **GAP-2 bare→generic upgrade**
   `hasGenericFullRankRealization_of_rigidOn_ofNormals`.
3. **The recon program** (design §1.44–§1.49) that produced the **corrected remaining-work
   picture**, scoped with signatures and handed to Phase 22h: GAPs 1–5, the `|V|=3` triangle
   leaves T1–T4, the `M₃` third-panel complex G4a–G4e + G0, and the G4b branch-interface verdict
   **(β)** (full conditioned IH through the no-rigid branch).

**GAP history (one line each; full traces design §1.44–§1.49):** §1.44 surfaced GAPs 1–3; §1.45
landed the GAP-2 bare→generic upgrade (B-derive); §1.46's GAP-1 "dissolution" was retracted by
§1.47 (it orphaned `hgab`; its `|V|=3`-splitOff-is-double-edge-`K₂` finding stands); §1.48 (the
commissioned recon) scoped the `|V|=3` triangle base to T1–T4, confirmed the `|V|≥4` `.1`-wiring,
and surfaced **GAP 4** (the `M₃` third-panel dispatch, G4a–G4e); §1.49 (the G4b design pass)
decided **G4b (β)**, scoped G4a/G0/G4c/G4d/G4e with signatures, and surfaced + machine-verified
**GAP 5** (the `IsProperRigidSubgraph` single-vertex degeneracy — `hnoRigid` unsatisfiable as
defined; repair = `2 ≤ V(H).ncard`, KT p. 659's `1 < |V′|`).

## Lemma checklist (final ledger; all landed entries axiom-clean)

- [x] **Leaf 1 — `case_III_claim612` existential restate** (RigidityMatrix.lean; graph-free).
  Premise-free six-join existential; `case_III_eq629_conditional` deleted, its blueprint node
  folded into the re-greened `lem:case-III-claim612`.
- [x] **Leaf 2a — the join↔meet bridge** (PanelLayer.lean; graph-free).
  `panelSupportExtensor_eq_complementIso_extensor` + `panelSupportExtensor_join_eq_zero_of_eq_zero`;
  defined the dangling `lem:case-III-claim612-line-in-panel-union` capstone node.
- [x] **Leaf 2b — the line-indexed candidate placement** (PanelLayer/CaseI.lean; graph-free; the
  §1.40 CRUX verdict (B)). Seed-from-line core
  `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`, block placement
  `case_III_old_new_blocks_of_line` (arbitrary second normal `n'`), per-line criterion runner
  `case_III_full_family_of_line` (the `M₁` criterion runs at `e_a`).
- [x] **R1 — homogeneous core + consumer restate** (RigidityMatrix/Extensor/CaseI.lean).
  `exists_homogeneousIncidence_of_normals` (four LI `pbar` with eq.-(6.45) incidence rel. a real LI
  triple) + the affine-free Lemma 2.1 `omitTwoExtensor_linearIndependent_of_li`; both consumers +
  the producer take bare `pbar`. R1-affine dissolved (§1.42).
- [x] **R3 — splitOff simplicity, COMPLETE for `|V| ≥ 4`** (Operations/Deficiency.lean; §1.42/§1.43).
  `splitOff_simple` (criterion), `splitOff_simple_of_noRigid` (discharge),
  `isKDof_zero_of_triangle` (deficiency-partition route, not a rank computation),
  `triangle_isProperRigidSubgraph` + `splitOff_simple_of_noRigid_of_card`. ON the `|V|≥4` live
  route (supplies the GP `.1` conjunct → `hgab`, §1.47); does NOT cover `|V|=3` (→ T1–T4, 22h).
- [x] **Leaf 3 graph-free pieces**: C2-feed assembly `case_III_realization_of_line` (the candidate
  `+1` row routes through C1's `span`-membership, not the panelRow device feed) + line-data leaf
  `exists_line_data_of_homogeneousIncidence` / `omitTwoExtensor_eq_extensor_kept` (witness-line
  extraction, `hann`-free, bare-`pbar`).
- [x] **Leaf 3 GAP-2 bare→generic upgrade** `hasGenericFullRankRealization_of_rigidOn_ofNormals`
  (CaseI.lean; §1.45). Concrete rigid+linking-transversal `ofNormals` → all 5 generic-motive
  conjuncts at an alg-indep seed; the `case_I_realization` rank-polynomial block over a single
  graph; `L`-independent. Also T4's keystone (§1.48(1)).
- [x] **22g-opening infrastructure (2026-06-07, pre-§1.39):** C1/C2/C3 (fixed-framework `_const`
  device feed + single-candidate brick + L0 producer spine `case_III_hsplit_producer`), the three
  selector recasts, the `r̂` candidate-vector data (`exists_redundant_panelRow_ab_lam`), the `+1`
  row membership (`hingeRow_mem_rigidityRows`), row-block infra L0–L5. All survive the §1.39
  restate as the infra the 22h producer consumes.
- [x] **OBSOLETE on the `d=3` live route** (built for the removed `hann`; reusable, likely re-enter
  at Phase-23 join↔meet duality): `exists_hduality_witness_of_panel_incidence`,
  `exists_independent_perp_pair`, `omitTwoExtensor_homogenize_eq_extensor_kept`,
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`, the C5a/C5b six-join dispatch.
  All graph-free, axiom-clean, still in tree (§1.39).

**Moved to Phase 22h** (the corrected assembly; signatures canonical in design §1.48–§1.49):
G5 (the `IsProperRigidSubgraph` predicate repair, FIRST), G4b-impl
(`minimal_kdof_reduction_full` + the `theorem_55_generic` (β) branch restate), G4a-i/ii + G0,
T1–T4, G4c-i/ii, G4d-i/ii, the (β)-shaped `hsplit` producer (G4e dispatch; the §38 trap), Leaf 4
(`theorem_55_generic (n:=2)(k:=2)` instance), Leaf 5 (the banner flips + Thm 5.5→5.6 push).

## Hand-off / next phase

**Phase 22h — the corrected `d=3` assembly** (`notes/Phase22h.md`): build order (design §1.49(6))
G5 → G4b-impl → {G4a+G0 ∥ T1–T4 ∥ G4c} → G4d → the (β)-shaped producer + G4e → Leaf 4 → Leaf 5,
~13–18 commits. **Smallest first commit: G5 part 1** — strengthen `IsProperRigidSubgraph` to
`2 ≤ V(H).ncard` (Deficiency.lean:381) + the censused consumer re-proofs, per design §1.49(0).
After 22h (the conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d` (KT Lemma 6.13),
scoped with the §1.33 (C) reuse map; the obsolete-at-`d=3` join↔meet leaves re-enter there.

## Decisions made during this phase

### Phase-local choices and proof techniques (settled verdicts)

- **§1.49 G4b verdict (β)** — the `hsplit`/`hsplitGP` branches reshape to receive `hnoRigid` + the
  full conditioned IH (mirroring `hcontract`); KT-faithful (Lemma 6.10 receives (6.1) and runs
  Lemma 4.6 itself), minimal-ripple (`minimal_kdof_reduction`/`theorem_55`/green nodes untouched),
  and the full IH does NOT replace G4c — eq. (6.44) forces the SAME seed transported by `ρ`.
  GAP 5 surfaced + machine-verified in the same pass. Lesson promoted (see below): a route recon
  must check the route's *hypotheses are satisfiable* down to the base predicates.
- **GAP 1 final form (§1.46–§1.48)** — `|V|≥4` buildable (R3 split-simplicity → the GP `.1`
  conjunct → `hgab`); `|V|=3` a genuine hole (the splitOff is the non-simple double-edge `K₂`, so
  `.1` is unavailable by any route) realized directly via T1–T4 (KT 6.7(i)/5.4). §1.46's bare-`.2`
  re-route was retracted (§1.47, coordinator cross-check): it orphaned `hgab`. Lessons promoted to
  DESIGN.md / the coordinate-phase command: *a recon traces the route, not the statements*; *a
  re-route must re-verify every other carried obligation*.
- **GAP 2 (B-derive, §1.45)** — the producer builds the candidate to bare `HasFullRankRealization`
  and composes the single-graph upgrade (the motive's framework is existentially quantified; the
  eq.-(6.12) seed is `ℚ`-alg-dependent and need not itself be generic — KT's Lemma 5.2 "convert to
  nonparallel without decreasing rank", p. 678 + footnote 4). Design choices: take the concrete
  `ofNormals`+`hne` as input (the `_linking` rank polynomial needs `hne` at the seed); inline the
  `rigidityRows` membership witness (TACTICS-QUIRKS §38).
- **GAP 3 (A)** — `hnewtrans : LinearIndependent ![n_a + t•n', n_b]`: the bad-`t` set is ≤ 1 value
  (from `hgab`), a good `t ≠ 0` exists; folded into the 22h producer.
- **Leaf-1 architecture (§1.39)** — existential conclusion, drop `hann` entirely; chosen over
  §1.38's B1 (which kept a false-shaped three-fixed conclusion and `hann` as undischarged producer
  data, re-introducing the honesty-gate problem). Five `hduality`-discharge leaves went obsolete
  (reusable); effort-accounting flagged to the user.
- **Leaf-2/3 design points (one line each):** the `M₁` criterion runs at `e_a` (its `rn` is the
  `e_a`-block, not the `_of_line` `e_b`-NEW block); `case_III_old_new_blocks_of_line` shears `v`
  along an arbitrary `n'` (the fixed-`n_b` case got `vb`-transversality free from `hgab`; arbitrary
  lines pay the explicit `hnewtrans`); the candidate's *sheared* `va`-support carries the witness
  (`(-t)`-multiple, cancels under `r`); the candidate `+1` row feeds C1's `span`-membership `hsub`
  (it is not a single panelRow); the line-data leaf is the obsolete `hduality` witness with the
  annihilation deleted, stated against bare `pbar`.
- **R3 route (§1.42–§1.43)** — `isKDof_zero_of_triangle` via the `def ≤ 0` deficiency-*partition*
  route (`ciSup_le` + per-`f` label-pattern count), not the recon's over-engineered rank
  computation; R3 is `rigidContract_simple`'s sibling, no 2-edge-connectivity needed.
- **The corrected L-wire (§1.35)** — the placed `+1` row is fed at the fixed `ofNormals` placement
  via `exists_good_realization_const` (no genericity device); drove C1–C3.
- **(B.1)** the `d=3` `hsplit`/`theorem_55` path does NOT consume `lem:cycle-realization` (the
  `\uses` edge is KT-narrative; `minimal_kdof_reduction` has no cycle branch). **(B.2)** the
  `d=3`-instance node is `theorem_55_generic (n:=2)(k:=2)` projecting `.2` (R2 verdict (B), §1.41),
  not a standalone `theorem_55_dim3`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *The `ofNormals`/`withGraph` defeq-timeout trap + extract-a-generic-helper mitigation* → TACTICS-QUIRKS §38.
- *The §38 call-site variant: pass a heavy-carrier-typed arg as an explicit literal (via `fin_cases`)* →
  TACTICS-QUIRKS §38 (Phase 22g addendum).
- *The §38 membership-witness variant: inline the `rigidityRows` `⟨e,u,v,…,rfl⟩` witness* →
  TACTICS-QUIRKS §38.
- *Recon-traces-the-route + re-route-re-verifies-carried-obligations + hypotheses-satisfiable-down-to-base-predicates*
  → DESIGN.md *Constructibility recon before a producer build* + the coordinate-phase command (step 3).
- *The `(Matrix.of ![pi,pj]).mulVecLin x i = ![pi,pj] i ⬝ᵥ x` per-coordinate unfold* → FRICTION [resolved].
- *"row-LI ⟹ `mulVecLin` surjective" composition* → FRICTION [resolved].
- *The unit-normalized combination from a span-of-the-others membership* → FRICTION [mirrored].
- *The standard-basis `Basis.toDual` self-pairing is the dot product* → FRICTION [mirrored].
- *`rw [eq]` of a function-valued term over-rewrites its partial applications — narrow with
  `conv_lhs`/`nth_rewrite`* → TACTICS-QUIRKS §41.
