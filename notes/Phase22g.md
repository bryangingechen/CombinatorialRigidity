# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. KT §6.4.1 (Lemma 6.10) at the
`k=0`/`d=3` scope. Cross-cutting design history lives in `notes/Phase22-realization-design.md`
§1.33–§1.48; this note carries current state, the live leaf sequence, blockers, and hand-off.

## Current state

**The `d=3` Case-III crux architecture is PINNED (`notes/Phase22-realization-design.md` §1.39,
2026-06-09 design pass — supersedes §1.37/§1.38's B1).** `case_III_claim612` is restated to the
**existential conclusion** `∃ q : six joins, r̂(join q) ≠ 0` with **no `hann`/`hduality` premise**:
the honest proof is the ~5-line contrapositive `by_contra → push Not → eq_zero_of_annihilates_span_top
(span_omitTwoExtensor_eq_top hp)`, reusing the current body's span→r=0 machinery (verified to close via
`lean_multi_attempt`). `hann` was never a supplied premise — it is the internal `by_contra` negation.
The existential ranges over the **six joins only** (they span via Lemma 2.1), not the line continuum.

*(Settled §1.39 history: the existential restate made five `hduality`-discharge leaves obsolete on the `d=3`
route — `exists_hduality_witness_of_panel_incidence`, `exists_independent_perp_pair`,
`omitTwoExtensor_homogenize_eq_extensor_kept`, `extensor_join_…_dotProduct`, the C5a/C5b dispatch — kept as
reusable graph-free lemmas, likely re-entering at Phase-23 join↔meet duality; the contradiction core, `r̂`
data, C1/C2/C3, row-space criterion, L1/L2/L4 all survive. Full account: design §1.39.)*

**The genuine remaining math** is producer-internal: the candidate is the eq.-(6.12) degenerate placement
at the witness join's line `L ⊂ Π(u)` (a candidate support is a **panel-meet**, PanelHinge.lean:89 `rfl`, =
the join's `complementIso`/`extensor` form — so the candidate's hinge line IS the witness join's line). **That
degenerate placement is exactly the source of GAP 2** (the seed is `ℚ`-alg-dependent, so it cannot carry the
GP motive's `AlgebraicIndependent ℚ` conjunct directly — resolved by the bare→generic upgrade, §1.45) — see
the sub-obligation status below.

**⚠️ Corrected status (§1.47 cross-check + the §1.48 commissioned recon, 2026-06-09).** §1.46's "GAP-1
DISSOLVED" is retracted (§1.47 — the bare-`.2` re-route orphans `hgab`, whose only source is the GP `.1`
conjunct's `IsGeneralPosition`; `.1` is needed, not unused). The §1.48 recon then answered §1.47's two
questions against the Lean + KT pp. 664/677/680–691:
- **`|V(G)| = 3` — NEW but bounded work (~3–4 commits), and the floor of the whole `hsplit` recursion**
  (the `|V|=4` producer's `.1` conjunct IS the triangle's GP realization). The green cycle bricks
  (`theorem_55_base`, `rankHypothesis_zero_of_cycle`, `exists_independent_panelSupportExtensor`) do NOT
  assemble: wrong relative form / `Fin m` body type / free-pair (not cyclically-consistent) normals.
  Decomposed into leaves **T1–T4** (third-edge + vertex-pin; `theorem_55_triangle` brick; concrete basis
  seed; assembly through the landed GAP-2 upgrade) — full signatures in design §1.48(1).
- **`|V(G)| ≥ 4` — the §1.47 `.1`-wiring CONFIRMS (hgab/R3/GAP-3/GAP-2-upgrade all close; plus the N3a
  triple-LI needs the `.1` alg-indep conjunct, a new small bridge leaf), BUT the six-join dispatch trace
  surfaces GAP 4:** witnesses in the third panel `Π(c)` are geometrically unplaceable at `v`'s hinges; KT
  covers them with **`M₃`** — the second split `G_a^{vc}` at an *adjacent degree-2 pair* (Lemma 4.6 chain),
  realized at the SAME seed via the `ρ = (a v)` relabel (eqs. (6.43)–(6.44) make it test the same `r̂`).
  Missing: **G4a** (Lemma-4.6 chain dichotomy, not formalized), **G4b** (the `hsplit`/`hsplitGP` branch
  interface hands a fixed `(v,a,b)` + split-only IH — cannot express the choice; repair (α) chain-data
  branch vs (β) full-IH branch, UNDECIDED), **G4c** (`ρ`-relabel transport), **G4d** (the (6.44)
  `M₃`-candidate-row bookkeeping), **G4e** (the dispatch trichotomy). Full trace: design §1.48(2).

**Next concrete step — the GAP-4 interface design pass (G4b (α) vs (β)), NOT the producer build:** the
producer signature cannot be finalized until the branch-interface decision is made; that pass should also
scope G4a/G4c/G4d to leaves. The T1–T4 triangle leaves are independently buildable now (T1/T2/T3 have no
GAP-4 dependency) and are the safest parallel work. THEN the §38-trap producer + Leaf 4/5. The GAP-2
keystone is built:
`hasGenericFullRankRealization_of_rigidOn_ofNormals` (CaseI.lean, axiom-clean) — takes the concrete
rigid+linking-transversal `ofNormals G ends q₀` (`hends`/`hne`/`hnev`/`hrig`) and concludes the generic motive
by re-realizing at an alg-indep seed `q₁`: the rational rank polynomial `Q` of `G`/`ends` *only*
(`exists_rankPolynomial_of_rigidOn_linking`), non-root at `q₁` via the alg-indep eval bridge; the GP factor
`Qgp` likewise; the seed `q₁` carries the alg-indep conjunct. Body = the `case_I_realization` rank-polynomial
block over a *single* graph (no two-block splice). The §1.45 design pass settled GAP 2 **(B-derive)**: the
producer does NOT conclude
`HasGenericFullRankRealization` *at the degenerate seed* (impossible — the seed is `ℚ`-alg-dependent by
construction; the motive's framework is **existentially quantified**, PanelHinge.lean:1033), it builds the
candidate to **bare** `HasFullRankRealization` (Leaf 3) then invokes this upgrade. KT's "convert (G,p1) to
a nonparallel realization by Lemma 5.2 without decreasing rank" (KT p. 678); `L`-independent (rank
polynomial is a graph property, `L` discarded once full rank is witnessed).
**R3 (`splitOff_simple_of_noRigid_of_card`, `|V|≥4`) is COMPLETE** (2026-06-09): part (1)
`isKDof_zero_of_triangle` (Deficiency.lean) + part (2) the `htri` discharge (`triangle_isProperRigidSubgraph`
+ the hypothesis-free `splitOff_simple_of_noRigid_of_card`, Operations.lean) are axiom-clean. **Per §1.47 it
is back ON the `|V|≥4` live route** (it supplies `(G.splitOff …).Simple`, the antecedent that unlocks the GP
`.1` conjunct → `hgab`) — not "off the route" as §1.46 said. KT Lemma 6.7(ii), sibling of `rigidContract_simple`.
Full detail per leaf in the *Lemma checklist* + *Hand-off*; the checklist is the canonical done/open ledger.

**Sub-obligation status** (canonical traces §1.47 + §1.48):
- **GAP 1 — the `|V|=3` triangle base case: scoped (§1.48(1), leaves T1–T4, ~3–4 commits)** (§1.47
  retracted §1.46's "dissolved"; the `|V|≥4` route needs the GP `.1` conjunct — see the ⚠️ block).
  §1.46-(2) stands: the `|V|=3` triangle's splitOff is the non-simple double-edge `K₂` (the surviving
  `ab`-edge + the fresh `e₀`), so split-simplicity is genuinely unavailable there and the triangle is
  realized directly (KT 6.7(i)/5.4 = T1–T4).
- **GAP 4 — the `M₃` third-panel complex: OPEN, blocks the producer signature (§1.48(2), G4a–G4e).** The
  six-join dispatch needs KT's second-split candidate `M₃` for `Π(c)`-witnesses; needs the Lemma-4.6 chain
  (G4a), a branch-interface change (G4b, (α)/(β) undecided), the `ρ`-relabel transport (G4c), the (6.44)
  candidate-row bookkeeping (G4d), and the dispatch leaf (G4e).
- **GAP 2 — LANDED 2026-06-09 (the upgrade leaf; B-derive, §1.45).** R2's `hsplitGP` shape makes the
  producer conclude `HasGenericFullRankRealization`. The eq.-(6.12) candidate seed shears `v` to
  `n_a + t•n'` — `ℚ`-alg-dependent, so it cannot itself carry the `AlgebraicIndependent ℚ` conjunct — but
  the motive's framework is **existentially quantified** (PanelHinge.lean:1033). The producer builds the
  candidate to **bare** `HasFullRankRealization` (Leaf 3), then invokes the **single-graph bare→generic
  upgrade `hasGenericFullRankRealization_of_rigidOn_ofNormals`** (CaseI.lean, axiom-clean): takes the
  concrete rigid+linking-transversal `ofNormals G ends q₀` and builds the rational rank polynomial `Q`
  (`exists_rankPolynomial_of_rigidOn_linking`, depends on `G`/`ends` ONLY, NOT `L`/the seed), nonzero at the
  `exists_injective_algebraicIndependent_real` alg-indep seed `q₁` via the alg-indep eval bridge → a generic
  alg-indep rigid witness, all five conjuncts. **KT's "convert (G,p1) to a nonparallel realization by Lemma
  5.2 without decreasing rank" (KT p. 678 + footnote 4).** L-independent (graph property; `L` discarded once
  full rank is witnessed). Body = the `case_I_realization` rank-polynomial block over a single graph (no
  two-block splice). **Remaining:** the producer (Leaf 3) composes this onto the bare candidate, supplying
  the upgrade's `hne` (linking transversality) from its candidate completion.
- **GAP 3 — bounded (A), *given* `hgab`:** `hnewtrans : LinearIndependent ![n_a + t•n', n_b]` — the bad-`t`
  set is at most a single value (the affine line `t↦n_a+t•n'` is not in `span{n_b}` since `n_a∉span{n_b}` from
  the pairwise GP `hgab`), so a good `t≠0` exists. Bounded linear algebra — **but it consumes `hgab`**, the same
  hypothesis the `|V|=3` GAP-1 hole leaves unavailable (so GAP 3 closes only on the `|V|≥4` route).

Full traces: `notes/Phase22-realization-design.md` §1.48 (the commissioned recon: T1–T4 + GAP 4) + §1.47
(the `hgab` correction) + §1.45 (GAP-2 resolution) + §1.44 (the three sub-obligations) + §1.39–§1.43.

**Landed (all axiom-clean; off the to-do list):** Leaf 1 (existential `case_III_claim612`), Leaf 2a/2b
(join↔meet bridge + line-indexed candidate placement `case_III_old_new_blocks_of_line` +
`case_III_full_family_of_line`), R1 (homogeneous core `exists_homogeneousIncidence_of_normals` +
consumer-restate to bare LI `pbar`), R3 **for `|V|≥4`** (criterion `splitOff_simple` + discharge
`splitOff_simple_of_noRigid` + triangle-0-dof `isKDof_zero_of_triangle` + `htri` discharge
`triangle_isProperRigidSubgraph`/`splitOff_simple_of_noRigid_of_card`), and the graph-free Leaf-3 pieces
(C2-feed assembly `case_III_realization_of_line`, line-data leaf `exists_line_data_of_homogeneousIncidence`).
The Lemma checklist carries the per-leaf detail.

**Remaining (→ phase close): NOT all-routine (§1.47 + §1.48).** (i) The GAP-4 interface design pass (G4b
(α) vs (β)) then the G4a/G4c/G4d/G4e leaves; (ii) the `|V|=3` triangle leaves T1–T4 (~3–4 commits,
buildable now); (iii) the §38-trap concrete-seed producer (the confirmed `.1`-chain + the GAP-2 upgrade +
GAP-3 + the new triple-LI bridge); (iv) Leaf 4 (`theorem_55_generic (n:=2)(k:=2)` instance, project `.2`)
+ Leaf 5 (case-II/III flips + Thm 5.5→5.6 push). The larger KT proof (Lemma 6.10 / Claim 6.11) is already
green via Phases 22d/22e/22f. Milestone unchanged: the molecular conjecture at `d=3`, unblocking Cor 5.7
(Phases 24–26). General `d` (KT Lemma 6.13) is **Phase 23** (§1.33 (C)).

## Lemma checklist — the live leaf sequence (§1.39)

- [x] **Leaf 1 — `case_III_claim612` existential restate** (2026-06-09; RigidityMatrix.lean; graph-free,
  axiom-clean). Conclusion `∃ q : six joins, r̂(join q) ≠ 0`, no premise; producer carries the single
  green-modulo `hcand`. `case_III_eq629_conditional` deleted; blueprint node folded into
  `lem:case-III-claim612`. Detail: Lean doc-comments + design §1.39.
- [x] **Leaf 2a — the join↔meet bridge** (2026-06-09; PanelLayer.lean; graph-free, axiom-clean).
  `panelSupportExtensor_eq_complementIso_extensor` + the producer-direction transfer
  `panelSupportExtensor_join_eq_zero_of_eq_zero`; defined the dangling
  `lem:case-III-claim612-line-in-panel-union` capstone node. Detail: doc-comments + §1.39(b)/(c).
- [x] **Leaf 2b — the line-indexed candidate placement** (2026-06-09; PanelLayer/CaseI.lean; graph-free,
  axiom-clean; four commits + the §1.40 CRUX recon, verdict (B)). Seed-from-line core
  `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` (`(-t)•C(L)`, shear rescales but never
  moves the line); block placement `case_III_old_new_blocks_of_line` (arbitrary second normal `n'`;
  explicit `hL`/`hnewtrans` — the fixed-`n_b` case got both free from `hgab`); per-line criterion
  `case_III_full_family_of_line` (the `M₁` criterion runs at `e_a`, `rn` extracted freshly there).
  Detail: doc-comments + design §1.40.
- [x] **R1 — homogeneous core + consumer-restate** (2026-06-09; RigidityMatrix/Extensor/CaseI.lean;
  graph-free, axiom-clean). `exists_homogeneousIncidence_of_normals` (four LI `pbar` with eq.-(6.45)
  incidence relative to a given real LI triple `n`; no genericity) + the bare-LI restate of both
  consumers and the producer (`omitTwoExtensor_linearIndependent_of_li`; affine form now a corollary).
  R1-affine DISSOLVED (§1.42 (A)). Detail: doc-comments + design §1.42.
- [x] **R3 — splitOff-simplicity COMPLETE for `|V|≥4`** (Operations/Deficiency.lean; graph-side,
  axiom-clean; §1.42 (A) + §1.43). Four leaves: `splitOff_simple`, `splitOff_simple_of_noRigid`,
  `isKDof_zero_of_triangle`, `triangle_isProperRigidSubgraph` + `splitOff_simple_of_noRigid_of_card`.
  **ON the `|V|≥4` live route** (§1.47: supplies the split-simplicity that unlocks the GP `.1` conjunct
  → `hgab`). Does **not** cover `|V|=3` (T1–T4 instead). Detail: doc-comments + design §1.42/§1.43.
- [ ] **Leaf 3 — discharge the producer's `hcand`** (`case_III_hsplit_producer`, CaseI.lean; **§38 trap**
  at the C2 feed). Sub-steps:
  - [x] **Leaf 3 C2-feed assembly** (`case_III_realization_of_line`, CaseI.lean; 2026-06-09, graph-free,
    axiom-clean). Closes `case_III_full_family_of_line` → C1; the `+1` row routes through C1's
    `span`-membership `hsub` (not the panelRow device feed, §1.35); count parameterized over the
    existential `sn`. Detail: doc-comment + *Decisions made*.
  - [x] **Leaf 3 line-data leaf** (`exists_line_data_of_homogeneousIncidence` +
    `omitTwoExtensor_eq_extensor_kept`, RigidityMatrix.lean; 2026-06-09, graph-free, axiom-clean). Per
    witness join hands the geometric line data `(n_u, n', pi, pj)` at the bare-`pbar` layer — the exact
    input of the Leaf-2b seed-from-line core. Detail: doc-comments + *Decisions made*.
  - [x] **Leaf 3 GAP-2 bare→generic upgrade** (`hasGenericFullRankRealization_of_rigidOn_ofNormals`,
    CaseI.lean; 2026-06-09, axiom-clean). Concrete rigid+linking-transversal `ofNormals G ends q₀`
    (`hends`/`hne`/`hnev`/`hrig`) → all 5 generic-motive conjuncts at an alg-indep seed; the
    `case_I_realization` rank-polynomial block over a single graph; `L`-independent. Also T4's keystone
    (§1.48(1)). Detail: doc-comment + *Decisions made* + design §1.45.
  - [ ] **Leaf 3 concrete seed (§38 trap) — blocked on GAP 4's interface decision (§1.48).** Restate the
    producer to `theorem_55_generic`'s `hsplitGP` shape (gains `G.Simple` + the conditioned IH; concludes
    `HasGenericFullRankRealization 2 G` via the GAP-2 upgrade leaf composed onto the bare candidate). For
    `|V|≥4`: discharge `(G.splitOff …).Simple` via R3 (`splitOff_simple_of_noRigid_of_card`) ⟹ the GP `.1`
    conjunct yields a generic split realization ⟹ pull `q` + `hgab` from **it** (via
    `hasGenericRealization_transport_ends`, mirroring `case_I_realization`); the N3a triple-LI from the
    `.1` alg-indep conjunct (new bridge leaf, §1.48(2)); build `hcand q hq`
    (`exists_line_data_of_homogeneousIncidence q` → `(n_u,n',pi,pj)`; dispatch on the witness panel —
    `M₁`/`M₂` via `case_III_old_new_blocks_of_line` + seed-from-line core + `hq` → `r̂(C(e_a))≠0` →
    `case_III_realization_of_line`; **`M₃` (`Π(c)`-witness) via the GAP-4 leaves G4a–G4e, OPEN**). The
    concrete `ofNormals` is the §38-trap surface. The remaining sub-obligations:
    - **GAP 1 — the `|V|=3` triangle base case: scoped to T1–T4 (§1.48(1)); `|V|≥4` `.1`-wiring confirmed
      (§1.47/§1.48).** `|V|=3`: splitOff is the non-simple double-edge `K₂` → `.1` unavailable → realize
      the triangle directly (T1 third-edge + vertex-pin; T2 `theorem_55_triangle`; T3 basis seed; T4
      assembly through the GAP-2 upgrade). T1/T2/T3 buildable now, no GAP-4 dependency.
    - **GAP 4 — the `M₃` third-panel complex: OPEN (§1.48(2), G4a–G4e).** Blocks the producer signature:
      the branch interface (fixed `(v,a,b)` + split-only IH) cannot express KT's adjacent-degree-2-pair
      choice + same-seed second split. Decision needed: G4b (α) chain-data branch vs (β) full-IH branch.
    - **GAP 2 (B-derive, §1.45) — bare→generic upgrade LANDED (the new leaf below).** The `hsplitGP` shape
      concludes `HasGenericFullRankRealization` (5 conjuncts). The candidate seed is `ℚ`-alg-dependent so
      cannot itself be generic — but the motive's framework is **existentially quantified**.
      `case_III_realization_of_line` produces the **bare** `HasFullRankRealization`; the new upgrade leaf
      `hasGenericFullRankRealization_of_rigidOn_ofNormals` re-realizes it generically (see the `[x]` entry
      above). The producer composes it onto the bare candidate, supplying its `hne` from the candidate
      completion. NO motive re-shaping.
    - **GAP 3 (A) — `hnewtrans` genericity-in-`t`: bounded.** `LinearIndependent ![n_a + t•n', n_b]`: the
      bad-`t` set is a single value (`n_a∉span{n_b}` from `hgab`, so the affine line `t↦n_a+t•n'` meets
      `span{n_b}` in ≤1 `t`), good `t≠0` exists. `Fin(k+2)→ℝ` linear algebra, off the §38 trap; also
      discharges GAP 2's pairwise-GP half.
- [ ] **Leaf 4 — `theorem_55_generic` `d=3`-instance node** (B.2 + R2 ripple §1.41; graph-free).
  Instantiate **`theorem_55_generic (n:=2) (k:=2)`** (not bare `theorem_55` — R2 verdict (B)) on the
  six green/green-modulo branch args (`hbase`/`hbaseGP`/`hsplit`/**`hsplitGP`** = the restated Case-III
  producer/`hcontract`/`hcontractGP` = `case_I_realization`); project the bare `HasFullRankRealization
  2 G` the capstone needs off the conclusion's **`.2` conjunct`** (the existing skeleton :1191–1206
  already threads the `⟨GP-if-simple, bare⟩` pair). Mint the small green blueprint node (**not** a
  standalone `theorem_55_dim3` — avoids duplicating the statement; general `thm:theorem-55` stays
  red-pending-Phase-23).
- [ ] **Leaf 5 — `lem:case-II-realization`/`lem:case-III` flips + Thm 5.5→5.6 push** feeding
  `rigidityMatrix_prop11`'s `hgen`. Unblocks Cor 5.7 at `d=3`.

### Landed leaves (one-line verdicts; full detail in the Lean source + git + design §1.35–§1.39)

- [x] **C1/C2/C3 — the fixed-framework device feed + single-candidate brick + L0 spine re-wire**
  (`hasFullRankRealization_of_independent_rigidityRow` / `…_of_candidateSelector` /
  `case_III_hsplit_producer`, CaseI.lean). The corrected §1.35 route: candidate `+1` row is a
  combination of `e_b`-panelRows (in `span rigidityRows`, not a single `panelRow`), fed at the *fixed*
  `ofNormals` placement via `exists_good_realization_const` — no genericity device. **Survive** the
  §1.39 restate (consume `r̂(Cᵢ)≠0`, which the producer still produces). (2026-06-07)
- [x] **The three selector recasts** (`linearIndependent_sum_{p2,p3,augment}_candidateRow_selector`,
  RigidityMatrix.lean) — package the producers into `hselᵢ : r(C(e))≠0 → LinearIndependent famᵢ`.
  Graph-free. **Survive.** (2026-06-07)
- [x] **The `r̂` candidate-vector data** (`exists_redundant_panelRow_ab_lam`, CaseI.lean; mirror
  `exists_smul_combination_eq_sub_of_mem_span_image_compl`). `r̂ = ∑_j λ_j r_j = wGv ≠ 0` (KT eq.
  (6.25), `λ_{i^*}=1`). **Survives.** (2026-06-08)
- [x] **The `+1` `r̂`-row membership** (`hingeRow_mem_rigidityRows`, Pinning.lean). `r ∈ hingeRowBlock e`
  + `IsLink e u v` ⟹ `hingeRow u v r ∈ rigidityRows`. **Survives.** (2026-06-07)
- [x] **Row-block infra L0–L5** (CaseI/Pinning.lean) — eq.-(6.12) `so`/`sn` blocks
  (`case_III_old_new_blocks`), L2 span bridge (`span_panelRow_comp_single_of_edge`), L4 membership
  (`panelRow_mem_rigidityRows_of_link`), columnOp bridge, row-swap core. **Survive** as the infra
  Leaf 2/3 consume; the swap core + `annihRow`-shaped L3/L5-pack are off the live route (reusable).
  (2026-06-07)
- [x] **OBSOLETE on the `d=3` live route (built to discharge the now-removed `hann`; reusable, likely
  re-enter at Phase-23 join↔meet duality):** `exists_hduality_witness_of_panel_incidence` (`2bd5fa2`),
  `exists_independent_perp_pair` (`07c537c`), `omitTwoExtensor_homogenize_eq_extensor_kept` (`b031eb3`),
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` (Meet.lean, `b8477db`). All graph-free,
  axiom-clean, still in tree. The C5a/C5b six-join `hduality` dispatch (`d851264`) was *removed* from
  `case_III_claim612`'s body by the Leaf-1 restate (the existential proof bypasses it). (2026-06-08/09) §1.39.
- [x] **`case_III_eq629_conditional` DELETED (Leaf 1, 2026-06-09).** The three-fixed-disjunction→selector
  glue had no code callers; its blueprint node `lem:case-III-eq629-conditional` folded into
  `lem:case-III-claim612`. (`hasFullRankRealization_of_independent_panelRow_index` — the abstract device
  feed — stays green.) (2026-06-07/09)

## Blockers / open questions

- **Architecture + CRUX PINNED — existential conclusion, no `hann`; CRUX verdict (B)** (canonical home
  `notes/Phase22-realization-design.md` §1.39–§1.40). Claim 6.12 is a genuine six-join existential (the
  three-fixed disjunction is undischargeable, dim 3 < 6; KT's lines are free). It is directly provable
  (premise-free) and consumable (candidate supports are panel-meets = join form). §1.40's "constructible
  for an arbitrary witness" verdict held at the *line-data* level only — per-witness **placeability** is
  GAP 4 (§1.48(2)): `Π(c)`-witnesses need the `M₃` second-split candidate, not the `v`-hinge placement.
- **The Leaf-3 producer gaps** (§1.44 surfaced three; §1.45 made GAP 2 bounded; §1.47 retracted §1.46's
  GAP-1 dissolution; **§1.48 scoped GAP 1's `|V|=3` half to T1–T4 and surfaced GAP 4** — see *Current
  state* ⚠️ block). The current status:
  - **GAP 1 — `|V|=3` scoped (T1–T4, §1.48(1)); `|V|≥4` `.1`-wiring confirmed (§1.47/§1.48).** The
    candidate placement needs `hgab : LinearIndependent ![q(a,·),q(b,·)]`, sourced only from the GP `.1`
    conjunct's `IsGeneralPosition` (R2 §1.41); at `|V|≥4`, `.1` is available (splitOff simple via R3). At
    `|V|=3` the splitOff is the non-simple double-edge `K₂` → the triangle is realized **directly**
    (KT 6.7(i)/5.4): T1 third-edge/vertex-pin (edge-count via `rank_add_deficiency_eq`), T2
    `theorem_55_triangle` (3-body sibling of `theorem_55_base`), T3 cyclically-consistent basis seed (the
    free-pair `exists_independent_panelSupportExtensor` does NOT apply), T4 assembly through the GAP-2
    upgrade. Signatures: design §1.48(1).
  - **GAP 4 — the `M₃` third-panel dispatch complex: OPEN, blocks the producer signature (§1.48(2)).**
    `Π(c)`-witness joins are unplaceable at `v`'s hinges (two panels can't cover the six joins; KT p. 686
    says so explicitly at `d ≥ 3`); KT's `M₃` = the second split `G_a^{vc}` at an adjacent degree-2 pair
    (Lemma 4.6 chain, p. 664), same-seed via the `ρ = (a v)` relabel, same `r̂` by eqs. (6.43)–(6.44).
    Missing leaves G4a (chain dichotomy), G4b (branch-interface change, (α) chain-data vs (β) full-IH —
    **the one structural decision; next design pass**), G4c (`ρ`-relabel transport), G4d ((6.44)
    candidate-row bookkeeping), G4e (dispatch trichotomy).
  - **GAP 2 (B-derive, §1.45 — supersedes §1.44's (C)) — the bare→generic upgrade dissolves it.** The
    `hsplitGP` shape concludes `HasGenericFullRankRealization`, and the eq.-(6.12) candidate seed
    (`v↦n_a+t•n'`) is `ℚ`-alg-dependent so cannot itself carry the `AlgebraicIndependent ℚ` conjunct — but
    the motive's realizing framework is **existentially quantified** (PanelHinge.lean:1033). The producer
    builds the candidate to **bare** `HasFullRankRealization`, then the single-graph upgrade leaf
    `hasGenericFullRankRealization_of_rigidOn_ofNormals` (LANDED; green machinery:
    `exists_rankPolynomial_of_rigidOn_linking` → rational `Q`, depends on `G`/`ends` only → non-root at the
    `exists_injective_algebraicIndependent_real` seed via the alg-indep eval bridge → generic alg-indep
    rigid witness) concludes the generic motive. This is KT's "convert to nonparallel by Lemma 5.2 without
    decreasing rank" (KT p. 678). L-independent (graph property; `L` discarded once full rank witnessed).
    **~1 commit, reuses `case_I_realization`'s rank-polynomial block.** No motive re-shaping.
  - **GAP 3 (A) — `hnewtrans` genericity-in-`t`: bounded.** The bad-`t` set is a single value, good `t≠0`
    exists; `Fin(k+2)→ℝ` linear algebra, folded into the producer.
- **The §1.41/§1.42 (R1/R2/R3) residuals (distinct from the §1.44 GAPs) — still valid as far as they
  went.** R1-affine (A) DISSOLVED + LANDED; R2 (B) the producer consumes the GP `_hsplit` (correct as an
  *input* fact; the GP *output* is GAP 2, now bounded via the §1.45 upgrade); R3 (A) the triangle
  simplicity mirror is COMPLETE **for `|V|≥4`** (criterion `splitOff_simple`, discharge
  `splitOff_simple_of_noRigid`, `isKDof_zero_of_triangle`,
  `triangle_isProperRigidSubgraph`/`splitOff_simple_of_noRigid_of_card`). Per §1.47, R3 is **ON the `|V|≥4`
  live route** (it supplies the split-simplicity that unlocks the GP `.1` conjunct → `hgab`), not off it as
  §1.46 said; and `(G.splitOff …).Simple` being *false* at `|V|=3` (the double-edge `K₂`) is exactly why
  `|V|=3` is a genuine hole (GAP 1 above), not a dissolution.
- **Blueprint: `lem:case-III-claim612` RE-GREENED, `lem:case-III-eq629-conditional` DELETED
  (Leaf 1, 2026-06-09).** The Lean decl is now the premise-free existential, so the node is honestly
  green (statement + proof prose rewritten to the existential contrapositive; `\uses` trimmed to the
  span + vanish leaves the formal proof actually invokes; the duality/eq644 leaves are conceptual
  `\cref`s only, off the live `\uses`). The eq629-conditional node folded into claim612 (all 10
  references rerouted to `lem:case-III-claim612` or reworded as the conceptual "eq.(6.29) conditional");
  `verify.sh` + supersession gate clean. (Downstream `lem:case-III-candidate-row` stays abstract-green.)
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites Leaf 2/3 (they
  instantiate the concrete carrier). `case_III_claim612` (Leaf 1) is graph-free — no trap. Keep
  reasoning over abstract `F`, instantiate only at the seed.

## Hand-off / next phase

**Landed and off the to-do list** (full per-leaf detail in the *Lemma checklist*): Leaf 1 (existential
`case_III_claim612`), Leaf 2a/2b (join↔meet bridge + line-indexed placement + `case_III_full_family_of_line`),
R1 (homogeneous core + bare-LI consumer-restate), R3 **for `|V|≥4`** (criterion `splitOff_simple`,
discharge `splitOff_simple_of_noRigid`, triangle-0-dof `isKDof_zero_of_triangle`, `htri` discharge
`triangle_isProperRigidSubgraph` + the hypothesis-free `splitOff_simple_of_noRigid_of_card`), and the
graph-free Leaf-3 pieces (C2-feed assembly `case_III_realization_of_line`, line-data leaf
`exists_line_data_of_homogeneousIncidence`, seed-from-line core, block placement, per-line criterion),
and the **GAP-2 bare→generic upgrade leaf** `hasGenericFullRankRealization_of_rigidOn_ofNormals`.

**GAP history (one line each; full traces in design §1.44–§1.48):** §1.44 surfaced GAPs 1–3; §1.45 landed
the GAP-2 bare→generic upgrade; §1.46's GAP-1 "dissolution" was retracted by §1.47 (it orphaned `hgab`;
its `|V|=3`-splitOff-is-double-edge-`K₂` finding stands); §1.48 (the commissioned recon) scoped the
`|V|=3` triangle base to T1–T4, confirmed the `|V|≥4` `.1`-wiring, and surfaced **GAP 4** (the `M₃`
third-panel dispatch complex, G4a–G4e).

**Smallest next forward commit — the GAP-4 interface design pass (G4b), a docs commit:** decide (α)
re-point the reduction's degree-2 selection at the Lemma-4.6 chain and hand chain data through the
`hsplit`/`hsplitGP` branch, vs (β) hand the branch the full conditioned IH (mirroring `hcontract`) and let
the producer choose its own adjacent pair — §1.48(2) carries the trade-offs (either way G4a + G4c are
needed; the `ρ`-relabel is forced by the same-seed `r̂` bookkeeping, eq. (6.44)). Scope G4a/G4c/G4d/G4e to
buildable leaves in the same pass. **Independently buildable now (no GAP-4 dependency): the `|V|=3`
triangle leaves T1, T2, T3** (§1.48(1) signatures) — safest parallel Lean work; T4 composes them with the
landed GAP-2 upgrade. THEN the §38-trap concrete-seed producer (the confirmed `.1`-chain: R3 → `.1` →
`hgab`/triple-LI-bridge; GAP-3 good-`t`; compose `hasGenericFullRankRealization_of_rigidOn_ofNormals` onto
the bare candidate) + Leaf 4 (`theorem_55_generic (n:=2)(k:=2)` instance, `.2` projection per the R2
ripple §1.41) + Leaf 5 (case-II/III flips + Thm 5.5→5.6 push) unblocking Cor 5.7.

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d` (KT
Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1; generalize the candidate
chain on the graph-free assembly; build the `⋀^{d−1}` duality via the top-power route per §1.33 (D), the
obsolete-at-`d=3` join↔meet leaves re-entering here; reuse the alg-independence machinery for the points).
Open Phase 23 with its own recon (eqs. 6.46–6.67 vs the `d=3` Lean) and add the general-`d`
alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **§1.48 commissioned recon — `|V|=3` scoped to T1–T4; `|V|≥4` `.1`-wiring confirmed; GAP 4 surfaced
  (2026-06-09; canonical home design §1.48).** The triangle base case is new-but-bounded (the green cycle
  bricks are the wrong shape: absolute/`Fin m`/free-pair); the `hgab`-from-`.1` chain closes (plus a new
  triple-LI-from-alg-indep bridge); but the six-join *dispatch* needs KT's `M₃` second-split candidate
  (adjacent degree-2 pair, Lemma 4.6; same-seed `ρ`-relabel; eq. (6.44)) — absent from the leaf inventory
  and inexpressible in the current branch interface (G4a–G4e). Lesson (same family as §1.44/§1.47): a
  recon must check per-witness data *placeability* (which construction consumes each witness), not just
  data *coverage* — §1.40-(4) verified the line data exists for all six joins while §1.40-(6)'s leaf cut
  silently collapsed the M₁/M₂/M₃ trichotomy §1.40-(2) itself had named.
- **GAP 1 — `|V|≥4` buildable (GP `.1` + R3), `|V|=3` a genuine hole (§1.46 recon + §1.47 correction,
  2026-06-09).** §1.44 flagged GAP 1 as a hole (`4 ≤ |V|` guard unmet at the reachable `|V|=3` triangle).
  §1.46 first claimed it *dissolved* (route the producer through bare `hIH.2`, GP `.1` unused); §1.47
  (coordinator cross-check) RETRACTED that — the candidate placement requires `hgab`, whose only source is the
  discarded `.1` conjunct, so the bare-`.2` re-route orphaned it. Final: at `|V|≥4` the producer uses `.1`
  (splitOff simple via R3) for `hgab` + the GAP-2 upgrade for the generic-`G` conclusion; at `|V|=3` the
  splitOff is the non-simple double-edge `K₂` (`.1` unavailable by any route) — a genuine hole needing a direct
  triangle base case (KT 6.7(i)/5.4). §1.46's "`|V|=3` simplicity branch is false" finding stands and is *why*
  the hole has no cheap fix. Lessons → DESIGN.md / coordinate-phase command: *recon traces the route, not the
  statements*; *a re-route must re-verify every other carried obligation*.
- **GAP-2 bare→generic upgrade LANDED — single-graph reuse of the `case_I_realization` rank-polynomial
  block (2026-06-09; CaseI.lean, `hasGenericFullRankRealization_of_rigidOn_ofNormals`).** Takes the concrete
  rigid+linking-transversal `ofNormals G ends q₀` and concludes the generic motive by re-realizing at an
  alg-indep seed `q₁`: rational rank `Q` of `G`/`ends` only (`exists_rankPolynomial_of_rigidOn_linking`) +
  GP factor `Qgp` → simultaneous non-root at `q₁` via the alg-indep eval bridge → all 5 conjuncts. The body
  is the `case_I_realization` block (CaseI.lean:1843–1936) stripped of the two-block (`H`/`c`) splice — one
  graph, one rank polynomial. Design choices: (a) **take the concrete `ofNormals`+`hne` (linking
  transversality) as input**, not a packaged `HasFullRankRealization` — the `_linking` rank polynomial needs
  `hne` at the seed, which a bare existential cannot supply but the producer's candidate completion can; (b)
  build the `rigidityRows` membership via an **inline-witness `hrow_mem`** (TACTICS-QUIRKS §38). Verdict
  (B-derive) settled in design §1.45: the motive's framework is existentially quantified, so the degenerate
  `ℚ`-alg-dependent seed need not itself be generic — KT's Lemma 5.2 "convert to nonparallel without
  decreasing rank" (KT p. 678; generic=alg-indep maximizes rank, footnote 4). L-independent.
- **Leaf-3 producer sub-obligations recon — GAP 1/2/3 surfaced (2026-06-09; §1.44, GAPs now tracked in
  *Blockers*).** Adjudicated the three sub-obligations against the *actual Lean route*, not the green
  lemmas' statements (GAP 1 corrected to a genuine `|V|=3` hole §1.47; GAP 2 landed §1.45; GAP 3 in
  *Blockers*). The recon-traces-the-route lesson (§1.44/§1.47) is now promoted to **DESIGN.md** *Constructibility
  recon …* and the **coordinate-phase command** (step 3): a recon must trace the producer's *wiring*, not the
  green lemmas' statements; and a recon that *re-routes* to dissolve a gap (§1.46: bare `.2` instead of GP
  `.1`) must re-verify every other carried obligation still closes — §1.46's re-route orphaned `hgab`, caught
  by the coordinator's §1.47 cross-check.
- **Leaf 3 line-data leaf — strip `hann` from the obsolete six-join witness; stay on the
  homogeneous-vector layer (2026-06-09; RigidityMatrix.lean, `exists_line_data_of_homogeneousIncidence`
  + `omitTwoExtensor_eq_extensor_kept`).** The producer's "extract the witness line `L`" step. The
  obsolete `exists_hduality_witness_of_panel_incidence` (§1.39) is `hann`-premised and concludes the
  per-join meet annihilation; the producer needs the *opposite* — just the geometric line data, no
  annihilation. So the new lemma is that lemma with `hann` + the annihilation conjunct **deleted** (same
  two builders verbatim: two-panel joins through `p̄ 0` → `{n u, n w}`; one-panel joins → `n u` +
  `exists_independent_perp_pair`), stated against bare `pbar` (not `homogenize ∘ p`) per §1.42 R1-affine,
  so it composes with the green homogeneous core directly. `omitTwoExtensor_eq_extensor_kept` is the
  verbatim bare-`pbar` generalization of `omitTwoExtensor_homogenize_eq_extensor_kept`. Graph-free,
  axiom-clean, no §38 trap. Pinned to `lem:case-III-claim612-line-in-panel-union`. Refactor candidate
  (not done, not friction): the affine `…homogenize…` form is now a one-line corollary of the bare form.
- **Leaf 3 C2-feed assembly — route the candidate `+1` row through C1's `span`-membership, not the
  panelRow device feed; parameterize the count over the existential `sn` (2026-06-09; CaseI.lean,
  `case_III_realization_of_line`).** The graph-free brick closing `case_III_full_family_of_line` → C1.
  Two design points: (a) the candidate `+1` row `hingeRow v a r` has `r(C(e_a)) ≠ 0` so it is *not* a
  single `panelRow` (every panelRow annihilates its edge's extensor); it lands in `span rigidityRows` via
  `hingeRow_mem_rigidityRows` (carried as `hcand_mem`), feeding C1's `hsub` rather than the
  panelRow-indexed device feed — the corrected §1.35 route. So the assembly calls C1
  (`hasFullRankRealization_of_independent_rigidityRow`) directly, not the conditional C2
  `hasFullRankRealization_of_candidateSelector`. (b) `case_III_full_family_of_line` binds the NEW-block
  index set `sn` existentially (it is extracted inside the criterion run), so the count obligation is
  phrased `∀ sn, |sn| = D−1 → D(|V|−1) ≤ |(sn ⊕ Unit) ⊕ ιo|` — the consumer (Leaf 3) discharges it from
  the L1/L5-pack arithmetic. `panelRow_mem_rigidityRows_of_link` accepts `G.IsLink e_a v a` defeq for
  `F.graph.IsLink` (`ofNormals_graph`/`toBodyHinge_graph` both `rfl`), so the `sn`-row membership needs no
  `change`. Axiom-clean, no friction, no §38 trap (abstract `F`).
- **R3 splitOff-simplicity COMPLETE (settled; one-line verdicts — full prose in git + Lean
  doc-comments + design §1.42/§1.43).** Four axiom-clean leaves, all in Operations.lean / Deficiency.lean,
  no blueprint node (sibling of the unpinned `rigidContract_simple`): (i) `splitOff_simple` — the bounded
  `hloop`/`hpar` criterion; (ii) `splitOff_simple_of_noRigid` — the combinatorial discharge from
  `[G.Simple]` + the `va`/`vb` edges + `hnoRigid`, the *mixed* `splitOff_isLink` case routed through the
  triangle brick `htri`; (iii) `isKDof_zero_of_triangle` — a triangle is `0`-dof via the `def ≤ 0`
  *partition* route (`ciSup_le` + `deficiency_nonneg`, per-`f` `D(|P|−1) ≤ (D−1)·d` over the five label
  patterns; the §1.43 recon over-engineered a rank computation); (iv) `triangle_isProperRigidSubgraph` +
  the hypothesis-free `splitOff_simple_of_noRigid_of_card` — assembles `IsProperRigidSubgraph
  (G.induce {v,a,b}) G n` from (iii) + `induce_le` + a `4 ≤ V(G).ncard` guard, dropping `htri` for the
  GP `hsplitGP` shape Leaf 3 consumes.
- **R1 LANDED (homogeneous core + consumer-restate; settled, one-line — full prose in git + Lean
  doc-comments).** `exists_homogeneousIncidence_of_normals` (RigidityMatrix.lean): from nonparallel
  `n : Fin 3 → ℝ⁴`, four LI `pbar` with eq.-(6.45) incidence rel. `n`, genericity-free (pairing
  surjectivity + triangular LI). R1-consumer-restate (Extensor/RigidityMatrix/CaseI.lean): the affine-free
  Lemma 2.1 `omitTwoExtensor_linearIndependent_of_li` is `omitTwoExtensor_linearIndependent`'s body minus
  the `homogenize` bridge (affine form now its corollary); both consumers + the producer take bare
  `pbar` + `LinearIndependent ℝ pbar`. R1-affine DISSOLVED (no de-homogenization, §1.42). Pure-refactor.
- **L2b-place per-line criterion — the `M₁` criterion runs at `e_a`, so its `rn` is the `e_a`-block,
  not the `_of_line` `e_b`-NEW block (2026-06-09; CaseI.lean, `case_III_full_family_of_line`).** The
  abstract-`F` row-space-criterion runner: from `hane`/`hold`/`holdindep` + witness `r̂(C(e_a)) ≠ 0`,
  builds the `M₁` completion and runs `linearIndependent_sum_augment_candidateRow_selector` at `e_a` →
  the full `D(|V|−1)`-family. The selector's operated `(rn ∘ Φ) ∘ single v` forms (`Φ = columnOp hva`)
  reduce to the bare L1/L2 `panelRow ∘ single v` forms by `comp_columnOp_comp_single`. Finding: the
  criterion edge is the `va`-line `e_a`, so `rn` is extracted freshly at `e_a` (both `e_a`/`e_b` link
  `v`); the `_of_line` `e_b`-NEW block is the lower-bound brick, off the criterion's `rn`. Graph-free,
  no §38 trap. Leaf 3 supplies `hane`/`hold`/`holdindep`/`hr` at the concrete `ofNormals` seed.
- **L2b-place block placement — `case_III_old_new_blocks_of_line` shears `v` along an arbitrary `n'`
  (2026-06-09; CaseI.lean).** Line-indexed generalization of `case_III_old_new_blocks`: replaces the
  fixed-`n_b` shear with an arbitrary witness-panel second normal `n'`, so the `va`-line is the witness
  `L = n_a ∧ n'`. The OLD block + vanishing + NEW-block `v`-column pin are *verbatim* (they never read
  `v`'s normal), so the diff is only the two support computations (`hane` via
  `panelSupportExtensor_add_smul_left`; `hnewne` via `panelSupportExtensor_ne_zero_iff` from the new
  hypothesis) and the seed. Key design point: the fixed-`n_b` case derived `vb`-transversality *free*
  from `hgab` via `panelSupportExtensor_add_smul_right`'s row reproduction, which only holds at
  `n' = n_b`; for an arbitrary line it becomes the explicit `hnewtrans : ![n_a + t•n', n_b]` indep — a
  genericity-in-`t` obligation the producer (Leaf 3) must supply. Structural duplication of ~90 lines
  with `case_III_old_new_blocks` is deliberate (the two differ in those computations); a common-core
  extraction is a later-refactor candidate, not build friction.
- **The three GP/CRUX recon verdicts — all settled, canonical home `notes/Phase22-realization-design.md`
  §1.40–§1.42.** One-line each (the reconstructions' arcs are compressed to verdicts; the landed Lean
  carries the rest): **CRUX (B)** (§1.40) — the line-indexed placement is constructible for an arbitrary
  witness join (N3a + perp-pair, producer's own non-degeneracy, NOT the `hann`-trap; the shear `t`
  rescales but does not move the line, so each candidate tests one fixed extensor). **R2 (B)** (§1.41) —
  the producer consumes the GP `_hsplit`'s `IsGeneralPosition` conjunct for `hgab` (= `case_I_realization`
  = `hcontractGP` precedent); Leaf-4 ripple = instantiate `theorem_55_generic`, project `.2`. **R1-affine
  (A) DISSOLVES + R3 (A) clean triangle mirror** (§1.42) — no de-homogenization (consumers are
  homogeneous-vector-native, R1-consumer-restate LANDED); R3 is `rigidContract_simple`'s sibling, no
  2-edge-connectivity, COMPLETE.
- **Leaf 2b seed-from-line core — the candidate's *sheared* `va`-support carries the witness
  (2026-06-09; PanelLayer.lean).** `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`:
  `r̂(extensor ![pi,pj]) ≠ 0 ⟹ r̂(panelSupportExtensor (n_u+t•n') n_u) ≠ 0` (`t ≠ 0`). Key insight:
  the row-space criterion tests `r̂(supportExtensor e_a)`, and at the eq.-(6.12) seed `e_a`'s support
  is the *sheared* `panelSupportExtensor (n_u+t•n') n_u`, **not** the unsheared `panelSupportExtensor
  n_u n'` Leaf 2a's transfer is stated against. The bridge is one `rw` of `panelSupportExtensor_add_
  smul_left` (= `(-t)•(unsheared)`, both already green) then `map_smul`/`smul_eq_zero`; the `-t` factor
  cancels under `r` (the `t=0` branch is `absurd … ht`). 8-line composition of green lemmas, no friction.
- **Leaf 2a — the join↔meet bridge reuses the green Phase-22f Meet core in the producer direction
  (2026-06-09; PanelLayer.lean).** The candidate `va`-hinge support `panelSupportExtensor n_u n'` IS
  the panel-meet `C(L) = complementIso ⟨extensor ![n_u,n'],_⟩` (`panelSupportExtensor_eq_complementIso_
  extensor`, one `congrArg`/`Subtype.ext (normalsJoin_coe)`); the transfer
  `panelSupportExtensor_join_eq_zero_of_eq_zero` is then a one-`rw` wrapper over the already-green
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`. Key insight: §1.39(c) lists the join↔meet
  leaves as obsolete, but only the *`hann`-discharge direction* is — the *proportionality* (`complementIso_
  smul_eq_extensor_join`) and its transfer are exactly the bridge §1.39(b) names, just read producer-side
  (`r̂(join) ≠ 0 ⟹ r̂(C(L)) ≠ 0`). Blueprint: defined the dangling `lem:case-III-claim612-line-in-panel-
  union` capstone (referenced by every green Phase-22f sub-leaf's `\cref`, no node) — a real broken-`\cref`
  fix. Graph-free, axiom-clean.
- **The `d=3` Case-III crux architecture: existential conclusion, drop `hann` entirely (2026-06-09
  design pass; canonical home `notes/Phase22-realization-design.md` §1.39, supersedes §1.37/§1.38's B1).**
  `case_III_claim612` → `∃ q : six joins, r̂(join q) ≠ 0`, no premise; ~5-line contrapositive (verified
  via `lean_multi_attempt`). `hann` was only ever the internal `by_contra` negation. The producer
  consumes the existential because candidate supports are panel-meets (= join form): pick the witness
  join, build the candidate at its line `L = pᵢpⱼ`. Five `hann`-discharge leaves (C5c assembly + two
  bricks + N3b `⬝ᵥ`-form + C5a/C5b dispatch) go obsolete on the `d=3` route (reusable, re-enter at
  Phase-23). Effort-accounting flagged to user. Everything else survives. Chosen over §1.38's B1 (which
  kept a false-shaped three-fixed conclusion, the obsolete assembly on-route, and `hann` as undischarged
  producer data — re-introducing the honesty-gate problem). Producer restructure (Leaf 2/3) is identical
  difficulty under both.
- **The `hann`-discharge diagnosis (CONFIRMED, §1.38, carried into §1.39).** Three-fixed antecedent
  `r C₁=0→r C₂=0→r C₃=0` undischargeable (three `2`-extensors span ≤ 3 of `⋀²ℝ⁴`'s 6 dims, verified);
  three-fixed-suffices escape REFUTED (KT lines free, not graph-fixed). Full account: §1.38/§1.39.
- **C5c-leaves landed then went obsolete (2026-06-08/09; full detail Lean source + §1.36/§1.39).** All
  graph-free, axiom-clean; built to carry/discharge the per-join `hduality` witness that the §1.39
  existential restate dissolves. `exists_hduality_witness_of_panel_incidence` (six-join assembly modulo
  `hann`, `fin_cases q` dispatch, §38 call-site variant → TACTICS-QUIRKS §38);
  `exists_independent_perp_pair` (second perp normal via `ker (Matrix.of ![pi,pj]).mulVecLin`
  rank–nullity); `omitTwoExtensor_homogenize_eq_extensor_kept` (kept pair = `{q.1,q.2}ᶜ.orderEmbOfFin`).
  Reusable; off the `d=3` route.
- **C5a/C5b landed then went obsolete (2026-06-09; §1.36/§1.39).** Restated `case_III_claim612`'s
  `hduality` *conclusion* to the per-join witness model + the six-join in-body dispatch; needed
  `public import …Molecular.Meet`. The §1.39 existential restate removes both the `hduality` premise and
  this dispatch. Reusable Meet-side brick `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`
  (`⬝ᵥ`-incidence form of the green N3b core).
- **The corrected L-wire — device feed is the fixed-framework `_const` route (2026-06-07; §1.35).**
  The placed `+1` row `hingeRow v b r̂` (`r̂(C(e_b))≠0`) is a combination of `e_b`-panelRows, in
  `span rigidityRows` but not a single `panelRow`; fed at the fixed `ofNormals` placement via
  `exists_good_realization_const` (constant family, `hg = eval_C`) + `…_finrank_le` — no genericity, no
  panelRow re-shaping. Drove C1–C3 + the L0 `hfamᵢ`-contract restate.
- **`hsplit` producer cracked green-modulo-skeleton-first; §38 trap isolated to the carrier-instantiating
  leaves (2026-06-07).** State the producer carrying residual graph-data obligations as explicit `h…`,
  flip the spine first, discharge each as a leaf. C1 lives in CaseI (not GenericityDevice — import
  direction). C2 generic over the family. C3 spine = `rcases` the conclusion + per-disjunct C2 calls.
- **(B.1) the `d=3` `hsplit`/`theorem_55` path does NOT consume `lem:cycle-realization` (2026-06-07,
  open).** `theorem_55` = `minimal_kdof_reduction` with three branches, base case `V=2` only; short
  cycles dissolve into repeated splits. The `\uses` edge is a KT-narrative (not Lean-load-bearing)
  dependency — kept with a clarifying prose note; the cited step is Crapo–Whiteley, not Claim 6.4/6.9
  (green). Fixed stale `case-i.tex:149–151`. (B.2) add a green instance node — now
  `theorem_55_generic (n:=2) (k:=2)` projecting `.2` (R2 verdict (B), §1.41), not bare `theorem_55`;
  not a standalone `theorem_55_dim3`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *The `ofNormals`/`withGraph` defeq-timeout trap + extract-a-generic-helper mitigation* → TACTICS-QUIRKS §38.
- *The §38 call-site variant: pass a heavy-carrier-typed arg as an explicit literal (via `fin_cases`)* →
  TACTICS-QUIRKS §38 (Phase 22g addendum).
- *The §38 membership-witness variant: inline the `rigidityRows` `⟨e,u,v,…,rfl⟩` witness rather than calling
  `panelRow_mem_rigidityRows` (whnf-times-out reconciling `F.graph` with `G`)* → TACTICS-QUIRKS §38.
- *The `(Matrix.of ![pi,pj]).mulVecLin x i = ![pi,pj] i ⬝ᵥ x` per-coordinate unfold* → FRICTION [resolved].
- *"row-LI ⟹ `mulVecLin` surjective" is not packaged — compose `LinearIndependent.rank_matrix` +
  `eq_top_of_finrank_eq`; the lemma is root `sum_dotProduct`* → FRICTION [resolved].
- *The unit-normalized combination from a span-of-the-others membership*
  (`exists_smul_combination_eq_sub_of_mem_span_image_compl`) → FRICTION [mirrored].
- *The standard-basis `Basis.toDual` self-pairing is the dot product* (`Pi.basisFun_toDual_apply`) → FRICTION [mirrored].
- *`rw [eq]` of a function-valued term over-rewrites its partial applications — narrow with
  `conv_lhs`/`nth_rewrite`* → TACTICS-QUIRKS §41.
