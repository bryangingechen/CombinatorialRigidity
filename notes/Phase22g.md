# Phase 22g — the `d=3` realization assembly (work log)

**Status:** in progress (opened 2026-06-07 on a build-free red-node consistency recon).
The deferred-unlettered "`d=3` assembly" cut, now lettered 22g. KT §6.4.1 (Lemma 6.10) at the
`k=0`/`d=3` scope. Cross-cutting design history lives in `notes/Phase22-realization-design.md`
§1.33–§1.39; this note carries current state, the live leaf sequence, blockers, and hand-off.

## Current state

**The `d=3` Case-III crux architecture is PINNED (`notes/Phase22-realization-design.md` §1.39,
2026-06-09 design pass — supersedes §1.37/§1.38's B1).** `case_III_claim612` is restated to the
**existential conclusion** `∃ q : six joins, r̂(join q) ≠ 0` with **no `hann`/`hduality` premise**:
the honest proof is the ~5-line contrapositive `by_contra → push Not → eq_zero_of_annihilates_span_top
(span_omitTwoExtensor_eq_top hp)`, reusing the current body's span→r=0 machinery (verified to close via
`lean_multi_attempt`). `hann` was never a supplied premise — it is the internal `by_contra` negation.
The existential ranges over the **six joins only** (they span via Lemma 2.1), not the line continuum.

**Effort-accounting flag (honest):** the existential restate makes five recently-landed leaves
**obsolete on the `d=3` live route** — they were the machinery for *carrying and discharging* the
per-join `hduality` witness, which no longer exists:
`exists_hduality_witness_of_panel_incidence` (the C5c assembly), `exists_independent_perp_pair`,
`omitTwoExtensor_homogenize_eq_extensor_kept`, `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`,
and the C5a/C5b six-join dispatch in `case_III_claim612`'s current body. They stay as reusable
graph-free lemmas (likely re-enter at **Phase-23** general-`d` join↔meet duality), but are off the
`d=3` route. The contradiction core, `candidateRow_ne_zero`/`candidateRow_ac_eq_neg`, the `r̂`-vector
data, C1/C2/C3, the row-space criterion, L1/L2/L4, and the `+1`-row membership all **survive verbatim**.

**The genuine remaining math** is producer-internal: the candidate construction must be
**re-parameterized over the witness join's line `L ⊂ Π(u)`** — build the eq.-(6.12) degenerate placement
at an arbitrary `L`, run the row-space criterion at `C(L)`. The geometric identity that makes the
existential consumable: a candidate support `(ofNormals …).supportExtensor e = panelSupportExtensor
(normal u) (normal v)` is a **panel-meet** (PanelHinge.lean:89, `rfl`), the same `complementIso`/`extensor`
form as a join — so the producer builds its candidate so its hinge line IS the witness join's line. **But
that degenerate placement is exactly the source of GAP 2** (the seed cannot carry the GP motive's
`AlgebraicIndependent ℚ` conjunct, §1.44) — see *Blockers*.

**Next concrete step (the §38-trap concrete-seed producer, Leaf 3 — GAP 1 DISSOLVED §1.46, GAP-2 upgrade
leaf LANDED, GAP 3 folds in):** the remaining `d=3` build is the §38-trap concrete-seed producer. Restate
`case_III_hsplit_producer` to `theorem_55_generic`'s `hsplitGP` shape; take the **bare** `_hsplit := hIH.2`
(no split-simplicity — see GAP-1 below), build the eq.-(6.12) degenerate candidate `ofNormals G ends q₀` to
**bare** `HasFullRankRealization` (`case_III_realization_of_line`), then **compose the landed GAP-2 upgrade
`hasGenericFullRankRealization_of_rigidOn_ofNormals`** onto it to conclude `HasGenericFullRankRealization k G`.
The producer supplies the upgrade's `hne` from its candidate completion (`hane`/`hnewtrans` cover the
`va`/`vb` hinges; remaining direct `G`-links are the candidate's panel hinges); GAP 3 (genericity-in-`t`,
`Fin(k+2)→ℝ` linear algebra) folds into the assembly. The GAP-2 keystone is built:
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
+ the hypothesis-free `splitOff_simple_of_noRigid_of_card`, Operations.lean) are axiom-clean. It stays as a
reusable KT Lemma 6.7(ii) graph-side fact (sibling of `rigidContract_simple`) — the `d=3` producer no longer
calls it (GAP 1 dissolved, §1.46: the producer takes the bare `hIH.2`, never the split graph's simplicity).
Full detail per leaf in the *Lemma checklist* + *Hand-off*; the checklist is the canonical done/open ledger.

**GAP 1 DISSOLVED (§1.46, 2026-06-09); TWO bounded sub-obligations remain in the Leaf-3 producer (§1.44
surfaced three; §1.45 reclassified GAP 2 from research-shaped to bounded; §1.46 dissolved GAP 1). The `d=3`
producer IS buildable — no research-shaped node remains in 22g.** The sub-obligations the §38-trapped
producer carries, all bounded:
- **GAP 1 — DISSOLVED (§1.46; was (C)).** The producer **never consumes `(G.splitOff …).Simple`** under the
  §1.45 GAP-2 B-derive route: it takes the **bare** `_hsplit := hIH.2 : HasFullRankRealization k (G.splitOff
  …)` (the *unconditional* `.2` conjunct of `theorem_55_generic`'s `hsplitGP` IH — no split-simplicity), builds
  the bare candidate, then upgrades via `hasGenericFullRankRealization_of_rigidOn_ofNormals`. The IH's *generic*
  `.1` conjunct (the only place split-simplicity would enter) is unused. Bonus finding: §1.44's proposed
  "`|V|=3` simplicity branch" was **false** — at `|V(G)|=3`, `D=3`, a minimal `0`-dof `G` is the triangle
  (`|E(G)| = 3·2/2 = 3`), whose splitOff carries BOTH the surviving `ab`-edge `f` AND the fresh `e₀` on `a-b`
  (a parallel pair), so it is the 2-vertex *double*-edge `K₂`, NOT simple. No `|V|=3` branch to build; R3
  (`splitOff_simple_of_noRigid_of_card`, `|V|≥4`) stays as a reusable graph-side fact (the producer no longer
  calls it). Full trace: §1.46.
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
- **GAP 3 — bounded (A):** `hnewtrans : LinearIndependent ![n_a + t•n', n_b]` — the bad-`t` set
  is at most a single value (the affine line `t↦n_a+t•n'` is not contained in `span{n_b}` since `n_a∉span{n_b}`
  from the pairwise GP `hgab`), so a good `t≠0` exists. Bounded `Fin(k+2)→ℝ` linear algebra, no new geometry.

Full traces: `notes/Phase22-realization-design.md` §1.46 (GAP-1 dissolution) + §1.45 (GAP-2 resolution) +
§1.44 (the three sub-obligations) + §1.39–§1.43.

**Landed (all axiom-clean; off the to-do list):** Leaf 1 (existential `case_III_claim612`), Leaf 2a/2b
(join↔meet bridge + line-indexed candidate placement `case_III_old_new_blocks_of_line` +
`case_III_full_family_of_line`), R1 (homogeneous core `exists_homogeneousIncidence_of_normals` +
consumer-restate to bare LI `pbar`), R3 **for `|V|≥4`** (criterion `splitOff_simple` + discharge
`splitOff_simple_of_noRigid` + triangle-0-dof `isKDof_zero_of_triangle` + `htri` discharge
`triangle_isProperRigidSubgraph`/`splitOff_simple_of_noRigid_of_card`), and the graph-free Leaf-3 pieces
(C2-feed assembly `case_III_realization_of_line`, line-data leaf `exists_line_data_of_homogeneousIncidence`).
The Lemma checklist carries the per-leaf detail.

**Remaining (→ phase close): all bounded, ~3–4 commits** (GAP 1 dissolved, §1.46). GAP-3 good-`t` (folded
into the producer) + the §38-trap concrete-seed producer (~1–2, takes the bare `hIH.2`, composes the landed
GAP-2 upgrade `hasGenericFullRankRealization_of_rigidOn_ofNormals` onto the bare candidate) + Leaf 4
(`theorem_55_generic (n:=2)(k:=2)` instance, project `.2`) + Leaf 5 (case-II/III flips + Thm 5.5→5.6 push).
**No research-shaped node remains in Phase 22g** — Lemma 6.10 / Claim 6.11 (the §4 risk register's largest
KT proof) is already green via Phases 22d/22e/22f. Milestone unchanged: the molecular conjecture at `d=3`,
unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma 6.13) is **Phase 23** (reuse map: §1.33 (C)).

## Lemma checklist — the live leaf sequence (§1.39)

- [x] **Leaf 1 — `case_III_claim612` existential restate** (DONE 2026-06-09; RigidityMatrix.lean;
  graph-free, axiom-clean). Conclusion now `∃ q : {q // q.1 < q.2}, r ⟨omitTwoExtensor (homogenize∘p)
  (ne_of_lt q.2), _⟩ ≠ 0`; no premise. Body = the verified 5-line contrapositive. `case_III_hsplit_producer`
  dropped `Cᵢ`/`hduality`/the three-fixed C2 inputs and carries a single green-modulo hypothesis
  `hcand : ∀ q, r(join q) ≠ 0 → HasFullRankRealization 2 G` (the line-indexed candidate placement,
  Leaf 2/3); body = `obtain ⟨q,hq⟩ := case_III_claim612 hr hp; exact hcand q hq`.
  `case_III_eq629_conditional` deleted (no code callers; blueprint node folded into
  `lem:case-III-claim612`, flipped green). The three selector recasts' doc-comments + the candidate-row
  selector doc rerouted off the deleted glue lemma.
- [x] **Leaf 2a — the join↔meet bridge** (DONE 2026-06-09; PanelLayer.lean; graph-free, axiom-clean).
  The seed-from-line geometric core: `panelSupportExtensor_eq_complementIso_extensor` (the candidate
  `va`-hinge support `panelSupportExtensor n_u n'` IS the Meet-form panel-meet `C(L) = complementIso
  ⟨extensor ![n_u,n'],_⟩`, via `normalsJoin_coe`) + `panelSupportExtensor_join_eq_zero_of_eq_zero` (the
  producer-direction annihilation transfer `r̂(C(L)) = 0 → r̂(pᵢ∨pⱼ) = 0`, contrapositive: the Leaf-1
  existential `r̂(join) ≠ 0` forces `r̂(C(L)) ≠ 0`, the C2 row-space input). Reuses the green Phase-22f
  Meet core (`extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct`); the proportionality
  `complementIso_smul_eq_extensor_join` was already green. Blueprint: defined the previously-dangling
  `lem:case-III-claim612-line-in-panel-union` capstone node (meet.tex, green) — the join↔meet duality
  the green Phase-22f sub-leaves all `\cref` but no node defined; pins the four duality lemmas. The
  duality is the bridge §1.39(b) names; the *transfer* form is producer-direction (the `hann`-discharge
  direction stays obsolete, §1.39(c)).
- [x] **Leaf 2b — the line-indexed candidate placement** (CaseI.lean; graph-free, axiom-clean; DONE
  2026-06-09, four commits).
  - [x] **2b seed-from-line geometric core** (DONE 2026-06-09; PanelLayer.lean, graph-free,
    axiom-clean): `panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero` — the candidate's
    *sheared* `va`-hinge support `panelSupportExtensor (n_u + t•n') n_u = (-t)•C(L)` (`t ≠ 0`) carries
    the existential witness: `r̂(extensor ![pi,pj]) ≠ 0 ⟹ r̂(panelSupportExtensor (n_u+t•n') n_u) ≠ 0`.
    The shear-invariant, candidate-direction reading of Leaf 2a's transfer
    (`panelSupportExtensor_join_eq_zero_of_eq_zero`); the `-t` factor cancels under `r`. This is the
    exact nonzero-row input `linearIndependent_sumElim_candidateRow_iff` tests at `e_a` (whose support
    IS `panelSupportExtensor (n_u+t•n') n_u`). Blueprint: added to `lem:case-III-claim612-line-in-panel-
    union`'s group `\lean{}` pin (corner-case variant), prose extended one clause for the sheared form.
  - [x] **2b producer-core recon (CRUX verdict)** (DONE 2026-06-09; `notes/Phase22-realization-design.md`
    §1.40, build-free). Read `case_II_placement_eq612` / `case_III_hsplit_producer` / C2 /
    row-space-criterion end-to-end; settled the constructibility CRUX as **(B)** (constructible for an
    arbitrary witness, needs non-degeneracy, producer's own N3a + perp-pair supplies it; NOT the
    `hann`-trap). Pinned the load-bearing fact (shear rescales but does not move the candidate line);
    mapped the §38 trap (confined to the `ofNormals` C2-feed carrier); decomposed the core into
    L2b-place / N3a-from-normals (R1) / per-line criterion / C2-feed (R2). Flagged R1/R2 (below).
  - [x] **L2b-place block placement** (DONE 2026-06-09; CaseI.lean,
    `case_III_old_new_blocks_of_line`, axiom-clean). The line-indexed generalization of
    `case_III_old_new_blocks`: shears body `v` along an *arbitrary* second normal `n'` (not the fixed
    IH `n_b`), so the `va`-hinge `e_a` is the witness line `L = n_a ∧ n'` (support `(-t)•C(L)`) and the
    OLD/NEW blocks come out at the line-indexed seed `q₀ = if p.1=v then (n_a + t•n') else q`. The two
    transversality facts now enter as explicit hypotheses: `hL : LinearIndependent ![n_a, n']` (the
    `va`-line genuine) and `hnewtrans : LinearIndependent ![n_a + t•n', n_b]` (the reproduced
    `vb`-transversal — the genericity-in-`t` condition the producer must supply; the fixed-`n_b` case
    got both free from `hgab` via `panelSupportExtensor_add_smul_right`'s row reproduction, which only
    holds at `n' = n_b`). OLD block + vanishing + NEW-block `v`-column pin are the verbatim
    `case_III_old_new_blocks` argument (never reads `v`'s normal). The §38 trap stayed confined to the
    two support computations (`hane`/`hnewne`, the existing `toBodyHinge_supportExtensor` rewrite path).
    Blueprint: added to `lem:case-III-claim612-line-in-panel-union`'s group `\lean{}` pin + one prose
    clause. **Carried open in this leaf:** the `(D−1)` block rows spanning `(span C(L))^⊥` is the L2
    span bridge, fed to the row-space criterion next (not yet wired).
  - [x] **L2b-place per-line criterion** (DONE 2026-06-09; CaseI.lean, `case_III_full_family_of_line`,
    graph-free, axiom-clean). The abstract-`F` row-space-criterion runner: from `hane` (`e_a` support
    ≠ 0), the OLD block (`hold`/`holdindep`), and the witness `r̂(C(e_a)) ≠ 0` (`hr`), builds the `M₁`
    candidate completion — NEW block at `e_a` itself (the `va`-line `L`-block,
    `exists_independent_panelRow_subfamily_of_edge`), pinned-independent + spanning `hingeRowBlock e_a`
    (L2 `span_panelRow_comp_single_of_edge`; the selector's operated `Φ∘single v` forms reduced to the
    bare `single v` ones by `comp_columnOp_comp_single`) — and runs
    `linearIndependent_sum_augment_candidateRow_selector` at `e_a` → the full
    `Sum.elim (Sum.elim rn {hingeRow v a r̂}) ro` `D(|V|−1)`-family. **Key architecture finding:** the
    `M₁` criterion runs at `e_a` (not `e_b`), so `rn` is the `e_a`-block, extracted freshly from `hane`
    (both `e_a`/`e_b` link `v`); the `_of_line` `e_b`-NEW block is the lower-bound brick, off the
    criterion's `rn`. Blueprint: added to `lem:case-III-claim612-line-in-panel-union`'s group `\lean{}`
    pin + one prose clause.
- [x] **R1 homogeneous-vector core LANDED** (`exists_homogeneousIncidence_of_normals`, RigidityMatrix.lean,
  axiom-clean; 2026-06-09): given `LinearIndependent ℝ n` (`n : Fin 3 → ℝ⁴`), produces four LI homogeneous
  vectors `pbar : Fin 4 → ℝ⁴` with the eq.-(6.45) triple-intersection incidence *relative to the real `n`*.
  Surjectivity of the pairing `mulVecLin (of n)` (full row rank) + the triangular LI argument. No
  genericity. **R1-affine DISSOLVES (§1.42, verdict (A)):** the de-homogenization to affine `ℝ³` is NOT
  needed — restate the two consumers (`span_omitTwoExtensor_eq_top`/`case_III_claim612`) to bare LI `pbar`
  (Lemma 2.1's spanning content holds for any LI 4-family; `omitTwoExtensor_linearIndependent_of_li`
  verified to close) and feed the homogeneous core directly. The remaining R1 work is the bounded
  consumer-restate (Leaf 3 below), NOT a genericity residual.
- [x] **R1-consumer-restate** (DONE 2026-06-09; Extensor.lean / RigidityMatrix.lean / CaseI.lean;
  graph-free, axiom-clean): added `omitTwoExtensor_linearIndependent_of_li` (the affine-free Lemma 2.1,
  body = verbatim `omitTwoExtensor_linearIndependent` minus the `homogenize` bridge; the affine form
  is now its one-line corollary); restated `span_omitTwoExtensor_eq_top` + `case_III_claim612` + the
  producer `case_III_hsplit_producer` to bare `pbar : Fin 4 → ℝ⁴` + `LinearIndependent ℝ pbar`,
  dropping the vestigial `AffineIndependent ℝ p`. Blueprint: `lem:case-III-claim612-points-affineIndep-
  real-normals` flipped green, `lem:case-III-claim612-extensor-span` + `lem:case-III-claim612`
  re-shaped to the bare-LI form, the affine-free core added to `lem:extensor-independence`'s group pin.
  The producer's `pbar` feed (`exists_homogeneousIncidence_of_normals`) is now type-aligned with the
  consumers. Build + lint + verify.sh + supersession-gate all clean.
- [x] **R3 splitOff-simplicity COMPLETE for `|V|≥4`** (Operations.lean / Deficiency.lean; graph-side,
  axiom-clean; §1.42 verdict (A)). Four leaves: `splitOff_simple` (criterion), `splitOff_simple_of_noRigid`
  (combinatorial discharge), `isKDof_zero_of_triangle` (triangle `0`-dof, `def ≤ 0` partition route), and
  `triangle_isProperRigidSubgraph` + the hypothesis-free `splitOff_simple_of_noRigid_of_card`. Per-leaf
  detail: *Decisions made* "R3 splitOff-simplicity COMPLETE" + the Lean doc-comments. **Now off the `d=3`
  live route** (GAP 1 dissolved, §1.46 — the producer takes the bare `hIH.2`, never split-simplicity); kept
  as a reusable KT Lemma 6.7(ii) graph-side fact (sibling of the unpinned `rigidContract_simple`).
- [ ] **Leaf 3 — discharge the producer's `hcand`** (`case_III_hsplit_producer`, CaseI.lean; **§38 trap**
  at the C2 feed). Sub-steps:
  - [x] **Leaf 3 C2-feed assembly** (`case_III_realization_of_line`, CaseI.lean; DONE 2026-06-09,
    graph-free, axiom-clean). The abstract-`F` brick closing `case_III_full_family_of_line` → C1: runs the
    per-line criterion at `e_a`, then feeds the full `D(|V|−1)` family
    `Sum.elim (Sum.elim rn {hingeRow v a r}) ro` straight into
    `hasFullRankRealization_of_independent_rigidityRow` (C1), with each summand's `span rigidityRows`
    membership from `panelRow_mem_rigidityRows_of_link` (`sn`-rows at the direct `G`-link `e_a`), the
    `hcand_mem` hypothesis (`+1` row, supplied by `hingeRow_mem_rigidityRows`), and the `hro_mem`
    hypothesis (OLD block). The `+1`-row is *not* a single `panelRow` (it has `r(C(e_a)) ≠ 0`), so it
    routes through C1's `span`-membership `hsub`, **not** the panelRow-indexed device feed (§1.35). The
    count `hcard` is parameterized over the existentially-bound `sn` (`∀ sn, |sn| = D−1 → …`) since the
    block-completion's `sn` only exists inside the criterion. No §38 trap (graph-free over abstract `F`).
  - [x] **Leaf 3 line-data leaf** (`exists_line_data_of_homogeneousIncidence` + the bare-`pbar` kept
    tabulation `omitTwoExtensor_eq_extensor_kept`, RigidityMatrix.lean; DONE 2026-06-09, graph-free,
    axiom-clean). The "extract the witness line `L`" step: producer-direction analogue of the obsolete
    `exists_hduality_witness_of_panel_incidence` with the `hann` premise + meet-annihilation conclusion
    **stripped** — for each of the six joins it hands over only the geometric line data
    `(n_u, n', pi, pj)` (`LinearIndependent ![n_u, n']`, the four `⬝ᵥ`-orthogonalities, the join identity
    `omitTwoExtensor pbar (ne_of_lt q.2) = extensor ![pi, pj]`), at the **homogeneous-vector layer**
    (bare `pbar`, fed by `exists_homogeneousIncidence_of_normals`, §1.42 R1-affine). Reuses the obsolete
    lemma's two builders verbatim (two-panel joins through `p̄ 0` → `{n u, n w}`; one-panel "opposite"
    joins → `n u` + `exists_independent_perp_pair`). `omitTwoExtensor_eq_extensor_kept` is the verbatim
    generalization of `omitTwoExtensor_homogenize_eq_extensor_kept` off the bare family (the affine
    `homogenize` form is now its special case — refactor candidate noted, not friction). Pinned to
    `lem:case-III-claim612-line-in-panel-union`'s group `\lean{}` + one prose clause. This is the exact
    input the Leaf-2b seed-from-line core consumes to turn `hq : r̂(join q) ≠ 0` into
    `r̂(panelSupportExtensor (n_u + t•n') n_u) ≠ 0`. Graph-free, no §38 trap.
  - [x] **Leaf 3 GAP-2 bare→generic upgrade** (`hasGenericFullRankRealization_of_rigidOn_ofNormals`,
    CaseI.lean; DONE 2026-06-09, axiom-clean). Takes the concrete rigid+linking-transversal
    `ofNormals G ends q₀` (`hends`/`hne`/`hnev`/`hrig`) and concludes `HasGenericFullRankRealization k G`:
    `exists_rankPolynomial_of_rigidOn_linking` → rational `Q` of `G`/`ends` ONLY (the seed enters only via
    `eval q₀ Q ≠ 0`; `L` enters nowhere) + `exists_generalPosition_polynomial` → `Qgp` → alg-indep seed `q₁`
    (`exists_injective_algebraicIndependent_real`) is a simultaneous non-root via the alg-indep eval bridge →
    `ofNormals G ends q₁` rigid (device-row closure) + GP (`hQgp_pos`) + links (`ofNormals_recordsLinks_of_hends`)
    + alg-indep (`halg`), all 5 conjuncts. Body = the `case_I_realization` rank-polynomial block
    (CaseI.lean:1843–1936) over a *single* graph (no two-block splice). §38: the `rigidityRows` membership
    is built via the **inline-witness** `hrow_mem` (take `G.IsLink` as an explicit arg, supply the
    `⟨e,u,v,…,rfl⟩` constructor) — the `panelRow_mem_rigidityRows` call timed out at `whnf` reconciling
    `F.graph` with `G` (TACTICS-QUIRKS §38 membership-witness variant). Pinned to
    `lem:case-III-claim612-line-in-panel-union`'s group `\lean{}` + one prose clause.
  - [ ] **Leaf 3 concrete seed (§38 trap) — UNBLOCKED (§1.45 reclassified GAP 2 bounded + GAP-2 leaf done;
    §1.46 dissolved GAP 1).** Restate the producer to `theorem_55_generic`'s `hsplitGP` shape (gains
    `G.Simple` + the conditioned IH; concludes `HasGenericFullRankRealization 2 G` — via the GAP-2 upgrade
    leaf composed onto the bare candidate). Take the **bare** `_hsplit := hIH.2` (no split-simplicity — GAP 1
    dissolved); pull `q` + `hgab` from the GP `_hsplit` (via `hasGenericRealization_transport_ends`,
    mirroring `case_I_realization`), build `hcand q hq` (`exists_line_data_of_homogeneousIncidence q` →
    `(n_u,n',pi,pj)`; the producer's own N3a real triple `n` for `pbar`/`hpbar`;
    `case_III_old_new_blocks_of_line`; seed-from-line core + `hq` → `r̂(C(e_a))≠0`;
    `case_III_realization_of_line`). The concrete `ofNormals` is the §38-trap surface. The remaining
    sub-obligations:
    - **GAP 1 — DISSOLVED (§1.46).** The producer never consumes `(G.splitOff …).Simple`: it takes the
      **bare** `hIH.2 : HasFullRankRealization k (G.splitOff …)` (the unconditional `.2` conjunct of the
      `hsplitGP` IH) and upgrades to generic via `hasGenericFullRankRealization_of_rigidOn_ofNormals` — the
      generic `.1` conjunct (the only split-simplicity consumer) is unused. §1.44's proposed `|V|=3`
      simplicity branch was **false** (at `|V|=3`, `D=3`, `G` is the triangle, whose splitOff carries the
      surviving `ab`-edge AND the fresh `e₀` = a parallel pair, so it is the double-edge `K₂`, not simple).
      No `|V|=3` branch to build; R3 (`|V|≥4`) stays a reusable graph-side fact.
    - **GAP 2 (B-derive, §1.45) — bare→generic upgrade LANDED (the new leaf below).** The `hsplitGP` shape
      concludes `HasGenericFullRankRealization` (5 conjuncts). The candidate seed is `ℚ`-alg-dependent so
      cannot itself be generic — but the motive's framework is **existentially quantified**.
      `case_III_realization_of_line` produces the **bare** `HasFullRankRealization`; the new upgrade leaf
      `hasGenericFullRankRealization_of_rigidOn_ofNormals` re-realizes it generically (see the `[x]` entry
      below). The producer composes it onto the bare candidate, supplying its `hne` from the candidate
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
  (premise-free) and consumable (candidate supports are panel-meets = join form), constructible for an
  arbitrary witness via the producer's own data (N3a + perp-pair, not the `hann`-trap).
- **TWO bounded gaps in the Leaf-3 producer — the `d=3` producer IS buildable, no research-shaped node
  remains** (canonical home §1.44 surfaced three, §1.45 reclassified GAP 2 bounded, §1.46 dissolved GAP 1).
  The remaining sub-obligations, all bounded:
  - **GAP 1 — DISSOLVED (§1.46, supersedes §1.44's (C)).** The producer **never consumes
    `(G.splitOff …).Simple`** under the §1.45 B-derive route: it takes the **bare**
    `hIH.2 : HasFullRankRealization k (G.splitOff …)` (the unconditional `.2` conjunct of
    `theorem_55_generic`'s `hsplitGP` IH), builds the bare candidate, then upgrades via
    `hasGenericFullRankRealization_of_rigidOn_ofNormals`. The IH's generic `.1` conjunct — the only
    split-simplicity consumer — is unused. §1.44's proposed `|V|=3` simplicity branch was **false** anyway:
    at `|V|=3`, `D=3`, `G` is the triangle (`|E(G)|=3`), whose splitOff carries the surviving `ab`-edge AND
    the fresh `e₀` on `a-b` (a parallel pair), so it is the double-edge `K₂`, not simple. No `|V|=3` branch
    to build.
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
  `triangle_isProperRigidSubgraph`/`splitOff_simple_of_noRigid_of_card`). R3 covers only `|V|≥4`, but the
  `|V|=3` gap GAP 1 originally named is **dissolved, not a hole** (§1.46): the producer never consumes split
  simplicity, and `(G.splitOff …).Simple` is in fact *false* at `|V|=3` (the triangle's splitOff is the
  double-edge `K₂`). R3 stays a reusable KT Lemma 6.7(ii) graph-side fact, off the `d=3` live route.
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

**Landed this commit (build-free recon, §1.46): GAP 1 DISSOLVED.** Re-traced the §1.44 GAP-1 "`4 ≤ |V(G)|`
proper-ness guard / `|V|=3` simplicity branch" against the now-green producer + `theorem_55_generic`'s
`hsplitGP` IH shape and found **GAP 1 needs no new lemma**: under the §1.45 GAP-2 B-derive route the producer
takes the **bare** `hIH.2 : HasFullRankRealization k (G.splitOff …)` (the unconditional `.2` conjunct, no
`(G.splitOff …).Simple`), builds the bare candidate, then upgrades via the landed
`hasGenericFullRankRealization_of_rigidOn_ofNormals`. The IH's *generic* `.1` conjunct (the sole
split-simplicity consumer) is unused. Bonus: §1.44's proposed `|V|=3` simplicity branch was **false** — at
`|V|=3`, `D=3`, a minimal `0`-dof `G` is the triangle (`|E(G)| = D(|V|−1)/(D−1) = 3`), whose splitOff carries
the surviving `ab`-edge AND the fresh `e₀` on `a-b` (a parallel pair), so it is the double-edge `K₂`, not
simple. No `|V|=3` branch to build; R3 (`splitOff_simple_of_noRigid_of_card`, `|V|≥4`) stays as a reusable KT
Lemma 6.7(ii) graph-side fact off the `d=3` live route. Build-free docs commit; full trace in design §1.46.

**Smallest next forward commit (the §38-trap concrete-seed producer, Leaf 3):** restate the producer to
`theorem_55_generic`'s `hsplitGP` shape, take the **bare** `_hsplit := hIH.2` (no split-simplicity — GAP 1
dissolved), build the concrete degenerate `ofNormals` candidate to **bare** `HasFullRankRealization`
(`case_III_realization_of_line`), then **compose the landed `hasGenericFullRankRealization_of_rigidOn_ofNormals`
onto it** — supplying the upgrade's `hne` (linking transversality) from the candidate completion
(`hane`/`hnewtrans` cover the `va`/`vb` hinges). Folds in **GAP 3 genericity-in-`t`** (the good-`t`
existence lemma, `Fin(k+2)→ℝ` linear algebra, off the §38 trap). Then **Leaf 4/5** (the
`theorem_55_generic (n:=2) (k:=2)` instance node + `.2` projection per the R2 ripple §1.41, the case-II/III
flips, the Thm 5.5→5.6 push) unblocking Cor 5.7. **Estimate to phase close: ~3–4 commits, all bounded.**
Full traces: `notes/Phase22-realization-design.md` §1.46 (GAP-1 dissolution) + §1.45 (GAP-2 resolution).

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d` (KT
Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1; generalize the candidate
chain on the graph-free assembly; build the `⋀^{d−1}` duality via the top-power route per §1.33 (D), the
obsolete-at-`d=3` join↔meet leaves re-entering here; reuse the alg-independence machinery for the points).
Open Phase 23 with its own recon (eqs. 6.46–6.67 vs the `d=3` Lean) and add the general-`d`
alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **GAP 1 DISSOLVED — the producer never consumes `(G.splitOff …).Simple` (build-free recon, 2026-06-09;
  §1.46).** §1.44 flagged GAP 1 as a hole (the `4 ≤ |V|` guard unmet at the `|V|=3` triangle) with unblock (i)
  "supply `(G.splitOff …).Simple` at `|V|=3` directly." Re-tracing the *route* after the GAP-2 leaf landed:
  under the §1.45 B-derive route the producer takes the **bare** `hIH.2 : HasFullRankRealization k
  (G.splitOff …)` (the unconditional `.2` conjunct of `theorem_55_generic`'s `hsplitGP` IH, PanelHinge.lean:
  1167–1175), builds the bare candidate, then upgrades via `hasGenericFullRankRealization_of_rigidOn_ofNormals`
  — the IH's generic `.1` conjunct (the only split-simplicity consumer) is unused. And §1.44's unblock (i)
  was **false**: at `|V|=3`, `D=3`, `G` is the triangle, whose splitOff carries the surviving `ab`-edge + the
  fresh `e₀` (a parallel pair) = the double-edge `K₂`, not simple. So no `|V|=3` lemma exists or is needed; R3
  (`|V|≥4`) stays a reusable graph-side fact. Same "recon-traces-the-route, not the verdicts" lesson §1.44 named.
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
  lemmas' statements (GAP 1 since dissolved §1.46; GAP 2 since landed §1.45; GAP 3 in *Blockers*). The
  recon-traces-the-route lesson is in §1.44's closing paragraph — flagged for FRICTION/the next phase-close
  organization review. §1.46 (GAP-1 dissolution) is a fresh data point for that lesson: §1.44 adjudicated
  GAP 1 as a *brick* (the `4 ≤ |V|` guard) without tracing whether the producer/IH wiring ever reaches for
  it, and asserted a `|V|=3` simplicity fact without checking the triangle's edge count.
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
