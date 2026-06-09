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

**The genuine remaining math** is producer-internal and unchanged in difficulty from §1.38: the
candidate construction (currently three fixed seeds) must be **re-parameterized over the witness
join's line `L ⊂ Π(u)`** — build the eq.-(6.12) degenerate placement at an arbitrary `L`, run the
row-space criterion at `C(L)`. The geometric identity that makes the existential consumable: a
candidate support `(ofNormals …).supportExtensor e = panelSupportExtensor (normal u) (normal v)` is a
**panel-meet** (PanelHinge.lean:89, `rfl`), the same `complementIso`/`extensor` form as a join — so the
producer builds its candidate so its hinge line IS the witness join's line.

**Next concrete step (smallest forward commit):** **Leaf 3 (concrete seed)** — the graph-free C2-feed
assembly `case_III_realization_of_line` has LANDED (2026-06-09; CaseI.lean, axiom-clean); the remaining
Leaf-3 work is the concrete `ofNormals` instantiation behind the §38 trap — restate
`case_III_hsplit_producer` to the `theorem_55_generic.hsplitGP` shape (R2), build the candidate at the
witness line via `case_III_old_new_blocks_of_line` + the seed-from-line core, and feed
`case_III_realization_of_line`. **R3 is COMPLETE** (2026-06-09):
part (1) `isKDof_zero_of_triangle` (Deficiency.lean) + part (2) the `htri` discharge
(`triangle_isProperRigidSubgraph` + the hypothesis-free `splitOff_simple_of_noRigid_of_card`,
Operations.lean) are both axiom-clean. The triangle brick assembles `IsProperRigidSubgraph (G.induce
{v,a,b}) G n` from `isKDof_zero_of_triangle` + `induce_le` + a `4 ≤ V(G).ncard` proper-ness guard;
`splitOff_simple_of_noRigid_of_card` is the no-`htri` simplicity lemma Leaf 3 calls for the GP `hsplitGP`
shape. Full detail per leaf in the *Lemma checklist* + *Hand-off*; the checklist is the canonical
done/open ledger.

**Architecture + both GP residuals are SETTLED — no research-shaped node remains, the `d=3` producer
is genuinely buildable** (full traces: `notes/Phase22-realization-design.md` §1.39–§1.42). The
CRUX/R2 are verdict (B) (line-indexed placement constructible for an arbitrary witness join via the
producer's own N3a + perp-pair; the producer consumes the GP `hsplitGP`, `hgab` = its
`IsGeneralPosition` conjunct, mirroring the green `case_I_realization` = `hcontractGP`). R1 (A)
DISSOLVED + landed; R3 (A) the clean bounded triangle mirror, **now COMPLETE**. **Landed:** Leaf 1
(existential `case_III_claim612`), Leaf 2a/2b (join↔meet bridge + line-indexed candidate placement +
`case_III_full_family_of_line`), R1 (homogeneous core `exists_homogeneousIncidence_of_normals` +
consumer-restate to bare LI `pbar`), R3 (criterion `splitOff_simple` + discharge
`splitOff_simple_of_noRigid` + triangle-0-dof `isKDof_zero_of_triangle` + `htri` discharge
`triangle_isProperRigidSubgraph`/`splitOff_simple_of_noRigid_of_card`) — all axiom-clean (Lemma
checklist carries the per-leaf detail).

**Remaining (→ phase close): ~3–4 commits** — Leaf 3 concrete seed (`hcand` §38-trap discharge, producer
restated to `theorem_55_generic.hsplitGP`; the graph-free C2-feed assembly `case_III_realization_of_line`
is LANDED) ~1–2, Leaf 4 (`theorem_55_generic (n:=2)(k:=2)` instance, project `.2`) ~1, Leaf 5
(case-II/III flips + Thm 5.5→5.6 push feeding `rigidityMatrix_prop11`'s `hgen`) ~1 (§1.42).
Milestone: the molecular conjecture at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT Lemma
6.13) is **Phase 23** (reuse map: §1.33 (C)).

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
- [x] **R3 splitOff-simplicity COMPLETE** (Operations.lean; graph-side, bounded; §1.42 verdict (A)).
  Three-way split — criterion (DONE), bounded combinatorial discharge (DONE), triangle-0-dof brick
  parts (1)+(2) (DONE 2026-06-09); `splitOff_simple_of_noRigid_of_card` is the hypothesis-free
  simplicity lemma Leaf 3 calls:
  - [x] **R3-criterion** — `splitOff_simple` (Operations.lean, DONE 2026-06-09; axiom-clean,
    `propext` only). The bounded `hloop`/`hpar`-hypothesis criterion `(G.splitOff …).Simple`, the
    splitting-off sibling of the green `rigidContract_simple` (the criterion form; `map_simple` is its
    contraction-side analogue). Graph-side helper, no blueprint node (matching `rigidContract_simple` /
    `map_simple`, neither pinned). `not_isLoopAt` via `isLink_self_iff`, `eq_of_isLink` = `hpar`.
  - [x] **R3-discharge (bounded combinatorial half)** — `splitOff_simple_of_noRigid`
    (Operations.lean, DONE 2026-06-09; axiom-clean). Discharges `splitOff_simple`'s `hloop`/`hpar` from
    `[G.Simple]` + `heab`/`hG_ea`/`hG_eb` + `hnoRigid`, carrying the triangle-rigidity brick as one
    explicit hypothesis `htri : ∀ f, G.IsLink f a b → ∃ H, H.IsProperRigidSubgraph G n`. The two
    combinatorial halves are bounded: looplessness (`a ≠ b` from `Simple.eq_of_isLink` on the two
    `va`-edges + `heab`; surviving edges inherit `IsLink.ne`) and the no-parallel-pair `rcases` over
    `splitOff_isLink`'s four cases (both-surviving = `Simple.eq_of_isLink`; both-fresh = `rfl`; the
    *mixed* KT obstruction = `htri f`+`hnoRigid`). **No 2-edge-connectivity** (standing §6.4 assumption,
    used in Lemma 4.6 to *find* the degree-2 vertex, already supplied). No friction, no blueprint node
    (sibling of the unpinned `rigidContract_simple`).
  - [x] **R3-triangle-brick part (1) — `isKDof_zero_of_triangle`** (Deficiency.lean, DONE 2026-06-09;
    axiom-clean, no blueprint node). A triangle is `0`-dof for `D ≥ 3`, via the `def ≤ 0` partition
    route (NOT the rank route §1.43 sketched). Full route + the recon-over-engineered lesson: *Decisions
    made* / *Hand-off*.
  - [x] **R3-triangle-brick part (2) — the `htri` discharge** (Operations.lean, DONE 2026-06-09;
    axiom-clean, no blueprint node). `triangle_isProperRigidSubgraph` assembles the
    `IsProperRigidSubgraph (G.induce {v,a,b}) G n` witness from `isKDof_zero_of_triangle` (the 0-dof,
    fed `rfl` for `V(H) = {v,a,b}` and the `E(H) = {eₐ,f,e_b}` computation), `induce_le`, and a
    `4 ≤ V(G).ncard` proper-ness guard (for `{v,a,b} ⊂ V(G)`). The edge-set exactness is the only
    `G.Simple` step — a fourth induced edge has loopless ends among `{v,a,b}`, so it is parallel to one
    of the three (`first | … |` over `IsLink.unique_edge`/`.symm`). `splitOff_simple_of_noRigid_of_card`
    then drops `htri` entirely (calls the triangle brick with `hnoRigid`), the form Leaf 3 consumes for
    the GP `hsplitGP` shape. The `isKDof_zero_of_triangle` arg order is vertices `v,a,b`, so its three
    edges are `va,ab,vb` (the `ab`-edge `f` is the *middle*). No friction; mathlib `Graph.induce` API
    (`induce_isLink`/`edgeSet_induce`, `V(induce X) = X` by `rfl`) slotted in cleanly.
- [ ] **Leaf 3 — discharge the producer's `hcand`** (`case_III_hsplit_producer`, CaseI.lean; **§38 trap**
  at the C2 feed). Two sub-steps:
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
  - [ ] **Leaf 3 concrete seed (§38 trap)** — **(R2) (B), §1.41: restate the producer to
    `theorem_55_generic`'s `hsplitGP` shape** (gains `G.Simple` + the conditioned IH; concludes
    `HasGenericFullRankRealization 2 G`), pull `q` + `hgab` from the GP `_hsplit`'s `IsGeneralPosition`
    conjunct, discharging `(G.splitOff …).Simple` via the R3 leaf. Mirrors the green `case_I_realization`
    (= `hcontractGP`). Feed `exists_homogeneousIncidence_of_normals` (the producer's own nonparallel
    triple) for `pbar`/`hpbar` (R1). Build `hcand q hq` from `hq : r̂(join q) ≠ 0`: extract line `L`, run
    `case_III_old_new_blocks_of_line` to build the candidate at `C(L)` (supplying `hane`/OLD-block
    `hold`/`holdindep`), get `r̂(C(e_a)) ≠ 0` from the seed-from-line core + `hq`, and feed
    `case_III_realization_of_line` (the C2-feed assembly above). **C5c-(ii) — OLD/NEW-block `hro_mem`/
    `hcand_mem`** ride alongside (`+1`-row via `hingeRow_mem_rigidityRows`; `so` via L4
    `panelRow_mem_rigidityRows_of_link`). Removes the green-modulo `hcand`. (~1–2 commits.)
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
- **All three GENERAL-POSITION obligations SETTLED — the `d=3` producer is buildable** (canonical home
  §1.41–§1.42). One-line verdicts:
  - **(R1-affine) (A) — DISSOLVES.** No de-homogenization: consumers bottom out on the affine-free
    Lemma 2.1 (any LI 4-family), feed the green homogeneous core directly. LANDED (core + consumer-restate).
  - **(R2) (B) — consume the GP `_hsplit`.** `hgab` is `theorem_55_generic.hsplitGP`'s `IsGeneralPosition`
    conjunct (green precedent `case_I_realization` = `hcontractGP`); Leaf-4 ripple = project `.2`.
  - **(R3) (A) — COMPLETE 2026-06-09, clean triangle mirror, no 2-edge-connectivity.** `(G.splitOff
    …).Simple` via the triangle-`{va,vb,ab}` contradiction off `_hnoRigid` (KT Lemma 6.7(ii)). All four
    pieces axiom-clean: criterion `splitOff_simple`, combinatorial discharge `splitOff_simple_of_noRigid`,
    triangle-0-dof `isKDof_zero_of_triangle` (the `def ≤ 0` partition route, NOT the §1.43 rank route),
    and the `htri` discharge `triangle_isProperRigidSubgraph` + the hypothesis-free
    `splitOff_simple_of_noRigid_of_card`.
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
R1 (homogeneous core + bare-LI consumer-restate), and **R3 COMPLETE** (criterion `splitOff_simple`,
discharge `splitOff_simple_of_noRigid`, triangle-0-dof `isKDof_zero_of_triangle`, `htri` discharge
`triangle_isProperRigidSubgraph` + the hypothesis-free `splitOff_simple_of_noRigid_of_card`). Both GP
residuals settled (§1.42): R1 dissolved, R3 a clean bounded triangle mirror. **No research-shaped node
remains — the `d=3` producer is genuinely buildable.**

**Landed this commit:** the graph-free C2-feed assembly `case_III_realization_of_line` (CaseI.lean,
axiom-clean) — runs `case_III_full_family_of_line` at `e_a` then feeds the full family straight into C1
(`hasFullRankRealization_of_independent_rigidityRow`); the abstract half of Leaf 3, off the §38 trap.

**Smallest next buildable sub-leaf — Leaf 3 concrete seed (the §38 trap; ~1–2 commits).**
- Restate `case_III_hsplit_producer` to `theorem_55_generic.hsplitGP` (GP `_hsplit`, `hgab` from the
  `IsGeneralPosition` conjunct, `(G.splitOff …).Simple` via R3 `splitOff_simple_of_noRigid_of_card`,
  mirroring the green `case_I_realization`); feed `exists_homogeneousIncidence_of_normals` (the producer's
  own nonparallel triple) for `pbar`/`hpbar`. For the witness `hq`, build the line-indexed candidate at
  `ofNormals G ends q₀` via `case_III_old_new_blocks_of_line` (supplying `hane`/OLD-block
  `hold`/`holdindep`), get `r̂(C(e_a)) ≠ 0` from the seed-from-line core + `hq`, assemble `hro_mem`/
  `hcand_mem`/`hcard`, and feed `case_III_realization_of_line` (landed). The concrete `ofNormals`
  instantiation is the only §38-trap surface left.
  Full plan: `notes/Phase22-realization-design.md` §1.42 (R1/R3) + §1.41 (R2) + §1.40 (CRUX) + §1.39.

**Leaf 4/5** (the green `theorem_55_generic (n:=2) (k:=2)` instance node + `.2` projection per the R2
ripple §1.41, the case-II/III flips, the Thm 5.5→5.6 push) unblock Cor 5.7.

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d` (KT
Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1; generalize the candidate
chain on the graph-free assembly; build the `⋀^{d−1}` duality via the top-power route per §1.33 (D), the
obsolete-at-`d=3` join↔meet leaves re-entering here; reuse the alg-independence machinery for the points).
Open Phase 23 with its own recon (eqs. 6.46–6.67 vs the `d=3` Lean) and add the general-`d`
alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

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
- **R1-consumer-restate — extract the affine-free Lemma 2.1 verbatim, make the affine form its
  corollary (2026-06-09; Extensor/RigidityMatrix/CaseI.lean).** `omitTwoExtensor_linearIndependent`'s
  proof never reads the affine origin of `v` — it bottoms out on `LinearIndependent ℝ v` and the
  `homogenize` bridge `have` was its only affine-aware step. So the affine-free core
  `omitTwoExtensor_linearIndependent_of_li` is the verbatim body minus that bridge, and the affine
  form is the one-line corollary at `v = homogenize ∘ p`. Both consumers (`span_omitTwoExtensor_eq_top`,
  `case_III_claim612`) + the producer (`case_III_hsplit_producer`) restate to bare `pbar : Fin 4 → ℝ⁴`
  + `LinearIndependent ℝ pbar`; the body of `case_III_claim612` was unchanged (the existential proof
  already routed only through `span_omitTwoExtensor_eq_top hp`). Pure-refactor, no friction.
- **R1 homogeneous-vector core — split R1 at the de-homogenization boundary, the genericity-free part
  first (2026-06-09; RigidityMatrix.lean, `exists_homogeneousIncidence_of_normals`).** Producing affine
  `p : Fin 4 → ℝ³` from arbitrary nonparallel `n` is genuinely genericity-bearing (an orthogonal
  vector can lie at infinity), so R1 split at that boundary: the homogeneous-vector layer (LI `pbar`
  + incidence rel. `n`) needs **no** genericity — surjectivity of the pairing `mulVecLin (of n)` (full
  row rank) hands a preimage per target, four-point LI is the triangular incidence argument. The
  affine de-homogenization (the genericity residual) is the deferred R1-affine sub-leaf. Mirrors how
  the green N3a bricks isolate `P ≠ 0` from the linear-algebra glue. Needed import `…Matrix.Rank`.
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
- **CaseI.lean producer-core recon — CRUX verdict (B) (2026-06-09; canonical home
  `notes/Phase22-realization-design.md` §1.40).** The line-indexed candidate placement is constructible
  for an arbitrary witness join (N3a + perp-pair cover all six uniformly; the Leaf-2b core feeds the
  criterion); the non-degeneracy needed is supplied by the producer's own construction, not a fragile
  hypothesis (NOT the `hann`-trap). Pinned the load-bearing fact: the shear `t` rescales but does not
  move the candidate line (`panelSupportExtensor_add_smul_left`), so each candidate tests one fixed
  extensor — re-confirming the three-fixed failure and the six-join existential. Surfaced two carried
  build obligations: (R1) N3a must be re-shaped to take the real panel normals (currently hardcodes
  `e₀,e₁,e₂`); (R2) the bare-vs-GP motive branch for the split-leg `ab`-transversality. Full trace +
  buildable-leaf decomposition: §1.40.
- **R2 producer-signature verdict — (B), the producer consumes the GP `_hsplit` (2026-06-09; canonical
  home `notes/Phase22-realization-design.md` §1.41).** `case_II_placement_eq612` needs the pair
  `hgab : LinearIndependent ![q(a,·),q(b,·)]`, which the **bare** `_hsplit` does not promise but the
  **GP** motive does (`IsGeneralPosition` ⇒ `LinearIndependent ![normal a, normal b]`, and `normal a =
  q(a,·)` by `rfl`, so GP-at-`a≠b` IS `hgab`). Green precedent: `case_I_realization` IS `hcontractGP`,
  pulling each leg's transversal from the GP IH. KT (pp. 680/682) takes `q` as *generic nonparallel*
  resting on `G_v^{ab}` simple (Lemma 6.7(ii)). Route: restate producer to `theorem_55_generic.hsplitGP`;
  Leaf-4 ripple = instantiate `theorem_55_generic`, project `.2` (capstone needs only the bare bound —
  GP is internal). New bounded sub-obligation **R3**: discharge `(G.splitOff …).Simple` (Lemma 6.7(ii)
  triangle argument, *not yet formalized*; sibling of Case I's green `rigidContract`-simplicity). (B)
  not (C): GP `_hsplit` cleanly available *given* R3, ripple absorbed by the existing skeleton.
- **R1-affine + R3 verdicts — both (A), no gap (2026-06-09; canonical home
  `notes/Phase22-realization-design.md` §1.42).** **R1-affine DISSOLVES:** the affine de-homogenization
  is not needed — Lemma 2.1's spanning content holds for any LI 4-family
  (`omitTwoExtensor_linearIndependent_of_li`, body verified to close) and the seed-from-line bridge is
  `⬝ᵥ`-orthogonality on bare `Fin 4 → ℝ`, so restate the consumers to bare LI `pbar` and feed the green
  homogeneous core directly (the at-infinity danger lives only in the de-homogenization map the build
  never calls; NOT the hann-trap). **R3 is the clean bounded triangle mirror** of the green
  `rigidContract_simple`: KT Lemma 6.7(ii) (p. 677) uses only `G.Simple` + `hnoRigid` + the split data +
  triangle-is-0-dof — **no 2-edge-connectivity** (a standing §6.4 assumption used elsewhere). Both
  dischargeable ⟹ the `d=3` producer is genuinely buildable. (Corrected §1.41's drifted
  `rigidContract_isSimple_of_isProperRigidSubgraph` pointer — the green decl is `rigidContract_simple`.)
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
- *The `(Matrix.of ![pi,pj]).mulVecLin x i = ![pi,pj] i ⬝ᵥ x` per-coordinate unfold* → FRICTION [resolved].
- *"row-LI ⟹ `mulVecLin` surjective" is not packaged — compose `LinearIndependent.rank_matrix` +
  `eq_top_of_finrank_eq`; the lemma is root `sum_dotProduct`* → FRICTION [resolved].
- *The unit-normalized combination from a span-of-the-others membership*
  (`exists_smul_combination_eq_sub_of_mem_span_image_compl`) → FRICTION [mirrored].
- *The standard-basis `Basis.toDual` self-pairing is the dot product* (`Pi.basisFun_toDual_apply`) → FRICTION [mirrored].
- *`rw [eq]` of a function-valued term over-rewrites its partial applications — narrow with
  `conv_lhs`/`nth_rewrite`* → TACTICS-QUIRKS §41.
