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

**Leaf 1 LANDED (2026-06-09).** `case_III_claim612` is now the existential `∃ q : six joins,
r̂(join q) ≠ 0`, no `hann`/`hduality` premise (the 5-line contrapositive, axiom-clean). The producer
`case_III_hsplit_producer` dropped `Cᵢ`/`hduality`/the three-fixed `hselᵢ`/`hmemᵢ`/`hcardᵢ`; it now
`obtain`s the witness join and carries a single green-modulo hypothesis `hcand` (the line-indexed
candidate placement, Leaf 2/3). `case_III_eq629_conditional` was deleted (no code callers; its
blueprint node folded into `lem:case-III-claim612` — now flipped green). Build + lint + verify.sh +
supersession-gate all clean.

**CRUX SETTLED — verdict (B) (`notes/Phase22-realization-design.md` §1.40, 2026-06-09 producer-core
recon).** Is the line-indexed candidate placement constructible for an *arbitrary* one of the six
witness joins? **(B): yes, needs non-degeneracy, and the producer's OWN construction supplies it** —
N3a (`exists_affineIndependent_panel_incidence`, green) gives the nonparallel panels + affinely-indep
points covering all six joins uniformly (the `exists_hduality_witness_of_panel_incidence` `fin_cases q`
panel-assignment + `exists_independent_perp_pair` second normals, both green), and the Leaf-2b core
turns the witness `r̂(pᵢ∨pⱼ) ≠ 0` into the row-space-criterion input `r̂(C(e_a)) ≠ 0`. **Not** the
`hann`-trap shape (no per-witness premise can fail; the existential is fully consumed). The KEY
geometric fact the recon pinned: the candidate's `va`-line is `(-t)•C(e₀)` (`panelSupportExtensor_add_
smul_left`) — the shear `t` rescales but does NOT move the line, so each candidate tests ONE fixed
extensor (re-confirming why the three-fixed `Cᵢ` failed and the six-join existential was forced).

**R2 SETTLED — verdict (B) (`notes/Phase22-realization-design.md` §1.41, 2026-06-09 producer-signature
recon).** The §1.40 (R2) carried obligation (the one genuine open architectural question) is resolved:
the split-leg `ab`-transversality `hgab : LinearIndependent ![q(a,·),q(b,·)]` that
`case_II_placement_eq612` needs is **not** promised by the **bare** `_hsplit` but **is** the
`IsGeneralPosition` conjunct of the **GP** motive (`P.normal a = q(a,·)` by `rfl`, so GP-at-`a≠b` IS
`hgab`). The producer is restated to `theorem_55_generic`'s **`hsplitGP`** branch (GP `_hsplit`);
the **green precedent does exactly this** — `case_I_realization` IS `hcontractGP`, pulling each leg's
transversal from the GP IH; KT (pp. 680/682) takes `q` as *generic nonparallel*. Leaf-4 ripple:
instantiate **`theorem_55_generic (n:=2)(k:=2)`** (not bare), project the `.2` conjunct the capstone
needs (the existing two-motive skeleton absorbs it). NOT (C): GP `_hsplit` cleanly available at `d=3`
*given* a bounded side-condition, ripple trivial. **One new bounded sub-obligation (R3):** discharge
`(G.splitOff …).Simple` (the antecedent of the GP IH conjunct) — KT Lemma 6.7(ii)'s triangle argument
from `hnoRigid`, **not yet formalized** (a sibling of Case I's green `rigidContract`-simplicity leaf).
Re-shapes **Leaf 3** (producer signature + R3 discharge) + **Leaf 4** (instantiate generic), bounded
restatements + the bounded R3 leaf, not new *hard* math.

**Next concrete step (smallest forward commit): L2b-place per-line criterion — wire
`case_III_old_new_blocks_of_line`'s NEW block + the L2 span bridge into the row-space criterion at
`e_a`** (CaseI.lean; **§38 `ofNormals` trap** at the C2-feed). The line-indexed *block placement*
LANDED 2026-06-09 (`case_III_old_new_blocks_of_line`, CaseI.lean, axiom-clean): the generalization of
`case_III_old_new_blocks` that shears body `v` along an arbitrary witness-panel second normal `n'`
(not the fixed IH `n_b`), so the `va`-hinge `e_a` is the witness line `L = n_a ∧ n'` (support
`(-t)•C(L)`), carrying the two transversality facts (`hL`, `hnewtrans`) as explicit hypotheses. The
*seed-from-line geometric core* (`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`,
PanelLayer.lean) already turns the existential witness `r̂(pᵢ∨pⱼ) ≠ 0 ⟹ r̂(supportExtensor e_a) ≠ 0`.
What remains in L2b-place: feed the NEW block + L2 span bridge (`span_panelRow_comp_single_of_edge`)
into `linearIndependent_sumElim_candidateRow_iff` at `e_a` with `r̂(C(L)) ≠ 0` (the 2b core, fed `hq`)
→ the independent `D(|V|−1)`-family. Keep reasoning over abstract `F`, instantiate `ofNormals` only at
the seed (C1/C2 §38 discipline). Then Leaf 3 wires it into `hcand`.
**Two carried obligations the build must own** (§1.40 (5), do NOT block L2b-place): **(R1)** the
abstract-N3a ↔ real-placement panel reconciliation (N3a hardcodes normals `e₀,e₁,e₂`; the producer
needs an N3a *parameterized by the real `n_a,n_b,n_c`* — a new bounded graph-free leaf via
`exists_ne_zero_dotProduct_eq_zero` + the green det-polynomial route); **(R2) SETTLED — verdict (B)
(`notes/Phase22-realization-design.md` §1.41, 2026-06-09).** The split-leg `ab`-transversality
`hgab : LinearIndependent ![q(a,·),q(b,·)]` that `case_II_placement_eq612` needs is **not** promised
by the **bare** `_hsplit`, but **is** the `IsGeneralPosition` conjunct of the **GP** motive
(`P.normal a = q(a,·)` by `rfl`, so GP-at-`a≠b` *is* `hgab`). So the producer must be restated to
`theorem_55_generic`'s **`hsplitGP`** branch (consuming the GP `_hsplit`); the **green precedent does
exactly this** — `case_I_realization` IS `hcontractGP` and pulls each leg's transversal from the GP
IH. **Leaf-4 ripple: instantiate `theorem_55_generic (n:=2)(k:=2)`** (not bare `theorem_55`), project
the bare conclusion off the **`.2` conjunct** the capstone needs; the existing two-motive skeleton
absorbs it. NOT (C): the GP `_hsplit` is cleanly available at `d=3` *given* a bounded side-condition,
and the ripple is trivial. **One new bounded sub-obligation (R3):** discharge `(G.splitOff …).Simple`
(antecedent of the GP IH conjunct) — KT Lemma 6.7(ii)'s triangle argument from `hnoRigid`, **not yet
formalized** (`minimal_kdof_reduction` does not hand it down; sibling of Case I's green
`rigidContract`-simplicity leaf). Re-shapes **Leaf 3** (producer signature + R3 discharge) + **Leaf 4**
(instantiate generic), bounded restatements + the bounded R3 leaf, not new *hard* math.

After the producer lands (Leaf 3): instantiate `theorem_55_generic (n:=2) (k:=2)` (R2 verdict (B),
§1.41 — not bare `theorem_55`) with the restated producer as `hsplitGP` + the green `hcontractGP`
(`case_I_realization`) and `hbase`/`hbaseGP`, projecting the bare `.2` conjunct; feed
`rigidityMatrix_prop11`'s `hgen` (its `hub` lower bound already green); Thm 5.5→5.6 push
(`lem:motions-mono-of-graph-le`).
Milestone: the molecular conjecture at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT
Lemma 6.13) is **Phase 23** (reuse map: §1.33 (C)).

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
- [~] **Leaf 2b — the line-indexed candidate placement** (CaseI.lean; **§38 `ofNormals` trap**;
  multi-commit, IN PROGRESS).
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
  - [ ] **L2b-place per-line criterion** (CaseI.lean; §38 trap at the `ofNormals` C2-feed): wire
    `case_III_old_new_blocks_of_line`'s NEW block + the L2 span bridge (`span_panelRow_comp_single_of_
    edge`) into `linearIndependent_sumElim_candidateRow_iff` at `e_a` with `r̂(C(L)) ≠ 0` (from the 2b
    geometric core, fed the witness `hq`) → the independent `D(|V|−1)`-family. Keep reasoning over
    abstract `F`, instantiate `ofNormals` only at the seed.
- [ ] **N3a-from-normals (R1)** (CaseI/RigidityMatrix.lean; graph-free): an N3a *parameterized by the
  real nonparallel `n_a,n_b,n_c`* — `∃ p, AffineIndependent p ∧ (six-join incidence rel. the real
  normals)` — via `exists_ne_zero_dotProduct_eq_zero` (green) per panel + the green det-polynomial
  affine-indep route. Replaces the hardcoded-normals `exists_affineIndependent_panel_incidence` for the
  producer; new but bounded (all machinery green).
- [ ] **Leaf 3 — discharge the producer's `hcand`** (`case_III_hsplit_producer`, CaseI.lean; **§38 trap**
  at the C2 feed). Build `hcand q hq` from `hq : r̂(pᵢ∨pⱼ) ≠ 0`: extract line `L` from `q`, run L2b-place
  to build the candidate at `C(L)`, run the row-space criterion at `C(L)` → independent family → C2.
  Supply the four points `p` adapted to the real three panels via N3a-from-normals (R1). **(R2) SETTLED
  — (B), §1.41: restate the producer to `theorem_55_generic`'s `hsplitGP` shape** (gains `G.Simple` +
  the conditioned IH; concludes `HasGenericFullRankRealization 2 G`), pull `q` + `hgab` from the GP
  `_hsplit`'s `IsGeneralPosition` conjunct (`P.normal a = q(a,·)` by `rfl`, so GP-at-`a≠b` IS `hgab`),
  discharging the `(G.splitOff …).Simple` antecedent of that conjunct via **the new bounded R3 leaf**
  (KT Lemma 6.7(ii)'s triangle argument from `hnoRigid` — not yet formalized; sibling of Case I's green
  `rigidContract`-simplicity). Mirrors the green `case_I_realization` (= `hcontractGP`). Removes the
  green-modulo `hcand` hypothesis. The six-join
  panel dispatch reuses `exists_hduality_witness_of_panel_incidence`'s `fin_cases q` assignment +
  `exists_independent_perp_pair` (both green). **C5c-(ii) — OLD/NEW-block `hmemᵢ`** rides alongside
  (`+1`-row already in hand via `hingeRow_mem_rigidityRows`; `so`/`sn` via L2
  `span_panelRow_comp_single_of_edge` / L4).
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

- **Architecture PINNED — existential conclusion, no `hann`** (2026-06-09, `notes/Phase22-realization-design.md`
  §1.39, supersedes §1.37/§1.38's B1). The three-fixed disjunction is undischargeable (dim 3 < 6,
  confirmed); KT's lines are *free* (eq. (6.12)/Claim 6.9), so Claim 6.12 is a genuine existential. The
  existential conclusion is directly provable (no premise) and consumable (candidate supports are
  panel-meets, matching the joins). No residual premise survives on `case_III_claim612`.
- **CRUX VERDICT (B) — constructible, needs non-degeneracy, producer's own data supplies it**
  (2026-06-09, `notes/Phase22-realization-design.md` §1.40). The line-indexed candidate placement IS
  constructible for an arbitrary one of the six witness joins: N3a + perp-pair cover all six uniformly,
  and the Leaf-2b core turns the witness into the row-space-criterion input. NOT (C): the non-degeneracy
  (nonparallel panels, affinely-indep points, per-opposite-join second normal) is supplied by the
  producer's own construction, not a fragile Case-III hypothesis that could fail for a specific witness;
  this is not the `hann`-trap shape (no per-witness premise survives).
- **Two carried obligations the build must own (§1.40 (5)), the reason it is (B) not (A):**
  - **(R1) abstract-N3a ↔ real-placement panels.** The Leaf-2b core's `n_u, n'` are the candidate's
    *real* IH normals (`n_a = q(a,·)`, `n_b = q(b,·)` off `_hsplit`), but `exists_affineIndependent_panel_
    incidence` hardcodes `n = e₀,e₁,e₂`. The build needs an N3a *parameterized by the real `n_a,n_b,n_c`*
    so the witness points are orthogonal to the real normals — a new bounded graph-free leaf (green
    machinery: `exists_ne_zero_dotProduct_eq_zero` + det-polynomial affine-indep route). The current N3a
    is the wrong shape for the producer.
  - **(R2) split-leg `ab`-transversality — SETTLED, verdict (B)** (`notes/Phase22-realization-design.md`
    §1.41, 2026-06-09). `case_II_placement_eq612` needs only the **pair** `hgab : LinearIndependent
    ![q(a,·),q(b,·)]` (not the triple — that is R1's witness-points stage). The **bare** `_hsplit`
    (`HasFullRankRealization`) carries no panel-normal LI promise; the **GP** motive
    (`HasGenericFullRankRealization`) does — its `IsGeneralPosition` conjunct is `∀ a b, a≠b →
    LinearIndependent ![normal a, normal b]`, and `normal a = q(a,·)` by `rfl`, so GP-at-`a≠b` **is**
    `hgab`. So the producer is restated to `theorem_55_generic.hsplitGP` (consume the GP `_hsplit`). The
    **green precedent settles it**: `case_I_realization` IS `hcontractGP`, pulling each leg's transversal
    from the GP IH (`hQHgp`). KT (pp. 680/682, Lemma 6.10) takes the IH realization `q` as **generic
    nonparallel** — the GP data — resting on `G_v^{ab}` simple (Lemma 6.7(ii)) + the "nonparallel if
    simple" standing IH. **One new bounded sub-obligation (R3):** the producer must discharge
    `(G.splitOff …).Simple` (the antecedent of the GP IH conjunct) — KT Lemma 6.7(ii)'s
    triangle-from-`hnoRigid` argument, **not yet formalized** (`minimal_kdof_reduction` does not hand it
    down; a sibling of Case I's green `rigidContract`-simplicity leaf). NOT (C): the GP `_hsplit` is
    cleanly available at `d=3` *given* R3's bounded side-condition, and the Leaf-4 ripple (instantiate
    `theorem_55_generic`, project `.2`) is
    absorbed by the existing two-motive skeleton. Fully tracked by the two-motive split — NOT a smuggled
    hypothesis.
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

**Smallest next buildable sub-leaf: L2b-place per-line criterion — wire
`case_III_old_new_blocks_of_line`'s NEW block + the L2 span bridge into
`linearIndependent_sumElim_candidateRow_iff` at `e_a`** (CaseI.lean, §38 `ofNormals` trap at the
C2-feed). The line-indexed *block placement* LANDED 2026-06-09 (`case_III_old_new_blocks_of_line`,
CaseI.lean, axiom-clean): the generalization of `case_III_old_new_blocks` shearing body `v` along an
arbitrary witness-panel second normal `n'` (not the fixed IH `n_b`), so the `va`-hinge `e_a` is the
witness line `L = n_a ∧ n'` (support `(-t)•C(L)`), with the two transversality facts (`hL`,
`hnewtrans`) as explicit hypotheses. Its *seed-from-line geometric core*
(`panelSupportExtensor_add_smul_left_ne_zero_of_join_ne_zero`, PanelLayer.lean) turns the existential
witness `r̂(join) ≠ 0 ⟹ r̂(supportExtensor e_a) ≠ 0` — the exact form
`linearIndependent_sumElim_candidateRow_iff` tests at `e_a`. What remains in L2b-place: feed that NEW
block + the L2 span bridge (`span_panelRow_comp_single_of_edge`, the `(D−1)` block rows spanning
`(span C(L))^⊥`) into the row-space criterion at `e_a` with `r̂(C(L)) ≠ 0` (the 2b core, fed the
witness `hq`) → the independent `D(|V|−1)`-family. Keep reasoning over abstract `F`, instantiate
`ofNormals` only at the seed (C1/C2 §38 discipline). Then **N3a-from-normals (R1)** and
**Leaf 3** discharge `hcand` (build the candidate at the witness line, run the criterion at `e_a` via
the 2b core, feed C2; supply `p` via the real-normals N3a). **(R2) is SETTLED — verdict (B), §1.41:**
Leaf 3 restates the producer to `theorem_55_generic.hsplitGP` (GP `_hsplit`, `hgab` from the
`IsGeneralPosition` conjunct, mirroring the green `case_I_realization`), and Leaf 4 instantiates
`theorem_55_generic (n:=2)(k:=2)` projecting `.2`; both bounded restatements against the existing
two-motive skeleton, not new math. Full plan: `notes/Phase22-realization-design.md` §1.41 (R2 verdict)
+ §1.40 (CRUX verdict + decomposition) + §1.39 (architecture).

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
- *The unit-normalized combination from a span-of-the-others membership*
  (`exists_smul_combination_eq_sub_of_mem_span_image_compl`) → FRICTION [mirrored].
- *The standard-basis `Basis.toDual` self-pairing is the dot product* (`Pi.basisFun_toDual_apply`) → FRICTION [mirrored].
- *`rw [eq]` of a function-valued term over-rewrites its partial applications — narrow with
  `conv_lhs`/`nth_rewrite`* → TACTICS-QUIRKS §41.
