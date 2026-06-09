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

**Next concrete step (smallest forward commit): Leaf 1 — `case_III_claim612` existential restate.**
Safe, local, buildable-now: replace the three-fixed-`Cᵢ`/`hduality` signature with the existential
conclusion (no premise), body = the verified 5-line contrapositive; ripple the two callers
(`case_III_eq629_conditional`, `case_III_hsplit_producer`). Reconcile the `lem:case-III-claim612`
blueprint prose to the existential in the same commit.

After the producer lands (Leaf 3): instantiate `theorem_55 (n:=2) (k:=2)` with it + the green
`hcontract` (`case_I_realization`) and `hbase` (`theorem_55_base`); feed `rigidityMatrix_prop11`'s
`hgen` (its `hub` lower bound already green); Thm 5.5→5.6 push (`lem:motions-mono-of-graph-le`).
Milestone: the molecular conjecture at `d=3`, unblocking Cor 5.7 (Phases 24–26). General `d` (KT
Lemma 6.13) is **Phase 23** (reuse map: §1.33 (C)).

## Lemma checklist — the live leaf sequence (§1.39)

- [ ] **Leaf 1 — `case_III_claim612` existential restate** (RigidityMatrix.lean; **graph-free**, no §38).
  Conclusion → `∃ q : {q // q.1 < q.2}, r ⟨omitTwoExtensor (homogenize∘p) (ne_of_lt q.2), _⟩ ≠ 0`;
  drop `C₁ C₂ C₃`/`hduality`. Body = `by_contra; push Not at h; exact hr (eq_zero_of_annihilates_span_top
  (span_omitTwoExtensor_eq_top hp) (by rintro x ⟨q, rfl⟩; exact h q))` (verified closes). **Ripple:**
  `case_III_eq629_conditional` (:1809) drops `hduality`/`Cᵢ` — restate or **delete** (no callers; fold
  its node into `lem:case-III-claim612` prose); `case_III_hsplit_producer` (CaseI.lean:3688) drops
  `hduality`/`Cᵢ`/the three-fixed `hselᵢ`/`hmemᵢ`/`hcardᵢ`, body becomes green-modulo
  (`obtain ⟨q,hq⟩ := case_III_claim612 hr hp` + a carried candidate-at-line obligation). Reconcile the
  `lem:case-III-claim612` prose (case-iii.tex:1124–1133 describes the obsolete carry-`hduality` model).
  One green unit.
- [ ] **Leaf 2 — the line-indexed candidate placement** (CaseI.lean; **§38 `ofNormals` trap**).
  Generalize `case_II_placement_eq612`'s seed/shear construction to an **arbitrary witness line** `L`
  (the join `pᵢ∨pⱼ`'s line, `L ⊂ Π(u)`): build the candidate framework whose `va`-hinge support is
  `C(L)` and its `(D−1)` block rows span `(span C(L))^⊥`. Keep the row-space/independence reasoning over
  abstract `F`, instantiate `ofNormals` only at the seed (C1/C2 §38 discipline). Likely splits
  (seed-from-line; per-line block-failure/span criterion). Multi-commit.
- [ ] **Leaf 3 — wire the producer** (`case_III_hsplit_producer`, CaseI.lean; **§38 trap** at the C2
  feed). `obtain ⟨q,hq⟩ := case_III_claim612 hr hp`; extract line `L` from `q`, run Leaf 2 to build the
  candidate, run the row-space criterion at `C(L)` with `hq : r̂(pᵢ∨pⱼ) ≠ 0` → independent family →
  C2. Supply the four points `p` adapted to the real three panels (N3a-pattern). Discharges Leaf 1's
  green-modulo obligation. **C5c-(ii) — OLD/NEW-block `hmemᵢ`** rides alongside (independent; the
  `+1`-row `hmemᵢ` already in hand via `hingeRow_mem_rigidityRows`; `so`/`sn` blocks via L2
  `span_panelRow_comp_single_of_edge` / L4 `panelRow_mem_rigidityRows_of_link`).
- [ ] **Leaf 4 — `theorem_55` `d=3`-instance node** (B.2; graph-free). Instantiate
  `theorem_55 (n:=2) (k:=2)` on the three green branch args; mint the small green blueprint node
  (**not** a standalone `theorem_55_dim3` — avoids duplicating the statement; general `thm:theorem-55`
  stays red-pending-Phase-23).
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
  `extensor_join_eq_zero_of_complementIso_eq_zero_dotProduct` (Meet.lean, `b8477db`), and the C5a/C5b
  six-join dispatch in `case_III_claim612`'s current body (`d851264`). All graph-free, axiom-clean.
  (2026-06-08/09) §1.39.
- [x] **Capstone + abstract device feed** (`case_III_eq629_conditional`,
  `hasFullRankRealization_of_independent_panelRow_index`) — `case_III_eq629_conditional` becomes
  obsolete under the existential restate (no callers; fold its node into `lem:case-III-claim612`).
  (2026-06-07)

## Blockers / open questions

- **Architecture PINNED — existential conclusion, no `hann`** (2026-06-09, `notes/Phase22-realization-design.md`
  §1.39, supersedes §1.37/§1.38's B1). The three-fixed disjunction is undischargeable (dim 3 < 6,
  confirmed); KT's lines are *free* (eq. (6.12)/Claim 6.9), so Claim 6.12 is a genuine existential. The
  existential conclusion is directly provable (no premise) and consumable (candidate supports are
  panel-meets, matching the joins). No residual premise survives on `case_III_claim612`.
- **The genuine remaining work is the producer line-indexed re-parameterization** (Leaf 2/3, multi-commit,
  §38 trap). Producer-internal, no phase boundary. Same difficulty as §1.38's C5c-(2); the existential
  just removes the dead `hann`/C5c-assembly scaffolding.
- **Blueprint: `lem:case-III-claim612` + `lem:case-III-eq629-conditional` `\leanok` DROPPED (now
  honestly RED, 2026-06-09).** Both Lean decls carry/forward the undischargeable `hduality`, so the
  green dep-graph nodes were dishonest (honesty gate). Statement-level prose already reads as the
  existential and the stale carry-`hduality` formalization-aside was trimmed; `\lean{}` pins kept.
  Re-green at Leaf 1 once the existential restate lands. (Downstream `lem:case-III-candidate-row` is
  abstract — legitimately green, stops the cascade.)
- **The `ofNormals`/`withGraph` defeq-timeout trap** (TACTICS-QUIRKS §38) bites Leaf 2/3 (they
  instantiate the concrete carrier). `case_III_claim612` (Leaf 1) is graph-free — no trap. Keep
  reasoning over abstract `F`, instantiate only at the seed.

## Hand-off / next phase

**Smallest next commit: Leaf 1 — `case_III_claim612` existential restate** (graph-free, buildable now).
Restate the conclusion to `∃ q : {q // q.1 < q.2}, r ⟨omitTwoExtensor (homogenize∘p) (ne_of_lt q.2), _⟩ ≠ 0`,
drop `C₁ C₂ C₃`/`hduality`; body = the verified 5-line contrapositive. Ripple the two callers (delete or
restate `case_III_eq629_conditional`; green-modulo `case_III_hsplit_producer`). Reconcile the blueprint
formalization-aside in the same commit. One green unit. Full verification + the leaf sequence:
`notes/Phase22-realization-design.md` §1.39.

**Then Leaf 2/3 (the producer restructure, §38 trap, multi-commit):** generalize the candidate placement
to an arbitrary witness line, then wire the producer (`obtain` the join, build the candidate at its line,
run the row-space criterion, feed C2). C5c-(ii) OLD/NEW `hmemᵢ` rides alongside. **Leaf 4/5** (the green
`theorem_55 (n:=2) (k:=2)` instance node, the case-II/III flips, the Thm 5.5→5.6 push) unblock Cor 5.7.

After 22g closes (molecular conjecture at `d=3`, Cor 5.7 unblocked): **Phase 23** = general `d` (KT
Lemma 6.13), scoped with the §1.33 (C) reuse map (reuse Claim 6.11 + Lemma 2.1; generalize the candidate
chain on the graph-free assembly; build the `⋀^{d−1}` duality via the top-power route per §1.33 (D), the
obsolete-at-`d=3` join↔meet leaves re-entering here; reuse the alg-independence machinery for the points).
Open Phase 23 with its own recon (eqs. 6.46–6.67 vs the `d=3` Lean) and add the general-`d`
alg-independence row to `notes/AlgebraicIndependence.md`.

## Decisions made during this phase

### Phase-local choices and proof techniques

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
  (green). Fixed stale `case-i.tex:149–151`. (B.2) add a green `theorem_55 (n:=2) (k:=2)` instance node,
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
