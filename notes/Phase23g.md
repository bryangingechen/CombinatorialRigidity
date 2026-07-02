# Phase 23g — Case III general `d`: ENTRY (chain extraction) + CHAIN-5 (dispatch reshape) (work log)

**Status:** in progress (opened 2026-07-01). The `ENTRY` sub-phase of the Case III
general-`d` program. **CHAIN-5 landed 2026-07-01** (`74bd9003`) — the 23f router
`chainData_dispatch` now *discharges* the Case-III chain dispatch at general `k`. **The ENTRY
extractor `hextract` (design §C.2) is now discharged at general `n`** (E3, landed 2026-07-02); the
single remaining Case-III green-modulo hypothesis is `hcycle` (E5, the Lemma 5.4 cycle brick).
`d=3` stays fully green throughout. Authoritative scoping:
`notes/Phase23-design.md` §C.0–C.6 (frozen CHAIN↔ENTRY contract) + **§(4.107)** (the ENTRY
satisfiability verdict + the E1–E5 leaf ladder; supersedes §C.2's chain-only reading) +
**§(4.107.G)** (the E2c/E2d/E2e settle: pinned signatures + the E2 internal build order) +
**§(4.108)** (the E5 detailed recon: the E5a/E5b/E5c ladder, exact signatures, blueprint plan,
3-commit estimate, keep-in-23g recommendation); the `d=3` map is §C.4. Program map:
`notes/MolecularConjecture.md`. `ASSEMBLY` = **23h** (later sub-phase).

## Current state

**Next concrete build step: E5c** — the `d=3`-patterned cycle-realization assembly
`PanelHingeFramework.cycle_realization` (`CaseIII/Arms.lean`, §(4.107.D) E5 pin verbatim; stanzas
in §(4.108.D)): `Function.extend cy.vtx` seed off `vtx_inj`, per-edge sign facts via
`endsOf_eq_or_swap` + `choose`, close with the GAP-2 upgrade
`hasGenericFullRankRealization_of_rigidOn_ofNormals` fed by E5b's `theorem_55_cycle`. Extracts the
new accessor `CycleData.range_vtx` (refactor of `vertexSet_ncard`'s inline `hrange`) and mints
`def:cycle-data` + pins/greens `lem:cycle-realization` (§(4.108.E)). **E5c closing discharges
`hcycle`, closes ENTRY, and closes 23g** — the phase-close checklist fires on it (incl. the E1–E3
`molecular-induction.tex` blueprint sync, §(4.108.E)).

**Landed 2026-07-02:** E5b (`theorem_55_cycle`, `Pinning.lean`, α-level cycle rigidity — the E5c
consumer) and E5a (`exists_cycle_normals`, `PanelLayer.lean`), both axiom-clean; E3
(`Graph.chainData_extract`) discharged `hextract` at general `n`; E2 (KT Lemma 4.6) closed. The
heavy machinery E5c assembles is all green (the `lem:cycle-realization` telescoping cluster, the
`m ≤ D` extensor existence, the GAP-2 upgrade); E5c is a triangle-patterned assembly plus the
`range_vtx` refactor. Recon **keep E5 in 23g, no own-letter split** (design §(4.108.F)) — pending
the user's call, surfaced by the coordinator.

**E2-assembly landed complete 2026-07-02**: `chainData_or_cycleData_of_noRigid`
(`ForestSurgery/ChainExtraction.lean`), the §(4.107.D) pinned public signature — closing the
**entire E2 leaf** (KT Lemma 4.6) green + axiom-clean. `by_contra` pushes the goal's negation into
E2d-4's `chainWalk_trichotomy` at every incidence, refuting its left (chain-or-cycle) arm to
supply the all-starts-terminated `hterm` E2d-7's `chainWalk_terminated_contradiction` consumes.
Per §(4.107.G.7)(i), E2b is **not** a dependency (confirmed in the assembly: the capped builder
starts from an arbitrary incidence, never from a degree-2 vertex specifically).

**E2d-5 landed 2026-07-02**: `chainWalk_isPrefix_or_isPrefix` (chain-walk determinism: two paths
sharing their first vertex and first edge, all interior vertices of degree 2, are
`WList.IsPrefix`-comparable), exact signature per design §(4.107.G.5),
`ForestSurgery/ChainExtraction.lean`. Structural induction on the pair: the shared first edge
forces a shared second vertex (`IsLink` endpoint determinism), a nil tail is a prefix outright,
and the degree-2 closure (`isLink_eq_of_degree_eq_two`) at the shared second vertex — interior
to both paths — pins the two tails' first edges equal for the recursion.

**Landed so far** (all exact-signature per the design pins; per-leaf detail in *Decisions made*
and the *Lemma checklist*): E1 + E4 (the interface leaves — `Graph.CycleData`, the shape-2
`hextract`/`hcycle` binder reshape at the four producer/spine sites, `d=3` wrappers refilled);
E2a (min-degree ≥ 2 + connectivity companion); E2b (degree-2 existence); E2c (the general
cycle→proper-rigid-subgraph triangle, both halves); E2d-1 (path→`ChainData` bridge, opened
`ForestSurgery/ChainExtraction.lean`); E2d-2 (cycle-branch confinement); E2d-3 (closed-walk
`Fin`-cyclic packaging + `CycleData` consumer); E2e (`kt_lemma_46_linking` + `le_bodyBarDim`);
E2d-4 (`chainWalk_trichotomy`, the capped-trichotomy walk-builder); E2d-5 (determinism); E2d-6
(the fiber lemma + `chainWalk_charging` proper); E2d-7 (`chainWalk_terminated_contradiction`, the
arithmetic close); **E2-assembly** (`chainData_or_cycleData_of_noRigid`, closing **E2** — KT
Lemma 4.6 — in full); **E3** (`Graph.chainData_extract`, discharging `hextract` at general `n`).
Remaining: E5. ENTRY satisfiability SETTLED
(design §(4.107)):
**OD-1 = shape 2** (Lemma 5.4 load-bearing, `hcycle`/E5 genuine). CHAIN-5 is done (dispatch
discharged at general `k`); `hextract`/`hcycle` are discharged at `n=3`; everything below the
contract is landed (the `ChainData` record with `d_eq : d = n` + `d_eq_kAdd`, the geometry arm,
the `chainData_dispatch` router, the C.4 adapter).

## Lemma checklist (the §(4.107.D) ENTRY ladder)

- [x] **E1** `Graph.CycleData` record + `CycleData.vertexSet_ncard` (`Operations.lean`) — landed
  2026-07-01
- [x] **E4** the `hextract` binder reshape to the shape-2 disjunction + the new green-modulo
  `hcycle` at the four producer/spine sites (`Arms.lean` ×2 / `Realization.lean` / `Theorem55.lean`);
  `d=3` wrappers: `Or.inl ∘ chainData_extract_d3` + vacuous `hcycle` (`omega`) — landed 2026-07-01,
  zero-regression
- [x] **E2** `Graph.chainData_or_cycleData_of_noRigid` — KT Lemma 4.6, the genuinely-new
  combinatorial leaf (the long pole) — landed complete 2026-07-02; **split along its §(4.107.D)
  sub-leaves, one commit each**:
  - [x] **E2a** min-degree ≥ 2 + connectivity companion — `two_le_degree_of_isKDof_zero` /
    `preconnected_of_isKDof_zero` (`Molecular/Deficiency.lean`) — landed 2026-07-01
  - [x] **E2b** degree-2 existence — `exists_degree_eq_two_of_noRigid`
    (`ForestSurgery/Reduction.lean`) — landed 2026-07-01
  - [x] **E2c** — deficiency count `isKDof_zero_of_cycle` (`Deficiency.lean`) + the wrapper
    `cycle_isProperRigidSubgraph` + helper `exists_isLink_not_eq_of_three_le_degree`
    (`Operations.lean`, the general `triangle_isProperRigidSubgraph`) — landed 2026-07-01
  - [x] **E2d** the maximal-chain walk-builder + KT (4.6)–(4.9) counting contradiction —
    **decomposed 2026-07-01 into sub-commits, exact signatures in §(4.107.G.5), all in the NEW
    `ForestSurgery/ChainExtraction.lean`** (build order E2d-1 → E2d-2 → E2d-3 → E2e → E2d-4 →
    E2d-5 → E2d-6 → E2d-7) — all sub-commits landed 2026-07-02:
    - [x] **E2d-1** `chainData_of_isPath` (length-`n` interior-deg-2 path → `ChainData`) +
      `isLink_eq_of_degree_eq_two` helper — opens `ChainExtraction.lean` — landed 2026-07-01
    - [x] **E2d-2** `closed_path_degree_two_spanning` (all-deg-2 closed path + connected ⟹
      `V(G)`/`E(G)` confinement) — landed 2026-07-01
    - [x] **E2d-3** `exists_cyclic_data_of_closed_path` (the shared `Fin`-cyclic packaging core)
      + `cycleData_of_closed_path` — landed 2026-07-02
    - [x] **E2d-4** `chainWalk_trichotomy` — the length-`n`-capped extension: chain-disjunct at
      the cap, cycle-disjunct at deg-2 closure, lollipop absurd via E2c + `hnp`, else a
      terminated walk of length `≤ n−1` (the dense commit) — landed 2026-07-02
    - [x] **E2d-5** `chainWalk_isPrefix_or_isPrefix` — chain-walk determinism — landed
      2026-07-02
    - [x] **E2d-6** `chainWalk_charging` — `2·|X₂| ≤ (n−2)·Σ_{deg≥3} deg` (the KT (4.6)+(4.7)
      double count, §(4.107.G.5)) — landed 2026-07-02, both the fiber-lemma split-off
      (`chainWalk_isPrefix_of_terminated`) and `chainWalk_charging` proper (below-contract
      via `Set.ncard_le_ncard_of_injOn`, not the pinned sketch's `Finset.card_eq_sum_card_fiberwise`
      — see *Decisions made*)
    - [x] **E2d-7** `chainWalk_terminated_contradiction` — the (4.8)/(4.9) arithmetic close
      (`False`) — landed 2026-07-02
  - [x] **E2e** the numeric linking identity — `kt_lemma_46_linking`
    (`3 ≤ i → i(n−2) + 2 ≤ (D−1)(i−2)`, KT's display above (4.9)) + `le_bodyBarDim`
    (`n ≤ bodyBarDim n`, the lollipop's `m ≤ n ≤ D` cap), `ChainExtraction.lean` — landed
    2026-07-02
  - [x] **E2-assembly** compose the ladder into `chainData_or_cycleData_of_noRigid` (§(4.107.D)
    signature verbatim): `by_contra` → every incidence terminates (`hterm`) → E2d-7 — landed
    2026-07-02. Consumes E2a + E2c + E2d-1…7; **E2b is not an input** (§(4.107.G.7) — it stays
    landed, KT-expositional)
- [x] **E3** `Graph.chainData_extract` — compose E2 + the landed Lemma-4.8 stack; discharges
  `hextract` at general `n` — landed 2026-07-02, `ForestSurgery/ChainExtraction.lean`
  (below-contract file home, §(4.107.G.2) — not the §(4.107.D) literal `Reduction.lean` pin)
- [ ] **E5** `PanelHingeFramework.cycle_realization` — the Lemma 5.4 brick discharging `hcycle`
  (Crapo–Whiteley 1982 Prop. 3.4 / Whiteley 1999 Prop. 3, both verified from the PDFs +
  the GAP-2 genericity upgrade). **Recon SETTLED (design §(4.108)): 3 sub-commits, exact
  signatures in §(4.108.D), blueprint plan §(4.108.E); recommendation keep-in-23g (no
  own-letter split)**:
  - [x] **E5a** `exists_cycle_normals` — the cyclic shared-normal family at `3 ≤ m ≤ k + 2`
    (basis-choice witness; generalizes `exists_triangle_normals`) — `PanelLayer.lean`, landed
    2026-07-02, axiom-clean
  - [x] **E5b** `theorem_55_cycle` — the telescoping cycle rigidity on the graph's own vertex
    type `α` (`IsInfinitesimallyRigidOn (Set.range vtx)`; no `vtx` injectivity needed) —
    `Pinning.lean`, landed 2026-07-02, axiom-clean
  - [ ] **E5c** the assembly, §(4.107.D) pin verbatim — `Function.extend` seed off
    `cy.vtx_inj`, sign facts via `endsOf_eq_or_swap` + `choose`, close with the GAP-2
    upgrade; extracts `CycleData.range_vtx`; pins + greens `lem:cycle-realization` and mints
    `def:cycle-data` — `CaseIII/Arms.lean`

## Hand-off / next phase

**The smallest concrete next build commit is E5c** — the only remaining E5 leaf and the last
23g deliverable: `PanelHingeFramework.cycle_realization` (`CaseIII/Arms.lean`, §(4.107.D) E5 pin
verbatim; stanzas + `Function.extend`/`choose`/GAP-2 route in §(4.108.D)), consuming E5b's
`theorem_55_cycle` (α-level rigidity) and E5a's `exists_cycle_normals` (cyclic normals). It also
extracts the accessor `CycleData.range_vtx` (refactor of `vertexSet_ncard`), mints `def:cycle-data`,
and pins/greens `lem:cycle-realization` (§(4.108.E)). **E5c closing discharges `hcycle`, closes
ENTRY, and closes 23g** — the phase-close checklist fires on it (incl. the E1–E3
`molecular-induction.tex` blueprint sync noted in §(4.108.E)). The recon's **keep-E5-in-23g, no
own-letter split** recommendation (design §(4.108.F)) is still the coordinator's to surface for the
user's call; E5b was the second of the three E5 commits, so only E5c remains before that boundary.

Once E5c discharges `hcycle`, both green-modulo Case-III hypotheses (`hextract` from E3, `hcycle`
from E5) are available at general `n`; E3 stayed purely additive (the `d = 3` wrappers still fill
`hextract` via `chainData_extract_d3`), so the producer-site rewire to consume them at general `n`
is **ASSEMBLY** work (23h), tracked there, not scoped in 23g.

The E4 interface is in place: `hextract` returns the shape-2 disjunction and `hcycle` is carried
green-modulo, so E5c lands the cycle brick without further binder churn.

**ENTRY satisfiability — SETTLED (2026-07-01, design §(4.107)).** KT Lemma 4.6 yields a chain of
length **exactly** `d = n` (never shorter — `d_eq : d = n` is right), OR a cycle on `≤ n`
vertices; the cycle branch is reachable under `hextract`'s premises at `n ≥ 4` (cycles
`4 ≤ |V| ≤ n`), so OD-1 = shape 2 is forced and `hcycle`/E5 is a genuine deliverable. The `hD`
floor lift dissolves (§(4.107.E): honest leaf floor `3 ≤ bodyBarDim n`, spine keeps 6).

## Frozen contract + tracking (do NOT change in 23g)

- **The frozen contract is §C.0–C.6** (invariant). No motive/IH change (§C.6): the chain data is
  purely combinatorial; the base `(G₁,q₁)` is the existing `HasGenericFullRankRealization` premise
  from the same 0-dof IH conjunct; the `d`-candidate splits `Gᵢ` are *smaller* minimal-0-dof graphs
  at the same dof — no higher-dof `G_v` pattern.
- **Carry forward GAP 6** (KT's all-`k` nested IH (6.1) vs the project's 0-dof-only motive —
  orthogonal to the cert; tracked separately). ASSEMBLY = 23h; not opened here.

## Decisions made

### E5b — LANDED complete (2026-07-02)
`theorem_55_cycle` (`Pinning.lean`, next to `theorem_55_triangle`), §(4.108.D) signature verbatim,
axiom-clean, first-try clean build. The `α`-level cycle rigidity: `IsInfinitesimallyRigidOn
(Set.range vtx)` for a `Fin m`-indexed cycle `hlink : IsLink (edge i) (vtx i) (vtx (i+1))` under LI
of the `m` supporting extensors — **no `vtx` injectivity** (only constancy of `S ∘ vtx` on the
range is used). Proof re-runs `eq_succ_of_isInfinitesimalMotion_cycle`'s telescoping
(`Equiv.sum_comp (Equiv.addRight 1)` + `eq_zero_of_mem_span_singleton_of_sum_eq_zero`) and
`isTrivialMotion_of_isInfinitesimalMotion_cycle`'s `Fin.ofNat` induction directly on `fun i => S
(vtx i)`, closing on `rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩` range membership. Zero friction (verbatim
adaptation of two green `Fin m`-body lemmas). Blueprint: added to `lem:cycle-realization-rigid`'s
`\lean` group + one α-level prose sentence (`case-i.tex`, §(4.108.E)); no new node.

### E5a — LANDED complete (2026-07-02)
`exists_cycle_normals` (`PanelLayer.lean`, next to `exists_triangle_normals`), §(4.108.D) signature,
axiom-clean. Witness = standard basis along `Fin.castLE` (`nrm i = e_{castLE hmk i}`), so the `m`
cyclic joins realize the distinct 2-subsets `{i, i+1}` (edges of `Cₘ`). LI route: cyclic family
`= ε • (ιMulti_family ∘ ι)`, `units_smul_iff`, `ιMulti_family_linearIndependent_ofBasis.comp` with
the cyclic-edge→2-subset map `ι` injective. Two new `private` helpers generalize the triangle's
per-position bash: `normalsJoin_basisFun_ne_zero_of_ne` + `normalsJoin_basisFun_eq_sign_smul`.
- **Two below-contract deviations:** (i) added `[NeZero m]` instance binder — the pin's block
  omitted it but §C.2 states "under `[NeZero m]`" and the `i + 1` OfNat statement can't elaborate
  without it (`OfNat (Fin m)` needs `NeZero`); the "(`haveI` from `hm3`)" note is subsumed. (ii)
  `ι`-injectivity via regular `AddCommGroup (Fin m)` cancellation (`add_eq_left`/`add_right_cancel`,
  `[NeZero m]`), NOT the §70 scoped-ring route — no `open Fin.CommRing` needed.
- **Promoted:** *`Pi.smul_apply'` for function-on-function smul* + *`lt_or_gt_of_ne h` not
  `h.lt_or_lt` on `Ne`* → FRICTION [idiom] (two entries).

### E5 recon — SETTLED (2026-07-02, docs-only; design §(4.108) is the record)
E5 = E5a (`exists_cycle_normals`, cyclic shared-normal basis witness, `3 ≤ m ≤ k+2`) → E5b
(`theorem_55_cycle`, telescoping rigidity on `α`, no `vtx` injectivity) → E5c (the pinned
assembly, triangle-patterned, closing via the GAP-2 upgrade). Landed machinery verified
sufficient: the `Fin m` cycle cluster (`rankHypothesis_zero_of_cycle` et al.) is body-type-pinned
(not `d=3`-pinned) and `exists_independent_panelSupportExtensor` gives free *pairs* (unusable for
a shared-panel seed) — hence exactly the two small suppliers. Index bridges traced (§(4.108.C)):
`Function.extend cy.vtx` off `vtx_inj`; `⟨1,_⟩ = 1` under `NeZero`; `range_vtx`; `m ≤ k+2` from
`n = k+1`. KT [4]/[34] citations verified from the PDFs. Recommendation: no own-letter split.

### E3 — LANDED complete (2026-07-02)
`Graph.chainData_extract` (`ForestSurgery/ChainExtraction.lean`), the §(4.107.D) pinned public
signature verbatim, no content deviation — discharges `hextract` at general `n`. Splits E2's
result (`obtain hchain | ⟨cy, hcym⟩` — the cycle disjunct forwards unchanged) and, on the chain
disjunct, reads the interior `ChainData` fields at `i = ⟨1, by omega⟩` directly in the pin's
literal `(a, b) = (vtx 0, vtx 2)` order (predecessor, successor) — `deg_two`/`isLink_pred_edge`/
`isLink_succ_edge`/`pred_edge_ne` all match without a `splitOff_swap_ab` reconciliation (contrast
`chainData_extract_d3`'s fixed `![b,v,a,c]` labeling, which needs one). Purely additive: no
producer/spine site touched (they still fill `hextract` via `chainData_extract_d3` at `d=3`, or
carry it as a green-modulo binder at general `k`); wiring a general-`n` closed theorem to consume
`chainData_extract` is ASSEMBLY (23h) scope. One friction (`rcases`/`obtain`'s `⟨cd⟩ | h` pattern
doesn't unwrap a `Nonempty` nested inside an `Or` alternative — split into two steps) →
FRICTION *[idiom] `rcases`/`obtain` on `Nonempty X ∨ Y`…*.

### E2-assembly — LANDED complete (2026-07-02)
`chainData_or_cycleData_of_noRigid` (`ForestSurgery/ChainExtraction.lean`), the §(4.107.D) pinned
public signature verbatim, no content deviation — closes the entire **E2** leaf (KT Lemma 4.6).
Proof exactly per the design sketch: `by_contra hcon`, then `hterm` (the all-starts-terminated
hypothesis) is built by applying `chainWalk_trichotomy` (E2d-4) to every incidence and refuting
its left (chain-or-cycle) arm against `hcon` (`absurd`), leaving only its right (terminated-walk)
arm; `chainWalk_terminated_contradiction` (E2d-7) then closes `False` directly. No witness
construction for "some incidence exists" was needed in the Lean text — `hterm`'s `∀`-shape and
E2d-7's own internal derivation (`V(G).Nonempty` from `hV3`) absorb that reasoning without a
separate step. Zero friction: first-try clean build, pure composition of E2d-4 + E2d-7.

### E2d ladder + E2e — LANDED complete (2026-07-01/02)
All in `ForestSurgery/ChainExtraction.lean`, exact §(4.107.G.5) signatures, no content deviation
(reasoning in git + design §(4.107.G); FRICTION pointers preserved):
- **E2d-1** `isLink_eq_of_degree_eq_two` (degree-2 closure helper) + `chainData_of_isPath`
  (`WList → Fin` boundary conversion) → TACTICS-QUIRKS § 48 (the `x - a + b` parse trap, broadened).
- **E2d-2** `closed_path_degree_two_spanning` (confinement closure; `V(G)`/`E(G)` spanning).
- **E2d-3** `exists_cyclic_data_of_closed_path` + `cycleData_of_closed_path` (`Fin`-cyclic
  packaging) → FRICTION *`List.getD_eq_getElem`/`getD_eq_default`…* + § 63.
- **E2d-4** `chainWalk_trichotomy` (capped trichotomy; strong induction on `n − P.length`) →
  FRICTION *[idiom] `interval_cases` on an opaque-`def` floor needs the identity first*.
- **E2d-5** `chainWalk_isPrefix_or_isPrefix` (chain-walk determinism), zero friction.
- **E2d-6** `chainWalk_isPrefix_of_terminated` (fiber lemma) + `chainWalk_charging` (charging bound
  via one `Set.ncard_le_ncard_of_injOn` map, not the pinned fiberwise sum) → **TACTICS-QUIRKS § 71**.
- **E2d-7** `chainWalk_terminated_contradiction` (the (4.8)/(4.9) arithmetic close: subtraction-
  avoiding additive reshape + `nlinarith` vs `no_rigid_edge_count`) → TACTICS-QUIRKS § 72.
- **E2e** `kt_lemma_46_linking` + `le_bodyBarDim` (`zify` + `nlinarith` on two nonneg slacks) →
  FRICTION *[idiom] `push_neg` deprecated, `omega` extracts the bound directly*.
Below-contract instance drops (unused `[DecidableEq α]`/`[DecidableEq β]`; `_`-named `hG0`/`hD`/`hV2`
in E2d-6/7) preserve signature content — binder naming is cosmetic, §(4.107.G.5) pins content.

### E2c/E2d/E2e design-settle — SETTLED (2026-07-01, docs-only; design §(4.107.G) is the record)
Walk-builder = the Matroid package `WList`/`IsPath` API (extension, prefix, reversal), converted
once at the boundary to the `Fin`-indexed records via `WList.get`/`idxOf_get`/`dInc_getElem`
(hand-rolled `Fin` extension REJECTED). E2c takes explicit `Fin`-cyclic data + non-anchor
closures + anchor degree (the `(G.induce X).CycleData` candidate REJECTED — its `edge_surj` is
what E2c proves). E2d = the length-`n`-capped trichotomy + a per-vertex-per-direction recount of
KT (4.6)–(4.9) (the `cy.m ≥ n+1` fold and the maximal-chain collection DROP; E2b drops out of the
assembly's dependencies). New file `ForestSurgery/ChainExtraction.lean` (Reduction.lean is past
the LoC tripwire). All below §C.0–C.6; E2's public signature unchanged from §(4.107.D).

### E2c deficiency count — LANDED (2026-07-01)
`isKDof_zero_of_cycle` (`Deficiency.lean`, next to `isKDof_zero_of_triangle`/`isKDof_zero_of_parallel_pair`),
the general triangle: an `m`-cycle with `3 ≤ m ≤ bodyBarDim n` is `0`-dof. Explicit-data signature
(cyclic `vtx`/`edge : Fin m → …`, `V = range vtx`, `E = range edge`, `edge` injective, `link`) matching
the triangle's style — `vtx` injectivity is **not** needed (dropped; the count holds without it). Proof:
`def ≤ 0` via `ciSup_le`, each `partitionDef = D(|P|−1) − (D−1)·d(P) ≤ 0` from the cyclic counting bound
`|P| ≤ d(P)` (when `|P| ≥ 2`) + `|P| ≤ m ≤ D`. The bound is an injection parts ↪ crossing edges: each
color class, nonempty and proper on the cyclic `Fin m`, has a *boundary* index (forward-closure ⟹
`col` constant, refuted by `|P| ≥ 2`), whose edge crosses. `Fin m` arithmetic needed
`open Fin.NatCast Fin.CommRing in` (scoped instances) → FRICTION *[idiom] Ring arithmetic on `Fin m`…* /
TACTICS-QUIRKS § 70.

### E2c wrapper — LANDED (2026-07-01)
`cycle_isProperRigidSubgraph` + helper `exists_isLink_not_eq_of_three_le_degree` (`Operations.lean`,
next to `triangle_isProperRigidSubgraph`), built exactly to the §(4.107.G.5) pin — no deviations.
Mirrors the triangle wrapper: `H := G.induce (range vtx)`, `E(H) = range edge` by antisymmetry
(any induced edge's two loopless ends are `vtx i`/`vtx j` with `i ≠ j`; at least one index is
`≠ i₀`, and `hcl` there pins the edge to one of its two cycle edges — `hcl`'s `x`-argument is
unconstrained so no rewriting to `vtx i₀` is needed), `0`-dof via `isKDof_zero_of_cycle`,
`2 ≤ |V(H)|` via `Set.ncard_range_of_injective`. Properness (no `4 ≤ |V(G)|` hypothesis): the
helper's third anchor edge `g` can't land back on `range vtx` — if its far end were a non-anchor
`vtx k`, `hcl` at `k` forces `g` to be one of `vtx k`'s two cycle edges, and `IsLink`
endpoint-uniqueness (`left_unique`/`eq_and_eq_or_eq_and_eq`) then forces `g` to be one of the
*anchor's* two named edges after all — contradiction. Two `Fin m`-arithmetic gotchas (both below
this proof's `haveI : NeZero m`) → TACTICS-QUIRKS § 70 addendum: `abel` on a `k - 1 + 1 = k`-shaped
goal needs `[NeZero m]` locally in scope (silently "no progress" without it, not a missing-instance
error), and the type ascription must wrap the whole arithmetic expression, not just the `⟨1, _⟩`
summand (ascribing only the summand misparses into an unrelated `Graph.deleteVerts` error).

### E2b — LANDED (2026-07-01)
`exists_degree_eq_two_of_noRigid` (`ForestSurgery/Reduction.lean`), at the honest floor
`3 ≤ bodyBarDim n`. Composes two already-landed pieces rather than re-deriving the count: the
general Phase-20 `exists_degree_le_two` (`no_rigid_edge_count`'s `davg < 3` count + the multigraph
handshake, already stated for any `IsMinimalKDof n k`, unifying `k := 0`) supplies `degree v ≤ 2`;
E2a's `two_le_degree_of_isKDof_zero` rules out `≤ 1`. The delta from the existing (older, more
general) `exists_degree_eq_two` is dropping its explicit `htec : TwoEdgeConnected` binder in favor
of deriving it from `hG : IsMinimalKDof n 0` directly (`hG.1`), matching E2's target hypothesis
list (no explicit 2EC premise, per §(4.107.B)). Zero friction: pure composition, first-try build.

### E2a — LANDED (2026-07-01)
Two compositions in `Molecular/Deficiency.lean`, both `IsKDof n 0 → …` at the honest floor
`1 ≤ bodyBarDim n` (§(4.107.E) discipline, not the ambient 3/6-floor): `two_le_degree_of_isKDof_zero`
(min-degree ≥ 2) and `preconnected_of_isKDof_zero` (connectivity companion). Both compose the
already-landed `twoEdgeConnected_of_isKDof_zero` (Phase 22i) with, respectively, the landed
`two_le_degree_of_twoEdgeConnected` and the new general `preconnected_of_twoEdgeConnected` (the
connected-component cut argument — mirrors `mulTilde_preconnected_of_isKDof_zero`'s cut-deficiency
technique for plain `G`, no `Fin (bodyHingeMult n)` edge-copy indexing needed). Zero friction: the
`TwoEdgeConnected`/`ConnBetween`/`cutEdges` infrastructure was already in place from Phase 22i.

### E4 — LANDED (2026-07-01)
The §(4.107.D) `hextract`/`hcycle` binder reshape — a CHAIN-5-style zero-regression lockstep in ONE
commit across the four producer/spine sites (`case_III_hsplit_producer_all_k` + its `k=2` wrapper,
`Arms.lean`; `case_III_realization_all_k`, `Realization.lean`; `theorem_55_minimalKDof_k_all_k`,
`Theorem55.lean`). `hextract`'s conclusion → `(⟨chain ∃⟩) ∨ ∃ cy : G.CycleData, cy.m ≤ n`; new
green-modulo `hcycle` (E5's Lemma-5.4 brick) rides alongside. `case_III_hsplit_producer_all_k`'s
chain arm: `obtain` → `rcases … | ⟨cy, hcym⟩` (right = `hcycle hV4' cy hcym`). `d=3` wrappers fill
`hextract` via `Or.inl ∘ chainData_extract_d3`, `hcycle` vacuously (`cy.vertexSet_ncard` → `omega`).
Blueprint untouched (`lem:case-III` → `case_III_realization` keeps its statement). Zero friction.

### E1 — LANDED (2026-07-01)
`Graph.CycleData` + `CycleData.vertexSet_ncard` (`Operations.lean`, own `/-! ##` section after
`end ChainData`; no decidability instances needed). Fields exactly the §(4.107.D) pinned list;
`vertexSet_ncard` via `Set.ncard_range_of_injective` + `Nat.card_fin` on `range vtx = V(G)`.
- **Below-contract deviation from the literal §(4.107.D) sketch:** the `link` field's cyclic
  successor is `vtx (i + ⟨1, by omega⟩)` (mod-`m` `Fin` add; `hm` in scope for the `by omega`),
  NOT the sketch's `vtx (i + 1)` — the OfNat `(1 : Fin m)` needs `NeZero m`, unavailable in a
  structure-field type. Same root cause as CHAIN-5's `Fin.mk` deviation → FRICTION *[idiom]
  carried-hypothesis field / `∃`-bundle indexing `cd.vtx ⟨2,_⟩`* (recurrence noted there).

### ENTRY satisfiability + OD-1/OD-2/OD-3 — SETTLED (2026-07-01, docs-only design pass)
Design §(4.107) is the full record. One-line verdicts: `d_eq : d = n` source-faithful (Lemma 4.6
chain branch = length exactly `d`); chain-only `hextract` (OD-1 shape 1) refuted at general `n`
(short-cycle counterexamples) → **shape 2 forced, Lemma 5.4 load-bearing** (`hcycle`/E5); KT 4.8(i)
already landed general (`splitOff_isMinimalKDof`), KT 4.6 not subsumed (new leaf E2); `hD` floor
lift dissolves. ENTRY re-scoped to the E1–E5 ladder (checklist above).

### CHAIN-5 — LANDED (`74bd9003`, 2026-07-01)
The C.0 lockstep reshape (`hcand`/`hdispatch` → the C.3 `(cd : G.ChainData n) (hd2 : 2 ≤ cd.d)`
shape across `case_III_hsplit_producer_all_k`/`case_III_hsplit_producer` (`Arms.lean`),
`case_III_realization_all_k` (`Realization.lean`), `theorem_55_minimalKDof_k_all_k` (`Theorem55.lean`))
+ the router wire-up composed in ONE commit. **Stronger than a pure reshape:** the dispatch is
*discharged* (not carried) via `fun cd hd2 hdef hsplitGP => chainData_dispatch cd hd2 hk1 hn hG hV3
hSimple hIH hG.1 hdef hsplitGP` inside `case_III_realization_all_k`, so 23f's router is now LIVE.
Signature deltas (all below §C.0–C.6, no motive/IH change): DROPPED `hdispatch`; ADDED
`hn : bodyBarDim n = screwDim k` (threaded from the spine) + `hextract`. The `d=3` wrappers
(`case_III_realization` / `theorem_55_minimalKDof_k`) fill `hextract` via `chainData_extract_d3`.
- **Below-contract deviation from the literal §C.3 shape:** the field uses `cd.vtx ⟨i, by omega⟩`
  (the router's `Fin.mk` form) + an explicit `hd2` binder, NOT the literal `cd.vtx 1` (OfNat) —
  `(1 : Fin (cd.d+1))` is not defeq to `⟨1,_⟩` at general `cd.d`. → FRICTION *[idiom]
  carried-hypothesis field / `∃`-bundle indexing `cd.vtx ⟨2,_⟩`*.
- **§C.4 `d=3` adapter** `chainData_of_exists_chain_data` (`Reduction.lean`, landed `9b65f960`):
  packages the `d=3` 4-tuple into a `ChainData` (`vtx = ![b,v,a,c]`, `edge = ![e_b,eₐ,e_c]`,
  `d_eq : 3 = n`); `chainData_extract_d3` then transports the `v₁`-split facts across the `a,b`-swap
  (`splitOff_swap_ab`).

## LIVE — DO NOT delete / DO NOT plan to delete
- `caseIIICandidate` + its API — the honest engine consumes it via `case_III_realization_of_rank`
  ← `case_III_arm_realization`.
- The non-aug edge-path helpers `rigidityMatrixEdge_mul_columnOp_*` (WITHOUT `Aug`) in
  `RigidityMatrix/Concrete.lean`.

(Distinct from the retired `_aug` fork, fully deleted across 23f's four deletion commits.)

## OUT-OF-SCOPE `d=3`-era orphans (later sweep / 23g housekeeping)
- `interior_hsplitGP` (`CaseIII/Realization.lean`).
- `case_III_realization_of_line` (`CaseIII/Arms.lean`).
