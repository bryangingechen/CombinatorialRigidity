# Phase 23g — Case III general `d`: ENTRY (chain extraction) + CHAIN-5 (dispatch reshape) (work log)

**Status:** in progress (opened 2026-07-01). The `ENTRY` sub-phase of the Case III
general-`d` program. **CHAIN-5 landed 2026-07-01** (`74bd9003`) — the 23f router
`chainData_dispatch` now *discharges* the Case-III chain dispatch at general `k`; the single
remaining Case-III green-modulo hypothesis is the **ENTRY extractor** `hextract` (design §C.2),
discharged at `n=3` today. `d=3` stays fully green throughout. Authoritative scoping:
`notes/Phase23-design.md` §C.0–C.6 (frozen CHAIN↔ENTRY contract) + **§(4.107)** (the ENTRY
satisfiability verdict + the E1–E5 leaf ladder; supersedes §C.2's chain-only reading) +
**§(4.107.G)** (the E2c/E2d/E2e settle: pinned signatures + the E2 internal build order); the
`d=3` map is §C.4. Program map: `notes/MolecularConjecture.md`. `ASSEMBLY` = **23h** (later
sub-phase).

## Current state

**E2d-1 landed 2026-07-01**: the path→`ChainData` bridge `chainData_of_isPath` + the closure
helper `isLink_eq_of_degree_eq_two`, exact signatures per design §(4.107.G.5), opening the new
`ForestSurgery/ChainExtraction.lean` (wired into the root import list). E2a/E2b/E2c/E2d-1 are now
landed. Next concrete build step: **E2d-2** — `closed_path_degree_two_spanning` (the cycle-branch
confinement component argument), same file. **E2c landed 2026-07-01** (both halves): the
deficiency count `isKDof_zero_of_cycle`
(`Deficiency.lean`) and the wrapper `cycle_isProperRigidSubgraph` + its helper
`exists_isLink_not_eq_of_three_le_degree` (`Operations.lean`), exact signature per design
§(4.107.G.5) — explicit `Fin`-cyclic data + non-anchor degree-2 closures + `3 ≤ degree` at the
anchor; properness internal via the anchor's third edge, no `4 ≤ |V|` hypothesis. E2 (KT Lemma
4.6) is now assessed to split along E2a–E2e (§(4.107.D)); **E2a/E2b/E2c/E2d-1 are landed, the
rest of E2d/E2e remain**. **E2c/E2d/E2e design-settle DONE 2026-07-01**
(§(4.107.G)): walk-builder = package `WList`/`IsPath` with one-shot `Fin`-record conversion;
E2d decomposed into sub-commits E2d-1…E2d-7 with exact signatures, new file
`ForestSurgery/ChainExtraction.lean`; E2e pinned (`kt_lemma_46_linking` + `le_bodyBarDim`). See
the *Lemma checklist* for the full ladder. **E2b landed
2026-07-01**: degree-2 existence
(`exists_degree_eq_two_of_noRigid`, `ForestSurgery/Reduction.lean`) — composes the already-general
Phase-20 `exists_degree_le_two` (the `no_rigid_edge_count` + handshake counting core, floor
`3 ≤ bodyBarDim n`) with E2a's `two_le_degree_of_isKDof_zero` to pin the vertex's degree to
exactly `2`, without an explicit `TwoEdgeConnected` premise (matching E2's hypothesis list).
**E2a landed 2026-07-01**: min-degree ≥ 2 (`two_le_degree_of_isKDof_zero`) and the
connectivity companion (`preconnected_of_isKDof_zero`), both compositions of the already-landed
`twoEdgeConnected_of_isKDof_zero`/`two_le_degree_of_twoEdgeConnected` (Phase 22i) plus the new
general `preconnected_of_twoEdgeConnected` (`Molecular/Deficiency.lean`). E2 (KT Lemma 4.6, the
chain/cycle dichotomy leaf, the long pole) is now assessed to **split along its scoped sub-leaves
E2a–E2e (§(4.107.D)), one sub-leaf per commit** — see the *Lemma checklist*. **E4 landed
2026-07-01**: the `hextract`/`hcycle` binder reshape at the four
producer/spine sites (`Arms.lean` ×2 / `Realization.lean` / `Theorem55.lean`) is a zero-regression
lockstep — `hextract`'s conclusion is now the §(4.107.D) shape-2 disjunction
(`… ∨ ∃ cy : G.CycleData, cy.m ≤ n`) and the new green-modulo `hcycle` (E5's Lemma-5.4 brick) rides
alongside; the `d = 3` wrappers fill `hextract` via `Or.inl ∘ chainData_extract_d3` and `hcycle`
vacuously (`cy.vertexSet_ncard` + `cy.m ≤ 3 < 4 ≤ |V|` → `omega`). **E1 landed 2026-07-01**:
`Graph.CycleData` + `CycleData.vertexSet_ncard` (`Operations.lean`). ENTRY satisfiability SETTLED
(design §(4.107)): the `d = n` chain shape is source-faithful, but the chain-only `hextract` is
unsatisfiable at general `n` — **OD-1 settled = shape 2** (Lemma 5.4 load-bearing). ENTRY is the
pinned leaf ladder **E1 → E4 → E2 → E3 → E5** (exact signatures in §(4.107.D)); the two interface
leaves (E1, E4) are now landed, pinning the shape-2 disjunction in Lean before the long-pole
combinatorics. CHAIN-5 is done (dispatch discharged at general `k`); `hextract`/`hcycle` are
discharged at `n=3`; everything below the contract is landed (the `ChainData` record with
`d_eq : d = n` + `d_eq_kAdd`, the geometry arm, the `chainData_dispatch` router, the C.4 adapter).

## Lemma checklist (the §(4.107.D) ENTRY ladder)

- [x] **E1** `Graph.CycleData` record + `CycleData.vertexSet_ncard` (`Operations.lean`) — landed
  2026-07-01
- [x] **E4** the `hextract` binder reshape to the shape-2 disjunction + the new green-modulo
  `hcycle` at the four producer/spine sites (`Arms.lean` ×2 / `Realization.lean` / `Theorem55.lean`);
  `d=3` wrappers: `Or.inl ∘ chainData_extract_d3` + vacuous `hcycle` (`omega`) — landed 2026-07-01,
  zero-regression
- [ ] **E2** `Graph.chainData_or_cycleData_of_noRigid` — KT Lemma 4.6, the genuinely-new
  combinatorial leaf (the long pole); **SPLITS along its §(4.107.D) sub-leaves, one commit each**:
  - [x] **E2a** min-degree ≥ 2 + connectivity companion — `two_le_degree_of_isKDof_zero` /
    `preconnected_of_isKDof_zero` (`Molecular/Deficiency.lean`) — landed 2026-07-01
  - [x] **E2b** degree-2 existence — `exists_degree_eq_two_of_noRigid`
    (`ForestSurgery/Reduction.lean`) — landed 2026-07-01
  - [x] **E2c** — deficiency count `isKDof_zero_of_cycle` (`Deficiency.lean`) + the wrapper
    `cycle_isProperRigidSubgraph` + helper `exists_isLink_not_eq_of_three_le_degree`
    (`Operations.lean`, the general `triangle_isProperRigidSubgraph`) — landed 2026-07-01
  - [ ] **E2d** the maximal-chain walk-builder + KT (4.6)–(4.9) counting contradiction —
    **decomposed 2026-07-01 into sub-commits, exact signatures in §(4.107.G.5), all in the NEW
    `ForestSurgery/ChainExtraction.lean`** (build order E2d-1 → E2d-2 → E2d-3 → E2e → E2d-4 →
    E2d-5 → E2d-6 → E2d-7):
    - [x] **E2d-1** `chainData_of_isPath` (length-`n` interior-deg-2 path → `ChainData`) +
      `isLink_eq_of_degree_eq_two` helper — opens `ChainExtraction.lean` — landed 2026-07-01
    - [ ] **E2d-2** `closed_path_degree_two_spanning` (all-deg-2 closed path + connected ⟹
      `V(G)`/`E(G)` confinement)
    - [ ] **E2d-3** `exists_cyclic_data_of_closed_path` (the shared `Fin`-cyclic packaging core)
      + `cycleData_of_closed_path`
    - [ ] **E2d-4** `chainWalk_trichotomy` — the length-`n`-capped extension: chain-disjunct at
      the cap, cycle-disjunct at deg-2 closure, lollipop absurd via E2c + `hnp`, else a
      terminated walk of length `≤ n−1` (the dense commit)
    - [ ] **E2d-5** `chainWalk_isPrefix_or_isPrefix` — chain-walk determinism
    - [ ] **E2d-6** `chainWalk_charging` — `2·|X₂| ≤ (n−2)·Σ_{deg≥3} deg` (the KT (4.6)+(4.7)
      double count, per-vertex-per-direction; candidate own-split at contact, §(4.107.G.5))
    - [ ] **E2d-7** `chainWalk_terminated_contradiction` — the (4.8)/(4.9) arithmetic close
      (`False`)
  - [ ] **E2e** the numeric linking identity — **pinned**: `kt_lemma_46_linking`
    (`3 ≤ i → i(n−2) + 2 ≤ (D−1)(i−2)`, KT's display above (4.9)) + `le_bodyBarDim`
    (`n ≤ bodyBarDim n`, the lollipop's `m ≤ n ≤ D` cap), `ChainExtraction.lean`; lands
    between E2d-3 and E2d-4
  - [ ] **E2-assembly** compose the ladder into `chainData_or_cycleData_of_noRigid` (§(4.107.D)
    signature verbatim): `by_contra` → every incidence terminates (`hterm`) → E2d-7. Consumes
    E2a + E2c + E2d-1…7; **E2b is not an input** (§(4.107.G.7) — it stays landed,
    KT-expositional)
- [ ] **E3** `Graph.chainData_extract` — compose E2 + the landed Lemma-4.8 stack; discharges
  `hextract` at general `n`
- [ ] **E5** `PanelHingeFramework.cycle_realization` — the Lemma 5.4 brick discharging `hcycle`
  (risk #4, genuine new panel content: Crapo–Whiteley realization + the GAP-2-style genericity
  upgrade). Own detailed recon at build; candidate own-letter split at contact.

## Hand-off / next phase

**E2d-1 landed** (`chainData_of_isPath` + `isLink_eq_of_degree_eq_two`, the new
`ForestSurgery/ChainExtraction.lean`, wired into the root import list), built exactly per the
pinned §(4.107.G.5) signatures — no deviations. E2a/E2b/E2c/E2d-1 are now all landed.
**Smallest concrete next build commit: E2d-2** — `closed_path_degree_two_spanning` (the
cycle-branch confinement: an all-deg-2 closed path + connected graph ⟹ `V(G)`/`E(G)`
confinement to the walk), same file, exact signature in design §(4.107.G.5). After E2d-2, the
remaining ladder of §(4.107.G.5), one commit each: **E2d-3** (cyclic packaging) → **E2e**
(`kt_lemma_46_linking` + `le_bodyBarDim`) → **E2d-4** (`chainWalk_trichotomy`, the capped
builder — dense) → **E2d-5** (determinism) → **E2d-6** (charging — dense, candidate split) →
**E2d-7** (arithmetic close) → **E2-assembly** (`chainData_or_cycleData_of_noRigid`,
§(4.107.D) signature verbatim). After E2: **E3** (`Graph.chainData_extract`, composition of E2
+ the landed Lemma-4.8 stack; discharges `hextract` at general `n`; home:
`ChainExtraction.lean`), then **E5** (`PanelHingeFramework.cycle_realization`, the Lemma-5.4
brick discharging `hcycle`; own detailed recon at build, candidate own-letter split).

The E4 interface is now in place: `hextract` returns the shape-2 disjunction and `hcycle` is carried
green-modulo, so E2/E3 land the chain-extractor discharge and E5 lands the cycle brick without
further binder churn.

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

### E2d-1 — LANDED (2026-07-01)
`isLink_eq_of_degree_eq_two` (the closure helper: a degree-2 vertex's two named incident edges
are its *only* two, via `degree_eq_ncard_inc` + `Set.eq_of_subset_of_ncard_le`) and
`chainData_of_isPath` (length-`n` interior-deg-2 path → `ChainData`, via the boundary `WList →
Fin` conversion: `vtx := P.get`, `edge := P.edge[·]`, `vtx_inj`/`edge_inj` from `WList.idxOf_get`
/ `List.Nodup.getElem_inj_iff`, `link` from `WList.DInc_get_get_succ` +
`IsWalk.isLink_of_dInc`, `deg_two` from `hdeg` + the closure helper applied to the two flanking
path edges), both built exactly per the pinned §(4.107.G.5) signatures in the new
`ForestSurgery/ChainExtraction.lean`. Zero content deviation; one build-time gotcha promoted
(next entry).

**Friction: `x - a + b` parses "overloaded, errors" / cascades to `unexpected token ':='` inside
`namespace Graph`** — the vendored `scoped notation:51 G:100 " - " S:100 => Graph.deleteVerts G
S` poisons *any* operator after `-` needing a ≥100-precedence left operand, not just a second
`-` (the already-documented § 48 case); merely having a `WList`/`Graph`-typed variable in local
context is enough to activate it. Hit building `chainData_of_isPath`'s `have heq1 : i - 1 + 1 =
i := by omega`; fixed by replacing the raw arithmetic with `Nat.sub_add_cancel (show 1 ≤ i by
omega)` (a lemma application whose type is built by substitution, not re-parsed source text).
**Lifted to:** TACTICS-QUIRKS § 48 (broadened in place, not a new entry — same root cause as the
existing Phase 22i occurrence).

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
