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

**E2d-6 landed complete 2026-07-02**: `chainWalk_charging` (`ForestSurgery/ChainExtraction.lean`),
the pinned §(4.107.G.5) charging bound `2·|X₂| ≤ (n−2)·Σ_{u : 3≤deg u} deg u`, consuming the fiber
lemma `chainWalk_isPrefix_of_terminated` landed the prior commit. Below-contract proof route (an
injective map into a product set via `Set.ncard_le_ncard_of_injOn`, not the pinned sketch's
`Finset.card_eq_sum_card_fiberwise`) — see *Decisions made*. **Next concrete build step: E2d-7**
(`chainWalk_terminated_contradiction`, the (4.8)/(4.9) arithmetic close), then **E2-assembly**
(`chainData_or_cycleData_of_noRigid`, §(4.107.D) signature verbatim).

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
(the fiber lemma + `chainWalk_charging` proper). Remaining in E2: E2d-7 → E2-assembly; then E3,
E5. ENTRY satisfiability SETTLED (design §(4.107)):
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
    - [ ] **E2d-7** `chainWalk_terminated_contradiction` — the (4.8)/(4.9) arithmetic close
      (`False`)
  - [x] **E2e** the numeric linking identity — `kt_lemma_46_linking`
    (`3 ≤ i → i(n−2) + 2 ≤ (D−1)(i−2)`, KT's display above (4.9)) + `le_bodyBarDim`
    (`n ≤ bodyBarDim n`, the lollipop's `m ≤ n ≤ D` cap), `ChainExtraction.lean` — landed
    2026-07-02
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

**E2d-6 landed complete** (`chainWalk_charging` + its fiber lemma, both in
`ForestSurgery/ChainExtraction.lean`) — the pinned §(4.107.G.5) charging bound. **Smallest
concrete next build commit: E2d-7** (`chainWalk_terminated_contradiction`, the pinned
§(4.107.G.5) signature) — the arithmetic close (`False`): E2d-6's `chainWalk_charging` +
E2e's `kt_lemma_46_linking` summed over `V₊ := {u ∈ V(G) | 3 ≤ deg u}`, plus the loopless
handshake identity (`handshake_degree_subtype`, landed vendored) and the landed
`no_rigid_edge_count` at `k = 0`; `zify` + `nlinarith` per the `exists_degree_le_two` template
(design §(4.107.G.4)'s worked arithmetic chain: `(D−1)·Σ_{V₊}(deg−2) ≥ (n−2)·Σ_{V₊}deg + 2|V₊| ≥
2|V|`, `Σ_{V₊}(deg−2) = 2|E|−2|V|`, hence `(D−1)|E| ≥ D|V|` against `no_rigid_edge_count`). After
E2d-7: **E2-assembly** (`chainData_or_cycleData_of_noRigid`, §(4.107.D) signature verbatim):
`by_contra` → push the negation into E2d-4's `chainWalk_trichotomy` for every incidence to build
`hterm` → E2d-7. Consumes E2a + E2c + E2d-1…7; E2b is not an input (§(4.107.G.7)). After E2:
**E3** (`Graph.chainData_extract`, composition of E2 + the landed Lemma-4.8 stack; discharges
`hextract` at general `n`; home: `ChainExtraction.lean`), then **E5**
(`PanelHingeFramework.cycle_realization`, the Lemma-5.4 brick discharging `hcycle`; own
detailed recon at build, candidate own-letter split).

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

### E2d-6 — LANDED complete (2026-07-02)
`chainWalk_isPrefix_of_terminated` (the fiber lemma) + `chainWalk_charging` (the pinned
§(4.107.G.5) charging bound), both `ForestSurgery/ChainExtraction.lean`.

**The fiber lemma.** Given `P`, `T` sharing a start incidence, both chain-walks (interior
degree 2), with `T` *terminated* (`1 ≤ T.length`, `3 ≤ deg T.last`) and `P` ending at a degree-2
vertex, concludes `P.IsPrefix T ∧ P.length < T.length`. Proof: `chainWalk_isPrefix_or_isPrefix`
(E2d-5) gives the dichotomy; the `T.IsPrefix P` alternative is refuted by casing on
`IsPrefix.length_le.lt_or_eq` — equal length forces `P = T` (`IsPrefix.eq_of_length_ge`) against
the degree mismatch, and `T.length < P.length` places `T.last = P.get T.length`
(`IsPrefix.get_eq_of_length_ge`) at a genuine interior position of `P` (`≠ P.first`/`P.last` via
a local `P.get`-injectivity `have`, the E2d-1/E2d-4 `hget_inj` idiom specialized to one path),
forcing `deg T.last = 2` against `3 ≤ deg T.last`. Zero friction.

**`chainWalk_charging`, exact §(4.107.G.5) signature, below-contract proof route.** The design
sketch's `Finset.card_eq_sum_card_fiberwise` is REJECTED in favor of a single injective map
`Φ : (v, e) ↦ (the reversed terminated walk's landing incidence, its length)` from
`Dom := {(v,e) | v ∈ X₂ ∧ G.Inc e v}` into `Tgt := I ×ˢ Set.Ico 1 (n-1)` (`I` the high-degree
incidence set), via `Set.ncard_le_ncard_of_injOn` — mathematically the same double count, but a
single cardinality-of-injection lemma is more direct in Lean than staging a fiberwise sum. `Φ`
reverses the terminated walk `Tfun v x e h` (from `hterm`) and destructures its `.reverse` via
`Nonempty.exists_cons` to expose the landing incidence `(destU, destE)`, feeding it back through
`hterm` for the "official" terminated walk `S` from that incidence; the fiber lemma places the
reversed walk as a proper prefix of `S`. Injectivity: equal incidences + equal lengths force
`S.take k` equality (`IsPrefix.take_eq`, no `.get`-injectivity needed), hence equal *original*
(pre-reversal) walks via `reverse_reverse`, hence equal `v` (via `hTfirst`) and equal `e` (via a
`Nonempty.firstEdge`-congruence helper). Domain/incidence-set cardinalities (`2·|X₂|`,
`Σ_{V₊} deg`) are both disjoint-union-over-`Finite.ncard_biUnion` computations. The ambient
`hG0`/`hD`/`hV2` hypotheses are pinned by *type* (carried for interface uniformity with the E2d
ladder) but genuinely unused by this route — kept as `_hG0`/`_hD`/`_hV2` (a binder-name cosmetic,
not a hypothesis-content change; §(4.107.G.5)'s preamble pins content, not binder order/naming).
Also dropped the pinned `[DecidableEq α] [DecidableEq β]` instances (genuinely unused, same
below-contract allowance for instance sets).
Four idiom frictions, all promoted → FRICTION *`choose` does not split a `Prop`-witnessed nested
existential*, *a `have`-introduced hypothesis is opaque to `omega`'s atom matching*, *`rw` on a
`Nonempty.firstEdge` argument needs `simp`*, and the `Set.PairwiseDisjoint`/`Function.onFun`
recurrence → **Lifted to: TACTICS-QUIRKS § 71**.

### E2d-5 — LANDED (2026-07-02)
`chainWalk_isPrefix_or_isPrefix` (`ForestSurgery/ChainExtraction.lean`), built exactly per the
pinned §(4.107.G.5) signature — no deviations. `induction P₁ generalizing P₂`; the tails' shared
first edge comes from `isLink_eq_of_degree_eq_two` at the shared second vertex, whose interiority
uses the tail-head's freshness for its own tail (below-contract micro-delta from the sketch's
`IsPath.first_eq_last_iff` route — same fact, one hop shorter). Zero friction: first-try clean
elaboration; the `.first`/`.last`-on-`cons` iota-reductions were pre-empted with defeq re-types
(`have hl₁' : G.IsLink e u a := hl₁`-style), the already-documented `show`-restatement family.

### E2d-4 — LANDED (2026-07-02)
`chainWalk_trichotomy` (`ForestSurgery/ChainExtraction.lean`), built exactly per the pinned
§(4.107.G.3)/(G.5) signature and recursion architecture — no deviations. Strong induction on
`n − P.length` (`Nat.strong_induction_on generalizing P`, the `Reduction.lean` precedent), seeded
from `cons v₀ f (nil x₀)`. `hlinkAt`/`hget_inj` hoisted to theorem scope (reusable across
recursion steps, generalizing E2d-1/2/3's per-lemma copies); a general fact `hgP : g ∉ P.edge`
(the exit edge is never already a path edge) is derived once before the branch split and reused
by all three branches. The lollipop exclusion rebuilds E2c's `hcl` closure via
`isLink_eq_of_degree_eq_two`, using `Fin.sub_val_of_le` (core `.val` order, no `CommRing`) for the
one edge-distinctness fact that needs `i ≠ 0` — the cyclic successor identity itself still goes
through `abel` (TACTICS-QUIRKS § 70). One friction → FRICTION *[idiom] `interval_cases n <;>
omega` on an opaque-`def` floor check needs the numeric identity established first*.

### E2e — LANDED (2026-07-02)
`kt_lemma_46_linking` + `le_bodyBarDim` (`ForestSurgery/ChainExtraction.lean`), built exactly per
the pinned §(4.107.G.5) signatures — no deviations. `kt_lemma_46_linking`: `n ≥ 2` from `hD` via
the `2 · bodyBarDim n = n(n+1)` identity (`Nat.mul_div_cancel'` + `Nat.even_mul_succ_self`, the
`Theorem55.lean` pattern) + a `by_contra`/`interval_cases` floor check; `zify` clears the three
`ℕ`-subtractions, then `nlinarith` closes against two explicit nonneg slack terms — `(n−2)(n−3) ≥
0` (case-split on `n < 3` vs `n ≥ 3`; not a valid *real* inequality on `2 ≤ n`, only an integer
one, so it needs the case split rather than a direct `nlinarith`) and `(i−3)(n²−n+2) ≥ 0` (`n²−n+2
> 0` always, via `sq_nonneg (2n−1)`). `le_bodyBarDim`: the same `2D = n(n+1)` identity plus
`Nat.mul_le_mul_left`, `n = 0` cased separately. One friction: `push_neg` is newly deprecated
(mathlib bump) — swapped the `by_contra`/`push_neg`/`interval_cases` idiom for a direct `omega`
bound extraction. → FRICTION *[idiom] `push_neg` deprecated, `omega` extracts the bound directly*.

### E2d-3 — LANDED (2026-07-02)
`exists_cyclic_data_of_closed_path` + `cycleData_of_closed_path`
(`ForestSurgery/ChainExtraction.lean`), built exactly per the pinned §(4.107.G.5) signatures — no
deviations. `vtx i := P.get i` (already total); `edge i := P.edge.getD i f` — `List.getD`'s
totality is a below-contract simplification of the design sketch's `dite` description, avoiding a
dependent if-then-else proof term. The consumer composes the core's two range equalities with
E2d-2's confinement to discharge `CycleData`'s `vtx_surj`/`edge_surj`. Two idiom frictions →
FRICTION *[idiom] `List.getD_eq_getElem`/`getD_eq_default` need an explicit import + explicit
args* + the already-documented § 63 `Fin.mk`/`omega` atomization family.

### E2d-2 — LANDED (2026-07-01)
`closed_path_degree_two_spanning` (`ForestSurgery/ChainExtraction.lean`), built exactly per the
pinned §(4.107.G.5) signature — no deviations. Proof: one **confinement closure**
`hclosure : ∀ x ∈ P, ∀ e y, G.IsLink e x y → y ∈ P ∧ e ∈ insert f {e|e∈P.edge}`, cased on `P.idxOf
x` (`0` / interior / `P.length`) to name the vertex's two known edges (flanking path edges, or
`f` at an endpoint — `P.length ≠ 0` first, from `hf.ne` ruling out `P.first = P.last`) via
E2d-1's closure helper; `V(G) ⊆ P` walks `hconn`'s witness stepping `hclosure` along it
(`IsWalk.cons`-induction), `E(G) ⊆ insert f {..}` pulls each edge's endpoint back via that
inclusion. Zero friction — the one live gotcha (§48's `-`-then-`+` parse trap, twice, both
`i - 1 + 1 = i`) was avoided proactively via the already-promoted `Nat.sub_add_cancel` idiom.

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
