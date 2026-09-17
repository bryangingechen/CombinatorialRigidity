# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`** — since 2026-09-16 a **three**-conjunct motive (bare; under `G.Simple` an
adjacent-distinct one; under simplicity plus feasibility a generic one). The landed theorem
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) derives
it from exactly **three carried hypotheses**: **`hcontract`** (W4; Lean build decomposed and
parked by the **2026-08-05 Lean hold**; informal argument closed, plus one new (α) obligation),
**`hK`** (kernel (K)) and **`hbareSplit`** (kernel (K-bare)). W0–W3, W5 (L0–L7), `hsplit` and
`hfresh` are Lean-closed.

**Two tracks since 2026-09-15.** *(1)* **Attack track** — research on the two open kernels,
one agent per lemma under `/attack <name>` (`HARNESS.md`); each lemma's status surface is
`notes/attacks/<name>/state.md`. Briefs for **S-mark** (`hbareSplit`, and the split step of
`hK`) and **(GR-10)** (uniform colouring, the crux of `hK` on the tight stratum) are at
`notes/attacks/{smark,gr10}/brief.md` (PI-reviewed 2026-09-15). **S-mark: five sessions and
two reviews (2026-09-15/16).** Review 2 retired route R1 — its obligations were never consumed
— and endorsed **route R2**: the kernels' own antecedent, read at the generic point, supplies
every block inequality the consumed step needs (workbook S14); and **`hK`/`hbareSplit` as
pinned are not locally provable** — their truth on the gap cells is the conjecture for the side
`G − chain` (the `a′` gap, S14(v)). **PI decision 2026-09-16: both kernels get the induction
hypothesis on smaller graphs.** *(2)* **Lean track** — this note and `/coordinate-phase 39`:
formalize the reductions and foundations the attacks stand on, cruxes carried as
hypotheses, no `sorry`. Items 1–3 DONE 2026-09-15 (`sec:pencil-girth-chain` fully green; field
hypothesis option C). **Items 4–5 DONE 2026-09-16.** The R2 recon settled the rank bridge,
side feasibility and `hK`'s conclusion; its open finding (the bare motive attains at
*coincident* points) the user settled **(α)**. **Item 5 landed in one slice:** both kernels
take the induction hypothesis (S14(v)), `hK` concludes `HasGenericPencilRealization K 3 G`,
and `hbareSplit` takes and returns the new motive `HasDistinctPencilRealization`. **For the kernels' current form read `notes/Phase39-design.md`
§ *Kernel restatement (2026-09-16)*, not the older pinned blocks.** **Next: the S-mark brief
rewrite** against the landed statements, then `/attack smark` session 6; **(GR-10) is
RE-SCOPED** (user, 2026-09-16): the char-2 probe runs; the grid/colouring route is a documented
fallback, not the path to `hK`. **Item 6 (deficiency laws) is UNPARKED** (user, 2026-09-16):
carrier recon DONE, **D1–D5 all SETTLED** (user, same day; *Blockers*), and Layer-A leaves
**A1/A2 LAND** (pendant law + combinatorial carriers, sorry-free) — a Layer A/B/C leaf list
with sites (*Lemma checklist*), no blueprint chapter, so the *Layer plan* is the to-do list.
Items 7–12 stay parked.

**The retired research arc** (2026-08-05 → 09-13: 127 directions, nineteen strategy passes,
under a coordinator loop retired 2026-09-15 — `notes/harness/incidents.md`). Its final
work-log state is **verbatim** at `notes/pencil/arc-worklog.md`; per-direction specs and
verdicts `notes/pencil/fanout.md`; the *State of (K)* gap map `notes/pencil/workbook/gapmap.md`
(read with `python3 notes/gapmap.py`, never `sed`/`grep`); claims via `python3 notes/ledger.py`.
**Standing result at retirement: `hK` is not closer** — (GR-15)/(GR-10) OPEN since 2026-08-07,
(BE-14) one lemma (S-mark) away since 2026-08-26; **no content commit under
`Molecule/Pencil/` since 2026-08-05.**

## Current state

**Item-6 leaves A1 and A2 LAND 2026-09-16** — `deficiency_removeVertex_of_degree_eq_one`
(`Induction/SplitOffDeficiency.lean`, beside `removeVertex_deficiency_ge`) and the
combinatorial carriers `deficiencyMerged`/`deficiencySep`/`weldPair`/`pairDelta` plus
`partitionDef_map` and the D4-settling bridge `deficiency_weldPair_eq_deficiencyMerged`
(`Deficiency.lean`), all transcribed sorry-free from `notes/Phase39-design.md` § *Item-6
carrier recon (2026-09-16)* with no new decisions. **Next concrete step: item-6 leaf A4** (the
substantive combinatorial leaf, D3's `max` form) **or Layer B1→B5** (the geometric carriers,
independent of A). In parallel, the **S-mark brief rewrite** against the *landed* kernel
statements (*Hand-off* item 2), then
`/attack smark` session 6; (GR-10)'s scope is settled (user, 2026-09-16 — *Blockers*):
re-scoped to the char-2 probe, the grid route kept as a documented fallback. Checklist items 4
and 5 are DONE 2026-09-16 and **item 6's carrier recon is DONE** 2026-09-16 (its build leaves
are open; A4 and B5 are the two substantive ones). S-mark has five sessions (2026-09-15/16) and two reviews. Review 1
(2026-09-15) re-aimed the attack at the consumed shape (the `hbareSplit` disjunct the brief had
dropped; workbook S10). Sessions 3–4 then attacked profile bounds on an arbitrary side
((O4′)/(O4″)) that turned out not to be consumed; session 5 re-read the consumer and found the
brief's second misreading — the kernels' antecedent `HasPencilRealization K 3 (G.splitOff …)`
is `H′ ∪ ear_{m−1}` attaining (`splitOff` deletes the degree-2 vertex and re-adds the edge),
not a discardable "realization of `G − x`" — and route R2 (workbook S14). Review 2
(2026-09-16, notes at workbook S15) verified the consumer reading against `Escape.lean` and
the S14 arithmetic, endorsed R2, and recorded three statement-level questions for the Lean
track — **answered by the item-4 recon 2026-09-16** (checklist item 4; record
`notes/Phase39-design.md` § *R2 recon*). `notes/attacks/smark/state.md` is the status surface; session 6 waits for the brief rewrite,
which must quote the **landed** kernels (`notes/Phase39-design.md` § *Kernel restatement
(2026-09-16)*), not the pinned blocks the brief was written against. (GR-10) has not started and
is now **re-scoped** (user, 2026-09-16): the recon confirms R2 covers `hK`'s arm at the statement level (S14(iii), (vii);
under the recon's (d) the chart form, hence proviso (P), drops out of `hK`'s statement), so the
grid/colouring route of `notes/attacks/gr10/brief.md` is **no longer the path to `hK`** — it is a
documented fallback if S14(iii)/(vii) or O7 stall, and session 1 does **not** run as briefed.
What runs is **the char-2 probe** (PI 2026-09-15, deferred to the attack track; spec in
`notes/Phase39-design.md` § *Field-hypothesis recon*, last subsection): the census shapes' chart matrix over `F_{2^k}` and a few odd `F_p` — a
full-rank hit is a proof of `hK` at that shape in that characteristic; systematic `F_{2^k}`
misses would be evidence the target itself fails in characteristic 2 and a re-pin trigger for
the headline typeclass. The attack decides when to run it.
**Lean track — checklist items 1–5 are DONE (items 1–3 2026-09-15, items 4–5 2026-09-16);
item 6 is UNPARKED (user, 2026-09-16), its recon is DONE, and its Layer-A leaves A1/A2 LAND
the same day.**
The design pass (`notes/Phase39-design.md` § *Lean-track design pass*) pinned items 1–2
as eight red nodes in `blueprint/src/chapter/pencil.tex` § *Girth and degree-two chains* (the
chapter's first section), and **all eight are now green**: G1–G4 in the new
`Molecular/Induction/Girth.lean` and in `Molecule/Pencil/Motive.lean` (`Graph.GirthGE` with
`.mono`/`.anti`, `range_vtx_eq_vertexSet_of_cycle_of_noRigid`,
`girthGE_of_noRigid_of_three_le_degree`, `ncard_closedNbhd_inter_le_two_of_girthGE`), then
M3a/M3b, M1, M2 and M4/M4′ in the new `Molecular/Induction/ForestSurgery/MaximalChain.lean`
(`connected_deleteVerts_interior_of_twoEdgeConnected`, `degree_deleteVerts_interior_add_one`,
`exists_cycleData_or_closed_or_terminated_of_twoEdgeConnected`,
`cycleData_or_hubLollipop_or_hubChain_of_degree_two_pair`,
`le_length_add_length_of_isPath_deleteVerts_interior_of_noRigid`,
`le_length_add_eDist_deleteVerts_interior_of_noRigid`). Item 3 is **SETTLED** (PI, option C):
the reduction stays `[Infinite K]`; the hypothesis lives on the kernel lemmas
(`notes/Phase39-design.md` § *Field-hypothesis recon*; chapter
`fmlnote:pencil-conditional-realization-pair-field`). **Items 6–12 stay parked by the hold**,
and no Lean work is queued — the next task is the brief rewrite (*Hand-off*). Builds need
`LAKE_CACHE_DIR` set (`notes/ToolchainBumps.md` *Environment*; session-wide via the gitignored
`.claude/settings.local.json`).

**Lean, landed:** the statement layer and stratum self-duality (W0), the KT Lemma 5.3/5.4
base cases (W1), the two-pencil layer (W2), W3, the whole of W5 (L0–L7, 2026-07-24 → 07-30),
`hsplit` in full and `hfresh`'s mechanical discharge (W5-L7c). **Lean, parked:** the W4 build
(route 3, packaging (b), adjudicated 2026-08-02; fully decomposed, gates N8/N9/N10/N10b
passed; canonical homes `notes/Phase39-design.md` §§ *W4 decomposition recon* / *W4-L4
identification recon* and `notes/pencil/workbook/W4.md`).

**Eight foundations findings from the briefs, the two reviews and the item-4 recon** (the
writers' readings, to be checked by the PI; this paragraph is a summary — the owning text is the brief or workbook
section named). **Frame gap — closed under R2** (review 2, 2026-09-16): the Lean's own induction composes only across the hub cut of a degree-2 chain, where the split-off antecedent supplies welded attainment (workbook S14(i)); no 3-block skeleton is consumed.
**Girth-5 restriction:** at girth ≥ 5 the coplanarity closure never fires, so the
coincident-flag arm the last six rounds worked is deleted by inducting inside girth-5 graphs
(`smark/brief.md` §6 idea 1, §7; adopted in session 1). Girth is `≥ 7` in the consumer's class
*unless `G` is itself a 5- or 6-cycle* — a spanning short cycle is not a *proper* rigid
subgraph. **Consumed-shape disjunct** (review 2026-09-15): `hbareSplit` carries
`¬ PencilHub a ∨ ¬ PencilHub b` — the blueprint's *"one of whose two neighbours is not a
pencil hub"* — which the S-mark brief dropped; the consumed instance is a hub-terminal side
against a degree-2 chain of length `≥ 2`, never a single degree-2 vertex between two hubs, and
the chain length stratifies the obligation: `≥ 4` closes from the attack's S3 + S8, `2` is the
core (`smark/brief.md` §3 *Consumed shape*; workbook S10, reviewer's arithmetic).
**Consumed-shape antecedent** (session 5 / review 2, 2026-09-16): the brief also misread the
kernels' antecedent as discardable; it is the split-off graph `H′ ∪ ear_{m−1}` attaining — the
certificate R2 reads at the generic point (S14; verified against `Escape.lean` at review 2,
S15; incident logged 2026-09-16). **Independence proviso:** the chain from (GR-15) to `hK` needs each hub's
closed-hub-neighbourhood points independent, which the 40 742- and 166 088-shape sweeps did
not certify (`notes/attacks/gr10/brief.md` §2 *Proviso (P)*, §3). **Field mismatch** —
*resolved 2026-09-15*: neither route needs characteristic 0 (the grid needs `char ≠ 2`; S-mark
needs algebraic closure only as stated); option C, checklist item 3. The briefs are committed
(PI-reviewed 2026-09-15; amended the same day for the formalization's corrections, edits marked
*[formalization 2026-09-15]*; workbook S11). **Rank bridge — CHECKED** (item-4 recon, 2026-09-16):
the attack's `dim M(G) = 6 + def₃(G)` is the Lean's `HasPencilRealization` rank equation wherever
adjacent points are distinct (five rows per hinge, `screwDim 2 = 6`, `deficiency 3 = def₃`;
compiled). **Bare-motive slack** (item-4 recon): the bare motive attains at coincident adjacent
points where no distinct configuration does (the parallel pair; compiled cap `≤ 5`), so a Lean
bare witness is not automatically a point of the attack's `Y(G)` — **settled (α)** 2026-09-16
by a third `PencilPair` conjunct, so `hbareSplit`'s antecedent is a `Y(G₋)`-point by
construction and O8's coincident stratum is deleted.

**Standing user adjudications that bind:** 2026-07-24 the phase stays open; 2026-08-05 the
Lean hold, and *"all of the scripts we run [are] committed"*; 2026-09-03 *"we should
ultimately be driven by the math … we shouldn't lock [declined directions] out forever"* and
*"if the current approach seems to be getting in a rut then it's time to reprioritize"*;
2026-09-15 the coordinator loop retired in favour of attack tracks. Verbatim record:
`notes/pencil/adjudications.md`.

## Lemma checklist — the Lean track

*Items 1–3 unparked 2026-09-15 (PI); items 4–10 stay parked by the hold. Ranked cheapest and
most decision-relevant first; each carries its crux as a HYPOTHESIS, never a `sorry`.*

- [x] **Girth lemmas** — **DONE 2026-09-15** (design pass same day, `notes/Phase39-design.md`
  § *Lean-track design pass*, leaves G1–G4; red nodes `def:girth`,
  `lem:pencil-short-cycle-spanning`, `lem:pencil-girth-of-hub`,
  `lem:pencil-closed-nbhd-girth-five` — all four now green). Carrier: `Fin m` cycle data and the
  predicate `Graph.GirthGE` (V1). Sharpened against the review: *any* vertex of degree `≥ 3`
  forces girth `≥ 7`, and no hub + 2EC makes `G` a cycle of any length `≥ 5` (V5);
  `|N[v] ∩ N[h]| ≤ 2` needs only girth `≥ 5` and `v ≠ h` (V6, needs neither `G.Simple` nor
  hubness). Landed in `Molecular/Induction/Girth.lean` (G1–G3) and `Molecule/Pencil/Motive.lean`
  (G4, `Graph.ncard_closedNbhd_inter_le_two_of_girthGE`) — G4's route streamlines the design
  note's shared pigeonhole into two direct `Set.ncard`-cardinality extractions (adjacent case:
  `Set.exists_mem_notMem_of_ncard_lt_ncard`; non-adjacent case: `v, h` provably absent from the
  intersection, so `Set.two_lt_ncard_iff`'s witnesses qualify directly).
- [x] **Consumed-shape normal form** — **DONE 2026-09-15** (design pass same §, leaves M1–M4′;
  red nodes `lem:pencil-chain-walk-extension`, `lem:pencil-degree-two-chain`,
  `lem:pencil-chain-side-connected`, `lem:pencil-chain-side-distance` — all four green, so
  `sec:pencil-girth-chain` is fully green). Carrier: `WList` paths in ∃-statements, no new
  record (V2); the builder is E2d-4 un-capped and 2EC-sourced. Two design-pass corrections to
  the review's shape are now formal: the normal form is a *trichotomy*, since the chain can
  close at a **single hub** (a cycle through a cut vertex — V3, *Blockers*), and `w ≁ v` holds
  only for `m ≤ 4`, the general clause being `dist_{G−chain}(w, v) ≥ 6 − m` (V4). All six
  declarations live in `Molecular/Induction/ForestSurgery/MaximalChain.lean`, whose module
  docstring is the index; the reusable core is the private `isLink_interior_iff_eq` (an interior
  vertex's `G`-neighbours are exactly its two path-flanking vertices). M4's `hdeg` is unused —
  the deleted set is defined syntactically from `P` — and is kept only because the blueprint
  node states it.
- [x] **The field hypothesis** — **SETTLED 2026-09-15 (PI, option C)**: the reduction stays
  `[Infinite K]` (its proof uses no characteristic); kernel (K) via the grid expects
  `[Infinite K] [NeZero (2 : K)]` (`char ≠ 2` — the quadric and the polarity's eigen-splitting
  collapse in characteristic 2); kernel (K-bare) via the 2-cut composition expects
  `[Infinite K]` in witness form, interim `IsAlgClosed K`; the corollary inherits the kernels'
  hypotheses. Record: `notes/Phase39-design.md` § *Field-hypothesis recon (2026-09-15)*;
  chapter `fmlnote:pencil-conditional-realization-pair-field`. The char-2 probe is the (GR-10)
  attack's (*Current state*).
- [x] **R2 recon (item 4) — DONE 2026-09-16** (read-only; record `notes/Phase39-design.md`
  § *R2 recon*, with the three compiled spike statements). One-line verdicts: **(a)** the rank
  bridge is exact on the adjacent-distinct locus — five rows per hinge (`hingeRowBlock`),
  `screwDim 2 = 6`, `deficiency 3 = def₃`, the hinge forced onto `p_u ∧ p_v` (compiled); the only
  divergence is (b)'s locus. **(b)** the bare motive attains at coincident adjacent points where no
  distinct configuration does (the parallel pair: landed witness at rank 6, compiled cap `≤ 5` at
  distinct points), so `hbareSplit`'s antecedent as pinned is a bare-space point, not a
  `Y(G₋)`-point; the named fix (a conjunct on `HasPencilPanelRealization`) is REFUTED — it
  falsifies `PencilPair` at every parallel class and would break the pinned `lem:pencil-self-dual`;
  the viable form is a simple-conditioned third `PencilPair` conjunct whose cost lands on
  `hcontract` — **(α)/(β) is the PI's call** (*Blockers*). **(c)** `G.Simple` and
  `PencilNondegFeasible` pass to every subgraph of a triangle-free simple feasible `G`, hence to
  `G − chain`, by reconstruction from `Steer.lean:1344` (compiled), not by restriction
  (`PencilNondegFeasible.mono` is gapped exactly at the chain ends' degree-2 demotion); on `hK`'s
  arm the IH's generic half is usable for the side. **(d)** CONFIRMED — `hEsc` is consumed once
  (`Escape.lean:420–422`); `hK` may conclude `HasGenericPencilRealization K 3 G` (the blueprint
  already states it so, `pencil.tex:843–845`).
- [x] **Kernel restatement (item 5) — DONE 2026-09-16**, one slice, all four pieces (user:
  *"One slice: IH + (d) + (c)-adder + whatever (b) decides"*). Both kernels take the induction
  hypothesis ahead of their antecedent (S14(v)); `hK` concludes `HasGenericPencilRealization K
  3 G` ((d)); `pencilNondegFeasible_of_le_of_triangleFree` landed in `Steer.lean` ((c) — the
  W5-L6b criterion it ends on lives there, and `Motive.lean` is upstream of it); and (α) added
  the motive `HasDistinctPencilRealization` (`Statement.lean`) as `PencilPair`'s
  simple-conditioned third conjunct, with `hbareSplit` taking and returning it. The cut arm was
  the one real cost — no distinct-level assembly existed — resolved by a `Prop` flag on one
  shared core (`hasPencilRealization_of_not_twoEdgeConnected_core`) instead of duplicating
  ~300 lines. Record, with the arm table as it actually discharged: `notes/Phase39-design.md`
  § *Kernel restatement (2026-09-16)*; blueprint `def:pencil-distinct-motive`,
  `def:pencil-conditioned-pair`, `lem:pencil-cut-nondegeneracy`, `lem:pencil-cut-case`,
  `thm:pencil-conditional-realization-pair`; W4's new obligation
  `notes/pencil/workbook/W4.md`.
- [ ] **Deficiency laws** (BINDUC's, cited by 45 claims through (BE-22)) — **UNPARKED
  2026-09-16 (user); the carrier recon is DONE the same day** (read-only; full record
  `notes/Phase39-design.md` § *Item-6 carrier recon (2026-09-16)*, which carries every
  signature, the two sorry-free proofs, the numerics and the sites). Read that arc before
  scoping a slice; the sub-items below are the buildable leaves, in dependency order.
  **Three findings reshape the item.** (i) **6a is proved**, not merely buildable — it is
  `deficiency_eq_of_cutEdges_ncard_le_one` (`Deficiency.lean:1767`) at `V₁ = {u}`, and the
  sorry-free proof is banked in the design arc. (ii) **6b is false as first stated**: with the
  sides taken as `G.induce V₁`, `G.induce V₂` overlapping in `{u,v}`, an edge `uv` sits in
  *both* sides and is charged twice — 346 failures in 2104 adjacent instances, minimal
  counterexample `V₁={u,v,a}`, `V₂={u,v,b}`, `E={av,bv,uv}` (`def₃ = 3`, both the `max` and the
  `min` form give `2`); it needs `¬ G.Adj u v` or an explicit edge bipartition (**D1**, the
  user's). Its arithmetic is otherwise **correct** as transcribed. (iii) **6b needs a carrier
  the slot-trace assigned to 6c** — `g = def₃(H/uv)` — while `f_sep` is needed by *only* the
  S6(ii) welded law. Correcting the opening slot-trace: 6c's four laws are **not** "exactly the
  laws S14(i)–(ii) consume" — only the fibre-product identity (read as S10(ii)'s **gluing**,
  not S7(i)'s `M_U` quotient) and the joint count **at `U = ⊥`** are; C3 is off the consumed
  path and the general-`U` joint count is keyed to (O4″), which workbook S14(vi) says is not
  consumed.
  - [x] **A1 — 6a, the pendant law** `def₃(G) = def₃(G − u) + 1` at a degree-1 vertex.
    `deficiency_removeVertex_of_degree_eq_one`. **LANDS 2026-09-16**, sorry-free, transcribed
    verbatim from the recon; sites in **`Induction/SplitOffDeficiency.lean`** beside its
    degree-2 inequality sibling `removeVertex_deficiency_ge` (`:405`) — **not** in
    `Deficiency.lean`, which is upstream of `Graph.removeVertex`
    (`Induction/Operations.lean:727`) and where the proof fails to elaborate.
  - [x] **A2 — the combinatorial carriers.** `deficiencyMerged` (= `g`), `deficiencySep`
    (= `f_sep`), `weldPair` (= `H/uv`), `pairDelta` (= `δ`), plus the general new
    `partitionDef_map` and the bridge `deficiency_weldPair_eq_deficiencyMerged` — **LANDS
    2026-09-16**, both proved sorry-free (so **D4**, which `g`-carrier is public, is settled by
    a proof, not a preference), plus the `bddAbove`/`le_ciSup` helpers the bridge needs
    (`bddAbove_range_partitionDef_merged`, `partitionDef_le_deficiencyMerged`). `deficiencySep`
    has **no consumer in this slice** (only the deferred A6, D2, needs it) and is defined bare,
    per the scope-pin. Site `Deficiency.lean`; `weldPair` inlines
    `fun x => if x = u then v else x` rather than use `Graph.collapseTo`
    (`Induction/ReducibleVertex.lean:1451`, downstream), the two being provably equal.
  - [ ] **A3** — `deficiency_eq_max` (`f = max(g, f_sep)`) and `pairDelta_le_bodyBarDim`
    (`δ ≤ D`, from the landed `partitionDef_merge`, `Deficiency.lean:1978`). Needed only for
    A5. Site `Deficiency.lean`.
  - [ ] **A4 — 6b, the vertex 2-cut law**, max form
    `def₃(G) = max(g₁+g₂, f₁+f₂−D)` (**D3**: recommended as primary — it needs neither `f_sep`
    nor `δ ≤ D`). The substantive combinatorial leaf: refining a labeling so no part straddles
    the two sides costs **zero** new crossing edges here (unlike the landed edge-cut law) and
    gains `+D` per split; then a two-case exact split on whether `u, v` share a part. Site
    `Deficiency.lean`; depends on A2.
  - [ ] **A5 — 6b′**, the transcribed `min` form `f₁+f₂ − min(δ₁+δ₂, D)`. A corollary of
    A3 + A4.
  - [ ] **A6 — C3**, the welded pendant `g(H) = max(g(H−u), f_sep(H−u) − (D−1))`, and
    `δ(H) = min(δ′+1, D)` (S6(ii)'s remaining clauses; both need `w ≠ v`). **DEFERRED by the
    user's D2 call (2026-09-16); reason: off the consumed path** — S6 is the side-degree-1 reduction and S14's `H′` has
    side-degree ≥ 2 at both ends (S10(iii)); it is also the only law needing `deficiencySep`.
    Kept as an entry, not dropped. Site `Induction/SplitOffDeficiency.lean` (uses
    `removeVertex`).
  - [ ] **B1 — the geometric carriers.** `relScrews` (= `ρ̄_{uv}`, `Submodule.map (screwDiff v
    u) F.infinitesimalMotions`), `jointRows`, `jointMotions` (= `M_U`), `weldedRank`. All four
    site in **`RigidityMatrix/Bricks.lean`** (verified: the whole of Layer B compiles against
    `RigidityMatrix/Basic.lean`'s import surface; the file is a `module` with a `public
    section`). `ρ̄`/`jointMotions`/`weldedRank` are forced by the laws' use; `jointRows`'
    annihilator phrasing is a free but recommended choice that makes the weld (`U = ⊥`) and the
    deferred profiles (general `U`) one definition.
  - [ ] **B2–B4 — the weld-rank identity.** `finrank_span_jointRows`,
    `inf_span_rigidityRows_span_jointRows_top`, then **C2-core** `weldedRank_eq`:
    `rank_w = rank + ρ`. This single fact *is* the whole linear-algebraic content of the
    transcribed welded bound `ρ ≤ δ + a`.
  - [ ] **B5–B6 — C1, the fibre-product / gluing identity**, rank form
    `rank(G) = rank(H₁) + rank(H₂) + dim(ρ̄₁ ⊔ ρ̄₂) − screwDim k`, whose core is the new brick
    `R₁ ⊓ R₂ = span (jointRows (ρ̄₁ ⊔ ρ̄₂) u v)`. **Genuinely new on two counts:** the landed
    `le_finrank_span_rigidityRows_of_cut` (`RigidityMatrix/Bricks.lean:284`) has
    vertex-**disjoint** sides *and* is an inequality, while S14 needs both directions. Unlike
    6b this law does **not** need `¬ G.Adj u v`.
  - [ ] **C1ℓ–C3ℓ — the losses.** `pencilLoss` (= `a`; `0 ≤ pencilLoss` is the landed
    `finrank_span_rigidityRows_add_deficiency_le`, `AlgebraicInduction/GenericityDevice.lean:564`),
    `weldedLoss` (= `a_w`, target `screwDim k·(|V|−1) − g`), `weldedLoss_nonneg` (= the joint
    count **at `U = ⊥`**, the one instance S14(i) consumes), and **C2** `finrank_relScrews_eq`
    (`ρ = δ + a − a_w`). Site a new `Molecule/Pencil/TwoCut.lean` — these need `deficiency`, so
    they cannot live in a `module` file; verified that `Molecule/Pencil/Arms.lean`'s surface
    sees everything Layer C needs.
  - [ ] **C4ℓ — the headline target:** `pencilLoss_vertexTwoCut`, which *is* S10(ii)'s
    attainment criterion `a(G) = a₁ + a₂ + min(δ₁+δ₂, 6) − dim(ρ̄₁ ⊔ ρ̄₂)`, in one statement.
    Depends on A4/A5, B6, C1ℓ. This is the most valuable single thing item 6 can produce.
  - [ ] **DEFERRED with reason, tracked not dropped** (all cheap once B1 lands): the
    **general-`U` joint count** (S7(iii)) and **`finrank_jointMotions_eq`** (S7(i)) — profile
    machinery keyed to (O4″), which S14(vi) says is not consumed, and the only statements that
    must be motion-side (hence `|α|`-laden); **S7(ii)** (the bar reading), **S7(v)** (Klein
    self-duality) and **S9** (the `ear1` criterion) — same family.
  - **Normalization, for any builder here.** `partitionDef` (`Deficiency.lean:262`) is the
    workbook's `count(P)` on the nose, so every combinatorial law is `D`-general with
    `6 ↦ bodyBarDim n`, `5 ↦ bodyBarDim n − 1` (checked at `D ∈ {3,4,6,10}`). But
    `F.infinitesimalMotions` lives over **all of `α`**, so motion-dimension statements carry
    `6·(|α| − |V(G)|)`: **state the geometric laws rank-side**, as `HasPencilRealization`
    already does. That is why every carrier above is rank-side and the one law that cannot be
    is the one deferred.
- [ ] **`hK` on the tight stratum from grid vanishing**, the colouring statement as
  hypothesis: decoupling, rank formula, Vandermonde, chart step, descent. Decides whether the
  **independence proviso** is a hypothesis of the crux (`notes/attacks/gr10/brief.md` §2
  *Proviso (P)*). Substantial: the chart
  machinery (`IsFin3SelectorOf`, `cross₃`, `pencilRow`) exists; the grid geometry does not.
- [ ] **Tree-triple ⇒ `dim Z = 0`**, and the circular-ladder family (GUNIZERO's uniform
  instance) as a formal witness.
- [ ] **W4 build**, when commissioned: W4-L4b (`exists_degree_two_of_co1_rigid`, pinned and
  spike-elaborated), then order-flexibly W4-L1/L2/L3′/L5; residual carry `hnoGood'`
  (non-vacuous — `|V| = 19` witness — so branch 4 needs content).
- [ ] **Reverse arms of the W0 transport** (need a `complementIso` involution lemma) — off
  every critical path (§(K-σ) *Step σ6*).

## Blockers / open questions

- **The Lean hold (2026-08-05) is the user's**; lifting it for named items is a PI call, made
  per item. **Lifted 2026-09-15 for checklist items 1–3** (verbatim record
  `notes/pencil/adjudications.md`); **lifted 2026-09-16 for checklist items 4–5** (the R2 Lean
  round; same record, verbatim); **lifted 2026-09-16 for checklist item 6** (the deficiency
  laws; same record) — items 7–12 stay parked.
- **Item 6's five decisions (D1–D5) — ALL SETTLED 2026-09-16 (user).** Verbatim:
  `notes/pencil/adjudications.md`. Full statements and the recon's reasoning:
  `notes/Phase39-design.md` § *Item-6 carrier recon (2026-09-16)*, *Open decisions*. The user
  took the recommendations on D1–D4 and decided D5 against a chapter. **Nothing below is open**;
  the recommendation text is kept because it carries the reasoning.
  - **D1 — the 6b hypothesis. The one that blocks a build.** With induced sides the vertex
    2-cut law is **false** when `u ~ v` (346/2104 adjacent instances; minimal counterexample in
    the *Lemma checklist*): it needs `¬ G.Adj u v` **or** an explicit edge bipartition
    `E(H₁) ⊎ E(H₂) = E(G)`. *Recommendation:* `¬ G.Adj u v` — free in the consumed shape
    (S10(iii)'s `w ≁ v`, from girth ≥ 7) and much cleaner in Lean. **SETTLED (user): `¬ G.Adj u v`.**
  - **D2 — is A6/C3 in item 6's scope?** It is the only law needing `deficiencySep` and it is
    off the consumed path. **SETTLED (user): DROPPED from item 6's scope** — A6 stays an
    explicit deferred entry with its reason, built only if S6's reduction becomes consumed. If
    that leaves `deficiencySep` with no consumer but A5, it lands as a minor helper, not a
    headline carrier (coordinator, same call).
  - **D3 — 6b's primary form. SETTLED (user): `max(g₁+g₂, f₁+f₂−D)` primary**, the
    transcribed `min` form a corollary (the max form needs neither `f_sep` nor `δ ≤ D`).
  - **D4 — `g`'s public face.** Settled mathematically (the two carriers are *provably* equal),
    so only a presentation call. **SETTLED (user): state the laws in `deficiencyMerged`**, keep
    `weldPair` as the faithful `H/uv`; both are defined.
  - **D5 — does item 6 open a blueprint chapter? SETTLED (user): NO, for now.** Reason given:
    *"it might not make sense to write a blueprint without the informal proof being complete"* —
    which is the same conclusion the unreachability finding below reaches from the other side
    (S14 needs a variety layer that does not exist even informally in Lean-compatible form), so
    a chapter would pin a shape likely to be reworked. The *Layer plan* in this note is item 6's
    to-do list instead. **This is a deliberate forward-mode deviation** (forward mode's usual
    answer to an incomplete argument is red nodes) and it creates **blueprint debt**, tracked in
    the next bullet.
- **Blueprint debt from D5 (opened 2026-09-16).** Item 6's leaves land with **no blueprint
  nodes**. Nothing catches this: `checkdecls` validates only `\lean{...}` pins that *exist*, so
  a decl with no node fails no gate. The debt is every decl Layers A/B/C land — at minimum
  `deficiency_removeVertex_of_degree_eq_one`, `deficiency_eq_of_vertexTwoCut`(`'`),
  `deficiencyMerged`/`deficiencySep`/`weldPair`/`pairDelta`, `partitionDef_map`,
  `deficiency_weldPair_eq_deficiencyMerged`, `bddAbove_range_partitionDef_merged`,
  `partitionDef_le_deficiencyMerged` (**A1/A2, landed 2026-09-16**),
  `relScrews`/`jointRows`/`jointMotions`/`weldedRank`,
  `weldedRank_eq`, `inf_span_rigidityRows_of_vertexTwoCut`,
  `finrank_span_rigidityRows_vertexTwoCut_eq`, `pencilLoss`/`weldedLoss`, `weldedLoss_nonneg`,
  `finrank_relScrews_eq`, `pencilLoss_vertexTwoCut`. **Discharge when the informal proof closes**
  (i.e. when the variety layer below is settled), or earlier if the user reverses D5. A build
  slice that lands a Layer leaf adds it to this list in the same commit.
- **Item 6 does NOT reach S14(i)–(ii), and the two gaps are outside it** (2026-09-16 recon;
  recorded here so a later session does not re-discover it). Even with Layers A–C all landed,
  S14(i)–(ii) still consumes **(a)** the **S8 ear-profile facts** — `ρ̄(ear_k)` is
  `(k+1)`-dimensional, `ear_k` attains and welded-attains — which have no carrier and are not
  in item 6's list; and **(b)** a **configuration-variety layer**, which the tree does not have
  at all: `HasPencilRealization` (`Statement.lean:103`), `HasDistinctPencilRealization`
  (`:131`) and `HasGenericPencilRealization` (`Motive.lean:141`) are single-configuration
  existentials, `IsNondegPencilRealization` (`Motive.lean:111`) is a nondegeneracy predicate,
  and `AlgebraicInduction/GenericityDevice.lean` is polynomial-non-vanishing, not irreducible
  components. S14's (α) irreducibility, (β) closure of the nondegenerate locus and (γ) descent
  have **no Lean surface**. So item 6 lands the *pointwise* combinatorial and linear-algebraic
  skeleton of S10(ii)/S14(i)–(ii) — durable and reusable — and the step itself needs a variety
  layer that is a separate, much larger decision.
- **Each attack's first move is a reading check, not a sweep:** the girth-5 restriction and
  the frame gap for S-mark; the independence proviso for (GR-10). Session 1 should settle or
  scope these before choosing a route. (S-mark's session 1 did the girth check but not a
  verbatim diff of the consuming hypotheses; the dropped disjunct was caught at review 1 and the
  misread antecedent only at session 5 — `notes/harness/incidents.md` 2026-09-15, 2026-09-16.)
  **`/harness-review` is due** (five S-mark sessions). Artifact-shaped candidates from review 2,
  for that review and not for any research session: the brief quotes the consumer's declaration
  verbatim, one hypothesis per line, each operator glossed from its definition body, and a
  script diffs that block against the source; every hypothesis the route does not use gets a
  one-line justification in the state file; every open obligation carries a "consumed because"
  line naming the Lean hypothesis that makes it necessary; a measured nonzero gets its witness
  exhibited before a mechanism is written; the reviewer's first step diffs the brief against
  the source.
- **Item 4's questions are ANSWERED and its one open decision is SETTLED (α)** (user,
  2026-09-16, verbatim in `notes/pencil/adjudications.md`; applied by item 5 the same day).
  `PencilPair` gained the simple-conditioned adjacent-distinct conjunct, so `hbareSplit`'s
  antecedent is a `Y(G₋)`-point and O8's coincident stratum is gone; the price is one new
  informal W4 obligation on the carried `hcontract` — un-coinciding at the contraction's
  parallel classes — logged with an (unpriced, expected-cheap) estimate in
  `notes/pencil/workbook/W4.md`. The attack's own structural residue is **O7** — irreducibility
  of the side's configuration space, or matching of the component the antecedent certifies with
  the one the IH certifies — on the bare arm, where some hub has three hub neighbours; no
  driver population has sampled that arm (every census branch has length `≥ 2`), and the
  2026-07-30 (K-bare) recon flagged the same evidence gap.
- **(GR-10)'s scope — SETTLED 2026-09-16 (user): re-scoped.** The recon's (a) and (c) HOLD and
  (d) is confirmed, so R2 covers `hK`'s arm at the statement level (S14(iii), (vii) — the latter
  still a sketch, not a proof); under (d) `hK` needs no chart, so the independence proviso (P)
  drops out of `hK`'s *statement* and survives only inside the grid route itself. The user's
  call: **run the char-2 probe now; keep the grid/colouring route as a documented fallback**, to
  be revisited only if S14(iii)/(vii) or O7 stall. Session 1 does not run as briefed, and the
  uniform-colouring statement (the weak form of `notes/attacks/gr10/brief.md` §2) is **not**
  being attacked. Verbatim: `notes/pencil/adjudications.md`; the gr10 brief's PI pointer now
  carries the decision, since an attack reads only its brief and state at start.
- **The (K-res) wave** (a kernel of `hK`'s difficulty class on the complementary habitat,
  scoped RESGRID, cheap items spent RPOOL) stays a user call; route σ is a live candidate
  that is not a route to (K-res). Detail: `notes/pencil/arc-worklog.md` *Hand-off*.
- **One L5 residual constrains statements — restated per the item-4 recon (c):** the bare
  `≤ 3`-closedHubNbhd count *alone* is refuted as a feasibility criterion
  (`not_pencilNondegFeasible_of_triangle_two_hubs`, `Motive.lean:684` — its graph is a triangle),
  while the count **plus triangle-freeness** is landed in both directions (`Motive.lean:410` ⇒,
  `Steer.lean:1344` ⇐): in the triangle-free habitat feasibility is exactly
  `∀ w, |closedHubNbhd w| ≤ 3` and passes to every subgraph by reconstruction — landed
  2026-09-16 as `pencilNondegFeasible_of_le_of_triangleFree` (`Steer.lean`). The
  triangle is why both readings coexist. Restricting a parent's witness instead is gapped at hubs
  demoted to degree 2 (`PencilNondegFeasible.mono`) — the chain ends.
- **Harness:** none open; incidents go to `notes/harness/incidents.md`, one line each, and
  `HARNESS.md` changes only in `/harness-review`.

## Hand-off / next phase

**The phase stays OPEN.** Checklist items 1–5 are DONE, item 6's carrier recon is DONE
(2026-09-16), item 6's **D1–D5 are all SETTLED** (2026-09-16, user; *Blockers*), and item 6's
**Layer-A leaves A1 and A2 LAND (2026-09-16)** — the record is `notes/Phase39-design.md`
§ *Item-6 carrier recon (2026-09-16)*, and the remaining buildable leaves are the A3–A6/B/C
sub-items under *Lemma checklist*. Read that arc before scoping any item-6 slice: it carries
the exact signatures, the sites (two of which the recon got wrong on its first pass and fixed
by compiling), and the numerics.
Next concrete task, in order: **(1) item-6 leaf A4** (the substantive combinatorial leaf,
`deficiency_eq_of_vertexTwoCut`'s `max` form, D3's primary statement; depends on A2, done)
**or Layer B1→B5** (the geometric carriers, independent of A), under `/coordinate-phase 39`.
**(2) The S-mark brief rewrite**, drafted by an agent from the
*landed* declarations and PI-reviewed. §2 = the kernel implication with the IH as landed; §3 =
both kernels quoted **verbatim from `Escape.lean` as they now stand** (`notes/Phase39-design.md`
§ *Kernel restatement (2026-09-16)* has the same text — **never** the pinned blocks under
§ *W5-L7 research recon*), one hypothesis per line, each operator glossed from its definition
body (`splitOff`, `PencilHub`, `PencilNondegFeasible`, `HasDistinctPencilRealization`,
`HasGenericPencilRealization`), the recon's answers to (a)–(d) (the design arc's *Material for
the brief's §3*), and a one-line justification for any hypothesis the route does not use; §6 =
O7 first — build an adjacent-hub side (a hub with three hub neighbours, each continued by a
branch of length `≥ 2` to `w` or `v`, girth `≥ 7`) and sample from several starts before
attempting the tower extension or component matching — then O9. **O8's coincident stratum is
deleted** by the (α) decision and must come out of the brief, not be re-stated. **(3)**
`/attack smark` session 6, a main session in its own worktree; and, when the PI chooses to spend
it, the **char-2 probe** as the sole live (GR-10) item (one driver leg beside `closure.py
--char2`; spec `notes/Phase39-design.md` § *Field-hypothesis recon*, last subsection) — a
systematic `F_{2^k}` miss is a re-pin trigger for the headline typeclass, so it reports to the
PI, not just to the attack. When an attack starts, its `state.md` is that lemma's status
surface and this note carries a two-line pointer to it, edited by the PI. **On a future HIT the
phase-boundary consequences are the USER's call** (`PHASE-BOUNDARIES.md`, against the
2026-07-24 no-split adjudication), surfaced with an estimate, never unilateral.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

### Phase-local choices

- **2026-09-16 — item 5 LANDED: the kernels take the induction hypothesis, `hK` weakens to
  the generic motive, and `PencilPair` gains an adjacent-distinct third conjunct (user: (α),
  one slice).** New motive `HasDistinctPencilRealization` (`Statement.lean`), *never* a
  conjunct on `HasPencilPanelRealization` (that is refuted and would break
  `lem:pencil-self-dual`). Cut arm done once with a `Prop` flag, not duplicated. (c) adder
  `pencilNondegFeasible_of_le_of_triangleFree` in `Steer.lean`. New informal W4 obligation.
  Record: `notes/Phase39-design.md` § *Kernel restatement (2026-09-16)*; verbatim decisions
  `notes/pencil/adjudications.md`; W4 `notes/pencil/workbook/W4.md`.

- **2026-09-16 — item 6's D1–D5 SETTLED (user).** D1 `¬ G.Adj u v` (the 6b law is false
  without it); D2 A6/C3 dropped from scope, kept as a deferred entry; D3 the `max` form primary;
  D4 laws stated in `deficiencyMerged`, `weldPair` kept; **D5 no blueprint chapter for now** —
  the informal proof is not complete, so a chapter would pin a shape likely to be reworked. D5
  is a deliberate forward-mode deviation and opens tracked blueprint debt (*Blockers*).
  Verbatim: `notes/pencil/adjudications.md`.

- **2026-09-16 — item 6 Layer-A leaves A1 and A2 LAND** (transcription from the recon, no new
  decisions). A1 `deficiency_removeVertex_of_degree_eq_one`
  (`Induction/SplitOffDeficiency.lean`, beside `removeVertex_deficiency_ge`). A2 the
  combinatorial carriers `deficiencyMerged`/`deficiencySep`/`weldPair`/`pairDelta` plus
  `partitionDef_map` and the D4-settling bridge `deficiency_weldPair_eq_deficiencyMerged`
  (`Deficiency.lean`), with two small `bddAbove`/`le_ciSup` helpers the bridge needs.
  `deficiencySep` has no consumer this slice (D2's A6 is deferred). Both sorry-free, gates
  green. Blueprint debt list extended (*Blockers*).

- **2026-09-16 — the Lean hold is LIFTED for checklist item 6 (user); the item is NOT one
  build slice, and its carrier recon is now RECORDED (coordinator-accepted).** A slot-trace
  split it 6a / 6b / 6c; the recon then *proved* 6a, found 6b **false** without
  `¬ G.Adj u v`, moved the `g` carrier from 6c to 6b, and **corrected this note's earlier
  claim that 6c's four laws are "exactly the laws S14(i)–(ii) consume"** — only the S10(ii)
  gluing identity and the joint count at `U = ⊥` are. Leaves, sites and D1–D5: *Lemma
  checklist* item 6 and *Blockers*. Record: `notes/Phase39-design.md` § *Item-6 carrier recon
  (2026-09-16)*. Verbatim: `notes/pencil/adjudications.md`.

- **2026-09-16 — (GR-10) RE-SCOPED (user).** R2 covers `hK`'s arm at the statement level and
  (d) drops the chart, hence proviso (P), out of `hK`'s statement, so the grid/colouring route is
  no longer the path to `hK`: it stays a **documented fallback** against a stall in S14(iii)/(vii)
  or O7, session 1 does not run as briefed, and the only live (GR-10) item is the **char-2
  probe** (the conjecture's field range, orthogonal to the route). Verbatim:
  `notes/pencil/adjudications.md`; brief pointer updated in place.

- **2026-09-16 — item 4 (the R2 recon) verdict RECORDED (coordinator-accepted).** (a) rank
  bridge exact, (c) side feasibility by reconstruction, (d) `hK` weakening confirmed; (b) left as
  the PI's (α)/(β) motive call; (GR-10) scope left as the user's. Record:
  `notes/Phase39-design.md` § *R2 recon*.
- **2026-09-16 — S-mark route R2 adopted; both kernels get the induction hypothesis (PI, on
  review 2's recommendation).** R1's obligations — profile bounds on an arbitrary hub-terminal
  side — were never consumed; the kernels' split-off antecedent read at the generic point
  supplies them (S14(iii)), and the pinned kernels are not locally provable without the side's
  attainment (S14(v)). Hold lifted for items 4–5 (user, same day); sequence: recon → kernel
  restatement → brief rewrite → session 6. Also settled by R2: the pending cut-vertex-case and
  induction-frame decisions (S14(iv), S14(i)); long-chain composition and the 3-block skeleton
  leave the checklist. Verbatim: `notes/pencil/adjudications.md`; review notes: workbook S15.
- **2026-09-15 — the field hypothesis: option C (PI).** The reduction stays `[Infinite K]`; the
  hypothesis lives on the kernel lemmas at the weakest form each proof needs — (K) via the grid
  `[Infinite K] [NeZero (2 : K)]` (`char ≠ 2`), (K-bare) via the 2-cut composition `[Infinite K]`
  in witness form (interim `IsAlgClosed K`) — and the unconditional corollary inherits them.
  Neither informal route needs characteristic 0; no landed proof uses one. Char-2 probe deferred
  to the (GR-10) attack. Verbatim: `notes/pencil/adjudications.md`; record:
  `notes/Phase39-design.md` § *Field-hypothesis recon*; chapter: `fmlnote:pencil-conditional-realization-pair-field`.
- **2026-09-15 — items 1–2 PINNED, then LANDED (design pass, `notes/Phase39-design.md`
  § *Lean-track design pass*).** Cycle carrier `Fin m` data + predicate `Graph.GirthGE` (not the
  Matroid package's `IsCycle`/`IsCyclicWalk`, not an `ℕ∞` girth); chain carrier `WList` paths in
  ∃-statements (no `ChainData` variant record yet); two new files, since
  `Deficiency.lean`/`Operations.lean` are past the tripwire. Findings: the consumed shape is a
  trichotomy (cut-vertex closure, V3); `w ≁ v` only for `m ≤ 4` (V4); any hub ⇒ girth `≥ 7` (V5).
  All eight nodes of `sec:pencil-girth-chain` went green the same day, every pinned signature
  typechecking as written.
- **2026-09-15 — the Lean hold is LIFTED for checklist items 1–3 (user).** Girth lemmas,
  consumed-shape normal form, the field-hypothesis decision (recon first; the PI decides on its
  verdict). Items 4–10 stay parked. Verbatim: `notes/pencil/adjudications.md`.
- **2026-09-15 — the research loop is RETIRED; attack tracks replace directions.** Six weeks
  and 127 directions moved no carried item; coordinator effort was ~55 % process; ~158
  imperatives, most single-incident. Rules: `HARNESS.md`; mechanics: `/attack`,
  `/review-attack`, `/harness-review`; record: `notes/harness/incidents.md`.
- **2026-08-05 — Lean hold (user).** Lean parked while ideas are sought; every script the
  project runs is committed (`notes/scripts/README.md`).
- **2026-08-02 — W4 route 3, packaging (b)** adjudicated; (K-res) a byte-identical sibling of
  `hK`; the build decomposed and then parked by the hold.
- **2026-07-24 — the phase stays open** rather than splitting at the three carried items.
- **Pre-arc Lean decisions (W0–W5, 2026-07-23 → 08-04)** — `notes/Phase39-design.md` and
  `notes/pencil/arc-worklog.md` *Decisions made*; the recon verdicts R1–R3 are
  `notes/pencil/structure.md` §"The question and the opening recon".

### Promoted to HARNESS / DESIGN / TACTICS

- *Evidence and reproducibility rules distilled from the arc* → `HARNESS.md` *Evidence*,
  *Reproducibility* (the retired manual `RESEARCH-ARC.md` is the provenance).
- *Both triggers of `linter.style.show` (goal-changing **and** no-op), plus the
  `haveI`-on-a-`Prop`-class sibling* → `TACTICS-GOLF.md` § 12; FRICTION entry
  *Two Lean style linters cost a build cycle each in one commit*.
- *`LinearIndependent.pair_map`* (injective linear map preserves pair independence)
  → mirrored, `CombinatorialRigidity/Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`.

### The research arc's record (2026-08-05 → 09-13)

- **127 one-line verdicts**, the (BE-14) and `hK` lanes' per-landing detail, the ranked
  carried items and route σ: `notes/pencil/arc-worklog.md` (verbatim), `notes/pencil/fanout.md`
  §"<CODE>", `notes/pencil/structure.md` blocks 8–14, `notes/pencil/strategy.md` §8.

## Citations (transcribed, project-canonical sources)

**RELOCATED 2026-09-01** (verbatim) to `notes/pencil/structure.md` §"Citations — the phase's
verified bibliography" (block 7), which carries the per-source venue data and the
verification dates. A direction or attack that verifies a new source adds it there.
