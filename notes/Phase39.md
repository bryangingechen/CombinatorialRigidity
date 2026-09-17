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
hypothesis option C). **Items 4–5 DONE 2026-09-16.** The R2 recon settled the rank bridge
(exact), side feasibility (by reconstruction) and `hK`'s conclusion (weakenable); its one open
finding — the bare motive attains at *coincident* adjacent points — the user settled **(α)**, a
simple-conditioned third `PencilPair` conjunct. **Item 5 then landed in one slice:** both kernels
take the induction hypothesis (S14(v): as pinned they are false on a never-attaining side), `hK`
concludes `HasGenericPencilRealization K 3 G`, and `hbareSplit` takes and returns the new motive
`HasDistinctPencilRealization`. **For the kernels' current form read `notes/Phase39-design.md`
§ *Kernel restatement (2026-09-16)*, not the older pinned blocks.** **Next: the S-mark brief
rewrite** against the landed statements, then `/attack smark` session 6; **(GR-10) is
RE-SCOPED** (user, 2026-09-16): the char-2 probe runs; the grid/colouring route is a documented
fallback, not the path to `hK`. Items 6–12 (the 2026-09-15 numbering's 4–10) stay parked by the hold.

**The retired research arc** (2026-08-05 → 09-13: 127 directions, nineteen strategy passes,
under a coordinator loop retired 2026-09-15 — `notes/harness/incidents.md`). Its final
work-log state is **verbatim** at `notes/pencil/arc-worklog.md`; per-direction specs and
verdicts `notes/pencil/fanout.md`; the *State of (K)* gap map `notes/pencil/workbook/gapmap.md`
(read with `python3 notes/gapmap.py`, never `sed`/`grep`); claims via `python3 notes/ledger.py`.
**Standing result at retirement: `hK` is not closer** — (GR-15)/(GR-10) OPEN since 2026-08-07,
(BE-14) one lemma (S-mark) away since 2026-08-26; **no content commit under
`Molecule/Pencil/` since 2026-08-05.**

## Current state

**Next concrete step: the S-mark brief rewrite** against the *landed* kernel statements
(*Hand-off* item 1), then `/attack smark` session 6; (GR-10)'s scope is settled (user,
2026-09-16 — *Blockers*): re-scoped to the char-2 probe, the grid route kept as a documented
fallback. Checklist items 4 and 5 are both DONE 2026-09-16. S-mark has five sessions (2026-09-15/16) and two reviews. Review 1
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
**Lean track — checklist items 1–5 are DONE (items 1–3 2026-09-15, items 4–5 2026-09-16).**
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
- [ ] **Deficiency laws** (BINDUC's, cited by 45 claims through (BE-22)): 3-connected ⇒
  `def₂ = 0`; the 2-cut law `def₃(G) = f₁ + f₂ − min(δ₁ + δ₂, 6)`; the fibre-product identity
  `dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁ + ρ̄₂)`; the welded bound `ρ_i ≤ δ_i + a_i` with
  equality iff `H_i/uv` attains (all three re-derived at the 2026-09-15 review, workbook
  S10(ii)); plus (review) the two pendant laws — deleting a degree-1 vertex drops `def₃` by
  exactly `1`, and welded `g(H) = max(g(H − u), f_sep(H − u) − 5)` — and the joint count
  `dim M_U(H) ≥ 6 + max(g, f + dim U − 6)` (workbook S6(ii), S7(iii);
  `partitionDef_split_of_sides`, `exists_sides_separated_partitionDef_le` are the pieces).
  Makes the composition criterion and the chain-length arithmetic (S10) exact; under R2 they are
  exactly what S14(i)–(ii) use, so the item backs the consumed step directly.
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
  round; same record, verbatim); items 6–12 stay parked.
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

**The phase stays OPEN.** Checklist items 1–5 are DONE; the Lean track has nothing queued.
Next concrete task, in order: **(1) The S-mark brief rewrite**, drafted by an agent from the
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
deleted** by the (α) decision and must come out of the brief, not be re-stated. **(2)**
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
