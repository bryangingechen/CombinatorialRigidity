# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`** — since 2026-09-16 a **three**-conjunct motive (bare; under `G.Simple` an
adjacent-distinct one; under simplicity plus feasibility a generic one). The landed theorem
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) derives
it from exactly **three carried hypotheses**: **`hcontract`** (W4; **REOPENED 2026-09-23**,
`notes/pencil/W4-reopen.md`; carries three kernels, (K-c), (K-bare-c), (K-res); (α) sits on (K-bare-c)),
**`hK`** (kernel (K)) and **`hbareSplit`** (kernel (K-bare)). W0–W3, W5 (L0–L7), `hsplit` and
`hfresh` are Lean-closed.

**Two tracks since 2026-09-15.** *(1)* **Attack track** — research on the two open kernels,
one agent per lemma under `/attack <name>` (`HARNESS.md`); each lemma's status surface is
`notes/attacks/<name>/state.md`. Briefs for **S-mark** (`hbareSplit`, and the split step of
`hK`) and **(GR-10)** (since the 2026-09-16 re-scope, the char-2 probe of `hK`'s conclusion) are at
`notes/attacks/{smark,gr10}/brief.md` (PI-reviewed 2026-09-15). **S-mark: route R2 (the split-off antecedent and the IH as
certificates for the generic point, S14; both kernels take the IH by the PI's 2026-09-16 decision); what is open is
`hbareSplit` at `m ≤ 4`. Session count, obligation count and next step live only in `notes/attacks/smark/state.md`
(latest review: workbook S38, 2026-09-23).** *(2)* **Lean track** — this note and `/coordinate-phase 39`:
formalize the reductions and foundations the attacks stand on, cruxes carried as
hypotheses, no `sorry`. Items 1–3 DONE 2026-09-15 (`sec:pencil-girth-chain` fully green; field
hypothesis option C). **Items 4–5 DONE 2026-09-16.** The R2 recon settled the rank bridge,
side feasibility and `hK`'s conclusion; its open finding (the bare motive attains at
*coincident* points) the user settled **(α)**. **Item 5 landed in one slice:** both kernels
take the induction hypothesis (S14(v)), `hK` concludes `HasGenericPencilRealization K 3 G`,
and `hbareSplit` takes and returns the new motive `HasDistinctPencilRealization`. **For the kernels' current form read `notes/Phase39-design.md`
§ *Kernel restatement (2026-09-16)*, not the older pinned blocks.** **Both attack briefs
CHECKED 2026-09-17** (PI-directed, against `084ee4ff`, after the Lean round closed):
`notes/attacks/smark/brief.md` (§§2, 3, 6 rewritten 2026-09-16 against the landed kernels)
verified hypothesis by hypothesis, patched again 2026-09-23 at review 3; `notes/attacks/gr10/brief.md`
restructured — **Part A the live char-2 probe** (the user's 2026-09-16 re-scope), Part B the
grid/colouring route as a documented fallback. **Item 6 (deficiency laws) is UNPARKED** (user, 2026-09-16):
carrier recon DONE, **D1–D5 SETTLED** (user; *Blockers*), and item 6 **DONE except the
deferred A6** — Layers A–C (A1–A5, B1–B7, C1ℓ–C4ℓ) all LAND 2026-09-17 (*Lemma checklist*, the
to-do list; no blueprint chapter). **Next: the PI's call on the main-component census** (DONE 2026-09-23, outcome A′ —
`notes/pencil/workbook/K-main.md` §(K-main); `notes/pencil/W4-reopen.md` P1; T1's Lean deferred, `kres` held; 2026-09-24 math pass (MC-11)–(MC-27), no census; the unranked directions' findings landing, (MC-28)–(MC-33) so far); `/attack smark` continues in its own worktree.
**gr10 CLOSED 2026-09-23** (PI, after review 1: char 2 limits the grid method only). Other items
parked.

**The retired research arc** (2026-08-05 → 09-13: 127 directions, nineteen strategy passes,
under a coordinator loop retired 2026-09-15 — `notes/harness/incidents.md`). Its final
work-log state is **verbatim** at `notes/pencil/arc-worklog.md`; per-direction specs and
verdicts `notes/pencil/fanout.md`; the *State of (K)* gap map `notes/pencil/workbook/gapmap.md`
(read with `python3 notes/gapmap.py`, never `sed`/`grep`); claims via `python3 notes/ledger.py`.
**Standing result at retirement: `hK` is not closer** — (GR-15)/(GR-10) OPEN since 2026-08-07,
(BE-14) one lemma (S-mark) away since 2026-08-26; **no content commit under
`Molecule/Pencil/` since 2026-08-05.**

## Current state

**Next: the PI's call on the main-component census** — DONE 2026-09-23, outcome **A′**: `X₀` attains at all 10 252 members, degenerate only at feasible graphs with a rigid subgraph (`notes/pencil/workbook/K-main.md` §(K-main); `notes/pencil/W4-reopen.md` P1; W4 REOPENED 2026-09-23; *Hand-off*). 2026-09-24: a math pass without a new census (PI) — (MC-11) the gain is exact, (MC-14) `X₀` nondegeneracy combinatorial mod Jackson–Jordán, (MC-15) `hK`'s habitat never A′, Step MC10 the ear step (every θ-graph attains). Later that day the three unranked W4-reopen directions were assessed and their findings are being landed step by step (Step MC11 the split-off step and (MC-33) Jackson–Jordán beyond ℝ so far); next per W4-reopen P1's *later* 2026-09-24 paragraph.
**Item 6 is DONE except the deferred A6 — Layer C (C1ℓ–C4ℓ) LANDS 2026-09-17** — A1–A5 the
pendant law, the combinatorial carriers,
the vertex 2-cut law and its two corollaries; B1–B6 the four geometric carriers, the joint's row
count, the welded-rank identity `weldedRank_eq` (`rank_w = rank + ρ`) and the 2-cut gluing
identity; B7 the welded **codimension** `weldedRank_add_finrank_jointMotions_bot` — all in
`section TwoCutCarriers` of `RigidityMatrix/Bricks.lean`. In `Molecule/Pencil/TwoCut.lean`: the
loss carriers `pencilLoss`/`weldedLoss` with C1ℓ `pencilLoss_nonneg` and C3ℓ
`finrank_relScrews_eq`, and **C2ℓ `weldedLoss_nonneg`** off the merged relative hub
`screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions`, with the workbook's own
`ρ ≤ δ + a` (`finrank_relScrews_le`) as a corollary. Sites, routes, the dropped hypotheses and
the **one tracked factoring item** (C2ℓ's hub duplicates ~85 lines of the landed hub) are in
the *Lemma checklist*; all sorry-free, gates green. **C4ℓ `pencilLoss_vertexTwoCut` LANDS
2026-09-17**, closing item 6's Lean track (only the deferred A6 and the factoring item remain,
both off any consumed path) — its route needed only A5+B6, not C1ℓ/C3ℓ (its own docstring).
**Both attack briefs are CHECKED 2026-09-17** (PI-directed docs session, against `084ee4ff`):
the S-mark brief's 2026-09-16 rewrite verified against `Escape.lean` and repinned, item 6's
landed laws glossed for the attack (its §4 *[Lean 2026-09-17]*), one `m ≥ 5` adjacency worry
added (§6); the gr10 brief restructured into Part A (the live char-2 probe, `hK` quoted
verbatim, obligations O1–O5, the certificate-is-a-proof reading through
`hasGenericPencilRealization_of_independent_pencilRow_target`) and Part B (the grid route as
documented fallback, §B3 restated against the landed `hK`). S-mark's own status surface is
`notes/attacks/smark/state.md` (its only status surface; counts and next step are kept there, not here); (GR-10)'s is `notes/attacks/gr10/state.md` — CLOSED 2026-09-23 after one session and review 1 (workbook `attack-gr10.md` S4, S5). Per this note's own policy (*Hand-off*) the
per-session narrative lives there, not here; the two consumer misreadings the reviews caught are
in the foundations paragraph below.
**Lean track — checklist items 1–5 are DONE (items 1–3 2026-09-15, items 4–5 2026-09-16);
item 6 is UNPARKED (user, 2026-09-16), its recon is DONE, its Layer A is DONE except the
deferred A6, and its Layer B and Layer C (C1ℓ–C4ℓ) are DONE (2026-09-16/17).**
Items 1–2's eight red nodes in `blueprint/src/chapter/pencil.tex` § *Girth and degree-two
chains* are **all green**; that chapter is their declaration index, so the names are not
re-listed here (files: `Molecular/Induction/Girth.lean`, `Molecule/Pencil/Motive.lean`,
`Molecular/Induction/ForestSurgery/MaximalChain.lean`). Item 3 is **SETTLED** (PI, option C):
the reduction stays `[Infinite K]`, the hypothesis lives on the kernel lemmas
(`notes/Phase39-design.md` § *Field-hypothesis recon*; chapter
`fmlnote:pencil-conditional-realization-pair-field`). Queued Lean work: none before P1 reports (*Hand-off*).
Builds need
`LAKE_CACHE_DIR` set (`notes/ToolchainBumps.md` *Environment*; session-wide via the gitignored
`.claude/settings.local.json`).

**Lean, landed:** the statement layer and stratum self-duality (W0), the KT Lemma 5.3/5.4
base cases (W1), the two-pencil layer (W2), W3, the whole of W5 (L0–L7, 2026-07-24 → 07-30),
`hsplit` in full and `hfresh`'s mechanical discharge (W5-L7c). **W4 — REOPENED 2026-09-23** (user;
route 3, packaging (b), adjudicated 2026-08-02; fully decomposed, gates N8/N9/N10/N10b
passed; canonical homes `notes/Phase39-design.md` §§ *W4 decomposition recon* / *W4-L4
identification recon* and `notes/pencil/workbook/W4.md`). Task list T0–T4 and the do-not list:
`notes/pencil/W4-reopen.md`; hold lifted for the wrapper and W4-L4b only (*Blockers*).

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
needs algebraic closure only as stated); option C, checklist item 3. **Rank bridge — CHECKED** (item-4 recon, 2026-09-16):
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

*Items 1–6 unparked 2026-09-15/16 (PI), the **W4 build** item in part 2026-09-23 (*Blockers*);
the rest stay parked by the hold. Ranked cheapest and most decision-relevant first; each
carries its crux as a HYPOTHESIS, never a `sorry`.*

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
- [x] **R2 recon (item 4) — DONE 2026-09-16** (read-only). All four verdicts, with the three
  compiled spike statements, are recorded in full at `notes/Phase39-design.md` § *R2 recon*
  (subsections (a)–(d)) and are not duplicated here; item 5 consumed them the same day. In one
  line each: **(a)** the rank bridge is exact on the adjacent-distinct locus; **(b)** the bare
  motive attains at coincident adjacent points where no distinct configuration does, the named
  fix REFUTED, settled **(α)** by the user; **(c)** feasibility passes to the side by
  reconstruction, not restriction; **(d)** `hK` may conclude `HasGenericPencilRealization K 3 G`.
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
  `deficiency_eq_of_cutEdges_ncard_le_one` (`Deficiency.lean:1767`) at `V₁ = {u}`. (ii) **6b is
  false as first stated**: with the sides taken as `G.induce V₁`, `G.induce V₂` overlapping in
  `{u,v}`, an edge `uv` sits in *both* sides and is charged twice — 346 failures in 2104
  adjacent instances, minimal counterexample `V₁={u,v,a}`, `V₂={u,v,b}`, `E={av,bv,uv}`
  (`def₃ = 3`, both the `max` and the `min` form give `2`); it needs `¬ G.Adj u v` or an explicit
  edge bipartition (**D1**, the user's). Its arithmetic is otherwise **correct**. (iii) **6b
  needs a carrier the slot-trace assigned to 6c** (`g = def₃(H/uv)`), and 6c's four laws are
  **not** "exactly the laws S14(i)–(ii) consume" — only S10(ii)'s **gluing** (not S7(i)'s `M_U`
  quotient) and the joint count **at `U = ⊥`** are.
  - [x] **A1–A3 — the pendant law, the carriers and their bounds** — **LAND 2026-09-16/17**, all
    sorry-free. **A1** = 6a `deficiency_removeVertex_of_degree_eq_one`, sited in
    **`Induction/SplitOffDeficiency.lean`** beside `removeVertex_deficiency_ge` (`:405`) — **not**
    `Deficiency.lean`, which is upstream of `Graph.removeVertex` (`Induction/Operations.lean:727`).
    **A2** = the carriers `deficiencyMerged` (`g`), `deficiencySep` (`f_sep`), `weldPair`
    (`H/uv`), `pairDelta` (`δ`), the general `partitionDef_map`, the bridge
    `deficiency_weldPair_eq_deficiencyMerged` — which settles **D4** by a proof, not a preference —
    and its `bddAbove`/`le_ciSup` helpers; `weldPair` inlines `if x = u then v else x` rather than
    the downstream `Graph.collapseTo`. **A3** = `pairDelta_le_bodyBarDim` (`δ ≤ D`) and
    `deficiency_eq_max`, `deficiencySep`'s only consumer and **not** needed by A5. Site
    `Deficiency.lean`.
  - [x] **A4 — 6b, the vertex 2-cut law**, max form `def₃(G) = max(g₁+g₂, f₁+f₂−D)` (**D3**).
    **LANDS 2026-09-17**, sorry-free, `deficiency_eq_of_vertexTwoCut` (`Deficiency.lean`), over
    A2. **The route supersedes the sketch above — no refinement lemma is needed:** one exact
    split identity valid for *every* labeling, `partitionDef_split_of_vertexTwoCut`
    (`= partitionDef₁ + partitionDef₂ + D*(1 − |f''V₁ ∩ f''V₂|)`), with `hnonadj` load-bearing
    *only* for crossing-edge disjointness; `≤`/`≥` then case-split on `f u = f v`.
  - [x] **A5 — 6b′**, the transcribed `min` form `f₁+f₂ − min(δ₁+δ₂, D)`. **LANDS 2026-09-17**,
    `deficiency_eq_of_vertexTwoCut'`, sorry-free. **A corollary of A4 alone, NOT A3** (the
    "A3 + A4" claim above was stale) — `pairDelta` is *definitionally* `deficiency −
    deficiencyMerged`, so `gᵢ = fᵢ − δᵢ` by `unfold`, and the `max`/`min` identity closes A4's
    statement into this one by pure arithmetic (`le_total (δ₁+δ₂) D`).
  - [ ] **A6 — C3**, the welded pendant `g(H) = max(g(H−u), f_sep(H−u) − (D−1))`, and
    `δ(H) = min(δ′+1, D)` (S6(ii)'s remaining clauses; both need `w ≠ v`). **DEFERRED by the
    user's D2 call (2026-09-16); reason: off the consumed path** — S6 is the side-degree-1
    reduction, S14's `H′` has side-degree ≥ 2 at both ends (S10(iii)), and it is the only law
    needing `deficiencySep`. Kept as an entry, not dropped. Site
    `Induction/SplitOffDeficiency.lean`.
  - [x] **B1–B4 — the carriers, the joint count and the weld-rank identity** — **LAND 2026-09-17**,
    sorry-free, in the new `section TwoCutCarriers` at the tail of **`RigidityMatrix/Bricks.lean`**,
    whose section header is their index: `relScrews` (= `ρ̄_{uv}`), `jointRows`, `jointMotions`
    (= `M_U`), `weldedRank`; `finrank_span_jointRows` (`= screwDim k − finrank U`, needs `u ≠ v`)
    through the unfolding lemma `span_jointRows_eq_map_dualAnnihilator`; and
    `inf_span_rigidityRows_span_jointRows_top` + **C2-core** `weldedRank_eq` (`rank_w = rank + ρ`),
    the whole linear-algebraic content of the transcribed welded bound `ρ ≤ δ + a`, with the
    reused helpers `map_screwDiff_comm` (the orientation flip) and `span_jointRows_bot`. The
    recon's unused instances are dropped throughout (no `[Finite β]` anywhere; B2 needs no
    `[Finite α]`, B3 not even `u ≠ v`). **Exposure: no obligation, no decision** (coordinator,
    2026-09-17, both cases run) — the `def`s are `public` but not `@[expose]`, so the *importer's*
    kind decides, and Layer C is necessarily non-`module` (it needs `Graph.bodyBarDim` from the
    non-`module` `BodyBar/Framework.lean`), so `TwoCut.lean` unfolds them by `rfl`. Full reading:
    `TwoCut.lean`'s module docstring.
  - [x] **B5–B6 — C1, the fibre-product / gluing identity** — **LAND 2026-09-17**, sorry-free:
    `inf_span_rigidityRows_of_vertexTwoCut` (C1′, `R₁ ⊓ R₂ = span (jointRows (ρ̄₁ ⊔ ρ̄₂) u v)`) and
    `finrank_span_rigidityRows_vertexTwoCut_eq` (C1, in `ℤ`:
    `rank(G) = rank₁ + rank₂ + dim(ρ̄₁ ⊔ ρ̄₂) − screwDim k`). Genuinely new against
    `le_finrank_span_rigidityRows_of_cut` (vertex-**disjoint** sides, and an inequality), and
    needing **no** `¬ G.Adj u v` — a cut edge is charged to both sides' *deficiencies* but
    contributes the **same rows** on either side, so it cannot disturb a row-span intersection.
    **The route that closed it is shorter than the reconned one:** rewrite both sides into the
    annihilator picture and the goal becomes one general dual fact, the new private
    `dualAnnihilator_eq_map_dualMap_screwDiff` (`W^⊥ = (map (screwDiff u v) W)^⊥.map dualMap`
    whenever `ker (screwDiff u v) ≤ W`) — no per-coordinate `Pi.single` bookkeeping. Its one
    geometric input, `mem_sup_infinitesimalMotions_induce` (dually `ker (screwDiff u v) ≤
    Z₁ ⊔ Z₂`), is one explicit `if`. B6 is the `weldedRank_eq` skeleton over B5 plus
    `rigidityRows_eq_union_induce`. **Three pinned hypotheses were dead and are dropped:**
    `[Finite β]`, `hcover` (in both leaves — a vertex in neither side carries no rows) and, in B5,
    `hsep`; of `hoverlap` only the `⊆` half is consumed. The private core's general form (any
    surjective `f`) is a mirror candidate, filed not mirrored (`notes/FRICTION.md`).
  - [x] **C1ℓ, C3ℓ — the loss carriers and the pure-algebra identity** — **LAND 2026-09-17**,
    sorry-free, new site `Molecule/Pencil/TwoCut.lean`: `pencilLoss` (= `a`), `weldedLoss`
    (= `a_w`, target `screwDim k·(|V|−1) − g`, **not** `·(|V|−2)`), **C1ℓ** `pencilLoss_nonneg`
    (the landed `finrank_span_rigidityRows_add_deficiency_le` over the new carrier) and **C3ℓ**
    `finrank_relScrews_eq` (`ρ = δ + a − a_w`, pure algebra over `weldedRank_eq`, no `hn`).
    Two more pinned instances dead and dropped (`[Finite α]` on both `def`s, `[Finite β]` on
    C3ℓ) — the Layer-B pattern recurring.
  - [x] **C2ℓ — `weldedLoss_nonneg`, plus the workbook's own `ρ ≤ δ + a`** — **LAND 2026-09-17**,
    sorry-free, in `TwoCut.lean` (with one Layer-B addendum in `Bricks.lean`). Settled by a
    compiler-checked spike (recon, same day) that closed the whole chain with **zero** residual
    goals; **the pivot is that `weldedRank` is a codimension** — the new B7
    `weldedRank_add_finrank_jointMotions_bot` (`rank_w + dim M_⊥ = screwDim k·|α|`, three
    annihilator identities: `span_union`, `span_rigidityRows_eq_dualAnnihilator_…`,
    `span_jointRows_bot` + `range_dualMap_eq_dualAnnihilator_ker_of_surjective`, then
    `Subspace.dualAnnihilator_inf_eq` — **`Subspace`, not `Submodule`**, and needing no
    finite-dimensionality). Route: the merged relative hub
    `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` is the landed hub's counting
    argument run at a labeling that keeps `u, v` together, whose partition motions are welded
    motions (`partitionMotions_le_jointMotions_bot`, read off `IsPartitionConstant`'s body
    `∀ u v, f u = f v → S u = S v`); B7 flips it from a motion lower bound to a rank upper bound.
    `hne` is dead (`⟨u, hu⟩`) and dropped; **`hu`/`hv` are provably necessary** — one vertex, no
    edges, `u, v ∉ V(G)` gives `weldedLoss = −screwDim k` (derivation in the docstring).
    `finrank_relScrews_le` (the transcribed `ρ ≤ δ + a`) rides along, one `linarith` over C3ℓ.
    The **alternative weld-graph route is dead by supersession *only***: it needs no
    support-extensor decision (`weldPair` is `Graph.map`, same `β`) and its `+ screwDim k` offset
    is right — both reasons for disliking it were wrong (witnesses in `notes/Phase39-design.md`).
  - [ ] **The shared hub normalization — a tracked factoring item, not a C2ℓ blocker.** C2ℓ's
    merged hub duplicates ~85 lines of
    `screwDim_mul_compl_add_deficiency_le_finrank_infinitesimalMotions`
    (`AlgebraicInduction/PanelLayer.lean:2187`) character-for-character; only the attaining
    labeling's subtype, one `g u = g v` step and the final monotonicity differ. Extract the `ι₀`
    normalization as one private lemma — for any `f`, some `g` with (i) `g '' V(G) ⊆ V(G)`,
    (ii) `numParts g = numParts f`, (iii) `crossingEdges g = crossingEdges f`,
    (iv) `|range g| = numParts f + |V(G)ᶜ|`, (v) `g x = g y ↔ f x = f y` on `V(G)` (which is what
    carries the merge) — and rebuild **both** hub sites on it. Deferred deliberately: it edits
    `PanelLayer.lean`, in the defeq-fragile zone, so it gets its own pass with its own
    verification (coordinator, 2026-09-17; Phase 38 is the precedent).
  - [x] **C4ℓ — the headline target `pencilLoss_vertexTwoCut`** — **LANDS 2026-09-17**,
    sorry-free, `TwoCut.lean`. S10(ii)'s attainment criterion in one statement, closed by
    unfolding `pencilLoss` and substituting only **A5+B6** (not C1ℓ/C3ℓ, despite the checklist's
    "depends on" line above) — route and the `hnonadj` asymmetry in the theorem's own docstring.
    **Layer C is now fully DONE (C1ℓ–C4ℓ)**, and item 6's Lean track is closed except the
    deferred A6 and the factoring item above.
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
- [ ] **W4 build — REOPENED 2026-09-23, staged; Lean DEFERRED until the census reports**
  (`notes/pencil/W4-reopen.md` P4, T1–T4). **Unparked:**
  **T1**, the W4 wrapper — a new declaration producing `hcontract`'s statement with (K-res)
  (restated against the 2026-09-16 `hK`) and any other unsettled piece as hypotheses, no edit
  to smark's consumer, red nodes in `pencil.tex`; and **W4-L4b** (`exists_degree_two_of_co1_rigid`,
  pinned and spike-elaborated). **Parked** until T1 and the (α) recon T2 report, then a PI call:
  W4-L1/L2/L3′/L5; residual carry `hnoGood'` (non-vacuous — `|V| = 19` witness — so branch 4
  needs content).
- [ ] **Reverse arms of the W0 transport** (need a `complementIso` involution lemma) — off
  every critical path (§(K-σ) *Step σ6*).

## Blockers / open questions

- **The Lean hold (2026-08-05) is the user's**; lifting it for named items is a PI call, made
  per item. **Lifted 2026-09-15 for checklist items 1–3** (verbatim record
  `notes/pencil/adjudications.md`); **lifted 2026-09-16 for checklist items 4–5** (the R2 Lean
  round; same record, verbatim); **lifted 2026-09-16 for checklist item 6** (the deficiency
  laws; same record); **lifted 2026-09-23, staged, for the W4 wrapper and W4-L4b only** (user:
  *"OK, sounds good."* to that recommendation; W4-L1/L2/L3′/L5 await T1 + T2 and one more call;
  same record) — the other items stay parked.
- **Item 6's five decisions (D1–D5) — ALL SETTLED 2026-09-16 (user).** Verbatim:
  `notes/pencil/adjudications.md`. Full statements and the recon's reasoning:
  `notes/Phase39-design.md` § *Item-6 carrier recon (2026-09-16)*, *Open decisions*. The user
  took the recommendations on D1–D4 and decided D5 against a chapter. **Nothing below is open**;
  the verdicts are one-lined below, the recon's full reasoning at the pointer above.
  - **D1 — the 6b hypothesis** (the one that blocked the build): **`¬ G.Adj u v`**. With
    induced sides the law is *false* when `u ~ v` (346/2104 adjacent instances; minimal
    counterexample in the *Lemma checklist*); an explicit edge bipartition was the alternative.
  - **D2 — A6/C3 DROPPED from item 6's scope** (off the consumed path; kept as an explicit
    deferred entry with its reason, built only if S6's reduction becomes consumed).
    `deficiencySep`'s only consumer turned out to be A3's `deficiency_eq_max` (A5 needs only
    A4) — landed as the minor helper the coordinator called it.
  - **D3 — 6b's primary form: `max(g₁+g₂, f₁+f₂−D)`**, the transcribed `min` form a corollary.
  - **D4 — state the laws in `deficiencyMerged`**, keeping `weldPair` as the faithful `H/uv`;
    both are defined, and the two carriers are *provably* equal, so this was presentation only.
  - **D5 — item 6 opens NO blueprint chapter, for now**, the reason given being that a
    blueprint without a complete informal proof would pin a shape likely to be reworked — the
    same conclusion the unreachability finding below reaches from the other side. The *Layer
    plan* in this note is item 6's to-do list instead. **A deliberate forward-mode deviation**
    (forward mode's usual answer to an incomplete argument is red nodes) creating **blueprint
    debt**, tracked in the next bullet.
- **Blueprint debt from D5 (opened 2026-09-16).** Item 6's leaves land with **no blueprint
  nodes**. Nothing catches this: `checkdecls` validates only `\lean{...}` pins that *exist*, so
  a decl with no node fails no gate. The debt is every decl Layers A/B/C land — at minimum
  `deficiency_removeVertex_of_degree_eq_one`, `deficiency_eq_of_vertexTwoCut`(`'`),
  `deficiencyMerged`/`deficiencySep`/`weldPair`/`pairDelta`, `partitionDef_map`,
  `deficiency_weldPair_eq_deficiencyMerged`, `bddAbove_range_partitionDef_merged`,
  `partitionDef_le_deficiencyMerged` (**A1/A2**, 2026-09-16); then, all 2026-09-17 and with
  every `private` helper exempt, `partitionDef_split_of_vertexTwoCut` (**A4**),
  `pairDelta_le_bodyBarDim`/`deficiency_eq_max` (**A3**, its four `Sep`/`Merged` bound helpers
  exempt too), `relScrews`/`jointRows`/`jointMotions`/`weldedRank` +
  `span_jointRows_eq_map_dualAnnihilator`/`finrank_span_jointRows` (**B1/B2**),
  `inf_span_rigidityRows_span_jointRows_top`/`weldedRank_eq` +
  `map_screwDiff_comm`/`span_jointRows_bot` (**B3/B4**),
  `inf_span_rigidityRows_of_vertexTwoCut`/`finrank_span_rigidityRows_vertexTwoCut_eq` (**B5/B6**),
  `pencilLoss`/`weldedLoss`/`finrank_relScrews_eq` (**C1ℓ/C3ℓ, 2026-09-17**),
  `weldedRank_add_finrank_jointMotions_bot` + `partitionMotions_le_jointMotions_bot` +
  `screwDim_mul_compl_add_deficiencyMerged_le_finrank_jointMotions` + `weldedLoss_nonneg` +
  `finrank_relScrews_le` (**B7/C2ℓ, 2026-09-17**), `pencilLoss_vertexTwoCut` (**C4ℓ,
  2026-09-17, LANDED — the whole debt list above is now item 6's full leaf set**).
  **Discharge when the informal proof closes**
  (i.e. when the variety layer below is settled), or earlier if the user reverses D5. A build
  slice that lands a Layer leaf adds it to this list in the same commit.
- **Item 6 does NOT reach S14(i)–(ii), and the two gaps are outside it** (2026-09-16 recon;
  recorded here so a later session does not re-discover it). Even with Layers A–C all landed,
  S14(i)–(ii) still consumes **(a)** the **S8 ear-profile facts** — `ρ̄(ear_k)` is
  `(k+1)`-dimensional, `ear_k` attains and welded-attains — which have no carrier and are not
  in item 6's list; and **(b)** a **configuration-variety layer**, which the tree does not have
  at all: `HasPencilRealization` (`Statement.lean:103`), `HasDistinctPencilRealization`
  (`:129`) and `HasGenericPencilRealization` (`Motive.lean:141`) are single-configuration
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
- **(K-res)** (a kernel of `hK`'s difficulty class on the complementary habitat) — **taken
  up by the 2026-09-23 reopening**: T1's partial pass restated it (residuals only); its Lean is
  deferred and the `kres` attack held until the census reports (`notes/pencil/W4-reopen.md` P4,
  P5; the predicted break is girth). W4 also carries (K-c) and (K-bare-c), never attacked.
  The grid route's (RS-5) is refuted at `R20` (method, not target); route σ is not a route to it.
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
**Layer A is DONE except the deferred A6, and its Layer B and Layer C (C1ℓ–C4ℓ) are DONE, all
2026-09-16/17** — the carrier recon record is `notes/Phase39-design.md`
§ *Item-6 carrier recon (2026-09-16)*, and the per-leaf routes (five of which supersede or
correct it — A4's sketch, A5's dependency, B1's exposure claim, C1ℓ/C3ℓ's dropped instances,
C4ℓ's two-input route) are in the *Lemma checklist* A3–C4ℓ entries.
**Item 6's Lean track is now closed**, except the deferred A6 and the shared-hub-normalization
factoring item (both tracked, off any consumed path; *Lemma checklist*). **W4 is REOPENED
(2026-09-23); the main-component census (P1, with P2 folded in) is DONE — outcome A′ of its pre-fixed decision table**
(`notes/pencil/workbook/K-main.md` §(K-main)). The next step is **the PI's call** on that row. A fresh session reads
`notes/pencil/W4-reopen.md` P1 for the agent's suggestion: an adversarial census, then P3 in two stop-ruled tracks. T1's Lean is deferred (P4), `kres` and a contraction attack held (P5). **(1)** `/attack smark`, a main session in its own worktree, from `notes/attacks/smark/state.md` *Next steps*
(brief last patched at review 5, workbook S38). **(2)** gr10 is CLOSED
(2026-09-23, PI, after review 1): no characteristic-2 miss at any shape tested (workbook
`attack-gr10.md` S4, S5), so no `[NeZero (2 : K)]` re-pin. Branch `attack-gr10` merged
2026-09-23 (`03f73e61`). Two PI calls stay open and block nothing: a registered label prefix for the attacks (both
number results S1…/P1… in their workbook files instead; incident 2026-09-15), and
`/harness-review`, due since five S-mark sessions (candidates in *Blockers*; one more from this
check in `notes/harness/incidents.md`). When an attack starts, its `state.md` is that
lemma's status surface and this note carries a two-line pointer to it, edited by the PI. **On a
future HIT the phase-boundary consequences are the USER's call** (`PHASE-BOUNDARIES.md`,
against the 2026-07-24 no-split adjudication), surfaced with an estimate, never unilateral.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

### Phase-local choices

- **2026-09-23 — W4 REOPENED (user); the hold lifted, staged, for the W4 wrapper and W4-L4b.**
  Tasks T0–T4: `notes/pencil/W4-reopen.md`; verbatim `notes/pencil/adjudications.md`.
- **2026-09-23 — strategy re-think (PI-requested; ranking delegated):** census of the main component
  first, T1's Lean deferred, `kres` held; W4 carries three kernels. `notes/pencil/W4-reopen.md` *START HERE*.
- **2026-09-17 — both attack briefs CHECKED against the tree** (PI-directed; no new mathematics;
  one incident: file:line pointers rot within days, cite by declaration name).
- **2026-09-16 — item 5 LANDED: the kernels take the induction hypothesis, `hK` weakens to the
  generic motive, `PencilPair` gains an adjacent-distinct third conjunct (user: (α), one
  slice).** New motive `HasDistinctPencilRealization`, *never* a conjunct on
  `HasPencilPanelRealization` (refuted; breaks `lem:pencil-self-dual`). Cut arm done once with a
  `Prop` flag. (c) adder `pencilNondegFeasible_of_le_of_triangleFree`. New informal W4
  obligation. Record: `notes/Phase39-design.md` § *Kernel restatement*; verbatim
  `notes/pencil/adjudications.md`; W4 `notes/pencil/workbook/W4.md`.
- **2026-09-16 — item 6's D1–D5 SETTLED (user).** Verdicts and rationale: *Blockers* (the
  D1–D5 entry). Verbatim: `notes/pencil/adjudications.md`.
- **2026-09-16 — the S-mark brief rewrite LANDS** (agent transcription, a user-sanctioned
  exception to the `/review-attack` rewrite path; §§2, 3, 6; O8 deleted (α)). Checked 2026-09-17.
- **2026-09-16/17 — item 6's Layers A/B and C1ℓ–C3ℓ LAND by transcription plus one recon
  spike; no new decisions** (A1–A5 `Deficiency.lean`/`SplitOffDeficiency.lean`; B1–B7
  `Bricks.lean` `section TwoCutCarriers`; C1ℓ–C3ℓ `Molecule/Pencil/TwoCut.lean`; A6 deferred by
  D2). Per-leaf routes, dropped instances and refuted claims are recorded **once** in the
  *Lemma checklist*; blueprint debt extended per leaf (*Blockers*).
- **2026-09-17 — C4ℓ `pencilLoss_vertexTwoCut` LANDS, closing Layer C and item 6's Lean track**
  (except the deferred A6 and the factoring item): A5+B6 only, `hnonadj` binding only through
  A5 — detail in the *Lemma checklist* C4ℓ entry; blueprint debt fully listed, no chapter (D5).
- **2026-09-16 — the Lean hold is LIFTED for item 6 (user); its carrier recon RECORDED**
  (coordinator-accepted) — 6a proved, 6b false without `¬ G.Adj u v`, the slot-trace's 6c claim
  corrected. Leaves/sites *Lemma checklist*; record `notes/Phase39-design.md` § *Item-6 carrier
  recon*; verbatim `notes/pencil/adjudications.md`.
- **2026-09-16 — (GR-10) RE-SCOPED (user)** to the char-2 probe, the grid route a documented
  fallback (R2 plus (d) drop proviso (P) from `hK`); the probe CLOSED 2026-09-23. Verbatim
  `notes/pencil/adjudications.md`.
- **2026-09-16 — item 4 (the R2 recon) verdict RECORDED (coordinator-accepted).** (a) rank
  bridge exact, (c) side feasibility by reconstruction, (d) `hK` weakening confirmed; (b) left as
  the PI's (α)/(β) call, (GR-10) scope as the user's. Record `notes/Phase39-design.md` § *R2
  recon*.
- **2026-09-16 — S-mark route R2 adopted; both kernels get the induction hypothesis** (PI, on
  review 2's recommendation) — R1's obligations were never consumed; the split-off antecedent at
  the generic point supplies them (S14(iii, v)). Verbatim `notes/pencil/adjudications.md`.
- **2026-09-15 — the field hypothesis: option C (PI).** The reduction stays `[Infinite K]`; the
  hypothesis lives on the kernel lemmas at the weakest form each proof needs — (K) via the grid
  `[Infinite K] [NeZero (2 : K)]`, (K-bare) via the 2-cut composition `[Infinite K]` (interim
  `IsAlgClosed K`) — and the corollary inherits them. Neither route needs characteristic 0.
  Record: `notes/Phase39-design.md` § *Field-hypothesis recon*; chapter
  `fmlnote:pencil-conditional-realization-pair-field`.
- **2026-09-15 — items 1–2 PINNED, then LANDED (design pass, `notes/Phase39-design.md`
  § *Lean-track design pass*).** Cycle carrier `Fin m` data + predicate `Graph.GirthGE` (not the
  Matroid package's `IsCycle`, not an `ℕ∞` girth); chain carrier `WList` paths in ∃-statements;
  two new files. Findings: the consumed shape is a trichotomy (V3); `w ≁ v` only for `m ≤ 4`
  (V4); any hub ⇒ girth `≥ 7` (V5). All eight `sec:pencil-girth-chain` nodes green that day.
- **2026-09-15 — the Lean hold is LIFTED for checklist items 1–3 (user).** Girth lemmas,
  consumed-shape normal form, the field-hypothesis decision (recon first, PI decides). Verbatim
  `notes/pencil/adjudications.md`.
- **2026-09-15 — the research loop is RETIRED; attack tracks replace directions.** Six weeks and
  127 directions moved no carried item; coordinator effort ~55 % process. Rules: `HARNESS.md`;
  mechanics `/attack`, `/review-attack`, `/harness-review`; record `notes/harness/incidents.md`.
- **2026-08-05 — Lean hold (user).** Lean parked while ideas are sought; every script the
  project runs is committed (`notes/scripts/README.md`).
- **2026-08-02 — W4 route 3, packaging (b)** adjudicated; (K-res) a byte-identical sibling of
  `hK`; the build decomposed, then parked by the hold (reopened 2026-09-23, above).
- **2026-07-24 — the phase stays open** rather than splitting at the three carried items.
- **Pre-arc Lean decisions (W0–W5, 2026-07-23 → 08-04)** — `notes/Phase39-design.md` and
  `notes/pencil/arc-worklog.md` *Decisions made*; the R1–R3 recon verdicts are
  `notes/pencil/structure.md` §"The question and the opening recon".

### Promoted to HARNESS / DESIGN / TACTICS

- *Evidence and reproducibility rules distilled from the arc* → `HARNESS.md` *Evidence*,
  *Reproducibility* (the retired manual `RESEARCH-ARC.md` is the provenance).
- *Both triggers of `linter.style.show`, plus the `haveI`-on-a-`Prop`-class sibling* →
  `TACTICS-GOLF.md` § 12; FRICTION *Two Lean style linters cost a build cycle each*.
- *`Submodule.span_image` won't fire when the image's function is an unbundled lambda —
  `Set.image_congr'` to the bundled coe first* → TACTICS-GOLF § 22; FRICTION [idiom] entry.
- *`LinearIndependent.pair_map`* (injective linear map preserves pair independence)
  → mirrored, `CombinatorialRigidity/Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`.

### The research arc's record (2026-08-05 → 09-13)

- **127 one-line verdicts**, the (BE-14) and `hK` lanes' per-landing detail, the ranked carried
  items and route σ: `notes/pencil/arc-worklog.md` (verbatim), `notes/pencil/fanout.md`
  §"<CODE>", `notes/pencil/structure.md` blocks 8–14, `notes/pencil/strategy.md` §8.

## Citations (transcribed, project-canonical sources)

**RELOCATED 2026-09-01** (verbatim) to `notes/pencil/structure.md` §"Citations — the phase's
verified bibliography" (block 7), which carries the per-source venue data and the
verification dates. A direction or attack that verifies a new source adds it there.
