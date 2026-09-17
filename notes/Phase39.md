# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`**; the landed theorem
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) derives
it from exactly **three carried hypotheses**: **`hcontract`** (W4; Lean build decomposed and
parked by the **2026-08-05 Lean hold**; informal argument closed), **`hK`** (kernel (K)) and
**`hbareSplit`** (kernel (K-bare)). W0–W3, W5 (L0–L7), `hsplit` and `hfresh` are Lean-closed.

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
hypothesis option C). **Next: the R2 Lean round** — checklist item 4 (a read-only recon, first)
and item 5 (the kernel-restatement slice), the Lean hold LIFTED for both by the PI 2026-09-16;
items 6–12 (the 2026-09-15 numbering's 4–10) stay parked by the hold.

**The retired research arc** (2026-08-05 → 09-13: 127 directions, nineteen strategy passes,
under a coordinator loop retired 2026-09-15 — `notes/harness/incidents.md`). Its final
work-log state is **verbatim** at `notes/pencil/arc-worklog.md`; per-direction specs and
verdicts `notes/pencil/fanout.md`; the *State of (K)* gap map `notes/pencil/workbook/gapmap.md`
(read with `python3 notes/gapmap.py`, never `sed`/`grep`); claims via `python3 notes/ledger.py`.
**Standing result at retirement: `hK` is not closer** — (GR-15)/(GR-10) OPEN since 2026-08-07,
(BE-14) one lemma (S-mark) away since 2026-08-26; **no content commit under
`Molecule/Pencil/` since 2026-08-05.**

## Current state

**Next concrete step: the R2 Lean round for S-mark — checklist item 4 (a read-only recon)
first, then item 5 (the kernel-restatement slice) — under `/coordinate-phase 39`; then the
S-mark brief is rewritten against the landed statements (*Hand-off*), and `/attack smark`
resumes at session 6.** S-mark has five sessions (2026-09-15/16) and two reviews. Review 1
(2026-09-15) re-aimed the attack at the consumed shape (the `hbareSplit` disjunct the brief had
dropped; workbook S10). Sessions 3–4 then attacked profile bounds on an arbitrary side
((O4′)/(O4″)) that turned out not to be consumed; session 5 re-read the consumer and found the
brief's second misreading — the kernels' antecedent `HasPencilRealization K 3 (G.splitOff …)`
is `H′ ∪ ear_{m−1}` attaining (`splitOff` deletes the degree-2 vertex and re-adds the edge),
not a discardable "realization of `G − x`" — and route R2 (workbook S14). Review 2
(2026-09-16, notes at workbook S15) verified the consumer reading against `Escape.lean` and
the S14 arithmetic, endorsed R2, and recorded three statement-level questions for the Lean
track (*Blockers*, checklist item 4). `notes/attacks/smark/state.md` is the status surface;
session 6 waits for the brief rewrite. (GR-10) has not started — **and should wait**: R2 covers
`hK`'s arm too (`smark/state.md` *Statement*; S14(iii), (vii)), so after the item-4 recon the PI
decides whether the grid route is still needed, re-scoped, or retired (*Blockers*). If it runs, it
writes its `state.md` from the template — **and its backlog
takes the char-2 probe** (PI 2026-09-15, deferred to the attack track; spec in
`notes/Phase39-design.md` § *Field-hypothesis recon*, last subsection): the census shapes' chart matrix over `F_{2^k}` and a few odd `F_p` — a
full-rank hit is a proof of `hK` at that shape in that characteristic; systematic `F_{2^k}`
misses would be evidence the target itself fails in characteristic 2 and a re-pin trigger for
the headline typeclass. The attack decides when to run it.
**Lean track — checklist items 1–3 are DONE (2026-09-15); items 4–5, the R2 Lean round, are
the queued work (PI 2026-09-16).** The design pass (`notes/Phase39-design.md` § *Lean-track design pass*) pinned items 1–2
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
`fmlnote:pencil-conditional-realization-pair-field`). **Items 6–12 stay parked by the hold**;
the R2 round (items 4–5) is the next Lean work, hold lifted 2026-09-16 (*Hand-off* for the order). Builds need `LAKE_CACHE_DIR` set (`notes/ToolchainBumps.md`
*Environment*; session-wide via the gitignored `.claude/settings.local.json`).

**Lean, landed:** the statement layer and stratum self-duality (W0), the KT Lemma 5.3/5.4
base cases (W1), the two-pencil layer (W2), W3, the whole of W5 (L0–L7, 2026-07-24 → 07-30),
`hsplit` in full and `hfresh`'s mechanical discharge (W5-L7c). **Lean, parked:** the W4 build
(route 3, packaging (b), adjudicated 2026-08-02; fully decomposed, gates N8/N9/N10/N10b
passed; canonical homes `notes/Phase39-design.md` §§ *W4 decomposition recon* / *W4-L4
identification recon* and `notes/pencil/workbook/W4.md`).

**Six foundations findings from the briefs and the two reviews** (the writers' readings, to
be checked by the PI; this paragraph is a summary — the owning text is the brief or workbook
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
*[formalization 2026-09-15]*; workbook S11).

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
- [ ] **R2 recon (item 4; read-only, before item 5; hold lifted PI 2026-09-16).** Three
  definition-body questions the S-mark route R2 depends on, each answered against the Lean
  source with the line pinned. **(a) The rank bridge** — the attack's "attains"
  (`dim M(G) = 6 + def₃(G)` at a configuration, five rows per hinge) against the Lean's
  `finrank (span rigidityRows) = 6(|V|−1) − deficiency 3` (`HasPencilRealization`,
  `Statement.lean:103`); "unchecked" in the brief since it was written, and every line of S14 is
  a rank statement. **(b) The bare variety at coincident points** — the bare motive quantifies
  over a `BodyHingeFramework` carrying its own hinge extensor per edge, constrained only to pass
  through both endpoint points, so at coincident adjacent points the hinge is any line in both
  panel planes: can such a degenerate witness attain the target without being a limit of
  nondegenerate configurations? If yes, the bare arm's antecedent certifies nothing about the
  generic point; the plausible fix is a conjunct "adjacent points projectively distinct" on the
  bare motive — assess its ripple through the reduction's arms. **(c) Restriction to the side**
  — do `PencilNondegFeasible K G` and `G.Simple` pass to `G − chain`? The chain ends drop to
  degree 2 there and become non-hubs, where `IsNondegPencilRealization`'s fourth conjunct (points
  independent on a non-hub's closed neighbourhood) bites and the parent's realization never had
  to satisfy it. Decides whether the IH's generic half is usable for the side on the feasible
  arm; argue from the realization, not from hub counts — *Blockers* records that every purely
  combinatorial feasibility criterion is refuted (`not_pencilNondegFeasible_of_triangle_two_hubs`).
  **Optional (d):** whether `hK`'s chart-form conclusion can be weakened to
  `HasGenericPencilRealization K 3 G` — the call site converts to that at once
  (`hasGenericPencilRealization_of_independent_pencilRow_target`) and uses nothing else — which
  is strictly easier to prove and touches the (GR-10) attack's target. Deliverable: a verdict
  per question plus the material for the brief's §3 (*Hand-off*). The recon is read-only; on
  accepting its verdict the coordinator commissions the same agent to **record it** as a
  design-pass commit — a new arc *appended* to `notes/Phase39-design.md` (frozen: append-only,
  plus an arc-index row) and one-line verdicts under this item — so item 5's builder reads it
  from the tree, not from a transcript. Review notes: workbook S15 (v)(c), (vii).
- [ ] **Kernel restatement with the induction hypothesis (item 5; one build slice, after
  item 4; PI decision and hold lift 2026-09-16).** Both `hK` and `hbareSplit` — in
  `pencilPair_of_splitOff_of_habitat` and the `pencil_conjecture_of_hcontract_hK_hbareSplit*`
  wrappers (`Escape.lean`) — gain `(∀ G' : Graph α β, V(G').Nonempty → V(G').ncard < V(G).ncard →
  PencilPair K 3 G') →` ahead of their antecedent, the form `hcontract` already uses; `hIH` is
  in scope at the sole call site, so threading is mechanical. Why (workbook S14(v)): with
  `G = H′ ∪ ear_m`, the split-off antecedent allows `δ′ + a′ ≤ 6 − m` while `G` attaining needs
  `a′ = 0` or `δ′ + a′ ≤ 5 − m`; on a never-attaining side the pinned implication is false, so
  a proof of it as stated would have to prove the conjecture for `G − chain` inside the kernel.
  Surfaces, all in the same commit (per-slice gate; `hbareSplit` is the grep key): **Lean** —
  `Escape.lean` (the two statements in `pencilPair_of_splitOff_of_habitat`, the wrapper and its
  `_of_card` successor, and the section docstrings) and the `hbareSplit` mentions in
  `Molecular/Induction/ForestSurgery/MaximalChain.lean` docstrings; `pencil_conjecture_of_arms_pair`
  (`Pair2.lean`) takes `hsplit`, not the kernels — confirm unaffected. **Blueprint**
  (`pencil.tex`): `thm:pencil-conditional-realization-pair` — its statement prose ("with
  split-off multigraph $G'$ already satisfying the conditioned pair") becomes "given that every
  strictly smaller such graph satisfies the conditioned pair", and its proof's last paragraph
  says how the kernels are fed; `fmlnote:pencil-conditional-realization-pair-kernels` gains the
  S14(v) fact (as pinned, not locally provable); `fmlnote:…-field`'s (K-bare) sentence if the
  witness-form remark shifts. **Design doc** — `notes/Phase39-design.md` is FROZEN: never edit
  residue (ii)'s pinned block in place; append a new arc with the restated forms, add its
  arc-index row, and add a one-line forward pointer beside the old pin. **Status surfaces** —
  this note's header and `ROADMAP.md`'s Phase 39 cell name the kernels as carried; re-read both.
  The `hbareSplit` mentions in `notes/scripts/{kbare,w4}/` are numerics comments, not pins —
  leave them. Apply item 4's verdicts ((b)'s motive conjunct if needed; (d) if adopted). Then
  the S-mark brief is rewritten (*Hand-off*).
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
- **Open for the Lean round (review 2, 2026-09-16): three statement-level questions** —
  checklist item 4 (a)–(c): the rank bridge, the bare variety at coincident points, restriction
  of feasibility to the side. The attack's own structural residue is **O7** — irreducibility of
  the side's configuration space, or matching of the component the antecedent certifies with
  the one the IH certifies — on the bare arm, where some hub has three hub neighbours; no
  driver population has sampled that arm (every census branch has length `≥ 2`), and the
  2026-07-30 (K-bare) recon flagged the same evidence gap.
- **PI decision after the item-4 recon: (GR-10)'s scope.** R2 discharges the consumed step on
  `hK`'s arm as well — `G` attains at the generic point from the IH and the split-off antecedent,
  on the feasible arm where the hub graph has maximum degree `≤ 2` (S14(iii), (vii)) — so if the
  recon's (a) and (c) hold and S14(vii) is written as a proof, the grid/colouring route of
  `notes/attacks/gr10/brief.md` becomes a cross-check or fallback, not the path to `hK`. Decide
  whether (GR-10) session 1 runs as briefed, re-scoped (e.g. to the char-2 probe alone, which is
  about the conjecture's field range rather than the route), or not at all. The gr10 brief
  carries a PI pointer saying to wait, since an attack reads only its brief and state at start.
- **The (K-res) wave** (a kernel of `hK`'s difficulty class on the complementary habitat,
  scoped RESGRID, cheap items spent RPOOL) stays a user call; route σ is a live candidate
  that is not a route to (K-res). Detail: `notes/pencil/arc-worklog.md` *Hand-off*.
- **One L5 residual constrains statements:** feasibility propagation as a proposition is
  refuted for any purely combinatorial (`≤ 3`-closedHubNbhd) criterion
  (`not_pencilNondegFeasible_of_triangle_two_hubs`).
- **Harness:** none open; incidents go to `notes/harness/incidents.md`, one line each, and
  `HARNESS.md` changes only in `/harness-review`.

## Hand-off / next phase

**The phase stays OPEN.** Next concrete task, in order (PI 2026-09-16): **(1) checklist item 4**
— the R2 recon, read-only, under `/coordinate-phase 39` (a `recon-fable`/`recon-opus`
dispatch), answering (a)–(c) against the Lean source with lines pinned, its verdict then recorded in the
tree per item 4's last sentence. **(2) Checklist item 5**
— the kernel-restatement slice, one build commit, applying the recon's verdicts and restating
the design-doc and blueprint pins in the same commit. **(3) The S-mark brief rewrite**, drafted
by an agent from the *landed* declarations and PI-reviewed: §2 = the kernel implication with
the IH as landed; §3 = both kernels quoted verbatim, one hypothesis per line, each operator
glossed from its definition body (`splitOff`, `PencilHub`, `PencilNondegFeasible`,
`HasPencilRealization`), the recon's answers to (a)–(c), and a one-line justification for any
hypothesis the route does not use; §6 = O7 first — build an adjacent-hub side (a hub with three
hub neighbours, each continued by a branch of length `≥ 2` to `w` or `v`, girth `≥ 7`) and
sample from several starts before attempting the tower extension or component matching — then
O8 against the Lean's *actual* bare space as (b) settles it, then O9; every obligation with a
"consumed because" line. **(4)** `/attack smark` session 6 — and `/attack gr10` session 1 only if the PI keeps it after
the recon (*Blockers*) — each a main session in its own worktree. When an attack
starts, its `state.md` is that lemma's status surface and this note carries a two-line pointer
to it, edited by the PI. **On a future HIT the phase-boundary consequences are the USER's
call** (`PHASE-BOUNDARIES.md`, against the 2026-07-24 no-split adjudication), surfaced with an
estimate, never unilateral.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

### Phase-local choices

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

### Promoted to HARNESS / DESIGN

- *Evidence and reproducibility rules distilled from the arc* → `HARNESS.md` *Evidence*,
  *Reproducibility* (the retired manual `RESEARCH-ARC.md` is the provenance).

### The research arc's record (2026-08-05 → 09-13)

- **127 one-line verdicts**, the (BE-14) and `hK` lanes' per-landing detail, the ranked
  carried items and route σ: `notes/pencil/arc-worklog.md` (verbatim), `notes/pencil/fanout.md`
  §"<CODE>", `notes/pencil/structure.md` blocks 8–14, `notes/pencil/strategy.md` §8.

## Citations (transcribed, project-canonical sources)

**RELOCATED 2026-09-01** (verbatim) to `notes/pencil/structure.md` §"Citations — the phase's
verified bibliography" (block 7), which carries the per-source venue data and the
verification dates. A direction or attack that verifies a new source adds it there.
