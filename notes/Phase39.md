# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** in progress — the phase stays OPEN (2026-07-24 adjudication). The target is
**`PencilPair K 3 G`**; the landed theorem
`pencil_conjecture_of_hcontract_hK_hbareSplit_of_card` (`Molecule/Pencil/Escape.lean`) derives
it from exactly **three carried hypotheses**: **`hcontract`** (W4; Lean build decomposed and
parked by the **2026-08-05 Lean hold**; informal argument closed), **`hK`** (kernel (K)) and
**`hbareSplit`** (kernel (K-bare)). W0–W3, W5 (L0–L7), `hsplit` and `hfresh` are Lean-closed.

**Two tracks since 2026-09-15.** *(1)* **Attack track** — research on the two open kernels,
one agent per lemma under `/attack <name>` (`HARNESS.md`); each lemma's status surface is
`notes/attacks/<name>/state.md`. **DRAFT one-page briefs** for **S-mark** (the 2-cut
composition lemma, all that stands before `hbareSplit`) and **(GR-10)** (uniform colouring,
the crux of `hK` on the tight stratum) are at `notes/attacks/{smark,gr10}/brief.md`,
**PI-reviewed 2026-09-15 and committed**. *(2)* **Lean track** — this note and `/coordinate-phase 39`:
formalize the reductions and foundations the attacks stand on, cruxes carried as
hypotheses, no `sorry`; **the Lean hold is LIFTED (2026-09-15, PI) for checklist items 1–3**
(girth lemmas and consumed-shape normal form, both PINNED; the field-hypothesis decision,
**SETTLED — option C**: the reduction stays `[Infinite K]`, the kernel lemmas take what their
proofs need); items 4–10 stay parked.

**The retired research arc** (2026-08-05 → 09-13: 127 directions, nineteen strategy passes,
under a coordinator loop retired 2026-09-15 — `notes/harness/incidents.md`). Its final
work-log state is **verbatim** at `notes/pencil/arc-worklog.md`; per-direction specs and
verdicts `notes/pencil/fanout.md`; the *State of (K)* gap map `notes/pencil/workbook/gapmap.md`
(read with `python3 notes/gapmap.py`, never `sed`/`grep`); claims via `python3 notes/ledger.py`.
**Standing result at retirement: `hK` is not closer** — (GR-15)/(GR-10) OPEN since 2026-08-07,
(BE-14) one lemma (S-mark) away since 2026-08-26; **no content commit under
`Molecule/Pencil/` since 2026-08-05.**

## Current state

**Next concrete step: session 3 of `/attack smark` and session 1 of `/attack gr10`**, each a
main session in its own worktree (`notes/attacks/README.md`). S-mark has two sessions and its
first `/review-attack` (all 2026-09-15): session 1's girth-5 check did delete the
coincident-flag arm; the review found the consumer's shape narrower than the brief recorded
(the *consumed-shape disjunct* below) and re-aimed the attack's O4 at it —
`notes/attacks/smark/state.md` is the status surface, and session 3 verifies the review's
arithmetic (workbook S10) before building on it. (GR-10) has not started; session 1 writes
its `state.md` from the template — **and its backlog takes the char-2 probe** (PI 2026-09-15,
deferred to the attack track; spec in `notes/Phase39-design.md` § *Field-hypothesis recon*,
last subsection): the census shapes' chart matrix over `F_{2^k}` and a few odd `F_p` — a
full-rank hit is a proof of `hK` at that shape in that characteristic; systematic `F_{2^k}`
misses would be evidence the target itself fails in characteristic 2 and a re-pin trigger for
the headline typeclass. The attack decides when to run it.
**Lean track (hold lifted 2026-09-15 for items 1–3):** items 1–2 are **PINNED** (design pass
2026-09-15, `notes/Phase39-design.md` § *Lean-track design pass*; eight red nodes in
`blueprint/src/chapter/pencil.tex` § *Girth and degree-two chains*, the chapter's first). **The
next concrete Lean commit is the first build, leaf G1 + G2:** the new file
`Molecular/Induction/Girth.lean` with `Graph.GirthGE` and the spanning-short-cycle lemma,
pinning `def:girth` / `lem:pencil-short-cycle-spanning` (S1/P2/B1; build order in the §). Item 3
(the field hypothesis) is **SETTLED** (PI, option C, 2026-09-15): the reduction stays
`[Infinite K]`; the hypothesis lives on the kernel lemmas (`notes/Phase39-design.md`
§ *Field-hypothesis recon*; chapter `fmlnote:pencil-conditional-realization-pair-field`).
Builds need `LAKE_CACHE_DIR` set
(`notes/ToolchainBumps.md` *Environment*; session-wide via the gitignored
`.claude/settings.local.json`).

**Lean, landed:** the statement layer and stratum self-duality (W0), the KT Lemma 5.3/5.4
base cases (W1), the two-pencil layer (W2), W3, the whole of W5 (L0–L7, 2026-07-24 → 07-30),
`hsplit` in full and `hfresh`'s mechanical discharge (W5-L7c). **Lean, parked:** the W4 build
(route 3, packaging (b), adjudicated 2026-08-02; fully decomposed, gates N8/N9/N10/N10b
passed; canonical homes `notes/Phase39-design.md` §§ *W4 decomposition recon* / *W4-L4
identification recon* and `notes/pencil/workbook/W4.md`).

**Five foundations findings from the briefs and the first review** (the writers' readings, to
be checked by the PI; this paragraph is a summary — the owning text is the brief section
named, and each is a Lean checklist item below). **Frame gap:** the S-mark induction does not
cover the partially assembled core of a 3-block with ≥ 2 children, and no corpus clause owns
that obligation (`notes/attacks/smark/brief.md` §3 *Why it suffices*, §6 idea 2); every version
of the composition lemma is vacuous without it — **PI decision pending** (*Blockers*).
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
**Independence proviso:** the chain from (GR-15) to `hK` needs each hub's
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

- [ ] **Girth lemmas** — **PINNED** (design pass 2026-09-15, `notes/Phase39-design.md`
  § *Lean-track design pass*, leaves G1–G4; red nodes `def:girth`,
  `lem:pencil-short-cycle-spanning`, `lem:pencil-girth-of-hub`,
  `lem:pencil-closed-nbhd-girth-five`). Carrier: `Fin m` cycle data and the predicate
  `Graph.GirthGE` (V1). Sharpened against the review: *any* vertex of degree `≥ 3` forces girth
  `≥ 7`, and no hub + 2EC makes `G` a cycle of any length `≥ 5` (V5); `|N[v] ∩ N[h]| ≤ 2` needs
  only girth `≥ 5` and `v ≠ h` (V6). Target: new `Molecular/Induction/Girth.lean` (G1–G3) and
  `Motive.lean` (G4). **First build: G1 + G2.**
- [ ] **Consumed-shape normal form** — **PINNED** (same §, leaves M1–M4′; red nodes
  `lem:pencil-chain-walk-extension`, `lem:pencil-degree-two-chain`,
  `lem:pencil-chain-side-connected`, `lem:pencil-chain-side-distance`). Carrier: `WList` paths
  in ∃-statements, no new record (V2); the builder is E2d-4 un-capped and 2EC-sourced. **Two
  corrections to the review's shape:** it is a *trichotomy* — the chain can close at a
  **single hub** (a cycle through a cut vertex; witness two 7-cycles sharing a vertex, inside
  `hbareSplit`'s hypotheses, outside the S-mark Lemma's 2-connected scope — V3, *Blockers*);
  and `w ≁ v` holds only for `m ≤ 4`, the general clause being `dist_{G−chain}(w, v) ≥ 6 − m`
  (V4). Target: new `Molecular/Induction/ForestSurgery/MaximalChain.lean`.
- [x] **The field hypothesis** — **SETTLED 2026-09-15 (PI, option C)**: the reduction stays
  `[Infinite K]` (its proof uses no characteristic); kernel (K) via the grid expects
  `[Infinite K] [NeZero (2 : K)]` (`char ≠ 2` — the quadric and the polarity's eigen-splitting
  collapse in characteristic 2); kernel (K-bare) via the 2-cut composition expects
  `[Infinite K]` in witness form, interim `IsAlgClosed K`; the corollary inherits the kernels'
  hypotheses. Record: `notes/Phase39-design.md` § *Field-hypothesis recon (2026-09-15)*;
  chapter `fmlnote:pencil-conditional-realization-pair-field`. The char-2 probe is the (GR-10)
  attack's (*Current state*).
- [ ] **Deficiency laws** (BINDUC's, cited by 45 claims through (BE-22)): 3-connected ⇒
  `def₂ = 0`; the 2-cut law `def₃(G) = f₁ + f₂ − min(δ₁ + δ₂, 6)`; the fibre-product identity
  `dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁ + ρ̄₂)`; the welded bound `ρ_i ≤ δ_i + a_i` with
  equality iff `H_i/uv` attains (all three re-derived at the 2026-09-15 review, workbook
  S10(ii)); plus (review) the two pendant laws — deleting a degree-1 vertex drops `def₃` by
  exactly `1`, and welded `g(H) = max(g(H − u), f_sep(H − u) − 5)` — and the joint count
  `dim M_U(H) ≥ 6 + max(g, f + dim U − 6)` (workbook S6(ii), S7(iii);
  `partitionDef_split_of_sides`, `exists_sides_separated_partitionDef_le` are the pieces).
  Makes the composition criterion and the chain-length arithmetic (S10) exact.
- [ ] **`hK` on the tight stratum from grid vanishing**, the colouring statement as
  hypothesis: decoupling, rank formula, Vandermonde, chart step, descent. Decides whether the
  **independence proviso** is a hypothesis of the crux (`notes/attacks/gr10/brief.md` §2
  *Proviso (P)*). Substantial: the chart
  machinery (`IsFin3SelectorOf`, `cross₃`, `pencilRow`) exists; the grid geometry does not.
- [ ] **Tree-triple ⇒ `dim Z = 0`**, and the circular-ladder family (GUNIZERO's uniform
  instance) as a formal witness.
- [ ] **Long-chain composition** (review 2026-09-15; optional). If the hub-terminal side attains
  and welded-attains at `(w, v)` and the ear's `≥ 6` hinge lines span `Λ²K⁴` (an explicit
  configuration, chain length `m ≥ 5`), the composed graph attains — the fibre-product identity
  plus a construction, no genericity. One arm of `hbareSplit`, conditional on the induction
  frame (workbook S10, `m ≥ 5`).
- [ ] **The 3-block induction skeleton** with the composition lemma as hypothesis. Decides
  the **frame gap** (`notes/attacks/smark/brief.md` §3, §6 idea 2). Heavy: 3-block trees are
  not in Mathlib.
- [ ] **W4 build**, when commissioned: W4-L4b (`exists_degree_two_of_co1_rigid`, pinned and
  spike-elaborated), then order-flexibly W4-L1/L2/L3′/L5; residual carry `hnoGood'`
  (non-vacuous — `|V| = 19` witness — so branch 4 needs content).
- [ ] **Reverse arms of the W0 transport** (need a `complementIso` involution lemma) — off
  every critical path (§(K-σ) *Step σ6*).

## Blockers / open questions

- **The Lean hold (2026-08-05) is the user's**; lifting it for named items is a PI call, made
  per item. **Lifted 2026-09-15 for checklist items 1–3** (verbatim record
  `notes/pencil/adjudications.md`); items 4–10 stay parked.
- **PI decision pending (design pass 2026-09-15): the cut-vertex case of the consumed shape**
  (`notes/Phase39-design.md` § *Lean-track design pass*, V3). The maximal degree-2 chain through
  the split vertex can close at a *single* hub; `hbareSplit`'s hypotheses include that case, the
  S-mark Lemma (2-connected `G`) does not, and the brief's §3 *Consumed shape* says 2-cut. Decide
  whether the brief is amended (attack track) and which informal clause — induction case (d), cut
  vertex — owns the composition there; the Lean normal form (`lem:pencil-degree-two-chain`) states
  all three cases already.
- **Each attack's first move is a reading check, not a sweep:** the girth-5 restriction and
  the frame gap for S-mark; the independence proviso for (GR-10). Session 1 should settle or
  scope these before choosing a route. (S-mark's session 1 did the girth check but not a
  verbatim diff of the consuming hypotheses; the dropped disjunct was caught at review —
  `notes/harness/incidents.md` 2026-09-15.)
- **PI decision pending (S-mark review 2026-09-15): the induction frame.** Every version of the
  composition lemma assumes welded attainment of the sides at generic flags, supplied by an
  induction no brief owns (the *frame gap*; `notes/attacks/smark/brief.md` §3, §6 item 2;
  state file *Worries*). Decide whether the frame gets its own brief, or is folded into the
  *3-block induction skeleton* checklist item; S-mark's O5/O6 wait on it.
- **The (K-res) wave** (a kernel of `hK`'s difficulty class on the complementary habitat,
  scoped RESGRID, cheap items spent RPOOL) stays a user call; route σ is a live candidate
  that is not a route to (K-res). Detail: `notes/pencil/arc-worklog.md` *Hand-off*.
- **One L5 residual constrains statements:** feasibility propagation as a proposition is
  refuted for any purely combinatorial (`≤ 3`-closedHubNbhd) criterion
  (`not_pencilNondegFeasible_of_triangle_two_hubs`).
- **Harness:** none open; incidents go to `notes/harness/incidents.md`, one line each, and
  `HARNESS.md` changes only in `/harness-review`.

## Hand-off / next phase

**The phase stays OPEN.** Next concrete task: *Current state*'s first paragraph (both tracks).
When the first attack starts, its `state.md` becomes that lemma's status surface and this note
carries a two-line pointer to it, edited by the PI. The hold is lifted for checklist items 1–3
(2026-09-15; item 3 settled, items 1–2 pinned): Lean commits land under `/coordinate-phase 39` in forward mode against the pencil
chapter's red nodes in the design §'s *Build order* (first: G1 + G2, new
`Molecular/Induction/Girth.lean`), with any crux as a hypothesis; a later lift for
items 4–10 follows the same rule. **On a future HIT
the phase-boundary consequences are the USER's call** (`PHASE-BOUNDARIES.md`, against the
2026-07-24 no-split adjudication), surfaced with an estimate, never unilateral.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

### Phase-local choices

- **2026-09-15 — the field hypothesis: option C (PI).** The reduction stays `[Infinite K]`; the
  hypothesis lives on the kernel lemmas at the weakest form each proof needs — (K) via the grid
  `[Infinite K] [NeZero (2 : K)]` (`char ≠ 2`), (K-bare) via the 2-cut composition `[Infinite K]`
  in witness form (interim `IsAlgClosed K`) — and the unconditional corollary inherits them.
  Neither informal route needs characteristic 0; no landed proof uses one. Char-2 probe deferred
  to the (GR-10) attack. Verbatim: `notes/pencil/adjudications.md`; record:
  `notes/Phase39-design.md` § *Field-hypothesis recon*; chapter: `fmlnote:pencil-conditional-realization-pair-field`.
- **2026-09-15 — items 1–2 PINNED (design pass, `notes/Phase39-design.md` § *Lean-track design
  pass*).** Cycle carrier `Fin m` data + predicate `Graph.GirthGE` (not the Matroid package's
  `IsCycle`/`IsCyclicWalk`, not an `ℕ∞` girth); chain carrier `WList` paths in ∃-statements (no
  `ChainData` variant record yet); two new files, since `Deficiency.lean`/`Operations.lean` are past
  the tripwire. Findings: the consumed shape is a trichotomy (cut-vertex closure, V3); `w ≁ v` only
  for `m ≤ 4` (V4); any hub ⇒ girth `≥ 7` (V5).
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
