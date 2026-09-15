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
hypotheses, no `sorry`; **parked by the Lean hold** until the PI names items to lift it for.

**The retired research arc** (2026-08-05 → 09-13: 127 directions, nineteen strategy passes,
under a coordinator loop retired 2026-09-15 — `notes/harness/incidents.md`). Its final
work-log state is **verbatim** at `notes/pencil/arc-worklog.md`; per-direction specs and
verdicts `notes/pencil/fanout.md`; the *State of (K)* gap map `notes/pencil/workbook/gapmap.md`
(read with `python3 notes/gapmap.py`, never `sed`/`grep`); claims via `python3 notes/ledger.py`.
**Standing result at retirement: `hK` is not closer** — (GR-15)/(GR-10) OPEN since 2026-08-07,
(BE-14) one lemma (S-mark) away since 2026-08-26; **no content commit under
`Molecule/Pencil/` since 2026-08-05.**

## Current state

**Next concrete step: session 1 of `/attack smark` and of `/attack gr10`** (the PI's call,
2026-09-15: both briefs worth a try), each a main session in its own worktree
(`notes/attacks/README.md`); session 1 writes `state.md` from the template. Recommended
order if serial: S-mark first, because its first check (the girth-5 restriction) may delete
an arm of the problem. Optional in parallel: lift the Lean hold for checklist items 1–2 only.

**Lean, landed:** the statement layer and stratum self-duality (W0), the KT Lemma 5.3/5.4
base cases (W1), the two-pencil layer (W2), W3, the whole of W5 (L0–L7, 2026-07-24 → 07-30),
`hsplit` in full and `hfresh`'s mechanical discharge (W5-L7c). **Lean, parked:** the W4 build
(route 3, packaging (b), adjudicated 2026-08-02; fully decomposed, gates N8/N9/N10/N10b
passed; canonical homes `notes/Phase39-design.md` §§ *W4 decomposition recon* / *W4-L4
identification recon* and `notes/pencil/workbook/W4.md`).

**Four foundations findings from the briefs** (the writers' readings, to be checked by the
PI; this paragraph is a summary — the owning text is the brief section named, and each is a
Lean checklist item below). **Frame gap:** the S-mark induction does not cover the partially
assembled core of a 3-block with ≥ 2 children, and no corpus clause owns that obligation
(`notes/attacks/smark/brief.md` §3 *Why it suffices*, §6 idea 2). **Girth-5 restriction:** at
girth ≥ 5 the coplanarity closure never fires, so the coincident-flag arm the last six rounds
worked may be deletable by inducting inside girth-5 graphs (`smark/brief.md` §6 idea 1, §7).
**Independence proviso:** the chain from (GR-15) to `hK` needs each hub's
closed-hub-neighbourhood points independent, which the 40 742- and 166 088-shape sweeps did
not certify (`notes/attacks/gr10/brief.md` §2 *Proviso (P)*, §3). **Field mismatch:** the
target is stated over any infinite field while the informal route is characteristic 0 (both
briefs, §3). The briefs are committed (PI-reviewed 2026-09-15).

**Standing user adjudications that bind:** 2026-07-24 the phase stays open; 2026-08-05 the
Lean hold, and *"all of the scripts we run [are] committed"*; 2026-09-03 *"we should
ultimately be driven by the math … we shouldn't lock [declined directions] out forever"* and
*"if the current approach seems to be getting in a rut then it's time to reprioritize"*;
2026-09-15 the coordinator loop retired in favour of attack tracks. Verbatim record:
`notes/pencil/adjudications.md`.

## Lemma checklist — the Lean track

*All parked by the hold; ranked cheapest and most decision-relevant first; each carries its
crux as a HYPOTHESIS, never a `sorry`.*

- [ ] **Girth lemmas.** No proper rigid subgraph ⇒ girth ≥ 7 (a ≤ 6-cycle of bodies is
  rigid; check whether the tight-stratum analysis already carries it); girth ≥ 5 ⇒
  `|N[v] ∩ N[h]| ≤ 2` for distinct hubs, so the coplanarity closure never forces `π_u = π_v`.
  Decides the **girth-5 restriction** (`notes/attacks/smark/brief.md` §6 idea 1).
- [ ] **The field hypothesis.** Decide whether the phase target scopes to characteristic 0
  (KT work over ℝ; the grid route descends through a nonvanishing ℤ-polynomial) or someone
  owes a positive-characteristic argument; record it in the blueprint chapter. The **field
  mismatch** (both briefs, §3; `Escape.lean` carries only `[Infinite K]`).
- [ ] **Deficiency laws** (BINDUC's, cited by 45 claims through (BE-22)): 3-connected ⇒
  `def₂ = 0`; the 2-cut law `def₃(G) = f₁ + f₂ − min(δ₁ + δ₂, 6)`; the fibre-product identity
  `dim M(G) = dim M₁ + dim M₂ − 6 − dim(ρ̄₁ + ρ̄₂)`; the welded bound `ρ_i ≤ δ_i + a_i` with
  equality iff `H_i/uv` attains. Makes the composition criterion exact.
- [ ] **`hK` on the tight stratum from grid vanishing**, the colouring statement as
  hypothesis: decoupling, rank formula, Vandermonde, chart step, descent. Decides whether the
  **independence proviso** is a hypothesis of the crux (`notes/attacks/gr10/brief.md` §2
  *Proviso (P)*). Substantial: the chart
  machinery (`IsFin3SelectorOf`, `cross₃`, `pencilRow`) exists; the grid geometry does not.
- [ ] **Tree-triple ⇒ `dim Z = 0`**, and the circular-ladder family (GUNIZERO's uniform
  instance) as a formal witness.
- [ ] **The 3-block induction skeleton** with the composition lemma as hypothesis. Decides
  the **frame gap** (`notes/attacks/smark/brief.md` §3, §6 idea 2). Heavy: 3-block trees are
  not in Mathlib.
- [ ] **W4 build**, when commissioned: W4-L4b (`exists_degree_two_of_co1_rigid`, pinned and
  spike-elaborated), then order-flexibly W4-L1/L2/L3′/L5; residual carry `hnoGood'`
  (non-vacuous — `|V| = 19` witness — so branch 4 needs content).
- [ ] **Reverse arms of the W0 transport** (need a `complementIso` involution lemma) — off
  every critical path (§(K-σ) *Step σ6*).

## Blockers / open questions

- **The Lean hold (2026-08-05) is the user's** and parks every checklist item above; lifting
  it for named items is a PI call, made per item.
- **Each attack's first move is a reading check, not a sweep:** the girth-5 restriction and
  the frame gap for S-mark; the independence proviso for (GR-10). Session 1 should settle or
  scope these before choosing a route.
- **The (K-res) wave** (a kernel of `hK`'s difficulty class on the complementary habitat,
  scoped RESGRID, cheap items spent RPOOL) stays a user call; route σ is a live candidate
  that is not a route to (K-res). Detail: `notes/pencil/arc-worklog.md` *Hand-off*.
- **One L5 residual constrains statements:** feasibility propagation as a proposition is
  refuted for any purely combinatorial (`≤ 3`-closedHubNbhd) criterion
  (`not_pencilNondegFeasible_of_triangle_two_hubs`).
- **Harness:** none open; incidents go to `notes/harness/incidents.md`, one line each, and
  `HARNESS.md` changes only in `/harness-review`.

## Hand-off / next phase

**The phase stays OPEN.** Next concrete task: *Current state*'s first paragraph. When the
first attack starts, its `state.md` becomes that lemma's status surface and this note carries
a two-line pointer to it, edited by the PI. When the hold lifts for a checklist item, the next
Lean commit is the first unchecked box above, landed under `/coordinate-phase 39` in forward
mode against the pencil blueprint chapter, with the crux as a hypothesis. **On a future HIT
the phase-boundary consequences are the USER's call** (`PHASE-BOUNDARIES.md`, against the
2026-07-24 no-split adjudication), surfaced with an estimate, never unilateral.

## Adjacent directions (orientation only, not this phase)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`), the
bar-joint-side analog, is next; the unqueued survey, incl. IDENT-PANEL, is `notes/IdeaBacklog.md`.

## Decisions made during this phase

### Phase-local choices

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
