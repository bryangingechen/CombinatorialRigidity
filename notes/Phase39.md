# Phase 39 — PENCIL: the hinge-pencil molecular conjecture (work log)

**Status:** ✓ complete **as a reduction** (opened 2026-07-23, closed 2026-09-25; PI-sanctioned,
verbatim `notes/pencil/adjudications.md`, the 2026-09-25 "(later)" entry). The target
`PencilPair K 3 G` — bare; adjacent-distinct under `G.Simple`; generic under simplicity plus
feasibility — holds for every spanning multigraph over any infinite field **given two statements
about the main component `X₀` of the pencil configuration space**: `pencil_conjecture_of_X0`
(`Molecule/Pencil/X0.lean`) carries `X0Dist` and `X0Gen` as hypotheses and nothing else (axioms
`[propext, Classical.choice, Quot.sound]`, re-run at the close). **The pencil conjecture itself is
not yet proved**; it is proved outright when **Phase 40** (PENCIL-X0, plan
`notes/Phase40-design.md`; sub-phase 40a open, `notes/Phase40a.md`) discharges the two statements.
The kernels (K-res)/`kres`, (K-c), (K-bare-c) with (α), the rest of the W4 build and the paused
smark attack are held as Phase 40's fallback (its design doc §6); A6, the hub-normalization
factoring item, the D5 blueprint debt and the two `[pending]` exposition entries are deferred to
it (§7). `blueprint/src/chapter/pencil.tex` is fully green (40 theorem-like nodes).

## Current state

**Phase complete.** Checklist item 0 landed 2026-09-25 in four commits: **L0a** the carried
headline (`X0Dist`, `X0Gen`, `pencilPair_of_X0`, `pencil_conjecture_of_X0`; new
`Molecule/Pencil/X0.lean`); **L0b** the non-simple bare case `hasPencilRealization_of_not_simple`
(W4-A, KT Lemma 6.2 without minimality) with its brick
`exists_linearIndependent_extensor_pair_through_given_point` (`Pencil/Statement.lean`), dropping
the carried `hW4A`; **L0c-i** the pre-close chapter pass (`pencil.tex` re-read end to end,
`blueprint/lint.sh` green, `notes/BlueprintExposition.md`'s pencil section written — 6 done, 2
`[pending]` on Phase 40); **L0c-ii** this close (ROADMAP row and §39, the status surfaces, the
deferred items moved, the dispatch log groomed, one stale Lean docstring repointed).

**Lean, landed** (declaration index: `pencil.tex`): W0–W3; W5 (L0–L7, `hsplit`/`hfresh`
discharged); checklist items 1–5 (2026-09-15/16); item 6's Layers A–C (2026-09-16/17); L0a/L0b
(2026-09-25). Sites: `Molecular/Molecule/Pencil/` (`Statement`, `Arms`, `Motive`, `Steer`,
`Habitat`, `Chart`, `Engine`, `Witness`, `Base`, `Reseed`, `Pair`, `Pair2`, `Escape`, `TwoCut`,
`X0`), `Molecular/Induction/Girth.lean`, `Induction/ForestSurgery/MaximalChain.lean`,
`Induction/SplitOffDeficiency.lean`, `Deficiency.lean`, `RigidityMatrix/Bricks.lean`
(`section TwoCutCarriers`). Builds need `LAKE_CACHE_DIR` set (`notes/ToolchainBumps.md`
*Environment*).

**The research arc (2026-08-05 → 09-13; retired 2026-09-15).** 127 directions and nineteen
strategy passes under a coordinator loop, retired in favour of attack tracks (`HARNESS.md`;
`notes/harness/incidents.md`). Its final work-log state is verbatim at
`notes/pencil/arc-worklog.md`; per-direction specs and verdicts `notes/pencil/fanout.md`; the
*State of (K)* gap map `notes/pencil/workbook/gapmap.md` (read with `python3 notes/gapmap.py`,
never `sed`/`grep`); claims via `python3 notes/ledger.py`. Standing result at retirement: `hK` not
closer — (GR-15)/(GR-10) open, (BE-14) one lemma away. The arc's mathematics that *did* land is
the `X₀` route: (MC-89), (MC-133), (MC-157), second-read, in `notes/pencil/workbook/K-main*.md`
§(K-main) — Phase 40's input.

**Standing user adjudications that bound the phase** (verbatim record
`notes/pencil/adjudications.md`): 2026-07-24 the phase stays open; 2026-08-05 the Lean hold and
*"all of the scripts we run [are] committed"*; 2026-09-03 *"we should ultimately be driven by the
math"*; 2026-09-15 the coordinator loop retired; 2026-09-25 the `X₀` route adopted over every
infinite field, Phase 40 minted, the hold lifted for L0 and W4-A, the kernels and smark held, and
Phase 39 to close on L0.

## Lemma checklist — the Lean track

Every item is done or moved. The per-leaf routes, dropped instances and refuted claims that the
in-progress note carried are in git at `e316891f` (this note's last in-progress form); the durable
record is the blueprint chapter and each declaration's docstring.

- [x] **0. L0 — the `X₀` headline and W4-A** (plan `notes/Phase40-design.md` §1; record
  `notes/Phase39-design.md` § *X₀ architecture recon*). L0a, L0b, L0c-i and L0c-ii all landed
  2026-09-25 (*Current state*).
- [x] **1–2. Girth lemmas and the consumed-shape normal form** — 2026-09-15
  (`Induction/Girth.lean`; `Molecule/Pencil/Motive.lean` G4; `ForestSurgery/MaximalChain.lean`);
  all eight `sec:pencil-girth-chain` nodes green. Findings: the normal form is a trichotomy (V3);
  `w ≁ v` only for `m ≤ 4` (V4); any hub ⇒ girth `≥ 7` (V5).
- [x] **3. The field hypothesis** — option C (PI, 2026-09-15): the reduction stays `[Infinite K]`;
  each kernel takes the weakest form its proof needs (`fmlnote:pencil-conditional-realization-pair-field`).
- [x] **4–5. The R2 recon and the kernel restatement** — 2026-09-16: both kernels take the induction
  hypothesis, `hK` concludes the generic motive, `PencilPair` gains the adjacent-distinct conjunct
  (α), `pencilNondegFeasible_of_le_of_triangleFree` (`Steer.lean`), the cut arm done once with a
  `Prop` flag. Record `notes/Phase39-design.md` §§ *R2 recon*, *Kernel restatement*.
- [x] **6. Deficiency laws, Layers A–C** — 2026-09-16/17. A1–A5 (`Deficiency.lean`,
  `SplitOffDeficiency.lean`): the pendant law, the carriers `deficiencyMerged`/`weldPair`/`pairDelta`,
  the vertex 2-cut law `deficiency_eq_of_vertexTwoCut` in `max` and `min` form (needs `¬ G.Adj u v`,
  D1). B1–B7 (`Bricks.lean` `section TwoCutCarriers`): `relScrews`, `jointRows`, `weldedRank`, the
  gluing identity `finrank_span_rigidityRows_vertexTwoCut_eq`. C1ℓ–C4ℓ (`Molecule/Pencil/TwoCut.lean`):
  `pencilLoss`, `weldedLoss`, `pencilLoss_vertexTwoCut`. **Item 6 does not reach S14(i)–(ii)**: the
  S8 ear-profile facts and a configuration-variety layer are outside it (recorded at `e316891f`,
  *Blockers*). **Moved to Phase 40 §7:** A6 (C3, deferred by D2), the shared hub-normalization
  factoring item, the S7/S9 profile laws, and the D5 blueprint debt (item 6's leaves have no
  blueprint nodes; STEPS pins them).
- [x] **Moved to Phase 40 §6 (the held fallback):** `hK` on the tight stratum from grid vanishing;
  tree-triple ⇒ `dim Z = 0`; the rest of the W4 build (T1, W4-L4b, W4-L2/L3′/L5, `hnoGood'`;
  `notes/pencil/W4-reopen.md`); the reverse arms of the W0 transport.

## Blockers / open questions

None for this phase. Two items live outside it:

- **`/harness-review` is due** (five S-mark sessions; the PI's call, `HARNESS.md`). The candidate
  artifacts from review 2 are listed in this note at `e316891f` (*Blockers*, "Each attack's first
  move is a reading check").
- **On a future HIT on a held kernel**, the phase-boundary consequences are the PI's call
  (`PHASE-BOUNDARIES.md`), surfaced with an estimate, never unilateral.

## Hand-off / next phase

**Phase closed 2026-09-25.** The successor is **Phase 40** (PENCIL-X0), already open: its plan is
`notes/Phase40-design.md` (layers by stable code, the label-level proof map, §6 the held fallback,
§7 the items deferred from this phase), and its open sub-phase **40a** (SPINE2, the KT spine at
`n = 2`) has its work log at `notes/Phase40a.md` — run it with `/coordinate-phase 40a`. The attack
tracks stay under `HARNESS.md`, outside any phase: smark paused (`notes/attacks/smark/state.md`
untouched by this close), gr10 CLOSED 2026-09-23. `notes/Phase39-design.md` is frozen (119 live
anchors; its header says so). The two `[pending]` `notes/BlueprintExposition.md` entries (the
main-component headline; the held-kernel theorem) are Phase 40's to write or close.

## Adjacent directions (orientation only)

The queue is `ROADMAP.md`'s *Queued post-program phases*: ORIGAMI (`notes/Origami.md`) is next
after Phase 40; PIN's re-scope is decided at 40a's close; the unqueued survey is
`notes/IdeaBacklog.md`.

## Decisions made during this phase

One line each. The reasoning is in `notes/Phase39-design.md` (frozen),
`notes/pencil/adjudications.md` (the PI's calls, verbatim) and the blueprint chapter.

### Phase-local choices

- **2026-09-25 — Phase 39 CLOSES on the reduction** (PI): `pencil_conjecture_of_X0` carries only
  `X0Dist`/`X0Gen`; Phase 40 discharges them. Verbatim `adjudications.md`, the "(later)" entry.
- **2026-09-25 — the `X₀` architecture ADOPTED over every infinite field; Phase 40 minted; the hold
  lifted for L0 and W4-A; the kernels and smark held** (PI). Verbatim `adjudications.md`.
- **2026-09-25 — L0a/L0b transcribed verbatim from compiled spikes**; `hW4A` dropped; the theorem
  needs neither `h2ec` nor `[Infinite K]`; `unusedDecidableInType` on `[DecidableEq β]` is
  load-bearing, suppressed with a recorded check.
- **2026-09-23 — W4 REOPENED (PI), the hold lifted in stages; the `X₀` census put first.**
  `notes/pencil/W4-reopen-archive.md`.
- **2026-09-17 — C4ℓ closes Layer C** (A5+B6 only); both attack briefs checked against the tree.
- **2026-09-16/17 — item 6's Layers A/B/C land by transcription plus one recon spike**; A6 deferred
  (D2); the weld-graph route dead by supersession only.
- **2026-09-16 — item 6's D1–D5 SETTLED (PI):** D1 `¬ G.Adj u v`; D2 A6/C3 out of scope; D3 the
  `max` form primary; D4 state the laws in `deficiencyMerged`; D5 no blueprint chapter (debt).
- **2026-09-16 — item 5 LANDED:** the kernels take the IH, `hK` weakens to the generic motive,
  `PencilPair` gains the adjacent-distinct conjunct (α); `HasDistinctPencilRealization` is *never* a
  conjunct on `HasPencilPanelRealization` (it breaks `lem:pencil-self-dual`).
- **2026-09-16 — the R2 recon RECORDED; (GR-10) RE-SCOPED to the char-2 probe (CLOSED 2026-09-23);
  the S-mark brief rewrite landed; route R2 adopted.**
- **2026-09-15 — the field hypothesis: option C (PI).** Reduction `[Infinite K]`; (K) via the grid
  `[Infinite K] [NeZero (2 : K)]`; (K-bare) `[Infinite K]`, interim `IsAlgClosed K`.
- **2026-09-15 — items 1–2 PINNED then LANDED** (`Fin m` cycle data + `Graph.GirthGE`; `WList`
  paths in ∃-statements); the hold lifted for items 1–3 (PI).
- **2026-09-15 — the research loop RETIRED; attack tracks replace directions** (`HARNESS.md`).
- **2026-08-05 — Lean hold (PI)**; every script the project runs is committed.
- **2026-08-02 — W4 route 3, packaging (b)**; (K-res) a byte-identical sibling of `hK`.
- **2026-07-24 — the phase stays open** rather than splitting at the three carried items.
- **Pre-arc Lean decisions (W0–W5, 2026-07-23 → 08-04)** — `notes/Phase39-design.md`,
  `notes/pencil/arc-worklog.md`; R1–R3 `notes/pencil/structure.md`.

### Promoted to HARNESS / DESIGN / TACTICS / the coordinator playbook

- *Evidence and reproducibility rules distilled from the arc* → `HARNESS.md` *Evidence*,
  *Reproducibility*.
- *Both triggers of `linter.style.show`, plus the `haveI`-on-a-`Prop`-class sibling* →
  `TACTICS-GOLF.md` § 12.
- *`Submodule.span_image` and an unbundled lambda — `Set.image_congr'` first* → TACTICS-GOLF § 22.
- *`LinearIndependent.pair_map`* → mirrored, `Mathlib/LinearAlgebra/LinearIndependent/Basic.lean`.
- *Dispatch-log Findings F8, F9, F12, F14, F19, F41, F42* → the `/coordinate-phase` *Dispatch
  playbook* (at this close); F5, F6, F10, F17 were already in the command, `CLAUDE.md` and the
  agent cores. The research-arc findings kept in the log await `/harness-review`.

### The research arc's record (2026-08-05 → 09-13)

127 one-line verdicts, the (BE-14) and `hK` lanes' detail, the ranked carried items and route σ:
`notes/pencil/arc-worklog.md`, `notes/pencil/fanout.md`, `notes/pencil/structure.md` blocks 8–14,
`notes/pencil/strategy.md` §8.

## Citations

Relocated 2026-09-01 (verbatim) to `notes/pencil/structure.md` §"Citations — the phase's verified
bibliography" (block 7), which carries the per-source venue data and verification dates.
