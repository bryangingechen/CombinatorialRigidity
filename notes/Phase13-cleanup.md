# Phase 13-cleanup — between Phase 13 and Phase 14 (work log)

**Status:** in progress.

Standard between-phases cleanup round (the default cadence in
`CLEANUP.md`), opened on the Phase 13 surface now that
Tutte–Nash-Williams tree-packing has closed. Round-level discipline:
`CLEANUP.md` at repo root. Per-commit discipline (build/lint gates,
friction review): `CombinatorialRigidity/CLAUDE.md`.

## Scope

The Phase 13 surface:

- **`CombinatorialRigidity/BodyBar/TreePacking.lean`** (531 LoC) — the
  whole file is Phase 13, original to this project.
- **`CombinatorialRigidity/Matroid/Constructions/Union.lean`** — only
  the **Phase-13 additions** (the rank-adapter lemmas, roughly lines
  470–600: `Union_rank_eq`, `Union_pow_rank_eq`, `adjMap_rk_eq`,
  `Union_pow_rk_eq`, `Union_pow_indep_iff_count`) are in scope. The
  rest of the file is **vendored** from `apnelson1/Matroid` and was
  audited in the **Phase 12-cleanup** round (`notes/Phase12-cleanup.md`);
  do not re-litigate vendored upstream proofs here.
- **`blueprint/src/chapter/body-bar.tex`** — the *Tree-packing as a
  corollary* subsection (`def:graph-sparse`,
  `thm:unionPow-cycle-indep-iff-sparse`, `thm:tutte-nash-williams`,
  `cor:k-spanning-trees`). The other body-bar nodes (`thm:k-frame-…`,
  `thm:tay-…`) are Phase 14/15 forward-scoped, out of scope.
- **`notes/Phase13.md`** (312 lines) — over the 250-line soft budget;
  D-compression candidate.

Audit categories in scope: **A, B, C, D** (all four).

**Batching (per user direction this round):** audit sweeps that close
no-op may be **batched into a single commit** rather than one commit
per category. Genuine fixes still land as their own commit.

## Lemma checklist (the A–D task list)

Populated up front per `CLEANUP.md` *Workflow* rule 2 (sweep findings
seeded from the opening grep; verify-and-fix in subsequent commits).

### A. Blueprint ↔ Lean divergence (body-bar.tex tree-packing subsection)
**No-op (this commit).** All four nodes' blueprint statements faithfully
match their Lean signatures; no formalization asides to discharge.
- [x] **A1** `def:graph-sparse` (`\lean{Graph.IsSparse, Graph.IsTight}`)
  — match. Blueprint phrases the bound subtractively (`|E'| ≤ k|V'| - ℓ`,
  global `|E| = k|V| - ℓ`); Lean is the additive `Set`-side form
  (`E'.ncard + ℓ ≤ k * (spanningVerts E').ncard`,
  `E(G).ncard + ℓ = k * V(G).ncard`), edge-subset-indexed
  (`∀ E' ⊆ E(G)`), with the additive phrasing already noted in the Lean
  doc-comment. Standard math gloss, not a divergence.
- [x] **A2** `thm:unionPow-cycle-indep-iff-sparse`
  (`Graph.unionPow_cycleMatroid_indep_iff_isSparse_restrict`) — match.
  Pointer resolves; the `restrict`/`E' ⊆ E(G)` shape (`hE' : E' ⊆ E(G)`,
  conclusion `… .Indep E' ↔ (G ↾ E').IsSparse k k`) is reflected by
  "a set of bars `E' ⊆ E(G)` … iff `G` restricted to that set is
  `(k,k)`-sparse".
- [x] **A3** `thm:tutte-nash-williams` (`Graph.tutte_nash_williams`) —
  match. `G.IsForestPacking k ↔ G.IsSparse k k`; the disjointify remark
  ("an acyclic cover disjointifies … a disjoint cover is a cover") is a
  math statement faithful to the `Fintype.exists_disjointed_le` step, not
  a Lean-cost gloss.
- [x] **A4** `cor:k-spanning-trees`
  (`Graph.isSpanningTreePacking_of_isTight`) — match. The Phase-13
  connectivity hypothesis IS reflected: blueprint "If `G` is connected
  and `(k,k)`-tight …" ↔ Lean `(hconn : G.Connected) (htight : G.IsTight
  k k)`; the per-copy maximal-acyclic-set count argument is the proof
  prose verbatim.
- [x] **A5** No "formalization aside" remarks anywhere in the
  tree-packing subsection (grep: only intro/preamble `formalized`/`Lean`
  mentions, no proof-level asides). Nothing to simplify.

### B. Code-smell sweep (TreePacking.lean + Phase-13 Union.lean additions)
**No-op (this commit).** All five smells clean across the surface.
- [x] **B1** `classical` × 4 in TreePacking (L69, 319, 433, 483) +
  the Phase-13 Union.lean adder (`Union_pow_rk_eq` L564) — each is the
  documented `[Finite]`-bridge idiom: pairs with a
  `Fintype.ofFinite`/`hCompFin.fintype` `haveI` to recover decidability
  under the project's `[Finite α] [Finite β]` boundary. No
  cleaner-`[DecidableEq]`-boundary site. No-op.
- [x] **B2** `haveI : Fintype _ := Fintype.ofFinite _` (TreePacking
  L68, 434, 484; `hCompFin.fintype` L325) — same `[Finite]`-bridge
  idiom. The `Fintype β := Fintype.ofFinite β` recurs (L434, L484) but
  in two distinct theorems; a shared helper saves nothing (one line
  each). No-op.
- [x] **B3** multi-step `rw` at TreePacking L328
  (`rw [hH, cycleMatroid_deleteVerts_isolatedSet, cycleMatroid_restrict,
  inter_eq_right.mpr hYG]`) — four genuine distinct steps: `hH` is the
  `set H` unfold, the rest are the cycleMatroid restriction bridge
  (delete-verts → restrict → `inter` simplification). Same idiom recurs
  at L168 but threads into a different target (`Matroid.eRank_restrict`
  vs. the `.restrict Y` form), so no single fused mirror lemma. No-op.
- [x] **B4** `Set`↔`Finset` ncard bridges (`← Finset.coe_sdiff,
  ncard_coe_finset` over an explicit `Finset.univ \ Y`: TreePacking L74;
  Phase-13 Union.lean L516, 572) — the autoparam pattern
  (`TACTICS-GOLF.md` §2) covers `Set.ncard`-of-`toFinset`-of-filter
  sites, not these explicit `Finset.univ \ Y` two-step bridges; already
  as tight as the idiom allows, and the same shape recurs in vendored
  code (L516). No-op.
- [x] **B5** confirmed absent across the surface: no `@[nolint]` /
  `set_option linter`, no `noncomputable def`, no `change`/`show`
  coaxing, no `show … from rfl`. No-op.

### C. Long-proof audit (TreePacking.lean)
**No-op (this commit).** Top sites walked; all structural assembly, no
extraction debt (CLEANUP.md §C calibration).
- [x] **C1** Top three by body (the seeded candidates) walked with the
  four-question gate:
  - `le_mul_cycleMatroid_rk_of_isSparse_restrict` (78 LoC) — component
    decomposition assembly; sub-pieces already named lemmas
    (`spanningVerts_edgeSet_eq_vertexSet_of_isCompOf`,
    `edgeSet_deleteVerts_isolatedSet_restrict`,
    `spanningVerts_restrict_of_subset`,
    `components_cycleMatroid_isSkewFamily`). Remaining length is the
    intrinsic ℕ↔ℕ∞ skew-sum cast plumbing. No further extract.
  - `isMaximalAcyclicSet_of_isForestPacking_of_isTight` (36 LoC) — the
    per-copy count argument; each `have` a distinct step, reads as
    composition. No-op.
  - `spanningVerts_edgeSet_eq_vertexSet_of_isCompOf` (27 LoC) — the
    two-direction `ext`/incidence walk; the closed-subgraph step is a
    single mathlib call. No-op.
  The two `eRk`-formula proofs are <15 LoC, tight restriction-bridge
  rewrites. No-op.

### D. Project-organization compression
- [ ] **D1** Compress `notes/Phase13.md` (312 → target ≤ ~200): the
  *Current state* section is a running per-commit narrative (8+ "…
  landed" paragraphs) that should collapse to a short summary + the
  *Lemma checklist* (already a clean index) + commit-log pointer, now
  that the phase is closed.
- [ ] **D2** Lift any cross-cutting Phase-13 lessons referenced 2+
  times (candidates: the isolated-vertex/`spanningVerts` cancellation
  pattern; the `eRk`↦`rk` / `encard`↦`ncard` `[Finite]`-cast bridges;
  the `IsSkewFamily.sum_eRk_eq_eRk_iUnion` component-sum idiom) to
  `TACTICS-GOLF.md` / `FRICTION.md`, replacing the Phase entry with a
  pointer.
- [ ] **D3** Re-skim `notes/FRICTION.md` status sections; migrate any
  resolved Phase-13 project-internal entry whose resolution is fully
  indexed elsewhere to `FRICTION-archive.md`.

## Decisions made during this round

- **A (blueprint↔Lean divergence) — no-op.** All four tree-packing
  nodes' blueprint statements faithfully match their Lean signatures
  (A1–A4); no formalization asides exist in the subsection (A5). Detail
  per-task in the checklist above. The subtractive-vs-additive phrasing
  of `def:graph-sparse` is the intended math gloss (Lean doc-comment
  already flags the additive `Set`-side form), not drift. No `\lean{...}`
  pointer touched, so no `checkdecls` run needed this commit.
- **B (code-smell sweep) — no-op, batched.** All five smells clean: the
  `classical`/`haveI Fintype` sites are the documented `[Finite]`-bridge
  idiom; the L328 / L74 multi-`rw` and ncard-bridge chains are genuine
  multi-step compositions with no fusable single-step mirror; the
  no-finding smells stay absent. Detail per-task in the checklist.
- **C (long-proof audit) — no-op, batched.** Top three proofs walked
  with the four-question gate; all are structural assembly over
  already-named sub-lemmas plus intrinsic ℕ↔ℕ∞ cast plumbing, no
  extraction debt (the CLEANUP.md §C calibration outcome). Detail in
  the checklist.

## Blockers / open questions
- None.

## Hand-off / next phase

**Clean handoff.** Audit categories A, B, C are closed (all no-op;
B+C batched into this commit per *Scope* → Batching, recorded above).
Next concrete commit: run **audit category D** (project-organization
compression, tasks D1–D3) — D1 compresses `notes/Phase13.md`
(312 → ≤ ~200) by collapsing the per-commit *Current state* narrative
to a summary + commit-log pointer; D2 lifts any cross-cutting Phase-13
lesson referenced 2+ times to `TACTICS-GOLF.md` / `FRICTION.md`; D3
re-skims `FRICTION.md` status sections for resolved Phase-13 entries to
migrate to `FRICTION-archive.md`. That D commit **closes the round**:
flip the ROADMAP Status row to ✓, sync no user-facing surfaces (a
cleanup round is not a phase), and record what (if anything) carried
over. All A–D have been no-op so far, so the round is shaping up as a
clean-bill cleanup; D1's compression is the only concrete edit
expected.
