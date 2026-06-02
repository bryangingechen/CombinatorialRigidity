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
- [ ] **A1** `def:graph-sparse` (`\lean{Graph.IsSparse, Graph.IsTight}`)
  — compare blueprint statement form vs the Lean signatures
  (edge-subset-indexed, `Set`-side, additive count).
- [ ] **A2** `thm:unionPow-cycle-indep-iff-sparse`
  (`Graph.unionPow_cycleMatroid_indep_iff_isSparse_restrict`) — pointer
  resolves + statement form (the `restrict`/`E' ⊆ E(G)` shape).
- [ ] **A3** `thm:tutte-nash-williams` (`Graph.tutte_nash_williams`) —
  forest-packing predicate form; prose proof (disjointify aside?).
- [ ] **A4** `cor:k-spanning-trees`
  (`Graph.isSpanningTreePacking_of_isTight`) — verify the **connectivity
  hypothesis** added in Phase 13 (Decisions: per-copy maximal-acyclic-set
  + `hconn : G.Connected`) is reflected in the blueprint statement/prose.
- [ ] **A5** Scan all four prose proofs for "formalization aside"
  remarks → attempt Lean simplification before letting any stand.

### B. Code-smell sweep (TreePacking.lean + Phase-13 Union.lean additions)
- [ ] **B1** `classical` × 4 in TreePacking (L69, 319, 433, 483) +
  the Phase-13 Union.lean adders — confirm each is the documented
  `[Finite]`-bridge idiom (DESIGN.md *Typeclass shape …*), not a
  cleaner-`[DecidableEq]`-boundary site. Expect no-op.
- [ ] **B2** `haveI : Fintype _ := Fintype.ofFinite _` (TreePacking
  L68, 434, 484; `hCompFin.fintype` L325) — same `[Finite]`-bridge
  idiom; check whether any is a repeated-`haveI` single-helper
  candidate. Expect no-op.
- [ ] **B3** multi-step `rw` at TreePacking L328 (4 rewrites) — judge
  whether it's one mathematical step needing a fused mirror lemma, or
  four genuine distinct steps. Likely fine.
- [ ] **B4** `Set`↔`Finset` ncard bridges (`ncard_coe_finset` /
  `Finset.coe_*` chains: TreePacking L74; Phase-13 Union.lean L516,
  572, 598) — does the autoparam pattern (`TACTICS-GOLF.md` §2)
  absorb any of these?
- [ ] **B5** confirm the no-finding smells (no `@[nolint]` /
  `set_option linter`, no `noncomputable def`, no `change`/`show`
  coaxing, no `show … from rfl`) stay absent across the surface.

### C. Long-proof audit (TreePacking.lean)
- [ ] **C1** Rank the top ~10 proofs by body length; walk each with
  the four-question gate (API extraction / missed mathlib lemma /
  tactic substitution / cross-proof unification). Candidates by eye:
  `le_mul_cycleMatroid_rk_of_isSparse_restrict` (component
  decomposition), `isMaximalAcyclicSet_of_isForestPacking_of_isTight`
  (the per-copy count argument), the two `eRk`-formula proofs.
  Calibration: expect mostly no-op (CLEANUP.md §C).

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
<to be filled as the round proceeds>

## Blockers / open questions
- None at open.

## Hand-off / next phase

**Round just opened (this commit).** Next concrete commit: run **audit
category A** (blueprint↔Lean divergence, tasks A1–A5) over the four
`body-bar.tex` tree-packing nodes; fix any divergence in the same
commit, or record A as no-op in *Decisions made*. No-op categories may
be batched (see *Scope* → Batching). The round closes by flipping the
ROADMAP Status row to ✓ and writing what (if anything) carried over.
