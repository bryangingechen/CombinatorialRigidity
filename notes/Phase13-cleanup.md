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

- **A (blueprint↔Lean divergence) — no-op.** All four tree-packing
  nodes' blueprint statements faithfully match their Lean signatures
  (A1–A4); no formalization asides exist in the subsection (A5). Detail
  per-task in the checklist above. The subtractive-vs-additive phrasing
  of `def:graph-sparse` is the intended math gloss (Lean doc-comment
  already flags the additive `Set`-side form), not drift. No `\lean{...}`
  pointer touched, so no `checkdecls` run needed this commit.

## Blockers / open questions
- None.

## Hand-off / next phase

**Clean handoff.** Audit category A is closed (no-op, recorded above).
Next concrete commit: run **audit category B** (code-smell sweep over
`TreePacking.lean` + the Phase-13 `Union.lean` adders, tasks B1–B5);
the seeded checklist expects mostly no-op (`classical`/`haveI` are the
documented `[Finite]`-bridge idiom). Per *Scope* → Batching, B and C
no-ops may be batched into a single commit. The round closes (likely
that same commit or the D-compression commit) by flipping the ROADMAP
Status row to ✓ and writing what (if anything) carried over.
