# Phase 12 — Matroid foundations: submodular functions & matroid union (work log)

**Status:** in progress (Layer 0 = phase opening).

This phase formalizes the abstract-matroid prerequisites of the
body-bar route: the matroid-from-submodular-function construction and
polymatroid rank formula (Edmonds 1970), the matroid-union theorem
(Nash-Williams 1966 / Edmonds), and Edmonds' matroid-partition rank
formula (Edmonds 1965). It is the first link of a re-scoped chain that
ends at body-bar Tay's theorem:

| Phase | Content |
|---|---|
| **12** (this) | submodular → matroid; matroid union / Edmonds partition |
| 13 | Tutte–Nash-Williams tree-packing; `Graph`-native `(k,ℓ)`-sparsity |
| 14 | `k`-frame matroid = `k`-fold cycle-matroid union (Whiteley Thm 1) |
| 15 | body-bar frameworks + Tay's theorem (existence form) |

This re-scoping replaced the old single "Phase 12 = body-bar Tay"
(which was blocked on vendoring the matroid-union machinery). The
body-bar target is now **Phase 15**; its architectural decisions
(carrier = mathlib core `Graph α β`, Plücker/two-extensor handling,
`namespace Graph` convention) live in `../ROADMAP.md` §15. The old
body-bar Layer plan is recoverable from git history (commits up to
`a55520b`); `blueprint/src/chapter/body-bar.tex` carries the 13–15
dep-graph.

**Workflow:** forward-mode. The blueprint chapter
`blueprint/src/chapter/matroid-union.tex` is the authoritative
dep-graph and lemma index; this file carries everything else.

**References** (all classical; verified — see `../CLAUDE.md`
*Referencing prior work*):
- Edmonds 1970, *Submodular functions, matroids, and certain
  polyhedra* — `ofSubmodular`, polymatroid rank.
- Nash-Williams 1966, *An application of matroids to graph theory* —
  matroid union.
- Edmonds 1965, *Minimum partition of a matroid into independent
  subsets* — matroid partition.
- Oxley 2011, *Matroid Theory* (2nd ed.) — textbook treatment.

## Current state

Layer 0 (this commit): phase opened. `matroid-union.tex` populated
with 8 red forward-mode nodes; user-facing status surfaces synced
(ROADMAP table + §12–§15, README, `home_page/index.md`, `intro.tex`);
Apache-2.0 `LICENSE` added; provenance/attribution recorded. No Lean
yet (Layer-0 pattern).

Next concrete step is **Layer 1, the route spike** (below): no
production Lean lands until the route is chosen.

## Architectural choices made up front

- **Build the matroid-union prerequisite locally** (mirror dir
  `CombinatorialRigidity/Matroid/`), not upstream-first. Decided by
  the user 2026-06-01. This is an explicit exception to the
  "Mirror directory = small upstream-eligible lemmas only" convention
  — see `../DESIGN.md` *Local mirror of the matroid-union subsystem*.
- **Route TBD via an early spike** (Layer 1). Two candidates; the
  spike picks one on measured cost, not a priori.
- **Provenance / attribution.** The Lean is ported from Peter Nelson's
  `apnelson1/Matroid` (Apache-2.0; same license as this project and
  mathlib). No license issue. Apache §4 obligations met by: a per-file
  header on each vendored file (copyright **Peter Nelson**;
  `Authors: Peter Nelson, Bryan Gin-ge Chen`; provenance + list of
  modifications), the credit paragraph in `matroid-union.tex`, and the
  `../DESIGN.md` + `../CLAUDE.md` provenance notes. See FRICTION
  `[matroid]`.

## Prerequisites audit (matroid package, pinned rev `e6852ce`)

> **Re-verified 2026-06-01**, correcting the earlier audit's claim that
> the machinery "exists nowhere as live, buildable code." The truth:
> the proofs **exist and are complete**; they are bit-rotted onto a
> superseded constructor.

**The WIP proofs are complete — zero internal sorries:**
- `WIP/Submodular.lean` (1236 L, **0 sorry**): `Submodular`,
  `ofSubmodular`, `PolymatroidFn`, `ofPolymatroidFn`,
  `polymatroid_rank_eq`.
- `WIP/Union.lean` (597 L, only a *commented-out* sorry):
  `Matroid.Union`, `union_indep_iff` / `union_indep_iff'`,
  `matroid_partition'`, `matroid_partition_eRk'`.

**Why they don't build (the actual blocker):** both rest on
`FinsetCircuitMatroid` (a Finset-based circuit-axiom constructor),
which upstream **commented out and superseded** with the Set-based
`FiniteCircuitMatroid` (the constructor `Graph.cycleMatroid` itself now
uses). `WIP/Submodular.lean` also imports a never-committed
`Matroid.Constructions.IsCircuitAxioms`. So the port is a **rebase onto
`FiniteCircuitMatroid`**, not a from-scratch proof.

**`Union` genuinely needs `Submodular`** — `union_indep_iff` /
`matroid_partition'` route through `ofPolymatroidFn` /
`polymatroid_rank_eq`. Union is *not* separable from the submodular
machinery (an over-optimistic survey claimed otherwise; it was wrong).

**Live and usable now (zero sorry, clean imports):**
- `Matroid.Intersection` — Edmonds' matroid *intersection* theorem
  (`exists_common_ind`). Union is classically derivable from
  intersection via duality — the basis of route (b) below.
- `Graph.cycleMatroid` + API (`Matroid/Graphic.lean`); `Matroid.ofFun`
  (Phase 8); `FiniteCircuitMatroid` constructor (`Matroid/Axioms/Circuit.lean`).

## Layer plan

### Layer 0 — phase opening (this commit)
Blueprint dep-graph (`matroid-union.tex`); status-surface sync;
`LICENSE`; provenance. No Lean.

### Layer 1 — route spike (decision gate; minimal throwaway Lean)
Prototype both routes far enough to compare actual cost, then record
the decision + rationale here (this resolves the deferred route choice):
- **(a) Submodular-repair.** Rebase `ofSubmodular` (and the
  `polymatroid_rank_eq` rank argument) from `FinsetCircuitMatroid` onto
  the live `FiniteCircuitMatroid`. The `cycleMatroid` precedent (same
  constructor) suggests this is mechanical; risk is the Finset→Set
  circuit-axiom translation. Proofs already exist (0 sorry).
- **(b) Union-from-intersection.** Build `Matroid.Union` from the live
  `Matroid.Intersection` via duality, bypassing the submodular
  machinery. Fewer vendored lines, more elegant, but a genuinely new
  derivation to formalize.
Spike deliverable: one of `ofSubmodular`-on-`FiniteCircuitMatroid` or
`Matroid.Union`-from-`Intersection` building (possibly with `sorry`s in
non-load-bearing spots) far enough to gauge effort. Pick, then delete
the losing prototype.

### Layer 2 — execute the chosen route
Mirror dir `CombinatorialRigidity/Matroid/`. For route (a), likely:
- **L2a** — `Constructions/Submodular.lean`: `Submodular`,
  `ofSubmodular`, `PolymatroidFn`, `ofPolymatroidFn`,
  `polymatroid_rank_eq`. Nodes `def:submodular`, `def:ofSubmodular`,
  `def:polymatroidFn`, `def:ofPolymatroidFn`, `lem:polymatroid-rank`.
- **L2b** — `Constructions/Union.lean`: `Matroid.Union`,
  `union_indep_iff`, `matroid_partition'` / `matroid_partition_eRk'`.
  Nodes `def:matroid-union`, `lem:union-indep-iff`,
  `thm:matroid-partition-rank`.
Each vendored file carries the Peter-Nelson attribution header.
Blueprint nodes flip green per file.

## Lemma checklist

High-level outline; the leaf-level to-do list is the
`matroid-union.tex` dep-graph (8 red nodes as of L0).

- [x] **L0:** `matroid-union.tex` populated; surfaces synced; LICENSE;
  provenance.
- [ ] **L1:** route spike + decision (recorded here).
- [ ] **L2a:** `def:submodular`, `def:ofSubmodular`,
  `def:polymatroidFn`, `def:ofPolymatroidFn`, `lem:polymatroid-rank`.
- [ ] **L2b:** `def:matroid-union`, `lem:union-indep-iff`,
  `thm:matroid-partition-rank`.

## Blockers / open questions

- **Route choice** — resolved at L1, not before.
- **`Matroid.ofFun` / polynomial-ring coefficient questions** belong to
  Phase 14 (k-frame), not here.
- **Upstream issue against `apnelson1/Matroid`** — optional. We are no
  longer waiting on upstream (local-mirror decision), but an issue
  asking whether the `FinsetCircuitMatroid`-based WIP will be revived
  on `FiniteCircuitMatroid` is still worth filing as a courtesy / to
  offer the port back. Not blocking.

## Hand-off / next phase

Next concrete commit: **Layer 1 route spike.** Prototype
`ofSubmodular` on `FiniteCircuitMatroid` (route a) and
union-from-`Intersection` (route b) far enough to compare, pick one,
record the decision in *Layer plan → Layer 1* above, and delete the
losing prototype. Production Lean (L2) follows once the route is fixed.

Phases 13–15 are scoped in `blueprint/src/chapter/{matroid-union →
body-bar}.tex` and `../ROADMAP.md` §13–§15 but **not opened** (no
`notes/Phase13.md` etc. until their first commit). Body-hinge /
panel-hinge → Phase 16; molecular conjecture (Katoh–Tanigawa) →
Phase 17.
