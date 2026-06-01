# Phase 12 — Matroid foundations: submodular functions & matroid union (work log)

**Status:** in progress (Layer 2a underway: the submodular file landed
green — `def:submodular`, `def:ofSubmodular`. Polymatroid nodes next).

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
- Oxley 2011, *Matroid Theory* (2nd ed.) — textbook treatment; the
  matroid-theory cross-check (covers all four results below).

Local PDFs on the shelf (`../.refs/`): `oxley-2011-matroid-theory.pdf`,
`schrijver-2004-combinatorial-optimization.pdf` (clean modern
union/intersection/partition proofs — matroid material in Vol. B),
`edmonds-1965-minimum-partition-matroid.pdf`. The Edmonds-1970 /
Nash-Williams-1966 primaries are *not* on the shelf — Oxley and
Schrijver subsume them, and the working proofs are the
`apnelson1/Matroid` WIP skeleton anyway.

## Current state

Layer 2a underway (this commit): created
`CombinatorialRigidity/Matroid/Constructions/Submodular.lean` (non-`module`,
since the `apnelson1/Matroid` package is not module-converted — same
constraint as `LinearRigidityMatroid.lean`), ported from
`apnelson1/Matroid`'s `WIP/Submodular.lean` with the Peter-Nelson
attribution header. Landed green, **0 sorry**: `Matroid.Submodular`
(`def:submodular`), `Matroid.ofSubmodular` (`def:ofSubmodular`, rebased
onto the live `FiniteCircuitMatroid` via the Set-lift
`∃ C₀, ↑C₀ = C ∧ Minimal P C₀` validated by the L1 spike), and the API
`circuit_ofSubmodular_iff` / `indep_ofSubmodular_iff`. The three helpers
the WIP pulled from the never-committed `IsCircuitAxioms` /
commented-out `ForMathlib/Finset.lean` are reconstructed as `private`
lemmas in the file: `setOf_minimal_antichain`,
`exists_minimal_satisfying_subset`, `intro_elimination_nontrivial`.
Both `matroid-union.tex` nodes flipped green; `checkdecls` passes; the
file is imported from the top-level `CombinatorialRigidity.lean`.

**Remaining L2a:** the polymatroid layer — `PolymatroidFn`
(`def:polymatroidFn`), `ofPolymatroidFn` (`def:ofPolymatroidFn`), and
`polymatroid_rank_eq` (`lem:polymatroid-rank`). The last needs the
`Matroid.r` → `rk` rename chase (17 sites in the WIP) noted at L1.

Layer 1 (prior commit): route spike complete; **route (a)
submodular-repair chosen** (rationale below). Layer 0: phase opened,
`matroid-union.tex` populated, surfaces synced, `LICENSE` + provenance.

Two porting gotchas hit and resolved (see FRICTION `[matroid]` L2a
note): the minimal import set does not transitively expose `linarith`
(added `import Mathlib.Tactic.Linarith`); `LinearOrderedAddCommMonoid`
was refactored out of this mathlib, so `Submodular`'s bound is
`[AddCommMonoid β] [LinearOrder β]` (order-compat instance dropped per
the `unusedArguments` linter).

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

### Layer 1 — route spike (DONE; **route (a) chosen**)

**Decision: route (a), submodular-repair.** Spiked in a throwaway
`Matroid/SpikeA.lean` (deleted post-decision). The spike rebased
`ofSubmodular` onto the live `FiniteCircuitMatroid` by keeping the
circuit predicate `Finset`-valued internally and feeding the
constructor a Set-valued lift `IsCircuitS C := ∃ C₀ : Finset α,
↑C₀ = C ∧ Minimal P C₀`. It **built green** with `sorry` only in the
two hard axiom fields and the helper. This confirmed the
`cycleMatroid` precedent: the constructor-lift is mechanical
(`empty_not_isCircuit` / `circuit_finite` / `circuit_subset_ground`
all closed trivially off the `∃ C₀` lift).

**Why (a) over (b) — three measured findings:**
1. **(b) has no scaffolding and would be invent-from-scratch.** The
   package's *only* matroid-union (`WIP/Union.lean`'s `Matroid.Union`)
   is itself **defined via `adjMap`/`sum'` and its rank theorem
   `matroid_partition'` routes through `ofPolymatroidFn` +
   `polymatroid_rank_eq`** — i.e. the union construction already
   depends on the submodular machinery. There is no
   union-from-intersection derivation anywhere; `Matroid.Intersection`
   exposes only `exists_common_ind` (a cardinality min-max), not a
   rank-function union. (b) would be a genuinely new formalization
   with zero reuse.
2. **(b) wouldn't deliver the polymatroid rank formula** (Edmonds
   1970) that Phase 14's k-frame argument needs — that lives only in
   the submodular file.
3. **(a)'s remaining work is bounded revival, not invention.** The
   `ofSubmodular` / `polymatroid_rank_eq` proofs exist and are
   complete; L2a is: (i) re-do the Finset→Set constructor lift
   already validated by the spike, (ii) reconstruct ~3 helper lemmas
   that lived in the never-committed `IsCircuitAxioms`
   (`setOf_minimal_antichain`, `intro_elimination_nontrivial`,
   `exists_minimal_satisfying_subset` — the last is a verbatim revival
   of a commented `ForMathlib/Finset.lean` lemma, modulo minor
   `Finset.exists_minimal` API drift), and (iii) chase the
   `Matroid.r` → `Matroid.rk` rename (17 sites in `polymatroid_rank_eq`).

**Two extra bit-rot points found beyond the audit** (both in scope
for L2a, neither a blocker): the WIP imports a never-committed
`Matroid.Constructions.IsCircuitAxioms`, and `polymatroid_rank_eq`
uses the old `Matroid.r` (now `rk`).

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
- [x] **L1:** route spike + decision — **route (a) chosen** (recorded
  above; spike built green, deleted).
- [~] **L2a:** `def:submodular` ✓, `def:ofSubmodular` ✓ (+
  `circuit_ofSubmodular_iff` / `indep_ofSubmodular_iff`);
  `def:polymatroidFn`, `def:ofPolymatroidFn`, `lem:polymatroid-rank`
  still to land.
- [ ] **L2b:** `def:matroid-union`, `lem:union-indep-iff`,
  `thm:matroid-partition-rank`.

## Blockers / open questions

- ~~**Route choice**~~ — **resolved at L1: route (a), submodular-repair**
  (see *Layer 1* above for the three measured findings).
- **`Matroid.ofFun` / polynomial-ring coefficient questions** belong to
  Phase 14 (k-frame), not here.
- **Upstream issue against `apnelson1/Matroid`** — optional. We are no
  longer waiting on upstream (local-mirror decision), but an issue
  asking whether the `FinsetCircuitMatroid`-based WIP will be revived
  on `FiniteCircuitMatroid` is still worth filing as a courtesy / to
  offer the port back. Not blocking.

## Hand-off / next phase

Next concrete commit: **continue Layer 2a, the polymatroid layer** in
`Constructions/Submodular.lean` (same file). Port from the WIP, in
order: `PolymatroidFn` (`def:polymatroidFn`) and `ofPolymatroidFn`
(`def:ofPolymatroidFn`) — both light wrappers around the now-landed
`ofSubmodular` plus `indep_ofPolymatroidFn_iff` — then the substantive
`polymatroid_rank_eq` (`lem:polymatroid-rank`). The rank lemma is the
one with real porting cost: the WIP's `polymatroid_rank_eq` /
`polymatroid_rank_eq_on_indep` use the old `Matroid.r` (now `rk`), so
chase the rename (~17 sites per the L1 audit) and re-check the
`r`-vs-`rk`/`eRk` API names against this mathlib. Smallest forward
commit: land `def:polymatroidFn` + `def:ofPolymatroidFn` + their indep
iff (a clean, quick win); assess `polymatroid_rank_eq` scope once those
close. Flip the matching `matroid-union.tex` nodes green per commit.

After L2a, **L2b** is `Constructions/Union.lean`: `Matroid.Union`,
`union_indep_iff`, `matroid_partition'` / `matroid_partition_eRk'`
(nodes `def:matroid-union`, `lem:union-indep-iff`,
`thm:matroid-partition-rank`). The WIP `Union.lean` routes through
`ofPolymatroidFn` + `polymatroid_rank_eq`, so it depends on L2a closing
first.

Reusable recipe for the port (validated this commit): non-`module`
file, Peter-Nelson header, `import Mathlib.Tactic.Linarith` explicitly
(not transitive), and for any new constructor reuse the Set-lift
`∃ C₀, ↑C₀ = C ∧ Minimal P C₀` pattern.

Phases 13–15 are scoped in `blueprint/src/chapter/{matroid-union →
body-bar}.tex` and `../ROADMAP.md` §13–§15 but **not opened** (no
`notes/Phase13.md` etc. until their first commit). Body-hinge /
panel-hinge → Phase 16; molecular conjecture (Katoh–Tanigawa) →
Phase 17.
