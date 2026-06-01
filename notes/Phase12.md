# Phase 12 — Matroid foundations: submodular functions & matroid union (work log)

**Status:** in progress (Layer 2a **complete**: submodular + polymatroid
machinery all green — `def:submodular`, `def:ofSubmodular`,
`def:polymatroidFn`, `def:ofPolymatroidFn`, `lem:polymatroid-rank`.
Layer 2b — `Constructions/Union.lean` — is next).

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

Layer 2a rank lemma (this commit, **closes L2a**): ported
`polymatroid_rank_eq` (`lem:polymatroid-rank`, Edmonds 1970 Prop. 11.1.7)
and its private helper `polymatroid_rank_eq_on_indep` into
`Constructions/Submodular.lean`. Landed green, **0 sorry**; blueprint node
`lem:polymatroid-rank` flipped green; `checkdecls` passes; `lake lint`
clean. The port did the `Matroid.r → rk` rename chase plus three other
API-drift fixes and two missing transitive imports — full detail in
FRICTION `[matroid]` *L2a rank lemma*. All five L2a blueprint nodes are
now green.

Layer 2a polymatroid layer (prior commit): added `PolymatroidFn`
(`def:polymatroidFn`, a `Prop` structure bundling `Submodular` + `Monotone`
+ `f ⊥ = 0`), `ofPolymatroidFn` (`def:ofPolymatroidFn`, a thin wrapper of
`ofSubmodular`), `indep_ofPolymatroidFn_iff`, and the corollary
`ofPolymatroidFn_nonempty_indep_le` to `Constructions/Submodular.lean`.
Landed green, **0 sorry**; both blueprint nodes flipped green; `checkdecls`
passes. One porting gotcha (see FRICTION `[matroid]` L2a polymatroid note):
the WIP's `@[simps!]` on `ofPolymatroidFn` breaks `simpNF` on
`indep_ofPolymatroidFn_iff` — restricted to `@[simps! E]` per the
`ofSubmodular` precedent.

Layer 2a submodular (prior commit): created
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

(At that point the polymatroid layer — `PolymatroidFn`, `ofPolymatroidFn`,
`polymatroid_rank_eq` — was still pending; all of it has since landed, see
*Current state*.)

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
- [x] **L2a:** `def:submodular` ✓, `def:ofSubmodular` ✓ (+
  `circuit_ofSubmodular_iff` / `indep_ofSubmodular_iff`),
  `def:polymatroidFn` ✓, `def:ofPolymatroidFn` ✓ (+
  `indep_ofPolymatroidFn_iff` / `ofPolymatroidFn_nonempty_indep_le`),
  `lem:polymatroid-rank` ✓ (+ private `polymatroid_rank_eq_on_indep`).
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

L2a is **complete** as of this commit (`polymatroid_rank_eq` landed,
`lem:polymatroid-rank` green). Next concrete commit: **open Layer 2b —
start `Constructions/Union.lean`.** Port the WIP `WIP/Union.lean`
(`apnelson1/Matroid`, 597 L, only a commented-out sorry): `Matroid.Union`
(node `def:matroid-union`), `union_indep_iff` / `union_indep_iff'`
(`lem:union-indep-iff`), then `matroid_partition'` / `matroid_partition_eRk'`
(`thm:matroid-partition-rank`). The WIP `Union` routes through
`ofPolymatroidFn` + `polymatroid_rank_eq` — both now available in
`Constructions/Submodular.lean` — so the dependency is satisfied.
Same port hazards expected as L2a (see the *Reusable recipe* below and
FRICTION `[matroid]` *L2a rank lemma* for the rename / missing-import /
stale-aesop-simp-list patterns to re-apply). Smallest-first move: land
`Matroid.Union` + `union_indep_iff` and flip those two nodes before
tackling the partition rank theorem; if `Union.lean` proves multi-session,
that split is a clean intermediate handoff. New file: Peter-Nelson
attribution header, non-`module`, audit transitive imports up front
(`linarith`, `Mathlib.Tactic.Cases`, `Mathlib.Data.Finset.CastCard`,
plus whatever `Union.lean` needs), wire it into `CombinatorialRigidity.lean`.

Reusable recipe for the port (validated across L2a): non-`module`
file, Peter-Nelson header, explicit `import` of tactics/lemmas the
minimal `Matroid.*` import set does not transitively expose —
`Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Cases` (for `induction'` /
non-prime `induction … using`), `Mathlib.Data.Finset.CastCard`
(`cast_card_{union,sdiff,inter}`) — chase `Matroid.r → rk` (and its
dot-lemmas `Indep.eRk → eRk_eq_encard`, `IsBasis.r → ncard_eq_rk` +
`Set.ncard_coe_finset`), and for any new constructor reuse the Set-lift
`∃ C₀, ↑C₀ = C ∧ Minimal P C₀` pattern.

Phases 13–15 are scoped in `blueprint/src/chapter/{matroid-union →
body-bar}.tex` and `../ROADMAP.md` §13–§15 but **not opened** (no
`notes/Phase13.md` etc. until their first commit). Body-hinge /
panel-hinge → Phase 16; molecular conjecture (Katoh–Tanigawa) →
Phase 17.
