# Phase 12 — Matroid foundations: submodular functions & matroid union (work log)

**Status:** in progress (Layer 2a **complete**; Layer 2b **underway** —
`Constructions/Union.lean` landed the union construction + independence
characterization green: `def:matroid-union`, `lem:union-indep-iff`. The
partition rank theorem `thm:matroid-partition-rank` is the one remaining
L2b node, but a **dependency re-scope** this commit found it blocked on a
~420-line un-ported Rado/Hall sub-tree — L2b is now split into **L2b-rado**
(the Rado prerequisite) and **L2b-partition** (the two target theorems);
see *Blockers* and *Hand-off*).

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

L2b dependency re-scope (this commit, **docs-only**): the next-commit plan
"port `polymatroid_of_adjMap` → `adjMap_rank_eq` → the two `matroid_partition*`
targets" assumed `rado` (Oxley Thm 11.2.2) was live upstream (per the prior
hand-off note). **It is not.** Audit of the live package
(`apnelson1/Matroid`, rev `e6852ce`):
- `polymatroid_of_adjMap` (`WIP/Union.lean:258`) builds its matching via the
  *sufficiency* direction of Rado's theorem: `(rado M A).mpr <rank-condition>`
  (`WIP/Union.lean:339`).
- `rado` is **not** in the live `Matroid.Intersection` — that file has only
  `rado_necessary` (the easy direction); `rado_sufficient` / `rado_iff` are
  commented-out Lean-3 and route through further dead machinery
  (`partition_matroid_on`, `exists_common_ind_with_isFlat_right`).
- The live `rado` (full iff) exists **only** in the shelved
  `WIP/Submodular.lean:891` — i.e. in the *same* WIP file L2a ported from, but
  in its **back half**, which the L2a port stopped short of (L2a ended at
  `polymatroid_rank_eq`, `WIP/Submodular.lean:~296`).
- `rado` rests on a self-contained but sizeable un-ported sub-tree
  (`WIP/Submodular.lean:323–942`, ~420 L, **0 sorry**): `generalized_halls_marriage`
  (matroidal Hall, routes through the already-ported `Submodular`/`Monotone` +
  `polymatroid_rank_eq`-adjacent rank API), the `PartialTransversal` structure
  + ~30 supporting lemmas, the `Transversal`/`Transverses` family, then `rado`
  / `rado_v2`. `generalized_halls_marriage`'s own deps are all within the
  L2a-ported surface, so the sub-tree is bounded and self-contained.

**L2b is therefore split into two sub-layers** (see *Layer plan* L2b-rado /
L2b-partition and *Hand-off*). This is the same class of deeper bit-rot the
*Prerequisites audit* flagged as a residual risk; the next concrete commit is
**L2b-rado**, not the two partition theorems.

Layer 2b union construction (prior commit, **opened L2b**): created
`Constructions/Union.lean`, ported from `apnelson1/Matroid`'s `WIP/Union.lean`
with the Peter-Nelson attribution header. Landed green, **0 sorry**:
`AdjIndep'` + `adjMap_indep_iff'` (Set-valued analogue of the live
`Matching.AdjIndep` / `adjMap_indep_iff`), `Matroid.Union` (node
`def:matroid-union`, via `(sum' Ms).adjMap (·.2 = ·) univ`), `Matroid.union`
(binary, over `Bool`), `Union_empty`, the two halves `union_indep_aux{,'}`,
and `union_indep_iff` / `union_indep_iff'` (node `lem:union-indep-iff`).
Both blueprint nodes flipped green; `checkdecls` passes; `lake build` +
`lake lint` clean. Port hazards (full detail in FRICTION `[matroid]` *L2b
union construction*): `open Function` for the ` on ` infix; reconstructed the
commented-out `exists_pairwiseDisjoint_iUnion_eq` as a `private` lemma;
reproved the brittle `Union_empty` via `eq_loopyOn_iff` + finitarity; used
`[Finite α]` over the WIP's `[Fintype α]` per project convention. The
partition rank theorem (`matroid_partition'` / `matroid_partition_eRk'`,
node `thm:matroid-partition-rank`) is **deferred** to the next commit — its
WIP proof routes through `polymatroid_of_adjMap` / `adjMap_rank_eq` /
`sum'_rk_eq_rk_sum`, a larger sub-chain (see *Hand-off*).

Layer 2a rank lemma (prior commit, **closed L2a**): ported
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
- **L2b** — split into two sub-layers after the dependency re-scope:
  - **L2b-union** (DONE) — `Constructions/Union.lean`: `Matroid.Union`,
    `union_indep_iff`. Nodes `def:matroid-union`, `lem:union-indep-iff`.
  - **L2b-rado** (NEXT) — port the Rado/Hall prerequisite from
    `WIP/Submodular.lean:323–942` (~420 L). Lands in `Constructions/Submodular.lean`
    (its home file) as a continuation of the L2a port, since `rado` lives in
    that WIP file and depends only on the already-ported `Submodular` surface.
    Sub-chain: `generalized_halls_marriage` → `PartialTransversal` (+ ~30
    lemmas) → `Transversal`/`Transverses` family → `rado` / `rado_v2`. No new
    blueprint node (Rado is an internal prerequisite); a `lem:rado` node may be
    added to `matroid-union.tex` if useful for the dep-graph.
  - **L2b-partition** — `Constructions/Union.lean`: `polymatroid_of_adjMap`,
    `adjMap_rank_eq`, `sum'_eRk_eq_eRk_sum{_on_indep}` / `sum'_rk_eq_rk_sum`,
    then `matroid_partition'` / `matroid_partition_eRk'`. Node
    `thm:matroid-partition-rank`. Unblocked once L2b-rado lands.
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
- [x] **L2b-union:** `def:matroid-union` ✓
  (`Matroid.Union` / `Matroid.union`), `lem:union-indep-iff` ✓
  (`union_indep_iff` / `union_indep_iff'`; + `adjMap_indep_iff'`,
  `Union_empty`, `union_indep_aux{,'}` support).
- [ ] **L2b-rado (NEW; prerequisite, ~420 L):** `generalized_halls_marriage`,
  `PartialTransversal` (+ ~30 lemmas), `Transversal`/`Transverses` family,
  `rado` / `rado_v2`. Port into `Constructions/Submodular.lean`.
- [ ] **L2b-partition:** `thm:matroid-partition-rank`
  (`matroid_partition'` / `matroid_partition_eRk'`); via
  `polymatroid_of_adjMap` / `adjMap_rank_eq` / `sum'_*` rank-distribution.
  Blocked on L2b-rado.

## Blockers / open questions

- ~~**Route choice**~~ — **resolved at L1: route (a), submodular-repair**
  (see *Layer 1* above for the three measured findings).
- **`Matroid.ofFun` / polynomial-ring coefficient questions** belong to
  Phase 14 (k-frame), not here.
- **L2b-rado prerequisite (active blocker for `thm:matroid-partition-rank`).**
  `polymatroid_of_adjMap` needs the *sufficiency* direction of Rado's theorem
  (`rado`), which is **not** live upstream — only `WIP/Submodular.lean:891`
  has it, on top of a ~420-line un-ported sub-tree
  (`generalized_halls_marriage` + `PartialTransversal` + `Transversal` family).
  Must be ported first; see *Current state* and *Layer plan* L2b-rado. This is
  bounded (self-contained, 0 sorry upstream) but is a genuine sub-phase, not a
  single commit.
- **Upstream issue against `apnelson1/Matroid`** — optional. We are no
  longer waiting on upstream (local-mirror decision), but an issue
  asking whether the `FinsetCircuitMatroid`-based WIP will be revived
  on `FiniteCircuitMatroid` is still worth filing as a courtesy / to
  offer the port back. Not blocking.

## Hand-off / next phase

This commit was a **docs-only re-scope**, not Lean: the planned next commit
(port the two `matroid_partition*` targets) proved infeasible as scoped —
its bridge `polymatroid_of_adjMap` needs Rado-sufficiency, which is not live
upstream (full analysis in *Current state* / *Blockers*). No Lean changed;
the tree still builds clean (L2b-union green).

**Next concrete commit: L2b-rado** — port the Rado/Hall prerequisite from
`WIP/Submodular.lean:323–942` (~420 L, 0 sorry upstream) into the local
`Constructions/Submodular.lean` (its home file, continuing the L2a port).
Sub-chain in order: `generalized_halls_marriage` (matroidal Hall;
`WIP/Submodular.lean:323`, deps all in the L2a-ported surface) →
`PartialTransversal` structure + ~30 supporting lemmas (`:504–740`) →
`Transversal` / `Transverses` / `Transverses'` family (`:804–888`) → `rado`
(`:891`, Oxley Thm 11.2.2) and `rado_v2` (`:742`). This is large enough that a
**clean intermediate handoff** is: land `generalized_halls_marriage` +
`PartialTransversal` first (the infrastructure), then `rado` itself as a second
step. A `lem:rado` blueprint node in `matroid-union.tex` is optional (internal
prerequisite) — add it if it helps the dep-graph read.

**Then L2b-partition** (unblocked once `rado` is green): port
`polymatroid_of_adjMap` (the key bridge — exhibits the `adjMap`-matroid as
`ofPolymatroidFn` of `f Y = M.rk {v | ∃ u ∈ Y, Adj v u}`, the longest proof,
calls `rado …).mpr`), `adjMap_rank_eq`, `sum'_eRk_eq_eRk_sum{_on_indep}` /
`sum'_rk_eq_rk_sum`, then `matroid_partition'` / `matroid_partition_eRk'`
(node `thm:matroid-partition-rank`) into `Constructions/Union.lean`. That
closes Phase 12.

Port hazards across both sub-layers (FRICTION `[matroid]` *L2a rank lemma* +
*L2b union construction*): the `Matroid.r → rk` rename (incl. `rk_submod` /
`rk_mono` / `rk_empty` now `[RankFinite M]`-gated, `coe_rank_eq → cast_rank_eq`,
`Indep.eRk → eRk_eq_encard`, `Indep.r → Indep.rk_eq_card`, `IsBasis.r →
ncard_eq_rk`), `open Function` for ` on ` / `onFun`, transitive-import gaps,
stale aesop simp-lists, and `[Fintype] → [Finite]` signature conversion per
project convention.

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
