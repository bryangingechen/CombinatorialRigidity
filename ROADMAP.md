# Combinatorial Rigidity — Roadmap

This directory aims to formalize a slice of **combinatorial rigidity theory**
in mathlib style, culminating in **Laman's theorem** (1970): a graph on
`n ≥ 2` vertices is generically rigid in the plane iff it contains a
spanning subgraph with `2n − 3` edges in which every subgraph on `k ≥ 2`
vertices has at most `2k − 3` edges. Such graphs are called *Laman graphs*
or *minimally rigid* graphs in the plane.

The work is expected to span multiple sessions. This file is the canonical
hand-off document: it carries the directory layout, status, mathematical
plan, and engineering conventions. Read it after `CLAUDE.md`.

> **Agents:** start with `CLAUDE.md` (the agent operating manual covering
> reading order, per-session workflow, friction review, and the
> `notes/PhaseN.md` template). This file is the *what*; CLAUDE.md is the
> *how*.
>
> Design rationale (why these choices and not others) lives in
> `DESIGN.md`. Open it only when you actually need to question a
> decision; otherwise this file is sufficient.

## Directory layout

```
<repo root>/
├── CLAUDE.md            agent operating manual — must-read first every session
├── ROADMAP.md           this file — directory layout, status, plan, conventions
├── DESIGN.md            rationale for cross-cutting design choices
├── TACTICS-GOLF.md      golf reference: grind, ncard, mirror rule, fun_prop
├── TACTICS-QUIRKS.md    rescue reference: subst, simp residuals, dot notation
├── notes/               per-phase work logs + cross-cutting logs
│   ├── PhaseN.md        lemma checklist + decisions + hand-off for Phase N
│   ├── FRICTION.md      long-running API/tactic friction log
│   └── PERFORMANCE.md   build-time + profiling notes — read before a perf pass
├── CombinatorialRigidity.lean   top-level entry point (imports LamanTheorem)
├── CombinatorialRigidity/       all Lean sources live here
│   ├── Mathlib/         mirror for upstream-eligible lemmas (see DESIGN.md)
│   │   └── …/           each file mirrors its eventual upstream path
│   ├── EdgesIn.lean     Phase 1 — `edgesIn` selector
│   ├── Sparsity.lean    Phase 1 — `IsSparse`, `IsTight`
│   ├── Laman.lean       Phase 1+2 — `IsLaman` and downstream
│   ├── Henneberg.lean   Phase 3 — `typeI`, `typeII` and downstream
│   ├── Framework.lean   Phase 4 — frameworks, rigidity map
│   ├── TrivialMotions.lean  Phase 6 — d-general translations + infinitesimal rotations
│   ├── HennebergRigidity.lean  Phase 5 milestone 2 — per-move rigidity preservation
│   ├── RigidityMatroid.lean  Phase 6 — row-independence, basis-pick, sparsity bridge
│   ├── LamanTheorem.lean  Phase 5+6 — Laman's theorem (both directions)
│   ├── CountMatroid.lean  Phase 7 — abstract (k, ℓ)-count matroid (ℓ < 2k)
│   └── MatroidIdentification.lean  Phase 7 — Lovász–Yemini hard direction + rigidity matroid
├── lakefile.toml        Lake build config; depends on mathlib4
├── lean-toolchain       pinned Lean version (matches mathlib4)
└── lake-manifest.json   resolved dependency revisions
```

The project was previously developed at `Archive/CombinatorialRigidity/` inside
the mathlib4 tree and lifted to this standalone repository; references to
`Archive/CombinatorialRigidity/<path>` in older commit messages and docs map
to `<path>` here (with Lean sources rehomed under `CombinatorialRigidity/`).

## Status

| Phase | File(s) | Status |
|---|---|---|
| 1. Sparsity | `EdgesIn.lean`, `Sparsity.lean`, `Laman.lean` | ✓ Complete (see `notes/Phase1.md`) |
| 2. Laman graphs | `Laman.lean` | ✓ Complete (see `notes/Phase2.md`) |
| 3. Henneberg moves | `Henneberg.lean` | ✓ Complete (see `notes/Phase3.md`) |
| 4. Frameworks | `Framework.lean` | ✓ Complete (see `notes/Phase4.md`) |
| 5. Laman's theorem (⇐) | `LamanTheorem.lean`, `HennebergRigidity.lean` | ✓ Complete (see `notes/Phase5.md`) |
| 6. Laman's theorem (⇒) | `LamanTheorem.lean`, `RigidityMatroid.lean` | ✓ Complete (see `notes/Phase6.md`) |
| 7. Lovász–Yemini matroid identification | `CountMatroid.lean`, `MatroidIdentification.lean` | ✓ Complete (see `notes/Phase7.md`) |
| ⋮ Cleanup round (pre-Phase-8) | project-wide | in progress (see `notes/Phase7-cleanup.md`; round manual: `CLEANUP.md`) |

Phase-level details (per-phase lemma checklists, decisions made during
that phase, hand-off notes) live under `notes/PhaseN.md`. Read those
when picking up a phase or reviewing how an earlier phase was finished.

**Cleanup rounds** between phases get their own work log under
`notes/PhaseN-cleanup.md` (named to sort next to the prior phase's
notes) and a row in this table for visibility. Round-level discipline
lives in `CLEANUP.md` at the repo root.

Add lemmas in the file that introduces the relevant definition; a
lemma about `IsSparse` belongs in `Sparsity.lean`, not in `Laman.lean`,
even if it is first used there. When starting a new phase, create the
corresponding `notes/PhaseN.md` file in your first commit.

## Mathematical roadmap

We follow the **Henneberg construction** route, which is elementary and
matches mathlib's combinatorics style. The matroid-theoretic route via
`Mathlib.Combinatorics.Matroid` is left as a future alternative framing.

### Phase 1 — Sparsity (`EdgesIn.lean`, `Sparsity.lean`, `Laman.lean`)

Complete. Defines `edgesIn`, `IsSparse`, `IsTight`, `IsLaman` and the
basic API (monotonicity, subgraph preservation, global edge bound,
vertex partition). See `notes/Phase1.md` for the full lemma list and
phase-specific decisions.

### Phase 2 — Laman graphs (`Laman.lean`)

Complete. Builds the Laman API on top of the Phase 1 `IsLaman`
definition: the `(2, 3)`-tightness `iff` unfolding, the K₂ base case
(promoted to a named theorem), and the degree results that feed into
the Henneberg induction (minimum degree ≥ 2 for `n ≥ 3`; existence of
a degree-2-or-3 vertex). See `notes/Phase2.md` for the full lemma list
and phase-specific decisions.

### Phase 3 — Henneberg moves (`Henneberg.lean`)

Complete. Type I and Type II moves on simple graphs (fresh vertex as
`none : Option V`, old vertices via `some`). Both moves preserve the
Laman property (`typeI_isLaman`, `typeII_isLaman`); both edge-set
decompositions land (`typeI_edgeSet[_ncard]`, `typeII_edgeSet[_ncard]`).
Iso transport (`IsSparse.iso`, `IsTight.iso`, `IsLaman.iso`, plus
`Iso.image_edgesIn`) lifts Laman across graph isomorphisms. The
`K₄ \ e` worked example (`top_fin_four_minus_edge_isLaman`) ties
these together. The canonical iso constructors
`typeI_iso_of_two_neighbors` and `typeII_iso_of_three_neighbors`
package the iso `G ≃g typeI G' a b` (resp. `…typeII…`) from
neighborhood data at a chosen vertex; downstream phases consume these
to bridge flat-form reverse decompositions with operation-form forward
preservation theorems.

The structural decomposition theorem
(`IsLaman.exists_typeI_or_typeII_reverse`, now in flat form per Phase 7
Commit 6) lives in `Henneberg.lean`. Phase 3 originally shipped only
the iso-only half (no `G'.IsLaman` claim) because the typeII reverse
can fail for an arbitrary non-adjacent pair (concrete 6-vertex
counter-example in `notes/Phase3.md`); the strengthened claim with
`G'.IsLaman` was deferred to Phase 5 — see §5 below — and re-presented
in flat form in Phase 7.

See `notes/Phase3.md` for the full lemma list and phase-specific
decisions.

Both moves additionally preserve generic rigidity (TODO in Phase 5,
because the proof needs the typeII reverse blocker argument).

### Phase 4 — Frameworks and infinitesimal rigidity (`Framework.lean`)

Complete. Defines `Framework V d` as `V → EuclideanSpace ℝ (Fin d)`,
the `RigidityMap G p` as an `ℝ`-linear map (the matrix view via
`LinearMap.toMatrix` is deferred until needed), `IsInfinitesimallyRigid
G p` as the kernel-dimension bound `dim ker ≤ d(d+1)/2`, and
`IsGenericallyRigid G d` as existence of an infinitesimally rigid
placement. Ships the basic `RigidityMap` API (`Framework.finrank`,
`rigidityMap_apply`, `rigidityMap_ker_mono`,
`rigidityMap_finrank_range_le`), the graph-monotonicity corollaries
(`IsInfinitesimallyRigid.mono`, `IsGenericallyRigid.mono`), the main
edge-count theorem `IsGenericallyRigid.card_mul_le` (`d * #V ≤ #E +
d(d+1)/2` for any generically rigid graph), and the K₂ worked example
`top_fin_two_isGenericallyRigid`. The `TrivialMotions` API (textbook
identification of kernel with rigid motions) and the
`finrank_trivialMotions_eq_of_affinelySpanning` lemma were deferred
in Phase 4 (neither was on the critical path for Phase 5) and landed
in Phase 6's `TrivialMotions.lean`. See `notes/Phase4.md` for the full
lemma list and phase-specific decisions.

### Phase 5 — Laman's theorem, (⇐) direction (`LamanTheorem.lean`, `HennebergRigidity.lean`)

Complete. The main iff statement lives in `LamanTheorem.lean`:
```
theorem SimpleGraph.isGenericallyRigid_two_iff_exists_isLaman_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (h : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```
*composed* from two named directional theorems —
`IsLaman.isGenericallyRigid_two` for (⇐), proved in Phase 5, and
`IsGenericallyRigid.exists_isLaman_le` for (⇒), `sorry`-blocked and
resolved in **Phase 6** (see §6 below).

**(⇐) recap.** Henneberg induction on `Fintype.card V`. K₂ base case
via `top_fin_two_isGenericallyRigidInj 1` + iso transport. Inductive
step via `IsLaman.exists_typeI_or_typeII_reverse` (strengthened
decomposition with `G'.IsLaman`, proved via the Henneberg blocker
argument) plus per-move rigidity preservation
(`typeI_isGenericallyRigidInj_two` /
`typeII_isGenericallyRigidInj_two`, both unconditional). The Type II
move's collinearity gap is discharged by `IsInfinitesimallyRigid.
eventually` (openness of IR via `LinearIndependent.eventually`) plus
a perpendicular perturbation packaged in
`exists_nonCollinear_rigid_placement_dim_two`. See `notes/Phase5.md`
for the full lemma list and proof techniques.

**Open refactor proposal** (not a blocker): the three contradiction
templates in the milestone-1 blocker argument
(`IsLaman.contradiction_{one,two,three}_pair`) plus the degree-3
dispatcher can be unified through two reusable `(k, ℓ)`-shaped
primitives, saving ~210 LoC. Full plan in `notes/Phase5.md`'s
appendix.

### Phase 6 — Laman's theorem, (⇒) direction (`LamanTheorem.lean`, `RigidityMatroid.lean`)

Complete. Builds the rigidity-matroid scaffolding in `RigidityMatroid.lean`
(row-independence, dual-module bridge, rank lower bound at generic
placement, rank upper bound at affinely-spanning placement, basis-pick),
then ships Lovász–Yemini's easy direction in dim 2:
`isSparse_of_edgeSetRowIndependent_dim_two` (row-independent edge sets
yield `(2, 3)`-sparse spanning subgraphs) and the assembly
`IsGenericallyRigid.exists_isLaman_le` (combine the affinely-spanning
rigid placement, basis-pick, and sparsity). The iff
`isGenericallyRigid_two_iff_exists_isLaman_le` in `LamanTheorem.lean`
now closes both directions. Phase 4 deliberately kept `Framework.lean`
matroid-agnostic (see DESIGN.md *Notion- and matroid-agnostic core*);
Phase 6 stood up `RigidityMatroid.lean` on top without packaging the
abstract `Matroid` instance, since the easy direction needs only the
row-independence relation and two linear-algebra facts.

The chapter ran in **forward blueprint mode** per `blueprint/DESIGN.md`
*Recommendation for Phase 6*: the blueprint chapter
`blueprint/src/chapter/laman-theorem.tex` (its $\Rightarrow$ subsection)
served as the authoritative dep-graph and lemma index throughout. See
`notes/Phase6.md` for the full lemma list and phase-specific decisions.

### Phase 7 — Lovász–Yemini matroid identification (`CountMatroid.lean`, `MatroidIdentification.lean`)

Complete. Phase 6 shipped the easy direction of Lovász–Yemini in dim 2
(row-independent $\Rightarrow$ $(2, 3)$-sparse). Phase 7 shipped the
converse, the general $(k, \ell)$-count matroid in the matroidal regime
$\ell < 2k$ (Whiteley 1996, Lee--Streinu 2008), and the planar
rigidity-matroid specialisation. Hard-direction induction lives in
`MatroidIdentification.lean` and routes through the matroidal-regime
$I$-component scaffolding in `Sparsity.lean` (`IsSparse.maxBlock` and
edge-disjointness); the abstract `(k, \ell)`-count matroid sits in its
own file `CountMatroid.lean` via `IndepMatroid.ofFinite`. The phase ran
in **forward blueprint mode** with `blueprint/src/chapter/count-matroid.tex`
and `blueprint/src/chapter/rigidity-matroid.tex` as the authoritative
dep-graphs and lemma indices. See `notes/Phase7.md` for the full lemma
list and phase-specific decisions.

The **linear-matroid framing** of the rigidity matroid (the
generic-placement matroid $M_p$ on $E(K_V)$ via `Matroid.ofFun` for
some generic $p$, with Lovász--Yemini stated as a matroid iso
$M_{p_{\text{gen}}} \cong \mathrm{rigidityMatroid}\,V$) is deferred to
**Phase 8**, which will add `apnelson1/Matroid` as a dependency.

## Engineering conventions

- **Namespace.** Everything sits inside `SimpleGraph` or
  `CombinatorialRigidity`. No top-level identifiers.
- **Vertex types.** Use `V : Type*` and add `[Fintype V]` only where needed.
  Edge counts use `Set.ncard` so we don't force `Fintype` everywhere.
- **Cardinalities.** Use `Set.ncard` for sets and `Finset.card` for finsets.
  Avoid `ℕ`-subtraction; rephrase `a ≤ b − c` as `a + c ≤ b`.
- **Style.** Module docstrings at the top of each file (`/-! # Title -/`).
  One declaration ↔ one purpose. Comments only when *why* is non-obvious.
- **Imports.** Each file imports the minimum it needs. `Sparsity.lean`
  should import only `SimpleGraph.Basic` + `Set.Card` + minor friends.
- **Decidability.** Add `[DecidableEq V]` / `[DecidableRel G.Adj]` only when
  needed for a specific finset construction. Many definitions can stay
  noncomputable via `Set.ncard`.
- **Predicates are `def`s, not `abbrev`s.** `IsSparse`, `IsTight`,
  `IsLaman`, and `edgesIn` are non-reducible. `grind` will not unfold
  them on its own. To break an `IsTight`/`IsLaman` goal into parts use
  `refine ⟨?_, ?_⟩`; for an `edgesIn` membership use the corresponding
  `mem_*` simp lemma. See `TACTICS-GOLF.md` § 4 for the full discussion.
- **Missing mathlib lemmas.** If you need a lemma that genuinely
  belongs upstream, put it under `Mathlib/<exact mathlib path>` so
  promotion is later a copy-paste. The directory is created lazily;
  don't pre-populate. See `DESIGN.md` "Mirror directory".
- **Tactic notes.** Practical guidance on `grind` (preferred closing
  tactic in this directory), the `Set.ncard` autoparam pattern, the
  mirror-first rule, and other cross-cutting idioms all live in
  `TACTICS-GOLF.md`. When in doubt, read it — the section TL;DRs are
  short and save iteration time.
- **No prose counts in shared docs.** Don't write "Phase X surfaced
  N upstream candidates" or similar in `ROADMAP.md`, `DESIGN.md`, or
  `TACTICS-GOLF.md` — counts drift the moment a new phase mirrors more
  lemmas. Link to `notes/FRICTION.md` "Mirrored" (or the mirror
  directory listing) as the source of truth instead.

## Working on the project

The per-session workflow (starting / working / friction review at
end-of-session / leave-it-ready-for-the-next-agent), and the
`notes/PhaseN.md` template, live in `CLAUDE.md`. Agents: read that
first.

## References

- G. Laman, *On graphs and rigidity of plane skeletal structures*, J. Engrg.
  Math. **4** (1970), 331–340.
- L. Lovász and Y. Yemini, *On generic rigidity in the plane*, SIAM J.
  Algebraic Discrete Methods **3** (1982), 91–98.
- J. Graver, B. Servatius, H. Servatius, *Combinatorial Rigidity*, AMS GSM 2,
  1993. — main textbook reference.
- T. Jordán, *Combinatorial rigidity: graphs and matroids in the theory of
  rigid frameworks*, MSJ Memoirs, 2016. — modern survey.
- A. Nixon, B. Schulze, W. Whiteley, surveys on rigidity matroids.
