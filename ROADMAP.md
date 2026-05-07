# Combinatorial Rigidity — Roadmap

This directory aims to formalize a slice of **combinatorial rigidity theory**
in mathlib style, culminating in **Laman's theorem** (1970): a graph on
`n ≥ 2` vertices is generically rigid in the plane iff it contains a
spanning subgraph with `2n − 3` edges in which every subgraph on `k ≥ 2`
vertices has at most `2k − 3` edges. Such graphs are called *Laman graphs*
or *minimally rigid* graphs in the plane.

The work is expected to span multiple sessions. This file is the canonical
hand-off document: read it first when picking up the project.

> Design rationale (why these choices and not others) lives in
> `DESIGN.md`. Open it only when you actually need to question a
> decision; otherwise this file is sufficient.

## Directory layout

```
Archive/CombinatorialRigidity/
├── ROADMAP.md         this file — must-read every session
├── DESIGN.md          rationale for cross-cutting design choices
├── GRIND.md           how to use the `grind` tactic in this project
├── notes/             per-phase work logs
│   └── PhaseN.md      lemma checklist + decisions + hand-off for Phase N
├── Mathlib/           lazy mirror for missing-from-mathlib lemmas (see DESIGN.md)
├── EdgesIn.lean       Phase 1 — `edgesIn` selector
├── Sparsity.lean      Phase 1 — `IsSparse`, `IsTight`
├── Laman.lean         Phase 1+2 — `IsLaman` and downstream
└── …                  later phases get their own files
```

## Status

| Phase | File(s) | Status |
|---|---|---|
| 1. Sparsity | `EdgesIn.lean`, `Sparsity.lean`, `Laman.lean` | ✓ Complete (see `notes/Phase1.md`) |
| 2. Laman graphs | `Laman.lean` | Pending |
| 3. Henneberg moves | `Henneberg.lean` | Not yet created |
| 4. Frameworks | `Framework.lean` | Not yet created |
| 5. Laman's theorem | `LamanTheorem.lean` | Not yet created |

Phase-level details (per-phase lemma checklists, decisions made during
that phase, hand-off notes) live under `notes/PhaseN.md`. Read those
when picking up a phase or reviewing how an earlier phase was finished.

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

Definitions:
- `SimpleGraph.IsLaman G := IsTight 2 3`.

Lemmas to develop:
- `IsLaman G ↔ G.IsSparse 2 3 ∧ #E = 2 * #V − 3`.
- The single-edge graph on `Fin 2` is Laman (`#V = 2`, `#E = 1 = 2·2 − 3`).
- A Laman graph on `n ≥ 2` vertices has minimum degree at least 2 (every vertex
  has degree at least 2) and contains a vertex of degree 2 or 3 (key for Henneberg).
- `K₄ \ e` is Laman.

### Phase 3 — Henneberg moves (`Henneberg.lean`)

Definitions:
- `Henneberg.typeI G v a b` — given `G : SimpleGraph V`, a fresh vertex `v ∉ V`
  and two distinct `a, b ∈ V`, produce a new graph on `V ⊕ {v}` with the two
  edges `{v, a}, {v, b}` added.
  *Implementation note:* We will likely use `SimpleGraph` over a sum / option
  type or a concretely indexed vertex set; keep an eye on dependent types.
- `Henneberg.typeII G e a b c` — given an edge `e = {a, b}` and a third vertex
  `c ≠ a, b`, delete `e`, add a fresh vertex `v`, add edges
  `{v, a}, {v, b}, {v, c}`.
- `Henneberg.Reachable G H` — inductive reachability of `H` from `G` by a
  finite sequence of Type I/II moves.

Lemmas to develop:
- Both moves preserve the Laman property.
- Both moves preserve generic rigidity (proved later in `Framework.lean`).
- **Henneberg's theorem**: every Laman graph is reachable from `K₂` by a
  finite sequence of Type I and II moves. (Proof: induction on `#V`; pick a
  degree-2 or degree-3 vertex and reverse the appropriate move.)

### Phase 4 — Frameworks and infinitesimal rigidity (`Framework.lean`)

Definitions:
- `Framework V d := V → EuclideanSpace ℝ (Fin d)` — a `d`-dimensional placement.
- `SimpleGraph.RigidityMatrix G p` — the `#E × d·#V` matrix encoding edge length
  derivatives. Concretely: row indexed by edge `{u, v}` has block
  `(p u − p v)` at columns for `u` and `−(p u − p v)` at columns for `v`.
- `SimpleGraph.IsInfinitesimallyRigid G p d` — null space of the rigidity
  matrix has dimension equal to the dimension of trivial motions
  (`d + d·(d−1)/2` for `#V ≥ d`).
- `SimpleGraph.IsGenericallyRigid G d` — there exists a placement `p` such
  that `G` is infinitesimally rigid at `p` (equivalently, the rigidity matrix
  has full rank for some `p`, hence on a Zariski-open set of placements).

Lemmas to develop:
- Trivial motions form a subspace of dimension `d·(d+1)/2` (when `#V ≥ d`).
- Generic rigidity depends only on `G` (not on the chosen generic `p`).
- Generic rigidity is monotone: `G ≤ G'` and `G` rigid → `G'` rigid.
- For `d = 2`: a generically rigid graph on `n ≥ 2` vertices has `≥ 2n − 3` edges.

### Phase 5 — Laman's theorem (`LamanTheorem.lean`)

The main theorem:
```
theorem SimpleGraph.IsGenericallyRigid_two_iff_hasLamanSubgraph
    {V : Type*} [Fintype V] (G : SimpleGraph V) (h : 2 ≤ Fintype.card V) :
    G.IsGenericallyRigid 2 ↔
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsLaman
```

Two directions:
- **(⇐)** Henneberg induction: `K₂` is rigid; both Henneberg moves preserve
  generic rigidity; hence every Laman graph is generically rigid; hence so
  is every supergraph.
- **(⇒)** If `G` is generically rigid, the rigidity matroid has full rank,
  so there is a basis (an independent edge set) of size `2n − 3`. The
  spanning subgraph on those edges is `(2, 3)`-tight by the matroid property.

The hard direction needs the equality of the **rigidity matroid** and the
**(2, 3)-count matroid** in dimension 2 — the deepest part of the proof.
Lovász–Yemini gave a clean argument; Whiteley's polarity is another route.

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
  `mem_*` simp lemma. See `GRIND.md` for the full discussion.
- **Missing mathlib lemmas.** If you need a lemma that genuinely
  belongs upstream, put it under `Mathlib/<exact mathlib path>` so
  promotion is later a copy-paste. The directory is created lazily;
  don't pre-populate. See `DESIGN.md` "Mirror directory".
- **Tactic notes.** Practical guidance on `grind` (preferred closing
  tactic in this directory) lives in `GRIND.md`. When in doubt, read
  it — the workflow recommendation in particular is short and saves
  iteration time.

## Per-session workflow

### Starting a session

1. **Read this file end-to-end.** It's short on purpose.
2. `git log --oneline BC-rigidity` to see what the last session did.
3. `lake build CombinatorialRigidity.Laman` (or the leftmost
   active phase's file) to confirm the tree still compiles cleanly
   on its own.
4. Identify the active phase from the Status table. Open
   `notes/PhaseN.md` for that phase if it exists. If the phase has not
   started yet, open ROADMAP's planning section for that phase below
   and create `notes/PhaseN.md` in your first commit (template below).
5. Check `GRIND.md` if you haven't seen the `grind?` → `grind only`
   workflow before.

### Working

- Use `TaskCreate` for short-lived intra-session todos. They don't
  persist across sessions.
- Use `notes/PhaseN.md` for lemma-level state that should outlast the
  session (in-progress lemma list, blockers, design choices made
  during this phase).
- When you add a lemma, put it in the file that introduces the
  relevant *definition*, not the file that first uses it. (Lemma
  about `IsSparse` → `Sparsity.lean`, even if first invoked in
  `Laman.lean`.)
- Run `lake build <leftmost active file>` before committing.

### Ending a session

- Update `notes/PhaseN.md`'s "Current state" / "Next" / "Blockers"
  sections so the next agent can resume cold.
- If the phase finishes, flip its row in this file's Status table to
  ✓ in the same commit.
- If you answered a "Choices to revisit" entry in `DESIGN.md`, update
  it in the same commit.

### Template for `notes/PhaseN.md`

When starting a phase, seed the file with sections like:

```markdown
# Phase N — <name> (work log)

**Status:** in progress.

## Current state
<one-paragraph: what's done, what's mid-stream, what's the next concrete step>

## Lemma checklist
- [x] `lemma_a` — done
- [ ] `lemma_b` — in progress; blocked on …
- [ ] `lemma_c`

## Decisions made during this phase
- <phase-local trade-offs; cross-cutting ones go in DESIGN.md>

## Blockers / open questions
- …

## Hand-off / next phase
<written when the phase finishes; what unlocks the next phase>
```

`notes/Phase1.md` is a complete-phase example.

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
