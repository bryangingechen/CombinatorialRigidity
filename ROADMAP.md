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

## Status

| File | What it contains | Status |
|---|---|---|
| `EdgesIn.lean` | `edgesIn` selector + basic API | **In progress — small** |
| `Sparsity.lean` | `IsSparse`, `IsTight` + basic API | **In progress — small** |
| `Laman.lean` | `IsLaman` + accessors; worked example for `K₂` | **In progress — small** |
| `Henneberg.lean` | Type I (vertex addition) and Type II (edge split) moves | Not yet created |
| `Framework.lean` | Bar-joint frameworks, rigidity matrix, infinitesimal rigidity | Not yet created |
| `LamanTheorem.lean` | Statement and assembly | Not yet created |

The first three files exist with a small amount of content each. Their
APIs are still likely to grow (or be revised) as downstream proofs
demand. Add lemmas in the file that introduces the relevant definition;
a lemma about `IsSparse` belongs in `Sparsity.lean`, not in `Laman.lean`,
even if it is first used there.

When creating a new file, update this table in the *same commit*.

## Mathematical roadmap

We follow the **Henneberg construction** route, which is elementary and
matches mathlib's combinatorics style. The matroid-theoretic route via
`Mathlib.Combinatorics.Matroid` is left as a future alternative framing.

### Phase 1 — Sparsity (`Sparsity.lean`)

Definitions:
- `SimpleGraph.edgesIn G s` — edges of `G` with both endpoints in `s : Set V`.
- `SimpleGraph.IsSparse G k ℓ` — for every finite `s ⊆ V` with `ℓ ≤ k * #s`,
  the number of edges in `s` plus `ℓ` is at most `k * #s`.
- `SimpleGraph.IsTight G k ℓ` — sparse and `#E + ℓ = k * #V`.

Lemmas to develop:
- Sparsity is preserved under taking subgraphs (`G ≤ G' → IsSparse G' k ℓ → IsSparse G k ℓ`).
- The empty graph is `(k, ℓ)`-sparse for all `k, ℓ`.
- `edgesIn` is monotone in the vertex set.
- `edgesIn` for `Set.univ` equals `edgeSet`.
- For finite `V`: deleting an edge preserves sparsity; adding an edge breaks tightness.
- For Laman's purposes: a `(2, 3)`-sparse graph has at most `2 * #V − 3` edges
  when `#V ≥ 2`.

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
- **Closing arithmetic / mixed-reasoning goals.** Prefer `grind` over
  `omega` for the closing tactic of an arithmetic step. `grind` handles
  the same linear-integer goals plus equational and propositional
  reasoning, so it tends to absorb the surrounding `rw` / `have` chain.
  Fall back to `omega` only if `grind` is the wrong tool for a specific
  goal.
- **Hint discovery for `grind`.** When `grind` fails or you suspect a
  smaller hint set will work, write `grind?` (or `grind? [foo, bar]`).
  It runs the tactic and prints a suggested `grind only [...]` call
  with exactly the lemmas it actually used. Replace `grind?` with the
  suggested call to land a deterministic, fast version. `grind only` is
  the preferred final form: it doesn't depend on the ambient
  `@[grind]`-annotated library beyond what's listed, so it's stable
  under mathlib changes.

## Hand-off checklist for the next session

1. **Read this file end-to-end.**
2. `git log --oneline BC-rigidity` for recent commits.
3. `lake build CombinatorialRigidity.Sparsity` (and any sibling
   modules) to confirm the current state still compiles.
4. Look at the Status table above and pick the leftmost active file.
5. Search inside the active `.lean` file(s) for `TODO` markers — these are
   the concrete next steps.
6. Update this `ROADMAP.md`'s Status table in the *same commit* as the
   code so the next session sees an accurate map. If you are revising or
   answering one of the "Choices to revisit" entries in `DESIGN.md`,
   update that file in the same commit too.

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
