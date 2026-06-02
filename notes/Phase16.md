# Phase 16 — Body-hinge Tay–Whiteley theorem (existence form) (work log)

**Status:** in progress (phase-opening commit: docs/planning only; no Lean yet).

## Current state

Phase opened. The target is the **body-hinge / panel-hinge Tay–Whiteley
theorem** in `n`-space (Tay 1989, Whiteley 1988), existence-of-realization
form, **via the matroid-union reduction to Phase 15's body-bar theorem**: a
multigraph `G` carries an independent (resp. isostatic) body-hinge framework
in `ℝⁿ` iff `(δ-1)·G` is `(δ,δ)`-sparse (resp. tight), where
`δ = bodyBarDim n = n(n+1)/2` and `(δ-1)·G` replaces each hinge by `δ-1`
parallel bars. This reduces node-for-node to `Graph.BodyBarFramework.tay_witness`
(Phase 15) once the hinge-to-bar reduction (`def:body-hinge-framework`,
`lem:edge-multiply-sparse`) lands.

Forward-mode phase. The authoritative dep-graph and lemma index is the new
blueprint chapter `body-hinge.tex` (§`sec:body-hinge`), seeded red this commit.
This file does not duplicate the node list. No Lean files exist yet; the planned
home is `BodyBar/BodyHinge.lean` (new), in the `CombinatorialRigidity.lean`
aggregator. Next concrete step is the leaf-most red node — `def:edge-multiply`
(`(δ-1)·G` parallel-edge multiplication on `Graph α β`).

## Architectural choices made up front

Carried over from the Phases 12–15 body-bar program (see ROADMAP §15,
`notes/Phase15.md` *Architectural choices*):

- **Carrier = mathlib core `Graph α β`**, matching Phases 13–15 (on which
  `cycleMatroid` and `BodyBarFramework` sit); Phases 1–11 stay on `SimpleGraph`.
  See `DESIGN.md` *Migrating Phases 1–11 …*.
- **Reduction-to-body-bar route, not a fresh rigidity matrix.** The body-hinge
  rigidity map is *defined* as the body-bar rigidity map of the induced
  framework on `(δ-1)·G` (each hinge = `δ-1` coincident bars spanning the
  hinge's dual space). No new linear algebra — the chapter adds only the
  hinge-to-bar device and its bookkeeping; the block-diagonal rank count,
  `tutte_nash_williams`, and `tay_witness` are reused verbatim. This is
  Whiteley 1988's matroid-union proof specialized; the `(δ-1)·G` device is
  exactly the multiplied graph of Katoh–Tanigawa 2011's molecular-conjecture
  statement.
- **Existence-of-realization form only**, matching Phase 15's scope. Whiteley's
  "almost all realizations are rigid" lift (Proposition 6, irreducible-variety
  machinery) deferred out of Phase 15 is re-assessed here; the standard-basis
  witness on `(δ-1)·G` is again sufficient for the existence form, so the lift
  remains deferred (now to the molecular-conjecture phase if ever pursued).
- **Plücker / two-extensor coordinates handled inline**, degenerate permitted,
  standard-basis witness only — as in Phase 15.
- **Graph-level defs under `namespace Graph`** (dot-notation on `G : Graph α β`);
  framework defs under `CombinatorialRigidity` / `BodyBar`. Phases 12–15
  exception to the "everything under `SimpleGraph`/`CombinatorialRigidity`"
  convention; see ROADMAP §15 + *Engineering conventions*.

## Lemma checklist

Tracked as the `body-hinge.tex` dep-graph (forward mode; the chapter IS the
checklist). Leaf-first landing order:

- [ ] `def:edge-multiply` — `(δ-1)·G` parallel-edge multiplication on
  `Graph α β`; vertex set preserved, `|E(m·G)| = m·|E(G)|`, spanning-vertex
  transport. **Leaf node — start here.**
- [ ] `def:body-hinge-framework` — body-hinge framework as the induced body-bar
  framework on `(δ-1)·G`; rigidity / independence inherited.
- [ ] `lem:edge-multiply-sparse` — independent/isostatic body-hinge ⇔
  `(δ,δ)`-sparse/tight `(δ-1)·G`; the count `(δ-1)|E| = δ(|V|-1)`.
- [ ] `thm:body-hinge-tay` — the chapter target; assemble from
  `lem:edge-multiply-sparse` + `tay_witness` + tree-packing reformulations.

## Decisions made during this phase

(none yet — phase just opened)

## Blockers / open questions

- **`(δ-1)·G` realization on `Graph α β`.** Need a clean construction of the
  multiplied multigraph on the mathlib `Graph α β` carrier (edge type `β`
  replaced by `β × Fin (δ-1)` or similar) such that `cycleMatroid`,
  `Graph.IsSparse`, and `vertexSet`/`edgeSet` cardinalities transport. First
  Lean spike (the `def:edge-multiply` leaf) will determine whether mathlib's
  `Graph` API gives this cheaply or whether a helper is needed — record the
  outcome here.
- **Degree of reuse of `tay_witness`.** The reduction should make
  `thm:body-hinge-tay` a near-`rw` of `tay_witness` on `(δ-1)·G`. If the
  body-hinge rigidity-map *definition* (routing through the induced body-bar
  framework) forces non-trivial glue (orientation transport across the edge
  multiplication, dual-space basis bookkeeping), that glue is the real Phase-16
  content — flag it once the spike lands.

## Hand-off / next phase

**Smallest next commit:** formalize `def:edge-multiply` — the
`(δ-1)·G` parallel-edge multiplication on `Graph α β` (a `def` producing a
`Graph α (β × Fin (δ-1))` or equivalent) with the three transport facts
(`V` preserved, `|E| = m·|E|`, spanning-vertex agreement) — in a new
`BodyBar/BodyHinge.lean`, and flip `def:edge-multiply` green in `body-hinge.tex`
in the same commit. This is the leaf-most red node; everything else `\uses` it.

Follow-on after Phase 16: the **molecular conjecture** (panel-and-hinge with
concurrent hinges; Tay–Whiteley conjecture, proved by Katoh–Tanigawa 2011) — a
longer-horizon **Phase 17** target, not opened. Whiteley's "almost all
realizations are rigid" irreducible-variety lift remains deferred.
