# Phase 16 — Body-hinge Tay–Whiteley theorem (existence form) (work log)

**Status:** in progress (leaf node `def:edge-multiply` landed).

## Current state

The target is the **body-hinge / panel-hinge Tay–Whiteley theorem** in
`n`-space (Tay 1989, Whiteley 1988), existence-of-realization form, **via the
matroid-union reduction to Phase 15's body-bar theorem**: a multigraph `G`
carries an independent (resp. isostatic) body-hinge framework in `ℝⁿ` iff
`(δ-1)·G` is `(δ,δ)`-sparse (resp. tight), where `δ = bodyBarDim n = n(n+1)/2`
and `(δ-1)·G` replaces each hinge by `δ-1` parallel bars. This reduces
node-for-node to `Graph.BodyBarFramework.tay_witness` (Phase 15) once the
hinge-to-bar reduction (`def:body-hinge-framework`, `lem:edge-multiply-sparse`)
lands.

Forward-mode phase. The authoritative dep-graph and lemma index is the
blueprint chapter `body-hinge.tex` (§`sec:body-hinge`). The leaf node
`def:edge-multiply` is now green: `Graph.edgeMultiply` and its three transport
facts live in `BodyBar/BodyHinge.lean` (new, in the `CombinatorialRigidity.lean`
aggregator). Next concrete step is `def:body-hinge-framework` — the body-hinge
framework as the induced body-bar framework on `(δ-1)·G`.

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

- [x] `def:edge-multiply` — `(δ-1)·G` parallel-edge multiplication on
  `Graph α β` (`Graph.edgeMultiply`, edge type `β × Fin m`); vertex set
  preserved, `|E(m·G)| = m·|E(G)|`, spanning-vertex transport (the latter under
  `[NeZero m]`). In `BodyBar/BodyHinge.lean`.
- [ ] `def:body-hinge-framework` — body-hinge framework as the induced body-bar
  framework on `(δ-1)·G`; rigidity / independence inherited.
- [ ] `lem:edge-multiply-sparse` — independent/isostatic body-hinge ⇔
  `(δ,δ)`-sparse/tight `(δ-1)·G`; the count `(δ-1)|E| = δ(|V|-1)`.
- [ ] `thm:body-hinge-tay` — the chapter target; assemble from
  `lem:edge-multiply-sparse` + `tay_witness` + tree-packing reformulations.

## Decisions made during this phase

### Phase-local choices and proof techniques

- **`edgeMultiply` edge type = `β × Fin m`, incidence on the first
  coordinate.** `m · G` is built as a direct `Graph α (β × Fin m)` literal:
  `vertexSet := V(G)`, `IsLink (e,i) x y := G.IsLink e x y`, `edgeSet :=
  {p | p.1 ∈ E(G)}`. `V` preservation and `edgeSet` are `rfl`; `|E| = m·|E(G)|`
  is `Set.ncard_prod` after `ext` to `E(G) ×ˢ univ`. Clean — no helper or
  mathlib gap; the `Graph` structure-literal route was cheap (resolves the
  Blockers spike).
- **`spanningVerts` transport needs `[NeZero m]`.** For `m = 0` the multiplied
  graph is edgeless, so `spanningVerts_edgeMultiply` is false; stated under
  `[NeZero m]`. The reduction uses `m = δ - 1 ≥ 1` (δ ≥ 3 for `n ≥ 2`), so the
  hypothesis is free downstream. Reverse direction picks the copy `(e, ⟨0,…⟩)`.

### Promoted to TACTICS-GOLF / TACTICS-QUIRKS / FRICTION / DESIGN

- *Bare `\lean{}` in blueprint prose poisons `lean_decls` / fails `checkdecls`*
  → `blueprint/SETUP-AND-PITFALLS.md` *Pitfalls* (hit on this commit: the
  phase-opening chapter preamble's "gains a `\lean{}` pointer" prose silently
  injected a blank decl that only failed once real `\lean{}` entries landed
  after it).

## Blockers / open questions

- **Degree of reuse of `tay_witness`.** The reduction should make
  `thm:body-hinge-tay` a near-`rw` of `tay_witness` on `(δ-1)·G`. If the
  body-hinge rigidity-map *definition* (routing through the induced body-bar
  framework) forces non-trivial glue (orientation transport across the edge
  multiplication, dual-space basis bookkeeping), that glue is the real Phase-16
  content — flag it once the spike lands.

## Hand-off / next phase

**Smallest next commit:** formalize `def:body-hinge-framework` — the body-hinge
framework as the induced body-bar framework on `(δ-1)·G`, reusing
`Graph.edgeMultiply` (now green) plus `Graph.BodyBarFramework` (Phase 15
`BodyBar/Framework.lean`). The body-hinge rigidity map is *defined* as the
body-bar rigidity map of the induced framework on `(δ-1)·G`, with infinitesimal
rigidity / independence inherited; assess whether the dual-space-basis
bookkeeping (each hinge's `δ-1` bars carry a basis of its dual space) forces
non-trivial glue or whether the standard-basis witness on `(δ-1)·G` routes
through verbatim. Land it in `BodyBar/BodyHinge.lean` and flip
`def:body-hinge-framework` green in `body-hinge.tex` in the same commit.

`def:edge-multiply` is done (`Graph.edgeMultiply` + 3 transport facts).

Follow-on after Phase 16: the **molecular conjecture** (panel-and-hinge with
concurrent hinges; Tay–Whiteley conjecture, proved by Katoh–Tanigawa 2011) — a
longer-horizon **Phase 17** target, not opened. Whiteley's "almost all
realizations are rigid" irreducible-variety lift remains deferred.
